package hol.syntax;

import hol.kernel.*;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

public final class Infer {
    private sealed interface Pretype permits Rigid, Meta, Op {
        // a type during inference
    }

    private record Rigid(String n) implements Pretype {
        // a type variable written by the user
    }

    private record Meta(int k) implements Pretype {
        // an unknown
    }

    private record Op(String n, List<Pretype> as) implements Pretype {
        // a type operator applied to arguments
    }

    private sealed interface Node permits Var, Const, Comb, Abs {
        // a resolved term
    }

    private record Var(String n, Pretype y) implements Node {
        // a variable, bound or free
    }

    private record Const(String n, Pretype y) implements Node {
        // a constant
    }

    private record Comb(Node f, Node x) implements Node {
        // an application
    }

    private record Abs(Var v, Node b) implements Node {
        // an abstraction
    }

    private int metas = 0;
    private final Map<Integer, Pretype> sigma = new HashMap<>();
    private final Deque<Var> bound = new ArrayDeque<>();
    private final Map<String, Var> frees = new HashMap<>();

    private Infer() {
        // static factory method
    }

    public static Term term(Preterm t) {
        Infer i = new Infer();
        Node n = i.infer(t);
        return i.build(n, i.defaults(n));
    }

    private Node infer(Preterm t) {
        return switch (t) {
            case Preterm.Var v -> name(v.n());
            case Preterm.Comb(Preterm f, Preterm x) -> {
                Node g = infer(f);
                Node y = infer(x);
                unify(typeOf(g), new Op("fun", List.of(typeOf(y), fresh())));
                yield new Comb(g, y);
            }
            case Preterm.Abs(Preterm v, Preterm b) -> {
                Var w = binding(v);
                bound.push(w);
                try {
                    yield new Abs(w, infer(b));
                } finally {
                    bound.pop();
                }
            }
            case Preterm.Typed(Preterm u, Type y) -> {
                Node v = infer(u);
                unify(typeOf(v), pretype(y, new HashMap<>(), false));
                yield v;
            }
        };
    }

    private Node name(String n) {
        for (Var v : bound)
            if (v.n().equals(n))
                return v;
        if (Sig.consts().containsKey(n))
            return new Const(n, pretype(Sig.constType(n), new HashMap<>(), true));
        if (Notation.isSpecial(n))
            throw new HolException("infer: " + n + " has notation but is not a declared constant");
        return frees.computeIfAbsent(n, m -> new Var(m, fresh()));
    }

    private Meta fresh() {
        return new Meta(metas++);
    }

    private Var binding(Preterm v) {
        return switch (v) {
            case Preterm.Var(String n) -> new Var(n, fresh());
            case Preterm.Typed(Preterm.Var(String n), Type y) -> new Var(n, pretype(y, new HashMap<>(), false));
            default -> throw new HolException("infer: a binder needs a variable: " + v);
        };
    }

    private Pretype typeOf(Node n) {
        return switch (n) {
            case Var v -> v.y();
            case Const c -> c.y();
            case Comb(Node f, Node _) -> ((Op) walk(typeOf(f))).as().get(1);
            case Abs(Var v, Node b) -> new Op("fun", List.of(v.y(), typeOf(b)));
        };
    }

    private Pretype pretype(Type y, Map<String, Meta> theta, boolean generic) {
        return switch (y) {
            case Type.Var(String n) -> generic ? theta.computeIfAbsent(n, m -> fresh()) : new Rigid(n);
            case Type.App(String o, List<Type> as) -> {
                List<Pretype> bs = new ArrayList<>();
                for (Type a : as)
                    bs.add(pretype(a, theta, generic));
                yield new Op(o, bs);
            }
        };
    }

    private void unify(Pretype y1, Pretype y2) {
        Pretype a = walk(y1);
        Pretype b = walk(y2);
        if (a.equals(b))
            return;
        if (a instanceof Meta(int k)) {
            if (occurs(k, b))
                throw new HolException("infer: cannot construct an infinite type " + show(a) + " = " + show(b));
            sigma.put(k, b);
        } else if (b instanceof Meta) {
            unify(b, a);
        } else if (a instanceof Op(String o1, List<Pretype> as) && b instanceof Op(String o2, List<Pretype> bs)
                && o1.equals(o2)) {
            for (int j = 0; j < as.size(); j++)
                unify(as.get(j), bs.get(j));
        } else
            throw new HolException("infer: cannot unify " + show(a) + " with " + show(b));
    }

    private Pretype walk(Pretype y) {
        while (y instanceof Meta(int k) && sigma.containsKey(k))
            y = sigma.get(k);
        return y;
    }

    private boolean occurs(int k, Pretype y) {
        return switch (walk(y)) {
            case Meta(int j) -> j == k;
            case Rigid _ -> false;
            case Op(String _, List<Pretype> as) -> as.stream().anyMatch(a -> occurs(k, a));
        };
    }

    private String show(Pretype y) {
        return switch (walk(y)) {
            case Rigid(String n) -> "'" + n;
            case Meta(int k) -> "?" + k;
            case Op(String o, List<Pretype> as) when o.equals("fun") ->
                "(" + show(as.get(0)) + " -> " + show(as.get(1)) + ")";
            case Op(String o, List<Pretype> as) when as.isEmpty() -> o;
            case Op(String o, List<Pretype> as) ->
                "(" + String.join(", ", as.stream().map(this::show).toList()) + ")" + o;
        };
    }

    private Map<Integer, Type> defaults(Node n) {
        Map<Integer, Type> d = new HashMap<>();
        Set<String> used = new HashSet<>();
        Set<Integer> open = new LinkedHashSet<>();
        collect(n, used, open);
        int c = 0;
        for (int k : open) {
            while (used.contains(letter(c)))
                c++;
            d.put(k, Type.var(letter(c)));
            used.add(letter(c));
            c++;
        }
        return d;
    }

    private void collect(Node n, Set<String> used, Set<Integer> open) {
        switch (n) {
            case Var v -> scan(v.y(), used, open);
            case Const c -> scan(c.y(), used, open);
            case Comb(Node f, Node x) -> {
                collect(f, used, open);
                collect(x, used, open);
            }
            case Abs(Var v, Node b) -> {
                scan(v.y(), used, open);
                collect(b, used, open);
            }
        }
    }

    private void scan(Pretype y, Set<String> used, Set<Integer> open) {
        switch (walk(y)) {
            case Rigid(String n) -> used.add(n);
            case Meta(int k) -> open.add(k);
            case Op(String _, List<Pretype> as) -> as.forEach(a -> scan(a, used, open));
        }
    }

    private static String letter(int k) {
        String s = String.valueOf((char) ('a' + k % 26));
        return k < 26 ? s : s + k / 26;
    }

    private Term build(Node n, Map<Integer, Type> d) {
        return switch (n) {
            case Var v -> new Term.Var(v.n(), type(v.y(), d));
            case Const c -> new Term.Const(c.n(), type(c.y(), d));
            case Comb(Node f, Node x) -> new Term.Comb(build(f, d), build(x, d));
            case Abs(Var v, Node b) -> new Term.Abs((Term.Var) build(v, d), build(b, d));
        };
    }

    private Type type(Pretype y, Map<Integer, Type> d) {
        return switch (walk(y)) {
            case Rigid(String n) -> Type.var(n);
            case Meta(int k) -> d.get(k);
            case Op(String o, List<Pretype> as) -> new Type.App(o, as.stream().map(a -> type(a, d)).toList());
        };
    }
}
