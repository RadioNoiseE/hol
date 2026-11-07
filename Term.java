import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

record Binding(Term.Var left, Term.Var right) {
    // package-private binding as entry for stacks
}

public sealed interface Term permits Term.Var, Term.Const, Term.Comb, Term.Abs {
    record Var(String name, Type type) implements Term {
        @Override
        public String toString() {
            return Term.show(this);
        }
    }

    record Const(String name, Type type) implements Term {
        @Override
        public String toString() {
            return Term.show(this);
        }
    }

    record Comb(Term fun, Term arg) implements Term {
        public Comb {
            Type funType = typeOf(fun);
            if (!Type.isFun(funType) || !Type.domain(funType).equals(typeOf(arg)))
                throw new HolException(
                        "Comb: cannot apply " + fun + " : " + funType + " to " + arg + " : " + typeOf(arg));
        }

        @Override
        public String toString() {
            return Term.show(this);
        }
    }

    record Abs(Var bvar, Term body) implements Term {
        @Override
        public String toString() {
            return Term.show(this);
        }
    }

    static Type typeOf(Term t) {
        return switch (t) {
            case Var v -> v.type();
            case Const c -> c.type();
            case Comb(Term f, Term _) -> Type.range(typeOf(f));
            case Abs(Var v, Term b) -> Type.fun(v.type(), typeOf(b));
        };
    }

    static Set<Var> frees(Term t) {
        Set<Var> result = new LinkedHashSet<>();
        switch (t) {
            case Var v -> result.add(v);
            case Const _ -> {
                // a const has no free variables
            }
            case Comb(Term f, Term x) -> {
                result.addAll(frees(f));
                result.addAll(frees(x));
            }
            case Abs(Var v, Term b) -> {
                result.addAll(frees(b));
                result.remove(v);
            }
        }
        return result;
    }

    static boolean freeIn(Var v, Term t) {
        return switch (t) {
            case Var w -> w.equals(v);
            case Const _ -> false;
            case Comb(Term f, Term x) -> freeIn(v, f) || freeIn(v, x);
            case Abs(Var w, Term b) -> !w.equals(v) && freeIn(v, b);
        };
    }

    static boolean aconv(Term s, Term t) {
        return aconv(s, t, new ArrayDeque<>());
    }

    private static boolean aconv(Term s, Term t, Deque<Binding> env) {
        if (s instanceof Var v && t instanceof Var w) {
            for (Binding b : env)
                if (b.left().equals(v) || b.right().equals(w))
                    return b.left().equals(v) && b.right().equals(w);
            return v.equals(w);
        }
        if (s instanceof Const c && t instanceof Const d)
            return c.equals(d);
        if (s instanceof Comb(Term f, Term x) && t instanceof Comb(Term g, Term y))
            return aconv(f, g, env) && aconv(x, y, env);
        if (s instanceof Abs(Var v, Term b) && t instanceof Abs(Var w, Term c)) {
            if (!typeOf(v).equals(typeOf(w)))
                return false;
            env.push(new Binding(v, w));
            try {
                return aconv(b, c, env);
            } finally {
                env.pop();
            }
        }
        return false;
    }

    static Var variant(Set<Var> avoid, Var v) {
        Set<String> s = new HashSet<>();
        for (Var w : avoid)
            s.add(w.name());
        String n = v.name();
        while (s.contains(n))
            n += '\'';
        return new Var(n, v.type());
    }

    static Term vsubst(Map<Var, Term> theta, Term t) {
        for (Map.Entry<Var, Term> e : theta.entrySet())
            if (!e.getKey().type().equals(typeOf(e.getValue())))
                throw new HolException(
                        "vsubst: cannot replace " + e.getKey() + " : " + e.getKey().type() + " by " + e.getValue()
                                + " : " + typeOf(e.getValue()));
        return vsubstChecked(theta, t);
    }

    private static Term vsubstChecked(Map<Var, Term> theta, Term t) {
        return switch (t) {
            case Var v -> theta.getOrDefault(v, v);
            case Const c -> c;
            case Comb(Term f, Term x) -> new Comb(vsubstChecked(theta, f), vsubstChecked(theta, x));
            case Abs(Var v, Term b) -> {
                Map<Var, Term> inner = new HashMap<>();
                Set<Var> avoid = frees(b);
                for (Map.Entry<Var, Term> e : theta.entrySet())
                    if (!e.getKey().equals(v) && avoid.contains(e.getKey()))
                        inner.put(e.getKey(), e.getValue());
                if (inner.isEmpty())
                    yield t;
                boolean capture = false;
                for (Map.Entry<Var, Term> e : inner.entrySet()) {
                    Set<Var> f = frees(e.getValue());
                    avoid.addAll(f);
                    if (f.contains(v))
                        capture = true;
                }
                if (!capture)
                    yield new Abs(v, vsubstChecked(inner, b));
                Var w = variant(avoid, v);
                inner.put(v, w);
                yield new Abs(w, vsubstChecked(inner, b));
            }
        };
    }

    static Term inst(Map<Type.Var, Type> theta, Term t) {
        return switch (t) {
            case Var v -> new Var(v.name(), Type.subst(theta, v.type()));
            case Const c -> new Const(c.name(), Type.subst(theta, c.type()));
            case Comb(Term f, Term x) -> new Comb(inst(theta, f), inst(theta, x));
            case Abs(Var v, Term b) -> {
                Set<Var> avoid = frees(b);
                Var w = new Var(v.name(), Type.subst(theta, v.type()));
                boolean clash = false;
                for (Var f : avoid)
                    if (!f.equals(v) && inst(theta, f).equals(w))
                        clash = true;
                if (!clash)
                    yield new Abs(w, inst(theta, b));
                w = variant(avoid, v);
                yield inst(theta, new Abs(w, vsubst(Map.of(v, w), b)));
            }
        };
    }

    static String show(Term t) {
        StringBuilder sb = new StringBuilder();
        show(t, 0, sb);
        return sb.toString();
    }

    // precedence: 0 = anywhere, 1 = function position, 2 = argument position
    private static void show(Term t, int prec, StringBuilder sb) {
        switch (t) {
            case Var v -> sb.append(v.name());
            case Const c -> {
                if (Character.isLetter(c.name().charAt(0)))
                    sb.append(c.name());
                else
                    sb.append('(').append(c.name()).append(')');
            }
            case Comb(Term f, Term x) -> {
                if (prec > 1)
                    sb.append('(');
                show(f, 1, sb);
                sb.append(' ');
                show(x, 2, sb);
                if (prec > 1)
                    sb.append(')');
            }
            case Abs(Var v, Term b) -> {
                if (prec > 0)
                    sb.append('(');
                sb.append('\\').append(v.name()).append(':').append(v.type()).append(". ");
                show(b, 0, sb);
                if (prec > 0)
                    sb.append(')');
            }
        }
    }
}
