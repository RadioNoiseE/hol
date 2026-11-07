import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

record Pair(Term.Var l, Term.Var r) {
    // package-private pair as entry for stacks
}

public sealed interface Term permits Term.Var, Term.Const, Term.Comb, Term.Abs {
    record Var(String n, Type t) implements Term {
        @Override
        public String toString() {
            return Term.show(this);
        }
    }

    record Const(String n, Type t) implements Term {
        @Override
        public String toString() {
            return Term.show(this);
        }
    }

    record Comb(Term f, Term x) implements Term {
        public Comb {
            Type t = typeOf(f);
            if (!Type.isFun(t) || !Type.domain(t).equals(typeOf(x)))
                throw new HolException(
                        "Comb: cannot apply " + f + " : " + t + " to " + x + " : " + typeOf(x));
        }

        @Override
        public String toString() {
            return Term.show(this);
        }
    }

    record Abs(Var v, Term b) implements Term {
        @Override
        public String toString() {
            return Term.show(this);
        }
    }

    static Type typeOf(Term t) {
        return switch (t) {
            case Var v -> v.t();
            case Const c -> c.t();
            case Comb(Term f, Term _) -> Type.range(typeOf(f));
            case Abs(Var v, Term b) -> Type.fun(v.t(), typeOf(b));
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

    private static boolean aconv(Term s, Term t, Deque<Pair> env) {
        if (s instanceof Var v && t instanceof Var w) {
            for (Pair p : env)
                if (p.l().equals(v) || p.r().equals(w))
                    return p.l().equals(v) && p.r().equals(w);
            return v.equals(w);
        }
        if (s instanceof Const c && t instanceof Const d)
            return c.equals(d);
        if (s instanceof Comb(Term f, Term x) && t instanceof Comb(Term g, Term y))
            return aconv(f, g, env) && aconv(x, y, env);
        if (s instanceof Abs(Var v, Term b) && t instanceof Abs(Var w, Term c)) {
            if (!v.t().equals(w.t()))
                return false;
            env.push(new Pair(v, w));
            try {
                return aconv(b, c, env);
            } finally {
                env.pop();
            }
        }
        return false;
    }

    static Var variant(Set<Var> vs, Var v) {
        Set<String> ns = new HashSet<>();
        for (Var w : vs)
            ns.add(w.n());
        String n = v.n();
        while (ns.contains(n))
            n += '\'';
        return new Var(n, v.t());
    }

    static Term vsubst(Map<Var, Term> theta, Term t) {
        for (Map.Entry<Var, Term> e : theta.entrySet()) {
            Var v = e.getKey();
            Term s = e.getValue();
            if (!v.t().equals(typeOf(s)))
                throw new HolException(
                        "vsubst: cannot replace " + v + " : " + v.t() + " by " + s
                                + " : " + typeOf(s));
        }
        return vsub(theta, t);
    }

    private static Term vsub(Map<Var, Term> theta, Term t) {
        return switch (t) {
            case Var v -> theta.getOrDefault(v, v);
            case Const c -> c;
            case Comb(Term f, Term x) -> new Comb(vsub(theta, f), vsub(theta, x));
            case Abs(Var v, Term b) -> {
                Map<Var, Term> sigma = new HashMap<>();
                Set<Var> vs = frees(b);
                for (Map.Entry<Var, Term> e : theta.entrySet())
                    if (!e.getKey().equals(v) && vs.contains(e.getKey()))
                        sigma.put(e.getKey(), e.getValue());
                if (sigma.isEmpty())
                    yield t;
                boolean capture = false;
                for (Map.Entry<Var, Term> e : sigma.entrySet()) {
                    Set<Var> f = frees(e.getValue());
                    vs.addAll(f);
                    if (f.contains(v))
                        capture = true;
                }
                if (!capture)
                    yield new Abs(v, vsub(sigma, b));
                Var w = variant(vs, v);
                sigma.put(v, w);
                yield new Abs(w, vsub(sigma, b));
            }
        };
    }

    static Term inst(Map<Type.Var, Type> theta, Term t) {
        return switch (t) {
            case Var v -> new Var(v.n(), Type.subst(theta, v.t()));
            case Const c -> new Const(c.n(), Type.subst(theta, c.t()));
            case Comb(Term f, Term x) -> new Comb(inst(theta, f), inst(theta, x));
            case Abs(Var v, Term b) -> {
                Set<Var> vs = frees(b);
                Var w = new Var(v.n(), Type.subst(theta, v.t()));
                boolean clash = false;
                for (Var f : vs)
                    if (!f.equals(v) && inst(theta, f).equals(w))
                        clash = true;
                if (!clash)
                    yield new Abs(w, inst(theta, b));
                w = variant(vs, v);
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
    private static void show(Term t, int p, StringBuilder sb) {
        switch (t) {
            case Var v -> sb.append(v.n());
            case Const c -> {
                if (Character.isLetter(c.n().charAt(0)))
                    sb.append(c.n());
                else
                    sb.append('(').append(c.n()).append(')');
            }
            case Comb(Term f, Term x) -> {
                if (p > 1)
                    sb.append('(');
                show(f, 1, sb);
                sb.append(' ');
                show(x, 2, sb);
                if (p > 1)
                    sb.append(')');
            }
            case Abs(Var v, Term b) -> {
                if (p > 0)
                    sb.append('(');
                sb.append('\\').append(v.n()).append(':').append(v.t()).append(". ");
                show(b, 0, sb);
                if (p > 0)
                    sb.append(')');
            }
        }
    }
}
