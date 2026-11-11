package hol.test;

import hol.kernel.*;
import hol.lib.*;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

final class Props {
    private Props() {
        // cannot be instantiated
    }

    // run prop on n random cases; prop returns null when the case
    // passes, otherwise a description of the counterexample
    private static void forAll(String name, long seed, int n, Function<Gen, String> prop) {
        Gen g = new Gen(seed);
        for (int i = 0; i < n; i++) {
            String bad;
            try {
                bad = prop.apply(g);
            } catch (RuntimeException e) {
                bad = "threw " + e;
            }
            if (bad != null) {
                Check.fail(name, Check.detail("seed", seed), Check.detail("case", i), Check.detail("found", bad));
                return;
            }
        }
        Check.pass(name);
    }

    private static Map<Type.Var, Type> typeSubst(Gen g) {
        return Map.of(Type.var("a"), g.type(1), Type.var("b"), g.type(1));
    }

    private static Term.Var instVar(Map<Type.Var, Type> theta, Term.Var v) {
        return new Term.Var(v.n(), Type.subst(theta, v.t()));
    }

    // a name-free rendering of a term (de Bruijn indices): two terms
    // are alpha-equivalent exactly when their renderings are equal
    private static String db(Term t, Deque<Term.Var> env) {
        return switch (t) {
            case Term.Var v -> {
                int i = 0;
                for (Term.Var w : env) {
                    if (w.equals(v))
                        yield "#" + i;
                    i++;
                }
                yield "free(" + v.n() + ":" + v.t() + ")";
            }
            case Term.Const c -> "const(" + c.n() + ":" + c.t() + ")";
            case Term.Comb(Term f, Term x) -> "(" + db(f, env) + " " + db(x, env) + ")";
            case Term.Abs(Term.Var v, Term b) -> {
                env.push(v);
                String s = "(\\:" + v.t() + ". " + db(b, env) + ")";
                env.pop();
                yield s;
            }
        };
    }

    private static boolean dbEqual(Term s, Term t) {
        return db(s, new ArrayDeque<>()).equals(db(t, new ArrayDeque<>()));
    }

    // free variables computed independently of Term.frees: walk the
    // term with a stack of binders and collect every variable not
    // bound on the stack
    private static void freesOracle(Term t, Deque<Term.Var> env, Set<Term.Var> acc) {
        switch (t) {
            case Term.Var v -> {
                if (!env.contains(v))
                    acc.add(v);
            }
            case Term.Const _ -> {
                // no free variables for const
            }
            case Term.Comb(Term f, Term x) -> {
                freesOracle(f, env, acc);
                freesOracle(x, env, acc);
            }
            case Term.Abs(Term.Var v, Term b) -> {
                env.push(v);
                freesOracle(b, env, acc);
                env.pop();
            }
        }
    }

    public static void main(String[] args) {
        long seed = args.length > 0 ? Long.parseLong(args[0]) : System.nanoTime();
        int n = args.length > 1 ? Integer.parseInt(args[1]) : 1000;
        Check.section("properties, seed " + seed + ", " + n + " cases each", () -> run(seed, n));
        Check.report();
    }

    static void run(long seed, int n) {
        forAll("aconv compares binder types", seed, n, g -> {
            Term b = g.term(g.type(1), 3);
            Term.Var v = g.var(g.type(1));
            Term.Var w = g.var(g.type(1));
            if (Term.freeIn(v, b) || Term.freeIn(w, b))
                return null;
            boolean same = v.t().equals(w.t());
            return Term.aconv(new Term.Abs(v, b), new Term.Abs(w, b)) == same ? null
                    : "\\" + v + ":" + v.t() + " and \\" + w + ":" + w.t() + " over " + b;
        });

        forAll("frees agrees with an independent computation", seed, n, g -> {
            Term t = g.term();
            Set<Term.Var> want = new HashSet<>();
            freesOracle(t, new ArrayDeque<>(), want);
            return new HashSet<>(Term.frees(t)).equals(want) ? null
                    : t + ": frees " + Term.frees(t) + ", wanted " + want;
        });

        forAll("aconv agrees with de Bruijn comparison", seed, n, g -> {
            Term t = g.term();
            Term u = g.coin() ? g.rename(t) : g.mutate(g.rename(t));
            return Term.aconv(t, u) == dbEqual(t, u) ? null
                    : t + "  vs  " + u + ": aconv says " + Term.aconv(t, u);
        });

        forAll("generated terms have the requested type", seed, n, g -> {
            Type ty = g.type(2);
            Term t = g.term(ty, 4);
            return Term.typeOf(t).equals(ty) ? null : t + " : " + Term.typeOf(t) + ", wanted " + ty;
        });

        forAll("aconv is reflexive", seed, n, g -> {
            Term t = g.term();
            return Term.aconv(t, t) ? null : t.toString();
        });

        forAll("renaming bound variables gives an alpha-equivalent term", seed, n, g -> {
            Term t = g.term();
            Term u = g.rename(t);
            if (!Term.aconv(t, u) || !Term.aconv(u, t))
                return t + "  vs  " + u;
            return Term.frees(t).equals(Term.frees(u)) ? null : "frees differ: " + t + "  vs  " + u;
        });

        forAll("vsubst preserves types", seed, n, g -> {
            Term t = g.term();
            for (Term.Var v : Term.frees(t)) {
                Term s = g.term(v.t(), 3);
                Term u = Term.vsubst(Map.of(v, s), t);
                if (!Term.typeOf(u).equals(Term.typeOf(t)))
                    return t + " [" + s + "/" + v + "] = " + u;
            }
            return null;
        });

        forAll("free variables after vsubst", seed, n, g -> {
            Term t = g.term();
            for (Term.Var v : Term.frees(t)) {
                Term s = g.term(v.t(), 3);
                Set<Term.Var> want = new HashSet<>(Term.frees(t));
                want.remove(v);
                want.addAll(Term.frees(s));
                Term u = Term.vsubst(Map.of(v, s), t);
                if (!new HashSet<>(Term.frees(u)).equals(want))
                    return t + " [" + s + "/" + v + "] = " + u + ", frees " + Term.frees(u) + ", wanted " + want;
            }
            return null;
        });

        forAll("vsubst respects alpha-equivalence", seed, n, g -> {
            Term t = g.term();
            Term u = g.rename(t);
            for (Term.Var v : Term.frees(t)) {
                Term s = g.term(v.t(), 3);
                Term t1 = Term.vsubst(Map.of(v, s), t);
                Term u1 = Term.vsubst(Map.of(v, s), u);
                if (!Term.aconv(t1, u1))
                    return t + " and " + u + " with [" + s + "/" + v + "] give " + t1 + " and " + u1;
            }
            return null;
        });

        forAll("inst preserves types", seed, n, g -> {
            Term t = g.term();
            Map<Type.Var, Type> theta = typeSubst(g);
            Term u = Term.inst(theta, t);
            Type want = Type.subst(theta, Term.typeOf(t));
            return Term.typeOf(u).equals(want) ? null : t + " with " + theta + " = " + u;
        });

        forAll("free variables after inst", seed, n, g -> {
            Term t = g.term();
            Map<Type.Var, Type> theta = typeSubst(g);
            Set<Term.Var> want = new HashSet<>();
            for (Term.Var v : Term.frees(t))
                want.add(instVar(theta, v));
            Term u = Term.inst(theta, t);
            return new HashSet<>(Term.frees(u)).equals(want) ? null
                    : t + " with " + theta + " = " + u + ", frees " + Term.frees(u) + ", wanted " + want;
        });

        forAll("inst respects alpha-equivalence", seed, n, g -> {
            Term t = g.term();
            Term u = g.rename(t);
            Map<Type.Var, Type> theta = typeSubst(g);
            Term t1 = Term.inst(theta, t);
            Term u1 = Term.inst(theta, u);
            return Term.aconv(t1, u1) ? null : t + " and " + u + " with " + theta + " give " + t1 + " and " + u1;
        });

        forAll("match undoes subst", seed, n, g -> {
            Type ty = g.type(3);
            Map<Type.Var, Type> theta = typeSubst(g);
            Type u = Type.subst(theta, ty);
            Type back = Type.subst(Type.match(ty, u), ty);
            return back.equals(u) ? null : ty + " against " + u + " gives " + back;
        });

        forAll("betaConv agrees with vsubst", seed, n, g -> {
            Type s1 = g.type(1);
            Term.Var v = g.var(s1);
            Term b = g.term(g.type(2), 3);
            Term s = g.term(s1, 3);
            Term t = new Term.Comb(new Term.Abs(v, b), s);
            Thm th = Equal.betaConv(t);
            Term.Eq e = Term.destEq(th.concl());
            if (!th.hyps().isEmpty() || !e.l().equals(t))
                return "wrong shape: " + th;
            Term want = Term.vsubst(Map.of(v, s), b);
            return Term.aconv(e.r(), want) ? null : th + ", wanted right side " + want;
        });

        forAll("sym swaps the sides", seed, n, g -> {
            Type ty = g.type(2);
            Term l = g.term(ty, 3);
            Term r = g.term(ty, 3);
            Thm th = Equal.sym(Thm.assume(Term.mkEq(l, r)));
            return th.concl().equals(Term.mkEq(r, l)) ? null : th.toString();
        });
    }
}
