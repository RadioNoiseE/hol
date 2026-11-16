package hol.lib;

import hol.kernel.*;
import java.util.Map;

public final class Classical {
    private Classical() {
        // cannot be instantiated
    }

    private static final Type.Var A = Type.var("a");
    private static final Type.Var B = Type.var("b");

    private static final Term.Var X = new Term.Var("x", A);
    private static final Term.Var G = new Term.Var("g", Type.fun(A, B));

    private static Term app(Term f, Term... xs) {
        Term t = f;
        for (Term x : xs)
            t = new Term.Comb(t, x);
        return t;
    }

    private static Term lam(Term.Var v, Term b) {
        return new Term.Abs(v, b);
    }

    private static Term.Var rty(Map<Type.Var, Type> theta, Term.Var v) {
        return new Term.Var(v.n(), Type.subst(theta, v.t()));
    }

    // ETA_AX: |- !g. (\x. g x) = g
    public static final Thm ETA_AX = Thm.newAxiom(Bool.mkForall(G, Term.mkEq(lam(X, app(G, X)), G)));

    // ETA_PTH: |- (\x. g x) = g
    private static final Thm ETA_PTH = Bool.spec(G, ETA_AX);

    // ETA_CONV: \v. f v => |- (\v. f v) = f
    public static Thm etaConv(Term t) {
        // v not free in f
        if (!(t instanceof Term.Abs(Term.Var v, Term.Comb(Term f, Term.Var w))) || !v.equals(w) || Term.freeIn(v, f))
            throw new HolException("etaConv: not an eta-redex: " + t);
        Map<Type.Var, Type> theta = Map.of(A, v.t(), A, Type.range(Term.typeOf(f)));
        Thm t1 = Thm.instType(theta, ETA_PTH); // |- (\x. g x) = g
        Thm t2 = Thm.inst(Map.of(rty(theta, G), f), t1); // |- (\x. f x) = f
        return Thm.trans(Thm.refl(t), t2);
    }
}
