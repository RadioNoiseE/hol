package hol.lib;

import hol.kernel.*;
import java.util.Map;

public final class Classical {
    private Classical() {
        // cannot be instantiated
    }

    private static final Type.Var A = Type.var("a");
    private static final Type.Var B = Type.var("b");

    private static final Type BOOL = Type.BOOL;
    private static final Type PRED = Type.fun(A, BOOL);

    private static final Term.Var X = new Term.Var("x", A);
    private static final Term.Var P = new Term.Var("p", BOOL);
    private static final Term.Var S = new Term.Var("s", PRED);
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

    static {
        Sig.newConst("@", Type.fun(PRED, A));
    }

    private static Term select(Type t) {
        return new Term.Const("@", Type.fun(Type.fun(t, BOOL), t));
    }

    public record Select(Term.Var v, Term b) {
        // the binding variable and the body
    }

    public static Term mkSelect(Term.Var v, Term b) {
        return app(select(v.t()), lam(v, b));
    }

    public static boolean isSelect(Term t) {
        return t instanceof Term.Comb(Term.Const c, Term.Abs(Term.Var _, Term _)) && c.n().equals("@");
    }

    public static Select destSelect(Term t) {
        if (t instanceof Term.Comb(Term.Const c, Term.Abs(Term.Var v, Term b)) && c.n().equals("@"))
            return new Select(v, b);
        throw new HolException("destSelect: not a selection: " + t);
    }

    // SELECT_AX: |- !s x. s x ==> s (@s)
    public static final Thm SELECT_AX = Thm
            .newAxiom(Bool.mkForall(S, Bool.mkForall(X, Bool.mkImp(app(S, X), app(S, app(select(A), S))))));

    // SELECTED: |- (@l) = c \/ p
    private static Thm selected(Term l, Term c) {
        // where l = \x. x = c \/ p
        Thm t1 = Bool.spec(c, Bool.spec(l, Thm.instType(Map.of(A, BOOL), SELECT_AX))); // |- l c ==> l (@l)
        Thm t2 = Equal.betaRule(t1); // |- c = c \/ p ==> (@l) = c \/ p
        return Bool.mp(t2, Bool.disj1(Thm.refl(c), P));
    }

    // EXCLUDED_MIDDLE: |- !p. p \/ ~p
    public static final Thm EXCLUDED_MIDDLE = Bool.gen(P, em());

    private static Thm em() {
        Term.Var x = new Term.Var("x", BOOL);
        Term l1 = lam(x, Bool.mkDisj(Term.mkEq(x, Bool.F), P)); // \x. x = F \/ p
        Term l2 = lam(x, Bool.mkDisj(Term.mkEq(x, Bool.T), P)); // \x. x = T \/ p
        Term a = app(select(BOOL), l1); // @l1
        Term b = app(select(BOOL), l2); // @l2
        Thm t1 = selected(l1, Bool.F); // |- a = F \/ p
        Thm t2 = selected(l2, Bool.T); // |- b = T \/ p
        Thm t3 = Bool.disj1(Thm.assume(P), Bool.mkNeg(P)); // p |- p \/ ~p
        Thm t4 = Thm.dar(Bool.disj2(Term.mkEq(x, Bool.F), Thm.assume(P)),
                Bool.disj2(Term.mkEq(x, Bool.T), Thm.assume(P))); // p |- (x = F \/ p) = (x = T \/ p)
        Thm t5 = Equal.apTerm(select(BOOL), Thm.abs(x, t4)); // p |- a = b
        Thm t6 = Thm.trans(Thm.trans(Equal.sym(Thm.assume(Term.mkEq(a, Bool.F))), t5),
                Thm.assume(Term.mkEq(b, Bool.T))); // a = F, b = T, p |- F = T
        Thm t7 = Thm.eqMp(Equal.sym(t6), Bool.TRUTH); // a = F, b = T, p |- F
        Thm t8 = Bool.disj2(P, Bool.notIntro(Bool.disch(P, t7))); // a = F, b = T |- p \/ ~p
        Thm t9 = Bool.disjCases(t2, t8, t3); // a = F |- p \/ ~p
        return Bool.disjCases(t1, t9, t3);
    }

    // CCONTR: A + {~p} |- F => A |- p
    public static Thm ccontr(Term p, Thm t) {
        if (Term.aconv(t.concl(), Bool.F))
            return Bool.disjCases(Bool.spec(p, EXCLUDED_MIDDLE), Thm.assume(p), Bool.contr(p, t));
        throw new HolException("ccontr: conclusion is not F: " + t);
    }
}
