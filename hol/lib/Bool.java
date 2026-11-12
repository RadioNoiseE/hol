package hol.lib;

import hol.kernel.*;
import java.util.Map;

public final class Bool {
    private Bool() {
        // cannot be instantiated
    }

    private static final Type BOOL = Type.BOOL;
    private static final Type BINOP = Type.fun(BOOL, Type.fun(BOOL, BOOL));

    private static final Term.Var P = new Term.Var("p", BOOL);
    private static final Term.Var Q = new Term.Var("q", BOOL);
    private static final Term.Var F = new Term.Var("f", BINOP);

    private static Term app(Term f, Term... xs) {
        Term t = f;
        for (Term x : xs)
            t = new Term.Comb(t, x);
        return t;
    }

    private static Term lam(Term.Var v, Term b) {
        return new Term.Abs(v, b);
    }

    // PROVE_HYP: A |- p, B |- q ==> A \/ (B - {p}) |- q
    public static Thm proveHyp(Thm t1, Thm t2) {
        // if p is not in B, yield just B |- q
        if (t2.hyps().stream().noneMatch(h -> Term.aconv(h, t1.concl())))
            return t2;
        return Thm.eqMp(Thm.dar(t1, t2), t1);
    }

    // T_DEF: |- T = ((\p. p) = (\p. p))
    public static final Thm T_DEF = Thm
            .newBasicDef(Term.mkEq(new Term.Var("T", BOOL), Term.mkEq(lam(P, P), lam(P, P))));

    public static final Term T = new Term.Const("T", BOOL);

    // TRUTH: |- T
    public static final Thm TRUTH = Thm.eqMp(Equal.sym(T_DEF), Thm.refl(lam(P, P)));

    // EQT_ELIM: A |- t = T ==> A |- t
    public static Thm eqtElim(Thm t) {
        return Thm.eqMp(Equal.sym(t), TRUTH);
    }

    // EQT_PTH: |- p = (p = T)
    private static final Thm EQT_PTH = eqtPth();

    private static Thm eqtPth() {
        Thm t1 = Thm.dar(Thm.assume(P), TRUTH); // p |- p, |- T ==> p |- p = T
        Thm t2 = eqtElim(Thm.assume(t1.concl())); // p = T |- p = T ==> p = T |- p
        return Thm.dar(t2, t1);
    }

    // EQT_INTRO: A |- t ==> A |- t = T
    public static Thm eqtIntro(Thm t) {
        return Thm.eqMp(Thm.inst(Map.of(P, t.concl()), EQT_PTH), t);
    }

    // AND_DEF: |- (/\) = \p q. (\f. f p q) = (\f. f T T)
    public static final Thm AND_DEF = Thm
            .newBasicDef(Term.mkEq(new Term.Var("/\\", BINOP),
                    lam(P, lam(Q, Term.mkEq(lam(F, app(F, P, Q)), lam(F, app(F, T, T)))))));

    public static final Term AND = new Term.Const("/\\", BINOP);

    public record Conj(Term l, Term r) {
        // the two sides of a conjunction
    }

    public static Term mkConj(Term l, Term r) {
        return app(AND, l, r);
    }

    public static Conj destConj(Term t) {
        if (t instanceof Term.Comb(Term.Comb(Term.Const c, Term l), Term r) && c.n().equals("/\\"))
            return new Conj(l, r);
        throw new HolException("destConj: not a conjunction: " + t);
    }

    // AND_PQ: |- p /\ q = ((\f. f p q) = (\f. f T T))
    private static final Thm AND_PQ = andPq();

    private static Thm andPq() {
        Thm t = Equal.apThm(Equal.apThm(AND_DEF, P), Q); // |- p /\ q = (\p q. (\f. f p q) = (\f. f T T)) p q
        return Thm.trans(t, Equal.betaNorm(Term.destEq(t.concl()).r()));
    }

    // CONJUNCT1_PTH: p /\ q |- p
    // CONJUNCT2_PTH: p /\ q |- q
    private static final Thm CONJUNCT1_PTH = conjunctPth(lam(P, lam(Q, P)));
    private static final Thm CONJUNCT2_PTH = conjunctPth(lam(P, lam(Q, Q)));

    private static Thm conjunctPth(Term s) {
        Thm t1 = Thm.eqMp(AND_PQ, Thm.assume(mkConj(P, Q))); // p /\ q |- (\f. f p q) = (\f. f T T)
        Thm t2 = Equal.betaRule(Equal.apThm(t1, s)); // p /\ q |- (s) p q = (s) T T
        return eqtElim(t2);
    }

    // CONJ_PTH: p |- q = (p /\ q)
    private static final Thm CONJ_PTH = conjPth();

    private static Thm conjPth() {
        Thm t1 = Thm.mkComb(Equal.apTerm(F, eqtIntro(Thm.assume(P))), eqtIntro(Thm.assume(Q))); // p, q |- f p q = f T T
        Thm t2 = Thm.abs(F, t1); // p, q |- (\f. f p q) = (\f. f T T)
        Thm t3 = Thm.eqMp(Equal.sym(AND_PQ), t2); // p, q |- p /\ q
        return Thm.dar(CONJUNCT2_PTH, t3);
    }

    // CONJ: A |- p, B |- q ==> A \/ B |- p /\ q
    public static Thm conj(Thm t1, Thm t2) {
        Thm t3 = Thm.inst(Map.of(P, t1.concl(), Q, t2.concl()), CONJ_PTH); // p |- q = (p /\ q)
        Thm t4 = Thm.dar(t1, t3); // A - {q = (p /\ q)} |- p = (q = (p /\ q))
        return Thm.eqMp(Thm.eqMp(t4, t1), t2);
    }

    // CONJUNCT1: A |- p /\ q ==> A |- p
    public static Thm conjunct1(Thm t) {
        Conj c = destConj(t.concl());
        Thm t1 = Thm.dar(t, Thm.inst(Map.of(P, c.l(), Q, c.r()), CONJUNCT1_PTH)); // A - {p} |- (p /\ q) = p
        return Thm.eqMp(t1, t);
    }

    // CONJUNCT2: A |- p /\ q ==> A |- q
    public static Thm conjunct2(Thm t) {
        Conj c = destConj(t.concl());
        Thm t1 = Thm.dar(t, Thm.inst(Map.of(P, c.l(), Q, c.r()), CONJUNCT2_PTH)); // A - {q} |- (p /\ q) = q
        return Thm.eqMp(t1, t);
    }

    // IMP_DEF: |- (==>) = \p q. (p /\ q) = p
    public static final Thm IMP_DEF = Thm
            .newBasicDef(Term.mkEq(new Term.Var("==>", BINOP), lam(P, lam(Q, Term.mkEq(mkConj(P, Q), P)))));

    public static final Term IMP = new Term.Const("==>", BINOP);

    public record Imp(Term l, Term r) {
        // the antecedent and consequent of an implication
    }

    public static Term mkImp(Term l, Term r) {
        return app(IMP, l, r);
    }

    public static boolean isImp(Term t) {
        return t instanceof Term.Comb(Term.Comb(Term.Const c, Term _), Term _) && c.n().equals("==>");
    }

    public static Imp destImp(Term t) {
        if (t instanceof Term.Comb(Term.Comb(Term.Const c, Term l), Term r) && c.n().equals("==>"))
            return new Imp(l, r);
        throw new HolException("destImp: not an implication: " + t);
    }

    // IMP_PQ: |- (p ==> q) = ((p /\ q) = p)
    private static final Thm IMP_PQ = Equal.betaRule(Equal.apThm(Equal.apThm(IMP_DEF, P), Q));

    // MP_PTH: p |- (p ==> q) = q
    private static final Thm MP_PTH = mpPth();

    private static Thm mpPth() {
        Thm t1 = conj(Thm.assume(P), Thm.assume(Q)); // p, q |- p /\ q
        Thm t2 = conjunct1(Thm.assume(mkConj(P, Q))); // p /\ q |- p
        Thm t3 = Thm.eqMp(Equal.sym(IMP_PQ), Thm.dar(t1, t2)); // q |- p ==> q
        Thm t4 = Thm.eqMp(IMP_PQ, Thm.assume(mkImp(P, Q))); // p ==> q |- (p /\ q) = p
        Thm t5 = conjunct2(Thm.eqMp(Equal.sym(t4), Thm.assume(P))); // p ==> q, p |- q
        return Thm.dar(t3, t5);
    }

    // MP: A |- p ==> q, B |- p ==> A \/ B |- q
    public static Thm mp(Thm t1, Thm t2) {
        Imp i = destImp(t1.concl());
        if (!Term.aconv(i.l(), t2.concl()))
            throw new HolException("mp: theorems do not agree: " + t1 + " and " + t2);
        Thm t = Thm.dar(t2, Thm.inst(Map.of(P, i.l(), Q, i.r()), MP_PTH)); // B - {...} |- p = ((p ==> q) = q)
        return Thm.eqMp(Thm.eqMp(t, t2), t1);
    }

    // DISCH_PTH: |- ((p /\ q) = p) = (p ==> q)
    private static final Thm DISCH_PTH = Equal.sym(IMP_PQ);

    // DISCH: p, A |- q ==> A - {p} |- p ==> q
    public static Thm disch(Term p, Thm t) {
        Thm t1 = conj(Thm.assume(p), t); // A \/ {p} |- p /\ q
        Thm t2 = conjunct1(Thm.assume(t1.concl())); // p /\ q |- p
        Thm t3 = Thm.dar(t1, t2); // A - {p} |- (p /\ q) = p
        Thm t4 = Thm.inst(Map.of(P, p, Q, t.concl()), DISCH_PTH); // |- ((p /\ q) = p) = (p ==> q)
        return Thm.eqMp(t4, t3);
    }

    // DISCH_ALL: p1, ..., pn |- q ==> |- p1 ==> ... ==> pn ==> q
    public static Thm dischAll(Thm t) {
        while (!t.hyps().isEmpty())
            t = disch(t.hyps().get(0), t);
        return t;
    }

    // UNDISCH: A |- p ==> q ==> A, p |- q
    public static Thm undisch(Thm t) {
        return mp(t, Thm.assume(destImp(t.concl()).l()));
    }

    // UNDISCH_ALL: A |- p1 ==> ... ==> pn ==> q ==> A, p1, ..., pn |- q
    public static Thm undischAll(Thm t) {
        while (isImp(t.concl()))
            t = undisch(t);
        return t;
    }

    // ADD_ASSUM: A |- q ==> A, p |- q
    public static Thm addAssum(Term p, Thm t) {
        return mp(disch(p, t), Thm.assume(p));
    }
}
