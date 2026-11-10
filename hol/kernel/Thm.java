package hol.kernel;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public final class Thm {
    private static final List<Thm> axioms = new ArrayList<>();

    // NEW_AXIOM: p ==> |- p
    public static Thm newAxiom(Term t) {
        if (!Term.typeOf(t).equals(Type.BOOL))
            throw new HolException("newAxiom: not a proposition: " + t);
        Thm th = new Thm(List.of(), t);
        axioms.add(th);
        return th;
    }

    public static List<Thm> axioms() {
        return List.copyOf(axioms);
    }

    private final List<Term> hyps;
    private final Term concl;

    private Thm(List<Term> h, Term c) {
        this.hyps = List.copyOf(h);
        this.concl = c;
    }

    public List<Term> hyps() {
        return hyps;
    }

    public Term concl() {
        return concl;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < hyps.size(); i++) {
            if (i > 0)
                sb.append(", ");
            sb.append(hyps.get(i));
        }
        if (!hyps.isEmpty())
            sb.append(' ');
        sb.append("|- ").append(concl);
        return sb.toString();
    }

    private static boolean contains(List<Term> ts, Term s) {
        for (Term t : ts)
            if (Term.aconv(t, s))
                return true;
        return false;
    }

    private static List<Term> union(List<Term> ss, List<Term> ts) {
        List<Term> us = new ArrayList<>(ss);
        for (Term t : ts)
            if (!contains(us, t))
                us.add(t);
        return us;
    }

    private static List<Term> remove(List<Term> ts, Term s) {
        List<Term> us = new ArrayList<>();
        for (Term t : ts)
            if (!Term.aconv(t, s))
                us.add(t);
        return us;
    }

    // REFL: |- t = t
    public static Thm refl(Term t) {
        return new Thm(List.of(), Term.mkEq(t, t));
    }

    // TRANS: A |- s = t, B |- t = u ==> A \/ B |- s = u
    public static Thm trans(Thm t1, Thm t2) {
        Term.Eq e1 = Term.destEq(t1.concl);
        Term.Eq e2 = Term.destEq(t2.concl);
        if (!Term.aconv(e1.r(), e2.l()))
            throw new HolException("trans: middle terms do not agree: " + e1.r() + " and " + e2.l());
        return new Thm(union(t1.hyps, t2.hyps), Term.mkEq(e1.l(), e2.r()));
    }

    // MK_COMB: A |- f = g, B |- x = y ==> A \/ B |- f x = g y
    public static Thm mkComb(Thm t1, Thm t2) {
        Term.Eq e1 = Term.destEq(t1.concl);
        Term.Eq e2 = Term.destEq(t2.concl);
        return new Thm(union(t1.hyps, t2.hyps),
                Term.mkEq(new Term.Comb(e1.l(), e2.l()), new Term.Comb(e1.r(), e2.r())));
    }

    // ABS: A |- s = t ==> A |- (\v. s) = (\v. t)
    public static Thm abs(Term.Var v, Thm t) {
        Term.Eq e = Term.destEq(t.concl);
        for (Term h : t.hyps)
            if (Term.freeIn(v, h))
                throw new HolException("abs: " + v + " is free in the hypothesis " + h);
        return new Thm(t.hyps, Term.mkEq(new Term.Abs(v, e.l()), new Term.Abs(v, e.r())));
    }

    // BETA: |- (\v. b) v = b
    public static Thm beta(Term t) {
        if (!(t instanceof Term.Comb(Term.Abs(Term.Var v, Term b), Term x)))
            throw new HolException("beta: not of the form (\\v. b) x: " + t);
        if (!x.equals(v))
            throw new HolException("beta: the argument " + x + " is not the bound variable " + v);
        return new Thm(List.of(), Term.mkEq(t, b));
    }

    // ASSUME: t |- t
    public static Thm assume(Term t) {
        if (!Term.typeOf(t).equals(Type.BOOL))
            throw new HolException("assume: not a proposition: " + t + " : " + Term.typeOf(t));
        return new Thm(List.of(t), t);
    }

    // EQ_MP: A |- p = q, B |- p ==> A \/ B |- q
    public static Thm eqMp(Thm t1, Thm t2) {
        Term.Eq e = Term.destEq(t1.concl);
        if (!Term.aconv(e.l(), t2.concl))
            throw new HolException("eqMp: " + t2.concl + " is not the left side of " + t1.concl);
        return new Thm(union(t1.hyps, t2.hyps), e.r());
    }

    // DAR: A |- p, B |- q ==> (A - {q}) \/ (B - {p}) |- p = q
    public static Thm dar(Thm t1, Thm t2) {
        List<Term> h1 = remove(t1.hyps, t2.concl);
        List<Term> h2 = remove(t2.hyps, t1.concl);
        return new Thm(union(h1, h2), Term.mkEq(t1.concl, t2.concl));
    }

    // INST: A |- p ==> theta(A) |- theta(p)
    public static Thm inst(Map<Term.Var, Term> theta, Thm t) {
        List<Term> hs = new ArrayList<>();
        for (Term h : t.hyps)
            hs.add(Term.vsubst(theta, h));
        return new Thm(union(List.of(), hs), Term.vsubst(theta, t.concl));
    }

    // INST_TYPE: A |- p ==> theta(A) |- theta(p)
    public static Thm instType(Map<Type.Var, Type> theta, Thm t) {
        List<Term> hs = new ArrayList<>();
        for (Term h : t.hyps)
            hs.add(Term.inst(theta, h));
        return new Thm(union(List.of(), hs), Term.inst(theta, t.concl));
    }

    // NEW_BASIC_DEF: c = t ==> |- c = t
    public static Thm newBasicDef(Term t) {
        Term.Eq e = Term.destEq(t);
        if (!(e.l() instanceof Term.Var v))
            throw new HolException("newBasicDef: the left side is not a variable: " + e.l());
        if (!Term.frees(e.r()).isEmpty())
            throw new HolException("newBasicDef: the right side has free variables " + Term.frees(e.r()));
        if (!Type.tyvars(v.t()).containsAll(Term.tyvars(e.r())))
            throw new HolException("newBasicDef: type variables of " + e.r() + " do not all occur in the type of " + v);
        Sig.newConst(v.n(), v.t());
        return new Thm(List.of(), Term.mkEq(new Term.Const(v.n(), v.t()), e.r()));
    }
}
