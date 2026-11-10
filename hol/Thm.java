package hol;

import java.util.ArrayList;
import java.util.List;

public final class Thm {
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
}
