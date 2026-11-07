package hol;

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

    // REFL: |- t = t
    public static Thm refl(Term t) {
        return new Thm(List.of(), Term.mkEq(t, t));
    }

    // ASSUME: t : bool |- t
    public static Thm assume(Term t) {
        if (!Term.typeOf(t).equals(Type.BOOL))
            throw new HolException("assume: not a proposition: " + t + " : " + Term.typeOf(t));
        return new Thm(List.of(t), t);
    }
}
