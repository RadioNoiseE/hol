package hol.lib;

import hol.kernel.*;
import java.util.Map;

public final class Equal {
    private Equal() {
        // cannot be instantiated
    }

    // BETA_CONV: (\v. b) s ==> |- (\v. b) s = b[s/v]
    public static Thm betaConv(Term t) {
        if (!(t instanceof Term.Comb(Term.Abs(Term.Var v, Term b), Term x)))
            throw new HolException("betaConv: not a beta-redex: " + t);
        Term t1 = new Term.Comb(new Term.Abs(v, b), v); // (\v. b) v
        return Thm.inst(Map.of(v, x), Thm.beta(t1));
    }

    // BETA_NORM: |- t = t'
    public static Thm betaNorm(Term t) {
        return switch (t) {
            case Term.Var v -> Thm.refl(v);
            case Term.Const c -> Thm.refl(c);
            case Term.Abs(Term.Var v, Term b) -> Thm.abs(v, betaNorm(b));
            case Term.Comb(Term f, Term x) -> {
                Thm t1 = Thm.mkComb(betaNorm(f), betaNorm(x)); // |- f x = f' x'
                Term r = Term.destEq(t1.concl()).r();
                if (!(r instanceof Term.Comb(Term.Abs _, Term _)))
                    yield t1;
                Thm t2 = Thm.trans(t1, betaConv(r)); // |- f x = f'' x''
                yield Thm.trans(t2, betaNorm(Term.destEq(t2.concl()).r()));
            }
        };
    }

    // BETA_RULE: A |- t ==> A |- t'
    public static Thm betaRule(Thm t) {
        return Thm.eqMp(betaNorm(t.concl()), t);
    }

    // AP_TERM: f, A |- x = y ==> A |- f x = f y
    public static Thm apTerm(Term f, Thm t) {
        return Thm.mkComb(Thm.refl(f), t);
    }

    // AP_THM: A |- f = g, x ==> A |- f x = g x
    public static Thm apThm(Thm t, Term x) {
        return Thm.mkComb(t, Thm.refl(x));
    }

    // SYM: A |- l = r ==> A |- r = l
    public static Thm sym(Thm t) {
        if (!Term.isEq(t.concl()) || !(t.concl() instanceof Term.Comb(Term.Comb(Term e, Term l), Term _)))
            throw new HolException("sym: not an equation: " + t.concl());
        Thm t1 = apTerm(e, t); // A |- (=) l = (=) r
        Thm t2 = apThm(t1, l); // A |- (l = l) = (r = l)
        return Thm.eqMp(t2, Thm.refl(l));
    }
}
