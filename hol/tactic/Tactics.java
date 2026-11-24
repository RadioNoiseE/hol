package hol.tactic;

import hol.kernel.*;
import hol.lib.*;
import hol.syntax.*;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;

public final class Tactics {
    private Tactics() {
        // cannot be instantiated
    }

    public static Thm prove(Term t, Tactic c) {
        Tactic.State s = c.apply(new Goal(List.of(), t));
        if (!s.gs().isEmpty())
            throw new HolException("prove: " + s.gs().size() + " goals left");
        Thm m = s.j().apply(List.of());
        if (m.hyps().isEmpty() && Term.aconv(m.concl(), t))
            return Thm.eqMp(Thm.refl(t), m);
        throw new HolException("prove: the tactic proved " + m + " instead");
    }

    public static Thm prove(String s, Tactic c) {
        return prove(Infer.term(Parser.parse("(" + s + " : bool)")), c);
    }

    public static Tactic repeat(Tactic c) {
        return g -> c.then(repeat(c)).orElse(ALL_TAC).apply(g);
    }

    public static Tactic acceptTac(Thm t) {
        return g -> {
            if (Term.aconv(t.concl(), g.c()))
                return new Tactic.State(List.of(), ts -> t);
            throw new HolException("acceptTac: " + t + " does not prove " + g.c());
        };
    }

    public static Tactic firstAssum(Function<Thm, Tactic> f) {
        return g -> {
            for (Thm a : g.as())
                try {
                    return f.apply(a).apply(g);
                } catch (HolException _) {
                    // try the next assumption
                }
            throw new HolException("firstAssum: no assumption works");
        };
    }

    public static final Tactic ALL_TAC = g -> new Tactic.State(List.of(g), ts -> ts.get(0));

    public static final Tactic NO_TAC = g -> {
        throw new HolException("NO_TAC");
    };

    public static final Tactic CONJ_TAC = g -> {
        Bool.Conj c = Bool.destConj(g.c());
        return new Tactic.State(List.of(new Goal(g.as(), c.l()), new Goal(g.as(), c.r())),
                ts -> Bool.conj(ts.get(0), ts.get(1)));
    };

    public static final Tactic DISCH_TAC = g -> {
        Bool.Imp i = Bool.destImp(g.c());
        List<Thm> as = new ArrayList<>(g.as());
        as.add(0, Thm.assume(i.l()));
        return new Tactic.State(List.of(new Goal(as, i.r())), ts -> Bool.disch(i.l(), ts.get(0)));
    };
}
