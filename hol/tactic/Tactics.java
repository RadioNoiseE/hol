package hol.tactic;

import hol.kernel.*;
import hol.lib.*;
import hol.syntax.*;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
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

    public static final Tactic NO_TAC = g -> {
        throw new HolException("NO_TAC");
    };

    public static final Tactic ALL_TAC = g -> new Tactic.State(List.of(g), ts -> ts.get(0));

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

    public static final Tactic CONJ_TAC = g -> {
        Bool.Conj c = Bool.destConj(g.c());
        return new Tactic.State(List.of(new Goal(g.as(), c.l()), new Goal(g.as(), c.r())),
                ts -> Bool.conj(ts.get(0), ts.get(1)));
    };

    public static Function<Thm, Tactic> conjunctsThen(Function<Thm, Tactic> f) {
        return t -> f.apply(Bool.conjunct1(t)).then(f.apply(Bool.conjunct2(t)));
    }

    public static final Tactic DISCH_TAC = g -> {
        Bool.Imp i = Bool.destImp(g.c());
        List<Thm> as = new ArrayList<>(g.as());
        as.add(0, Thm.assume(i.l()));
        return new Tactic.State(List.of(new Goal(as, i.r())), ts -> Bool.disch(i.l(), ts.get(0)));
    };

    public static Tactic dischThen(Function<Thm, Tactic> f) {
        return g -> {
            Bool.Imp i = Bool.destImp(g.c());
            Tactic.State s = f.apply(Thm.assume(i.l())).apply(new Goal(g.as(), i.r()));
            return new Tactic.State(s.gs(), ts -> Bool.disch(i.l(), s.j().apply(ts)));
        };
    }

    public static final Tactic GEN_TAC = g -> {
        Bool.Forall f = Bool.destForall(g.c());
        Set<Term.Var> fs = new HashSet<>(Term.frees(g.c()));
        for (Thm a : g.as()) {
            for (Term h : a.hyps())
                fs.addAll(Term.frees(h));
            fs.addAll(Term.frees(a.concl()));
        }
        Term.Var v = Term.variant(fs, f.v());
        return new Tactic.State(List.of(new Goal(g.as(), Term.vsubst(Map.of(f.v(), v), f.b()))),
                ts -> Bool.gen(v, ts.get(0)));
    };

    public static Tactic existsTac(Term t) {
        return g -> {
            Bool.Exists e = Bool.destExists(g.c());
            return new Tactic.State(List.of(new Goal(g.as(), Term.vsubst(Map.of(e.v(), t), e.b()))),
                    ts -> Bool.exists(g.c(), t, ts.get(0)));
        };
    }

    public static final Tactic DISJ1_TAC = g -> {
        Bool.Disj d = Bool.destDisj(g.c());
        return new Tactic.State(List.of(new Goal(g.as(), d.l())), ts -> Bool.disj1(ts.get(0), d.r()));
    };

    public static final Tactic DISJ2_TAC = g -> {
        Bool.Disj d = Bool.destDisj(g.c());
        return new Tactic.State(List.of(new Goal(g.as(), d.r())), ts -> Bool.disj2(d.l(), ts.get(0)));
    };

    public static final Tactic EQ_TAC = g -> {
        Term.Eq e = Term.destEq(g.c());
        Term t1 = Bool.mkImp(e.l(), e.r());
        Term t2 = Bool.mkImp(e.r(), e.l());
        return new Tactic.State(List.of(new Goal(g.as(), t1), new Goal(g.as(), t2)),
                ts -> Bool.impAntisymRule(ts.get(0), ts.get(1)));
    };

    public static Tactic assumeTac(Thm t) {
        return g -> {
            List<Thm> as = new ArrayList<>(g.as());
            as.add(0, t);
            return new Tactic.State(List.of(new Goal(as, g.c())), ts -> Bool.proveHyp(t, ts.get(0)));
        };
    }

    public static Tactic mpTac(Thm t) {
        return g -> {
            Term m = Bool.mkImp(t.concl(), g.c());
            return new Tactic.State(List.of(new Goal(g.as(), m)), ts -> Bool.mp(ts.get(0), t));
        };
    }

    public static Tactic disjCasesTac(Thm t) {
        return g -> {
            Bool.Disj d = Bool.destDisj(t.concl());
            List<Thm> as1 = new ArrayList<>(g.as());
            List<Thm> as2 = new ArrayList<>(g.as());
            as1.add(0, Thm.assume(d.l()));
            as2.add(0, Thm.assume(d.r()));
            return new Tactic.State(List.of(new Goal(as1, g.c()), new Goal(as2, g.c())),
                    ts -> Bool.disjCases(t, ts.get(0), ts.get(1)));
        };
    }

    public static Function<Thm, Tactic> chooseThen(Function<Thm, Tactic> f) {
        return t -> g -> {
            Bool.Exists e = Bool.destExists(t.concl());
            Set<Term.Var> fs = new HashSet<>(Term.frees(g.c()));
            for (Thm a : g.as()) {
                for (Term h : a.hyps())
                    fs.addAll(Term.frees(h));
                fs.addAll(Term.frees(a.concl()));
            }
            for (Term m : t.hyps())
                fs.addAll(Term.frees(m));
            fs.addAll(Term.frees(t.concl()));
            Term.Var v = Term.variant(fs, e.v());
            Tactic.State s = f.apply(Thm.assume(Term.vsubst(Map.of(e.v(), v), e.b()))).apply(g);
            return new Tactic.State(s.gs(), ts -> Bool.choose(v, t, s.j().apply(ts)));
        };
    }

    public static Tactic chooseTac(Thm t) {
        return chooseThen(Tactics::assumeTac).apply(t);
    }

    public static Function<Thm, Tactic> disjCasesThen(Function<Thm, Tactic> f) {
        return t -> g -> {
            Bool.Disj d = Bool.destDisj(t.concl());
            Tactic.State s1 = f.apply(Thm.assume(d.l())).apply(g);
            Tactic.State s2 = f.apply(Thm.assume(d.r())).apply(g);
            List<Goal> gs = new ArrayList<>(s1.gs());
            gs.addAll(s2.gs());
            int k = s1.gs().size();
            return new Tactic.State(gs, ts -> Bool.disjCases(t, s1.j().apply(ts.subList(0, k)),
                    s2.j().apply(ts.subList(k, ts.size()))));
        };
    }

    public static Tactic stripAssumeTac(Thm t) {
        Term c = t.concl();
        if (Bool.isConj(c))
            return conjunctsThen(Tactics::stripAssumeTac).apply(t);
        if (Bool.isExists(c))
            return chooseThen(Tactics::stripAssumeTac).apply(t);
        if (Bool.isDisj(c))
            return disjCasesThen(Tactics::stripAssumeTac).apply(t);
        return assumeTac(t);
    }

    public static final Tactic STRIP_TAC = GEN_TAC.orElse(CONJ_TAC).orElse(dischThen(Tactics::stripAssumeTac));
}
