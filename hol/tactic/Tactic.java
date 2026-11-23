package hol.tactic;

import hol.kernel.*;
import java.util.ArrayList;
import java.util.List;

@FunctionalInterface
public interface Tactic {
    State apply(Goal g);

    record State(List<Goal> gs, Justification j) {
        public State {
            gs = List.copyOf(gs);
        }
    }

    @FunctionalInterface
    interface Justification {
        Thm apply(List<Thm> ts);
    }

    default Tactic then(Tactic t) {
        return g -> {
            State s = apply(g);
            List<State> us = new ArrayList<>();
            List<Goal> gs = new ArrayList<>();
            for (Goal h : s.gs()) {
                State u = t.apply(h);
                us.add(u);
                gs.addAll(u.gs());
            }
            return new State(gs, ts -> {
                List<Thm> rs = new ArrayList<>();
                int i = 0;
                for (State u : us) {
                    int k = u.gs().size();
                    rs.add(u.j().apply(ts.subList(i, i + k)));
                    i += k;
                }
                return s.j().apply(rs);
            });
        };
    }

    default Tactic orElse(Tactic t) {
        return g -> {
            try {
                return apply(g);
            } catch (HolException _) {
                return t.apply(g);
            }
        };
    }
}
