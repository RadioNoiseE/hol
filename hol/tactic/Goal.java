package hol.tactic;

import hol.kernel.*;
import java.util.List;

public record Goal(List<Thm> as, Term c) {
    // assumptions as theorems, and the conclusion to prove
    public Goal {
        as = List.copyOf(as);
    }
}
