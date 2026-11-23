package hol.tactic;

import hol.kernel.*;
import java.util.List;

public record Goal(List<Thm> a, Term c) {
    // assumptions as theorems, and the conclusion to prove
    public Goal {
        a = List.copyOf(a);
    }
}
