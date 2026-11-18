package hol.syntax;

import hol.kernel.Type;

public sealed interface Preterm permits Preterm.Var, Preterm.Comb, Preterm.Abs, Preterm.Typed {
    record Var(String n) implements Preterm {
        @Override
        public String toString() {
            return n;
        }
    };

    record Comb(Preterm f, Preterm x) implements Preterm {
        @Override
        public String toString() {
            return "(" + f + " " + x + ")";
        }
    }

    record Abs(Preterm v, Preterm b) implements Preterm {
        @Override
        public String toString() {
            return "(\\" + v + ". " + b + ")";
        }
    }

    record Typed(Preterm t, Type y) implements Preterm {
        @Override
        public String toString() {
            return "(" + t + " : " + y + ")";
        }
    }
}
