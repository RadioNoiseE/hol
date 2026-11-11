package hol.test;

import hol.kernel.*;
import java.util.Map;
import java.util.Random;

final class Gen {
    private static final Type A = Type.var("a");
    private static final Type B = Type.var("b");
    private static final String[] NAMES = { "x", "y", "z" };

    private final Random r;

    Gen(long seed) {
        r = new Random(seed);
    }

    boolean coin() {
        return r.nextBoolean();
    }

    Type type(int d) {
        if (d == 0 || r.nextInt(3) > 0)
            return switch (r.nextInt(3)) {
                case 0 -> A;
                case 1 -> B;
                default -> Type.BOOL;
            };
        return Type.fun(type(d - 1), type(d - 1));
    }

    Term.Var var(Type t) {
        return new Term.Var(NAMES[r.nextInt(NAMES.length)], t);
    }

    Term term(Type t, int d) {
        int k = r.nextInt(10);
        if (d == 0 || k < 2)
            return var(t);
        if (k < 5 && Type.isFun(t))
            return new Term.Abs(var(Type.domain(t)), term(Type.range(t), d - 1));
        if (k < 7 && t.equals(Type.BOOL)) {
            Type s = type(1);
            return Term.mkEq(term(s, d - 1), term(s, d - 1));
        }
        Type s = type(1);
        return new Term.Comb(term(Type.fun(s, t), d - 1), term(s, d - 1));
    }

    Term term() {
        return term(type(2), 4);
    }

    // rename every bound variable, avoiding capture: the result is
    // alpha-equivalent
    Term rename(Term t) {
        return switch (t) {
            case Term.Var v -> v;
            case Term.Const c -> c;
            case Term.Comb(Term f, Term x) -> new Term.Comb(rename(f), rename(x));
            case Term.Abs(Term.Var v, Term b) -> {
                Term c = rename(b);
                Term.Var w = Term.variant(Term.frees(c), var(v.t()));
                yield new Term.Abs(w, Term.vsubst(Map.of(v, w), c));
            }
        };
    }

    // replace one variable occurrence, chosen at random, by a
    // variable of the same type (possibly with another name): the
    // result may or may not be alpha-equivalent
    Term mutate(Term t) {
        return switch (t) {
            case Term.Var v -> var(v.t());
            case Term.Const c -> c;
            case Term.Comb(Term f, Term x) -> {
                if (coin())
                    yield new Term.Comb(mutate(f), x);
                else
                    yield new Term.Comb(f, mutate(x));
            }
            case Term.Abs(Term.Var v, Term b) -> new Term.Abs(v, mutate(b));
        };
    }
}
