public sealed interface Term permits Term.Var, Term.Const, Term.Comb, Term.Abs {
    record Var(String name, Type type) implements Term {
        @Override
        public String toString() {
            return Term.show(this);
        }
    }

    record Const(String name, Type type) implements Term {
        @Override
        public String toString() {
            return Term.show(this);
        }
    }

    record Comb(Term fun, Term arg) implements Term {
        public Comb {
            Type funType = typeOf(fun);
            if (!Type.isFun(funType) || !Type.domain(funType).equals(typeOf(arg)))
                throw new HolException(
                        "Comb: cannot apply" + fun + " : " + funType + " to " + arg + " : " + typeOf(arg));
        }

        @Override
        public String toString() {
            return Term.show(this);
        }
    }

    record Abs(Var bvar, Term body) implements Term {
        @Override
        public String toString() {
            return Term.show(this);
        }
    }

    static Type typeOf(Term t) {
        return switch (t) {
            case Var v -> v.type();
            case Const c -> c.type();
            case Comb(Term f, Term _) -> Type.range(typeOf(f));
            case Abs(Var v, Term body) -> Type.fun(v.type(), typeOf(body));
        };
    }

    static String show(Term t) {
        StringBuilder sb = new StringBuilder();
        show(t, 0, sb);
        return sb.toString();
    }

    // precedence: 0 = anywhere, 1 = function position, 2 = argument position
    private static void show(Term t, int prec, StringBuilder sb) {
        switch (t) {
            case Var v -> sb.append(v.name());
            case Const c -> {
                if (Character.isLetter(c.name().charAt(0)))
                    sb.append(c.name());
                else
                    sb.append('(').append(c.name()).append(')');
            }
            case Comb(Term f, Term x) -> {
                if (prec > 1)
                    sb.append('(');
                show(f, 1, sb);
                sb.append(' ');
                show(x, 2, sb);
                if (prec > 1)
                    sb.append(')');
            }
            case Abs(Var v, Term body) -> {
                if (prec > 0)
                    sb.append('(');
                sb.append('\\').append(v.name()).append(':').append(v.type()).append(". ");
                show(body, 0, sb);
                if (prec > 0)
                    sb.append(')');
            }
        }
    }
}
