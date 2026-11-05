import java.util.List;

public sealed interface Type permits Type.Var, Type.App {
    record Var(String name) implements Type {
        @Override
        public String toString() {
            return Type.show(this);
        }
    }

    record App(String op, List<Type> args) implements Type {
        public App {
            args = List.copyOf(args);
        }

        @Override
        public String toString() {
            return Type.show(this);
        }
    }

    Type BOOL = new App("bool", List.of());

    static Var var(String name) {
        return new Var(name);
    }

    static Type fun(Type dom, Type ran) {
        return new App("fun", List.of(dom, ran));
    }

    static boolean isFun(Type t) {
        return t instanceof App(String op, List<Type> args) && op.equals("fun") && args.size() == 2;
    }

    static Type domain(Type t) {
        if (t instanceof App(String op, List<Type> args) && op.equals("fun") && args.size() == 2)
            return args.get(0);
        throw new HolException("domain: not a function type: " + t);
    }

    static Type range(Type t) {
        if (t instanceof App(String op, List<Type> args) && op.equals("fun") && args.size() == 2)
            return args.get(1);
        throw new HolException("domain: not a function type: " + t);
    }

    static String show(Type t) {
        StringBuilder sb = new StringBuilder();
        show(t, false, sb);
        return sb.toString();
    }

    private static void show(Type t, boolean leftOfArrow, StringBuilder sb) {
        switch (t) {
            case Var v -> sb.append('\'').append(v.name());
            case App(String _, List<Type> args) when isFun(t) -> {
                if (leftOfArrow)
                    sb.append('(');
                show(args.get(0), true, sb);
                sb.append(" -> ");
                show(args.get(1), false, sb);
                if (leftOfArrow)
                    sb.append(')');
            }
            case App(String op, List<Type> args) -> {
                if (!args.isEmpty()) {
                    sb.append('(');
                    for (int i = 0; i < args.size(); i++) {
                        if (i > 0)
                            sb.append(", ");
                        show(args.get(i), false, sb);
                    }
                    sb.append(')');
                }
                sb.append(op);
            }
        }
    }
}
