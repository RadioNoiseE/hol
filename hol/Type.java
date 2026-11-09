package hol;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public sealed interface Type permits Type.Var, Type.App {
    record Var(String n) implements Type {
        @Override
        public String toString() {
            return Type.show(this);
        }
    }

    record App(String o, List<Type> a) implements Type {
        public App {
            a = List.copyOf(a);
        }

        @Override
        public String toString() {
            return Type.show(this);
        }
    }

    Type BOOL = new App("bool", List.of());

    static Var var(String n) {
        return new Var(n);
    }

    static Type fun(Type d, Type r) {
        return new App("fun", List.of(d, r));
    }

    static boolean isFun(Type t) {
        return t instanceof App(String o, List<Type> a) && o.equals("fun") && a.size() == 2;
    }

    static Type domain(Type t) {
        if (t instanceof App(String o, List<Type> a) && o.equals("fun") && a.size() == 2)
            return a.get(0);
        throw new HolException("domain: not a function type: " + t);
    }

    static Type range(Type t) {
        if (t instanceof App(String o, List<Type> a) && o.equals("fun") && a.size() == 2)
            return a.get(1);
        throw new HolException("range: not a function type: " + t);
    }

    static Type subst(Map<Var, Type> theta, Type t) {
        return switch (t) {
            case Var v -> theta.getOrDefault(v, v);
            case App(String o, List<Type> as) -> {
                List<Type> l = new ArrayList<>();
                for (Type a : as)
                    l.add(subst(theta, a));
                yield new App(o, l);
            }
        };
    }

    static Map<Var, Type> match(Type p, Type t) {
        return match(p, t, new HashMap<>());
    }

    private static Map<Var, Type> match(Type p, Type t, Map<Var, Type> theta) {
        switch (p) {
            case Var v -> {
                Type u = theta.get(v);
                if (u != null && !u.equals(t))
                    throw new HolException("match: " + v + " cannot be both " + u + " and " + t);
                theta.put(v, t);
                return theta;
            }
            case App(String o, List<Type> as) -> {
                if (!(t instanceof App(String o2, List<Type> bs)) || !o.equals(o2) || as.size() != bs.size())
                    throw new HolException("match: " + p + " does not match " + t);
                for (int i = 0; i < as.size(); i++)
                    match(as.get(i), bs.get(i), theta);
                return theta;
            }
        }
    }

    static String show(Type t) {
        StringBuilder sb = new StringBuilder();
        show(t, false, sb);
        return sb.toString();
    }

    private static void show(Type t, boolean left, StringBuilder sb) {
        switch (t) {
            case Var v -> sb.append('\'').append(v.n());
            case App(String _, List<Type> a) when isFun(t) -> {
                if (left)
                    sb.append('(');
                show(a.get(0), true, sb);
                sb.append(" -> ");
                show(a.get(1), false, sb);
                if (left)
                    sb.append(')');
            }
            case App(String o, List<Type> a) -> {
                if (!a.isEmpty()) {
                    sb.append('(');
                    for (int i = 0; i < a.size(); i++) {
                        if (i > 0)
                            sb.append(", ");
                        show(a.get(i), false, sb);
                    }
                    sb.append(')');
                }
                sb.append(o);
            }
        }
    }
}
