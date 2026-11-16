package hol.kernel;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

public final class Sig {
    private static final Map<String, Integer> types = new HashMap<>();
    private static final Map<String, Type> consts = new HashMap<>();

    static {
        types.put("bool", 0);
        types.put("fun", 2);

        Type a = Type.var("a");
        Type b = new Type.App("bool", List.of());
        consts.put("=", Type.fun(a, Type.fun(a, b)));
    }

    private Sig() {
        // this cannot be instantiated
    }

    public static void newType(String n, int k) {
        if (types.containsKey(n))
            throw new HolException("newType: " + n + " is already declared");
        types.put(n, k);
    }

    public static int typeArity(String n) {
        Integer k = types.get(n);
        if (k == null)
            throw new HolException("typeArity: " + n + " is not a declared type");
        return k;
    }

    public static Map<String, Integer> types() {
        return Map.copyOf(types);
    }

    public static void newConst(String n, Type t) {
        if (consts.containsKey(n))
            throw new HolException("newConst: " + n + " is already declared");
        consts.put(n, t);
    }

    public static Type constType(String n) {
        Type t = consts.get(n);
        if (t == null)
            throw new HolException("constType: " + n + " is not a declared constant");
        return t;
    }

    public static Map<String, Type> consts() {
        return Map.copyOf(consts);
    }
}
