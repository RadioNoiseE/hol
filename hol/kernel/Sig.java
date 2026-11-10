package hol.kernel;

import java.util.HashMap;
import java.util.Map;

public final class Sig {
    private static final Map<String, Type> consts = new HashMap<>();

    static {
        Type a = Type.var("a");
        consts.put("=", Type.fun(a, Type.fun(a, Type.BOOL)));
    }

    private Sig() {
        // this cannot be instantiated
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
}
