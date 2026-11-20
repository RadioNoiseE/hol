import hol.kernel.*;
import hol.lib.*;
import hol.syntax.*;

class Test {
    static {
        Classical.EXCLUDED_MIDDLE.hashCode(); // load the theories

        Sig.newType("list", 1);
        Sig.newType("prod", 2);
        Sig.newType("trip", 3);

        Sig.newConst("c", Type.var("a"));
    }

    static final Type.Var A = Type.var("a");
    static final Type.Var B = Type.var("b");
    static final Type BOOL = Type.BOOL;

    static Type type(String s) {
        return Parser.parseType(s);
    }

    static Term term(String s) {
        return Infer.term(Parser.parse(s));
    }

    static Term prop(String s) {
        return term("(" + s + " : bool)");
    }

    static void same(Object o1, Object o2) {
        if (!o1.equals(o2))
            throw new AssertionError("expected: " + o1 + ", got " + o2);
    }

    static void fail(Runnable a) {
        try {
            a.run();
        } catch (HolException e) {
            return;
        }
        throw new AssertionError("expected a hol exception");
    }

    static void hold(Thm t, String c, String... hs) {
        if (!Term.aconv(t.concl(), prop(c)) || t.hyps().size() != hs.length)
            throw new AssertionError("expected " + String.join(", ", hs) + " |- " + c + ", got " + Printer.show(t));
        for (String h : hs)
            if (t.hyps().stream().noneMatch(u -> Term.aconv(u, prop(h))))
                throw new AssertionError("missing hypothesis " + h + " in " + Printer.show(t));
    }
}
