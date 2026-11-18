package hol.syntax;

import hol.kernel.HolException;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public final class Notation {
    private Notation() {
        // cannot be instantiated
    }

    public enum Assoc {
        LEFT, RIGHT, NONE
    }

    public enum Order {
        TIGHTER, LOOSER, SAME, UNRELATED
    }

    private static final Map<String, Assoc> infixes = new HashMap<>();
    private static final Map<String, Set<String>> looser = new HashMap<>();
    private static final Set<String> binders = new HashSet<>();
    private static final Set<String> prefixes = new HashSet<>();

    static {
        infix("=", Assoc.NONE);
        infix("/\\", Assoc.RIGHT);
        infix("\\/", Assoc.RIGHT);
        infix("==>", Assoc.RIGHT);

        tighter("=", "/\\");
        tighter("/\\", "\\/");
        tighter("\\/", "==>");

        binder("\\");
        binder("!");
        binder("?");
        binder("@");

        prefix("~");
    }

    public static void infix(String n, Assoc a) {
        if (isSpecial(n))
            throw new HolException("infix: " + n + " already has a notation");
        infixes.put(n, a);
        looser.put(n, new HashSet<>());
    }

    public static void binder(String n) {
        if (isSpecial(n))
            throw new HolException("binder: " + n + " already has a notation");
        binders.add(n);
    }

    public static void prefix(String n) {
        if (isSpecial(n))
            throw new HolException("prefix: " + n + " already has a notation");
        prefixes.add(n);
    }

    public static void tighter(String n1, String n2) {
        if (!isInfix(n1) || !isInfix(n2))
            throw new HolException("tighter: " + n1 + " and " + n2 + " must both be infixes");
        if (n1.equals(n2) || reaches(n2, n1))
            throw new HolException("tighter: " + n1 + " tighter than " + n2 + " would make a cycle");
        looser.get(n1).add(n2);
    }

    public static Order compare(String n1, String n2) {
        if (n1.equals(n2))
            return Order.SAME;
        if (reaches(n1, n2))
            return Order.TIGHTER;
        if (reaches(n2, n1))
            return Order.LOOSER;
        return Order.UNRELATED;
    }

    private static boolean reaches(String n1, String n2) {
        Deque<String> todo = new ArrayDeque<>();
        Set<String> seen = new HashSet<>();
        todo.push(n1);
        while (!todo.isEmpty()) {
            String n = todo.pop();
            if (n.equals(n2))
                return true;
            if (seen.add(n))
                todo.addAll(looser.get(n));
        }
        return false;
    }

    public static Assoc assoc(String n) {
        return infixes.get(n);
    }

    public static boolean isInfix(String n) {
        return infixes.containsKey(n);
    }

    public static boolean isBinder(String n) {
        return binders.contains(n);
    }

    public static boolean isPrefix(String n) {
        return prefixes.contains(n);
    }

    public static boolean isSpecial(String n) {
        return isInfix(n) || isBinder(n) || isPrefix(n);
    }
}
