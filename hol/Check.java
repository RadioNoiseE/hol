package hol;

import java.util.Objects;

public final class Check {
    private static int passed = 0;
    private static int failed = 0;

    private Check() {
        // cannot be instantiated from outside
    }

    public static void checkHold(String name, boolean condition) {
        if (condition) {
            passed++;
        } else {
            failed++;
            System.out.println("FAIL  " + name);
        }
    }

    public static void checkEqual(String name, Object expected, Object actual) {
        if (Objects.equals(expected, actual)) {
            passed++;
        } else {
            failed++;
            System.out.println("FAIL  " + name);
            System.out.println("      expected: " + expected);
            System.out.println("      actual: " + actual);
        }
    }

    public static void checkThrow(String name, Runnable action) {
        try {
            action.run();
            failed++;
            System.out.println("FAIL  " + name + "  (no HolException was thrown)");
        } catch (HolException e) {
            passed++;
        } catch (RuntimeException e) {
            failed++;
            System.out.println("FAIL  " + name + "  (threw " + e + " instead of HolException)");
        }
    }

    public static void report() {
        System.out.println(passed + " passed, " + failed + " failed");
        if (failed > 0)
            System.exit(1);
    }
}
