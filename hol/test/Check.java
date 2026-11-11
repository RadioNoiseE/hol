package hol.test;

import hol.kernel.*;
import java.util.Objects;

public final class Check {
    private static final String LINE = "%-6s%s%n";
    private static final String DETAIL = "%6s%-10s%s%n";

    private static int passed = 0;
    private static int failed = 0;

    private Check() {
        // cannot be instantiated from outside
    }

    public record Detail(String label, Object value) {
    }

    public static Detail detail(String label, Object value) {
        return new Detail(label, value);
    }

    public static void section(String name, Runnable checks) {
        System.out.println();
        System.out.printf(LINE, "****", name);
        checks.run();
    }

    public static void pass(String name) {
        passed++;
        System.out.printf(LINE, "PASS", name);
    }

    public static void fail(String name, Detail... ds) {
        failed++;
        System.out.printf(LINE, "FAIL", name);
        for (Detail d : ds)
            System.out.printf(DETAIL, "", d.label() + ":", d.value());
    }

    public static void checkHold(String name, boolean condition) {
        if (condition)
            pass(name);
        else
            fail(name);
    }

    public static void checkEqual(String name, Object expected, Object actual) {
        if (Objects.equals(expected, actual))
            pass(name);
        else
            fail(name, detail("expected", expected), detail("actual", actual));
    }

    public static void checkThrow(String name, Runnable action) {
        try {
            action.run();
            fail(name, detail("expected", "HolException"), detail("actual", "no exception"));
        } catch (HolException e) {
            pass(name);
        } catch (RuntimeException e) {
            fail(name, detail("expected", "HolException"), detail("actual", e));
        }
    }

    public static void report() {
        System.out.println();
        System.out.printf(LINE, "", passed + " passed, " + failed + " failed");
        if (failed > 0)
            System.exit(1);
    }
}
