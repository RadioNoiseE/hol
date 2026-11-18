package hol.syntax;

import hol.kernel.*;
import java.util.ArrayList;
import java.util.List;

public final class Printer {
    private Printer() {
        // cannot be instantiated
    }

    private enum Pos {
        TOP, FUN, ARG, PRE, LEFT, RIGHT
    }

    public static String show(Term t) {
        StringBuilder sb = new StringBuilder();
        term(t, Pos.TOP, null, sb);
        return sb.toString();
    }

    public static String show(Thm t) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < t.hyps().size(); i++) {
            if (i > 0)
                sb.append(", ");
            term(t.hyps().get(i), Pos.TOP, null, sb);
        }
        if (!t.hyps().isEmpty())
            sb.append(' ');
        sb.append("|- ");
        term(t.concl(), Pos.TOP, null, sb);
        return sb.toString();
    }

    private static void term(Term t, Pos p, String op, StringBuilder sb) {
        switch (t) {
            case Term.Var v -> atom(v.n(), sb);
            case Term.Const c -> atom(c.n(), sb);
            case Term.Abs _ -> binder("\\", t, p, sb);
            case Term.Comb(Term f, Term x) -> {
                String prefix = head(t, 1);
                String infix = head(t, 2);
                if (prefix != null && Notation.isPrefix(prefix)) {
                    boolean paren = p == Pos.FUN || p == Pos.ARG;
                    open(paren, sb);
                    sb.append(prefix);
                    String h = head(x, 1);
                    if (h != null && Notation.isPrefix(h))
                        sb.append(' ');
                    term(x, Pos.PRE, null, sb);
                    close(paren, sb);
                } else if (prefix != null && Notation.isBinder(prefix) && x instanceof Term.Abs) {
                    binder(prefix, t, p, sb);
                } else if (infix != null && Notation.isInfix(infix)) {
                    boolean paren = !fits(infix, p, op);
                    Term l = ((Term.Comb) f).x();
                    open(paren, sb);
                    term(l, Pos.LEFT, infix, sb);
                    sb.append(' ').append(infix).append(' ');
                    term(x, Pos.RIGHT, infix, sb);
                    close(paren, sb);
                } else {
                    boolean paren = p == Pos.ARG;
                    open(paren, sb);
                    term(f, Pos.FUN, null, sb);
                    sb.append(' ');
                    term(x, Pos.ARG, null, sb);
                    close(paren, sb);
                }
            }
        }
    }

    private static void atom(String n, StringBuilder sb) {
        if (Notation.isSpecial(n))
            sb.append('(').append(n).append(')');
        else
            sb.append(n);
    }

    private static void binder(String b, Term t, Pos p, StringBuilder sb) {
        List<Term.Var> vs = new ArrayList<>();
        Term u = t;
        while (true) {
            if (b.equals("\\") && u instanceof Term.Abs(Term.Var v, Term c)) {
                vs.add(v);
                u = c;
            } else if (u instanceof Term.Comb(Term.Const c, Term.Abs(Term.Var v, Term d)) && c.n().equals(b)) {
                vs.add(v);
                u = d;
            } else
                break;
        }
        boolean paren = p != Pos.TOP;
        open(paren, sb);
        sb.append(b);
        for (int i = 0; i < vs.size(); i++)
            sb.append(i > 0 ? " " : "").append(vs.get(i).n());
        sb.append(". ");
        term(u, Pos.TOP, null, sb);
        close(paren, sb);
    }

    private static String head(Term t, int k) {
        List<Term> xs = new ArrayList<>();
        Term h = t;
        while (h instanceof Term.Comb(Term f, Term x)) {
            xs.add(x);
            h = f;
        }
        return h instanceof Term.Const c && xs.size() == k ? c.n() : null;
    }

    private static boolean fits(String i, Pos p, String op) {
        return switch (p) {
            case TOP -> true;
            case FUN, ARG, PRE -> false;
            case LEFT, RIGHT -> switch (Notation.compare(i, op)) {
                case TIGHTER -> true;
                case LOOSER, UNRELATED -> false;
                case SAME -> Notation.assoc(i) == (p == Pos.LEFT ? Notation.Assoc.LEFT : Notation.Assoc.RIGHT);
            };
        };
    }

    private static void open(boolean paren, StringBuilder sb) {
        if (paren)
            sb.append('(');
    }

    private static void close(boolean paren, StringBuilder sb) {
        if (paren)
            sb.append(')');
    }
}
