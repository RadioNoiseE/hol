package hol.syntax;

import hol.kernel.HolException;
import hol.kernel.Type;
import java.util.ArrayList;
import java.util.List;

public final class Parser {
    private final List<Lexer.Token> ts;
    private int i = 0;

    private Parser(List<Lexer.Token> ts) {
        this.ts = ts;
    }

    public static Preterm parse(String s) {
        Parser p = new Parser(Lexer.lex(s));
        Preterm t = p.term();
        p.end();
        return t;
    }

    public static Type parseType(String s) {
        Parser p = new Parser(Lexer.lex(s));
        Type y = p.type();
        p.end();
        return y;
    }

    // term := infix
    private Preterm term() {
        return infix(null);
    }

    // type := btype ['->' type]
    private Type type() {
        Type y = btype();
        if (at("->")) {
            i++;
            return Type.fun(y, type());
        }
        return y;
    }

    private void end() {
        if (i < ts.size())
            throw error("unexpected " + peek());
    }

    // infix := operand (INFIX operand)*
    private Preterm infix(String op) {
        Preterm l = operand();
        while (peek() != null && Notation.isInfix(peek())) {
            String o = peek();
            if (op != null) {
                switch (Notation.compare(o, op)) {
                    case TIGHTER -> {
                        // o belongs to this operand
                    }
                    case LOOSER -> {
                        // o belongs to the caller
                        return l;
                    }
                    case UNRELATED -> throw error(o + " and " + op + " are unrelated: add parentheses");
                    case SAME -> {
                        switch (Notation.assoc(o)) {
                            case RIGHT -> {
                                // o belongs to this operand
                            }
                            case LEFT -> {
                                // o belongs to the caller
                                return l;
                            }
                            case NONE -> throw error(o + " is not associative: add parentheses");
                        }
                    }
                }
            }
            i++;
            Preterm r = infix(o);
            l = new Preterm.Comb(new Preterm.Comb(new Preterm.Var(o), l), r);
        }
        return l;
    }

    // operand := PREFIX operand | BINDER variable+ '.' term | atom+
    private Preterm operand() {
        String s = peek();
        if (s != null && Notation.isPrefix(s)) {
            i++;
            return new Preterm.Comb(new Preterm.Var(s), operand());
        }
        if (s != null && Notation.isBinder(s)) {
            i++;
            return binder(s);
        }
        Preterm t = atom();
        while (startsAtom())
            t = new Preterm.Comb(t, atom());
        return t;
    }

    // binder := BINDER variable+ '.' term
    private Preterm binder(String b) {
        List<Preterm> vs = new ArrayList<>();
        do
            vs.add(variable());
        while (!at("."));
        i++;
        Preterm t = term();
        for (int j = vs.size() - 1; j >= 0; j--) {
            Preterm a = new Preterm.Abs(vs.get(j), t);
            t = b.equals("\\") ? a : new Preterm.Comb(new Preterm.Var(b), a);
        }
        return t;
    }

    // variable := NAME | '(' NAME ':' type ')'
    private Preterm variable() {
        if (at("(")) {
            i++;
            String n = name();
            expect(":");
            Type y = type();
            expect(")");
            return new Preterm.Typed(new Preterm.Var(n), y);
        }
        return new Preterm.Var(name());
    }

    // atom := NAME | '(' SPECIAL ')' | '(' term ')' | '(' term ':' type ')'
    private Preterm atom() {
        if (at("(")) {
            i++;
            if (Notation.isSpecial(peek()) && ")".equals(peek(1))) {
                String s = next();
                expect(")");
                return new Preterm.Var(s);
            }
            Preterm t = term();
            if (at(":")) {
                i++;
                t = new Preterm.Typed(t, type());
            }
            expect(")");
            return t;
        }
        return new Preterm.Var(name());
    }

    private boolean startsAtom() {
        String s = peek();
        return s != null && (s.equals("(") || isName(s));
    }

    // btype := atypes NAME*
    private Type btype() {
        List<Type> as = atypes();
        Type y = as.size() == 1 ? as.get(0) : null;
        while (peek() != null && isName(peek()) && !peek().startsWith("'"))
            y = new Type.App(next(), y == null ? as : List.of(y));
        if (y == null)
            throw error("expected a type operator after a tuple of types");
        return y;
    }

    // atypes := TYVAR | NAME | '(' type (',' type)* ')'
    private List<Type> atypes() {
        if (at("(")) {
            i++;
            List<Type> as = new ArrayList<>();
            as.add(type());
            while (at(",")) {
                i++;
                as.add(type());
            }
            expect(")");
            return as;
        }
        String n = name();
        if (n.startsWith("'"))
            return List.of(Type.var(n.substring(1)));
        return List.of(new Type.App(n, List.of()));
    }

    private String name() {
        String s = peek();
        if (s == null || !isName(s))
            throw error("expected a name");
        i++;
        return s;
    }

    private static boolean isName(String s) {
        char c = s.charAt(0);
        return !Notation.isSpecial(s) && (Character.isLetterOrDigit(c) || c == '\'' || c == '_');
    }

    private String peek() {
        return peek(0);
    }

    private String peek(int k) {
        return i + k < ts.size() ? ts.get(i + k).s() : null;
    }

    private boolean at(String s) {
        return s.equals(peek());
    }

    private String next() {
        if (i >= ts.size())
            throw error("unexpected end of input");
        return ts.get(i++).s();
    }

    private void expect(String s) {
        if (!at(s))
            throw error("expected " + s);
        i++;
    }

    private HolException error(String m) {
        if (i < ts.size())
            return new HolException("parse: " + m + " at " + ts.get(i).i());
        return new HolException("parse: " + m + " at end of input");
    }
}
