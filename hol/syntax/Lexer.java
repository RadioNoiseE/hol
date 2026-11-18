package hol.syntax;

import hol.kernel.HolException;
import java.util.ArrayList;
import java.util.List;

public final class Lexer {
    private Lexer() {
        // cannot be instantiated
    }

    private static final String SPACES = " \t\n\r";
    private static final String SEPARATORS = ",;";
    private static final String BRACKETS = "()[]{}";
    private static final String SYMBOLS = "~!@#$%^&*-+=|\\:<>.?/";
    private static final String ALPHAS = "'_abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";
    private static final String NUMBERS = "0123456789";

    public record Token(String s, int i) {
        // token's text and its position
    }

    public static List<Token> lex(String s) {
        List<Token> ts = new ArrayList<>();
        int i = 0;
        while (i < s.length()) {
            char c = s.charAt(i);
            int j = i + 1;
            if (isSpace(c)) {
                i = j;
                continue;
            }
            if (isSymbol(c))
                while (j < s.length() && isSymbol(s.charAt(j)))
                    j++;
            else if (isName(c))
                while (j < s.length() && isName(s.charAt(j)))
                    j++;
            else if (!isSeparator(c) && !isBracket(c))
                throw new HolException("lex: unexpected character " + c + " at " + i);
            ts.add(new Token(s.substring(i, j), i));
            i = j;
        }
        return List.copyOf(ts);
    }

    private static boolean isName(char c) {
        return isAlpha(c) || isNumber(c);
    }

    private static boolean isSpace(char c) {
        return SPACES.indexOf(c) >= 0;
    }

    private static boolean isSeparator(char c) {
        return SEPARATORS.indexOf(c) >= 0;
    }

    private static boolean isBracket(char c) {
        return BRACKETS.indexOf(c) >= 0;
    }

    private static boolean isSymbol(char c) {
        return SYMBOLS.indexOf(c) >= 0;
    }

    private static boolean isAlpha(char c) {
        return ALPHAS.indexOf(c) >= 0;
    }

    private static boolean isNumber(char c) {
        return NUMBERS.indexOf(c) >= 0;
    }
}
