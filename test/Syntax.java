import hol.kernel.*;
import hol.lib.*;
import hol.syntax.*;
import java.util.List;

final class Syntax extends Test {
    static void run() {
        same(List.of("!", "x", "y", ".", "x", "=", "y"),
                Lexer.lex("!x y. x = y").stream().map(Lexer.Token::s).toList());
        same(List.of("x'", "=", "x''"), Lexer.lex("x' = x''").stream().map(Lexer.Token::s).toList());
        same(List.of("(", "x", ":", "'a", ")"), Lexer.lex("(x:'a)").stream().map(Lexer.Token::s).toList());
        same(List.of("~", "~", "p"), Lexer.lex("~ ~p").stream().map(Lexer.Token::s).toList());
        same(List.of("~~", "p"), Lexer.lex("~~p").stream().map(Lexer.Token::s).toList());
        same(List.of("p", "/\\", "q"), Lexer.lex("p   /\\q").stream().map(Lexer.Token::s).toList());
        same(List.of(), Lexer.lex(" \t\n"));
        same(5, Lexer.lex("p /\\ q").get(2).i());
        fail(() -> Lexer.lex("p £ q"));

        same(Notation.Order.TIGHTER, Notation.compare("=", "==>"));
        same(Notation.Order.LOOSER, Notation.compare("==>", "/\\"));
        same(Notation.Order.SAME, Notation.compare("/\\", "/\\"));
        fail(() -> Notation.tighter("==>", "="));
        fail(() -> Notation.tighter("/\\", "~"));
        fail(() -> Notation.infix("~", Notation.Assoc.LEFT));

        same("((/\\ p) ((/\\ q) r))", Parser.parse("p /\\ q /\\ r").toString());
        same("((/\\ ((/\\ p) q)) r)", Parser.parse("(p /\\ q) /\\ r").toString());
        same("((==> ((/\\ p) q)) ((\\/ p) q))", Parser.parse("p /\\ q ==> p \\/ q").toString());
        same("((/\\ ((= x) y)) p)", Parser.parse("x = y /\\ p").toString());
        same("((/\\ (~ p)) q)", Parser.parse("~p /\\ q").toString());
        same("(~ (f x))", Parser.parse("~f x").toString());
        same("((f x) y)", Parser.parse("f x y").toString());
        same("(f (g x))", Parser.parse("f (g x)").toString());
        same("(! (\\x. (! (\\y. ((= x) y)))))", Parser.parse("!x y. x = y").toString());
        same("((/\\ p) (! (\\x. ((/\\ q) r))))", Parser.parse("p /\\ !x. q /\\ r").toString());
        same("(\\(x : 'a). y)", Parser.parse("\\(x:'a). y").toString());
        same("((\\x. y) : ('a, 'b)fun)", Parser.parse("(\\x. y : 'a -> 'b)").toString());
        same("((/\\ p) q)", Parser.parse("(/\\) p q").toString());
        fail(() -> Parser.parse("x = y = z"));
        fail(() -> Parser.parse("(p"));
        fail(() -> Parser.parse("p q)"));
        fail(() -> Parser.parse("p /\\"));
        fail(() -> Parser.parse("!x y x = y"));
        fail(() -> Parser.parse("\\x:'a. y"));
        fail(() -> Parser.parse("\\x. y : 'a"));
        fail(() -> Parser.parse(""));

        same(Type.fun(A, Type.fun(B, A)), Parser.parseType("'a -> 'b -> 'a"));
        same(Type.fun(Type.fun(A, B), A), Parser.parseType("('a -> 'b) -> 'a"));
        same(new Type.App("list", List.of(BOOL)), Parser.parseType("bool list"));
        same(new Type.App("list", List.of(new Type.App("list", List.of(A)))), Parser.parseType("'a list list"));
        same(new Type.App("prod", List.of(A, BOOL)), Parser.parseType("('a, bool)prod"));
        same(Type.fun(new Type.App("list", List.of(A)), BOOL), Parser.parseType("'a list -> bool"));
        fail(() -> Parser.parseType("(bool, bool)"));
        fail(() -> Parser.parseType("'a ->"));
        fail(() -> Parser.parseType("bool list list list bool"));

        same(new Term.Abs(X, new Term.Var("y", B)), term("\\x. y"));
        same(new Term.Abs(new Term.Var("x", B), Y), term("\\x. (y:'a)"));
        same(new Term.Abs(new Term.Var("x", B), new Term.Var("x", B)), term("\\(x:'b). x"));
        same(List.of(new Term.Var("p", BOOL), new Term.Var("q", BOOL)), List.copyOf(Term.frees(term("p /\\ q ==> q"))));
        same(List.of(new Term.Var("f", Type.fun(BOOL, A)), new Term.Var("x", BOOL)),
                List.copyOf(Term.frees(term("f x = f T"))));
        same(List.of(new Term.Var("f", Type.fun(A, A)), X), List.copyOf(Term.frees(term("f (f x)"))));
        same(new Term.Const("c", A), term("c"));
        same(new Term.Const("c", BOOL), ((Term.Comb) term("~c")).x());
        same(new Term.Abs(new Term.Var("T", A), new Term.Var("T", A)), term("\\T. T"));
        fail(() -> term("x x"));
        fail(() -> term("(x:bool) = (y:'a)"));
        fail(() -> term("~(x:'a)"));

        same("p /\\ q /\\ r", Printer.show(term("p /\\ (q /\\ r)")));
        same("(p /\\ q) /\\ r", Printer.show(term("(p /\\ q) /\\ r")));
        same("p /\\ q ==> p \\/ q", Printer.show(term("(p /\\ q) ==> (p \\/ q)")));
        same("p ==> q ==> r", Printer.show(term("p ==> (q ==> r)")));
        same("(p ==> q) ==> r", Printer.show(term("(p ==> q) ==> r")));
        same("x = y /\\ p", Printer.show(term("(x = y) /\\ p")));
        same("(p = q) = r", Printer.show(term("(p = q) = r")));
        same("~p /\\ q", Printer.show(term("(~p) /\\ q")));
        same("~(p /\\ q)", Printer.show(term("~(p /\\ q)")));
        same("~ ~p", Printer.show(term("~(~p)")));
        same("~f x", Printer.show(term("~(f x)")));
        same("f (g x)", Printer.show(term("f (g x)")));
        same("f (~p)", Printer.show(term("f (~p)")));
        same("!x y. x = y", Printer.show(term("!x. !y. x = y")));
        same("(!p. p) /\\ q", Printer.show(term("(!p. p) /\\ q")));
        same("p /\\ (!x. q)", Printer.show(term("p /\\ (!x. q)")));
        same("\\x y. f x", Printer.show(term("\\x. \\y. f x")));
        same("(\\x. x) y", Printer.show(term("(\\x. x) y")));
        same("(/\\) p", Printer.show(term("(/\\) p")));
        same("|- x = x", Printer.show(Thm.refl(term("x"))));
        same("x = y, y = z |- x = z", Printer.show(Thm.trans(Thm.assume(prop("x = y")), Thm.assume(prop("y = z")))));

        same(true, Term.aconv(Bool.FORALL_DEF.concl(), prop(Printer.show(Bool.FORALL_DEF.concl()))));
        same(true, Term.aconv(Bool.EXISTS_DEF.concl(), prop(Printer.show(Bool.EXISTS_DEF.concl()))));
        same(true, Term.aconv(Bool.IMP_DEF.concl(), prop(Printer.show(Bool.IMP_DEF.concl()))));
        same(true, Term.aconv(Bool.OR_DEF.concl(), prop(Printer.show(Bool.OR_DEF.concl()))));
        same(true, Term.aconv(Bool.NOT_DEF.concl(), prop(Printer.show(Bool.NOT_DEF.concl()))));
        same(true, Term.aconv(Classical.ETA_AX.concl(), prop(Printer.show(Classical.ETA_AX.concl()))));
        same(true, Term.aconv(Classical.SELECT_AX.concl(), prop(Printer.show(Classical.SELECT_AX.concl()))));
        same(true,
                Term.aconv(Classical.EXCLUDED_MIDDLE.concl(), prop(Printer.show(Classical.EXCLUDED_MIDDLE.concl()))));
    }
}
