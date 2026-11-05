import java.util.List;

public class Tests {
    static final Type A = Type.var("a");
    static final Type B = Type.var("b");
    static final Type BOOL = Type.BOOL;

    static final Term.Var X = new Term.Var("x", A);
    static final Term.Var Y = new Term.Var("y", A);
    static final Term.Var F = new Term.Var("f", Type.fun(A, A));
    static final Term.Var P = new Term.Var("p", BOOL);

    public static void main(String[] args) {
        typeTests();
        termTests();
        Check.report();
    }

    static void typeTests() {
        Check.checkEqual("print type variable", "'a", A.toString());
        Check.checkEqual("print arrow", "'a -> bool", Type.fun(A, BOOL).toString());
        Check.checkEqual("arrow is right-associative",
                "'a -> 'b -> 'a", Type.fun(A, Type.fun(B, A)).toString());
        Check.checkEqual("parenthesize arrow on the left",
                "('a -> 'b) -> 'a", Type.fun(Type.fun(A, B), A).toString());
        Check.checkEqual("print bool", "bool", Type.BOOL.toString());
        Check.checkEqual("print one-argument operator",
                "(bool)list", new Type.App("list", List.of(BOOL)).toString());
        Check.checkEqual("print two-argument operator",
                "('a, bool)prod", new Type.App("prod", List.of(A, BOOL)).toString());

        Check.checkEqual("types are compared by structure",
                Type.fun(A, BOOL), Type.fun(Type.var("a"), Type.BOOL));
        Check.checkHold("different types are not equal", !Type.fun(A, B).equals(Type.fun(B, A)));

        Check.checkEqual("domain", A, Type.domain(Type.fun(A, BOOL)));
        Check.checkEqual("range", BOOL, Type.range(Type.fun(A, BOOL)));
        Check.checkThrow("domain of bool fails", () -> Type.domain(BOOL));
        Check.checkThrow("range of a type variable fails", () -> Type.range(A));
    }

    static void termTests() {
        Term fx = new Term.Comb(F, X);
        Term idx = new Term.Abs(X, X);

        Check.checkEqual("type of a variable", A, Term.typeOf(X));
        Check.checkEqual("type of an application", A, Term.typeOf(fx));
        Check.checkEqual("type of an abstraction", Type.fun(A, A), Term.typeOf(idx));
        Check.checkEqual("type of a nested abstraction",
                Type.fun(A, Type.fun(A, A)), Term.typeOf(new Term.Abs(X, new Term.Abs(Y, X))));

        Check.checkThrow("cannot apply a non-function", () -> new Term.Comb(X, Y));
        Check.checkThrow("argument type must match", () -> new Term.Comb(F, P));

        Check.checkEqual("print application", "f (f x)", new Term.Comb(F, fx).toString());
        Check.checkEqual("print abstraction", "\\x:'a. f x", new Term.Abs(X, fx).toString());
        Check.checkEqual("print redex", "(\\x:'a. x) y", new Term.Comb(idx, Y).toString());
        Check.checkEqual("print symbolic constant", "(=)",
                new Term.Const("=", Type.fun(A, Type.fun(A, BOOL))).toString());

        Check.checkHold("same name and type: same variable", X.equals(new Term.Var("x", A)));
        Check.checkHold("same name but different type: different variable",
                !X.equals(new Term.Var("x", BOOL)));
        Check.checkHold("equals is structural but not alpha-equivalence",
                !idx.equals(new Term.Abs(Y, Y)));
    }

}
