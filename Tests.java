import java.util.List;
import java.util.Map;
import java.util.Set;

public class Tests {
    static final Type.Var A = Type.var("a");
    static final Type.Var B = Type.var("b");

    static final Type BOOL = Type.BOOL;

    static final Term.Var X = new Term.Var("x", A);
    static final Term.Var Y = new Term.Var("y", A);
    static final Term.Var F = new Term.Var("f", Type.fun(A, A));
    static final Term.Var P = new Term.Var("p", BOOL);

    public static void main(String[] args) {
        typeTests();
        termTests();
        freeTests();
        substTests();
        aconvTests();
        variantTests();
        vsubstTests();
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

    static void freeTests() {
        Term.Var g = new Term.Var("g", Type.fun(A, Type.fun(A, A)));
        Term.Var x = new Term.Var("x", BOOL);
        Term.Const c = new Term.Const("c", A);
        Term t = new Term.Abs(X, new Term.Comb(new Term.Comb(g, X), Y));

        Check.checkEqual("a variable is free in itself", Set.of(X), Term.frees(X));
        Check.checkEqual("a constant has no free variables", Set.of(), Term.frees(c));
        Check.checkEqual("application: union of both sides",
                Set.of(F, X), Term.frees(new Term.Comb(F, X)));
        Check.checkEqual("abstraction binds its variable",
                Set.of(), Term.frees(new Term.Abs(X, X)));
        Check.checkEqual("abstraction only binds its own variable",
                Set.of(Y), Term.frees(new Term.Abs(X, Y)));
        Check.checkEqual("inner binder shadows outer: \\x. \\x. x is closed",
                Set.of(), Term.frees(new Term.Abs(X, new Term.Abs(X, X))));
        Check.checkEqual("bound variable with a different type does not bind",
                Set.of(X), Term.frees(new Term.Abs(x, X)));

        Check.checkEqual("free variables in order of first occurrence",
                List.of(g, Y), List.copyOf(Term.frees(t)));

        Check.checkHold("y is free in \\x. y", Term.freeIn(Y, new Term.Abs(X, Y)));
        Check.checkHold("x is not free in \\x. y", !Term.freeIn(X, new Term.Abs(X, Y)));
    }

    static void substTests() {
        Type l = new Type.App("list", List.of(A));

        Check.checkEqual("replace a variable", Type.fun(BOOL, B), Type.subst(Map.of(A, BOOL), Type.fun(A, B)));
        Check.checkEqual("variables not in the map are unchanged", Type.fun(A, B),
                Type.subst(Map.of(Type.var("c"), BOOL), Type.fun(A, B)));
        Check.checkEqual("empty substitution is the identity", l, Type.subst(Map.of(), l));
        Check.checkEqual("bool has no variables to replace",
                BOOL, Type.subst(Map.of(A, B), BOOL));
        Check.checkEqual("works inside any type operator",
                new Type.App("list", List.of(BOOL)), Type.subst(Map.of(A, BOOL), l));
        Check.checkEqual("a variable can become a compound type",
                Type.fun(Type.fun(B, B), BOOL),
                Type.subst(Map.of(A, Type.fun(B, B)), Type.fun(A, BOOL)));
        Check.checkEqual("simultaneous a and b swap",
                Type.fun(B, A), Type.subst(Map.of(A, B, B, A), Type.fun(A, B)));
        Check.checkEqual("the replacement is not substituted again",
                Type.fun(A, A), Type.subst(Map.of(A, Type.fun(A, A)), A));
    }

    static void aconvTests() {
        Term.Var z = new Term.Var("z", A);
        Term.Var x = new Term.Var("x", BOOL);
        Term.Const c = new Term.Const("c", A);

        Check.checkHold("a variable is alpha-equivalent to itself", Term.aconv(X, X));
        Check.checkHold("different free variables are not", !Term.aconv(X, Y));
        Check.checkHold("same name, different type: not equivalent", !Term.aconv(X, x));
        Check.checkHold("equal constants", Term.aconv(c, new Term.Const("c", A)));
        Check.checkHold("a variable is not a constant", !Term.aconv(X, new Term.Const("x", A)));
        Check.checkHold("applications compare both sides",
                Term.aconv(new Term.Comb(F, X), new Term.Comb(F, X)));
        Check.checkHold("applications with different arguments",
                !Term.aconv(new Term.Comb(F, X), new Term.Comb(F, Y)));

        Check.checkHold("\\x. x is \\y. y",
                Term.aconv(new Term.Abs(X, X), new Term.Abs(Y, Y)));
        Check.checkHold("\\x. f x is \\y. f y",
                Term.aconv(new Term.Abs(X, new Term.Comb(F, X)), new Term.Abs(Y, new Term.Comb(F, Y))));
        Check.checkHold("\\x. \\y. x is \\y. \\x. y",
                Term.aconv(new Term.Abs(X, new Term.Abs(Y, X)), new Term.Abs(Y, new Term.Abs(X, Y))));
        Check.checkHold("\\x. \\y. x is not \\x. \\y. y",
                !Term.aconv(new Term.Abs(X, new Term.Abs(Y, X)), new Term.Abs(X, new Term.Abs(Y, Y))));

        Check.checkHold("\\x. y is \\z. y",
                Term.aconv(new Term.Abs(X, Y), new Term.Abs(z, Y)));
        Check.checkHold("\\x. y is not \\y. y",
                !Term.aconv(new Term.Abs(X, Y), new Term.Abs(Y, Y)));
        Check.checkHold("\\y. y is not \\x. y",
                !Term.aconv(new Term.Abs(Y, Y), new Term.Abs(X, Y)));

        Check.checkHold("\\x. \\x. x is \\y. \\z. z",
                Term.aconv(new Term.Abs(X, new Term.Abs(X, X)), new Term.Abs(Y, new Term.Abs(z, z))));
        Check.checkHold("\\x. \\x. x is not \\y. \\z. y",
                !Term.aconv(new Term.Abs(X, new Term.Abs(X, X)), new Term.Abs(Y, new Term.Abs(z, Y))));
        Check.checkHold("\\x. \\y. x is not \\y. \\y. y",
                !Term.aconv(new Term.Abs(X, new Term.Abs(Y, X)), new Term.Abs(Y, new Term.Abs(Y, Y))));

        Check.checkHold("\\x:bool. x is not \\x:'a. x",
                !Term.aconv(new Term.Abs(x, x), new Term.Abs(X, X)));

        Check.checkHold("an abstraction is not an application",
                !Term.aconv(new Term.Abs(X, X), new Term.Comb(F, X)));
    }

    static void variantTests() {
        Term.Var x1 = new Term.Var("x'", A);

        Check.checkEqual("no clash: name unchanged", X, Term.variant(Set.of(Y), X));
        Check.checkEqual("clash: add a prime", x1, Term.variant(Set.of(X), X));
        Check.checkEqual("keep adding primes until free",
                new Term.Var("x''", A), Term.variant(Set.of(X, x1), X));
        Check.checkEqual("names clash even when types differ",
                x1, Term.variant(Set.of(new Term.Var("x", BOOL)), X));
    }

    static void vsubstTests() {
        Term.Var z = new Term.Var("z", A);
        Term.Var x1 = new Term.Var("x'", A);
        Term.Var g = new Term.Var("g", Type.fun(A, Type.fun(A, A)));
        Term.Const c = new Term.Const("c", A);
        Term.Const eq = new Term.Const("=", Type.fun(A, Type.fun(A, BOOL)));

        Check.checkEqual("replace a variable",
                new Term.Comb(F, Y), Term.vsubst(Map.of(X, Y), new Term.Comb(F, X)));
        Check.checkEqual("variables not in the map are unchanged",
                new Term.Comb(F, X), Term.vsubst(Map.of(Y, z), new Term.Comb(F, X)));
        Check.checkEqual("constants are unchanged", c, Term.vsubst(Map.of(X, Y), c));
        Check.checkEqual("replace by a compound term",
                new Term.Comb(F, new Term.Comb(F, Y)),
                Term.vsubst(Map.of(X, new Term.Comb(F, Y)), new Term.Comb(F, X)));
        Check.checkEqual("simultaneous: x = y becomes y = x",
                new Term.Comb(new Term.Comb(eq, Y), X),
                Term.vsubst(Map.of(X, Y, Y, X), new Term.Comb(new Term.Comb(eq, X), Y)));

        Term idX = new Term.Abs(X, X);
        Check.checkEqual("a bound variable is not replaced", idX, Term.vsubst(Map.of(X, Y), idX));
        Check.checkEqual("a free variable under a binder is replaced",
                new Term.Abs(X, z), Term.vsubst(Map.of(Y, z), new Term.Abs(X, Y)));
        Check.checkEqual("no renaming when nothing would be captured",
                new Term.Abs(X, new Term.Comb(new Term.Comb(g, X), z)),
                Term.vsubst(Map.of(Y, z), new Term.Abs(X, new Term.Comb(new Term.Comb(g, X), Y))));
        Check.checkEqual("no renaming for entries whose variable is not free in the body",
                idX, Term.vsubst(Map.of(Y, X), idX));

        Term captured = Term.vsubst(Map.of(Y, X), new Term.Abs(X, Y));
        Check.checkHold("(\\x. y)[y := x] is \\z. x up to renaming",
                Term.aconv(captured, new Term.Abs(z, X)));
        Check.checkEqual("(\\x. y)[y := x] keeps x free", Set.of(X), Term.frees(captured));

        Term body = new Term.Comb(new Term.Comb(g, Y), x1);
        Term result = Term.vsubst(Map.of(Y, X), new Term.Abs(X, body));
        Check.checkHold("renamed binder avoids the body's other free variables",
                Term.aconv(result, new Term.Abs(z, new Term.Comb(new Term.Comb(g, X), x1))));
        Check.checkEqual("free variables after renaming", Set.of(g, X, x1), Term.frees(result));

        Term nested = new Term.Abs(X, new Term.Abs(z, new Term.Comb(new Term.Comb(g, Y), z)));
        Term nestedResult = Term.vsubst(Map.of(Y, X), nested);
        Check.checkHold("capture avoided under nested binders",
                Term.aconv(nestedResult,
                        new Term.Abs(Y, new Term.Abs(z, new Term.Comb(new Term.Comb(g, X), z)))));

        Check.checkThrow("replacement must have the variable's type",
                () -> Term.vsubst(Map.of(X, P), X));
    }
}
