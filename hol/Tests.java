package hol;

import java.util.List;
import java.util.Map;
import java.util.Set;

public class Tests {
    public static void main(String[] args) {
        typeTests();
        termTests();
        freesTests();
        substTests();
        aconvTests();
        variantTests();
        vsubstTests();
        instTests();
        eqTests();
        thmTests();
        matchTests();
        Check.report();
    }

    static final Type.Var A = Type.var("a");
    static final Type.Var B = Type.var("b");
    static final Type BOOL = Type.BOOL;

    static final Term.Var x = var("x", A);
    static final Term.Var x1 = var("x'", A);
    static final Term.Var xb = var("x", B);
    static final Term.Var xB = var("x", BOOL);
    static final Term.Var y = var("y", A);
    static final Term.Var yB = var("y", BOOL);
    static final Term.Var z = var("z", A);
    static final Term.Var p = var("p", BOOL);
    static final Term.Var f = var("f", fun(A, A));
    static final Term.Var fb = var("f", fun(BOOL, BOOL));
    static final Term.Var g = var("g", fun(A, A, A));
    static final Term.Var h = var("h", fun(fun(A, A), A));
    static final Term.Const c = new Term.Const("c", A);

    static Type fun(Type... types) {
        Type result = types[types.length - 1];
        for (int i = types.length - 2; i >= 0; i--)
            result = Type.fun(types[i], result);
        return result;
    }

    static Type op(String name, Type... args) {
        return new Type.App(name, List.of(args));
    }

    static Term.Var var(String name, Type type) {
        return new Term.Var(name, type);
    }

    static Term app(Term fn, Term... args) {
        Term result = fn;
        for (Term arg : args)
            result = new Term.Comb(result, arg);
        return result;
    }

    static Term lam(Term.Var v, Term body) {
        return new Term.Abs(v, body);
    }

    static Term eq(Term l, Term r) {
        Type t = Term.typeOf(l);
        return app(new Term.Const("=", fun(t, t, BOOL)), l, r);
    }

    static void prints(String expected, Object value) {
        Check.checkEqual("prints " + expected, expected, value.toString());
    }

    static void hasType(Type expected, Term t) {
        Check.checkEqual("type of " + t, expected, Term.typeOf(t));
    }

    static void illTyped(String name, Runnable build) {
        Check.checkThrow("ill-typed: " + name, build);
    }

    static void freesAre(Term t, Term.Var... expected) {
        Check.checkEqual("frees(" + t + ")", List.of(expected), List.copyOf(Term.frees(t)));
    }

    static void alpha(Term s, Term t) {
        Check.checkHold(s + "  ~  " + t, Term.aconv(s, t));
    }

    static void notAlpha(Term s, Term t) {
        Check.checkHold(s + "  !~  " + t, !Term.aconv(s, t));
    }

    static void substEq(Type expected, Map<Type.Var, Type> theta, Type t) {
        Check.checkEqual("subst " + theta + " in " + t, expected, Type.subst(theta, t));
    }

    static void vsubstEq(Term expected, Map<Term.Var, Term> theta, Term t) {
        Check.checkEqual("vsubst " + theta + " in " + t, expected, Term.vsubst(theta, t));
    }

    static void vsubstAlpha(Term expected, Map<Term.Var, Term> theta, Term t) {
        Term actual = Term.vsubst(theta, t);
        Check.checkHold("vsubst " + theta + " in " + t + "  ~  " + expected
                + "   (got " + actual + ")",
                Term.aconv(expected, actual));
    }

    static void instEq(Term expected, Map<Type.Var, Type> theta, Term t) {
        Check.checkEqual("inst " + theta + " in " + t, expected, Term.inst(theta, t));
    }

    static void instAlpha(Term expected, Map<Type.Var, Type> theta, Term t) {
        Term actual = Term.inst(theta, t);
        Check.checkHold("inst " + theta + " in " + t + "  ~  " + expected
                + "   (got " + actual + ")",
                Term.aconv(expected, actual));
    }

    static void matchEq(Map<Type.Var, Type> expected, Type p, Type t) {
        Check.checkEqual("match " + p + " against " + t, expected, Type.match(p, t));
    }

    static void noMatch(Type p, Type t) {
        Check.checkThrow("no match: " + p + " against " + t, () -> Type.match(p, t));
    }

    static void typeTests() {
        prints("'a", A);
        prints("bool", BOOL);
        prints("'a -> bool", fun(A, BOOL));
        prints("'a -> 'b -> 'a", fun(A, B, A)); // -> is right-associative
        prints("('a -> 'b) -> 'a", fun(fun(A, B), A));
        prints("(bool)list", op("list", BOOL));
        prints("('a, bool)prod", op("prod", A, BOOL));

        Check.checkEqual("types are compared by structure", fun(A, BOOL), fun(Type.var("a"), BOOL));
        Check.checkHold("different types are not equal", !fun(A, B).equals(fun(B, A)));

        Check.checkEqual("domain", A, Type.domain(fun(A, BOOL)));
        Check.checkEqual("range", BOOL, Type.range(fun(A, BOOL)));
        Check.checkThrow("domain of bool fails", () -> Type.domain(BOOL));
        Check.checkThrow("range of a type variable fails", () -> Type.range(A));
    }

    static void termTests() {
        hasType(A, x);
        hasType(A, app(f, x));
        hasType(fun(A, A), lam(x, x));
        hasType(fun(A, A, A), lam(x, lam(y, x)));
        hasType(BOOL, eq(x, y));

        illTyped("x y (x is not a function)", () -> app(x, y));
        illTyped("f p (f wants 'a, p is bool)", () -> app(f, p));

        prints("f (f x)", app(f, app(f, x)));
        prints("g x y", app(g, x, y));
        prints("\\x:'a. f x", lam(x, app(f, x)));
        prints("(\\x:'a. x) y", app(lam(x, x), y));
        prints("(=)", new Term.Const("=", fun(A, A, BOOL)));

        Check.checkHold("same name and type: same variable", x.equals(var("x", A)));
        Check.checkHold("same name, different type: different variable", !x.equals(xB));
        Check.checkHold("equals is structural, not alpha-equivalence", !lam(x, x).equals(lam(y, y)));
    }

    static void freesTests() {
        freesAre(x, x);
        freesAre(c);
        freesAre(app(f, x), f, x);
        freesAre(lam(x, x));
        freesAre(lam(x, y), y);
        freesAre(lam(x, lam(x, x))); // inner binder shadows outer
        freesAre(lam(xB, x), x); // binder of another type does not bind
        freesAre(lam(x, app(g, x, y)), g, y); // order of first occurrence
        freesAre(lam(y, app(g, x, app(h, lam(x, x)))), g, x, h); // x both free and bound

        Check.checkHold("y is free in \\x. y", Term.freeIn(y, lam(x, y)));
        Check.checkHold("x is not free in \\x. y", !Term.freeIn(x, lam(x, y)));
    }

    static void substTests() {
        substEq(fun(BOOL, B), Map.of(A, BOOL), fun(A, B));
        substEq(fun(A, B), Map.of(Type.var("c"), BOOL), fun(A, B)); // not in map: unchanged
        substEq(op("list", A), Map.of(), op("list", A)); // empty: identity
        substEq(BOOL, Map.of(A, B), BOOL);
        substEq(op("list", BOOL), Map.of(A, BOOL), op("list", A)); // inside any operator
        substEq(fun(fun(B, B), BOOL), Map.of(A, fun(B, B)), fun(A, BOOL));
        substEq(fun(B, A), Map.of(A, B, B, A), fun(A, B)); // simultaneous swap
        substEq(fun(A, A), Map.of(A, fun(A, A)), A); // no re-substitution
    }

    static void aconvTests() {
        // no binders: same as equals
        alpha(x, x);
        notAlpha(x, y);
        notAlpha(x, xB);
        alpha(c, new Term.Const("c", A));
        notAlpha(x, new Term.Const("x", A));
        alpha(app(f, x), app(f, x));
        notAlpha(app(f, x), app(f, y));

        // renaming bound variables
        alpha(lam(x, x), lam(y, y));
        alpha(lam(x, app(f, x)), lam(y, app(f, y)));
        alpha(lam(x, lam(y, x)), lam(y, lam(x, y)));
        notAlpha(lam(x, lam(y, x)), lam(x, lam(y, y)));

        // free variables stay free
        alpha(lam(x, y), lam(z, y));
        notAlpha(lam(x, y), lam(y, y)); // free vs bound
        notAlpha(lam(y, y), lam(x, y)); // bound vs free

        // shadowing: the innermost binder wins
        alpha(lam(x, lam(x, x)), lam(y, lam(z, z)));
        notAlpha(lam(x, lam(x, x)), lam(y, lam(z, y)));
        notAlpha(lam(x, lam(y, x)), lam(y, lam(y, y)));

        notAlpha(lam(xB, xB), lam(x, x)); // binder types matter
        notAlpha(lam(x, x), app(f, x)); // different shapes
    }

    static void variantTests() {
        Check.checkEqual("no clash: name unchanged", x, Term.variant(Set.of(y), x));
        Check.checkEqual("clash: add a prime", x1, Term.variant(Set.of(x), x));
        Check.checkEqual("keep adding primes", var("x''", A), Term.variant(Set.of(x, x1), x));
        Check.checkEqual("names clash even when types differ", x1, Term.variant(Set.of(xB), x));
    }

    static void vsubstTests() {
        // no binders
        vsubstEq(app(f, y), Map.of(x, y), app(f, x));
        vsubstEq(app(f, x), Map.of(y, z), app(f, x)); // not in map: unchanged
        vsubstEq(c, Map.of(x, y), c);
        vsubstEq(app(f, app(f, y)), Map.of(x, app(f, y)), app(f, x));
        vsubstEq(eq(y, x), Map.of(x, y, y, x), eq(x, y)); // simultaneous

        // binders without capture: the result is exact, no renaming
        vsubstEq(lam(x, x), Map.of(x, y), lam(x, x)); // bound x untouched
        vsubstEq(lam(x, z), Map.of(y, z), lam(x, y));
        vsubstEq(lam(x, app(g, x, z)), Map.of(y, z), lam(x, app(g, x, y)));
        vsubstEq(lam(x, x), Map.of(y, x), lam(x, x)); // y not free: no renaming
        vsubstEq(lam(y, app(g, z, app(h, lam(x, x)))), // only the free x replaced
                Map.of(x, z), lam(y, app(g, x, app(h, lam(x, x)))));

        // capture: the binder must be renamed
        vsubstAlpha(lam(z, x), Map.of(y, x), lam(x, y));
        freesAre(Term.vsubst(Map.of(y, x), lam(x, y)), x);
        vsubstAlpha(lam(z, app(g, x, x1)), Map.of(y, x), lam(x, app(g, y, x1))); // avoid x' too
        freesAre(Term.vsubst(Map.of(y, x), lam(x, app(g, y, x1))), g, x, x1);
        vsubstAlpha(lam(y, lam(z, app(g, x, z))), Map.of(y, x), lam(x, lam(z, app(g, y, z))));

        Check.checkThrow("vsubst: replacement must have the variable's type",
                () -> Term.vsubst(Map.of(x, p), x));
    }

    static void instTests() {
        // types change everywhere: variables, constants, binders
        instEq(xB, Map.of(A, BOOL), x);
        instEq(lam(xB, xB), Map.of(A, BOOL), lam(x, x));
        instEq(eq(xB, yB), Map.of(A, BOOL), eq(x, y)); // the constant = too
        instEq(app(fb, xB), Map.of(A, BOOL), app(f, x));
        instEq(app(f, x), Map.of(B, BOOL), app(f, x)); // other type variables: unchanged
        instEq(lam(x, app(f, x)), Map.of(), lam(x, app(f, x))); // empty: identity
        instEq(lam(xb, x), Map.of(A, B, B, A), lam(x, xb)); // simultaneous swap, no renaming

        // two free variables may become one: that is fine
        Term.Var r = var("r", fun(A, B, BOOL));
        instEq(app(var("r", fun(A, A, BOOL)), x, x), Map.of(B, A), app(r, x, xb));

        // a bound variable must not capture a free one that becomes equal to it
        instAlpha(lam(z, x), Map.of(B, A), lam(x, xb));
        freesAre(Term.inst(Map.of(B, A), lam(x, xb)), x);

        // ... and the renamed binder must still get its new type
        instAlpha(lam(var("z", BOOL), xB), Map.of(A, BOOL, B, BOOL), lam(x, xb));

        // no renaming when the clashing variable is bound further in
        instEq(lam(x, lam(x, x)), Map.of(B, A), lam(x, lam(xb, xb)));
    }

    static void eqTests() {
        prints("x = y", eq(x, y));
        prints("(\\x:'a. x) = (\\y:'a. y)", eq(lam(x, x), lam(y, y)));
        prints("f x = y", eq(app(f, x), y));
        prints("\\x:'a. x = x", lam(x, eq(x, x)));
        prints("f (x = y)", app(fb, eq(x, y)));
        prints("(x = y) = (y = x)", eq(eq(x, y), eq(y, x)));

        Check.checkEqual("mkEq builds the same term as eq", eq(x, y), Term.mkEq(x, y));
        Check.checkThrow("mkEq: both sides need the same type", () -> Term.mkEq(x, p));

        Check.checkHold("x = y is an equation", Term.isEq(eq(x, y)));
        Check.checkHold("f x is not an equation", !Term.isEq(app(f, x)));
        Check.checkEqual("destEq: left side", x, Term.destEq(eq(x, y)).l());
        Check.checkEqual("destEq: right side", y, Term.destEq(eq(x, y)).r());
        Check.checkThrow("destEq fails on a non-equation", () -> Term.destEq(x));
    }

    static void thmTests() {
        prints("|- x = x", Thm.refl(x));
        prints("|- (\\x:'a. x) = (\\x:'a. x)", Thm.refl(lam(x, x)));
        Check.checkEqual("refl has no hypotheses", List.of(), Thm.refl(x).hyps());
        Check.checkEqual("refl: conclusion", eq(f, f), Thm.refl(f).concl());

        prints("p |- p", Thm.assume(p));
        prints("x = y |- x = y", Thm.assume(eq(x, y)));
        Check.checkEqual("assume: hypotheses", List.of(p), Thm.assume(p).hyps());
        Check.checkEqual("assume: conclusion", p, Thm.assume(p).concl());
        Check.checkThrow("assume needs a proposition", () -> Thm.assume(x));
    }

    static void matchTests() {
        // variables in the pattern
        matchEq(Map.of(A, BOOL), A, BOOL);
        matchEq(Map.of(A, A), A, A);
        matchEq(Map.of(A, fun(B, B)), A, fun(B, B));

        // no variables in the pattern
        matchEq(Map.of(), BOOL, BOOL);
        noMatch(BOOL, A); // the pattern is not more general

        // function types
        matchEq(Map.of(A, BOOL), fun(A, A), fun(BOOL, BOOL));
        matchEq(Map.of(A, BOOL, B, BOOL), fun(A, B), fun(BOOL, BOOL));
        matchEq(Map.of(A, fun(B, B)), fun(A, BOOL), fun(fun(B, B), BOOL));
        matchEq(Map.of(A, B, B, A), fun(A, B), fun(B, A)); // pattern and target variables are separate
        noMatch(fun(A, A), fun(BOOL, B)); // a cannot be both bool and b
        noMatch(fun(A, BOOL), BOOL);

        // -> is right-associative
        matchEq(Map.of(A, fun(B, B)), fun(A, A), fun(fun(B, B), fun(B, B))); // ('b -> 'b) -> 'b -> 'b
        noMatch(fun(A, A), fun(B, B, B, B)); // 'b -> 'b -> 'b -> 'b

        // other type operators
        matchEq(Map.of(A, BOOL), op("list", A), op("list", BOOL));
        matchEq(Map.of(A, BOOL, B, B), op("triple", A, B, A), op("triple", BOOL, B, BOOL));
        noMatch(op("triple", A, A, A), op("triple", BOOL, B, BOOL));
        noMatch(op("list", A), op("prod", A, A)); // different operators
        noMatch(op("list", A), op("list", BOOL, BOOL)); // target has more arguments
        noMatch(op("list", A, A), op("list", BOOL)); // target has fewer arguments

        // what match means: substituting the result into the pattern gives the target
        Type q = fun(A, fun(B, A));
        Type r = fun(BOOL, fun(fun(A, A), BOOL));
        Check.checkEqual("subst(match(q, r), q) = r", r, Type.subst(Type.match(q, r), q));
    }
}
