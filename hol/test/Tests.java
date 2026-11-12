package hol.test;

import hol.kernel.*;
import hol.lib.*;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class Tests {
    public static void main(String[] args) {
        Check.section("types", Tests::typeTests);
        Check.section("terms", Tests::termTests);
        Check.section("frees", Tests::freesTests);
        Check.section("Type.subst", Tests::substTests);
        Check.section("aconv", Tests::aconvTests);
        Check.section("variant", Tests::variantTests);
        Check.section("vsubst", Tests::vsubstTests);
        Check.section("Term.inst", Tests::instTests);
        Check.section("tyvars", Tests::tyvarsTests);
        Check.section("match", Tests::matchTests);
        Check.section("equations", Tests::eqTests);
        Check.section("constants", Tests::constTests);
        Check.section("REFL and ASSUME", Tests::thmTests);
        Check.section("TRANS", Tests::transTests);
        Check.section("MK_COMB", Tests::mkCombTests);
        Check.section("ABS", Tests::absTests);
        Check.section("BETA", Tests::betaTests);
        Check.section("EQ_MP", Tests::eqMpTests);
        Check.section("DEDUCT_ANTISYM_RULE", Tests::darTests);
        Check.section("INST", Tests::thmInstTests);
        Check.section("INST_TYPE", Tests::instTypeTests);
        Check.section("axioms", Tests::axiomTests);
        Check.section("definitions", Tests::defTests);
        Check.section("Equal", Tests::equalTests);
        Check.section("Bool", Tests::boolTests);
        Check.section("implication", Tests::impTests);
        Check.report();
    }

    static final Type.Var A = Type.var("a");
    static final Type.Var B = Type.var("b");
    static final Type BOOL = Type.BOOL;

    static final Term.Var x = var("x", A);
    static final Term.Var y = var("y", A);
    static final Term.Var z = var("z", A);
    static final Term.Var x1 = var("x'", A);
    static final Term.Var xB = var("x", B);
    static final Term.Var xBool = var("x", BOOL);
    static final Term.Var yBool = var("y", BOOL);
    static final Term.Var zBool = var("z", BOOL);
    static final Term.Var p = var("p", BOOL);
    static final Term.Var q = var("q", BOOL);
    static final Term.Var f = var("f", fun(A, A));
    static final Term.Var f1 = var("f'", fun(A, A));
    static final Term.Var fBool = var("f", fun(BOOL, BOOL));
    static final Term.Var g = var("g", fun(A, A, A));
    static final Term.Var h = var("h", fun(fun(A, A), A));
    static final Term.Var r = var("r", fun(A, B, BOOL));
    static final Term.Var rA = var("r", fun(A, A, BOOL));
    static final Term.Var id = var("I", fun(A, A)); // becomes a constant in defTests
    static final Term.Var k = var("k", A); // definitions of k always fail
    static final Term.Var kBool = var("k", BOOL);

    static {
        Sig.newConst("c", A);
        Sig.newConst("x", A);
    }

    static final Term.Const c = new Term.Const("c", A);
    static final Term.Const cx = new Term.Const("x", A); // same name as the variable x

    static Type fun(Type... ts) {
        Type result = ts[ts.length - 1];
        for (int i = ts.length - 2; i >= 0; i--)
            result = Type.fun(ts[i], result);
        return result;
    }

    static Type op(String n, Type... ts) {
        return new Type.App(n, List.of(ts));
    }

    static Term.Var var(String n, Type t) {
        return new Term.Var(n, t);
    }

    static Term app(Term f, Term... xs) {
        Term result = f;
        for (Term x : xs)
            result = new Term.Comb(result, x);
        return result;
    }

    static Term lam(Term.Var v, Term b) {
        return new Term.Abs(v, b);
    }

    static Term eq(Term l, Term r) {
        return Term.mkEq(l, r);
    }

    static void prints(String expected, Object value) {
        Check.checkEqual("prints " + expected, expected, value.toString());
    }

    static void illTyped(String why, Runnable build) {
        Check.checkThrow("ill-typed: " + why, build);
    }

    static void freesAre(Term t, Term.Var... vs) {
        Check.checkEqual("frees(" + t + ")", List.of(vs), List.copyOf(Term.frees(t)));
    }

    static void alpha(Term s, Term t) {
        Check.checkHold(s + " ~ " + t, Term.aconv(s, t));
    }

    static void notAlpha(Term s, Term t) {
        Check.checkHold(s + " !~ " + t, !Term.aconv(s, t));
    }

    static void substEq(Type expected, Map<Type.Var, Type> theta, Type t) {
        Check.checkEqual("subst " + theta + " in " + t, expected, Type.subst(theta, t));
    }

    static void vsubstEq(Term expected, Map<Term.Var, Term> theta, Term t) {
        Check.checkEqual("vsubst " + theta + " in " + t, expected, Term.vsubst(theta, t));
    }

    static void instEq(Term expected, Map<Type.Var, Type> theta, Term t) {
        Check.checkEqual("inst " + theta + " in " + t, expected, Term.inst(theta, t));
    }

    static void matchEq(Map<Type.Var, Type> expected, Type p, Type t) {
        Check.checkEqual("match " + p + " against " + t, expected, Type.match(p, t));
    }

    static void noMatch(Type p, Type t) {
        Check.checkThrow("no match: " + p + " against " + t, () -> Type.match(p, t));
    }

    static void isAxiom(Thm th) {
        Check.checkHold("axioms() lists " + th, Thm.axioms().contains(th));
    }

    static void hypsAre(int n, Thm th) {
        Check.checkEqual("number of hypotheses of " + th, n, th.hyps().size());
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

        Check.checkEqual("domain of 'a -> bool", A, Type.domain(fun(A, BOOL)));
        Check.checkEqual("range of 'a -> bool", BOOL, Type.range(fun(A, BOOL)));
        Check.checkThrow("domain of bool fails", () -> Type.domain(BOOL));
        Check.checkThrow("range of a type variable fails", () -> Type.range(A));
    }

    static void termTests() {
        illTyped("x y (x is not a function)", () -> app(x, y));
        illTyped("f p (f wants 'a, p is bool)", () -> app(f, p));

        prints("f (f x)", app(f, app(f, x)));
        prints("g x y", app(g, x, y));
        prints("\\x:'a. f x", lam(x, app(f, x)));
        prints("(\\x:'a. x) y", app(lam(x, x), y));
        prints("(=)", new Term.Const("=", fun(A, A, BOOL)));

        Check.checkHold("same name and type: same variable", x.equals(var("x", A)));
        Check.checkHold("same name, different type: different variable", !x.equals(xBool));
        Check.checkHold("equals is structural, not alpha-equivalence", !lam(x, x).equals(lam(y, y)));
    }

    static void freesTests() {
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
        alpha(lam(x, x), lam(y, y)); // renaming bound variables
        notAlpha(lam(x, y), lam(y, y)); // free vs bound
        alpha(lam(x, lam(x, x)), lam(y, lam(z, z))); // the innermost binder wins
        notAlpha(x, cx); // a variable is not a constant of the same name
    }

    static void variantTests() {
        Check.checkEqual("no clash: name unchanged", x, Term.variant(Set.of(y), x));
        Check.checkEqual("clash: add a prime", x1, Term.variant(Set.of(x), x));
        Check.checkEqual("keep adding primes", var("x''", A), Term.variant(Set.of(x, x1), x));
        Check.checkEqual("names clash even when types differ", x1, Term.variant(Set.of(xBool), x));
    }

    static void vsubstTests() {
        vsubstEq(eq(y, x), Map.of(x, y, y, x), eq(x, y)); // simultaneous
        vsubstEq(lam(x, x), Map.of(x, y), lam(x, x)); // bound x untouched
        vsubstEq(lam(x, app(g, x, z)), Map.of(y, z), lam(x, app(g, x, y))); // no renaming needed
        vsubstEq(lam(x, x), Map.of(y, x), lam(x, x)); // y not free: no renaming
        vsubstEq(lam(y, app(g, z, app(h, lam(x, x)))), // only the free x replaced
                Map.of(x, z), lam(y, app(g, x, app(h, lam(x, x)))));
        Check.checkThrow("vsubst: replacement must have the variable's type",
                () -> Term.vsubst(Map.of(x, p), x));
    }

    static void instTests() {
        instEq(eq(xBool, yBool), Map.of(A, BOOL), eq(x, y)); // the constant = too
        instEq(lam(xB, x), Map.of(A, B, B, A), lam(x, xB)); // simultaneous swap, no renaming
        instEq(app(rA, x, x), Map.of(B, A), app(r, x, xB)); // two free variables may become one
        instEq(lam(x, lam(x, x)), Map.of(B, A), lam(x, lam(xB, xB))); // bound further in: no renaming
    }

    static void tyvarsTests() {
        Check.checkEqual("tyvars of bool", Set.of(), Type.tyvars(BOOL));
        Check.checkEqual("tyvars in order", List.of(B, A), List.copyOf(Type.tyvars(fun(B, fun(A, B)))));
        Check.checkEqual("tyvars of a term", List.of(A), List.copyOf(Term.tyvars(lam(x, app(f, x)))));
        Check.checkEqual("tyvars include bound variables' types", Set.of(A),
                Term.tyvars(eq(lam(x, x), lam(x, x))));
    }

    static void matchTests() {
        matchEq(Map.of(A, BOOL), fun(A, A), fun(BOOL, BOOL));
        matchEq(Map.of(A, B, B, A), fun(A, B), fun(B, A)); // pattern and target variables are separate
        matchEq(Map.of(A, fun(B, B)), fun(A, A), fun(fun(B, B), fun(B, B))); // ('b -> 'b) -> 'b -> 'b

        noMatch(BOOL, A); // the pattern is not more general
        noMatch(fun(A, A), fun(BOOL, B)); // 'a cannot be both bool and 'b
        noMatch(fun(A, BOOL), BOOL);
        noMatch(fun(A, A), fun(B, B, B, B)); // 'b -> 'b -> 'b -> 'b
        noMatch(op("triple", A, A, A), op("triple", BOOL, B, BOOL));
        noMatch(op("list", A), op("prod", A, A)); // different operators
        noMatch(op("list", A), op("list", BOOL, BOOL)); // target has more arguments
        noMatch(op("list", A, A), op("list", BOOL)); // target has fewer arguments
    }

    static void eqTests() {
        prints("x = y", eq(x, y));
        prints("(\\x:'a. x) = (\\y:'a. y)", eq(lam(x, x), lam(y, y)));
        prints("f x = y", eq(app(f, x), y));
        prints("\\x:'a. x = x", lam(x, eq(x, x)));
        prints("f (x = y)", app(fBool, eq(x, y)));
        prints("(x = y) = (y = x)", eq(eq(x, y), eq(y, x)));

        Check.checkThrow("mkEq: both sides need the same type", () -> Term.mkEq(x, p));
        Check.checkHold("x = y is an equation", Term.isEq(eq(x, y)));
        Check.checkHold("f x is not an equation", !Term.isEq(app(f, x)));
        Check.checkEqual("destEq: left side", x, Term.destEq(eq(x, y)).l());
        Check.checkEqual("destEq: right side", y, Term.destEq(eq(x, y)).r());
        Check.checkThrow("destEq fails on a non-equation", () -> Term.destEq(x));
    }

    static void constTests() {
        Check.checkEqual("= is declared as 'a -> 'a -> bool", fun(A, A, BOOL), Sig.constType("="));
        Check.checkThrow("constType of an undeclared name", () -> Sig.constType("undeclared"));
        Check.checkThrow("a constant cannot be declared twice", () -> Sig.newConst("=", BOOL));

        Check.checkEqual("= at bool -> bool -> bool", fun(BOOL, BOOL, BOOL),
                new Term.Const("=", fun(BOOL, BOOL, BOOL)).t());
        Check.checkThrow("= cannot have type bool", () -> new Term.Const("=", BOOL));
        Check.checkThrow("= needs both arguments of the same type",
                () -> new Term.Const("=", fun(BOOL, A, BOOL)));
        Check.checkThrow("undeclared constants are rejected", () -> new Term.Const("undeclared", A));
        Check.checkEqual("c, declared at 'a, can be used at bool", BOOL, new Term.Const("c", BOOL).t());
    }

    static void thmTests() {
        prints("|- x = x", Thm.refl(x));
        prints("|- (\\x:'a. x) = (\\x:'a. x)", Thm.refl(lam(x, x)));
        prints("p |- p", Thm.assume(p));
        prints("x = y |- x = y", Thm.assume(eq(x, y)));
        Check.checkThrow("assume needs a proposition", () -> Thm.assume(x));
    }

    static void transTests() {
        prints("x = y, y = z |- x = z", Thm.trans(Thm.assume(eq(x, y)), Thm.assume(eq(y, z))));
        prints("f = (\\x:'a. x), (\\y:'a. y) = f |- f = f", // middle terms up to renaming
                Thm.trans(Thm.assume(eq(f, lam(x, x))), Thm.assume(eq(lam(y, y), f))));
        Check.checkThrow("trans: middle terms must agree",
                () -> Thm.trans(Thm.assume(eq(x, y)), Thm.assume(eq(x, z))));
        Check.checkThrow("trans: first theorem must be an equation",
                () -> Thm.trans(Thm.assume(p), Thm.refl(p)));
        Check.checkThrow("trans: second theorem must be an equation",
                () -> Thm.trans(Thm.refl(p), Thm.assume(p)));
    }

    static void mkCombTests() {
        prints("x = y |- f x = f y", Thm.mkComb(Thm.refl(f), Thm.assume(eq(x, y))));
        prints("f = f', x = y |- f x = f' y", Thm.mkComb(Thm.assume(eq(f, f1)), Thm.assume(eq(x, y))));
        hypsAre(1, Thm.mkComb(Thm.assume(eq(lam(x, x), f)), // alpha-equivalent hypotheses merged
                Thm.mkComb(Thm.assume(eq(lam(z, z), f)), Thm.refl(x))));
        Check.checkThrow("mkComb: argument type must fit", () -> Thm.mkComb(Thm.refl(f), Thm.refl(p)));
        Check.checkThrow("mkComb: first theorem must be an equation",
                () -> Thm.mkComb(Thm.assume(p), Thm.refl(x)));
        Check.checkThrow("mkComb: second theorem must be an equation",
                () -> Thm.mkComb(Thm.refl(f), Thm.assume(p)));
    }

    static void absTests() {
        prints("|- (\\x:'a. f x) = (\\x:'a. f x)", Thm.abs(x, Thm.refl(app(f, x))));
        prints("x = z |- (\\y:'a. x) = (\\y:'a. z)", Thm.abs(y, Thm.assume(eq(x, z))));
        Check.checkThrow("abs: the variable must not be free in a hypothesis",
                () -> Thm.abs(x, Thm.assume(eq(x, y))));
        Check.checkThrow("abs: the theorem must be an equation", () -> Thm.abs(x, Thm.assume(p)));
    }

    static void betaTests() {
        prints("|- (\\x:'a. f x) x = f x", Thm.beta(app(lam(x, app(f, x)), x)));
        Check.checkThrow("beta: the argument must be the bound variable", () -> Thm.beta(app(lam(x, x), y)));
        Check.checkThrow("beta: an application of a variable is not a redex", () -> Thm.beta(app(f, x)));
        Check.checkThrow("beta: a variable is not a redex", () -> Thm.beta(x));
    }

    static void eqMpTests() {
        prints("p = q, p |- q", Thm.eqMp(Thm.assume(eq(p, q)), Thm.assume(p)));
        prints("((\\x:'a. x) = f) = p, (\\y:'a. y) = f |- p", // antecedent up to renaming
                Thm.eqMp(Thm.assume(eq(eq(lam(x, x), f), p)), Thm.assume(eq(lam(y, y), f))));
        Check.checkThrow("eqMp: first theorem must be an equation",
                () -> Thm.eqMp(Thm.assume(p), Thm.assume(p)));
        Check.checkThrow("eqMp: second theorem must match the left side",
                () -> Thm.eqMp(Thm.assume(eq(p, q)), Thm.assume(q)));
    }

    static void darTests() {
        prints("|- p = p", Thm.dar(Thm.assume(p), Thm.assume(p)));
        prints("p, q |- p = q", Thm.dar(Thm.assume(p), Thm.assume(q)));
        hypsAre(0, Thm.dar(Thm.assume(eq(lam(x, x), f)), // removed up to renaming
                Thm.assume(eq(lam(y, y), f))));
        prints("p, p = q |- p = q", // p leaves the second theorem's hypotheses only
                Thm.dar(Thm.assume(p), Thm.eqMp(Thm.assume(eq(p, q)), Thm.assume(p))));
    }

    static void thmInstTests() {
        prints("y = z |- y = z", Thm.inst(Map.of(x, y), Thm.assume(eq(x, z)))); // hypotheses too
        hypsAre(1, Thm.inst(Map.of(z, x), // two hypotheses become one
                Thm.dar(Thm.assume(eq(x, y)), Thm.assume(eq(z, y)))));
        Check.checkThrow("inst: replacement must have the variable's type",
                () -> Thm.inst(Map.of(x, p), Thm.refl(x)));
    }

    static void instTypeTests() {
        Check.checkEqual("instType: hypotheses get the new type", List.of(eq(xBool, yBool)),
                Thm.instType(Map.of(A, BOOL), Thm.assume(eq(x, y))).hyps());
        hypsAre(1, Thm.instType(Map.of(B, A), // two hypotheses become one
                Thm.dar(Thm.assume(eq(x, x)), Thm.assume(eq(xB, xB)))));
    }

    static void axiomTests() {
        prints("|- c = c", Thm.newAxiom(eq(c, c))); // harmless: REFL proves it anyway
        isAxiom(Thm.newAxiom(eq(c, c)));
        Check.checkThrow("an axiom must be a proposition", () -> Thm.newAxiom(x));
    }

    static void defTests() {
        prints("|- I = (\\x:'a. x)", Thm.newBasicDef(eq(id, lam(x, x))));
        Check.checkEqual("I is declared with the type of its definition", fun(A, A), Sig.constType("I"));
        Check.checkEqual("I can be used at an instance of its type", fun(BOOL, BOOL),
                new Term.Const("I", fun(BOOL, BOOL)).t());

        Check.checkThrow("cannot define a name twice", () -> Thm.newBasicDef(eq(id, lam(y, y))));
        Check.checkThrow("the right side must have no free variables", () -> Thm.newBasicDef(eq(k, x)));
        Check.checkThrow("a failed definition declares nothing", () -> Sig.constType("k"));
        Check.checkThrow("type variables of the right side must occur in the constant's type",
                () -> Thm.newBasicDef(eq(kBool, eq(lam(x, x), lam(x, x)))));
        Check.checkThrow("the left side must be a variable", () -> Thm.newBasicDef(eq(c, c)));
        Check.checkThrow("the definition must be an equation", () -> Thm.newBasicDef(p));
    }

    static void equalTests() {
        prints("x = y |- f x = f y", Equal.apTerm(f, Thm.assume(eq(x, y))));
        prints("f = f' |- f x = f' x", Equal.apThm(Thm.assume(eq(f, f1)), x));
        Check.checkThrow("sym needs an equation", () -> Equal.sym(Thm.assume(p)));
        Check.checkThrow("betaConv needs a redex", () -> Equal.betaConv(app(f, x)));
    }

    static void boolTests() {
        prints("|- T = ((\\p:bool. p) = (\\p:bool. p))", Bool.T_DEF);
        prints("|- T", Bool.TRUTH);
        prints("p |- p = T", Bool.eqtIntro(Thm.assume(p)));
        prints("T |- T = T", Bool.eqtIntro(Thm.assume(Bool.T))); // the hypothesis T is kept
        prints("p = T |- p", Bool.eqtElim(Thm.assume(eq(p, Bool.T))));
        Check.checkThrow("eqtElim needs an equation with T", () -> Bool.eqtElim(Thm.assume(eq(p, q))));
        prints("|- T", Bool.proveHyp(Bool.TRUTH, Thm.assume(Bool.T)));
        prints("q = q |- q = q", Bool.proveHyp(Thm.assume(p), Thm.assume(eq(q, q)))); // nothing to discharge

        prints("|- (/\\) T T", Bool.conj(Bool.TRUTH, Bool.TRUTH));
        prints("p, q |- (/\\) p q", Bool.conj(Thm.assume(p), Thm.assume(q)));
        prints("(/\\) p q |- p", Bool.conjunct1(Thm.assume(Bool.mkConj(p, q))));
        prints("(/\\) p q |- q", Bool.conjunct2(Thm.assume(Bool.mkConj(p, q))));
        prints("p, q |- q", Bool.conjunct2(Bool.conj(Thm.assume(p), Thm.assume(q))));
        prints("x = y |- x = y", Bool.conjunct1(Bool.conj(Thm.assume(eq(x, y)), Bool.TRUTH)));
        prints("x = y, p |- (/\\) (x = y) p", Bool.conj(Thm.assume(eq(x, y)), Thm.assume(p)));
        prints("p |- (/\\) p p", Bool.conj(Thm.assume(p), Thm.assume(p))); // shared hypothesis kept once
        Check.checkThrow("conjunct1 needs a conjunction", () -> Bool.conjunct1(Thm.assume(p)));
    }

    static void impTests() {
        prints("|- (==>) = (\\p:bool. \\q:bool. (/\\) p q = p)", Bool.IMP_DEF);

        prints("p, (==>) p q |- q", Bool.mp(Thm.assume(Bool.mkImp(p, q)), Thm.assume(p)));
        Check.checkThrow("mp: the antecedent must match",
                () -> Bool.mp(Thm.assume(Bool.mkImp(p, q)), Thm.assume(q)));
        Check.checkThrow("mp needs an implication", () -> Bool.mp(Thm.assume(p), Thm.assume(p)));

        prints("|- (==>) p p", Bool.disch(p, Thm.assume(p)));
        prints("q |- (==>) p q", Bool.disch(p, Thm.assume(q))); // p was not a hypothesis
        prints("q |- (==>) p ((/\\) p q)", Bool.disch(p, Bool.conj(Thm.assume(p), Thm.assume(q))));
        Check.checkThrow("disch needs a proposition", () -> Bool.disch(x, Thm.assume(p)));

        prints("p, (==>) p q |- q", Bool.undisch(Thm.assume(Bool.mkImp(p, q))));
        Check.checkThrow("undisch needs an implication", () -> Bool.undisch(Thm.assume(p)));

        prints("|- (==>) q ((==>) p ((/\\) p q))", Bool.dischAll(Bool.conj(Thm.assume(p), Thm.assume(q))));
        prints("p, q |- (/\\) p q", Bool.undischAll(Bool.dischAll(Bool.conj(Thm.assume(p), Thm.assume(q)))));
        prints("p |- x = x", Bool.addAssum(p, Thm.refl(x)));
    }
}
