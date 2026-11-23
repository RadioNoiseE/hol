import hol.kernel.*;
import hol.lib.*;

final class Lib extends Test {
    static void run() {
        hold(Equal.betaConv(term("(\\x. (f:'a->'a) x) y")), "(\\x. (f:'a->'a) x) y = f y");
        hold(Equal.betaNorm(term("(\\x y. (f:'a->'a->'a) x y) a b")), "(\\x y. (f:'a->'a->'a) x y) a b = f a b");
        hold(Equal.betaRule(Thm.assume(prop("(\\x. x) p"))), "p", "(\\x. x) p");
        hold(Equal.apTerm(term("(f:'a->'a)"), Thm.assume(prop("x = y"))), "(f:'a->'a) x = f y", "x = y");
        hold(Equal.apThm(Thm.assume(prop("(f:'a->'a) = g")), term("x")), "(f:'a->'a) x = g x", "(f:'a->'a) = g");
        hold(Equal.sym(Thm.assume(prop("x = y"))), "y = x", "x = y");
        fail(() -> Equal.betaConv(term("(f:'a->'a) x")));
        fail(() -> Equal.sym(Thm.assume(prop("p"))));

        hold(Bool.T_DEF, "T = ((\\(p:bool). p) = \\p. p)");
        hold(Bool.TRUTH, "T");
        hold(Bool.proveHyp(Bool.TRUTH, Thm.assume(prop("T"))), "T");
        hold(Bool.eqtIntro(Thm.assume(prop("p"))), "p = T", "p");
        hold(Bool.eqtElim(Thm.assume(prop("p = T"))), "p", "p = T");

        hold(Bool.AND_DEF, "(/\\) = \\p q. (\\(f:bool->bool->bool). f p q) = \\f. f T T");
        hold(Bool.conj(Thm.assume(prop("p")), Thm.assume(prop("q"))), "p /\\ q", "p", "q");
        hold(Bool.conjunct1(Thm.assume(prop("p /\\ q"))), "p", "p /\\ q");
        hold(Bool.conjunct2(Thm.assume(prop("p /\\ q"))), "q", "p /\\ q");
        fail(() -> Bool.conjunct1(Thm.assume(prop("p"))));

        hold(Bool.IMP_DEF, "(==>) = \\p q. (p /\\ q) = p");
        hold(Bool.mp(Thm.assume(prop("p ==> q")), Thm.assume(prop("p"))), "q", "p ==> q", "p");
        hold(Bool.disch(prop("p"), Thm.assume(prop("q"))), "p ==> q", "q");
        hold(Bool.dischAll(Bool.conj(Thm.assume(prop("p")), Thm.assume(prop("q")))), "q ==> p ==> p /\\ q");
        hold(Bool.undisch(Thm.assume(prop("p ==> q"))), "q", "p ==> q", "p");
        hold(Bool.undischAll(Thm.assume(prop("p ==> q ==> r"))), "r", "p ==> q ==> r", "p", "q");
        hold(Bool.addAssum(prop("p"), Thm.refl(term("x"))), "x = x", "p");
        fail(() -> Bool.mp(Thm.assume(prop("p ==> q")), Thm.assume(prop("q"))));

        hold(Bool.FORALL_DEF, "(!) = \\(s:'a->bool). s = \\x. T");
        hold(Bool.spec(term("y"), Thm.assume(prop("!x. x = c"))), "y = c", "!x. x = c");
        hold(Bool.gen(X, Thm.refl(term("x"))), "!x. x = x");
        fail(() -> Bool.spec(prop("p"), Thm.assume(prop("!x. x = c"))));

        hold(Bool.EXISTS_DEF, "(?) = \\(s:'a->bool). !q. (!x. s x ==> q) ==> q");
        hold(Bool.exists(term("?x. x = y"), term("y"), Thm.refl(term("y"))), "?x. x = y");
        hold(Bool.choose(Y, Thm.assume(prop("?x. x = c /\\ q")), Bool.conjunct2(Thm.assume(prop("y = c /\\ q")))),
                "q", "?x. x = c /\\ q");
        fail(() -> Bool.exists(term("?x. x = y"), prop("p"), Thm.refl(term("y"))));

        hold(Bool.OR_DEF, "(\\/) = \\p q. !r. (p ==> r) ==> (q ==> r) ==> r");
        hold(Bool.disj1(Thm.assume(prop("p")), prop("q")), "p \\/ q", "p");
        hold(Bool.disj2(prop("p"), Thm.assume(prop("q"))), "p \\/ q", "q");
        hold(Bool.disjCases(Thm.assume(prop("p \\/ q")), Thm.assume(prop("r")), Thm.assume(prop("r"))),
                "r", "p \\/ q", "r");
        fail(() -> Bool.disjCases(Thm.assume(prop("p \\/ q")), Thm.assume(prop("p")), Thm.assume(prop("q"))));

        hold(Bool.F_DEF, "F = !p. p");
        hold(Bool.NOT_DEF, "(~) = \\p. p ==> F");
        hold(Bool.notElim(Thm.assume(prop("~p"))), "p ==> F", "~p");
        hold(Bool.notIntro(Thm.assume(prop("p ==> F"))), "~p", "p ==> F");
        hold(Bool.contr(prop("q"), Thm.assume(prop("F"))), "q", "F");
        hold(Bool.eqfIntro(Thm.assume(prop("~p"))), "p = F", "~p");
        hold(Bool.eqfElim(Thm.assume(prop("p = F"))), "~p", "p = F");
        fail(() -> Bool.notIntro(Thm.assume(prop("p ==> q"))));
        fail(() -> Bool.contr(prop("q"), Thm.assume(prop("p"))));
        fail(() -> Bool.eqfElim(Thm.assume(prop("(p:bool) = q"))));

        hold(Classical.ETA_AX, "!(g:'a->'b). (\\x. g x) = g");
        hold(Classical.SELECT_AX, "!(s:'a->bool) x. s x ==> s ((@) s)");
        hold(Classical.EXCLUDED_MIDDLE, "!p. p \\/ ~p");
        hold(Classical.etaConv(term("\\x. (f:'a->'b) x")), "(\\x. (f:'a->'b) x) = f");
        hold(Classical.ccontr(prop("p"), Bool.mp(Bool.notElim(Thm.assume(prop("~ ~p"))), Thm.assume(prop("~p")))),
                "p", "~ ~p");
        fail(() -> Classical.etaConv(term("\\x. x")));
        fail(() -> Classical.ccontr(prop("p"), Thm.assume(prop("p"))));
    }
}
