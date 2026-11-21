import hol.kernel.*;
import java.util.List;
import java.util.Map;
import java.util.Set;

final class Kernel extends Test {
    static void run() {
        fail(() -> type("list"));
        fail(() -> type("fake"));

        same(A, Type.domain(type("'a -> 'b")));
        same(B, Type.range(type("'a -> 'b")));
        fail(() -> Type.domain(A));
        fail(() -> Type.range(A));

        same(type("bool -> 'b"), Type.subst(Map.of(A, BOOL), type("'a -> 'b")));
        same(type("'a -> 'b"), Type.subst(Map.of(Type.var("c"), BOOL), type("'a -> 'b")));
        same(type("bool list"), Type.subst(Map.of(A, BOOL), type("'a list")));
        same(type("'b -> 'a"), Type.subst(Map.of(A, B, B, A), type("'a -> 'b")));
        same(type("'a -> 'a"), Type.subst(Map.of(A, type("'a -> 'a")), A));

        same(Map.of(A, BOOL), Type.match(A, BOOL));
        same(Map.of(A, B), Type.match(type("'a -> 'a"), type("'b -> 'b")));
        same(Map.of(A, B, B, A), Type.match(type("'a -> 'b"), type("'b -> 'a")));
        same(Map.of(A, type("'a -> 'a")), Type.match(type("'a -> 'a"), type("('a -> 'a) -> 'a -> 'a")));
        fail(() -> Type.match(BOOL, A));
        fail(() -> Type.match(type("'a -> 'a"), type("'b -> bool")));
        fail(() -> Type.match(type("'a list"), type("('a, 'a)prod")));

        same(Set.of(), Type.tyvars(BOOL));
        same(List.of(B, A), List.copyOf(Type.tyvars(type("'b -> 'a -> bool"))));

        fail(() -> new Term.Const("=", BOOL));
        fail(() -> new Term.Const("=", type("bool -> 'a -> bool")));
        fail(() -> new Term.Const("undeclared", A));
        same(BOOL, new Term.Const("c", BOOL).t());

        fail(() -> new Term.Comb(X, Y));
        fail(() -> new Term.Comb(term("(f:'a->'a)"), term("(p:bool)")));

        fail(() -> Term.mkEq(term("x"), prop("p")));
        same(true, Term.isEq(term("x = y")));
        same(false, Term.isEq(term("f x")));

        same(term("x"), Term.destEq(term("x = y")).l());
        same(term("y"), Term.destEq(term("x = y")).r());
        fail(() -> Term.destEq(term("x")));

        same(List.of("g", "y"), Term.frees(term("\\x. g x y")).stream().map(Term.Var::n).toList());
        same(List.of("g", "x", "h"), Term.frees(term("\\y. g x (h (\\x. x))")).stream().map(Term.Var::n).toList());

        same(List.of(A, B), List.copyOf(Term.tyvars(term("\\x. (f:'a->'b) x"))));
        same(Set.of(A), Term.tyvars(term("(\\x. x) = (\\x. x)")));

        same(true, Term.freeIn((Term.Var) term("(y:'a)"), term("\\x. (y:'a)")));
        same(false, Term.freeIn((Term.Var) term("(x:'a)"), term("\\(x:'a). y")));

        same(true, Term.aconv(term("\\x. x"), term("\\y. y")));
        same(true, Term.aconv(term("\\x x. x"), term("\\y z. z")));
        same(false, Term.aconv(term("\\(x:'a). (y:'a)"), term("\\x. x")));

        same(X, Term.variant(Set.of(Y), X));
        same(A, Term.variant(Set.of(X), X).t());
        same(false, Term.variant(Set.of(X), X).n().equals("x"));
        same(false, Set.of("x", "x'").contains(Term.variant(Set.of(X, (Term.Var) term("x'")), X).n()));
        same(false, Term.variant(Set.of((Term.Var) term("(x:bool)")), X).n().equals("x"));

        same(term("y = x"), Term.vsubst(Map.of(X, term("y"), Y, term("x")), term("x = y")));
        same(term("\\x. x"), Term.vsubst(Map.of(X, term("y")), term("\\x. x")));
        same(term("\\(x':'a). (x:'a)"), Term.vsubst(Map.of(Y, term("x")), term("\\(x:'a). (y:'a)")));
        same(term("\\y. (g:'a->'a->'a) z (h (\\x. x))"),
                Term.vsubst(Map.of(X, term("z")), term("\\y. (g:'a->'a->'a) x (h (\\x. x))")));

        same(term("(x:bool) = y"), Term.inst(Map.of(A, BOOL), term("x = y")));
        same(term("\\(x:'a). (y:'b)"), Term.inst(Map.of(A, B, B, A), term("\\(x:'b). (y:'a)")));
        same(term("\\(x:'a) (x:'a). x"), Term.inst(Map.of(B, A), term("\\(x:'a) (x:'b). x")));
    }
}
