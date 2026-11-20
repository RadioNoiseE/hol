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
    }
}
