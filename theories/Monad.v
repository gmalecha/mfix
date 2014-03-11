Class Monad (M : Type -> Type) : Type :=
{ mret : forall T, T -> M T
; mbind : forall T U, M T -> (T -> M U) -> M U
}.

Class MonadFix (M : Type -> Type) : Type :=
{ mfix : forall {A B : Type}, ((A -> M B) -> A -> M B) -> A -> M B
}.

