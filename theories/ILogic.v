Class ILogic (L : Type) : Type :=
{ lentails : L -> L -> Prop
; ltrue : L
; lfalse : L
; land : L -> L -> L
; lor : L -> L -> L
; limpl : L -> L -> L
}.

Class Qaunt (L : Type) (I : Type) (U : I -> Type) : Type :=
{ lforall : forall (i : I), (U i -> L) -> L
; lexists : forall (i : I), (U i -> L) -> L
}.


Instance ILogic_Prop : ILogic Prop :=
{ lentails := fun x y => x -> y
; ltrue := True
; lfalse := False
; land := and
; lor := or
; limpl := fun x y => x -> y
}.

Instance ILogic_Fun (T L : Type) (IL : ILogic L) : ILogic (T -> L) :=
{ lentails := fun P Q => forall x, lentails (P x) (Q x)
; ltrue := fun _ => ltrue
; lfalse := fun _ => lfalse
; land := fun P Q x => land (P x) (Q x)
; lor := fun P Q x => lor (P x) (Q x)
; limpl := fun P Q x => limpl (P x) (Q x)
}.
