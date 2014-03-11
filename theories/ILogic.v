Class ILogic (L : Type) : Type :=
{ lentails : L -> L -> Prop
; ltrue : L
; lfalse : L
; land : L -> L -> L
; lor : L -> L -> L
; limpl : L -> L -> L
}.

Class Quant (L : Type) : Type :=
{ lforall : forall (i : Type), (i -> L) -> L
; lexists : forall (i : Type), (i -> L) -> L
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

Instance Quant_Prop : Quant Prop :=
{ lforall := fun T P => forall x : T, P x
; lexists := fun T P => exists x : T, P x
}.

Instance Quant_Fun (T L : Type) (IL : Quant L) : Quant (T -> L) :=
{ lforall := fun T P x => lforall T (fun y => P y x)
; lexists := fun T P x => lexists T (fun y => P y x)
}.
