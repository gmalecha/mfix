Require Import RelationClasses.

Class ILogic (L : Type) : Type :=
{ lentails : L -> L -> Prop
; ltrue : L
; lfalse : L
; land : L -> L -> L
; lor : L -> L -> L
; limpl : L -> L -> L
}.

Class ILogicOk L (IL : ILogic L) : Type :=
{ Refl_lentails :> Reflexive lentails
; Trans_lentails :> Transitive lentails
; ltrueR : forall G, lentails G ltrue
; lfalseL : forall G, lentails lfalse G
; landR : forall G P Q, lentails G P -> lentails G Q -> lentails G (land P Q)
; landL1 : forall G P Q, lentails P G -> lentails (land P Q) G
; landL2 : forall G P Q, lentails Q G -> lentails (land P Q) G
; lorR1  : forall G P Q, lentails G P -> lentails G (lor P Q)
; lorR2  : forall G P Q, lentails G Q -> lentails G (lor P Q)
; limplR : forall G P Q, lentails G (limpl P Q) -> lentails (land P G) Q
; limplL : forall G P Q, lentails (land P G) Q -> lentails G (limpl P Q)
}.

Class Quant (L : Type) : Type :=
{ lforall : forall (i : Type), (i -> L) -> L
; lexists : forall (i : Type), (i -> L) -> L
}.


Class QuantOk L (IL : ILogic L) (Q : Quant L) : Prop :=
{ lforallR : forall i (P : i -> L) G, (forall x, lentails G (P x)) -> lentails G (lforall _ P)
; lforallL : forall i (P : i -> L) G x, lentails (P x) G -> lentails (lforall i P) G
; lexistsL : forall i (P : i -> L) G, (forall x, lentails (P x) G) -> lentails (lexists _ P) G
; lexistsR : forall i (P : i -> L) G x, lentails G (P x) -> lentails G (lexists i P)
}.

Notation "P |-- Q" := (@lentails _ _ P Q) (at level 50).
Notation "P //\\ Q" := (@land _ _ P Q) (at level 80).
Notation "P \\// Q" := (@lor _ _ P Q) (at level 85).
Notation "P -->> Q" := (@limpl _ _ P Q) (at level 90).
Notation "'All' x : T , P" := (@lforall _ _ T (fun x => P)) (at level 200).
Notation "'Ex' x : T , P" := (@lexists _ _ T (fun x => P)) (at level 200).
Notation "'All' x , P" := (@lforall _ _ _ (fun x => P)) (at level 200, only parsing).
Notation "'Ex' x , P" := (@lexists _ _ _ (fun x => P)) (at level 200, only parsing).

Instance ILogic_Prop : ILogic Prop :=
{ lentails := fun x y => x -> y
; ltrue := True
; lfalse := False
; land := and
; lor := or
; limpl := fun x y => x -> y
}.

Instance ILogicOk_Prop : ILogicOk _ ILogic_Prop.
Admitted.

Instance ILogic_Fun (T L : Type) (IL : ILogic L) : ILogic (T -> L) :=
{ lentails := fun P Q => forall x, lentails (P x) (Q x)
; ltrue := fun _ => ltrue
; lfalse := fun _ => lfalse
; land := fun P Q x => land (P x) (Q x)
; lor := fun P Q x => lor (P x) (Q x)
; limpl := fun P Q x => limpl (P x) (Q x)
}.

Instance ILogicOk_Fun T L IL (ILO : @ILogicOk L IL): ILogicOk _ (@ILogic_Fun T L IL).
Admitted.

Instance Quant_Prop : Quant Prop :=
{ lforall := fun T P => forall x : T, P x
; lexists := fun T P => exists x : T, P x
}.

Instance QuantOk_Prop : QuantOk _ _ Quant_Prop.
Admitted.

Instance Quant_Fun (T L : Type) (IL : Quant L) : Quant (T -> L) :=
{ lforall := fun T P x => lforall T (fun y => P y x)
; lexists := fun T P x => lexists T (fun y => P y x)
}.

Instance QuantOk_Fun T L IL Q (ILO : @ILogicOk L IL) : QuantOk _ (ILogic_Fun _ _ IL) (Quant_Fun T L Q).
Admitted.
