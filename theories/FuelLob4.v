Require Import Lt.
Require Import Omega.
Require Import MFix.Monad.
Require Import MFix.ILogic.
Require Import MFix.Fuel.

Set Implicit Arguments.
Set Maximal Implicit Insertion.


Instance ILogic_Fuel P (IL : ILogic P) : ILogic (fuel -> P) :=
{ lentails := fun P Q => forall f, lentails (P f) (Q f)
; ltrue := fun _ => ltrue
; lfalse := fun _ => lfalse
; land := fun P Q n => land (P n) (Q n)
; lor := fun P Q n => lor (P n) (Q n)
; limpl := fun P Q n => limpl (P n) (Q n)
}.

Section IndexedInd.
  (* Indexed fixpoint induction, take4 *)
  (* Critique:
    - Too low level, you need to unfold ret and bind to get anywhere.
   *)
  Definition FuelProp := fuel -> Prop.

  Definition later (fp : FuelProp) : FuelProp :=
    fun n => match n with
               | 0 => ltrue
               | S n => fp n
             end.

  Definition satisfies {B} (c : M B) (P : option B -> FuelProp) : FuelProp :=
    fun fuel => match fuel with
                  | 0 => ltrue
                  | _ => P (c fuel) fuel
                end.
  Definition satisfiesF {A B} (c : A -> M B) (P : (A -> option B) -> FuelProp) : FuelProp :=
    fun fuel => match fuel with
                  | 0 => ltrue
                  | _ =>
                    P (fun x => c x fuel) fuel
                end.

  Variable (A B : Type).
  Variable P : (A -> option B) -> FuelProp.
  Variable f : (A -> M B) -> (A -> M B).

  Hypothesis Step
  : forall (r : A -> M B),
      monotoneF r ->
      lentails (later (satisfiesF r P)) (satisfiesF (f r) P).

  Theorem mfixind1 : lentails ltrue (satisfiesF (mfix f) P).
    specialize (fun z =>
                  @mfixind1' A B (fun fuel g =>
                                    satisfiesF (fun x _ => g x) P
                                               fuel)
                             z f).
    intros. intro. intro.
    eapply H; clear H.
    { red. simpl. auto. }
    { intros. simpl in *.
      specialize (fun r mR => @Step r mR (S n)).
      simpl in *. apply Step. assumption. clear - H. apply H. }
  Qed.
End IndexedInd.


Module ExampleFactorial.

  Definition mkfact (fact : nat -> M nat) (n : nat) : M nat :=
    match n with
      | 0 => ret 1
      | S n' => bind (fact n') (fun m => ret (n*m))
    end.

  Definition fact := mfix mkfact.

  (* This works as expected. *)
  Eval compute in (fact 5 10).
  Eval compute in (fact 5 2).

  Fixpoint rfact (n : nat) :=
    match n with
      | 0 => 1
      | (S n') => n * (rfact n')
    end.

  Example fact_correct :
    forall m n,  (m > n) -> fact n m = Some (rfact n).
  intros m n.
  pose (H:= @mfixind1' nat nat (fun fuel res=> forall arg, (fuel > arg) -> res arg = Some (rfact arg))).
  simpl in H.
  unfold fact.
  apply H.
  { intros.  inversion H0. }
  { intros.
    unfold mkfact.
    destruct arg.
    { unfold ret. reflexivity. }
    { apply lt_S_n in H2.
      apply H0 in H2.
      unfold bind.
      assert (n0 < S n0) by omega.
      specialize (H1 arg n0 (S n0) H3).
      destruct H1; try congruence.
      { inversion H2. unfold ret.
        reflexivity. } } }
  Qed.

  Theorem factTerminates : forall n, Terminates (fact n).
  intros. exists (S n).
  abstract (rewrite fact_correct; auto; congruence).
  Defined.

  Definition pure_fact : nat -> nat :=
    Eval compute in purifyF fact (@factTerminates).

  (** pure_fact is a little bit slower... **)
  Time Eval vm_compute in pure_fact 7.
  Time Eval vm_compute in rfact 7.

End ExampleFactorial.