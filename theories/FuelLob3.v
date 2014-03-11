Require Import Lt.
Require Import Omega.
Require Import MFix.Monad.
Require Import MFix.ILogic.
Require Import MFix.Fuel.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Section IndexedInd.
  (* Indexed fixpoint induction, take3 *)
  (* Critique:
    - Too low level, you need to unfold ret and bind to get anywhere.
   *)
  Variable (A B : Type).
  Variable P : nat -> (A -> option B) -> Prop.
  Hypothesis P_bot : forall r, P 0 r.
  Variable f : (A -> M B) -> (A -> M B).

(* TODO: I still find it a little strange that we don't need this...
  Hypothesis f_mono : forall g, monotoneF g -> monotoneF (f g).
 *)
  Hypothesis Step : forall n (r : A -> M B), (P n (fun x => r x n))
                                -> monotoneF r
                                -> (P (S n) (fun x => f r x (S n))).

  Theorem mfixind1' : forall n, P n (fun x => mfix f x n).
    induction n; intros.
    { simpl. apply P_bot. }
    { simpl. apply Step.
      { assumption. }
      { red. red. intros. destruct (mfix f x n); constructor. } }
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