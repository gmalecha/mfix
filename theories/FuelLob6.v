Require Import Lt.
Require Import Omega.
Require Import MFix.Monad.
Require Import MFix.ILogic.
Require Import MFix.Fuel.

Set Implicit Arguments.
Set Strict Implicit.

Section monotone.

  Inductive LTE_option {A}  : option A -> option A -> Prop :=
  | None_LTE :  forall x  , LTE_option None x
  | Some_LTE :  forall (x : A), LTE_option (Some x) (Some x).

  Definition lteM {A} (mx : M A) (my : M A) :=
    forall n, LTE_option (mx n) (my n).

  Definition monotoneM {A} (r : M A) : Prop :=
    forall n m, n < m -> LTE_option (r n) (r m).

  Definition monotoneF {A B} (f : A -> M B) : Prop :=
    forall x, monotoneM (f x).

  Definition lteP {A} (P Q : M A -> Prop) : Prop :=
    forall x y, lteM x y -> P x -> P y.

  Definition ltePF {A B} (P Q : (B -> M A) -> Prop) : Prop :=
    forall v : B,
    forall x y, lteM (x v) (y v) -> P x -> P y.

End monotone.

Section IndexedInd.
  (* Indexed fixpoint induction, take4 *)
  (* Critique:
    - Too low level, you need to unfold ret and bind to get anywhere.
   *)
  Definition FuelProp := fuel -> Prop.

  Definition Inj : Prop -> FuelProp := fun P _ => P.

  Definition atleast (n : nat) : FuelProp :=
    fun fuel => fuel >= n.

  (** ?? **)
  Definition later (fp : FuelProp) : FuelProp :=
    fun n => forall m, m < n -> fp m.

  Definition now {B} (c : M B) (P : B -> FuelProp) : FuelProp :=
    fun fuel => match c fuel with
                  | None => ltrue
                  | Some x => P x fuel
                end.

  Definition nowF {A B} (c : A -> M B) (P : A -> B -> FuelProp) : FuelProp :=
    fun fuel =>
      lforall A (fun x => match c x fuel with
                            | None => ltrue
                            | Some v => P x v fuel
                          end).

  Variable (A B : Type).
  Variable P : (A -> M B) -> FuelProp.
  Hypothesis Pok : forall x y,
                     (forall v, lteM (x v) (y v)) ->
                     (forall n m, n <= m -> P x m -> P y n).
  Variable f : (A -> M B) -> (A -> M B).
  Variable G : FuelProp.

  Hypothesis Step
  : lentails G (limpl (P (mfix f)) (P (f (mfix f)))).

  Theorem mfixind1 : lentails G (P (mfix f)).
  Proof.
    red. simpl. 
    induction x.
    { ?? }
    { simpl in *. unfold satisfiesF in *. simpl in *.
      eapply Step.
      { red. red. intros.
        destruct (mfix f x0 x); constructor. }
      { simpl. auto. } }
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

  Definition Pfact : (nat -> M nat) -> FuelProp :=
    satisfiesF (fun n fn => limpl (atleast n) (Inj (fn = rfact n))).

  Example fact_correct
  : lentails ltrue (Pfact fact).
  Proof.
    eapply mfixind1.
    { unfold mkfact, satisfiesF, later; simpl. intros.
      destruct x0; simpl.
      { reflexivity. }
      { unfold bind.
        destruct x.
        { inversion H0. }
        { specialize (H0 x0).
          assert (x < S x) by omega.
          do 2 red in H. specialize (H x0 x (S x) H1).
          inversion H.
          { subst. rewrite <- H3 in *.
          
        remember (r x0 x). destruct o.
        { simpl. intros. red.


  Example fact_correct :
    forall m,  (m > n) -> fact n m = Some (rfact n).
  intros m n.
  pose (H:= @mfixind1 nat nat (fun fuel res=> forall arg, (fuel > arg) -> res arg = Some (rfact arg))).
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