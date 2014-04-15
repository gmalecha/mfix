Require Import Lt.
Require Import Omega.
Require Import MFix.Monad.
Require Import MFix.ILogic.
Require Import MFix.Fuel.
Require Import MFix.FuelLob3.

Set Implicit Arguments.
Set Strict Implicit.

Section logical.
  Variable T : Type.
  Variable ILogic_T : ILogic T.
  Variable Quant_T : Quant T.

  Variables A B : Type.

  Definition At (a : A) (P : B -> T) : (A -> B) -> T :=
    fun f => P (f a).
  Definition At' (P : A -> B -> T) : (A -> B) -> T :=
    fun f => lforall _ (fun x => P x (f x)).

End logical.

Section IndexedInd.
  (* Indexed fixpoint induction, take4 *)
  (* Critique:
    - Too low level, you need to unfold ret and bind to get anywhere.
   *)
  Definition FuelProp := fuel -> Prop.

  Definition Inj : Prop -> FuelProp := fun P _ => P.

  Definition atleast (n : nat) : FuelProp :=
    fun fuel => fuel >= n.

  (** |> P |- P  ->  P
   ** P |- |> P
   ** P must hold for divergence
   **)
  Definition later (fp : FuelProp) : FuelProp :=
    fun n => forall m, m < n -> fp m.

  Definition satisfies {B} (P : B -> FuelProp) (c : M B) : FuelProp :=
    fun fuel => match c fuel with
                  | None => ltrue
                  | Some x => P x fuel
                end.
(*
  Definition satisfiesF {A B} (P : A -> B -> FuelProp) (c : A -> M B) : FuelProp :=
    fun fuel =>
      forall x,
        match c x fuel with
          | None => ltrue
          | Some v =>
            P x v fuel
        end.
*)

  Definition satisfiesF {A B} (P : A -> B -> FuelProp) : (A -> M B) -> FuelProp :=
    At' _ (fun a => satisfies (P a)).

  Theorem satisfiesF_satisfiesF'
  : forall A B (P : A -> B -> FuelProp) c,
      forall f, (satisfiesF P c f <-> satisfiesF' P c f).
  Proof. reflexivity. Qed.



  Variable (A B : Type).
  Variable P : A -> B -> FuelProp.
  Variable f : (A -> M B) -> (A -> M B).


  Hypothesis Step
  : forall (r : A -> M B),
      monotoneF r ->
      lentails (satisfiesF (fun x y => later (P x y)) r) (satisfiesF P (f r)).

  Theorem mfixind : lentails ltrue (satisfiesF P (mfix f)).
  Proof.
    red. simpl. intros x [].
    induction x.
    { compute. auto. }
    { simpl in *. unfold satisfiesF in *. simpl in *.
      eapply Step.
      { red. red. intros.
        destruct (mfix f x0 x); constructor. }
      { simpl. auto. } }
  Qed.

(** NOTE: This is not the same because it requires you to only
 ** prove for a certain amount of fuel
  Theorem mfixind
  : (lforall _ (fun r : A -> M B =>
             Inj (monotoneF r) -->>
             (satisfiesF (fun x y => later (P x y)) r -->>
              satisfiesF P (f r))))
    |-- satisfiesF P (mfix f).
**)
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

  Definition TerminatesWith {T} (n : fuel) (P : T -> Prop) : M T -> FuelProp :=
    fun c fuel => fuel >= n ->
                  match c fuel with
                    | None => False
                    | Some val => P val
                  end.
  Definition IfTerminates {T} (P : T -> Prop) : M T -> FuelProp :=
    fun c fuel => match c fuel with
                    | None => True
                    | Some val => P val
                  end.

  (** This is the same as the statement that we proved in FuelLob3 except that
   ** it uses >= rather than just >
   **)
  Definition Pfact : (nat -> M nat) -> FuelProp :=
    lforall _ (fun n => At n (TerminatesWith (S n) (fun result => result = rfact n))).

  Eval cbv beta iota zeta delta
       [ Pfact lforall  Quant_Fun Quant_Prop At TerminatesWith Inj lentails ltrue ILogic_Prop ILogic_Fun ]
    in lentails ltrue (Pfact fact).

  Example fact_correct
  : lentails ltrue (Pfact fact).
  Proof.
    unfold Pfact. simpl. intros. clear H.
    red. red.
    generalize @mfixind. simpl. unfold satisfiesF. simpl.
    intros.
    unfold fact.
    apply (fun b d => @mfixind1' nat nat (fun fuel f =>
                                            fuel >= S x0 ->
                                            match f x0 with
                                              | None => False
                                              | Some val => val = rfact x0
                                            end) b mkfact d x).
    { clear. intros.  inversion H. }
    { intros. unfold mkfact.
      
    

    { unfold mkfact, satisfiesF, later; simpl. intros.
      destruct x0; simpl.
      { reflexivity. }
      { unfold bind.
        specialize (H0 x0).
        destruct (r x0 x); auto.
        simpl in *. destruct x; intuition.
        red. assert (atleast x0 x). red. red in H1. omega.
        apply H0 in H2.
        red in H2. subst. reflexivity. } }


(** Old version, this isn't correct because it doesn't imply termination
  Definition Pfact : (nat -> M nat) -> FuelProp :=
     satisfiesF (fun n fn => limpl (atleast n) (Inj (fn = rfact n)) f).

  Example fact_correct
  : lentails ltrue (Pfact fact).
  Proof.
    eapply mfixind.
    { unfold mkfact, satisfiesF, later; simpl. intros.
      destruct x0; simpl.
      { reflexivity. }
      { unfold bind.
        specialize (H0 x0).
        destruct (r x0 x); auto.
        simpl in *. destruct x; intuition.
        red. assert (atleast x0 x). red. red in H1. omega.
        apply H0 in H2.
        red in H2. subst. reflexivity. } }
  Qed.
**)

  Theorem factTerminates : forall n, Terminates (fact n).
  Proof.
    intros. exists (S n).
    generalize (@fact_correct (S n) I n).
    destruct (fact n (S n)).
    abstract (rewrite fact_correct; auto; congruence).
  Defined.

  Definition pure_fact : nat -> nat :=
    Eval compute in purifyF fact (@factTerminates).

  (** pure_fact is a little bit slower... **)
  Time Eval vm_compute in pure_fact 7.
  Time Eval vm_compute in rfact 7.

End ExampleFactorial.