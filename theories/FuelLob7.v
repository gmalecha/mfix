Require Import Lt.
Require Import Omega.
Require Import Relation_Definitions.
Require Import RelationClasses.
Require Import Morphisms.
Require Import MFix.Monad.
Require Import MFix.ILogic.
Require Import MFix.Fuel.

Set Implicit Arguments.
Set Strict Implicit.

Section monotone.

  Inductive LTE_option {A}  : option A -> option A -> Prop :=
  | None_LTE :  forall x  , LTE_option None x
  | Some_LTE :  forall (x : A), LTE_option (Some x) (Some x).

  Definition lteM {A} : M A -> M A -> Prop :=
    (le ==> LTE_option)%signature.

  Definition lteMF {A B} : relation (B -> M A) :=
    pointwise_relation _ (@lteM A).

  Definition monotoneM {A} : M A -> Prop :=
    Proper lteM.

  Definition monotoneF {A B} : (A -> M B) -> Prop :=
    Proper lteMF.

  Definition lteP {A} : relation (M A -> Prop) :=
    (lteM ==> Basics.impl)%signature.

  Definition ltePF {A B} : relation ((B -> M A) -> Prop) :=
    (pointwise_relation _ (@lteM _) ==> Basics.impl)%signature.

  Lemma monotoneF_mfix
  : forall T U (f : (T -> M U) -> _),
      (Proper (lteMF ==> lteMF) f) ->
      monotoneF (mfix f).
  Proof.
    unfold monotoneF, monotoneM.
    intros. red. red. red. red. red.
    intros a n; revert a.
    induction n.
    { simpl in *. intros. constructor. }
    { intros. destruct y.
      { exfalso. omega. }
      { simpl. unfold lteMF, lteM in H.
        eapply H. 2: omega.
        intros.
        red. intros. red. intros.
        eapply IHn. omega. } }
  Qed.

  Lemma Proper_mfix
  : forall T U,
      Proper ((lteMF ==> lteMF) ==> lteMF) (@mfix T U).
  Proof.
    intros.
    repeat red. intros. revert a.
    generalize dependent y0.
    induction x0.
    { intros. simpl. constructor. }
    { intros. destruct y0.
      { exfalso. omega. }
      { simpl. eapply H; eauto.
        repeat red; intros.
        eapply IHx0. omega. } }
  Qed.

(*
  Instance Refl_lteM {T} : forall x, Proper Reflexive (@lteM T).
  Proof.
    red. intro. red. intros.
    destruct (x n); try constructor. (** TODO: Not true! **)
    (** TODO: cleaner proof **)
  Admitted.
*)


End monotone.

Section IndexedInd.
  Definition FuelProp := fuel -> Prop.

  Definition Inj : Prop -> FuelProp := fun P f => f > 0 -> P.

  Definition atleast (n : nat) : FuelProp :=
    fun fuel => fuel >= n.

  (** ?? **)
  Definition later (fp : FuelProp) : FuelProp :=
    fun n => forall m, m < n -> fp m.

  Definition laterF {T} (fp : T -> FuelProp) : T -> FuelProp :=
    fun v => later (fp v).

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

  Definition FuelPropOk (P : FuelProp) : Prop :=
    P 0 /\ forall n m, m <= n -> P n -> P m.

  Section unfold.
    Context {A B : Type}.
    Variable P : (A -> M B) -> FuelProp.
    Variable f : (A -> M B) -> A -> M B.

    Hypothesis Proper_f : Proper (lteMF ==> lteMF) f.
    Hypothesis Pok : forall x y,
                       (forall v, lteM (x v) (y v)) ->
                       (forall n m, n <= m -> P y n -> P x m).
    Variable Pok' : FuelPropOk (P (mfix f)).

    Theorem mfix_unfold
    : lentails (laterF P (f (mfix f))) (P (mfix f)).
    Proof.
      simpl. unfold laterF, later.
      induction x.
      { simpl; intros.
        destruct Pok'. auto. }
      { intros. eapply Pok.
        2: instantiate (1 := x); auto.
        2: eapply IHx.
        intros. eapply Proper_mfix. eapply Proper_f.
        intros. eapply H. omega. }
    Qed.
  End unfold.

(*
  Context {A : Type}.
  Variable P : M A -> FuelProp.
(*  Variable G : FuelProp. *)
  Variable val : M A.

  Hypothesis Pok0 : forall val, P val 0.
  Hypothesis Pok : forall n m val, m <= n -> P val n -> P val m.

  Hypothesis Step
  : lentails ltrue (limpl ((laterF P) val) (P val)).

  Theorem lob : lentails ltrue (P val).
  Proof.
    red. simpl.
    induction x.
    { auto. }
    { simpl in *. unfold laterF, later in *.
      intros. eapply Step; auto.
      intros.
      eapply Pok. instantiate (1 := x). omega. eapply IHx. trivial. }
  Qed.
*)

  Theorem lob : forall P, FuelPropOk P -> lentails (later P) P -> lentails ltrue P.
  Proof.
    intros.
    red. simpl.
    induction x.
    { destruct H. auto. }
    { simpl in *. unfold later in *.
      intros.
      eapply H0. intros.
      destruct H. eapply H3. 2: eapply IHx; auto. omega. }
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

  Definition Pfact (f : nat -> M nat) : FuelProp :=
    lforall _ (fun n : nat => now (f n) (fun val => Inj (val = rfact n))).
(*    satisfiesF (fun n fn => limpl (atleast n) (Inj (fn = rfact n))). *)

  Lemma FuelPropOk_lforall
  : forall T P,
      (forall x : T, FuelPropOk (P x)) ->
      FuelPropOk (lforall _ P).
  Proof.
    unfold FuelPropOk. simpl in *. intuition.
    { specialize (H x). intuition. }
    { specialize (H x). specialize (H1 x). intuition. eauto. }
  Qed.

  Lemma FuelPropOk_ltrue
  : FuelPropOk ltrue.
  Proof.
    unfold FuelPropOk. simpl in *. intuition.
  Qed.

  Lemma FuelPropOk_Inj
  : forall P, FuelPropOk (Inj P).
  Proof.
    unfold FuelPropOk, Inj. intuition. inversion H.
  Qed.

  Lemma FuelPropOk_now
  : forall T (c : M T) P, monotoneM c -> (forall b, FuelPropOk (P b)) -> FuelPropOk (now c P).
  Proof.
    unfold FuelPropOk, now. intuition.
    { destruct (c 0); simpl; eauto.
      specialize (H0 t). intuition. }
    { destruct H1. auto.
      red in H.
      assert (m <= S m0) by omega.
      specialize (H m (S m0) H3).
      destruct H; simpl; auto.
      specialize (H0 x). intuition.
      eapply H4. 2: eapply H2. omega. }
  Qed.

  (** NOTE: False is not ok which is a problem **)

  Lemma FuelPropOk_Pfact : forall x, monotoneF x -> FuelPropOk (Pfact x).
  Proof.
    unfold Pfact. intros.
    eapply FuelPropOk_lforall.
    intros.
    eapply FuelPropOk_now.
    eapply H.
    intros. apply FuelPropOk_Inj.
  Qed.

  Lemma lteM_ret T (t : T) : lteM (ret t) (ret t).
  Proof.
    constructor.
  Qed.

  Lemma lteM_bind T U (c c' : M T) (f f' : T -> M U)
  : lteM c c' -> lteMF f f' -> lteM (bind c f) (bind c' f').
  Proof.
    intros.
    unfold bind. red. red. intros.
    specialize (H x y H1).
    destruct H. constructor.
    apply H0. auto.
  Qed.

  Lemma monotoneF_fact : monotoneF fact.
  Proof.
    apply monotoneF_mfix.
    unfold mkfact.
    red. red. intros. red. red. intros.
    destruct a. apply lteM_ret.
    eapply lteM_bind. apply H.
    red. red. intros. apply lteM_ret.
  Qed.

  Opaque lentails lforall.

  Example fact_correct
  : lentails ltrue (Pfact fact).
  Proof.
    generalize monotoneF_fact; intro.
    eapply lob.
    { eapply FuelPropOk_Pfact; auto. }
    { unfold Pfact, fact.
      set (P := fun x => lforall nat
           (fun n : nat =>
            now (x n) (fun val : nat => Inj (val = rfact n)))).
      change (lentails (later (P (mfix mkfact))) (P (mfix mkfact))).
      etransitivity. 2: eapply mfix_unfold.
      3: eapply FuelPropOk_Pfact; auto.
      unfold laterF.
      unfold P.
      Lemma lentails_later
      : forall P Q,
          lentails P Q ->
          lentails (later P) (later Q).
      Proof.
      Admitted.
      eapply lentails_later.
      Lemma lentails_lforall
      : forall T (P Q : T -> FuelProp),
          (forall x, lentails (P x) (Q x)) ->
          lentails (lforall _ P) (lforall _ Q).
      Proof.
      Admitted.
      eapply lentails_lforall; intros.
      unfold mkfact at 2.
      destruct x; simpl.
      { Lemma now_ret : forall T (x : T) P, now (ret x) P = P x.
        Proof.
          intros. compute. reflexivity. (** eta **)
        Qed.
        rewrite now_ret.
        admit. }
      { Lemma now_bind
        : forall T U (x : M T) (f : T -> M U) P,
            now (bind x f) P = ?
                           
      
      


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