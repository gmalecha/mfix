(* Gregory's fuel monad. *)


Require Import Lt.
Require Import Omega.

CoInductive M (A : Type) := 
  | Now : A -> M A
  | Later : M A -> M A.

Definition M (A : Type) := nat -> option A.

Definition bind {A B:Type} (f : A -> M B) (ma : M A) : M B :=
  fun n =>
    match (ma n) with
      | None => None
      | Some x =>  f x n
    end.

Definition ret {A:Type} (a:A) : M A :=
  fun n => Some a.

Lemma bind_ret {A B :Type} (f : A -> M B) (a : A) : 
  bind f (ret a) = f a.
Proof.
reflexivity.
Qed.

Axiom funext : forall A B (f g : forall (x:A), B x),
 (forall x, f x = g x) -> f = g.

Lemma ret_bind {A B : Type} (ma : M A) :
  bind ret ma = ma.
Proof.
apply funext. intros x.
   unfold bind. destruct (ma x); reflexivity.
Qed.

Lemma bind_bind {A B C : Type} (ma : M A) (f : A -> M B) (g : B -> M C) :
  bind g (bind f ma) = bind (fun x=> bind g (f x)) ma.
Proof.
apply funext.
intros x.
unfold bind.
destruct (ma x); reflexivity.
Qed.

Definition ap {A B : Type} (mf : M (A -> B)) (ma : M A) : M B :=
  bind (fun f => (bind (fun x => ret (f x)) ma)) mf.

(* This is like Nuprl's fix. (?) *)
Fixpoint mfix1 {A:Type} (f : M A -> M A) (n:nat) : option A :=
  match n with
    | 0 => None
    | S n' => f (fun m => mfix1 f n') n
  end.

Definition mkfact1 (mfact : M (nat -> nat)) : M (nat -> nat) :=  
  bind (fun fact =>
          (ret (fun n =>
                 match n with
                   | 0 => 1
                   | S n' => n * (fact n')
                 end)))
       mfact. 
Definition fact1 := mfix1 mkfact1.

(* But it doesn't work! *)
Eval compute in fact1 20.
Eval compute in ((ap fact1 (ret 5)) 20).

(* This is like the fixpoint operator in Capretta's paper. *)
Fixpoint mfix {A B:Type} (f : (A -> M B) -> A -> M B) (a:A) (n:nat) : option B :=
  match n with
    | 0 => None
    | S n' => f (fun a' _ => mfix f a' n') a n
  end.

Definition mkfact (fact : nat -> M nat) (n : nat) : M nat :=
  match n with 
    | 0 => ret 1
    | S n' => bind (fun m => ret (n*m)) (fact n')
  end.

Definition fact := mfix mkfact.

(* This works as expected. *)
Eval compute in (fact 5 10).
Eval compute in (fact 5 2).

Definition diverge {A:Type} : M A := fun _ => None.

Inductive LTE_option {A}  : option A -> option A -> Prop :=
  | None_LTE :  forall x  , LTE_option None x
  | Some_LTE :  forall (x : A), LTE_option (Some x) (Some x).

Definition LTE {A} (mx : M A) (my : M A) :=
  forall n, LTE_option (mx n) (my n).

Definition monotoneM {A} (r : M A) : Prop := 
  forall n m, n < m -> LTE_option (r n)(r m).

Definition monotoneF {A B} (f : A -> M B) : Prop :=
  forall x, monotoneM (f x).

(* Indexed fixpoint induction, take3 *)
(* Critique:
    - Too low level, you need to unfold ret and bind to get anywhere.
*)
Section IndexedInd.
  Variable (A B : Type).
  Variable P : nat -> (A -> option B) -> Prop.
  Hypothesis P_bot : forall r, P 0 r.
  Variable f : (A -> M B) -> (A -> M B).

(*  Hypothesis f_mono : forall g, monotoneF g -> monotoneF (f g). *)
  Hypothesis Step : forall n (r : A -> M B), (P n (fun x => r x n)) 
                                -> monotoneF r
                                -> (P (S n) (fun x => f r x (S n))).

 Theorem mfixind1 : forall n, P n (fun x => mfix f x n).
   induction n; intros.
     simpl. apply P_bot.   
     simpl. apply Step. assumption.

red. red. intros. destruct (mfix f x n); constructor.
 Qed.
End IndexedInd.

Fixpoint rfact (n : nat) := 
  match n with
   | 0 => 1
   | (S n') => n * (rfact n')
  end.

Example fact_correct : 
 forall m n,  (m > n) -> fact n m = Some (rfact n).
 intros m n.
 pose (H:= mfixind1 nat nat (fun fuel res=> forall arg, (fuel > arg) -> res arg = Some (rfact arg))).
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
       reflexivity. } }
Qed.


(* Indexed fixpoint induction, take2 *)
(* Critique:
    - Too low level, you need to unfold ret and bind to get anywhere.
*)
Section IndexedInd.
  Variable (A B : Type).
  Variable P : nat -> A -> (option B) -> Prop.
  Hypothesis P_bot : forall a r, P 0 a r.
  Variable f : (A -> M B) -> (A -> M B).

(*  Hypothesis f_mono : forall g, monotoneF g -> monotoneF (f g). *)
  Hypothesis Step : forall n r, (forall a, P n a (r a n)) 
                                -> monotoneF r
                                -> (forall a, P (S n) a (f r a (S n))).

 Theorem mfixind1 : forall n a, P n a (mfix f a n).
   induction n; intros a.
     simpl. apply P_bot.   
     simpl. apply Step. assumption.

red. red. intros. destruct (mfix f x n); constructor.
 Qed.
End IndexedInd.

Example fact_terminates : 
 forall m n,  (m > n) -> exists k, fact n m = Some k.
 intros m n.
 pose (H:= mfixind1 nat nat (fun m n res=> (m > n) -> exists k, res = Some k)).
 simpl in H.
 unfold fact.
 apply H.

   intros.  inversion H0.

   intros.
   unfold mkfact.
   destruct a.
   unfold ret. eexists; auto.

   apply lt_S_n in H2.
   apply H0 in H2.
   destruct H2 as [k  H2].
   exists (S a * k).
   unfold bind.
   assert (n0 < S n0) by omega.
   specialize (H1 a n0 (S n0) H3).
   destruct H1.
    congruence.
    inversion H2. unfold ret. reflexivity.
Qed.

Fixpoint rfact (n : nat) := 
  match n with
   | 0 => 1
   | (S n') => n * (rfact n')
  end.

Example fact_correct : 
 forall m n,  (m > n) -> fact n m = Some (rfact n).
 intros m n.
 pose (H:= mfixind1 nat nat (fun m n res=> (m > n) -> res = Some (rfact n))).
 simpl in H.
 unfold fact.
 apply H.

   intros.  inversion H0.

   intros.
   unfold mkfact.
   destruct a.
   unfold ret. reflexivity.

   apply lt_S_n in H2.
   apply H0 in H2.
   (* destruct H2 as [k  H2].
   exists (S a * k). *)
   unfold bind.
   assert (n0 < S n0) by omega.
   specialize (H1 a n0 (S n0) H3).
   destruct H1.
    congruence.
    inversion H2. unfold ret. 
    reflexivity.
Qed.


(* Indexed fixpoint induction, take1 *)
(* Critique:
    - Can not be used to prove termination.
    - Too low level, you need to unfold ret and bind to get anywhere.
    - In fact, can't get anywhere anyway, because it doesn't track monotonicity.
*)
Section IndexedInd.
  Variable (A B : Type).
  Variable P : nat -> A -> (option B) -> Prop.
  Hypothesis P_bot : forall n a, P n a None.
  Variable f : (A -> M B) -> (A -> M B).
  Hypothesis Step : forall n r, (forall a, P n a (r a n)) 
                                -> (forall a, P (S n) a (f r a (S n))).

 Theorem mfixind1 : forall n a, P n a (mfix f a n).
   induction n; intros a.
     simpl. apply P_bot.   
     simpl. apply Step. assumption.
 Qed.
End IndexedInd.

Example fact_terminates : 
 forall m n,  (m > n) -> exists k, fact n m = Some k.
 intros m n.
 pose (H:= mfixind1 nat nat (fun m n res=> (m > n) -> exists k, res = Some k)).
 simpl in H.
 unfold fact.
 apply H.
 
   admit. (* Well, clearly this doesn't work. *)

   intros.
   unfold mkfact.
   destruct a.
   unfold ret. eexists; auto.

   unfold bind. 
   (* also, at this point is seems we want to know that r is monotone. *)
Abort.
