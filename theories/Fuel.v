Require Import Lt.
Require Import Omega.
Require Import MFix.Monad.
Require Import MFix.ILogic.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Definition fuel := nat.

Definition M (A : Type) := fuel -> option A.

Definition bind {A B:Type} (ma : M A) (f : A -> M B) : M B :=
  fun n =>
    match (ma n) with
      | None => None
      | Some x =>  f x n
    end.

Definition ret {A:Type} (a:A) : M A :=
  fun n => Some a.

Instance Monad_Fuel : Monad M :=
{ mbind := @bind
; mret := @ret
}.


Lemma bind_ret {A B :Type} (f : A -> M B) (a : A) :
  bind (ret a) f = f a.
Proof.
reflexivity.
Qed.

Axiom funext : forall A B (f g : forall (x:A), B x),
 (forall x, f x = g x) -> f = g.

Lemma ret_bind {A B : Type} (ma : M A) :
  bind ma ret = ma.
Proof.
apply funext. intros x.
   unfold bind. destruct (ma x); reflexivity.
Qed.

Lemma bind_bind {A B C : Type} (ma : M A) (f : A -> M B) (g : B -> M C) :
  bind (bind ma f) g = bind ma (fun x=> bind (f x) g).
Proof.
apply funext.
intros x.
unfold bind.
destruct (ma x); reflexivity.
Qed.

Definition ap {A B : Type} (mf : M (A -> B)) (ma : M A) : M B :=
  bind mf (fun f => (bind ma (fun x => ret (f x)))).

Inductive LTE_option {A}  : option A -> option A -> Prop :=
  | None_LTE :  forall x  , LTE_option None x
  | Some_LTE :  forall (x : A), LTE_option (Some x) (Some x).

Definition LTE {A} (mx : M A) (my : M A) :=
  forall n, LTE_option (mx n) (my n).

Definition monotoneM {A} (r : M A) : Prop :=
  forall n m, n < m -> LTE_option (r n)(r m).

Definition monotoneF {A B} (f : A -> M B) : Prop :=
  forall x, monotoneM (f x).

Definition diverge {A:Type} : M A := fun _ => None.

(* This is like the fixpoint operator in Capretta's paper. *)
Section mfix.
  Context {A B:Type} (f : (A -> M B) -> A -> M B).

  Fixpoint mfix (a:A) (n:nat) : option B :=
    match n with
      | 0 => None
      | S n' => f (fun a' _ => mfix a' n') a n
    end.
End mfix.

Definition Terminates {A} (m : M A) : Type :=
{ n : nat & m n <> None }.

Section purify.
  Variable A : Type.
  Variable c : M A.
  Variable Term_c : Terminates c.

  Definition purify : A :=
    match Term_c with
      | existT n pf =>
        match c n as z return z <> None -> A with
          | None => fun pf => match pf eq_refl with end
          | Some val => fun _ => val
        end pf
    end.
End purify.

Section purifyF.
  Variable A B : Type.
  Variable c : A -> M B.
  Variable Term_c : forall x, Terminates (c x).

  Definition purifyF (a : A) : B :=
    match Term_c a with
      | existT n pf =>
        match c a n as z return z <> None -> B with
          | None => fun pf => match pf eq_refl with end
          | Some val => fun _ => val
        end pf
    end.
End purifyF.