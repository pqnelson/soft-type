Require Import String.
Require Import Lia.
Require Import List.
Require Import Nat.
Require Import Coq.Vectors.Vector.
Require Export Coq.Arith.Compare_dec.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.FunctionalExtensionality.
From ST Require Import EVarsScratchwork.
Import ListNotations.
Import VectorNotations.
Open Scope string_scope.

(* TODO: re-do the local context so that it meshes with locally nameless
variables correctly. *)

(** * Introduction

We have a couple of helper type classes for recurring functions expected on
constructs, things like [eqb] for boolean equality testing, and [subst] for
substituting a [Term] for a [V]ariable.
*)

(** Exercise #1.
Extend this definition to make [eqb] a proper equivalence relation, specifically:

- [eqb_refl : forall (a : A), eqb a a = true]
- [eqb_sym : forall (a b : A), eqb a b = eqb b a]
- [eqb_trans : forall (a b c : A), eqb a b = eqb b c -> eqb a c]

Exercise #2.
Extend this definition to include
- [eqb_eq : forall (a b : A), eqb a b = true <-> a = b]
- [eqb_neq : forall (a b : A), eqb a b = false <-> a <> b] 
*)
Class Eq A :=
  {
    eqb: A -> A -> bool;
  }.

Fixpoint list_eqb {A : Type} (v1 v2 : list A) (eq : A -> A -> bool) : bool :=
  match v1,v2 with
  | List.nil, List.nil => true
  | List.cons h1 t1, List.cons h2 t2 => andb (eq h1 h2) (list_eqb t1 t2 eq)
  | _, _ => false
  end.

Global Instance natEq : Eq nat := {
  eqb (n1 n2 : nat) := Nat.eqb n1 n2
}.

Global Instance stringEq : Eq string := {
  eqb := String.eqb
}.

(** * Soft Type System

We begin formalizing our soft type system by defining variables and terms,
and the other syntactic constructs. Then we will inductively define the rules
of inference for the soft type system.

** Names and Variables

We use locally nameless encoding of bound variables. Free variables are any
arbitrary [name] instances. Bound variables are de Bruijn indices.
*)

Definition name : Type := string.

Inductive V :=
| FVar : name -> V
| BVar : nat -> V.

Definition is_free (x : V) :=
match x with
| FVar _ => True
| _ => False
end.

Global Instance VEq : Eq V := {
  eqb (x y : V) :=
  match x, y with
  | FVar s1, FVar s2 => eqb s1 s2
  | BVar n1, BVar n2 => eqb n1 n2
  | _, _ => false
  end
}.

Lemma eqb_refl : forall a : V, eqb a a = true.
Proof.
  intros. destruct a.
  - unfold eqb; unfold VEq. simpl; auto. apply String.eqb_refl.
  - unfold eqb; unfold VEq. simpl; auto. apply Nat.eqb_refl.
Qed.

Lemma eq_dec : forall a b : V, {a = b} + {a <> b}.
Proof. decide equality.
  try (left; reflexivity); try (right; congruence).
  - apply string_dec.
  - decide equality.
Defined.

Theorem easy : forall p q:Prop, (p->q)->(~q->~p).
Proof.
  intros. intro. apply H0. apply H. exact H1. 
Qed.

Lemma PPNN : forall p:Prop, p -> ~ ~ p.
Proof.
  unfold not; intros; elim (classic p); auto.
Qed.

Theorem contra  : forall p q:Prop, (~q->~p) -> (p->q).
Proof. intros. 
  apply (easy (~q) (~p)) in H.
  apply NNPP in H. assumption. apply PPNN; assumption. 
Qed.

Lemma eqb_eq : forall a b : V, eqb a b = true <-> a = b.
Proof.
  intros. split.
  - intros. destruct a.
  + unfold eqb in H; unfold VEq in H. destruct b. apply String.eqb_eq in H.
    rewrite H; reflexivity. discriminate H.
  + unfold eqb in H; unfold VEq in H. destruct b. discriminate.
    apply Nat.eqb_eq in H.
    rewrite H; reflexivity.
  - intros. rewrite H; apply eqb_refl.
Qed.

(** We now need to handle [lift]-ing a bound variable. Since this will occur
wherever a [BVar] can occur (and wherever a [Term] may occur), we will use a
typeclass to handle this. *)

Class Lift A := {
  lift : nat -> nat -> A -> A;
  unlift : nat -> nat -> A -> A
}.

Definition shift {A : Type} `{Lift A} (a : A) : A := lift 0 1 a.
Definition unshift {A : Type} `{Lift A} (a : A) : A := unlift 0 1 a.

Global Instance VLift : Lift V := {
  lift (cutoff depth : nat) (x : V) :=
  match x with
  | FVar nm => x
  | BVar n => if (* lt_dec n cutoff *) Nat.ltb n cutoff then x else BVar (n+depth)
  end;
  unlift (cutoff depth : nat) (x : V) :=
  match depth with
  | 0 => x
  | S d' => match x with
            | FVar nm => x
            | BVar n => if Nat.ltb n cutoff then x 
                        else BVar (n - depth)
            end
  end
}.

(** Lemma: [lift 0 0] is the identity transformation.
Lemma zero_lift_is_id0 : forall (n : nat), lift 0 0 (BVar n) = (BVar n).
Proof.
  intros. simpl. auto.
Qed.
Lemma zero_lift_is_id : forall (x : V), lift 0 0 x = x.
Proof.
  intros. destruct x.
  - simpl; auto.
  - simpl; auto.
Qed.
 *)


Lemma zero_lift_is_id :  lift 0 0 = id.
Proof.
  apply functional_extensionality.
  intros. destruct x.
  - simpl; auto.
  - simpl; auto. assert (n + 0 = n). { lia. } rewrite H. unfold id. reflexivity.
Qed.


Theorem case_lift_is_not_id : forall (i k n : nat), n >= k -> lift k i (BVar n) = BVar (n+i).
Proof.
  intros. simpl. bdestruct (Nat.ltb n k).
  - contradict H. lia.
  - reflexivity.
Qed.

Theorem case_lift_is_id : forall (i k n : nat), n < k -> lift k i (BVar n) = BVar (n).
Proof.
  intros. simpl. bdestruct (Nat.ltb n k).
  - reflexivity.
  - contradict H. lia.
Qed.

Corollary bigger_lift_is_id : forall (i k1 k2 : nat) (x : V), k1 < k2 -> lift k1 i x = x -> lift k2 i x = x.
Proof.
  intros. simpl. destruct x.
  - reflexivity.
  - bdestruct (Nat.ltb n k1).
  + apply case_lift_is_id; simpl; auto. lia.
  + apply case_lift_is_not_id with (i := i) in H1 as H2.
    rewrite H0 in H2. inversion H2. rewrite <- H4. rewrite <- H4.
    apply Tauto.if_same.
Qed.

Theorem lift_comp : forall (c d1 d2 : nat) (x : V),
  lift c d1 (lift c d2 x) = lift c (d1 + d2) x.
Proof.
  intros.
  destruct x as[|n].
  - simpl; auto. (* le_gt_dec n m: {n <= m} + {n > m} *)
  - assert({c <= n} + {c > n}). apply le_gt_dec. destruct H.
  + rewrite case_lift_is_not_id. rewrite case_lift_is_not_id. rewrite case_lift_is_not_id.
    assert (n + d2 + d1 = n + (d1 + d2)). { lia. } rewrite H; reflexivity.
    assumption. lia. assumption.
  + rewrite case_lift_is_id. rewrite case_lift_is_id. rewrite case_lift_is_id. reflexivity.
    assumption. assumption. assumption.
Qed.

Theorem lift_seq : forall (c d1 d2 : nat) (x : V),
  d1 > 0 -> lift (S c) d2 (lift c d1 x) = lift c (d2 + d1) x.
Proof.
  intros.
  destruct x as [|n].
  - simpl; auto.
  - assert({c <= n} + {c > n}). apply le_gt_dec. destruct H0.
  + rewrite case_lift_is_not_id. 
    rewrite case_lift_is_not_id.
    rewrite case_lift_is_not_id.
    rewrite Plus.plus_assoc_reverse; rewrite (Nat.add_comm d1 d2). 
    reflexivity.
    assumption. lia. assumption.
  + rewrite case_lift_is_id. rewrite case_lift_is_id. rewrite case_lift_is_id. reflexivity.
    assumption. lia. assumption.
Qed.

(* WTS: (lift (S m) 1 (lift 1 m t)) = lift 1 (S m) t *)
Corollary variadic_quantifier_lift_seq_general :
  forall (c1 c2 m : nat) (x : V),
  c2 + m = c1 -> (lift (c2 + m) 1 (lift c1 m x)) = lift c1 (S m) x.
Proof.
  intros. destruct x.
  - simpl; auto.
  - assert({c1 <= n} + {c1 > n}). apply le_gt_dec. destruct H0.
  + rewrite case_lift_is_not_id. 
    rewrite case_lift_is_not_id.
    rewrite case_lift_is_not_id.
    assert (n + m + 1 = n + S m). lia. rewrite H0. 
    reflexivity. assumption.
    lia. lia.
  + rewrite case_lift_is_id.
    rewrite case_lift_is_id.
    rewrite case_lift_is_id. reflexivity. assumption. lia. lia.
Qed.

(* lift (S (S m)) 1 (lift 2 m A)) = Exists (lift 2 (S m) A) *)
Corollary variadic_quantifier_lift_seq :
  forall (m k : nat) (x : V),
  k > 0 -> (lift (k + m) 1 (lift k m x)) = lift k (S m) x.
Proof.
  intros. destruct x.
  - simpl; auto.
  - assert({k <= n} + {k > n}). apply le_gt_dec. destruct H0.
  + rewrite case_lift_is_not_id. 
    rewrite case_lift_is_not_id.
    rewrite case_lift_is_not_id.
    assert (n + m + 1 = n + S m). lia. rewrite H0. 
    reflexivity. assumption.
    lia. lia.
  + rewrite case_lift_is_id.
    rewrite case_lift_is_id.
    rewrite case_lift_is_id. reflexivity. assumption. lia. lia.
Qed.

(* WTS: (lift (S m) 1 (lift 1 m t)) = lift 1 (S m) t *)
Corollary variadic_quantifier_lift_seq0 :
  forall (m : nat) (x : V),
  (lift (S m) 1 (lift 1 m x)) = lift 1 (S m) x.
Proof.
  intros. destruct x.
  - simpl; auto.
  - assert({1 <= n} + {1 > n}). apply le_gt_dec. destruct H.
  + rewrite case_lift_is_not_id. 
    rewrite case_lift_is_not_id.
    rewrite case_lift_is_not_id.
    assert (n + m + 1 = n + S m). lia. rewrite H. 
    reflexivity. assumption.
    lia. lia.
  + rewrite case_lift_is_id.
    rewrite case_lift_is_id.
    rewrite case_lift_is_id. reflexivity. assumption. lia. lia.
Qed.
  

Example shift_really_shifts : forall (n : nat), shift (BVar n) = BVar (n + 1).
Proof.
  trivial.
Qed.