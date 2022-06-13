Require Import String.
Require Import Lia.
Require Import List.
Require Import Nat.
Require Import Coq.Vectors.Vector.
Require Import Coq.Vectors.VectorEq.
Require Import Coq.Arith.Bool_nat.
Require Export Coq.Arith.Compare_dec.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.FunctionalExtensionality.
Require Export RelationClasses.
Require Export Morphisms.
Require Import Program.
From ST Require Import EVarsScratchwork.
From ST Require Import Vector.
From ST Require Export Logic.V Logic.Term SoftType.Attribute.
Import ListNotations.
Import VectorNotations.
Open Scope string_scope.

(** ** Adjectives

An adjective is either a "positive [Attribute]" or a "negative [Attribute]".
*)

Inductive Adjective : Type :=
| Pos : Attribute -> Adjective
| Neg : Attribute -> Adjective.

Global Instance EqAdjective : Eq Adjective := {
  eqb (A1 A2 : Adjective) :=
  match A1,A2 with
  | Pos a1, Pos a2 => eqb a1 a2
  | Neg a1, Neg a2 => eqb a1 a2
  | _, _ => false
  end
}.

Global Instance substAdj : Subst Adjective := {
  subst (x : V) (t : Term) (alpha : Adjective) :=
  match alpha with
  | Pos a => Pos (subst x t a)
  | Neg a => Neg (subst x t a)
  end
}.

Global Instance liftAdj : Lift Adjective :=
{
  lift (c d : nat) (alpha : Adjective) :=
  match alpha with
  | Pos a => Pos (lift c d a)
  | Neg a => Neg (lift c d a)
  end;
  unlift (c d : nat) (alpha : Adjective) :=
  match alpha with
  | Pos a => Pos (unlift c d a)
  | Neg a => Neg (unlift c d a)
  end
}.

Global Instance EnumerateEVarsAdjective : EnumerateEVars Adjective := {
list_evars adj := match adj with
| Pos a => list_evars a
| Neg a => list_evars a
end
}.

Theorem list_evars_adjective_sorted : forall (A : Adjective),
  sorted (list_evars A).
Proof. intros. destruct A.
  - assert(list_evars (Pos a) = list_evars a). { simpl; auto. }
    rewrite H.
    apply list_evars_attribute_sorted.
  - assert(list_evars (Neg a) = list_evars a). { simpl; auto. }
    rewrite H.
    apply list_evars_attribute_sorted.
Qed.