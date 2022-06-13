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
From ST Require Export Logic.V Logic.Term.
Import ListNotations.
Import VectorNotations.
Open Scope string_scope.
(** ** Radix Types

These are "mother types". In full Mizar, this is either a [Mode] or a [Struct] 
or a set (what we call [Ast]).
*)
Inductive Radix : Type :=
| Ast : Radix
| Mode : forall (n : nat), name -> Vector.t Term n -> Radix.

Definition arity (R : Radix) : nat :=
  match R with
  | Ast => 0
  | Mode n _ _ => n
  end.

Definition radix_is_mode (R : Radix) : Prop :=
  match R with
  | Mode _ _ _ => True
  | _ => False
  end.

Fixpoint vectors_eqb {A : Type} {n1 n2} (v1 : Vector.t A n1) (v2 : Vector.t A n2) (eq : A -> A -> bool) : bool :=
match v1, v2 with
| Vector.nil _, Vector.nil _ => true
| Vector.cons _ h1 k1 t1,  Vector.cons _ h2 k2 t2 => if andb (eqb k1 k2) (eq h1 h2) then (vectors_eqb t1 t2 eq) else false
| _, _ => false
end.

Global Instance EqRadix : Eq Radix := {
  eqb (R1 R2 : Radix) :=
  match R1,R2 with
  | Ast, Ast => true
  | Mode n1 s1 args1, Mode n2 s2 args2 => if andb (eqb n1 n2) (eqb s1 s2) then
    vectors_eqb args1 args2 term_eqb
    else false
  | _, _ => false
  end
}.

Global Instance substRadix : Subst Radix :=
{
  subst (x : V) (t : Term) (R : Radix) :=
  match R with
  | Ast => R
  | Mode n s args => Mode n s (Vector.map (fun (arg : Term) => subst x t arg) args)
  end
}.

Global Instance liftRadix : Lift Radix :=
{
  lift (c d : nat) (R : Radix) :=
  match R with
  | Ast => R
  | Mode n s args => Mode n s (Vector.map (fun (a : Term) => lift c d a) args)
  end;
  unlift (c d : nat) (R : Radix) :=
  match R with
  | Ast => R
  | Mode n s args => Mode n s (Vector.map (fun (a : Term) => unlift c d a) args)
  end
}.

Global Instance EnumerateEVarsRadix : EnumerateEVars Radix := {
list_evars R := match R with
| Ast => []%list
| Mode n s args => Vector.fold_left (fun l' => fun (arg : Term) => insert_merge (list_evars arg) l') []%list args
end
}.

Theorem list_evars_radix_sorted : forall (R : Radix),
  sorted (list_evars R).
Proof.
  intros.
  induction R.
  - simpl; auto. apply sorted_nil.
  - rename t into args.
    unfold list_evars; unfold EnumerateEVarsRadix.
    apply insert_merge_vector_fold_sorted2.
    apply sorted_nil.
Qed.