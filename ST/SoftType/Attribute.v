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
From ST Require Export SoftType.Radix.
Import ListNotations.
Import VectorNotations.
Open Scope string_scope.
(** ** Attributes

Attributes may be prepended to types, when registered in an existential cluster.
Otherwise, we can create a formula [Term is Attribute]. 
*)

Inductive Attribute : Type := 
| Attr : forall (n : nat), name -> Vector.t Term n -> Attribute.

Global Instance EqAttribute : Eq Attribute := {
  eqb (A1 A2 : Attribute) :=
  match A1,A2 with
  | Attr n1 s1 args1, Attr n2 s2 args2 => if andb (eqb n1 n2) (eqb s1 s2) then
    vectors_eqb args1 args2 term_eqb
    else false
  end
}.

Global Instance substAttr : Subst Attribute :=
{
  subst (x : V) (t : Term) (a : Attribute) :=
  match a with
  | Attr n s args => Attr n s (Vector.map (fun (arg : Term) => subst x t arg) args)
  end
}.

Global Instance liftAttr : Lift Attribute :=
{
  lift (c d : nat) (a : Attribute) :=
  match a with
  | Attr n s args => Attr n s (Vector.map (fun (a : Term) => lift c d a) args)
  end;
  unlift (c d : nat) (a : Attribute) :=
  match a with
  | Attr n s args => Attr n s (Vector.map (fun (a : Term) => unlift c d a) args)
  end
}.

Global Instance EnumerateEVarsAttribute : EnumerateEVars Attribute := {
list_evars attr := match attr with
| Attr n s args => Vector.fold_left (fun l' => fun (arg : Term) => insert_merge (list_evars arg) l') []%list args
end
}.

Theorem list_evars_attribute_sorted : forall (A : Attribute),
  sorted (list_evars A).
Proof. intros. destruct A. rename t into args.
  unfold list_evars; unfold EnumerateEVarsAttribute.
  apply insert_merge_vector_fold_sorted2.
  apply sorted_nil.
Qed.
