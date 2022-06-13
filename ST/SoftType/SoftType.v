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
From ST Require Export SoftType.Radix SoftType.Adjective.
Import ListNotations.
Import VectorNotations.
Open Scope string_scope.
(* ** Soft Types

We can encode a [SoftType] as an ordered pair of a list of [Adjective] and
a [Radix] type.
*)
Definition SoftType : Type := (list Adjective)*Radix.
Definition Star : SoftType := (List.nil, Ast).

Definition arity (T : SoftType) : nat :=
  match T with
  | (_, R) => Radix.arity R
  end.

Global Instance EqSoftType : Eq SoftType := {
  eqb (T1 T2 : SoftType) :=
  match T1,T2 with
  | (adjs1, R1), (adjs2, R2) => andb (list_eqb adjs1 adjs2 eqb) (eqb R1 R2)
  end
}.

Global Instance substSoftType : Subst SoftType := {
  subst (x : V) (t : Term) (T : SoftType) :=
  match T with
  | (List.nil, R) => (List.nil, subst x t R)
  | (adjs, R) => (List.map (fun (a : Adjective) => subst x t a) adjs, subst x t R)
  end
}.

Global Instance liftSoftType : Lift SoftType :=
{
  lift (c d : nat) (T : SoftType) :=
  match T with
  | (adjs, R) => (List.map (fun (a : Adjective) => (lift c d a)) adjs, lift c d R)
  end;
  unlift (c d : nat) (T : SoftType) :=
  match T with
  | (adjs, R) => (List.map (fun (a : Adjective) => (unlift c d a)) adjs, unlift c d R)
  end
}.

Global Instance EnumerateEVarsSoftType : EnumerateEVars SoftType := {
list_evars T := match T with
| (adjectives,T) => List.fold_left (fun l' => fun (adj : Adjective) => insert_merge (list_evars adj) l')
 adjectives (list_evars T)
end
}.

Theorem list_evars_soft_type_sorted : forall (T : SoftType),
  sorted (list_evars T).
Proof. intros. destruct T.
  assert (sorted (list_evars r)). { apply list_evars_radix_sorted. }
  unfold list_evars; unfold EnumerateEVarsSoftType.
  apply insert_merge_list_fold_sorted2 with (init := list_evars r).
  assumption.
Qed.

(** *** Miscellaneous predicates concerning soft types *)
Definition type_is_named (T : SoftType) (n : name) : Prop :=
  match T with
  | (_, Mode k1 s1 args1) => n = s1
  | _ => False
  end.

Definition mk_mode {n} (M : name) (args : Vector.t Term n) : SoftType :=
  (List.nil, (Mode n M args)).

Definition prefix (a : Adjective) (T : SoftType) : SoftType :=
  match T with
  | (adjs, R) => if List.existsb (fun (adj : Adjective) => eqb a adj) adjs 
                 then T else (List.cons a adjs, R)
  end.

Fixpoint prefix_all (adjs : list Adjective) (T : SoftType) : SoftType :=
  match adjs with
  | List.nil => T
  | List.cons a ad2 => prefix_all ad2 (prefix a T)
  end.

Definition non (a : Adjective) : Adjective :=
  match a with
  | Pos attr => Neg attr
  | Neg attr => Pos attr
  end.
