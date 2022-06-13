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
From ST Require Export SoftType.Radix SoftType.Attribute SoftType.Adjective SoftType.SoftType SoftType.JudgementType.
From ST Require Export SoftType.LocalContext.
Import ListNotations.
Import VectorNotations.
Open Scope string_scope.



(** ** Global Contexts

We now can track definitions of terms, types, etc., using a [GlobalContext].
This is encoded as just a list of [JudgementType] and the relevant local 
variables as found in a [LocalContext].
*)
Definition GlobalContext := list (LocalContext * JudgementType).


Definition list_evars_gc_def (d : LocalContext * JudgementType) :=
match d with
  | (lc, T) => insert_merge (list_evars lc) (list_evars T)
  end.

Global Instance EnumerateEVarsGlobalContext : EnumerateEVars GlobalContext := {
list_evars gc := List.fold_left (fun l' => fun d => 
  insert_merge (list_evars_gc_def d)  l')
 gc []%list
}.

Theorem list_evars_global_context_sorted : forall (gc : GlobalContext),
  sorted (list_evars gc).
Proof.
  intros.
  unfold list_evars; unfold EnumerateEVarsGlobalContext.
  apply insert_merge_list_fold_sorted. apply sorted_nil.
Qed.


(** Judgements of the form [t : T] are where we define new constant terms. *)
Fixpoint gc_defines_term (gc : GlobalContext) (n : name) : Prop :=
  match gc with
  | List.cons (lc, Esti (Fun nm _) T) tl => (n = nm) \/ gc_defines_term tl n
  | _ => False
  end.

Fixpoint gc_defines_type (gc : GlobalContext) (n : name) : Prop :=
  match gc with
  | List.cons (lc, Subtype T1 T2) tl => (type_is_named T1 n) \/ (type_is_named T2 n) \/ (gc_defines_type  tl n)
  | List.cons (lc, Inhabited T) tl =>(type_is_named T n) \/ (gc_defines_type  tl n)
  | _ => False
  end.

Fixpoint gc_defines_attr (gc : GlobalContext) (n : name) : Prop :=
  match gc with
  | List.cons (lc, HasAttribute (Attr _ a args) T) tl => (a = n) \/ (gc_defines_attr tl n)
  | _ => False
  end.

Fixpoint gc_contains (Γ : GlobalContext) (def : (LocalContext * JudgementType)) : Prop :=
  match Γ,def with
  | List.cons (lc, J') Γ', (subcontext, J) => ((lc_is_subcontext subcontext lc) /\ J = J') \/ gc_contains Γ' def
  | List.nil, _ => False
  end.
