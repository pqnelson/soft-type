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
From ST Require Export SoftType.LocalContext SoftType.GlobalContext.
Import ListNotations.
Import VectorNotations.
Open Scope string_scope.


(** * Inference Rules for Soft Types

We can now code up the inference rules for Wiedijk's soft type system inductively. 
*)
Definition Judgement : Type := GlobalContext * LocalContext * JudgementType.

Definition Judgement_body (j : Judgement) :=
match j with
| (_,_, body) => body
end.

Global Instance EnumerateEVarsJudgement : EnumerateEVars Judgement := {
list_evars j := match j with
| (gc,lc,judge) => insert_merge (list_evars gc) (insert_merge (list_evars lc) (list_evars judge))
end
}.

Theorem list_evars_judgement_sorted : forall (j : Judgement),
  sorted (list_evars j).
Proof. intros. destruct j.
  unfold list_evars; unfold EnumerateEVarsJudgement.
  assert (sorted (list_evars j)). { apply list_evars_judgement_type_sorted. }
  destruct p.
  assert (sorted (insert_merge (list_evars l) (list_evars j))). {
    apply insert_merge_sorted2; assumption.
  }
  apply insert_merge_sorted2; assumption.
Qed.

Definition push {A : Type} (a : A) (l : list A) : list A :=
  List.app l (List.cons a List.nil).
Close Scope string_scope.
Import ListNotations.

Notation "gc ;; lc |- j" := (gc, lc, j) (at level 80).
Import ListNotations.
Open Scope list_scope.
Inductive well_typed : Judgement -> Prop :=
| wt_empty_context : well_typed ([] ;; [] |- CorrectContext)
| wt_var : forall (?? : GlobalContext) (?? : LocalContext) (T : SoftType) (J : JudgementType),
  well_typed (?? ;; ?? |- Inhabited T) ->
  well_typed (?? ;; (push T ??) |- CorrectContext)
(* TODO: substitution rule for a vector of declarations *)
| wt_subst : forall (?? : GlobalContext) (?? : LocalContext) (t : Term) (T : SoftType) (J : JudgementType),
  well_typed (?? ;; (List.cons T ??) |- J) ->
  well_typed (?? ;; ?? |- Esti t T) ->
  well_typed (?? ;; (capture_free_subst 0 t ??) |- (subst (BVar (length ??)) t J))
(* XXX Wiedijk combines this [wt_assume] rule with [wt_subst] in a single step, I decompose them into two. *)
| wt_assume : forall (?? : GlobalContext) (?? : LocalContext) (J : JudgementType),
  gc_contains ?? (??, J) ->
  well_typed (?? ;; ?? |- J)
(* TODO: inhabited types produce new local variables *)
| wt_subtype_star_star : forall (?? : GlobalContext) (?? : LocalContext),
  well_typed (?? ;; ?? |- CorrectContext) ->
  well_typed (?? ;; ?? |- Subtype Star Star)
| wt_inhabited_star : forall (?? : GlobalContext) (?? : LocalContext),
  well_typed (?? ;; ?? |- CorrectContext) ->
  well_typed (?? ;; ?? |- Inhabited Star)
| wt_subtype_refl : forall (?? : GlobalContext) (?? : LocalContext) (T1 T2 : SoftType),
  well_typed (?? ;; ?? |- Subtype T1 T2) ->
  well_typed (?? ;; ?? |- Subtype T1 T1)
| wt_subtype_trans : forall (?? : GlobalContext) (?? : LocalContext) (T1 T2 T3 : SoftType),
  well_typed (?? ;; ?? |- Subtype T1 T2) ->
  well_typed (?? ;; ?? |- Subtype T2 T3) ->
  well_typed (?? ;; ?? |- Subtype T1 T3)
| wt_subsumption : forall (?? : GlobalContext) (?? : LocalContext) (T1 T2 : SoftType) (t : Term),
  well_typed (?? ;; ?? |- Esti t T1) ->
  well_typed (?? ;; ?? |- Subtype T1 T2) ->
  well_typed (?? ;; ?? |- Esti t T2)
| wt_parent_inhabited : forall (?? : GlobalContext) (?? : LocalContext) (T1 T2 : SoftType),
  well_typed (?? ;; ?? |- Subtype T1 T2) ->
  well_typed (?? ;; ?? |- Inhabited T1) ->
  well_typed (?? ;; ?? |- Inhabited T2)
| wt_cons_pos : forall (?? : GlobalContext) (?? : LocalContext) (T : SoftType) (A : Attribute),
  well_typed (?? ;; ?? |- HasAttribute A T) ->
  well_typed (?? ;; ?? |- Subtype (prefix (Pos A) T) T)
| wt_cons_neg : forall (?? : GlobalContext) (?? : LocalContext) (T : SoftType) (A : Attribute),
  well_typed (?? ;; ?? |- HasAttribute A T) ->
  well_typed (?? ;; ?? |- Subtype (prefix (Neg A) T) T)
| wt_adj_subtype : forall (?? : GlobalContext) (?? : LocalContext) (T1 T2 : SoftType) (a : Adjective),
  well_typed (?? ;; ?? |- Subtype T1 T2) ->
  well_typed (?? ;; ?? |- Subtype (prefix a T2) T2) ->
  well_typed (?? ;; ?? |- Subtype (prefix a T1) T1)
| wt_adj_subtype_adj : forall (?? : GlobalContext) (?? : LocalContext) (T1 T2 : SoftType) (a : Adjective),
  well_typed (?? ;; ?? |- Subtype T1 T2) ->
  well_typed (?? ;; ?? |- Subtype (prefix a T2) T2) ->
  well_typed (?? ;; ?? |- Subtype (prefix a T1) (prefix a T2))
| wt_adj_diamond : forall (?? : GlobalContext) (?? : LocalContext) (T1 T2 : SoftType) (a1 a2 : Adjective),
  well_typed (?? ;; ?? |- Subtype T1 (prefix a1 T2)) ->
  well_typed (?? ;; ?? |- Subtype T1 (prefix a2 T2)) ->
  well_typed (?? ;; ?? |- Subtype T1 (prefix a1 (prefix a2 T2)))
  (* Rules governing Definitions *)
| wt_functor_def : forall (?? : GlobalContext) (?? : LocalContext) (T : SoftType) (f : name),
  not (gc_defines_term ?? f) ->
  well_typed (?? ;; ?? |- Inhabited T) ->
  well_typed (?? ++ [(??, (Esti (Fun f (local_vars ??)) T))] ;; [] |- CorrectContext)
| wt_mode_def : forall (?? : GlobalContext) (?? : LocalContext) (T : SoftType) (M : name), 
  not (gc_defines_type ?? M) ->
  well_typed (?? ;; ?? |- Inhabited T) ->  
  well_typed (?? ++
              [(??, (Subtype (mk_mode M (local_vars ??)) T)) ;
                (??, (Inhabited (mk_mode M (local_vars ??))))] ;; [] |- CorrectContext)
| wt_attr_def : forall (?? : GlobalContext) (?? : LocalContext) (T : SoftType) (alpha : name), 
  not (gc_defines_attr ?? alpha) ->
  well_typed (?? ;; ?? |- Inhabited T) ->
  well_typed (?? ++ [(??, HasAttribute (Attr (List.length ??) alpha (local_vars ??)) T)] ;; List.nil |- CorrectContext)
  (* Rules governing clusters *)
| wt_cluster_exist : forall (?? : GlobalContext) (?? : LocalContext) (T : SoftType) (a : Adjective), 
  well_typed (?? ;; ?? |- Subtype (prefix a T) T) ->
  well_typed (?? ;; ?? |- Inhabited T) ->
  well_typed (?? ++ [(??, (Inhabited (prefix a T)))] ;; [] |- CorrectContext)
| wt_cluster_cond : forall (?? : GlobalContext) (?? : LocalContext) (T : SoftType) (a1 a2 : list Adjective), 
  well_typed (?? ;; ?? |- Subtype (prefix_all a1 T) T) ->
  well_typed (?? ;; ?? |- Subtype (prefix_all a2 T) T) ->
  well_typed (List.app ?? (List.cons (??, (Subtype (prefix_all a1 T) (prefix_all a2 T))) List.nil) ;; List.nil |- CorrectContext)
| wt_cluster_fun : forall (?? : GlobalContext) (?? : LocalContext) (t : Term) (T : SoftType) (a : Adjective), 
  well_typed (?? ;; ?? |- Esti t T) ->
  well_typed (?? ;; ?? |- Subtype (prefix a T) T) ->
  well_typed (?? ++ [(??, (Esti t (prefix a T)))] ;; [] |- CorrectContext)
  (* Rules governing redefinitions *)
| wt_redef_fun : forall (?? : GlobalContext) (????? ????? : LocalContext) (t : Term) (T1 T2 T3 : SoftType), 
  term_is_fun t ->
  well_typed (?? ;; ????? |- Inhabited T2) ->
  well_typed (?? ;; ????? |- Subtype T2 T3) ->
  well_typed (?? ;; (????? ++ ?????) |- Esti (fun_with_locals t ?????) T3) ->
  well_typed (?? ++ [((????? ++ ?????), (Esti (fun_with_locals t ?????) T3))] ;; List.nil |- CorrectContext)
| wt_redef_mode : forall (?? : GlobalContext) (????? ????? : LocalContext) (M : Radix) (T1 T2 T3 : SoftType), 
  radix_is_mode M ->
  well_typed (?? ;; ????? |- Inhabited T2) ->
  well_typed (?? ;; ????? |- Subtype T2 T3) ->
  well_typed (?? ;; (????? ++ ?????) |- Subtype ([], (mode_with_locals M ?????)) T3) ->
  well_typed (?? ++ [((????? ++ ?????), (Subtype ([], (mode_with_locals M ?????)) T3))] ;; [] |- CorrectContext).

