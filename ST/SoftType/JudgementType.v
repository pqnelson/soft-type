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
From ST Require Export SoftType.Radix SoftType.Attribute SoftType.Adjective SoftType.SoftType.
Import ListNotations.
Import VectorNotations.
Open Scope string_scope.



(** ** Judgement Types *)

Inductive JudgementType :=
| CorrectContext : JudgementType
| Esti : Term -> SoftType -> JudgementType
| Subtype : SoftType -> SoftType -> JudgementType
| Inhabited : SoftType -> JudgementType
| HasAttribute : Attribute -> SoftType -> JudgementType.

Global Instance substJudgementType : Subst JudgementType := {
  subst (x : V) (t : Term) (J : JudgementType) :=
  match J with
  | CorrectContext => J
  | Esti tm Tp => Esti (subst x t tm) (subst x t Tp)
  | Subtype T1 T2 => Subtype (subst x t T1) (subst x t T2)
  | Inhabited T => Inhabited (subst x t T)
  | HasAttribute a T => HasAttribute (subst x t a) (subst x t T)
  end
}.

Global Instance liftJudgementType : Lift JudgementType := {
  lift (c d : nat) (J : JudgementType) :=
  match J with
  | CorrectContext => J
  | Esti tm Tp => Esti (lift c d tm) (lift c d Tp)
  | Subtype T1 T2 => Subtype (lift c d T1) (lift c d T2)
  | Inhabited T => Inhabited (lift c d T)
  | HasAttribute a T => HasAttribute (lift c d a) (lift c d T)
  end;
  unlift (c d : nat) (J : JudgementType) :=
  match J with
  | CorrectContext => J
  | Esti tm Tp => Esti (unlift c d tm) (unlift c d Tp)
  | Subtype T1 T2 => Subtype (unlift c d T1) (unlift c d T2)
  | Inhabited T => Inhabited (unlift c d T)
  | HasAttribute a T => HasAttribute (unlift c d a) (unlift c d T)
  end
}.

Global Instance EnumerateEVarsJudgementType : EnumerateEVars JudgementType := {
list_evars Judg := match Judg with
| CorrectContext => []%list
| Esti t T => insert_merge (list_evars t) (list_evars T)
| Subtype T1 T2 => insert_merge (list_evars T1) (list_evars T2)
| Inhabited T => list_evars T
| HasAttribute a T => insert_merge (list_evars a) (list_evars T)
end
}.

Theorem list_evars_judgement_type_sorted : forall (j : JudgementType),
  sorted (list_evars j).
Proof.
  intros. induction j.
  - unfold list_evars; unfold EnumerateEVarsJudgementType. apply sorted_nil.
  - unfold list_evars; unfold EnumerateEVarsJudgementType.
    assert (sorted (list_evars s)). { apply list_evars_soft_type_sorted. }
    apply insert_merge_sorted2. assumption.
  - unfold list_evars; unfold EnumerateEVarsJudgementType.
    assert (sorted (list_evars s0)). { apply list_evars_soft_type_sorted. }
    apply insert_merge_sorted2. assumption.
  - unfold list_evars; unfold EnumerateEVarsJudgementType.
    assert (sorted (list_evars s)). { apply list_evars_soft_type_sorted. }
    assumption.
  - unfold list_evars; unfold EnumerateEVarsJudgementType.
    assert (sorted (list_evars s)). { apply list_evars_soft_type_sorted. }
    apply insert_merge_sorted2. assumption.
Qed.
