Require Import String.
Require Import List.
Require Import Nat.
Require Import Coq.Vectors.Vector.
Require Export Coq.Arith.Compare_dec.
Require Export List.
Require Export RelationClasses.
Require Export Morphisms.
Import ListNotations.
Open Scope string_scope.
From ST Require Export SoftType.
From ST Require Import Logic VariadicQuantifiers.
Import VectorNotations.
(** * Translation of Soft Types to First-Order Logic 

We now have a mapping [|.|] of soft types, judgements, and related linguistic
constructs, to first-order logic.

For now, this is just a mocked stub.
*)
Class Translatable A :=
  {
    translate: A -> Formula;
  }.
  
Import VectorNotations.
  
Global Instance TranslatableRadix : Translatable Radix := {
  translate (R : Radix) :=
  match R with
  | Ast => Verum
  | Mode n M args => (Atom (P (S n) (String.append "Mode_" M) ((Var (BVar 0))::(Vector.map shift args))))
  end
}.
  
Global Instance TranslatableAttr : Translatable Attribute := {
  translate (attr : Attribute) :=
  match attr with
  | Attr n s args => (Atom (P (S n) (String.append "Attr_" s) ((Var (BVar 0))::(Vector.map shift args))))
  end
}.
  
Global Instance TranslatableAdj : Translatable Adjective := {
  translate (adj : Adjective) :=
  match adj with
  | Pos a => translate a
  | Neg a => Not (translate a)
  end
}.

(* Consider: shift everything by 1, and have [BVar 0] reserved for future
use in translating judgements. *)
Global Instance TranslatableSoftType : Translatable SoftType := {
  translate (T : SoftType) :=
  match T with
  | (adjs, R) => let fix tr_adjs (ads : list Adjective) :=
                     match ads with
                     | List.cons a tl => And (translate a) (tr_adjs tl)
                     | List.nil => Verum
                     end
                     in And (tr_adjs adjs) (translate R)
  end
}.

Global Instance TranslatableJudgementType : Translatable JudgementType := {
  translate (J : JudgementType) := 
  match J with
  | Esti tm Tp => quantifier_elim_subst 0 tm (translate Tp)
  | Subtype T1 T2 => match (translate T1), (translate T2) with
                     | A1, A2 => Forall (Implies A1 A2)
                     end
  | Inhabited T => Exists (translate T)
  | _ => Verum
  end
}.

(** Global definitions are a list of definitions, which are a [LocalContext]
and a [JudgementType]. There may be a clever way to encode this, but I am at
a loss at the moment. Instead I will cheat and use Currying. *)

(*
_         __   _                         _                 __       _ _
\ \      / /__( )_ __ ___     __ _  ___ (_)_ __   __ _    / _|_   _| | |
 \ \ /\ / / _ \/| '__/ _ \   / _` |/ _ \| | '_ \ / _` |  | |_| | | | | |
  \ V  V /  __/ | | |  __/  | (_| | (_) | | | | | (_| |  |  _| |_| | | |
   \_/\_/ \___| |_|  \___|   \__, |\___/|_|_| |_|\__, |  |_|  \__,_|_|_|
                             |___/               |___/
  ____
 / ___|   _ _ __ _ __ _   _
| |  | | | | '__| '__| | | |
| |__| |_| | |  | |  | |_| |
 \____\__,_|_|  |_|   \__, |
                      |___/

*)
Fixpoint translate_antecedent (lc : LocalContext) (j : JudgementType) : Formula :=
match lc with
| List.nil => translate j
| List.cons (_,T) List.nil => Forall (Implies (translate T) (translate j))
| List.cons (_,T) tl => Forall (Implies (translate T) (translate_antecedent tl j))
end.

Definition translate_definition (defn : LocalContext*JudgementType) : Formula :=
match defn with
| (lc, J) => translate_antecedent lc J
end.

Fixpoint translate_gc (gc : GlobalContext) :=
match gc with
| List.nil => Verum
| List.cons d List.nil => translate_definition d
| List.cons d tl => And (translate_definition d) (translate_gc tl)
end.

Global Instance TranslatableGlobalContext : Translatable GlobalContext := {
  translate := translate_gc
}.

Global Instance TranslatableJudgement : Translatable Judgement := {
translate (judge : Judgement) :=
  match judge with
  | (Γ, Δ, j) => Implies (translate Γ) (translate_antecedent Δ j)
  end
}.

(** * Main Results

We can now articulate the correctness results. *)

(*

Hint Constructors JudgementType Radix Term Adjective : core.

Print HintDb typeclass_instances.

Hint Constructors JudgementType Radix Term Adjective Predicate Formula : typeclass_instances.
*)

Lemma empty_context_correctness :
  well_typed (List.nil ;; List.nil |- CorrectContext) -> proves (translate (List.nil ;; List.nil |- CorrectContext)).
Proof. 
  intros; simpl; apply Verum_implies_Verum.
Qed.

Hint Unfold GlobalContext LocalContext : typeclass_instances.
Hint Constructors well_typed deducible : core.
Lemma star_sub_star_correctness :
  forall (Γ : GlobalContext) (Δ : LocalContext),
  well_typed (Γ ;; Δ |- Subtype Star Star) -> proves (translate (Γ ;; Δ |- Subtype Star Star)).
Admitted.

Lemma global_weakening : forall (J : JudgementType) (Γ1 Γ2 : GlobalContext) (Δ : LocalContext),
  List.incl Γ1 Γ2 ->
  well_typed (Γ1 ;; Δ |- J) ->
  well_typed (Γ2 ;; Δ |- J).
Admitted.

Lemma local_weakening : forall (J : JudgementType) (Γ : GlobalContext) (Δ1 Δ2 : LocalContext),
  List.incl Δ1 Δ2 ->
  well_typed (Γ ;; Δ1 |- J) ->
  well_typed (Γ ;; Δ2 |- J).
Admitted.

Lemma proves_true_weakening : forall (J1 J2 : JudgementType) (Γ : GlobalContext) (Δ1 Δ2 : LocalContext),
  List.incl Δ1 Δ2 -> (translate J2 = Verum) ->
  proves (translate (Γ ;; Δ1 |- J1)) ->
  proves (translate (Γ ;; Δ2 |- J2)).
Admitted.

Lemma well_typed_contexts : forall (J : JudgementType) (Γ : GlobalContext) (Δ : LocalContext),
  well_typed (Γ ;; Δ |- J) ->
  well_typed (Γ ;; Δ |- CorrectContext).
Admitted.

Hint Unfold translate_antecedent : core.
Theorem correctness : forall (J : Judgement),
  well_typed J -> proves (translate J).
Proof.
  intros.
  induction H.
  - intros; simpl; apply Verum_implies_Verum. (* Γ ;; Δ |- CorrectContext *)
  - intros. simpl. (* Γ;; push (x, T) Δ |- CorrectContext *)
  (* ... and the rest! *)
Qed.