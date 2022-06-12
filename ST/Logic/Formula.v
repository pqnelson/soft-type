Require Import String.
Require Import Nat.
Require Import Lia.
Require Export Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Vectors.Vector.
Require Export RelationClasses.
Require Export Morphisms.
Require Import List.
Import ListNotations.
Open Scope string_scope.
From ST Require Import EVarsScratchwork Vector.
From ST Require Export SoftType.
From ST Require Export Logic.V Logic.Term Logic.Predicate.
Import VectorNotations.
(** ** Formulas

The grammar of formulas is rather straightforward. Honestly, I was unsure how
"slick" I should be: [Verum] could be defined as [Not Falsum], but using a 
minimal set of connectives seemed _too_ slick for my tastes.
*)
Inductive Formula : Type :=
| Falsum
| Atom : Predicate -> Formula
| And : Formula -> Formula -> Formula
| Or : Formula -> Formula -> Formula
| Implies : Formula -> Formula -> Formula
| Exists : Formula -> Formula.

Definition Not (p : Formula) := Implies p Falsum.
Definition Verum : Formula := Implies Falsum Falsum.
Definition Forall (p : Formula) := Not (Exists (Not p)).

Fixpoint formula_contains_bvar (index : nat) (A : Formula) : Prop :=
match A with
  | Falsum => False
  | Atom pred => contains_bvar index pred
  | And fm1 fm2 | Or fm1 fm2 | Implies fm1 fm2 => (formula_contains_bvar index fm1) \/ (formula_contains_bvar index fm2)
  | Exists fm => (formula_contains_bvar (S index) fm)
end.

Global Instance ContainsBVarFormula : ContainsBVar Formula := {
  contains_bvar := formula_contains_bvar
}.

Fixpoint is_ground_formula (phi : Formula) :=
match phi with
| Falsum => True
| Atom p => is_ground p
| And f1 f2 | Or f1 f2 | Implies f1 f2 => (is_ground_formula f1) /\ (is_ground_formula f2)
| Exists f => is_ground_formula f
end.

Global Instance GroundFormula : Ground Formula := {
  is_ground := is_ground_formula
}.

Definition is_sentence (A : Formula) := is_ground_formula A.

(** We can recursively test if two [Formula] objects are identical. This is an
equality at the level of syntax. *)
Fixpoint eq_formula (A B : Formula) : bool :=
match A,B with
| Falsum, Falsum => true
| Atom (P n1 s1 args1), Atom (P n2 s2 args2) => 
      if andb (eqb n1 n2) (eqb s1 s2)
      then vectors_eqb args1 args2 term_eqb
      else false
| And A1 A2, And B1 B2 => andb (eq_formula A1 B1) (eq_formula A2 B2)
| Or A1 A2, Or B1 B2 => andb (eq_formula A1 B1) (eq_formula A2 B2)
| Implies A1 A2, Implies B1 B2 =>  andb (eq_formula A1 B1) (eq_formula A2 B2)
| Exists A1, Exists B1 => eq_formula A1 B1
| _, _ => false
end.

Global Instance EqFormula : Eq Formula := {
  eqb := eq_formula
}.

Theorem Formula_eq_dec : forall a b : Formula, {a = b} + {a <> b}.
Proof.
  decide equality. apply Predicate.eq_dec.
Defined.

(** "Variable closing", or binding a free variable to a quantifier (or any
binder), is a bit tricky. We have a helper function here for the iterative
step. It behaves "functorially", descending to the leafs, i.e., [Falsum] and
[Atom]. *)
Fixpoint var_closing_iter (x : name) (n : nat) (phi : Formula) : Formula :=
match phi with
| Falsum => phi
| Atom pred => Atom (subst (FVar x) (Var (BVar n)) pred)
| And fm1 fm2 => And (var_closing_iter x n fm1) (var_closing_iter x n fm2)
| Or fm1 fm2 => Or (var_closing_iter x n fm1) (var_closing_iter x n fm2)
| Implies fm1 fm2 => Implies (var_closing_iter x n fm1) (var_closing_iter x n fm2)
| Exists fm => Exists (var_closing_iter x (S n) fm)
end.

Definition quantify (x : name) (phi : Formula) : Formula :=
  var_closing_iter x 0 phi.

(** Substitution, when replacing a bound variable with an arbitrary term,
requires care. Why? Because we need to lift the bound variable as we encounter
quantifiers. 

Particular care must be taken when the term refers to variables or quantities
in the "context part". Towards that end, we must [lift] the term whenever a
quantifier is encountered.
*)

Fixpoint subst_bvar_inner (n : nat) (t : Term) (phi : Formula) : Formula :=
match phi with
| Falsum => phi
| Atom pred => Atom (subst (BVar n) t pred)
| And fm1 fm2 => And (subst_bvar_inner n t fm1) (subst_bvar_inner n t fm2)
| Or fm1 fm2 => Or (subst_bvar_inner n t fm1) (subst_bvar_inner n t fm2)
| Implies fm1 fm2 => Implies (subst_bvar_inner n t fm1) (subst_bvar_inner n t fm2)
| Exists fm => Exists (subst_bvar_inner (S n) (lift (S n) 1 t) fm)
end.

(** Specialization and choosing a witness for existential quantification
amounts to the same "operations" of peeling off an outermost quantifier, then
behaving as expected. *)
Fixpoint quantifier_elim_subst (n : nat) (t : Term) (phi : Formula) : Formula :=
match phi with
| Exists fm => subst_bvar_inner n t fm
| And A B => And (quantifier_elim_subst n t A) (quantifier_elim_subst n t B)
| Or A B => Or (quantifier_elim_subst n t A) (quantifier_elim_subst n t B)
| Implies A B => Implies (quantifier_elim_subst n t A) (quantifier_elim_subst n t B)
| _ => phi
end.

Example subst_bvar_1 : quantifier_elim_subst 0 (Fun "t" []) (Forall (Exists (Atom (P 2 "P" [Var (BVar 0); Var (BVar 1)]))))
= Not (Not (Exists (Atom (P 2 "P" [Var (BVar 0); Fun "t" []])))).
Proof.
  trivial.
Qed.

Fixpoint lift_formula (c d : nat) (phi : Formula) : Formula :=
  match phi with
  | Falsum => phi
  | Atom pred => Atom (lift c d pred)
  | And fm1 fm2 => And (lift_formula c d fm1) (lift_formula c d fm2)
  | Or fm1 fm2 => Or (lift_formula c d fm1) (lift_formula c d fm2)
  | Implies fm1 fm2 => Implies (lift_formula c d fm1) (lift_formula c d fm2)
  | Exists fm => Exists (lift_formula (S c) d fm)
  end.

Global Instance LiftFormula : Lift Formula :=
{
  lift := lift_formula
}.
(**
We would encode $\forall x\exists y P(x,y)$ as 
[Forall (Exists (Atom (P 2 "P" [BVar 1; BVar 0])))], using de Bruijn indices.
*)
Check Forall (Exists (Atom (P 2 "P" [Var (BVar 1); Var (BVar 0)]))).


(**
We now have a helper function to quantify over a given variable. They handle
lifting and replacement, if the variable appears at all in the [Formula]. If
[n] does not appear in [Formula], then the formula [phi] is returned unchanged.
*)
Definition every (n : name) (phi : Formula) : Formula :=
  let phi' := quantify n (shift phi)
  in if eqb phi' (shift phi) then phi else Forall phi'.

Definition any (n : name) (phi : Formula) : Formula :=
  let phi' := quantify n (shift phi)
  in if eqb phi' (shift phi) then phi else Exists phi'.

(** As a smoke check, we see if variations on a simple formula are "parsed" as
expected. *)
Example quantifier_example_1 : (every "x" (any "y" (Atom (P 2 "P" [Var (FVar "x"); Var (FVar "y")]))))
= Forall (Exists (Atom (P 2 "P" [Var (BVar 1); Var (BVar 0)]))).
Proof.
  trivial.
Qed.

Example quantifier_example_2 : 
  every "z" (any "y" (Atom (P 2 "P" [Var (FVar "x"); Var (FVar "y")])))
  = Exists (Atom (P 2 "P" [Var (FVar "x"); Var (BVar 0)])).
Proof.
  trivial.
Qed.


Fixpoint fresh_formula (c : Term) (p : Formula) : Prop :=
  match p with
  | Falsum => True
  | Atom phi => fresh c phi
  | And A B | Or A B | Implies A B => (fresh_formula c A) /\ (fresh_formula c B)
  | Exists A => fresh_formula c A
  end.
  
Global Instance FreshFormula : Fresh Formula := {
  fresh := fresh_formula
}.

Global Instance FreshContext : Fresh (list Formula) := {
  fresh c Γ := List.Forall (fun fm => fresh c fm) Γ
}.

(** * Listing the Existential Variables appearing in a Formula *)
Fixpoint list_evars_formula (phi : Formula) : list nat :=
match phi with
| Falsum => []%list
| Atom pred => list_evars pred
| And fm1 fm2 | Or fm1 fm2 | Implies fm1 fm2 => insert_merge (list_evars_formula fm1) (list_evars_formula fm2)
| Exists fm => (list_evars_formula fm)
end.

Global Instance EnumerateEVarsFormula : EnumerateEVars Formula := {
list_evars := list_evars_formula
}. 

Theorem list_evars_formula_sorted : forall (phi : Formula),
  sorted (list_evars phi).
Proof. intros. induction phi.
- simpl; auto. apply sorted_nil.
- unfold list_evars; unfold EnumerateEVarsFormula. apply list_evars_predicate_sorted.
- unfold list_evars; unfold EnumerateEVarsFormula.
  apply insert_merge_sorted2; assumption.
- unfold list_evars; unfold EnumerateEVarsFormula.
  apply insert_merge_sorted2; assumption.
- unfold list_evars; unfold EnumerateEVarsFormula.
  apply insert_merge_sorted2; assumption.
- simpl; auto.
Qed.

Global Instance EnumerateEVarsFormulaList : EnumerateEVars (list Formula) := {
list_evars Γ := (List.fold_left (fun l' => fun (phi : Formula) => insert_merge (list_evars phi) l')
 Γ []%list)
}. 

Theorem list_evars_formula_list_sorted : forall (l : list Formula),
  sorted (list_evars l).
Proof.
  intros. unfold list_evars; unfold EnumerateEVarsFormulaList.
  apply insert_merge_list_fold_sorted. apply sorted_nil.
Qed.

Fixpoint shift_evars_formula (phi : Formula) : Formula :=
match phi with
| Falsum => phi
| Atom pred => Atom (shift_evars pred)
| And fm1 fm2 => And (shift_evars_formula fm1) (shift_evars_formula fm2)
| Or fm1 fm2 => Or (shift_evars_formula fm1) (shift_evars_formula fm2)
| Implies fm1 fm2 => Implies (shift_evars_formula fm1) (shift_evars_formula fm2)
| Exists fm => Exists (shift_evars_formula fm)
end.

Global Instance ShiftEvarsFormula : ShiftEvars Formula := {
  shift_evars := shift_evars_formula
}.

Global Instance ShiftEvarsListFormula : ShiftEvars (list Formula) := {
  shift_evars Γ := List.map shift_evars Γ
}.

Definition fresh_evar_counter (Γ : list Formula) (p : Formula) : nat :=
first_new 0 (list_evars (p::Γ)%list).

Definition fresh_evar (Γ : list Formula) (p : Formula) : Term :=
EConst (fresh_evar_counter Γ p).

(* TODO: these next two results should be proven, but I am lazy. *)
Lemma fresh_evar_context : forall (Γ : list Formula) (p : Formula),
  fresh (fresh_evar Γ p) Γ.
Admitted.

(* Exercise: Prove the following.

Lemma fresh_evar_body : forall (Γ : list Formula) (p : Formula),
  fresh (fresh_evar Γ p) p.
Admitted.
*)