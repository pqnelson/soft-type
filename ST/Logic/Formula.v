Require Import String.
Require Import Nat.
Require Import Coq.Vectors.Vector.
Require Import List.
Require Import Lia.
Import ListNotations.
Open Scope string_scope.
From ST Require Import EVarsScratchwork.
From ST Require Export ST.SoftType.
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

Definition is_and (p : Formula) : bool :=
match p with
| And _ _ => true
| _ => false
end.

Definition Is_and (p : Formula) : Prop :=
match p with
| And _ _ => True
| _ => False
end.

Definition Iff (a b : Formula) :=
  And (Implies a b) (Implies b a).

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

Theorem eq_dec : forall a b : Formula, {a = b} + {a <> b}.
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

Fixpoint capture_free_subst (n : nat) (t : Term) (phi : Formula) : Formula :=
match phi with
| Falsum => phi
| Atom pred => Atom (subst (BVar n) t pred)
| And fm1 fm2 => And (capture_free_subst n t fm1) (capture_free_subst n t fm2)
| Or fm1 fm2 => Or (capture_free_subst n t fm1) (capture_free_subst n t fm2)
| Implies fm1 fm2 => Implies (capture_free_subst n t fm1) (capture_free_subst n t fm2)
| Exists fm => Exists (capture_free_subst (S n) (lift (S n) 1 t) fm)
end.

Lemma forall_subst : forall (n : nat) (t : Term) (A : Formula),
  capture_free_subst n t (Forall A) = Forall (capture_free_subst (S n) (lift (S n) 1 t) A).
Proof.
  intros; simpl; auto.
Qed.

(** Specialization and choosing a witness for existential quantification
amounts to the same "operations" of peeling off an outermost quantifier, then
behaving as expected. *)
Fixpoint quantifier_elim_subst (n : nat) (t : Term) (phi : Formula) : Formula :=
match phi with
| Exists fm => capture_free_subst n t fm
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

Example subst_bvar_2 : quantifier_elim_subst 0 (Fun "t" [Var (BVar 0)]) (Forall (Exists (Atom (P 2 "P" [Var (BVar 0); Var (BVar 1)]))))
= Not (Not (Exists (Atom (P 2 "P" [Var (BVar 0); Fun "t" [Var (BVar 0)]])))).
Proof.
  trivial.
Qed.

Example subst_bvar_3 : quantifier_elim_subst 0 (Fun "t" []) 
(Forall (Forall (Forall (Exists (Atom (P 3 "P" [Var (BVar 0); Var (BVar 1); Var (BVar 3)]))))))
= Not (Not (Forall (Forall (Exists (Atom (P 3 "P" [Var (BVar 0); Var (BVar 1); (Fun "t" []) ])))))).
Proof.
  simpl; auto.
Qed.

(* In [Fun "t" [(Var (BVar 1))]], the parameter [BVar 1] is interpreted as a 
free variable. For this reason, it will be "kept above" the syntactic depth
of the outermost binder in the resulting formula. There are 3 quantifiers
in the result, therefore we expect it to be [BVar 4] in the outcome. *)
Example subst_bvar_4 : quantifier_elim_subst 0 (Fun "t" [(Var (BVar 1))]) 
(Forall (Forall (Forall (Exists (Atom (P 3 "P" [Var (BVar 0); Var (BVar 1); Var (BVar 3)]))))))
= Not (Not (Forall (Forall (Exists (Atom (P 3 "P" [Var (BVar 0); Var (BVar 1); (Fun "t" [(Var (BVar 4))]) ])))))).
Proof.
  simpl; auto.
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

Theorem lift_id : forall (A : Formula),
  lift_formula 0 0 A = A.
Proof.
  intros. induction A.
  - simpl; auto.
  - unfold lift_formula. rewrite Predicate.lift_id. reflexivity.
  - simpl; auto; rewrite IHA1; rewrite IHA2; reflexivity.
  - simpl; auto; rewrite IHA1; rewrite IHA2; reflexivity.
  - simpl; auto; rewrite IHA1; rewrite IHA2; reflexivity.
  - simpl; auto. 
(* This requires some tricky argument, but it's true. *)
Admitted.

Fixpoint unlift_formula (c d : nat) (phi : Formula) : Formula :=
  match phi with
  | Falsum => phi
  | Atom pred => Atom (unlift c d pred)
  | And fm1 fm2 => And (unlift_formula c d fm1) (unlift_formula c d fm2)
  | Or fm1 fm2 => Or (unlift_formula c d fm1) (unlift_formula c d fm2)
  | Implies fm1 fm2 => Implies (unlift_formula c d fm1) (unlift_formula c d fm2)
  | Exists fm => Exists (unlift_formula (S c) d fm)
  end.

Global Instance LiftFormula : Lift Formula :=
{
  lift := lift_formula;
  unlift := unlift_formula
}.
  
Lemma lift_forall : forall (c d : nat) (A : Formula),
  lift c d (Forall A) = Forall (lift (S c) d A).
Proof.
  intros; simpl; auto.
Qed.
(**
We would encode $\forall x\exists y P(x,y)$ as 
[Forall (Exists (Atom (P 2 "P" [BVar 1; BVar 0])))], using de Bruijn indices.
*)


Theorem lift_comp : forall (c d1 d2 : nat) (A : Formula),
  lift c d1 (lift c d2 A) = lift c (d1 + d2) A.
Proof.
  intros. generalize dependent c.
  induction A.
  - intros. simpl; auto.
  - intros. assert(lift c d1 (lift c d2 (Atom p)) = Atom (lift c d1 (lift c d2 p))). {
      simpl; auto.
    } rewrite H.
    assert (lift c (d1 + d2) (Atom p) = Atom (lift c (d1 + d2) p)). {
      simpl; auto.
    } rewrite H0.
    assert (lift c d1 (lift c d2 p) = lift c (d1 + d2) p). {
      apply Predicate.lift_comp.
    } rewrite H1. reflexivity.
  - intros. assert (lift c d1 (lift c d2 (And A1 A2)) = And (lift c d1 (lift c d2 A1)) (lift c d1 (lift c d2 A2))). {
      simpl; auto.
    } rewrite H; rewrite IHA1; rewrite IHA2.
    assert (lift c (d1 + d2) (And A1 A2) = And (lift c (d1 + d2) A1) (lift c (d1 + d2) A2)). {
      simpl; auto.
    } rewrite H0. reflexivity.
  - intros. assert (lift c d1 (lift c d2 (Or A1 A2)) = Or (lift c d1 (lift c d2 A1)) (lift c d1 (lift c d2 A2))). {
      simpl; auto.
    } rewrite H; rewrite IHA1; rewrite IHA2.
    assert (lift c (d1 + d2) (Or A1 A2) = Or (lift c (d1 + d2) A1) (lift c (d1 + d2) A2)). {
      simpl; auto.
    } rewrite H0. reflexivity.
  - intros. assert (lift c d1 (lift c d2 (Implies A1 A2)) = Implies (lift c d1 (lift c d2 A1)) (lift c d1 (lift c d2 A2))). {
      simpl; auto.
    } rewrite H; rewrite IHA1; rewrite IHA2.
    assert (lift c (d1 + d2) (Implies A1 A2) = Implies (lift c (d1 + d2) A1) (lift c (d1 + d2) A2)). {
      simpl; auto.
    } rewrite H0. reflexivity.
  - intros. assert (lift c d1 (lift c d2 (Exists A)) = Exists (lift (S c) d1 (lift (S c) d2 A))). { simpl; auto. }
    assert (lift c (d1 + d2) (Exists A) = Exists (lift (S c) (d1 + d2) A)). { simpl; auto. }
    rewrite H; rewrite H0. rewrite (IHA (S c)). reflexivity.
Qed.

Theorem lift_seq : forall (c d2 d1 : nat) (A : Formula),
  d1 > 0 -> lift (S c) d2 (lift c d1 A) = lift c (d2 + d1) A.
Proof.
  intros. generalize dependent c.
  induction A.
  - intros. simpl; auto.
  - intros. assert(lift (S c) d2 (lift c d1 (Atom p)) = Atom (lift (S c) d2 (lift c d1 p))). {
      simpl; auto.
    } rewrite H0.
    assert (lift c (d2 + d1) (Atom p) = Atom (lift c (d2 + d1) p)). {
      simpl; auto.
    } rewrite H1.
    assert (lift (S c) d2 (lift c d1 p) = lift c (d2 + d1) p). {
      apply Predicate.lift_seq. assumption.
    } rewrite H2. reflexivity.
  - intros. assert (lift (S c) d2 (lift c d1 (And A1 A2)) = And (lift (S c) d2 (lift c d1 A1)) (lift (S c) d2 (lift c d1 A2))). {
      simpl; auto.
    } rewrite H0; rewrite IHA1; rewrite IHA2.
    assert (lift c (d2 + d1) (And A1 A2) = And (lift c (d2 + d1) A1) (lift c (d2 + d1) A2)). {
      simpl; auto.
    } rewrite H1. reflexivity.
  - intros. assert (lift (S c) d2 (lift c d1 (Or A1 A2)) = Or (lift (S c) d2 (lift c d1 A1)) (lift (S c) d2 (lift c d1 A2))). {
      simpl; auto.
    } rewrite H0; rewrite IHA1; rewrite IHA2.
    assert (lift c (d2 + d1) (Or A1 A2) = Or (lift c (d2 + d1) A1) (lift c (d2 + d1) A2)). {
      simpl; auto.
    } rewrite H1. reflexivity.
  - intros. assert (lift (S c) d2 (lift c d1 (Implies A1 A2)) = Implies (lift (S c) d2 (lift c d1 A1)) (lift (S c) d2 (lift c d1 A2))). {
      simpl; auto.
    } rewrite H0; rewrite IHA1; rewrite IHA2.
    assert (lift c (d2 + d1) (Implies A1 A2) = Implies (lift c (d2 + d1) A1) (lift c (d2 + d1) A2)). {
      simpl; auto.
    } rewrite H1. reflexivity.
  - intros. assert (lift (S c) d2 (lift c d1 (Exists A)) = Exists (lift (S (S c)) d2 (lift (S c) d1 A))). { simpl; auto. }
    assert (lift c (d2 + d1) (Exists A) = Exists (lift (S c) (d2 + d1) A)). { simpl; auto. }
    rewrite H0; rewrite H1. rewrite (IHA (S c)). reflexivity.
Qed.

(*
Lemma variadic_lift_seq : forall (m : nat) (A : Formula),
  (lift (S m) 1 (lift 1 m A)) = lift 1 (S m) A.
Proof.
  intros. generalize dependent m.
  induction A.
  - intros. simpl; auto.
  - intros. assert(lift (S m) 1 (lift 1 m (Atom p)) = Atom (lift (S m) 1 (lift 1 m p))). {
      simpl; auto.
    } rewrite H.
    assert (lift 1 (S m) (Atom p) = Atom (lift 1 (S m) p)). {
      simpl; auto.
    } rewrite H0.
    assert (lift (S m) 1 (lift 1 m p) = lift 1 (S m) p). {
      apply Predicate.variadic_lift_seq.
    } rewrite H1. reflexivity.
  - intros. assert (lift (S m) 1 (lift 1 m (And A1 A2)) = And (lift (S m) 1 (lift 1 m A1)) (lift (S m) 1 (lift 1 m A2))). {
      simpl; auto.
    } rewrite H; rewrite IHA1; rewrite IHA2.
    assert (lift 1 (S m) (And A1 A2) = And (lift 1 (S m) A1) (lift 1 (S m) A2)). {
      simpl; auto.
    } rewrite H0. reflexivity.
  - intros. assert (lift (S m) 1 (lift 1 m (Or A1 A2)) = Or (lift (S m) 1 (lift 1 m A1)) (lift (S m) 1 (lift 1 m A2))). {
      simpl; auto.
    } rewrite H; rewrite IHA1; rewrite IHA2.
    assert (lift 1 (S m) (Or A1 A2) = Or (lift 1 (S m) A1) (lift 1 (S m) A2)). {
      simpl; auto.
    } rewrite H0. reflexivity.
  - intros. assert (lift (S m) 1 (lift 1 m (Implies A1 A2)) = Implies (lift (S m) 1 (lift 1 m A1)) (lift (S m) 1 (lift 1 m A2))). {
      simpl; auto.
    } rewrite H; rewrite IHA1; rewrite IHA2.
    assert (lift 1 (S m) (Implies A1 A2) = Implies (lift 1 (S m) A1) (lift 1 (S m) A2)). {
      simpl; auto.
    } rewrite H0. reflexivity.
  - intros. assert (lift (S m) 1 (lift 1 m (Exists A)) = Exists (lift (S (S m)) 1 (lift 2 m A))). { simpl; auto. }
    assert (lift 1 (S m) (Exists A) = Exists (lift 2 (S m) A)). { simpl; auto. }
    rewrite H; rewrite H0. rewrite (IHA (S m)). reflexivity.
Qed.
*)


Lemma variadic_lift_seq : forall (k m : nat) (A : Formula),
  k > 0 -> (lift (k + m) 1 (lift k m A)) = lift k (S m) A.
Proof.
  intros. generalize dependent k. generalize dependent m.
  induction A.
  - intros. simpl; auto.
  - intros. assert(lift (k + m) 1 (lift k m (Atom p)) = Atom (lift (k + m) 1 (lift k m p))). {
      simpl; auto.
    } rewrite H0.
    assert (lift k (S m) (Atom p) = Atom (lift k (S m) p)). {
      simpl; auto.
    } rewrite H1.
    assert (lift (k + m) 1 (lift k m p) = lift k (S m) p). {
      apply Predicate.variadic_quantifier_lift_seq. assumption.
    } rewrite H2. reflexivity.
  - intros. assert (lift (k + m) 1 (lift k m (And A1 A2)) 
                    = And (lift (k + m) 1 (lift k m A1)) (lift (k + m) 1 (lift k m A2))). {
      simpl; auto.
    } rewrite H0; rewrite IHA1. rewrite IHA2.
    assert (lift k (S m) (And A1 A2) = And (lift k (S m) A1) (lift k (S m) A2)). {
      simpl; auto.
    } rewrite H1. reflexivity. assumption. assumption.
  - intros. assert (lift (k + m) 1 (lift k m (Or A1 A2)) = Or (lift (k + m) 1 (lift k m A1)) (lift (k + m) 1 (lift k m A2))). {
      simpl; auto.
    } rewrite H0; rewrite IHA1. rewrite IHA2.
    assert (lift k (S m) (Or A1 A2) = Or (lift k (S m) A1) (lift k (S m) A2)). {
      simpl; auto.
    } rewrite H1. reflexivity. assumption. assumption.
  - intros. assert (lift (k + m) 1 (lift k m (Implies A1 A2)) = Implies (lift (k + m) 1 (lift k m A1)) (lift (k + m) 1 (lift k m A2))). {
      simpl; auto.
    } rewrite H0; rewrite IHA1. rewrite IHA2.
    assert (lift k (S m) (Implies A1 A2) = Implies (lift k (S m) A1) (lift k (S m) A2)). {
      simpl; auto.
    } rewrite H1. reflexivity. assumption. assumption.
  - intros. assert (lift (k + m) 1 (lift k m (Exists A)) = Exists (lift (S (k + m)) 1 (lift (S k) m A))). { simpl; auto. }
    assert (lift k (S m) (Exists A) = Exists (lift (S k) (S m) A)). { simpl; auto. }
    rewrite H0; rewrite H1.
    assert (lift (S k + m) 1 (lift (S k) m A) = lift (S k) (S m) A). {
      apply (IHA m (S k)). apply Gt.gt_Sn_O.
    }
    assert (S k + m = S (k + m)). lia. rewrite H3 in H2.
    rewrite H2; reflexivity.
Qed.

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
  fresh c Γ := List.Forall (fresh c) Γ
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

Fixpoint lift_evars_formula (k : nat) (phi : Formula) : Formula :=
match phi with
| Falsum => phi
| Atom pred => Atom (lift_evars k pred)
| And fm1 fm2 => And (lift_evars_formula k fm1) (lift_evars_formula k fm2)
| Or fm1 fm2 => Or (lift_evars_formula k fm1) (lift_evars_formula k fm2)
| Implies fm1 fm2 => Implies (lift_evars_formula k fm1) (lift_evars_formula k fm2)
| Exists fm => Exists (lift_evars_formula k fm)
end.

Global Instance LiftEvarsFormula : LiftEvars Formula := {
  lift_evars := lift_evars_formula
}.

Global Instance LiftEvarsListFormula : LiftEvars (list Formula) := {
  lift_evars k Γ := List.map (lift_evars k) Γ
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
(*
Lemma capture_free_subst_id0 : forall (p : Formula),
  capture_free_subst 0 (Var (BVar 0)) p = p.
Proof.
  intros. induction p.
  - simpl; auto.
  - unfold capture_free_subst; rewrite Predicate.subst_id; reflexivity.
  - simpl; auto; rewrite IHp1; rewrite IHp2; reflexivity. 
  - simpl; auto; rewrite IHp1; rewrite IHp2; reflexivity. 
  - simpl; auto; rewrite IHp1; rewrite IHp2; reflexivity. 
  - assert (capture_free_subst 0 (Var (BVar 0)) (Exists p)
            = Exists (capture_free_subst (S 0) (lift (S 0) 1 (Var (BVar 0))) p)). {
      simpl; auto.
    admit.
    }
    rewrite H.
    assert (lift 1 1 (Var (BVar 0)) = Var (BVar 0)). {
      simpl; auto.
    }
    rewrite H0.
    admit.
Admitted.

Lemma capture_free_subst_id : forall (n : nat) (p : Formula),
  capture_free_subst n (Var (BVar n)) p = p.
Proof.
  intros. generalize dependent n. induction p.
  - intros; simpl; auto.
  - intros; unfold capture_free_subst; rewrite Predicate.subst_id; reflexivity.
  - intros; simpl; auto; rewrite IHp1; rewrite IHp2; reflexivity. 
  - intros; simpl; auto; rewrite IHp1; rewrite IHp2; reflexivity. 
  - intros; simpl; auto; rewrite IHp1; rewrite IHp2; reflexivity. 
  - intros.
    assert (capture_free_subst n (Var (BVar n)) (Exists p)
            = Exists (capture_free_subst (S n) (lift (S n) 1 (Var (BVar n))) p)). {
      simpl; auto.
    }
    assert (lift (S n) 1 (Var (BVar n)) = Var (BVar n)). {
      assert (lift (S n) 1 (Var (BVar n)) = Var (lift (S n) 1 (BVar n))). {
        simpl; auto.
      } rewrite H0.
      assert (lift (S n) 1 (BVar n) = BVar n). {
        apply case_lift_is_id. simpl; auto.
      }
      rewrite H1; reflexivity.
    }
    rewrite H; rewrite H0.
Admitted.
*)

Fixpoint contains_formula (sub : Term) (fm : Formula) : Prop := match fm with
  | Falsum => False
  | Atom p => contains sub p
  | And A B | Or A B | Implies A B => (contains_formula sub A) \/ (contains_formula sub B)
  | Exists A => contains_formula sub A
end.

Global Instance ContainsFormula : Contains Formula := {
  contains := contains_formula
}.


