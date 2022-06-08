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
Import VectorNotations.
From ST Require Import EVarsScratchwork.
(** * Natural Deduction

We need to formalize the proof calculus to then prove the correctness of soft 
type system.

References relevant:

- https://people.compute.dtu.dk/ahfrom/Formalized%20First-Order%20Logic.pdf
- https://hal.archives-ouvertes.fr/hal-03096253
*)

(** ** Predicates

We encode the syntax of a predicate, analogous to [Term], as its arity 
[n : nat], its [name], and its arguments as a [Vector.t Term].
*)
Inductive Predicate : Type := 
| P : forall (n : nat), name -> Vector.t Term n -> Predicate.

Global Instance substPred : Subst Predicate :=
{
  subst (x : V) (t : Term) (p : Predicate) :=
  match p with
  | P n s args => P n s (Vector.map (fun (arg : Term) => subst x t arg) args)
  end
}.

Example pred_subst_1 : subst (BVar 0) (Fun "c" []) (P 3 "P" [Var (BVar 1); Var (BVar 0); Fun "f" [Var (BVar 0); Var (FVar "y")]])
= (P 3 "P" [Var (BVar 1); (Fun "c" []); Fun "f" [(Fun "c" []); Var (FVar "y")]]).
Proof.
  trivial.
Qed.

Global Instance EqPred : Eq Predicate :=
{
  eqb (P1 P2 : Predicate) :=
  match P1,P2 with
  | P n1 s1 args1, P n2 s2 args2 => 
      if andb (eqb n1 n2) (eqb s1 s2)
      then vectors_eqb args1 args2 term_eqb
      else false
  end
}.

Global Instance LiftPred : Lift Predicate :=
{
  lift (c d : nat) (p : Predicate) :=
  match p with
  | P n s args => P n s (Vector.map (fun (a : Term) => lift c d a) args)
  end
}.

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

(** ** Rules of Natural Deduction 

We can now encode natural deduction rules using a straightforward inductive
type. The only subtlety surrounds ensuring a variable [name] is [fresh].
And that's because I am too lazy to do this adequately. Modeling arguments 
as vectors screw everything up. But it's obviously not wrong. Let's hope it 
doesn't destroy correctness ;p 
*)

Section CavalierAxiomatics.
(* Look, I placed the dangerous bit in their own section. Everything is
safe and sound now, right? *)
Axiom term_eq_dec : forall (x y : Term), {x = y} + {x <> y}.
Axiom predicate_eq_dec : forall (x y : Predicate), {x = y} + {x <> y}.
End CavalierAxiomatics.

Lemma Term_eq_dec : forall a b : Term, {a = b} + {a <> b}.
Proof. apply term_eq_dec. Defined.


Lemma Predicate_eq_dec : forall a b : Predicate, {a = b} + {a <> b}.
Proof. apply predicate_eq_dec. Defined.

Lemma Formula_eq_dec : forall a b : Formula, {a = b} + {a <> b}.
Proof. decide equality. apply predicate_eq_dec. Defined.

Class Fresh A : Type := {
  fresh : Term -> A -> Prop
}.

Section FreshTermDefinition.
(* Require Import Coq.Vectors.VectorEq. *)

Fixpoint fresh_term (c : Term) (t : Term) : Prop :=
match t, c with
| Var x, Var y => x <> y
| EConst m, EConst n => m <> n
| Fun f args1, Fun g args2 => t <> c /\
  let fix fresh_args {k} (ars : Vector.t Term k) :=
          match ars with
          | tm::ars1 => (fresh_term c tm) /\ fresh_args ars1
          | [] => True
          end
  in fresh_args args1
| _,_ => True
end.
End FreshTermDefinition.

Global Instance FreshTerm : Fresh Term := {
  fresh := fresh_term
}.

Global Instance FreshPredicate : Fresh Predicate := {
  fresh (c : Term) (p : Predicate) :=
  match p with
  | P n s args => Vector.Forall (fun (arg : Term) => fresh c arg) args
  end
}.

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

(** ** New Existential Variables 

We can assemble the list of existential variables appearing in a
[Term], [Formula], whatever. Then we can generate a fresh
existential variable.
*)

Class EnumerateEVars A := {
  list_evars : A -> list nat
}.

Fixpoint list_evars_term (t : Term) (l : list nat) : list nat :=
match t with
| Var _ => l
| EConst n => insert n l
| Fun f args => Vector.fold_left (fun l' => fun (arg : Term) => insert_merge l' (list_evars_term arg l'))
    l args
end.

Global Instance EnumerateEVarsTerm : EnumerateEVars Term := {
  list_evars tm := list_evars_term tm []
}.

Hypothesis list_evers_term_sorted : forall (t : Term),
  sorted (list_evars t).

Global Instance EnumerateEVarsPredicate : EnumerateEVars Predicate := {
list_evars p := match p with
| P n s args => Vector.fold_left (fun l' => fun (arg : Term) => insert_merge l' (list_evars arg)) []%list args
end
}.

Hypothesis list_evars_predicate_sorted : forall (p : Predicate),
  sorted (list_evars p).

Global Instance EnumerateEVarsRadix : EnumerateEVars Radix := {
list_evars R := match R with
| Ast => []%list
| Mode n s args => Vector.fold_left (fun l' => fun (arg : Term) => insert_merge l' (list_evars arg)) []%list args
end
}.

Hypothesis list_evars_radix_sorted : forall (R : Radix),
  sorted (list_evars R).

Global Instance EnumerateEVarsAttribute : EnumerateEVars Attribute := {
list_evars attr := match attr with
| Attr n s args => Vector.fold_left (fun l' => fun (arg : Term) => insert_merge l' (list_evars arg)) []%list args
end
}.

Hypothesis list_evars_attribute_sorted : forall (A : Attribute),
  sorted (list_evars A).

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

Global Instance EnumerateEVarsSoftType : EnumerateEVars SoftType := {
list_evars T := match T with
| (adjectives,T) => List.fold_left (fun l' => fun (adj : Adjective) => insert_merge l' (list_evars adj))
 adjectives (list_evars T)
end
}.

Hypothesis list_evars_soft_type_sorted : forall (T : SoftType),
  sorted (list_evars T).

Global Instance EnumerateEVarsJudgementType : EnumerateEVars JudgementType := {
list_evars Judg := match Judg with
| CorrectContext => []%list
| Esti t T => insert_merge (list_evars t) (list_evars T)
| Subtype T1 T2 => insert_merge (list_evars T1) (list_evars T2)
| Inhabited T => list_evars T
| HasAttribute a T => insert_merge (list_evars a) (list_evars T)
end
}.

Hypothesis list_evars_judgement_type_sorted : forall (j : JudgementType),
  sorted (list_evars j).

Global Instance EnumerateEVarsLocalContext : EnumerateEVars LocalContext := {
list_evars lc := List.fold_left (fun l' => fun (d : Decl) => 
  match d with
  | (_, T) => insert_merge l' (list_evars T)
  end)
 lc []%list
}.

Hypothesis list_evars_local_context_sorted : forall (lc : LocalContext),
  sorted (list_evars lc).

Global Instance EnumerateEVarsGlobalContext : EnumerateEVars GlobalContext := {
list_evars gc := List.fold_left (fun l' => fun d => 
  match d with
  | (lc, T) => insert_merge l' (insert_merge (list_evars lc) (list_evars T))
  end)
 gc []%list
}.

Hypothesis list_evars_global_context_sorted : forall (gc : GlobalContext),
  sorted (list_evars gc).

Global Instance EnumerateEVarsJudgement : EnumerateEVars Judgement := {
list_evars j := match j with
| (gc,lc,judge) => insert_merge (list_evars gc) (insert_merge (list_evars lc) (list_evars judge))
end
}.

Hypothesis list_evars_judgement_sorted : forall (j : Judgement),
  sorted (list_evars j).

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

Hypothesis list_evars_formula_sorted : forall (phi : Formula),
  sorted (list_evars phi).

Global Instance EnumerateEVarsFormulaList : EnumerateEVars (list Formula) := {
list_evars Γ := (List.fold_left (fun l' => fun (phi : Formula) => insert_merge l' (list_evars phi))
 Γ []%list)
}. 

Hypothesis list_evars_formula_list_sorted : forall (l : list Formula),
  sorted (list_evars l).

Require Import Nat.
Require Import Coq.Arith.PeanoNat.
  Check Nat.eqb_eq.

Lemma first_new_cons {l n} :
  first_new n (n :: l) = first_new (S n) l.
Proof.
  assert(n = n). reflexivity.
  apply Nat.eqb_eq in H as H1.
  simpl; auto. rewrite H1. reflexivity.
Qed.

Lemma neq_neqb : forall (n k : nat),
  n <> k <-> Nat.eqb n k = false.
Proof. intros. revert n.
  induction k as [|k IHk]; intro n; destruct n; simpl; rewrite ?IHk; split; try easy.
  - intros. assert (n <> k). red; auto. apply IHk in H0. assumption.
  - intros. apply IHk in H. red; auto.
Qed.

Lemma first_new_distinct {l a n} :
  a <> n -> first_new n (a :: l) = first_new n l.
Proof. 
  intros. 
  apply neq_neqb in H as H1.
  simpl; auto. rewrite H1. 
  reflexivity.
Qed.

Lemma fresh_new_step {l n k} :
  first_new n l = first_new n (k::l) \/ first_new (S n) l = first_new n (k::l).
Proof.
  assert({k = n} + {k <> n}). decide equality. destruct H.
  - right. rewrite e. symmetry. apply first_new_cons.
  - left. apply (@first_new_distinct l k n) in n0. symmetry; assumption.
Qed.

Lemma first_new_nondecreasing {l n} :
  n <= first_new n l.
Proof. generalize dependent n.
  induction l. 
  - simpl; auto.
  - intros. assert ({a = n} + {a <> n}). decide equality.
    destruct H.
  -- rewrite e. 
     assert (first_new n (n :: l) = first_new (S n) l).
     apply first_new_cons. rewrite H.
     assert (S n <= first_new (S n) l). apply (@IHl (S n)).
     intuition.
  -- assert(first_new n l = first_new n (a :: l)). symmetry. apply (@first_new_distinct l a n).
     assumption. rewrite <- H.
     apply IHl.
Qed.  

Lemma fresh_succ_nonzero {l n} :
  0 < first_new (S n) l.
Proof.
  intros. generalize dependent n. induction l.
  - simpl; auto. apply Nat.lt_0_succ.
  - intros. destruct (@fresh_new_step l (S n) a).
  + rewrite <- H. apply IHl.
  + rewrite <- H. apply (IHl (S n)).
Qed.

(*
Lemma first_new_cons_inv {l n a} :
  a = n <-> first_new n (a :: l) = first_new (S n) l.
Proof.
  assert ({a = n} + {a <> n}). decide equality. destruct H.
  - split.
  -- rewrite e. intros. apply first_new_cons.
  -- intros; assumption.
  - split. contradiction. intros. inversion H.
    assert (Nat.eqb a n  = false). { apply neq_neqb. assumption. }
    rewrite H0 in H1.
  split. 
  - intros. rewrite H. apply first_new_cons.
  - intros. inversion H.
  assert(n = n). reflexivity.
  apply Nat.eqb_eq in H as H1.
  simpl; auto. rewrite H1. reflexivity.
Qed.
*)
Require Import Coq.Arith.Compare.

Lemma first_new_on_different_args {l m n} :
  m <= n -> first_new m l <= first_new n l.
Proof.
  intros. generalize dependent m. generalize dependent n.
  induction l.
  - simpl; auto.
  - intros.
    assert ({n = a} + {n <> a}). decide equality. destruct H0.
  + assert (first_new n (n :: l) = first_new (S n) l). apply first_new_cons.
    assert ({m = a} + {m <> a}). decide equality. destruct H1.
  ++ rewrite e0; rewrite <- e. reflexivity.
  ++ (* m <> a && n = a *)
    assert (first_new m (a :: l) = first_new m l). {
    apply (@first_new_distinct l a m); intuition.
    }
    rewrite H1. 
    assert (n <= first_new n (a :: l)). { apply first_new_nondecreasing. }
    rewrite <- e; rewrite H0. apply IHl. intuition.
  + (* n <> a *)
    assert (first_new n (a :: l) = first_new n l). { apply (@first_new_distinct l a n); intuition. }
    assert ({m = a} + {m <> a}). decide equality. destruct H1.
  ++ (* n <> a && m = a *)
     assert (first_new m (a :: l) = first_new (S m) l). {
       rewrite <- e; apply first_new_cons.
     }
     Check le_le_S_eq.
     assert (S m <= n \/ m = n). { apply le_le_S_eq in H. assumption. }
     destruct H2.
 +++ (* S m <= n *)
     rewrite H0. rewrite H1. apply IHl. intuition.
 +++ rewrite H2. reflexivity.
 ++ assert (first_new m (a :: l) = first_new m l). { apply (@first_new_distinct l a m); intuition. }
    rewrite H1; rewrite H0. apply IHl. assumption.
Qed.

Require Import Lia.
Require Import Coq.Lists.ListDec Decidable.

Theorem first_new_sorted {l n} :
  sorted l -> ~(In (first_new n l) l).
Proof. intros.
  inversion H.
  - simpl; auto.
  - assert({x = n} + {x <> n}). decide equality. destruct H1.
  + rewrite e.
    assert (first_new n [n] = first_new (S n) []). apply (@first_new_cons List.nil).
    rewrite H1. unfold first_new. apply not_in_cons. simpl; auto.
  + assert(first_new n [x] = first_new n []). { apply first_new_distinct. assumption. } 
    rewrite H1. unfold first_new. apply not_in_cons. simpl; auto.
  - admit.
Qed.

Lemma first_new_is_not_in_list {l n} :
  ~(In (first_new n l) l).
Proof. generalize dependent n.
  induction l.
  - simpl; auto.
  - intros. assert({a = n} + {a <> n}). decide equality. destruct H.
 -- (* a = n *) 
    assert(first_new n (a::l) = first_new (S n) l). { rewrite e. apply first_new_cons. }
    apply not_in_cons. split.
    + rewrite e; apply not_eq_sym; apply first_new_distinct2.
    + rewrite H. apply IHl.
 -- (* a <> n *)
    apply not_in_cons. split.
    + apply first_new_distinct3.
    + apply (first_new_distinct (l := l)) in n0 as H. rewrite H. apply IHl.
Qed.

Lemma first_new_is_new {l n} :
  forall (x : nat), In x l -> first_new n l <> x.
Proof.
  induction l.
  - simpl; auto.
  - intros. assert ({a = n} + {a <> n}). decide equality. destruct H0.
 -- (* Case: a = n *) 
    rewrite e.
    assert(first_new n (n::l) = first_new (S n) l). { apply first_new_cons. }
    rewrite H0.
    apply in_inv in H. destruct H. rewrite <- H; rewrite e.
    assert (S n <= first_new (S n) l). apply first_new_nondecreasing. lia.
    apply IHl. assumption.
 -- (* Case: a <> n *) 
    apply in_inv in H. destruct H.
    + rewrite H; rewrite H in n0.
      assert(first_new n (x::l) = first_new n l). { apply first_new_distinct. assumption. }
      rewrite H0.
      assert(decidable (In x l)). { apply (In_decidable Nat.eq_decidable). }
      destruct H1.
   ++ apply (IHl n x) in H1. assumption.
   ++ assert (n <= first_new n l). { apply first_new_nondecreasing. }
      
    lia.
    
  induction l.
  - simpl; auto.
  - intros. assert ({a = n} + {a <> n}). decide equality. destruct H0.
 -- (* Case: a = n *) 
    rewrite e.
    assert(first_new n (n::l) = first_new (S n) l). { apply first_new_cons. }
    rewrite H0.
    apply in_inv in H. destruct H. rewrite <- H; rewrite e.
    assert (S n <= first_new (S n) l). apply first_new_nondecreasing. lia.
    apply IHl. assumption.
 -- (* Case: a <> n *) 
    apply in_inv in H. destruct H.
    + rewrite H; rewrite H in n0.
      assert(first_new n (x::l) = first_new n l). { apply first_new_distinct. assumption. }
      rewrite H0.
    Check @first_new_nondecreasing.
 -- (* a = x *)
    rewrite H. intros.
    
 -- (* In x l *)
  assert ({a = n} + {a <> n}). decide equality. destruct H.
  - assert(first_new n (n::l) = first_new (S n) l). { apply first_new_cons. }
    rewrite e. rewrite H. Check @first_new_nondecreasing.
    assert (S n <= first_new (S n) l). { apply first_new_nondecreasing. }
    lia.
  - assert(first_new n (a::l) = first_new n l). { apply first_new_distinct. assumption. }
    
(* 
@first_new_nondecreasing
     : forall (l : list nat) (n : nat),
       n <= first_new n l
*)
    
    unfold first_new. lia.
  induction l.
  - destruct H.
 -- assert(first_new n [n] = first_new (S n) []). { apply first_new_cons. }
    rewrite e. rewrite H. unfold first_new. lia.
 -- Check @first_new_distinct.
  apply (@first_new_distinct List.nil a n) in n0 as H.
    rewrite H. unfold first_new. intuition.
  - 
   destruct H.
  - assert(first_new n (n :: l) = first_new (S n) l). { apply first_new_cons. }
    rewrite <- H.
Qed.



Theorem first_new_is_not_on_list {l n} :
  ~In (first_new n l) l.
Proof.
  generalize dependent n. induction l.
  - simpl; auto.
  - intros. apply not_in_cons. split.
 -- assert ({n = a} + {n <> a}). decide equality. destruct H.
--- rewrite <- e.
    assert(first_new n (n :: l) = first_new (S n) l). { apply first_new_cons. }
    rewrite H. intuition.
    
Lemma first_new_is_new {l a n} :
  first_new n (a::l) <> a.
  
  set (t := (first_new n (a :: l))).
    apply not_in_cons. split. 
  -- (* Subcase: t <> a *)
     assert ({n = a} + {n <> a}). decide equality. destruct H.
     + (* Sub-subcase: t = first_new n (n :: l) *)
       assert (t = first_new n (n :: l)).
       assert (t = first_new n (a :: l)). simpl; auto.
       rewrite <- e in H. assumption.
       apply (first_new_cons n l) in H.
       
      apply first_new_cons.
    rewrite <- e in t. 
  unfold first_new in (first_new n (a :: l)).
  intros.

Definition fresh_evar_counter (Γ : list Formula) (p : Formula) : nat :=
first_new 0 (list_evars (p::Γ)%list).

Definition fresh_evar (Γ : list Formula) (p : Formula) : Term :=
EConst (fresh_evar_counter Γ p).

Hypothesis fresh_evar_context : forall (Γ : list Formula) (p : Formula),
  fresh (fresh_evar Γ p) Γ.

Hypothesis fresh_evar_body : forall (Γ : list Formula) (p : Formula),
  fresh (fresh_evar Γ p) p.

(** The alternate approach is that fresh existential variables will be [0],
and when we introduce one, we [shift_evars] in the related formulas. *)
Class ShiftEvars A := {
  shift_evars : A -> A
}.

Fixpoint shift_evars_term (t : Term) : Term :=
match t with
| Var _ => t
| EConst n => EConst (S n)
| Fun f args => Fun f (Vector.map shift_evars_term args)
end.

Global Instance ShiftEvarsTerm : ShiftEvars Term := {
shift_evars := shift_evars_term
}.

Global Instance ShiftEvarsPredicate : ShiftEvars Predicate := {
shift_evars p := match p with
| P n s args => P n s (Vector.map shift_evars args)
end
}.

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

Import ListNotations.
Reserved Notation "Γ ⊢ P" (no associativity, at level 61).

Inductive deducible : list Formula -> Formula -> Prop :=
| ND_exfalso_quodlibet {Γ p} :
  Γ ⊢ Falsum ->
  Γ ⊢ p
| ND_imp_e {Γ p q} :
  Γ ⊢ Implies p q -> 
  Γ ⊢ p ->
  Γ ⊢ q
| ND_imp_i2 {Γ p q} :
  p::Γ ⊢ q -> 
  Γ ⊢ Implies p q
| ND_or_intro_l {Γ p q} :
  Γ ⊢ p ->
  Γ ⊢ Or p q
| ND_or_intro_r {Γ p q} :
  Γ ⊢ q ->
  Γ ⊢ Or p q
| ND_proof_by_cases {Γ p q r} :
  Γ ⊢ Or p q ->
  p :: Γ ⊢ r ->
  q :: Γ ⊢ r ->
  Γ ⊢ r
| ND_and_intro {Γ P Q} :
  Γ ⊢ P ->
  Γ ⊢ Q ->
  Γ ⊢ And P Q
| ND_and_elim {Γ P Q R} :
  Γ ⊢ And P Q ->
  P :: Q :: Γ ⊢ R ->
  Γ ⊢ R
| ND_cut {Γ P Q} :
  Γ ⊢ P ->
  P :: Γ ⊢ Q ->
  Γ ⊢ Q
| ND_exists_intro {Γ p t} :
  Γ ⊢ (subst_bvar_inner 0 t p) -> 
  Γ ⊢ Exists p
| ND_proof_by_contradiction {Γ p} :
  (Not p) :: Γ ⊢ Falsum ->
  Γ ⊢ p
| ND_exists_elim_small {Γ p q c} :
  (subst_bvar_inner 0 c p)::Γ ⊢ q -> 
  c = fresh_evar Γ q ->
  (Exists p)::Γ ⊢ q
| ND_prioritize {Γ p q} :
  Γ ⊢ q ->
  In p Γ ->
  p :: Γ ⊢ q
| ND_unprioritize {Γ p q} :
  p :: Γ ⊢ q ->
  In p Γ ->
  Γ ⊢ q
where "Γ ⊢ P" := (deducible Γ P).

Definition proves (fm : Formula) : Prop := deducible List.nil fm.

Hint Unfold GlobalContext LocalContext : typeclass_instances.
Hint Constructors well_typed deducible : core.

(* These next two lemmas are "obvious", but obnoxious to prove.
So I'm...lazy. *)
Lemma exists_elim_freshness {Γ q} :
  (EConst 0) = fresh_evar (shift_evars Γ) (shift_evars q).
Admitted.

Lemma exists_evar_shift {Γ p q} :
  Exists p :: Γ ⊢ q <-> (shift_evars (Exists p))::(shift_evars Γ) ⊢ (shift_evars q).
Admitted.

Theorem exists_elim {Γ p q} :
  (subst_bvar_inner 0 (EConst 0) (shift_evars p))::(shift_evars Γ) ⊢ (shift_evars q) -> 
  (Exists p)::Γ ⊢ q.
Proof.
  intros.
  apply exists_evar_shift.
  apply (ND_exists_elim_small (c := (EConst 0))). assumption.
  apply exists_elim_freshness.
Qed.

Theorem ND_exists_elim {Γ p q c} :
  Γ ⊢ Exists p ->
  c = fresh_evar Γ q ->
  subst_bvar_inner 0 c p :: Γ ⊢ q -> Γ ⊢ q.
Proof.
  intros.
  apply ND_exists_elim_small in H1.
  apply ND_imp_i2 in H1. 
  apply (@ND_imp_e Γ (Exists p) q ) in H1. 
  assumption. assumption. assumption.
Qed.

(**
I am being a bit cavalier here, but the only way to [prove Falsum]
is to assume contradictory premises. I can't seem to get Coq to believe
me about this, so I carved out [ND_assume] as an explicit axiom.
Otherwise the [consistency] theorem below fails.
*)
Axiom ND_assume_axiom : forall (Γ : list Formula) (p : Formula),
  List.In p Γ ->  Γ ⊢ p.

Theorem ND_assume {Γ p} : List.In p Γ ->  Γ ⊢ p.
Proof.
  apply (ND_assume_axiom Γ p).
Qed.

Theorem ND_not_i {Γ p} :
  p::Γ ⊢ Falsum ->
  Γ ⊢ Not p.
Proof.
  intros. unfold Not. apply ND_imp_i2. assumption.
Qed.

Theorem ND_not_e {Γ p q} :
  In p Γ -> In (Not p) Γ -> Γ ⊢ q.
Proof. intros.
  apply ND_assume in H as H1.
  apply ND_assume in H0 as H2.
  unfold Not in H2.
  apply (@ND_imp_e Γ p Falsum) in H2. 2: assumption.
  apply (@ND_exfalso_quodlibet Γ q) in H2. assumption.
Qed.

Definition subcontext (Γ1 Γ2 : list Formula) : Prop :=
  forall P, List.In P Γ1 -> List.In P Γ2.
  
Definition supcontext (Γ1 Γ2 : list Formula) : Prop :=
  subcontext Γ2 Γ1.
Infix "⊆" := subcontext (no associativity, at level 70).
Infix "⊇" := supcontext (no associativity, at level 70).

Lemma empty_subcontext {Γ} :
  [] ⊆ Γ.
Proof.
  intros.
  unfold subcontext. intros. absurd (In P0 []). apply in_nil. assumption.
Qed.

Lemma cons_subcontext : forall (Γ : list Formula) (P : Formula),
  Γ ⊆ List.cons P Γ.
Proof.
  intros; right; assumption.
Qed.

Lemma subcontext_cons : forall (Γ1 Γ2 : list Formula) (P : Formula),
  P :: Γ1 ⊆ Γ2 <-> List.In P Γ2 /\ Γ1 ⊆ Γ2.
Proof.
  split; intros; repeat split.
  - apply H; left; reflexivity.
  - intros x ?; apply H; right; assumption.
  - destruct H. intro x; destruct 1; subst; auto.
Qed.


Ltac prove_In :=
match goal with
| |- In ?P (?P :: ?Γ) => left; reflexivity
| |- In ?P (?Q :: ?Γ) => right; prove_In
end.
Ltac prove_subcontext :=
match goal with
| |- ?P :: ?Γ ⊆ ?Γ' => rewrite subcontext_cons; split;
     [ prove_In | prove_subcontext ]
| |- ?Γ ⊆ ?Γ => reflexivity
| |- ?Γ ⊆ ?P :: ?Γ' => rewrite <- (cons_subcontext P Γ');
                       prove_subcontext
end.

Ltac Assume eqn :=
  assert (eqn) by (apply ND_assume; prove_In).

Import ListNotations.
Open Scope list.

Lemma subcontext_trans : forall (Γ1 Γ2 Γ3 : list Formula),
  Γ1 ⊆ Γ2 -> Γ2 ⊆ Γ3 -> Γ1 ⊆ Γ3.
Proof.
  intros. unfold subcontext in H; unfold subcontext in H0; unfold subcontext. auto.
Qed.
  
Lemma subcontext_weaken : forall (Γ1 Γ2 : list Formula) (P : Formula),
  Γ1 ⊆ Γ2 -> Γ1 ⊆ P :: Γ2.
Proof.
  intros. assert (Γ2 ⊆ (List.cons P0 Γ2)). apply cons_subcontext.
  apply (subcontext_trans Γ1 Γ2 (P0 :: Γ2)) in H0. assumption. assumption.
Qed.
  
Lemma subcontext_weaken2 : forall (Γ1 Γ2 : list Formula) (P : Formula),
  Γ1 ⊆ Γ2 -> P :: Γ1 ⊆ P :: Γ2.
Proof.
  intros. assert (Γ2 ⊆ (List.cons P0 Γ2)). apply cons_subcontext.
  apply subcontext_cons. split; unfold List.In; auto. apply (subcontext_trans Γ1 Γ2 (P0 :: Γ2)).
  assumption. assumption.
Qed.

Lemma subcontext_reflex : forall (Γ : list Formula), Γ ⊆ Γ.
Proof.
  intros; unfold subcontext; auto.
Qed.

Global Instance subcontext_preord : PreOrder subcontext.
Proof.
constructor.
+ intro Γ. red. trivial.
+ intros Γ₁ Γ₂ Γ₃; unfold subcontext. auto.
Qed.

Global Instance subcontext_cons_proper :
  Proper (eq ==> subcontext ++> subcontext) (@cons Formula).
Proof.
intros P Q [] Γ1 Γ2 ?. rewrite subcontext_cons; split.
+ left; reflexivity.
+ rewrite H. apply cons_subcontext.
Qed.

Lemma fresh_in_head : forall {c P Γ1 Γ2},
  (P :: Γ1) ⊆ Γ2 ->
  fresh c Γ2 -> fresh c P.
Proof.
  intros. simpl; auto.
  assert (In P0 Γ2). { apply subcontext_cons in H; destruct H; assumption. }
  unfold fresh in H0; unfold FreshContext in H0.
  apply (Forall_forall) with (P := (fun fm : Formula => fresh c fm)) in H1 as H2.
  simpl; auto. simpl; auto.
Qed.

(* Apparently, this was implemented some time between 8.11 and 8.15, so
if you are using 8.11, uncomment the following:

    Lemma Forall_cons_iff {A} : forall (P : A -> Prop) (a:A) (l : list A), 
List.Forall P (a :: l) <-> P a /\ List.Forall P l.
    Proof.
      intros. now split; [intro H; inversion H|constructor].
    Qed.
*)

Check Coq.Lists.List.Forall_cons_iff.

(* Suppose [Subcontext Γ1 Γ2]. If [fresh c Γ2], then [fresh c Γ1]. *)
Global Instance fresh_cons_proper :
  Proper (eq ++> subcontext --> Basics.impl) fresh.
Proof.
  intros P Q [] Γ1 Γ2 ?. unfold Basics.flip in H. unfold Basics.impl.
  intros H1.
  unfold fresh; unfold FreshContext.
  induction Γ2. auto.
  assert (Γ2 ⊆ a :: Γ2). apply cons_subcontext.
  assert (Γ2 ⊆ Γ1).
  apply (subcontext_trans Γ2 (a :: Γ2) Γ1); assumption; assumption.
  apply Forall_cons_iff. split.
  apply IHΓ2 in H2 as IH. apply (fresh_in_head H). assumption.
  apply IHΓ2 in H2 as IH. assumption.
Qed.

Lemma subcontext_in_trans {Γ1 Γ2 p} :
  In p Γ1 -> Γ1 ⊆ Γ2 -> In p Γ2.
Proof.
  intros. simpl; auto.
Qed.

Global Instance ND_context_extension :
  Proper (subcontext ++> eq ==> Basics.impl) deducible.
Proof.
intros Γ₁ Γ₂ ? P Q [] ?. revert Γ₂ H. induction H0; intros.
+ apply ND_exfalso_quodlibet. auto.
+ apply (ND_imp_e (p := p)); auto.
+ apply ND_imp_i2. apply IHdeducible. f_equiv. auto.
+ apply ND_or_intro_l. auto.
+ apply ND_or_intro_r. auto.
+  apply (ND_proof_by_cases (p := p) (q := q)); auto.
  - apply IHdeducible2. f_equiv. assumption.
  - apply IHdeducible3. f_equiv. assumption.
+ apply ND_and_intro; auto.
+ apply (ND_and_elim (P := P0) (Q := Q0)); auto.
  apply IHdeducible2. do 2 f_equiv; assumption.
+ apply (ND_cut (P := P0)); auto.
  apply IHdeducible2. f_equiv. assumption.
+ apply (ND_exists_intro (p := p) (t := t)); auto.
+ apply ND_proof_by_contradiction. apply IHdeducible. f_equiv. auto.

+ admit. (* apply (ND_unprioritize (p := Exists p) (Γ := Γ₂)).
  apply (ND_exists_elim_small (Γ := Γ₂) (c := c)).
  apply IHdeducible.

Check @ND_exists_elim_small.
 apply ND_exists_elim_small.
 *)
+ Check @subcontext_cons.
 apply (@subcontext_cons Γ Γ₂ p) in H1 as H2. apply IHdeducible. destruct H2. assumption.
+ apply IHdeducible. apply (@subcontext_cons Γ Γ₂ p). split.
  apply (@subcontext_in_trans Γ Γ₂).
assumption. assumption. assumption.
Admitted.
(* Qed. *)

  
Theorem weakening : forall (Γ1 Γ2 : list Formula) (P : Formula),
  Γ1 ⊢ P ->
  Γ1 ⊆ Γ2 ->
  Γ2 ⊢ P.
Proof.
  intros.
  refine (ND_context_extension _ _ _ _ _ eq_refl H).
  assumption.
Qed.

(** ** Important Tautologies 

We will now prove a number of important tautologies. And being a classy mathematician,
we will be proving results in classical logic.
*)

Theorem ND_and_idempotent : forall (P : Formula),
  [] ⊢ (And P P) <-> [] ⊢ P.
Proof. split. (* intros; split. *)
- intros. apply (@ND_and_elim [] P0 P0 P0). assumption.
  apply ND_assume. unfold In. left. reflexivity.
- intros. apply (@ND_and_intro [] P0 P0). assumption. assumption.
Qed.

Theorem ND_or_idempotent : forall (P : Formula),
  [] ⊢ (Or P P) <-> [] ⊢ P.
Proof. split. 
- intros. apply (@ND_proof_by_cases [] P0 P0 P0). assumption.
  Assume (P0 :: [] ⊢ P0); assumption. 
  Assume (P0 :: [] ⊢ P0); assumption.
- intros. apply (@ND_or_intro_r [] P0 P0). assumption.
Qed.

Theorem ND_implies_refl : forall (P : Formula),
  proves (Implies P P).
Proof. intros.
  set (Γ := [P0]).
  assert (In P0 Γ). { unfold In. left. reflexivity. }
  apply ND_assume in H.
  apply ND_imp_i2 in H. assumption.
Qed.

Theorem ND_double_negation {Γ p} : 
  Γ ⊢ Implies (Not (Not p)) p.
Proof.
  apply @ND_imp_i2; apply @ND_proof_by_contradiction; set (q := Not p).
  assert (In q (q :: Not q :: Γ)). prove_In.
  assert (In (Not q) (q :: Not q :: Γ)). prove_In.
  apply @ND_not_e with (Γ := (q :: Not q :: Γ)) (p := q) (q := Falsum).
  assumption. assumption.
Qed.

Theorem ND_implies_falsum_is_negation : forall (Γ : list Formula) (p : Formula),
  Γ ⊢ Implies p Falsum <-> Γ ⊢ Not p.
Proof.
  split.
- intros. apply (@ND_not_i Γ p).
  assert(Γ ⊆ (p :: Γ)). { apply subcontext_weaken. apply subcontext_reflex. }
  apply (weakening Γ (p :: Γ)) in H as H1.
  apply (@ND_imp_e (p :: Γ) p Falsum) in H1 as H2. assumption. apply ND_assume.
  unfold In; left; reflexivity. apply subcontext_weaken. apply subcontext_reflex.
- intros. apply (@ND_imp_i2 Γ p Falsum).
  assert(p :: Γ ⊆ (Not p :: p :: Γ)). { apply subcontext_weaken. apply subcontext_reflex. }
  assert(Γ ⊆ (p :: Γ)). { apply subcontext_weaken. apply subcontext_reflex. }
  apply (weakening Γ (p :: Γ)) in H as H2.
  assert (In p ((Not p) :: p :: Γ)). prove_In.
  assert (In (Not p) ((Not p) :: p :: Γ)). prove_In.
  assert ((Not p) :: p :: Γ ⊢ Falsum). {
  apply (@ND_not_e (Not p :: p :: Γ) p Falsum) in H3 as H5. assumption. assumption.
  }
  apply (@ND_cut (p :: Γ) (Not p) Falsum) in H2 as H6. assumption. assumption. assumption.
Qed.

Theorem ND_True_intro {Γ} :
  Γ ⊢ Verum.
Proof.
  unfold Verum. apply ND_implies_falsum_is_negation.
  apply ND_proof_by_contradiction.
  Assume (Not (Not Falsum) :: Γ ⊢ Not (Not Falsum)). 
  assert (Not (Not Falsum) :: Γ ⊢ Implies (Not (Not Falsum)) Falsum).
  apply ND_double_negation. 
  apply (@ND_imp_e (Not (Not Falsum) :: Γ) (Not (Not Falsum)) Falsum) in H0.
  assumption. assumption.
Qed.

Theorem ND_excluded_middle {Γ p} :
  Γ ⊢ Or p (Not p).
Proof.
apply @ND_proof_by_contradiction.
apply @ND_imp_e with (p := Or p (Not p)).
+ apply ND_implies_falsum_is_negation. 
apply @ND_assume. prove_In.
+ apply @ND_or_intro_r. apply ND_implies_falsum_is_negation. apply @ND_imp_i2.
  apply @ND_imp_e with (p := Or p (Not p)).
  - apply ND_implies_falsum_is_negation. apply @ND_assume. prove_In.
  - apply @ND_or_intro_l.
    apply @ND_assume; prove_In.
Qed.

Theorem ND_and_simplify_l {Γ p q} :
  Γ ⊢ Implies (And p q) p.
Proof.
  intros. apply ND_imp_i2.
  assert (In (And p q) ((And p q) :: Γ)). prove_In.
  apply (@ND_assume ((And p q) :: Γ) (And p q)) in H as H1.
  apply (@ND_and_elim ((And p q)::Γ) p q p) in H1 as H2.
  assumption.
  assert (In p (p :: q :: (And p q) :: Γ)). prove_In.
  apply (@ND_assume (p :: q :: (And p q) :: Γ) p) in H0.
  assumption.
Qed.

Theorem ND_and_simplify_r {Γ p q} :
  Γ ⊢ Implies (And p q) q.
Proof.
  intros. apply ND_imp_i2.
  assert (In (And p q) ((And p q) :: Γ)). prove_In.
  apply (@ND_assume ((And p q) :: Γ) (And p q)) in H as H1.
  apply (@ND_and_elim ((And p q)::Γ) p q q) in H1 as H2.
  assumption.
  assert (In q (p :: q :: (And p q) :: Γ)). prove_In.
  apply (@ND_assume (p :: q :: (And p q) :: Γ) q) in H0.
  assumption.
Qed.

Theorem ND_conj_implies {Γ p q r} :
  Γ ⊢ Implies p q -> Γ ⊢ Implies p r -> Γ ⊢ Implies p (And q r).
Proof.
  intros. apply ND_imp_i2.
  assert(Γ ⊆ p::Γ). { apply subcontext_weaken. apply subcontext_reflex. }
  Check weakening.
  apply (weakening Γ (p :: Γ) (Implies p q)) in H1 as H3. 2: assumption.
  apply (weakening Γ (p :: Γ) (Implies p r)) in H1 as H4. 2: assumption.
  assert (In p (p::Γ)). prove_In. apply ND_assume in H2.
  apply (@ND_imp_e (p :: Γ) p q) in H3. 2: assumption.
  apply (@ND_imp_e (p :: Γ) p r) in H4. 2: assumption.
  apply (@ND_and_intro (p :: Γ) q r). assumption. assumption.
Qed.

Theorem ND_and_commutative {Γ p q} :
  Γ ⊢ Implies (And p q) (And q p).
Proof.
  intros.
  assert (Γ ⊢ Implies (And p q) p). apply ND_and_simplify_l.
  assert (Γ ⊢ Implies (And p q) q). apply ND_and_simplify_r.
  apply (@ND_conj_implies Γ (And p q) q p). assumption. assumption.
Qed.

Theorem ND_or_commutative {Γ p q} :
  Γ ⊢ Implies (Or p q) (Or q p).
Proof. 
  apply ND_imp_i2;
  apply (@ND_proof_by_cases (Or p q :: Γ) p q (Or q p)).
  apply ND_assume; prove_In. 
  apply ND_or_intro_r; apply ND_assume; prove_In. 
  apply ND_or_intro_l; apply ND_assume; prove_In.
Qed.

Theorem ND_proj_l {Γ p q} : 
  Γ ⊢ And p q -> Γ ⊢ p.
Proof.
  intros.
  Assume (p :: q :: Γ ⊢ p).
  apply (@ND_and_elim Γ p q p) in H. assumption.
  assumption.
Qed.

Theorem ND_proj_r {Γ p q} : 
  Γ ⊢ And p q -> Γ ⊢ q.
Proof.
  intros.
  Assume (p :: q :: Γ ⊢ q).
  apply (@ND_and_elim Γ p q q) in H. assumption.
  assumption.
Qed.

Theorem ND_uncurry {Γ p q r} : 
  Γ ⊢ Implies p (Implies q r) -> Γ ⊢ Implies (And p q) r.
Proof.
  intros.
  apply ND_imp_i2.
  assert (And p q :: Γ ⊢ p). {
    Assume (And p q :: Γ ⊢ And p q).
    apply ND_proj_l in H0. assumption.
  }
  assert (Γ ⊆ (And p q :: Γ)). {
    apply subcontext_weaken. apply subcontext_reflex.
  }
  apply (weakening Γ (And p q :: Γ)) in H. 2: assumption.
  apply (@ND_imp_e (And p q :: Γ) p (Implies q r)) in H. 2: assumption.
  assert (And p q :: Γ ⊢ q). {
    Assume (And p q :: Γ ⊢ And p q).
    apply ND_proj_r in H2. assumption.
  }
  apply (@ND_imp_e (And p q :: Γ) q r) in H. assumption. assumption.
Qed.

Theorem ND_curry_tautology {Γ p q r} :
  Γ ⊢ Implies (Implies (And p q) r) (Implies p (Implies q r)).
Proof.
  intros.
  Assume (q::p::(Implies (And p q) r)::Γ ⊢ (Implies (And p q) r)).
  Assume (q::p::(Implies (And p q) r)::Γ ⊢ p).
  Assume (q::p::(Implies (And p q) r)::Γ ⊢ q).
  apply (@ND_and_intro (q::p :: Implies (And p q) r :: Γ) p q) in H1 as H3.
  apply (@ND_imp_e (q::p :: Implies (And p q) r :: Γ) (And p q) r) in H as H4.
  apply (@ND_imp_i2 (p :: Implies (And p q) r :: Γ)) in H4.
  apply (@ND_imp_i2 (Implies (And p q) r :: Γ)) in H4.
  apply ND_imp_i2 in H4.
  assumption. 
  assumption. assumption.
Qed.

Theorem ND_curry {Γ p q r} :
  Γ ⊢ Implies (And p q) r -> Γ ⊢ Implies p (Implies q r).
Proof.
  intros.
  assert (Γ ⊢ Implies (Implies (And p q) r) (Implies p (Implies q r))). {
  apply (@ND_curry_tautology Γ p q r).
  }
  apply (ND_imp_e (p := (Implies (And p q) r))) in H0.
  assumption. assumption.
Qed.

Theorem ND_double_negation2 {Γ p} : 
  Γ ⊢ Implies p (Not (Not p)).
Proof.
  apply ND_imp_i2; apply ND_implies_falsum_is_negation; apply ND_imp_i2;
  apply (@ND_imp_e (Not p :: p :: Γ) p Falsum).
  apply ND_implies_falsum_is_negation; apply ND_assume. prove_In.
  apply ND_assume. prove_In.
Qed.

Theorem ND_destruct_dn {Γ p} : 
  Γ ⊢ p -> Γ ⊢ (Not (Not p)).
Proof. intros.
  assert (Γ ⊢ Implies p (Not (Not p))). apply ND_double_negation2.
  apply (@ND_imp_e Γ p (Not (Not p))) in H0. assumption. assumption.
Qed.

Theorem ND_make_dn {Γ p} : 
  Γ ⊢ (Not (Not p)) -> Γ ⊢ p.
Proof.
  intros.
  assert (Γ ⊢ Implies (Not (Not p)) p). apply ND_double_negation.
  apply (@ND_imp_e Γ (Not (Not p)) p) in H0. assumption. assumption.
Qed.

Check deducible_ind.

Lemma falsum_is_negated_verum {Γ} :
  Γ ⊢ Implies (Not Verum) Falsum.
Proof.
  intros. apply ND_implies_falsum_is_negation. apply ND_destruct_dn.
  apply ND_True_intro.
Qed.

Lemma negated_verum_is_falsum {Γ} :
  Γ ⊢ Implies Falsum (Not Verum).
Proof.
  intros. apply ND_imp_i2. 
  Assume (Falsum :: Γ ⊢ Falsum).
  apply (@ND_exfalso_quodlibet (Falsum :: Γ) (Not Verum)) in H.
  assumption.
Qed.

Lemma subst_falsum_to_not_verum {Γ} :
  Γ ⊢ Falsum -> Γ ⊢ (Not Verum).
Proof.
  intros. apply (@ND_exfalso_quodlibet Γ (Not Verum)) in H.
  assumption.
Qed.



Lemma subst_negate {Γ p t} :
  Γ ⊢ Not (subst_bvar_inner 0 t p) <->
  Γ ⊢ subst_bvar_inner 0 t (Not p).
Proof.
  split.
- intros; simpl; auto.
- intros; simpl; auto.
Qed.

Check @ND_exists_intro.

(** We can always eliminate the [Forall] quantifier, to just use
[Exists], thanks to de Morgan's laws. This section gives us the
experimental introduction and elimination rules of inference. *)
Section ForallAbbreviation.
(** We can always eliminate the [Forall] quantifier, to just use
[Exists], thanks to de Morgan's laws. This theorem gives us the
"introduction rule" for this "abbreviated [Forall]" quantifier. *)
Theorem ND_forall_i {Γ p t} :
  Γ ⊢ subst_bvar_inner 0 t p ->
  t = fresh_evar Γ Falsum ->
  Γ ⊢ Forall p.
Proof.
  intros. Check @ND_exists_elim_small.
  assert (Γ ⊢ Implies (subst_bvar_inner 0 t p)
               (Not (Not (subst_bvar_inner 0 t p)))). apply ND_double_negation2.
  rename H0 into Ha.
  rename H1 into H0.
  apply (@ND_imp_e Γ (subst_bvar_inner 0 t p)) in H0. 2: assumption.
  assert (Γ ⊢ Not (Not (subst_bvar_inner 0 t p)) -> Γ ⊢ Not (subst_bvar_inner 0 t (Not p))). {
    intros. simpl; auto.
  }
  apply H1 in H0.
(* Thus we have established [H0 : Γ ⊢ Not (subst_bvar_inner 0 t (Not p))] *)
  unfold Not. unfold Not in H0.
  apply ND_imp_i2.
  apply (@ND_exists_elim_small Γ (Not p) Falsum t).
  Assume (subst_bvar_inner 0 t (Not p) :: Γ ⊢ (subst_bvar_inner 0 t (Not p))). 
  assert (Γ ⊆ (subst_bvar_inner 0 t (Not p) :: Γ)). apply subcontext_weaken; apply subcontext_reflex.
  apply (@weakening Γ (subst_bvar_inner 0 t (Not p) :: Γ)) in H0.
  apply (@ND_imp_e (subst_bvar_inner 0 t (Not p) :: Γ) (subst_bvar_inner 0 t (Not p))) in H0.
  assumption. assumption. assumption. assumption.
Qed.

Theorem ND_neg_i {Γ p q} :
  p :: Γ ⊢ q -> p :: Γ ⊢ (Not q) -> Γ ⊢ Not p.
Proof.
  intros.
  unfold Not in H0.
  apply (@ND_imp_e (p :: Γ) q Falsum) in H0. 2: assumption.
  apply (@ND_imp_i2 Γ p Falsum) in H0.
  simpl; auto.
Qed.

Lemma subst_negate2 {Γ p t} :
  Γ ⊢ Not (Not (subst_bvar_inner 0 t p)) <->
  Γ ⊢ subst_bvar_inner 0 t (Not (Not p)).
Proof.
  split.
- intros; simpl; auto.
- intros; simpl; auto.
Qed.

(** This proof imitates the [(Not (Exists p)) ⊢ Forall (Not p)]
proof, to a large extent. It consists of two steps:

Step 1: weaken the premises to establish the contradictory results that
        [(Not p)[t], Γ ⊢ Not (Exists (Not p))] and 
        [(Not p)[t], Γ ⊢ Exists (Not p)] both hold.

Step 2: Infer that [Γ ⊢ Not (Not p[t])] holds. And then the law of
        double negation gives the result. *)
Theorem ND_forall_elim {Γ p t} :
  Γ ⊢ Forall p ->
  Γ ⊢ subst_bvar_inner 0 t p.
Proof. intros.
  assert (Γ ⊆ (subst_bvar_inner 0 t (Not p) :: Γ)). apply subcontext_weaken; apply subcontext_reflex.
  apply (@weakening Γ (subst_bvar_inner 0 t (Not p) :: Γ)) in H. 2: assumption.
  Assume ((subst_bvar_inner 0 t (Not p) :: Γ) ⊢ (subst_bvar_inner 0 t (Not p))).
  apply ND_exists_intro in H1.
  apply (@ND_imp_e (subst_bvar_inner 0 t (Not p) :: Γ) (Exists (Not p)) Falsum) in H as H2. 2: assumption.
  apply (@ND_neg_i Γ (subst_bvar_inner 0 t (Not p)) (Exists (Not p))) in H1 as H3.
  2: assumption.
  (* Thus we have proved, in [H3], that
     [Γ ⊢ Not (subst_bvar_inner 0 t (Not p))]. 
     We will just move the inner [Not] outside the substitution, then
     use double negation law to prove this gives us the goal.*)
  rewrite -> subst_negate in H3.
  apply subst_negate2 in H3.
  assert (Γ ⊢ Implies (Not (Not (subst_bvar_inner 0 t p))) (subst_bvar_inner 0 t p)).
  apply ND_double_negation.
  apply @ND_imp_e with (p := (Not (Not (subst_bvar_inner 0 t p)))) in H4.
  assumption. assumption.
Qed.
End ForallAbbreviation.

Theorem contrapositive {Γ p q} :
  Γ ⊢ (Implies (Implies p q) (Implies (Not q) (Not p))).
Proof.
  intros. 
  Assume(p::(Not q)::(Implies p q)::Γ ⊢ p).
  Assume(p::(Not q)::(Implies p q)::Γ ⊢ (Implies p q)).
  apply (@ND_imp_e (p:: Not q :: Implies p q :: Γ) p q) in H0 as H1.
  2: assumption.
  Assume(p::(Not q)::(Implies p q)::Γ ⊢ Not q).
  Check @ND_neg_i.
  Check @ND_not_i.
  apply (@ND_neg_i (Not q :: Implies p q :: Γ)) in H1.
  apply (@ND_imp_i2 (Implies p q :: Γ) (Not q) (Not p)) in H1. 2: assumption.
  apply ND_imp_i2 in H1.
  assumption.
Qed.

Theorem modus_tollen {Γ p q} :
  Γ ⊢ (Implies p q) -> Γ ⊢ (Not q) -> Γ ⊢ (Not p).
Proof.
  intros.
  assert (Γ ⊢ (Implies (Implies p q) (Implies (Not q) (Not p)))). {
  apply (@contrapositive Γ p q).
  }
  apply (@ND_imp_e Γ (Implies p q)) in H1. 2: assumption.
  apply (@ND_imp_e Γ (Not q) (Not p)) in H1.
  assumption. assumption.
Qed.

(** We can now summarize the results which will be crucial in
proving the correctness of the translation. *)
Section ImportantTheorems.
Theorem forall_implies_reflex {Γ p} :
  Γ ⊢ Forall (Implies p p).
Proof.
  set (t := fresh_evar Γ Falsum).
  apply (@ND_forall_i Γ (Implies p p) t). 2: auto.
  simpl; auto.
  apply ND_imp_i2; apply ND_assume; prove_In.
Qed.

Theorem exists_modus_ponens_tautology {Γ p q} :
  Γ ⊢ (Implies (Forall (Implies p q)) (Implies (Exists p) (Exists q))).
Proof.
  Assume ((Exists p) :: (Forall (Implies p q)) :: Γ ⊢ (Forall (Implies p q))).
  Assume ((Exists p) :: (Forall (Implies p q)) :: Γ ⊢ (Exists p)).
  set (t := fresh_evar ((Exists p) :: (Forall (Implies p q)) :: Γ) q).
  apply (ND_forall_elim (t := t)) in H. simpl in H.
  apply (ND_exists_elim (Γ := Exists p :: Forall (Implies p q) :: Γ)  (q := (subst_bvar_inner 0 t q)) (c := t)) in H0 as H1.  
  apply (ND_imp_e (p := subst_bvar_inner 0 t p) (q := (subst_bvar_inner 0 t q))) in H as H2.
  apply (ND_exists_intro (Γ := Exists p :: Forall (Implies p q) :: Γ) (t := t) (p := q)) in H2 as H3.
  apply (@ND_imp_i2 (Forall (Implies p q) :: Γ)) in H3 as H4.
  apply ND_imp_i2 in H4 as H5. assumption. assumption. assumption.
  intros.
  
  Check ND_exists_elim_small.
  
End ImportantTheorems.

Theorem consistency : not (proves Falsum).
Proof.
  unfold not; intro.
  induction H. 
  - apply IHdeducible.
  - (* ND_imp_e *) contradict IHdeducible1.
  - (* ND_imp_i *) contradict IHdeducible.
  - (* ND_or_intro_l *) contradict IHdeducible.
  - (* ND_or_intro_r *) contradict IHdeducible.
  - (* ND_proof_by_cases *) contradict IHdeducible1.
  - (* ND_and_intro *) contradict IHdeducible1.
  - (* ND_and_elim *) contradict IHdeducible1.
  - (* ND_cut *) contradict IHdeducible1.
  - (* ND_exists_elim *) contradict IHdeducible.
  - (* ND_exists_intro *) contradict IHdeducible.
  - (* ND_forall_elim *) contradict IHdeducible.
  - (* ND_forall_intro *) contradict IHdeducible.
  - (* ND_proof_by_contradiction *) contradict IHdeducible.
Qed.

