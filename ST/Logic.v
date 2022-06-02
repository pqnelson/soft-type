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

Example pred_subst_1 : subst (BVar 0) (Fun 0 "c" []) (P 3 "P" [Var (BVar 1); Var (BVar 0); Fun 2 "f" [Var (BVar 0); Var (FVar "y")]])
= (P 3 "P" [Var (BVar 1); (Fun 0 "c" []); Fun 2 "f" [(Fun 0 "c" []); Var (FVar "y")]]).
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
| Verum
| Atom : Predicate -> Formula
| Not : Formula -> Formula
| And : Formula -> Formula -> Formula
| Or : Formula -> Formula -> Formula
| Implies : Formula -> Formula -> Formula
| Forall : Formula -> Formula
| Exists : Formula -> Formula.

(** We can recursively test if two [Formula] objects are identical. This is an
equality at the level of syntax. *)
Fixpoint eq_formula (A B : Formula) : bool :=
match A,B with
| Falsum, Falsum => true
| Verum, Verum => true
| Atom (P n1 s1 args1), Atom (P n2 s2 args2) => 
      if andb (eqb n1 n2) (eqb s1 s2)
      then vectors_eqb args1 args2 term_eqb
      else false
| Not A1, Not B1 => eq_formula A1 B1
| And A1 A2, And B1 B2 => andb (eq_formula A1 B1) (eq_formula A2 B2)
| Or A1 A2, Or B1 B2 => andb (eq_formula A1 B1) (eq_formula A2 B2)
| Implies A1 A2, Implies B1 B2 =>  andb (eq_formula A1 B1) (eq_formula A2 B2)
| Forall A1, Forall B1 => eq_formula A1 B1
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
| Falsum | Verum => phi
| Atom pred => Atom (subst (FVar x) (Var (BVar n)) pred)
| Not fm => Not (var_closing_iter x n fm)
| And fm1 fm2 => And (var_closing_iter x n fm1) (var_closing_iter x n fm2)
| Or fm1 fm2 => Or (var_closing_iter x n fm1) (var_closing_iter x n fm2)
| Implies fm1 fm2 => Implies (var_closing_iter x n fm1) (var_closing_iter x n fm2)
| Forall fm => Forall (var_closing_iter x (S n) fm)
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
| Falsum | Verum => phi
| Atom pred => Atom (subst (BVar n) t pred)
| Not fm => Not (subst_bvar_inner n t fm)
| And fm1 fm2 => And (subst_bvar_inner n t fm1) (subst_bvar_inner n t fm2)
| Or fm1 fm2 => Or (subst_bvar_inner n t fm1) (subst_bvar_inner n t fm2)
| Implies fm1 fm2 => Implies (subst_bvar_inner n t fm1) (subst_bvar_inner n t fm2)
| Forall fm => Forall (subst_bvar_inner (S n) (lift (S n) 1 t) fm)
| Exists fm => Exists (subst_bvar_inner (S n) (lift (S n) 1 t) fm)
end.

(** Specialization and choosing a witness for existential quantification
amounts to the same "operations" of peeling off an outermost quantifier, then
behaving as expected. *)
Fixpoint quantifier_elim_subst (n : nat) (t : Term) (phi : Formula) : Formula :=
match phi with
| Forall fm => subst_bvar_inner n t fm
| Exists fm => subst_bvar_inner n t fm
| Not A => Not (quantifier_elim_subst n t A)
| And A B => And (quantifier_elim_subst n t A) (quantifier_elim_subst n t B)
| Or A B => Or (quantifier_elim_subst n t A) (quantifier_elim_subst n t B)
| Implies A B => Implies (quantifier_elim_subst n t A) (quantifier_elim_subst n t B)
| _ => phi
end.

Example subst_bvar_1 : quantifier_elim_subst 0 (Fun 0 "t" []) (Forall (Exists (Atom (P 2 "P" [Var (BVar 0); Var (BVar 1)]))))
= Exists (Atom (P 2 "P" [Var (BVar 0); Fun 0 "t" []])).
Proof.
  trivial.
Qed.

Fixpoint lift_formula (c d : nat) (phi : Formula) : Formula :=
  match phi with
  | Falsum | Verum => phi
  | Atom pred => Atom (lift c d pred)
  | Not fm => Not (lift_formula c d fm)
  | And fm1 fm2 => And (lift_formula c d fm1) (lift_formula c d fm2)
  | Or fm1 fm2 => Or (lift_formula c d fm1) (lift_formula c d fm2)
  | Implies fm1 fm2 => Implies (lift_formula c d fm1) (lift_formula c d fm2)
  | Forall fm => Forall (lift_formula (S c) d fm)
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
  fresh : name -> A -> Prop
}.

Fixpoint fresh_term (c : name) (t : Term) : Prop :=
match t with
| Var (FVar x) => x = c
| Var (BVar _) => True
| EConst _ => True
| Fun n f args => let fix fresh_args {k} (ars : Vector.t Term k) :=
                  match ars with
                  | tm::ars1 => (fresh_term c tm) /\ fresh_args ars1
                  | [] => True
                  end
                  in fresh_args args
end.

Fixpoint nat_in_list (n : nat) (l : list nat) : bool :=
match l with
| List.nil => false
| List.cons h tl => if eqb n h then true else nat_in_list h tl
end.

Fixpoint insert (i : nat) (l : list nat) : list nat :=
match l with
| List.nil => List.cons i List.nil
| List.cons h t => if ltb i h then (List.cons i l) 
                   else if Nat.eqb i h then l
                   else (List.cons h (insert i t))
end.
  
Fixpoint insert_in_list (n : nat) (l : list nat) : list nat :=
match l with
| List.nil => List.cons n l
| List.cons h tl => if lt_dec h n then (List.cons n l)
                    else if Nat.eqb h n then l
                    else insert_in_list n tl
end.

Lemma insert_cons : forall (i h : nat) (t : list nat),
  h < i -> insert i (List.cons h t) = List.cons h (insert i t).
Admitted.

Lemma insert_cons_eq : forall (i h : nat) (t : list nat),
  h = i -> insert i (List.cons h t) = List.cons i t.
Admitted.

Inductive sorted : list nat -> Prop :=
| sorted_nil : sorted List.nil
| sorted_l : forall (n : nat),
  sorted (List.cons n List.nil)
| sorted_cons : forall (x y : nat) (l : list nat),
  x < y -> sorted (List.cons y l) -> sorted (List.cons x (List.cons y l)).
  
Lemma sorted_tl : forall (a : nat) (l : list nat),
  sorted (List.cons a l) -> sorted l.
Proof.
  intros. induction l.
  - apply sorted_nil.
  - inversion H. assumption.
Qed.

Hint Constructors sorted : core.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.EqNat.
Require Import OrdersTac Lia.
Require Import Coq.Bool.Bool.
Require Import NPeano.
Import ListNotations.

Lemma eqb_isnt_ltb : forall (m n : nat),
  true = Nat.eqb n m -> false = Nat.ltb n m.
Proof.
  intros. symmetry.
  unfold Nat.ltb.
  rewrite (leb_iff_conv m (S n)). 
  assert (n = m). { apply beq_nat_true. auto. }
  replace (m) with (n). auto.
Qed.

Import ListNotations.

Lemma insert_lt_singleton : forall (n n0 : nat),
  n < n0 -> insert n [n0] = [n; n0]%list.
Proof.
  intros. unfold insert. apply (Nat.ltb_lt n n0) in H as H0.
  rewrite H0. reflexivity.
Qed.

Lemma gt_is_neither_leb_nor_eqb : forall (n n0 : nat),
  n > n0 -> (Nat.eqb n n0 = false) /\ (Nat.ltb n n0 = false).
Admitted.

Lemma insert_gt_singleton : forall (n n0 : nat),
  n > n0 -> insert n [n0] = [n0; n]%list.
Proof.
  intros. unfold insert. apply (gt_is_neither_leb_nor_eqb n n0) in H as H0.
  assert ((n =? n0)%nat = false). apply H0.
  assert ((n <? n0)%nat = false). apply H0.
  rewrite H1. rewrite H2. reflexivity.
Qed.

Lemma lt_to_gt : forall (a b : nat),
  a > b -> b < a.
Admitted.

Lemma leb_to_ltb : forall (a b : nat),
  Nat.leb a b = false -> Nat.ltb a b = false.
Admitted.

Lemma not_leb_implies_not_eqb : forall (n n0 : nat),
  (n <=? n0)%nat = false -> Nat.eqb n n0 = false.
Admitted.

Lemma not_leb_implies_not_ltb : forall (n a0 : nat),
  (n <=? a0)%nat = false -> (n <? a0)%nat = false.
Admitted.

Lemma eqb_implies_not_ltb : forall (n n0 : nat),
  Nat.eqb n n0 = true -> (n <? n0)%nat = false.
Admitted.

Lemma every_nat_ordered : forall (n n0 : nat),
  n < n0 \/ n = n0 \/ n > n0.
Admitted.

Lemma swap_sorted_car : forall (a a0 : nat) (l : list nat),
  a < a0 -> sorted (a0 :: l)%list -> sorted (a :: l)%list.
Admitted.

Lemma sort_head : forall (a a0 n : nat) (l : list nat),
  sorted (insert n (a0 :: l)%list) -> 
  Some n = List.hd_error (insert n ((a0 :: l)%list)) \/ List.hd_error (insert n ((a0 :: l)%list)) = Some a0.
Admitted.

Lemma insert_sorted_ll : forall (a n : nat) (l : list nat),
  a < n -> sorted (a :: l) -> sorted (insert n l) -> sorted (a :: (insert n l)).
Proof.
  intros. apply (sorted_tl a l) in H0 as H2.
  (* destruct H2. *)
  (* induction H2. *)
  induction l.
  - (* sorted (a :: insert n []) *)
    unfold insert. auto.
  - (* sorted (a :: insert n (a0 :: l)) *)
    inversion H0. clear H7.
    apply (swap_sorted_car a a0 l) in H5 as H7.
    assert (n < a0 \/ n = a0 \/ n > a0). { apply (every_nat_ordered n a0). }
    destruct H8.
  -- (* n < a0 -> sorted (a :: insert n (a0 :: l)) *)
     assert (insert n (a0 :: l)%list = (n :: a0 :: l)%list). {
     unfold insert. apply (Nat.ltb_lt n a0) in H8 as H9. rewrite H9. reflexivity.
     } rewrite H9. rewrite H9 in H1.
     apply (sorted_cons a n (a0 :: l)%list) in H as H10.
     assumption. assumption.
  -- destruct H8.
  --- (* n = a0 -> sorted (a :: insert n (a0 :: l)) *)
      assert (insert n (a0 :: l)%list = (a0 :: l)%list). {
      unfold insert. apply (Nat.eqb_eq n a0) in H8 as H9. rewrite H9. auto.
      apply (eqb_implies_not_ltb n a0) in H9 as H10. rewrite H10. reflexivity.
      } rewrite H9. assumption.
  --- (* n > a0 -> sorted (a :: insert n (a0 :: l)) *)
      set (l1 := (insert n l)).
      set (l2 := (List.cons a0 (insert n l))).
      assert (l2 = insert n (a0 :: l)%list). {
      unfold insert. apply (leb_correct_conv a0 n) in H8 as H9.
      apply (not_leb_implies_not_ltb n a0) in H9 as H10.
      rewrite H10. clear H10.
      apply (not_leb_implies_not_eqb n a0) in H9 as H10. rewrite H10.
      unfold insert in l2. auto.
      }
      rewrite <- H9.
      rewrite <- H9 in H1.
      Check sorted_tl. apply sorted_tl in H1 as H12.
      Check sorted_cons. apply (sorted_cons a a0 (insert n l)).
      assumption. assumption.
  -- assumption.
Qed.

Theorem insert_sorted :
  forall (n : nat) (l : list nat),
  sorted l -> sorted (insert n l).
Proof.
  intros. induction l as [| a].
  - unfold insert. apply sorted_l.
  - (* unfold insert. *) induction (lt_eq_lt_dec n a) as [Hleq | Hgt]. destruct Hleq.
    + (* case: n < a *)
      assert (true = ltb n a). { apply Nat.ltb_lt in l0. symmetry; assumption. } 
      unfold insert. rewrite <- H0; apply sorted_cons. 
      assumption. assumption.
    + (* case: n = a *)
      assert (true = Nat.eqb n a). { apply Nat.eqb_eq in e. symmetry; assumption. }
      assert (false = Nat.ltb n a). { apply eqb_isnt_ltb. assumption. }
      unfold insert. rewrite <- H0. rewrite <- H1. assumption.
    + (* case: n > a *)
      apply (Nat.ltb_lt a n) in Hgt as H2.
      apply (leb_correct_conv a n) in Hgt as H3. 
      apply (Nat.leb_gt n a) in H3 as H4. intuition. auto.
      assert (insert n (a :: l) = List.cons a (insert n l)). { apply (insert_cons n a l). assumption. }
      rewrite H0.
      apply (sorted_tl a l) in H as H5. apply IHl in H5.
      apply (insert_sorted_ll a n l). assumption. assumption. assumption.
Qed.

Fixpoint insert_merge (l1 l2 : list nat) : list nat :=
match l1 with
| []%list => l2
| (h::t)%list => insert_merge t (insert h l2)
end.
  
Fixpoint existential_vars_term (t : Term) : list nat :=
match t with
| Var _ => List.nil
| EConst n => List.cons n List.nil
| Fun n f args => let fix exist_args {k} (ars : Vector.t Term k) :=
                  match ars with
                  | tm::ars1 => insert_merge (existential_vars_term tm) (exist_args ars1)
                  | [] => List.nil
                  end
                  in exist_args args
end.


Global Instance FreshTerm : Fresh Term := {
  fresh := fresh_term
}.

Global Instance FreshPredicate : Fresh Predicate := {
  fresh (c : name) (p : Predicate) :=
  match p with
  | P n s args => Vector.Forall (fun (arg : Term) => fresh c arg) args
  end
}.

Fixpoint fresh_formula (c : name) (p : Formula) : Prop :=
  match p with
  | Falsum => True
  | Verum => True
  | Atom phi => fresh c phi
  | Not A => fresh_formula c A
  | And A B | Or A B | Implies A B => (fresh_formula c A) /\ (fresh_formula c B)
  | Forall A | Exists A => fresh_formula c A
  end.
  
Global Instance FreshFormula : Fresh Formula := {
  fresh := fresh_formula
}.

Fixpoint fresh_list (c : name) (Γ : list Formula) : Prop :=
match Γ with
| List.nil => True
| List.cons p Γ' => (fresh c p) /\ (fresh_list c Γ')
end.

Global Instance FreshContext : Fresh (list Formula) := {
  fresh := fresh_list
}.

Import ListNotations.
Reserved Notation "Γ ⊢ P" (no associativity, at level 61).

Inductive deducible : list Formula -> Formula -> Prop :=
| ND_exfalso_quodlibet {Γ p} :
  Γ ⊢ Falsum ->
  Γ ⊢ p
| ND_True_intro {Γ} :
  Γ ⊢ Verum
| ND_assume {Γ p} :
  List.In p Γ -> 
  Γ ⊢ p
| ND_imp_e {Γ p q} :
  Γ ⊢ Implies p q -> Γ ⊢ p ->
  Γ ⊢ q
  (*
| ND_imp_i {Γ p q} :
  List.In p Γ -> Γ ⊢ q ->
  (List.remove Formula_eq_dec p Γ) ⊢ Implies p q
  *)
| ND_imp_i2 {Γ p q} :
  p::Γ ⊢ q -> Γ ⊢ Implies p q
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
| ND_exists_elim {Γ p q c} :
  Γ ⊢ (Exists p) -> fresh c (List.cons p (List.cons q Γ)) ->
  (subst_bvar_inner 0 (constant c) p)::Γ ⊢ q ->
  Γ ⊢ q
| ND_exists_intro {Γ p c} :
  Γ ⊢ (subst_bvar_inner 0 (constant c) p) -> 
  Γ ⊢ Exists p
| ND_forall_elim {Γ p t} :
  Γ ⊢ (Forall p) -> 
  Γ ⊢ (quantifier_elim_subst 0 t p)
| ND_forall_intro {Γ p c} :
  Γ ⊢ (subst_bvar_inner 0 (constant c) p) -> 
  fresh c (List.cons p Γ) ->
  Γ ⊢ Forall p
where "Γ ⊢ P" := (deducible Γ P).

Definition proves (fm : Formula) : Prop := deducible List.nil fm.

Hint Unfold GlobalContext LocalContext : typeclass_instances.
Hint Constructors well_typed deducible : core.

Theorem Verum_implies_Verum :
  proves (Implies Verum Verum).
Proof. 
  unfold proves; auto.
Qed.


Definition subcontext (Γ1 Γ2 : list Formula) : Prop :=
  forall P, List.In P Γ1 -> List.In P Γ2.
  
Definition supcontext (Γ1 Γ2 : list Formula) : Prop :=
  subcontext Γ2 Γ1.
Infix "⊆" := subcontext (no associativity, at level 70).
Infix "⊇" := supcontext (no associativity, at level 70).

Lemma cons_subcontext : forall (Γ : list Formula) (P : Formula),
  Γ ⊆ List.cons P Γ.
Proof.
  intros. right. assumption.
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

(*
Require Export List.
Require Export RelationClasses.
Require Export Morphisms.
*)

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
Admitted.

(* Suppose [Subcontext Γ1 Γ2]. If [fresh c Γ2], then [fresh c Γ1]. *)
Global Instance fresh_cons_proper :
  Proper (eq ++> subcontext --> Basics.impl) fresh.
Proof.
  intros P Q [] Γ1 Γ2 ?. unfold Basics.flip in H. unfold Basics.impl.
  intros H1.
  unfold fresh; unfold FreshContext; unfold fresh_list.
  induction Γ2. auto.
  assert (Γ2 ⊆ a :: Γ2). apply cons_subcontext.
  assert (Γ2 ⊆ Γ1).
  apply (subcontext_trans Γ2 (a :: Γ2) Γ1); assumption; assumption.
  apply IHΓ2 in H2 as IH; split. apply (fresh_in_head H). assumption.
  assumption.
Qed.

Theorem fresh_cons_1 : forall (Γ1 Γ2 : list Formula) (P : Formula) (c : name),
  Γ1 ⊆ Γ2 -> fresh c (P :: Γ1) -> fresh c (P :: Γ2).
Admitted.

Theorem fresh_cons_2 : forall (Γ1 Γ2 : list Formula) (P Q : Formula) (c : name),
  Γ1 ⊆ Γ2 -> fresh c (P :: Q :: Γ1) -> fresh c (P :: Q :: Γ2).
Admitted.
(*
Proof.
  intros. unfold fresh in H0; unfold FreshContext in H0; unfold fresh_list in H0.
  unfold fresh; unfold FreshContext; unfold fresh_list. intuition.
  apply H.
   set (G1 := Q :: Γ1). set (G2 := Q :: Γ2).
Admitted.
*)

Global Instance ND_context_extension :
  Proper (subcontext ++> eq ==> Basics.impl) deducible.
Proof.
intros Γ₁ Γ₂ ? P Q [] ?. revert Γ₂ H. induction H0; intros.
+ apply ND_exfalso_quodlibet. auto.
+ apply ND_True_intro.
+ apply ND_assume. auto.
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
+ apply (ND_exists_elim (p := p) (q := q) (c := c)). auto.
  apply (fresh_cons_2 Γ Γ₂ p q). assumption. apply H. apply IHdeducible2. f_equiv. assumption.
+ apply (ND_exists_intro (p := p) (c := c)); auto.
+ apply (ND_forall_elim (p := p) (t := t)). auto.
+ apply (ND_forall_intro (p := p) (c := c)). auto.
  apply (fresh_cons_1 Γ Γ₂ p). apply H1. apply H.
Qed.

Theorem weakening : forall (Γ1 Γ2 : list Formula) (P : Formula),
  Γ1 ⊢ P ->
  Γ1 ⊆ Γ2 ->
  Γ2 ⊢ P.
Proof.
  intros.
  refine (ND_context_extension _ _ _ _ _ eq_refl H).
  assumption.
Qed.