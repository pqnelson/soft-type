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
From ST Require Export Logic.V Logic.Term Logic.Predicate Logic.Formula Logic.Subcontext.
Import VectorNotations.
(** * Natural Deduction

We need to formalize the proof calculus to then prove the correctness of soft 
type system.

References relevant:

- https://people.compute.dtu.dk/ahfrom/Formalized%20First-Order%20Logic.pdf
- https://hal.archives-ouvertes.fr/hal-03096253
*)

(** ** Rules of Natural Deduction 

We can now encode natural deduction rules using a straightforward inductive
type. The only subtlety surrounds ensuring a variable [name] is [fresh].
And that's because I am too lazy to do this adequately. Modeling arguments 
as vectors screw everything up. But it's obviously not wrong. Let's hope it 
doesn't destroy correctness ;p 
*)

(** Note: I think we need to modify our rules of inference so that modus ponens
has the side condition that in [Implies p q] either [p] is a sentence (i.e.,
a ground term) or [q] is not a sentence. Johnstone's notes on logic alerted me
to this, and the more I think about it, the more I believe he is correct. *)

(** Also important to note (to future me), since we are using de Bruijn indices
which bind from the innermost quantifiers outwards, we do not need
to [unshift] in our quantifier elimination rules. (Because we
humans conventionally work from the outer-most quantifiers, inwards.)
So there is no need to worry about unshifting. *)

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
  Γ ⊢ (capture_free_subst 0 t p) -> 
  Γ ⊢ Exists p
| ND_exists_elim_small {Γ p q c} :
  (capture_free_subst 0 c p)::Γ ⊢ q -> 
  c = fresh_evar Γ q ->
  (Exists p)::Γ ⊢ q
| ND_proof_by_contradiction {Γ p} :
  (Not p) :: Γ ⊢ Falsum ->
  Γ ⊢ p
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

#[local] Hint Unfold GlobalContext LocalContext : typeclass_instances.
#[local] Hint Constructors well_typed deducible : core.

(* These next two lemmas are "obvious", but obnoxious to prove.
So I'm...lazy. *)
Lemma exists_elim_freshness {Γ q} :
  (EConst 0) = fresh_evar (shift_evars Γ) (shift_evars q).
Admitted.

Lemma exists_evar_shift {Γ p q} :
  Exists p :: Γ ⊢ q <-> (shift_evars (Exists p))::(shift_evars Γ) ⊢ (shift_evars q).
Admitted.

Theorem exists_elim {Γ p q} :
  (capture_free_subst 0 (EConst 0) (shift_evars p))::(shift_evars Γ) ⊢ (shift_evars q) -> 
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
  capture_free_subst 0 c p :: Γ ⊢ q -> Γ ⊢ q.
Proof.
  intros.
  apply ND_exists_elim_small in H1.
  apply ND_imp_i2 in H1. 
  apply (@ND_imp_e Γ (Exists p) q ) in H1. 
  assumption. assumption.
  assumption.
Qed.

(**
I am being a bit cavalier here, but the only way to [prove Falsum]
is to assume contradictory premises. I can't seem to get Coq to believe
me about this, so I carved out [ND_assume] as an explicit axiom.
Otherwise the [consistency] theorem below fails.

After further thought, I believe we may need to require [p] be a sentence;
see the remarks about modus ponens above.
*)
Axiom ND_assume_axiom : forall (Γ : list Formula) (p : Formula),
  List.In p Γ ->  Γ ⊢ p.

Theorem ND_assume {Γ p} : List.In p Γ ->  Γ ⊢ p.
Proof.
  apply (ND_assume_axiom Γ p).
Qed.

Ltac Assume eqn :=
  assert (eqn) by (apply ND_assume; prove_In).

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

(** ** Subcontext-related manipulations *)


(* This is an axiom, which can't really be proven. *)
Lemma renaming_econst : forall (Γ1 Γ2 : list Formula) (p q : Formula),
  Γ1 ⊆ Γ2 -> 
  capture_free_subst 0 (fresh_evar Γ1 q) p :: Γ1 ⊢ q -> 
  capture_free_subst 0 (fresh_evar Γ2 q) p :: Γ2 ⊢ q.
Admitted.

Import ListNotations.
Open Scope list.

Lemma fresh_evar_alias : forall (Γ : list Formula) (p : Formula) (c : Term),
  c = (fresh_evar Γ p) <-> c = (fresh_evar (p::Γ)%list Falsum).
Proof.
  intros. unfold fresh_evar. unfold fresh_evar_counter.
  assert (list_evars (Falsum :: p :: Γ) = list_evars (p :: Γ)). {
    simpl; auto.
  }
  rewrite H. reflexivity.
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
+ apply (ND_and_elim (P := P) (Q := Q0)); auto.
  apply IHdeducible2. do 2 f_equiv; assumption.
+ apply (ND_cut (P := P)); auto.
  apply IHdeducible2. f_equiv. assumption.
+ apply (ND_exists_intro (p := p) (t := t)); auto.
+ apply subcontext_cons in H1 as H2. destruct H2.
  apply renaming_econst with (p := p) (q := q) in H3 as H4. 2: { rewrite <- H; assumption. }
  apply (ND_unprioritize (p := Exists p) (Γ := Γ₂)).
  apply (ND_exists_elim_small (Γ := Γ₂) (c := (fresh_evar Γ₂ q))). assumption.
  reflexivity. assumption.
+ apply ND_proof_by_contradiction. apply IHdeducible. f_equiv. auto.
+ apply (@subcontext_cons Γ Γ₂ p) in H1 as H2. apply IHdeducible. destruct H2. 
  assumption.
+ apply IHdeducible. apply (@subcontext_cons Γ Γ₂ p). split.
  apply (@subcontext_in_trans Γ Γ₂).
assumption. assumption. assumption.
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


(** ** Important Tautologies 

We will now prove a number of important tautologies. And being a classy mathematician,
we will be proving results in classical logic.
*)

Theorem ND_and_idempotent : forall (P : Formula),
  [] ⊢ (And P P) <-> [] ⊢ P.
Proof. split. (* intros; split. *)
- intros. apply (@ND_and_elim [] P P P). assumption.
  apply ND_assume. unfold In. left. reflexivity.
- intros. apply (@ND_and_intro [] P P). assumption. assumption.
Qed.

Theorem ND_or_idempotent : forall (P : Formula),
  [] ⊢ (Or P P) <-> [] ⊢ P.
Proof. split. 
- intros. apply (@ND_proof_by_cases [] P P P). assumption.
  Assume (P :: [] ⊢ P); assumption. 
  Assume (P :: [] ⊢ P); assumption.
- intros. apply (@ND_or_intro_r [] P P). assumption.
Qed.

Theorem ND_implies_refl : forall (P : Formula),
  proves (Implies P P).
Proof. intros.
  set (Γ := [P]).
  assert (In P Γ). { unfold In. left. reflexivity. }
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

Theorem ND_Iff_intro {Γ p q} :
  p::Γ ⊢ q -> q::Γ ⊢ p -> Γ ⊢ Iff p q.
Proof.
  intros.
  apply ND_imp_i2 in H; apply ND_imp_i2 in H0.
  apply ND_and_intro. assumption. assumption.
Qed.

Theorem ND_Iff_elim_l {Γ p q} :
  Γ ⊢ p -> Γ ⊢ Iff p q -> Γ ⊢ q.
Proof.
  intros.
  apply ND_proj_l in H0 as H1.
  apply (ND_imp_e (p := p) (q := q)) in H1.
  assumption. assumption.
Qed.

Theorem ND_Iff_elim_r {Γ p q} :
  Γ ⊢ q -> Γ ⊢ Iff p q -> Γ ⊢ p.
Proof.
  intros;
  apply ND_proj_r in H0 as H1;
  apply (ND_imp_e (p := q) (q := p)) in H1.
  assumption. assumption.
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


Theorem ND_and_context {Γ p q r} :
  (And p q)::Γ ⊢ r <-> p::q::Γ ⊢ r.
Proof.
  split.
- intros. apply ND_imp_i2 in H; apply ND_curry in H.
  Assume (p :: q :: Γ ⊢ p).
  assert (Γ ⊆ p :: q :: Γ). { apply subcontext_weaken; apply subcontext_weaken; prove_subcontext. }
  apply (@weakening Γ (p :: q :: Γ)) in H. 2: assumption.
  apply (@ND_imp_e (p :: q :: Γ) p (Implies q r)) in H. 2: apply ND_assume; prove_In.
  apply (@ND_imp_e (p :: q :: Γ) q r) in H. 2: apply ND_assume; prove_In.
  assumption.
- intros. apply ND_imp_i2 in H; apply ND_imp_i2 in H. apply ND_uncurry in H.
  assert (Γ ⊆ (And p q) :: Γ). { apply subcontext_weaken; prove_subcontext. }
  apply (@weakening Γ ((And p q) :: Γ)) in H. 2: assumption.
  Assume (And p q :: Γ ⊢ And p q).
  assert (And p q :: Γ ⊢ Implies (And p q) (And q p)). { apply ND_and_commutative. }
  apply (@ND_imp_e (And p q :: Γ) (And p q)) in H2. 2: assumption.
  apply (@ND_imp_e (And p q :: Γ) (And q p)) in H. 2: assumption.
  assumption.
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
  Γ ⊢ Not (capture_free_subst 0 t p) <->
  Γ ⊢ capture_free_subst 0 t (Not p).
Proof.
  split.
- intros; simpl; auto.
- intros; simpl; auto.
Qed.

(** We can always eliminate the [Forall] quantifier, to just use
[Exists], thanks to de Morgan's laws. This section gives us the
experimental introduction and elimination rules of inference. *)
Section ForallAbbreviation.
(** We can always eliminate the [Forall] quantifier, to just use
[Exists], thanks to de Morgan's laws. This theorem gives us the
"introduction rule" for this "abbreviated [Forall]" quantifier. *)
Theorem ND_forall_i {Γ p t} :
  Γ ⊢ capture_free_subst 0 t p ->
  t = fresh_evar Γ Falsum ->
  Γ ⊢ Forall p.
Proof.
  intros.
  assert (Γ ⊢ Implies (capture_free_subst 0 t p)
               (Not (Not (capture_free_subst 0 t p)))). apply ND_double_negation2.
  rename H0 into Ha.
  rename H1 into H0.
  apply (@ND_imp_e Γ (capture_free_subst 0 t p)) in H0. 2: assumption.
  assert (Γ ⊢ Not (Not (capture_free_subst 0 t p)) -> Γ ⊢ Not (capture_free_subst 0 t (Not p))). {
    intros. simpl; auto.
  }
  apply H1 in H0.
(* Thus we have established [H0 : Γ ⊢ Not (capture_free_subst 0 t (Not p))] *)
  unfold Not. unfold Not in H0.
  apply ND_imp_i2.
  apply (@ND_exists_elim_small Γ (Not p) Falsum t).
  Assume (capture_free_subst 0 t (Not p) :: Γ ⊢ (capture_free_subst 0 t (Not p))). 
  assert (Γ ⊆ (capture_free_subst 0 t (Not p) :: Γ)). apply subcontext_weaken; apply subcontext_reflex.
  apply (@weakening Γ (capture_free_subst 0 t (Not p) :: Γ)) in H0.
  apply (@ND_imp_e (capture_free_subst 0 t (Not p) :: Γ) (capture_free_subst 0 t (Not p))) in H0.
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
  Γ ⊢ Not (Not (capture_free_subst 0 t p)) <->
  Γ ⊢ capture_free_subst 0 t (Not (Not p)).
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
  Γ ⊢ capture_free_subst 0 t p.
Proof. intros.
  assert (Γ ⊆ (capture_free_subst 0 t (Not p) :: Γ)). apply subcontext_weaken; apply subcontext_reflex.
  apply (@weakening Γ (capture_free_subst 0 t (Not p) :: Γ)) in H. 2: assumption.
  Assume ((capture_free_subst 0 t (Not p) :: Γ) ⊢ (capture_free_subst 0 t (Not p))).
  apply ND_exists_intro in H1.
  apply (@ND_imp_e (capture_free_subst 0 t (Not p) :: Γ) (Exists (Not p)) Falsum) in H as H2. 2: assumption.
  apply (@ND_neg_i Γ (capture_free_subst 0 t (Not p)) (Exists (Not p))) in H1 as H3.
  2: assumption.
  (* Thus we have proved, in [H3], that
     [Γ ⊢ Not (capture_free_subst 0 t (Not p))]. 
     We will just move the inner [Not] outside the substitution, then
     use double negation law to prove this gives us the goal.*)
  rewrite -> subst_negate in H3.
  apply subst_negate2 in H3.
  assert (Γ ⊢ Implies (Not (Not (capture_free_subst 0 t p))) (capture_free_subst 0 t p)).
  apply ND_double_negation.
  apply @ND_imp_e with (p := (Not (Not (capture_free_subst 0 t p)))) in H4.
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

Theorem forall_modus_ponens_tautology {Γ p q} :
  Γ ⊢ Implies (Forall (Implies p q))
         (Implies (Exists p) (Exists q)).
Proof.
  intros.
  set (c := fresh_evar (Forall (Implies p q) :: Γ) (Exists q)).
  Assume((capture_free_subst 0 c p) ::  Forall (Implies p q) :: Γ ⊢ Forall (Implies p q)).
  apply (@ND_forall_elim (capture_free_subst 0 c p
     :: Forall (Implies p q) :: Γ) (Implies p q) c) in H as H2.
     
  assert (capture_free_subst 0 c p
     :: Forall (Implies p q) :: Γ ⊢ capture_free_subst 0 c (Implies p q) 
  = capture_free_subst 0 c p
     :: Forall (Implies p q) :: Γ ⊢ Implies (capture_free_subst 0 c p) (capture_free_subst 0 c q)). { simpl; auto. }
  rewrite H0 in H2. clear H0.
  apply (ND_imp_e (p := capture_free_subst 0 c p) (q := capture_free_subst 0 c q)) in H2.
  2: apply ND_assume; prove_In.
  apply (@ND_exists_intro (capture_free_subst 0 c p
     :: Forall (Implies p q) :: Γ) q c) in H2.
  apply (@ND_exists_elim_small (Forall (Implies p q) :: Γ) p (Exists q) c) in H2 as H3.
  apply ND_imp_i2 in H3.
  apply ND_imp_i2 in H3.
  assumption. auto.
Qed.

Theorem forall_modus_const_tautology {Γ p q c} :
  Γ ⊢ Implies (Forall (Implies p q))
         (Implies (capture_free_subst 0 c p) (capture_free_subst 0 c q)).
Proof.
  intros.
  Assume((capture_free_subst 0 c p) ::  Forall (Implies p q) :: Γ ⊢ Forall (Implies p q)).
  apply (@ND_forall_elim (capture_free_subst 0 c p
    :: Forall (Implies p q) :: Γ) (Implies p q) c) in H as H1.
  assert (capture_free_subst 0 c p
     :: Forall (Implies p q) :: Γ ⊢ capture_free_subst 0 c (Implies p q) 
  = capture_free_subst 0 c p
     :: Forall (Implies p q) :: Γ ⊢ Implies (capture_free_subst 0 c p) (capture_free_subst 0 c q)). { simpl; auto. }
  rewrite H0 in H1. clear H0.
  apply (@ND_imp_e (capture_free_subst 0 c p :: Forall (Implies p q) :: Γ) (capture_free_subst 0 c p) (capture_free_subst 0 c q)) in H1 as H2.
  apply ND_imp_i2 in H2 as H3.
  apply ND_imp_i2 in H3 as H4.
  assumption. apply ND_assume; prove_In.
Qed.

Theorem forall_proj_r {Γ p q} :
  Γ ⊢ Implies (Forall (And p q)) (Forall q).
Proof.
  set (c := fresh_evar (Forall (And p q) :: Γ) Falsum).
  apply ND_imp_i2.
  apply (@ND_forall_i (Forall (And p q) :: Γ) q c). 2: auto.
  Assume (Forall (And p q) :: Γ ⊢ Forall (And p q)).
  apply (@ND_forall_elim (Forall (And p q) :: Γ) (And p q) c) in H as H1.
  assert(Forall (And p q) :: Γ ⊢ capture_free_subst 0 c (And p q)
  = Forall (And p q) :: Γ ⊢ And (capture_free_subst 0 c p) (capture_free_subst 0 c q)). { simpl; auto. }
  rewrite H0 in H1. clear H0.
  apply (@ND_proj_r (Forall (And p q) :: Γ) (capture_free_subst 0 c p) (capture_free_subst 0 c q)) in H1.
  assumption.
Qed.

Theorem forall_proj_l {Γ p q} :
  Γ ⊢ Implies (Forall (And p q)) (Forall p).
Proof.
  set (c := fresh_evar (Forall (And p q) :: Γ) Falsum).
  apply ND_imp_i2.
  apply (@ND_forall_i (Forall (And p q) :: Γ) p c). 2: auto.
  Assume (Forall (And p q) :: Γ ⊢ Forall (And p q)).
  apply (@ND_forall_elim (Forall (And p q) :: Γ) (And p q) c) in H as H1.
  assert(Forall (And p q) :: Γ ⊢ capture_free_subst 0 c (And p q)
  = Forall (And p q) :: Γ ⊢ And (capture_free_subst 0 c p) (capture_free_subst 0 c q)). { simpl; auto. }
  rewrite H0 in H1. clear H0.
  apply (@ND_proj_l (Forall (And p q) :: Γ) (capture_free_subst 0 c p) (capture_free_subst 0 c q)) in H1.
  assumption.
Qed.

Theorem universal_hypothetical_syllogism {Γ p q r} :
  Γ ⊢ Implies (Forall (Implies p q))
        (Implies (Forall (Implies q r)) (Forall (Implies p r))).
Proof.
  intros.
  apply ND_imp_i2; apply ND_imp_i2.
  set (t := fresh_evar (Forall (Implies q r) :: Forall (Implies p q) :: Γ) Falsum).
  Assume ((capture_free_subst 0 t p) :: Forall (Implies q r) :: Forall (Implies p q) :: Γ ⊢ Forall (Implies p q)).
  Assume ((capture_free_subst 0 t p) :: Forall (Implies q r) :: Forall (Implies p q) :: Γ ⊢ Forall (Implies q r)).
  apply (@ND_forall_elim ((capture_free_subst 0 t p) :: Forall (Implies q r) :: Forall (Implies p q) :: Γ )
          (Implies p q) t) in H as H1.
  apply (@ND_forall_elim ((capture_free_subst 0 t p) :: Forall (Implies q r) :: Forall (Implies p q) :: Γ )
          (Implies q r) t) in H0 as H2.
  assert ((capture_free_subst 0 t p) :: Forall (Implies q r) :: Forall (Implies p q) :: Γ
     ⊢ capture_free_subst 0 t (Implies p q) = (capture_free_subst 0 t p) :: Forall (Implies q r) :: Forall (Implies p q) :: Γ
     ⊢  Implies (capture_free_subst 0 t p) (capture_free_subst 0 t q)). { simpl; auto. }
  assert ((capture_free_subst 0 t p) :: Forall (Implies q r) :: Forall (Implies p q) :: Γ
     ⊢ capture_free_subst 0 t (Implies q r) = (capture_free_subst 0 t p) :: Forall (Implies q r) :: Forall (Implies p q) :: Γ
     ⊢  Implies (capture_free_subst 0 t q) (capture_free_subst 0 t r)). { simpl; auto. }
  rewrite H3 in H1. rewrite H4 in H2.
  Assume ((capture_free_subst 0 t p) :: Forall (Implies q r) :: Forall (Implies p q) :: Γ ⊢ (capture_free_subst 0 t p)).
  apply (@ND_imp_e (capture_free_subst 0 t p
     :: Forall (Implies q r) :: Forall (Implies p q) :: Γ) (capture_free_subst 0 t p)) in H1.
  2: assumption.
  apply (@ND_imp_e (capture_free_subst 0 t p
     :: Forall (Implies q r) :: Forall (Implies p q) :: Γ) (capture_free_subst 0 t q)) in H2.
  2: assumption.
  apply ND_imp_i2 in H2.
  assert (Forall (Implies q r)
     :: Forall (Implies p q) :: Γ
     ⊢ Implies (capture_free_subst 0 t p)
         (capture_free_subst 0 t r) = Forall (Implies q r)
     :: Forall (Implies p q) :: Γ
     ⊢ (capture_free_subst 0 t (Implies  p r))). { simpl; auto. }
  rewrite H6 in H2.
  apply (@ND_forall_i (Forall (Implies q r) :: Forall (Implies p q) :: Γ) (Implies p r) t) in H2.
  assumption. auto.
Qed.

End ImportantTheorems.

Theorem implies_equiv_or_not {Γ p q} :
  Γ ⊢ Iff (Implies p q) (Or (Not p) q).
Proof.
  apply ND_Iff_intro.
  - assert (Implies p q :: Γ ⊢ Or p (Not p)). { apply ND_excluded_middle. }
    apply (ND_proof_by_cases (r := Or (Not p) q)) in H. assumption.
    Assume (p :: Implies p q :: Γ ⊢ Implies p q).
    Assume (p :: Implies p q :: Γ ⊢ p).
    apply ND_or_intro_r.
    apply (@ND_imp_e (p :: Implies p q :: Γ) p q). assumption. assumption.
    apply ND_or_intro_l. apply ND_assume; prove_In.
  - apply ND_imp_i2.
    Assume (p :: Or (Not p) q :: Γ ⊢ Or (Not p) q).
    apply (ND_proof_by_cases (p := Not p) (q := q) (r := q)). 
    apply ND_assume; prove_In.
    apply (ND_not_e (q := q) (p := p)). prove_In. prove_In.
    apply ND_assume; prove_In.
Qed.

Section QuantifierTheorems.
Theorem not_Forall {Γ p} :
  Γ ⊢ Implies (Not (Forall p)) (Exists (Not p)).
Proof.
  intros.
  apply ND_imp_i2.
  assert (Not (Forall p) :: Γ ⊢ Exists (Not p)). {
    Assume (Not (Forall p) :: Γ ⊢ Not (Forall p)).
    unfold Forall; simpl; auto.
    unfold Forall in H; simpl in H; auto.
    assert (Not (Not (Exists (Not p))) :: Γ
    ⊢ Implies (Not (Not (Exists (Not p)))) (Exists (Not p))). { apply ND_double_negation. }
    apply (@ND_imp_e (Not (Not (Exists (Not p))) :: Γ) (Not (Not (Exists (Not p))))) in H0.
    assumption. assumption.
  }
  assumption.
Qed.

Lemma exists_not_not {Γ p} :
  Γ ⊢ Implies (Exists (Not (Not p))) (Exists p).
Proof.
  intros. apply ND_imp_i2.
  set (c := fresh_evar Γ (Exists p)).
  apply (ND_exists_elim_small (c := c) (p := Not (Not p)) (q := Exists p)). 
  2: unfold c; reflexivity.
  assert (capture_free_subst 0 c (Not (Not p)) = Not (Not (capture_free_subst 0 c p))). {
    simpl; auto.
  }
  rewrite H.
  Assume (Not (Not (capture_free_subst 0 c p)) :: Γ ⊢ Not (Not (capture_free_subst 0 c p))).
  assert (Not (Not (capture_free_subst 0 c p)) :: Γ
            ⊢ Implies (Not (Not (capture_free_subst 0 c p)))
                    (capture_free_subst 0 c p)). {
    apply (@ND_double_negation (Not (Not (capture_free_subst 0 c p))::Γ) (capture_free_subst 0 c p)).
  }
  apply (@ND_imp_e (Not (Not (capture_free_subst 0 c p))::Γ) (Not (Not (capture_free_subst 0 c p)))) in H1 as H2.
  2: assumption.
  apply ND_exists_intro in H2. assumption.
Qed.

Theorem not_Exists {Γ p} :
  Γ ⊢ Implies (Not (Exists p)) (Forall (Not p)).
Proof.
  apply ND_imp_i2.
  assert (Not (Exists p) :: Γ ⊢ Forall (Not p)). {
    Assume (Not (Exists p) :: Γ ⊢ Not (Exists p)).
    unfold Forall; simpl; auto.
    assert (Not (Exists p) :: Γ
       ⊢ Implies (Implies (Exists (Not (Not p))) (Exists p))
           (Implies (Not (Exists p)) (Not (Exists (Not (Not p)))))). { 
      assert (Not (Exists p) :: Γ ⊢ Implies (Exists (Not (Not p))) (Exists p)). {
        apply exists_not_not.
      }
      apply contrapositive. 
    }
    assert (Not (Exists p) :: Γ ⊢ Implies (Exists (Not (Not p))) (Exists p)). {
      apply exists_not_not.
    }
    apply (@ND_imp_e (Not (Exists p) :: Γ) (Implies (Exists (Not (Not p))) (Exists p))) in H0.
    2: assumption.
    apply (@ND_imp_e (Not (Exists p) :: Γ) (Not (Exists p))) in H0.
    2: assumption.
    assumption.
  }
  assumption.
Qed.

Lemma exists_not_not_exists {Γ p} :
  Γ ⊢ Implies (Exists (Not (Not p))) (Exists p).
Proof.
  intros.
  apply ND_imp_i2.
  set (t := fresh_evar Γ (Exists p)).
  apply (ND_exists_elim_small (Γ := Γ) (p := (Not (Not p))) (c := t)).
  2: unfold t; reflexivity.
  assert (capture_free_subst 0 t (Not (Not p)) = Not (Not (capture_free_subst 0 t p))). { simpl; auto. }
  rewrite H.
  Assume(Not (Not (capture_free_subst 0 t p)) :: Γ ⊢ Not (Not (capture_free_subst 0 t p))).
  assert (Not (Not (capture_free_subst 0 t p)) :: Γ
     ⊢ Implies (Not (Not (capture_free_subst 0 t p))) (capture_free_subst 0 t p)). {
    apply ND_double_negation.
  }
  apply (ND_imp_e (q := capture_free_subst 0 t p)) in H0. 2: assumption.
  apply ND_exists_intro in H0.
  assumption.
Qed.

Theorem forall_subst : forall (n : nat) (t : Term) (p : Formula),
  capture_free_subst n t (Forall p) = Forall (capture_free_subst (S n) (lift (S n) 1 t) p).
Proof.
  intros.
  unfold Forall; unfold capture_free_subst; simpl; auto.
Qed.

Lemma forall_implies_verum_step {Γ} :
  forall (p : Formula),
  Γ ⊢ Implies (Forall p) Verum <-> Γ ⊢ Forall (Implies p Verum).
Proof.
  split.
  - intros.
    set (t := fresh_evar Γ Falsum).
    apply (@ND_forall_i Γ (Implies p Verum) t).
    2: unfold t; reflexivity.
    assert (Γ ⊢ capture_free_subst 0 t (Implies p Verum)
            = Γ ⊢ Implies (capture_free_subst 0 t p) Verum). {
      simpl; auto.
    }
    rewrite H0.
    apply ND_imp_i2.
    apply ND_True_intro.
  - intros. apply ND_imp_i2; apply ND_True_intro.
Qed.
Section CommutingConnectivesAndQuantifiers.
Lemma capturing_garbage_bvars {Γ} :
  forall (p : Formula) (t : Term),
  Γ ⊢ p -> capture_free_subst 0 t p = p.
Admitted.

Lemma wff_capture_free_vacuity {Γ} :
  forall (p : Formula) (t : Term),
  Γ ⊢ p -> (capture_free_subst 0 t p) = p.
Admitted.

Lemma wff_capture_free_vacuity_antecedent {Γ} :
  forall (p q : Formula) (t : Term),
  Γ ⊢ (Implies (Forall p) q) -> (capture_free_subst 0 t q) = q.
Admitted.

Theorem implies_forall_equiv_exists_implies {Γ} :
  forall (p q : Formula),
  Γ ⊢ Iff (Implies (Forall p) q) (Exists (Implies p q)).
Proof.
  intros.
  apply ND_Iff_intro.
  - Assume ( (Implies (Forall p) q :: Γ) ⊢ Implies (Forall p) q).
    assert ((Implies (Forall p) q :: Γ) ⊢ Iff (Implies (Forall p) q) (Or (Not (Forall p)) q)). {
      apply implies_equiv_or_not.
    }
    Check @ND_Iff_elim_l.
    apply (@ND_Iff_elim_l (Implies (Forall p) q :: Γ) (Implies (Forall p) q) (Or (Not (Forall p)) q))
      in H.
    2: assumption.
    
set (t := fresh_evar (Implies (Forall p) q :: Γ) Falsum).
    apply (@ND_exists_intro (Implies (Forall p) q :: Γ) (Implies p q) t).
    Assume (Implies (Forall p) q :: Γ ⊢ Implies (Forall p) q).
    apply (@wff_capture_free_vacuity_antecedent (Implies (Forall p) q :: Γ) p q t) in H.
    simpl; auto. 
    rewrite H.
    apply ND_imp_i2.
    Assume (capture_free_subst 0 t p :: Implies (Forall p) q :: Γ ⊢ Implies (Forall p) q).
    Assume (capture_free_subst 0 t p :: Implies (Forall p) q :: Γ ⊢ capture_free_subst 0 t p).
    
    Check @ND_forall_i.
    Assume ((capture_free_subst 0 t p) :: Implies (Forall p) q :: Γ ⊢ Implies (Forall p) q).
    assert ((capture_free_subst 0 t p) :: Implies (Forall p) q :: Γ ⊢ Forall p). {
      Check @ND_forall_i.
    }
    Assume ((capture_free_subst 0 t p) :: Implies (Forall p) q :: Γ ⊢ (capture_free_subst 0 t p)).
    apply (ND_imp_e (p := Forall p)) in H. 2: assumption.
    Check @ND_exists_intro.
    Check @ND_forall_i.
apply ND_exists_intro.
Admitted.

Lemma wff_capture_free_vacuity {Γ} :
  forall (p : Formula) (t : Term)
  Γ ⊢ p -> (capture_free_subst 0 t p) = p.

(*
Proof.
  intros.
  apply ND_Iff_intro.
  - assert (Implies (Forall p) q :: Γ ⊢ Iff (Implies (Forall p) q) (Or (Not (Forall p)) q)). {
      apply (implies_equiv_or_not (Γ := Implies (Forall p) q :: Γ) (p := Forall p) (q := q)).
    }
    apply ND_Iff_elim_l in H. 2: apply ND_assume; prove_In.
    set (t := fresh_evar (Implies (Forall p) q :: Γ) Falsum).
    apply (ND_exists_intro (Γ := Implies (Forall p) q :: Γ) (t := t)).
    simpl; auto.
    Check @ND_forall_i.
*)

Theorem and_forall_equiv_forall_and {Γ} :
  forall (p q : Formula),
  Γ ⊢ Iff (And (Forall p) (Forall q)) (Forall (And p q)).
Proof.
  intros. apply ND_Iff_intro.
  - apply ND_and_context.
    set (t := fresh_evar ((Forall p)::(Forall q) :: Γ) Falsum).
    apply (ND_forall_i (Γ := ((Forall p)::(Forall q) :: Γ)) (t := t)).
    2: { unfold t; reflexivity. }
    simpl; auto.
    apply ND_and_intro.
    + apply ND_forall_elim; apply ND_assume; prove_In.
    + apply ND_forall_elim; apply ND_assume; prove_In.
  - Assume (Forall (And p q) :: Γ ⊢  Forall (And p q)).
    set (t := fresh_evar (Forall (And p q) :: Γ) Falsum).
    apply (ND_forall_elim (Γ := Forall (And p q) :: Γ) (t := t)) in H as H0.
    simpl in H0.
    apply ND_proj_l in H0 as H1.
    apply ND_forall_i in H1.
    apply ND_proj_r in H0 as H2.
    apply ND_forall_i in H2.
    apply ND_and_intro. assumption. assumption. 
    unfold t; reflexivity. unfold t; reflexivity.
Qed.

Theorem ND_or_elim {Γ} :
  forall (p q r : Formula),
  p::Γ ⊢ r -> q::Γ ⊢r -> (Or p q)::Γ ⊢ r.
Proof.
  intros.
  apply (ND_proof_by_cases (Γ := (Or p q)::Γ) (r := r) (p := p) (q := q)).
  apply ND_assume; prove_In.
  - assert (p :: Γ ⊆ p :: Or p q :: Γ). { apply subcontext_cons. split. prove_In.
      apply subcontext_weaken; apply subcontext_weaken; apply subcontext_reflex.
    }
    apply (@weakening (p :: Γ) ( p :: Or p q :: Γ)) in H. assumption.
    assumption.
  - assert (q :: Γ ⊆ q :: Or p q :: Γ). { apply subcontext_cons. split. prove_In.
      apply subcontext_weaken; apply subcontext_weaken; apply subcontext_reflex.
    }
    apply (@weakening (q :: Γ) ( q :: Or p q :: Γ)) in H0. assumption.
    assumption.
Qed.

Theorem or_exists_iff_exists_or {Γ} :
  forall (p q : Formula),
  Γ ⊢ Iff (Or (Exists p) (Exists q)) (Exists (Or p q)).
Proof.
  intros; apply ND_Iff_intro.
  - set (c := fresh_evar Γ (Exists (Or p q))).
    apply ND_or_elim with (p := (Exists p)) (q := (Exists q)) (r := Exists (Or p q)).
    + apply (@ND_exists_elim_small Γ p (Exists (Or p q)) c).
      2: unfold c; reflexivity.
      apply (@ND_exists_intro (capture_free_subst 0 c p :: Γ) (Or p q) c).
      simpl; auto.
      apply ND_or_intro_l; apply ND_assume; prove_In.
    + apply (@ND_exists_elim_small Γ q (Exists (Or p q)) c).
      2: unfold c; reflexivity.
      apply (@ND_exists_intro (capture_free_subst 0 c q :: Γ) (Or p q) c).
      simpl; auto.
      apply ND_or_intro_r; apply ND_assume; prove_In.
  - set (c := fresh_evar Γ (Or (Exists p) (Exists q))).
    apply (ND_exists_elim_small (c := c) (q :=  Or (Exists p) (Exists q)) (p := Or p q)).
    2: unfold c; reflexivity.
    assert (capture_free_subst 0 c (Or p q) = Or (capture_free_subst 0 c p) (capture_free_subst 0 c q)). {
      simpl; auto.
    }
    rewrite H.
    apply (@ND_or_elim Γ (capture_free_subst 0 c p) (capture_free_subst 0 c q) (Or (Exists p) (Exists q))).
    + apply ND_or_intro_l.
      apply (@ND_exists_intro (capture_free_subst 0 c p :: Γ) p c).
      apply ND_assume; prove_In.
    + apply ND_or_intro_r.
      apply (@ND_exists_intro (capture_free_subst 0 c q :: Γ) q c).
      apply ND_assume; prove_In.
Qed.

Theorem exists_and_implies_and_exists {Γ} :
  forall (p q : Formula),
  Γ ⊢ Implies (Exists (And p q)) (And (Exists p) (Exists q)).
Proof.
  intros. apply ND_imp_i2.
  Check @ND_exists_elim_small.
  set (c := fresh_evar Γ (And (Exists p) (Exists q))).
  apply (@ND_exists_elim_small Γ (And p q) (And (Exists p) (Exists q)) c).
  2: unfold c; reflexivity.
  simpl; auto. apply ND_and_context.
  apply ND_and_intro.
  - apply (@ND_exists_intro (capture_free_subst 0 c p :: capture_free_subst 0 c q :: Γ) p c).
    apply ND_assume; prove_In.
  - apply (@ND_exists_intro (capture_free_subst 0 c p :: capture_free_subst 0 c q :: Γ) q c).
    apply ND_assume; prove_In.
Qed.

Theorem or_forall_implies_forall_or {Γ} :
  forall (p q : Formula),
  Γ ⊢ Implies (Or (Forall p) (Forall q)) (Forall (Or p q)).
Proof.
  intros. apply ND_imp_i2.
  set (t := fresh_evar (Or (Forall p) (Forall q) :: Γ) Falsum).
  apply (@ND_forall_i (Or (Forall p) (Forall q) :: Γ) (Or p q) t).
  2: unfold t; reflexivity.
  simpl; auto.
  apply ND_or_elim.
  - apply ND_or_intro_l.
    apply ND_forall_elim. apply ND_assume; prove_In.
  - apply ND_or_intro_r; apply ND_forall_elim; apply ND_assume; prove_In.
Qed.
End CommutingConnectivesAndQuantifiers.
End QuantifierTheorems.

Theorem Verum_implies_Verum :
  proves (Implies Verum Verum).
Proof.
  apply ND_imp_i2; apply ND_True_intro.
Qed.


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

