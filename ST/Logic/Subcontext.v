Require Export RelationClasses.
Require Export Morphisms.
Require Import List.
Import ListNotations.
From ST Require Export Logic.Formula.

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
  unfold subcontext. intros. absurd (In P []). apply in_nil. assumption.
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
  intros. assert (Γ2 ⊆ (List.cons P Γ2)). { apply cons_subcontext. }
  apply (subcontext_trans Γ1 Γ2 (P :: Γ2)) in H0. assumption. assumption.
Qed.
  
Lemma subcontext_weaken2 : forall (Γ1 Γ2 : list Formula) (P : Formula),
  Γ1 ⊆ Γ2 -> P :: Γ1 ⊆ P :: Γ2.
Proof.
  intros. 
  assert (Γ2 ⊆ (List.cons P Γ2)). { apply cons_subcontext. }
  apply subcontext_cons. 
  split; unfold List.In; auto. 
  apply (subcontext_trans Γ1 Γ2 (P :: Γ2)).
  - assumption.
  - assumption.
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
  assert (In P Γ2). { apply subcontext_cons in H; destruct H; assumption. }
  unfold fresh in H0; unfold FreshContext in H0.
  apply (List.Forall_forall) with (P := (fun fm : Formula => fresh c fm)) in H1 as H2.
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
  apply List.Forall_cons_iff. split.
  apply IHΓ2 in H2 as IH. apply (fresh_in_head H). assumption.
  apply IHΓ2 in H2 as IH. assumption.
Qed.

(*
Definition fresh_evar_counter (Γ : list Formula) (p : Formula) : nat :=
first_new 0 (list_evars (p::Γ)%list).

Check fresh_evar. Check fresh.
Theorem lemma_list_evars : forall (Γ1 Γ2 : list Formula),
  Γ1 ⊆ Γ2 -> incl (list_evars Γ1) (list_evars Γ2).
Proof. intros.
*)
  
Theorem fresh_econst : forall (Γ1 Γ2 : list Formula) (p : Formula),
  Γ1 ⊆ Γ2 -> fresh (fresh_evar Γ2 p) Γ1.
Proof.
  intros. set (c := (fresh_evar Γ2 p)).
  assert (fresh c Γ2). { apply fresh_evar_context. }
  assert (c = c). { reflexivity. }
  apply (fresh_cons_proper c c H1 _ _ H).
  assumption.
Qed.
