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
From ST Require Import Vector.
From ST Require Import EVarsScratchwork Logic.
Import VectorNotations.

Fixpoint Every (n : nat) (p : Formula) : Formula :=
match n with
| 0 => p
| (S n') => Forall (Every n' p)
end.

Fixpoint Some (n : nat) (p : Formula) : Formula :=
match n with
| 0 => p
| S n' => Exists (Some n' p)
end.  

Theorem every_comp :
  forall (m n : nat) (p : Formula),
  Every m (Every n p) = Every (m + n) p.
Proof.
  intros.
  induction m.
  - intros. simpl; auto.
  - intros.
    assert (Every m (Every n p) = Every (m + n) p). { apply (IHm). }
    assert (Forall (Every m (Every n p)) = Every (S m) (Every n p)). {
      simpl; auto.
    }
    rewrite <- H0. rewrite H. simpl; auto.
Qed.

Corollary every_ind :
  forall (n : nat) (p : Formula),
  Every n (Forall p) = Every (S n) p.
Proof. intros.
  assert (Every n (Every 1 p) = Every (n + 1) p). {
    apply (every_comp n 1 p).
  }
  assert (S n = 1 + n). lia.
  rewrite H0.
  assert(Every n (Every 1 p) = Every n (Forall p)). simpl; auto.
  rewrite <- H1. assert (n + 1 = 1 + n). lia.
  rewrite <- H2.
  assumption.
Qed.

Theorem some_comp :
  forall (m n : nat) (p : Formula),
  Some m (Some n p) = Some (m + n) p.
Proof.
  intros.
  induction m.
  - intros. simpl; auto.
  - intros.
    assert (Some m (Some n p) = Some (m + n) p). { apply IHm. }
    assert (Exists (Some m (Some n p)) = Some (S m) (Some n p)). {
      simpl; auto.
    }
    rewrite <- H0. rewrite H. simpl; auto.
Qed.

Corollary some_ind :
  forall (n : nat) (p : Formula),
  Some n (Exists p) = Some (S n) p.
Proof. intros.
  assert (Some n (Some 1 p) = Some (n + 1) p). {
    apply (some_comp n 1 p).
  }
  assert (S n = 1 + n). lia.
  rewrite H0.
  assert(Some n (Some 1 p) = Some n (Exists p)). simpl; auto.
  rewrite <- H1. assert (n + 1 = 1 + n). lia.
  rewrite <- H2.
  assumption.
Qed.

Lemma nor_not_and : forall (A B : Prop),
  ~A /\ ~B <-> ~(A \/ B).
Proof.
  intros. split.
  - apply and_not_or.
  - apply not_or_and.
Qed.


(** Substitution in Predicates and Formulas. *)



(*
Lemma list_de_morgan {A : Type} : forall  (P : A -> Prop) (l : list A),
  ~(List.Exists P l) <-> List.Forall (fun a => ~(P a)) l.
Proof.
  intros; split.
  - intros. simpl; auto. induction l. simpl; auto.
    assert (List.Exists P0 (a :: l) <-> P0 a \/ List.Exists P0 l). { apply List.Exists_cons. }
    rewrite H0 in H.
    apply Decidable.not_or in H.
    apply List.Forall_cons_iff. split. destruct H. assumption.
    destruct H. apply IHl in H1. assumption.
  - intros. induction l.
  + assert (List.Exists P0 [] <-> False). { apply List.Exists_nil. } rewrite H0. simpl; auto.
  + assert (List.Exists P0 (a :: l) <-> P0 a \/ List.Exists P0 l). { apply List.Exists_cons. }
    rewrite H0.
    Forall_cons.
    set (notP0 := (fun (a : A) => ~ P0 a)).
    apply (List.Forall_cons_iff) in H. destruct H. apply IHl in H1 as IH.
    apply and_not_or. split. assumption. assumption.
Qed.

Lemma formula_predicate_contains_bvar : forall (n : nat) (p : Predicate),
  contains_bvar n (Atom p) <-> contains_bvar n p.
Proof.
  intros; split.
  - intros. unfold contains_bvar; assumption.
  - intros. unfold contains_bvar; assumption.
Qed.

Lemma predicate_subst_bvar_free : forall (n : nat) (p : Predicate) (t : Term),
  ~(contains_bvar n p) -> (subst (BVar n) t p) = p.
Proof.
  intros. destruct p as [k nm args]. unfold subst; unfold substPred.
  unfold subst; unfold substTerm.
  unfold contains_bvar in H; unfold ContainsBVarPredicate in H.
  apply vector_de_morgan in H.
  induction args.
  - simpl; auto.
  - apply Vector_Forall_cons_iff in H as H1. destruct H1.
    apply IHargs in H1 as IH.
    assert ((Vector.map
          (fun arg : Term => tsubst (BVar n) t arg)
          args) = args). {
      inversion IH. apply inj_pair2_eq_dec in H3. 2: decide equality.
      rewrite H3. assumption.
    }
    assert ((Vector.map (fun arg : Term => tsubst (BVar n) t arg) (h :: args)%vector) 
            = ((tsubst (BVar n) t h)::(Vector.map (fun arg : Term => tsubst (BVar n) t arg) args))%vector). {
      simpl; auto.
    }
    rewrite H3. rewrite H2.
    assert ((tsubst (BVar n) t h) = h). {
      set (P := (fun a : Term => ~ contains_bvar n a)). fold P in H.
      set (v := (h :: args)%vector). fold v in H.
      assert (forall a : Term, VectorDef.In a v -> P a). {
        apply (Vector.Forall_forall). assumption.
      }
      assert (Vector.In h v). {
        apply Vector.In_cons_hd.
      }
      apply H4 in H5. unfold P in H5.
      apply term_subst_bvar_free. assumption.
    }
    rewrite H4. reflexivity.
Qed.

Lemma formula_and_not_contains_bvar : forall (n : nat) (A1 A2 : Formula),
  ~(contains_bvar n (And A1 A2)) -> ~contains_bvar n A1 /\ ~contains_bvar n A2.
Proof.
  intros.
  assert (contains_bvar n (And A1 A2) <-> contains_bvar n A1 \/ contains_bvar n A2). {
    simpl; auto. intuition.
  }
  rewrite H0 in H.
  apply not_or_and. assumption. 
Qed.

Theorem subst_bvar_free : forall (n : nat) (A : Formula) (t : Term),
  ~(contains_bvar n A) -> (capture_free_subst n t A) = A.
Proof.
  intros. generalize dependent n. generalize dependent t. induction A.
  - simpl; auto.
  - intros. apply predicate_subst_bvar_free with (t := t) in H as H1. 
    unfold capture_free_subst. rewrite H1. reflexivity.
  - intros. assert (~contains_bvar n A1 /\ ~contains_bvar n A2). { 
      assert (contains_bvar n (And A1 A2) <-> contains_bvar n A1 \/ contains_bvar n A2). {
        simpl; auto. intuition.
      }
      rewrite H0 in H.
      apply not_or_and. assumption. 
    } destruct H0.
    apply (IHA1 t n) in H0; apply (IHA2 t n) in H1.
    assert (capture_free_subst n t (And A1 A2) = And (capture_free_subst n t A1) (capture_free_subst n t A2)). {
      simpl; auto.
    }
    rewrite H2. rewrite H0; rewrite H1; reflexivity.
  - intros. assert (~contains_bvar n A1 /\ ~contains_bvar n A2). { 
      assert (contains_bvar n (And A1 A2) <-> contains_bvar n A1 \/ contains_bvar n A2). {
        simpl; auto. intuition.
      }
      rewrite H0 in H.
      apply not_or_and. assumption. 
    } destruct H0.
    apply (IHA1 t n) in H0; apply (IHA2 t n) in H1.
    assert (capture_free_subst n t (Or A1 A2) = Or (capture_free_subst n t A1) (capture_free_subst n t A2)). {
      simpl; auto.
    }
    rewrite H2. rewrite H0; rewrite H1; reflexivity.
  - intros. assert (~contains_bvar n A1 /\ ~contains_bvar n A2). { 
      assert (contains_bvar n (And A1 A2) <-> contains_bvar n A1 \/ contains_bvar n A2). {
        simpl; auto. intuition.
      }
      rewrite H0 in H.
      apply not_or_and. assumption. 
    } destruct H0.
    apply (IHA1 t n) in H0; apply (IHA2 t n) in H1.
    assert (capture_free_subst n t (Implies A1 A2) = Implies (capture_free_subst n t A1) (capture_free_subst n t A2)). {
      simpl; auto.
    }
    rewrite H2. rewrite H0; rewrite H1; reflexivity.
  - intros. assert (~contains_bvar (S n) A). {
      unfold contains_bvar in H. unfold ContainsBVarFormula in H. simpl; auto.
    }
    assert (capture_free_subst n t (Exists A) = Exists (capture_free_subst (S n) (lift (S n) 1 t) A)). {
      unfold contains_bvar; unfold ContainsBVarFormula; simpl; auto.
    }
    apply (IHA (lift (S n) 1 t) (S n)) in H0 as H2. rewrite H1; rewrite H2.
    reflexivity.
Qed.

Lemma bvar_lift_composed_step : forall (c n : nat),
  ~(0 < c /\ n = c) -> lift (S c) 1 (lift c c (BVar n)) = lift (S c) (S c) (BVar n).
Proof. intros.
  bdestruct (Nat.ltb n c).
  - assert(lift (S c) (S c) (BVar n) = BVar (n)). {
      apply case_lift_is_id. lia.
    }
    rewrite H1.
    assert(lift (S c) 1 (BVar n) = BVar (n)). {
      apply case_lift_is_id. lia.
    }
    assert(lift c c (BVar n) = BVar (n)). {
      apply case_lift_is_id. assumption.
    }
    rewrite H3.
    rewrite H2. reflexivity.
  - bdestruct (Nat.ltb n (S c)).
  + assert (n = c). lia.
    assert(lift (S c) (S c) (BVar n) = BVar (n)). {
      apply case_lift_is_id. lia.
    }
    rewrite H2.
    destruct c.
 ++ rewrite H2 in H3. rewrite H3. 
    assert(lift 0 0 (BVar 0) = BVar 0). {
      apply case_lift_is_not_id. lia.
    } rewrite H4.
    assert(lift 1 1 (BVar 0) = BVar 0). {
      apply case_lift_is_id. lia.
    }
    rewrite H5. reflexivity.
 ++ contradict H. lia.
  + assert (lift c c (BVar n) = BVar (n + c)). {
      apply case_lift_is_not_id. lia.
    }
    rewrite H2.
    
    assert (lift (S c) (S c) (BVar n) = BVar (n + S c)). {
      apply case_lift_is_not_id. lia.
    }
    rewrite H3.
    assert (lift (S c) 1 (BVar (n + c)) = BVar (n + c + 1)). {
      apply case_lift_is_not_id. lia.
    }
    rewrite H4.
    assert (n + c + 1 = n + S c). lia.
    rewrite H5. reflexivity.
Qed.


Lemma var_lift_composed_step : forall (x : V) (c : nat),
  ~(exists (n : nat), x = BVar n /\ (0 < c /\ n = c)) -> lift (S c) 1 (lift c c x) = lift (S c) (S c) x.
Proof.
  intros. destruct x.
  - simpl; auto.
  - apply not_ex_all_not with (n := n) in H.
    assert (BVar n = BVar n). reflexivity.
    apply not_and_or in H. destruct H.
    + contradict H. assumption.
    + apply bvar_lift_composed_step. assumption.
Qed.

Theorem capture_free_subst_forall_init : forall (n : nat) (t : Term) (phi : Formula),
  capture_free_subst n t (Forall phi) = Forall (capture_free_subst (S n) (lift (S n) 1 t) phi).
Proof.
  intros. unfold Forall; unfold capture_free_subst; simpl; auto.
Qed.

Theorem capture_free_subst_forall_step : forall (c d n : nat) (t : Term) (phi : Formula),
  capture_free_subst n (lift c d t) (Forall phi) 
  = Forall (capture_free_subst (S n) (lift (S n) 1 (lift c d t)) phi).
Proof.
  intros. unfold Forall; unfold capture_free_subst; simpl; auto.
Qed.

Lemma every_eq {k n p q} :
  Every (k + n) p = Every k q -> Every n p = q.
Proof.
  intros. generalize dependent n.
  induction k.
  - intros. simpl; auto.
  - intros.
    assert (Every (k + n) p = Every k q). {
      assert (Every (S k + n) p = Forall (Every (k + n) p)). {
        simpl; auto.
      }
      assert (Every (S k) q = Forall (Every k q)). {
        simpl; auto.
      }
      rewrite H0 in H. rewrite H1 in H.
      injection H. simpl; auto.
    }
    apply IHk in H0; apply H0.
Qed.

Theorem every_subst {n t p} :
  capture_free_subst 0 t (Every n p) = Every n (capture_free_subst n (tlift n n t) p).
Proof.
  intros. generalize dependent p.
  induction n.
  - unfold Every. 
    assert (tlift 0 0 t = t). {
      unfold lift. apply term_zero_lift_is_id.
    } 
    rewrite H. reflexivity.
  - intros. 
    assert (capture_free_subst 0 t (Every n (Forall p)) =
      Every n (capture_free_subst n (tlift n n t) (Forall p))). {
      apply (IHn (Forall p)).
    }
    assert (Every n (Forall p) = Every (S n) p). { apply (every_ind n p). }
    
    rewrite H0 in H; rewrite H.
    rewrite capture_free_subst_forall_init.
    Print capture_free_subst.
   (* assert ((capture_free_subst n (tlift n n t) (Forall p)) =
    assert ((capture_free_subst n t (Exists p)) = Exists (capture_free_subst (S n) t p)). {
      simpl; auto. unfold capture_free_subst.
      *)
Admitted.

(** I am trying to formalize the situation where we "condense" several quantifiers
into a single binder. For example, [Forall (Forall (Forall p))] could be
abbreviated as [Every 3 p]. 

Now, substitution would be [subst_bvar_vec 0 [t1;t2;t3] p] which has the property
[subst_bvar_vec 0 [t1] p = capture_free_subst 0 t1 p]. 
The nullary case amounts to just producing the equation [p].
The inductive case amounts to iterating the single [capture_free_subst] over
and over, again and again. The default case will be [n = 0]...but ostensibly,
there could be a time when a generic [n] may be useful.
*)
Fixpoint subst_bvar_vec {k} (n : nat) (v : Vector.t Term k) (p : Formula) :=
match v with
| []%vector => p
| (h::tl)%vector => subst_bvar_vec n tl (capture_free_subst n h p)
end.

Fixpoint shift_evars_term_by (offset : nat) (t : Term) : Term :=
match t with
| Var _ => t
| EConst n => EConst (offset + n)
| Fun f args => Fun f (Vector.map (shift_evars_term_by offset) args)
end.

Inductive fresh_evar_vector : forall {n}, nat -> (list Formula) -> (Vector.t Term n) -> Prop :=
| FEV_nil {offset ??} : 
  fresh_evar_vector offset ?? []%vector
| FEV_cons {?? n} : forall (offset : nat) (t : Term) (v : Vector.t Term n),
  t = shift_evars_term_by offset (fresh_evar ?? Falsum) ->
  ~(Vector.In t v) ->
  fresh_evar_vector (S offset) ?? v ->
  fresh_evar_vector offset ?? (t::v)%vector.
*)

Lemma forall_implies_verum_step {??} :
  forall (p : Formula),
  ?? ??? Implies (Forall p) Verum <-> ?? ??? Forall (Implies p Verum).
Proof.
  split.
  - intros.
    set (t := fresh_evar ?? Falsum).
    apply (@ND_forall_i ?? (Implies p Verum) t).
    2: unfold t; reflexivity.
    assert (?? ??? capture_free_subst 0 t (Implies p Verum)
            = ?? ??? Implies (capture_free_subst 0 t p) Verum). {
      simpl; auto.
    }
    rewrite H0.
    apply ND_imp_i2.
    apply ND_True_intro.
  - intros. apply ND_imp_i2; apply ND_True_intro.
Qed.

Theorem deduce_every_verum_step {??} :
  forall (n : nat) (p : Formula),
  ?? ??? Implies (Every (S n) p) Verum <-> ?? ??? Forall (Implies (Every n p) Verum).
Proof.
  intros.
  assert (Every (S n) p = Forall (Every n p)). { simpl; auto. }
  rewrite H. apply forall_implies_verum_step.
Qed.

(* I should prove this, but am too lazy to work through all the cases. *)
Lemma subst_bvar_with_itself : forall (n : nat) (p : Formula),
  capture_free_subst n (Var (BVar n)) p = p.
Admitted.

Theorem generalize_a_valid_deduction {??} :
  forall (p : Formula),
  ?? ??? Forall p -> ?? ??? p.
Proof.
  intros.
  set (t := (Var (BVar 0))).
  apply (@ND_forall_elim ?? p t) in H as H0. unfold t in H0.
  rewrite (subst_bvar_with_itself 0 p) in H0.
  assumption.
Qed.

Corollary iter_generalize_a_valid_deduction {??} :
  forall (n : nat) (p : Formula),
  ?? ??? Every n p -> ?? ??? p.
Proof.
  intros. generalize dependent p. induction n.
  - unfold Every; simpl; auto.
  - intros.
    assert (?? ??? Forall (Every n p) -> ?? ??? Every n p). {
      apply (generalize_a_valid_deduction (Every n p)).
    }
    assert (?? ??? Every n p -> ?? ??? p). {
      apply (IHn p).
    }
    apply H1; apply H0.
    assert (Every (S n) p = Forall (Every n p)). {
      simpl; auto.
    }
    rewrite <- H2.
    assumption.
Qed.

Lemma forall_swap_body {??} :
  forall (p q : Formula),
  ?? ??? Implies (Forall p) (Forall q) <-> ?? ??? Forall (Implies p q).
Admitted.

Lemma forall_verum {??} :
  ?? ??? Forall Verum.
Proof.
  intros. 
  set (t := fresh_evar ?? Falsum).
  assert (capture_free_subst 0 t Verum = Verum). {
    simpl; auto.
  }
  assert (?? ??? Verum). { apply ND_True_intro. }
  rewrite <- H in H0.
  apply (@ND_forall_i ?? Verum t) in H0 as H1.
  assumption. unfold t; reflexivity.
Qed.

Lemma deduce_every_verum_step2 {??} :
  forall (n : nat) (p : Formula),
  ?? ??? Every n (Implies (Forall p) Verum) -> ?? ??? Every n (Forall (Implies p Verum)).
Admitted.

Theorem deduce_every_verum {??} :
  forall (n : nat) (p : Formula),
  ?? ??? Implies (Every n p) Verum <-> ?? ??? Every n (Implies p Verum).
Proof.
  intros.
  generalize dependent p.
  induction n.
  - unfold Every; reflexivity.
  - intros. split. 2: { intros. apply ND_imp_i2; apply ND_True_intro. }
  + apply contra. intros.
    assert (?? ??? Implies (Every (S n) p) Verum). {
      apply ND_imp_i2; apply ND_True_intro.
    }
    assert (?? ??? Implies (Every n (Every 1 p)) Verum <-> ?? ??? Every n (Implies (Every 1 p) Verum)). {
      apply (IHn (Every 1 p)).
    }
    assert ((Every n (Every 1 p)) = Every (n + 1) p). {
      apply every_comp.
    } rewrite H2 in H1.
    assert (S n = n + 1). lia.
    rewrite <- H3 in H1.
    apply H1 in H0 as IH.
    assert (Every n (Implies (Every 1 p) Verum) = Every n (Implies (Forall p) Verum)). {
      unfold Every; simpl; auto.
    }
    rewrite H4 in IH. clear H4.
    apply deduce_every_verum_step2 in IH.
    assert(Every n (Forall (Implies p Verum)) = Every n (Every 1 (Implies p Verum))). {
      unfold Every; simpl; auto.
    }
    rewrite H4 in IH. rewrite (every_comp n 1 (Implies p Verum)) in IH.
    rewrite <- H3 in IH.
    contradiction.
Qed.

Theorem every_verum :
  forall (n : nat) (p : Formula),
  proves (Every n (Implies p Verum)).
Proof.
  intros.
  assert (proves (Implies (Every n p) Verum)). { apply ND_imp_i2; apply ND_True_intro. }
  unfold proves in H.
  apply deduce_every_verum in H.
  unfold proves.
  assumption.
Qed.

(*
Theorem ungeneralize_a_valid_deduction {??} :
  forall (p : Formula),
  ?? ??? p -> ?? ??? Forall p.
Proof.
  intros.
  set (t := (Var (BVar 0))).
  apply (@ND_forall_elim ?? p t) in H as H0. unfold t in H0.
  rewrite (subst_bvar_with_itself 0 p) in H0.
  assumption.
Qed.
*)
(*
Corollary every_swap_body {??} :
  forall (n : nat) (p q : Formula),
  ?? ??? Implies p q -> ?? ??? Every n p -> ?? ??? Every n q.
Proof.
  intros. generalize dependent p. generalize dependent q.
  induction n.
  - intros. unfold Every in H0; unfold Every. apply (ND_imp_e (p := p) (q := q)) in H.
    assumption. assumption.
  - intros. 
*)
(*
tlift = 
fix tlift (c d : nat) (t : Term) {struct t} : Term :=
  match t with
  | Var y => Var (lift c d y)
  | EConst _ => t
  | @Fun n f args =>
      Fun f (Vector.map (fun a : Term => tlift c d a) args)
  end
     : nat -> nat -> Term -> Term

Arguments tlift (c d)%nat_scope t

Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Peano_dec.
Lemma tlift_zero_zero : forall (t1 t2 : Term),
  tlift 0 0 t1 = t2 -> t1 = t2.
Proof.
  intros. generalize dependent t1. destruct t2.
  - intros. induction v. simpl; auto. simpl; auto; assert(n + 0 = n). lia. rewrite H; reflexivity.
  - simpl; auto.
  - rename t into args. induction args.
  + simpl; auto.
  + inversion IHargs. apply inj_pair2_eq_dec in H0. inversion H0. simpl; auto.
    assert (tlift 0 0 (Fun n0 args) = Fun n0 (Vector.map (fun a : Term => tlift 0 0 a) args)). {
      unfold tlift; simpl; auto.
    }
    assert (forall (a : Term), Vector.In a args -> tlift 0 0 a = a). {
      intros. simpl; auto.
    assert (Vector.map (fun a : Term => tlift 0 0 a) args = args). {
      simpl; auto.
    }
    rename t into args. induction args.
  + simpl; auto.
  + assert (tlift 0 0 (Fun n0 args) = Fun n0 args) as IH. apply IHargs.
    assert (tlift 0 0 (Fun n0 args) = Fun n0 (Vector.map (fun a : Term => tlift 0 0 a) args)). {
      unfold tlift; simpl; auto.
    }
    unfold tlift in IH.
Theorem every_subst {n t p} :
  capture_free_subst 0 t (Every n p) = Every n (capture_free_subst n (tlift n n t) p).
Proof.
  intros. generalize dependent p.
  induction n.
  - intros; simpl; auto.
  - intros. 
    assert (capture_free_subst 0 t (Every n (Forall p)) =
      Every n (capture_free_subst n t (Forall p))). {
      apply (IHn (Forall p)).
    }
    assert (Every n (Forall p) = Every (S n) p). apply (every_ind n p).
    rewrite H0 in H.
    assert ((capture_free_subst n t (Exists p)) = Exists (capture_free_subst (S n) t p)). {
      simpl; auto. unfold capture_free_subst.
*)
(* 
Every = 
fix Every (n : nat) (p : Formula) {struct n} : Formula :=
  match n with
  | 0 => p
  | S n' => Forall (Every n' p)
  end
     : nat -> Formula -> Formula
*)

(* 
Lemma every_subst {n t p} :
  capture_free_subst 0 t (Every n p) = Every n (capture_free_subst n (lift n n t) p).
Proof.
  intros. generalize dependent p.
  induction n.
  - intros. unfold Every. simpl; auto.
  - intros. 
    assert (capture_free_subst 0 t (Every n (Forall p)) =
      Every n (capture_free_subst n t (Forall p))). {
      apply (IHn (Forall p)).
    }
    assert (Every n (Forall p) = Every (S n) p). apply (every_ind n p).
    rewrite H0 in H.
    assert ((capture_free_subst n t (Exists p)) = Exists (capture_free_subst (S n) t p)). {
      simpl; auto. unfold capture_free_subst.
*)

(* 
Lemma not_some_not_is_every {??} :
  forall (n : nat) (p : Formula),
  ?? ??? Implies (Not (Some n (Not p))) (Every n p).
Proof.
  intros. generalize dependent ??. generalize dependent p.
  induction n.
  - simpl; auto. intros. apply ND_double_negation.
  - intros. apply ND_imp_i2.
    Assume(Not (Some (S n) (Not p)) :: ?? ??? Not (Some (S n) (Not p))).
    assert(Not (Some (S n) (Not p)) :: ?? ??? Not (Some (S n) (Not p))
           = Not (Some (S n) (Not p)) :: ?? ??? Not (Exists (Some n (Not p)))). {
      simpl; auto.
    }
    rewrite H0 in H. clear H0.
    assert (?? ??? Implies (Not (Some n (Not (Forall p)))) (Every n (Forall p))). {
      apply (IHn (Forall p) ??).
    }
    assert (Every (S n) p = Forall (Every n p)). { simpl; auto. }
    set (t := fresh_evar (Not (Some (S n) (Not p)) :: ??) Falsum).
    rewrite H1.
    apply (@ND_forall_i (Not (Some (S n) (Not p)) :: ??) (Every n p) t).
    2: unfold t; reflexivity.
*)

(* 
Theorem not_some {??} :
  forall (n : nat) (p : Formula),
  ?? ??? Not (Some n p) -> ?? ??? Every n (Not p).
Proof.
  intros. generalize dependent ??. generalize dependent p.
  induction n.
  - simpl; auto.
  - intros.
    set (q := Forall (Forall p)).
    unfold Forall in q.
Lemma not_some_not_is_every {??} :
  forall (n : nat) (p : Formula),
  ?? ??? Implies (Not (Some n (Not p))) (Every n p).
    assert (?? ??? Not (Some (S n) p) = ?? ??? Not (Exists (Some n p))). { simpl; auto. }
    assert (?? ??? Implies (Not (Exists (Some n p)))
                (Forall (Not (Some n p)))). {
      set (q := (Some n p)).
      apply not_Exists.
    }
    Assume((Not (Exists (Some n p))) :: ?? ??? (Not (Exists (Some n p)))).
    assert(?? ??? (Not (Exists (Some n p))) :: ??). { apply subcontext_weaken; apply subcontext_reflex. }
    apply (@weakening ?? ((Not (Exists (Some n p))) :: ??)) in H1 as H4. 2: assumption.
    apply (@ND_imp_e (Not (Exists (Some n p)) :: ??) (Not (Exists (Some n p)))) in H4.
    2: assumption.
    set (t := fresh_evar ?? Falsum).
    assert (?? ??? capture_free_subst 0 t (Every n (Not p))).
     assert(?? ??? Some (S n) (Not p) = ?? ??? Exists (Some n (Not p))). { simpl; auto. }
    assert(?? ??? Implies (Not (Forall (Every n p)))
                (Exists (Not (Every n p)))). {
      set (q := (Every n p)).
      apply (not_Forall (p := q)).
    }
    assert(?? ??? (Every (S n) p) = ?? ??? (Forall (Every n p))). {
      simpl; auto.
    }
    assert(?? ??? Implies (Not (Every (S n) p))
            (Exists (Not (Every n p)))). {
      assert (?? ??? Implies (Not (Every (S n) p)) (Exists (Not (Every n p)))
              = ?? ??? Implies (Not (Forall (Every n p))) (Exists (Not (Every n p)))). { simpl; auto. }
      apply not_Forall.
    }
    Assume ((Not (Every (S n) p)) :: ?? ??? (Not (Every (S n) p))).
    assert(?? ??? (Not (Every (S n) p)) :: ??). { apply subcontext_weaken; apply subcontext_reflex. }
    apply (@weakening ?? ((Not (Every (S n) p)) :: ??)) in H3 as H6.
    apply (@ND_imp_e ((Not (Every (S n) p)) :: ??) (Not (Every (S n) p))) in H6.
    2: assumption.
*)

Lemma capture_free_subst_every :
  forall (m n : nat) (p : Formula) (t : Term),
  capture_free_subst 0 t (Every m p) = Every m (capture_free_subst m (lift 1 m t) p).
Proof.
  intros. generalize dependent p.
  induction m.
  - intros; unfold Every. assert (lift 1 0 t = t). {
      apply (Term.bigger_lift_is_id 0 0 1). lia. apply term_zero_lift_is_id.
    } rewrite H; reflexivity.
  - intros; assert ((Every (S m) p) = (Every m (Forall p))). { symmetry; apply every_ind. }
    rewrite H. rewrite (IHm (Forall p)). rewrite forall_subst.
    fold (Every (S m)).
    assert (lift (S m) 1 (lift 1 m t) = lift 1 (S m) t). {
      assert (lift (S m) 1 (lift 1 m t) = lift (1 + m) 1 (lift 1 m t)). {
        assert (S m = 1 + m). lia.
        rewrite H0. reflexivity.
      }
      rewrite H0.
      apply (Term.variadic_quantifier_lift_seq m 1 t). lia.
    }
    rewrite H0. rewrite every_ind. reflexivity.
Qed.

Lemma move_forall_from_antecedent {??} :
  forall (m : nat) (p q : Formula),
  ?? ??? Implies p (Forall q) -> ?? ??? Implies (lift 0 1 p) q.
Proof.
  intros.
  apply ND_imp_i2.
  set (t := fresh_evar (lift 0 1 p :: ??) Falsum).
  apply (@weakening ?? (p::??)) in H as H1.
  Assume(p :: ?? ??? p).
  apply (ND_imp_e (p := p)) in H1. 2: assumption. 2: prove_subcontext.
  Check @ND_forall_elim.
  apply (ND_forall_elim (t := t)) in H1 as H2.
Admitted.

Lemma move_every_from_antecedent1 {??} :
  forall (m : nat) (p q : Formula),
  ?? ??? Every m (Implies p (Forall q)) -> ?? ??? Every (S m) (Implies (lift 0 1 p) q).
Proof.
  intros. 
Admitted.

Theorem move_every_from_antecedent {??} :
  forall (m n : nat) (p q : Formula),
  ?? ??? Every m (Implies p (Every n q)) -> ?? ??? Every (m + n) (Implies (lift 0 n p) q).
Proof.
  intros. generalize dependent m. generalize dependent p. generalize dependent q.
  induction n.
  - intros. rewrite PeanoNat.Nat.add_0_r. rewrite Formula.lift_id.
    assert (Every 0 q = q). { unfold Every; reflexivity. }
    rewrite H0 in H. assumption.
  - intros. assert(?? ??? Every m (Implies p (Every (S n) q)) = ?? ??? Every m (Implies p (Forall (Every n q)))). {
      simpl; auto.
    }
    rewrite H0 in H. apply (move_every_from_antecedent1 m p (Every n q)) in H as H1.
    apply IHn in H1 as H2. rewrite lift_comp in H2. rewrite PeanoNat.Nat.add_1_r in H2.
    rewrite (Plus.plus_Snm_nSm m n) in H2. assumption.
Qed.

Theorem provable_antecedent_result {??} :
  forall (m : nat) (gc A body : Formula),
  ?? ??? body -> (gc::??)%list ??? Every m (Implies A body).
Proof.
  intros.
  apply (@weakening ?? (gc::??)%list) in H as H1.
  2: { 
    apply subcontext_weaken; apply subcontext_reflex.
  }
  induction m.
  - unfold Every; apply ND_imp_i2.
    apply (@weakening (gc::??)%list (A :: gc::??)%list).
    assumption.
    apply subcontext_weaken; apply subcontext_reflex.
  - assert (Every (S m) (Implies A body) = Forall (Every m (Implies A body))). {
      simpl; auto.
    } rewrite H0; clear H0.
(*
1 goal
?? : list Formula
m : nat
gc, A, body : Formula
H : ?? ??? body
H1 : gc :: ?? ??? body
IHm : gc :: ?? ??? Every m (Implies A body)
______________________________________(1/1)
gc :: ?? ??? Forall (Every m (Implies A body))
*)
Admitted.

Lemma testing_multiple_forall_stuff2 {?? p q r} :
  ?? ??? Implies q r ->
  ?? ??? Forall (Forall (Implies p q)) ->
  ?? ??? Forall (Forall (Implies p r)).
Proof.
  intros.
  set (t1 := fresh_evar ?? Falsum).
  apply (ND_forall_i (t := t1)). 2: unfold t1; reflexivity.
  assert (capture_free_subst 0 t1 (Forall (Implies p r))
          = Forall (Implies (capture_free_subst 1 t1 p)
                            (capture_free_subst 1 t1 r))). {
    simpl; auto.
  } rewrite H1.
  apply (ND_forall_i (t := t1)). 2: unfold t1; reflexivity.
  assert (capture_free_subst 0 t1 (Implies (capture_free_subst 1 t1 p) (capture_free_subst 1 t1 r))
          = Implies (capture_free_subst 0 t1 ((capture_free_subst 1 t1 p)))
                    (capture_free_subst 0 t1 ((capture_free_subst 1 t1 r)))). {
    simpl; auto.
  } rewrite H2.
  apply ND_imp_i2. clear H1 H2.
  apply (ND_forall_elim (t := Var (BVar (pred 0)))) in H0 as H1.
  rewrite forall_subst in H1.
  unfold lift in H1; unfold liftTerm in H1; unfold term_map_var in H1; unfold lift in H1;
  unfold VLift in H1; simpl in H1.
Admitted.

(* Actually used *)
Theorem variadic_transport {?? m A q r} :
  ?? ??? Implies q r ->
  ?? ??? Every m (Implies A q) ->
  ?? ??? Every m (Implies A r).
Proof.
  intros.
Admitted.

(* Actually used. *)
Theorem variadic_modus_ponens {?? m a p q} :
  ?? ??? Every m (Implies a (Implies p q)) ->
  ?? ??? Every m (Implies a p) ->
  ?? ??? Every m (Implies a q).
Proof.
Admitted.

(* Actually used. *)
Theorem variadic_universal_hypothetical_syllogism {?? m p q r} :
  ?? ??? Implies (Every m (Implies p q))
        (Implies (Every m (Implies q r)) (Every m (Implies p r))).
Proof.
Admitted.

Theorem variadic_premised_universal_hypothetical_syllogism {?? m A p q r} :
  ?? ??? Implies (Every m (Implies A (Forall (Implies p q))))
        (Implies (Every m (Implies A (Forall (Implies q r))))
                 (Every m (Implies A (Forall (Implies p r))))).
Proof.
Admitted.
  