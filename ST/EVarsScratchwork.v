Require Import List.
Require Import Nat.
Import ListNotations.



Lemma eq_list {A} : forall (a : A) (l1 l2 : list A),
  a :: l1 = a :: l2 -> l1 = l2.
Proof.
  intros.
  inversion H. reflexivity.
Qed.

Fixpoint insert (i : nat) (l : list nat) :=
  match l with
  | [] => [i]
  | h :: t => if i <? h then i :: h :: t  
              else if i =? h then l
              else h :: insert i t
  end.

Lemma insert_lt : forall (n h : nat) (t : list nat),
  n < h -> insert n (h :: t) = n :: h :: t.
Admitted.

Lemma insert_eq : forall (n h : nat) (t : list nat),
  n = h -> insert n (h :: t) = h :: t.
Admitted.

Lemma insert_gt : forall (n h : nat) (t : list nat),
  n > h -> insert n (h :: t) = h :: (insert n t).
Admitted.

Require Import Nat.
Require Import Bool.
Require Export Coq.Arith.Compare_dec.
Require Import Coq.Arith.PeanoNat.

Check iff_reflect : forall (P : Prop) (b : bool),
    P <-> b = true -> reflect P b.

Lemma eqb_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.eqb_eq.
Qed.
Lemma ltb_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.ltb_lt.
Qed.
Lemma leb_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.leb_le.
Qed.

Hint Resolve ltb_reflect leb_reflect eqb_reflect : bdestruct.
Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [eauto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].

Require Import Lia.

Inductive sorted : list nat -> Prop :=
| sorted_nil :
    sorted []
| sorted_1 : forall x,
    sorted [x]
| sorted_cons : forall x y l,
    x < y -> sorted (y :: l) -> sorted (x :: y :: l).

Theorem sorted_tl : forall (n : nat) (l : list nat),
  sorted (n :: l) -> sorted l.
Proof.
  intros. induction l.
  - apply sorted_nil.
  - inversion H. assumption.
Qed.

Theorem insert_nondecreasing : forall (n : nat) (l : list nat),
  length l <= length (insert n l).
Admitted.

Theorem insert_nonempty : forall (n : nat) (l : list nat),
  [] <> (insert n l).
Proof. intros. induction l.
  - unfold insert. apply nil_cons.
Admitted.

(*
Lemma uh_what : forall (n : nat) (l : list nat),
  n::l <> [].
Proof. intros. apply  not_eq_sym. apply nil_cons. Qed.
*)

Lemma sorted_insert_sorted_tl : forall (n : nat) (l : list nat),
  sorted (insert n l) -> sorted l.
Admitted.

Lemma sorted_split : forall (l1 l2 : list nat),
  sorted (l1 ++ l2) -> sorted l1 /\ sorted l2.
Proof. intros. induction l1.
  - rewrite (app_nil_l l2) in H; split. apply sorted_nil. apply H.
  - rewrite <- (app_comm_cons l1 l2 a) in H. apply sorted_tl in H as H1.
    apply IHl1 in H1. split. destruct l1.
  -- apply sorted_1.
  -- inversion H. assert (sorted (n :: l1)). apply H1. apply sorted_tl in H6 as H7.
     apply (sorted_cons a n l1). assumption. assumption.
  -- apply H1.
Qed.

Lemma sorted_head : forall (n k : nat) (l : list nat),
  sorted (n :: l) -> In k l -> n < k.
Proof.
  intros. induction l.
  - contradict H0.
  - apply (sorted_tl n (a::l)) in H as IH. destruct l.
  -- unfold In in H0. inversion H. destruct H0. apply eq_sym in H0. rewrite H0. assumption.
     contradict H0.
  -- inversion H. inversion H5. clear H6 H7 H9 H1 H2 H4.
     assert (n < n0). { rewrite <- H8. assumption. }
     inversion H0. apply eq_sym in H2. rewrite H2. assumption.
     apply (sorted_cons n n0 l) in H1. apply IHl in H1 as IH1. assumption. assumption.
     assumption.
Qed.

Lemma sorted_split_ends : forall (l1 l2 : list nat),
  sorted (l1 ++ l2) ->
  (forall (a b : nat), In a l1 /\ In b l2 -> a < b).
Proof. intros. induction l1.
  - apply proj1 in H0. contradict H0.
  - apply proj1 in H0 as H1; apply proj2 in H0 as H2.
    destruct l1.
 -- (* Subcase: l1 = [] *) apply sorted_tl in H as IH. 
    unfold app in IHl1; unfold app in H. assert (a0 = a). { unfold In in H1. intuition. }
    rewrite H3 in H; rewrite H3 in H1; rewrite H3 in H0.
    apply (sorted_head a b l2) in H. assumption. assumption.
 -- (* Subcase: l1 = n :: l1 *) 
    rewrite <- (app_comm_cons (n :: l1) l2 a0) in H.
    apply sorted_tl in H as IH. 
    assert (a = a0 \/ a <> a0). { lia. }
    inversion H3.
  + (* a = a0 *) rewrite <- H4 in H; rewrite <- H4 in H1.
    apply (sorted_head a b ((n :: l1) ++ l2)) in H.
    assumption. apply (in_or_app (n :: l1) l2 b). auto.
  + (* a <> a0 *)
    assert (In a (n :: l1)). { inversion H1. apply eq_sym in H5. 
      contradict H5. assumption. assumption.
    }
    apply IHl1 in IH. assumption. split. assumption. assumption.
Qed.

Lemma insert_split : forall (n : nat) (l1 l2 : list nat),
  sorted (l1 ++ n::l2) -> (l1 ++ n::l2) = insert n (l1 ++ n::l2).
Admitted.

Theorem insert_existing_sorted : forall (n : nat) (l : list nat),
  sorted l -> In n l -> l = insert n l.
Proof.
  intros.
  apply in_split in H0 as H1. destruct H1. destruct H1.
  rewrite H1 in H.
  apply insert_split in H.
  rewrite <- H1 in H. apply H.
Qed.

Theorem insert_singleton_invert : forall (n x : nat) (l : list nat),
  [x] = (insert n l) -> l = [].
Proof.
  intros. assert (sorted [x]). apply sorted_1.
  assert (sorted (insert n l)). rewrite <- H. assumption.
  apply sorted_insert_sorted_tl in H1 as H2.
  inversion H1. auto.
  destruct l. 
  - reflexivity.
  - assert ([] <> n0 :: l). apply nil_cons.
Admitted.

Require Import Coq.Classes.RelationClasses.

Theorem nat_comparison : forall (a b : nat),
  a < b \/ a = b \/ a > b.
Proof.
  intros. lia.
Qed.

Lemma gt_to_not_ltb : forall (n a : nat),
  n > a -> Nat.ltb n a = false.
Admitted.

Lemma gt_to_not_eqb : forall (n a : nat),
  n > a -> Nat.eqb n a = false.
Admitted.

Lemma sorted_omit : forall (a b : nat) (l : list nat),
  sorted (a :: b :: l) -> sorted (a :: l).
Proof.
  intros.
  induction l.
  - apply sorted_1.
  - apply sorted_tl in H as H1. apply sorted_tl in H1.
    inversion H. clear H0 H2 H4.
    inversion H5. clear H0 H2 H6.
    assert (a < a0). lia.
    apply sorted_cons. assumption. assumption.
Qed.

Lemma invert_insert_sorted : forall (n a n0 : nat) (l l0 : list nat),
  sorted (a :: l) -> insert n (a :: l) = a :: n0 :: l0 ->
  a < n0.
(*
Proof.
  intros. induction l.
  2: { inversion H. apply sorted_tl in H5.
   apply (sorted_1 a) in H. unfold insert in H0.
  inversion H0.
*)
Admitted.

Theorem insert_preserves_sorted : forall (n : nat) (l : list nat),
  sorted l -> sorted (insert n l).
Proof.
  intros.
  induction l.
  - unfold insert. apply sorted_1.
  - apply sorted_tl in H as H1. apply IHl in H1.
    assert (n < a \/ n = a \/ n > a). lia.
    inversion H0.
  -- (*  Case: n < a *)
     apply (insert_lt n a l) in H2 as H3. rewrite H3.
     apply sorted_cons. assumption. assumption.
  -- (* Case: n = a *)
     inversion H2. apply (insert_eq n a l) in H3 as H4. rewrite H4.
     assumption.
     (* Case: n > a *)
     apply (insert_gt n a l) in H3 as H4. rewrite H4. destruct (insert n l).
  + apply sorted_1.
  + clear H0; clear H2.
    apply sorted_tl in H1 as H5.
    assert (n < n0 \/ n = n0 \/ n > n0). lia. inversion H0.
    (* case: n < n0 *)
  ++ apply sorted_cons. rewrite <- H2. assumption. assumption.
  ++ (* case: n = n0 *)
     inversion H2. apply sorted_cons. rewrite <- H6. assumption. assumption.
     (* case: n > n0 *)
     clear H2 H0.
     inversion H4. apply gt_to_not_ltb in H3 as H8.
     rewrite H8. rewrite H8 in H2. clear H8; apply gt_to_not_eqb in H3 as H8.
     rewrite H8; rewrite H8 in H2.
     apply (invert_insert_sorted n a n0 l l0) in H4 as H7.
     apply eq_list in H2. rewrite H2. apply sorted_cons. assumption.
     assumption. assumption.
Qed.


Theorem insert_preserves_sorted2 : forall (n : nat) (l : list nat),
  sorted l -> sorted (insert n l).
Proof.
  intros.
  induction l.
  - unfold insert. apply sorted_1.
  - apply sorted_tl in H as H1. apply IHl in H1.
    assert (n < a \/ n = a \/ n > a). lia.
    inversion H0.
  -- apply (insert_lt n a l) in H2 as H3. rewrite H3.
     apply sorted_cons. assumption. assumption.
  -- inversion H2.
  --- apply (insert_eq n a l) in H3 as H4. rewrite H4. assumption.
  --- apply (insert_gt n a l) in H3 as H4. rewrite H4.
      destruct (insert n l). apply sorted_1.
      set (ln := insert n l). inversion H4. auto; simpl.
  + apply sorted_1.
  + assert (n = n0 \/ n <> n0). lia. inversion H5.
  ++ apply sorted_cons. rewrite <- H6. assumption. rewrite <- H6.
  +  unfold insert in ln. unfold ln. apply sorted_cons.
    assumption. apply sorted_1.
  + 

      destruct l.
  + unfold insert. apply sorted_cons. assumption. apply sorted_1.
  + 
      set (ln := insert n l). destruct l. auto.
      apply (sorted_cons a n l) in H3.
      apply (sorted_tl a (insert n l)) in H1 as H5.
      apply sorted_tl with (n := a) (l := insert n l) in H1 as H5.
      apply (sorted_cons a n l) in H3.
Admitted.





Theorem insert_preserves_sorted : forall (n : nat) (l : list nat),
  sorted l -> sorted (insert n l).
Proof.
  intros.
  induction l.
  - unfold insert. apply sorted_1.
  - apply sorted_tl in H as H1. apply IHl in H1.
    assert (n < a \/ n = a \/ n > a). lia.
    inversion H0.
  -- apply (insert_lt n a l) in H2 as H3. rewrite H3.
     apply sorted_cons. assumption. assumption.
  -- inversion H2.
  --- apply (insert_eq n a l) in H3 as H4. rewrite H4. assumption.
  --- apply (insert_gt n a l) in H3 as H4. rewrite H4.
      apply (sorted_cons a n l) in H3.

  -- contradict H2. apply insert_nonempty.
  -- apply (insert_singleton_invert n x l) in H2. rewrite H2.
     assert (n < a \/ n = a \/ n > a). lia.
     inversion H0.
  --- apply (insert_lt n a []) in H3 as H4. rewrite H4.
      apply sorted_cons. assumption. apply sorted_1.
  --- inversion H3. apply (insert_eq n a []) in H4 as H5. rewrite H5.
      apply sorted_1.
      apply (insert_gt n a []) in H4 as H5. rewrite H5. unfold insert.
      apply sorted_cons. assumption. apply sorted_1.
  -- auto.
  --- auto.

Lemma insert_different : forall (a n : nat) (l : list nat),
  sorted (a :: l) -> a <> n ->
  (n < a -> sorted (n :: a :: l)) /\ (a < n -> sorted (a :: insert n l)).
Proof.
  intros. split.
  - intro H1. apply sorted_cons. assumption. assumption.
  - intro H1. apply (insert_gt n a l) in H1 as H2. rewrite <- H2.

 apply sorted_tl in H as H2. destruct l.
  -- unfold insert. apply sorted_cons. assumption. apply sorted_1.
  -- apply (sorted_cons a n (n0 :: l)) in H1. inversion H1.
     unfold insert.
  assert (a < n \/ n > a).
  2: { split. }

Theorem insert_if_present :
  forall (n : nat) (l : list nat),
  sorted l -> In n l -> insert n l = l.
Proof.
  intros. induction l.
  - unfold In in H. contradiction.
  - bdestruct (n =? a).
  -- unfold insert. 
     assert (~ n < a). { lia. } (* intuition. *)
     assert (Nat.ltb n a = false). { apply Nat.nlt_ge in H2 as H3.
      unfold Nat.ltb. apply leb_correct_conv. intuition.
     }
     rewrite H3. apply (Nat.eqb_eq n a) in H1. rewrite H1. reflexivity.
  -- apply List.in_inv in H0 as H2.
     assert (List.In n l).  {  firstorder. contradict H0. auto. }
     apply sorted_tl in H as H4.
     apply IHl in H3 as IHl2. discriminate. intuition.
  --- symmetry in H5. contradict H5. auto.
  --- auto.
     assert (a < n).
     2: { intuition. apply Nat.ltb_lt in H5 as H6. unfold insert. apply H6.
  --- unfold insert. apply Nat.eqb_eq in H5.
 simpl. auto.
 apply (ltb_reflect n a) in H1. auto.
 rewrite H0. rewrite <- H0.
Lemma insert_different : forall (a n : nat) (l : list nat),
  sorted (a :: l) -> a <> n ->
  sorted (n :: a :: l) \/ sorted (a :: insert n l).


