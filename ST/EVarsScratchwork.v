Require Import List.
Require Import Nat.
Require Import Bool.
Require Export Coq.Arith.Compare_dec.
Require Import Coq.Arith.Lt.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

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

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [eauto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].
#[export]
Hint Resolve ltb_reflect leb_reflect eqb_reflect : bdestruct.

Lemma eq_list {A} : forall (a : A) (l1 l2 : list A),
  a :: l1 = a :: l2 -> l1 = l2.
Proof.
  intros.
  inversion H. reflexivity.
Qed.

(** * Insertion

Inserting a number into a list will guarantee the number appears exactly once.
*)
Fixpoint insert (i : nat) (l : list nat) :=
  match l with
  | [] => [i]
  | h :: t => if i <? h then i :: h :: t  
              else if i =? h then l
              else h :: insert i t
  end.

Lemma insert_lt : forall (n h : nat) (t : list nat),
  n < h -> insert n (h :: t) = n :: h :: t.
Proof.
  intros.
  apply Nat.ltb_lt in H as H1.
  unfold insert. rewrite H1. reflexivity.
Qed.

Lemma insert_eq : forall (n h : nat) (t : list nat),
  n = h -> insert n (h :: t) = h :: t.
Proof.
  intros.
  apply Nat.eqb_eq in H as H1. 
  unfold insert.
  destruct (ltb_reflect n h). 
  contradict l. Nat.order.
  rewrite H1. reflexivity.
Qed.

Lemma insert_gt : forall (n h : nat) (t : list nat),
  n > h -> insert n (h :: t) = h :: (insert n t).
Proof.
  intros.
  apply Nat.ltb_lt in H as H1.
  unfold insert.
  destruct (ltb_reflect n h). 
  contradict l. apply le_not_lt. lia.
  destruct (eqb_reflect n h). 
  contradict e. lia. reflexivity.
Qed.

Theorem insert_inv : forall (n : nat) (l : list nat),
  In n (insert n l).
Proof.
  intros.
  induction l.
  - (* Base case: l = [] *)
    unfold insert; unfold In. auto.
  - (* Inductive case: l = a::l *)
    assert (n = a \/ n > a \/ n < a). lia.
    inversion H.
  -- (* Subcase: n = a *) 
    rewrite <- H0. apply Nat.eqb_eq in H0 as H1. unfold insert.
    destruct (ltb_reflect n n). apply (in_eq n (n :: l)).
    rewrite <- H0 in H1. rewrite H1. apply (in_eq n l).
  -- inversion H0.
  --- (* Subcase: n > a *)
      apply (insert_gt n a l) in H1 as H2. rewrite H2.
      apply (in_cons a n (insert n l)). assumption.
  --- (* Subcase: n < a *)
      apply (insert_lt n a l) in H1 as H2. rewrite H2.
      apply (in_eq n (a :: l)).
Qed.

Theorem insert_preserves_elts : forall (e n : nat) (l : list nat),
  In e l -> In e (insert n l).
Proof.
  intros. induction l.
  - contradict H.
  - (* Inductive case: l = a :: l *) 
    assert (e = a \/ e <> a). lia. inversion H0.
    + (* Case: e = a *) 
      assert (n = a \/ n < a \/ n > a). lia. inversion H2.
      ++ apply (insert_eq n a l) in H3. rewrite H3. assumption.
      ++ inversion H3.
      +++ (* Subcase: n = a *)
          apply (insert_lt n a l) in H4 as H5. rewrite H5. rewrite <- H1.
          unfold In. auto.
      +++ (* Subcase n < a *)
          apply (insert_gt n a l) in H4 as H5. rewrite H5. rewrite <- H1.
          apply (in_eq e (insert n l)).
    + (* Case: e <> a *)
      assert (n = a \/ n < a \/ n > a). lia. inversion H2.
    ++ (* Subcase: a = n *)
       apply (insert_eq n a l) in H3 as H4. rewrite H4. assumption.
    ++ inversion H3.
    +++ (* Subcase: n < a *)
        apply (insert_lt n a l) in H4 as H5. rewrite H5.
        assert (e = n \/ e <> n). lia. inversion H6.
        rewrite H7. apply (in_eq n (a::l)).
        unfold In. simpl; auto.
    +++ (* Subcase: n > a *)
        apply (insert_gt n a l) in H4 as H5. rewrite H5.
        assert (e = n \/ e <> n). lia. inversion H6.
        rewrite H7. apply (in_cons a n (insert n l)). apply (insert_inv n l).
        apply (in_cons a e (insert n l)).
        inversion H. apply eq_sym in H8. contradict H8. assumption.
         apply IHl. assumption.
Qed.

Theorem insert_nonempty : forall (n : nat) (l : list nat),
  [] <> (insert n l).
Proof. intros. induction l.
  - unfold insert. apply nil_cons.
  - assert (n < a \/ n = a \/ n > a). lia. inversion H.
  + apply (insert_lt n a l) in H0 as H1. rewrite H1. discriminate.
  + inversion H0.
  ++ apply (insert_eq n a l) in H1 as H2. rewrite H2. discriminate.
  ++ apply (insert_gt n a l) in H1 as H2. rewrite H2. discriminate.
Qed.


(** Now we have an inductive way to specify if our set of [nat]
is sorted or not. *)
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

Lemma sorted_head : forall (n a : nat) (l : list nat),
  sorted (a :: l) -> Some a = hd_error (insert n (a :: l)) \/ Some n = hd_error (insert n (a :: l)).
Proof.
  intros.
  assert (a < n \/ n = a \/ a > n). lia. inversion H0.
  - (* Case 1: a < n *)
    apply (insert_gt n a l) in H1. left. rewrite H1. unfold hd_error. reflexivity.
  - inversion H1.
  + (* Case 2: a = n *)
    apply (insert_eq n a l) in H2. left. rewrite H2. unfold hd_error. reflexivity.
  + (* Case 3: a > n *)
    apply (insert_lt n a l) in H2. right. rewrite H2. unfold hd_error. reflexivity.
Qed.

Lemma sorted_head_ge : forall (n a : nat) (l : list nat),
  sorted (a :: l) -> n >= a -> Some a = hd_error (insert n (a :: l)).
Proof.
  intros. assert (n = a \/ n > a). lia. inversion H1.
  - (* Case: a = n *)
    apply (insert_eq n a l) in H2. rewrite H2. unfold hd_error; reflexivity.
  - (* Case: n > a *)
    apply (insert_gt n a l) in H2. rewrite H2. unfold hd_error; reflexivity.
Qed.

(*
Lemma sorted_tail : forall (n : nat) (l l0 : list nat),
  sorted l -> n :: l0 = insert n l -> (~(In n l) -> l0 = l).
Proof.
  intros. inversion H.
  destruct l as [|a tl]. 
  - (* Case: l = [] *)
  unfold insert in H0; injection H0; auto.
  - (* Case: l = a::tl *)
  (* Goal: l0 = a :: tl *)
  inversion H as [|b|b tl']. (* sorted (a :: tl) can be considerd in two 
  subcases: tl=[] and sorted_cons : a < b -> sorted (b::tl') -> sorted(a::b::tl').
  The sorted_nil case isn't possible. *)
  + (* Subcase: l = a::[] *)
  rewrite <- H3 in H; rewrite <- H3 in H0; rewrite <- H3 in H1.
  
  - (* Subcase: l = a::b::tl' *)
  apply sorted_tl in H as IH. 
  apply IHtl in IH.
  inversion H.
  + (* Subcase: tl = []; goal becomes l0 = [a] *)
  rewrite <- H4 in H0.
  
  inversion H0.
  assert (sorted []) as IH. apply sorted_nil.
  apply IHtl in IH.
  
  apply IHtl in H1.
  assert(In n (insert n tl)).

  assert (a < n \/ n = a \/ a > n). lia.
  inversion H1.
  - apply (insert_gt n a l) in H2 as H3.
    assert (n :: l0 = a :: insert n l). { rewrite <- H3; rewrite <- H0; reflexivity. }
Admitted.

Lemma sorted_insert_sorted_tl : forall (n : nat) (l : list nat),
  sorted (insert n l) -> sorted l.
Proof.
  intros. induction l.
  - apply sorted_nil.
  - (* Inductive case: l = a :: l *)
    assert (n < a \/ n = a \/ n > a). lia. inversion H0.
  + (* Subcase: n < a *)
    apply (insert_lt n a l) in H1 as H2. rewrite H2 in H.
    apply (sorted_cons n a l) in H1. apply sorted_tl in H1 as H3. assumption.
    apply sorted_tl in H. assumption.
  + inversion H1.
  ++ (* Subcase: n = a *)
     apply (insert_eq n a l) in H2 as H3. rewrite H3 in H. assumption.
  ++ (* Subcase: n > a *)
     apply (insert_gt n a l) in H2 as H3. rewrite H3 in H.
     apply sorted_tl in H as IH. apply IHl in IH.
     inversion IH. apply sorted_1. rewrite <- H4 in H.
     assert (x < n \/ x = n \/ x > n). lia. inversion H5.
     (* Sub-subcases [sorted [a; x]]. *)
     * (* Sub-subcase: x < n *)
       apply (insert_gt n x []) in H6 as H7. rewrite H7 in H. unfold insert in H.
       inversion H. apply (sorted_cons a x []) in H10 as H13. assumption.
       apply sorted_1.
     * inversion H6.
     ** (* Sub-subcase: x = n *) apply eq_sym in H7.
        apply (insert_eq n x []) in H7 as H8. rewrite H8 in H. assumption.
     ** (* Sub-subcase: x > n *)
        assert (a < x). lia.
        apply (sorted_cons a x []) in H8. assumption. apply sorted_1.
     (* Subcases to prove [sorted (a :: x :: y :: l0)] *)
     * apply (sorted_cons x y l0) in H4 as H4a. inversion H. contradict H9.
       apply (insert_nonempty n l).
       assert (Some y0 = hd_error (insert n l)). { rewrite <- H8. unfold hd_error; reflexivity. }
       assert (x = y0 \/ n = y0). { apply (sorted_head n x (y :: l0)) in H4a as H4b.
       rewrite H6 in H4b. rewrite <- H11 in H4b. inversion H4b.
       left. injection H12. auto.
       right. injection H12. auto. }
       inversion H12.
     ** (* insert n l = x :: (stuff) *) 
       rewrite <- H13 in H8; rewrite <- H13 in H10; rewrite <- H13 in H9.
       apply (sorted_cons a x (y :: l0)) in H9. apply H9. apply H4a.
     ** (* insert n l = n :: l *)
       rewrite <- H13 in H8; rewrite <- H13 in H10; rewrite <- H13 in H9.
       inversion H8. unfold insert in H15. rewrite <- H6 in H15. 
       apply (sorted_cons a n (y :: l0)) in H9. apply H9.
        sorted (a :: n :: y :: l0)
       rewrite H6 in H4b. 
        apply (insert_lt n x []) in H7 as H8. rewrite H8 in H.
     unfold insert in H. 
     
     induction l. apply sorted_1.
     inversion IH. rewrite <- H6 in IH.
Admitted.
*)

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

Lemma sorted_head_min : forall (n k : nat) (l : list nat),
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

(*
Lemma sorted_split_ends : forall (l1 l2 : list nat),
  sorted (l1 ++ l2) ->
  (forall (a b : nat), In a l1 /\ In b l2 -> a < b).
Admitted.
Proof. intros. induction l1.
  - apply proj1 in H0. contradict H0.
  - apply proj1 in H0 as H1; apply proj2 in H0 as H2.
    destruct l1.
 -- (* Subcase: l1 = [] *) apply sorted_tl in H as IH. 
    unfold app in IHl1; unfold app in H. assert (a0 = a). { unfold In in H1. intuition. }
    rewrite H3 in H; rewrite H3 in H1; rewrite H3 in H0.
    apply (sorted_head b a l2) in H. apply IHl1 in IH. assumption. assumption.
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
*)

(*

Theorem insert_existing_sorted : forall (n : nat) (l : list nat),
  sorted l -> In n l -> l = insert n l.
Proof.
  intros.
  apply in_split in H0 as H1. destruct H1. destruct H1.
  rewrite H1 in H.
  apply insert_split in H.
  rewrite <- H1 in H. apply H.
Qed.
*)

Lemma sorted_in_inv : forall (n h : nat) (tl : list nat),
  sorted(h :: tl) -> In n (h::tl) -> h=n \/ (In n tl).
Proof.
  intros. apply in_inv in H0. trivial.
Qed.

Lemma sorted_surgery : forall ( a b : nat) (tl : list nat),
  sorted (a :: b :: tl) -> sorted (a :: tl).
Proof.
  intros. inversion H. apply sorted_tl in H4 as H5.
  destruct tl.
  - apply sorted_1.
  - inversion H4.
    assert (a < n). { Nat.order. }
    apply (sorted_cons a n tl) in H11. assumption. assumption.
Qed.


Lemma sorted_in_tl : forall (n h : nat) (tl : list nat),
  sorted (h :: tl) -> In n tl -> h < n.
Proof.
  intros. induction tl.
  - (* Base case: tl = [] *)
    contradict H0.
  - (* Inductive case: tl = a::tl *)
    inversion H.
(*
  -- (* Case: sorted_1 *)
    contradict H0. rewrite <- H3. apply in_nil.
*)
  -- (* Case: sorted_cons where [h < y] and [tl = y::l] *)
    rewrite <- H2 in H0. apply in_inv in H0 as H6.
    case H6.
  + (* Subcase: [n = y] *)
    intro. rewrite H7 in H2. rewrite <- H2 in H3. assumption.
  + (* Subcase: [In n l] *)
    intro. apply sorted_surgery in H as IH. apply IHtl in IH.
    apply IH. assumption.
Qed.

Theorem insert_existing_sorted : forall (n : nat) (l : list nat),
  sorted l -> In n l -> l = insert n l.
Proof.
  intros. 
  induction l as [|h tl].
  - contradict H0. 
  - inversion H.
  + rewrite <- H3 in H0; rewrite <- H3 in H.
    assert (h = n). { unfold In in H0. intuition. }
    rewrite H1; rewrite H1 in H0; rewrite H1 in H.
    assert (n = n). reflexivity.
    apply (insert_eq n n []) in H4. symmetry. assumption.
  + (* Subcase sorted_cons : tl=y::l, h < y, sorted(y :: l) *)
    apply in_inv in H0. case H0. 
  ++ (* Case of [In h n::tl] when [h = n] *)
    intro. rewrite H5. rewrite (insert_eq n n (y::l)). reflexivity. reflexivity.
  ++ (* Case of [In h n::tl] when [In h tl] *)
    intro. (* apply sorted_tl in H as IH. apply IHtl in IH. *)
    rewrite <- H2 in H5. apply in_inv in H5. case H5.
    (* Since [tl = y::l], we do this again! *)
  +++ intro.  rewrite H6; rewrite H6 in H5; rewrite H6 in H2; rewrite H6 in H3; rewrite H6 in H4.
    rewrite (insert_gt n h (n :: l)).
    rewrite (insert_eq n n l). reflexivity. reflexivity. assumption.
  +++ (* Last case: In n l -> h :: y :: l = insert n (h :: y :: l) *)
    intro. (* INDUCTION SAVES US, AT LONG LAST! *)
    apply sorted_tl in H as IH. apply IHtl in IH.
    rewrite H2. apply (sorted_in_tl n h tl) in H as IH1.
    apply (insert_gt n h tl) in IH1. rewrite <- IH in IH1. auto.
    rewrite <- H2. simpl; auto.
    rewrite <- H2. simpl; auto.
Qed.

Lemma eq_lists_eq_len {A} : forall (l1 l2 : list A),
  l1 = l2 -> length l1 = length l2.
Proof.
  intros.
  rewrite H. reflexivity.
Qed.

(*
Theorem insert_nondecreasing : forall (n : nat) (l : list nat),
  sorted l -> length l <= length (insert n l).
Proof.
  intros.
  assert (In n l \/ ~In n l).
  2: { inversion H0.
  - apply (insert_existing_sorted n l) in H as H2. 
    apply eq_lists_eq_len in H2 as H3. Nat.order. assumption.
  - 
  assumption.
  
Admitted.

*)









Lemma in_singleton_eq : forall {A} (a x : A),
  In a [x] -> a = x.
Proof. intros. unfold In in H. intuition. Qed.


Theorem insert_singleton_invert : forall (n x : nat) (l : list nat),
  [x] = (insert n l) -> l = [] \/ l = [n].
Proof.
  intros. 
  assert (sorted [x]). apply sorted_1.
  rewrite H in H0. 
  assert (In n [x]). { rewrite H. apply (insert_inv n l). }
  apply  (in_singleton_eq n x) in H1. rewrite <- H1 in H.
  clear H1.
  induction l as [|n0 l0].
  - (* Case: l = [] *) left; reflexivity.
  - (* Case: l = n0::l0 *) 
    assert (n < n0 \/ n = n0 \/ n > n0). lia. 
  -- destruct H1.
  + (* Subcase: n < n0 *)
    apply (insert_lt n n0 l0) in H1. rewrite H1 in H; rewrite H1 in H0.
    inversion H0; right; discriminate.
  + destruct H1.
  ++ (* Subcase: n = n0 *)
    apply (insert_eq n n0 l0) in H1. rewrite H1 in H; rewrite H1 in H0.
    right; symmetry. apply H.
  ++ (* Subcase: n > n0 *)
    apply  (insert_gt n n0 l0) in H1 as H2. rewrite H2 in H; rewrite H2 in H0.
    inversion H0.
  +++ (* Sub-subcase (sorted_1) : l0 = [] *)
    right. rewrite <- H5 in H.
    contradict H5. apply (insert_nonempty n l0).
  +++ (* Sub-subcase (sorted_cons) [sorted (insert n (n0 :: l0))] becomes : 
         n0 < y -> sorted( y :: l) -> sorted(n0 :: y :: l)*)
      rewrite <- H4 in H; rewrite <- H4 in H2. left. discriminate.
Qed.

Require Import Coq.Classes.RelationClasses.

Theorem nat_comparison : forall (a b : nat),
  a < b \/ a = b \/ a > b.
Proof.
  intros. lia.
Qed.

Lemma gt_to_not_ltb : forall (n a : nat),
  n > a -> Nat.ltb n a = false.
Proof. intros.
  bdestruct (n <? a); simpl.
  contradict H0. lia. reflexivity.
Qed.

Lemma gt_to_not_eqb : forall (n a : nat),
  n > a -> Nat.eqb n a = false.
Proof. intros.
  bdestruct (n =? a); simpl.
  contradict H0. lia. reflexivity.
Qed.


Lemma invert_insert_sorted : forall (n a n0 : nat) (l l0 : list nat),
  sorted (a :: l) -> insert n (a :: l) = a :: n0 :: l0 ->
  a < n0.
Proof.
  intros.
  assert (a > n \/ a = n \/ a < n). lia.
  generalize dependent l0.
  induction l.
  - intros. destruct H1.
  -- (* Subcase: a > n *)
    apply (insert_lt n a []) in H1 as H2. rewrite H2 in H0.
    contradict H0. injection. intros. lia.
  -- destruct H1.
  --- (* Subcase: a = n *) apply eq_sym in H1.
    apply (insert_eq n a []) in H1 as H2. rewrite H2 in H0.
    contradict H0. injection. discriminate.
  --- (* Subcase: a < n *)
    apply (insert_gt n a []) in H1 as H2. rewrite H2 in H0.
    unfold insert in H0. injection H0. intros. rewrite H4 in H1. assumption.
 - (* Inductive case: l = a0::l *)
  destruct H1.
  -- intros. apply Nat.ltb_lt in H0 as H2. unfold insert in H1.
    rewrite H2 in H1. contradict H1. injection.
    intros. rewrite <- H3 in H1. injection H1. intro. lia.
  -- destruct H0.
  + (* Subcase: a = n *) intros. apply eq_sym in H0.
    apply (insert_eq n a (a0::l)) in H0 as H3.
    rewrite H3 in H1. injection H1. intros.
    rewrite H4 in H. inversion H. assumption.
  + (* Subase: a < n *) intros.
    apply (sorted_surgery a a0 l) in H as IH.
    apply (insert_gt n a (a0 :: l)) in H0 as H2.
    assert (a0 < n \/ a0 = n \/ a0 > n). lia.
    destruct H3.
  ++ (* a0 < n *)
    apply (insert_gt n a0 l) in H3 as H4.
    apply (insert_gt n a (a0 :: l)) in H0 as H5.
    rewrite H4 in H2. rewrite H2 in H1. injection H1.
    intros. rewrite H7 in H. inversion H. assumption.
  ++ destruct H3.
  * (* Case a0 = n *) apply eq_sym in H3.
    apply (insert_eq n a0 l) in H3 as H4.
    rewrite H4 in H2. rewrite H2 in H1. injection H1. intros.
    inversion H. rewrite H6 in H9. assumption.
  * (* Case a0 > n *)
    apply (insert_lt n a0 l) in H3 as H4. 
    assert (insert n (a :: a0 :: l) = a :: insert n (a0 :: l)). assumption.
    rewrite H4 in H2.
    rewrite H4 in H5. rewrite H1 in H5. injection H5. intros. rewrite H7. assumption.
Qed. 

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

(*
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
*)



(*
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
*)

Lemma insert_different : forall (a n : nat) (l : list nat),
  sorted (a :: l) -> a <> n ->
  (n < a -> sorted (n :: a :: l)) /\ (a < n -> sorted (a :: insert n l)).
  (*
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
*)
Admitted.

(*
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

*)

Fixpoint insert_merge (l1 l2 : list nat) :=
match l1 with
| [] => l2
| a::tl => insert_merge tl (insert a l2)
end.

Theorem insert_merge_sorted : forall (l1 l2 : list nat),
  sorted l1 -> sorted l2 -> sorted (insert_merge l1 l2).
Proof.
  intros. generalize dependent l2.
  induction l1.
  - (* Base case: l1 = nil *)
    intros. unfold insert_merge; auto.
  - (* Inductive case: l1 = a::l1 *)
    intros.
    assert (forall l2 : list nat, sorted l2 -> sorted (insert_merge l1 l2)). {
      apply IHl1. apply sorted_tl in H. assumption.
    }
    assert (sorted (insert a l2)). {
    apply insert_preserves_sorted. assumption.
    }
    assert (insert_merge (a :: l1) l2 = insert_merge l1 (insert a l2)). {
      unfold insert. simpl; auto.
    }
    rewrite H3.
    apply H1 in H2. assumption.
Qed.

Theorem insert_merge_sorted2 : forall (l1 l2 : list nat),
  sorted l2 -> sorted (insert_merge l1 l2).
Proof.
  intros. generalize dependent l2.
  induction l1.
  - (* Base case: l1 = nil *)
    intros. unfold insert_merge; auto.
  - (* Inductive case: l1 = a::l1 *)
    intros.
    assert (forall l2 : list nat, sorted l2 -> sorted (insert_merge l1 l2)). {
      apply IHl1.
    }
    assert (sorted (insert a l2)). {
    apply insert_preserves_sorted. assumption.
    }
    assert (insert_merge (a :: l1) l2 = insert_merge l1 (insert a l2)). {
      unfold insert. simpl; auto.
    }
    rewrite H2. apply H0.
    apply insert_preserves_sorted. assumption.
Qed.

Theorem insert_merge_idempotent : forall (l1 l2 : list nat),
  sorted l2 -> incl l1 l2 -> l2 = insert_merge l1 l2.
Proof.
  intros.
  induction l1.
  - simpl; auto.
  - apply incl_cons_inv in H0 as H1. destruct H1.
    assert (insert_merge (a :: l1) l2 = insert_merge l1 (insert a l2)). {
      simpl; auto.
    }
    assert(l2 = insert a l2). { apply insert_existing_sorted. assumption. assumption. }
    rewrite H3. rewrite <- H4.
    apply IHl1.
    assumption.
Qed.

Lemma insert_merge_idem_right : forall l,
  insert_merge l [] = l.
Admitted.

(** * Fresh Number

The other important function we want to implement concerns,
given a list [l : list nat], find the first natural number
*not* in the list.
*)

Fixpoint first_new (n : nat) (l : list nat) : nat :=
match l with
| (h::tl)%list => if Nat.eqb h n then first_new (S n) tl else first_new n tl
| []%list => n
end.

Lemma first_new_eq {l n} :
  first_new n (n::l) = first_new (S n) l.
Proof.
  intros.
  assert (Nat.eqb n n = true). apply Nat.eqb_eq; reflexivity.
  unfold first_new; rewrite H. reflexivity.
Qed.

Require Import Coq.Arith.EqNat.

Lemma neq_is_neqb {a b} :
  a <> b -> Nat.eqb a b = false.
Admitted.

Lemma first_new_not_eq {l a n} :
  a <> n -> first_new n (a::l) = first_new n l.
Proof.
  intros.
  assert (Nat.eqb a n = false). apply neq_is_neqb; assumption.
  unfold first_new. rewrite H0. simpl; auto.
Qed. 

Require Import Coq.Lists.ListDec.

Theorem first_new_nondecreasing {l n} :
  n <= first_new n l.
Proof.
  generalize dependent n. induction l.
  - simpl; auto.
  - intros.
    assert({a = n} + {a <> n}). decide equality.
    destruct H.
    + (* Case: a = n *) rewrite e.
      assert (first_new n (n::l) = first_new (S n) l). apply first_new_eq.
      rewrite H.
      assert (n < S n). lia.
      assert (S n <= first_new (S n) l). apply IHl.
      lia.
    + (* Case: a <> n *)
      apply (@first_new_not_eq l a n) in n0. rewrite n0.
      apply IHl.
Qed. 

Theorem first_new_lt {l x n} :
  sorted (x :: l) -> n < x -> first_new n (x::l) = n.
Proof. intros.
  induction l.
  - assert (x <> n). lia.
    apply (@first_new_not_eq [] x n) in H1.
    rewrite H1. unfold first_new. reflexivity.
  - assert (sorted (x :: l)). { apply sorted_surgery in H. assumption. }
    apply IHl in H1 as H2.
    assert (x <> n). lia.
    apply (@first_new_not_eq l x n) in H3 as H4.
    inversion H. clear H5 H8 H6.
    assert (a <> n). lia.
    apply (@first_new_not_eq l a n) in H5 as H6.
    assert (first_new n (x :: a :: l) = first_new n (a :: l)). {
      apply (@first_new_not_eq (a::l) x n). assumption.
    }
    rewrite H8. rewrite H6. rewrite <- H4. assumption.
Qed.

Lemma first_new_not_in_lt {l l0 a n} :
  l = a::l0 -> sorted (l) -> n < a -> ~In (first_new n l) l.
Proof. intros.
  assert (first_new n (a::l0) = n). {
    apply (@first_new_lt l0 a n). rewrite <- H. assumption. assumption.
  }
  rewrite H. rewrite H2. rewrite <- H. generalize dependent a.
  generalize dependent l0.
  induction H0.
  - intros; apply in_nil.
  - intros; apply not_in_cons. split. inversion H. lia. apply in_nil.
  - intros.
    assert (sorted (x :: y :: l)). { apply (sorted_cons x y l). assumption.
      assumption.
    }
    apply not_in_cons. split.
    + inversion H1. lia.
    + apply (IHsorted l y). 
      reflexivity. inversion H1. lia.
      apply first_new_lt. assumption. inversion H1. lia.
Qed.

Lemma first_new_not_in_gt {l x y n} : 
  forall (IHsorted : forall n : nat, ~ In (first_new n (y :: l)) (y :: l)),
  sorted (y :: l) -> x < n -> x < y -> ~ In (first_new n (x :: y :: l)) (x :: y :: l).
Proof.
  intros.
  apply not_in_cons. split.
  - assert(n <= first_new n (x :: y :: l)). { apply first_new_nondecreasing. }
    lia.
  - assert(x <> n). lia.
    apply (@first_new_not_eq (y::l) x n) in H2.
    rewrite H2. apply IHsorted.
Qed.
   
Theorem first_new_not_in {l n} :
  sorted l -> ~ In (first_new n l) l.
Proof.
  intros. generalize dependent n.
  induction H.
  - (* Base case: sorted_nil. *) simpl; auto.
  - (* Base case: sorted_1. *) intros. assert ({x = n} + {x <> n}). decide equality. destruct H.
   + (* If x = n *) rewrite e.
     assert (first_new n [n] = first_new (S n) []). apply first_new_eq.
     rewrite H. unfold first_new. 
     apply not_in_cons. simpl; auto.
   + (* If x <> n *)
     apply (@first_new_not_eq [] x n) in n0 as H.
     rewrite H. unfold first_new.
     apply not_in_cons. simpl; auto.
  - (* Inductive case (sorted_cons): x < y && sorted (y::l0) && l = x::y::l0 *)
    intros.
    assert ({x < n} + {x = n} + {n < x}). apply lt_eq_lt_dec. destruct H1. destruct s.
 -- (* x < n *)
    apply (@first_new_not_in_gt l x y n IHsorted). assumption.
    assert (x <> n). lia. assumption. assumption.
 -- (* x = n *) rewrite e.
     assert (first_new n (n :: y :: l) = first_new (S n) (y :: l)). apply first_new_eq.
     rewrite H1.
     apply not_in_cons.
     assert (S n <> n). lia.
     assert (S n <= first_new (S n) (y :: l)). apply first_new_nondecreasing.
     split. lia. apply IHsorted.
 -- (* x > n *)
    apply (@first_new_not_in_lt (x :: y :: l) (y :: l) x n).
    reflexivity. apply sorted_cons. assumption. assumption. assumption.
Qed.

Theorem insert_merge_list_fold_sorted : forall (A : Type) (f : A -> list nat) (l : list A) (init : list nat),
  sorted init -> sorted (List.fold_left (fun l' => fun (a : A) => insert_merge (f a) l') l init%list).
Proof.
  intros. generalize dependent init.
  induction l.
  - simpl; auto.
  - intros.
    assert((fold_left (fun (l' : list nat) (a0 : A) => insert_merge (f a0) l') (a :: l) init)
          = (fold_left (fun (l' : list nat) (a0 : A) => insert_merge (f a0) l') l (insert_merge (f a) init))). {
      simpl; auto.
    } rewrite H0.
    assert (sorted (insert_merge (f a) init)). {
      apply insert_merge_sorted2. assumption.
    }
    apply IHl in H1 as IH. apply IH.
Qed.

Theorem insert_merge_list_fold_sorted2 : forall (A : Type) (f : A -> list nat -> list nat) (l : list A) (init : list nat),
  sorted init -> sorted (List.fold_left (fun l' => fun (a : A) => insert_merge (f a l') l') l init%list).
Proof.
  intros. generalize dependent init.
  induction l.
  - simpl; auto.
  - intros.
    assert((fold_left (fun (l' : list nat) (a0 : A) => insert_merge (f a0 l') l') (a :: l) init)
          = (fold_left (fun (l' : list nat) (a0 : A) => insert_merge (f a0 l') l') l (insert_merge (f a init) init))). {
      simpl; auto.
    } rewrite H0.
    assert (sorted (insert_merge (f a init) init)). {
      apply insert_merge_sorted2. assumption.
    }
    apply IHl in H1 as IH. apply IH.
Qed.

Require Export Coq.Vectors.VectorSpec.

Theorem insert_merge_vector_fold_sorted {n} : forall (A : Type) (f : A -> list nat) (v : Vector.t A n) (init : list nat),
  sorted init -> sorted (Vector.fold_left (fun l' => fun (a : A) => insert_merge (f a) l') init v).
Proof.
  intros.
  assert(Vector.fold_left (fun l' => fun (a : A) => insert_merge (f a) l') init v
          = List.fold_left (fun l' => fun (a : A) => insert_merge (f a) l') (Vector.to_list v) init).
  { apply to_list_fold_left. }
  rewrite H0.
  apply insert_merge_list_fold_sorted.
  assumption.
Qed.

Theorem insert_merge_vector_fold_sorted2 {n} : forall (A : Type) (f : A -> list nat -> list nat) (v : Vector.t A n) (init : list nat),
  sorted init -> sorted (Vector.fold_left (fun l' => fun (a : A) => insert_merge (f a l') l') init v).
Proof.
  intros.
  assert(Vector.fold_left (fun l' => fun (a : A) => insert_merge (f a l') l') init v
          = List.fold_left (fun l' => fun (a : A) => insert_merge (f a l') l') (Vector.to_list v) init).
  { apply to_list_fold_left. }
  rewrite H0.
  apply insert_merge_list_fold_sorted2.
  assumption.
Qed.
  

Require Import Nat.
Require Import Coq.Arith.PeanoNat.

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

(*
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
*)

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
     assert (S m <= n \/ m = n). { apply le_le_S_eq in H. assumption. }
     destruct H2.
 +++ (* S m <= n *)
     rewrite H0. rewrite H1. apply IHl. intuition.
 +++ rewrite H2. reflexivity.
 ++ assert (first_new m (a :: l) = first_new m l). { apply (@first_new_distinct l a m); intuition. }
    rewrite H1; rewrite H0. apply IHl. assumption.
Qed.


(** * Segments -- range of integers 
At present, it seems like I will need to use a consecutive,
finite sequence of natural numbers. I defined it as a 
fixpoint, then proved a number of useful theorems about it.
*)
Fixpoint nat_range_list (n : nat) : list nat :=
match n with
| 0 => []%list
| S n' => ((nat_range_list n') ++ [n'])%list
end.

Lemma test_works2 :
  [0;1;2]%list = nat_range_list 3.
Proof. unfold nat_range_list.
  simpl; auto.
Qed.

Lemma nat_range_list_ind :
  forall (n : nat), 
  nat_range_list (S n) = ((nat_range_list n) ++ [n])%list.
Proof.
  intros. induction n.
  - unfold nat_range_list; simpl; auto.
  - unfold nat_range_list; simpl; auto.
Qed.

Require Import Lia.

Theorem nat_range_list_length :
  forall (n : nat), length (nat_range_list n) = n.
Proof.
  intros. induction n.
  - unfold nat_range_list; simpl; auto.
  - assert (nat_range_list (S n) = ((nat_range_list n) ++ [n])%list). {
      apply nat_range_list_ind.
    }
    rewrite H. 
    assert (length (nat_range_list n ++ [n]) = (length (nat_range_list n)) + (length [n]%list)). {
      apply List.app_length.
    } 
    rewrite H0. rewrite IHn. unfold length. lia.
Qed.

Lemma nth_cons :
  forall {A} (n : nat) (l : list A) (a default : A),
  nth (S n) (a::l) default = nth n l default.
Proof. intros.
  induction l.
  - unfold nth; simpl; auto.
  - unfold nth; simpl; auto.
Qed.

Lemma last_nth :
  forall {A} (n n' : nat) (l : list A) (default : A),
  S n' = n -> n = length l -> List.nth n' l default = List.last l default.
Proof.
  intros. generalize dependent n'. generalize dependent n. induction l.
  - intros. unfold length in H0. rewrite H0 in H. contradict H. unfold length; simpl; auto.
  - intros. destruct l.
  + unfold length in H0. rewrite H0 in H.
    assert (n' = 0). lia.
    rewrite H1. unfold nth; unfold last; simpl; auto.
  + set (n'' := length l).
    assert (S n'' = length (a0 :: l)). { unfold length; simpl; auto; lia. }
    assert (S (S n'') = length (a :: a0 :: l)). { unfold length; simpl; auto; lia. }
    
    assert (S (S n'') = n). { lia. }
    assert (S n'' = n'). { lia. }
    assert (n' = length (a0 :: l)). lia.
    rewrite <- H4.
    assert(last (a :: a0 :: l) default = last (a0 :: l) default). {
      simpl; auto. 
    }
    rewrite H6.
    assert (nth (S n'') (a :: a0 :: l) default = nth n'' (a0 :: l) default). {
      simpl; auto.
    }
    rewrite H7.
    apply (IHl n'). assumption. assumption.
Qed.

Lemma nat_range_list_incl_end :
  forall (n : nat),
  List.incl (nat_range_list n) (nat_range_list (S n)).
Proof.
  intros.
  induction n.
  - unfold nat_range_list; simpl; auto. unfold incl; simpl; auto.
  - set (m := S n).
    assert (nat_range_list m = (nat_range_list n ++ [n])%list). {
      unfold nat_range_list; unfold m; simpl; auto.
    }
    assert (nat_range_list (S m) = (nat_range_list m ++ [m])%list). {
      unfold nat_range_list; unfold m; simpl; auto.
    }
    assert (nat_range_list (S m) = (nat_range_list n ++ [n; m])%list). {
      rewrite H0.
      rewrite H. symmetry. apply (List.app_assoc (nat_range_list n) ([n]%list) ([m]%list)).
    }
    rewrite H1. rewrite H.
    assert (incl [n]%list [n; m]%list). { unfold incl; simpl; auto.
      intros. destruct H2. left; simpl; auto. simpl; auto.
    }
    apply List.incl_app_app; simpl; auto.
    apply List.incl_refl.
Qed.

Theorem nat_range_list_incl :
  forall (m n : nat),
  m < n -> List.incl (nat_range_list m) (nat_range_list n).
Proof.
  intros. generalize dependent m.
  induction n.
  - intros. contradict H; lia.
  - intros. 
    assert (incl (nat_range_list n) (nat_range_list (S n))). {
      apply nat_range_list_incl_end.
    }
    assert ({m = n} + {m <> n}). decide equality.
    destruct H1.
  + rewrite e. assumption.
  + assert (m < n). { lia. }
    assert (incl (nat_range_list m) (nat_range_list n)). {
      apply IHn. assumption.
    }
    apply (@incl_tran nat (nat_range_list m) (nat_range_list n) (nat_range_list (S n))).
    assumption.
    assumption.
Qed.

Theorem nat_range_list_firstn :
  forall (m n : nat),
  m < n -> List.firstn m (nat_range_list n) = nat_range_list m.
Proof.
  intros. generalize dependent m.
  induction n.
  - intros. contradict H; lia.
  - intros. 
    assert({m = n} + {m <> n}). decide equality.
    assert(nat_range_list (S n) = (nat_range_list n ++ [n])%list). {
      unfold nat_range_list; simpl; auto.
    }
    destruct H0.
  + rewrite e. rewrite H1.
    set (l := nat_range_list n).
    assert (n = length l). { symmetry. apply nat_range_list_length. }
    assert (firstn (length l + 0) (l ++ [n])%list = l). {
      assert (firstn 0 [n]%list = List.nil). { simpl; auto. }
      assert (l = (l ++ (firstn 0 [n]%list))%list). { simpl; auto. symmetry. apply app_nil_r. }
      set (l2 := firstn (length l + 0) (l ++ [n])%list).
      rewrite H3. unfold l2.
      apply (@firstn_app_2 nat 0 l ([n])%list).
    }
    assert (length l + 0 = length l). { simpl; auto. }
    rewrite H3 in H2. rewrite <- H0 in H2. assumption.
  + assert (m < n) as IH. lia.
    apply IHn in IH.
    destruct m as [| m'].
 ++ (* m = 0 *)
    apply firstn_O.
 ++ (* m = S m' *)
    set (l := skipn (S m') (nat_range_list n)).
    assert (nat_range_list n = (nat_range_list (S m') ++ l)%list). {
      symmetry. rewrite <- IH. unfold l.
      apply (@firstn_skipn nat (S m') (nat_range_list n)).
    }
    assert (nat_range_list (S n) = ((nat_range_list (S m') ++ l) ++ [n])%list). {
      rewrite <- H0. rewrite H1. reflexivity.
    }
    rewrite H2.
    assert (((nat_range_list (S m') ++ l) ++ [n])%list 
            = (nat_range_list (S m') ++ (l ++ [n]))%list). {
      symmetry. apply app_assoc.
    }
    rewrite H3.
    set (l' := (l ++ [n])%list).
    assert (length (nat_range_list (S m')) = S m'). {
      apply nat_range_list_length.
    }
    assert (firstn (length (nat_range_list (S m')) + 0) (nat_range_list (S m') ++ l')%list =
            ((nat_range_list (S m')) ++ firstn 0 l')%list). {
      apply (@firstn_app_2 nat 0).
    }
    rewrite H4 in H5.
    assert ((nat_range_list (S m') ++ firstn 0 l')%list = nat_range_list (S m')). {
      assert (firstn 0 l' = []%list). simpl; auto.
      rewrite H6.
      apply app_nil_r.
    } rewrite H6 in H5.
    assert (firstn (S m' + 0)
       (nat_range_list (S m') ++ l') = firstn (S m')
       (nat_range_list (S m') ++ l')). { assert(S m' + 0 = S m').
       simpl; auto. rewrite H7. reflexivity.
    }
    rewrite H7 in H5. assumption.
Qed.

Theorem nat_range_list_entry :
  forall (k n : nat),
  k < n -> nth k (nat_range_list n) (S n) = k.
Proof.
  intros. generalize dependent k.
  induction n as [|n'].
  - intros. contradict H. lia.
  - intros. set (n := S n').
    assert (nat_range_list n = (nat_range_list n' ++ [n'])%list). {
      simpl; auto.
    }
    assert ({k = n'} + {k <> n'}). decide equality.
    destruct H1.
  + (* Case: k = n' *)
    assert (nth k (nat_range_list (S k)) (S (S k)) = last (nat_range_list (S k)) (S (S k))). {
      apply (@last_nth nat n k). lia.
      rewrite e. unfold n. symmetry.
      apply nat_range_list_length.
    } unfold n. rewrite <- e.
    rewrite H1.
    unfold n in H0.
    rewrite <- e in H0.
    rewrite H0.
    apply last_last.
  + assert (k < n'). lia.
    assert (length (nat_range_list n') = n'). {
      apply nat_range_list_length.
    }
    apply IHn' in H1 as IH.
    rewrite H0.
    assert (nth k (nat_range_list n' ++ [n'])%list (S n') = nth k (nat_range_list n') (S n')). {
      apply app_nth1 with (d := (S n')). rewrite H2. assumption.
    }
    assert (nth k (nat_range_list n' ++ [n']) (S n) = nth k (nat_range_list n' ++ [n']) (S n')). {
      apply nth_indep.
      assert (length (nat_range_list n') + 1 = length (nat_range_list n' ++ [n'])). {
        symmetry. apply app_length.
      }
      lia.
    } rewrite H4.
    rewrite H3. rewrite IH. reflexivity.
Qed.

Definition rev_nat_range_list (n : nat) : list nat :=
  List.rev (nat_range_list n).

Example ex_rev_nat_range_list_4 :
  rev_nat_range_list 4 = [3;2;1;0]%list.
Proof.
  simpl; auto.
Qed.

Theorem rev_nat_range_list_length : forall (n : nat),
  length (rev_nat_range_list n) = n.
Proof.
  intros.
  unfold rev_nat_range_list.
  assert (length (rev (nat_range_list n)) = length (nat_range_list n)). {
    apply (rev_length (nat_range_list n)).
  }
  rewrite H.
  apply nat_range_list_length.
Qed.
(* 
  Lemma rev_nth : forall l d n, n < length l ->
    nth n (rev l) d = nth (length l - S n) l d.
nat_range_list_entry
     : forall k n : nat,
       k < n -> nth k (nat_range_list n) (S n) = k
nth k (rev_nat_range_list n) d
= nth (n - k) (nat_range_list n) d
= (n - k)
*)

Theorem rev_nat_range_list_entry :
  forall (k n : nat),
  k < n -> nth k (rev_nat_range_list n) (S n) = (n - S k).
Proof.
  intros. unfold rev_nat_range_list.
  assert (length (nat_range_list n) = n). { apply nat_range_list_length. }
  assert (nth k (rev (nat_range_list n)) (S n)
          = nth (length (nat_range_list n) - S k) (nat_range_list n) (S n)). {
    apply (@rev_nth nat (nat_range_list n) (S n) k).
    rewrite H0. assumption.
  } rewrite H0 in H1.
  assert (nth (n - S k) (nat_range_list n) (S n) = (n - S k)). {
    apply nat_range_list_entry. lia.
  } rewrite H1. rewrite H2.
  reflexivity.
Qed.

(* Coq thinks [Vector.of_list (rev_nat_range_list n)] is a [Vector]
of size [length (rev_nat_range_list n)]. So we have to explicitly
spell it out for Coq. *)


Require Fin List.
Require Import VectorDef PeanoNat Eqdep_dec.
Import VectorNotations EqNotations.
Fixpoint rev_nat_range_vector (n : nat) : Vector.t nat n :=
match n with
| 0 => []
| S n' => (n') :: (rev_nat_range_vector n')
end.

Lemma rev_nat_range_vector_last :
  forall (n' : nat),
  Vector.last (rev_nat_range_vector (S n')) = 0.
Proof.
  intros. induction n'.
  - unfold rev_nat_range_vector. simpl; auto.
  - assert((rev_nat_range_vector (S (S n')))
            = Vector.cons nat (S n') (S n') (rev_nat_range_vector (S n'))). {
      simpl; auto.
    }
    rewrite H.
    assert (Vector.last (Vector.cons nat (S n') (S n') (rev_nat_range_vector (S n')))
            = Vector.last (rev_nat_range_vector (S n'))). {
      simpl; auto.
    }
    rewrite H0. apply IHn'.
Qed.

Example rev_nat_range_vector_0 :
  rev_nat_range_vector 0 = [].
Proof. simpl; auto. Qed.

Example rev_nat_range_vector_1 :
  rev_nat_range_vector 1 = [0].
Proof. simpl; auto. Qed.

Example rev_nat_range_vector_2 :
  rev_nat_range_vector 2 = [1;0].
Proof. simpl; auto. Qed.


Lemma rev_nat_range_vector_hd :
  forall (n' : nat),
  Vector.hd (rev_nat_range_vector (S n')) = n'.
Proof.
  intros. unfold rev_nat_range_vector. simpl; auto.
Qed.

Lemma rev_nat_range_vector_tl :
  forall (n' : nat),
  Vector.tl (rev_nat_range_vector (S (S n'))) = rev_nat_range_vector (S n').
Proof.
  intros. unfold rev_nat_range_vector. simpl; auto.
Qed.

(* These next two lemmas are true, but I am too stupid to understand
Coq's inner workings to prove them. *)
Lemma rev_nat_range_vector_entry_base_case :
  forall (k : nat) (H : k < 1),
  nth_order (rev_nat_range_vector 1) H = 1 - S k.
Admitted.

Lemma rev_nat_range_vector_entry_inductive_case_subtlety :
  forall (k n : nat) (H : k < S (S n)) (e : k = S n) (H0 : S n < S (S n)),
  nth_order (rev_nat_range_vector (S (S n))) H 
  = nth_order (rev_nat_range_vector (S (S n))) H0.
Admitted.

Theorem rev_nat_range_vector_entry :
  forall (k n : nat) (H : k < S n),
  nth_order (rev_nat_range_vector (S n)) H = (S n - S k).
Proof.
  intros.
  generalize dependent k. induction n.
  - intros. apply rev_nat_range_vector_entry_base_case.
  - intros. assert({k = S n} + {k <> S n}). decide equality. destruct H0.
    + assert (S n < S (S n)) as H0. lia.
      assert (nth_order (rev_nat_range_vector (S (S n))) H 
              = nth_order (rev_nat_range_vector (S (S n))) H0). {
        apply rev_nat_range_vector_entry_inductive_case_subtlety. assumption.
      }
      rewrite H1. rewrite e.
      assert (last (rev_nat_range_vector (S (S n))) = 0). {
        apply rev_nat_range_vector_last.
      }
      assert (nth_order (rev_nat_range_vector (S (S n))) H0 = last (rev_nat_range_vector (S (S n)))). {
        apply (@nth_order_last nat (S n) (rev_nat_range_vector (S (S n)))).
      }
      rewrite H3; rewrite H2; lia.
    + destruct k as [|k'].
  ++ (* k = 0 *)
     apply nth_order_hd.
  ++ (* k = S k' *)
     set (k := S k'). assert (k' < S n). lia.
     assert (nth_order (rev_nat_range_vector (S n)) H0 = S n - S k') as IH. {
        apply (IHn k' H0).
     }
     assert (S (S n) - S k = S n - S k'). lia. rewrite H1.
     rewrite <- IH. symmetry.
     assert (Vector.tl (rev_nat_range_vector (S (S n))) = rev_nat_range_vector (S n)). {
       apply rev_nat_range_vector_tl.
     }
     rewrite <- H2.
     apply (@nth_order_tl nat (S n) k' (rev_nat_range_vector (S (S n)))).
Qed.
