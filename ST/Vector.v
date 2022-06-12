Require Import Lia.
Require Import Coq.Vectors.Vector.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.Classical_Prop.
Import VectorNotations.

(**
I found myself looking for analogous functions as what could be found in the
[List] standard library. I sadly found none. This forced me to implement
my own. And here they are!
*)

Section Vector.
Hint Constructors Vector.Exists : core.
Lemma Vector_Exists_cons {A} (P : A -> Prop) (x : A) {n} (l : Vector.t A n):
      Vector.Exists P (x::l)%vector <-> P x \/ Vector.Exists P l.
Proof.
  split.
  - intros. inversion H. apply inj_pair2_eq_dec in H3. left; assumption.
    decide equality. apply inj_pair2_eq_dec in H3. 2: decide equality. right. rewrite H3 in H2. assumption.
  - intros. destruct H. auto. auto.
Qed.

Lemma Vector_Exists_nil {A} (P : A -> Prop): Vector.Exists P []%vector <-> False.
Proof. split; inversion 1. Qed.

Lemma Vector_Forall_cons_iff  {A} (P : A -> Prop) : 
  forall (a:A) {n} (l : Vector.t A n), Vector.Forall P (a :: l)%vector <-> P a /\ Vector.Forall P l.
Proof.
intros. split. 
- intro H; inversion H.
  apply inj_pair2_eq_dec in H2. 2: decide equality. rewrite H2 in H4. split.
  apply H3. apply H4.
- constructor. destruct H. apply H.  destruct H. apply H0.
Qed.

Lemma vector_de_morgan {A : Type} {n} : forall  (P : A -> Prop) (l : Vector.t A n),
  ~(Vector.Exists P l) <-> Vector.Forall (fun a => ~(P a)) l.
Proof.
  intros; split.
  - intros. simpl; auto. induction l. apply Vector.Forall_nil.
    assert (Vector.Exists P (h :: l)%vector <-> P h \/ Vector.Exists P l). { apply Vector_Exists_cons. }
    rewrite H0 in H.
    apply Decidable.not_or in H.
    apply Vector_Forall_cons_iff. split. destruct H. assumption.
    destruct H. apply IHl in H1. assumption.
  - intros. induction l.
  + assert (Vector.Exists P []%vector <-> False). { apply Vector_Exists_nil. } rewrite H0. simpl; auto.
  + assert (Vector.Exists P (h :: l)%vector <-> P h \/ Vector.Exists P l). { apply Vector_Exists_cons. }
    rewrite H0.
    set (notP0 := (fun (a : A) => ~ P a)).
    apply (Vector_Forall_cons_iff) in H. destruct H. apply IHl in H1 as IH.
    apply and_not_or. split. assumption. assumption.
Qed.
End Vector.