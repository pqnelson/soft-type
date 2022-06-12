Require Import String.
Require Import Lia.
Require Import List.
Require Import Nat.
Require Import Coq.Vectors.Vector.
Require Import Coq.Vectors.VectorEq.
Require Import Coq.Arith.Bool_nat.
Require Export Coq.Arith.Compare_dec.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.FunctionalExtensionality.
Require Export RelationClasses.
Require Export Morphisms.
Require Import Program.
From ST Require Import EVarsScratchwork.
From ST Require Import Vector.
From ST Require Import Logic.V.
Import ListNotations.
Import VectorNotations.
Open Scope string_scope.
(** ** Terms

A [Term] is either a variable, or an n-ary function. Constants are just nullary 
functions. We do carve out [EConst] for existential constants, to make
logic easier later on.
*)

Unset Elimination Schemes.
Inductive Term : Type :=
| Var : V -> Term
| EConst : nat -> Term
| Fun {n : nat} : name -> Vector.t Term n -> Term.

Definition Term_ind (P : Term -> Prop)
       (HVar : forall v : V, P (Var v))
       (HConst : forall n : nat, P (EConst n))
       (HFun : forall (n : nat) (n0 : name) (t : t Term n),
         Vector.Forall P t -> P (Fun n0 t))
       (* ^ extra hypothesis *)
  : forall t : Term, P t.
Proof.
  fix SELF 1; intros [ | | n m t].
  - apply HVar.
  - apply HConst.
  - apply HFun.
    induction t as [ | ? ? ? IH ]; constructor.
    + apply SELF.
    + apply IH.
Qed.

  Definition Term_rect := 
fun (P : Term -> Type)
  (f : forall v : V, P (Var v))
  (f0 : forall n : nat, P (EConst n))
  (f1 : forall (n : nat) (n0 : name)
          (t : t Term n), P (@Fun n n0 t))
  (t : Term) =>
match t as t0 return (P t0) with
| Var v => f v
| EConst n => f0 n
| @Fun n n0 t0 => f1 n n0 t0
end.
(*
  Section Term_rect.
    Variable P : Term -> Type.
    Variable P_vector : forall n, Vector.t Term n -> Type.
    Hypothesis P_nil : P_vector 0 []%vector.
    Hypothesis P_cons : forall {n} t l, P t -> P_vector n l -> P_vector (S n) (t :: l)%vector.
    Hypothesis P_Var : forall a, P (Var a).
    Hypothesis P_EConst : forall n, P (EConst n).
    Hypothesis P_Fun : forall {n} nm l, P_vector n l -> P (@Fun n nm l).
Print list_rect.
    Fixpoint Term_rect (t : Term) : P t :=
      let fix go_vector {n} (l : Vector.t Term n) : P_vector n l :=
          match l with
          | []%vector => P_nil
          | (t :: l)%vector => P_cons t l (Term_rect t) (go_vector l) (* (Term_rect t) (go_vector l) *)
          end
      in
      match t with
      | Var x => P_Var x
      | EConst n => P_EConst n
      | Fun nm args => P_Fun nm args (go_vector args)
      end.
  End Term_rect.
*)
(*
  Section Term_rect.
    Variable P : Term -> Type.
    Variable P_vector : forall n, Vector.t Term n -> Type.
    Hypothesis P_nil : P_vector 0 []%vector.
    Hypothesis P_cons : forall {n} t l, P t -> P_vector n l -> P_vector (S n) (t :: l)%vector.
    Hypothesis P_Var : forall a, P (Var a).
    Hypothesis P_EConst : forall n, P (EConst n).
    Hypothesis P_Fun : forall {n} nm l, P_vector n l -> P (@Fun n nm l).
Print list_rect.
    Fixpoint Term_rect (t : Term) : P t :=
      let fix go_vector {n} (l : Vector.t Term n) : P_vector n l :=
          match l with
          | []%vector => P_nil
          | (t :: l)%vector => P_cons t l (Term_rect t) (go_vector l) (* (Term_rect t) (go_vector l) *)
          end
      in
      match t with
      | Var x => P_Var x
      | EConst n => P_EConst n
      | Fun nm args => P_Fun nm args (go_vector args)
      end.
  End Term_rect.
*)
Set Elimination Schemes.

Definition constant (c : name) : Term :=
@Fun 0 c [].

Fixpoint term_eqb (t1 t2 : Term) : bool :=
match t1,t2 with
| Var x1, Var x2 => eqb x1 x2
| EConst n1, EConst n2 => eqb n1 n2
| @Fun n1 s1 args1, @Fun n2 s2 args2 => 
  (* eqb n1 n2 && eqb s1 s2 && (Vector.eqb Term term_eqb args1 args2) *)
  let fix args_eqb {n1 n2} (ar1 : Vector.t Term n1) (ar2 : Vector.t Term n2) : bool :=
      match ar1,ar2 with
      | Vector.nil _, Vector.nil _ => true
      | Vector.cons _ h1 k1 t1,  Vector.cons _ h2 k2 t2 => (andb (term_eqb h1 h2) (args_eqb t1 t2))
      | _, _ => false
      end
  in (eqb n1 n2) && (eqb s1 s2) && (args_eqb args1 args2) 
| _, _ => false
end.

Fixpoint args_eqb {n1 n2} (ar1 : Vector.t Term n1) (ar2 : Vector.t Term n2) : bool :=
match ar1,ar2 with
| Vector.nil _, Vector.nil _ => true
| Vector.cons _ h1 k1 t1,  Vector.cons _ h2 k2 t2 => (andb (term_eqb h1 h2) (args_eqb t1 t2))
| _, _ => false
end.

Global Instance EqTerm : Eq Term := {
  eqb := term_eqb
}.

(*
Require Import Coq.Vectors.VectorSpec.
Lemma args_eqb_length (n1 n2 : nat) (args1 : Vector.t Term n1) (args2 : Vector.t Term n2) :
  n1 <> n2 -> args_eqb (args1) (args2) = false.
Proof.
  intros. apply Coq.Arith.Compare_dec.not_eq in H.
  destruct H.
  - set (n := min n1 n2).
    assert (n = n1). lia. 
    set (k := n2 - n).
    assert (n2 = n + k). lia.
    revert args2. rewrite H1.
    revert args1. assert(n + 0 = n1). lia. rewrite <- H2.
    intros.
    set (vs := (@Vector.splitat Term n k args2)).
    set (us := (@Vector.splitat Term n 0 args1)).
    destruct vs as [ls2 tls2]. destruct us as [ls1 tls1].
    assert ({args_eqb ls1 ls2 = true} + {args_eqb ls1 ls2 <> true}). { decide equality. }
    destruct H3.
    + 
    apply min_l in H as H1.
    Vector.splitat(n, 
*)

Lemma args_eqb_ind (n : nat) (h1 h2 : Term) (args1 args2 : Vector.t Term n) :
  args_eqb (h1::args1) (h2::args2)
  = (eqb h1 h2) && (args_eqb args1 args2).
Proof.
  intros. unfold args_eqb; unfold EqTerm; unfold term_eqb. simpl; auto.
Qed.

(*
Require Import Coq.Arith.EqNat.
Lemma args_eqb_ind2 (n1 n2 : nat) (h1 h2 : Term) (args1 : Vector.t Term n1) (args2 : Vector.t Term n2) :
  args_eqb (h1::args1) (h2::args2)
  = (eqb n1 n2) && (eqb h1 h2) && (args_eqb args1 args2).
Proof.
  intros. assert ({n1 = n2} + {n1 <> n2}). decide equality. destruct H.
  - revert args1; revert args2. rewrite e. intros.
    assert (args_eqb (h1::args1) (h2::args2) = (eqb h1 h2) && (args_eqb args1 args2)). {
      apply args_eqb_ind.
    }
    assert (eqb n2 n2 = true). apply Nat.eqb_refl. rewrite H0.
    rewrite H. unfold andb; simpl; auto.
  - 
    
  induction args1.
  - destruct args2.
  + unfold args_eqb; unfold EqTerm; unfold term_eqb. simpl; auto.
  + simpl; auto. unfold args_eqb. apply andb_false_r.
  - induction args2.
  + simpl; auto. unfold args_eqb. apply andb_false_r.
  +
    assert (eqb (S n) (S n0) && eqb h1 h2 && args_eqb (h :: args1) (h0 :: args2)
            
   reflexivity. simpl; auto.
    unfold args_eqb; unfold EqTerm; unfold term_eqb. simpl; auto.
Qed.
*)
Lemma fun_eqb (n : nat) (s1 s2 : name) (args1 args2 : Vector.t Term n) :
  eqb (Fun s1 args1) (Fun s2 args2) =
  (eqb n n) && (eqb s1 s2) && (args_eqb args1 args2).
Proof.
  unfold eqb; unfold EqTerm; unfold term_eqb.
  unfold andb. simpl; auto.
Qed.

Lemma fun_eqb2 (n1 n2 : nat) (s1 s2 : name) (args1 : Vector.t Term n1) (args2 : Vector.t Term n2) :
  eqb (Fun s1 args1) (Fun s2 args2) =
  (eqb n1 n2) && (eqb s1 s2) && (args_eqb args1 args2).
Proof.
  unfold eqb; unfold EqTerm; unfold term_eqb.
  unfold andb. simpl; auto.
Qed.

Lemma constant_eqb_refl (s : name) : eqb (Fun s []) (Fun s []) = true.
Proof.
  intros.
  assert ((eqb s s) = true). apply String.eqb_refl.
  assert ((eqb 0 0) = true). unfold eqb; apply Nat.eqb_refl.
  unfold eqb; unfold EqTerm; unfold term_eqb.
  rewrite H; rewrite H0. unfold andb. reflexivity.
Qed.

Lemma fun_eqb_step (n : nat) (n0 : name) (t : Vector.t Term n) (h : Term) 
  (IH : Forall (fun t : Term => eqb t t = true) t ->
        (forall a : Term, VectorDef.In a t -> (fun t : Term => eqb t t = true) a) ->
        eqb n n = true -> eqb (Fun n0 t) (Fun n0 t) = true) :
  Forall (fun t : Term => eqb t t = true) (h :: t) -> eqb (Fun n0 (h :: t)) (Fun n0 (h :: t)) = true.
Proof.
  intros. set (P := (fun t : Term => eqb t t = true)). fold P in H.
  assert (forall a : Term, VectorDef.In a (h :: t) -> P a). {
    apply (Vector.Forall_forall Term P (S n) (h::t)).
    assumption.
  }
  assert (Forall P (h :: t)) as IH1. assumption.
  apply Vector_Forall_cons_iff in IH1. destruct IH1.
  assert (forall a : Term, VectorDef.In a t -> P a). {
    apply (Vector.Forall_forall Term P n t).
    assumption.
  }
  fold P in IH.
  assert (eqb (Fun n0 t) (Fun n0 t) = true). {
    apply IH. assumption. assumption. apply Nat.eqb_refl.
  }
  unfold P in H1.
  
  assert (eqb (@Fun (S n) n0 (h :: t)) (@Fun (S n) n0 (h :: t)) = 
          ((eqb (S n) (S n)) && (eqb n0 n0) &&
            (args_eqb (h :: t) (h :: t)))). {
    apply fun_eqb.
  }
  rewrite H5. 
  assert (eqb (S n) (S n) = true). apply Nat.eqb_refl.
  rewrite H6.
  assert (eqb n0 n0 = true). apply String.eqb_refl.
  rewrite H7. unfold andb.
  
  assert (args_eqb (h :: t) (h :: t) = 
          eqb h h && args_eqb t t). {
    apply args_eqb_ind.
  }
  rewrite H8. rewrite H1. unfold andb.
  
  assert (eqb (@Fun n n0 t) (@Fun n n0 t) = 
          ((eqb n n) && (eqb n0 n0) &&
            (args_eqb t t))). {
    apply fun_eqb.
  }
  assert (eqb n n = true). apply Nat.eqb_refl.
  rewrite H7 in H9. rewrite H10 in H9. unfold andb in H9.
  rewrite H9 in H4. assumption.
Qed.

Theorem term_eqb_refl (t : Term) : eqb t t = true.
Proof.
  induction t.
  - unfold eqb; apply V_eqb_refl.
  - unfold eqb; apply Nat.eqb_refl.
  - set (P := (fun t : Term => eqb t t = true)).
    fold P in H. Check Vector.Forall_forall.
    assert (forall a : Term, VectorDef.In a t -> P a). {
      apply (Vector.Forall_forall Term P n t). assumption.
    }
    assert ((eqb n n) = true). unfold eqb; apply Nat.eqb_refl.
    assert ((eqb n0 n0) = true). apply String.eqb_refl.
    induction t.
    apply (constant_eqb_refl n0).
    apply fun_eqb_step. assumption. assumption.
Qed.

(*
Theorem term_eqb_eq (t1 t2 : Term) : eqb t1 t2 = true -> t1 = t2.
Proof.
  intros. induction t1.
  - unfold eqb in H; unfold EqTerm in H; unfold term_eqb in H. destruct t2.
  + apply V_eqb_eq in H. rewrite H; reflexivity.
  + discriminate.
  + discriminate.
  - unfold eqb in H; unfold EqTerm in H; unfold term_eqb in H. destruct t2. discriminate.
    apply Nat.eqb_eq in H. rewrite H; reflexivity. discriminate.
  - destruct t2. discriminate. discriminate.
    assert (eqb (Fun n0 t) (Fun n2 t0)
            = eqb n n1 && eqb n0 n2 && args_eqb t t0). {
      apply (fun_eqb2 n n1 n0 n2 t t0).
    }
    rewrite H in H1.
    assert (eqb n n1 && eqb n0 n2 = true /\ args_eqb t t0 = true). apply andb_prop. assumption.
    destruct H2.
    assert (eqb n n1 = true /\ eqb n0 n2 = true). apply andb_prop; assumption.
    destruct H4.
    apply String.eqb_eq in H5. rewrite H5.
    apply Nat.eqb_eq in H4. rename t into args1. rename t0 into args2.
    rename n2 into nm.
    induction args1.
    + destruct args2. reflexivity. contradict H3. unfold args_eqb. discriminate.
    + destruct args2. contradict H3; unfold args_eqb; discriminate.
      Check args_eqb_ind.
      
      apply (args_eqb_ind n h h0 args1 args2) in H3 as H6.
    assert (eqb n n1 = true). {
      destruct H. unfold andb.
    }
  + assert ({v = v0} + {v <> v0}). { apply V_eq_dec. } destruct H0.
    rewrite e; reflexivity.
    contradiction.
   destruct v; destruct v0. unfold eqb in H; unfold VEq in H. inversion H.
    assert (Bool.reflect (n = n0) (n =? n0)). { apply eqb_spec. }
    simpl; auto.
    Compute (eqb_spec n n0).
    apply eqb_spec in H1.
     decide equality.
   simpl; auto. unfold eqb in H; unfold EqTerm in H; unfold term_eqb in H. bdestruct (eqb v v0).
  ++ 
Qed.

Lemma fun_eqb (n : nat) (s1 s2 : name) (args1 : Vector.t Term n) (args2 : Vector.t Term n) :
  eqb (@Fun n s1 args1) (@Fun n s2 args2) = true <-> (s1 = s2 /\ args1 = args2).
Proof.
  intros.
  split.
  - intros. inversion H.
    assert ((s1 =? s2) = true). {
      unfold andb in H1; simpl; auto.
      assert ((n =? n)%nat = true). apply Nat.eqb_refl.
      rewrite H0 in H1.
      destruct (s1 =? s2). reflexivity. discriminate.
    }
    assert ((n =? n)%nat = true). apply Nat.eqb_refl.
    rewrite H0 in H1. rewrite H2 in H1. simpl in H1.
    apply String.eqb_eq in H0.
    split. assumption.
    Check Vector.eqb_eq.
    apply (Vector.eqb_eq Term term_eqb in H1. simpl; auto.

Theorem term_dec (x y : Term) : {x = y} + {x <> y}.
Proof.
  intros. destruct (eqb x y) eqn:H.
  - left. now apply eqb_eq.
  decide equality. apply string_dec. 
  decide equality.
Qed.
*)

Lemma eq_dec : forall (x y : Term), {x = y} + {x <> y}. Admitted.

(** *** Substitution Type Class

We will want to substitute a term for a variable frequently in many syntactic
constructs. Towards that end, we have a [Subst] type class.

We may also want to do this with a vector of variables and a vector of terms,
both vectors of the same length. Fortunately, we only have to define this
"many-folded substitution" function only once.
*)
Class Subst A : Type := 
{
  subst : V -> Term -> A -> A
}.

Fixpoint subst_many {n} {A : Type} `{Subst A} (vars : Vector.t V n) (terms : Vector.t Term n) (a : A) : A :=
match vars, terms with
| x::xs, t::tms => subst_many xs (Vector.tl terms) (subst x t a)
| _, _ => a
end.

(* HACK: since Coq cannot handle recursive typeclasses, we isolate the only
recursive substitution here.

See: https://stackoverflow.com/a/52349387 *)
Fixpoint tsubst (x : V) (t : Term) (e : Term) : Term :=
match e with
| Var y => if eqb x y then t else e
| @Fun n f args => @Fun n f (Vector.map (fun (a : Term) => tsubst x t a) args)
| EConst _ => e
end.

Global Instance substTerm : Subst Term :=
{
  subst (x : V) (t : Term) (e : Term) := tsubst x t e
}.

Compute (subst (BVar 1) (Fun "c" []) (Fun "f" [Var (BVar 1) ; Var (FVar "x")])).

Example term_subst_1 : subst (BVar 1) (Fun "c" []) (Fun "f" [Var (BVar 1) ; Var (FVar "x")])
= Fun "f" [(Fun "c" []) ; Var (FVar "x")].
Proof.
  trivial.
Qed.

Example term_subst_2 : subst (FVar "x") (Fun "c" []) (Fun "f" [Var (BVar 1) ; Var (FVar "x")])
= Fun "f" [Var (BVar 1) ; (Fun "c" [])].
Proof.
  trivial.
Qed.

Example term_subst_3 : subst (BVar 3) (Fun "c" []) (Fun "f" [Var (BVar 1) ; Var (FVar "x")])
= Fun "f" [Var (BVar 1) ; Var (FVar "x")].
Proof.
  trivial.
Qed.

Example term_subst_4 : subst (FVar "z") (Fun "c" []) (Fun "f" [Var (BVar 1) ; Var (FVar "x")])
= Fun "f" [Var (BVar 1) ; Var (FVar "x")].
Proof.
  trivial.
Qed.

Fixpoint term_map_var (f : V -> V) (t : Term) : Term :=
match t with
| Var x => Var (f x)
| EConst _ => t
| Fun nm args => Fun nm (Vector.map (fun (a : Term) => term_map_var f a) args)
end.

Lemma term_map_var_id : forall (t : Term),
  term_map_var id t = t.
Proof. intros. induction t.
 (* apply Term_ind_mut.  dependent inversion t.  (fun (args : TermArgs) => (List.map (term_m.  *)
  - simpl; auto.
  - simpl; auto.
  - rename t into args. 
    assert(forall (t : Term), Vector.In t args -> ((fun t : Term => term_map_var id t = t) t)). {
      apply Vector.Forall_forall. assumption.
    }
    assert (term_map_var id (Fun n0 args) = Fun n0 (Vector.map (fun (a : Term) => term_map_var id a) args)). {
      unfold term_map_var; simpl; auto.
    } rewrite H1.
    simpl in H0.
    assert (Vector.map (fun a : Term => term_map_var id a) args = args) as IH. {
      induction args.
      simpl; auto.
      assert (Vector.map (fun a : Term => term_map_var id a) (h :: args)
               = (term_map_var id h)::(Vector.map (fun a : Term => term_map_var id a) args)). {
        unfold Vector.map; simpl; auto.
      }
      rewrite H2.
      assert (term_map_var id h = h). {
        apply H0. apply In_cons_hd.
      }
      rewrite H3.
      assert (Vector.map (fun a : Term => term_map_var id a) args = args). { 
        apply IHargs. simpl; auto. inversion H.
        - apply Vector.Forall_forall.
          assert (forall a : Term, VectorDef.In a args -> VectorDef.In a (h :: args)). {
            intros. apply In_cons_tl. assumption.
          }
          intros.
          simpl; auto.
        - intros. assert (Vector.In t (h :: args)). apply In_cons_tl. assumption.
          apply H0 in H5. assumption.
        - simpl; auto.
      }
      rewrite H4. reflexivity.
    }
    rewrite IH. reflexivity.
Qed.


Fixpoint term_contains_bvar (index : nat) (t : Term) : Prop :=
match t with
| Var x => x = BVar index
| EConst _ => False
| @Fun n nm args => 
  let fix args_contain_bvar {k} (ar : Vector.t Term k) :=
     (match ar with
      | Vector.nil _ => False
      | Vector.cons _ h _ tl => term_contains_bvar index h \/ args_contain_bvar tl
      end)
  in args_contain_bvar args
end.

Class ContainsBVar A := {
  contains_bvar : nat -> A -> Prop
}.

Global Instance ContainsBVarTerm : ContainsBVar Term := {
  contains_bvar := term_contains_bvar
}.

Lemma term_subst_bvar_free : forall (n : nat) (t h : Term),
  ~(contains_bvar n h) -> (subst (BVar n) t h) = h.
Proof.
  unfold contains_bvar; unfold ContainsBVarTerm. intros. induction h as [x|k|k nm args].
  - destruct x.
  + simpl; auto.
  + unfold term_contains_bvar in H. simpl; auto.
    assert (n0 <> n). { simpl; auto. }
    bdestruct (Nat.eqb n n0).
 ++ contradict H1; simpl; auto.
 ++ reflexivity.
  - simpl; auto.
  - set (P := (fun h : Term => ~ term_contains_bvar n h -> subst (BVar n) t h = h)).
    fold P in H0.
    assert (forall (a : Term), VectorDef.In a args -> P a). {
      apply Vector.Forall_forall. assumption.
    }
    assert(subst (BVar n) t (Fun nm args) = Fun nm (Vector.map (fun a : Term => tsubst (BVar n) t a) args)). {
      simpl; auto.
    } rewrite H2.
    assert ((Vector.map (fun a : Term => tsubst (BVar n) t a) args) = args). {
      induction args.
      - simpl; auto.
      - assert(Vector.map (fun a : Term => tsubst (BVar n) t a) (h :: args)%vector
           = ((tsubst (BVar n) t h)::(Vector.map (fun a : Term => tsubst (BVar n) t a) args))%vector). {
          simpl; auto.
        }
        rewrite H3.
        assert(~ term_contains_bvar n (Fun nm (h :: args)%vector)
                    -> ~ term_contains_bvar n (Fun nm args)). {
          unfold term_contains_bvar; simpl; auto.
        }
        assert (Vector.Forall P args) as IH1. {
          apply Vector.Forall_forall. intros; apply H1;
            apply Vector.In_cons_tl; apply H5.
        }
        assert (~ term_contains_bvar n (Fun nm args)) as IH2. {
          apply H4. apply H.
        }
        assert (forall a : Term, VectorDef.In a args -> P a) as IH3. {
          intros. apply H1.  apply Vector.In_cons_tl; apply H5.
        }
        assert (subst (BVar n) t (Fun nm args) =
                Fun nm (Vector.map (fun a : Term => tsubst (BVar n) t a) args)). {
          unfold subst; simpl; auto.
        }
        assert((Vector.map (fun a : Term => tsubst (BVar n) t a) args) = args). {
          apply IHargs. simpl; auto. simpl; auto. simpl; auto. simpl; auto.
        } rewrite H6.
        clear IH1 IH2 IH3 H6.
        assert (tsubst (BVar n) t h = h). {
          assert (P h). {
            apply H1. apply Vector.In_cons_hd.
          }
          unfold P in H6. unfold subst in H6; unfold substTerm in H6.
          apply H6.
          assert (~ term_contains_bvar n (Fun nm (h :: args)%vector) -> ~ term_contains_bvar n h). {
            simpl; auto.
          }
          apply H7. apply H.
        }
        rewrite H6. reflexivity.
    }
    rewrite H3. reflexivity.
Qed.

(*
Definition tlift (c d : nat) (t : Term) := term_map_var (lift c d) t.

Fixpoint tlift (c d : nat) (t : Term) : Term :=
match t with
| Var y => Var (lift c d y)
| Fun f args => Fun f (Vector.map (fun (a : Term) => tlift c d a) args)
| EConst _ => t
end.
*)

Global Instance liftTerm : Lift Term :=
{
  lift (c d : nat) (t : Term) := term_map_var (lift c d) t
}.

Definition tlift := lift.
(* (c d : nat) (t : Term) := term_map_var (lift c d) t. *)

(** Lemma: [lift 0 0] is the identity transformation. *)
Lemma term_zero_lift_is_id : forall (t : Term), lift 0 0 t = id t.
Proof.
  intros. induction t.
  - assert (@lift V VLift 0 0 = id). apply zero_lift_is_id.
    unfold lift; unfold liftTerm. rewrite H. 
    assert (id (Var v) = Var v). { unfold id; simpl; auto. }
    assert (@lift V VLift 0 0 v = id v). {
      apply equal_f. trivial.
    }
    unfold term_map_var. unfold id. reflexivity.
  - unfold lift; unfold term_map_var; simpl; auto.
  - rename t into args.
    set (P := (fun t : Term => lift 0 0 t = id t)). fold P in H.
    assert (forall a : Term, VectorDef.In a args -> P a). {
      apply (Vector.Forall_forall Term P n args). assumption.
    }
    
    assert (lift 0 0 (Fun n0 args) = Fun n0 (Vector.map (fun a : Term => term_map_var (lift 0 0) a) args)). {
      unfold lift; unfold liftTerm; unfold term_map_var; simpl; auto.
    } rewrite H1. clear H1.
    assert (Vector.map (fun a : Term => term_map_var (lift 0 0) a) args = args). {
      admit.
    }
    rewrite H1. unfold id. reflexivity.
Admitted.

Definition term_is_fun (t : Term) : Prop :=
  match t with
  | Fun _ _ =>  True
  | _ => False
  end.

Class Fresh A : Type := {
  fresh : Term -> A -> Prop
}.

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

Global Instance FreshTerm : Fresh Term := {
  fresh := fresh_term
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
| Fun f args => Vector.fold_left (fun l' => fun (arg : Term) => insert_merge (list_evars_term arg l') l')
    l args
end.

Theorem list_evars_term_sorted : forall (t : Term) (l : list nat),
  sorted l -> sorted (list_evars_term t l).
Proof.
  intros.
  induction t.
  - assert (list_evars_term (Var v) l = l). { simpl; auto. }
    rewrite H0. assumption.
  - assert (list_evars_term (EConst n) l = insert n l). { simpl; auto. }
    rewrite H0. apply insert_preserves_sorted. assumption.
  - rename t into args.
    assert (list_evars_term (Fun n0 args) l = Vector.fold_left (fun l' => fun (arg : Term) => insert_merge (list_evars_term arg l') l')
    l args). { simpl; auto. }
    rewrite H1. apply insert_merge_vector_fold_sorted2.
    assumption.
Qed.

Global Instance EnumerateEVarsTerm : EnumerateEVars Term := {
  list_evars tm := list_evars_term tm []
}.

Theorem list_evers_term_sorted : forall (t : Term),
  sorted (list_evars t).
Proof. intros.
  unfold list_evars; unfold EnumerateEVarsTerm.
  assert (sorted []%list). { apply sorted_nil. }
  apply list_evars_term_sorted.
  assumption.
Qed.

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