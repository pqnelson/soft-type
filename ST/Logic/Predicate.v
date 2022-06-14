Require Import String.
Require Import Nat.
Require Import Coq.Vectors.Vector.
Require Import List.
Import ListNotations.
From ST Require Import Logic.V Logic.Term ST.SoftType.
From ST Require Import EVarsScratchwork.
Import VectorNotations.
(** * Natural Deduction

We need to formalize the proof calculus to then prove the correctness of soft 
type system.

References relevant:

- https://people.compute.dtu.dk/ahfrom/Formalized%20First-Order%20Logic.pdf
- https://hal.archives-ouvertes.fr/hal-03096253
*)


Class Ground A : Type := {
  is_ground : A -> Prop
}.

Fixpoint is_ground_term (t : Term) :=
match t with
| Var x => match x with
           | FVar _ => True
           | _ => False
           end
| EConst _ => False
| Fun f args => let fix are_args_ground {k} (ars : Vector.t Term k) :=
                    match ars with
                    | [] => True
                    | a::tl => is_ground_term a /\ are_args_ground tl
                    end
                in are_args_ground args
end.

Global Instance GroundTerm : Ground Term := {
  is_ground := is_ground_term
}.

(** ** Predicates

We encode the syntax of a predicate, analogous to [Term], as its arity 
[n : nat], its [name], and its arguments as a [Vector.t Term].
*)
Inductive Predicate : Type := 
| P : forall (n : nat), name -> Vector.t Term n -> Predicate.

Global Instance ContainsBVarPredicate : ContainsBVar Predicate := {
  contains_bvar (index : nat) (p : Predicate) :=
  match p with
  | P n nm args => Vector.Exists (fun (arg : Term) => contains_bvar index arg)
                   args
  end
}.

Global Instance GroundPredicate : Ground Predicate := {
  is_ground (p : Predicate) := match p with
  | P n s args => Vector.Forall is_ground args
  end
}.

Global Instance substPred : Subst Predicate :=
{
  subst (x : V) (t : Term) (p : Predicate) :=
  match p with
  | P n s args => P n s (Vector.map (fun (arg : Term) => subst x t arg) args)
  end
}.

Open Scope string_scope.

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

(* TODO I am too lazy to prove this... *)
Lemma eq_dec : forall (x y : Predicate), 
  {x = y} + {x <> y}.
Admitted.

Global Instance LiftPred : Lift Predicate :=
{
  lift (c d : nat) (p : Predicate) :=
  match p with
  | P n s args => P n s (Vector.map (fun (a : Term) => lift c d a) args)
  end;
  unlift (c d : nat) (p : Predicate) :=
  match p with
  | P n s args => P n s (Vector.map (fun (a : Term) => unlift c d a) args)
  end
}.

Require Import Coq.Logic.Eqdep_dec.

Theorem lift_id : forall (p : Predicate),
  lift 0 0 p = p.
Proof. intros. destruct p. rename t into args.
  unfold lift; unfold LiftPred.
  assert (Vector.map (fun a : Term => lift 0 0 a) args = args). {
    induction args.
    - simpl; auto.
    - assert (Vector.map (fun a : Term => lift 0 0 a) (h::args)
               = ((fun a : Term => lift 0 0 a) h)::(Vector.map (fun a : Term => lift 0 0 a) args)). {
        simpl; auto.
      }
      rewrite H. rewrite IHargs.
      rewrite Term.term_zero_lift_is_id. unfold id. reflexivity.
  }
  rewrite H; reflexivity.
Qed.

Require Import Coq.Logic.Eqdep_dec.

Lemma bigger_lift_is_id : forall (i k1 k2 : nat) (p : Predicate),
  k1 < k2 -> lift k1 i p = p -> lift k2 i p = p.
Proof.
  intros. destruct p.
  unfold lift; unfold LiftPred. rename t into args.
  assert (Vector.map (fun (a : Term) => lift k1 i a) args = args). {
    unfold lift in H0; unfold LiftPred in H0.
    inversion H0. apply inj_pair2_eq_dec in H2. rewrite H2.
    2: decide equality.
    unfold lift; unfold liftTerm. simpl; auto.
  }
  assert (Vector.map (fun (a : Term) => lift k2 i a) args = args). {
    apply bigger_lift_is_id_vector with (k2 := k2) in H1 as IH.
    simpl; auto. assumption.
  }
  rewrite H2; reflexivity.
Qed.

Theorem lift_comp : forall (c d1 d2 : nat) (p : Predicate),
  lift c d1 (lift c d2 p) = lift c (d1 + d2) p.
Proof.
  intros. destruct p as [n nm args].
  unfold lift; unfold LiftPred.
  rewrite vect_lift_comp. reflexivity.
Qed.

Global Instance FreshPredicate : Fresh Predicate := {
  fresh (c : Term) (p : Predicate) :=
  match p with
  | P n s args => Vector.Forall (fun (arg : Term) => fresh c arg) args
  end
}.

Global Instance EnumerateEVarsPredicate : EnumerateEVars Predicate := {
list_evars p := match p with
| P n s args => Vector.fold_left (fun l' => fun (arg : Term) => insert_merge (list_evars arg) l') []%list args
end
}.

Theorem list_evars_predicate_sorted : forall (p : Predicate),
  sorted (list_evars p).
Proof. intros.
  destruct p.
  rename t into args.
  unfold list_evars; unfold EnumerateEVarsPredicate.
  apply insert_merge_vector_fold_sorted2.
  apply sorted_nil.
Qed.

Global Instance ShiftEvarsPredicate : ShiftEvars Predicate := {
shift_evars p := match p with
| P n s args => P n s (Vector.map shift_evars args)
end
}.