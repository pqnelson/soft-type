Require Import String.
Require Import List.
Require Import Nat.
Require Import Coq.Vectors.Vector.
Require Export Coq.Arith.Compare_dec.
Require Import Coq.Arith.PeanoNat.
Require Export List.
Require Export RelationClasses.
Require Export Morphisms.
From ST Require Export EVarsScratchwork.
Import ListNotations.
Import VectorNotations.
Open Scope string_scope.


(* TODO: re-do the local context so that it meshes with locally nameless
variables correctly. *)

(** * Introduction

We have a couple of helper type classes for recurring functions expected on
constructs, things like [eqb] for boolean equality testing, and [subst] for
substituting a [Term] for a [V]ariable.
*)

Class Eq A :=
  {
    eqb: A -> A -> bool;
  }.

Fixpoint list_eqb {A : Type} (v1 v2 : list A) (eq : A -> A -> bool) : bool :=
  match v1,v2 with
  | List.nil, List.nil => true
  | List.cons h1 t1, List.cons h2 t2 => andb (eq h1 h2) (list_eqb t1 t2 eq)
  | _, _ => false
  end.

Global Instance natEq : Eq nat := {
  eqb (n1 n2 : nat) := Nat.eqb n1 n2
}.

Global Instance stringEq : Eq string := {
  eqb := String.eqb
}.

(** * Soft Type System

We begin formalizing our soft type system by defining variables and terms,
and the other syntactic constructs. Then we will inductively define the rules
of inference for the soft type system.

** Names and Variables

We use locally nameless encoding of bound variables. Free variables are any
arbitrary [name] instances. Bound variables are de Bruijn indices.
*)

Definition name : Type := string.

Inductive V :=
| FVar : name -> V
| BVar : nat -> V.

Global Instance VEq : Eq V := {
  eqb (x y : V) :=
  match x, y with
  | FVar s1, FVar s2 => eqb s1 s2
  | BVar n1, BVar n2 => eqb n1 n2
  | _, _ => false
  end
}.

Lemma V_eq_dec : forall a b : V, {a = b} + {a <> b}.
Proof. decide equality.
  try (left; reflexivity); try (right; congruence).
  - apply string_dec.
  - decide equality.
Defined.

(** We now need to handle [lift]-ing a bound variable. Since this will occur
wherever a [BVar] can occur (and wherever a [Term] may occur), we will use a
typeclass to handle this. *)

Class Lift A := {
  lift : nat -> nat -> A -> A
}.

Definition shift {A : Type} `{Lift A} (a : A) : A := lift 0 1 a.

Global Instance VLift : Lift V := {
  lift (cutoff depth : nat) (x : V) :=
  match x with
  | FVar nm => x
  | BVar n => if lt_dec n cutoff then x else BVar (n+depth)
  end
}.

(** Lemma: [lift 0 0] is the identity transformation. *)
Lemma zero_lift_is_id : forall (n : nat), lift 0 0 (BVar n) = (BVar n).
Proof.
  intros. simpl. auto.
Qed.

Theorem case_lift_is_not_id : forall (i k n : nat), k <= n -> lift k i (BVar n) = BVar (n+i).
Proof.
  intros. simpl. destruct (lt_dec n k).
  - contradict H. apply Gt.gt_not_le in l. auto.
  - auto.
Qed.

Theorem case_lift_is_id : forall (i k n : nat), k > n -> lift k i (BVar n) = BVar (n).
Proof.
  intros. simpl. destruct (lt_dec n k). 
  - auto.
  - apply not_lt in n0. contradict n0. apply Gt.gt_not_le in H. trivial.
Qed.

Example shift_is_not_id : shift (BVar 0) = (BVar 1).
Proof.
  trivial.
Qed.

Example shift_really_shifts : forall (n : nat), shift (BVar n) = BVar (n + 1).
Proof.
  trivial.
Qed.

(** ** Terms

A [Term] is either a variable, or an n-ary function. Constants are just nullary 
functions. We do carve out [EConst] for existential constants, to make
logic easier later on.
*)

Inductive Term : Type :=
| Var : V -> Term
(*
| Fun : forall (n : nat), name -> Vector.t Term n -> Term
*)
| EConst : nat -> Term
| Fun {n} : name -> Vector.t Term n -> Term.

Definition constant (c : name) : Term :=
@Fun 0 c [].

Fixpoint term_eqb (t1 t2 : Term) : bool :=
match t1,t2 with
| Var x1, Var x2 => eqb x1 x2
| EConst n1, EConst n2 => eqb n1 n2
| @Fun n1 s1 args1, @Fun n2 s2 args2 => 
  let fix args_eqb {n1 n2} (ar1 : Vector.t Term n1) (ar2 : Vector.t Term n2) : bool :=
      match ar1,ar2 with
      | Vector.nil _, Vector.nil _ => true
      | Vector.cons _ h1 k1 t1,  Vector.cons _ h2 k2 t2 => if (eqb k1 k2) then
                                                            (if (term_eqb h1 h2) then (args_eqb t1 t2) else false)
                                                           else false
      | _, _ => false
      end
  in (eqb n1 n2) && (eqb s1 s2) && (args_eqb args1 args2)
| _, _ => false
end.

Fixpoint map_vars_term (f : V -> V) (t : Term) : Term :=
match t with
| Var x => Var (f x)
| EConst _ => t
| Fun s args => Fun s (Vector.map (map_vars_term f) args)
end.

Global Instance EqTerm : Eq Term := {
  eqb := term_eqb
}.

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

Definition tlift (c d : nat) (t : Term) : Term :=
map_vars_term (lift c d) t.

Global Instance liftTerm : Lift Term :=
{
  lift := tlift
}.

Definition term_is_fun (t : Term) : Prop :=
  match t with
  | Fun _ _ =>  True
  | _ => False
  end.

(** ** Radix Types

These are "mother types". In full Mizar, this is either a [Mode] or a [Struct] 
or a set (what we call [Ast]).
*)
Inductive Radix : Type :=
| Ast : Radix
| Mode : forall (n : nat), name -> Vector.t Term n -> Radix.

Definition radix_is_mode (R : Radix) : Prop :=
  match R with
  | Mode _ _ _ => True
  | _ => False
  end.

Fixpoint vectors_eqb {A : Type} {n1 n2} (v1 : Vector.t A n1) (v2 : Vector.t A n2) (eq : A -> A -> bool) : bool :=
match v1, v2 with
| Vector.nil _, Vector.nil _ => true
| Vector.cons _ h1 k1 t1,  Vector.cons _ h2 k2 t2 => if andb (eqb k1 k2) (eq h1 h2) then (vectors_eqb t1 t2 eq) else false
| _, _ => false
end.

Global Instance EqRadix : Eq Radix := {
  eqb (R1 R2 : Radix) :=
  match R1,R2 with
  | Ast, Ast => true
  | Mode n1 s1 args1, Mode n2 s2 args2 => if andb (eqb n1 n2) (eqb s1 s2) then
    vectors_eqb args1 args2 term_eqb
    else false
  | _, _ => false
  end
}.

Global Instance substRadix : Subst Radix :=
{
  subst (x : V) (t : Term) (R : Radix) :=
  match R with
  | Ast => R
  | Mode n s args => Mode n s (Vector.map (fun (arg : Term) => subst x t arg) args)
  end
}.

Global Instance liftRadix : Lift Radix :=
{
  lift (c d : nat) (R : Radix) :=
  match R with
  | Ast => R
  | Mode n s args => Mode n s (Vector.map (fun (a : Term) => lift c d a) args)
  end
}.

(** ** Attributes

Attributes may be prepended to types, when registered in an existential cluster.
Otherwise, we can create a formula [Term is Attribute]. 
*)

Inductive Attribute : Type := 
| Attr : forall (n : nat), name -> Vector.t Term n -> Attribute.

Global Instance EqAttribute : Eq Attribute := {
  eqb (A1 A2 : Attribute) :=
  match A1,A2 with
  | Attr n1 s1 args1, Attr n2 s2 args2 => if andb (eqb n1 n2) (eqb s1 s2) then
    vectors_eqb args1 args2 term_eqb
    else false
  end
}.

Global Instance substAttr : Subst Attribute :=
{
  subst (x : V) (t : Term) (a : Attribute) :=
  match a with
  | Attr n s args => Attr n s (Vector.map (fun (arg : Term) => subst x t arg) args)
  end
}.

Global Instance liftAttr : Lift Attribute :=
{
  lift (c d : nat) (a : Attribute) :=
  match a with
  | Attr n s args => Attr n s (Vector.map (fun (a : Term) => lift c d a) args)
  end
}.

(** ** Adjectives

An adjective is either a "positive [Attribute]" or a "negative [Attribute]".
*)

Inductive Adjective : Type :=
| Pos : Attribute -> Adjective
| Neg : Attribute -> Adjective.

Global Instance EqAdjective : Eq Adjective := {
  eqb (A1 A2 : Adjective) :=
  match A1,A2 with
  | Pos a1, Pos a2 => eqb a1 a2
  | Neg a1, Neg a2 => eqb a1 a2
  | _, _ => false
  end
}.

Global Instance substAdj : Subst Adjective := {
  subst (x : V) (t : Term) (alpha : Adjective) :=
  match alpha with
  | Pos a => Pos (subst x t a)
  | Neg a => Neg (subst x t a)
  end
}.

Global Instance liftAdj : Lift Adjective :=
{
  lift (c d : nat) (alpha : Adjective) :=
  match alpha with
  | Pos a => Pos (lift c d a)
  | Neg a => Neg (lift c d a)
  end
}.

(* ** Soft Types

We can encode a [SoftType] as an ordered pair of a list of [Adjective] and
a [Radix] type.
*)
Definition SoftType : Type := (list Adjective)*Radix.
Definition Star : SoftType := (List.nil, Ast).

Global Instance EqSoftType : Eq SoftType := {
  eqb (T1 T2 : SoftType) :=
  match T1,T2 with
  | (adjs1, R1), (adjs2, R2) => andb (list_eqb adjs1 adjs2 eqb) (eqb R1 R2)
  end
}.

Global Instance substSoftType : Subst SoftType := {
  subst (x : V) (t : Term) (T : SoftType) :=
  match T with
  | (List.nil, R) => (List.nil, subst x t R)
  | (adjs, R) => (List.map (fun (a : Adjective) => subst x t a) adjs, subst x t R)
  end
}.

Global Instance liftSoftType : Lift SoftType :=
{
  lift (c d : nat) (T : SoftType) :=
  match T with
  | (adjs, R) => (List.map (fun (a : Adjective) => (lift c d a)) adjs, lift c d R)
  end
}.

Definition type_is_named (T : SoftType) (n : name) : Prop :=
  match T with
  | (_, Mode k1 s1 args1) => n = s1
  | _ => False
  end.

Definition mk_mode {n} (M : name) (args : Vector.t Term n) : SoftType :=
  (List.nil, (Mode n M args)).

Definition prefix (a : Adjective) (T : SoftType) : SoftType :=
  match T with
  | (adjs, R) => if List.existsb (fun (adj : Adjective) => eqb a adj) adjs 
                 then T else (List.cons a adjs, R)
  end.

Fixpoint prefix_all (adjs : list Adjective) (T : SoftType) : SoftType :=
  match adjs with
  | List.nil => T
  | List.cons a ad2 => prefix_all ad2 (prefix a T)
  end.

Definition non (a : Adjective) : Adjective :=
  match a with
  | Pos attr => Neg attr
  | Neg attr => Pos attr
  end.

(** ** Judgement Types *)

Inductive JudgementType :=
| CorrectContext : JudgementType
| Esti : Term -> SoftType -> JudgementType
| Subtype : SoftType -> SoftType -> JudgementType
| Inhabited : SoftType -> JudgementType
| HasAttribute : Attribute -> SoftType -> JudgementType.

Global Instance substJudgementType : Subst JudgementType := {
  subst (x : V) (t : Term) (J : JudgementType) :=
  match J with
  | CorrectContext => J
  | Esti tm Tp => Esti (subst x t tm) (subst x t Tp)
  | Subtype T1 T2 => Subtype (subst x t T1) (subst x t T2)
  | Inhabited T => Inhabited (subst x t T)
  | HasAttribute a T => HasAttribute (subst x t a) (subst x t T)
  end
}.

Global Instance liftJudgementType : Lift JudgementType := {
  lift (c d : nat) (J : JudgementType) :=
  match J with
  | CorrectContext => J
  | Esti tm Tp => Esti (lift c d tm) (lift c d Tp)
  | Subtype T1 T2 => Subtype (lift c d T1) (lift c d T2)
  | Inhabited T => Inhabited (lift c d T)
  | HasAttribute a T => HasAttribute (lift c d a) (lift c d T)
  end
}.

(** ** Local Contexts

A local context is just a finite list of [Decl] (declaration of variables and
their types). We will turn this into arguments for a [Term] (or [Attribute], 
or...), so we have a [local_vars] helper function to accomodate this.


TODO: I think this is not quite right. Using locally nameless terms, a 
declaration simplifies to just a [SoftType]. Then a [LocalContext] is just
a list of [Decl].

TODO 2: Think hard about whether lifting is necessary for local contexts.
*)
Definition Decl : Type := V*SoftType.
Definition LocalContext := list SoftType.

(**
Given a [LocalContext], we can turn it into a vector of variables, to be used as
the arguments for a [Term], [Attribute], or [SoftType] (or whatever).
*)
Definition local_vars (lc : LocalContext) : Vector.t Term (List.length lc) :=
  Vector.map (fun (n : nat) => Var (BVar n))
  (rev_nat_range_vector (length lc)).

Example local_vars_3 :
  (local_vars [Star; Star; Star]%list) = [Var (BVar 2); Var (BVar 1); Var (BVar 0)].
Proof.
  simpl; auto.
Qed.

(* Helper function to turn a [nat] into a [string]. *)
Fixpoint string_of_nat_aux (time n : nat) (acc : string) : string :=
  let d := match n mod 10 with
           | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5"
           | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
           end in
  let acc' := d ++ acc in
  match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => string_of_nat_aux time' n' acc'
      end
  end.

Definition string_of_nat (n : nat) : string :=
  string_of_nat_aux n n "".

(** Given a [LocalContext] and a [Term], we can redefine it using the local
variables from our [LocalContext]. *)
Definition fun_with_locals (t : Term) (lc : LocalContext) : Term :=
  match t with
  | Fun f args => Fun f (local_vars lc)
  | EConst _ => t
  | Var var => match var with
               | FVar x => Fun x (local_vars lc)
               | BVar n => Fun ("BoundVar_" ++ string_of_nat n) (local_vars lc)
               end
  end.
  
Definition mode_with_locals (R : Radix) (lc : LocalContext) : Radix :=
  match R with
  | Ast => Ast
  | Mode n nm args => Mode (List.length lc) nm (local_vars lc)
  end.

Fixpoint lc_is_subcontext (subcontext lc : LocalContext) : Prop :=
  match subcontext with
  | List.cons (x,T) subcontext' => List.In (x,T) lc /\ lc_is_subcontext subcontext' lc
  | List.nil => True
  end.

(** ** Global Contexts

We now can track definitions of terms, types, etc., using a [GlobalContext].
This is encoded as just a list of [JudgementType] and the relevant local 
variables as found in a [LocalContext].
*)
Definition GlobalContext := list (LocalContext * JudgementType).

(** Judgements of the form [t : T] are where we define new constant terms. *)
Fixpoint gc_defines_term (gc : GlobalContext) (n : name) : Prop :=
  match gc with
  | List.cons (lc, Esti (Fun nm _) T) tl => (n = nm) \/ gc_defines_term tl n
  | _ => False
  end.

Fixpoint gc_defines_type (gc : GlobalContext) (n : name) : Prop :=
  match gc with
  | List.cons (lc, Subtype T1 T2) tl => (type_is_named T1 n) \/ (type_is_named T2 n) \/ (gc_defines_type  tl n)
  | List.cons (lc, Inhabited T) tl =>(type_is_named T n) \/ (gc_defines_type  tl n)
  | _ => False
  end.

Fixpoint gc_defines_attr (gc : GlobalContext) (n : name) : Prop :=
  match gc with
  | List.cons (lc, HasAttribute (Attr _ a args) T) tl => (a = n) \/ (gc_defines_attr tl n)
  | _ => False
  end.

Fixpoint gc_contains (Γ : GlobalContext) (def : (LocalContext * JudgementType)) : Prop :=
  match Γ,def with
  | List.cons (lc, J') Γ', (subcontext, J) => ((lc_is_subcontext subcontext lc) /\ J = J') \/ gc_contains Γ' def
  | List.nil, _ => False
  end.

(** * Inference Rules for Soft Types

We can now code up the inference rules for Wiedijk's soft type system inductively. 
*)
Definition Judgement : Type := GlobalContext * LocalContext * JudgementType.

Definition Judgement_body (j : Judgement) :=
match j with
| (_,_, body) => body
end.

Definition push {A : Type} (a : A) (l : list A) : list A :=
  List.app l (List.cons a List.nil).

Notation "gc ;; lc |- j" := (gc, lc, j) (at level 80).
Inductive well_typed : Judgement -> Prop :=
| wt_empty_context : well_typed (List.nil ;; List.nil |- CorrectContext)
| wt_var : forall (Γ : GlobalContext) (Δ : LocalContext) (T : SoftType) (J : JudgementType),
  well_typed (Γ ;; Δ |- Inhabited T) ->
  well_typed (Γ ;; (push T Δ) |- CorrectContext)
(* TODO: substitution rule for a vector of declarations *)
| wt_subst : forall (Γ : GlobalContext) (Δ : LocalContext) (t : Term) (T : SoftType) (J : JudgementType),
  gc_contains Γ ((List.cons T List.nil), J) ->
  well_typed (Γ ;; Δ |- Esti t T) ->
  well_typed (Γ ;; Δ |- (subst (BVar 0) t J))
(* TODO: inhabited types produce new local variables *)
| wt_subtype_star_star : forall (Γ : GlobalContext) (Δ : LocalContext),
  well_typed (Γ ;; Δ |- CorrectContext) ->
  well_typed (Γ ;; Δ |- Subtype Star Star)
| wt_inhabited_star : forall (Γ : GlobalContext) (Δ : LocalContext),
  well_typed (Γ ;; Δ |- CorrectContext) ->
  well_typed (Γ ;; Δ |- Inhabited Star)
| wt_subtype_refl : forall (Γ : GlobalContext) (Δ : LocalContext) (T1 T2 : SoftType),
  well_typed (Γ ;; Δ |- Subtype T1 T2) ->
  well_typed (Γ ;; Δ |- Subtype T1 T1)
| wt_subtype_trans : forall (Γ : GlobalContext) (Δ : LocalContext) (T1 T2 T3 : SoftType),
  well_typed (Γ ;; Δ |- Subtype T1 T2) ->
  well_typed (Γ ;; Δ |- Subtype T2 T3) ->
  well_typed (Γ ;; Δ |- Subtype T1 T3)
| wt_subsumption : forall (Γ : GlobalContext) (Δ : LocalContext) (T1 T2 : SoftType) (t : Term),
  well_typed (Γ ;; Δ |- Esti t T1) ->
  well_typed (Γ ;; Δ |- Subtype T1 T2) ->
  well_typed (Γ ;; Δ |- Esti t T2)
| wt_parent_inhabited : forall (Γ : GlobalContext) (Δ : LocalContext) (T1 T2 : SoftType),
  well_typed (Γ ;; Δ |- Subtype T1 T2) ->
  well_typed (Γ ;; Δ |- Inhabited T1) ->
  well_typed (Γ ;; Δ |- Inhabited T2)
| wt_cons_adj : forall (Γ : GlobalContext) (Δ : LocalContext) (T : SoftType) (A : Attribute),
  well_typed (Γ ;; Δ |- HasAttribute A T) ->
  well_typed (Γ ;; Δ |- Subtype (prefix (Pos A) T) T)
| wt_cons_non : forall (Γ : GlobalContext) (Δ : LocalContext) (T : SoftType) (A : Attribute),
  well_typed (Γ ;; Δ |- HasAttribute A T) ->
  well_typed (Γ ;; Δ |- Subtype (prefix (Neg A) T) T)
| wt_adj_subtype : forall (Γ : GlobalContext) (Δ : LocalContext) (T1 T2 : SoftType) (a : Adjective),
  well_typed (Γ ;; Δ |- Subtype T1 T2) ->
  well_typed (Γ ;; Δ |- Subtype (prefix a T2) T2) ->
  well_typed (Γ ;; Δ |- Subtype (prefix a T1) T1)
| wt_adj_subtype_adj : forall (Γ : GlobalContext) (Δ : LocalContext) (T1 T2 : SoftType) (a : Adjective),
  well_typed (Γ ;; Δ |- Subtype T1 T2) ->
  well_typed (Γ ;; Δ |- Subtype (prefix a T2) T2) ->
  well_typed (Γ ;; Δ |- Subtype (prefix a T1) (prefix a T2))
| wt_adj_diamond : forall (Γ : GlobalContext) (Δ : LocalContext) (T1 T2 : SoftType) (a1 a2 : Adjective),
  well_typed (Γ ;; Δ |- Subtype T1 (prefix a1 T2)) ->
  well_typed (Γ ;; Δ |- Subtype T1 (prefix a2 T2)) ->
  well_typed (Γ ;; Δ |- Subtype T1 (prefix a1 (prefix a2 T2)))
  (* Rules governing Definitions *)
| wt_functor_def : forall (Γ : GlobalContext) (Δ : LocalContext) (T : SoftType) (f : name),
  not (gc_defines_term Γ f) ->
  well_typed (Γ ;; Δ |- Inhabited T) ->
  well_typed ((List.app Γ (List.cons (Δ, (Esti (Fun f (local_vars Δ)) T)) List.nil)) ;; List.nil |- CorrectContext)
| wt_mode_def : forall (Γ : GlobalContext) (Δ : LocalContext) (T : SoftType) (M : name), 
  not (gc_defines_type Γ M) ->
  well_typed (Γ ;; Δ |- Inhabited T) ->  
  well_typed ((List.app Γ 
              (List.cons (Δ, (Subtype (mk_mode M (local_vars Δ)) T))
                (List.cons (Δ, (Inhabited (mk_mode M (local_vars Δ)))) List.nil))) ;; List.nil |- CorrectContext)
| wt_attr_def : forall (Γ : GlobalContext) (Δ : LocalContext) (T : SoftType) (alpha : name), 
  not (gc_defines_attr Γ alpha) ->
  well_typed (Γ ;; Δ |- Inhabited T) ->
  well_typed (List.app Γ (List.cons (Δ, HasAttribute (Attr (List.length Δ) alpha (local_vars Δ)) T) List.nil) ;; List.nil |- CorrectContext)
  (* Rules governing clusters *)
| wt_cluster_exist : forall (Γ : GlobalContext) (Δ : LocalContext) (T : SoftType) (a : Adjective), 
  well_typed (Γ ;; Δ |- Subtype (prefix a T) T) ->
  well_typed (Γ ;; Δ |- Inhabited T) ->
  well_typed (List.app Γ (List.cons (Δ, (Inhabited (prefix a T))) List.nil) ;; List.nil |- CorrectContext)
| wt_cluster_cond : forall (Γ : GlobalContext) (Δ : LocalContext) (T : SoftType) (a1 a2 : list Adjective), 
  well_typed (Γ ;; Δ |- Subtype (prefix_all a1 T) T) ->
  well_typed (Γ ;; Δ |- Subtype (prefix_all a2 T) T) ->
  well_typed (List.app Γ (List.cons (Δ, (Subtype (prefix_all a1 T) (prefix_all a2 T))) List.nil) ;; List.nil |- CorrectContext)
| wt_cluster_fun : forall (Γ : GlobalContext) (Δ : LocalContext) (t : Term) (T : SoftType) (a : Adjective), 
  well_typed (Γ ;; Δ |- Esti t T) ->
  well_typed (Γ ;; Δ |- Subtype (prefix a T) T) ->
  well_typed (List.app Γ (List.cons (Δ, (Esti t (prefix a T))) List.nil) ;; List.nil |- CorrectContext)
  (* Rules governing redefinitions *)
| wt_redef_fun : forall (Γ : GlobalContext) (Δ₁ Δ₂ : LocalContext) (t : Term) (T1 T2 T3 : SoftType), 
  term_is_fun t ->
  well_typed (Γ ;; Δ₂ |- Inhabited T2) ->
  well_typed (Γ ;; Δ₂ |- Subtype T2 T3) ->
  well_typed (Γ ;; (List.app Δ₁ Δ₂) |- Esti (fun_with_locals t Δ₂) T3) ->
  well_typed ((List.app Γ (List.cons ((List.app Δ₁ Δ₂), (Esti (fun_with_locals t Δ₂) T3)) List.nil)) ;; List.nil |- CorrectContext)
| wt_redef_mode : forall (Γ : GlobalContext) (Δ₁ Δ₂ : LocalContext) (M : Radix) (T1 T2 T3 : SoftType), 
  radix_is_mode M ->
  well_typed (Γ ;; Δ₂ |- Inhabited T2) ->
  well_typed (Γ ;; Δ₂ |- Subtype T2 T3) ->
  well_typed (Γ ;; (List.app Δ₁ Δ₂) |- Subtype (List.nil, (mode_with_locals M Δ₂)) T3) ->
  well_typed ((List.app Γ (List.cons ((List.app Δ₁ Δ₂), (Subtype (List.nil, (mode_with_locals M Δ₂)) T3)) List.nil)) ;; List.nil |- CorrectContext).
