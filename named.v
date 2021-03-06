Require Import String.
Require Import List.
Require Import Nat.
Require Import Coq.Vectors.Vector.
Require Export Coq.Arith.Compare_dec.
Require Export List.
Require Export RelationClasses.
Require Export Morphisms.
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

Require Import Coq.Arith.PeanoNat.

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
functions.
*)

Inductive Term : Type :=
| Var : V -> Term
| Fun : forall (n : nat), name -> Vector.t Term n -> Term.

Definition constant (c : name) : Term :=
Fun 0 c [].

Fixpoint term_eqb (t1 t2 : Term) : bool :=
match t1,t2 with
| Var x1, Var x2 => eqb x1 x2
| Fun n1 s1 args1, Fun n2 s2 args2 => 
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
| Fun n f args => Fun n f (Vector.map (fun (a : Term) => tsubst x t a) args)
end.

Global Instance substTerm : Subst Term :=
{
  subst (x : V) (t : Term) (e : Term) := tsubst x t e
}.

Compute (subst (BVar 1) (Fun 0 "c" []) (Fun 2 "f" [Var (BVar 1) ; Var (FVar "x")])).

Example term_subst_1 : subst (BVar 1) (Fun 0 "c" []) (Fun 2 "f" [Var (BVar 1) ; Var (FVar "x")])
= Fun 2 "f" [(Fun 0 "c" []) ; Var (FVar "x")].
Proof.
  trivial.
Qed.

Example term_subst_2 : subst (FVar "x") (Fun 0 "c" []) (Fun 2 "f" [Var (BVar 1) ; Var (FVar "x")])
= Fun 2 "f" [Var (BVar 1) ; (Fun 0 "c" [])].
Proof.
  trivial.
Qed.

Example term_subst_3 : subst (BVar 3) (Fun 0 "c" []) (Fun 2 "f" [Var (BVar 1) ; Var (FVar "x")])
= Fun 2 "f" [Var (BVar 1) ; Var (FVar "x")].
Proof.
  trivial.
Qed.

Example term_subst_4 : subst (FVar "z") (Fun 0 "c" []) (Fun 2 "f" [Var (BVar 1) ; Var (FVar "x")])
= Fun 2 "f" [Var (BVar 1) ; Var (FVar "x")].
Proof.
  trivial.
Qed.

Fixpoint tlift (c d : nat) (t : Term) : Term :=
match t with
| Var y => Var (lift c d y)
| Fun n f args => Fun n f (Vector.map (fun (a : Term) => tlift c d a) args)
end.

Global Instance liftTerm : Lift Term :=
{
  lift := tlift
}.

Definition term_is_fun (t : Term) : Prop :=
  match t with
  | Fun _ _ _ =>  True
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
| Context : JudgementType
| Esti : Term -> SoftType -> JudgementType
| Subtype : SoftType -> SoftType -> JudgementType
| Inhabited : SoftType -> JudgementType
| HasAttribute : Attribute -> SoftType -> JudgementType.

Global Instance substJudgementType : Subst JudgementType := {
  subst (x : V) (t : Term) (J : JudgementType) :=
  match J with
  | Context => J
  | Esti tm Tp => Esti (subst x t tm) (subst x t Tp)
  | Subtype T1 T2 => Subtype (subst x t T1) (subst x t T2)
  | Inhabited T => Inhabited (subst x t T)
  | HasAttribute a T => HasAttribute (subst x t a) (subst x t T)
  end
}.

Global Instance liftJudgementType : Lift JudgementType := {
  lift (c d : nat) (J : JudgementType) :=
  match J with
  | Context => J
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
Definition LocalContext := list Decl.

(**
Given a [LocalContext], we can turn it into a vector of variables, to be used as
the arguments for a [Term], [Attribute], or [SoftType] (or whatever).
*)
Fixpoint local_vars (lc : LocalContext) : Vector.t Term (List.length lc) :=
  match lc with
  | List.cons (x,_) tl => (Var x)::(local_vars tl)
  | List.nil => []
  end.

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
  | Fun n f args => Fun (List.length lc) f (local_vars lc)
  | Var var => match var with
               | FVar x => Fun (List.length lc) x (local_vars lc)
               | BVar n => Fun (List.length lc) ("BoundVar_" ++ string_of_nat n) (local_vars lc)
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
  | List.cons (lc, Esti (Fun k nm _) T) tl => (n = nm) \/ gc_defines_term tl n
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

Fixpoint gc_contains (?? : GlobalContext) (def : (LocalContext * JudgementType)) : Prop :=
  match ??,def with
  | List.cons (lc, J') ??', (subcontext, J) => ((lc_is_subcontext subcontext lc) /\ J = J') \/ gc_contains ??' def
  | List.nil, _ => False
  end.

(** * Inference Rules for Soft Types

We can now code up the inference rules for Wiedijk's soft type system inductively. 
*)
Definition Judgement : Type := GlobalContext * LocalContext * JudgementType.

Definition push {A : Type} (a : A) (l : list A) : list A :=
  List.app l (List.cons a List.nil).

Notation "gc ;; lc |- j" := (gc, lc, j) (at level 80).
Inductive well_typed : Judgement -> Prop :=
| wt_empty_context : well_typed (List.nil ;; List.nil |- Context)
| wt_var : forall (?? : GlobalContext) (?? : LocalContext) (x : V) (T : SoftType) (J : JudgementType),
  well_typed (?? ;; ?? |- Inhabited T) ->
  well_typed (?? ;; (push (x,T) ??) |- Context)
(* TODO: substitution rule for a vector of declarations *)
| wt_subst : forall (?? : GlobalContext) (?? : LocalContext) (x : V) (t : Term) (T : SoftType) (J : JudgementType),
  gc_contains ?? ((List.cons (x,T) List.nil), J) ->
  well_typed (?? ;; ?? |- Esti t T) ->
  well_typed (?? ;; ?? |- (subst x t J))
(* TODO: inhabited types produce new local variables *)
| wt_subtype_star_star : forall (?? : GlobalContext) (?? : LocalContext),
  well_typed (?? ;; ?? |- Context) ->
  well_typed (?? ;; ?? |- Subtype Star Star)
| wt_inhabited_star : forall (?? : GlobalContext) (?? : LocalContext),
  well_typed (?? ;; ?? |- Context) ->
  well_typed (?? ;; ?? |- Inhabited Star)
| wt_subtype_refl : forall (?? : GlobalContext) (?? : LocalContext) (T1 T2 : SoftType),
  well_typed (?? ;; ?? |- Subtype T1 T2) ->
  well_typed (?? ;; ?? |- Subtype T1 T1)
| wt_subtype_trans : forall (?? : GlobalContext) (?? : LocalContext) (T1 T2 T3 : SoftType),
  well_typed (?? ;; ?? |- Subtype T1 T2) ->
  well_typed (?? ;; ?? |- Subtype T2 T3) ->
  well_typed (?? ;; ?? |- Subtype T1 T3)
| wt_subsumption : forall (?? : GlobalContext) (?? : LocalContext) (T1 T2 : SoftType) (t : Term),
  well_typed (?? ;; ?? |- Esti t T1) ->
  well_typed (?? ;; ?? |- Subtype T1 T2) ->
  well_typed (?? ;; ?? |- Esti t T2)
| wt_parent_inhabited : forall (?? : GlobalContext) (?? : LocalContext) (T1 T2 : SoftType),
  well_typed (?? ;; ?? |- Subtype T1 T2) ->
  well_typed (?? ;; ?? |- Inhabited T1) ->
  well_typed (?? ;; ?? |- Inhabited T2)
| wt_cons_adj : forall (?? : GlobalContext) (?? : LocalContext) (T : SoftType) (A : Attribute),
  well_typed (?? ;; ?? |- HasAttribute A T) ->
  well_typed (?? ;; ?? |- Subtype (prefix (Pos A) T) T)
| wt_cons_non : forall (?? : GlobalContext) (?? : LocalContext) (T : SoftType) (A : Attribute),
  well_typed (?? ;; ?? |- HasAttribute A T) ->
  well_typed (?? ;; ?? |- Subtype (prefix (Neg A) T) T)
| wt_adj_subtype : forall (?? : GlobalContext) (?? : LocalContext) (T1 T2 : SoftType) (a : Adjective),
  well_typed (?? ;; ?? |- Subtype T1 T2) ->
  well_typed (?? ;; ?? |- Subtype (prefix a T2) T2) ->
  well_typed (?? ;; ?? |- Subtype (prefix a T1) T1)
| wt_adj_subtype_adj : forall (?? : GlobalContext) (?? : LocalContext) (T1 T2 : SoftType) (a : Adjective),
  well_typed (?? ;; ?? |- Subtype T1 T2) ->
  well_typed (?? ;; ?? |- Subtype (prefix a T2) T2) ->
  well_typed (?? ;; ?? |- Subtype (prefix a T1) (prefix a T2))
| wt_adj_diamond : forall (?? : GlobalContext) (?? : LocalContext) (T1 T2 : SoftType) (a1 a2 : Adjective),
  well_typed (?? ;; ?? |- Subtype T1 (prefix a1 T2)) ->
  well_typed (?? ;; ?? |- Subtype T1 (prefix a2 T2)) ->
  well_typed (?? ;; ?? |- Subtype T1 (prefix a1 (prefix a2 T2)))
  (* Rules governing Definitions *)
| wt_functor_def : forall (?? : GlobalContext) (?? : LocalContext) (T : SoftType) (f : name),
  not (gc_defines_term ?? f) ->
  well_typed (?? ;; ?? |- Inhabited T) ->
  well_typed ((List.app ?? (List.cons (??, (Esti (Fun (List.length ??) f (local_vars ??)) T)) List.nil)) ;; List.nil |- Context)
| wt_mode_def : forall (?? : GlobalContext) (?? : LocalContext) (T : SoftType) (M : name), 
  not (gc_defines_type ?? M) ->
  well_typed (?? ;; ?? |- Inhabited T) ->  
  well_typed ((List.app ?? 
              (List.cons (??, (Subtype (mk_mode M (local_vars ??)) T))
                (List.cons (??, (Inhabited (mk_mode M (local_vars ??)))) List.nil))) ;; List.nil |- Context)
| wt_attr_def : forall (?? : GlobalContext) (?? : LocalContext) (T : SoftType) (alpha : name), 
  not (gc_defines_attr ?? alpha) ->
  well_typed (?? ;; ?? |- Inhabited T) ->
  well_typed (List.app ?? (List.cons (??, HasAttribute (Attr (List.length ??) alpha (local_vars ??)) T) List.nil) ;; List.nil |- Context)
  (* Rules governing clusters *)
| wt_cluster_exist : forall (?? : GlobalContext) (?? : LocalContext) (T : SoftType) (a : Adjective), 
  well_typed (?? ;; ?? |- Subtype (prefix a T) T) ->
  well_typed (?? ;; ?? |- Inhabited T) ->
  well_typed (List.app ?? (List.cons (??, (Inhabited (prefix a T))) List.nil) ;; List.nil |- Context)
| wt_cluster_cond : forall (?? : GlobalContext) (?? : LocalContext) (T : SoftType) (a1 a2 : list Adjective), 
  well_typed (?? ;; ?? |- Subtype (prefix_all a1 T) T) ->
  well_typed (?? ;; ?? |- Subtype (prefix_all a2 T) T) ->
  well_typed (List.app ?? (List.cons (??, (Subtype (prefix_all a1 T) (prefix_all a2 T))) List.nil) ;; List.nil |- Context)
| wt_cluster_fun : forall (?? : GlobalContext) (?? : LocalContext) (t : Term) (T : SoftType) (a : Adjective), 
  well_typed (?? ;; ?? |- Esti t T) ->
  well_typed (?? ;; ?? |- Subtype (prefix a T) T) ->
  well_typed (List.app ?? (List.cons (??, (Esti t (prefix a T))) List.nil) ;; List.nil |- Context)
  (* Rules governing redefinitions *)
| wt_redef_fun : forall (?? : GlobalContext) (????? ????? : LocalContext) (t : Term) (T1 T2 T3 : SoftType), 
  term_is_fun t ->
  well_typed (?? ;; ????? |- Inhabited T2) ->
  well_typed (?? ;; ????? |- Subtype T2 T3) ->
  well_typed (?? ;; (List.app ????? ?????) |- Esti (fun_with_locals t ?????) T3) ->
  well_typed ((List.app ?? (List.cons ((List.app ????? ?????), (Esti (fun_with_locals t ?????) T3)) List.nil)) ;; List.nil |- Context)
| wt_redef_mode : forall (?? : GlobalContext) (????? ????? : LocalContext) (M : Radix) (T1 T2 T3 : SoftType), 
  radix_is_mode M ->
  well_typed (?? ;; ????? |- Inhabited T2) ->
  well_typed (?? ;; ????? |- Subtype T2 T3) ->
  well_typed (?? ;; (List.app ????? ?????) |- Subtype (List.nil, (mode_with_locals M ?????)) T3) ->
  well_typed ((List.app ?? (List.cons ((List.app ????? ?????), (Subtype (List.nil, (mode_with_locals M ?????)) T3)) List.nil)) ;; List.nil |- Context).

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
| Var (BVar _) => False
| Fun n f args => let fix fresh_args {k} (ars : Vector.t Term k) :=
                  match ars with
                  | tm::ars1 => (fresh_term c tm) /\ fresh_args ars1
                  | [] => True
                  end
                  in fresh_args args
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

Fixpoint fresh_list (c : name) (?? : list Formula) : Prop :=
match ?? with
| List.nil => True
| List.cons p ??' => (fresh c p) /\ (fresh_list c ??')
end.

Global Instance FreshContext : Fresh (list Formula) := {
  fresh := fresh_list
}.

Import ListNotations.
Reserved Notation "?? ??? P" (no associativity, at level 61).

Inductive deducible : list Formula -> Formula -> Prop :=
| ND_exfalso_quodlibet {?? p} :
  ?? ??? Falsum ->
  ?? ??? p
| ND_True_intro {??} :
  ?? ??? Verum
| ND_assume {?? p} :
  List.In p ?? -> 
  ?? ??? p
| ND_imp_e {?? p q} :
  ?? ??? Implies p q -> ?? ??? p ->
  ?? ??? q
  (*
| ND_imp_i {?? p q} :
  List.In p ?? -> ?? ??? q ->
  (List.remove Formula_eq_dec p ??) ??? Implies p q
  *)
| ND_imp_i2 {?? p q} :
  p::?? ??? q -> ?? ??? Implies p q
| ND_or_intro_l {?? p q} :
  ?? ??? p ->
  ?? ??? Or p q
| ND_or_intro_r {?? p q} :
  ?? ??? q ->
  ?? ??? Or p q
| ND_proof_by_cases {?? p q r} :
  ?? ??? Or p q ->
  p :: ?? ??? r ->
  q :: ?? ??? r ->
  ?? ??? r
| ND_and_intro {?? P Q} :
  ?? ??? P ->
  ?? ??? Q ->
  ?? ??? And P Q
| ND_and_elim {?? P Q R} :
  ?? ??? And P Q ->
  P :: Q :: ?? ??? R ->
  ?? ??? R
| ND_cut {?? P Q} :
  ?? ??? P ->
  P :: ?? ??? Q ->
  ?? ??? Q
| ND_exists_elim {?? p q c} :
  ?? ??? (Exists p) -> fresh c (List.cons p (List.cons q ??)) ->
  (subst_bvar_inner 0 (constant c) p)::?? ??? q ->
  ?? ??? q
| ND_exists_intro {?? p c} :
  ?? ??? (subst_bvar_inner 0 (constant c) p) -> 
  ?? ??? Exists p
| ND_forall_elim {?? p t} :
  ?? ??? (Forall p) -> 
  ?? ??? (quantifier_elim_subst 0 t p)
| ND_forall_intro {?? p c} :
  ?? ??? (subst_bvar_inner 0 (constant c) p) -> 
  fresh c (List.cons p ??) ->
  ?? ??? Forall p
where "?? ??? P" := (deducible ?? P).

Definition proves (fm : Formula) : Prop := deducible List.nil fm.

Hint Unfold GlobalContext LocalContext : typeclass_instances.
Hint Constructors well_typed deducible : core.

Theorem Verum_implies_Verum :
  proves (Implies Verum Verum).
Proof. 
  unfold proves; auto.
Qed.


Definition subcontext (??1 ??2 : list Formula) : Prop :=
  forall P, List.In P ??1 -> List.In P ??2.
  
Definition supcontext (??1 ??2 : list Formula) : Prop :=
  subcontext ??2 ??1.
Infix "???" := subcontext (no associativity, at level 70).
Infix "???" := supcontext (no associativity, at level 70).

Lemma cons_subcontext : forall (?? : list Formula) (P : Formula),
  ?? ??? List.cons P ??.
Proof.
  intros. right. assumption.
Qed.

Lemma subcontext_cons : forall (??1 ??2 : list Formula) (P : Formula),
  P :: ??1 ??? ??2 <-> List.In P ??2 /\ ??1 ??? ??2.
Proof.
  split; intros; repeat split.
  - apply H; left; reflexivity.
  - intros x ?; apply H; right; assumption.
  - destruct H. intro x; destruct 1; subst; auto.
Qed.


Ltac prove_In :=
match goal with
| |- In ?P (?P :: ???) => left; reflexivity
| |- In ?P (?Q :: ???) => right; prove_In
end.
Ltac prove_subcontext :=
match goal with
| |- ?P :: ??? ??? ???' => rewrite subcontext_cons; split;
     [ prove_In | prove_subcontext ]
| |- ??? ??? ??? => reflexivity
| |- ??? ??? ?P :: ???' => rewrite <- (cons_subcontext P ??');
                       prove_subcontext
end.

Import ListNotations.
Open Scope list.

Lemma subcontext_trans : forall (??1 ??2 ??3 : list Formula),
  ??1 ??? ??2 -> ??2 ??? ??3 -> ??1 ??? ??3.
Proof.
  intros. unfold subcontext in H; unfold subcontext in H0; unfold subcontext. auto.
Qed.
  
Lemma subcontext_weaken : forall (??1 ??2 : list Formula) (P : Formula),
  ??1 ??? ??2 -> ??1 ??? P :: ??2.
Proof.
  intros. assert (??2 ??? (List.cons P0 ??2)). apply cons_subcontext.
  apply (subcontext_trans ??1 ??2 (P0 :: ??2)) in H0. assumption. assumption.
Qed.
  
Lemma subcontext_weaken2 : forall (??1 ??2 : list Formula) (P : Formula),
  ??1 ??? ??2 -> P :: ??1 ??? P :: ??2.
Proof.
  intros. assert (??2 ??? (List.cons P0 ??2)). apply cons_subcontext.
  apply subcontext_cons. split; unfold List.In; auto. apply (subcontext_trans ??1 ??2 (P0 :: ??2)).
  assumption. assumption.
Qed.

Lemma subcontext_reflex : forall (?? : list Formula), ?? ??? ??.
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
+ intro ??. red. trivial.
+ intros ????? ????? ?????; unfold subcontext. auto.
Qed.

Global Instance subcontext_cons_proper :
  Proper (eq ==> subcontext ++> subcontext) (@cons Formula).
Proof.
intros P Q [] ??1 ??2 ?. rewrite subcontext_cons; split.
+ left; reflexivity.
+ rewrite H. apply cons_subcontext.
Qed.

Lemma fresh_in_head : forall {c P ??1 ??2},
  (P :: ??1) ??? ??2 ->
  fresh c ??2 -> fresh c P.
Admitted.

(* Suppose [Subcontext ??1 ??2]. If [fresh c ??2], then [fresh c ??1]. *)
Global Instance fresh_cons_proper :
  Proper (eq ++> subcontext --> Basics.impl) fresh.
Proof.
  intros P Q [] ??1 ??2 ?. unfold Basics.flip in H. unfold Basics.impl.
  intros H1.
  unfold fresh; unfold FreshContext; unfold fresh_list.
  induction ??2. auto.
  assert (??2 ??? a :: ??2). apply cons_subcontext.
  assert (??2 ??? ??1).
  apply (subcontext_trans ??2 (a :: ??2) ??1); assumption; assumption.
  apply IH??2 in H2 as IH; split. apply (fresh_in_head H). assumption.
  assumption.
Qed.

Theorem fresh_cons_1 : forall (??1 ??2 : list Formula) (P : Formula) (c : name),
  ??1 ??? ??2 -> fresh c (P :: ??1) -> fresh c (P :: ??2).
Admitted.

Theorem fresh_cons_2 : forall (??1 ??2 : list Formula) (P Q : Formula) (c : name),
  ??1 ??? ??2 -> fresh c (P :: Q :: ??1) -> fresh c (P :: Q :: ??2).
Admitted.
(*
Proof.
  intros. unfold fresh in H0; unfold FreshContext in H0; unfold fresh_list in H0.
  unfold fresh; unfold FreshContext; unfold fresh_list. intuition.
  apply H.
   set (G1 := Q :: ??1). set (G2 := Q :: ??2).
Admitted.
*)

Global Instance ND_context_extension :
  Proper (subcontext ++> eq ==> Basics.impl) deducible.
Proof.
intros ????? ????? ? P Q [] ?. revert ????? H. induction H0; intros.
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
  apply (fresh_cons_2 ?? ????? p q). assumption. apply H. apply IHdeducible2. f_equiv. assumption.
+ apply (ND_exists_intro (p := p) (c := c)); auto.
+ apply (ND_forall_elim (p := p) (t := t)). auto.
+ apply (ND_forall_intro (p := p) (c := c)). auto.
  apply (fresh_cons_1 ?? ????? p). apply H1. apply H.
Qed.

Theorem weakening : forall (??1 ??2 : list Formula) (P : Formula),
  ??1 ??? P ->
  ??1 ??? ??2 ->
  ??2 ??? P.
Proof.
  intros.
  refine (ND_context_extension _ _ _ _ _ eq_refl H).
  assumption.
Qed.

(** * Translation of Soft Types to First-Order Logic 

We now have a mapping [|.|] of soft types, judgements, and related linguistic
constructs, to first-order logic.

For now, this is just a mocked stub.
*)
Class Translatable A :=
  {
    translate: A -> Formula;
  }.
  
Import VectorNotations.
  
Global Instance TranslatableRadix : Translatable Radix := {
  translate (R : Radix) :=
  match R with
  | Ast => Verum
  | Mode n M args => (Atom (P (S n) (String.append "Mode_" M) ((Var (BVar 0))::(Vector.map shift args))))
  end
}.
  
Global Instance TranslatableAttr : Translatable Attribute := {
  translate (attr : Attribute) :=
  match attr with
  | Attr n s args => (Atom (P (S n) (String.append "Attr_" s) ((Var (BVar 0))::(Vector.map shift args))))
  end
}.
  
Global Instance TranslatableAdj : Translatable Adjective := {
  translate (adj : Adjective) :=
  match adj with
  | Pos a => translate a
  | Neg a => Not (translate a)
  end
}.

(* Consider: shift everything by 1, and have [BVar 0] reserved for future
use in translating judgements. *)
Global Instance TranslatableSoftType : Translatable SoftType := {
  translate (T : SoftType) :=
  match T with
  | (adjs, R) => let fix tr_adjs (ads : list Adjective) :=
                     match ads with
                     | List.cons a tl => And (translate a) (tr_adjs tl)
                     | List.nil => Verum
                     end
                     in And (tr_adjs adjs) (translate R)
  end
}.

Global Instance TranslatableJudgementType : Translatable JudgementType := {
  translate (J : JudgementType) := 
  match J with
  | Esti tm Tp => quantifier_elim_subst 0 tm (translate Tp)
  | Subtype T1 T2 => match (translate T1), (translate T2) with
                     | A1, A2 => Forall (Implies A1 A2)
                     end
  | Inhabited T => Exists (translate T)
  | _ => Verum
  end
}.

(** Global definitions are a list of definitions, which are a [LocalContext]
and a [JudgementType]. There may be a clever way to encode this, but I am at
a loss at the moment. Instead I will cheat and use Currying. *)

(*
_         __   _                         _                 __       _ _
\ \      / /__( )_ __ ___     __ _  ___ (_)_ __   __ _    / _|_   _| | |
 \ \ /\ / / _ \/| '__/ _ \   / _` |/ _ \| | '_ \ / _` |  | |_| | | | | |
  \ V  V /  __/ | | |  __/  | (_| | (_) | | | | | (_| |  |  _| |_| | | |
   \_/\_/ \___| |_|  \___|   \__, |\___/|_|_| |_|\__, |  |_|  \__,_|_|_|
                             |___/               |___/
  ____
 / ___|   _ _ __ _ __ _   _
| |  | | | | '__| '__| | | |
| |__| |_| | |  | |  | |_| |
 \____\__,_|_|  |_|   \__, |
                      |___/

*)
Fixpoint translate_antecedent (lc : LocalContext) (j : JudgementType) : Formula :=
match lc with
| List.nil => translate j
| List.cons (_,T) List.nil => Forall (Implies (translate T) (translate j))
| List.cons (_,T) tl => Forall (Implies (translate T) (translate_antecedent tl j))
end.

Definition translate_definition (defn : LocalContext*JudgementType) : Formula :=
match defn with
| (lc, J) => translate_antecedent lc J
end.

Fixpoint translate_gc (gc : GlobalContext) :=
match gc with
| List.nil => Verum
| List.cons d List.nil => translate_definition d
| List.cons d tl => And (translate_definition d) (translate_gc tl)
end.

Global Instance TranslatableGlobalContext : Translatable GlobalContext := {
  translate := translate_gc
}.

Global Instance TranslatableJudgement : Translatable Judgement := {
translate (judge : Judgement) :=
  match judge with
  | (??, ??, j) => Implies (translate ??) (translate_antecedent ?? j)
  end
}.

(** * Main Results

We can now articulate the correctness results. *)

(*

Hint Constructors JudgementType Radix Term Adjective : core.

Print HintDb typeclass_instances.

Hint Constructors JudgementType Radix Term Adjective Predicate Formula : typeclass_instances.
*)

Lemma empty_context_correctness :
  well_typed (List.nil ;; List.nil |- Context) -> proves (translate (List.nil ;; List.nil |- Context)).
Proof. 
  intros; simpl; apply Verum_implies_Verum.
Qed.

Hint Unfold GlobalContext LocalContext : typeclass_instances.
Hint Constructors well_typed deducible : core.
Lemma star_sub_star_correctness :
  forall (?? : GlobalContext) (?? : LocalContext),
  well_typed (?? ;; ?? |- Subtype Star Star) -> proves (translate (?? ;; ?? |- Subtype Star Star)).
Admitted.

Lemma global_weakening : forall (J : JudgementType) (??1 ??2 : GlobalContext) (?? : LocalContext),
  List.incl ??1 ??2 ->
  well_typed (??1 ;; ?? |- J) ->
  well_typed (??2 ;; ?? |- J).
Admitted.

Lemma local_weakening : forall (J : JudgementType) (?? : GlobalContext) (??1 ??2 : LocalContext),
  List.incl ??1 ??2 ->
  well_typed (?? ;; ??1 |- J) ->
  well_typed (?? ;; ??2 |- J).
Admitted.

Lemma proves_true_weakening : forall (J1 J2 : JudgementType) (?? : GlobalContext) (??1 ??2 : LocalContext),
  List.incl ??1 ??2 -> (translate J2 = Verum) ->
  proves (translate (?? ;; ??1 |- J1)) ->
  proves (translate (?? ;; ??2 |- J2)).
Admitted.

Lemma well_typed_contexts : forall (J : JudgementType) (?? : GlobalContext) (?? : LocalContext),
  well_typed (?? ;; ?? |- J) ->
  well_typed (?? ;; ?? |- Context).
Admitted.

Hint Unfold translate_antecedent : core.
Theorem correctness : forall (J : Judgement),
  well_typed J -> proves (translate J).
Proof.
  intros.
  induction H.
  - intros; simpl; apply Verum_implies_Verum. (* ?? ;; ?? |- Context *)
  - intros. simpl. (* ??;; push (x, T) ?? |- Context *)
  (* ... and the rest! *)
Qed.
