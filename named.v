Require Import String.
Require Import List.
Require Import Nat.
Require Import Coq.Vectors.Vector.
Import ListNotations.
Import VectorNotations.
Open Scope string_scope.

Class Eq A :=
  {
    eqb: A -> A -> bool;
  }.
Print Vector.cons.

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

(** *** Terms

A [Term] is either a variable, or an n-ary function. Constants are just nullary functions.
*)

Inductive Term : Type :=
| Var : V -> Term
| Fun : forall (n : nat), name -> Vector.t Term n -> Term.

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

Class Subst A : Type := 
{
  subst : V -> Term -> A -> A
}.

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

Definition term_is_fun (t : Term) : Prop :=
  match t with
  | Fun _ _ _ =>  True
  | _ => False
  end.

(** *** Radix Types

These are "mother types". In full Mizar, this is either a [Mode] or a [Struct] or a set (what we call [Ast]).
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

(** *** Attributes

Attributes may be prepended to types, when registered in an existential cluster. Otherwise, we can create a formula
[Term is Attribute]. *)

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

(** *** Adjectives

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

Definition type_is_named (T : SoftType) (n : name) : Prop :=
  match T with
  | (_, Mode k1 s1 args1) => n = s1
  | _ => False
  end.

Definition mk_mode {n} (M : name) (args : Vector.t Term n) : SoftType :=
  (List.nil, (Mode n M args)).

Definition prefix (a : Adjective) (T : SoftType) : SoftType :=
  match T with
  | (adjs, R) => if List.existsb (fun (adj : Adjective) => eqb a adj) adjs then T else (List.cons a adjs, R)
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

(** *** Judgement Types *)
Definition Decl : Type := V*SoftType.

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

Definition LocalContext := list Decl.

(**
Given a [LocalContext], we can turn it into a vector of variables, to be used as the arguments for
a [Term], [Attribute], or [SoftType] (or whatever).
*)
Fixpoint local_vars (lc : LocalContext) : Vector.t Term (List.length lc) :=
  match lc with
  | List.cons (x,_) tl => (Var x)::(local_vars tl)
  | List.nil => []
  end.


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

Fixpoint gc_contains (Γ : GlobalContext) (def : (LocalContext * JudgementType)) : Prop :=
  match Γ,def with
  | List.cons (lc, J') Γ', (subcontext, J) => ((lc_is_subcontext subcontext lc) /\ J = J') \/ gc_contains Γ' def
  | List.nil, _ => False
  end.

(** * Inference Rules for Soft Types

We can now code up the inference rules for Wiedijk's soft type system inductively. 
*)
Definition Judgement : Type := GlobalContext * LocalContext * JudgementType.

Notation "gc ;; lc |- j" := (gc, lc, j) (at level 80).
Inductive well_typed : Judgement -> Prop :=
| wt_empty_context : well_typed (List.nil ;; List.nil |- Context)
(* TODO: substitution rule for a vector of declarations *)
| wt_subst : forall (Γ : GlobalContext) (Δ : LocalContext) (x : V) (t : Term) (T : SoftType) (J : JudgementType),
  gc_contains Γ ((List.cons (x,T) List.nil), J) ->
  well_typed (Γ ;; Δ |- Esti t T) ->
  well_typed (Γ ;; Δ |- (subst x t Context))
(* TODO: inhabited types produce new local variables *)
| wt_subtype_star_star : forall (Γ : GlobalContext) (Δ : LocalContext),
  well_typed (Γ ;; Δ |- Context) ->
  well_typed (Γ ;; Δ |- Subtype Star Star)
| wt_inhabited_star : forall (Γ : GlobalContext) (Δ : LocalContext),
  well_typed (Γ ;; Δ |- Context) ->
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
  well_typed ((List.app Γ (List.cons (Δ, (Esti (Fun (List.length Δ) f (local_vars Δ)) T)) List.nil)) ;; List.nil |- Context)
| wt_mode_def : forall (Γ : GlobalContext) (Δ : LocalContext) (T : SoftType) (M : name), 
  not (gc_defines_type Γ M) ->
  well_typed (Γ ;; Δ |- Inhabited T) ->  
  well_typed ((List.app Γ 
              (List.cons (Δ, (Subtype (mk_mode M (local_vars Δ)) T))
                (List.cons (Δ, (Inhabited (mk_mode M (local_vars Δ)))) List.nil))) ;; List.nil |- Context)
| wt_attr_def : forall (Γ : GlobalContext) (Δ : LocalContext) (T : SoftType) (alpha : name), 
  not (gc_defines_attr Γ alpha) ->
  well_typed (Γ ;; Δ |- Inhabited T) ->
  well_typed (List.app Γ (List.cons (Δ, HasAttribute (Attr (List.length Δ) alpha (local_vars Δ)) T) List.nil) ;; List.nil |- Context)
  (* Rules governing clusters *)
| wt_cluster_exist : forall (Γ : GlobalContext) (Δ : LocalContext) (T : SoftType) (a : Adjective), 
  well_typed (Γ ;; Δ |- Subtype (prefix a T) T) ->
  well_typed (Γ ;; Δ |- Inhabited T) ->
  well_typed (List.app Γ (List.cons (Δ, (Inhabited (prefix a T))) List.nil) ;; List.nil |- Context)
| wt_cluster_cond : forall (Γ : GlobalContext) (Δ : LocalContext) (T : SoftType) (a1 a2 : list Adjective), 
  well_typed (Γ ;; Δ |- Subtype (prefix_all a1 T) T) ->
  well_typed (Γ ;; Δ |- Subtype (prefix_all a2 T) T) ->
  well_typed (List.app Γ (List.cons (Δ, (Subtype (prefix_all a1 T) (prefix_all a2 T))) List.nil) ;; List.nil |- Context)
| wt_cluster_fun : forall (Γ : GlobalContext) (Δ : LocalContext) (t : Term) (T : SoftType) (a : Adjective), 
  well_typed (Γ ;; Δ |- Esti t T) ->
  well_typed (Γ ;; Δ |- Subtype (prefix a T) T) ->
  well_typed (List.app Γ (List.cons (Δ, (Esti t (prefix a T))) List.nil) ;; List.nil |- Context)
  (* Rules governing redefinitions *)
| D_redef_fun : forall (Γ : GlobalContext) (Δ₁ Δ₂ : LocalContext) (t : Term) (T1 T2 T3 : SoftType), 
  term_is_fun t ->
  well_typed (Γ ;; Δ₂ |- Inhabited T2) ->
  well_typed (Γ ;; Δ₂ |- Subtype T2 T3) ->
  well_typed (Γ ;; (List.app Δ₁ Δ₂) |- Esti (fun_with_locals t Δ₂) T3) ->
  well_typed ((List.app Γ (List.cons ((List.app Δ₁ Δ₂), (Esti (fun_with_locals t Δ₂) T3)) List.nil)) ;; List.nil |- Context)
| D_redef_mode : forall (Γ : GlobalContext) (Δ₁ Δ₂ : LocalContext) (M : Radix) (T1 T2 T3 : SoftType), 
  radix_is_mode M ->
  well_typed (Γ ;; Δ₂ |- Inhabited T2) ->
  well_typed (Γ ;; Δ₂ |- Subtype T2 T3) ->
  well_typed (Γ ;; (List.app Δ₁ Δ₂) |- Subtype (List.nil, (mode_with_locals M Δ₂)) T3) ->
  well_typed ((List.app Γ (List.cons ((List.app Δ₁ Δ₂), (Subtype (List.nil, (mode_with_locals M Δ₂)) T3)) List.nil)) ;; List.nil |- Context).

(** * Natural Deduction

We need to formalize the proof calculus to then prove the correctness of soft type system.

References relevant:

- https://people.compute.dtu.dk/ahfrom/Formalized%20First-Order%20Logic.pdf
- https://hal.archives-ouvertes.fr/hal-03096253
*)

(** ** Predicates

We encode the syntax of a predicate, analogous to [Term], as its arity [n : nat], its [name], and its arguments as a [Vector.t Term].
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

(** ** Formulas

*)
Inductive Formula : Type :=
| Falsum
| Atom : Predicate -> Formula
| Not : Formula -> Formula
| And : Formula -> Formula -> Formula
| Or : Formula -> Formula -> Formula
| Implies : Formula -> Formula -> Formula
| Forall : Formula -> Formula
| Exists : Formula -> Formula.

(**
We would encode $\forall x\exists y P(x,y)$ as [Forall (Exists (Atom (P 2 "P" [BVar 1; BVar 0])))],
using de Bruijn indices.
*)
Check Forall (Exists (Atom (P 2 "P" [Var (BVar 1); Var (BVar 0)]))).


(* TODO: have helper functions like [every "x" <formula>] to produce an [Forall <modified formula>],
and [some "x" <formula>] to produce an [Exists <modified formula>]. *)

(** ** Rules of Natural Deduction *)
Reserved Notation "Γ ⊢ P" (no associativity, at level 61).

Inductive deducible : list Formula -> Formula -> Prop :=
| ND_exfalso_quodlibet {Γ P} :
  Γ ⊢ Falsum ->
  Γ ⊢ P
where "Γ ⊢ P" := (deducible Γ P).

Definition proves (fm : Formula) : Prop := deducible List.nil fm.

Check not.

(** * Translation of Soft Types to First-Order Logic 

We now have a mapping [|.|] of soft types, judgements, and related linguistic constructs, to first-order logic.
For now, this is just a mocked stub.
*)
Class Translatable A :=
  {
    translate: A -> Formula;
  }.

Global Instance TranslatableJudgement : Translatable Judgement := {
  translate (J : Judgement) := Falsum
}.

(** * Main Results

We can now articulate the correctness results. *)
Theorem correctness : forall (Γ : GlobalContext) (Δ : LocalContext) (J : JudgementType),
  well_typed (Γ ;; Δ |- J) -> proves (translate (Γ ;; Δ |- J)).
