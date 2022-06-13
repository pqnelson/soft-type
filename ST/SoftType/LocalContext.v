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
From ST Require Export Logic.V Logic.Term.
From ST Require Export SoftType.Radix SoftType.Attribute SoftType.Adjective SoftType.SoftType.
Import ListNotations.
Import VectorNotations.
Open Scope string_scope.

(** ** Local Contexts

A local context is just a finite list of [Decl] (declaration of variables and
their types). We will turn this into arguments for a [Term] (or [Attribute], 
or...), so we have a [local_vars] helper function to accomodate this.


TODO: I think this is not quite right. Using locally nameless terms, a 
declaration simplifies to just a [SoftType]. Then a [LocalContext] is just
a list of [Decl].

TODO 2: Think hard about whether lifting is necessary for local contexts.
*)
Definition Decl : Type := SoftType.
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

Definition evars_local_declaration (d : Decl) :=
  match d with
  | T => (list_evars T)
  end.

Global Instance EnumerateEVarsLocalContext : EnumerateEVars LocalContext := {
list_evars lc := List.fold_left (fun l' => fun (d : Decl) => 
  insert_merge (evars_local_declaration d) l')
 lc []%list
}.

Theorem list_evars_local_context_sorted : forall (lc : LocalContext),
  sorted (list_evars lc).
Proof. intros.
  unfold list_evars; unfold EnumerateEVarsLocalContext.
  apply insert_merge_list_fold_sorted. apply sorted_nil.
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