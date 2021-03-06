Require Import String.
Require Import Nat.
Require Import Coq.Vectors.Vector.
Require Export Coq.Arith.Compare_dec.
Require Import Coq.Logic.PropExtensionality.
Require Export List.
Require Export RelationClasses.
Require Export Morphisms.
Import ListNotations.
Open Scope string_scope.
From ST Require Import EVarsScratchwork.
From ST Require Export ST.SoftType.
From ST Require Import Logic VariadicQuantifiers.
Import VectorNotations.
(** * Translation of Soft Types to First-Order Logic 

We now have a mapping [|.|] of soft types, judgements, and related linguistic
constructs, to first-order logic.
*)
Class Translatable A :=
  {
    translate: A -> Formula;
  }.
  
Import VectorNotations.

(**
When translating a [Radix], it will either be [Ast] --- in which case it translates
to [Verum] --- or else it will be a [Mode] type. In this case, we default to
the case where it will be tossed into a quantifier, with its leading argument
bound to that quantifier. For this reason, we make the first slot [BVar 0],
and we must [shift] the remaining arguments.
*)
Global Instance TranslatableRadix : Translatable Radix := {
  translate (R : Radix) :=
  match R with
  | Ast => Verum
  | Mode n M args => (Atom (P (S n) (String.append "Mode_" M) ((Var (BVar 0))::(Vector.map shift args))))
  end
}.

(* Unit Tests *)
Example translate_radix_ast :
  translate (Ast) = Verum.
Proof. simpl; auto. Qed.

Example translate_radix_mode_1 :
  translate (Mode 3 "MyMode" [(Var (FVar "x")); (constant "c"); (Var (BVar 3))])
  = Atom (P 4 "Mode_MyMode" [(Var (BVar 0)); (Var (FVar "x")); (constant "c"); (Var (BVar 4))]).
Proof. unfold constant; simpl; auto. Qed.

(** The same caveat applies to attributes, namely its first argument will be
[BVar 0], and we must shift the remaining arguments. *)
Global Instance TranslatableAttr : Translatable Attribute := {
  translate (attr : Attribute) :=
  match attr with
  | Attr n s args => (Atom (P (S n) (String.append "Attr_" s) ((Var (BVar 0))::(Vector.map shift args))))
  end
}.

(* Unit Tests *)
Example translate_attr_1 :
  translate (Attr 3 "MyMode" [(Var (FVar "x")); (constant "c"); (Var (BVar 3))])
  = Atom (P 4 "Attr_MyMode" [(Var (BVar 0)); (Var (FVar "x")); (constant "c"); (Var (BVar 4))]).
Proof. unfold constant; simpl; auto. Qed.

(** Adjectives can be translated simply thanks to the [Attribute] doing the
heavy lifting. Negated adjectives produce simply the negated [Attribute] translation. *)
Global Instance TranslatableAdj : Translatable Adjective := {
  translate (adj : Adjective) :=
  match adj with
  | Pos a => translate a
  | Neg a => Not (translate a)
  end
}.

(* Unit Tests *)
Example translate_adj_1 :
  translate (Pos (Attr 3 "SimplyConnected" [(Var (FVar "x")); (constant "c"); (Var (BVar 3))]))
  = Atom (P 4 "Attr_SimplyConnected" [(Var (BVar 0)); (Var (FVar "x")); (constant "c"); (Var (BVar 4))]).
Proof. unfold constant; simpl; auto. Qed.

Example translate_adj_2 :
  translate (Neg (Attr 3 "SimplyConnected" [(Var (FVar "x")); (constant "c"); (Var (BVar 3))]))
  = Not (Atom (P 4 "Attr_SimplyConnected" [(Var (BVar 0)); (Var (FVar "x")); (constant "c"); (Var (BVar 4))])).
Proof. unfold constant; simpl; auto. Qed.

(* Helper functions for translating soft types. *)
Definition null {A} (l : list A) : bool :=
match l with
| []%list => true
| _ => false
end.

Fixpoint right_and (a b : Formula) : Formula :=
match a with
| And a1 a2 => And a1 (right_and a2 b)
| _ => And a b
end.

Require Import Coq.Bool.Bool.

Lemma right_and_def : forall (a b : Formula),
  false = is_and a -> right_and a b = And a b.
Proof.
  intros; simpl; auto. unfold right_and.
  destruct a.
  simpl; auto. simpl; auto.
  contradict H; simpl; auto.
  simpl; auto. simpl; auto. simpl; auto.
Qed.

(* Consider: shift everything by 1, and have [BVar 0] reserved for future
use in translating judgements. *)
(* Convention: 
translate (ad::tl, R) = And (translate ad)
                            (translate (tl, R)).
*)
Global Instance TranslatableSoftType : Translatable SoftType := {
  translate (T : SoftType) :=
  match T with
  | (List.nil, R) => translate R
  | (adjs, R) => 
    let fix tr_adjs (ads : list Adjective) :=
    match ads with
    | (a::tl)%list => And (translate a) (tr_adjs tl)
    | List.nil => (translate R)
    end
    in tr_adjs adjs
  end
}.

(* Unit Tests *)
Example translate_soft_type_1 :
let st : SoftType := ([Neg (Attr 3 "SimplyConnected" [(Var (FVar "x")); (constant "c"); 
                       (Var (BVar 3))]%vector);
                       Pos (Attr 1 "Smooth" [(Var (FVar "y"))]%vector)]%list,
(Mode 3 "Manifold" [(Var (FVar "x")); (constant "c"); (Var (BVar 3))]))
in (translate st)
= And (translate (Neg (Attr 3 "SimplyConnected" [(Var (FVar "x")); (constant "c"); (Var (BVar 3))])))
      (And (translate (Pos (Attr 1 "Smooth" [(Var (FVar "y"))])))
           (translate (Mode 3 "Manifold" [(Var (FVar "x")); (constant "c"); (Var (BVar 3))]))).
Proof. unfold constant; simpl; auto. Qed.

Example translate_soft_type_2 :
let st : SoftType := ([Pos (Attr 0 "Complex" []%vector);
                       Pos (Attr 0 "Ricci-flat" []%vector);
                       Neg (Attr 3 "SimplyConnected" [(Var (FVar "x")); (constant "c"); (Var (BVar 3))]%vector);
                       Pos (Attr 1 "Smooth" [(Var (FVar "y"))]%vector)]%list,
(Mode 3 "Manifold" [(Var (FVar "x")); (constant "c"); (Var (BVar 3))]))
in (translate st)
= And (translate (Pos (Attr 0 "Complex" []%vector)))
      (And (translate (Pos (Attr 0 "Ricci-flat" []%vector)))
           (And (translate (Neg (Attr 3 "SimplyConnected" [(Var (FVar "x")); (constant "c"); (Var (BVar 3))])))
                (And (translate (Pos (Attr 1 "Smooth" [(Var (FVar "y"))])))
                     (translate (Mode 3 "Manifold" [(Var (FVar "x")); (constant "c"); (Var (BVar 3))]))))).
Proof. unfold constant; simpl; auto. Qed.

Lemma translate_prefixed_soft_type : forall (a : Adjective) (adjs : list Adjective) (R : Radix) (T : SoftType),
  T = (adjs,R) ->
  translate (prefix a T) = translate ((a::adjs)%list, R).
Proof.
  intros. rewrite H; unfold prefix; reflexivity.
Qed.

(* The [capture_free_subst] usage here requires shifting, then unshifting,
the bound variables. Otherwise, we end up with accidentally capturing the
wrong variables later on. This is due to the conventions adopted earlier on,
to make the first slot [BVar 0] and to shift the remaining arguments. It's
precisely what is needed for the [Subtype] and [Inhabited] judgement types,
but for [Esti] we must "undo" this decision.

We are assuming the translation of any [SoftType] is a conjunction of
predicates whose first argument corresponds to a [Term]. This is the whole
design of soft type systems, after all. *)
Global Instance TranslatableJudgementType : Translatable JudgementType := {
  translate (J : JudgementType) := 
  match J with
  | Esti tm Tp => unshift (capture_free_subst 0 (shift tm) (translate Tp))
  | Subtype T1 T2 => match (translate T1), (translate T2) with
                     | A1, A2 => Forall (Implies A1 A2)
                     end
  | Inhabited T => Exists (translate T)
  | _ => Verum
  end
}.

(* Unit Tests *)
Example translate_judgement_1 :
translate (Esti (Fun "Sphere" [(constant "n")])
  ([Pos (Attr 0 "Smooth" []%vector); (Pos (Attr 1 "-dimensional" [(constant "n")]%vector))]%list, (Mode 1 "Manifold" [(constant "REAL")])))
= let sphere : Term := (Fun "Sphere" [(constant "n")])
  in And (Atom (P 1 "Attr_Smooth" [ sphere ]))
         (And (Atom (P 2 "Attr_-dimensional" [sphere; Fun "n" []]))
              (Atom (P 2 "Mode_Manifold" [sphere; Fun "REAL" []]))).
Proof. cbv; auto. Qed.

Example translate_judgement_2 :
translate (Esti (Fun "FrattiniSubgroup" [(Var (BVar 0))])
  ([Pos (Attr 1 "-local" [(Var (BVar 0))]%vector); 
   (Pos (Attr 1 "-parabolic" [(constant "n")]%vector))]%list, 
   (Mode 2 "Subgroup" [(constant "G"); Var (BVar 0)])))
= let G : Term := (Fun "FrattiniSubgroup" [(Var (BVar 0))])
  in And (Atom (P 2 "Attr_-local" [ G; Var (BVar 0) ]))
         (And (Atom (P 2 "Attr_-parabolic" [G; (constant "n")]))
              (Atom (P 3 "Mode_Subgroup" [G; (constant "G"); Var (BVar 0)]))).
Proof. cbv. auto. Qed.

Example translate_judgement_3 :
translate (Inhabited
  ([Pos (Attr 1 "-local" [(Var (BVar 0))]%vector); 
   (Pos (Attr 1 "-parabolic" [(constant "n")]%vector))]%list, 
   (Mode 2 "Subgroup" [(constant "G"); Var (BVar 1)])))
= let x : Term := (Var (BVar 0))
  in 
Exists (And (Atom (P 2 "Attr_-local" [ x; Var (BVar 1) ]))
            (And (Atom (P 2 "Attr_-parabolic" [x; (constant "n")]))
                 (Atom (P 3 "Mode_Subgroup" [x; (constant "G"); Var (BVar 2)])))).
Proof. cbv. auto. Qed.

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
Fixpoint naive_curried_translate_antecedent (lc : LocalContext) (j : JudgementType) : Formula :=
match lc with
| List.nil => translate j
| List.cons T tl => if null tl then Forall (Implies (translate T) (translate j))
                    else Forall (Implies (translate T) (naive_curried_translate_antecedent tl j))
end.

Definition curried_translate_antecedent (lc : LocalContext) (j : JudgementType) : Formula :=
match lc with
| List.nil => translate j
| List.cons T tl => List.fold_left (fun a => fun b => Forall (Implies b a))
                     (List.rev (map translate lc)) (translate j)
end.

Theorem curried_translate_equiv : forall (lc : LocalContext) (j : JudgementType),
  curried_translate_antecedent lc j = naive_curried_translate_antecedent lc j.
Proof.
  intros.
  induction lc.
  - simpl; auto.
  - destruct lc.
  + simpl; auto.
  + assert(naive_curried_translate_antecedent (a :: s ::lc)%list j
          = Forall (Implies (translate a) (naive_curried_translate_antecedent (s ::lc)%list j))). {
      simpl; auto.
    }
    rewrite H. rewrite <- IHlc. 
    assert (curried_translate_antecedent (a :: s :: lc)%list j
            = List.fold_left (fun a => fun b => Forall (Implies b a))
                     (List.rev (map translate (a :: s :: lc)%list)) (translate j)). {
      unfold curried_translate_antecedent; reflexivity.

    }
    assert(List.fold_left (fun a => fun b => Forall (Implies b a))
    (List.rev (map translate (a::(s :: lc))%list)) (translate j)
    = List.fold_left (fun a => fun b => Forall (Implies b a))
    (List.rev (((translate a) :: ((translate s) :: (map translate lc)))%list)) (translate j)). {
      simpl; auto.
    }
    assert (List.fold_left (fun a => fun b => Forall (Implies b a))
    (List.rev (((translate a) :: ((translate s) :: (map translate lc)))%list)) (translate j) = 
    List.fold_left (fun a => fun b => Forall (Implies b a))
    ((List.rev ((translate s) :: (map translate lc)) ++ [translate a])%list) (translate j)). {
      simpl; auto.
    }
    assert (List.fold_left (fun a => fun b => Forall (Implies b a))
    (List.rev ((translate s) :: (map translate lc)) ++ [translate a])%list (translate j)
    = List.fold_left (fun a => fun b => Forall (Implies b a))
    (List.rev (([translate a] ++ ((translate s) :: (map translate lc)))%list)) (translate j)). {
      simpl; auto.
    }
    assert (fold_left (fun a b : Formula => Forall (Implies b a))
       (rev ([translate a] ++ translate s :: map translate lc))
       (translate j)
    = fold_left (fun a b : Formula => Forall (Implies b a))
       ((rev (translate s :: map translate lc)) ++ [translate a])
       (translate j)). {
      simpl; auto.
    }
    assert (fold_left (fun a b : Formula => Forall (Implies b a))
       ((rev (translate s :: map translate lc)) ++ [translate a])
       (translate j)
    = fold_left (fun a b : Formula => Forall (Implies b a))
      [translate a]%list (fold_left (fun a b : Formula => Forall (Implies b a))
                          (rev (translate s :: map translate lc))
                          (translate j))). {
      apply (List.fold_left_app (fun a b : Formula => Forall (Implies b a))). 
    }
    rewrite H5 in H4. rewrite H4 in H3.
    rewrite H3 in H2. rewrite H2 in H1. rewrite H1 in H0. assumption.
Qed.

Example curried_translate_antecedent_ex2 : 
(curried_translate_antecedent [(mk_mode "T1" []%vector) ; (mk_mode "T2" [(Var (BVar 0))]%vector)]%list
(Esti (Fun "f" [(Var (BVar 1));(Var (BVar 0))]) (mk_mode "T3" [(Var (BVar 0));(Var (BVar 1))]%vector)))
(* Expected: *)
= Forall (Implies (Atom (P 1 "Mode_T1" [Var (BVar 0)]))
                  (Forall (Implies (Atom (P 2 "Mode_T2" [Var (BVar 0); Var (BVar 1)]))
                                   (Atom (P 3 "Mode_T3" [Fun "f" [Var (BVar 1); Var (BVar 0)]; Var (BVar 0); Var (BVar 1)]))))).
Proof. simpl; auto. Qed.


(* Translate [[(x : T1, y : T2(x))](f(x,y) : T3(y,x))]. *)
(* Expected: Forall x (Forall y (|T1|(x) /\ |T2|(y,x) -> |T3|(f(x,y), y, x)))
             Forall x, |T1|(x) -> Forall y |T2|(y,x) -> |T3|(f(x,y), y, x)
Or namelessly: Forall (Forall (|T1|(1) /\ |T2|(0,1) -> |T3|(f(1,0), 0,1))). *)
Example curried_translate_antecedent_ex1 : 
(curried_translate_antecedent [(mk_mode "T1" []%vector) ; (mk_mode "T2" [(Var (BVar 0))]%vector)]%list
(Esti (Fun "f" [(Var (BVar 1));(Var (BVar 0))]) (mk_mode "T3" [(Var (BVar 0));(Var (BVar 1))]%vector)))
(* Expected: *)
= Forall (Implies (Atom (P 1 "Mode_T1" [Var (BVar 0)]))
                  (Forall (Implies (Atom (P 2 "Mode_T2" [Var (BVar 0); Var (BVar 1)]))
                                   (Atom (P 3 "Mode_T3" [Fun "f" [Var (BVar 1); Var (BVar 0)]; Var (BVar 0); Var (BVar 1)]))))).
Proof. simpl; auto. Qed.

Example curried_translate_antecedent_ex23 :
let field_mode := mk_mode "Field" []%vector
in let vector_space_mode := mk_mode "VectorSpace" [(Var (BVar 0))]%vector
in let lie_algebra_mode := mk_mode "LieAlgebra" [(Var (BVar 0)); (Var (BVar 1))]%vector
in let affine_lie_algebra_mode := mk_mode "AffineLieAlgebra" [(Var (BVar 2)); (Var (BVar 0)); (Var (BVar 1))]%vector
in (curried_translate_antecedent
    [field_mode ; vector_space_mode ; lie_algebra_mode ]%list
    (Esti (Fun "f" [(Var (BVar 1));(Var (BVar 0))]) affine_lie_algebra_mode))
= Forall (Implies (translate field_mode)
                  (Forall 
                    (Implies (translate vector_space_mode)
                             (Forall
                              (Implies (translate lie_algebra_mode)
                                       (translate (Esti (Fun "f" [(Var (BVar 1));(Var (BVar 0))]) affine_lie_algebra_mode))))))).
Proof. simpl; auto. Qed.

(** The uncurried version is preferable for proving properties
of the translation process. For example, we will take advantage of the
fact that a large class of well-typed derivations translate to a trivial
derivation of the form [Every n (Implies p Verum)]. It is a nightmare
to prove this using the curried version. *)

Definition right_conjoin_many (h : Formula) (tl : list Formula) : Formula :=
  List.fold_left (fun current => fun next => (right_and (shift current) next))
    tl h.

(* List.fold_left conventions are so weird, I better have a smoke check. *)
Example right_conjoin_many_ex1 :
  (let A := Atom (P 1 "A" [(Var (BVar 0))])
in let B := Atom (P 2 "B" [(Var (BVar 0));(Var (BVar 1))])
in let C := Atom (P 3 "C" [(Var (BVar 0));(Var (BVar 1));(Var (BVar 2))])
in let D := Atom (P 3 "D" [(Var (BVar 0));(Var (BVar 1));(Var (BVar 2))])
in right_conjoin_many A [B;C;D]%list)
= And (Atom (P 1 "A" [Var (BVar 3)]))
      (And (Atom (P 2 "B" [Var (BVar 2); Var (BVar 3)]))
           (And (Atom (P 3 "C" [Var (BVar 1); Var (BVar 2); Var (BVar 3)]))
                (Atom (P 3 "D" [Var (BVar 0); Var (BVar 1); Var (BVar 2)])))).
Proof. simpl; auto. Qed.

Lemma right_conjoin_many_nil : forall (h t : Formula) (tl : list Formula),
  right_conjoin_many h []%list = h.
Proof. intro; simpl; auto.  Qed.

Theorem right_conjoin_many_step : forall (fm h : Formula) (l : list Formula),
  right_conjoin_many fm (h::l)%list
  = right_conjoin_many (right_and (shift fm) h) l.
Proof.
  intros.
  simpl; auto.
Qed.

Definition uncurried_translate_antecedent (lc : LocalContext) (j : JudgementType) : Formula :=
match lc with
| List.nil => translate j
| (h::tl)%list => Every (length lc) (Implies (right_conjoin_many (translate h) (List.map translate tl))
                                             (translate j))
end.

Example uncurried_translate_antecedent_ex1 : 
(uncurried_translate_antecedent [(mk_mode "T1" []%vector) ; (mk_mode "T2" [(Var (BVar 0))]%vector)]%list
(Esti (Fun "f" [(Var (BVar 1));(Var (BVar 0))]) (mk_mode "T3" [(Var (BVar 0));(Var (BVar 1))]%vector)))
= Every 2 (Implies (And (Atom (P 1 "Mode_T1" [Var (BVar 1)]))
                        (Atom (P 2 "Mode_T2" [Var (BVar 0); Var (BVar 1)])))
                   (Atom (P 3 "Mode_T3" [Fun "f" [Var (BVar 1); Var (BVar 0)]; Var (BVar 0); Var (BVar 1)]))).
Proof. simpl; auto. Qed.

Example uncurried_translate_antecedent_ex2 :
let field_mode := mk_mode "Field" []%vector
in let vector_space_mode := mk_mode "VectorSpace" [(Var (BVar 0))]%vector
in let lie_algebra_mode := mk_mode "LieAlgebra" [(Var (BVar 0)); (Var (BVar 1))]%vector
in let affine_lie_algebra_mode := mk_mode "AffineLieAlgebra" [(Var (BVar 2)); (Var (BVar 0)); (Var (BVar 1))]%vector
in (uncurried_translate_antecedent
    [field_mode ; vector_space_mode ; lie_algebra_mode ]%list
    (Esti (Fun "f" [(Var (BVar 1));(Var (BVar 0))]) affine_lie_algebra_mode))
= Every 3 (Implies (And (lift 0 2 (translate field_mode))
                        (And (lift 0 1 (translate vector_space_mode))
                             (translate lie_algebra_mode)))
                   (translate (Esti (Fun "f" [(Var (BVar 1));(Var (BVar 0))]) affine_lie_algebra_mode))).
Proof. simpl; auto. Qed.

Lemma uncurried_translate_antecedent_structure :
  forall (lc : LocalContext) (j : JudgementType),
  lc <> []%list ->
  exists (A : Formula), 
  uncurried_translate_antecedent lc j
  = Every (length lc)
          (Implies A (translate j)).
Proof.
  intros. induction lc.
  - contradict H. reflexivity.
  - destruct lc.
  + set (A := (right_conjoin_many (translate a) (List.map translate []%list))).
    exists A. simpl; auto.
  + intros. set (A := (right_conjoin_many (translate a) (List.map translate (s::lc)%list))).
    exists A. simpl; auto.
Qed.

Lemma uncurried_translate_antecedent_ind :
forall (a h : SoftType) (tl : LocalContext) (j : JudgementType),
uncurried_translate_antecedent (a :: h :: tl)%list j
= Every (length (a :: h :: tl)%list) 
  (Implies (right_conjoin_many (right_and (shift (translate a)) (translate h)) (List.map translate tl))
           (translate j)).
Proof.
  intros. simpl; auto.
Qed.

Lemma uncurried_translate_antecedent_implies_curried {??} :
  forall (lc : LocalContext) (j : JudgementType),
  uncurried_translate_antecedent lc j :: ??
  ??? curried_translate_antecedent lc j.
Proof.  intros. 
induction lc.
  - assert (uncurried_translate_antecedent []%list j = translate j). { simpl; auto. }
    rewrite H.
    assert (curried_translate_antecedent []%list j = translate j). { simpl; auto. }
    rewrite H0. apply ND_assume. prove_In.
  - unfold curried_translate_antecedent.
    unfold uncurried_translate_antecedent.
    assert (fold_left (fun a0 b : Formula => Forall (Implies b a0))
                      (rev (map translate (a :: lc)))
                      (translate j)
            = fold_left (fun a0 b : Formula => Forall (Implies b a0))
                        [(translate a)]
                        (fold_left (fun a0 b : Formula => Forall (Implies b a0))
                                   (rev (map translate lc))
                                   (translate j))). {
      assert (fold_left (fun a0 b : Formula => Forall (Implies b a0))
                        (rev (map translate (a :: lc)))
                        (translate j)
              = fold_left (fun a0 b : Formula => Forall (Implies b a0))
                          ((rev (map translate lc)) ++ [(translate a)])
                          (translate j)). {
        simpl; auto.
      } rewrite H. apply fold_left_app.
    } rewrite H. destruct lc.
    + assert ((map translate []) = []%list). { simpl; auto. }
      unfold right_conjoin_many. unfold map. unfold rev.
      assert ((fold_left
       (fun a0 b : Formula =>
        Forall (Implies b a0)) [] 
       (translate j)) = translate j). { simpl; auto. }
      rewrite H1. unfold fold_left. unfold length; unfold Every.
      apply ND_assume; prove_In.
    + assert (fold_left (fun a0 b : Formula => Forall (Implies b a0)) [translate a]
              (fold_left (fun a0 b : Formula => Forall (Implies b a0))
                          (rev (map translate (s :: lc))) (translate j)) 
            = Forall (Implies (translate a)
                             (List.fold_left (fun a0 b : Formula => Forall (Implies b a0))
                                             (rev (map translate (s :: lc)))  (translate j)))). {
        simpl; auto.
      } rewrite H0.
Admitted.

Lemma curried_translate_antecedent_implies_uncurried {??} :
  forall (lc : LocalContext) (j : JudgementType),
  curried_translate_antecedent lc j :: ??
  ??? uncurried_translate_antecedent lc j.
Admitted.

Theorem translate_antecedent_equiv {??} :
  forall (lc : LocalContext) (j : JudgementType),
  ?? ??? Iff (uncurried_translate_antecedent lc j)
          (curried_translate_antecedent lc j).
Proof.
  intros. apply ND_Iff_intro.
  - apply uncurried_translate_antecedent_implies_curried.
  - apply curried_translate_antecedent_implies_uncurried.
Qed.

Definition translate_antecedent := uncurried_translate_antecedent.

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

Theorem provable_body_translations_provable :
  forall (judgement : Judgement),
  proves (translate (Judgement_body judgement)) -> proves (translate judgement).
Proof.
  intros. destruct judgement as [[?? ??] j]. unfold Judgement_body in H.
  unfold translate; unfold TranslatableJudgement. apply ND_imp_i2.
  destruct ?? as [|d ??'].
  - unfold translate_antecedent; unfold uncurried_translate_antecedent.
    apply (@weakening [] [translate ??]). assumption. apply empty_subcontext.
  - set (?? := (d::??')%list).
    assert (?? <> []%list). { discriminate. }
    apply (@uncurried_translate_antecedent_structure ?? j) in H0. 
    unfold translate_antecedent. destruct H0 as [A].
    rewrite H0.
    apply (provable_antecedent_result (?? := List.nil) (length ??) (translate ??) A) in H as H1.
    assumption.
Qed.

Corollary vacuous_translations_provable :
  forall (judgement : Judgement),
  Verum = translate (Judgement_body judgement) -> proves (translate judgement).
Proof.
  intros.
  apply provable_body_translations_provable.
  rewrite <- H. apply ND_True_intro.
Qed.

(*
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
*)

Corollary correct_contexts_are_trivial : forall (gc : GlobalContext) (lc : LocalContext),
  proves (translate (gc, lc, CorrectContext)).
Proof.
  intros.
  set (j := (gc ;; lc |- CorrectContext)).
  assert (Judgement_body j = CorrectContext). simpl; auto.
  assert (translate CorrectContext = Verum). simpl; auto.
  apply vacuous_translations_provable. symmetry; assumption.
Qed.

Corollary has_attributes_are_trivial : forall (gc : GlobalContext) (lc : LocalContext) a T,
  proves (translate (gc, lc, HasAttribute a T)).
Proof.
  intros.
  set (j := (gc ;; lc |- HasAttribute a T)).
  assert (Judgement_body j = HasAttribute a T). simpl; auto.
  assert (translate (HasAttribute a T) = Verum). simpl; auto.
  apply vacuous_translations_provable. symmetry; assumption.
Qed.

(**
In effect, we only need to prove correctness for the translations of
judgement types  [Esti tm Tp], [Subtype T1 T2], and [Inhabited T].
*)
(** * Main Results

We can now articulate the correctness results. *)
(* Tedious proof by induction, sigh *)
Theorem global_context_to_context : forall (?? : GlobalContext) (?? : LocalContext) (J : JudgementType),
  (proves (translate (??;; ?? |- J))) <-> ((map translate_definition ??) ??? (translate_antecedent ?? J)).
Proof. intro.
  induction ?? as [ | h ??'].
  - unfold map. unfold translate; unfold TranslatableJudgement; unfold translate;
    unfold TranslatableGlobalContext; unfold translate_gc. split.
    + intros.
      apply (ND_imp_e (p := Verum)) in H. assumption. apply ND_True_intro.
    + intros. apply ND_imp_i2. apply (@weakening []%list [Verum]%list) in H.
      assumption. apply empty_subcontext.
  - intros.
    split.
    + assert (proves (translate (??';; ?? |- J)) ->
       map translate_definition ??' ??? translate_antecedent ?? J). {
        apply (IH??' ?? J).
      }
      destruct ??' as [ | s ??''].
 ++ unfold translate; unfold TranslatableJudgement; unfold translate;
    unfold TranslatableGlobalContext; unfold translate_gc. intros.
    apply (@weakening []%list [(translate_definition h)]%list) in H0.
    unfold map. apply (ND_imp_e (p := translate_definition h)) in H0.
    assumption. apply ND_assume; prove_In. apply empty_subcontext.
 ++ intros.
    assert (translate ((h :: s :: ??'')%list;; ?? |- J) =
            Implies (And (translate_definition  h) (translate_gc (s :: ??'')%list))
                    (translate_antecedent ?? J)). {
      unfold translate; unfold TranslatableJudgement; unfold translate;
      unfold TranslatableGlobalContext.
      assert (translate_gc (h :: s ::  ??'')%list = And (translate_definition h) (translate_gc (s :: ??'')%list)). {
        unfold translate_gc. auto.
      }
      auto.
    }
    fold GlobalContext in H0; fold GlobalContext in H1.
    rewrite H1 in H0. apply ND_curry in H0 as H2.
Admitted.

Lemma explicit_uncurried_translate_antecedent_structure :
  forall (T : SoftType) (lc : LocalContext) (j : JudgementType) (A : Formula),
  A = (right_conjoin_many (translate T) (List.map translate lc)) ->
  uncurried_translate_antecedent (T::lc)%list j
  = Every (length (T::lc)%list)
          (Implies A (translate j)).
Proof.
  intros. destruct lc.
  + assert (A = translate T). { unfold translate in H.
      assert (map (let (translate) := TranslatableSoftType in
          translate) [] = []%list). { simpl; auto. }
      rewrite H0 in H. clear H0.
      unfold right_conjoin_many in H. auto.
    } unfold uncurried_translate_antecedent. rewrite <- H. reflexivity.
  + unfold uncurried_translate_antecedent. rewrite H. reflexivity.
Qed.

Lemma hamburger_helper : forall (J1 J2 J3 : JudgementType) (?? : GlobalContext) (?? : LocalContext),
  proves (Implies (translate J1) (Implies (translate J2) (translate J3))) ->
  proves (translate (??;; ?? |- J1)) ->
  proves (translate (??;; ?? |- J2)) ->
  proves (translate (??;; ?? |- J3)).
Proof.
  intros.
  rewrite global_context_to_context; rewrite global_context_to_context in H0; rewrite global_context_to_context in H1.
  destruct ?? as [|s ??'].
  - assert (translate_antecedent []%list J1 = translate J1). { simpl; auto. }
    rewrite H2 in H0. clear H2.
    assert (translate_antecedent []%list J2 = translate J2). { simpl; auto. }
    rewrite H2 in H1. clear H2.
    assert (translate_antecedent []%list J3 = translate J3). { simpl; auto. }
    rewrite H2. clear H2.
    apply (@weakening []%list (map translate_definition ??)) in H as H2. 2: apply empty_subcontext.
    apply (ND_imp_e (p := translate J1)) in H2.
    apply (ND_imp_e (p := translate J2)) in H2.
    assumption. assumption. assumption.
  - set (?? := (s::??')%list). fold LocalContext in ??. fold ?? in H0; fold ?? in H1.
    assert (?? <> []%list). { discriminate. }
    set (A := (right_conjoin_many (translate s) (List.map translate ??'))).
    
    Check (explicit_uncurried_translate_antecedent_structure s ??' J1 A).
    assert (uncurried_translate_antecedent (s :: ??')%list J1 = Every (Datatypes.length (s :: ??')) (Implies A (translate J1))). {
      apply (explicit_uncurried_translate_antecedent_structure s ??' J1 A). auto.
    } unfold translate_antecedent in H0. fold ?? in H3. rewrite H3 in H0. clear H3.
    assert (uncurried_translate_antecedent (s :: ??')%list J2 = Every (Datatypes.length (s :: ??')) (Implies A (translate J2))). {
      apply (explicit_uncurried_translate_antecedent_structure s ??' J2 A). auto.
    } unfold translate_antecedent in H1; fold ?? in H3. rewrite H3 in H1; clear H3.
    assert (uncurried_translate_antecedent (s :: ??')%list J3 = Every (Datatypes.length (s :: ??')) (Implies A (translate J3))). {
      apply (explicit_uncurried_translate_antecedent_structure s ??' J3 A). auto.
    } unfold translate_antecedent; fold ?? in H3. rewrite H3; clear H3.
    apply (@weakening []%list (map translate_definition ??)) in H as H3. 2: apply empty_subcontext.
    apply (variadic_transport (m := length ??) (q := translate J1) (r := Implies (translate J2) (translate J3)) (A := A)) in H3 as H4. 
    2: assumption.
    apply (variadic_modus_ponens (m := length ??) (p := translate J2) (q := translate J3) (a := A)) in H4 as H5. 
    assumption. assumption.
Qed.

Lemma assume_correctness : forall (?? : GlobalContext) (?? : LocalContext) (J : JudgementType),
  gc_contains ?? (??, J) -> proves (translate (??;; ?? |- J)).
Proof.
  intros.
  apply global_context_to_context.
  assert (List.In (translate_definition (??, J)) (map translate_definition ??)). {
    unfold gc_contains in H. apply List.in_map. assumption.
  }
  apply ND_assume in H0.
  assumption.
Qed.

Lemma empty_context_correctness :
  well_typed (List.nil ;; List.nil |- CorrectContext) -> proves (translate (List.nil ;; List.nil |- CorrectContext)).
Proof. 
  intros; simpl; apply Verum_implies_Verum.
Qed.

(* XXX TODO: need to replace [t] with [iter_tlift (something) 0 t].

Why? Because it should be [proves (Implies (translate ??) (capture_free_subst t 0 (translate_antecedent ?? J))]. *)
(* XXX XXX XXX: this rule of inference is incorrect!

We should have the conclusion be:

[translate (??;; (some_kind_of_substitution t ??) |- subst (BVar (length ??)) t J)]

Because what we're really doing is considering:

[?? ??? Forall T (Every m (Implies A (translate J))) ->
 ?? ??? Every m (translate (Esti t T)) ->
 ?? ??? capture_free_subst 0 t (Every m (Implies A (translate J)))]

The translation of the [?? : LocalContext] (which we denote by [A]) may depend
on the variable bound to the leading [Forall T]. And in *that* case, we need
to substitute [t] in for it.

We need to "untranslate" this rule back to the soft type system, then correct
the rule of inference. Basically, it seems we need a [capture_free_subst] for
[LocalContext], and nothing else (since the only way to have a bound variable
is from the [LocalContext], at least, in the soft type system).
*)

Lemma translate_antecedent_step {?? : list Formula} :
  forall (T : SoftType) (?? : LocalContext) (J : JudgementType),
?? ??? translate_antecedent (T :: ??)%list J = ?? ??? Forall (Implies (translate T) (translate_antecedent ?? J)).
Proof.
  intros.
  set (A := right_conjoin_many (translate T) (map translate ??)).
  assert (translate_antecedent (T :: ??)%list J = uncurried_translate_antecedent (T :: ??)%list J). {
    auto.
  } rewrite H.
  rewrite (explicit_uncurried_translate_antecedent_structure T ?? J A). 2: auto.
  admit. (* Tedious proof commuting "And"-ed clauses *)
Admitted.

Lemma wt_subst_correctness : forall (T : SoftType) (?? : GlobalContext) (?? : LocalContext) (t : Term) (J : JudgementType),
  proves (translate (??;; (T :: ??)%list |- J)) ->
  proves (translate (??;; ?? |- Esti t T)) ->
  proves (translate (??;; (LocalContext.capture_free_subst 0 t ??) |- subst (BVar (length ??)) t J)).
Proof.
  intros. destruct ?? as [| s ??'].
  - unfold LocalContext.capture_free_subst; unfold length.
    unfold translate; unfold TranslatableJudgement; unfold translate_antecedent; unfold uncurried_translate_antecedent.
    unfold translate in H; unfold TranslatableJudgement in H; unfold translate_antecedent in H; unfold uncurried_translate_antecedent in H.
    unfold map in H; unfold length in H; unfold Every in H.
    assert (right_conjoin_many (translate T) [] = translate T). { auto. }
    rewrite H1 in H. apply (implies_forall_e (translate ??) (Implies (translate T) (translate J)) t) in H as H2.
    unfold translate in H0; unfold TranslatableJudgement in H0; unfold translate_antecedent in H0; unfold uncurried_translate_antecedent in H0.
    assert (translate (Esti t T) = unshift (capture_free_subst 0 (shift t) (translate T))). { auto. }
    rewrite H3 in H0.
    
Admitted.

Lemma inhabited_star_correctness : forall (?? : GlobalContext) (?? : LocalContext),
  proves (translate (??;; ?? |- Inhabited Star)).
Proof.
  intros.
  set (j := (?? ;; ?? |- Inhabited Star)).
  assert (Judgement_body j = Inhabited Star). { simpl; auto. }
  assert (translate (Inhabited Star) = Exists Verum). {
    simpl; auto.
  }
  apply provable_body_translations_provable. rewrite H; rewrite H0.
  apply exists_Verum.
Qed.

Lemma star_sub_star_correctness :
  forall (?? : GlobalContext) (?? : LocalContext),
  well_typed (?? ;; ?? |- Subtype Star Star) -> proves (translate (?? ;; ?? |- Subtype Star Star)).
Proof.
  intros.
  set (j := (?? ;; ?? |- Subtype Star Star)).
  assert (Judgement_body j = Subtype Star Star). { simpl; auto. }
  assert (translate (Subtype Star Star) = Forall (Implies Verum Verum)). {
    simpl; auto.
  }
  apply provable_body_translations_provable. rewrite H0; rewrite H1.
  apply forall_Verum_implies_Verum.
Qed.

Lemma subtype_refl_correctness :
  forall (?? : GlobalContext) (?? : LocalContext) (T1 : SoftType),
  well_typed (??;; ?? |- Subtype T1 T1) -> proves (translate (?? ;; ?? |- Subtype T1 T1)).
Proof.
  intros.
  set (j := (?? ;; ?? |- Subtype T1 T1)).
  assert (Judgement_body j = Subtype T1 T1). { simpl; auto. }
  assert (translate (Subtype T1 T1) = Forall (Implies (translate T1) (translate T1))). {
    simpl; auto.
  }
  apply provable_body_translations_provable. rewrite H0; rewrite H1.
  apply forall_implies_reflex.
Qed.

Lemma subtype_trans_correctness :
  forall (?? : GlobalContext) (?? : LocalContext) (T1 T2 T3 : SoftType),
  proves (translate (??;; ?? |- Subtype T1 T2)) ->
  proves (translate (??;; ?? |- Subtype T2 T3)) ->
  proves (translate (??;; ?? |- Subtype T1 T3)).
Proof.
  intros.
  assert (proves (Implies (translate (Subtype T1 T2))
                          (Implies (translate (Subtype T2 T3)) (translate (Subtype T1 T3))))). {
    assert (translate (Subtype T1 T2) = Forall (Implies (translate T1) (translate T2))). {
      auto.
    }
    assert (translate (Subtype T2 T3) = Forall (Implies (translate T2) (translate T3))). {
      auto.
    }
    assert (translate (Subtype T1 T3) = Forall (Implies (translate T1) (translate T3))). {
      auto.
    } rewrite H1; rewrite H2; rewrite H3.
    apply universal_hypothetical_syllogism.
  }
  apply (hamburger_helper (Subtype T1 T2) (Subtype T2 T3) (Subtype T1 T3)).
  assumption. assumption. assumption.
Qed.

(* This is just [forall_modus_const_tautology]. *)
Lemma subsumption_correctness : forall (t : Term) (T1 T2 : SoftType) (?? : GlobalContext) (?? : LocalContext),
  proves (translate (??;; ?? |- Esti t T1)) ->
  proves (translate (??;; ?? |- Subtype T1 T2)) ->
  proves (translate (??;; ?? |- Esti t T2)).
Proof.
  intros.
  assert (translate (Esti t T1) = unshift (capture_free_subst 0 (shift t) (translate T1))). {
    auto.
  }
  assert (translate (Esti t T2) = unshift (capture_free_subst 0 (shift t) (translate T2))). {
    auto.
  }
  assert (translate (Subtype T1 T2) = Forall (Implies (translate T1) (translate T2))). {
    auto.
  }
  assert (proves (Implies (unshift (capture_free_subst 0 (shift t) (translate T1)))
                          (Implies (Forall (Implies (translate T1) (translate T2)))
                                   (unshift (capture_free_subst 0 (shift t) (translate T2)))))). {
    apply ND_imp_i2; apply ND_imp_i2.
    Assume ([Forall (Implies (translate T1) (translate T2)); unshift (capture_free_subst 0 (shift t) (translate T1))] ??? Forall (Implies (translate T1) (translate T2))).
    Assume ([Forall (Implies (translate T1) (translate T2)); unshift (capture_free_subst 0 (shift t) (translate T1))] ??? unshift (capture_free_subst 0 (shift t) (translate T1))).
    admit.
  } rewrite <- H3 in H4; rewrite <- H2 in H4; rewrite <- H1 in H4.
  apply (hamburger_helper (Esti t T1) (Subtype T1 T2) (Esti t T2) ?? ??).
  assumption. assumption. assumption.
Admitted.

(* This is just [forall_modus_ponens_tautology] *)
Lemma parent_inhabited_correctness : forall (T1 T2 : SoftType) (?? : GlobalContext) (?? : LocalContext),
  proves (translate (??;; ?? |- Subtype T1 T2)) ->
  proves (translate (??;; ?? |- Inhabited T1)) ->
  proves (translate (??;; ?? |- Inhabited T2)).
Proof. intros.
  assert (proves (Implies (translate (Subtype T1 T2))
                          (Implies (translate (Inhabited T1)) (translate (Inhabited T2))))). {
    assert (translate (Subtype T1 T2) = Forall (Implies (translate T1) (translate T2))). {
      auto.
    } rewrite H1.
    assert (translate (Inhabited T1) = Exists (translate T1)). {
      auto.
    } rewrite H2.
    assert (translate (Inhabited T2) = Exists (translate T2)). {
      auto.
    } rewrite H3.
    apply forall_modus_ponens_tautology.
  }
  apply (hamburger_helper (Subtype T1 T2) (Inhabited T1) (Inhabited T2)).
  assumption. assumption. assumption.
Qed.

Lemma unfolded_translate_prefixed_soft_type : forall adj T,
  translate (prefix adj T) = And (translate adj) (translate T).
Proof.
  intros. destruct T.
  assert (prefix adj (l, r) = ((adj::l)%list, r)). { simpl; auto. }
  fold LocalContext in H. rewrite H. clear H. induction l.
  - simpl; auto.
  - simpl; auto. 
Qed.

(* This is just [forall_proj_r] *)
Lemma cons_pos_correctness : forall A T ?? ??,
  proves (translate (??;; ?? |- HasAttribute A T)) ->
  proves (translate (??;; ?? |- Subtype (prefix (Pos A) T) T)).
Proof.
  intros.
  set (j := (?? ;; ?? |- Subtype (prefix (Pos A) T) T)).
  assert (Judgement_body j = Subtype (prefix (Pos A) T) T). { simpl; auto. }
  assert (translate (Subtype (prefix (Pos A) T) T)
         = Forall (Implies (And (translate (Pos A)) (translate T)) (translate T))). {
    assert (translate (Subtype (prefix (Pos A) T) T) = Forall (Implies (translate (prefix (Pos A) T)) (translate T))). {
      simpl; auto.
    } rewrite H1.
    rewrite unfolded_translate_prefixed_soft_type. reflexivity.
  }
  apply provable_body_translations_provable. rewrite H0; rewrite H1.
  apply forall_proj_r.
Qed.

(* This is just [forall_proj_r] *)
Lemma cons_neg_correctness : forall A T ?? ??,
  proves (translate (??;; ?? |- HasAttribute A T)) ->
  proves (translate (??;; ?? |- Subtype (prefix (Neg A) T) T)).
Proof. intros.
  set (j := (?? ;; ?? |- Subtype (prefix (Neg A) T) T)).
  assert (Judgement_body j = Subtype (prefix (Neg A) T) T). { simpl; auto. }
  assert (translate (Subtype (prefix (Neg A) T) T)
         = Forall (Implies (And (translate (Neg A)) (translate T)) (translate T))). {
    assert (translate (Subtype (prefix (Neg A) T) T) = Forall (Implies (translate (prefix (Neg A) T)) (translate T))). {
      simpl; auto.
    } rewrite H1.
    rewrite unfolded_translate_prefixed_soft_type. reflexivity.
  }
  apply provable_body_translations_provable. rewrite H0; rewrite H1.
  apply forall_proj_r.
Qed.

(* This is just [forall_proj_r] *)
Lemma adj_subtype_correctness : forall (T2 T1 : SoftType) a ?? ??,
  proves (translate (??;; ?? |- Subtype T1 T2)) ->
  proves (translate (??;; ?? |- Subtype (prefix a T2) T2)) ->
  proves (translate (??;; ?? |- Subtype (prefix a T1) T1)).
Proof.
  intros.
  set (j := (?? ;; ?? |- Subtype (prefix a T1) T1)).
  assert (Judgement_body j = Subtype (prefix a T1) T1). { simpl; auto. }
  assert (translate (Subtype (prefix a T1) T1)
         = Forall (Implies (And (translate a) (translate T1)) (translate T1))). {
    assert (translate (Subtype (prefix a T1) T1) = Forall (Implies (translate (prefix a T1)) (translate T1))). {
      simpl; auto.
    } rewrite H2.
    rewrite unfolded_translate_prefixed_soft_type. reflexivity.
  }
  apply provable_body_translations_provable. rewrite H1; rewrite H2.
  apply forall_proj_r.
Qed.

Lemma nested_subtype_syllogism : forall ?? A p q,
  ?? ??? Implies (Forall (Implies p q))
              (Implies (Forall (Implies (And A q) q))
                       (Forall (Implies (And A p) (And A q)))).
Proof.
  intros.
  apply ND_imp_i2; apply ND_imp_i2.
  Assume (Forall (Implies (And A q) q) :: Forall (Implies p q) :: ?? ??? Forall (Implies (And A q) q)).
  Assume (Forall (Implies (And A q) q) :: Forall (Implies p q) :: ?? ??? Forall (Implies p q)).
  set (t := fresh_evar (Forall (Implies (And A q) q) :: Forall (Implies p q) :: ??) Falsum).
  apply (ND_forall_i (t := t)). 2: unfold t; reflexivity.
  simpl; auto.
  apply ND_imp_i2.
  apply ND_and_context.
  apply ND_and_intro.
  apply ND_assume; prove_In.
  apply (ND_forall_elim (t := t)) in H.
  apply (ND_forall_elim (t := t)) in H0. simpl in H0.
  apply (ND_imp_e (p := capture_free_subst 0 t p)).
  apply (@weakening (Forall (Implies (And A q) q) :: Forall (Implies p q) :: ??) (capture_free_subst 0 t A
:: capture_free_subst 0 t p :: Forall (Implies (And A q) q) :: Forall (Implies p q) :: ??)) in H0.  
   assumption.
   apply subcontext_weaken; apply subcontext_weaken; apply subcontext_reflex.
   apply ND_assume; prove_In.
Qed.

Corollary adj_subtype_adj_correctness : forall ?? ?? a T1 T2,
  proves (translate (??;; ?? |- Subtype T1 T2)) ->
  proves (translate (??;; ?? |- Subtype (prefix a T2) T2)) ->
  proves (translate (??;; ?? |- Subtype (prefix a T1) (prefix a T2))).
Proof.
  intros. 
  assert (translate (Subtype T1 T2) = Forall (Implies (translate T1) (translate T2))). { auto. }
  assert (translate (prefix a T1) = And (translate a) (translate T1)) as Tr1. { apply unfolded_translate_prefixed_soft_type. }
  assert (translate (prefix a T2) = And (translate a) (translate T2)) as Tr2. { apply unfolded_translate_prefixed_soft_type. }
  assert (proves (Implies (translate (Subtype T1 T2))
                          (Implies (translate (Subtype (prefix a T2) T2)) 
                                   (translate (Subtype (prefix a T1) (prefix a T2)))))). {
    assert (translate (Subtype T1 T2) = Forall (Implies (translate T1) (translate T2))). { auto. }
    assert (translate (Subtype (prefix a T2) T2) = Forall (Implies (And (translate a) (translate T2)) (translate T2))). {
      rewrite <- unfolded_translate_prefixed_soft_type; auto.
    }
    assert (translate (Subtype (prefix a T1) (prefix a T2))
           = Forall (Implies (And (translate a) (translate T1)) (And (translate a) (translate T2)))). {
      rewrite <- unfolded_translate_prefixed_soft_type; rewrite <- unfolded_translate_prefixed_soft_type; auto.
    } rewrite H2; rewrite H3; rewrite H4.
    apply (nested_subtype_syllogism [] (translate a) (translate T1) (translate T2)).
  }
  apply (hamburger_helper (Subtype T1 T2) (Subtype (prefix a T2) T2)).
  assumption. assumption. assumption.
Qed.

Lemma diamond_lemma : forall (?? : list Formula) (p q a1 a2 : Formula),
  ?? ??? Implies (Forall (Implies p (And a1 q)))
              (Implies (Forall (Implies p (And a2 q)))
                       (Forall (Implies p (And a1 (And a2 q))))).
Proof.
  intros.
  apply ND_imp_i2; apply ND_imp_i2.
  set (t := fresh_evar (Forall (Implies p (And a2 q)) :: Forall (Implies p (And a1 q)) :: ??) Falsum).
  apply (ND_forall_i (t := t)). 2: unfold t; reflexivity.
  simpl. apply ND_imp_i2.
  Assume (capture_free_subst 0 t p :: Forall (Implies p (And a2 q)) :: Forall (Implies p (And a1 q)) :: ?? ??? Forall (Implies p (And a1 q))).
  Assume (capture_free_subst 0 t p :: Forall (Implies p (And a2 q)) :: Forall (Implies p (And a1 q)) :: ?? ??? Forall (Implies p (And a2 q))).
  apply (ND_forall_elim (t := t)) in H; simpl in H.
  apply (ND_forall_elim (t := t)) in H0; simpl in H0.
  apply (ND_imp_e (p := capture_free_subst 0 t p)) in H. 2: apply ND_assume; prove_In.
  apply (ND_imp_e (p := capture_free_subst 0 t p)) in H0. 2: apply ND_assume; prove_In.
  apply ND_proj_l in H as H1.
  apply (ND_and_intro (P := (capture_free_subst 0 t a1))).
  assumption. assumption.
Qed.

Lemma adj_diamond_correctness : forall T1 T2 a1 a2 ?? ??,
  proves (translate (??;; ?? |- Subtype T1 (prefix a1 T2))) ->
  proves (translate (??;; ?? |- Subtype T1 (prefix a2 T2))) ->
  proves (translate (??;; ?? |- Subtype T1 (prefix a1 (prefix a2 T2)))).
Proof.
  intros.
  set (J1 := Subtype T1 (prefix a1 T2)). fold J1 in H.
  set (J2 := Subtype T1 (prefix a2 T2)). fold J2 in H0.
  set (J3 := Subtype T1 (prefix a1 (prefix a2 T2))).
  assert (proves (Implies (translate J1) (Implies (translate J2) (translate J3)))). {
    unfold J1; unfold J2; unfold J3.
    assert (translate (Subtype T1 (prefix a1 T2))
            = Forall (Implies (translate T1) (And (translate a1) (translate T2)))). {
      rewrite <- unfolded_translate_prefixed_soft_type; auto.
    }
    assert (translate (Subtype T1 (prefix a2 T2))
            = Forall (Implies (translate T1) (And (translate a2) (translate T2)))). {
      rewrite <- unfolded_translate_prefixed_soft_type; auto.
    } rewrite H1; rewrite H2.
    assert (translate (Subtype T1 (prefix a1 (prefix a2 T2)))
            = Forall (Implies (translate T1) (And (translate a1) (And (translate a2) (translate T2))))). {
      rewrite <- unfolded_translate_prefixed_soft_type; rewrite <- unfolded_translate_prefixed_soft_type; auto.
    } rewrite H3.
    apply (@diamond_lemma []%list (translate T1) (translate T2) (translate a1) (translate a2)).
  }
  apply (hamburger_helper J1 J2 J3 ?? ??).
  assumption.
  assumption.
  assumption.
Qed.

Theorem correctness : forall (J : Judgement),
  well_typed J -> proves (translate J).
Proof.
  intros.
  induction H.
  - (* ?? ;; ?? |- CorrectContext *)
    apply correct_contexts_are_trivial; apply Verum_implies_Verum.
  - (* ??;; push (x, T) ?? |- CorrectContext *)
    intros. simpl. apply correct_contexts_are_trivial; apply Verum_implies_Verum. 
  - (* Substitution rule = Forall elimination *)
    apply (wt_subst_correctness T); assumption; assumption.
  - (* Assume rule = ND_assume *)
    apply assume_correctness. assumption.
  - (*  Subtype Star Star *)
    apply star_sub_star_correctness; apply wt_subtype_star_star; assumption.
  - (* ??;; ?? |- Inhabited Star *)
    apply inhabited_star_correctness.
  - (* proves (translate (??;; ?? |- Subtype T1 T1)) *)
    apply subtype_refl_correctness; apply wt_subtype_refl in H; assumption. 
  - (* transitivity of subtype *)
    apply (subtype_trans_correctness ?? ?? T1 T2); assumption.
  - (* Subsumption ("Liskov") property [t : T1] and [T1 <= T2] implies [t : T2] *)
    apply (subsumption_correctness t T1); assumption; assumption. 
  - (* [T1 <= T2] and [Inhabited T1] implies [Inhabited T2] *)
    apply (parent_inhabited_correctness T1); assumption; assumption.
  - (* translate (??;; ?? |- Subtype (prefix (Pos A) T) T) *)
    apply cons_pos_correctness; assumption.
  - (* translate (??;; ?? |- Subtype (prefix (Neg A) T) T) *)
    apply cons_neg_correctness; assumption.
  - (* ??;; ?? |- Subtype (prefix a T1) T1 *)
    apply (adj_subtype_correctness T2); assumption; assumption.
  - (* ??;; ?? |- Subtype (prefix a T1) (prefix a T2) *)
    apply adj_subtype_adj_correctness; assumption; assumption.
  - (* ??;; ?? |- Subtype T1 (prefix a1 (prefix a2 T2)) *)
    apply adj_diamond_correctness; assumption; assumption.
(* Rules governing Definitions *)
  - apply correct_contexts_are_trivial.
  - apply correct_contexts_are_trivial.
  - apply correct_contexts_are_trivial.
(* Rules governing clusters *)
  - apply correct_contexts_are_trivial.
  - apply correct_contexts_are_trivial.
  - apply correct_contexts_are_trivial.
(* Rules governing redefinitions *)
  - apply correct_contexts_are_trivial.
  - apply correct_contexts_are_trivial.
Qed.