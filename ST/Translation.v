Require Import String.
Require Import List.
Require Import Nat.
Require Import Coq.Vectors.Vector.
Require Export Coq.Arith.Compare_dec.
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

Example translate_radix_ast :
  translate (Ast) = Verum.
Proof. simpl; auto. Qed.

Example translate_radix_mode_1 :
  translate (Mode 3 "MyMode" [(Var (FVar "x")); (constant "c"); (Var (BVar 3))])
  = Atom (P 4 "Mode_MyMode" [(Var (BVar 0)); (Var (FVar "x")); (constant "c"); (Var (BVar 4))]).
Proof. unfold constant; simpl; auto. Qed.

Global Instance TranslatableAttr : Translatable Attribute := {
  translate (attr : Attribute) :=
  match attr with
  | Attr n s args => (Atom (P (S n) (String.append "Attr_" s) ((Var (BVar 0))::(Vector.map shift args))))
  end
}.

Example translate_attr_1 :
  translate (Attr 3 "MyMode" [(Var (FVar "x")); (constant "c"); (Var (BVar 3))])
  = Atom (P 4 "Attr_MyMode" [(Var (BVar 0)); (Var (FVar "x")); (constant "c"); (Var (BVar 4))]).
Proof. unfold constant; simpl; auto. Qed.

Global Instance TranslatableAdj : Translatable Adjective := {
  translate (adj : Adjective) :=
  match adj with
  | Pos a => translate a
  | Neg a => Not (translate a)
  end
}.

Example translate_adj_1 :
  translate (Pos (Attr 3 "SimplyConnected" [(Var (FVar "x")); (constant "c"); (Var (BVar 3))]))
  = Atom (P 4 "Attr_SimplyConnected" [(Var (BVar 0)); (Var (FVar "x")); (constant "c"); (Var (BVar 4))]).
Proof. unfold constant; simpl; auto. Qed.

Example translate_adj_2 :
  translate (Neg (Attr 3 "SimplyConnected" [(Var (FVar "x")); (constant "c"); (Var (BVar 3))]))
  = Not (Atom (P 4 "Attr_SimplyConnected" [(Var (BVar 0)); (Var (FVar "x")); (constant "c"); (Var (BVar 4))])).
Proof. unfold constant; simpl; auto. Qed.

Definition null {A} (l : list A) : bool :=
match l with
| []%list => true
| _ => false
end.

(* Consider: shift everything by 1, and have [BVar 0] reserved for future
use in translating judgements. *)
(* Convention: 
translate (ad::tl, R) = And (left_fold And (map translate tl) (translate ad))
                            (translate R).
*)
Global Instance TranslatableSoftType : Translatable SoftType := {
  translate (T : SoftType) :=
  match T with
  | (List.nil, R) => translate R
  | (adjs, R) => let fix tr_adjs (ads : list Adjective) :=
                     match ads with
                     | List.cons a tl => if null tl then translate a else And (translate a) (tr_adjs tl)
                     | List.nil => Verum
                     end
                     in And (tr_adjs adjs) (translate R)
  end
}.

Example translate_soft_type_1 :
let st : SoftType := ([Neg (Attr 3 "SimplyConnected" [(Var (FVar "x")); (constant "c"); (Var (BVar 3))]%vector);
  Pos (Attr 1 "Smooth" [(Var (FVar "y"))]%vector)]%list,
(Mode 3 "Manifold" [(Var (FVar "x")); (constant "c"); (Var (BVar 3))]))
in (translate st)
= And (And (translate (Neg (Attr 3 "SimplyConnected" [(Var (FVar "x")); (constant "c"); (Var (BVar 3))])))
           (translate (Pos (Attr 1 "Smooth" [(Var (FVar "y"))]))))
      (translate (Mode 3 "Manifold" [(Var (FVar "x")); (constant "c"); (Var (BVar 3))])).
Proof. unfold constant; simpl; auto. Qed.

(* The [capture_free_subst] usage here requires shifting, then unshifting,
the bound variables. Otherwise, we end up with accidentally capturing the
wrong variables later on. 

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

Example translate_judgement_1 :
translate (Esti (Fun "Sphere" [(constant "n")])
  ([Pos (Attr 0 "Smooth" []%vector); (Pos (Attr 1 "-dimensional" [(constant "n")]%vector))]%list, (Mode 1 "Manifold" [(constant "REAL")])))
= let sphere : Term := (Fun "Sphere" [(constant "n")])
  in And (And (Atom (P 1 "Attr_Smooth" [ sphere ]))
              (Atom (P 2 "Attr_-dimensional" [sphere; Fun "n" []])))
         (Atom (P 2 "Mode_Manifold" [sphere; Fun "REAL" []])).
Proof. unfold constant; simpl; auto. Qed.

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

Lemma uncurried_translate_antecedent_implies_curried {Γ} :
  forall (lc : LocalContext) (j : JudgementType),
  uncurried_translate_antecedent lc j :: Γ
  ⊢ curried_translate_antecedent lc j.
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

Lemma curried_translate_antecedent_implies_uncurried {Γ} :
  forall (lc : LocalContext) (j : JudgementType),
  curried_translate_antecedent lc j :: Γ
  ⊢ uncurried_translate_antecedent lc j.
Admitted.

Theorem translate_antecedent_equiv {Γ} :
  forall (lc : LocalContext) (j : JudgementType),
  Γ ⊢ Iff (uncurried_translate_antecedent lc j)
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
  | (Γ, Δ, j) => Implies (translate Γ) (translate_antecedent Δ j)
  end
}.

Theorem provable_body_translations_provable :
  forall (judgement : Judgement),
  proves (translate (Judgement_body judgement)) -> proves (translate judgement).
Proof.
  intros. destruct judgement as [[Γ Δ] j]. unfold Judgement_body in H.
  unfold translate; unfold TranslatableJudgement. apply ND_imp_i2.
  destruct Δ as [|d Δ'].
  - unfold translate_antecedent; unfold uncurried_translate_antecedent.
    apply (@weakening [] [translate Γ]). assumption. apply empty_subcontext.
  - set (Δ := (d::Δ')%list).
    assert (Δ <> []%list). { discriminate. }
    apply (@uncurried_translate_antecedent_structure Δ j) in H0. 
    unfold translate_antecedent.
Admitted.

Corollary vacuous_translations_provable :
  forall (judgement : Judgement),
  Verum = translate (Judgement_body judgement) -> proves (translate judgement).
Proof.
  intros.
  apply provable_body_translations_provable.
  rewrite <- H. apply ND_True_intro.
Qed.
(*
Proof.
  intros.
  destruct judgement. destruct p.
  unfold translate; unfold TranslatableJudgement.
  unfold proves; apply ND_imp_i2.
  unfold Judgement_body in H. set (Γ := translate g).
  generalize dependent Γ.
  induction l.
  - intros. unfold translate_antecedent. rewrite <- H.
    apply ND_True_intro.
  - intros. destruct l as [| b l'].
  + unfold translate_antecedent. rewrite <- H.
    set (t := fresh_evar [Γ] Falsum).
    apply (@ND_forall_i [Γ] (Implies (translate a) Verum) t).
    assert ([Γ] ⊢ capture_free_subst 0 t (Implies (translate a) Verum)
            = [Γ] ⊢ Implies (capture_free_subst 0 t (translate a)) Verum). {
      simpl; auto.
    }
    rewrite H0. apply ND_imp_i2; apply ND_True_intro.
    unfold t; reflexivity.
  + assert ([Γ] ⊢ translate_antecedent (a :: b :: l')%list j
            = [Γ] ⊢ Forall (Implies (translate a) (translate_antecedent (b :: l')%list j))). {
      unfold translate_antecedent; simpl; auto.
    }
    rewrite H0.
    set (t := fresh_evar [Γ] Falsum).
    apply (@ND_forall_i [Γ] (Implies (translate a) (translate_antecedent (b :: l')%list j)) t).
    2: unfold t; reflexivity.
    assert ([Γ] ⊢ capture_free_subst 0 t (Implies (translate a) (translate_antecedent (b :: l')%list j))
          = [Γ] ⊢ Implies (capture_free_subst 0 t (translate a)) (capture_free_subst 0 t (translate_antecedent (b :: l')%list j))). {
      simpl; auto.
    }
    rewrite H1.
    apply ND_imp_i2.
    apply ND_and_context. 
    assert([And (capture_free_subst 0 t (translate a)) Γ] ⊢ translate_antecedent (b :: l')%list j). {
      apply (@IHl (And (capture_free_subst 0 t (translate a)) Γ)).
    }
    forall Γ : Formula,
      [Γ] ⊢ translate_antecedent (b :: l')%list j
unfold translate_antecedent. rewrite <- H.
*)

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

(*

Hint Constructors JudgementType Radix Term Adjective : core.

Print HintDb typeclass_instances.

Hint Constructors JudgementType Radix Term Adjective Predicate Formula : typeclass_instances.
*)

Lemma empty_context_correctness :
  well_typed (List.nil ;; List.nil |- CorrectContext) -> proves (translate (List.nil ;; List.nil |- CorrectContext)).
Proof. 
  intros; simpl; apply Verum_implies_Verum.
Qed.

Hint Unfold GlobalContext LocalContext : typeclass_instances.
Hint Constructors well_typed deducible : core.
Lemma star_sub_star_correctness :
  forall (Γ : GlobalContext) (Δ : LocalContext),
  well_typed (Γ ;; Δ |- Subtype Star Star) -> proves (translate (Γ ;; Δ |- Subtype Star Star)).
Admitted.

Lemma global_weakening : forall (J : JudgementType) (Γ1 Γ2 : GlobalContext) (Δ : LocalContext),
  List.incl Γ1 Γ2 ->
  well_typed (Γ1 ;; Δ |- J) ->
  well_typed (Γ2 ;; Δ |- J).
Admitted.

Lemma local_weakening : forall (J : JudgementType) (Γ : GlobalContext) (Δ1 Δ2 : LocalContext),
  List.incl Δ1 Δ2 ->
  well_typed (Γ ;; Δ1 |- J) ->
  well_typed (Γ ;; Δ2 |- J).
Admitted.

Lemma proves_true_weakening : forall (J1 J2 : JudgementType) (Γ : GlobalContext) (Δ1 Δ2 : LocalContext),
  List.incl Δ1 Δ2 -> (translate J2 = Verum) ->
  proves (translate (Γ ;; Δ1 |- J1)) ->
  proves (translate (Γ ;; Δ2 |- J2)).
Admitted.

Lemma well_typed_contexts : forall (J : JudgementType) (Γ : GlobalContext) (Δ : LocalContext),
  well_typed (Γ ;; Δ |- J) ->
  well_typed (Γ ;; Δ |- CorrectContext).
Admitted.

Hint Unfold translate_antecedent : core.
Theorem correctness : forall (J : Judgement),
  well_typed J -> proves (translate J).
Proof.
  intros.
  induction H.
  - apply correct_contexts_are_trivial; apply Verum_implies_Verum. (* Γ ;; Δ |- CorrectContext *)
  - intros. simpl. (* Γ;; push (x, T) Δ |- CorrectContext *)
  (* ... and the rest! *)
Qed.