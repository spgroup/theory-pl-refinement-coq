Module FeatureModelSemantics.

Require Export form name decidability feature_model formula_theory.
Import Name FormulaTheory Form Decidability FeatureModel.
Require Import Coq.Lists.ListSet Coq.Lists.List.

(*well-formed feature model*)
Definition wfFM (fm : FM) : Prop := (wfTree fm) /\ (wfFormulae fm).

Record WFM : Type := {
fms:> FM;
wfm:> Prop; }.

 (*configuration only contain names from the feature model*)
Definition satImpConsts (fm : WFM) (c : Configuration) : Prop := 
 forall n: Name, set_In n (c) -> set_In n (fst fm.(fms)).

Definition satExpConsts (fm : WFM) (c : Configuration) : Prop := 
  forall f: Formula, set_In f (snd fm.(fms)) -> (satisfies f c = True).

Definition Is_truePB (b:Prop) : bool :=
  match b with
    | True => true
  end.

Fixpoint filter (fm:WFM) (s: set Configuration) : set Configuration :=
  match s with
   | nil => nil
   | a1 :: x1 => 
        if Is_truePB ((satImpConsts fm a1) /\
              (satExpConsts fm a1)) then a1 :: filter fm x1 
         else filter fm x1
  end.

Fixpoint genConf (fm : set Name) : set Configuration := 
  match fm with
  | nil => nil
  | x :: xs => (set_add conf_dec (set_add name_dec x (nil)) (genConf xs)) ++ (genConf xs)
  end.
 
(* semantics of a feature model *)
Definition semantics (fm : WFM) : set Configuration := 
  filter fm (genConf (names_ fm)).

(* refinement notion for feature models *)
Definition refines (abs : WFM) (con : WFM) : Prop :=
    forall (conf : Configuration), 
      set_In conf (semantics {|fms:=abs; wfm := wfFM abs|}) -> set_In conf (semantics con).

(*mais abrangente, permitindo rename, por exemplo*)
Definition refines2 (abs : WFM) (con : WFM) : Prop :=
  forall (conf1 : Configuration), set_In conf1 (semantics abs) ->
    exists (conf2 : Configuration),  set_In conf2 (semantics con).


(* garante que um refinamento é bem tipado*)
Lemma wtFormRefinement : forall (abs : FM) (con : FM), forall (name : Name),
 set_In name (fst abs) -> set_In name (fst con) /\ (wfTree abs) /\
 (wfTree con) -> (forall (f : Formula), (wt abs f) -> (wt con f)).
Proof.
induction f.
  + auto.
  + auto.
  + destruct H0. intros. simpl. rewrite name in H0.
    rewrite n. apply H0. 
  + auto. 
  + simpl. intros. destruct H1. split.
    - apply IHf1. apply H1.
    - apply IHf2. apply H2.
  + simpl. intros. split. 
    - apply IHf1. destruct H1. apply H1.
    - apply IHf2. destruct H1. apply H2.
Qed.  


(* garante que um FM bem formado não apresenta configurações inválidas. *)
Theorem notMember : forall (fm : WFM) (opt : Name), 
   ~(set_In opt (names_ fm)) -> (forall (conf : Configuration), 
    set_In conf (semantics fm) -> ~ (set_In opt (conf))).
    Proof.
    intros.
    unfold not in H.
    unfold not. 
    intro H2.
    destruct conf in H0.
    + destruct fm. destruct fms0. unfold names_ in H. simpl in H. destruct f. 
      - simpl in H0. contradiction. 
      - destruct n. destruct f. simpl in H. simpl in H0. intuition.
          *  apply H0. destruct opt. reflexivity.
          * simpl in H. apply H. left. destruct opt. reflexivity.
    + destruct fm. destruct fms0. unfold names_ in H. simpl in H. destruct f. 
      - simpl in H0. contradiction. 
      - destruct n. destruct f. simpl in H. simpl in H0. intuition.
          *  apply H0. destruct n0, opt. reflexivity.
          * simpl in H. apply H. left. destruct opt, n0. reflexivity.
Qed.

End FeatureModelSemantics.

