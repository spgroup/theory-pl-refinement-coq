Module FeatureModelSemantics.

Require Export form name decidability feature_model formula_theory.
Import Name FormulaTheory Form Decidability FeatureModel.

Require Export Coq.Lists.List.
Require Export Coq.Sets.Powerset.
Require Export Coq.Bool.Bool.

Definition wfFM (fm : FM) : Prop := (wfTree fm) /\ 
(wtFormulae fm).

Definition satImpConsts (fm : FM) (c : Configuration) : Prop := 
 forall n: Name, set_In n (c) -> set_In n (names_ fm).

Definition satExpConsts (fm : FM) (c : Configuration) : Prop := 
  forall f: Formula, set_In f (snd fm) -> (satisfies f c = True).

Definition Is_truePB (b:Prop) : bool :=
  match b with
    | True => true
  end.

Fixpoint filter (fm:FM) (s: set Configuration) : set Configuration :=
  match s with
   | nil => nil
   | a1 :: x1 => 
        if Is_truePB ((satImpConsts fm a1) /\
              (satExpConsts fm a1)) then a1 :: filter fm x1 
         else filter fm x1
  end.

Fixpoint genConf (fm : features) : set Configuration := 
  match fm with
  | nil => nil
  | x :: xs => (set_add conf_dec (set_add name_dec x (nil)) (genConf xs)) ++ (genConf xs)
  end.
 
Definition semantics (fm : FM) : set Configuration := 
  filter fm (genConf (names_ fm)).


Definition refines (abs : FM) (con : FM) : Prop :=
  if andb (Is_truePB (wfFM abs)) (Is_truePB(wfFM con)) then
  forall (conf : Configuration), set_In conf (semantics abs) -> set_In conf (semantics con)
  else False.


Definition refines2 (abs : FM) (con : FM) : Prop :=
  forall (conf1 : Configuration), set_In conf1 (semantics abs) ->
  exists (conf2 : Configuration),  set_In conf2 (semantics con).

Lemma wtFormRefinement : forall (abs : FM) (con : FM), forall (name : Name),
 set_In name (fst abs) -> set_In name (fst con) /\ (wfTree abs) /\
 (wfTree con) -> (forall (f : Formula), (wt (fst abs) f) -> (wt (fst con) f)).
Proof.
induction f.
  + simpl; tauto.
  + simpl; tauto.
  + destruct H0. intros. simpl. rewrite name in H0.
    rewrite n. apply H0. 
  + simpl; tauto.
  + simpl. intros. destruct H1. split.
    - apply IHf1. apply H1.
    - apply IHf2. apply H2.
  + simpl. intros. split. 
    - apply IHf1. destruct H1. apply H1.
    - apply IHf2. destruct H1. apply H2.
Qed.  

Theorem notMember : forall (fm : FM), wfFM fm = True -> ( forall (opt : Name), 
   ~(set_In opt ( fst fm)) -> (forall (conf : Configuration), 
    set_In conf (semantics fm) -> ~ (set_In opt (conf)))).
    Proof.
    intros.
    unfold not in H.
    unfold not. 
    destruct opt.
    intro H2.
    destruct conf in H1.
    + destruct fm. destruct f. 
      - simpl in H1. apply H1.
      - destruct n. destruct f; 
        simpl in H; apply H0; left; reflexivity.

    + destruct fm. destruct f.
      - simpl in H1. apply H1.
      - simpl in H. apply H0. left. rewrite n0. reflexivity.
Qed.

End FeatureModelSemantics.
