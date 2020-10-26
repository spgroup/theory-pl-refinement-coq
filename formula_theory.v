Module FormulaTheory.
Require Export form name decidability feature_model.
Import Name Form Decidability FeatureModel.
Require Import Coq.Lists.ListSet Coq.Lists.List.

(*yields names for a formula*)
Fixpoint names_ (f : Formula) : set Name :=
  match f with
    | TRUE_FORMULA    => empty_set Name
    | FALSE_FORMULA   => empty_set Name
    | NAME_FORMULA n1 => set_add name_dec n1 nil
    | NOT_FORMULA f1  => names_ f1
    | AND_FORMULA f1 f2     => set_union name_dec  (names_ f1) 
                                  (set_diff name_dec  (names_ f2) (names_ f1))  
    | IMPLIES_FORMULA f1 f2 => set_union name_dec  (names_ f1) 
                                  (set_diff name_dec  (names_ f2) (names_ f1)) 
  end.  


(* indicates whether a formula is well-typed*)
Fixpoint wt (fm : FM) (f : Formula) : Prop :=
  match f with
    | TRUE_FORMULA    => True
    | FALSE_FORMULA   => True
    | NAME_FORMULA n1 => set_In n1 (fst fm)
    | NOT_FORMULA f1  => wt fm f1
    | AND_FORMULA f1 f2     => (wt fm f1) /\ (wt fm f2)  
    | IMPLIES_FORMULA f1 f2 => (wt fm f1) /\ (wt fm f2)
   end.

(*indicates whether a feature model has all of its formulae well-typed*)
Definition wfFormulae (fm: FM) : Prop :=
  forall (f: Formula), set_In f (formulas fm) -> wt fm f.

(*indicates when a configuration satisfies a formula*)
Fixpoint satisfies (f: Formula) ( c : Configuration) : Prop :=
  match f with
    | TRUE_FORMULA   => True
    | FALSE_FORMULA  => False
    | NAME_FORMULA n => set_In n c
    | NOT_FORMULA f1 => not (satisfies f1 c)
    | AND_FORMULA f1 f2     => and(satisfies f1 c) (satisfies f2 c)  
    | IMPLIES_FORMULA f1 f2 => (satisfies f1 c) -> (satisfies f2 c)
   end.

(*a well-typed formula only contains names from the feature model*)
Lemma formNames : forall (fm : FM) (f : Formula),  
 (wt fm f) -> ( forall (n : Name), set_In n (names_ f) -> set_In n (fst fm)).
Proof.
induction f.
   + simpl. intuition.
   + simpl. intuition.
   + simpl. intuition. rewrite H1 in H. apply H.
   + intuition.
   + simpl. intros H ; destruct H. intros. apply set_union_elim in H1. inversion H1.
      - apply IHf1. apply H. apply H2.
      - apply set_diff_elim1 in H2. apply IHf2. apply H0. apply H2.
    + simpl. intros H. destruct H. intros. apply set_union_elim in H1. inversion H1.
      - apply IHf1. apply H. apply H2. 
      - apply set_diff_elim1 in H2. apply IHf2. apply H0. apply H2.
Qed.

Lemma formNames2 : forall (fm : FM) (f : Formula) (n: Name) , and (wt fm f) 
  (not(set_In n (fst fm))) -> (not(set_In n (names_ f))).
Proof.
induction f.
   + intuition.
   + intuition.
   + simpl. intuition. rewrite H in H1. apply H2. apply H1.
   + intuition.
   + simpl. intros. destruct H; destruct H.  intuition. apply set_union_elim in H2. inversion H2.
      - apply (IHf1 n). intuition. apply H3.
      - apply set_diff_elim1 in H3. apply (IHf2 n). intuition. apply H3. 
   + simpl. intros. destruct H. destruct H. intuition. apply set_union_elim in H2. inversion H2.
      - apply (IHf1 n). intuition. apply H3.
      - apply set_diff_elim1 in H3. apply (IHf2 n). intuition. apply H3.
Qed. 


Theorem not_compat : forall A B : Prop,
  (A = B) -> ((~ A) = (~B)).
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.


Lemma set_union_elim_not :
   forall (a:Name) (x y:set Name),
     ~(set_In a (set_union name_dec x y)) -> ~(set_In a x) /\ ~(set_In a y).
Proof.
  intros. split.
    + intuition. apply H. apply set_union_intro1. apply H0.
    + intuition. apply H. apply set_union_intro2. apply H0.
Qed.

Lemma set_union_elim_not2 :
   forall (a:Name) (x y:set Name),
     ~(set_In a x) /\ ~(set_In a y) ->  ~(set_In a (set_union name_dec x y)).
Proof.  
  intros. destruct H.
  intuition. apply H. 
  apply set_union_elim in H1.
  generalize H1. tauto.
Qed.

Theorem or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros P Q H.
  tauto. Qed. 


Lemma set_diff_elim_not:
    forall (n : Name) (f1 f2 : Formula),
    (not (set_In n (set_diff name_dec (names_ f1) (names_ f2)))) -> or (not (set_In n (names_ f1))) (set_In n (names_ f2)).
Proof.
  intros. left.
  intuition. apply H.
  apply set_diff_intro.
  + apply H0.
  + unfold not. intro.
  apply H. apply set_diff_intro.
  apply H0.
Admitted.

(* satisfies's result is equal if we add a feature to the configuration that is not in the formula *)
Lemma satisfies1 : forall (f: Formula) (c : Configuration) (n : Name),
  not(set_In n (names_ f)) -> satisfies f c = satisfies f (set_add name_dec n c).
Proof.
induction f. 
  + intuition.
  + intuition.
  + simpl. intuition. exfalso. apply H0. rewrite n. rewrite n0. reflexivity.
  + simpl. intros. apply not_compat. apply (IHf c). apply H.
  + simpl. intros. apply set_union_elim_not in H. destruct H as [H1 H2]. 
    specialize (IHf1 c n). specialize (IHf2 c n).
    apply set_diff_elim_not in H2. inversion H2.
    -  apply IHf1 in H1. apply IHf2 in H. rewrite H1.
      rewrite H. reflexivity.
    - contradiction.
 + simpl. intros. apply set_union_elim_not in H. destruct H as [H1 H2]. 
    specialize (IHf1 c n). specialize (IHf2 c n).
    apply set_diff_elim_not in H2. inversion H2.
    -  apply IHf1 in H1. apply IHf2 in H. rewrite H1.
      rewrite H. reflexivity.
    - contradiction.
Qed.

(*satisfies's result is equal if we remove a feature from the configuration that is not in the formula*)
Lemma satisfies2 : forall (f: Formula) (c : Configuration) (n : Name),
  not(set_In n (names_ f)) -> satisfies f c = satisfies f (set_remove name_dec n c).
Proof.
induction f. 
  + intuition.
  + intuition.
  + simpl. intuition. exfalso. apply H0. rewrite n. rewrite n0. reflexivity.
  + simpl. intros. apply not_compat. apply (IHf c). apply H.
  + simpl. intros. apply set_union_elim_not in H. destruct H as [H1 H2]. 
    specialize (IHf1 c n). specialize (IHf2 c n).
    apply set_diff_elim_not in H2. inversion H2.
    -  apply IHf1 in H1. apply IHf2 in H. rewrite H1.
      rewrite H. reflexivity.
    - contradiction.
 + simpl. intros. apply set_union_elim_not in H. destruct H as [H1 H2]. 
    specialize (IHf1 c n). specialize (IHf2 c n).
    apply set_diff_elim_not in H2. inversion H2.
    -  apply IHf1 in H1. apply IHf2 in H. rewrite H1.
      rewrite H. reflexivity.
    - contradiction.
Qed.

(* well-typed formulae from a FM continue well-typed in another FM with the same features *)
Lemma wtFormSameFeature : forall (abs : FM) (con : FM), (fst abs = fst con
  /\ (wfTree abs) /\ (wfTree con) -> ( forall (f : Formula), (wt abs f) ->  (wt con f))).
Proof.
  intros.
  destruct H as [equals_abs_con wf_abs_con].
  destruct wf_abs_con as [wf_abs wf_con].
  induction f.
    + auto. 
    + auto. 
    + simpl. simpl in H0. rewrite equals_abs_con in H0. apply H0. 
    + auto. 
    + induction abs, con. simpl. destruct H0. intuition. 
    + induction abs, con. simpl. destruct H0. intuition. 
Qed.

End FormulaTheory.



