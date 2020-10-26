Module FeatureModelRefinements.

Require Export form name decidability feature_model formula_theory feature_model_semantics.
Import Name FormulaTheory Form Decidability FeatureModel FeatureModelSemantics.
  Require Import Coq.Lists.ListSet.

(*useful lemma*)

Lemma wtFormAddNode: forall (abs con: FM) (n1 n2: Name),
  wfTree(abs) /\ wfTree(con) /\
    names_ (con) = set_add name_dec n2 (names_ (abs)) /\
      set_In n1 (names_ (abs)) /\
        (~set_In n2 (names_ (abs)))
          -> (forall (f: Formula), wt abs f -> wt con f).
Proof.
  induction f. 
  - intuition.
  - intuition.
  - destruct H. destruct H0. destruct H1. destruct H2.
    intros. unfold not in H3.
    unfold wt. unfold wt in H4. unfold names_ in H2.
    unfold names_ in H3. unfold names_ in H1. rewrite H1. 
    destruct n1, n2, n. intuition.
  - intuition.
  -  simpl. destruct H. destruct H0. destruct H1. destruct H2.
    intros. unfold not in H3. destruct H4.
    split. 
    + apply IHf1. apply H4.
    + apply IHf2. apply H5.
  -  simpl. destruct H. destruct H0. destruct H1. destruct H2.
    intros. unfold not in H3. destruct H4.
    split. 
    + apply IHf1. apply H4.
    + apply IHf2. apply H5.
Qed.

(*===============  Add Mandatory Node ====================*)

Definition addMandatoryNode (abs: WFM) (con: FM) (n1 n2: Name): Prop :=
  names_ con = set_add name_dec n2 (names_ abs) /\
      formulas con = set_union form_dec (app
        ((IMPLIES_FORMULA (NAME_FORMULA(n2)) (NAME_FORMULA(n1)))::nil) 
        ((IMPLIES_FORMULA (NAME_FORMULA(n1)) (NAME_FORMULA(n2)))::nil))
          (formulas(abs)) /\  set_In n1 (names_ abs) /\ (~set_In n2 (names_ (abs))). 


Theorem addMandatoryWF: forall (abs: WFM) (n1 n2: Name) (con:WFM),
  addMandatoryNode abs con n1 n2 -> wfFM (con).
Proof.
  intros. 
  unfold addMandatoryNode in H. destruct H. 
  rewrite n1, n2 in H0. intuition.
Qed.


Theorem addMandatoryT: forall (abs: WFM) (n1 n2: Name),
  exists (con: WFM), addMandatoryNode abs con n1 n2 ->
    (forall (c: Configuration),
      set_In c (semantics abs)
        -> if Is_truePB(set_In n1 c) then (set_In (set_add name_dec n2 c) (semantics con))
         else set_In c (semantics con)) /\
           (forall (c: Configuration),
              set_In c (semantics con)
                -> if Is_truePB(set_In n2 c) then (set_In (set_remove name_dec n2 c) (semantics abs))
                  else set_In c (semantics abs)) /\
                    wfFM(con).
Proof.
  unfold addMandatoryNode. simpl. intros. exists abs.
  intros. destruct H. destruct H0.  rewrite n1, n2 in H1.
  intuition.
Qed.

Theorem addMandatoryTWF: forall (abs: WFM) (con: WFM) (n1 n2: Name),
  addMandatoryNode abs con n1 n2 ->
    (forall (c: Configuration),
      set_In c (semantics abs)
        -> if Is_truePB(set_In n1 c) then (set_In (set_add name_dec n2 c) (semantics con))
         else set_In c (semantics con)) /\
           (forall (c: Configuration),
              set_In c (semantics con)
                -> if Is_truePB(set_In n2 c) then (set_In (set_remove name_dec n2 c) (semantics abs))
                  else set_In c (semantics abs)) /\
                    wfFM(con).
Proof.
  simpl. intros. unfold addMandatoryNode in H. destruct H. destruct H0.
  rewrite n1, n2 in H1. intuition.
Qed.


(*===================== Add Optional Node =====================*)


Definition addOptionalNode (abs: WFM) (con: FM) (n1 n2: Name): Prop :=
  names_ (con) = set_add name_dec n2 (names_ (abs)) /\ set_In n1 (names_ abs) /\
     formulas (con) = set_add form_dec (IMPLIES_FORMULA (NAME_FORMULA(n2)) (NAME_FORMULA(n1)))
          (formulas(abs)) /\ (~set_In n2 (names_ (abs))).  


(*preserva a semantica estática*)
Lemma wfPreservation: forall (abs: WFM) (con: WFM) (n1 n2: Name),
  addOptionalNode abs con n1 n2 ->
    wfFM (con).
Proof.
  intros. 
  unfold addOptionalNode in H. destruct H. 
  rewrite n1, n2 in H0. intuition.
Qed.

Theorem addNode: forall (abs: WFM) (con: WFM) (n1 n2: Name),
  exists (con: WFM), (addOptionalNode abs con n1 n2 ->
    refines abs con /\ wfFM con).
Proof.
  intros. 
  exists abs. unfold addOptionalNode. intros. destruct H. 
  rewrite n1, n2 in H0. intuition.
Qed.

Theorem addOptNode: forall (abs: WFM) (con: WFM) (n1 n2: Name),
  addOptionalNode abs con n1 n2 -> 
     refines abs con /\ wfFM con.
Proof.
  simpl. intros. unfold addOptionalNode in H. destruct H. destruct H0.
  rewrite n2 in H1. rewrite n1 in H0. intuition.
Qed.


End FeatureModelRefinements.









