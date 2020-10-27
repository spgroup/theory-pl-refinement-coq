Require Export Coq.Lists.ListSet. 
Require Export Coq.Classes.SetoidDec.
Require Export Coq.Lists.List.
Require Export Coq.Bool.Bool.
Require Export Coq.Classes.RelationClasses. 
Require Export formulatheory_def.
Require Export formulatheory_proofs.
Require Export formulatheory_int.
Import FormulaTheory.


Program Instance FormulaTheory_Ins: FormulaTheory Formula Name FM := 
  {
  names:= names_func;
  wfTree:= wfTree_func;
  names_:= ns_func;
  wt:= wt_func;
  wtFormulae:= wfFormulae_func;
  satisfies:= satisfies_func;
  my_set_add := my_set_add_func;
  my_set_remove := my_set_remove_func;

}.  Next Obligation.
{ (*name_dec*)
  apply name_dec_axiom.

} Qed. 
  Next Obligation.
{ (*formNames*)
  induction f.
    + simpl in H0. contradiction.
    + simpl in H0. contradiction.
    + simpl in H, H0. intuition. rewrite H1 in H. apply H.
    + simpl in H, H0. intuition.
    + simpl in H. destruct H. intuition. simpl in H0.
    apply set_union_elim in H0. inversion H0.
      - apply H2. apply H4. 
      - apply set_diff_elim1 in H4. apply H3. apply H4.
    + simpl in H. destruct H. simpl in H0. apply set_union_elim in H0.
      inversion H0.
      - apply IHf1. apply H. apply H2. 
      - apply set_diff_elim1 in H2. apply IHf2. 
        * apply H1.
        * apply H2.

} Qed. 
  Next Obligation.
{ (*formNames2*)
  unfold not.
  induction f.
    + simpl; tauto.
    + simpl; tauto.
    + simpl in H. unfold not in H0. intros.
      simpl in H1. intuition. apply H0. rewrite <- H2. apply H.
    + simpl; tauto.
    + simpl. intros. simpl in H. destruct H. apply set_union_elim in H1.
      inversion H1.
      - apply IHf1.
        * apply H.
        * apply H3.
      - apply set_diff_elim1 in H3. apply IHf2. 
        * apply H2.
        * apply H3.
   + simpl. intros. simpl in H. destruct H. apply set_union_elim in H1.
      inversion H1.
      - apply IHf1.
        * apply H.
        * apply H3.
      - apply set_diff_elim1 in H3. apply IHf2. 
        * apply H2.
        * apply H3.

} Qed. 
  Next Obligation.  { (*satisfies1*) 
    induction f. 
  + simpl; reflexivity.
  + simpl; reflexivity.
  + simpl. simpl in H. unfold not in H. intuition. apply H1 in H0. 
    - contradiction. 
    - rewrite n. rewrite n0. reflexivity.
  + simpl. intros. apply not_compat. apply IHf. apply H.
  + simpl. intros. apply set_union_elim_not in H. destruct H as [H1 H2]. 
    specialize IHf1. specialize IHf2.
    apply set_diff_elim_not in H2. inversion H2.
    -  apply IHf1 in H1. apply IHf2 in H. rewrite H1.
      rewrite H. reflexivity.
    - contradiction.
 + simpl. intros. apply set_union_elim_not in H. destruct H as [H1 H2]. 
    specialize IHf1. specialize IHf2.
    apply set_diff_elim_not in H2. inversion H2.
    -  apply IHf1 in H1. apply IHf2 in H. rewrite H1.
      rewrite H. reflexivity.
    - contradiction. 
} Qed.
  Next Obligation. 
{ (*satisfies2*)
   induction f. 
  + simpl; reflexivity.
  + simpl; reflexivity.
  + simpl. simpl in H. unfold not in H. intuition. apply H1 in H0. 
    - contradiction. 
    - rewrite n. rewrite n0. reflexivity.
  + simpl. intros. apply not_compat. apply IHf. apply H.
  + simpl. intros. apply set_union_elim_not in H. destruct H as [H1 H2]. 
    specialize IHf1. specialize IHf2.
    apply set_diff_elim_not in H2. inversion H2.
    -  apply IHf1 in H1. apply IHf2 in H. rewrite H1.
      rewrite H. reflexivity.
    - contradiction.
 + simpl. intros. apply set_union_elim_not in H. destruct H as [H1 H2]. 
    specialize IHf1. specialize IHf2.
    apply set_diff_elim_not in H2. inversion H2.
    -  apply IHf1 in H1. apply IHf2 in H. rewrite H1.
      rewrite H. reflexivity.
    - contradiction. 
} Qed.
  Next Obligation.
{ (*wtFormSameFeature*)
 induction f.
    + auto. 
    + auto. 
    + simpl. simpl in H0. unfold ns_func in H.
    rewrite H in H0. apply H0. 
    + auto. 
    + induction abs, con. simpl. destruct H0. intuition. 
    + induction abs, con. simpl. destruct H0. intuition. 
} Qed. 