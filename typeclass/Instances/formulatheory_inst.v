Require Export Coq.Lists.ListSet.
Require Export Coq.Lists.List.
Require Export Coq.Bool.Bool.
Require Export Coq.Classes.RelationClasses.
Require Export formulatheory_def.
Require Export formulatheory_proofs.
Require Export formulatheory_int.
Import FormulaTheory.


Instance FormulaTheory_Ins: FormulaTheory Formula Name FM := 
  {
  names:= names_func;
  wfTree:= wfTree_func;
  names_:= ns_func;
  wt:= wt_func;
  wtFormulae:= wtFormulae_func;
  satisfies:= satisfies_func;

}. Proof.
{ (*name_dec*)
  apply name_dec_axiom.

} { (*formNames*)
  induction f.
    + simpl; tauto.
    + simpl; tauto.
    + simpl. intros. intuition. rewrite H1 in H. apply H.
    + simpl. tauto.
    + simpl. intros H ; destruct H. intros. apply set_union_elim in H1. inversion H1.
      - apply IHf1. apply H. apply H2.
      - apply set_diff_elim1 in H2. apply IHf2. apply H0. apply H2.
    + simpl. intros H. destruct H. intros. apply set_union_elim in H1. inversion H1.
      - apply IHf1. apply H. apply H2. 
      - apply set_diff_elim1 in H2. apply IHf2. apply H0. apply H2.

} { (*formNames2*)
  unfold not.
  induction f.
    + simpl; tauto.
    + simpl; tauto.
    + simpl. intros. intuition. rewrite H in H1. apply H2. apply H1.
    + simpl; tauto.
    + simpl. intros. destruct H; destruct H. apply set_union_elim in H0. inversion H0.
      - apply (IHf1 n). intuition. apply H3.
      - apply set_diff_elim1 in H3. apply (IHf2 n). intuition. apply H3. 
    + simpl. intros. destruct H. destruct H. apply set_union_elim in H0. inversion H0.
      - apply (IHf1 n). intuition. apply H3.
      - apply set_diff_elim1 in H3. apply (IHf2 n). intuition. apply H3.

} { (*satisfies1*)
    induction f. 
  + simpl; intros; reflexivity.
  + simpl; intros; reflexivity.
  + simpl. intros. intuition. apply H1 in H0. 
    - contradiction. 
    - rewrite n. rewrite n0. reflexivity.
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

} { (*satisfies2*)
  induction f.
  + simpl. intros. reflexivity.
  + simpl. intros. reflexivity.
  + simpl. intros. intuition. apply H1 in H0. 
    - contradiction. 
    - rewrite n. rewrite n0. reflexivity.
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
} { (*wtFormSameFeature*)
  intros.
  destruct H as [equals_abs_con wf_abs_con].
  destruct wf_abs_con as [wf_abs wf_con].
  induction f.
    + rewrite equals_abs_con in H0. apply H0. 
    + rewrite equals_abs_con in H0. apply H0. 
    + simpl. simpl in H0. rewrite equals_abs_con in H0. apply H0. 
    + apply IHf. apply H0. 
    + rewrite equals_abs_con in H0. apply H0. 
    + rewrite equals_abs_con in H0. apply H0. 

} Qed.