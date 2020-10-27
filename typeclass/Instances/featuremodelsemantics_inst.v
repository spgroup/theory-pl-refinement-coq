Require Export Coq.Lists.ListSet.
Require Export Coq.Lists.List.
Require Export Coq.Bool.Bool.
Require Export Coq.Classes.RelationClasses.
Require Export featuremodelsemantics_int.
Require Export featuremodelsemantics_def.
Require Export formulatheory_int.
Require Export formulatheory_def.
Require Export formulatheory_inst.
Require Export formulatheory_proofs.
Import FormulaTheory.
Import FeatureModelSemantics.

Program Instance FeatureModelSemantics_Int : FeatureModelSemantics Formula FM Name:= 
{
  wfFM:= wfFM_func;
  satImpConsts:= satImpConsts_func;
  satExpConsts:= satExpConsts_func;
  semantics:= semantics_func;
  refines:= refines_func;
  refines2:= refines_func;
  ns := nsf_func

}. Next Obligation.
{ (*wtFormRefinement*)
  induction f.
  + simpl; tauto.
  + simpl; tauto.
  + simpl. rewrite name in H0.
    rewrite n. apply H0. 
  + simpl; tauto.
  + simpl in H1. destruct H1. split.
    - apply IHf1. apply H1.
    - apply IHf2. apply H4.
  + simpl in H1.  split. 
    - apply IHf1. destruct H1. apply H1.
    - apply IHf2. destruct H1. apply H4.

} Qed.
  Next Obligation.
 (* notMember*)
    (*intros.
    unfold not in H.
    unfold not. 
    destruct opt.
    intro H2.
    destruct conf in H1.
    + destruct fm. unfold wfFM_func in H. intuition.
      


destruct formulae. 
      - destruct FM. simpl in H1. apply H1.
      - destruct n. destruct f; 
        simpl in H; apply H0; left; reflexivity.

    + destruct fm. destruct f.
      - simpl in H1. apply H1.
      - simpl in H. apply H0. left. rewrite n0. reflexivity.
} *) Admitted.
