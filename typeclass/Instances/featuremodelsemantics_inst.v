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

Instance FeatureModelSemantics_Int : FeatureModelSemantics Formula FM Name:= 
{
  wfFM:= wfFM_func;
  satImpConsts:= satImpConsts_func;
  satExpConsts:= satExpConsts_func;
  semantics:= semantics_func;
  refines:= refines_func;
  refines2:= refines_func;
  ns := nsf_func

}. Proof.
{ (*wtFormRefinement*)
  admit.

} { (*notMember*)
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
} Admitted.
