Require Export Coq.Lists.ListSet. 
Require Export Coq.Classes.SetoidDec.
Require Export Coq.Lists.List.
Require Export Coq.Bool.Bool.
Require Export Coq.Classes.RelationClasses. 
Require Export featuremodelrefinement_def.
Require Export featuremodelrefinement_int.
Import FeatureModelRefinimentTheory.
Require Export formulatheory_def.
Require Export formulatheory_proofs.
Require Export formulatheory_int.
Import FormulaTheory.

Program Instance FeatureModelRefinement_Ins: FeatureModelRefinement Formula Name FM := 
{
  addMandatoryNode:= addMandatoryNode_func;
  addOptionalNode := addOptionalNode_func;

}. Next Obligation. {
  apply name_dec_axiom.
} Qed. Next Obligation. {
  apply form_dec_axiom.
} Qed. Next Obligation. {
  unfold not in H4. unfold ns_func. unfold ns_func in H0, H3, H4, H2.
  intuition. admit.
  
} Admitted. Next Obligation. {
  unfold FeatureModelSemantics.wfFM_func. split. unfold addMandatoryNode_func in H.
  destruct H. destruct H0. intuition. admit.
  admit.

} Admitted. Next Obligation. {
  admit.
} Admitted. Next Obligation. {
  admit.
} Admitted. Next Obligation. {
  admit.
} Admitted. Next Obligation. {
  admit.

} Admitted. Next Obligation. {
  admit.

} Admitted.


