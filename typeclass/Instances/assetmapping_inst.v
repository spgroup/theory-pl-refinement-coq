Require Export Coq.Lists.ListSet.
Require Export Coq.Lists.List.
Require Export Coq.Bool.Bool.
Require Export Coq.Classes.RelationClasses.
Require Export maps_def.
Require Export assettheory_def.
Require Export formulatheory_def.
Require Export featuremodelsemantics_def.
Require Export assettheory_int.
Require Export assettheory_inst.
Require Export assetmapping_def.
Require Export assetmapping_int.
Import AssetMapping.
Import FormulaTheory.
Import Maps.
Import AssetTheory.
Import FeatureModelSemantics.



Instance AssetMapping_Int : AssetMapping AssetName Asset map_ := 
{
   aMR := aMR_func;

}. Proof.
{ (*assetMappingRefinement*)
  apply assetMappingRefinement_axiom.

}{ (*amRefCompositional*)
  induction am2. 
  - induction am1.
    + induction aSet.
      { intros. destruct H0. intuition. }
      { intros. destruct H0. intuition. }
    + induction aSet.
      { intros. destruct H0. intuition. apply IHam1. admit. admit. admit. }
      { intros. destruct H0. intuition. admit. }
  - induction am1.
    + induction aSet.
      { intros.
         destruct H1. intuition. admit. }
      { intuition. admit. }
    + induction aSet.
      { intuition. admit. }
      { intuition. admit. }

} Admitted.