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



Program Instance AssetMapping_Int : AssetMapping AssetName Asset map_ := 
{
   aMR := aMR_func;

}. Next Obligation.
{ (*assetMappingRefinement*)
  (* generalize H, H1, H0. apply assetMappingRefinement_axiom. *)
  assert (H3: aMR_func x x /\ aMR_func x y).
 split.
 + apply H.
 + apply H1.
 + generalize H3, H0. apply assetMappingRefinement_axiom.

} Qed.
  Next Obligation.
{ (*amRefCompositional*)
  induction am2. 
  - induction am1.
    + induction aSet.
      { intros. destruct H2. intuition. }
      { intros. destruct H2. intuition. }
    + induction aSet.
      { intros. destruct H2. intuition. }
      { intros. destruct H2. intuition. }
  - induction am1.
    + induction aSet.
      { intros.
         destruct H2. intuition. }
      { intuition. }
    + induction aSet.
      { intuition. }
      { intuition. }

} Qed.