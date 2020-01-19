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
Require Export assettheory_int.
Require Export assettheory_def.
Require Export maps_def.
Require Export maps_int.
Require Export maps_inst.
Import FormulaTheory.
Import FeatureModelSemantics.
Import AssetTheory.
Import Maps.


 Program Instance AssetTheory_Int : AssetTheory AssetName Asset map_ := 
{
  wfProduct:= wfProduct_ind;
  assetRef:= assetRef_func;

}. Next Obligation.
{ (*ANdec_eq*)
  apply ANdec_eq_axiom.

} Qed.
  Next Obligation.
 { (*Asset_dec*)
  apply Asset_dec_axiom.
} Qed.
  Next Obligation.
{ (*assetRefinement*)
 assert (H3: assetRef_func x x /\ assetRef_func x y).
 split.
 + apply H.
 + apply H1.
 + generalize H3, H0.
   apply assetRefinement_axiom.
} Qed.
  Next Obligation. 
{ (*asRefCompositional_axiom*)
    assert (H3: assetRef_func S1 S2 /\ wfProduct_ind (union_t_func S1 aSet)).
  split.
  + apply H.
  + apply H0.
  + apply asRefCompositional_axiom. apply H3.
} Qed. 