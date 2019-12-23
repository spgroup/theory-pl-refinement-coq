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


 Instance AssetTheory_Int : AssetTheory AssetName Asset map_ := 
{
  wfProduct:= wfProduct_ind;
  assetRef:= assetRef_func;

}. Proof.
{ (*ANdec_eq*)
  apply ANdec_eq_axiom.

} { (*Asset_dec*)
  apply Asset_dec_axiom.
} { (*assetRefinement*)
  apply assetRefinement_axiom.
} { (*asRefCompositional_axiom*)
  admit.
}{ (*assetTest*)
  admit.
} Admitted.