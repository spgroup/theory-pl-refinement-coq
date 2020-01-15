Require Export assetmapping_spl_int.
Require Export maps_proofs.
Require Export maps_inst.
Require Export maps_int.
Require Export maps_def.
Require Export assetmapping_spl_def.
Require Import Coq.Lists.ListSet.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Specif.
Require Export Coq.Lists.List.
Import Maps.
Import AssetMappingSPL.  


Program Instance Ins_AssetMapping: AssetMapping Asset AssetName AM :=
{
  assetRef      := assetRef_func;
  wfProduct     := wfProduct_ind;
  aMR           := aMR_func;
}.
Next Obligation.
  {(*assetRefinementReflexivity*)
   apply assetRefinementReflexivity_axiom.
} Qed.
Next Obligation.
 { (*assetRefinementTranstivity*)
  generalize H H0. apply assetRefinementTranstivity_axiom.
} Qed.
Next Obligation.
{ (*as_dec*)
   apply as_dec_axiom.
} Qed.
Next Obligation.
 { (*asRefCompositional*)
  admit. (*apply asRefCompositional_axiom.*)
} Admitted.
Next Obligation. { (*assetMappingRefinement*)
  generalize H0. apply assetMappingRefinement_axiom. split.
    + apply H. 
    + apply H1.
} Qed.
