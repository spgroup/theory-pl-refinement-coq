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


Instance Ins_AssetMapping: AssetMapping Asset AssetName AM :=
{
  assetRef      := assetRef_func;
  wfProduct     := wfProduct_ind;
  aMR           := aMR_func;
}.
Proof.
  {(*assetRefinementReflexivity*)
   apply assetRefinementReflexivity_axiom.
} { (*assetRefinementTranstivity*)
   apply assetRefinementTranstivity_axiom.
} { (*as_dec*)
   apply as_dec_axiom.
} { (*asRefCompositional*)
   apply asRefCompositional_axiom.
} { (*assetMappingRefinement*)
  apply assetMappingRefinement_axiom.
} Qed.
