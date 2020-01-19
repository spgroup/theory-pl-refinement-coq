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
  my_set_union  := my_set_union_func;
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
 { (*asRefCompositional*)
assert (H3: assetRef_func S1 S2 /\ wfProduct_ind (my_set_union_func S1 aSet)).
 split.
 + apply H.
 + apply H0.
 + generalize H3.
  apply asRefCompositional_axiom.
} Qed.
Next Obligation. { (*assetMappingRefinement*)
  generalize H0. apply assetMappingRefinement_axiom. split.
    + apply H. 
    + apply H1.
} Qed.
