Require Export assetmapping_spl_def.
Require Export featuremodel_spl_def.
Require Export cktrans_spl_def. 
Require Export spl_int.
Require Export assetmapping_spl_int.
Require Export assetmapping_spl_inst.

Require Export featuremodel_spl_int.
Require Export featuremodel_spl_inst.
Require Export featuremodel_spl_proofs.

Require Export cktrans_spl_int.
Require Export cktrans_spl_proofs.
Require Export cktrans_spl_inst.

Require Export maps_proofs.
Require Export maps_int.
Require Export maps_def.
Require Export maps_inst.

Require Export spl_def.

Require Import Coq.Lists.ListSet.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Specif.
Require Export Coq.Lists.List.
Import Maps.
Import CKTransSPL.
Import FeatureModelSPL.
Import AssetMappingSPL.
Import SPL. 


    Lemma equalsRefinementAlt:
      forall pl1 pl2, pl1 = pl2-> plRefinementAlt_func pl1 pl2.
      Proof.
      intros. rewrite H.
      unfold plRefinementAlt_func.
      intros.
      exists p1.
      split.
        + apply H0.
        + apply assetRefinementReflexivity_axiom.
      Qed.

    Lemma equalsStrongerPL:
    forall pl1 pl2, pl1 = pl2 -> strongerPLrefinement_func pl1 pl2.
    Proof.
    intros.
    unfold strongerPLrefinement_func.
    intros. split.
    - rewrite H in H0. apply H0.
    - rewrite H. apply assetRefinementReflexivity_axiom.
    Qed.
   
   Lemma equalsPL:
    forall pl1 pl2, pl1 = pl2 -> plRefinement_func pl1 pl2.
    Proof.
    intros.
    unfold plRefinement_func.
    intros.  exists c1. split.
    - rewrite H in H0. apply H0.
    - rewrite H. apply assetRefinementReflexivity_axiom.
    Qed.

    Axiom fmref: FMRef = FMRef_Func.
    Axiom equivalentCK_axiom:  equivalentCKs = equivalentCKs_func.
    Axiom weakerEqCK_axiom:  weakerEqCK = weakerEqCK_func.
    

