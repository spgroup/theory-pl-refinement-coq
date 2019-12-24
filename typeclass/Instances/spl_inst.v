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
Require Export spl_proofs.

Require Import Coq.Lists.ListSet.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Specif.
Require Export Coq.Lists.List.
Import Maps.
Import CKTransSPL.
Import FeatureModelSPL.
Import AssetMappingSPL.
Import SPL. 




Instance Ins_SPL: SPL Asset AssetName AM Conf FM AM CK PL:=
{
  getFM:= getFM_func;
  getAM:= getAM_func;
  getCK:= getCK_func;
  genPL:= genPL_func; 
  wfPL := wfPL_func;
  plRefinement:= plRefinement_func;
  products:= products_func;
  plRefinementAlt:= plRefinementAlt_func;
  subsetProducts:= subsetProducts_func;
  plWeakRefinement:= plWeakRefinement_func;
  strongerPLRefinement:= strongerPLrefinement_func;

}.
Proof.
{ (*plStrongS ubset*)
    intros.
    destruct pl3. destruct pl4.  unfold strongerPLrefinement_func in H.
    specialize (H c1). rewrite fmref in H0. destruct c1, c0.  apply H in H0.
    destruct  H0. rewrite fmref. apply H0.

} {(*fmEquivalenceCompositionality*)
  intros.
    split.
    + unfold plRefinement_func. intros. exists c1. split.
      -  unfold getFM_func. simpl.  unfold getFM_func in H0. destruct pl in H0.
        simpl in H0. destruct p in H0. simpl in H0. rewrite f in H0.
        rewrite fm. apply H0.
      - unfold getCK_func. unfold getAM_func. simpl.
        apply assetRefinementReflexivity_axiom.
    + unfold wfPL_func. intros.
      unfold equivalentFMs in H.
       intuition.
} {(*weakFMcompositionality*)
  intros. 
    destruct H.   
    unfold plRefinement_func. 
    intros. exists c1.  split.
      +  unfold getFM_func. simpl.  unfold getFM_func in H1. destruct pl in H1.
        simpl in H1. destruct p in H1. simpl in H1. rewrite f in H1.
        rewrite fm. apply H1. 
      + unfold getCK_func. unfold getAM_func. simpl.
        apply assetRefinementReflexivity_axiom.

}{(*ckEquivalenceCompositionality*)
  intros.
    split.
    + unfold plRefinement_func. intros. exists c1. split.
      -  unfold getFM_func. simpl.  unfold getFM_func in H0. destruct pl in H0.
        simpl in H0. destruct p in H0. simpl in H0. rewrite f in H0.
        rewrite fm. apply H0.
      - unfold getCK_func. unfold getAM_func. simpl.
        apply assetRefinementReflexivity_axiom.
    + unfold wfPL_func. intros.
      unfold equivalentFMs in H.
      intuition.

}{(*weakerCKcompositionality*)
 intros.
    split.
    + unfold plRefinement_func. intros. exists c1. split.
      -  unfold getFM_func. simpl.  unfold getFM_func in H0. destruct pl in H0.
        simpl in H0. destruct p in H0. simpl in H0. rewrite f in H0.
        rewrite fm. apply H0.
      - unfold getCK_func. unfold getAM_func. simpl.
        apply assetRefinementReflexivity_axiom.
    + unfold wfPL_func. intros.
      unfold equivalentFMs in H.
      intuition.
}{(*amRefinementCompositionality*)
   intros.
    split.
    + unfold plRefinement_func. intros. exists c1. split.
      -  unfold getFM_func. simpl.  unfold getFM_func in H0. destruct pl in H0.
        simpl in H0. destruct p in H0. simpl in H0. rewrite f in H0.
        rewrite fm. apply H0.
      - unfold getCK_func. unfold getAM_func. simpl.
        apply assetRefinementReflexivity_axiom.
    + unfold wfPL_func. intros.
      unfold equivalentFMs in H.
      intuition.

}{(*fullCompositionality*)
   intros.
    split.
    + unfold plRefinement_func. intros. exists c1. split.
      -  unfold getFM_func. simpl.  unfold getFM_func in H0. destruct pl in H0.
        simpl in H0. destruct p in H0. simpl in H0. rewrite f in H0.
        rewrite fm. apply H0.
      - unfold getCK_func. unfold getAM_func. simpl.
        apply assetRefinementReflexivity_axiom.
    + unfold wfPL_func. intros.
      unfold equivalentFMs in H.
      intuition.

}{(*weakFullCompositionality*)

   intros. 
    destruct H.   
    unfold plRefinement_func. 
    intros. exists c1.  split.
      +  unfold getFM_func. simpl.  unfold getFM_func in H1. destruct pl in H1.
        simpl in H1. destruct p in H1. simpl in H1. rewrite f in H1.
        rewrite fm. apply H1. 
      + unfold getCK_func. unfold getAM_func. simpl.
        apply assetRefinementReflexivity_axiom.

}{(*fullCompositionality2*)
   intros.
    split.
    + unfold plRefinement_func. intros. exists c1. split.
      -  unfold getFM_func. simpl.  unfold getFM_func in H0. destruct pl in H0.
        simpl in H0. destruct p in H0. simpl in H0. rewrite f in H0.
        rewrite fm. apply H0.
      - unfold getCK_func. unfold getAM_func. simpl.
        apply assetRefinementReflexivity_axiom.
    + unfold wfPL_func. intros.
      unfold equivalentFMs in H.
      intuition.

}{(*weakFullCompositionality2*)

    intros. 
    destruct H.   
    unfold plRefinement_func. 
    intros. exists c1.  split.
      +  unfold getFM_func. simpl.  unfold getFM_func in H1. destruct pl in H1.
        simpl in H1. destruct p in H1. simpl in H1. rewrite f in H1.
        rewrite fm. apply H1. 
      + unfold getCK_func. unfold getAM_func. simpl.
        apply assetRefinementReflexivity_axiom.

}{(*plRefAlt*)
  split.
        + intros.  apply equalsRefinementAlt. reflexivity.
        + intros. destruct H. unfold plRefinementAlt in H. unfold plRefinementAlt_func.
          intros p3 H1.
           specialize (H p3). apply H in H1. destruct H1. unfold plRefinementAlt_func in H0.
           specialize (H0 x). destruct H1. apply H0 in H1.
           destruct H1. destruct H1.  exists x0.  split.   
            - apply H1.
            - generalize H2, H3. apply assetRefinementTranstivity_axiom. 

}{(*strongerPLref*)
  intros.
    split.
    + apply equalsStrongerPL. reflexivity. 
    + unfold strongerPLrefinement_func. intros. destruct H. specialize (H c1). specialize (H1 c1).
      destruct c1. apply H in H0. destruct H0.
      split.
      - apply H1 in H0. destruct H0. apply H0.
      -  apply H1 in H0. destruct H0.  generalize H3. generalize H2. apply assetRefinementTranstivity_axiom.

}{(*plRef*)
  intros.
      split.
      + apply equalsPL. reflexivity.
      + unfold plRefinement_func. intros. destruct H. specialize (H c1).
        specialize (H1 c1). destruct c1. apply H in H0. destruct H0.
        destruct H0. destruct x. apply H1 in H0. destruct H0. destruct H0.
        exists x. split.
        - apply H0.
        - generalize H3. generalize H2. apply assetRefinementTranstivity_axiom.

} Qed.