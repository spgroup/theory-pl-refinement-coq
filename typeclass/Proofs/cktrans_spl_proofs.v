Require Export cktrans_spl_int.  
Require Export cktrans_spl_def.   
Require Export featuremodel_spl_def.
Import CKTransSPL.
Import FeatureModelSPL.

Lemma equalsCK:
  forall ck1 ck2, ck1 = ck2 -> equivalentCKs_func ck1 ck2.
    Proof.
    intros.
    rewrite H.
    unfold equivalentCKs_func. 
    unfold equivalentCKsAux. split.
    + rewrite equalsSetDiff.
      - trivial.
      - reflexivity.
    + rewrite equalsSetDiff.
      - trivial.
      - reflexivity.
     Qed.