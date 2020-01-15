Require Export featuremodel_spl_int.
Require Export featuremodel_spl_def.
Import FeatureModelSPL.

Require Import Coq.Lists.ListSet.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Specif.
Require Export Coq.Lists.List.

  Lemma equals: forall fm1 fm2, fm1 = fm2 -> equivalentFMs_func fm1 fm2.
    Proof.
    intros.
    unfold equivalentFMs_func.
    unfold FMRefinement_func. 
    rewrite H. split.  
    - rewrite equalsSetDiff.
      + trivial.
      + reflexivity.
    - rewrite equalsSetDiff.
      + trivial.
      + reflexivity.
    Qed.


