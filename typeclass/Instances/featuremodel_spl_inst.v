Require Export featuremodel_spl_proofs.
Require Export featuremodel_spl_int.
Require Export featuremodel_spl_def.
Import FeatureModelSPL.

Require Import Coq.Lists.ListSet.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Specif.
Require Export Coq.Lists.List.

Program Instance Ins_FeatureModel: FeatureModel FM Conf :=
{
  FMRef := FMRef_Func;
  FMRefinement := FMRefinement_func;
  equivalentFMs := equivalentFMs_func;
}.
 Next Obligation.
  { (* eqFM*)
    intros.
    split.
      + rewrite fm1. apply equals. reflexivity.
      + split. 
        - intros. rewrite fm0, fm2. rewrite fm0, fm2 in H. apply H.
        - intros. destruct H. rewrite fm0, fm3. rewrite fm2, fm3 in H0. apply H0.
} Qed. Next Obligation. { (*refFM*)
      intros. rewrite fm3, fm1. rewrite fm1 in H. rewrite fm2 in H. apply H.
}  Qed.