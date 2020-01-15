Require Export cktrans_spl_int.
Require Export cktrans_spl_def.
Require Export cktrans_spl_proofs.
Require Import Coq.Lists.ListSet.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Specif.
Require Export Coq.Lists.List.
Import CKTransSPL.  
Require Export featuremodel_spl_def.
Import FeatureModelSPL.
Require Export assetmapping_spl_def.
Import AssetMappingSPL.  

Program Instance Ins_CKTrans: CKTrans FM Asset AM CK Conf :=
{
  CKSem         := CKSem_func;
  CKConf        := CKConf_func;
  equivalentCKs := equivalentCKs_func;
  weakerEqCK    := weakerEqCK_func;
}. Next Obligation.
{ (*eqCK*)
  intros.
    split.
    + rewrite ck1. apply equalsCK. reflexivity.
    + split. 
      - intros. rewrite ck0, ck2. rewrite ck0, ck2 in H. apply H.
      - intros. destruct H. rewrite ck0, ck3. rewrite ck0, ck2 in H. apply H.
} 
Qed. Next Obligation. { (*weakerEqReflexive*)
      intros. unfold weakerEqCK_func. intros. reflexivity.
} Qed. Next Obligation.
{ (*weakerEqSymmetric*)
       intros. rewrite ck2, ck1. rewrite ck1, ck2 in H.
      apply H.
} Qed. Next Obligation. { (*weakerEqTransitive*)
      intros.
      rewrite ck1, ck3. rewrite ck2, ck3 in H0.
      apply H0.
} Qed. 