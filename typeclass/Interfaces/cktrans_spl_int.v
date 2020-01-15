Require Import Coq.Lists.ListSet.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Specif.
Require Export Coq.Lists.List.

Class CKTrans (F A AM ck Conf: Type): Type :=
{
  (*====================functions=======================*)
  CKSem         : ck -> AM -> Conf -> set A;
  CKConf        : ck -> set Conf;
  equivalentCKs : ck -> ck -> Prop;
  weakerEqCK    : F -> ck -> ck -> Prop;

  (*===========Axioms - Lemmas - Theorems====================*)
  eqCK:
    forall ck1: ck, equivalentCKs ck1 ck1 /\
      (forall ck1 ck2: ck, equivalentCKs ck1 ck2 
        -> equivalentCKs ck2 ck1) /\
         (forall ck1 ck2 ck3: ck, equivalentCKs ck1 ck2
           /\ equivalentCKs ck2 ck3 -> equivalentCKs ck1 ck3);
  weakerEqReflexive: 
    forall (fm: F) (ck1: ck),
      weakerEqCK fm ck1 ck1;
  weakerEqSymmetric:
    forall (fm: F) (ck1 ck2: ck),
        weakerEqCK fm ck1 ck2 -> weakerEqCK fm ck2 ck1;
  weakerEqTransitive:
     forall (fm: F) (ck1 ck2 ck3: ck),
        weakerEqCK fm ck1 ck2 -> weakerEqCK fm ck2 ck3 
          -> weakerEqCK fm ck1 ck3
  
}.