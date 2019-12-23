Require Import Coq.Lists.ListSet.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Specif.
Require Export Coq.Lists.List.

Class FeatureModel (F Conf: Type) : Type :=
{
  FMRef        : F -> set Conf;
  FMRefinement : F -> F -> Prop;
  equivalentFMs: F -> F -> Prop;
  eqFM : 
    forall fm1: F, equivalentFMs fm1 fm1 /\
      (forall fm1 fm2: F,equivalentFMs fm1 fm2 -> equivalentFMs fm2 fm1) /\
         (forall fm1 fm2 fm3: F, equivalentFMs fm1 fm2 /\ equivalentFMs fm2 fm3 -> equivalentFMs fm1 fm3);
  refFM:
   forall fm1 fm2 fm3: F, FMRefinement fm1 fm2 -> FMRefinement fm2 fm3 -> FMRefinement fm1 fm3
}.