Require Import Coq.Lists.ListSet.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Specif.
Require Export Coq.Lists.List.

Class AssetMapping (A N m: Type): Type :=
{
  (*====================functions=======================*)
  assetRef    : set A -> set A -> Prop;
  wfProduct   : set A -> Prop;
  aMR         : m -> m -> Prop;
  my_set_union: set A -> set A -> set A;

  (*===========Axioms - Lemmas - Theorems====================*)
  assetRefinementReflexivity : 
    forall x: set A, assetRef x x;
  assetRefinementTranstivity : 
    forall x y z: set A, 
      assetRef x y -> assetRef y z ->  assetRef x z;
  asRefCompositional         :  
    forall (S1 : set A) (S2 : set A) (aSet : set A),
      (assetRef S1 S2) /\ wfProduct (my_set_union S1 aSet) 
        -> (wfProduct (my_set_union S2 aSet)) 
          /\ assetRef (my_set_union S1 aSet) 
             (my_set_union S2 aSet);
  assetMappingRefinement: 
    forall x y z: m, 
      aMR x x /\ aMR x y -> aMR y z ->  aMR x z;
}.