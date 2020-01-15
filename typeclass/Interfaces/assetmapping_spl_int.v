Require Import Coq.Lists.ListSet.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Specif.
Require Export Coq.Lists.List.

Class AssetMapping (A N m: Type): Type :=
{
  (*====================functions=======================*)
  assetRef  : set A -> set A -> Prop;
  wfProduct : set A -> Prop;
  aMR       : m -> m -> Prop;

  (*===========Axioms - Lemmas - Theorems====================*)
  assetRefinementReflexivity : 
    forall x: set A, assetRef x x;
  assetRefinementTranstivity : 
    forall x y z: set A, 
      assetRef x y -> assetRef y z ->  assetRef x z;
  as_dec                     : 
      forall x y:A, {x = y} + {x <> y};
  asRefCompositional         :  
    forall (S1 : set A) (S2 : set A) (aSet : set A),
      (assetRef S1 S2) /\ wfProduct (set_union as_dec S1 aSet) 
        -> (wfProduct (set_union as_dec S2 aSet)) 
          /\ assetRef (set_union as_dec S1 aSet) 
             (set_union as_dec S2 aSet);
  assetMappingRefinement: 
    forall x y z: m, 
      aMR x x /\ aMR x y -> aMR y z ->  aMR x z;
}.