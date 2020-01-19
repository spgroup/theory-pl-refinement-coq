Require Export Coq.Lists.ListSet.
Require Export Coq.Lists.List.
Require Export Coq.Bool.Bool.
Require Export Coq.Classes.RelationClasses.
Require Export maps_int.

Class AssetTheory (A N m: Type) {Mp: Maps A N m} : Type :=  
{
  (*====================functions=======================*)

  wfProduct: set N -> Prop;
  assetRef : set N -> set N -> Prop;

  (*===========Axioms - Lemmas - Theorems====================*)  
  ANdec_eq : 
    forall x y: A, {x = y} + {x <> y};
  Asset_dec : 
    forall x y: N, {x = y} + {x <> y};
  assetRefinement:
    forall x y z: set N, assetRef x x /\ 
      assetRef x y -> assetRef y z ->  assetRef x z;
  asRefCompositional :
     forall (S1 : set N) (S2 : set N) (aSet : set N),
      (assetRef S1 S2) /\ wfProduct (union_t S1 aSet) 
        -> (wfProduct (union_t S2 aSet)) 
          /\ assetRef (union_t S1 aSet) 
             (union_t S2 aSet);
}. 