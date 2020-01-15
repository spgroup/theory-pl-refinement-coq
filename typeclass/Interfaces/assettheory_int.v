Require Export Coq.Lists.ListSet.
Require Export Coq.Lists.List.
Require Export Coq.Bool.Bool.
Require Export Coq.Classes.RelationClasses.
Require Export maps_int.

Class AssetTheory (A N m: Type) {Mp: Maps A N m} : Type :=  
{
  wfProduct: set N -> Prop;
  ANdec_eq : 
    forall x y: A, {x = y} + {x <> y};
  Asset_dec : 
    forall x y: N, {x = y} + {x <> y};
  assetRef: set N -> set N -> Prop;
  assetRefinement:
    forall x y z: set N, assetRef x x /\ 
      assetRef x y -> assetRef y z ->  assetRef x z;
  asRefCompositional :
     forall (S1 : set N) (S2 : set N) (aSet : set N),
      (assetRef S1 S2) /\ wfProduct (union_t S1 aSet) 
        -> (wfProduct (union_t S2 aSet)) 
          /\ assetRef (union_t S1 aSet) 
             (union_t S2 aSet);
  assetTest:
  forall (S1 S2 x y : set N) (a b : N),
    wfProduct x /\ (assetRef S1 S2) /\ (set_In a x) /\ 
      (assetRef (set_add Asset_dec a nil) (set_add Asset_dec b nil))
        /\ (x = set_add Asset_dec a S1) /\ (y = set_add Asset_dec b S2) 
          -> assetRef x y 
}. 