Require Export Coq.Lists.ListSet.
Require Export Coq.Lists.List.
Require Export Coq.Bool.Bool.
Require Export Coq.Classes.RelationClasses.
Require Export maps_int.
Require Export assettheory_int.


Class AssetMapping (A N m: Type) {Mp: Maps A N m} {As: AssetTheory A N m}: Type := {
  aMR : m -> m -> Prop;
  assetMappingRefinement:
    forall x y z: m, aMR x x /\ aMR x y -> aMR y z ->  aMR x z;
  amRefCompositional:
    forall (am1 am2: m), aMR am1 am2 ->
      (unique_ am1) /\ (unique_ am2) ->
        forall (anSet: set A),
          forall (aSet: set N) (defaultT: N),
              assetRef (set_union Asset_dec aSet (maps defaultT am1 anSet)) 
                (set_union Asset_dec aSet (maps defaultT am2 anSet)) /\  
                  wfProduct (set_union Asset_dec aSet (maps defaultT am1 anSet)) ->
                    wfProduct (set_union Asset_dec aSet (maps defaultT am2 anSet))

}.