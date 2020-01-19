Module AssetMappingSPL.
Require Export assetmapping_spl_int.
Require Export maps_proofs.
Require Export maps_inst.
Require Export maps_int.
Require Export maps_def.
Require Import Coq.Lists.ListSet.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Specif.
Require Export Coq.Lists.List.
Import Maps.


  Definition Asset : Type     := T.
  Definition AssetName : Type := S.

  (*Assumption <Assets refinement>*)
  Parameter assetRef_func : 
    set Asset -> set Asset -> Prop.

  Inductive wfProduct_ind (aSet : set Asset) : Prop.

  Axiom assetRefinementReflexivity_axiom:
    forall x: set Asset, assetRef_func x x.

  Axiom assetRefinementTranstivity_axiom:
    forall x y z, assetRef_func x y -> assetRef_func y z ->  assetRef_func x z.

  Axiom as_dec_axiom : forall x y:Asset, {x = y} + {x <> y}.
  Axiom an_dec_axiom : forall x y:AssetName, {x = y} + {x <> y}.
  Definition my_set_union_func (S1 S2: set Asset): set Asset :=
   set_union as_dec_axiom S1 S2.


  Axiom asRefCompositional_axiom :
    forall (S1 : set Asset) (S2 : set Asset) (aSet : set Asset),
      (assetRef_func S1 S2) /\ wfProduct_ind (set_union as_dec_axiom S1 aSet) 
        -> (wfProduct_ind (set_union as_dec_axiom S2 aSet)) 
          /\ assetRef_func (set_union as_dec_axiom S1 aSet) 
             (set_union as_dec_axiom S2 aSet). 

  Definition AM := map_.

 Definition aMR_func (am1 am2: AM) : Prop := (dom_ am1 = dom_ am2) /\
    forall (an : AssetName), set_In an (dom_ am1) -> 
      exists (a1 a2: Asset), (isMappable_ am1 an a1) 
        /\ (isMappable_ am2 an a2)
          /\ (assetRef_func (set_add as_dec_axiom a1 nil) (set_add as_dec_axiom a2 nil)).
  
  (*Axiom <Asset refinement is pre-order>*)
  Axiom assetMappingRefinement_axiom:
    forall x y z: AM, aMR_func x x /\ aMR_func x y -> aMR_func y z ->  aMR_func x z.

End AssetMappingSPL.