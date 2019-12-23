Module AssetTheory.
Require Export Coq.Lists.ListSet.
Require Export Coq.Lists.List.
Require Export Coq.Bool.Bool.
Require Export Coq.Classes.RelationClasses.
Require Export maps_def.
Import Maps.


  Definition Asset : Type := T.
  Definition AssetName : Type := S.

  Variable a a1 a2 a3 : Asset.
  Variable aSet S1 S2 : set Asset.
  
  (* Decidibilidade *)
  Axiom ANdec_eq_axiom : 
    forall x y: AssetName, {x = y} + {x <> y}.
  Axiom Asset_dec_axiom : 
    forall x y: Asset, {x = y} + {x <> y}.

  (*Assumption <Assets refinement>*)
  Parameter inline assetRef_func : 
    set Asset -> set Asset -> Prop.

  Inductive wfProduct_ind (aSet : set Asset) : Prop.

  (*Axiom <Asset refinement is pre-order>*)

  Axiom assetRefinement_axiom:
    forall x y z: set Asset, assetRef_func x x /\ 
      assetRef_func x y -> assetRef_func y z ->  assetRef_func x z.


   (*Axiom 5 <Asset refinement compositionality>*)
  Axiom asRefCompositional_axiom :
    forall (S1 : set Asset) (S2 : set Asset) (aSet : set Asset),
      (assetRef_func S1 S2) /\ wfProduct_ind (union_t_func  S1 aSet) 
        -> (wfProduct_ind (union_t_func  S2 aSet)) 
          /\ assetRef_func (union_t_func  S1 aSet) 
             (union_t_func S2 aSet).

End AssetTheory.