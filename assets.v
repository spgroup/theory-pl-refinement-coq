Module Assets.
Require Export maps.
  Import Maps.
  Require Import Coq.Lists.ListSet. 

  (** Esse mapeamento trata da especificação do Asset da Teoria 
    de Refinamento de Linhas de produtos*)

  (* O AM é o mapeamento do nome do Asset para o Asset propriamente dito, logo 
      definimos Asset e Asset Name como se segue *)
  Definition Asset : Type := Maps.T.
  Definition AssetName : Type := Maps.S.

  Variable a a1 a2 a3 : Asset.
  Variable aSet S1 S2 : set Asset.
  
  (* Decidibilidade *)
  Axiom ANdec_eq : 
    forall x y: Asset, {x = y} + {x <> y}.
  Axiom Asset_dec : 
    forall x y: Asset, {x = y} + {x <> y}.

  (*Assumption <Assets refinement>*)
  Parameter inline assetRef : 
    set Asset -> set Asset -> Prop.

  Inductive wfProduct (aSet : set Asset) : Prop.
  Definition Product (aSet : set Asset) : Type := wfProduct aSet.

  (*Axiom <Asset refinement is pre-order>*)

  Axiom assetRefinement:
    forall x y z: set Asset, assetRef x x /\ 
      assetRef x y -> assetRef y z ->  assetRef x z.


  (*Axiom 5 <Asset refinement compositionality>*)
  Axiom asRefCompositional :
    forall (S1 : set Asset) (S2 : set Asset) (aSet : set Asset),
      (assetRef S1 S2) /\ wfProduct (Maps.union_t  S1 aSet) 
        -> (wfProduct (Maps.union_t  S2 aSet)) 
          /\ assetRef (Maps.union_t  S1 aSet) 
             (Maps.union_t S2 aSet).

  Theorem assetTest:
  forall (S T x y : set Asset) (a b : Asset),
    wfProduct x /\ (assetRef S T) /\ (set_In a x) /\ 
      (assetRef (set_add Asset_dec a nil) (set_add Asset_dec b nil))
        /\ (x = set_add Asset_dec a S) /\ (y = set_add Asset_dec b T) 
          -> assetRef x y.
  Proof.  
  Admitted.

End Assets.
