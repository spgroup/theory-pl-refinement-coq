Module Assets.
Require Export maps.
  Import Maps.
  Require Import Coq.Lists.ListSet. 

  Definition Asset : Type := Maps.T.
  Definition AssetName : Type := Maps.S.

  Variable a a1 a2 a3 : Asset.
  Variable aSet S1 S2 : set Asset.

  (* Decidibilidade *)
  Axiom ANdec_eq : forall x y: Asset, {x = y} + {x <> y}.
  Axiom Asset_dec : forall x y: Asset, {x = y} + {x <> y}.

  (*Assumption <Assets refinement>*)
  Parameter inline assetRef : 
    set Asset -> set Asset -> Prop.

  Notation "|-" := assetRef (at level 70).

  Inductive wfProduct (aSet : set Asset) : Prop.
  Lemma wfaux: forall aSet, True -> wfProduct aSet.
  intuition.
  Qed.
(*produto é bem formado*)
  Record Product : Type := {
    setA:> set Asset;
    wfm:> Prop; }.

  (*Axiom <Asset refinement is pre-order>*)

  Axiom assetReflexivity:
    forall x: set Asset, |- x x.

  Axiom assetTransitivity:
    forall x y z: set Asset, 
      |- x y -> |- y z ->  |- x z.

  Axiom assetRefinement:
    forall x y z: set Asset, |- x x /\ 
      |- x y -> |- y z ->  |- x z.


  (*Axiom 5 <Asset refinement compositionality>*)
  (*refinar um conjunto de assets que faz parte de um produto bem
     formado produz um produto bem formado refinado*)
  Axiom asRefCompositional :
    forall S1 S2 aSet,
      (|- S1 S2) /\ wfProduct (union_t  S1 aSet) 
        -> wfProduct (union_t S2 aSet) /\ assetRef (union_t S1 aSet) (union_t S2 aSet).

End Assets.