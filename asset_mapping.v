Module AssetMapping.
Require Export maps assets.

  Import Maps Assets.
  Require Import Coq.Lists.ListSet.

  (** Um AM se trata de um map_*)
  Definition AM := map_.

  Variable am am1 am2: AM.
  Variable a1 a2 a3: Asset.
  Variable an an1 an2: Assets.AssetName.
  Variable anSet: set AssetName.
  Variable aSet S1 S2: set Asset.
  Variable defaultT: Maps.T.

  Definition pair : Type := AssetName * Asset.
  Definition pairs := set pair.


  (* Asset mapping refinement *)
  (** Para os mapeamentos de ativos A e A ', o último refina 
     o primeiro, denotado por A ⊑ A', sempre que:
     dom (A) = dom (A ') ∧ ∀ n ∈ dom (A) · A <n> ⊑ A' < n> *)
  Definition aMR (am1 am2: AM) : Prop := (dom am1 = dom am2) /\
    forall (an : AssetName), set_In an (dom am1) -> 
      exists (a1 a2: Asset), (isMappable am1 an a1) 
        /\ (isMappable am2 an a2)
          /\ (assetRef (set_add Asset_dec a1 nil) (set_add Asset_dec a2 nil)).

  (*Axiom <Asset refinement is pre-order>*)
  Axiom assetMappingRefinement:
    forall x y z: AM, aMR x x /\ aMR x y -> aMR y z ->  aMR x z.
 
  (*Asset mapping domain membership*)
  Lemma inDom :
    forall am (an: AssetName) (a: Asset), 
      isMappable am an a -> set_In an (dom am).
  Proof.
    intros am0 an0 a HMpb.
    induction am0. 
      - simpl in HMpb. contradiction.
      - apply isMappable_elim in HMpb.  inversion HMpb.
        clear HMpb. destruct H as [Heql1 Heql2].
        + rewrite Heql1. simpl. apply set_add_intro2. reflexivity.
        + simpl. apply set_add_intro1. apply IHam0.
          apply H.
        + intuition.
        + intuition.
    Qed.
  
  (*Asset mapping domain membership*)
  Lemma inImg :
    forall am (an: AssetName) (a: Asset), 
      isMappable am an a -> set_In a (img am).
  Proof.
    intros am0 an0 a HMpb.
    induction am0. 
      - simpl in HMpb. contradiction.
      - apply isMappable_elim in HMpb.  inversion HMpb.
        clear HMpb. destruct H as [Heql1 Heql2].
        + rewrite Heql2. simpl. apply set_add_intro2. reflexivity.
        + simpl. apply set_add_intro1. apply IHam0.
          apply H.
        + intuition.
        + intuition.
    Qed.

  Lemma amRefCompositional:
  forall am1 am2, aMR am1 am2 ->
    (unique am1) /\ (unique am2) ->
      forall anSet,
        forall aSet defaultT,
              assetRef (set_union Asset_dec aSet (maps defaultT am1 anSet)) 
                (set_union Asset_dec aSet (maps defaultT am2 anSet)) /\  
                  wfProduct (set_union Asset_dec aSet (maps defaultT am1 anSet)) ->
                    wfProduct (set_union Asset_dec aSet (maps defaultT am2 anSet)).
  Proof.
  induction am2.
  - induction am1.
    + induction aSet.
      { intros am2 am4 HAM Hunq anSet0 aSet0 defaulT0.
        destruct Hunq. intuition. }
      { intros am2 am4 HAM Hunq anSet0 aSet0 defaulT0.
        destruct Hunq. intuition. }
    + induction aSet.
      { intros. destruct H0. intuition. }
      { intros am2 am4 HAM Hunq anSet0 aSet0 defaulT0.
         destruct Hunq. intuition. }
  - induction am1.
    + induction aSet.
      { intros am2 am4 HAM Hunq anSet0 aSet0 defaulT0.
         destruct Hunq. intuition. }
      { intuition. }
    + induction aSet.
      { intuition. }
      { intuition. }
  Qed.

End AssetMapping.
