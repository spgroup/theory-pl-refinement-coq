Module AssetMapping.
Require Export Coq.Lists.ListSet.
Require Export Coq.Lists.List.
Require Export Coq.Bool.Bool.
Require Export Coq.Classes.RelationClasses.
Require Export maps_def.
Require Export assettheory_def.
Require Export formulatheory_def.
Require Export featuremodelsemantics_def.
Require Export assettheory_int.
Require Export assettheory_inst.
Import FormulaTheory.
Import Maps.
Import AssetTheory.
Import FeatureModelSemantics.


  Definition pair : Type := AssetName * Asset.
  Definition pairs := set pair.
  (** Um AM se trata de um map_*)
  Definition AM := map_.


  (* Asset mapping refinement *)
  (** Para os mapeamentos de ativos A e A ', o último refina 
     o primeiro, denotado por A ⊑ A', sempre que:
     dom (A) = dom (A ') ∧ ∀ n ∈ dom (A) · A <n> ⊑ A' < n> *)
  Definition aMR_func (am1 am2: AM) : Prop := (dom_func am1 = dom_func am2) /\
    forall (an : AssetName), set_In an (dom_func am1) -> 
      exists (a1 a2: Asset), (isMappable_func am1 an a1) 
        /\ (isMappable_func am2 an a2)
          /\ (assetRef_func (set_add Asset_dec a1 nil) (set_add Asset_dec a2 nil)). 

  (*Axiom <Asset refinement is pre-order>*)
  Axiom assetMappingRefinement_axiom:
    forall x y z: AM, aMR_func x x /\ aMR_func x y -> aMR_func y z ->  aMR_func x z.


End AssetMapping.
