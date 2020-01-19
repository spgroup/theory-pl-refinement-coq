Require Export Coq.Lists.ListSet.
Require Export Coq.Lists.List.
Require Export Coq.Bool.Bool.
Require Export Coq.Classes.RelationClasses.
Require Export maps_def.
Require Export maps_int.
Require Export maps_inst.
Require Export maps_proofs.
Require Export assettheory_def.
Require Export formulatheory_def.
Require Export formulatheory_int.
Require Export formulatheory_inst.
Require Export formulatheory_proofs.
Require Export featuremodelsemantics_def.
Require Export featuremodelsemantics_int.
Require Export featuremodelsemantics_inst.
Require Export assettheory_int.
Require Export assettheory_inst.
Require Export assetmapping_def.
Require Export assetmapping_int. 
Require Export assetmapping_inst.
Require Export cktrans_int.
Require Export cktrans_def.
Import AssetMapping.
Import FormulaTheory.
Import Maps.
Import AssetTheory.
Import FeatureModelSemantics.
Import CKTrans.


Program Instance CKTrans_Inst : CKTrans CK Formula Item Transformation map_ Name AssetName Asset FM :=
{
  exps       := exps_func;
  getExp     := getExp_func;
  getRS      := getRS_func;
  transform  := transform_func;
  semanticsCK:= semanticsCK_func;
  semanticCK := semanticCK_func;
  semantics_ := semantics_func_;
  getNames   := getNames_func;
  unionCK    := unionCK_func;

}. Next Obligation.
{ (*similarFunctions*)
    induction ck.
      - induction amt.
        + induction am. 
          * intros. simpl. reflexivity.
          * intros. simpl. reflexivity.
        + induction amt.
          * intros. simpl. reflexivity.
          * intros. simpl. reflexivity.
      - induction amt.
        + induction am. 
          * intros. simpl. intuition. admit.
          * intros. simpl. intuition. admit.
        + induction amt.
          * intros. simpl. intuition. admit.
          * intros. simpl. intuition. admit.

} Admitted.
 Next Obligation.
{ (*compAmRefEmptyset*)
  induction am1.
      - induction am2.
        + induction ck.
          { apply H2. }
          { intros. intuition. }
        + induction ck.
          { intros. intuition. }
          { intuition. }
      - induction am2.
        + induction ck.
          { intuition. }
          { intuition. }
        + induction ck.
          { intuition. }
          { intuition. }

} Qed. 
  Next Obligation.
{ (*compAmRef*)
     induction am1.
      - induction am2.
        + induction ck.
          { intuition. }
          { intuition. }
        + induction ck.
          { intuition. }
          { intuition. }
      - induction am2.
        + induction ck.
          { intuition. }
          { intuition. }
        + induction ck.
          { intuition. }
          { intuition. }

} Qed.
  Next Obligation.
{ (*addItemsBefore*)
  admit.

} Admitted.
  Next Obligation.
{ (*addItemsAfter*)
  admit.

} Admitted.
