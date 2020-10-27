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
Require Export ckcomp_int.
Require Export ckcomp_def.
Require Export assetmapping_spl_int.
Require Export assetmapping_spl_def.
Import AssetMappingSPL.
Import FormulaTheory.
Import Maps.
Import AssetTheory.
Import FeatureModelSemantics.
Import CKComp.


Program Instance CKComp_Inst : CKComp CK Configuration Formula Item map_ Name AssetName Asset FM :=
{
    getExp       := getExp_func;
    getRS        := getRS_func;
    exps         := exps_func;
    SetCompAux   := SetCompAux_func;
    evalCK       := evalCK_func;
    assetsCK     := assetsCK_func;
    imgCK        := imgCK_func;
    eval         := eval_func;
    eval2        := eval2_func;
    notshowupItem:= notshowupItem_func;
    showupItem   := showupItem_func;
    semantics_   := semantics_func_;
    wfCK         := wfCK_func;
    wfCK2        := wfCK2_func;
    ckEq         := ckEq_func;
    ckEq2        := ckEq2_func;
    renameCKitem := renameCKitem_func;
    renameCKitem_:= renameCKitem_func_;
    renamecK     := renamecK_func;

}. Next Obligation.
{ 
  apply as_dec_axiom.

} Qed. Next Obligation.
{
  apply its_dec_axiom.
} Qed. Next Obligation.
{
  apply its_dec_axiom.
} Qed. Next Obligation.
{
  induction ck.
  - intros.
    simpl. reflexivity. 
  - admit.
} Admitted. Next Obligation.
{ admit.

} Admitted. Next Obligation.
{ 
  intros. unfold ckEq_func.
  intros. reflexivity.

} Qed. Next Obligation.
{
  unfold ckEq_func. unfold ckEq_func in H. intros. specialize (H c). 
  intuition.
} Qed. Next Obligation.
{
  unfold ckEq_func. unfold ckEq_func in H. unfold ckEq_func in H0. intros.
  specialize (H0 c). specialize (H c).
  intuition. rewrite H2, H. reflexivity.
} Qed. Next Obligation.
{
  unfold ckEq2_func. reflexivity.
}Qed. Next Obligation.
{
  unfold ckEq2_func.   unfold ckEq2_func in H. rewrite H. reflexivity.
} Qed. Next Obligation.
{
  unfold ckEq2_func. unfold ckEq2_func in H. unfold ckEq2_func in H0. 
  rewrite H, H0. reflexivity.
} Qed. Next Obligation.
{
  unfold not. intros. unfold not in H. apply H.
  unfold ns_func. unfold wfCK_func in H1. destruct H1. intuition. 
  admit.
} Admitted.














