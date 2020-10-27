Module SpecificSPL. 

Require Export maps_int formulatheory_int featuremodelsemantics_int assettheory_int
               assetmapping_int featuremodelrefinement_int.

Require Export maps_def formulatheory_def featuremodelsemantics_def featuremodelrefinement_def
               assettheory_def assetmapping_def ckcomp_int ckcomp_def.

Import FormulaTheory FeatureModelSemantics AssetTheory AssetMapping CKComp
       Maps FeatureModelRefinimentTheory.

Require Export formulatheory_inst featuremodelsemantics_inst assettheory_inst maps_inst
               assetmapping_inst featuremodelrefinement_inst  ckcomp_inst.

Require Import Coq.Lists.ListSet.

  Variable fm fm1 fm2: FM.
  Variable am am1 am2 pairs: AM.
  Variable ck ck1 ck2: CK.
  Variable item item1 item2: Item.
  Variable items items1 items2: set Item. 
  Variable c c1 c2: Configuration.
  Variable expr: Formula.
  Variable Fe G H opt: Name.
  Variable a a1 a2 a3: Asset.
  Variable an an1 an2: AssetName.


  Axiom item_dec : forall x y:Item, {x = y} + {x <> y}.
  Axiom pair_dec : forall x y:pair_, {x = y} + {x <> y}.
  Axiom ns_dec : forall   x y:Name, {x = y} + {x <> y}.
  Axiom an_dec : forall   x y:AssetName, {x = y} + {x <> y}.
  Axiom as_dec : forall   x y:AssetName, {x = y} + {x <> y}.

Require Export spl_int spl_def spl_proofs spl_inst.
Import SPL.

  (*========= IF WE ADD NEW ASSETS TO AM THAT DID NOT EXIST BEFORE, 
              CK EVALUATION IS THE SAME =============*)
  Lemma mapSubsetAM :
   forall fm am1 am2 ck,
    forall an, set_In an (dom_func am2) -> ~(set_In an (dom_func am1)) /\
      wfCK_func fm am1 ck   
        -> forall (c: Configuration), set_In c (semantics fm)
          -> (semantics_func_ ck am1 c =
              semantics_func_ ck (set_union pair_dec am1 am2) c).
  Proof.
  unfold wfCK_func.
  induction am4.
  + induction am3.
    - simpl. intuition.
    - simpl. intuition. 
  + intuition. specialize (IHam4 ck0 an0). 
    apply set_add_elim in H0. intuition.
Admitted. 

 (*============= REPLACE FEATURE EXPRESSION ==================*)


  Definition syntaxReplaceFeatureExp ck1 ck2 item1 item2 items: Prop:=
    (ck1 =  app (items :: nil) (item1 :: nil) ) /\
      (ck2 = app (items :: nil) (item2 :: nil)) /\
        item1.(assets) = item2.(assets).  
 
 Definition conditionsReplaceFeatureExp (fm:FM) item1 item2: Prop :=
    wt fm (item2.(exp)) /\
      forall c, set_In c (semantics fm) ->
        iff (satisfies (item1.(exp)) c) (satisfies (item2.(exp)) c).  

 Theorem replaceFeatureExp_EqualCKeval 
    {Mp: Maps Asset AssetName AM}
      {Ft: FormulaTheory Formula Name FM}
        {FtM: FeatureModel FM Configuration} 
          {AssetM: AssetMapping Asset AssetName AM} 
            {ckTrans: CKTrans FM Asset AM CK Configuration} 
              {SPL: SPL Asset Configuration FM AM CK PL}: 
    forall (pl: PL) ck2 item1 item2 items,
      (
        (
         wfCK_func (getFM pl) (getAM pl) (getCK pl) /\
          syntaxReplaceFeatureExp (getCK pl) ck2 item1 item2 items /\
           conditionsReplaceFeatureExp (getFM pl) item1 item2
       )
         ->
          forall (c: Configuration), set_In c (semantics (getFM pl))
            -> semantics_ (getCK pl)(getAM pl) c 
              = semantics_ ck2 (getAM pl) c
       ).
  Proof.
  intros. destruct H0. destruct H2. 
  unfold syntaxReplaceFeatureExp in H2. destruct H2.
  destruct H4. rewrite H4. rewrite H2. simpl. 
  induction item4. induction item3.
  simpl in H5. rewrite H5.  intuition. 
  Qed.

 Theorem replaceFeatureExpression 
    {Mp: Maps Asset AssetName AM}
      {Ft: FormulaTheory Formula Name FM}
        {FtM: FeatureModel FM Configuration} 
          {AssetM: AssetMapping Asset AssetName AM} 
            {ckTrans: CKTrans FM Asset AM CK Configuration} 
              {SPL: SPL Asset Configuration FM AM CK PL}: 
    forall (pl: PL) ck2 item1 item2 items,
      (
        (
         wfCK_func (getFM pl) (getAM pl) (getCK pl) /\
          syntaxReplaceFeatureExp (getCK pl) ck2 item1 item2 items /\
           conditionsReplaceFeatureExp (getFM pl) item1 item2
       )
         ->
          plRefinement_func pl (gerPL fm2 (getAM pl) ck2) /\
          wfCK_func (getFM pl) (getAM pl) ck2 /\
          wfPL (gerPL fm2 (getAM pl) ck2)         
       ).
  Proof. 
(*unfold plRefinement_func.
  intros pl  ck item3 item4 items0 H. split.
  +  intros c.  intros.
     apply (replaceFeatureExp_EqualCKeval c) in H.
  + unfold plRefinement_func.  intros. exists c3. split.
      -  destruct gerPL. unfold getFM_func. simpl.  unfold getFM_func in H2. destruct pl in H2. 
        simpl in H2. destruct pls1. simpl in H2. destruct p.
        destruct pls0.  simpl in H2. destruct p.
        simpl in H2. destruct f, f0. simpl. apply H2. 
    -  

specialize (H7 an). destruct H7. destruct H10. destruct G, F.
        intuition.
  + intros. unfold syntaxReplaceFeatureExp in H0. destruct H0.
  destruct H2. rewrite H2.
  symmetry in H4. simpl.
  induction item4. induction item3.
  simpl in H4, H1, H2, H3. rewrite H4. intuition.
  Search wfCK_func. rewrite H0 in H1.
  simpl in H1. unfold conditionsReplaceFeatureExp in H3.
  destruct H3. Search satisfies.*)
Admitted.


 (*==================  ADD MANDATORY FEATURE ======================*)


(* FOR ALL PRODUCTS OF A FM, EVALUATING THE CK WITH A DEAD FEATURE IS EQUIVALENT TO EVALUATING THE CK WITHOUT IT*)

 Theorem evalCKdeadFeature 
  {Mp: Maps Asset AssetName AM}
    {Ft: FormulaTheory Formula Name FM}
      {FtM: FeatureModel FM Configuration} 
        {AssetM: AssetMapping Asset AssetName AM} 
          {ckTrans: CKTrans FM Asset AM CK Configuration} 
            {SPL: SPL Asset Configuration FM AM CK PL} 
              {FormT: FormulaTheory Formula Name FM}
                {FMS: FeatureModelSemantics Formula FM Name}
                  {FMR: FeatureModelRefinement Formula Name FM}:
    forall pl (opt: Name),
      ~(set_In opt (nsf_func ((fst(fst pl))))) /\
        wfCK (fst(fst pl)) (snd(fst pl)) (snd pl) 
          -> forall c, set_In c (semantics_func (fst(fst pl)))
            -> semantics_func_ (snd pl) (snd(fst pl)) c = 
              semantics_func_ (snd pl) (snd(fst pl)) (app (opt:: nil) c). 
  Proof. 
  simpl. intuition. simpl. simpl in H1, H2, H0. unfold nsf_func in H1. 
  destruct a4. simpl in H1, H2, H0. destruct f. intuition.
  destruct opt0, n.  simpl in H1. intuition.  
  Qed.


 Definition syntaxConditionsAddMandatoryFeature (fm1 fm2: FM) (F G: Name) 
  {FormT: FormulaTheory Formula Name FM} {FMS: FeatureModelSemantics Formula FM Name }
  {FMR: FeatureModelRefinement Formula Name FM}: Prop :=
    addMandatoryNode_func fm1 fm2 F G. 


 (*ADDING A MANDATORY FEATURE G WITHOUT CHANGING CK AND AM IS PL REFINEMENT*)

 Theorem addMandatoryFeat 
    {Mp: Maps  AssetName Asset AM}
      {FtM: FeatureModel FM Configuration} 
        {AssetM: AssetMapping Asset AssetName AM} 
          {ckTrans: CKTrans FM Asset AM CK Configuration} 
            {SPL: SPL Asset Configuration FM AM CK PL} 
              {FormT: FormulaTheory Formula Name FM} 
                {FMS: FeatureModelSemantics Formula FM Name }
                  {FMR: FeatureModelRefinement Formula Name FM}:
    forall (pl: PL) (F G: Name) (fm2: FM),
      (
        syntaxConditionsAddMandatoryFeature (getFM pl) fm2 F G /\
          wfCK (getFM pl) (getAM pl) (getCK pl)
            ->
            plRefinement_func pl (gerPL fm2 (getAM pl) (getCK pl)) 
              /\ wfCK fm2 (getAM pl) (getCK pl)
                /\ wfPL (gerPL fm2 (getAM pl) (getCK pl))
       ). 
  Proof.
 intuition. simpl. unfold syntaxConditionsAddMandatoryFeature in H1.
 unfold addMandatoryNode_func in H1. destruct F, G0.
 intuition. unfold syntaxConditionsAddMandatoryFeature in H1.
 unfold addMandatoryNode_func in H1. destruct F, G0.
 intuition. unfold syntaxConditionsAddMandatoryFeature in H1.
 unfold addMandatoryNode_func in H1. destruct F, G0.
 intuition.
Qed.

(* =============SPLIT ASSETS====================*)

  (* SPLIT ASSETS conditions *)
  
 Definition syntaxSplitAssets am1 am2 (ck1 ck2:CK) (item1 item2: Item) items
              (an1 an2: AssetName) (a1 a2 a3: Asset) pairs: Prop :=  
    am1 = set_add pair_dec (an1, a1)  pairs /\
    am2 = set_add pair_dec (an1, a2) (set_add pair_dec (an2, a3) pairs) /\
    ck1 =  app (item1::nil) items /\
    ck2 = app (item2::nil) items /\
      item1.(exp) = item2.(exp) /\
    item1.(assets) =  set_add an_dec an1 nil /\ 
    item2.(assets) = set_add an_dec an1 (an2::nil). 
  
  Definition conditionsSplitAssets a1 a2 a3 an1 an2 items: Prop :=
    assetRef_func (a1::nil) (app (a2::nil) (a3::nil)) /\
      forall (item: Item), set_In item items
        -> ~(set_In an1 (item.(assets))) /\
          (~ set_In an2 (item.(assets))).  

  Lemma same_add: forall (p:pair_) pairs, set_add pair_dec p pairs = 
        set_add pair_dec p (set_add pair_dec p pairs).
  Proof.
  intros. induction p.
  unfold set_add. induction pairs0.
  - case_eq (pair_dec (a0,b) (a0,b)).
    + intros. reflexivity.
    + intros. intuition.
  - intuition. case_eq (pair_dec (a0, b) a4).
    + intros. rewrite e. case_eq (pair_dec (a0,b) a4).
      * intros. case_eq (pair_dec a4 a4).
        { intuition. }
        { intuition. }
      * intuition.
    + intuition. rewrite IHpairs0. intuition.
      induction a4. simpl. intuition. 
      case_eq (pair_dec (a0, b) (a4, b0)).
        {intuition. }
        { intuition. destruct a0, b, a4, b0. 
          intuition. }
Qed.


Theorem splitNotEvalItem 
  {Mp: Maps Asset AssetName AM}
   {Ft: FormulaTheory Formula Name FM}
    {FtM: FeatureModel FM Configuration}
     {AssetM: AssetMapping Asset AssetName AM} 
      {ckTrans: CKTrans FM Asset AM CK Configuration} 
       {SPL: SPL Asset Configuration FM AM CK PL}:
     forall pl am2 ck2 item1 item2 a1 a2 a3 an1 an2 items pairs,
  (
    ( 
        wfCK_func (fst(fst pl)) (snd(fst pl)) (snd pl) /\
          syntaxSplitAssets (snd(fst pl)) am2 (snd pl) ck2 item1 item2 items an1 an2 a1 a2 a3 pairs /\
            conditionsSplitAssets a1 a2 a3 an1 an2 items
    )
    ->
      forall c, set_In c (semantics_func (fst(fst pl))) /\
        ~(satisfies_func (item1.(exp)) c)
          -> semantics_func_ (snd pl) (snd(fst pl)) c = semantics_func_ ck2 am2 c). 
  Proof. 
  destruct pl. destruct p. simpl. destruct f. intros am ck item1 item2 a1 a2 a3 an1 an2 items pairs.
  unfold syntaxSplitAssets. unfold conditionsSplitAssets. simpl. 
  intuition. specialize (H5 item1). rewrite H8 in H5.
  induction item1, item2.
  simpl in H1, H2, H0, H5, H3, H4, H6, H7, H8, H10, H11, H12. simpl. 
  intuition. rewrite H4, H2, H6, H3.
  rewrite H7, H8, H10. rewrite H7, H8 in H5.
  intuition. case_eq (an_dec an1 an2). 
  + intros.  rewrite same_add. destruct an1, a1, a2, an2, a3. reflexivity. 
  + intros. destruct n. destruct an1, an2. reflexivity.
Qed.

   (*When splitting assets, if item1 is evaluated as true, ck evaluation is equal to the asset mapped by this item union evaluation of other items*)

 Theorem splitEvalItemUnion 
  {Mp: Maps Asset AssetName AM}
   {Ft: FormulaTheory Formula Name FM}
    {FtM: FeatureModel FM Configuration} 
     {AssetM: AssetMapping Asset AssetName AM} 
      {ckTrans: CKTrans FM Asset AM CK Configuration} 
       {SPL: SPL Asset Configuration FM AM CK PL}:
    forall pl am2 ck2 item1 item2 a1 a2 a3 an1 an2 items pairs,
    (
      ( 
          wfCK (fst(fst pl)) (snd(fst pl)) (snd pl) /\
          syntaxSplitAssets (snd(fst pl)) am2 (snd pl) ck2 item1 item2 items an1 an2 a1 a2 a3 pairs /\
            conditionsSplitAssets a1 a2 a3 an1 an2 items
    )
    ->
        forall c, set_In c (semantics_func (fst(fst pl))) /\ (satisfies_func (item1.(exp)) c)
    -> semantics_func_ (snd pl) (snd (fst pl)) c = app (a1::nil) (semantics_func_ items (snd (fst pl)) c) /\
       semantics_func_ ck2 am2 c = app (app (a2:: nil) (a3::nil)) (semantics_func_ items am2 c)). 
    Proof.   
    destruct pl. destruct p. simpl. 
    intros am ck item1 item2 a1 a2 a3 an1 an2 items pairs.
    unfold syntaxSplitAssets. unfold conditionsSplitAssets. 
    simpl. intros. intuition.
  (*+   rewrite H6.  induction item1.


unfold semantics_func_. 

 rewrite H8. unfold wfCK_func in H1.
     destruct H1. destruct H9. specialize (H9 c0).
     intuition. specialize (H13 exp0). 
     rewrite H4 in H13. unfold wfFM_func in H1. 
     destruct H1.
     unfold wfFormulae_func in H9. specialize (H9 exp0).
     rewrite H2. simpl.   admit.
  + rewrite H6. rewrite H10. case_eq (an_dec an1 an2).
    - intros. admit.
    - intros. destruct an1, an2. intuition. *)
    Admitted.

 Theorem splitEvalRemainingItems 
  {Mp: Maps Asset AssetName AM}
   {Ft: FormulaTheory Formula Name FM}
    {FtM: FeatureModel FM Configuration} 
     {AssetM: AssetMapping Asset AssetName AM} 
      {ckTrans: CKTrans FM Asset AM CK Configuration} 
       {SPL: SPL Asset Configuration FM AM CK PL}:
  forall pl am2 ck2 (item1 item2: Item) (a1 a2 a3: Asset) (an1 an2: AssetName) (items: list Item) (pairs: AM),
    (
      ( 
        wfCK (fst(fst pl)) (snd(fst pl)) (snd pl)  /\
          syntaxSplitAssets (snd(fst pl)) am2 (snd pl) ck2 item1 item2 items an1 an2 a1 a2 a3 pairs /\
            conditionsSplitAssets a1 a2 a3 an1 an2 items
    )
    ->
      forall c, set_In c (semantics (fst(fst pl))) 
    ->
        (semantics_ items (snd(fst pl)) c) = (semantics_ items am2 c)).
  Proof.
 destruct pl. destruct p. simpl. destruct f. intros am ck item1 item2 a1 a2 a3 an1 an2 items pairs.
  unfold syntaxSplitAssets. unfold conditionsSplitAssets. simpl. 
  intuition. 
  specialize (H5 item1). rewrite H8 in H5.
  induction item1, item2.
  simpl in H1, H2, H0, H5, H3, H4, H6, H7, H8, H10. simpl. 
  intuition.
  rewrite H2, H3.
  rewrite same_add. destruct an1, a1, a2, an2, a3. reflexivity. 
  Qed.

  
 (* Split assets preserves CK well-formedness *)

  Theorem splitAssetWFCK 
    {Mp: Maps Asset AssetName AM}
      {Ft: FormulaTheory Formula Name FM}
        {FtM: FeatureModel FM Configuration} 
          {AssetM: AssetMapping Asset AssetName AM} 
            {ckTrans: CKTrans FM Asset AM CK Configuration} 
              {SPL: SPL Asset Configuration FM AM CK PL}:
    forall pl (am2:AM) (ck2: CK) (item1 item2: Item) (a1 a2 a3: Asset) (an1 an2: AssetName) items pairs,
    (
      ( 
       wfCK_func (fst(fst pl)) (snd(fst pl)) (snd pl)  /\
          syntaxSplitAssets (snd(fst pl)) am2 (snd pl) ck2 item1 item2 items an1 an2 a1 a2 a3 pairs /\
            conditionsSplitAssets a1 a2 a3 an1 an2 items
    )
    ->
      wfCK_func (fst(fst pl)) am2 ck2).
  Proof.
  destruct pl. destruct p. simpl. destruct f. intros am ck item1 item2 a1 a2 a3 an1 an2 items pairs.
  unfold syntaxSplitAssets. unfold conditionsSplitAssets. simpl. 
  intuition. 
  specialize (H5 item1). rewrite H8 in H5.
  induction item1, item2.
  simpl in H1, H2, H0, H5, H3, H4, H6, H7, H8, H10. simpl. 
  intuition.
  rewrite H6, H3. rewrite H2, H4 in H1.
  rewrite H10. rewrite H8 in H1. 
  intuition. case_eq (an_dec an1 an2). 
  + intros.  rewrite same_add in H1. destruct an1, a1, a2, an2, a3. rewrite H7 in H1. apply H1. 
  + intros. destruct n. destruct an1, an2. reflexivity.
  Qed.


 Theorem splitAsset
    {Mp: Maps Asset AssetName AM}
      {Ft: FormulaTheory Formula Name FM}
        {FtM: FeatureModel FM Configuration} 
          {AssetM: AssetMapping Asset AssetName AM} 
            {ckTrans: CKTrans FM Asset AM CK Configuration} 
              {SPL: SPL Asset Configuration FM AM CK PL}:
    forall (pl:PL) (am2:AM) (ck2: CK) (item1 item2: Item) (a1 a2 a3: Asset) (an1 an2: AssetName) items pairs,
    (
      ( 
       wfCK_func (getFM pl) (getAM pl) (getCK pl)  /\
          syntaxSplitAssets (getAM pl) am2 (getCK pl) 
          ck2 item1 item2 items an1 an2 a1 a2 a3 pairs /\
            conditionsSplitAssets a1 a2 a3 an1 an2 items
    )
    ->
      plRefinement_func pl (gerPL (getFM pl) am2 ck2) /\
      wfCK_func (getFM pl) am2 ck2) /\
      wfPL (gerPL (getFM pl) am2 ck2).
  Proof.
  intuition.
  + unfold plRefinement_func. intros. admit.
  + Search wfCK_func.  

  Admitted.

 (* ================= ADD OPTIONAL FEATURE ==================*)

 Definition syntaxAddOptionalFeature 
  {FormT: FormulaTheory Formula Name FM}
   {FMS: FeatureModelSemantics Formula FM Name }
    {FMR: FeatureModelRefinement Formula Name FM} 
    (fm1: FM) (am1: AM) (ck1: CK) (fm2: FM) (am2: AM) (ck2: CK) (F G: Name) items (pairs: AM) :Prop :=
    fst fm2 = app (G::nil)  (fst fm1) /\
    set_In F (fst fm1) /\
    (snd fm2) = set_add form_dec (IMPLIES_FORMULA (NAME_FORMULA(G)) (NAME_FORMULA(F))) (snd fm1) /\
    am2 = app am1 (pairs) /\
    ck2 = app ck1 items. 

 Definition conditionsAddOptionalFeature (fm1 fm2: FM) (am1 am2 pairs: AM) (ck2: CK) (G: Name) (items: set Item) 
    {Mp: Maps AssetName Asset AM}
     {Ft: FormulaTheory Formula Name FM}
      {FtM: FeatureModel FM Configuration} {AssetM: AssetMapping Asset AssetName AM} 
          {ckTrans: CKTrans FM Asset AM CK Configuration} 
            {SPL: SPL Asset Configuration FM AM CK PL} : Prop :=
    wfPL (gerPL fm2 am2 ck2) /\
    wfCK_func fm2 am2 ck2 /\ forall an: AssetName,  ~(set_In an (dom_func am1)) /\ (~ set_In G (fst fm1)) /\
    forall c: Configuration, forall expr, set_In expr (exps items) /\
    satisfies expr c -> satisfies (NAME_FORMULA(G)) c.

  Theorem addOptionalFeatureEqualProducts 
    {Mp: Maps AssetName Asset AM}
      {Ft: FormulaTheory Formula Name FM}
        {FtM: FeatureModel FM Configuration} 
          {AssetM: AssetMapping Asset AssetName AM} 
            {ckTrans: CKTrans FM Asset AM CK Configuration} 
              {SPL: SPL Asset Configuration FM AM CK PL} 
                {FormT: FormulaTheory Formula Name FM} 
                  {FMS: FeatureModelSemantics Formula FM Name }
                    {FMR: FeatureModelRefinement Formula Name FM}:
    forall pl (fm2: FM) (am2: AM) (ck2: CK) (F G: Name) (items:set Item) (pairs: AM),
      wfCK_func (fst (fst pl)) (snd (fst pl)) (snd pl) /\
        syntaxAddOptionalFeature (fst (fst pl)) (snd (fst pl)) (snd pl) fm2 am2 ck2 F G items pairs /\
          conditionsAddOptionalFeature (fst (fst pl)) fm2 (snd (fst pl)) am2 pairs ck2 G items
    ->
      forall c, set_In c (semantics_func (fst (fst pl))) -> 
        semantics_func_ (snd pl) (snd (fst pl)) c = semantics_func_ ck2 am2 c. 
  Proof.
  unfold syntaxAddOptionalFeature. unfold conditionsAddOptionalFeature.
  simpl.  intros pl fm am ck F G items pairs. destruct pl. destruct p.
  simpl. intuition.
  specialize (H7 an). rewrite H6, H9. destruct f. destruct fm. 
  simpl in H5, H2, H0, H6, H3, H1, H4, H8, H7. destruct H7. destruct H10. destruct G, F.
  intuition.
  Qed.


  Theorem addOptionalFeature 
    {Mp: Maps AssetName Asset AM}
      {Ft: FormulaTheory Formula Name FM}
        {FtM: FeatureModel FM Configuration} 
          {AssetM: AssetMapping Asset AssetName AM} 
            {ckTrans: CKTrans FM Asset AM CK Configuration} 
              {SPL: SPL Asset Configuration FM AM CK PL} 
                {FormT: FormulaTheory Formula Name FM} 
                  {FMS: FeatureModelSemantics Formula FM Name }
                    {FMR: FeatureModelRefinement Formula Name FM}:
    forall (pl: PL) (fm2: FM) (am2: AM) (ck2: CK) (F G: Name) (items:set Item) (pairs: AM),
      wfCK_func (getFM pl) (getAM pl) (getCK pl) /\
        syntaxAddOptionalFeature (getFM pl) (getAM pl) (getCK pl) fm2 am2 ck2 F G items pairs  /\
          conditionsAddOptionalFeature (getFM pl) fm2 (getAM pl) am2 pairs ck2 G items
            -> plRefinement_func pl (gerPL fm2 am2 ck2) 
              /\ wfCK_func fm2 am2 ck2 /\ wfPL (gerPL fm2 am2 ck2).
  Proof. 
  intros pl fm am ck F G items pairs. unfold syntaxAddOptionalFeature.
  unfold conditionsAddOptionalFeature. intros. 
  simpl. intuition. rewrite H6, H9. destruct gerPL. 
  unfold plRefinement_func.  intros. exists c3. split.
      +  destruct gerPL. unfold getFM_func. simpl.  unfold getFM_func in H8. destruct pl in H8. 
        simpl in H8. destruct pls1. simpl. destruct p.
        destruct pls2 in H8.  simpl in H8. destruct p.
        simpl in H8. destruct f, f0. simpl. apply H8. 
      +  specialize (H7 an). destruct H7. destruct H10. destruct G, F.
        intuition.
  Qed. 

(*=================== ADD UNUSED ASSETS ===================*)

Fixpoint assetsCK (items:set Item): set AssetName := 
  match items with
  | nil => nil
  | x :: xs => x.(assets) ++ assetsCK xs
  end.

Definition Is_truePB (b:Prop) : bool :=
    match b with
      | True => true
    end.


Fixpoint remov (ls: set AssetName) am1: AM :=
  match am1 with
  | nil => nil
  | x :: xs => if Is_truePB(set_In (fst x) (ls)) then remov ls xs else (x :: remov ls xs)
  end.

Definition syntaxAddUnusedAssets (am1 am2 pairs: AM) : Prop :=
  am2 = app pairs (remov (dom_func pairs) am1).

Definition conditionsAddUnusedAssets {Mp: Maps AssetName Asset AM} pairs ck: Prop :=
  forall an, set_In an (dom_ pairs) -> (~ set_In an (assetsCK ck)).

 Theorem addUnusedAssetsSameCK 
  {Mp: Maps AssetName Asset AM}
    {Ft: FormulaTheory Formula Name FM}
      {FtM: FeatureModel FM Configuration} 
        {AssetM: AssetMapping Asset AssetName AM} 
          {ckTrans: CKTrans FM Asset AM CK Configuration} 
            {SPL: SPL Asset Configuration FM AM CK PL}:
  forall pl am2 pairs,
    (
      syntaxAddUnusedAssets (snd( fst pl)) am2 pairs /\
        conditionsAddUnusedAssets pairs (snd pl)
          -> forall (c: Configuration), set_In c (semantics_func (fst(fst pl)))
            -> (semantics_func_ (snd pl) (snd( fst pl)) c) =
              semantics_func_ (snd pl) am2 c).
  Proof.
  simpl. intuition. simpl. simpl in H0.
  unfold syntaxAddUnusedAssets in H1.
  unfold conditionsAddUnusedAssets in H2.
  specialize (H2 an).  simpl in H1, H2, H0. rewrite H1.
  simpl. 

 (*
  
  destruct pl. destruct pls0. destruct p. destruct getFM.
  destruct c0.
  simpl. simpl in H1. unfold semantics_func in H1. simpl in H1. *)
  Admitted.


  Theorem addUnusedAssets
  {Mp: Maps AssetName Asset AM}
    {Ft: FormulaTheory Formula Name FM}
      {FtM: FeatureModel FM Configuration}
       {AssetM: AssetMapping Asset AssetName AM} 
          {ckTrans: CKTrans FM Asset AM CK Configuration} 
            {SPL: SPL Asset Configuration FM AM CK PL}:
    forall pl am2 pairs,
      (
        syntaxAddUnusedAssets (getAM pl) am2 pairs /\
        conditionsAddUnusedAssets pairs (getCK pl)
      ->
        strongerPLrefinement_func pl (gerPL (getFM pl) am2 (getCK pl)) 
          /\ wfPL (gerPL (getFM pl) am2 (getCK pl))). 
  Proof.
   intros. destruct H0. unfold syntaxAddUnusedAssets in H0. 
unfold conditionsAddUnusedAssets in H1.
  specialize (H1 an). intuition.
  - unfold strongerPLrefinement_func. intros. split.
    + unfold getFM_func. simpl.  unfold getFM_func in H2. destruct pl in H2.
        simpl in H2. destruct gerPL. destruct pls1. simpl. destruct p.
        simpl in H2.  destruct pls0 in H2. simpl in H2. destruct p.
        simpl in H2. destruct f, f0. simpl. apply H2.
    + destruct gerPL. unfold getCK_func. unfold getAM_func. simpl.
      induction pl, pls0. simpl. induction pls1. simpl. simpl in H0. admit.
  - intuition. destruct gerPL. Search dom_.
Admitted.

(*================== REMOVE UNUSED ASSETS =======================*)

  Theorem removeUnusedAssetsSameEvalCK  {Mp: Maps AssetName Asset AM}
     {Ft: FormulaTheory Formula Name FM}
      {FtM: FeatureModel FM Configuration} {AssetM: AssetMapping Asset AssetName AM} 
          {ckTrans: CKTrans FM Asset AM CK Configuration} 
            {SPL: SPL Asset Configuration FM AM CK PL}:
    forall (pl: PL) am2 pairs,
    (
      syntaxAddUnusedAssets am2 (getAM pl) pairs /\
      conditionsAddUnusedAssets pairs (getCK pl)
      -> forall c, set_In c (semantics (getFM pl)) ->
       (semantics_func_ (getCK pl) (getAM pl) c) =  semantics_func_ (getCK pl) am2 c). 
  Proof.
  unfold syntaxAddUnusedAssets. 
  unfold conditionsAddUnusedAssets.
  intuition.
  specialize (H2 an). 
  Admitted.


  Theorem removeUnusedAssets{Mp: Maps AssetName Asset AM}
    {Ft: FormulaTheory Formula Name FM}
      {FtM: FeatureModel FM Configuration} {AssetM: AssetMapping Asset AssetName AM} 
          {ckTrans: CKTrans FM Asset AM CK Configuration} 
            {SPL: SPL Asset Configuration FM AM CK PL}:
    forall pl am2 pairs,
      (
        syntaxAddUnusedAssets am2 (getAM pl) pairs /\
        conditionsAddUnusedAssets pairs (getCK pl)
      ->
        strongerPLrefinement_func pl (gerPL (getFM pl) am2 (getCK pl)) /\ wfPL (gerPL (getFM pl) am2 (getCK pl))). 
  Proof.
  intros. destruct H0. unfold syntaxAddUnusedAssets in H0. 
unfold conditionsAddUnusedAssets in H1.
  specialize (H1 an). intuition.
  - unfold strongerPLrefinement_func. intros. split.
    + unfold getFM_func. simpl.  unfold getFM_func in H2. destruct pl in H2.
        simpl in H2. destruct gerPL. destruct pls1. simpl. destruct p.
        simpl in H2.  destruct pls0 in H2. simpl in H2. destruct p.
        simpl in H2. destruct f, f0. simpl. apply H2.
    + destruct gerPL. unfold getCK_func. unfold getAM_func. simpl.
      induction pl, pls0. simpl. induction pls1. simpl. simpl in H0. intuition.

  Admitted.

End SpecificSPL.

