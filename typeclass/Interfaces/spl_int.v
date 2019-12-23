Require Export cktrans_spl_int.
Require Export cktrans_spl_def.
Require Export cktrans_spl_proofs.
Require Export featuremodel_spl_int.
Require Export featuremodel_spl_def.
Require Export featuremodel_spl_proofs.
Require Export assetmapping_spl_int.
Require Export assetmapping_spl_def.

Require Import Coq.Lists.ListSet.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Specif.
Require Export Coq.Lists.List.
Import CKTransSPL.
Import FeatureModelSPL.
Import AssetMappingSPL.  


Class SPL (A N M Conf F AM CK PL: Type) {FM: FeatureModel F Conf}
         {AssetM : AssetMapping Asset AssetName AM}
         {ckTrans: CKTrans F A AM CK Conf}: Type :=
{ 
  getFM               : PL -> F; 
  getAM               : PL -> AM;
  getCK               : PL -> CK;
  genPL               : F -> PL -> PL; 
  wfPL                : PL -> Prop;
  plRefinement        : PL -> PL -> Prop;
  products            : PL -> set A;
  plRefinementAlt     : PL -> PL -> Prop;
  subsetProducts      : PL -> set A -> Prop;
  plWeakRefinement    : PL -> PL -> Prop;
  strongerPLRefinement: PL -> PL -> Prop;
  plStrongSubset:
   forall pl1 pl2: PL,
      strongerPLRefinement pl1 pl2 
        -> (forall c: Conf, set_In c (FMRef (getFM pl1)) -> set_In c (FMRef (getFM pl2)));
  fmEquivalenceCompositionality:
     forall (pl: PL) (fm: F),
       equivalentFMs (getFM pl) fm ->
         (plRefinement pl (genPL fm pl)) /\
           wfPL (genPL fm pl);
   weakFMcompositionality:
    forall (pl: PL) (fm: F),      
        (FMRefinement (getFM pl) fm) /\ wfPL (genPL fm pl) ->
          (plRefinement pl (genPL fm pl));
  ckEquivalenceCompositionality:
    forall (pl: PL) (fm: F) (ck: CK),
      equivalentCKs (getCK pl) ck ->
        (plRefinement pl (genPL fm pl)) /\
           wfPL (genPL fm pl);
  weakerCKcompositionality:
    forall (pl: PL) (fm: F) (ck: CK),
      weakerEqCK (getFM pl) (getCK pl) (ck) ->
        plRefinement pl (genPL fm pl) /\
           wfPL (genPL fm pl);
  amRefinementCompositionality:
    forall (pl: PL) (fm: F) (ck: CK) (am: AM),
      aMR (getAM pl) am ->
        plRefinement pl (genPL fm pl) /\
           wfPL (genPL fm pl);
  fullCompositionality:
    forall (pl: PL) (fm: F) (ck: CK) (am: AM),
      equivalentFMs (getFM pl) fm /\
        equivalentCKs (getCK pl) ck /\
          aMR (getAM pl) am ->
            plRefinement pl (genPL fm pl) /\
              wfPL (genPL fm pl);
  weakFullCompositionality:
    forall  (pl: PL) (fm: F) (ck: CK),
      (FMRefinement (getFM pl) fm) /\
        equivalentCKs (getCK pl) ck /\
           wfPL (genPL fm pl) ->
             plRefinement pl (genPL fm pl);
  fullCompositionality2:
    forall  (pl: PL) (fm: F) (ck: CK) (am: AM),
      equivalentFMs (getFM pl) fm /\
        weakerEqCK (getFM pl) (getCK pl) (ck) /\ 
          aMR (getAM pl) am ->
            plRefinement pl (genPL fm pl) /\
              wfPL (genPL fm pl);
  weakFullCompositionality2:
        forall  (pl: PL) (fm: F) (am: AM),       
          (FMRefinement (getFM pl) fm) /\
            aMR (getAM pl) am /\ wfPL (genPL fm pl) ->
              plRefinement pl (genPL fm pl);
  plRefAlt:
       (forall (pl1: PL), plRefinementAlt pl1 pl1)/\
        (forall (pl1 pl2 pl3: PL), plRefinementAlt pl1 pl2 /\
          plRefinementAlt pl2 pl3 -> plRefinementAlt pl1 pl3);
  strongerPLref:
      forall (pl1: PL),strongerPLRefinement pl1 pl1 
        /\ ( forall (pl1 pl2 pl3: PL), strongerPLRefinement pl1 pl2 /\
          strongerPLRefinement pl2 pl3 -> strongerPLRefinement pl1 pl3);
  plRef:
      forall (pl1: PL), plRefinement pl1 pl1 /\
        (forall (pl1 pl2 pl3: PL), plRefinement pl1 pl2 /\
          plRefinement pl2 pl3 -> plRefinement pl1 pl3)
}.