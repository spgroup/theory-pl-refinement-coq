Module SPL.
Require Export assetmapping_spl_def.
Require Export featuremodel_spl_def.
Require Export cktrans_spl_def. 
Require Export spl_int.
Require Export assetmapping_spl_int.
Require Export assetmapping_spl_inst.

Require Export featuremodel_spl_int.
Require Export featuremodel_spl_inst.
Require Export featuremodel_spl_proofs.

Require Export cktrans_spl_int.
Require Export cktrans_spl_proofs.
Require Export cktrans_spl_inst.

Require Export maps_proofs.
Require Export maps_int.
Require Export maps_def.
Require Export maps_inst.

Require Import Coq.Lists.ListSet.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Specif.
Require Export Coq.Lists.List.
Import Maps.
Import CKTransSPL.
Import FeatureModelSPL.
Import AssetMappingSPL.  

  Variable c : Conf.
  Axiom confs_dec : forall x y:set Conf, {x = y} + {x <> y}.
  Axiom as_dec : forall x y: Asset, {x = y} + {x <> y}.


  Definition ArbitrarySPL: Type := FM * AM * CK.

  (* Definition <Well-formed SPL> *)

  Definition getFM_func (PL: ArbitrarySPL) : FM := fst ( fst PL).
  Definition getAM_func (PL: ArbitrarySPL) : AM := snd ( fst PL).
  Definition getCK_func (PL: ArbitrarySPL) : CK := snd PL.
  Definition getCk_func ck : CK := ck.

  Definition wfPL_func (pl:ArbitrarySPL): Prop :=
    (forall c, set_In c (FMRef_Func (getFM_func pl)) ->
      wfProduct_ind (CKSem_func (getCK_func pl) (getAM_func pl) c)).


  (* Definition <Product line> *) 
  Record PL: Type := {
        pls:> ArbitrarySPL;
        wfpl:> Prop }.

  Variable pl pl1 pl2: PL.

  Definition plRefinement_func (pl1 pl2: PL): Prop :=
      (forall c1, set_In c1 (FMRef_Func (getFM_func pl1)) ->
        (exists c2, set_In c2 (FMRef_Func (getFM_func pl2)) /\
          ( assetRef_func (CKSem_func (getCK_func pl1) (getAM_func pl1) (c1)) 
              (CKSem_func (getCK_func pl2) (getAM_func pl2) (c2))))). 


  Fixpoint genConf (AS : set Asset) : set Asset := 
  match AS with
  | nil => nil
  | x :: xs => (set_add as_dec x (genConf xs)) ++ (genConf xs)
  end.

  Fixpoint filterAux (pl: PL) (AS: set Asset) (c: Conf) : set Asset :=
  match AS with
   | nil => nil
   | a1 :: x1 => 
        if is_true ((set_In c (FMRef_Func (getFM_func pl))) /\
              AS = (CKSem_func (getCK_func pl) (getAM_func pl) c)) then a1 :: filterAux pl x1 c
         else filterAux pl x1 c
  end. 

   Fixpoint filter (pl: PL) (AS: set Asset) (cs: set Conf) : set Asset :=
  match cs with
   | nil => nil
   | a1 :: x1 => filterAux pl AS a1 ++ filter pl AS x1
  end.

  

  Definition products_func (pl : PL): set Asset := 
                filter pl (genConf (CKSem_func (getCK_func pl) (getAM_func pl) c)) (FMRef_Func (getFM_func pl)).

   Definition  plRefinementAlt_func (pl1 pl2 : PL) : Prop :=  
    (forall p1: set Asset, set_diff as_dec p1 (products_func pl1) = nil -> 
      (exists p2: set Asset, set_diff as_dec p2 (products_func pl2) = nil /\
        (assetRef_func p1 p2))).

  Definition subsetProducts_func (pl :PL) (prods: set Asset): Prop :=
    set_diff as_dec prods (products_func pl1) = nil.  

  Definition plWeakRefinement_func (pl1 pl2: PL) : Prop :=
    forall p1, set_In p1 (genConf (products_func pl1))->
      exists p2, set_In p2 (products_func pl2) /\
        (assetRef_func (set_add as_dec p1 nil) (set_add as_dec p2 nil)).   

  Definition strongerPLrefinement_func (pl1 pl2:PL) : Prop :=
    forall c, set_In c (FMRef (getFM_func pl1)) ->
      set_In c (FMRef (getFM_func pl2)) /\
          (assetRef_func (CKSem (getCK_func pl1) (getAM_func pl1) c)
               (CKSem (getCK_func pl2) (getAM_func pl2) c)).

  Definition genPL_func  (fm: FM) (pl: PL) : PL :=
     {|pls := (fm ,(getAM_func pl), (getCK_func pl)); 
      wfpl := wfPL_func (fm ,(getAM_func pl), (getCK_func pl)) |}.

  Definition genPLCK_func  (ck: CK) (pl: PL) : PL :=
     {|pls := ((getFM_func pl) ,(getAM_func pl), ck); 
      wfpl := wfPL_func ((getFM_func pl) ,(getAM_func pl), ck) |}.


  Definition genPLAM_func  (am: AM) (pl: PL) : PL :=
     {|pls := ((getFM_func pl) ,am, (getCK_func pl)); 
      wfpl := wfPL_func ((getFM_func pl) ,am, (getCK_func pl)) |}.

  Definition gerPL_func 
         (fm: FM) (am: AM) (ck: CK): PL :=
     {|pls := (fm ,am , ck); 
      wfpl := wfPL_func (fm ,am , ck) |}.

End SPL.
