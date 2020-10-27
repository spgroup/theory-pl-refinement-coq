Module CKComp.

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
Require Export assetmapping_spl_int.
Require Export assetmapping_spl_def.
Import AssetMappingSPL.
Import FormulaTheory.
Import Maps.
Import AssetTheory.
Import FeatureModelSemantics.

  Record Item : Type := {
  exp: Formula;
  assets: set AssetName;
}.
  Definition CK : Type := list Item.
  Axiom form_dec_axiom : forall x y:Formula, {x = y} + {x <> y}.

  Variable am am1 am2: AM.
  Variable  an an1 an2: AssetName.
  Variable fm: FM.
  Variable expr: Formula.
  Variable ck: CK. 
  Variable item it: Item.
  Variable items its1 its2: list Item.
  Variable c c1 c2: Configuration.
  Variable F G H opt: Name.

  (* get Formula*)
  Definition getExp_func (it : Item) : Formula := it.(exp).
  
  (* get set AssetName*)
  Definition getRS_func (it: Item) : set AssetName := it.(assets).

   (* Get all Formulas*)
  Fixpoint exps_func (ck: CK) : set Formula :=
    match ck with
    | nil => nil
    | x :: xs => set_union form_dec_axiom (set_add form_dec_axiom (x.(exp)) nil) (exps_func xs)
    end.

  Fixpoint SetCompAux_func ck c: set Item :=
    match ck with
      | nil => nil
      | x :: xs => if Is_truePB (satisfies (getExp_func x) c) then
                   x :: (SetCompAux_func xs c) else (SetCompAux_func xs c)
    end.

  (*evaluates a CK against a product configuration and
     yields only CK items evaluated as true *)
  Definition evalCK_func ck c : set Item := SetCompAux_func ck c.

  (*yields all asset names referenced in a given set of CK items*)

  Fixpoint assetsCK_func (items: list Item): set AssetName :=
    match items with
      | nil => nil
      | x :: xs =>  (x.(assets)) ++ (assetsCK_func xs)
    end.

  (*  % yields all asset names of a given CK *)
  Definition imgCK_func ck: set AssetName:=
    assetsCK_func ck.

  (*yields only the asset names evaluated as true for a given product configuration*)
  Definition eval_func ck c: set AssetName :=
    assetsCK_func (evalCK_func ck c).

  (*yields only the asset names evaluated as true for a given product configuration*)
  Definition eval2_func ck c: set AssetName :=
    assetsCK_func (evalCK_func ck c).

   Definition notshowupItem_func (it: Item) (an:AssetName) : Prop :=
    ~ set_In an (it.(assets)).
  
  Definition showupItem_func (it: Item) (an:AssetName) : Prop :=
    set_In an (it.(assets)).
  
  Variable a: T.

  (*yields the assets to build a product for a given product configuration 
   sCK : [ConfigKnowledge->[AM->[Configuration->finite_sets[Asset].finite_set]]] =*)
  Definition semantics_func_ (ck: CK) (am: AM) (c: Configuration) : set Asset := maps a am (eval_func ck c).

  Axiom as_dec_axiom : forall x y: Asset, {x = y} + {x <> y}.
  Axiom an_dec_axiom : forall x y: AssetName, {x = y} + {x <> y}.
  Axiom its_dec_axiom : forall x y: Item, {x = y} + {x <> y}.
  Axiom ns_dec_axiom : forall x y: Name, {x = y} + {x <> y}.

  Definition wfCK_func fm am ck : Prop :=
    wfFM_func fm /\ (forall c, set_In c (semantics_func fm) -> (set_diff an_dec_axiom (eval_func ck c) (dom_ am) = nil)) /\
    (forall exp, set_In exp (exps_func ck) -> wt fm exp).

  Definition wfCK2_func (fm: FM) (am: AM) (ck:CK) : Prop :=
    (forall item, set_In item ck -> (set_diff an_dec_axiom (item.(assets)) (dom_ am) = nil)) /\
    (forall exp, set_In exp (exps_func ck) -> wt fm exp).


  (* esta vai ser nossa nocao de equivalencia*)
  Definition ckEq_func (fm: FM) am (ck1 ck2: CK) : Prop :=
        forall (c: Configuration), set_In c (semantics_func fm) -> ((semantics_func_ ck1 am c) = (semantics_func_ ck2 am c)).

   (*esta vai ser nossa nocao de equivalencia *)
  Definition ckEq2_func ck1 ck2 : Prop :=
    eval2_func ck1 = eval2_func ck2.

  Definition renameCKitem_func item (an1 an2: AssetName): Item :=
    if Is_truePB(set_In an1 (item.(assets))) then item else item.

  Definition renameCKitem_func_ item (F G: Name): Item :=
    item.

  (*operacao de renaming --> ren: CK x F x F -> CK
%  renameCK(ck: CK, F,G:Name): set[CKitem] =*)

    Fixpoint renamecK_func (ck: CK) (F G: Name): CK :=
    nil.
  
End CKComp.
