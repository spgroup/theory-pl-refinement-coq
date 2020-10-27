Module CKTrans.
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
Require Export assetmapping_def.
Require Export assetmapping_int.
Import AssetMapping.
Import FormulaTheory.
Import Maps.
Import AssetTheory.
Import FeatureModelSemantics.


  Inductive Transformation : Type.

  Record Item : Type := {
  exp: Formula;
  tasks: Transformation;
}.

  Definition CK : Type := list Item.


  Axiom form_dec : forall x y:Formula, {x = y} + {x <> y}.


  (* Get all Formulas*)
  Fixpoint exps_func (ck: CK) : set Formula :=
    match ck with
    | nil => nil
    | x :: xs => set_union form_dec (set_add form_dec (x.(exp)) nil) (exps_func xs)
    end. 

  (* get Formula*)
  Definition getExp_func (it : Item) : Formula := it.(exp).

 Definition wfCK_func (fm: FM) (am :AM) (ck: CK) : Prop :=
      forall (exp : Formula), set_In exp (exps_func ck) -> wt_func fm exp.

  
  (* get Transformation*)
  Definition getRS_func (it: Item) : Transformation := it.(tasks).

  Parameter Inline(40) transform_func : Transformation -> AM-> AM -> AM.
  
  Axiom preserv_axiom :
   forall am1 am2 amt1 amt2 t, 
      (unique_ am1) /\ (unique_ am2) /\ (unique_ amt1) /\ (unique_ amt2) ->
      aMR_func am1 am2 /\ aMR_func amt1 amt2 ->
        aMR_func (transform_func t am1 am2) (transform_func t am2 amt2).

  (* get each asset if it satisfies a configuration*)
  Fixpoint semanticsCK_func (ck : CK) (am amt: AM) (c: Configuration) : set Asset :=
    match ck with
     | nil => img_func amt
     | x :: xs => if is_true (satisfies_func (getExp_func x) c) then 
                    semanticsCK_func xs am (transform_func (getRS_func x) am amt) c  
                  else semanticsCK_func xs am amt c 
    end.
  
  (* get AM if it satisfies a configuration*)
  Fixpoint semanticCK_func (ck : CK) (am amt: AM) (c: Configuration) : AM :=
    match ck with
    |nil => amt
    | x :: xs => if is_true (satisfies_func (getExp_func x) c) 
                    then semanticCK_func xs am (transform_func (getRS_func x) am amt) c 
                 else semanticCK_func xs am amt c
    end. 
  
  Definition semantics_func_ (ck: CK) (am: AM) (c: Configuration): set Asset :=
    semanticsCK_func ck am (nil) c.

  Definition getNames_func (fm : FM) : set Formula := snd fm.
  Definition unionCK_func (ck1 ck2: CK): CK := ck1 ++ ck2.

End CKTrans.
