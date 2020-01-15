Module FeatureModelSemantics.
Require Export Coq.Lists.ListSet.
Require Export Coq.Lists.List.
Require Export Coq.Bool.Bool.
Require Export Coq.Classes.RelationClasses.
Require Export formulatheory_int.
Require Export formulatheory_def.
Import FormulaTheory.

  Definition wfFM_func (fm : FM) : Prop := (wfTree_func fm) /\ 
    (wtFormulae_func fm).

  Definition satImpConsts_func (fm : FM) (c : Configuration) : Prop := 
    forall n: Name, set_In n (c) -> set_In n (fst fm).

  Definition satExpConsts_func (fm : FM) (c : Configuration) : Prop := 
    forall f: Formula, set_In f (snd fm) -> (satisfies_func f c = True).

  Definition Is_truePB (b:Prop) : bool :=
    match b with
      | True => true
    end.

  Fixpoint filter (fm:FM) (s: set Configuration) : set Configuration :=
    match s with
    | nil => nil
    | a1 :: x1 => 
          if Is_truePB ((satImpConsts_func fm a1) /\
              (satExpConsts_func fm a1)) then a1 :: filter fm x1 
           else filter fm x1
    end.

  Fixpoint genConf (fm : features) : set Configuration := 
    match fm with
    | nil => nil
    | x :: xs => (set_add conf_dec_axiom (set_add name_dec_axiom x (nil)) (genConf xs)) ++ (genConf xs)
  end.
 
  Definition semantics_func (fm : FM) : set Configuration := 
    filter fm (genConf (fst fm)).

  Definition refines_func (abs : FM) (con : FM) : Prop := 
    if andb (Is_truePB (wfFM_func abs)) (Is_truePB(wfFM_func con)) then
      forall (conf : Configuration), set_In conf (semantics_func abs) 
        -> set_In conf (semantics_func con)
          else False. 


  Definition refines2_func (abs : FM) (con : FM) : Prop :=
    forall (conf1 : Configuration), set_In conf1 (semantics_func abs) ->
      exists (conf2 : Configuration),  set_In conf2 (semantics_func con).
  
  Definition nsf_func (fm : FM) : set Name := fst fm.

End FeatureModelSemantics.