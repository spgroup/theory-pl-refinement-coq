Require Export Coq.Lists.ListSet.
Require Export Coq.Lists.List.
Require Export Coq.Bool.Bool.
Require Export Coq.Classes.RelationClasses.
Require Export formulatheory_int.


Class FeatureModelSemantics (FL F N: Type) {FormT: FormulaTheory FL N F} : Type :=
{
  (*====================functions=======================*)

  wfFM        : F -> Prop;
  satImpConsts: F -> set N -> Prop;
  satExpConsts: F -> set N -> Prop;
  semantics   : F -> set (set N);
  refines     : F -> F -> Prop;
  refines2    : F -> F -> Prop;
  ns          : F -> set N;

  (*===========Axioms - Lemmas - Theorems====================*)  

  wtFormRefinement :
    forall (abs : F) (con : F), forall (name : N),
      set_In name (ns abs) -> set_In name (ns con) /\ (wfTree abs) /\
        (wfTree con) -> (forall (f : FL), (wt abs f) -> (wt con f));
  notMember : 
    forall (fm : F) (opt : N), 
      ~(set_In opt ( ns fm)) -> (forall (conf : set N), 
        set_In conf (semantics fm) -> ~ (set_In opt (conf)))
}.  
