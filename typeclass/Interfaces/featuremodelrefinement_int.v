Require Import Coq.Lists.ListSet.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Specif.
Require Export Coq.Lists.List.


Require Export formulatheory_int formulatheory_def formulatheory_inst
               featuremodelsemantics_def featuremodelsemantics_int featuremodelsemantics_inst.

Import  FormulaTheory FeatureModelSemantics.


Class FeatureModelRefinement (FML Nm F: Type) {FormT: FormulaTheory FML Nm F} 
                             {FMS: FeatureModelSemantics FML F Nm }: Type :=
 {
  (*====================functions=======================*)
  addMandatoryNode: F -> F -> Nm -> Nm -> Prop;
  addOptionalNode : F -> F -> Nm -> Nm -> Prop;
  

  (*===========Axioms - Lemmas - Theorems====================*)  
  name_dec : 
    forall x y: Nm, {x = y} + {x <> y};
  form_dec : 
    forall x y: FML, {x = y} + {x <> y};
  wtFormAddNode: forall (abs con: F) (n1 n2: Nm),
    wfTree(abs) /\ wfTree(con) /\
      names_(con) = set_add name_dec n2 (names_ (abs)) /\
        set_In n1 (names_ (abs)) /\
          (~set_In n2 (names_ (abs)))
            -> (forall (f: FML), wt abs f -> wt con f);
  addMandatoryWF: forall (abs: F) (n1 n2: Nm) (con:F),
    addMandatoryNode abs con n1 n2 -> wfFM (con);
  addMandatoryT: forall (abs: F) (n1 n2: Nm),
    exists (con: F), addMandatoryNode abs con n1 n2 ->
      (forall (c: set Nm),
        set_In c (semantics abs)
          -> if Is_truePB(set_In n1 c) then (set_In (set_add name_dec n2 c) (semantics con))
            else set_In c (semantics con)) /\
              (forall (c: set Nm),
                set_In c (semantics con)
                  -> if Is_truePB(set_In n2 c) then (set_In (set_remove name_dec n2 c) (semantics abs))
                    else set_In c (semantics abs)) /\
                      wfFM(con);
  addMandatoryTWF: forall (abs: F) (con: F) (n1 n2: Nm),
  addMandatoryNode abs con n1 n2 ->
    (forall (c: set Nm),
      set_In c (semantics abs)
        -> if Is_truePB(set_In n1 c) then (set_In (set_add name_dec n2 c) (semantics con))
         else set_In c (semantics con)) /\
           (forall (c: set Nm),
              set_In c (semantics con)
                -> if Is_truePB(set_In n2 c) then (set_In (set_remove name_dec n2 c) (semantics abs))
                  else set_In c (semantics abs)) /\
                    wfFM(con);
  wfPreservation: forall (abs: F) (con: F) (n1 n2: Nm),
    addOptionalNode abs con n1 n2 -> wfFM (con);
  addNode: forall (abs: F) (n1 n2: Nm),
    exists (con: F), addOptionalNode abs con n1 n2 ->
      refines abs con /\ wfFM con;
  addOptNode: forall (abs: F) (con: F) (n1 n2: Nm),
    addMandatoryNode abs con n1 n2 -> 
     refines abs con /\ wfFM con

}.