Module FeatureModelRefinimentTheory.
Require Import Coq.Lists.ListSet.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Specif.
Require Export Coq.Lists.List.


Require Export formulatheory_int formulatheory_def formulatheory_inst
               featuremodelsemantics_def featuremodelsemantics_int featuremodelsemantics_inst.

Import  FormulaTheory FeatureModelSemantics.

Axiom  name_dec_axiom : 
    forall x y: Name, {x = y} + {x <> y}.
Axiom form_dec_axiom : 
    forall x y: Formula, {x = y} + {x <> y}.

Definition addMandatoryNode_func (abs: FM) (con: FM) (n1 n2: Name): Prop :=
  fst con = set_add name_dec_axiom n2 (ns_func (abs)) /\
      snd con = set_union form_dec_axiom (app ((IMPLIES_FORMULA (NAME_FORMULA(n2)) (NAME_FORMULA(n1)))::nil) 
      ((IMPLIES_FORMULA (NAME_FORMULA(n1)) (NAME_FORMULA(n2)))::nil))
          (snd abs) /\ set_In n1 (fst abs) /\ (~set_In n2 (fst abs)). 

Definition addOptionalNode_func (abs: FM) (con: FM) (n1 n2: Name): Prop :=
  fst con = set_add name_dec_axiom n2 (ns_func (abs)) /\ set_In n1 (names_ abs) /\
     snd con = set_add form_dec_axiom (IMPLIES_FORMULA (NAME_FORMULA(n2)) (NAME_FORMULA(n1)))
          (snd abs) /\ (~set_In n2 (names_ (abs))).

End FeatureModelRefinimentTheory.

 