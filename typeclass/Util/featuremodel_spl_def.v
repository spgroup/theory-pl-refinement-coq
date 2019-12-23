Module FeatureModelSPL.
Require Export featuremodel_spl_int.
Require Import Coq.Lists.ListSet.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Specif.
Require Export Coq.Lists.List.

  Inductive Conf: Type.
  Inductive FM: Type.
 
  Parameter inline FMRef_Func : 
    FM -> set Conf.

  Variable fm fm1 fm2: FM.
  Variable c c1 c2 c3: Conf.

  Axiom fm_dec : forall x y:FM, {x = y} + {x <> y}.
  Axiom conf_dec : forall x y:Conf, {x = y} + {x <> y}.


  (*Definition <Feature model refinement> -- definir com forall e exists?*)
  Definition FMRefinement_func (fm1 fm2: FM): Prop :=
    match (set_diff conf_dec (FMRef_Func fm1) (FMRef_Func fm2)) with
      | nil => True
      | _ => False
      end.

  (*   % Definition <Feature model equivalence> *)
  Definition equivalentFMs_func (fm1 fm2: FM): Prop :=
    (FMRefinement_func fm1 fm2) /\ (FMRefinement_func fm2 fm1).

  Axiom equalsSetDiff: 
    forall a b: set Conf, a = b -> set_diff conf_dec a b = nil.  

End FeatureModelSPL.