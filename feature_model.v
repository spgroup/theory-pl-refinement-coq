Module FeatureModel.

Require Export form name.

Import Name Form.
Require Export Coq.Lists.ListSet.

Definition features : Type := set Name.
Definition formulae : Type := set Formula.

Definition FM : Type := features * formulae.

Definition names_ (fm : FM) : features := fst fm.
Definition formulas (fm : FM) : formulae := snd fm.

Definition  wfTree (fm: FM): Prop := True.


End FeatureModel.