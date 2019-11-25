# Porting the Theory of Software Product Line Refinement to the Coq proof assistant

This repository contains an ongoing specification of the theory of Software Product Line Refinement using the Coq proof assistant, porting from the formalization already made in PVS.
The formalization was split into modules and these were included in different files. We give a brief description of these files below.
- **name.v**: Here, we define configuration in _Name Module_ as a set of feature names, specifically, a _Name set_, where _Name_ is an uninterpreted type.
- **form.v**: The _form.v_ file contains the _Form Module_ where a formula is declared as a new set of data values - in this case an enumerated type.
- **feature_model.v**: In this file, we represent an _FM_ as a pair of _features_ and _formulae_, where _features_ is a set of feature names and _formulae_ is a set of formulas.
- **decidability.v**: In Coq, dealing with lists requires that the types of elements used in these lists be decidable. In this file, we add axioms that all elements of type _Name_, _Formula_, and _Configuration_ are the same or different, making their type decidable.
- **formula_theory.v**: This file contains definitions of functions and lemmas that guarantee properties involving the _Formula_ type.
- **feature_model_semantics.v**: This file contains definitions of functions, lemmas and theorems that provide a guarantee of properties involving the _FM_ type.
- **assets.v**: In a product line, we specify and implement features with reusable assets. This file contains the theory of _Assets_.
- **asset_mapping.v**: This file contains the theory of _Asset Mapping_ - mappings from asset names to actual assets.
- **ck_trans.v**: We must relate features related to assets, whether code or other kinds of assets that specify or realize features. The _CK_ specifies this relation. We can express the _CK_ in different ways. _ck_trans.v_ contains a more advanced CK notion, that associates feature expressions with transformations over assets.
- **maps.v**: For _AM_ we need a _Map_ structure that allows the mapping of a feature name to a real artifact, so we chose to formalize a theory that deals with this structure that is contained in this file.
- **spl_refinement.v**: specify the general theory of LPS refinement.

