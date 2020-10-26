Module Form.
 
Require Export name.
Import Name.

Inductive Formula : Type :=
  | TRUE_FORMULA  : Formula
  | FALSE_FORMULA : Formula
  | NAME_FORMULA  : Name -> Formula
  | NOT_FORMULA   : Formula -> Formula
  | AND_FORMULA   : Formula -> Formula -> Formula
  | IMPLIES_FORMULA : Formula -> Formula -> Formula.

End Form.