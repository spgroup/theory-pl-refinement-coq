Module FormulaTheory.
Require Export Coq.Lists.ListSet.
Require Export Coq.Lists.List.
Require Export Coq.Bool.Bool.
Require Export Coq.Classes.RelationClasses.
  
  Inductive Name : Type.
  Definition Configuration : Type := set Name.

  Inductive Formula : Type :=
  | TRUE_FORMULA : Formula
  | FALSE_FORMULA : Formula
  | NAME_FORMULA : Name -> Formula
  | NOT_FORMULA : Formula -> Formula
  | AND_FORMULA : Formula -> Formula -> Formula
  | IMPLIES_FORMULA : Formula -> Formula -> Formula.

  Axiom name_dec_axiom : forall x y:Name, {x = y} + {x <> y}.
  Axiom form_dec_axiom : forall x y:Formula, {x = y} + {x <> y}.
  Axiom conf_dec_axiom : forall x y:Configuration, {x = y} + {x <> y}.

  (*yields names for a formula*) 
Fixpoint names_func (f : Formula) : set Name :=
  match f with
    | TRUE_FORMULA => empty_set Name
    | FALSE_FORMULA => empty_set Name
    | NAME_FORMULA n1 => set_add name_dec_axiom n1 nil
    | NOT_FORMULA f1 => names_func f1
    | AND_FORMULA f1 f2 => set_union name_dec_axiom  (names_func f1) (set_diff name_dec_axiom  (names_func f2) (names_func f1))  
    | IMPLIES_FORMULA f1 f2 => set_union name_dec_axiom  (names_func f1) (set_diff name_dec_axiom  (names_func f2) (names_func f1)) 
  end.

(* indicates whether a formula is well-typed*)
Fixpoint wt_func (fs : set Name) (f : Formula) : Prop :=
  match f with
    | TRUE_FORMULA => True
    | FALSE_FORMULA => True
    | NAME_FORMULA n1 =>  In n1 fs
    | NOT_FORMULA f1 => wt_func fs f1
    | AND_FORMULA f1 f2 => (wt_func fs f1) /\ (wt_func fs f2)  
    | IMPLIES_FORMULA f1 f2 => (wt_func fs f1) /\ (wt_func fs f2)
   end.

  Definition features : Type := set Name.
  Definition formulae : Type := set Formula.

  Definition FM : Type := features * formulae.
  Definition  wfTree_func (fm: FM): Prop := True.
  Definition ns_func (fm : FM) : set Name := fst fm.


Fixpoint wtFormulaeAux(fm : FM) (fs : formulae): Prop :=
   match fs with 
     | nil => True
     | a1 :: x1 => (wt_func (fst fm) a1) /\ (wtFormulaeAux fm x1)
   end.

  Definition my_set_add_func (n: Name) (c: Configuration): Configuration :=
    set_add name_dec_axiom n c.

   Definition my_set_remove_func (n: Name) (c: Configuration): Configuration :=
    set_remove name_dec_axiom n c.

(*indicates whether a feature model has all of its formulae well-typed*)
Fixpoint wtFormulae_func (fm : FM) : Prop := 
  wtFormulaeAux fm (snd fm).

(*indicates when a configuration satisfies a formula*)
Fixpoint satisfies_func (f: Formula) ( c : Configuration) : Prop :=
  match f with
    | TRUE_FORMULA => True
    | FALSE_FORMULA => False
    | NAME_FORMULA n => set_In n c
    | NOT_FORMULA f1 => ~(satisfies_func f1 c)
    | AND_FORMULA f1 f2 => (satisfies_func f1 c) /\ (satisfies_func f2 c)  
    | IMPLIES_FORMULA f1 f2 => (satisfies_func f1 c) -> (satisfies_func f2 c)
   end.

End FormulaTheory.
