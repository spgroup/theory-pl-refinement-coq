Require Export Coq.Lists.ListSet.
Require Export Coq.Lists.List.
Require Export Coq.Bool.Bool.
Require Export Coq.Classes.RelationClasses.

Class FormulaTheory (FL N F: Type) : Type :=
{
  names: FL -> set N;
  wfTree: F -> Prop;
  names_: F -> set N;
  wt: set N -> FL -> Prop;
  wtFormulae: F -> Prop;
  satisfies: FL -> set N -> Prop;
  name_dec : forall x y:N, {x = y} + {x <> y};
  formNames: forall (fm : F) (f : FL),  
    (wt (names_ fm) f) -> ( forall (n : N),
      set_In n (names f) -> set_In n (names_ fm));
  formNames2 : forall (fm : F) (f : FL) (n: N),
    (wt (names_ fm) f) /\ (~(set_In n (names_ fm))) 
      -> (~(set_In n (names f)));
  satisfies1 : forall (f: FL) (c : set N) (n : N),
    ~(set_In n (names f)) -> satisfies f c =
      satisfies f (set_add name_dec n c);
  satisfies2 : forall (f: FL) (c : set N) (n : N),
    ~(set_In n (names f)) -> satisfies f c = 
      satisfies f (set_remove name_dec n c);
  wtFormSameFeature : forall (abs : F) (con : F), (names_ abs = names_ con
  /\ (wfTree abs) /\ (wfTree con) -> forall (f : FL), (wt (names_ abs) f)
  ->  (wt (names_ con) f))
}.