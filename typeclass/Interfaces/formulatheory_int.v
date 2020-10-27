Require Export Coq.Lists.ListSet.
Require Export Coq.Lists.List.
Require Export Coq.Bool.Bool.
Require Export Coq.Classes.RelationClasses.

Class FormulaTheory (FL N F: Type) : Type :=
{
  (*====================functions=======================*)

  names        : FL -> set N;
  wfTree       : F -> Prop;
  names_       : F -> set N;
  wt           : F -> FL -> Prop;
  wtFormulae   : F -> Prop;
  satisfies    : FL -> set N -> Prop;
  my_set_add   : N -> set N -> set N;
  my_set_remove: N -> set N -> set N;

  (*===========Axioms - Lemmas - Theorems====================*)  

  name_dec : 
    forall x y:N, {x = y} + {x <> y};
  formNames: 
    forall (fm : F) (f : FL),  
      (wt fm f) -> ( forall (n : N),
        set_In n (names f) -> set_In n (names_ fm));
  formNames2 : 
    forall (fm : F) (f : FL) (n: N),
      (wt fm f) /\ (~(set_In n (names_ fm))) 
        -> (~(set_In n (names f)));
  satisfies1 : 
    forall (f: FL) (c : set N) (n : N),
      ~(set_In n (names f)) -> satisfies f c =
        satisfies f (my_set_add n c);
  satisfies2 : 
    forall (f: FL) (c : set N) (n : N),
      ~(set_In n (names f)) -> satisfies f c = 
        satisfies f (my_set_remove n c);
  wtFormSameFeature :
    forall (abs : F) (con : F), (names_ abs = names_ con
      /\ (wfTree abs) /\ (wfTree con) -> forall (f : FL), (wt abs f)
        ->  (wt con f))
}.