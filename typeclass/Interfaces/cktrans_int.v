Require Export Coq.Lists.ListSet.
Require Export Coq.Lists.List.
Require Export Coq.Bool.Bool.
Require Export Coq.Classes.RelationClasses.
Require Export maps_int.
Require Export assettheory_int.
Require Export assetmapping_int.
Require Export formulatheory_int.



Class CKTrans (Ck FML IT T m Nm A N F:Type) {Mp: Maps A N m} {As: AssetTheory A N m} 
              {Am: AssetMapping A N m}   {Ft: FormulaTheory FML Nm F} : Type :=
{
  (*====================functions=======================*)

  exps       : Ck -> set FML;
  getExp     : IT -> FML;
  getRS      : IT -> T;
  transform  : T -> m -> m -> m;
  semanticsCK: Ck -> m -> m -> set Nm -> set N;
  semanticCK : Ck -> m -> m -> set Nm-> m;
  semantics_ : Ck ->  m -> set Nm -> set N;
  getNames   : F -> set FML;
  unionCK    : Ck -> Ck -> Ck;

  (*===========Axioms - Lemmas - Theorems====================*)  
  similarFunctions: 
    forall (ck: Ck) (am amt: m) (c: set Nm), (unique_ am) -> semanticsCK ck am amt c 
      = img (semanticCK ck am amt c);
  compAmRefEmptyset:
    forall (am1 am2: m),
      (unique_ am1) /\ (unique_ am2) ->
        aMR am1 am2 ->
          forall (ck: Ck) (c: set Nm),
            assetRef (semantics_ ck am1 c) (semantics_ ck am2 c) /\
            wfProduct (semantics_ ck am1 c) ->
               wfProduct (semantics_ ck am2 c); 
  compAmRef:
    forall (am1 am2: m),
      (unique_ am1) /\ (unique_ am2) ->
        aMR am1 am2 ->
          (forall (ck: Ck) (c: set Nm) (amt1 amt2: m),
            assetRef (semanticsCK ck am1 amt1 c) (semanticsCK ck am2 amt2 c) /\
            aMR amt1 amt2 /\ wfProduct (semanticsCK ck am1 amt1 c) ->
              wfProduct (semanticsCK ck am2 amt2 c));
  addItemsBefore:
    forall (am amt: m) (ck: Ck) (its: Ck) (s: set (set Nm)),
      (unique_ am) /\ (unique_ amt) ->
        forall (c: set Nm),
          set_In c s -> (
            (forall (exp:FML), set_In exp (exps its) -> ~(satisfies exp c) ->
              (semanticsCK ck am amt c = semanticsCK (unionCK its ck) am amt c)));
  addItemsAfter:
    forall (am amt: m) (ck: Ck) (its: Ck) (s: set (set Nm)),
      (unique_ am) /\ (unique_ amt) ->
        forall (c: set Nm),
          set_In c s-> (
            (forall (exp:FML), set_In exp (exps its) -> ~(satisfies exp c) ->
              (semanticsCK ck am amt c = semanticsCK (unionCK its ck) am amt c)))
  
}.
