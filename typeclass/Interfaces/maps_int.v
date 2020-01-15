Require Import Coq.Lists.ListSet.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Specif.
Require Export Coq.Lists.List.

Class Maps (S T m: Type) : Type :=
{
  (*====================functions=======================*)
  unique_      : m -> Prop;
  dom_         : m -> set S;
  img          : m -> set T;
  getTs        : m -> S -> set T;
  isMappable_  : m -> S -> T -> Prop;  
  maps         : T -> m -> set S -> set T;
  union_s      : set S -> set S -> set S;
  union_t      : set T -> set T -> set T;
  set_add_S    : S -> set S -> set S;
  set_add_T    : T -> set T -> set T;

  (*===========Axioms - Lemmas - Theorems====================*)
  mappingUnique: forall m {l: S}, (unique_ m) \/ (getTs m l) = nil;
  inDom        : forall m {l: S} {r: T}, isMappable_ m l r -> set_In l (dom_ m);
  eqdecS       : forall x y : S, {x = y} + {x <> y};
  eqdecT       : forall x y : T, {x = y} + {x <> y};
  unionMap:
  forall m {ls1 ls2: set S} {defaulT: T},
    (maps defaulT m (union_s ls1 ls2)) =  
        union_t (maps defaulT m ls1) (maps defaulT m ls2);
  existsMap: 
  forall m {l: S} {r : T},
    isMappable_ m l r -> eq_nat (length (getTs m l)) 1;
  notExists:
    forall {ls: set S} m {defaulT: T}, (unique_ m) ->
      ~(exists l, set_In l ls /\ set_In l (dom_ m))
        -> maps defaulT m ls = nil;
  mapAM:
    forall m {ls: set S} {l: S} {defaulT: T}, (unique_ m) ->
      set_In l (dom_ m) ->
        exists {r : T}, (isMappable_ m l r) 
          /\ (maps defaulT m (set_add eqdecS l ls) 
            = set_add eqdecT r (maps defaulT m ls))
}.
