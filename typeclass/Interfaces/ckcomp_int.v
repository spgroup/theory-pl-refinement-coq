Require Export Coq.Lists.ListSet.
Require Export Coq.Lists.List.
Require Export Coq.Bool.Bool.
Require Export Coq.Classes.RelationClasses.
Require Export assettheory_int.
Require Export formulatheory_int.
Require Export maps_int.


Class CKComp (Ck Conf FML IT m Nm A N F:Type) {Ft: FormulaTheory FML Nm F} : Type :=
{
  (*====================functions=======================*)
    getExp       : IT -> FML;
    getRS        : IT -> set A;
    exps         : list IT -> set FML;
    SetCompAux   : list IT -> Conf -> set IT;
    evalCK       : list IT -> Conf -> set IT;
    assetsCK     : list IT -> set A;
    imgCK        : list IT -> set A;
    eval         : list IT -> Conf -> set A;
    eval2        : list IT -> Conf -> set A;
    notshowupItem: IT -> A -> Prop;
    showupItem   : IT -> A -> Prop;
    semantics_   : list IT -> m -> Conf -> set N;
    wfCK         : F -> m -> list IT -> Prop;
    wfCK2        : F -> m -> list IT -> Prop;
    ckEq         : F -> m -> list IT -> list IT -> Prop;
    ckEq2        : list IT -> list IT -> Prop;
    renameCKitem : IT -> A -> A -> IT;
    renameCKitem_: IT -> Nm -> Nm -> IT;
    renamecK     : list IT -> Nm -> Nm -> list IT;

  (*===========Axioms - Lemmas - Theorems====================*)
  as_dec : 
    forall x y: N, {x = y} + {x <> y};
  item_dec: 
    forall x y: IT, {x = y} + {x <> y};
  ck_dec: 
    forall x y: IT, {x = y} + {x <> y};
  lemmaSetComp: forall (ck: list IT) (c: Conf),
    SetCompAux ck c = set_inter ck_dec ck (SetCompAux ck c);
  evalUnion: forall (items its1 its2: list IT) (c: Conf) (am: m),
    items = set_union item_dec its1 its2
      -> semantics_ items am c = set_union as_dec (semantics_ its1 am c) (semantics_ its2 am c);
  eqReflexive:
    forall (fm: F) (am: m) (ck: list IT), ckEq fm am ck ck;
  eqSymmetric:
    forall (fm: F) (am: m) (ck1 ck2: list IT), ckEq fm am ck1 ck2 -> ckEq fm am ck2 ck1;
  eqTransitive:
    forall (fm: F) (am: m) (ck1 ck2 ck3: list IT),
      ckEq fm am ck1 ck2 /\ ckEq fm am ck2 ck3 -> ckEq fm am ck1 ck3;
  eqReflexive2:
    forall (ck: list IT), ckEq2 ck ck;
  eqSymmetric2:
    forall (ck1 ck2: list IT),
      ckEq2 ck1 ck2 -> ckEq2 ck2 ck1;
  eqTransitive2:
    forall (ck1 ck2 ck3: list IT),
      ckEq2 ck1 ck2 /\ ckEq2 ck2 ck3 -> ckEq2 ck1 ck3;
  ckNames: forall (fm: F) (am: m) (ck: list IT) (opt: Nm),
    (
      (~set_In opt (names_ fm)) /\
        wfCK fm am ck
    )
    ->
    (forall exp, set_In exp (exps ck) -> (~set_In opt (names exp)))

}.
























