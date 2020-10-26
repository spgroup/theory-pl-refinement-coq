Module CKComp.

Require Export name form feature_model decidability feature_model_semantics formula_theory maps
               feature_model_refinement asset_mapping assets.
Import Name Decidability Form FeatureModel FeatureModelSemantics 
       FeatureModelRefinements AssetMapping Assets FormulaTheory Maps.


 Record Item : Type := {
  exp_: Formula;
  assets_: set AssetName;
}.

  Definition CK: Type := set Item.


  Variable am am1 am2: AM.
  Variable  an an1 an2: AssetName.
  Variable fm: WFM.
  Variable exp: Formula.
  Variable ck: CK. 
  Variable item it: Item.
  Variable items its1 its2: list Item.
  Variable c c1 c2: Configuration.
  Variable F G H opt: Name.

  (* get Formula*)
  Definition getExp it: Formula := it.(exp_).
  
  (* get set AssetName*)
  Definition getRS (it: Item) : set AssetName := it.(assets_).

   (* Get all Formulas*)
  Fixpoint exps ck : set Formula :=
    match ck with
    | nil => nil
    | x :: xs => set_union form_dec (set_add form_dec (x.(exp_)) nil) (exps xs)
    end.

  Axiom item_dec : forall x y:Item, {x = y} + {x <> y}.

  Fixpoint SetCompAux ck c: set Item :=
    match ck with
      | nil => nil
      | x :: xs => if Is_truePB (satisfies (getExp x) c) then
                   x :: (SetCompAux xs c) else (SetCompAux xs c)
    end.

  Lemma lemmaSetComp: forall ck c,
    SetCompAux ck c = set_inter item_dec ck (SetCompAux ck c).
  Proof.
  induction ck0.
  - intros.
    simpl. reflexivity.
  - specialize (IHck0 c).
    intro c. 
  Admitted.

   (*evaluates a CK against a product configuration and
     yields only CK items evaluated as true *)
  Definition evalCK ck c : set Item := SetCompAux ck c.

  (*yields all asset names referenced in a given set of CK items*)

  Fixpoint assetsCK items: set AssetName :=
    match items with
      | nil => nil
      | x :: xs =>  (x.(assets_)) ++ (assetsCK xs)
    end.

  (*  % yields all asset names of a given CK *)
  Definition imgCK ck: set AssetName:=
    assetsCK ck.

  (*yields only the asset names evaluated as true for a given product configuration*)
  Definition eval ck c: set AssetName :=
    assetsCK (evalCK ck c).

  (*yields only the asset names evaluated as true for a given product configuration*)
  Definition eval2 ck c: set AssetName :=
    assetsCK (evalCK ck c).

  Definition notshowupItem it an : Prop :=
    ~ set_In an (it.(assets_)).
  
  Definition showupItem it an: Prop :=
    set_In an (it.(assets_)).
  
  Variable a: T.

  (*yields the assets to build a product for a given product configuration 
   sCK : [ConfigKnowledge->[AM->[Configuration->finite_sets[Asset].finite_set]]] =*)
  Definition semantics_ (ck: CK) (am: AM) (c: Configuration) : set Asset := maps a am (eval ck c).

  Axiom as_dec : forall x y: Asset, {x = y} + {x <> y}.
  Axiom an_dec : forall x y: AssetName, {x = y} + {x <> y}.
  Axiom its_dec : forall x y: Item, {x = y} + {x <> y}.
  Axiom ns_dec : forall x y: Name, {x = y} + {x <> y}.
    
   (* Evaluate union*)
  Lemma evalUnion: forall items its1 its2 c am,
    items = set_union its_dec its1 its2
      -> semantics_ items am c = set_union as_dec (semantics_ its1 am c) (semantics_ its2 am c).
  Proof.
  intuition.
  rewrite H0. intuition.
  Admitted. 

  Definition wfCK (fm: WFM) am ck : Prop :=
    wfFM fm /\ (forall c, set_In c (semantics fm) -> (set_diff an_dec (eval ck c) (dom am) = nil)) /\
    (forall exp, set_In exp (exps ck) -> wt fm exp).

  Definition wfCK2 (fm: FM) (am: AM) (ck:CK) : Prop :=
    (forall item, set_In item ck -> (set_diff an_dec (item.(assets_)) (dom am) = nil)) /\
    (forall exp, set_In exp (exps ck) -> wt fm exp).


  (* esta vai ser nossa nocao de equivalencia*)
  Definition ckEq (fm: WFM) am (ck1 ck2: CK) : Prop :=
    forall c, set_In c (semantics fm) -> ((semantics_ ck1 am c) = (semantics_ ck2 am c)).

  (*Equivalence properties - reflexive *)
  Theorem eqReflexive:
    forall fm am ck, ckEq fm am ck ck.
  Proof.
  intros. unfold ckEq.
  intros. reflexivity.
  Qed.

  (*equivalence properties - symmetric*)
  Theorem eqSymmetric:
    forall fm am ck1 ck2, ckEq fm am ck1 ck2 -> ckEq fm am ck2 ck1.
  Proof.
  intros fm am ck1 ck2.
  unfold ckEq. intros.
  specialize (H0 c0). intuition.
  Qed.

  (* equivalence properties - transitive *)
  Theorem eqTransitive:
    forall fm am ck1 ck2 ck3,
      ckEq fm am ck1 ck2 /\ ckEq fm am ck2 ck3 -> ckEq fm am ck1 ck3.  
  Proof.
  intros fm0 am0 ck1 ck2 ck3.
  unfold ckEq. intros.
  destruct H0. specialize (H0 c0). specialize (H2 c0).
  intuition. rewrite H3, H0. reflexivity.
  Qed.

  (*esta vai ser nossa nocao de equivalencia *)
  Definition ckEq2 ck1 ck2 : Prop :=
    eval2 ck1 = eval2 ck2.

  (*Equivalence properties - reflexive*)
  Theorem eqReflexive2:
    forall ck, ckEq2 ck ck.
  Proof.
  intro ck0. intuition.
  Qed.

  (*equivalence properties - symmetric*)
  Theorem eqSymmetric2:
    forall ck1 ck2,
      ckEq2 ck1 ck2 -> ckEq2 ck2 ck1.
  Proof.
  intros. intuition.
  Qed.

  (*equivalence properties - transitive*)
  Theorem eqTransitive2:
    forall ck1 ck2 ck3,
      ckEq2 ck1 ck2 /\ ckEq2 ck2 ck3 -> ckEq2 ck1 ck3.
  Proof.
  intros ck1 ck2 ck3. unfold ckEq2. intros.
  destruct H0. rewrite H0, H1. reflexivity.
  Qed. 


End CKComp.
  










