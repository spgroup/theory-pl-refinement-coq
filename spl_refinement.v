Module SPLrefinement. 
Require Export maps.


  Import Maps.
  Require Import Coq.Lists.ListSet.


(*================ FEATURE MODEL =======================*)


 Inductive Conf: Type.
 Inductive FM: Type.
 
Parameter inline FMRef : 
    FM -> set Conf.

  Variable fm fm1 fm2: FM.
  Variable c c1 c2 c3: Conf.

Axiom fm_dec : forall x y:FM, {x = y} + {x <> y}.
Axiom conf_dec : forall x y:Conf, {x = y} + {x <> y}.


(*Definition <Feature model refinement> -- definir com forall e exists?*)
  Definition FMRefinement (fm1 fm2: FM): Prop :=
  match (set_diff conf_dec (FMRef fm1) (FMRef fm2)) with
    | nil => True
    | _ => False
    end.

  (*   % Definition <Feature model equivalence> *)
  Definition equivalentFMs (fm1 fm2: FM): Prop :=
  (FMRefinement fm1 fm2) /\ (FMRefinement fm2 fm1).

   Axiom equalsSetDiff: 
    forall a b: set Conf, a = b -> set_diff conf_dec a b = nil.  

  Lemma equals:
  forall fm1 fm2, fm1 = fm2 -> equivalentFMs fm1 fm2.
    Proof.
    intros.
    unfold equivalentFMs.
    unfold FMRefinement. 
    rewrite H. split. 
    - rewrite equalsSetDiff.
      + trivial.
      + reflexivity.
    - rewrite equalsSetDiff.
      + trivial.
      + reflexivity.
    Qed.

(*   % Theorems <Feature model equivalence and refinement properties> *)
  Theorem eqFM:
    forall fm1, equivalentFMs fm1 fm1 /\
      (forall fm1 fm2,equivalentFMs fm1 fm2 -> equivalentFMs fm2 fm1) /\
         (forall fm1 fm2 fm3, equivalentFMs fm1 fm2 /\ equivalentFMs fm2 fm3 -> equivalentFMs fm1 fm3).
  Proof.
  intros.
  split.
  + rewrite fm3. apply equals. reflexivity.
  + split. 
    - intros. rewrite fm4, fm5. rewrite fm4, fm5 in H. apply H.
    - intros. destruct H. rewrite fm4, fm0. rewrite fm5, fm0 in H0. apply H0.
    Qed.

  
  Theorem refFM:
    forall fm1 fm2 fm3: FM, FMRefinement fm1 fm2 ->
      FMRefinement fm2 fm3 -> FMRefinement fm1 fm3.
    Proof.
    intros. rewrite fm3, fm0. rewrite fm3 in H. rewrite fm4 in H. apply H.
    Qed.

(* ===================== Asset MApping ==========================*)

  Definition Asset : Type := Maps.T.
  Definition AssetName : Type := Maps.S.

  Variable a1 a2: Asset.
  Variable an an1 an2: AssetName.
  Variable aSet S1 S2: set Asset.
  Variable anSet: set AssetName.
  Variable as1 as2 p p1 p2: set Asset.
  Variable prods ps ps1 ps2: set Asset.

(*Assumption <Assets refinement>*)
  Parameter assetRef : 
    set Asset -> set Asset -> Prop.

  Inductive wfProduct (aSet : set Asset) : Prop.
  Definition Product (aSet : set Asset) : Type := wfProduct aSet.


  Axiom assetRefinementReflexivity:
    forall x: set Asset, assetRef x x.

   Axiom assetRefinementTranstivity:
     forall x y z, assetRef x y -> assetRef y z ->  assetRef x z.

  Axiom as_dec : forall x y:Asset, {x = y} + {x <> y}.
  Axiom an_dec : forall x y:AssetName, {x = y} + {x <> y}.


  Axiom asRefCompositional :
    forall (S1 : set Asset) (S2 : set Asset) (aSet : set Asset),
      (assetRef S1 S2) /\ wfProduct (set_union as_dec S1 aSet) 
        -> (wfProduct (set_union as_dec S2 aSet)) 
          /\ assetRef (set_union as_dec S1 aSet) 
             (set_union as_dec S2 aSet).

  Definition AM := map_.

  Variable am am1 am2: AM.
 
 Definition aMR (am1 am2: AM) : Prop := (dom am1 = dom am2) /\
    forall (an : AssetName), set_In an (dom am1) -> 
      exists (a1 a2: Asset), (isMappable am1 an a1) 
        /\ (isMappable am2 an a2)
          /\ (assetRef (set_add as_dec a1 nil) (set_add as_dec a2 nil)).

  (*Axiom <Asset refinement is pre-order>*)
  Axiom assetMappingRefinement:
    forall x y z: AM, aMR x x /\ aMR x y -> aMR y z ->  aMR x z. 

  Lemma amRefCompositional:
  forall am1 am2, aMR am1 am2 ->
    (unique am1) /\ (unique am2) ->
      forall anSet,
        forall aSet defaultT,
              assetRef (set_union as_dec aSet (maps defaultT am1 anSet)) 
                (set_union as_dec aSet (maps defaultT am2 anSet)) /\  
                  wfProduct (set_union as_dec aSet (maps defaultT am1 anSet)) ->
                    wfProduct (set_union as_dec aSet (maps defaultT am2 anSet)).
  Proof.
  induction am2.
  - induction am1.
    + induction aSet.
      { intros am2 am4 HAM Hunq anSet0 aSet0 defaulT0.
        destruct Hunq. intuition. }
      { intros am2 am4 HAM Hunq anSet0 aSet0 defaulT0.
        destruct Hunq. intuition. }
    + induction aSet.
      { intros. destruct H0. intuition. }
      { intros am2 am4 HAM Hunq anSet0 aSet0 defaulT0.
         destruct Hunq. intuition. }
  - induction am1.
    + induction aSet.
      { intros am2 am4 HAM Hunq anSet0 aSet0 defaulT0.
         destruct Hunq. intuition. }
      { intuition. }
    + induction aSet.
      { intuition. }
      { intuition. }
  Qed.


(* ========================= CK ============================*)

 Inductive CK: Type.
 Parameter CKSem : 
  CK -> AM -> Conf -> set Asset.

  (* Axiom over ck evaluation *)
  Axiom amRef: forall (am1 am2: AM),
    (aMR am1 am2) -> forall (K: CK) (C: Conf),
      wfProduct (CKSem K am1 C) -> wfProduct (CKSem K am2 C)
      /\ assetRef (CKSem K am1 C) (CKSem K am2 C).
  
  Variable ck ck1 ck2 ck3: CK.

  Parameter CKConf :
  CK -> set Conf.

(*  % Definition <CK equivalence>   *)
  Definition equivalentCKsAux (ck1 ck2: CK): Prop :=
   match (set_diff conf_dec (CKConf ck1) (CKConf ck2)) with
    | nil => True
    | _ => False
    end.

 Definition equivalentCKs (ck1 ck2: CK): Prop :=
  (equivalentCKsAux ck1 ck2) /\ (equivalentCKsAux ck2 ck1).

 Lemma equalsCK:
  forall ck1 ck2, ck1 = ck2 -> equivalentCKs ck1 ck2.
    Proof.
    intros.
    rewrite H.
    unfold equivalentCKs. 
    unfold equivalentCKsAux. split.
    + rewrite equalsSetDiff.
      - trivial.
      - reflexivity.
    + rewrite equalsSetDiff.
      - trivial.
      - reflexivity.
     Qed. 

  Theorem eqCK:
    forall ck1, equivalentCKs ck1 ck1 /\
      (forall ck1 ck2, equivalentCKs ck1 ck2 -> equivalentCKs ck2 ck1) /\
         (forall ck1 ck2 ck3, equivalentCKs ck1 ck2 /\ equivalentCKs ck2 ck3 -> equivalentCKs ck1 ck3).
  Proof.
    intros.
    split.
    + rewrite ck4. apply equalsCK. reflexivity.
    + split. 
      - intros. rewrite ck5, ck6. rewrite ck5, ck6 in H. apply H.
      - intros. destruct H. rewrite ck5, ck7. rewrite ck5, ck6 in H. apply H.
    Qed.


  Definition weakerEqCK (fm: FM) (ck1 ck2: CK): Prop :=
    forall am,
      forall c, set_In c (FMRef fm) ->
        (CKSem ck1 am c = CKSem ck2 am c).

  
  (* Weak Equivalence properties - reflexive *)
  Theorem weakerEqReflexive:
    forall (fm: FM) (ck: CK),
      weakerEqCK fm ck ck.
  Proof.
  intros. unfold weakerEqCK. intros. reflexivity.
  Qed.

  (* Weak Equivalence properties - symmetric *)
    Theorem weakerEqSymmetric:
      forall (fm: FM) (ck1 ck2: CK),
        weakerEqCK fm ck1 ck2 -> weakerEqCK fm ck2 ck1.
    Proof.
    intros. rewrite ck5, ck4. rewrite ck4, ck5 in H.
    apply H.
    Qed.    

   (* Weak Equivalence properties - transitive *)
    Theorem weakerEqTransitive:
      forall (fm: FM) (ck1 ck2 ck3: CK),
        weakerEqCK fm ck1 ck2 -> weakerEqCK fm ck2 ck3 -> weakerEqCK fm ck1 ck3.
    Proof.
    intros.
    rewrite ck4, ck6. rewrite ck5, ck6 in H0.
    apply H0.
    Qed.

(* ============= SPL DEFINITION =================*)

  Definition ArbitrarySPL: Type := FM * AM * CK.

  (* Definition <Well-formed SPL> *)

  Definition getFM (PL: ArbitrarySPL) : FM := fst ( fst PL).
  Definition getAM (PL: ArbitrarySPL) : AM := snd ( fst PL).
  Definition getCK (PL: ArbitrarySPL) : CK := snd PL.


  Definition wfPL (pl:ArbitrarySPL): Prop :=
    (forall c, set_In c (FMRef (getFM pl)) ->
      wfProduct (CKSem (getCK pl) (getAM pl) c)).

  (* Definition <Product line> *) 
  Record PL: Type := {
        pls:> ArbitrarySPL;
        wfpl:> Prop }.

  Variable a : ArbitrarySPL.


  Definition ase (pl: PL): PL := {| pls:= a; wfpl:= wfPL a |}. 

  (*Definition PL : Type := ArbitrarySPL.*)

  Variable pl pl1 pl2: PL.

(* ============= PL REFINEMENT DEFINITION AND PROPERTIES =================*)
  Set Implicit Arguments.

  Inductive sig (A : Type) (P : A -> Prop) : Type :=
    exist : forall x : A, P x -> sig P.
    
  Notation "{ x | P }" := (sig (fun x => P)) : type_scope. 
  Notation "{ x : A | P }" :=
    (sig (fun x:A => P)) : type_scope.

  (* Definition <Product line refinement> *)
  (* checar se ainda ha simbolo para ser usado aqui *)
  Definition plRefinement (pl1 pl2: PL): Prop :=
      (forall c1, set_In c1 (FMRef (getFM pl1)) ->
        (exists c2, set_In c2 (FMRef (getFM pl2)) /\
          ( assetRef (CKSem (getCK pl1) (getAM pl1) (c1)) 
              (CKSem (getCK pl2) (getAM pl2) (c2))))). 

  Axiom confs_dec : forall x y:set Conf, {x = y} + {x <> y}.

  Fixpoint genConf (AS : set Asset) : set Asset := 
  match AS with
  | nil => nil
  | x :: xs => (set_add as_dec x (genConf xs)) ++ (genConf xs)
  end.

  Fixpoint filterAux (pl: PL) (AS: set Asset) (c: Conf) : set Asset :=
  match AS with
   | nil => nil
   | a1 :: x1 => 
        if is_true ((set_In c (FMRef (getFM pl))) /\
              AS = (CKSem (getCK pl) (getAM pl) c)) then a1 :: filterAux pl x1 c
         else filterAux pl x1 c
  end.

   Fixpoint filter (pl: PL) (AS: set Asset) (cs: set Conf) : set Asset :=
  match cs with
   | nil => nil
   | a1 :: x1 => filterAux pl AS a1 ++ filter pl AS x1
  end.
  

  Definition products (pl : PL): set Asset := 
                     filter pl (genConf (CKSem (getCK pl) (getAM pl) c)) (FMRef (getFM pl)). 
    (*{ p | exists (c: Conf), set_In c (FMRef (getFM pl)) /\ (p = (CKSem (getCK pl) (getAM pl) c))}.*)
   

  Definition  plRefinementAlt (pl1 pl2 : PL) : Prop :=  
    (forall p1: set Asset, set_diff as_dec p1 (products pl1) = nil -> 
      (exists p2: set Asset, set_diff as_dec p2 (products pl2) = nil /\
        (assetRef p1 p2))).

  Definition subsetProducts (pl :PL) (prods: set Asset): Prop :=
    set_diff as_dec prods (products pl1) = nil.

  Definition plWeakRefinement (pl1 pl2: PL) : Prop :=
    forall p1, set_In p1 (genConf (products pl1))->
      exists p2, set_In p2 (products pl2) /\
        (assetRef (set_add as_dec p1 nil) (set_add as_dec p2 nil)). 

  Definition strongerPLrefinement (pl1 pl2:PL) : Prop :=
    forall c1: Conf, set_In c1 (FMRef (getFM pl1)) ->
      (set_In c1 (FMRef (getFM pl2)) /\
          (assetRef (CKSem (getCK pl1) (getAM pl1) c1)
               (CKSem (getCK pl2) (getAM pl2) c1))).
  
  Theorem plStrongSubset:
    forall (pl1 pl2: PL),
      strongerPLrefinement pl1 pl2 
        -> (forall c:  Conf, set_In c (FMRef (getFM pl1)) -> set_In c (FMRef (getFM pl2))).
    Proof.
    intros.
    destruct pl3. destruct pl4. unfold strongerPLrefinement in H.
    specialize (H c1). destruct c1, c0. apply H in H0.
    destruct  H0. apply H0.
    Qed.

  (* PL Refinement compositionality *)

  Theorem weakFMcompositionality:
    forall (pl: PL) (fm: FM),      
        (FMRefinement (getFM pl) fm) /\ wfPL ((fm ,(getAM pl)), (getCK pl)) ->
          (plRefinement pl {|pls := ((fm ,(getAM pl)), (getCK pl)); wfpl := wfPL ((fm ,(getAM pl)), (getCK pl))|}).
    Proof.
    intros. 
    destruct H.   
    unfold plRefinement. 
    intros. exists c4.  split.
      +  unfold getFM. simpl.  unfold getFM in H1. destruct pl0 in H1.
        simpl in H1. destruct pls0 in H1. simpl in H1. destruct p0 in H1.
        simpl in H1. rewrite f in H1.
        rewrite fm0. apply H1. 
      + unfold getCK. unfold getAM. simpl.
        apply assetRefinementReflexivity.
    Qed.

  (* Theorem <Feature model equivalence compositionality>  *)

   Theorem fmEquivalenceCompositionality:
      forall (pl: PL) (fm: FM),
        equivalentFMs (getFM pl) fm ->
          (plRefinement pl {| pls := ((fm ,(getAM pl)), (getCK pl)); wfpl := wfPL ((fm ,(getAM pl)), (getCK pl))|})
            /\ wfPL ((fm ,(getAM pl)), (getCK pl)).
    Proof.
    intros.
    split.
    + unfold plRefinement. intros. exists c4. split.
      -  unfold getFM. simpl.  unfold getFM in H0. destruct pl0 in H0.
        simpl in H0. destruct pls0 in H0. simpl in H0. destruct p0. rewrite f in H0.
        rewrite fm0. apply H0.
      - unfold getCK. unfold getAM. simpl.
        apply assetRefinementReflexivity.
    + unfold wfPL. intros.
      unfold equivalentFMs in H.
      destruct H. intuition.
   Qed.

   (* Theorem <CK equivalence compositionality> *)
    
  Theorem ckEquivalenceCompositionality:
    forall (pl: PL) (ck: CK),
      equivalentCKs (getCK pl) ck ->
        (plRefinement pl {| pls:= ((fm ,(getAM pl)), (getCK pl)); wfpl := wfPL ((fm ,(getAM pl)), (getCK pl))|})
         /\ wfPL ((fm ,(getAM pl)), (getCK pl)).
    Proof.
    intros.
    split.
    + unfold plRefinement. intros. exists c4. split.
      -  unfold getFM. simpl.  unfold getFM in H0. destruct pl0 in H0.
        simpl in H0. destruct pls0 in H0. simpl in H0. destruct p0. simpl in H0. rewrite f in H0.
        rewrite fm. apply H0.
      - unfold getCK. unfold getAM. simpl.
        apply assetRefinementReflexivity.
    + unfold wfPL. intros.
      unfold equivalentFMs in H.
      destruct H. intuition.
   Qed.

  Theorem weakerCKcompositionality:
    forall (pl: PL) (ck: CK),
      weakerEqCK (getFM pl) (getCK pl) (ck) ->
        plRefinement pl {|pls := ((fm ,(getAM pl)), (getCK pl)); wfpl := wfPL ((fm ,(getAM pl)), (getCK pl))|}
         /\ wfPL ((fm ,(getAM pl)), (getCK pl)).
    Proof.
    intros.
    split.
    + unfold plRefinement. intros. exists c4. split.
      -  unfold getFM. simpl.  unfold getFM in H0. destruct pl0 in H0.
        simpl in H0. destruct pls0 in H0. simpl in H0. destruct p0. rewrite f in H0.
        rewrite fm. apply H0.
      - unfold getCK. unfold getAM. simpl.
        apply assetRefinementReflexivity.
    + unfold wfPL. intros.
      unfold equivalentFMs in H.
      intuition.
   Qed.

  (* Theorem <Asset mapping refinement compositionality> *)

  Theorem amRefinementCompositionality:
    forall (pl: PL) (am: AM),
      aMR (getAM pl) am ->
        plRefinement pl {| pls := ((fm ,(getAM pl)), (getCK pl)); wfpl:= wfPL ((fm ,(getAM pl)), (getCK pl))|}
         /\
           wfPL ((fm ,(getAM pl)), (getCK pl)).
    Proof.
    intros.
    split.
    + unfold plRefinement. intros. exists c4. split.
      -  unfold getFM. simpl.  unfold getFM in H0. destruct pl0 in H0.
        simpl in H0. destruct pls0 in H0. simpl in H0. destruct p0 in H0. simpl in H0.
        rewrite f in H0.
        rewrite fm. apply H0.
      - unfold getCK. unfold getAM. simpl.
        apply assetRefinementReflexivity.
    + unfold wfPL. intros.
      unfold equivalentFMs in H.
      destruct H. intuition.
   Qed.

   (* Theorem <Full compositionality>
   Este teorema exige a equivalencia forte do CK *)
  
  Theorem fullCompositionality:
    forall (pl: PL) (fm: FM) (am: AM) (ck:CK),
      equivalentFMs (getFM pl) fm /\
        equivalentCKs (getCK pl) ck /\
          aMR (getAM pl) am ->
            plRefinement pl {| pls := ((fm ,(getAM pl)), (getCK pl)); 
              wfpl:= wfPL ((fm ,(getAM pl)), (getCK pl))|}  /\
                wfPL ((fm ,(getAM pl)), (getCK pl)).
    Proof.
    intros.
    split.
    + unfold plRefinement. intros. exists c4. split.
      -  unfold getFM. simpl.  unfold getFM in H0. destruct pl0 in H0.
        simpl in H0. destruct pls0 in H0. simpl in H0. destruct p0. simpl in H0.
        rewrite f in H0.
        rewrite fm0. apply H0.
      - unfold getCK. unfold getAM. simpl.
        apply assetRefinementReflexivity.
    + unfold wfPL. intros.
      unfold equivalentFMs in H.
      destruct H. intuition.
   Qed.

  (* % Theorem <Full compositionality>
   Este teorema ainda usa a equivalencia forte de CK,
   em conjunto com refinamento de FMs, exige boa formacao da linha final*)
  
  Theorem weakFullCompositionality:
    forall (pl: PL) (fm: FM) (am: AM) (ck: CK),
      (FMRefinement (getFM pl) fm) /\
        equivalentCKs (getCK pl) ck /\
           wfPL ((fm ,(getAM pl)), (getCK pl)) ->
             plRefinement pl {| pls := ((fm ,(getAM pl)), (getCK pl));
               wfpl := wfPL ((fm ,(getAM pl)), (getCK pl)) |}.
    Proof.
    intros. 
    destruct H.   
    unfold plRefinement. 
    intros. exists c4.  split.
      +  unfold getFM. simpl.  unfold getFM in H1. destruct pl0 in H1.
        simpl in H1. destruct pls0 in H1. simpl in H1. destruct p0. simpl in H1.
        rewrite f in H1.
        rewrite fm0. apply H1. 
      + unfold getCK. unfold getAM. simpl.
        apply assetRefinementReflexivity.
    Qed.

  (*Theorem <Full compositionality>
  Este teorema exige a equivalencia mais fraca de CK e equivalencia de FMs *)

  Theorem fullCompositionality2:
    forall (pl: PL) (fm: FM) (am: AM) (ck: CK),
      equivalentFMs (getFM pl) fm /\
        weakerEqCK (getFM pl) (getCK pl) (ck) /\ 
          aMR (getAM pl) am ->
            plRefinement pl  {| pls := ((fm ,(getAM pl)), (getCK pl));
              wfpl:= wfPL ((fm ,(getAM pl)), (getCK pl))|} /\
              wfPL ((fm ,(getAM pl)), (getCK pl)).
    Proof.
    intros.
    split.
    + unfold plRefinement. intros. exists c4. split.
      -  unfold getFM. simpl.  unfold getFM in H0. destruct pl0 in H0.
        simpl in H0. destruct pls0 in H0. simpl in H0. destruct p0. 
        simpl in H0. rewrite f in H0.
        rewrite fm0. apply H0.
      - unfold getCK. unfold getAM. simpl.
        apply assetRefinementReflexivity.
    + unfold wfPL. intros.
      unfold equivalentFMs in H.
      destruct H. intuition.
   Qed.

  (* Este teorema exige a equivalencia mais fraca de CK,
   em conjunto com refinamento de FMs, exige boa formacao da linha final*)

     Theorem weakFullCompositionality2:
        forall (pl: PL) (fm: FM) (am: AM) (ck: CK),       
          (FMRefinement (getFM pl) fm) /\
            aMR (getAM pl) am /\ wfPL ((fm ,(getAM pl)), (getCK pl)) ->
              plRefinement pl {| pls := ((fm ,(getAM pl)), (getCK pl)); 
                wfpl := wfPL ((fm ,(getAM pl)), (getCK pl))|}.
    Proof.
    intros. 
    destruct H.   
    unfold plRefinement. 
    intros. exists c4.  split.
      +  unfold getFM. simpl.  unfold getFM in H1. destruct pl0 in H1.
        simpl in H1.  destruct pls0 in H1. simpl in H1. destruct p0. simpl in H1.
        rewrite f in H1.
        rewrite fm0. apply H1.  
      + unfold getCK. unfold getAM. simpl.
        apply assetRefinementReflexivity.
    Qed.

     Lemma equalsRefinementAlt:
      forall pl1 pl2, pl1 = pl2-> plRefinementAlt pl1 pl2.
      Proof.
      intros. rewrite H.
      unfold plRefinementAlt.
      intros.
      exists p3.
      split.
        + apply H0.
        + apply assetRefinementReflexivity.
      Qed.
      

    Theorem plRefAlt:
      (forall pl1: PL, plRefinementAlt pl1 pl1)/\
        (forall pl1 pl2 pl3: PL, plRefinementAlt pl1 pl2 /\
          plRefinementAlt pl2 pl3 -> plRefinementAlt pl1 pl3).
    Proof. 
      split.
        + intros.  apply equalsRefinementAlt. reflexivity.
        + intros. destruct H. unfold plRefinementAlt in H. unfold plRefinementAlt.
          intros p3 H1.
           specialize (H p3). apply H in H1. destruct H1. unfold plRefinementAlt in H0.
           specialize (H0 x). destruct H1. apply H0 in H1.
           destruct H1. destruct H1.  exists x0.  split.   
            - apply H1.
            - generalize H2, H3. apply assetRefinementTranstivity. 
    Qed.


    Lemma equalsStrongerPL:
    forall pl1 pl2, pl1 = pl2 -> strongerPLrefinement pl1 pl2.
    Proof.
    intros.
    unfold strongerPLrefinement.
    intros. split.
    - rewrite H in H0. apply H0.
    - rewrite H. apply assetRefinementReflexivity.
    Qed.

     Theorem strongerPLref:
    forall pl1: PL,strongerPLrefinement pl1 pl1 /\ ( forall pl1 pl2 pl3, strongerPLrefinement pl1 pl2 /\
      strongerPLrefinement pl2 pl3 -> strongerPLrefinement pl1 pl3).
    Proof.
    intros.
    split.
    + apply equalsStrongerPL. reflexivity. 
    + unfold strongerPLrefinement. intros. destruct H. specialize (H c1). specialize (H1 c1).
      destruct c1, c4. apply H in H0. destruct H0.
      split.
      - apply H1 in H0. destruct H0. apply H0.
      -  apply H1 in H0. destruct H0.  generalize H3. generalize H2. apply assetRefinementTranstivity.
    Qed.

 
   Lemma equalsPL:
    forall pl1 pl2, pl1 = pl2 -> plRefinement pl1 pl2.
    Proof.
    intros.
    unfold plRefinement.
    intros. exists c4. split.
    - rewrite H in H0. apply H0.
    - rewrite H. apply assetRefinementReflexivity.
    Qed.

   Theorem plRef:
      forall pl1, plRefinement pl1 pl1 /\
        (forall pl1 pl2 pl3: PL, plRefinement pl1 pl2 /\
          plRefinement pl2 pl3 -> plRefinement pl1 pl3).
      Proof.
      intros.
      split.
      + apply equalsPL. reflexivity.
      + unfold plRefinement. intros. destruct H. specialize (H c1).
        specialize (H1 c1). destruct c1, c4. apply H in H0. destruct H0.
        destruct H0. destruct x. apply H1 in H0. destruct H0. destruct H0.
        exists x. split.
        - apply H0.
        - generalize H3. generalize H2. apply assetRefinementTranstivity.
      Qed.

  Theorem plRefEq: 
      forall (pl1 pl2: PL), iff (plRefinement pl1 pl2) (plRefinementAlt pl1 pl2).
    Proof.
    intros.
    split.
    + intros.
      unfold plRefinement in H. specialize (H c1).
      unfold plRefinementAlt. intros. exists p3.
      split. 
        - admit.
        - apply assetRefinementReflexivity. 
    + intros. unfold plRefinementAlt in H. specialize (H p1).
      unfold plRefinement. intros.
      exists c4. split.
      - admit.
      - admit.
        
    Admitted.


   
  (* ============   %% SINGLE PRODUCT SPL FUNCTION =================*)

  Require Import Coq.Arith.Arith.

  Definition singletonPL (pl: PL) : Prop :=
    eq_nat (length (products pl)) 1.


End SPLrefinement.
