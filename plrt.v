Module Name.

Require Import Coq.Lists.ListSet. 

Inductive Name : Type.

Definition Configuration : Type := set Name.

End Name.

Module Form.

Import Name.

Inductive Formula : Type :=
  | TRUE_FORMULA : Formula
  | FALSE_FORMULA : Formula
  | NAME_FORMULA : Name -> Formula
  | NOT_FORMULA : Formula -> Formula
  | AND_FORMULA : Formula -> Formula -> Formula
  | IMPLIES_FORMULA : Formula -> Formula -> Formula.

End Form.

Module Decidability.
Import Name Form.

Axiom name_dec : forall x y:Name, {x = y} + {x <> y}.
Axiom form_dec : forall x y:Formula, {x = y} + {x <> y}.
Axiom conf_dec : forall x y:Configuration, {x = y} + {x <> y}.

End Decidability.

Module FeatureModel.

Import Name Form.
Require Export Coq.Lists.ListSet.

Definition features : Type := set Name.
Definition formulae : Type := set Formula.

Definition FM : Type := features * formulae.

Definition names_ (fm : FM) : features := fst fm.
Definition formulas (fm : FM) : formulae := snd fm.

Definition  wfTree (fm: FM): Prop := True.


End FeatureModel.

Module FormulaTheory.

Import Name Form Decidability FeatureModel.
Require Export Coq.Lists.ListSet.
Require Export Coq.Lists.List.
Require Export Coq.Bool.Bool.
Require Export Coq.Classes.RelationClasses.

(*yields names for a formula*)
Fixpoint names (f : Formula) : set Name :=
  match f with
    | TRUE_FORMULA => empty_set Name
    | FALSE_FORMULA => empty_set Name
    | NAME_FORMULA n1 => set_add name_dec n1 nil
    | NOT_FORMULA f1 => names f1
    | AND_FORMULA f1 f2 => set_union name_dec  (names f1) (set_diff name_dec  (names f2) (names f1))  
    | IMPLIES_FORMULA f1 f2 => set_union name_dec  (names f1) (set_diff name_dec  (names f2) (names f1)) 
  end.

(* indicates whether a formula is well-typed*)
Fixpoint wt (fs : features) (f : Formula) : Prop :=
  match f with
    | TRUE_FORMULA => True
    | FALSE_FORMULA => True
    | NAME_FORMULA n1 => In n1 fs
    | NOT_FORMULA f1 => wt fs f1
    | AND_FORMULA f1 f2 => (wt fs f1) /\ (wt fs f2)  
    | IMPLIES_FORMULA f1 f2 => (wt fs f1) /\ (wt fs f2)
   end.

Fixpoint wtFormulaeAux(fm : FM) (fs : formulae): Prop :=
   match fs with 
     | nil => True
     | a1 :: x1 => (wt (names_ fm) a1) /\ (wtFormulaeAux fm x1)
   end.
 
(*indicates whether a feature model has all of its formulae well-typed*)
Fixpoint wtFormulae (fm : FM) : Prop := 
  wtFormulaeAux fm (formulas fm).

(*indicates when a configuration satisfies a formula*)
Fixpoint satisfies (f: Formula) ( c : Configuration) : Prop :=
  match f with
    | TRUE_FORMULA => True
    | FALSE_FORMULA => False
    | NAME_FORMULA n => set_In n c
    | NOT_FORMULA f1 => ~(satisfies f1 c)
    | AND_FORMULA f1 f2 => (satisfies f1 c) /\ (satisfies f2 c)  
    | IMPLIES_FORMULA f1 f2 => (satisfies f1 c) -> (satisfies f2 c)
   end.


(*a well-typed formula only contains names from the feature model*)
Lemma formNames : forall (fm : FM) (f : Formula),  
 (wt (names_ fm) f) -> ( forall (n : Name),
 set_In n (names f) -> set_In n (names_ fm)).
Proof.
  induction f.
    + simpl. tauto.
    + simpl. tauto. 
    + simpl. intros. intuition. rewrite H1 in H. apply H.
    + simpl. tauto.
    + simpl. intros H. destruct H. intros. apply set_union_elim in H1. inversion H1.
      - apply IHf1. apply H. apply H2.
      - apply set_diff_elim1 in H2. apply IHf2. apply H0. apply H2.
    + simpl. intros H. destruct H. intros. apply set_union_elim in H1. inversion H1.
      - apply IHf1. apply H. apply H2. 
      - apply set_diff_elim1 in H2. apply IHf2. apply H0. apply H2.
Qed.

Lemma formNames2 : forall (fm : FM) (f : Formula) (n: Name) ,(wt (names_ fm) f) /\ 
  (~(set_In n (names_ fm))) -> (~(set_In n (names f))).
Proof. 
  unfold not.
  induction f.
    + simpl. tauto.
    + simpl. tauto.
    + simpl. intros. intuition. rewrite H in H1. apply H2. apply H1.
    + simpl. tauto.
    + simpl. intros. destruct H. destruct H. apply set_union_elim in H0. inversion H0.
      - apply (IHf1 n). intuition. apply H3.
      - apply set_diff_elim1 in H3. apply (IHf2 n). intuition. apply H3. 
    + simpl. intros. destruct H. destruct H. apply set_union_elim in H0. inversion H0.
      - apply (IHf1 n). intuition. apply H3.
      - apply set_diff_elim1 in H3. apply (IHf2 n). intuition. apply H3. 
Qed.

Theorem not_compat : forall A B : Prop,
  (A = B) -> ((~ A) = (~B)).
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.


Lemma set_union_elim_not :
   forall (a:Name) (x y:set Name),
     ~(set_In a (set_union name_dec x y)) -> 
        ~(set_In a x) /\ ~(set_In a y).
Proof.
  intros. split.
    + intuition. apply H. apply set_union_intro1. apply H0.
    + intuition. apply H. apply set_union_intro2. apply H0.
Qed.

Lemma set_union_elim_not2 :
   forall (a:Name) (x y:set Name),
     ~(set_In a x) /\ ~(set_In a y) ->
      ~(set_In a (set_union name_dec x y)).
Proof.  
  intros. destruct H.
  intuition. apply H. 
  apply set_union_elim in H1.
  generalize H1. tauto.
Qed.

Theorem or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros P Q H.
  tauto. Qed.

Lemma set_diff_elim_not:
    forall (n : Name) (f1 f2 : Formula),
    ~ set_In n (set_diff name_dec (names f1) (names f2)) ->
    ~ set_In n (names f1) \/ set_In n (names f2).
Proof.
  intros.
  left.
  intuition.
  apply H.
  apply set_diff_intro.
  apply H0.
  unfold not. 
  intro.
  apply H.
  apply set_diff_intro.
  apply H0.
Admitted.

Lemma satisfies1 : forall (f: Formula) (c : Configuration) (n : Name),
  ~(set_In n (names f)) -> satisfies f c = satisfies f (set_add name_dec n c).
Proof.
induction f. 
  + simpl. intros. reflexivity.
  + simpl. intros. reflexivity.
  + simpl. intros. intuition. apply H1 in H0. 
    - contradiction. 
    - rewrite n. rewrite n0. reflexivity.
  + simpl. intros. apply not_compat. apply (IHf c). apply H.
  + simpl. intros. apply set_union_elim_not in H. destruct H as [H1 H2]. 
    specialize (IHf1 c n). specialize (IHf2 c n).
    apply set_diff_elim_not in H2. inversion H2.
    -  apply IHf1 in H1. apply IHf2 in H. rewrite H1.
      rewrite H. reflexivity.
    - contradiction.
 + simpl. intros. apply set_union_elim_not in H. destruct H as [H1 H2]. 
    specialize (IHf1 c n). specialize (IHf2 c n).
    apply set_diff_elim_not in H2. inversion H2.
    -  apply IHf1 in H1. apply IHf2 in H. rewrite H1.
      rewrite H. reflexivity.
    - contradiction.
Qed.
    
Lemma satisfies2 : forall (f: Formula) (c : Configuration) (n : Name),
  ~(set_In n (names f)) -> satisfies f c = satisfies f (set_remove name_dec n c).
induction f.
  + simpl. intros. reflexivity.
  + simpl. intros. reflexivity.
  + simpl. intros. intuition. apply H1 in H0. 
    - contradiction. 
    - rewrite n. rewrite n0. reflexivity.
  + simpl. intros. apply not_compat. apply (IHf c). apply H. 
  + simpl. intros. apply set_union_elim_not in H. destruct H as [H1 H2]. 
    specialize (IHf1 c n). specialize (IHf2 c n).
    apply set_diff_elim_not in H2. inversion H2.
    -  apply IHf1 in H1. apply IHf2 in H. rewrite H1.
      rewrite H. reflexivity.
    - contradiction.
 + simpl. intros. apply set_union_elim_not in H. destruct H as [H1 H2]. 
    specialize (IHf1 c n). specialize (IHf2 c n).
    apply set_diff_elim_not in H2. inversion H2.
    -  apply IHf1 in H1. apply IHf2 in H. rewrite H1.
      rewrite H. reflexivity.
    - contradiction.
Qed.

Lemma wtFormSameFeature : forall (abs : FM) (con : FM), (names_ abs = names_ con
  /\ (wfTree abs) /\ (wfTree con) -> forall (f : Formula), (wt (names_ abs) f)
  ->  (wt (names_ con) f)).
Proof.
  intros.
  destruct H as [equals_abs_con wf_abs_con].
  destruct wf_abs_con as [wf_abs wf_con].
  induction f.
    + rewrite equals_abs_con in H0. apply H0. 
    + rewrite equals_abs_con in H0. apply H0. 
    + simpl. simpl in H0. rewrite equals_abs_con in H0. apply H0. 
    + apply IHf. apply H0. 
    + rewrite equals_abs_con in H0. apply H0. 
    + rewrite equals_abs_con in H0. apply H0. 
Qed.

End FormulaTheory.

Module FeatureModelSemantics.

Import Name FormulaTheory Form Decidability FeatureModel.

Require Export Coq.Lists.List.
Require Export Coq.Sets.Powerset.
Require Export Coq.Bool.Bool.

Definition wfFM (fm : FM) : Prop := (wfTree fm) /\ 
(wtFormulae fm).

Definition satImpConsts (fm : FM) (c : Configuration) : Prop := 
 forall n: Name, set_In n (c) -> set_In n (names_ fm).

Definition satExpConsts (fm : FM) (c : Configuration) : Prop := 
  forall f: Formula, set_In f (snd fm) -> (satisfies f c = True).

Definition Is_truePB (b:Prop) : bool :=
  match b with
    | True => true
  end.

Fixpoint filter (fm:FM) (s: set Configuration) : set Configuration :=
  match s with
   | nil => nil
   | a1 :: x1 => 
        if Is_truePB ((satImpConsts fm a1) /\
              (satExpConsts fm a1)) then a1 :: filter fm x1 
         else filter fm x1
  end.

Fixpoint genConf (fm : features) : set Configuration := 
  match fm with
  | nil => nil
  | x :: xs => (set_add conf_dec (set_add name_dec x (nil)) (genConf xs)) ++ (genConf xs)
  end.
 
Definition semantics (fm : FM) : set Configuration := 
  filter fm (genConf (names_ fm)).


Definition refines (abs : FM) (con : FM) : Prop :=
  if andb (Is_truePB (wfFM abs)) (Is_truePB(wfFM con)) then
  forall (conf : Configuration), set_In conf (semantics abs) -> set_In conf (semantics con)
  else False.


Definition refines2 (abs : FM) (con : FM) : Prop :=
  forall (conf1 : Configuration), set_In conf1 (semantics abs) ->
  exists (conf2 : Configuration),  set_In conf2 (semantics con).

Lemma wtFormRefinement : forall (abs : FM) (con : FM), forall (name : Name),
 set_In name (fst abs) -> set_In name (fst con) /\ (wfTree abs) /\
 (wfTree con) -> (forall (f : Formula), (wt (fst abs) f) -> (wt (fst con) f)).
Proof.
induction f.
  + simpl. tauto.
  + simpl. tauto.
  + destruct H0. intros. simpl. rewrite name in H0.
    rewrite n. apply H0. 
  + simpl. tauto.
  + simpl. intros. destruct H1. split.
    - apply IHf1. apply H1.
    - apply IHf2. apply H2.
  + simpl. intros. split. 
    - apply IHf1. destruct H1. apply H1.
    - apply IHf2. destruct H1. apply H2.
Qed.  

Theorem notMember : forall (fm : FM), wfFM fm = True -> ( forall (opt : Name), 
   ~(set_In opt ( fst fm)) -> (forall (conf : Configuration), 
    set_In conf (semantics fm) -> ~ (set_In opt (conf)))).
    Proof.
    intros.
    unfold not in H.
    unfold not. 
    destruct opt.
    intro H2.
    destruct conf in H1.
    + destruct fm. destruct f. 
      - simpl in H1. apply H1.
      - destruct n. destruct f; 
        simpl in H; apply H0; left; reflexivity.

    + destruct fm. destruct f.
      - simpl in H1. apply H1.
      - simpl in H. apply H0. left. rewrite n0. reflexivity.
Qed.
End FeatureModelSemantics.

Module Maps.

  (** Esse módulo trata-se de uma teoria para Map em Coq *)

  Set Implicit Arguments.

  (*Imports*)
  Require Export Coq.Lists.List.
  Require Import Coq.Arith.Arith.
  Require Import Coq.Init.Specif.
  Require Import Coq.Bool.Bool.

  (*library of finite set*)
  Require Export Coq.Lists.ListSet.

  Section Types.

  (*Key and value*)
  Inductive S: Type.
  Inductive T: Type.

  (*pair and map definition*)
  Definition pair_     :Type := prod S T.
  Definition map_     :Type := list pair_.

  Definition empty_map : set T := nil.

  Notation "[-]"        := empty_map.
  Notation "( x , y )" := (pair_ x y).

  End Types.

  Section Spec.

  (*Local Vars*)
  Variable l l1 l2    : S.
  Variable r r1 r2    : T.
  Variable ls ls1 ls2 : set S.
  Variable s m1 m2    : map_.
   
  (** Trabalhar com listas em Coq requer que os seus tipos sejam decidíveis.
      Dessa forma, foi necessário incluir alguns axiomas para os tipos definidos nesse
      arquivo. *) 
  (* decidability to S,T, pair and map *)
  Axiom (Seq_dec : forall x y: S, {x = y} + {x <> y}).
  Axiom (Teq_dec : forall x y: T, {x = y} + {x <> y}).
  Axiom (Peq_dec : forall x y: pair_, {x = y} + {x <> y}).
  Axiom (Mapeq_dec : forall x y: map_, {x = y} + {x <> y}).

  (* get key and value*)
  Definition getKey (p: pair_)   : S := fst p.
  Definition getValue (p: pair_) : T :=  snd p.
  
  (** Foi preferível trabalhar com Prop*)
  (* Prop to bool *)
  Definition is_true (b:Prop) : bool :=
   match b with
     | True => true
   end.

  (** Checa se há um mapeamento entre uma chave e um determinado valor *)
  Fixpoint isMappable (s: map_) (l: S) (r: T): Prop :=
        match s with
          | nil     => False
          | p :: ps => if is_true ((fst p) = l) then 
                          if is_true (snd p = r) then True 
                          else (isMappable ps l r)
                       else (isMappable ps l r)
        end.

  (** mapeamento único: se há um mapeamento entre uma chave para dois valores
      esses valores devem ser os mesmos.*)
  Definition unique s : Prop :=
    forall (l: S) (r1 r2: T), 
      (isMappable s l r1 /\ isMappable s l r2) -> r1 = r2.

  (** Se não levarmos em consideração um elemento do map_ 
      que tem mapeamento único, continuará sendo único*)
   Lemma unique_red:
    forall (s: map_) (p: pair_),
      unique (p :: s) -> unique (s).
    Proof.
      intros s0 p HunqList. 
      unfold unique in HunqList. specialize (HunqList l r1 r2).
      unfold unique. intros l0 r0 r3 Hmap.
      destruct Hmap as [Hmap1 Hmap2]. destruct r0, r3. reflexivity.
    Qed.

  (** Um lema útil para quando queremos 'eliminar' um pair da checagem do mapeamento *)
  Lemma isMappable_elim :
     forall (s: map_) (a: pair_) (l :S) (r: T),
        isMappable (a :: s) l r -> (l = fst a /\ r = snd a)
          \/ isMappable s l r.
  Proof. 
    induction a.
    induction s0.
    - intros l0 r0 HMapList. simpl. simpl in HMapList.
      rewrite l0, a, r0, b. left.
      split. 
      + reflexivity. 
      + reflexivity.
    - intros l0 r0 HMapList. specialize (IHs0 l r).
      left. split.
      + simpl. rewrite l0, a. reflexivity.
      + simpl. rewrite r0, b. reflexivity.
  Qed.

  (* da mesma forma, podemos incluir esse pair no mapeamento *)
  Lemma isMappable_intro :
     forall (s: map_) (a: pair_) (l :S) (r: T),
        (l = fst a /\ r = snd a)
          \/ isMappable s l r ->  isMappable (a :: s) l r.
  Proof.
  induction a.
    induction s0.
    - intros l0 r0 HMapListElim. inversion HMapListElim.
      + clear HMapListElim. destruct H. simpl in H0. simpl in H.
      rewrite H0. rewrite H. simpl. trivial.
      + simpl in H. contradiction.
    - specialize (IHs0 l r). intros l0 r0 HMapListElim. intuition. rewrite H0.
      rewrite H1. simpl. simpl in H0, H1. rewrite l0, a in H0.
      generalize H0. tauto.
  Qed. 
  
  (** ============================EMPTY_MAP============================= **)
  
(** se é vazio, não há mapeamento*)
  Definition Empty (s: map_) := 
    forall (l : S)(r: T) , ~ isMappable s l r.
  
  (* O map_ é vazio? *)
  Definition is_map_empty (s : map_ ) : Prop :=
     if is_true (Empty s) then True else False.
  
  (*Segue que não há um mapeamento entre quaisquer S e T *)
  Lemma empty_is_not_mappable:
    forall (s: map_) (l : S)(r: T),
      Empty s -> ~ isMappable s l r. 
  Proof.
   intros s0 l0 r0.  unfold Empty. 
   intros HnotMpb. specialize (HnotMpb l r). rewrite l0, r0.
   rewrite l, r in HnotMpb. assumption.
  Qed.

  (** Um lema útil para quando queremos 'eliminar' um pair da checagem de é empty *)
  Lemma empty_elim:
    forall (s: map_) (p: pair_),
      Empty (p :: s) -> Empty ( p :: nil) /\ Empty s.
  Proof. 
    induction p.
    induction s0.
    - intros HEmptyNil1. split.
        + apply HEmptyNil1.
        + unfold Empty. intros l0 r0. 
          unfold Empty in HEmptyNil1. specialize (HEmptyNil1 l r).
          simpl in HEmptyNil1. unfold not in HEmptyNil1. contradiction.
    - auto.
  Qed. 

  (* da mesma forma, podemos incluir esse pair*)
  Lemma empty_intro:
    forall (s: map_) (p: pair_),
       Empty s /\ Empty ( p :: nil)  -> Empty (p :: s).
  Proof.
    induction p.
    induction s0.
    - intros HEptConj. destruct HEptConj as [HEmpt1 HEmpt2]. 
      apply HEmpt2.
    - intros HEptConj. destruct HEptConj. intuition.
  Qed.
  
  (** quando temos que um map_ acrescido de um elemento é vazios, podemos inferir
      que tal map_ é vazio*)
  Lemma is_map_empty_elim: 
    forall (p: pair_) (s: map_),
      is_map_empty (p :: s) = True-> (is_map_empty (p :: nil)) = True 
        /\ (is_map_empty s) = True.
  Proof.
     induction p.
     induction s0.
        - intros HMapEmp. split.
          + assumption.
          + unfold is_map_empty.  simpl. reflexivity.
    - tauto.
  Qed. 

  (** Empty e is_map_empty indicam a mesma coisa*)
  Lemma is_map_empty2:forall s, Empty s -> is_map_empty s = True.
  Proof.
   intros s0. induction s0. 
    - simpl. intros HEmptNil. reflexivity. 
    - intros HEmpt. apply empty_elim in HEmpt. auto.
  Qed.


 
(*==========================add_map==========================================*)

  (* função para add um pair_ ao map_*)
 Fixpoint add_map (s: map_) (p: pair_): map_ :=
 match s with
  | nil     => set_add Peq_dec p s
  | x :: xs => if is_true(isMappable s (getKey p) (getValue p)) then 
                    set_add Peq_dec p s 
                else s
  end.
 
  Lemma unique_red_same:
    forall (s: map_) (p1 p2: pair_), 
      ((p1 = p2) /\ (unique (add_map s p2)))
      ->
  (unique (add_map s p1)).
  Proof.
    induction s0.
      - intros p1 p2 Hconj.
        destruct Hconj as [HdecEq HnilMap].
        simpl in HnilMap. inversion HdecEq.
        + intuition.
      - intros p1 p2 HConj.
        destruct HConj as [Heq Hunq]. rewrite Heq.
        apply Hunq.    
  Qed.
  
  (* O mapeamento após a adição deve continuar sendo único*)
  Lemma unique_add:
    forall (s: map_) (p: pair_),
      unique s -> unique (add_map s p).
  Proof.
  induction p.
  induction s0.
  - simpl. unfold unique.
    intros HMpConj1 l0 r3 r4 HMpConj2. 
    rewrite r3, r4. reflexivity.
  - intros HUnqList. apply unique_red in HUnqList.
    apply IHs0 in HUnqList. (*apply unique_red_add.
    split. 
      + left. destruct a0. rewrite s1, t, a, b. reflexivity.    
      + apply HUnqList.*)
  Admitted.

(*=============================remove map========================*) 

  (* função para remover um pair_ do map_*)
  Fixpoint remove_map (s: map_) (p: pair_) : map_ :=
  match s with
  | nil     => s
  | x :: xs => if is_true(x =p) then
                set_remove Peq_dec p s
                else remove_map xs p
    end.

  Lemma unique_red_rmv:
    forall (s: map_) (p1 p2: pair_), 
      ((p1 = p2) \/ (p1 <> p2)) /\ (unique (remove_map s p2))
      ->
  (unique (remove_map (p1 :: s) p2)).
  Proof.
    induction p1.
    induction p2.
    induction s0. 
    - intros. admit.
    - intros Helim. destruct Helim. intuition.
  Admitted.

  (* O mapeamento após a remoção deve continuar sendo único*)
  Lemma unique_rmv:
    forall (s: map_) (p: pair_),
      unique s -> unique (remove_map s p).
  Proof.
  induction p.
  induction s0.
  - simpl. unfold unique. intros H1 l0 r0 r3 H2.
   specialize (H1 l r1 r2). 
    rewrite r0, r3. reflexivity.
  - intro HUnq. apply unique_red in HUnq. 
    apply IHs0 in HUnq. apply unique_red_rmv.
    split. destruct a0. 
      + left. rewrite s1, t, a, b. reflexivity.    
      + apply HUnq.
  Qed.

(*=======================dom img==========================*)

  (* obtêm os domínio dos pares*)
  Fixpoint dom (m: map_) : set S := 
    match m with 
      | nil     => nil
      | p :: ps => set_add Seq_dec (fst p) (dom ps)
    end.

  (* obtêm a imagem dos pares*)
  Fixpoint img (m: map_) : set T := 
    match m with 
      | nil     => nil
      | p :: ps => set_add Teq_dec (snd p) (img ps)
    end.

(*=============================union map========================*) 
   
  (* função para unir dois map_*)
  Definition union_map (s1 s2: map_) : map_:=
      match s1 with
        | nil => s2
        | x :: xs => match s2 with
                      | nil => s1
                      | y :: ys => set_union Peq_dec s1 (set_diff Peq_dec s1 s2)
                       end
        end.
    
  Lemma union_map_nil_left:
    forall (s1: map_),
      union_map nil s1 = s1.
    Proof.
      intros. simpl. reflexivity.
    Qed.

  Lemma union_map_nil_right:
    forall (s1: map_),
      union_map s1 nil = s1.
    Proof.
      intros. induction s1.
      + simpl. reflexivity.
      + simpl. reflexivity.
    Qed.
  
  (* se o mapeamento de dois map_ é único, então o que há no domínio de um, não
      estará no domínio do outro, dessa forma a união resulta em mapeamento único.*)
   Lemma uniqueUnion:
    forall m1 m2, (unique m1) /\ (unique m2) ->
      (forall l,
        set_In l (dom m1) -> ~(set_In l (dom m2)))
          -> unique(app m1 m2).
  Proof.
    intros. 
    destruct H.
    induction m0.
      - induction m3.
        + specialize (H0 l). simpl in H0. exact H.
        + specialize (H0 l). simpl. exact H1.
      - specialize (H0 l). auto.
  Qed.

(*=================================union l e r===================================*)
 
(*união de S*)
Fixpoint union_s (ls1 ls2: set S) : set S:=
    match ls1 with
    | nil => ls2
    | x :: xs => match ls2 with
                  | nil => ls1
                  | y :: ys => if is_true(set_In y ls1) then
                                set_add Seq_dec x ( union_s xs ys)
                                else set_add Seq_dec x (set_add Seq_dec y ( union_s xs ys))
                    end
    end.  
  (*União de T*)
  Definition union_t (rs1 rs2: set T) : set T := 
  match rs1 with
    | nil => rs2
    | x :: xs => match rs2 with
                  | nil => rs1
                  | y :: ys => set_union Teq_dec rs1 rs2
                  end
  end. 


(*==========================================================================*)

  (* Indicates whether there is a key *)
  Fixpoint existsT (s: map_) (l: S): Prop :=
      match s with
      | nil     => False
      | x :: xs => (fst x = l) \/ existsT xs l
      end.

   (* can pick up more than one value for a key, if there is *)
  Fixpoint getTs (s: map_) (l: S) : set T :=
   match s with
    | nil     => nil
    | x :: xs => if is_true(fst x = l) 
                  then set_add Teq_dec (snd x) (getTs xs l) 
                 else getTs xs l
    end.

  Definition option_elim (defaulT: T) (o : option T) : T :=
    match o with
      | Some n'=> n'
      | None   =>  defaulT
    end.

  (* get value *) 
  Fixpoint getT (s: map_) (l: S) : option T :=
   match s with
    | nil     => None
    | x :: xs => if is_true (fst x = l) then Some (snd x) else getT xs l
    end.


  Lemma mappingUnique:
    forall s l, (unique s) \/ (getTs s l) = nil.
   Proof.
   induction s0.
    + intros. intuition.
    + intros. specialize (IHs0 l).
      left. unfold unique. intros.
      rewrite r0, r3. reflexivity.
  Qed. 

(*Asset mapping domain membership*)
  Lemma inDom :
    forall s l r,
      isMappable s l r -> set_In l (dom s).
  Proof.
    intros.
    induction s0.
      + simpl in H. contradiction.
      + apply isMappable_elim in H. intuition.
        - rewrite H. apply set_add_intro2. reflexivity.
        - simpl. apply set_add_intro1. apply H. 
    Qed.

  (*asset mapping function*)
  Fixpoint maps (defaulT: T) (s: map_) (ls: set S) : set T :=
    match s with
      | nil     => nil
      | c :: cs => match ls with
                    | nil     => nil
                    | x :: xs => if is_true (existsT s x) 
                                    then app (option_elim defaulT (getT s x) :: nil) 
                                      (maps defaulT s xs)
                                 else (maps defaulT s xs)
                   end
    end.

  (* an auxiliary lemma for UnionMap *)
  Lemma nilMap:
      forall ls defaulT, 
        maps defaulT nil ls = nil.
    Proof.
    induction ls0.
    - simpl. tauto.
    - intro defaulT. specialize (IHls0 defaulT). 
      simpl. reflexivity.
    Qed.

  Lemma nilKeys:
      forall s defaulT, 
        maps defaulT s nil = nil.
    Proof.
    induction s0.
    - simpl. tauto.
    - intros defaulT. specialize (IHs0 defaulT). 
      simpl. reflexivity.
    Qed.

(* Map over union is equivalent to union of maps*)

  Lemma unionMap:
  forall s ls1 ls2 defaulT, (maps defaulT s (union_s ls1 ls2)) =  
        union_t (maps defaulT s ls1) (maps defaulT s ls2).
  Proof.
    induction s0.
      + induction ls3.
        - induction ls0.
           * simpl. auto.
           * simpl. auto.
        - induction ls0.
           * simpl. auto.
           * simpl. intros. rewrite nilMap. reflexivity.
      + induction ls3.
        -  induction ls0. 
           * simpl. auto.
           * simpl. intros. intuition.
        - induction ls0.
           * simpl. intuition.
           * intuition. specialize (IHs0 ls1 ls2 defaulT).
             specialize (IHls3 defaulT). simpl in IHs0.  admit.
  Admitted.

  Lemma existsMap:
    forall s l r, isMappable s l r -> eq_nat (length (getTs s l)) 1.
  Proof.
  induction s0.
  + intros. simpl in H. contradiction.
  + intros. specialize (IHs0 l r). 
    Admitted.
     

  Lemma notExists:
    forall s ls (defaulT: T), (unique s) ->
      ~(exists l, set_In l ls /\ set_In l (dom s))
        -> maps defaulT s ls = nil.
  Proof.
  intros. assert (forall (l:S), 
    (set_In l ls0 /\ set_In l (dom s0)) -> False) as H2.
    - clear - H0; intros l P1.
      unfold not at 1 in H0.
      apply H0. exists l.
      exact P1. 
    - clear H0. specialize (H2 l).
      induction s0.
      + apply nilMap.
      + induction ls0.
        { apply nilKeys. }
        { intuition. unfold unique in H. specialize (H l r1 r2).
          unfold unique in IHs0.  intuition.
  Admitted.

  (* Distributed mapping over singleton *)
  Lemma mapAM:
    forall s (ls: set S) (l: S) (defaulT: T), (unique s) ->
      set_In l (dom s) ->
        exists (r : T), (isMappable s l r) 
          /\ (maps defaulT s (set_add Seq_dec l ls) 
            = set_add Teq_dec r (maps defaulT s ls)).
  Proof.
    intros. 
    assert (forall (s: map_) (ls: set S) (l: S) (defaulT: T) r0, 
      (isMappable s0 l0 r0 /\ maps defaulT s0 (set_add Seq_dec l0 ls0) =
        set_add Teq_dec r0 (maps defaulT s0 ls0))) as H2. 
      - clear - H0; intros. split.
        induction ls. 
        + induction s0.
           { intuition. }
           { intuition. simpl. simpl in H0. intuition. }
        + induction s0.
           { intuition. }
           { intuition. }
        + induction s0.
           { rewrite nilMap. rewrite -> nilMap. simpl. simpl in H0. contradiction. }
           { admit. }
      - 
Admitted.



End Spec. 

End Maps.

Module Assets.

  Import Maps.
  Require Import Coq.Lists.ListSet. 

  (** Esse mapeamento trata da especificação do Asset da Teoria 
    de Refinamento de Linhas de produtos*)

  (* O AM é o mapeamento do nome do Asset para o Asset propriamente dito, logo 
      definimos Asset e Asset Name como se segue *)
  Definition Asset : Type := Maps.T.
  Definition AssetName : Type := Maps.S.

  Variable a a1 a2 a3 : Asset.
  Variable aSet S1 S2 : set Asset.
  
  (* Decidibilidade *)
  Axiom ANdec_eq : 
    forall x y: Asset, {x = y} + {x <> y}.
  Axiom Asset_dec : 
    forall x y: Asset, {x = y} + {x <> y}.

  (*Assumption <Assets refinement>*)
  Parameter inline assetRef : 
    set Asset -> set Asset -> Prop.

  Inductive wfProduct (aSet : set Asset) : Prop.
  Definition Product (aSet : set Asset) : Type := wfProduct aSet.

  (*Axiom <Asset refinement is pre-order>*)

  Axiom assetRefinement:
    forall x y z: set Asset, assetRef x x /\ 
      assetRef x y -> assetRef y z ->  assetRef x z.


  (*Axiom 5 <Asset refinement compositionality>*)
  Axiom asRefCompositional :
    forall (S1 : set Asset) (S2 : set Asset) (aSet : set Asset),
      (assetRef S1 S2) /\ wfProduct (Maps.union_t  S1 aSet) 
        -> (wfProduct (Maps.union_t  S2 aSet)) 
          /\ assetRef (Maps.union_t  S1 aSet) 
             (Maps.union_t S2 aSet).

  Theorem assetTest:
  forall (S T x y : set Asset) (a b : Asset),
    wfProduct x /\ (assetRef S T) /\ (set_In a x) /\ 
      (assetRef (set_add Asset_dec a nil) (set_add Asset_dec b nil))
        /\ (x = set_add Asset_dec a S) /\ (y = set_add Asset_dec b T) 
          -> assetRef x y.
  Proof.  
  Admitted.

End Assets.

Module AssetMapping.

  Import Maps Assets.
  Require Import Coq.Lists.ListSet.

  (** Um AM se trata de um map_*)
  Definition AM := map_.

  Variable am am1 am2: AM.
  Variable a1 a2 a3: Asset.
  Variable an an1 an2: Assets.AssetName.
  Variable anSet: set AssetName.
  Variable aSet S1 S2: set Asset.
  Variable defaultT: Maps.T.

  Definition pair : Type := AssetName * Asset.
  Definition pairs := set pair.


  (* Asset mapping refinement *)
  (** Para os mapeamentos de ativos A e A ', o último refina 
     o primeiro, denotado por A ⊑ A', sempre que:
     dom (A) = dom (A ') ∧ ∀ n ∈ dom (A) · A <n> ⊑ A' < n> *)
  Definition aMR (am1 am2: AM) : Prop := (dom am1 = dom am2) /\
    forall (an : AssetName), set_In an (dom am1) -> 
      exists (a1 a2: Asset), (isMappable am1 an a1) 
        /\ (isMappable am2 an a2)
          /\ (assetRef (set_add Asset_dec a1 nil) (set_add Asset_dec a2 nil)).

  (*Axiom <Asset refinement is pre-order>*)
  Axiom assetMappingRefinement:
    forall x y z: AM, aMR x x /\ aMR x y -> aMR y z ->  aMR x z.
 
  (*Asset mapping domain membership*)
  Lemma inDom :
    forall am (an: AssetName) (a: Asset), 
      isMappable am an a -> set_In an (dom am).
  Proof.
    intros am0 an0 a HMpb.
    induction am0. 
      - simpl in HMpb. contradiction.
      - apply isMappable_elim in HMpb.  inversion HMpb.
        clear HMpb. destruct H as [Heql1 Heql2].
        + rewrite Heql1. simpl. apply set_add_intro2. reflexivity.
        + simpl. apply set_add_intro1. apply IHam0.
          apply H.
        + intuition.
        + intuition.
    Qed.
  
  (*Asset mapping domain membership*)
  Lemma inImg :
    forall am (an: AssetName) (a: Asset), 
      isMappable am an a -> set_In a (img am).
  Proof.
    intros am0 an0 a HMpb.
    induction am0. 
      - simpl in HMpb. contradiction.
      - apply isMappable_elim in HMpb.  inversion HMpb.
        clear HMpb. destruct H as [Heql1 Heql2].
        + rewrite Heql2. simpl. apply set_add_intro2. reflexivity.
        + simpl. apply set_add_intro1. apply IHam0.
          apply H.
        + intuition.
        + intuition.
    Qed.

  Lemma amRefCompositional:
  forall am1 am2, aMR am1 am2 ->
    (unique am1) /\ (unique am2) ->
      forall anSet,
        forall aSet defaultT,
              assetRef (set_union Asset_dec aSet (maps defaultT am1 anSet)) 
                (set_union Asset_dec aSet (maps defaultT am2 anSet)) /\  
                  wfProduct (set_union Asset_dec aSet (maps defaultT am1 anSet)) ->
                    wfProduct (set_union Asset_dec aSet (maps defaultT am2 anSet)).
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

End AssetMapping.

Module CK.

  Import Maps Assets AssetMapping 
  Name FormulaTheory Form Decidability FeatureModel.
  Require Import Coq.Lists.ListSet.


  Inductive Transformation : Type.

  Definition Item : Type := Formula * Transformation.
  Definition CK : Type := list Item.

  Variable ts: list Transformation.
  Variable t: Transformation.
  Variable am am1 am2 amt1 amt2: AM.
  Variable fm: FM.
  Variable exp: Formula.
  Variable ck ck2 its: CK.
  Variable item it it2: Item.
  Variable items its1 its2: list Item.
  Variable c: Configuration.
  Variable assets S S1 S2: set Asset.
  Variable s: set Configuration.
  Variable an: AssetName.


 Variable l l1 l2    : Maps.S.
 Variable r r1 r2    : Maps.T.
 Variable ls ls1 ls2 : set Maps.S.

  (* Get all Formulas*)
  Fixpoint exps (ck: CK) : set Formula :=
    match ck with
    | nil => nil
    | x :: xs => set_union form_dec (set_add form_dec (fst x) nil) (exps xs)
    end. 

  (* get Formula*)
  Definition getExp (it : Item) : Formula := fst it.
  
  (* get Transformation*)
  Definition getRS (it: Item) : Transformation := snd it.

  Parameter Inline(40) transform : Transformation -> AM-> AM -> AM.
  
  Axiom preserv :
   forall am1 am2 amt1 amt2 t, 
      (unique am1) /\ (unique am2) /\ (unique amt1) /\ (unique amt2) ->
      aMR am1 am2 /\ aMR amt1 amt2 ->
        aMR (transform t am1 am2) (transform t am2 amt2). 

  
  (* get each asset if it satisfies a configuration*)
  Fixpoint semanticsCK (ck : CK) (am amt: AM) (c: Configuration) : set Asset :=
    match ck with
     | nil => img amt
     | x :: xs => if is_true (satisfies (getExp x) c) then 
                    semanticsCK xs am (transform (getRS x) am amt) c  
                  else semanticsCK xs am amt c
    end.
  
  (* get AM if it satisfies a configuration*)
  Fixpoint semanticCK (ck : CK) (am amt: AM) (c: Configuration) : AM :=
    match ck with
    |nil => amt
    | x :: xs => if is_true (satisfies (getExp x) c) 
                    then semanticCK xs am (transform (getRS x) am amt) c 
                 else semanticCK xs am amt c
    end. 
  
  Definition semantics (ck: CK) (am: AM) (c: Configuration): set Asset :=
    semanticsCK ck am (nil) c. 
  
  (* return the same result*)
  Lemma similarFunctions: 
    forall ck am amt c, (unique am) -> semanticsCK ck am amt c 
      = img (semanticCK ck am amt c).
  Proof.
    induction ck0.
      - induction amt.
        + induction am0. 
          * intros. simpl. reflexivity.
          * intros. simpl. reflexivity.
        + induction amt.
          * intros. simpl. reflexivity.
          * intros. simpl. reflexivity.
      - induction amt.
        + induction am0. 
          * intros. simpl. intuition.
          * intros. simpl. intuition.
        + induction amt.
          * intros. simpl. intuition.
          * intros. simpl. intuition.
  Qed.

  (* Provar este teorema garante que esta linguagem é consistente
     com a teoria de refinamento da linha de produtos*)

  Theorem compAmRefEmptyset:
    forall am1 am2,
      (unique am1) /\ (unique am2) ->
        aMR am1 am2 ->
          forall ck c,
            assetRef (semantics ck am1 c) (semantics ck am2 c) /\
            wfProduct (semantics ck am1 c) ->
               wfProduct (semantics ck am2 c).
  Proof.
    induction am1.
      - induction am2.
        + induction ck.
          { intros. destruct H. unfold unique in H. unfold unique in H2.
            specialize (H l r1 r2). specialize (H2 l r1 r2).
            intuition. }
          { intros. destruct H. intuition. }
        + induction ck.
          { intros. destruct H. intuition. }
          { intuition. }
      - induction am2.
        + induction ck.
          { intuition. }
          { intuition. }
        + induction ck.
          { intuition. }
          { intuition. }
  Qed.
  
 (*  O seguinte teorema estabelece que a avaliação de CK sobre 
  o refinamento de AM produz produtos bem formados*)
  
  Theorem compAmRef:
    forall am1 am2,
      (unique am1) /\ (unique am2) ->
        aMR am1 am2 ->
          (forall ck c amt1 amt2,
            assetRef (semanticsCK ck am1 amt1 c) (semanticsCK ck am2 amt2 c)) /\
            aMR amt1 amt2 /\ wfProduct (semanticsCK ck am1 amt1 c) ->
              wfProduct (semanticsCK ck am2 amt2 c).
  Proof.
   induction am1.
      - induction am2.
        + induction ck.
          { intuition. }
          { intuition. }
        + induction ck.
          { intuition. }
          { intuition. }
      - induction am2.
        + induction ck.
          { intuition. }
          { intuition. }
        + induction ck.
          { intuition. }
          { intuition. }
  Qed.

  Lemma wfCKAux:
  forall exp ck f (a: Item),
    (set_In exp (exps ck) -> wt f exp) ->
      (set_In exp (exps (a :: ck)) ->
        wt f exp).
  Proof.
    induction exp0.
    + intros. simpl. intuition.
    + intros. simpl. intuition.
    + intros. admit.
    + intros. simpl. specialize (IHexp0 ck f a). simpl in H. 
      
  Admitted.

  Lemma wfCK (fm: FM) (am :AM) (ck: CK) :
    (unique am) ->
      forall (exp : Formula), set_In exp (exps ck) -> wt (fst fm) exp.
  Proof.
    intros.
    destruct fm.
    simpl.
    induction ck.
      + simpl in H. contradiction.
      + generalize H0. apply wfCKAux.
        apply IHck.
  Qed.


  Lemma addItemsBefore:
    forall am amt ck its s,
      (unique am) /\ (unique amt) ->
        forall c,
          set_In c s-> (
            (forall exp, set_In exp (exps its) -> ~(satisfies exp c) ->
              (semanticsCK ck am amt c = semanticsCK ( its ++ ck) am amt c))).
  Proof.
        induction am1.
      - induction am2.
        + induction ck. 
          { unfold not. intros. destruct H. simpl. intuition.  admit. }
          { auto. }
        + induction ck.
          { auto. }
          { auto. }
      - induction am2.
        + induction ck.
          { auto. }
          { auto. }
        + induction ck.
          { auto. }
          { auto. }


  Admitted.
  
  Lemma addItemsAfter:
    forall am amt ck its s,
      (unique am) /\ (unique amt) ->
        forall c,
          set_In c s-> (
            (forall (exp: Formula), set_In exp (exps its) -> ~(satisfies exp c) ->
              (semanticsCK ck am amt c = semanticsCK ( ck ++ its) am amt c))).
  Proof.
   induction am1.
      - induction am2.
        + induction ck.
          { unfold not. intros. destruct H. admit. }
          { auto. }
        + induction ck.
          { auto. }
          { auto. }
      - induction am2.
        + induction ck.
          { auto. }
          { auto. }
        + induction ck.
          { auto. }
          { auto. }

Admitted.
  
  
End CK.

Module SPLrefinement. 


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
  Definition PL : Type := ArbitrarySPL.
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
          (plRefinement pl ((fm ,(getAM pl)), (getCK pl))).
    Proof.
    intros. 
    destruct H.   
    unfold plRefinement. 
    intros. exists c4.  split.
      +  unfold getFM. simpl.  unfold getFM in H1. destruct pl0 in H1.
        simpl in H1. destruct p0 in H1. simpl in H1. rewrite f in H1.
        rewrite fm0. apply H1. 
      + unfold getCK. unfold getAM. simpl.
        apply assetRefinementReflexivity.
    Qed.

  (* Theorem <Feature model equivalence compositionality>  *)

   Theorem fmEquivalenceCompositionality:
      forall (pl: PL) (fm: FM),
        equivalentFMs (getFM pl) fm ->
          (plRefinement pl ((fm ,(getAM pl)), (getCK pl))) /\
            wfPL ((fm ,(getAM pl)), (getCK pl)).
    Proof.
    intros.
    split.
    + unfold plRefinement. intros. exists c4. split.
      -  unfold getFM. simpl.  unfold getFM in H0. destruct pl0 in H0.
        simpl in H0. destruct p0 in H0. simpl in H0. rewrite f in H0.
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
        (plRefinement pl ((fm ,(getAM pl)), (getCK pl))) /\
           wfPL ((fm ,(getAM pl)), (getCK pl)).
    Proof.
    intros.
    split.
    + unfold plRefinement. intros. exists c4. split.
      -  unfold getFM. simpl.  unfold getFM in H0. destruct pl0 in H0.
        simpl in H0. destruct p0 in H0. simpl in H0. rewrite f in H0.
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
        plRefinement pl ((fm ,(getAM pl)), (getCK pl)) /\
           wfPL ((fm ,(getAM pl)), (getCK pl)).
    Proof.
    intros.
    split.
    + unfold plRefinement. intros. exists c4. split.
      -  unfold getFM. simpl.  unfold getFM in H0. destruct pl0 in H0.
        simpl in H0. destruct p0 in H0. simpl in H0. rewrite f in H0.
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
        plRefinement pl ((fm ,(getAM pl)), (getCK pl)) /\
           wfPL ((fm ,(getAM pl)), (getCK pl)).
    Proof.
    intros.
    split.
    + unfold plRefinement. intros. exists c4. split.
      -  unfold getFM. simpl.  unfold getFM in H0. destruct pl0 in H0.
        simpl in H0. destruct p0 in H0. simpl in H0. rewrite f in H0.
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
            plRefinement pl ((fm ,(getAM pl)), (getCK pl)) /\
              wfPL ((fm ,(getAM pl)), (getCK pl)).
    Proof.
    intros.
    split.
    + unfold plRefinement. intros. exists c4. split.
      -  unfold getFM. simpl.  unfold getFM in H0. destruct pl0 in H0.
        simpl in H0. destruct p0 in H0. simpl in H0. rewrite f in H0.
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
             plRefinement pl ((fm ,(getAM pl)), (getCK pl)).
    Proof.
    intros. 
    destruct H.   
    unfold plRefinement. 
    intros. exists c4.  split.
      +  unfold getFM. simpl.  unfold getFM in H1. destruct pl0 in H1.
        simpl in H1. destruct p0 in H1. simpl in H1. rewrite f in H1.
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
            plRefinement pl ((fm ,(getAM pl)), (getCK pl)) /\
              wfPL ((fm ,(getAM pl)), (getCK pl)).
    Proof.
    intros.
    split.
    + unfold plRefinement. intros. exists c4. split.
      -  unfold getFM. simpl.  unfold getFM in H0. destruct pl0 in H0.
        simpl in H0. destruct p0 in H0. simpl in H0. rewrite f in H0.
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
              plRefinement pl ((fm ,(getAM pl)), (getCK pl)).
    Proof.
    intros. 
    destruct H.   
    unfold plRefinement. 
    intros. exists c4.  split.
      +  unfold getFM. simpl.  unfold getFM in H1. destruct pl0 in H1.
        simpl in H1. destruct p0 in H1. simpl in H1. rewrite f in H1.
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










