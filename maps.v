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
    + intros l0 r0 HMapList. simpl. simpl in HMapList.
      rewrite l0, a, r0, b. left.
      split. 
      - reflexivity. 
      - reflexivity.
    + intros l0 r0 HMapList. specialize (IHs0 l r).
      left. split.
      - simpl. rewrite l0, a. reflexivity.
      - simpl. rewrite r0, b. reflexivity.
  Qed.

  (* da mesma forma, podemos incluir esse pair no mapeamento *)
  Lemma isMappable_intro :
     forall (s: map_) (a: pair_) (l :S) (r: T),
        (l = fst a /\ r = snd a)
          \/ isMappable s l r ->  isMappable (a :: s) l r.
  Proof.
  induction a.
    induction s0.
    + intros l0 r0 HMapListElim. inversion HMapListElim.
      - clear HMapListElim. destruct H. simpl in H0. simpl in H.
      rewrite H0. rewrite H. simpl. trivial.
      - simpl in H. contradiction.
    + specialize (IHs0 l r). intros l0 r0 HMapListElim. intuition. rewrite H0.
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

  Lemma empty_elim:
    forall (s: map_) (p: pair_),
      Empty (p :: s) -> Empty ( p :: nil) /\ Empty s.
  Proof. 
    induction p.
    induction s0.
    + intros HEmptyNil1. split.
        - apply HEmptyNil1.
        - unfold Empty. intros l0 r0. 
          unfold Empty in HEmptyNil1. specialize (HEmptyNil1 l r).
          simpl in HEmptyNil1. unfold not in HEmptyNil1. contradiction.
    + auto.
  Qed. 

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
      + intros HMapEmp. split.
        - assumption.
        - unfold is_map_empty.  simpl. reflexivity.
      + tauto.
  Qed. 

  (** Empty e is_map_empty indicam a mesma coisa*)
  Lemma is_map_empty2:forall s, Empty s -> is_map_empty s = True.
  Proof.
   intros s0. induction s0. 
    + simpl. intros HEmptNil. reflexivity. 
    + intros HEmpt. apply empty_elim in HEmpt. auto.
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
      + intros p1 p2 Hconj.
        destruct Hconj as [HdecEq HnilMap].
        simpl in HnilMap. inversion HdecEq.
        intuition.
      + intros p1 p2 HConj.
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
