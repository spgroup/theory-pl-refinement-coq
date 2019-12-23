Require Export maps_int.
Require Export maps_def.
Import Maps.

Require Import Coq.Lists.ListSet.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Specif.
Require Export Coq.Lists.List.

(** Um lema útil para quando queremos 'eliminar' um pair da checagem do mapeamento *)
  Lemma isMappable_elim :
     forall (s: map_) (a: pair_) (l :S) (r: T),
        isMappable_func (a :: s) l r -> (l = fst a /\ r = snd a)
          \/ isMappable_func s l r.
  Proof. 
    induction a.
    induction s.
    + intros l0 r0 HMapList. simpl. simpl in HMapList.
      rewrite l0, a, r0, b. left.
      split. 
      - reflexivity. 
      - reflexivity.
    + intros l0 r0 HMapList. specialize (IHs l0 r0).
      left. split.
      - simpl. rewrite l0, a. reflexivity.
      - simpl. rewrite r0, b. reflexivity.
  Qed.

  