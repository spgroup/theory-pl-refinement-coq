Require Export maps_int.
Require Export maps_def.
Require Export maps_proofs.
Import Maps.

Require Import Coq.Lists.ListSet.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Specif.
Require Export Coq.Lists.List.

Instance Maps_Inst : Maps S T map_:=
{
  unique_ := unique_func;
  dom_ := dom_func;
  img := img_func;
  getTs:= getTs_func;
  isMappable_ := isMappable_func;
  maps := maps_func;
  union_s:= union_s_func;
  union_t:= union_t_func;
  set_add_S := set_add_S_func;
  set_add_T := set_add_T_func;

}. Proof.
{ (*mappingUnique*)
  induction m.
    + intros. intuition.
    + intros. specialize (IHm l).
      left. unfold unique_func. intros.
      rewrite r1, r2. reflexivity.

} { (*inDom*)
  intros.
    induction m.
      + simpl in H. contradiction.
      + apply isMappable_elim in H. intuition.
        - rewrite H. apply set_add_intro2. reflexivity.
        - simpl. apply set_add_intro1. apply H. 
}{ (*eqdecS*)
  apply Seq_dec.
}{ (*eqdecT*)
  apply Teq_dec.
}{ (*unionMap*)
  admit.
}{ (*existsMap*)
  admit.
}{ (*notExists*)
  admit.
}{ (*mapAM*)
  admit.
} Admitted.


