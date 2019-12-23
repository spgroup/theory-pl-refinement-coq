Module CKTransSPL.
Require Export cktrans_spl_int.
Require Export assetmapping_spl_def.
Require Export featuremodel_spl_def.
Import FeatureModelSPL.
Import AssetMappingSPL.  
Require Import Coq.Lists.ListSet.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Specif.
Require Export Coq.Lists.List.


 Inductive CK: Type.
 Parameter CKSem_func : 
  CK -> AM -> Conf -> set Asset.

  (* Axiom over ck evaluation *)
  Axiom amRef_func: forall (am1 am2: AM),
    (aMR_func am1 am2) -> forall (K: CK) (C: Conf),
      wfProduct_ind (CKSem_func K am1 C) -> wfProduct_ind (CKSem_func K am2 C)
      /\ assetRef_func (CKSem_func K am1 C) (CKSem_func K am2 C). 

  Parameter CKConf_func:
  CK -> set Conf.

(*  % Definition <CK equivalence>   *)
  Definition equivalentCKsAux (ck1 ck2: CK): Prop :=
   match (set_diff conf_dec (CKConf_func ck1) (CKConf_func ck2)) with
    | nil => True
    | _ => False
    end.

 Definition equivalentCKs_func (ck1 ck2: CK): Prop :=
  (equivalentCKsAux ck1 ck2) /\ (equivalentCKsAux ck2 ck1).


  Definition weakerEqCK_func (fm: FM) (ck1 ck2: CK): Prop :=
    forall am,
      forall c, set_In c (FMRef_Func fm) ->
        (CKSem_func ck1 am c = CKSem_func ck2 am c).

End CKTransSPL.
