Require Export Coq.Lists.ListSet.
Require Export Coq.Lists.List.
Require Export Coq.Bool.Bool.
Require Export Coq.Classes.RelationClasses.
Require Export formulatheory_def.
Import FormulaTheory.


Theorem not_compat : forall A B : Prop,
  (A = B) -> ((~ A) = (~B)).
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma set_union_elim_not :
   forall (a:Name) (x y:set Name),
     ~(set_In a (set_union name_dec_axiom x y)) -> 
        ~(set_In a x) /\ ~(set_In a y).
Proof.
  intros. split.
    + intuition. apply H. apply set_union_intro1. apply H0.
    + intuition. apply H. apply set_union_intro2. apply H0.
Qed.

Lemma set_union_elim_not2 :
   forall (a:Name) (x y:set Name),
     ~(set_In a x) /\ ~(set_In a y) ->
      ~(set_In a (set_union name_dec_axiom x y)).
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
    ~ set_In n (set_diff name_dec_axiom (names_func f1) (names_func f2)) ->
    ~ set_In n (names_func f1) \/ set_In n (names_func f2).
Proof.
  intros. left.
  intuition. apply H.
  apply set_diff_intro.
  + apply H0.
  + unfold not. intro.
  apply H. apply set_diff_intro.
  apply H0.
Admitted.