Module Maps.

Require Export maps_int.
Require Import Coq.Lists.ListSet.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Specif.
Require Export Coq.Lists.List.

(*Key and value*)
  Inductive S: Type.
  Inductive T: Type.

  (*pair and map definition*)
  Definition pair_     :Type := prod S T.
  Definition map_     :Type := list pair_.

  Definition empty_map : set T := nil.

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
  Fixpoint isMappable_func (s: map_) (l: S) (r: T): Prop :=
        match s with
          | nil     => False
          | p :: ps => if is_true ((fst p) = l) then 
                          if is_true (snd p = r) then True 
                          else (isMappable_func ps l r)
                       else (isMappable_func ps l r)
        end.

  (** mapeamento único: se há um mapeamento entre uma chave para dois valores
      esses valores devem ser os mesmos.*)
  Definition unique_func s : Prop :=
    forall (l: S) (r1 r2: T), 
      (isMappable_func s l r1 /\ isMappable_func s l r2) -> r1 = r2.

  (* obtêm os domínio dos pares*)
  Fixpoint dom_func (m: map_) : set S := 
    match m with 
      | nil     => nil
      | p :: ps => set_add Seq_dec (fst p) (dom_func ps)
    end.

  (* obtêm a imagem dos pares*)
  Fixpoint img_func (m: map_) : set T := 
    match m with 
      | nil     => nil
      | p :: ps => set_add Teq_dec (snd p) (img_func ps)
    end. 

  (*união de S*)
Fixpoint union_s_func (ls1 ls2: set S) : set S:=
    match ls1 with
    | nil => ls2
    | x :: xs => match ls2 with
                  | nil => ls1
                  | y :: ys => if is_true(set_In y ls1) then
                                set_add Seq_dec x ( union_s_func xs ys)
                                else set_add Seq_dec x (set_add Seq_dec y ( union_s_func xs ys))
                    end
    end.  
  (*União de T*)
  Definition union_t_func (rs1 rs2: set T) : set T := 
  match rs1 with
    | nil => rs2
    | x :: xs => match rs2 with
                  | nil => rs1
                  | y :: ys => set_union Teq_dec rs1 rs2
                  end
  end.

    (* Indicates whether there is a key *)
  Fixpoint existsT (s: map_) (l: S): Prop :=
      match s with
      | nil     => False
      | x :: xs => (fst x = l) \/ existsT xs l
      end.

   (* can pick up more than one value for a key, if there is *)
  Fixpoint getTs_func (s: map_) (l: S) : set T :=
   match s with
    | nil     => nil
    | x :: xs => if is_true(fst x = l) 
                  then set_add Teq_dec (snd x) (getTs_func xs l) 
                 else getTs_func xs l
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

  (*asset mapping function*)
  Fixpoint maps_func (defaulT: T) (s: map_) (ls: set S) : set T :=
    match s with
      | nil     => nil
      | c :: cs => match ls with
                    | nil     => nil
                    | x :: xs => if is_true (existsT s x) 
                                    then app (option_elim defaulT (getT s x) :: nil) 
                                      (maps_func defaulT s xs)
                                 else (maps_func defaulT s xs)
                   end
    end.

  Definition set_add_S_func (s: S) (s1: set S): set S := set_add Seq_dec s s1.
  Definition set_add_T_func (t: T) (t1: set T): set T := set_add Teq_dec t t1.

End Maps.
