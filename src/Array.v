From Tactical Require Import Propositional.

From SepLogic Require Import Mem Pred Cancel.
(* BUG: coqdep doesn't understand From Array makes this unambiguous (even though
it's more precise than this) *)
Require Import Array.Array.

Require Import Omega.

Section Arrays.
  Import List.ListNotations.
  Open Scope list.

  Import PredNotations.
  Open Scope pred.

  Context (V:Type).
  Notation list := (list V).
  Notation mem := (mem nat V).
  Notation pred := (pred nat V).
  Definition array (l:list) : mem := mkMem (index l).

  Lemma array_read l :
    mem_read (array l) = index l.
  Proof.
    reflexivity.
  Qed.

  Hint Rewrite array_read : array.

  Lemma array_inj l1 l2 :
    array l1 = array l2 ->
    l1 = l2.
  Proof.
    unfold array; simpl; intros.
    inversion H; auto.
    apply index_ext_eq; congruence.
  Qed.

  Definition ptsto_array (n:nat) (x:list) : pred :=
    fun m =>
      forall i, (i < n -> m i = None) /\
           (i >= n -> m i = index x (i-n)).

  Theorem ptsto_array_subslice n x :
    forall l, ptsto_array n x (array l) ->
         subslice l n (length x) = x.
  Proof.
    unfold ptsto_array; propositional.
    apply index_ext_eq; intros i.
    simpl in *.
    destruct (lt_dec i (length x));
      autorewrite with array in *.
    specialize (H (n+i)); propositional.
    specialize (H0 ltac:(omega)).
    rewrite minus_plus in H0; auto.
    auto.
  Qed.

  Theorem ptsto_array_oob_small n x m :
    ptsto_array n x m ->
    forall i, i < n -> m i = None.
  Proof.
    unfold ptsto_array; propositional.
    specialize (H i); propositional.
  Qed.

  Theorem ptsto_array_oob_large n x m :
    ptsto_array n x m ->
    forall i, i >= n + length x -> m i = None.
  Proof.
    unfold ptsto_array; propositional.
    specialize (H i); propositional.
    specialize (H1 ltac:(omega)).
    autorewrite with array in H1.
    auto.
  Qed.

  Definition array_at_mem n x : mem :=
    mkMem (fun i => if le_dec n i then index x (i-n)
                 else None).

  Theorem ptsto_array_mem n x m :
    ptsto_array n x m <->
    m = array_at_mem n x.
  Proof.
    unfold ptsto_array; split; intros.
    - apply mem_ext_eq; simpl; intros i.
      destruct (le_dec n i).
      specialize (H i); propositional.
      specialize (H i); propositional.
      specialize (H ltac:(omega)); auto.
    - subst; simpl.
      destruct (le_dec n i); intuition (auto; try omega).
  Qed.

  Theorem ptsto_array_to_mem n x :
    ptsto_array n x === eq (array_at_mem n x).
  Proof.
    split; intros.
    - apply ptsto_array_mem in H; auto.
    - apply ptsto_array_mem; auto.
  Qed.

  Fixpoint array_ptsto_star n l : pred :=
    match l with
    | [] => emp
    | x::xs => ptsto n x * array_ptsto_star (S n) xs
    end.

  Lemma ptsto_array_nil n :
    ptsto_array n [] === emp.
  Proof.
    rewrite ptsto_array_to_mem.
    unfold emp, empty.
    split; intros; subst; simpl.
    - apply mem_ext_eq; intros i; simpl.
      destruct (le_dec n i); auto.
    - apply mem_ext_eq; intros i; simpl.
      destruct (le_dec n i); auto.
  Qed.

  Lemma array_at_mem_cons n x xs :
    array_at_mem n (x::xs) = union (singleton n x) (array_at_mem (S n) xs).
  Proof.
    apply mem_ext_eq; intros i; simpl.
    subst; simpl.
    destruct (le_dec n i), (Instances.equal n i), (le_dec (S n) i);
      try omega;
      auto.
    replace (i - n) with 0 by omega; auto.
    destruct_with_eqn (i - n); try omega.
    f_equal; omega.
  Qed.

  Lemma ptsto_array_cons n x xs :
    ptsto_array n (x::xs) === ptsto n x * ptsto_array (S n) xs.
  Proof.
    rewrite ?ptsto_array_to_mem.
    split; intros.
    - unfold star.
      eexists (singleton n x), _; intuition eauto.
      + unfold ptsto; auto.
      + apply disjoint_from_singleton.
        simpl.
        destruct (le_dec (S n) n); auto; try omega.
      + rewrite array_at_mem_cons in *; auto.
    - unfold star, ptsto in H; propositional.
      rewrite array_at_mem_cons; auto.
  Qed.

  Theorem ptsto_array_ptsto_star l :
    forall n, ptsto_array n l === array_ptsto_star n l.
  Proof.
    induction l; simpl; intros.
    - apply ptsto_array_nil.
    - rewrite ptsto_array_cons.
      rewrite IHl.
      reflexivity.
  Qed.

  Theorem ptsto_array_seq n1 x1 n2 x2 :
    n2 = n1 + length x1 ->
    ptsto_array n1 x1 * ptsto_array n2 x2 === ptsto_array n1 (x1 ++ x2).
  Proof.
    intros; subst.
    rewrite ?ptsto_array_ptsto_star.
    generalize dependent x2.
    generalize dependent n1.
    induction x1; simpl; intros.
    - replace (n1 + 0) with n1 by omega;
      cancel.
    - rewrite <- IHx1.
      rewrite Nat.add_succ_r.
      cancel.
  Qed.

End Arrays.
