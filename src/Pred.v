From Coq Require Import Morphisms.
From Coq Require Import RelationClasses.

From Tactical Require Import
     Propositional
     ExistentialVariants.

Require Import SepLogic.Mem.
Require Import SepLogic.Instances.

Import MemNotations.
Local Open Scope mem.

Set Implicit Arguments.

Section Pred.
  Context (A V:Type).
  Notation mem := (mem A V).
  Notation empty := (empty A V).

  Definition pred := mem -> Prop.

  Implicit Types (a:A) (v:V).
  Implicit Types (m:mem) (p:pred).

  Definition pimpl p1 p2 :=
    forall m, p1 m -> p2 m.

  Infix "===>" := pimpl (at level 60, no associativity).

  Global Instance pimpl_preorder : PreOrder pimpl.
  firstorder.
  Qed.

  Definition piff p1 p2 :=
    forall m, p1 m <-> p2 m.

  Infix "===" := piff (at level 60, no associativity).

  Global Instance piff_equivalence : Equivalence piff.
  firstorder.
  Qed.

  Theorem pimpl_to_piff p1 p2 :
    p1 ===> p2 ->
    p2 ===> p1 ->
    p1 === p2.
  Proof.
    firstorder.
  Qed.

  Theorem piff_to_pimpl p1 p2 :
    p1 === p2 ->
    p1 ===> p2 /\
    p2 ===> p1.
  Proof.
    firstorder.
  Qed.

  Hint Unfold pimpl piff : pred.
  Hint Rewrite empty_union1 empty_union2 : mem.

  Ltac t :=
    autounfold with pred;
    repeat match goal with
           | |- _ <-> _ => split
           | [ H: (_ + _) # _ |- _ ] =>
             apply disjoint_sym1 in H; apply union_disjoint_elim in H
           | [ H: _ # (_ + _)  |- _ ] =>
             apply union_disjoint_elim in H
           | _ => progress propositional
           | _ => progress autorewrite with mem
           | _ => solve [ eauto 10 ]
           end.

  Notation magic := ltac:(t) (only parsing).

  Definition emp : pred := fun m => m = empty.
  Definition lift (P: Prop) : pred := fun m => P /\ m = empty.

  Hint Unfold emp lift : pred.

  Definition lift_emp : forall P, lift P ===> emp
    := magic.

  Definition emp_to_lift : forall (P:Prop),
      P -> emp === lift P
    := magic.

  Definition star p1 p2 : pred :=
    fun m => exists m1 m2, p1 m1 /\ p2 m2 /\
                   m1 # m2 /\
                   m = m1 + m2.
  Infix "*" := star.

  Hint Unfold star : pred.

  Hint Resolve disjoint_sym1.
  Hint Resolve disjoint_union_comm.
  Hint Resolve union_disjoint_intro.
  Hint Resolve empty_disjoint1 empty_disjoint2.

  Hint Rewrite <- union_assoc : mem.

  Definition star_comm p1 p2 :
    p1 * p2 === p2 * p1
    := magic.

  Definition star_assoc p1 p2 p3 :
    p1 * (p2 * p3) === p1 * p2 * p3.
  Proof.
    t.
    repeat match goal with
           | [ |- exists _, _ ] => eexists
           | [ |- _ /\ _ ] => split
           | [ |- _ = _ ] => reflexivity
           | _ => (exact H || exact H3 || exact H0)
           end; t.
    repeat match goal with
           | [ |- exists _, _ ] => eexists
           | [ |- _ /\ _ ] => split
           | [ |- _ = _ ] => reflexivity
           | _ => (exact H || exact H3 || exact H0)
           end; t.
  Qed.

  Theorem star_emp_r p :
    p * emp === p.
  Proof.
    t.
    descend; intuition eauto.
    t.
  Qed.

  Theorem star_emp_l p :
    emp * p === p.
  Proof.
    rewrite star_comm.
    apply star_emp_r.
  Qed.

  Definition lift_star : forall P1 P2,
      lift P1 * lift P2 === lift (P1 /\ P2)
    := magic.

  Definition impl_with_lift (P:Prop) p1 p2 :
    (P -> p1 ===> p2) ->
    lift P * p1 ===> p2
    := magic.

  Definition lift_equiv : forall P1 P2,
      P1 <-> P2 ->
      lift P1 === lift P2
    := magic.

  Global Instance lift_respects_iff :
    Proper (iff ==> piff) lift.
  Proof.
    firstorder.
  Qed.

  Definition lift_impl : forall (P1 P2:Prop),
      P1 -> P2 ->
      lift P1 ===> lift P2
    := magic.

  Global Instance lift_respects_impl :
    Proper (Basics.impl ==> pimpl) lift.
  Proof.
    firstorder.
  Qed.

  Definition sep_ex T (p: T -> pred) : pred :=
    fun m => exists x, p x m.

  Context `{Aeq: EqDec A}.

  (* not strictly necessary to use decidable equality for ptsto, but in practice
probably fine *)
  Definition ptsto a v : pred :=
    fun m => m = singleton a v.

  Hint Unfold ptsto : pred.

  Theorem ptsto_strictly_exact a v m1 m2 :
    ptsto a v m1 ->
    ptsto a v m2 ->
    m1 = m2.
  Proof.
    t.
  Qed.

  Hint Resolve disjoint_different_singleton.

  Ltac simpl_union :=
    unfold union; cbn [mem_read];
    autorewrite with upd; auto.

  Theorem upd_ptsto m a v0 v p :
    (star p (ptsto a v0)) m ->
    (star p (ptsto a v)) (upd m a v).
  Proof.
    t.
    exists m1, (singleton a v);
      intuition eauto.
    apply mem_ext_eq; intro a'.
    destruct (a == a'); subst; autorewrite with upd.
    - rewrite disjoint_union_comm by eauto.
      simpl_union.
    - simpl_union.
  Qed.

  Theorem ptsto_eq m a v p :
    (star p (ptsto a v)) m ->
    m a = Some v.
  Proof.
    t.
    rewrite disjoint_union_comm by auto.
    simpl_union.
  Qed.

  Global Instance star_respects_impl :
    Proper (pimpl ==> pimpl ==> pimpl) star.
  Proof.
    unfold Proper, "==>"; intros.
    t.
  Qed.

  Global Instance piff_subrelation :
    subrelation piff pimpl.
  Proof.
    firstorder.
  Qed.

  Global Instance star_respects_iff :
    Proper (piff ==> piff ==> piff) star.
  Proof.
    unfold Proper, "==>"; intros.
    apply piff_to_pimpl in H.
    apply piff_to_pimpl in H0.
    t.
  Qed.

  Global Instance piff_pimpl_partial_apply p :
    Proper (piff ==> Basics.impl) (pimpl p).
  Proof.
    firstorder.
  Qed.

  Global Instance piff_pimpl_applied :
    Proper (piff ==> piff ==> Basics.impl) pimpl.
  Proof.
    firstorder.
  Qed.

End Pred.

Module PredNotations.
  Declare Scope pred_scope.
  Delimit Scope pred_scope with pred.
  Infix "===>" := pimpl (at level 60, no associativity) : pred_scope.
  Infix "===" := piff (at level 60, no associativity) : pred_scope.
  Infix "*" := star : pred_scope.
  Notation "a |-> v" := (ptsto a v) (at level 35, no associativity) : pred_scope.
  Notation "[ P ]" := (lift P) : pred_scope.
  Notation "'exists' x .. y , p" :=
    (sep_ex (fun x => .. (sep_ex (fun y => p)) ..)) : pred_scope.
End PredNotations.

Arguments emp {A V}.
