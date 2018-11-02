From Coq Require Export FunctionalExtensionality.
From Coq Require Import Setoid.

From Tactical Require Import
     Propositional
     SimplMatch.

Require Import SepLogic.Instances.

Set Implicit Arguments.
Generalizable All Variables.

Section Memory.
  Context (A V:Type).
  Definition mem := A -> option V.
  Implicit Types (a:A) (v:V).
  Implicit Types (m:mem).

  Definition empty : mem :=
    fun _ => None.

  Definition union m1 m2 : mem :=
    fun x => match m1 x with
          | Some v => Some v
          | None => m2 x
          end.

  Definition disjoint m1 m2 :=
    forall x v, m1 x = Some v -> forall v', m2 x = Some v' -> False.

  Infix "#" := disjoint (at level 70, no associativity).
  Infix "+" := union.

  Theorem disjoint_match1 m1 m2 :
    m1 # m2 <->
    (forall x, match m1 x with
          | Some v => m2 x = None
          | None => True
          end).
  Proof.
    unfold disjoint; split; intros.
    destruct_with_eqn (m1 x); destruct_with_eqn (m2 x); eauto.
    exfalso; eauto.
    specialize (H x).
    replace (m1 x) in H.
    congruence.
  Qed.

  Theorem disjoint_sym m1 m2 :
    m1 # m2 <-> m2 # m1.
  Proof.
    firstorder.
  Qed.

  Theorem disjoint_sym1 m1 m2 :
    m1 # m2 -> m2 # m1.
  Proof.
    firstorder.
  Qed.

  Theorem disjoint_match2 m1 m2 :
    m1 # m2 <->
    (forall x, match m2 x with
          | Some v => m1 x = None
          | None => True
          end).
  Proof.
    setoid_rewrite disjoint_sym.
    apply disjoint_match1.
  Qed.

  Context {Aeq: EqDec A}.

  Definition upd (m: mem) (a0:A) (v:V) : mem :=
    fun a => if a0 == a then Some v else m a.

  Theorem mem_ext_eq m1 m2 :
    (forall a, m1 a = m2 a) ->
    m1 = m2.
  Proof.
    intros.
    extensionality a; auto.
  Qed.

  Ltac t :=
    unfold upd, empty, disjoint, union;
    repeat match goal with
           | |- @eq mem _ _ => apply mem_ext_eq; intros
           | _ => progress destruct matches
           | _ => progress propositional
           | _ => congruence
           | _ => solve [ eauto ]
           | _ => solve [ exfalso; eauto ]
           end.

  Notation magic := ltac:(t) (only parsing).

  Definition upd_eq m a v :
    upd m a v a = Some v
    := magic.

  Definition upd_ne m a v a' :
    a <> a' ->
    upd m a v a' = m a'
    := magic.

  Definition upd_upd m a v v' :
    upd (upd m a v) a v' = upd m a v'
    := magic.

  Definition upd_upd_ne m a v a' v' :
    a <> a' ->
    upd (upd m a v) a' v' = upd (upd m a' v') a v
    := magic.

  Definition empty_disjoint1 m :
    m # empty
    := magic.

  Definition empty_disjoint2 m :
    empty # m
    := magic.

  Definition empty_union1 m :
    m + empty = m
    := magic.

  Definition empty_union2 m :
    empty + m = m
    := magic.

  Definition disjoint_union_comm m1 m2 :
    m1 # m2 ->
    m1 + m2 = m2 + m1
    := magic.

  Definition union_disjoint1 m m1 m2 :
    m # (m1 + m2) ->
    m # m1.
  Proof.
    t.
    specialize (H _ _ ltac:(eauto)).
    replace (m1 x) in *; t.
  Qed.

  Definition union_disjoint2 m m1 m2 :
    m # (m1 + m2) ->
    m # m2.
  Proof.
    t.
    specialize (H _ _ ltac:(eauto)).
    destruct_with_eqn (m1 x); t.
  Qed.

  Definition union_disjoint_intro m m1 m2 :
    m # m1 ->
    m # m2 ->
    m # (m1 + m2).
  Proof.
    t.
    destruct_with_eqn (m1 x); t.
  Qed.

End Memory.

Arguments empty A V : clear implicits.
