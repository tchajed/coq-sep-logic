Require Import SepLogic.Cancel.

Import PredNotations.
Local Open Scope pred.

Section Tests.
  Context (A V:Type).
  Notation pred := (pred A V).
  Implicit Types (p:pred).
  Implicit Types (P Q:Prop).

  Theorem test_assoc p1 p2 p3 :
    p1 * p2 * p3 ===> p1 * (p2 * p3).
  Proof.
    norm; reflexivity.
  Qed.

  Theorem test_reorder p1 p2 p3 :
    p1 * p2 * p3 ===> p1 * (p3 * p2).
  Proof.
    norm; reflexivity.
  Qed.

  Theorem test_collapse_emp p1 :
    emp * p1 ===> p1 * emp * emp.
  Proof.
    norm; reflexivity.
  Qed.

  Theorem test_lift_prop p1 p2 p3 Q :
    p1 * p2 * p3 * [Q] ===> p1 * (p3 * p2).
  Proof.
    norm.
    match goal with
    | [ H: Q |- _ ] => reflexivity
    end.
  Qed.

  Theorem test_norm_repeat p1 p2 :
    p1 * p2 ===> p2 * p1.
  Proof.
    norm.
    try (progress norm; fail 1 "norm should do nothing if repeated").
    reflexivity.
  Qed.

  Theorem test_norm_nice_goals p1 p2 p3 p (P Q: Prop) :
    (P -> p1 * p2 * p3 ===> p) ->
    p1 * [Q] * p2 * p3 * [P] ===> p.
  Proof.
    intros Himpl.
    norm.
    exact (Himpl ltac:(assumption)).
  Qed.

End Tests.
