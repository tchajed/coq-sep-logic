From SepLogic Require Import Pred.
From SepLogic Require Export Cancel.

Ltac pred_impl :=
  match goal with
  | [ H: predApply ?p1 ?m  |- predApply ?p2 ?m ] =>
    apply (@pred_impl_apply _ _ p1 p2 m H)
  end.

Ltac pred_iff :=
  match goal with
  | [ H: predApply ?p1 ?m  |- predApply ?p2 ?m ] =>
    apply (@pred_iff_apply _ _ p1 p2 m H)
  end.
