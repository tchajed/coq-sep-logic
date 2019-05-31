From SepLogic Require Import Pred Tactics Cancel.

Import PredNotations.

Theorem pred_impl_test1 (p1 p2: pred nat bool) m :
  (p1 * p2)%pred m ->
  (p2 * p1)%pred m.
Proof.
  intros.
  pred_impl.
  cancel.
Qed.

Theorem pred_iff_test1 (p1 p2: pred nat bool) m :
  (p1 * p2)%pred m ->
  (p2 * p1)%pred m.
Proof.
  intros.
  pred_iff.
  cancel.
Qed.
