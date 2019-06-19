Require Import SepLogic.Cancel.

Import PredNotations.
Local Open Scope pred.

Section Tests.
  Context (A V:Type).
  Notation pred := (pred A V).
  Implicit Type (p:pred).
  Implicit Types (P Q:Prop).

  Theorem test_assoc p1 p2 p3 :
    p1 * p2 * p3 ===> p1 * (p2 * p3).
  Proof.
    cancel.
  Qed.

  Theorem test_reorder p1 p2 p3 :
    p1 * p2 * p3 ===> p1 * (p3 * p2).
  Proof.
    cancel.
  Qed.

  Theorem test_collapse_emp p1 :
    emp * p1 ===> p1 * emp * emp.
  Proof.
    cancel.
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

  Theorem test_cancel_extra_prop p1 (P Q:Prop) :
    (P -> Q) ->
    p1 * [P] ===> p1 * [Q].
  Proof.
    cancel.
    (* cancel only solves the most trivial extra props *)
    auto.
  Qed.

  Theorem test_cancel_exact_prop p1 (P:Prop) :
    p1 * [P] ===> p1 * [P].
  Proof.
    cancel.
  Qed.

  Theorem test_cancel_hyp p1 p2 p3 p4 :
    p4 * p1 ===> p3 ->
    p1 * p2 * p4 ===> p2 * p3.
  Proof.
    intros.
    (* norm_with ensures normalization prefers the hypothesis terms *)
    norm_with H.
    rewrite H.
    reflexivity.
  Qed.

  Theorem test_cancel_hyp2 p1 p2 p3 p4 :
    p3 ===> p4 * p1 ->
    p2 * p3 ===> p1 * p2 * p4.
  Proof.
    intros.
    norm_with H.
    rewrite <- H.
    reflexivity.
  Qed.

  Theorem test_lift_hyp1 (P: Prop) p m :
    predApply ([P] * p) m ->
    P.
  Proof.
    intro H.
    norm_hyp H.
    assumption.
  Qed.

  Theorem test_lift_hyp2 (P Q: Prop) p1 p2 m :
    predApply (p1 * [P] * [Q] * p2) m ->
    Q.
  Proof.
    intro H.
    norm_hyp H.
    assumption.
  Qed.

End Tests.

Module GitHubIssues.
  Inductive perm := Public | Private.
  Definition value : Type := perm * nat.
  Theorem test_issue_4 (F: pred nat value) v v1 v2 :
    F * 0 |-> (Public, v) * 1 |-> v1 * 2 |-> v2 ===>
    F * 1 |-> v1 * 2 |-> v2 * 0 |-> (Public, v).
  Proof.
    cancel.
  Qed.
End GitHubIssues.

Module Demo.

  Arguments Atom {A V}.
  Arguments LiftedProp {A V}.

  Import Norm.
  Import Varmap.VarmapNotations.
  Local Open Scope vm.

  Theorem test_demo A V (p1 p2 p3: pred A V) (P Q:Prop) :
    P ->
    p1 * (p2 * p3 * emp) * [Q] ===> [P] * p1 * emp * (p3 * p2).
  Proof.
    Demo.norm.
    Demo.simpl_flatten.
    (* flatten doesn't even keep the [emp]s *)
    Demo.simpl_sorting.
    (* sorting reorders all lifted props to the front, and orders atoms by their
    index (which in practice will be the order from the left hand side) *)
    Demo.simpl_grab_props.
    (* finally, flatten_props1 and interpret_l make sure to produce the correct
    associativity and for non-empty lists do not leave an extra True or emp at
    the end *)
    simpl.
    cleanup_normed_goal; normed_cancellation.
  Qed.

End Demo.
