Require Import SepLogic.Instances.
Require Export FunctionalExtensionality.

Set Implicit Arguments.
Generalizable All Variables.

Section Memory.
  Context (A V:Type).
  Definition mem := A -> option V.
  Implicit Type (m:mem).

  Definition union m1 m2 : mem :=
    fun x => match m1 x with
          | Some v => Some v
          | None => m2 x
          end.

  Definition disjoint m1 m2 :=
    forall x, m1 x = None <-> m2 x = None.

  Theorem disjoint_sym m1 m2 :
    disjoint m1 m2 -> disjoint m2 m1.
  Proof.
    firstorder.
  Qed.

  Context {Aeq: EqDec A}.

  Definition upd (m: mem) (a0:A) (v:V) : mem :=
    fun a => if a0 == a then Some v else m a.

  Theorem upd_eq m a v :
    upd m a v a = Some v.
  Proof.
    unfold upd.
    destruct (a == a); try congruence.
  Qed.

  Theorem upd_ne m a v a' :
    a <> a' ->
    upd m a v a' = m a'.
  Proof.
    unfold upd; intros.
    destruct (a == a'); try congruence.
  Qed.

  Theorem mem_ext_eq m1 m2 :
    (forall a, m1 a = m2 a) ->
    m1 = m2.
  Proof.
    intros.
    extensionality a; auto.
  Qed.

  Theorem upd_upd m a v v' :
    upd (upd m a v) a v' = upd m a v'.
  Proof.
    unfold upd; intros.
    apply mem_ext_eq; intros.
    destruct (a == a0); subst; auto.
  Qed.

  Theorem upd_upd_ne m a v a' v' :
    a <> a' ->
    upd (upd m a v) a' v' = upd (upd m a' v') a v.
  Proof.
    unfold upd; intros.
    apply mem_ext_eq; intros.
    destruct (a == a0); subst; auto.
    destruct (a' == a0); try congruence.
  Qed.

End Memory.
