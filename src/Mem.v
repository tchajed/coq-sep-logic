From Coq Require Export FunctionalExtensionality.
From Coq Require Import Setoid.

From Tactical Require Import
     Propositional
     SimplMatch.

Require Import SepLogic.Instances.

Set Implicit Arguments.

Section Memory.
  Context (A V:Type).
  Record mem :=
    mkMem { mem_read :> A -> option V }.
  Implicit Types (a:A) (v:V).
  Implicit Types (m:mem).

  Definition empty : mem :=
    mkMem (fun _ => None).

  Definition union m1 m2 : mem :=
    mkMem (fun x => match m1 x with
                 | Some v => Some v
                 | None => m2 x
                 end).

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

  Global Instance disjoint_symmetric : Symmetric disjoint.
  exact disjoint_sym1.
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
    mkMem (fun a => if a0 == a then Some v else m a).

  Theorem mem_ext_eq m1 m2 :
    (forall a, m1 a = m2 a) ->
    m1 = m2.
  Proof.
    intros.
    destruct m1, m2.
    f_equal.
    extensionality a; auto.
  Qed.

  Hint Unfold mem_read.
  Hint Unfold upd empty disjoint union : mem.

  Ltac t :=
    autounfold with mem;
    simpl;
    repeat match goal with
           | [ m: mem |- _ ] =>
             destruct m as m
           | |- context[mem_read] => progress simpl
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

  Definition union_disjoint_elim m m1 m2 :
    m # (m1 + m2) ->
    m # m1 /\ m # m2.
  Proof.
    split; eauto using union_disjoint1, union_disjoint2.
  Qed.

  Definition union_disjoint_intro m m1 m2 :
    m # m1 ->
    m # m2 ->
    m # (m1 + m2).
  Proof.
    t.
    destruct_with_eqn (m1 x); t.
  Qed.

  Definition union_assoc m1 m2 m3 :
    m1 + m2 + m3 = m1 + (m2 + m3)
    := magic.

  Definition singleton a v : mem := upd empty a v.

  Hint Unfold singleton : mem.

  Definition disjoint_different_singleton m a v v' :
    m # singleton a v ->
    m # singleton a v'.
  Proof.
    t.
    destruct matches in *;
      repeat match goal with
             | [ H: Some _ = Some _ |- _ ] =>
               inversion H; subst; clear H
             end.
    specialize (H _ _ ltac:(eauto)).
    rewrite Heqs in *; eauto.
  Qed.

  Lemma disjoint_from_singleton a v m :
    m a = None ->
    disjoint (singleton a v) m.
  Proof.
    t.
    destruct (a == x); try congruence.
  Qed.

  Lemma disjoint_singleton_oob a v m :
    disjoint (singleton a v) m ->
    m a = None.
  Proof.
    t.
    destruct_with_eqn (m a); eauto.
    specialize (H a v).
    destruct (a == a); try congruence.
    exfalso; eauto.
  Qed.

  Definition singleton_eq a v :
    singleton a v a = Some v
    := magic.

  Definition singleton_ne a v a' :
    a <> a' ->
    singleton a v a' = None
    := magic.

End Memory.

Opaque upd singleton.
Arguments empty A V : clear implicits.

Module MemNotations.
  Declare Scope mem_scope.
  Delimit Scope mem_scope with mem.
  Infix "#" := disjoint (at level 70, no associativity) : mem_scope.
  Infix "+" := union : mem_scope.
  Notation "m [ a  :=  v ]" := (upd m a v) (at level 12, left associativity) : mem_scope.

  (* we need to enable printing of the coercion to use the notation (as opposed
  to printing an application) *)
  Add Printing Coercion mem_read.
  Notation "m [ a ]" := (mem_read m a) (at level 13, no associativity) : mem_scope.
End MemNotations.

Hint Rewrite upd_eq : upd.
Hint Rewrite upd_ne using solve [ trivial || congruence ] : upd.
Hint Rewrite singleton_eq : upd.
Hint Rewrite singleton_ne using solve [ trivial || congruence ] : upd.
Hint Rewrite upd_upd : upd.
