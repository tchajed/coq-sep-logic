From Coq Require List.

From Tactical Require Import Misc.

Require Import SepLogic.Reification.Varmap.
Require Import SepLogic.Reification.Sorting.
Require Import SepLogic.Mem.
Require Export SepLogic.Pred.

Import PredNotations.
Local Open Scope pred.

Set Implicit Arguments.

(*! Setting up reified syntax *)
Instance pred_def A V : Default (pred A V) := @emp A V.

Section Mem.
  Context (A V:Type).
  Notation pred := (pred A V).
  Notation emp := (@emp A V).

  (* non-recursive part of reification *)
  Inductive op_element :=
  | Leaf (x:pred)
  | Atom (i:varmap.I)
  | LiftedProp (P:Prop)
  | ConstEmp
  .

  Definition interpret_e (vm: varmap.t pred) (e: op_element) : pred :=
    match e with
    | Leaf x => x
    | Atom i => varmap.find i vm
    | LiftedProp P => lift P
    | ConstEmp => emp
    end.

  Inductive op_tree :=
  | Element (e: op_element)
  | StarNode (l r: op_tree)
  .


  Fixpoint interpret (vm: varmap.t pred) t : pred :=
    match t with
    | Element e => interpret_e vm e
    | StarNode l r => star (interpret vm l) (interpret vm r)
    end.
End Mem.

(*! Boilerplate for doing reification *)
Local Ltac reify_helper A V term ctx :=
  let reify_rec term ctx := reify_helper A V term ctx in
  lazymatch ctx with
  | context[varmap.cons ?i term _] =>
    constr:( (ctx, Element (Atom A V i)) )
  | _ =>
    lazymatch term with
    | @emp _ _ => constr:( (ctx, Element (ConstEmp A V)) )
    | lift ?P => constr:( (ctx, Element (LiftedProp A V P)) )
    | star ?x ?y =>
      let ctx_x := reify_rec x ctx in
      let ctx_y := reify_rec y (fst ctx_x) in
      let r := (eval cbv [fst snd] in
                   (fst ctx_y, @StarNode A V (snd ctx_x) (snd ctx_y))) in
      constr:(r)
    | _ =>
      let v' := (eval cbv [varmap.length] in (varmap.length ctx)) in
      let ctx' := constr:( varmap.cons v' term ctx ) in
      constr:( (ctx', Element (Atom A V v')) )
    end
  end.

Local Ltac with_reified A V ctx x rx :=
  let ctx_t := reify_helper A V x ctx in
  let ctx := (eval cbv [fst] in (fst ctx_t)) in
  let t := (eval cbv [snd] in (snd ctx_t)) in
  rx ctx t.

Local Ltac init_reify A V x rx :=
  with_reified A V (varmap.empty (pred A V)) x rx.

Ltac quote_impl :=
  match goal with
  | |- @pimpl ?A ?V ?x ?y =>
    let init := init_reify A V in
    let then_do := with_reified A V in
    init x
         ltac:(
      fun ctx xt =>
        then_do ctx y
                ltac:(
          fun ctx' yt =>
            change (interpret ctx' xt ===> interpret ctx' yt)))
  end.

Ltac quote_impl_hyp H :=
  match type of H with
  | ?lhs ===> ?rhs =>
    match goal with
    | |- @pimpl ?A ?V ?x ?y =>
      let init := init_reify A V in
      let then_do := with_reified A V in
      init lhs ltac:(
        fun ctx _ =>
          then_do ctx rhs ltac:(
            fun ctx _ =>
              then_do ctx x ltac:(
                fun ctx xt =>
                  then_do ctx y ltac:(
                    fun ctx' yt =>
                      change (interpret ctx' xt ===> interpret ctx' yt)))))
    end
  end.

Theorem reify_test A V (p1 p2 p3: pred A V) :
  p1 * p2 * p3 ===> p1 * (p2 * p3).
Proof.
  quote_impl.
Abort.

Theorem reify_with_hyp_test A V (p1 p2 p3: pred A V) :
  p3 * p2 ===> p2 ->
  p1 * p2 * p3 ===> p1 * (p2 * p3).
Proof.
  intros.
  quote_impl_hyp H.
Abort.

(*! Proving theorems on reified syntax *)
Module Norm.
  Section Mem.
    Context (A V:Type).
    Notation pred := (pred A V).
    Notation emp := (@emp A V).

    Notation op_tree := (op_tree A V).
    Notation op_element := (op_element A V).

    Import List.ListNotations.
    Local Open Scope list.

    Hint Resolve (ltac:(reflexivity) : forall (p:pred), p === p).

    Fixpoint flatten (t:op_tree) : list op_element :=
      match t with
      | Element e => match e with
                    | ConstEmp _ _ => []
                    | _ => [e]
                    end
      | StarNode l r => flatten l ++ flatten r
      end.

    Fixpoint int_l vm (l: list op_element) : pred :=
      match l with
      | [] => emp
      | e::es => star (interpret_e vm e) (int_l vm es)
      end.

    Fixpoint int_l' vm (acc:pred) (l: list op_element) : pred :=
      match l with
      | [] => acc
      | e::es => int_l' vm (acc * interpret_e vm e) es
      end.

    Definition interpret_l vm (l: list op_element) : pred :=
      match l with
      | [] => emp
      | e::es => int_l' vm (interpret_e vm e) es
      end.

    Theorem int_l'_to_int_l vm l acc :
      int_l' vm acc l === acc * int_l vm l.
    Proof.
      gen acc.
      induction l; intros; simpl.
      - rewrite star_emp_r; auto.
      - rewrite IHl.
        rewrite star_assoc; auto.
    Qed.

    Theorem interpret_l_to_int_l vm l :
      interpret_l vm l === int_l vm l.
    Proof.
      destruct l; simpl; auto.
      rewrite int_l'_to_int_l; auto.
    Qed.

    (* use a simple recursive definition using the above proof *)
    Ltac simplify :=
      rewrite ?interpret_l_to_int_l.

    Theorem int_l_app vm l1 l2 :
      int_l vm (l1 ++ l2) === int_l vm l1 * int_l vm l2.
    Proof.
      induction l1; simpl.
      rewrite star_emp_l; auto.
      rewrite <- star_assoc.
      rewrite IHl1; auto.
    Qed.

    Theorem interpret_flatten vm t :
      interpret vm t === interpret_l vm (flatten t).
    Proof.
      simplify.
      induction t; simpl.
      destruct e; simpl;
        try rewrite star_emp_r; auto.
      rewrite int_l_app.
      rewrite IHt1, IHt2; auto.
    Qed.

    Theorem int_l_perm vm l1 l2:
      Permutation l1 l2 ->
      int_l vm l1 === int_l vm l2.
    Proof.
      induction 1; simpl; auto.
      - rewrite IHPermutation; auto.
      - rewrite ?star_assoc.
        apply star_respects_iff; auto.
        rewrite star_comm; auto.
      - rewrite IHPermutation1, IHPermutation2; auto.
    Qed.

    Definition get_key (e:op_element) : option nat :=
      match e with
      | Atom _ _ i => Some (S i)
      | LiftedProp _ _ _ => Some 0
      | _ => None
      end.

    Theorem interpret_l_sort vm l :
      interpret_l vm l === interpret_l vm (sortBy get_key l).
    Proof.
      simplify.
      apply int_l_perm.
      apply sortBy_permutation.
    Qed.

    Theorem interpret_l_sort_impl vm l1 l2 :
      interpret_l vm (sortBy get_key l1) ===> interpret_l vm (sortBy get_key l2) ->
      interpret_l vm l1 ===> interpret_l vm l2.
    Proof.
      rewrite <- ?interpret_l_sort; auto.
    Qed.

    Local Fixpoint flatten_props (l: list Prop) : Prop :=
      match l with
      | [] => True
      | P::Ps => P /\ flatten_props Ps
      end.

    Fixpoint flatten_props1 (l: list Prop) : Prop :=
      match l with
      | [] => True
      | [P] => P
      | P::Ps => P /\ flatten_props1 Ps
      end.

    Theorem flatten_props1_ok l :
      flatten_props l <-> flatten_props1 l.
    Proof.
      destruct l.
      - firstorder.
      - induction l; simpl.
        firstorder.
        destruct l; firstorder.
    Qed.

    Fixpoint grab_props (l:list op_element) : list Prop * list op_element :=
      match l with
      | [] => ([], [])
      | e::es => let (acc, es') := grab_props es in
                match e with
                | LiftedProp _ _ P =>
                  (P::acc, es')
                | _ => (acc, e::es')
                end
      end.

    Definition int_props vm (x: list Prop * list op_element) : pred :=
      let '(P, es) := x in
      lift (flatten_props1 P) * interpret_l vm es.

    Local Definition int_props' vm (x: list Prop * list op_element) : pred :=
      let '(P, es) := x in
      lift (flatten_props P) * int_l vm es.

    Local Theorem int_props'_ok vm x :
      int_props vm x === int_props' vm x.
    Proof.
      unfold int_props, int_props'.
      destruct x.
      simplify.
      rewrite flatten_props1_ok.
      auto.
    Qed.

    Local Lemma abc_to_bac (p1 p2 p3:pred) :
      p1 * p2 * p3 === p2 * p1 * p3.
    Proof.
      apply star_respects_iff; auto.
      apply star_comm.
    Qed.

    Theorem interpret_grab_props vm l :
      interpret_l vm l === int_props vm (grab_props l).
    Proof.
      simplify.
      rewrite int_props'_ok.
      induction l; simpl.
      rewrite star_emp_r.
      apply emp_to_lift; auto.
      destruct_with_eqn (grab_props l).
      rewrite IHl.
      destruct a; simpl in *;
        rewrite ?star_assoc;
        try solve [ apply abc_to_bac] .
      rewrite lift_star; auto.
    Qed.

    Local Lemma impl_with_lifts (P Q:Prop) (p q: pred) :
      (P -> p ===> q /\ Q) ->
      lift P * p ===> lift Q * q.
    Proof.
      intros.
      apply impl_with_lift; intuition idtac.
      rewrite H.
      rewrite <- emp_to_lift; auto.
      rewrite star_emp_l; reflexivity.
    Qed.

    Theorem grab_props_impl vm l1 l2 :
      (let (P, p) := grab_props l1 in
       let (Q, q) := grab_props l2 in
       flatten_props1 P ->
       interpret_l vm p ===> interpret_l vm q /\ flatten_props1 Q) ->
      interpret_l vm l1 ===> interpret_l vm l2.
    Proof.
      intros.
      rewrite ?interpret_grab_props.
      destruct (grab_props l1) as [P p].
      destruct (grab_props l2) as [Q q].
      simpl.
      apply impl_with_lifts; eauto.
    Qed.

  End Mem.
End Norm.

Ltac norm_reified :=
  rewrite ?Norm.interpret_flatten;
  apply Norm.interpret_l_sort_impl;
  apply Norm.grab_props_impl.

Ltac cleanup_normed_goal :=
  match goal with
  | |- True -> _ => intros _
  | _ => intros
  end;
  try match goal with
      | |- _ /\ True => split; [ | exact I ]
      end;
  repeat match goal with
         | [ H: _ /\ _ |- _ ] => destruct H
         end.

Ltac norm :=
  intros;
  quote_impl;
  norm_reified; simpl;
  cleanup_normed_goal.

Ltac norm_hyp H :=
  intros;
  quote_impl_hyp H;
  norm_reified; simpl;
  cleanup_normed_goal.

Ltac normed_cancellation :=
  try match goal with
      | |- _ /\ _ => split
      end;
  try match goal with
      | |- ?p ===> ?p => reflexivity
      | [ H: ?P |- ?P ] => exact H
      end.

Ltac cancel :=
  norm; normed_cancellation.

Module Demo.
  Ltac norm :=
    intros;
    quote_impl;
    norm_reified.

  Ltac simpl_flatten :=
    cbn [Norm.flatten app].

  Ltac simpl_sorting :=
    cbn [Sorting.sortBy Sorting.sort Sorting.insert_sort Sorting.insert
                        Norm.get_key PeanoNat.Nat.leb].

  Ltac simpl_grab_props :=
    cbn [Norm.grab_props].
End Demo.
