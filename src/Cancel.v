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
Ltac reify_helper A V term ctx :=
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

Ltac quote_with A V ctx term :=
  let ctx_x := reify_helper A V term ctx in
  let ctx := (eval cbv [fst] in (fst ctx_x)) in
  let x := (eval cbv [snd] in (snd ctx_x)) in
  constr:(interpret ctx x).

Ltac quote term rx :=
  match type of term with
  | pred ?A ?V =>
    let reified := quote_with A V (varmap.empty (pred A V)) term in
    rx reified
  end.

Ltac quote_impl :=
  match goal with
  | |- @pimpl ?A ?V ?x ?y =>
    quote x ltac:(fun x' =>
                    match x' with
                    | interpret ?ctx ?xt =>
                      let y' := quote_with A V ctx y in
                      match y' with
                      | interpret ?ctx' ?yt =>
                        change (interpret ctx' xt ===> interpret ctx' yt)
                      end
                    end)
  end.

Notation "[ i1 |-> v1 ]  :: vm" := (varmap.cons i1 v1 vm)
                                     (at level 20, vm at level 80,
                                      only printing).
Notation "[]" := (varmap.empty _) (at level 0, only printing).

Theorem reify_test A V (p1 p2 p3: pred A V) :
  p1 * p2 * p3 ===> p1 * (p2 * p3).
Proof.
  quote_impl.
Abort.

(*! Proving theorems on reified syntax *)
Section Mem.
  Context (A V:Type).
  Notation pred := (pred A V).
  Notation emp := (@emp A V).

  Notation op_tree := (op_tree A V).
  Notation op_element := (op_element A V).

  Import List.ListNotations.
  Local Open Scope list.

  Fixpoint flatten (t:op_tree) : list op_element :=
    match t with
    | Element e => match e with
                  | ConstEmp _ _ => []
                  | _ => [e]
                  end
    | StarNode l r => flatten l ++ flatten r
    end.

  (*
  Fixpoint flatten (t:op_tree) : list Prop * list op_element :=
    match t with
    | Element e => match e with
                  | ConstEmp _ _ => ([], [])
                  | LiftedProp _ _ P => ([P], [])
                  | _ => ([], [e])
                  end
    | StarNode l r => let (ps1, es1) := flatten l in
                     let (ps2, es2) := flatten r in
                     (ps1 ++ ps2, es2 ++ es2)
    end.
   *)

  Fixpoint int_l vm (l: list op_element) : pred :=
    match l with
    | [] => emp
    | e::es => star (interpret_e vm e) (int_l vm es)
    end.

  Hint Resolve (ltac:(reflexivity) : forall (p:pred), p === p).

  Theorem int_l_app vm l1 l2 :
    int_l vm (l1 ++ l2) === int_l vm l1 * int_l vm l2.
  Proof.
    induction l1; simpl.
    rewrite star_emp_l; auto.
    rewrite <- star_assoc.
    rewrite IHl1; auto.
  Qed.

  Fixpoint flatten_props (l: list Prop) : Prop :=
    match l with
    | [] => True
    | [P] => P
    | P::Ps => P /\ flatten_props Ps
    end.

  Theorem interpret_flatten vm t :
      interpret vm t === int_l vm (flatten t).
  Proof.
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

  Theorem int_l_sort vm l :
      int_l vm l === int_l vm (sortBy get_key l).
  Proof.
    apply int_l_perm.
    apply sortBy_permutation.
  Qed.

  Theorem int_l_sort_eqn vm l1 l2 :
      int_l vm (sortBy get_key l1) === int_l vm (sortBy get_key l2) ->
      int_l vm l1 === int_l vm l2.
  Proof.
    intros.
    rewrite <- ?int_l_sort in H; auto.
  Qed.

  Theorem int_l_sort_impl vm l1 l2 :
      int_l vm (sortBy get_key l1) ===> int_l vm (sortBy get_key l2) ->
      int_l vm l1 ===> int_l vm l2.
  Proof.
    intros.
    setoid_rewrite <- int_l_sort in H; auto.
  Qed.

End Mem.

Ltac norm :=
  intros;
  quote_impl;
  rewrite ?interpret_flatten;
  apply int_l_sort_impl;
  simpl;
  repeat (apply impl_with_lift; intros).
