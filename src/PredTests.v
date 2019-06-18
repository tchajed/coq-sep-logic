From Coq Require List.
Import List.ListNotations.
Open Scope list.

From SepLogic Require Import Mem Pred.
Import PredNotations.
Open Scope pred.

From Tactical Require Import Propositional.

Inductive handle := Handle (n:nat).
Axiom block : Type.

Theorem exists_manipulation (F: pred nat block) (o: list handle) (s: nat -> option unit) a (d: mem nat block) :
  (F * (exists! v h o', [o = Handle h :: o'] * [s h = None] * a |-> v))%pred d ->
  True.
Proof.
  intros.
  (* TODO: argh, preserving binder names is hard here *)
  repeat setoid_rewrite pred_ex_over_star in H.
  repeat (apply pred_ex_elim in H; deex).
  match type of H with
  | context[pred_ex] => fail 1 "should no longer be exists"
  | _ => idtac
  end.
Abort.
