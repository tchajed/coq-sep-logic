Class EqDec A := equal : forall (x y:A), {x=y} + {x<>y}.

Infix "==" := equal (at level 70, no associativity).

#[export]
Hint Extern 2 (EqDec _) => hnf; decide equality : typeclass_instances.

Global Instance unit_eqdec : EqDec unit := ltac:(typeclasses eauto).
Global Instance nat_eqdec : EqDec nat := ltac:(typeclasses eauto).
