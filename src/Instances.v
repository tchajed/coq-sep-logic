Class EqDec A := equal : forall (x y:A), {x=y} + {x<>y}.

Infix "==" := equal (at level 70, no associativity).

Instance unit_eqdec : EqDec unit := ltac:(hnf; decide equality).
Instance nat_eqdec : EqDec nat := ltac:(hnf; decide equality).
