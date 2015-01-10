Inductive kind := k : nat -> kind.

Inductive typ :=
  | Var : nat -> typ
  | Arrow : typ -> typ -> typ
  | Poly : nat -> kind -> typ -> typ.

