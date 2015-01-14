Require Import Arith.

Inductive kind := k : nat -> kind.

Inductive typ :=
  | typ_var : nat -> typ
  | typ_arrow : typ -> typ -> typ
  | typ_poly : typ -> typ -> typ.

Eval compute in if le_gt_dec 3 5 then true else false.

(** Shifting function for types
typ_shift (X:nat) (T:typ) : typ increments by one every var greater than X in T. **)

Fixpoint typ_shift (X : nat) (T : typ) : typ := 
  match T with
    | typ_var Y  => if le_gt_dec X Y then 
                      typ_var (Y + 1)
                    else
                      typ_var Y
    | typ_arrow T U => typ_arrow (typ_shift X T) (typ_shift X U)
    | typ_poly T U => typ_poly (typ_shift X T) (typ_shift (X + 1) U)
  end.

Fixpoint tsubst (X : nat) (T2 : typ) (T : typ) : typ := 
  match T with
    | typ_var Y => match lt_eq_lt_dec X Y with
                     | inleft (left _) => typ_var (Y -1)
                     | inleft (right _) => T2
                     | inright _ => typ_var Y
                   end
    | typ_arrow T U => typ_arrow (tsubst X T2 T) (tsubst X T2 U)
    | typ_poly T U => typ_poly (tsubst X T2 T) (tsubst (X + 1) (typ_shift 0 T2) U)
  end.

Inductive term :=
  | var : nat -> term
  | lambda : typ -> term -> term
  | app : term -> term -> term
  | tlambda : typ -> term -> term
  | tapp : term -> typ -> term.

Fixpoint term_shift (x : nat) (t : term) : term :=
  match t with
    | var y => if le_gt_dec x y then
                 var (y + 1)
               else
                 var y
    | lambda T t => lambda T (term_shift (x + 1) t)
    | app t u => app (term_shift x t) (term_shift x u)
    | tlambda T t => tlambda T (term_shift x t)
    | tapp t T => tapp (term_shift x t) T
  end.

Fixpoint term_shift_typ (X: nat) (t : term) : term :=
  match t with
    | var y => var y
    | lambda T t => lambda (typ_shift X T) (term_shift_typ X t)
    | app t u => app (term_shift_typ X t) (term_shift_typ X u)
    | tlambda T t => tlambda (typ_shift X T) (term_shift_typ (X + 1) t)
    | tapp t T => tapp (term_shift_typ X t) (typ_shift X T)
  end.

Fixpoint subst_typ (X : nat) (T' : typ) (t : term) : term := 
  match t with
    | var y => var y
    | lambda T t => lambda (tsubst X T' T) (subst_typ X T' t)
    | app t u => app (subst_typ X T' t) (subst_typ X T' u)
    | tlambda T t => tlambda (tsubst X T' T) (subst_typ (X + 1) (typ_shift 0 T') t)
    | tapp t T => tapp (subst_typ X T' t) (tsubst X T' T)
end.

Fixpoint subst (x : nat) (t' : term) (t : term) : term :=
  match t with
  | var y =>
      match lt_eq_lt_dec y x with
      | inleft (left _)  => var y
      | inleft (right _) => t'
      | inright _        => var (y - 1)
      end
  | lambda T t  => lambda T (subst (x + 1) (term_shift 0 t') t)
  | app t u  => app (subst x t' t) (subst x t' u)
  | tlambda T t => tlambda T (subst x (term_shift_typ 0 t') t)
  | tapp t T => tapp (subst x t' t) T
  end.

Inductive env :=
  | empty : env
  | consTyp : typ -> env -> env
  | consKind : kind -> env -> env.

Fixpoint get_typ (x : nat) (e : env) : option typ :=
  match e with
    | empty => None
    | consKind _ e =>
        match x with
          | 0 => None
          | S n => get_typ n e
        end
    | consTyp T e => 
        match x with
          | 0 => Some T
          | S n => get_typ n e
        end
  end.

Fixpoint get_kind (X : nat) (e : env) : option kind :=
  match e with
    | empty => None
    | consTyp _ e =>
        match X with
          | 0 => None
          | S n => get_kind n e
        end
    | consKind kd e =>
        match X with
          | 0 => Some kd
          | S n => get_kind n e
        end
  end.