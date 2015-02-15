Require Import Arith.
Require Import Bool.
Require Import Max.
Require Import NPeano.
Require Import Omega.

(** 1.2.1 Types and substitutions *)
Inductive kind := consk : nat -> kind.

Inductive typ :=
  | typ_var : nat -> typ
  | typ_arrow : typ -> typ -> typ
  | typ_all : kind -> typ -> typ.

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
    | typ_all k T => typ_all k (typ_shift (X + 1) T)
  end.

Fixpoint tsubst (X : nat) (T2 : typ) (T : typ) : typ := 
  match T with
    | typ_var Y => match lt_eq_lt_dec X Y with
                     | inleft (left _) => typ_var (Y -1)
                     | inleft (right _) => T2
                     | inright _ => typ_var Y
                   end
    | typ_arrow T U => typ_arrow (tsubst X T2 T) (tsubst X T2 U)
    | typ_all k T => typ_all k (tsubst (X + 1) (typ_shift 0 T2) T)
  end.

(** 1.2.2 Terms and substitutions *)

Inductive term :=
  | var : nat -> term
  | lambda : typ -> term -> term
  | app : term -> term -> term
  | tlambda : kind -> term -> term
  | tapp : term -> typ -> term.

Fixpoint term_shift (x : nat) (t : term) : term :=
  match t with
    | var y => if le_gt_dec x y then
                 var (y + 1)
               else
                 var y
    | lambda T t => lambda T (term_shift (x + 1) t)
    | app t u => app (term_shift x t) (term_shift x u)
    | tlambda k t => tlambda k (term_shift x t)
    | tapp t T => tapp (term_shift x t) T
  end.

Fixpoint term_shift_typ (X: nat) (t : term) : term :=
  match t with
    | var y => var y
    | lambda T t => lambda (typ_shift X T) (term_shift_typ X t)
    | app t u => app (term_shift_typ X t) (term_shift_typ X u)
    | tlambda k t => tlambda k (term_shift_typ (X + 1) t)
    | tapp t T => tapp (term_shift_typ X t) (typ_shift X T)
  end.

Fixpoint subst_typ (X : nat) (T' : typ) (t : term) : term := 
  match t with
    | var y => var y
    | lambda T t => lambda (tsubst X T' T) (subst_typ X T' t)
    | app t u => app (subst_typ X T' t) (subst_typ X T' u)
    | tlambda k t => tlambda k (subst_typ (X + 1) (typ_shift 0 T') t)
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

(** 1.2.3 ENvironments and accessors *)

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




(** 1.2.4a Well-formedness *)
Fixpoint wf_typ ( e : env) (T : typ) : Prop :=
  match T with
    | typ_var X => get_kind X e = None -> False
    | typ_arrow T U => wf_typ e T /\ wf_typ e U
    | typ_all k T =>  wf_typ (consKind k e) T
  end.

Fixpoint wf_env (e : env) : Prop :=
  match e with
    | empty => True
    | consTyp T e => wf_typ e T /\ wf_env e
    | consKind k e => wf_env e
  end.

Fixpoint wf_typ_bool ( e : env) (T : typ) : bool :=
  match T with
    | typ_var X =>match get_kind X e with
                    |None => false
                    |_ => true
                  end
    | typ_arrow T U => wf_typ_bool e T && wf_typ_bool e U
    | typ_all k T =>  wf_typ_bool (consKind k e) T
  end.
Fixpoint wf_env_bool (e : env) : bool :=
  match e with
    | empty => true
    | consTyp T e => wf_typ_bool e T && wf_env_bool e
    | consKind k e => wf_env_bool e
  end.

(** 1.2.4b Kinding *)
(* Definition max (n p : nat) := if le_lt_dec n p then p else n. *)

Inductive kinding : env -> typ -> kind -> Prop :=
| K_var :
  forall (e : env) (X : nat) (k l : nat),
    wf_env e -> get_kind X e = Some (consk k) -> k <= l -> kinding e (typ_var X) (consk l)
| K_arrow :
  forall (e : env) (T1 T2 : typ) (k1 k2 : nat),
    kinding e T1 (consk k1) -> kinding e T2 (consk k2)
    -> kinding e (typ_arrow T1 T2) (consk (max k1 k2))
| K_all :
  forall (e : env) (X T : typ) (k1 k2 : nat),
    kinding (consKind (consk k1) e) T (consk k2) -> kinding e (typ_all (consk k1) T) (consk (S (max k1 k2)))
.

Inductive typing : env -> term -> typ -> Prop :=
| T_var : 
  forall (e : env) (x : nat) (T : typ),
    wf_env e -> get_typ x e = Some T -> typing e (var x) T
| T_lambda :
  forall (e : env) (t : term) (T1 T2 : typ),
    typing (consTyp T1 e) t T2 -> typing e (lambda T1 t) (typ_arrow T1 T2)
| T_app :
  forall (e : env) (t1 t2 : term) (T1 T2 : typ),
    typing e t1 (typ_arrow T1 T2) -> typing e t2 T1 -> typing e (app t1 t2) T2
| T_tlambda : 
  forall (e : env) (k : kind) (t : term) (T : typ),
    typing (consKind k e) t T -> typing e (tlambda k t) (typ_all k T)
| T_tapp :
  forall (e : env) (k :kind) (t : term) (T1 T2 : typ),
    typing e t (typ_all k T1) -> kinding e T2 k 
    -> typing e (tapp t T2) (tsubst 0 T2 T1) (* !! *)
.

(** 1.2.5 *)
Lemma eq_kind : forall (k1 k2 : kind), {k1 = k2} + {k1 <> k2}.
Proof.
  intros k1 k2.
  destruct k1, k2.
  decide equality.
  apply eq_nat_dec.
Qed.

Lemma eq_typ : forall (T1 T2 : typ), {T1 = T2} + {T1 <> T2}.
Proof.
  decide equality; decide equality.
  apply eq_nat_dec.
Qed.

(** 1.2.5a Kind inference *)
Fixpoint kindIt (e  : env) (T : typ) : option kind :=
  match T with
      typ_var X => get_kind X e
    | typ_arrow T U => match kindIt e T, kindIt e U with
                         | None, _ | _, None => None
                         | Some (consk k1), Some (consk k2) => Some (consk (max k1 k2))
                       end
    | typ_all (consk k) T => match kindIt (consKind (consk k) e) T with
                               | None => None
                               | Some (consk k2) => Some (consk ( S(max k k2)))
                             end
end.

Fixpoint typIt (e : env) (t : term) : option typ :=
  match t with
    | var x => get_typ x e
    | lambda T t => match typIt (consTyp T e) t with
                      | None => None
                      | Some T2 => Some (typ_arrow T T2)
                    end
    | app t u => match typIt e t, typIt e u with
                     | Some (typ_arrow T1 U), Some T2 => if eq_typ T1 T2 then 
                                               Some U
                                             else None
                     | _, _ => None
                 end
    | tlambda k t => match typIt (consKind k e) t with
                       | None => None
                       | Some T => Some (typ_all k T)
                     end
    | tapp t T => match typIt e t, kindIt e T with
                    | Some (typ_all k1 T1), Some k2 => if eq_kind k1 k2 then
                                                         Some (tsubst 0 T T1)
                                                       else None
                    | _, _ => None
                  end
  end.


Lemma ok_kinding : forall (T : typ) (e : env) (k : nat),
                     wf_env e -> kindIt e T = Some (consk k) -> kinding e T (consk k).
Proof.
induction T; intros e k0 H H2.
+ simpl in H2.
  now apply K_var with k0.
+ simpl in H2.
  remember (kindIt e T1) as opt1; destruct opt1.
  - remember (kindIt e T2) as opt2; destruct opt2.
    *  destruct k, k1.
       inversion H2.
       apply K_arrow.
       now apply IHT1. 
       now apply IHT2. 
    * destruct k.
      discriminate H2.
  - discriminate H2.

+ simpl in H2.
  destruct k. remember (kindIt (consKind (consk n) e) T) as opt. destruct opt. destruct k.
  inversion H2.
  apply K_all.
  - trivial.
  - apply IHT.
    * symmetry in Heqopt.
      now simpl.
    * now rewrite Heqopt.

  - discriminate H2.
Qed.

Lemma ok_typing : forall (t : term) (e : env) (T : typ),
                   wf_env e -> typIt e t = Some T -> typing e t T.
Proof.
induction t; intros e T HE H; simpl in H.
+ apply T_var; assumption.

+ remember (typIt (consTyp t e) t0) as opt.
  destruct opt.
  - inversion H.
    apply T_lambda.
    apply IHt.
    * admit.
    *  now symmetry.

  - discriminate H.

+ remember (typIt e t1) as opt.
  destruct opt.
  * destruct t.
    - discriminate H.
    - remember (typIt e t2) as opt2; destruct opt2.
      remember (eq_typ t3 t) as opt3; destruct opt3.
      inversion H. subst.
            apply T_app with t.
            apply IHt1. assumption.
            now symmetry.
            apply IHt2. assumption.
            now symmetry.
            discriminate H.

          discriminate H.
    - discriminate H.
  * discriminate H.

+ remember (typIt (consKind k e) t) as opt1; destruct opt1.
  * inversion H.  
    apply T_tlambda.
    apply IHt.
    - assumption.
    - now symmetry.
  * discriminate H.

+ remember (typIt e t) as opt; destruct opt.
  - destruct t1.
    * discriminate H.
    * discriminate H.
    * remember (kindIt e t0) as opt2; destruct opt2.
      remember (eq_kind k k0) as opt3; destruct opt3.
        inversion H.
        apply T_tapp with k.
        apply IHt. assumption.
        now symmetry.
          
        destruct k. apply ok_kinding. assumption.
        rewrite e0. now symmetry.

        discriminate H.
      
      discriminate H.
-  discriminate H.
Qed.

Lemma cumulativity : forall (T : typ) (e : env) (k1 k2 : nat), kinding e T (consk k1) -> k1 <= k2 -> kinding e T (consk k2).
Proof.
induction T.
- intros k1 k2 H H0 H1.
  inversion H0.
  eapply K_var.
  + assumption.  
  + eassumption. 
  + omega.
- intros e k1 k2 H H0.
  inversion H; subst.
  replace k2 with (max k2 k2).
  + apply K_arrow.
    * apply IHT1 with k0.
      assumption.
      apply max_lub_l in H0.
      assumption.
    * apply IHT2 with k3.
      assumption.
      apply max_lub_r in H0.
      assumption.
  +  now apply max_idempotent.


- intros e k1 k2 H H0.
  inversion H; subst.
  destruct k2.
  + now inversion H0.
  + apply le_S_n in H0.
    replace k2 with (max k0 k2).
    * apply K_all.
      now trivial.
      apply (IHT _ k3 k2).
      assumption.
      apply max_lub_r in H0.
      assumption.
    * apply max_lub_l in H0.
      apply max_l in H0.
      replace (max k0 k2) with (max k2 k0).
      assumption.
      now apply max_comm.
Qed.

(** 1.3.1.1 insert_kind : nat -> env -> env -> Prop *)
Inductive insert_kind : nat -> env -> env -> Prop :=
  Now : forall (k : kind) (e : env), insert_kind 0 e (consKind k e)
| AfterTyp : forall (X : nat) (k : kind) (e e' : env) (T : typ),
                insert_kind (S X) (consTyp T e) (consTyp (typ_shift X T) e')
| AfterKind : forall (X : nat) (k :kind) (e e' : env),
                 insert_kind (S X) (consKind k e) (consKind k e').

(** 1.3.1.2 Invariants *)
Lemma typ_subst_wf_type : forall (X : nat) (T : typ) (e e' : env),
          wf_typ e T -> wf_env e -> insert_kind X e e' -> wf_typ e' (typ_shift X T).
Proof.
  intros X T e e' H H0 H1.
  induction H1.
  - destruct T.
    + simpl. intros H1.
 Qed.



Lemma insert_kind_wf_env : forall (X : nat) (e e' : env),
                             wf_env e -> insert_kind X e e' -> wf_env e'.
Proof.
  intros X e e' H H0.
  induction e.
  - destruct H0.
    + now simpl.
    + simpl. split.
      * simpl in H. case H.
        apply typ_subst_wf_type.