(* CoreMLDef.v *)
(* 2014/10/31 by Yukiyoshi Kameyama *)

Require Export SfLib.
Require Import Ascii String.
Require Import BinInt.

Open Scope type_scope.

Inductive ty : Type :=
  | Tint   : ty
  | Tbool  : ty
  | Tvar   : id -> ty 
  | Tarrow : ty -> ty -> ty
  | Tprod  : ty -> ty -> ty
.

Inductive pty : Type :=
  | Tmono  : ty -> pty
  | Tall   : ty -> pty -> pty  (* Tall (Tvar id) pty *)
.

Inductive tm : Type :=
  | TM_var   : id -> tm 
  | TM_int   : Z -> tm
  | TM_bool  : bool -> tm
  | TM_add   : tm -> tm -> tm
  | TM_eq    : tm -> tm -> tm
  | TM_gt    : tm -> tm -> tm
  | TM_lam   : tm -> tm -> tm  
  | TM_app   : tm -> tm -> tm
  | TM_pair  : tm -> tm -> tm
  | TM_left  : tm -> tm
  | TM_right : tm -> tm
  | TM_if    : tm -> tm -> tm -> tm
  | TM_fix   : tm -> tm -> tm -> tm   (* fix f x -> t100 *)
  | TM_let   : tm -> tm -> tm -> tm   (* let x = t100 in t2 *)
.

(*
Eval compute in 3.
Eval compute in 3%Z.
Eval compute in (-3)%Z.
*)

Inductive valueT : Type :=
  | V_int    : Z -> valueT
  | V_bool   : bool -> valueT
  | V_pair   : valueT -> valueT -> valueT
  | V_closure : tm -> tm -> list (tm * valueT) -> valueT   (* lam x -> t in E *)
  | V_rclosure : tm -> tm -> tm -> list (tm * valueT) -> valueT   (* fix f x -> t in E *)
.

Definition envT := list (tm * valueT).

Inductive tytm := 
  | typeOf : tm -> ty -> tytm
.
Notation "t '\in' T" := (typeOf t T) (at level 80).

Fixpoint lookup (x : id) (Gamma : list tytm) : option ty :=
  match Gamma with
      | ((TM_var y) \in T) :: Gamma2 => if eq_id_dec x y then Some T
                                     else lookup x Gamma2
      | _  => None
  end
.
Definition extend Gamma t T := (t \in T) :: Gamma.

Reserved Notation "Gamma '|-' tt" (at level 90, t at level 40).

Inductive has_type : list tytm -> tytm -> Set :=
  | T_int    : forall n Gamma,
                 Gamma |- (TM_int n) \in Tint
  | T_bool   : forall b Gamma,
                 Gamma |- (TM_bool b) \in Tbool
  | T_var    : forall id1 ty1 Gamma,
                 (lookup id1 Gamma = Some ty1)
                  -> Gamma |- (TM_var id1) \in ty1
  | T_add    : forall t1 t2 Gamma, 
                 Gamma |- t1 \in Tint
               -> Gamma |- t2 \in Tint
               -> Gamma |- (TM_add t1 t2) \in Tint
  | T_eq    : forall t1 t2 Gamma, 
                 Gamma |- t1 \in Tint
               -> Gamma |- t2 \in Tint
               -> Gamma |- (TM_eq t1 t2) \in Tbool
  | T_gt    : forall t1 t2 Gamma, 
                 Gamma |- t1 \in Tint
               -> Gamma |- t2 \in Tint
               -> Gamma |- (TM_gt t1 t2) \in Tbool
  | T_lam    : forall x t ty1 ty2 Gamma, 
                 ((x \in ty1) :: Gamma) |- t \in ty2
                 -> Gamma |- (TM_lam x t) \in (Tarrow ty1 ty2)
  | T_app    : forall t1 t2 ty1 ty2 Gamma, 
                 Gamma |- t1 \in (Tarrow ty1 ty2) 
               -> Gamma |- t2 \in ty1
               -> Gamma |- (TM_app t1 t2) \in ty2
  | T_pair   : forall t1 t2 ty1 ty2 Gamma, 
               Gamma |- t1 \in ty1
               -> Gamma |- t2 \in ty2 
               -> Gamma |- (TM_pair t1 t2) \in (Tprod ty1 ty2)
  | T_left   : forall t ty1 ty2 Gamma, 
               Gamma |- t \in (Tprod ty1 ty2) 
               -> Gamma |- (TM_left t) \in ty1
  | T_right  : forall t ty1 ty2 Gamma, 
               Gamma |- t \in (Tprod ty1 ty2) 
               -> Gamma |- (TM_right t) \in ty2
  | T_if  : forall t1 t2 t3 ty1 Gamma, 
                Gamma |- t1 \in Tbool
               -> Gamma |- t2 \in ty1
               -> Gamma |- t3 \in ty1
               -> Gamma |- (TM_if t1 t2 t3) \in ty1
  | T_fix  : forall f x t ty1 ty2 Gamma, 
               ((f \in Tarrow ty1 ty2) :: (x \in ty1) :: Gamma) |- t \in ty2
               -> Gamma |- (TM_fix f x t) \in Tarrow ty1 ty2
  | T_let  : forall t1 t2 x ty1 ty2 Gamma, 
               Gamma |- t1 \in ty1
               -> (x \in ty1) :: Gamma |- t2 \in ty2
               -> Gamma |- (TM_let x t1 t2) \in ty2
where "Gamma '|-' tt" := (has_type Gamma tt).

Ltac Rint      := apply T_int.
Ltac Rbool     := apply T_bool.
Ltac Rvar      := apply T_var; reflexivity.
Ltac Radd      := apply T_add.
Ltac Rplus     := apply T_add.   (* alias for rule name *)
Ltac Req       := apply T_eq.
Ltac Rgt       := apply T_gt.
Ltac Rcomp     := apply T_gt.    (* alias for rule name *)
Ltac Rlam      := apply T_lam.
Ltac Rlambda   := apply T_lam.
Ltac Rapply T1 := apply (T_app _ _ T1 _ _).
Ltac Rapp   T1 := apply (T_app _ _ T1 _ _).
Ltac Rpair     := apply T_pair.
Ltac Rleft T2  := apply (T_left _ _ T2 _).
Ltac Rright T1 := apply (T_right _ T1 _ _).
Ltac Rif       := apply T_if.
Ltac Rfix      := apply T_fix.
Ltac Rlet T1   := apply (T_let _ _ _ T1).

