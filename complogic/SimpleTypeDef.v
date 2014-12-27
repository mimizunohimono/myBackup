(* SipmleTypeDef.v *)
(* Simply typed lambda calculus with products and sums; definitions *)
(* 2014/10/22 by Yukiyoshi Kameyama *)

Require Export SfLib.
Require Import Ascii String.

Open Scope type_scope.

(* the following type is defined in SfLib.v 
Inductive id : Type := 
  Id : nat -> id.
Theorem eq_id_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
*)

Inductive ty : Type :=
  | Empty : ty 
  | Tvar  : id -> ty 
  | Arrow : ty -> ty -> ty
  | Prod  : ty -> ty -> ty
  | Sum   : ty -> ty -> ty
.

Inductive tm : Type :=
  | var    : id -> tm 
  | lam    : tm -> ty -> tm -> tm  
  | app    : tm -> tm -> tm
  | pair   : tm -> tm -> tm
  | left   : tm -> tm
  | right  : tm -> tm
  | inl    : tm -> tm
  | inr    : tm -> tm
  | case   : tm -> tm -> ty -> tm -> tm -> ty -> tm -> tm
  | abort  : tm -> tm
.

Inductive tytm := 
  | typeOf : tm -> ty -> tytm
.
Notation "t '\in' T" := (typeOf t T) (at level 80).

(*
The following definition is inlined, to make the theorems readable. 
Definition extend Gamma t T := (t \in T) :: Gamma.
*)

Fixpoint lookup (x : id) (Gamma : list tytm) : option ty :=
  match Gamma with
      | ((var y) \in T) :: Gamma2 => if eq_id_dec x y then Some T
                                     else lookup x Gamma2
      | _  => None
  end
.

Reserved Notation "Gamma '|-' tt" (at level 90, t at level 40).

Inductive has_type : list tytm -> tytm -> Prop :=
  | T_var    : forall x T1 Gamma, 
                 (lookup x Gamma = Some T1) 
                 -> Gamma |- (var x) \in T1
  | T_lam    : forall x t T1 T2 Gamma, 
                 (((var x) \in T1) :: Gamma) |- t \in T2
                 -> Gamma |- (lam (var x) T1 t) \in (Arrow T1 T2)
  | T_app    : forall t1 t2 T1 T2 Gamma, 
                 Gamma |- t1 \in (Arrow T1 T2) 
               -> Gamma |- t2 \in T1
               -> Gamma |- (app t1 t2) \in T2
  | T_pair   : forall t1 t2 T1 T2 Gamma, 
               Gamma |- t1 \in T1 
               -> Gamma |- t2 \in T2 
               -> Gamma |- (pair t1 t2) \in (Prod T1 T2)
  | T_left   : forall t T1 T2 Gamma, 
               Gamma |- t \in (Prod T1 T2) -> Gamma |- (left t) \in  T1
  | T_right  : forall t T1 T2 Gamma, 
               Gamma |- t \in (Prod T1 T2) -> Gamma |- (right t) \in T2
  | T_inl    : forall t T1 T2 Gamma, 
               Gamma |- t \in T1 -> Gamma |- (inl t) \in (Sum T1 T2)
  | T_inr    : forall t T1 T2 Gamma, 
               Gamma |- t \in T2 -> Gamma |- (inr t) \in (Sum T1 T2)
  | T_case   : forall x y t0 t1 t2 T1 T2 T3 Gamma, 
               Gamma |- t0 \in (Sum T1 T2) 
               -> (((var x) \in T1) :: Gamma) |- t1 \in T3
               -> (((var y) \in T2) :: Gamma) |- t2 \in T3 
               -> Gamma |- (case t0 (var x) T1 t1 (var y) T2 t2) \in T3
  | T_abort  : forall t T Gamma, 
               Gamma |- t \in Empty -> Gamma |- (abort t) \in T
where "Gamma '|-' tt" := (has_type Gamma tt).

Ltac Rvar      := apply T_var; reflexivity.
Ltac rvar      := apply T_var; reflexivity.
Ltac Rlambda   := apply T_lam.
Ltac rlambda   := apply T_lam.
Ltac Rlam      := apply T_lam.
Ltac rlam      := apply T_lam.
Ltac Rapply T1 := apply (T_app _ _ T1 _ _).
Ltac rapply T1 := apply (T_app _ _ T1 _ _).
Ltac Rapp   T1 := apply (T_app _ _ T1 _ _).
Ltac rapp   T1 := apply (T_app _ _ T1 _ _).
Ltac Rpair     := apply T_pair.
Ltac rpair     := apply T_pair.
Ltac Rleft  T2 := apply (T_left _ _ T2 _).
Ltac rleft  T2 := apply (T_left _ _ T2 _).
Ltac Rright T1 := apply (T_right _ T1 _ _).
Ltac rright T1 := apply (T_right _ T1 _ _).
Ltac Rinl      := apply T_inl.
Ltac rinl      := apply T_inl.
Ltac Rinr      := apply T_inr.
Ltac rinr      := apply T_inr.
Ltac Rcase     := apply T_case.
Ltac rcase     := apply T_case.
Ltac Rabort    := apply T_abort.
Ltac rabort    := apply T_abort.

Notation T := (Tvar (Id 0)).
Notation S := (Tvar (Id 1)).
Notation U := (Tvar (Id 2)).
Notation V := (Tvar (Id 3)).
Notation W := (Tvar (Id 4)).
Notation X := (Tvar (Id 5)).
Notation Y := (Tvar (Id 6)).
Notation Z := (Tvar (Id 7)).

Notation a := (var (Id 101)).
Notation b := (var (Id 102)).
Notation c := (var (Id 103)).
Notation d := (var (Id 104)).
Notation e := (var (Id 105)).
Notation f := (var (Id 106)).
Notation g := (var (Id 107)).
Notation h := (var (Id 108)).
Notation i := (var (Id 109)).
Notation j := (var (Id 110)).
Notation k := (var (Id 111)).
Notation l := (var (Id 112)).
Notation m := (var (Id 113)).
Notation n := (var (Id 114)).
Notation o := (var (Id 115)).
Notation p := (var (Id 116)).
Notation q := (var (Id 117)).
Notation r := (var (Id 118)).
Notation s := (var (Id 119)).
Notation t := (var (Id 128)).
Notation u := (var (Id 121)).
Notation v := (var (Id 122)).
Notation w := (var (Id 123)).
Notation x := (var (Id 124)).
Notation y := (var (Id 125)).
Notation z := (var (Id 126)).

Inductive ex (X : Type) (P : X -> Prop) : Prop :=
  ex_intro : forall (witness : X), P witness -> ex X P.

Close Scope type_scope.

Notation "T1 -> T2" := (Arrow T1 T2) (at level 51, right associativity).
Notation "T1 + T2"  := (Sum T1 T2) (at level 50, left associativity).
Notation "T1 * T2"  := (Prod T1 T2) (at level 40, left associativity).

Notation "'\lambda' ( x \in T1 ) t1" := (lam x T1 t1) (at level 40, x at level 0).
Notation "t1 @ t2" := (app t1 t2) (at level 40, left associativity).
Notation "( t , s )" := (pair t s) (at level 0).
Notation "'case' ( t0 , ( x \in T1 ) t1 , ( y \in T2 ) t2 )"
           := (case t0 x T1 t1 y T2 t2) (at level 0, x at level 0, y at level 0).

Notation "'exists_term' t , P" := (ex tm (fun t => P)) (at level 100, t at level 100).
Ltac Ex t := (apply ex_intro with (witness:=t)).

(* Print Grammar constr. *)
(* Print Scopes. *)

