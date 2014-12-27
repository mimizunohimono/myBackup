(* CoreML.v *)
(* 2014/10/31 by Yukiyoshi Kameyama *)

Require Export SfLib.
Require Import Ascii String.
Require Import BinInt.
Require Import CoreMLDef.

(* The following notation is defined in CoreMLDef.v
Notation "t '\in' T"     := (typeOf t T).
Notation "Gamma '|-' tt" := (has_type Gamma tt).
*)

(* types *)
Notation int  := Tint.
Notation bool := Tbool.
Notation "T1 -> T2" := (Tarrow T1 T2) (at level 51, right associativity).
Notation "T1 * T2"  := (Tprod  T1 T2) (at level 40, left  associativity).

(* variables *)
Notation x := (TM_var (Id 0)).
Notation y := (TM_var (Id 1)).
Notation z := (TM_var (Id 2)).
Notation u := (TM_var (Id 3)).
Notation v := (TM_var (Id 4)).
Notation w := (TM_var (Id 5)).

(* terms *)
Notation "% t1" := (TM_int t1) (at level 50).
Notation _true := (TM_bool true).
Notation _false := (TM_bool false).
Notation "t1 + t2" := (TM_add t1 t2) (at level 50, left associativity).
Notation "t1 = t2" := (TM_eq  t1 t2) (at level 70).
Notation "t1 > t2" := (TM_gt  t1 t2) (at level 70).
Notation "( t1 , t2 )" := (TM_pair t1 t2) (at level 0).
Notation "'_left' t1 " := (TM_left t1) (at level 50).
Notation "'_right' t1 " := (TM_right t1) (at level 50).
Notation "'_lam' ( x ) t1" := (TM_lam x t1) (at level 60).
Notation "'_lambda' ( x ) t1" := (TM_lam x t1) (at level 60).
Notation "t1 @ t2" := (TM_app t1 t2) (at level 41, left associativity).
Notation "'_if' t1 'then' t2 'else' t3" := (TM_if t1 t2 t3) (at level 73).
Notation "'_let' x = t1 'in' t2" := (TM_let x t1 t2) (at level 72, x at level 0).
Notation "'_fix' f ( x ) t1" := (TM_fix f x t1) (at level 72, f at level 0, x at level 0, left associativity).

(* Typing rules
   Rvar     
   Rint
   Rbool    
   Rplus     
   Req      
   Rcomp
   Rpair     
   Rleft (B)       ... B is the type in A * B
   Rright (A)      ... A is the type in A * B
   Rlambda         
   Rlam            ... the same as Rlambda
   Rapply (A)      ... A is the type in A -> B
   Rapp (A)        ... the same as Rapply
   Rif       
   Rlet (A)        ... A is the type of let-bound term
   Rfix      
*)

(* terms
   % 10       ... integer 10  (for some reason, we need %)
   _true      ... boolean literan "true"  
   _false     ... boolean literan "false" 
   t1 + t2
   t1 = t2
   t1 > t2
   (t1,t2)
   _left t1   ... left t1  (you can write _left(t1) )
   _right t1  ... right t1
   _lambda (x) t1  ...   lambda x. t1
   _lam (x) t1     ...   lambda x. t1  
   t1 @ t2
   _if t1 then t2 else t3  ... if t1 then t2 else t3  (ONLY if needs _)
   _let x = t1 in t2   ...   let x = t1 in t2
   _fix x (y) t1       ...   fix x.y. t1
*)

Theorem e251 : 
  [] |- % 10 \in int.
Proof.
  Rint.
Qed.

Theorem e252 : 
  [] |- % -5 \in int.
Proof.
  Rint.
Qed.

Theorem e253 : 
  [] |- _true \in bool.
Proof.
  Rbool.
Qed.

Theorem e254 : 
  [] |- (% 10) + (% -3) \in int.
Proof.

  Rplus.
  Rint. Rint.
Qed.

Theorem e255 : 
  [] |- (% 10) + (% -5) = (% 3) \in bool.
Proof.
  Req.
  Rplus.
  Rint. Rint.
  Rint.
Qed.

Theorem e256 : 
  [] |- (% 10) > (% -5) + (% 3) \in bool.
Proof.
  Rcomp.
  Rint.
  Rplus.
  Rint. Rint.
Qed.

Theorem e257 : 
  [] |- _lam ( x ) (x + % 10) \in int -> int.
Proof.
  Rlambda.
  Rplus.
  Rvar. Rint.
Qed.


Theorem e258 : 
  [] |- (_if _true then (%1) else (%0)) \in int.
Proof.
  Rif.
  Rbool.
  Rint.
  Rint.
Qed.

Theorem e259 : 
  [x \in int -> int] |- (x , ( _if (% 100) = x @ (% 10) then x else x )) 
                     \in (int -> int) * (int -> int).
Proof.
  Rpair.
  Rvar.
  Rif.
  Req.
  Rint.
  Rapply(int). Rvar.
  Rint.
  Rvar. Rvar.
Qed.

Theorem e260 : 
  [] |- _lam (x) (_right x, _left x) \in (int * bool) -> (bool * int).
Proof.
  Rlambda.
  Rpair.
  Rright(int). Rvar.
  Rleft(bool). Rvar.
Qed.
  

Theorem e261 : 
  [] |- (_lam (z) (_lam (x) (z @ (z @ (z @ x))))) @ (_lam (y) (y + %3)) @ (%10) \in int.
Proof.
  Rapply(int).
  Rapply(int -> int).
  Rlambda.
  Rlambda.
  Rapply(int). Rvar.
  Rapply(int). Rvar.
  Rapply(int). Rvar.
  Rvar.
  Rlambda.
  Rplus. Rvar. Rint.
  Rint.
Qed.

Theorem e262 : 
  [] |- 
    _fix x ( y ) 
     ( _if y = (%0) then (%0) else y + (x @ (y + (% (-1))))) \in int -> int.
Proof.
  Rfix.
  Rif.
  Req. Rvar. Rint. Rint.  
  Rplus. Rvar.
  Rapply(int). Rvar.
  Rplus. Rvar. Rint.
Qed.

Theorem e263 : 
  [] |- 
    (_let x = (%10) + (%20) in
    _let y = (x > %3) in
    _let z = (x > %30) in
     ( _if y then x else 
       ( _if z then x + x else (%100))))
       \in int.
Proof.
  Rlet(int).
  Rplus. Rint. Rint.
  Rlet(bool).
  Rcomp. Rvar. Rint.
  Rlet(bool).
  Rcomp. Rvar. Rint.
  Rif. Rvar. Rvar.
  Rif. Rvar.
  Rplus. Rvar. Rvar.
  Rint.
Qed.

Theorem e264 : 
  [] |- 
    _let z = (_fix x ( y ) 
     ( _if y = (%0) then (%0) else y + (x @ (y + (% (-1)))))) in
        z @ (%10) \in int.
Proof.
  Rlet(int -> int).
  Rfix.
  Rif.
  Req. Rvar. Rint.
  Rint.
  Rplus. Rvar.
  Rapply(int). Rvar.
  Rplus. Rvar. Rint.
  Rapply(int). Rvar. Rint.
Qed.

Theorem e265 : 
  [] |- 
    (_fix z ( x ) 
       _if ((_left x) = %0) then _false 
       else _if ((_right x) = %0) then _true
       else z @ ((_left x) + (%-1), (_right x) + (%-1)))
    @ (%10, %3)
    \in bool.
Proof.
  Rapply(int*int).
  Rfix.
  Rif.
  Req. Rleft(int). Rvar. Rint.
  Rbool.
  Rif. Req. Rright(int). Rvar. Rint.
  Rbool.
  Rapply(int*int). Rvar.
  Rpair. 
  Rplus. Rleft(int). Rvar. Rint.
  Rplus. Rright(int). Rvar. Rint.
  Rpair. Rint. Rint.
Qed.

Inspect 50.
