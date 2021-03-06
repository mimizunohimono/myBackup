(* SimpleType.v *)
(* Simply typed lambda calculus; theorems *)
(* 2014/10/22 by Yukiyoshi Kameyama *)

Require Export SfLib.
Require Import Ascii String.
Require Import SimpleTypeDef.

Theorem ex101 : [x \in T] |- x \in T.
Proof.
  Rvar.
Qed.

Theorem ex102 : [x \in T; y \in S] |- x \in T.
Proof.
  Rvar.
Qed.

Theorem ex103 : [x \in T; y \in S] |-  (x,y)   \in T * S.
Proof.
  Rpair.
  Rvar.
  Rvar.
Qed.

Theorem ex104 : [x \in T * S] |- left x \in T.
Proof.
  Rleft (S).
  Rvar.
Qed.

Theorem ex105 : [x \in T] |- (x,x) \in T * T.
Proof.
  Rpair.
  Rvar.
  Rvar.
Qed.

Theorem ex106 : [x \in T * S] |- (left x, (right x, left x)) \in T * (S * T).
Proof.
  Rpair.
    Rleft (S); Rvar.
    Rpair. Rright (T); Rvar.
          Rleft (S); Rvar.
Qed.

Theorem ex107 : [x \in (T * S) * U] |- (left (left x), (right (left x),right x)) \in T * (S * U).
Proof.
  Rpair.
    Rleft (S). Rleft (U). Rvar.
    Rpair.
      Rright (T). Rleft (U). Rvar.
      Rright (T * S). Rvar.
Qed.

Theorem ex108 : [x \in T * (S * U)] 
|- ((left x, left (right x)), right (right x)) \in (T * S) * U.
Proof.
  Rpair.
  Rpair. Rleft (S * U). Rvar.
  Rleft(U). Rright(T). Rvar.
  Rright(S). Rright(T). Rvar.
Qed.

Theorem ex109 : [] |- \lambda (x \in T) x \in T -> T.
Proof.
  Rlambda.
  Rvar.
Qed.

Theorem ex110 : [] |- \lambda (x \in T) (\lambda (y \in T) x) \in T -> T -> T.
Proof.
  Rlambda.
  Rlambda.
  Rvar.
Qed.

Theorem ex111 : [] |- \lambda (x \in T) (\lambda (y \in S) x) \in T -> S -> T.
  Rlambda.
  Rlambda.  
  Rvar.
Qed.

Theorem ex112 : [] |- \lambda (f \in T -> T -> S) (\lambda (x \in T) 
((f @ x) @ x)) \in (T -> T -> S) -> (T -> S).
Proof.
  Rlambda.
  Rlambda.
  Rapply(T).
  Rapply(T).
  Rvar. Rvar. Rvar.
Qed.

Theorem ex113 : [] |- 
  \lambda (f \in T -> S -> U) (
     \lambda (g \in T -> S) (
        \lambda (x \in T) (
          ((f @ x) @ (g @ x))
   )))
  \in
   (T -> S -> U) -> (T -> S) -> (T -> U).
Proof.
  Rlambda.
  Rlambda.
  Rlambda.
  Rapply(S).
  Rapply(T).
  Rvar.  Rvar.
  Rapply(T).
  Rvar. Rvar.
Qed.

Theorem ex114 : [] |- \lambda (x \in T * S) ( right x, left x) \in T * S -> S * T.
Proof.
  Rlambda.
  Rpair.
  Rright(T). Rvar.
  Rleft(S). Rvar.
Qed.

Theorem ex115 : [] |- \lambda (x \in T) (\lambda (f \in T -> S) (f @ x))
                \in T -> (T -> S) -> S.
Proof.
  Rlambda.
  Rlambda.
  Rapply(T). Rvar.
  Rvar.
Qed.
  
Theorem ex116 : [] |- \lambda (x \in T) (inl x) \in T -> T + S.
Proof.
  Rlambda.
  Rinl.
  Rvar.
Qed.

Theorem ex117 : [] |- \lambda (x \in T) (inr x) \in T -> S + T.
Proof.
  Rlambda.
  Rinr.
  Rvar.
Qed.

Theorem ex118 : [] |- \lambda (x \in T + T) 
                      (case (x, (y \in T) y, (z \in T) z)) 
                   \in T + T -> T.
Proof.
  Rlambda.
  Rcase.
  Rvar.
  Rvar.
  Rvar.
Qed.

Theorem ex120 : [] |- \lambda (x \in T + (S + U)) 
                         (case(x, (y \in T) inl (inl y),
                                  (z \in S + U) 
                                    (case(z, (u \in S) inl (inr u),
                                             (v \in U) inr(v)))))
                         \in (T + (S + U)) -> ((T + S) + U).
Proof.
  Rlambda.
  Rcase.
  Rvar.
  Rinl. Rinl. Rvar.
  Rcase.
  Rvar.
  Rinl. Rinr. Rvar.
  Rinr. Rvar.
Qed.

Theorem ex121 : [] |- \lambda (x \in T * (S + U)) (
                        case(right x,
                             (y \in S) inl (left x, y),
                             (z \in U) inr (left x, z)))
                  \in (T * (S + U)) -> ((T * S) + (T * U)).
Proof.
  Rlambda.
  Rcase.
  Rright(T). Rvar.
  Rinl. Rpair.
  Rleft(S + U). Rvar. Rvar.
  Rinr. Rpair.
  Rleft(S + U). Rvar. Rvar.
Qed.

Theorem ex122 : [] |-  (\lambda (x \in ((T * S) + (T * U))) 
                          (case (x, (y \in T * S) (left y, inl (right y)),
                                    (z \in T * U) (left z, inr (right z)))))
                       \in ((T * S) + (T * U)) -> (T * (S + U)).
Proof.
  Rlambda.
  Rcase. Rvar.
  Rpair. 
  Rleft(S). Rvar.
  Rinl. Rright(T). Rvar.
  Rpair.
  Rleft(U). Rvar.
  Rinr. Rright(T). Rvar.
Qed.

Theorem ex123 : [] |- \lambda (x \in (T + (S * U))) 
                         (case (x, (y \in T) (inl(y), inl(y)),
                                   (z \in S * U) (inr(left(z)), inr(right(z)))))
                      \in (T + (S * U)) -> ((T + S) * (T + U)).
Proof.
   Rlambda.
   Rcase.  Rvar.
   Rpair.
   Rinl. Rvar.
   Rinl. Rvar.
   Rpair.
   Rinr. Rleft(U). Rvar.
   Rinr. Rright(S). Rvar.
Qed.

Theorem ex124 : [] |- \lambda (x \in (T+S) * (T+U))
                        (case(left(x), (y \in T) inl(y),
                                       (z \in S) 
                                         (case (right(x),
                                                 (u \in T) inl(u),
                                                 (v \in U) inr(z, v)))))
                      \in ((T + S) * (T + U)) -> (T + (S * U)).
Proof.
  Rlambda.
  Rcase.
  Rleft(T + U). Rvar.
  Rinl. Rvar.
  Rcase.
  Rright(T + S). Rvar.
  Rinl. Rvar.
  Rinr. Rpair. Rvar. Rvar.
Qed.

Theorem ex127 : [] |- \lambda (x \in T * (T -> Empty))
                        (abort ( (right x) @ (left x)))
                      \in T * (T -> Empty) -> S.
Proof.
  Rlambda.
  Rabort.
  Rapply(T).
  Rright(T). Rvar.
  Rleft(T -> Empty). Rvar.
Qed.

Theorem ex128 : [] |- \lambda (x \in T)
                        (\lambda (f \in T -> U)
                           (f @ x))
                       \in T -> ((T -> U) -> U).
Proof.
  Rlambda.
  Rlambda.
  Rapply(T). Rvar.
  Rvar.
Qed.

Theorem ex129 : [] |- \lambda (f \in T -> S)
                         (\lambda (g \in S -> U)
                             (\lambda (x \in T)
                                  (g @ (f @ x))))
                      \in (T -> S) -> ((S -> U) -> (T -> U)).
Proof.
  Rlambda.
  Rlambda.
  Rlambda.
  Rapply(S). Rvar.
  Rapply(T). Rvar.
  Rvar.
Qed.

Theorem ex130 : [] |- \lambda (f \in ((T -> Empty) -> Empty) -> Empty)
                         (\lambda (x \in T)
                             (f @ (\lambda (g \in T -> Empty) 
                                     (g @ x))))
                      \in (((T -> Empty) -> Empty) -> Empty) -> (T -> Empty).
Proof.
  Rlambda.
  Rlambda.
  Rapply((T -> Empty) -> Empty). Rvar.
  Rlambda.
  Rapply(T). Rvar.
  Rvar.
Qed.

Theorem ex133 : exists_term t, [] |- t \in T -> T.
Proof.
  Ex (\lambda (x \in T) x).
  Rlambda. Rvar.
Qed.

Theorem ex136 : exists_term t, [] |- t \in  T * Empty -> S * T.
Proof.
  Ex(\lambda(x \in T * Empty) (abort(right(x)), abort(right(x)))).
  Rlambda.
  Rpair.
  Rabort.
  Rright(T). Rvar.
  Rabort.
  Rright(T). Rvar.
Qed.

Theorem ex137 : exists_term t, [] |- t \in  (T -> S) -> (((T -> Empty) + S) -> Empty) -> Empty.
Proof.
  Ex(\lambda(f \in T -> S) (\lambda(g \in (T -> Empty) + S -> Empty) (g@inl(\lambda(t \in T)(g@(inr(f@t))))))).
  Rlambda.
  Rlambda.
  Rapply((T -> Empty) + S).
  Rvar.
  Rinl.
  Rlambda.
  Rapply((T -> Empty) + S).
  Rvar.
  Rinr.
  Rapply(T). Rvar. Rvar.
Qed.


(*case(x@x, (x \in T -> Empty)x, (x \in S)x) @ x*)

Theorem ex138 : exists_term t, [] |- t \in  ((T -> Empty) + S) -> T -> S.
Proof.
  Ex(\lambda (f \in  ((T -> Empty) + S)) (\lambda (g \in T) (case(f, (x \in T -> Empty)abort(x@g), (x \in S)x)))).
  Rlambda.
  Rlambda.
  Rcase.
  Rvar.
  Rabort.
  Rapply(T).
  Rvar. Rvar. Rvar.
Qed.

Theorem ex139 : exists_term t, [] |- t \in  (T -> S -> U) -> (T * S -> U).
Proof.
  Ex(\lambda (f \in T -> S -> U)(\lambda (g \in T*S) (f@(left(g))@(right(g))))).
  Rlambda.
  Rlambda.
  Rapply(S).
  Rapply(T). Rvar.
  Rleft(S). Rvar.
  Rright(T). Rvar.
Qed.

Theorem ex140 : exists_term t, [] |- t \in  (T * S -> U) -> (T -> S -> U).
Proof.
  Ex(\lambda(f \in T * S -> U)(\lambda(t \in T)(\lambda(s \in S)(f@(t, s))))).
  Rlambda.
  Rlambda.
  Rlambda.
  Rapply(T*S).
  Rvar.
  Rpair.
  Rvar. Rvar.
Qed.  

Theorem ex141 : exists_term t, [] |- t \in  (T + S -> U) -> (T -> U) * (S -> U).
Proof.
  Ex(\lambda(f \in T + S -> U)(\lambda(t \in T)(f@inl(t)),  \lambda(s \in S)(f@inr(s)))).
  Rlambda.
  Rpair.
  Rlambda.
  Rapply(T+S). Rvar.
  Rinl. Rvar.
  Rlambda.
  Rapply(T+S).
  Rvar.
  Rinr. Rvar. 
Qed.


Theorem ex142 : exists_term t, [] |- t \in  (T -> U) * (S -> U) -> (T + S -> U).
Proof.
  Ex(\lambda(f \in (T -> U) * (S -> U))(\lambda(g \in T + S)(case(g, (t \in T)((left(f))@t), (s \in S)((right(f))@s))))).
  Rlambda.
  Rlambda.
  Rcase. Rvar.
  Rapply(T). 
  Rleft(S -> U).
  Rvar. Rvar.
  Rapply(S).
  Rright(T -> U).
  Rvar. Rvar.
Qed.

Theorem ex143 : exists_term t, [] |- t \in  (T -> S) -> (S -> U) -> (U -> S) -> (T -> S).
Proof.
  Ex(\lambda(f \in T -> S)(\lambda(g \in S -> U)(\lambda(h \in U -> S)f))).
  Rlambda.
  Rlambda.
  Rlambda.
  Rvar.
Qed.

Theorem ex144 : exists_term t, [] |- t \in  (T + S) -> (T -> U) -> (S -> U) -> U.
Proof.
  Ex(\lambda(f \in T + S)(\lambda(g \in T -> U)(\lambda(h \in S -> U)(case(f, (t \in T)(g@t), (s \in S)(h@s)))))).
  Rlambda.
  Rlambda.
  Rlambda.
  Rcase.
  Rvar.
  Rapply(T).
  Rvar. Rvar.
  Rapply(S).
  Rvar. Rvar.
Qed.

Theorem ex145 : exists_term t, [] |- t \in  ((T + (T -> Empty)) -> Empty) -> Empty.
Proof.
  Ex(\lambda(f \in (T + (T -> Empty)) -> Empty)(f@(inr( \lambda(t \in T)(f@inl(t)) )))).
  Rlambda.
  Rapply(T + (T -> Empty)). 
  Rvar.
  Rinr.
  Rlambda.
  Rapply(T + (T -> Empty)). Rvar.
  Rinl. Rvar.
Qed.

Theorem ex146 : exists_term t, [] |- t \in ((((T -> Empty) -> Empty) -> T) -> Empty) -> Empty.
Proof.
  Ex(\lambda(f \in ((((T -> Empty) -> Empty) -> T) -> Empty))( f@( \lambda(g \in ((T -> Empty) -> Empty))(abort(g@(\lambda(t \in T)(f@(\lambda(g \in ((T -> Empty) -> Empty))t)))))))).
  Rlambda.
  Rapply((((T -> Empty) -> Empty) -> T)). Rvar.
  Rlambda.
  Rabort.
  Rapply(T -> Empty). Rvar.
  Rlambda.
  Rapply((((T -> Empty) -> Empty) -> T)). Rvar.
  Rlambda. Rvar.
Qed.  

Theorem ex147 : exists_term t, [] |- t \in ((((T -> S) -> T) -> T) -> Empty) -> Empty.
Proof.
  Ex(\lambda(f \in ((((T -> S) -> T) -> T) -> Empty))(f@( \lambda(g \in (T -> S) -> T)(g@(\lambda(t \in T)(abort(f@(\lambda(g \in ((T -> S) -> T))t))) ) ) ) ) ).
  Rlambda.
  Rapply(((T -> S) -> T) -> T). Rvar.
  Rlambda.
  Rapply(T -> S). Rvar.
  Rlambda.
  Rabort.
  Rapply(((T -> S) -> T) -> T). Rvar.
  Rlambda. Rvar.
Qed.  

Theorem ex148 : exists_term t, [] |- t \in ((T -> S) -> T) -> (T -> Empty) -> Empty.
Proof. 
  Ex(\lambda(f \in ((T -> S) -> T))(\lambda(g \in T -> Empty)(g@(f@(\lambda(t \in T)(abort(g@t))))))).
  Rlambda.
  Rlambda.
  Rapply(T). Rvar.
  Rapply(T -> S). Rvar.
  Rlambda.
  Rabort.
  Rapply(T). Rvar. Rvar.
Qed.

Theorem ex149 : exists_term t, [] |- t \in (((T -> S) + (S -> T)) -> Empty) -> Empty.
Proof. 
  Ex(\lambda(f \in ((T -> S) + (S -> T)) -> Empty)(f@(inl((\lambda(t \in T)(abort(f@(inr(\lambda(s \in S)t))))))))).
  Rlambda.
  Rapply((T -> S) + (S -> T)). Rvar.
  Rinl.
  Rlambda.
  Rabort.
  Rapply((T -> S) + (S -> T)). Rvar.
  Rinr.
  Rlambda. Rvar.
Qed.


Theorem ex150 : exists_term t, [] |- t \in  ((T -> S) -> U) -> ((S + (T -> Empty)) -> U).
Proof. 
  Ex(\lambda(f \in (T -> S) -> U)(\lambda(g \in S + (T -> Empty))(f@(\lambda(t \in T)(case(g, (s \in S)s, (h \in T -> Empty)(abort(h@t)))))))).
  Rlambda.
  Rlambda.
  Rapply(T -> S).  Rvar.
  Rlambda.
  Rcase. Rvar. Rvar.
  Rabort.
  Rapply(T). Rvar. Rvar.
Qed.

Inspect 50.



