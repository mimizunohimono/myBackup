(* PropLogic.v *)
(* Propositional Logic; Exercises *)
(* 2014/10/8 by Yukiyoshi Kameyama *)

Require Export SfLib.
Require Import Ascii String.
Require Export PropLogicDef.

(**************)
(*  Exercises *)
(**************)

Theorem ex01 : [P] |- P.
Proof.
  assume.
Qed.

Theorem ex02 : [P; Q] |- P.
Proof.
  assume.
Qed.

Theorem ex03 : [P; Q] |- (P /\ Q).
Proof.
  andI.
  assume.
  assume.
Qed.
Print ex03.

Theorem ex04 : [P /\ Q] |- P.
Proof.
  andEL(Q).
  assume.
Qed.

Theorem ex05 : [P] |- P /\ P.
Proof.
  andI.
  assume.
  assume.
Qed.

Theorem ex06 : [P /\ Q] |- P /\ (Q /\ P).
Proof.
  andI.
  andEL(Q).
  assume.
  andI.
  andER(P).
  assume.
  andEL(Q).
  assume.
Qed.

Theorem ex07 : [(P /\ Q) /\ R] |- P /\ (Q /\ R).
Proof.
  andI.
  andEL(Q).
  andEL(R).
  assume.
  andI.
  andER(P).
  andEL(R).
  assume.
  andER(P/\Q).
  assume.
Qed.


Theorem ex08 : [P /\ (Q /\ R)] |- (P /\ Q) /\ R.
Proof.
  andI.
  andI.
  andEL(Q/\R).
  assume.
  andEL(R).
  andER(P).
  assume.
  andER(Q).
  andER(P).
  assume.
Qed.

Theorem ex09 : [] |- P -> P.
Proof.
  impI.
  assume.
Qed.


Theorem ex10 : [] |- P -> P -> P.
Proof.
  impI.
  impI.
  assume.
Qed.

Theorem ex11 : [] |- P -> Q -> P.
Proof.
  impI.
  impI.
  assume.
Qed.

Theorem ex12 : [] |- (P -> P -> Q) -> (P -> Q).
Proof.
  impI.
  impI.
  impE(P).
  impE(P).
  assume.
  assume.
  assume.
Qed.


Theorem ex13 : [] |- (P -> Q -> R) -> (P -> Q) -> (P -> R).
Proof.
  impI.
  impI.
  impI.
  impE (Q).
  impE (P).
  assume.
  assume.
  impE (P).
  assume.
  assume.
Qed.

Theorem ex14 : [] |- P /\ Q -> Q /\ P.
Proof.
  impI.
  andI.
    andER (P). assume.
    andEL (Q). assume.
Qed.

Theorem ex15 : [] |- P -> (P -> Q) -> Q.
Proof.
  impI.
  impI.
  impE(P).
  assume.
  assume.
Qed.

Theorem ex16 : [] |- P -> P \/ Q.
Proof.
  impI.
  orIL.
  assume.
Qed.

Theorem ex17 : [] |- P -> Q \/ P.
Proof.
  impI.
  orIR.
  assume.
Qed.

Theorem ex18 : [] |- P \/ P -> P.
Proof.
  impI.
  orE(P)(P).
  assume.
  assume.
  assume.
Qed.

Theorem ex19 : [] |- P \/ Q -> Q \/ P.
Proof.
  impI.
  orE (P) (Q).
    assume.
    orIR. assume.
    orIL. assume.
Qed.

Theorem ex20 : [] |- (P \/ (Q \/ R)) -> ((P \/ Q) \/ R).
Proof.
  impI.
  orE(P)(Q\/R).
  assume.
  orIL.
  orIL.
  assume.
  orE(Q)(R).
  assume.
  orIL.
  orIR.
  assume.
  orIR.
  assume.
Qed.

Theorem ex21 : [] |- (P /\ (Q \/ R)) -> ((P /\ Q) \/ (P /\ R)).
Proof.
  impI.
  orE(Q)(R).
  andER(P).
  assume.
  orIL.
  andI.
  andEL(Q\/R).
  assume.
  assume.
  orIR.
  andI.
  andEL(Q\/R).
  assume.
  assume.
Qed.

Theorem ex22 : [] |- ((P /\ Q) \/ (P /\ R)) -> (P /\ (Q \/ R)).
Proof.
  impI.
  andI.
  orE(P/\Q)(P/\R).
  assume.
  andEL(Q).
  assume.
  andEL(R).
  assume.
  orE(P/\Q)(P/\R).
  assume.
  orIL.
  andER(P).
  assume.
  orIR.
  andER(P).
  assume.
Qed.

Theorem ex23 : [] |- (P \/ (Q /\ R)) -> ((P \/ Q) /\ (P \/ R)).
Proof.
  impI.
  andI.
  orE(P)(Q/\R).
  assume.
  orIL.
  assume.
  orIR.
  andEL(R).
  assume.
  orE(P)(Q/\R).
  assume.
  orIL.
  assume.
  orIR.
  andER(Q).
  assume.
Qed.

Theorem ex24 : [] |- ((P \/ Q) /\ (P \/ R)) -> (P \/ (Q /\ R)).
Proof.
  impI.
  orE(P)(Q).
  andEL(P \/ R).
  assume.
  orIL.
  assume.
  orE(P)(R).
  andER(P \/ Q).
  assume.
  orIL.
  assume.
  orIR.
  andI.
  assume. assume.
Qed.

Theorem ex25 : [] |- (P -> False) -> ~ P.
Proof.
  impI.
  notI.
  impE(P).
  assume.
  assume.
Qed.

Theorem ex26 : [] |- ~P -> (P -> False).
Proof.
  impI.
  impI.
  notE(P).
  assume.
  assume.
Qed.

Theorem ex27 : [] |- P /\ ~P -> Q.
Proof.
  impI.
  falseE.
  notE(P).
  andER(P).
  assume.
  andEL(~P).
  assume.
Qed.

Theorem ex28 : [] |- P -> ~~P.
Proof.
  impI.
  notI.
  notE(P).
  assume.
  assume.
Qed.

Theorem ex29 : [] |- (P -> Q) -> (~Q -> ~P).
Proof.
  impI.
  impI.
  notI.
  notE(Q).
  assume.
  impE(P).
  assume.
  assume.
Qed.

Theorem ex30 : [] |- ~~~P -> ~P.
Proof.
  impI.
  notI.  
  notE(~~P).
  assume.
  notI.
  notE(P).
  assume.
  assume.
Qed.

(* classical theorem   [] |- ~(P /\ Q) -> ~P \/ ~Q *)
Theorem ex31 : [] |- ~~(~(P /\ Q) -> ~P \/ ~Q).
Proof.
  notI.
  notE(~ (P /\ Q) -> ~ P \/ ~ Q).
  assume.
  impI.
  orIL.
  notI.
  notE(P/\Q).
  assume.
  andI.
  assume.
  notnotE.
  notI.
  notE(~ (P /\ Q) -> ~ P \/ ~ Q).
  assume.
  impI.
  orIR.
  assume.
Qed.

Theorem ex32 : [] |- ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  impI.
  andI.
  notI.
  notE(P\/Q).
  assume.
  orIL.
  assume.
  notI.
  notE(P\/Q).
  assume.
  orIR.
  assume.
Qed.

Theorem ex33 : [] |- (P \/ False) -> P.
Proof.
  impI.
  orE(P)(False).
  assume.
  assume.
  falseE.
  assume.
Qed.

Theorem ex34 : [] |- ~ False.
Proof.
  notI.
  assume.
Qed.

Theorem ex35 : [] |- ~ (P /\ ~P).
Proof.
  notI.
  notE(P).
  andER(P).
  assume.
  andEL(~P).
  assume.
Qed.

Theorem ex36 : [] |- P /\ False -> Q /\ P.
Proof.
  impI.
  andI.
  orE(Q)(False).
  orIR.
  andER(P).
  assume.
  assume.
  falseE.
  assume.
  andEL(False).
  assume.
Qed.

(* classical theorem  [] |- (P -> Q) -> (~P \/ Q) *)
Theorem ex37 : [] |- (P -> Q) -> ~~ (~P \/ Q).
Proof.
  impI.
  notI.
  notE(~P\/Q).
  assume.
  orIL.
  notI.
  notE(~P\/Q).
  assume.
  orIR.
  impE(P).
  assume. assume.
Qed.  

Theorem ex38 : [] |- (~P \/ Q) -> P -> Q.
Proof.
  impI.
  impI.
  orE(~P)(Q).
  assume.
  falseE.
  notE(P).
  assume.
  assume.
  assume.
Qed.

Theorem ex39 : [] |- (P -> Q -> R) -> (P /\ Q -> R).
Proof.
  impI.
  impI.
  orE(P)(Q).
  orIL.
  andEL(Q).
  assume.
  impE(Q).
  impE(P).
  assume.
  assume.
  andER(P).
  assume.
  impE(Q).
  impE(P).
  assume.
  andEL(Q).
  assume.
  assume.
Qed.

Theorem ex40 : [] |- (P /\ Q -> R) -> (P -> Q -> R).
Proof.
  impI.
  impI.
  impI.
  impE(P/\Q).
  assume.
  andI.
  assume.
  assume.
Qed.  

Theorem ex41 : [] |- (P \/ Q -> R) -> (P -> R) /\ (Q -> R).
Proof.
  impI.
  andI.
  impI.
  impE(P\/Q).
  assume.
  orIL.
  assume.
  impI.
  impE(P\/Q).
  assume.
  orIR.
  assume.
Qed.

Theorem ex42 : [] |- (P -> R) /\ (Q -> R) -> (P \/ Q -> R).
Proof.
  impI.
  impI.
  orE(P)(Q).
  assume.
  impE(P).
  andEL(Q -> R).
  assume.
  assume.
  impE(Q).
  andER(P -> R).
  assume.
  assume.
Qed.

Theorem ex43 : [] |- (P -> Q) -> (Q -> R) -> (R -> S) -> (P -> S).
Proof.
  impI.  impI.  impI.  impI.
  impE(R).
  assume.
  impE(Q).
  assume.
  impE(P).
  assume.
  assume.
Qed.

Theorem ex44 : [] |- (P \/ Q) -> (P -> R) -> (Q -> R) -> R.
Proof.
  impI.  impI.  impI.
  orE(P)(Q).
  assume.
  impE(P).
  assume.
  assume.
  impE(Q).
  assume.
  assume.
Qed.

(* classical theorem  [] |- P \/ (~ p) *)
Theorem ex45 : [] |- ~~(P \/ (~ P)).
Proof.
  notI.
  notE (P \/ ~P).
    assume.
    orIR. notI. notE (P \/ ~P).
      assume.
      orIL. assume.
Qed.

(* classical theorem  [] |- ~~P -> P *)
Theorem ex46 : [] |- ~~(~~P -> P).
Proof.
  notI.
  notE(~~P -> P).
  assume.
  impI.
  orE(P)(~P).
  orIL.
  notnotE.
  assume.
  assume.
  falseE.
  notE(~P).
  assume.
  assume.
Qed.

(* classical theorem  [] |- ((P -> Q) -> P) -> P *)
Theorem ex47 : [] |- ~~(((P -> Q) -> P) -> P).
Proof.
  notI.
  notE (((P -> Q) -> P) -> P).
    assume.
    impI.
    impE (P->Q).
      assume.
      impI.
      falseE.
      notE (((P -> Q) -> P) -> P).
      assume.
      impI.
      assume.
Qed.

Theorem ex48 : [] |- ((P -> Q) -> P) -> ~~P.
Proof. 
  impI.
  notI.
  notE(P).
  assume.
  impE(P -> Q).
  assume.
  impI.
  falseE.
  notE(P).
  assume.
  assume.
Qed.

(* classical theorem  [] |- (P -> Q) \/ (Q -> P) *)
Theorem ex49 : [] |- ~~((P -> Q) \/ (Q -> P)).
Proof. 
  notI.
  notE((P -> Q) \/ (Q -> P)).
  assume.
  orIL.
  impI.  
  falseE.
  notE((P -> Q) \/ (Q -> P)).
  assume.
  orIR.
  impI.
  assume.
Qed.

Theorem ex50 : [] |- ((P -> Q) -> R) -> (Q \/ ~P -> R).
Proof. 
  impI.
  impI.
  impE (P -> Q).
  assume.
  impI.
  orE (Q) (~P).
    assume.
    assume.
    falseE.
    notE (P).
      assume.
      assume.
Qed.

Inspect 50.




