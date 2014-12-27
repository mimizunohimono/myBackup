(* PropLogicDef.v *)
(* Propositional Logic; Definitions *)
(* 2014/10/8 by Yukiyoshi Kameyama *)

Require Export SfLib.
Require Import Ascii String.
Open Scope type_scope.

Inductive prop : Type :=
  | False : prop 
  | Pvar  : nat -> prop 
  | Imp   : prop -> prop -> prop
  | And   : prop -> prop -> prop
  | Or    : prop -> prop -> prop
  | Not   : prop -> prop 
.

Fixpoint eqprop (p1 p2 : prop) : bool :=
  match (p1,p2) with
  | (False,False) => true
  | ((Pvar n1),(Pvar n2)) => beq_nat n1 n2
  | ((Imp p11 p12),(Imp p21 p22)) => andb (eqprop p11 p21) (eqprop p12 p22)
  | ((And p11 p12),(And p21 p22)) => andb (eqprop p11 p21) (eqprop p12 p22)
  | ((Or p11 p12),(Or p21 p22)) => andb (eqprop p11 p21) (eqprop p12 p22)
  | ((Not p11),(Not p21)) => (eqprop p11 p21)
  | (_,_) => false
  end
.

Fixpoint contains (pl : list prop) (p : prop) : bool :=
  match pl with
  | nil => false
  | cons p2 pl2 => orb (eqprop p p2) (contains pl2 p)
  end
.

Fixpoint discharge (pl : list prop) (p : prop) : list prop :=
  match pl with
  | nil => nil
  | cons p2 pl2 => if (eqprop p p2) then pl2 else cons p2 (discharge pl2 p)
  end
.

(* Note that we use Set, rather than Prop; to decompose this inductive data later *)
Inductive proves : list prop -> prop -> Set :=
  | Assume : forall p pl, (contains pl p = true) -> proves pl p
  | ImpI   : forall p q pl, proves (cons p pl) q -> proves pl (Imp p q)
  | ImpE   : forall p q pl, proves pl (Imp p q) -> proves pl p -> proves pl q
  | AndI   : forall p q pl, proves pl p -> proves pl q -> proves pl (And p q)
  | AndEL  : forall p q pl, proves pl (And q p) -> proves pl q
  | AndER  : forall p q pl, proves pl (And p q) -> proves pl q
  | OrIL   : forall p q pl, proves pl p -> proves pl (Or p q)
  | OrIR   : forall p q pl, proves pl q -> proves pl (Or p q)
  | OrE    : forall p q r pl, proves pl (Or p q) -> proves (cons p pl) r
                            -> proves (cons q pl) r -> proves pl r
  | NotI   : forall p pl, proves (cons p pl) False -> proves pl (Not p)
  | NotE   : forall p pl, proves pl (Not p) -> proves pl p -> proves pl False
  | FalseE : forall p pl, proves pl False -> proves pl p
  | NotNotE: forall p pl, proves pl (Not (Not p)) -> proves pl p
.


Notation P := (Pvar 0).
Notation Q := (Pvar 1).
Notation R := (Pvar 2).
Notation S := (Pvar 3).
Notation T := (Pvar 4).
Notation U := (Pvar 5).
Notation V := (Pvar 6).
Notation W := (Pvar 7).
Notation X := (Pvar 8).
Notation Y := (Pvar 9).
Notation Z := (Pvar 10).

Notation "pl |- p" := (proves pl p) (at level 100).
Notation "p1 /\ p2" := (And p1 p2) (at level 80, right associativity).
Notation "p1 \/ p2" := (Or p1 p2) (at level 85, right associativity).
Notation "p1 -> p2" := (Imp p1 p2) (at level 90, right associativity).
Notation "~ p1" := (Not p1) (at level 75, right associativity).
Print Grammar constr.

Ltac assume  := apply Assume; reflexivity.
Ltac andI    := apply AndI.
Ltac andEL P := apply (AndEL P).
Ltac andER P := apply (AndER P).
Ltac orIL    := apply OrIL.
Ltac orIR    := apply OrIR.
Ltac orE P Q := apply (OrE P Q).
Ltac impI    := apply ImpI.
Ltac impE P  := apply (ImpE P).
Ltac notI    := apply NotI.
Ltac notE P  := apply (NotE P).
Ltac falseE  := apply FalseE.
Ltac notnotE := apply NotNotE.

(* 
  Rules:
    assume           assume
    impI             ->I
    impE (P)         ->E
    andI             /\I
    andEL (P)        /\EL
    andER (P)        /\ER
    orIL             \/IL
    orIR             \/IR
    orE (P) (Q)      \/E
    notI             ¢ÌI
    notE (P)         ¢ÌE
    falseE           ¢ÝE
    notnotE          ¢Ì¢ÌE
*)



