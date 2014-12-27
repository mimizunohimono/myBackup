(** * SfLib: Software Foundations Library *)

(* $Date: 2013-07-17 16:19:11 -0400 (Wed, 17 Jul 2013) $ *)

(** Here we collect together several useful definitions and theorems
    from Basics.v, List.v, Poly.v, Ind.v, and Logic.v that are not
    already in the Coq standard library.  From now on we can [Import]
    or [Export] this file, instead of cluttering our environment with
    all the examples and false starts in those files. *)

(** * From the Coq Standard Library *)

Require Omega.   (* needed for using the [omega] tactic *)
Require Export Bool.
Require Export List.
Export ListNotations.
Require Export Arith.
Require Export Arith.EqNat.  (* Contains [beq_nat], among other things *)

(** * From Basics.v *)

Definition admit {T: Type} : T.  Admitted.

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Theorem andb_true_elim1 : forall b c,
  andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".
    reflexivity.
  Case "b = false".
    rewrite <- H. reflexivity.  Qed.

Theorem andb_true_elim2 : forall b c,
  andb b c = true -> c = true.
Proof.
  intros b c H1.
  destruct b.
  Case "b=true".
    simpl in H1.
    apply H1.
  Case "b=false".
    simpl in H1.
    inversion H1.
Qed.

Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
  intros n. induction n as [|n'].
  Case "n=O".
     intros m.  simpl. 
     destruct m as [|m'].
     SCase "m=O". reflexivity.
     SCase "m=Sm'". reflexivity.
  Case "n=Sn'".
     intros m.  
     destruct m as [|m'].
     SCase "m=O". reflexivity.
     SCase "m=Sm'". simpl. apply IHn'.
Qed.

(** * From Props.v *)

Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).

(** * From Logic.v *)

Theorem andb_true : forall b c,
  andb b c = true -> b = true /\ c = true.
Proof.
  intros b c H.
  destruct b.
    destruct c.
      apply conj. reflexivity. reflexivity.
      inversion H.
    inversion H.  Qed.

Theorem false_beq_nat: forall n n' : nat,
     n <> n' ->
     beq_nat n n' = false.
Proof. 
(* An exercise in Logic.v *)
  intros n m H1. 
  destruct (beq_nat n m) eqn:Heqn.
  Case "beq_nat n m = true".
     apply beq_nat_true in Heqn.
     apply H1 in Heqn.
     inversion Heqn.
  Case "beq_nat n m = false".
     reflexivity.
Qed.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  inversion contra.  Qed.

Theorem ev_not_ev_S : forall n,
  ev n -> ~ ev (S n).
Proof. 
(* An exercise in Logic.v *)
  unfold not. intros n H. induction H. (* not n! *)
  Case "ev 1".  intros H2. inversion H2.
  Case "ev n+3".  intros H2. inversion H2.
                  apply IHev in H1.  apply H1.
Qed.

Lemma O_le_n : forall n, 0 <= n.
Proof.
 intros n. induction n as [|n'].
 Case "O". 
    apply le_n.
 Case "Sn'". 
    apply le_S.
    apply IHn'.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m, n <= m -> S n <= S m.
Proof. 
 intros n m E1.
 induction E1 as [n1|n1 m1 E2].
 Case "le_n". 
    apply le_n.
 Case "le_S". 
 Case "le_S". 
    apply le_S.
    apply E2.
Qed.

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
(* An exercise in MoreProp.v *)
Proof. 
  intros n.
  induction n as [|n'].
  Case "n=O".
    intros m E1.
    apply O_le_n.
  Case "n=S n'".
    intros m E1.
    destruct m as [|m'].
    SCase "m=O".
       simpl in E1.
       inversion E1.
    SCase "m=S m'". 
       simpl in E1.
       apply n_le_m__Sn_le_Sm.
       apply IHn'.
       apply E1.
Qed.

(* From MoreProp.v *)
Theorem le_zero_nat : forall n m, n <= m -> m = O -> n = O.
Proof.
  intros n m E1 E2.
  induction E1 as [n1|n1 m1 E3].
  Case "le_n".  apply E2.
  Case "le_S".  inversion E2.
Qed.
(* From MoreProp.v *)
Lemma le_suc : forall n o, S n <= o -> n <= o.
Proof.
  intros n o E1.
  induction E1 as [|n1 E2].
  Case "le_n".
    apply le_S.
    apply le_n.
  Case "le_S".
    apply le_S.
    apply IHE2.
Qed.
(* From MoreProp.v *)
Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o E1.
  generalize dependent o.
  induction E1 as [|n1 E2].
  Case "le_n". 
    intros o E3.
    apply E3.
  Case "le_S".
    intros o E3.
    apply IHE2.
    apply le_suc.
    apply E3.
Qed.
(* From MoreProp.v *)
Theorem Sn_le_Sm__n_le_m : forall n m n1 m1, n1 = S n -> m1 = S m -> n1 <= m1 -> n <= m.
Proof. 
 intros n m n1 m1 En Em E1.
 induction E1 as [n2|n2 E2 E3].
 Case "le_n". 
    destruct n1 as [|n11].
    SCase "n1=O".  inversion En.
    SCase "n1=S n11".  
       inversion En.
       inversion Em.
       rewrite <- H0.
       rewrite <- H1.
       apply le_n.
 Case "le_S". 
    rewrite En in E2.
    inversion Em.
    rewrite H0 in E2.
    apply le_trans with (n:= S n).
    apply le_S.
    apply le_n.
    apply E2.
Qed.
(* From MoreProp.v *)
Lemma le_ble_nat : forall n m, n <= m -> ble_nat n m = true.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [|m'].
  Case "m=O".
     intros n E1.
     assert (H1: n=O).
     apply le_zero_nat with (m:=O).
     apply E1.
     reflexivity.
     rewrite -> H1.
     reflexivity.
  Case "m=S m'".
     intros n E1.      
     destruct n as [|n'].
     SCase "n=O".
        reflexivity.
     SCase "n=Sn'".
        simpl. 
        apply IHm'.
        apply Sn_le_Sm__n_le_m with (n1:=S n') (m1:= S m').
        reflexivity.
        reflexivity.
        apply E1.
Qed.

Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
(* An exercise in Logic.v *)
Proof.
  intros n m H1 H2.
  apply le_ble_nat in H2.
  rewrite -> H1 in H2.
  inversion H2.
Qed.

Inductive appears_in (n : nat) : list nat -> Prop :=
| ai_here : forall l, appears_in n (n::l)
| ai_later : forall m l, appears_in n l -> appears_in n (m::l).

Inductive next_nat (n:nat) : nat -> Prop :=
  | nn : next_nat n (S n).

Inductive total_relation : nat -> nat -> Prop :=
  tot : forall n m : nat, total_relation n m.

Inductive empty_relation : nat -> nat -> Prop := .

(** * From Later Files *)

Definition relation (X:Type) := X -> X -> Prop.

Definition deterministic {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2. 

Inductive multi (X:Type) (R: relation X) 
                            : X -> X -> Prop :=
  | multi_refl  : forall (x : X),
                 multi X R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi X R y z ->
                    multi X R x z.
Implicit Arguments multi [[X]]. 

Tactic Notation "multi_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "multi_refl" | Case_aux c "multi_step" ].

Theorem multi_R : forall (X:Type) (R:relation X) (x y : X),
       R x y -> multi R x y.
Proof.
  intros X R x y r.
  apply multi_step with y. apply r. apply multi_refl.   Qed.

Theorem multi_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      multi R x y ->
      multi R y z ->
      multi R x z.
Proof.
  intros X R x y z Hxy.
  generalize dependent z.
  induction Hxy as [x|x1 w1 y1 H1 H2].
  Case "multi_refl".
    intros z H. apply H.
  Case "multi_step".
    intros z H.         
    apply multi_step with (y:=w1).
    SCase "R x1 w1".  apply H1.
    SCase "multi R w1 z". 
       apply IHH2. 
       apply H.
Qed.

(**  Identifiers and polymorphic partial maps. *)

Inductive id : Type := 
  Id : nat -> id.

Theorem eq_id_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
Proof.
   intros id1 id2.
   destruct id1 as [n1]. destruct id2 as [n2].
   destruct (eq_nat_dec n1 n2) as [Heq | Hneq].
   Case "n1 = n2".
     left. rewrite Heq. reflexivity.
   Case "n1 <> n2".
     right. intros contra. inversion contra. apply Hneq. apply H0.
Defined. 

Lemma eq_id : forall (T:Type) x (p q:T), 
              (if eq_id_dec x x then p else q) = p. 
Proof.
  intros. 
  destruct (eq_id_dec x x); try reflexivity. 
  apply ex_falso_quodlibet; auto.
Qed.

Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> 
               (if eq_id_dec x y then p else q) = q. 
Proof.
  intros T x y p q.
  destruct (eq_id_dec x y); try reflexivity. 
  intros H1.
  apply H1 in e.
  inversion e.
Qed.

Definition partial_map (A:Type) := id -> option A.

Definition empty {A:Type} : partial_map A := (fun _ => None). 

Notation "'\empty'" := empty.

Definition extend {A:Type} (Gamma : partial_map A) (x:id) (T : A) :=
  fun x' => if eq_id_dec x x' then Some T else Gamma x'.

Lemma extend_eq : forall A (ctxt: partial_map A) x T,
  (extend ctxt x T) x = Some T.
Proof.
  intros. unfold extend. rewrite eq_id; auto. 
Qed.

Lemma extend_neq : forall A (ctxt: partial_map A) x1 T x2,
  x2 <> x1 ->
  (extend ctxt x2 T) x1 = ctxt x1.
Proof.
  intros. unfold extend. rewrite neq_id; auto. 
Qed.

Lemma extend_shadow : forall A (ctxt: partial_map A) t1 t2 x1 x2,
  extend (extend ctxt x2 t1) x2 t2 x1 = extend ctxt x2 t2 x1.
Proof with auto.
  intros. unfold extend. destruct (eq_id_dec x2 x1)...
Qed.

(** -------------------- *)

(** * Some useful tactics *)

Tactic Notation "solve_by_inversion_step" tactic(t) :=  
  match goal with  
  | H : _ |- _ => solve [ inversion H; subst; t ] 
  end
  || fail "because the goal is not solvable by inversion.".

Tactic Notation "solve" "by" "inversion" "1" :=
  solve_by_inversion_step idtac.
Tactic Notation "solve" "by" "inversion" "2" :=
  solve_by_inversion_step (solve by inversion 1).
Tactic Notation "solve" "by" "inversion" "3" :=
  solve_by_inversion_step (solve by inversion 2).
Tactic Notation "solve" "by" "inversion" :=
  solve by inversion 1.
