Require Import Coq.Arith.EqNat.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Logic.Classical_Prop.

(* Definition of predicate and FO variable types, using Pred and Var constructors repectively.
Assumes countably infinite for each. *)
Inductive predicate : Type :=
  Pred : nat -> predicate.
Inductive FOvariable : Type :=
  Var : nat -> FOvariable.

(* SO formaula definition with equality. *)
Inductive SecOrder :=
    predSO : predicate -> FOvariable -> SecOrder
  | relatSO : FOvariable -> FOvariable -> SecOrder
  | eqFO : FOvariable -> FOvariable -> SecOrder
  | allFO : FOvariable -> SecOrder -> SecOrder
  | exFO : FOvariable -> SecOrder -> SecOrder
  | negSO : SecOrder -> SecOrder 
  | conjSO : SecOrder -> SecOrder -> SecOrder 
  | disjSO : SecOrder -> SecOrder -> SecOrder 
  | implSO : SecOrder -> SecOrder -> SecOrder 
  | allSO : predicate -> SecOrder -> SecOrder
  | exSO : predicate -> SecOrder -> SecOrder .
(*  | eqSO : predicate -> predicate -> SecOrder. *)

(* SO Semantics *)

(* Semantics requires ability to change interpretation on variables slightly: *)
Fixpoint alt_Iv {D:Set} (Iv: FOvariable -> D) (d:D) (x:FOvariable) (y:FOvariable) : D :=
  match y, x with 
    Var m, Var n=> (if beq_nat n m then d else (Iv (Var m)))
  end.

(* Semantics requires ability to change interpretation on predicates slightly: *)
Fixpoint alt_Ip {D:Set} (Ip: predicate -> D -> Prop) (pred_asgmt: D -> Prop) 
                      (P: predicate) (Q: predicate) : D -> Prop :=
  match Q, P with
    Pred m, Pred n => (if beq_nat n m then pred_asgmt else Ip (Pred m))
  end.


(* Iv = interpretation of FOvariables; 
   Ip = interpretation of predicates (here a function D -> Prop is seen as denoting a set); 
   Ir = interpretation on binary relation. *)
Fixpoint SOturnst (D:Set) (Iv: FOvariable -> D) (Ip: predicate -> D -> Prop) (Ir: D -> D -> Prop) 
                     (alpha:SecOrder) : Prop :=
  match alpha with
    predSO P x => (Ip P (Iv x))
  | relatSO x y => (Ir (Iv x) (Iv y))
  | eqFO x y => (Iv x) = (Iv y)
  | allFO x beta => forall d:D, SOturnst D (alt_Iv Iv d x) Ip Ir beta
  | exFO x beta => (exists d:D, SOturnst D (alt_Iv Iv d x) Ip Ir beta)
  | negSO beta => ~ SOturnst D Iv Ip Ir beta
  | conjSO beta1 beta2 => (SOturnst D Iv Ip Ir beta1) /\ (SOturnst D Iv Ip Ir beta2)
  | disjSO beta1 beta2 => (SOturnst D Iv Ip Ir beta1) \/ (SOturnst D Iv Ip Ir beta2)
  | implSO beta1 beta2 => (SOturnst D Iv Ip Ir beta1) -> (SOturnst D Iv Ip Ir beta2)
  | allSO P beta => forall (pred_asgmt: D -> Prop), 
                               SOturnst D Iv (alt_Ip Ip pred_asgmt P) Ir beta
  | exSO P beta => (exists (pred_asgmt: D -> Prop), 
                              (SOturnst D Iv (alt_Ip Ip pred_asgmt P) Ir beta))
  end.


(*----------------------------------------------------------------------------*)

(* "By definition" lemmas of SOturnst *)

Lemma SOturnst_allFO : forall (D:Set) (Iv: FOvariable -> D) (Ip: predicate -> D -> Prop) (Ir: D -> D -> Prop)
                              (x:FOvariable) (beta:SecOrder), 
                                   (SOturnst D Iv Ip Ir (allFO x beta)) 
                                        = (forall (d:D), SOturnst D (alt_Iv Iv d x) Ip Ir beta).
Proof.
  intros D Iv Ip Ir x beta; destruct x.
  simpl; reflexivity.
Qed.

Lemma SOturnst_exFO : forall (D:Set) (Iv: FOvariable -> D) (Ip: predicate -> D -> Prop) (Ir: D -> D -> Prop)
                              (x:FOvariable) (beta:SecOrder), 
                                   (SOturnst D Iv Ip Ir (exFO x beta)) 
                                        = (exists (d:D), (SOturnst D (alt_Iv Iv d x) Ip Ir beta)).
Proof.
  intros D Iv Ip Ir x beta; destruct x.
  simpl; reflexivity.
Qed.

Lemma SOturnst_implSO : forall (D:Set) (Iv: FOvariable -> D) (Ip: predicate -> D -> Prop) 
                        (Ir: D -> D -> Prop) (beta_1 beta_2 : SecOrder),
                            (SOturnst D Iv Ip Ir (implSO beta_1 beta_2)) =
                             ((SOturnst D Iv Ip Ir beta_1) -> (SOturnst D Iv Ip Ir beta_2)).
Proof.
  intros D Iv Ip Ir beta_1 beta_2.
  simpl; reflexivity.
Qed.

Lemma SOturnst_conjSO : forall (D:Set) (Iv:FOvariable -> D) (Ip: predicate -> D -> Prop) 
                        (Ir: D -> D -> Prop) (beta_1 beta_2 : SecOrder),
                            (SOturnst D Iv Ip Ir (conjSO beta_1 beta_2)) =
                             ((SOturnst D Iv Ip Ir beta_1) /\ (SOturnst D Iv Ip Ir beta_2)).
Proof.
  intros D Iv Ip Ir beta_1 beta_2.
  simpl; reflexivity.
Qed.

Lemma SOturnst_disjSO : forall (W:Set) (beta_1 beta_2 : SecOrder) (Iv: FOvariable -> W)
                               (Ip : predicate -> W -> Prop) (Ir: W -> W -> Prop),
       SOturnst W Iv Ip Ir (disjSO beta_1 beta_2) 
    = ((SOturnst W Iv Ip Ir beta_1) \/ (SOturnst W Iv Ip Ir beta_2)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma SOturnst_allSO : forall (D:Set) (Iv:FOvariable -> D) (Ip: predicate -> D -> Prop) 
                        (Ir: D -> D -> Prop) (P: predicate) (beta : SecOrder), 
         SOturnst D Iv Ip Ir (allSO P beta) = (forall (pred_asgmt: D -> Prop), 
                               SOturnst D Iv (alt_Ip Ip pred_asgmt P) Ir beta).
Proof.
  intros D Iv Ip Ir P beta.
  destruct P.
  simpl; reflexivity.
Qed.

Lemma SOturnst_exSO : forall (D:Set) (Iv:FOvariable -> D) (Ip: predicate -> D -> Prop) 
                        (Ir: D -> D -> Prop) (P: predicate) (beta : SecOrder), 
         SOturnst D Iv Ip Ir (exSO P beta) = (exists (pred_asgmt: D -> Prop), 
                               SOturnst D Iv (alt_Ip Ip pred_asgmt P) Ir beta).
Proof.
  intros D Iv Ip Ir P beta.
  destruct P.
  simpl; reflexivity.
Qed.

Lemma SOturnst_negSO : forall (D:Set) (Iv:FOvariable -> D) (Ip: predicate -> D -> Prop) 
                        (Ir: D -> D -> Prop) (beta : SecOrder), 
        SOturnst D Iv Ip Ir (negSO beta) = ~ SOturnst D Iv Ip Ir beta.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

(* --------------------------------------------------------------------------------- *)

(* List of predicates in given SecOrder formula. *)
Fixpoint preds_in (alpha:SecOrder) : list predicate :=
  match alpha with
    predSO P _ => cons P nil
  | relatSO _ _ => nil
  | eqFO _ _ => nil
  | allFO _ beta => preds_in beta
  | exFO _ beta => preds_in beta
  | negSO beta => preds_in beta
  | conjSO beta1 beta2 => app (preds_in beta1) (preds_in beta2) 
  | disjSO beta1 beta2 => app (preds_in beta1) (preds_in beta2)
  | implSO beta1 beta2 => app (preds_in beta1) (preds_in beta2)
  | allSO P beta => cons P (preds_in beta)
  | exSO P beta => cons P (preds_in beta)
(*  | eqSO (Pred n) (Pred m) => cons (Pred n) (cons (Pred m) nil) *)
  end.

(* Function that quantifies over the predicates in the given list. *)
Fixpoint list_closed_SO (alpha:SecOrder) (l: list predicate) : SecOrder :=
  match l with
    nil => alpha
  | cons P ls => allSO P (list_closed_SO alpha ls)
  end.

(* Universally closes SO formulas. *)
Definition uni_closed_SO (alpha:SecOrder) : SecOrder := list_closed_SO alpha (preds_in alpha).

(* -------------------------------------------------------------------------------------------- *)

Lemma unalt_fun : forall (D:Set) (Ip: predicate -> D -> Prop) (P: predicate),
                      (alt_Ip Ip (Ip P) P) = Ip.
Proof.
  intros.
  apply functional_extensionality; intros.
  apply functional_extensionality; intros.
  destruct x as [Qm].
  destruct P as [Pn].
  simpl.
  case_eq (beq_nat Pn Qm).
    intros.
    pose proof (beq_nat_true Pn Qm).
    pose proof (H0 H).
    rewrite H1.
    reflexivity.

    intros.
    reflexivity.
Qed.

Lemma unalt_fun_Iv : forall (D:Set) (Iv: FOvariable -> D) (x : FOvariable),
                      (alt_Iv Iv (Iv x) x) = Iv.
Proof.
  intros.
  apply functional_extensionality; intros y.
  destruct x as [xn]; destruct y as [ym].
  simpl.
  case_eq (beq_nat xn ym); intros Hbeq;
    [rewrite (beq_nat_true _ _ Hbeq) |];
    reflexivity.
Qed.

(* -------------------------------------------------------------------------------------------- *)

(* Proof of classicality *)

Lemma SO_lem : forall alpha D Iv Ip Ir,
  SOturnst D Iv Ip Ir (disjSO alpha (negSO alpha)).
Proof.
  intros alpha D Iv Ip Ir. apply classic.
Qed.