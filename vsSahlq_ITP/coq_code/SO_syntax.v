Require Import base_mods.


(* Definition of predicate and first order variable types, using Pred and Var
 constructors repectively. Assumes countably infinite for each. *)

Inductive predicate : Type :=
  Pred : nat -> predicate.

Lemma predicate_dec : forall (P Q : predicate), {P = Q} + {P <> Q}.
Proof.
  intros [p] [q]. destruct (Nat.eq_dec p q).
  subst. auto.
  right. intros H. inversion H. subst. auto.
Qed.

Lemma predicate_dec_l : forall {T : Type} P Q (x y : T),
    P = Q ->
    (if predicate_dec P Q then x else y) =  x.
Proof.
  intros T [Pn] [Qm] x y H.
  inversion H. subst.
  destruct (predicate_dec (Pred Qm) (Pred Qm)); firstorder.
Qed.

Lemma predicate_dec_r : forall {T : Type} P Q (x y : T),
    P <> Q ->
    (if predicate_dec P Q then x else y) =  y.
Proof.
  intros T [Pn] [Qm] x y H.
  destruct (predicate_dec (Pred Pn) (Pred Qm)); firstorder.
Qed.

Lemma predicate_dec_refl : forall {T : Type} P (a b : T),
    (if predicate_dec P P then a else b) = a.
Proof. intros. rewrite predicate_dec_l; firstorder. Qed.

Lemma Pred_neq : forall Pn Qm,
  Pred Pn <> Pred Qm -> Pn <> Qm.
Proof. intros xn ym H1 H2. subst. contradiction. Qed.

Lemma in_predicate_dec : forall (a : predicate) l, {In a l} + {~ In a l}.
Proof.
  intros. apply in_dec. apply predicate_dec.
Qed.

Lemma in_predicate_dec_l : forall {T : Type} (a : predicate) l (x y : T),
    In a l -> ((if in_predicate_dec a l then x else y) = x).
Proof.
  intros. destruct (in_predicate_dec a l) as [H2 | H2].
  auto. contradiction.
Qed.

Lemma in_predicate_dec_r : forall {T : Type} (a : predicate) l (x y : T),
    ~ In a l -> ( (if in_predicate_dec a l then x else y) = y).
Proof.
  intros. destruct (in_predicate_dec a l) as [H2 | H2].
  contradiction. auto.
Qed.

Inductive FOvariable : Type :=
  Var : nat -> FOvariable.

Lemma FOvariable_dec : forall (x y : FOvariable), {x = y} + {x <> y}.
Proof.
  intros [p] [q]. destruct (PeanoNat.Nat.eq_dec p q).
  subst. auto. right. intros H. 
  inversion H. subst. auto.
Qed.

Lemma FOvariable_dec_l : forall {T : Type} z1 z2 (x y : T),
    z1 = z2 ->
    (if FOvariable_dec z1 z2 then x else y) =  x.
Proof.
  intros T z1 z2 x y H. subst.
  destruct (FOvariable_dec z2); firstorder.                                 
Qed.

Lemma FOvariable_dec_r : forall {T : Type} P Q (x y : T),
    P <> Q ->
    (if FOvariable_dec P Q then x else y) =  y.
Proof.
  intros T z1 z2 x y H.
  destruct (FOvariable_dec z1 z2); firstorder.
Qed.

Lemma FOvariable_dec_refl : forall {T : Type} x (a b : T),
 (if FOvariable_dec x x then a else b) = a.
Proof. intros. rewrite FOvariable_dec_l; firstorder. Qed.

Lemma Var_neq : forall xn ym,
  Var xn <> Var ym -> xn <> ym.
Proof. intros xn ym H1 H2. subst. contradiction. Qed.

Lemma FOv_not : forall n m,
    n <> m <-> Var n <> Var m.
Proof.
  intros n m; split; intros H1 H2; 
  inversion H2 as [H3]; subst; firstorder.
Qed.

(* Second order formula (precisely: monadic second order logic with 
a single binary relation and equality over firstorder variables.) *)
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
  | exSO : predicate -> SecOrder -> SecOrder.

Notation "$ P" := (predSO P) (at level 1) : SO_scope.
Notation "x =FOv y" := (eqFO x y) (at level 2) : SO_scope.
Notation "SO~ α" := (negSO α) (at level 2) : SO_scope.
Notation "A SO∨ B" := (disjSO A B) (at level 15, right associativity) : SO_scope.
Notation "A SO∧ B" := (conjSO A B) (at level 15, right associativity) : SO_scope.
Notation "A SO→ B" := (implSO A B) (at level 16, right associativity) : SO_scope.

(* Given a conditional, return the antecedent. Don't care about other
   inputs. *)
Fixpoint calc_ante_SO alpha :=
  match alpha with
  | predSO _ _ => alpha
  | relatSO _ _ => alpha
  | eqFO _ _ => alpha
  | allFO x beta => alpha
  | exFO x beta => alpha
  | negSO beta => alpha
  | conjSO beta1 beta2 => alpha
  | disjSO beta1 beta2 => alpha
  | implSO beta1 beta2 => beta1
  | allSO Q beta => alpha
  | exSO Q beta => alpha
  end.

(* Given a conditional, returns the consequent. Don't care about other
   inputs. *)
Fixpoint calc_cons_SO alpha :=
  match alpha with
  | predSO _ _ => alpha
  | relatSO _ _ => alpha
  | eqFO _ _ => alpha
  | allFO x beta => alpha
  | exFO x beta => alpha
  | negSO beta => alpha
  | conjSO beta1 beta2 => alpha
  | disjSO beta1 beta2 => alpha
  | implSO beta1 beta2 => beta2
  | allSO Q beta => alpha
  | exSO Q beta => alpha
  end.
