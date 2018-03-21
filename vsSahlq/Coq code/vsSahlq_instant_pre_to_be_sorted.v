Require Import SecOrder.
Require Import P_occurs_in_alpha.
Require Import ST_setup.
Require Import Correctness_ST.
Require Import Arith.EqNat my_bool.
Require Import List_machinery_impl My_List_Map.
Require Import Unary_Predless nList_egs Rep_Pred_FOv Indicies Identify.
Require Import pos_SO2 neg_SO2 Num_Occ Bool my_bool Is_Pos_Rep_Pred P_occ_rep_pred.
Require Import Uniform_Defns Monotonicity_SO Pre_Sahlqvist_Uniform_Pos P_occ_rep_pred.
Require Import Unary_Predless_l Num_Occ_l2 Occ_In_Alpha My_Prop Sahlqvist_Uniform_Pos.
Require Import vsSahlq_preprocessing1 vsSahlq_preprocessing2 vsSahlq_preprocessing3.
Require Import vsSahlq_instant3 my_arith__my_leb_nat.

Lemma max_refl : forall n,
  max n n = n.
Proof.
  induction n. reflexivity.
    simpl. rewrite IHn.
    reflexivity.
Qed.

Lemma max_comm : forall n m,
  max n m = max m n.
Proof.
  induction n; intros m.
    simpl. destruct m; reflexivity.

    simpl. destruct m. reflexivity.
    simpl. rewrite IHn. reflexivity.
Qed.


Lemma max_suc_l : forall n,
  max (S n) n = S n.
Proof.
  induction n. reflexivity.
  simpl in *. rewrite IHn. reflexivity.
Qed.

Lemma neq_beq_nat_FOv : forall xn ym,
  ~ (Var xn) = (Var ym) -> beq_nat xn ym = false.
Proof.
  intros xn ym H.
  case_eq (beq_nat xn ym); intros Hbeq.
    rewrite (beq_nat_true _ _ Hbeq) in *.
    contradiction (H eq_refl).

    reflexivity.
Qed.

Lemma beq_nat_false_FOv: forall n m : nat, 
  beq_nat n m = false -> (Var n) <> (Var m).
Proof.
  intros n m H1 H2.
  inversion H2 as [H2'].
  rewrite H2' in *. rewrite <- beq_nat_refl in H1.
  discriminate.
Qed.

Lemma leb_max_l : forall n m,
  Nat.leb m n = true ->
  max n m = n.
Proof.
  induction n; intros m Hleb.
    rewrite leb_beq_zero in Hleb.
    rewrite (beq_nat_true _ _ Hleb).
    reflexivity.

    destruct m. simpl. reflexivity.
    simpl. rewrite IHn. reflexivity.
      apply Hleb.
Qed.

Lemma rename_FOv__n : forall alpha xn ym,
  rename_FOv alpha (Var xn) (Var ym) = 
  rename_FOv_n alpha xn ym.
Proof.
  reflexivity.
Qed.

Lemma max_max : forall i j k,
  max (max i j) k =
  max (max i k) (max j k).
Proof.
  induction i; intros j k.
    simpl. rewrite max_comm.
    rewrite PeanoNat.Nat.max_assoc.
    rewrite max_refl. reflexivity.

    simpl. destruct j. destruct k.
      reflexivity.
      simpl. rewrite <- PeanoNat.Nat.max_assoc.
      rewrite max_refl. reflexivity.

      destruct k.  reflexivity.
        simpl. rewrite IHi. reflexivity.
Qed.

Lemma leb_min_r : forall n m1 m2,
  Nat.leb n (min m1 m2) = true ->
  Nat.leb n m1 = true /\ Nat.leb n m2 = true.
Proof.
  induction n; intros m1 m2 Hleb.
    simpl in *. apply conj; reflexivity.

    simpl in *. destruct m1.
      simpl in *. discriminate.
    destruct m2. simpl in *.
      discriminate.
    simpl in *.
    apply IHn. assumption.
Qed.


Lemma min_suc : forall n,
  min (S n) n = n.
Proof.
  induction n. reflexivity.
  simpl in *. rewrite IHn.
  reflexivity.
Qed.

Lemma min_plus_l : forall n m,
  min (n + m) n = n.
Proof.
  induction n; intros m.
    simpl. apply PeanoNat.Nat.min_0_r.

    simpl. rewrite IHn. reflexivity.
Qed.

Lemma nlist_empty_nil : forall {A : Type} (l2:list A),
  nlist_list _ (nlist_empty (length l2)) = nil ->
  l2 = nil.
Proof.
  intros A. induction l2; intros H.
    reflexivity.

    simpl in *. discriminate.
Qed.


Lemma leb_suc_f2 : forall n m,
  Nat.leb (S n + m) n = false.
Proof.
  intros n. induction m.
    rewrite <- plus_n_O.
    rewrite one_suc.
    apply leb_notswitch.
    apply leb_refl.

    rewrite PeanoNat.Nat.add_succ_r.
    rewrite one_suc.
    apply leb_notswitch.
    apply leb_switch in IHm.
    assumption.
Qed.

Lemma neq_comm : forall {A : Type} (x y : A),
  ~ x = y -> ~ y = x.
Proof.
  intros A x y H1 H2.
    rewrite H2 in H1. contradiction (H1 eq_refl).
Qed.

Lemma beq__leb : forall n m,
  beq_nat n m = true ->
  Nat.leb n m = true.
Proof.
  induction n; intros m Hbeq.
    reflexivity.

    destruct m. simpl in Hbeq.
      discriminate.
    simpl in *. apply IHn. assumption.
Qed.

Lemma min_comm : forall n m,
  min n m = min m n.
Proof.
  induction n; intros m.
    simpl.
    symmetry. apply PeanoNat.Nat.min_0_r.

    simpl. destruct m. reflexivity.
    simpl. rewrite IHn. reflexivity.
Qed.

Lemma min_or : forall n a,
Nat.min n a = n \/ Nat.min n a = a.
Proof.
  induction n; intros a.
    left. reflexivity.

    simpl. destruct a. right. reflexivity.
    destruct (IHn a) as [H1 | H1];
      rewrite H1; [left | right];
      reflexivity.
Qed.

Lemma leb_min_l : forall n m,
  Nat.leb (min n m) n = true.
Proof.
  induction n; intros m.
    reflexivity.

    simpl. destruct m. reflexivity.
    simpl. apply IHn.
Qed.

Lemma leb_min : forall n m,
  min n m = n ->
  Nat.leb n m = true.
Proof.
  induction n; intros m Hmin.
    reflexivity.

    simpl in *. destruct m. discriminate.
    inversion Hmin.
    rewrite min_comm.
    apply leb_min_l.
Qed.

Lemma leb_min_l2 : forall a b c,
  Nat.leb a b = true ->
  Nat.leb (min a c) b = true.
Proof.
  induction a; intros b c H.
    simpl in *. reflexivity.

    simpl in *. destruct b. discriminate.
    destruct c. reflexivity.
    simpl. apply IHa. assumption.
Qed.

Lemma leb_min_max : forall n m a,
  Nat.leb n m = true ->
  Nat.leb (min a n) (max a m) = true.
Proof.
  intros n m a H. 
  apply (leb_trans _ n).  
    rewrite min_comm.
    apply leb_min_l2. apply leb_refl.

    apply (leb_trans _ m). assumption.
    rewrite max_comm. 
    apply leb_max_suc3. apply leb_refl.
Qed.

Lemma leb_or : forall n m,
  Nat.leb n m = true \/ Nat.leb m n = true.
Proof.
  induction n; intros m.
    left. reflexivity.

    destruct m. right. reflexivity.
    simpl. apply IHn.
Qed.

Lemma FOv_neq_switch : forall xn ym,
  ~ Var xn = Var ym ->
  ~ Var ym = Var xn.
Proof.
  intros xn ym H1 H2.
  inversion H2 as [H2'].
  rewrite H2' in *. 
  contradiction (H1 eq_refl).
Qed.