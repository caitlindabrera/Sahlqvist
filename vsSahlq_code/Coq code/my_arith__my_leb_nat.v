Require Import Modal SecOrder.
Require Import Arith.EqNat Coq.Arith.PeanoNat.
Require Import my_bool.

Lemma leb_defn_suc : forall (n m : nat),
  Nat.leb (S n) (S m) = Nat.leb n m.
Proof.
  intros; simpl in *; reflexivity.
Qed.

Lemma beq_nat_zero : forall (a b : nat),
  beq_nat (a + b) 0 = true -> beq_nat a 0 = true.
Proof.
  intros.
  induction a; simpl in *; try reflexivity;
  try apply IHa; try exact H.
Qed.

Lemma leb_beq_zero : forall (n : nat),
  Nat.leb n 0 = beq_nat n 0.
Proof.
  induction n; simpl in *; try rewrite IHn; try reflexivity.
Qed.


Lemma beq_nat_suc_false : forall (n:nat), (EqNat.beq_nat (n+1) n) = false.
Proof.
  induction n.
    simpl.
    reflexivity.

    simpl.
    exact IHn.
Qed.

(* ------------------------------------------------------ *)

Lemma not_zero : forall n:nat, beq_nat (n + 1) 0 = false.
Proof.
  intros; destruct n; simpl; reflexivity.
Qed.

Lemma plus_zero : forall (n : nat),
  n + 0 = n.
Proof.
  induction n; simpl in *; try rewrite IHn; try reflexivity.
Qed.

Lemma one_suc : forall (n : nat),
  S n = n + 1.
Proof.
  induction n; simpl in *; try rewrite IHn; try reflexivity.
Qed. 

Lemma arith_plus_assoc : forall (a b c : nat),
  a + b + c = a + (b + c).
Proof.
  intros.
  induction a; simpl in *; try rewrite IHa; reflexivity.
Qed.

Lemma arith_plus_comm : forall (a b : nat),
  a + b = b + a.
Proof.
  intros.
  induction a; simpl in *.
    induction b; simpl in *; try rewrite <- IHb; try reflexivity.
      rewrite IHa.
      rewrite one_suc.
      rewrite arith_plus_assoc.
      rewrite <- one_suc.
      reflexivity.
Qed.

Lemma arith_minus_zero : forall (a : nat),
  a - 0 = a.
Proof.
  induction a; simpl; reflexivity.
Qed.

Lemma arith_minus_suc : forall (a b : nat),
  Nat.leb b a = true ->  S (a - b) = S a - b.
Proof.
  induction a.
    induction b.
      simpl; reflexivity.

      intros H.
      simpl in *.
      discriminate.

    induction b.
      simpl in *.
      reflexivity.

      intros H.
      simpl minus at 1.
      rewrite IHa.
        simpl minus at 2.
        case_eq b.
          simpl; reflexivity.

          intros n Hb.
          simpl.
          reflexivity.

        exact H.
Qed.

Lemma arith_plus_3 : forall (a b : nat),
  a + b - a = b.
Proof.
  intros.
  induction a; simpl in *; try exact IHa.
    induction b; simpl in *; try reflexivity.
Qed.

Lemma arith_plus_zero : forall (n m : nat),
  n + m = 0 -> n = 0.
Proof.
  intros.
  induction n; simpl in *; try reflexivity.
    discriminate.
Qed.


Lemma arith_minus_exp_pre : forall (n  m : nat),
  n - (m + 1) = n - m - 1.
Proof.
  induction n.
    intros.
    simpl.
    reflexivity.

    intros.
    induction m.
      simpl.
      reflexivity.

      simpl.
      apply IHn.
Qed.

Lemma arith_minus_exp : forall (i n m : nat),
  n - (m + i) = n - m - i.
Proof.
  induction i.
    intros.
    rewrite plus_zero.
    rewrite arith_minus_zero.
    reflexivity.

    intros n m.
    rewrite one_suc.
    rewrite arith_plus_comm with (a := i).
    rewrite <- arith_plus_assoc.
    rewrite IHi.
    rewrite IHi.
    rewrite arith_minus_exp_pre.
    reflexivity.
Qed.

(* ------------------------------------------------------ *)

Lemma leb_zero : forall (i : nat),
  Nat.leb i 0 = true -> i = 0.
Proof.
  intros i  H.
  induction i.
    reflexivity.
    simpl in H; discriminate.
Qed.  

Lemma leb_suc_r : forall (i j : nat),
  Nat.leb i j = true -> Nat.leb i (S j) = true.
Proof.
  induction i.
    reflexivity.

    induction j.
      intros; simpl in *.
      discriminate.

      intros H.
      apply IHi.
      simpl in H.
      exact H.
Qed.

Lemma leb_suc_l : forall (i n : nat),
  Nat.leb (S i) n = true -> Nat.leb i n = true.
Proof.
  intros i.
  induction i.
    simpl; reflexivity.

    induction n.
      intros H.
      pose proof (leb_zero (S (S i)) H) as Hi.
      discriminate.

      intros H.
      simpl.
      apply IHi.
      exact H.
Qed.

Lemma leb_plus_r : forall (i n m : nat),
  Nat.leb i n = true -> Nat.leb i (n + m) = true.
Proof.
  intros i' n' m.
  generalize n' i'.
  induction m; intros n i H.
    rewrite plus_zero.
    exact H.

    specialize (IHm (n + 1) i).
    rewrite one_suc.
    rewrite arith_plus_comm with (a := m).
    rewrite <- arith_plus_assoc.
    apply IHm.
    rewrite <- one_suc.
    apply leb_suc_r.
    exact H.
Qed.

Lemma leb_plus_l : forall (n m : nat),
  Nat.leb (n + m) n = Nat.leb m 0.
Proof.
  intros.
  induction n; simpl in *; try rewrite IHn; reflexivity.
Qed.

Lemma leb_plus_gen : forall (i j n m : nat),
  Nat.leb i j = true -> Nat.leb n m = true ->
    Nat.leb (i + n) (j + m) = true.
Proof.
  intros i.
  induction i.
    intros j.
    induction j.
      intros n m H1 H2.
      simpl in *.
      exact H2.

      intros n m H1 H2.
      simpl in *.
      rewrite one_suc.
      rewrite arith_plus_comm with (a := j).
      rewrite arith_plus_assoc.
      apply leb_plus_r.
      exact H2.

    intros j.
    induction j.
      intros n m H1 H2.
      simpl in *.
      discriminate.

      intros n m H1 H2.
      simpl in *.
      apply IHi.
      exact H1.
      exact H2.
Qed.


Lemma leb_refl : forall (n : nat),
  Nat.leb n n = true.
Proof.
  induction n; simpl; try reflexivity; try exact IHn.
Qed.

Lemma leb_plus_pre : forall (i n m : nat),
  Nat.leb i n = Nat.leb (m+i) (m+n).
Proof.
  induction m; simpl in *.
    reflexivity.

    exact IHm.
Qed.

Lemma leb_plus : forall (i n m : nat),
  Nat.leb i n = Nat.leb (i+m) (n+m).
Proof.
  intros.
  rewrite arith_plus_comm.
  rewrite (arith_plus_comm n m).
  rewrite <- leb_plus_pre.
  reflexivity.
Qed.

(* ------------------------------------------------------ *)

Lemma arith_plus_minus_assoc : forall (a b c : nat),
  Nat.leb b a = true -> 
    Nat.leb c b = true -> a - b + c = a - (b - c).
Proof.
  induction b.
    intros c H1 H2.
    simpl.
    rewrite arith_minus_zero.
    case_eq c.
      rewrite plus_zero; reflexivity.

      intros n Hc; rewrite Hc in *; discriminate.

    intros c H1 H2.
    case_eq a.
      simpl.
      intros Ha; rewrite Ha in *.
      simpl in H1; discriminate.

      intros n Ha.
      rewrite Ha in *.
      case_eq c.
        simpl.
        rewrite plus_zero.
        reflexivity.

        intros m Hc.
        rewrite Hc in *.
        simpl minus at 1.
        simpl minus at 3.
        rewrite <- IHb.
        rewrite <- arith_minus_suc.
        simpl.
        rewrite one_suc.
        rewrite one_suc with (n:= n - b + m).
        rewrite <- arith_plus_assoc.
        reflexivity.

        exact H1.

        rewrite one_suc.
        rewrite leb_plus_r.
          reflexivity.

          exact H1.

          exact H2.
Qed.

Lemma arith_minus_comm : forall (n m i : nat),
  n - m - i = n - i - m.
Proof.
  intros.
  rewrite <- arith_minus_exp.
  rewrite arith_plus_comm.
  rewrite arith_minus_exp.
  reflexivity.
Qed.

Lemma leb_minus_pre : forall (n m : nat),
  Nat.leb n m = true -> Nat.leb (n-1) (m-1) = true.
Proof.
  intros n m Hleb.
  induction n.
    induction m.
      simpl; reflexivity.

      simpl in *; reflexivity.

    induction m.
      simpl in *; discriminate.

      simpl in *.
      do 2 rewrite arith_minus_zero.
      assumption.
Qed.

Lemma leb_minus : forall (i n m : nat),
  Nat.leb n m = true -> Nat.leb (n-i) (m-i) = true.
Proof.
  induction i.
    intros.
    do 2 rewrite arith_minus_zero; assumption.

    intros n m Hleb.
    rewrite one_suc.
    rewrite arith_plus_comm.
    do 2 rewrite arith_minus_exp.
    apply IHi.
    apply leb_minus_pre.
    assumption.
Qed.

Lemma beq_nat_0 : forall (n m : nat),
  n + m = 0 -> (n = 0 /\ m = 0).
Proof.
  intros n m Hplus.
  induction n; apply conj.
    reflexivity.
    simpl in *; assumption.
    simpl in Hplus; inversion Hplus.
    simpl in Hplus; inversion Hplus.
Qed.


Lemma leb_notswitch : forall (n m : nat),
  Nat.leb n m = true -> Nat.leb (m + 1) n = false.
Proof.
  intros n.
  induction n.
    intros.
    rewrite <- one_suc.
    simpl.
    reflexivity.

    intros m Hleb.
    rewrite <- one_suc.
    simpl.
    case_eq m.
      intros Heq.
      rewrite Heq in *.
      simpl in *.
      discriminate.

      intros a Heq.
      rewrite one_suc.
      apply IHn.
      rewrite Heq in Hleb.
      apply Hleb.
Qed.

Lemma leb_suc_f : forall (n :nat),
  Nat.leb (S n) n = false.
Proof.
  intros.
  induction n; simpl in *.
    reflexivity.

    assumption.
Qed.

Lemma arith_plus_4 : forall (n : nat),
  Nat.leb 1 n = true -> (1 + (n - 1)) = n.
Proof.
  intros n Hleb.
  induction n.
    simpl in *; discriminate.

    simpl; rewrite arith_minus_zero; 
    reflexivity. 
Qed.

Lemma leb_ex : forall (n m : nat),
  Nat.leb n m = true -> exists (i : nat), n + i = m.
Proof.
  intros.
  induction n.
    exists m; simpl; reflexivity.

    simpl in H.
    destruct m.
      discriminate.

      assert (Nat.leb n m = true) as H'.
        assumption.
      apply leb_plus_r with (m := 1) in H.
      rewrite one_suc in IHn.
      specialize (IHn H).
      destruct IHn as [i Hi].
      rewrite <- one_suc in Hi. 
      rewrite <- Hi.
      rewrite one_suc.
      case_eq (beq_nat i 0); intros Hbeq.
        remember i as t.
        rewrite (beq_nat_true t 0 Hbeq) in *.
        rewrite plus_zero in Hi.
        rewrite Hi in H'.
        rewrite leb_suc_f in H'; discriminate.

        exists (i-1).
        rewrite arith_plus_assoc. 
        rewrite arith_plus_4.
          reflexivity.

          case_eq i.
            intros Heq.
            rewrite Heq in *.
            simpl in Hbeq; discriminate.

            intros a Heq.
            simpl; reflexivity.
Qed.

Lemma beq_nat_leb : forall (n m : nat),
  beq_nat (n - m) 0 = true -> Nat.leb n m = true.
Proof.
  intros n0 m.
  generalize n0; induction m.
    intros n  Hbeq.
    rewrite arith_minus_zero in *.
    induction n.
      simpl; reflexivity.

      simpl in Hbeq; discriminate.

    intros n Hbeq.
    induction n.
      simpl; reflexivity.

      simpl; apply IHm.
      simpl in *.
      assumption.
Qed.

Lemma arith_plus_minus_assoc3 : forall (b c : nat),
  Nat.leb c b = true ->
    1 + (b - c) = 1 + b - c.
Proof.
  induction b.
    intros c H.
    case_eq c.
      simpl; reflexivity.

      intros n Hc.
      rewrite Hc in H. 
      simpl in *; discriminate.

    intros c H.
    case_eq c.
      intros Hc.
      simpl; reflexivity. 

      intros n Hc.
      simpl.
      rewrite one_suc.
      rewrite arith_plus_comm.
      rewrite IHb.
      case_eq n.
        simpl; reflexivity. 

        intros m Hn.
        simpl.
        reflexivity.

        rewrite Hc in H.
        simpl in *; assumption.
Qed.

Lemma arith_plus_minus_assoc2 : forall (a b c : nat),
  Nat.leb c b = true ->
    a + (b - c) = a + b - c.
Proof.
  intros a b c H.
  induction a.
    simpl; reflexivity.

    rewrite one_suc.
    rewrite arith_plus_comm with (a:= a).
    rewrite arith_plus_assoc.
    rewrite IHa.
    rewrite arith_plus_minus_assoc3.
      rewrite arith_plus_assoc.
      reflexivity.

      rewrite arith_plus_comm.
      apply leb_plus_r.
      assumption.
Qed.

Lemma arith_plus_minus_assoc4 : forall (c a b :nat),
  Nat.leb b a = true ->
    a - b + c = a + c - b.
Proof.
  induction c.
  intros.
    do 2 rewrite plus_zero.
    reflexivity.

    intros a b H.
    rewrite one_suc.
    rewrite arith_plus_comm with (a := c).
    rewrite <- arith_plus_assoc with(a :=a).
    rewrite <- IHc.
    rewrite <- one_suc.
    rewrite <- arith_minus_suc.
    rewrite one_suc with (n := a - b).
    rewrite arith_plus_assoc.
    reflexivity.

    assumption.
    apply leb_plus_r.
    assumption.
Qed.

Lemma leb_plus_minus : forall (n a b c d : nat),
  Nat.leb n (a - c) = true ->
    Nat.leb c a = true ->
      Nat.leb d b = true ->
        Nat.leb n (a + b - ( c + d)) = true.
Proof.
  intros n a b c d H1 H2 H3.
  rewrite arith_minus_exp.
  apply leb_plus_r with (m:= (b-d)) in H1.
  rewrite arith_plus_minus_assoc2 in H1.
    rewrite <- arith_plus_minus_assoc4; assumption.

    assumption.
Qed.

Lemma leb_plus_minus2 : forall (n a b c d : nat),
  Nat.leb n (a + b - (c + d)) = true ->
    Nat.leb c a = true ->
      Nat.leb d b = true ->
        Nat.leb n ((a - c) + (b - d)) = true.
Proof.
  intros n a b c d H1 H2 H3;
  rewrite arith_minus_exp in H1;
  rewrite arith_plus_comm in H1;
  rewrite <- arith_plus_minus_assoc2 in H1;
    rewrite arith_plus_comm in H1.
    rewrite <- arith_plus_minus_assoc2 in H1;
      assumption.
      assumption.
Qed.

Lemma leb_switch : forall (a b : nat),
  Nat.leb a b = false -> Nat.leb b a = true.
Proof.
  double induction a b.
    simpl; intros; discriminate.

    intros n H1 H2.
    simpl in *.
    discriminate.

    intros n H1 H2.
    simpl in *.
    reflexivity.

    intros n H1 m H2 H3.
    simpl.
    simpl in *.
    apply H2.
    apply H3.
Qed.

Lemma arith_minus_plus : forall (a b : nat),
  Nat.leb b a = true ->
    a - b + b = a.
Proof.
  induction a.
    intros b H.
    rewrite leb_beq_zero in H.
    simpl.
    apply beq_nat_true.
    assumption.

    intros b H2.
    simpl.
    case_eq b.
      intros Hb.
      rewrite plus_zero.
      reflexivity.

      intros n Hb.
      rewrite Hb in *.
      simpl in *.
      rewrite one_suc.
      rewrite one_suc with (n := a).
      rewrite <- arith_plus_assoc.
      rewrite IHa.
        reflexivity.

      assumption.
Qed.

Lemma arith_minus_refl : forall (n : nat),
  n - n = 0.
Proof.
  induction n;
    simpl.
    reflexivity.
    assumption.
Qed.

Lemma leb_trans : forall (i j k : nat),
  Nat.leb i j = true ->
    Nat.leb j k = true ->
      Nat.leb i k = true.
Proof.
  induction i.
    intros; reflexivity.

    intros j k H1 H2.
    simpl.
    case_eq k.
      intros Hk.
      rewrite Hk in *.
      rewrite leb_beq_zero in H2.
      rewrite (beq_nat_true _ _ H2) in H1.
      simpl in H1.
      discriminate.

      intros n Hk.
      case_eq j.
        intros Hj.
        rewrite Hj in H1; simpl in *; discriminate.

        intros m Hj.
        rewrite Hj in *.
        simpl in *.
        rewrite Hk in *.
        apply IHi with (j := m);
          assumption.
Qed.


Lemma beq_nat_comm : forall (n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
  intros.
  case_eq (beq_nat n m); intros Hbeq.
    rewrite (beq_nat_true n m Hbeq).
    apply beq_nat_refl.

    case_eq (beq_nat m n); intros Hbeq2.
      rewrite (beq_nat_true m n Hbeq2) in Hbeq.
      rewrite <- beq_nat_refl in Hbeq.
      discriminate.

      reflexivity.
Qed.


Lemma beq_nat_comm_t : forall (n m : nat),
  beq_nat n m = true -> beq_nat m n = true.
Proof.
  intros n m H.
  rewrite beq_nat_comm in H; assumption.
Qed.

Lemma beq_nat_comm_f : forall (n m : nat),
  beq_nat n m = false -> beq_nat m n = false.
Proof.
  intros n m H.
  rewrite beq_nat_comm in H; assumption.
Qed.


Lemma leb_suc : forall (n m a : nat),
  Nat.leb (S n) (m - a) = true ->
    Nat.leb n (m - S a) = true.
Proof.
  intros n m a H.
  rewrite one_suc.
  rewrite arith_minus_exp.
  apply leb_minus with (i := 1) in H.
  simpl in H.
  rewrite arith_minus_zero in H.
  assumption.
Qed.

Lemma arith_plus_minus : forall (a b c :nat),
  a + b = c -> a = c - b.
Proof.
  induction a;
    intros b c H.
    simpl in *; rewrite H.
    rewrite arith_minus_refl.
    reflexivity.

    rewrite one_suc in H.
    rewrite arith_plus_assoc in H.
    rewrite arith_plus_comm with (a := 1) in H.
    rewrite <- arith_plus_assoc in H.
    rewrite <- one_suc in H.
    case_eq c.
      intros Hc; rewrite Hc in *.
      discriminate.

      intros n Hc.
      rewrite Hc in H.
      inversion H as [H1].
      rewrite (IHa b n).
        rewrite arith_plus_minus_assoc.
        rewrite arith_minus_refl.
        rewrite arith_minus_zero.
        rewrite <- H1.
        rewrite arith_plus_comm.
        rewrite arith_plus_3.
        rewrite arith_plus_comm.
        rewrite (one_suc (a+b)).
        rewrite arith_plus_assoc.
        rewrite (arith_plus_comm b 1).
        rewrite <- arith_plus_assoc.
        rewrite <- one_suc.
        rewrite arith_plus_comm.
        rewrite arith_plus_3.
          reflexivity.

          rewrite <- H1.
          rewrite arith_plus_comm.
          apply leb_plus_r.
          apply leb_refl.

          apply leb_refl.

          assumption.
Qed.

Lemma leb_suc2 : forall (a b : nat),
  Nat.leb a (S b) = true ->
    Nat.leb a b = true \/ a = S b.
Proof.
  induction a;
    intros b H.
    left; simpl; reflexivity.

    simpl in *.
    case_eq b.
      intros Hb.
      rewrite Hb in *.
      rewrite (leb_beq_zero _) in H.
      rewrite (beq_nat_true _ _  H).
      right; reflexivity.

      intros n Hb.
      rewrite Hb in H.
      destruct (IHa n H) as [H2 | H2].
        left; assumption.

        right.
        rewrite H2.
        reflexivity.
Qed.

Lemma leb_pairs : forall (a b c d : nat),
  Nat.leb c a = true ->
    Nat.leb d b = true ->
      a + b - (c + d) = (a - c) + (b - d).
Proof.
  induction a;
    intros b c d H1 H2. simpl.
    rewrite leb_beq_zero in H1.
    rewrite (beq_nat_true _ _ H1).
    simpl; reflexivity.

    rewrite one_suc.
    case_eq (Nat.leb c a); intros Hleb.
      rewrite <- arith_plus_minus_assoc4 with (a := a); try assumption.
      rewrite arith_plus_assoc with (c := (b-d)).
      rewrite arith_plus_comm with (a := 1) (b := (b-d)).
      rewrite <- arith_plus_assoc.
      rewrite <- IHa; try assumption.
      rewrite arith_plus_assoc.
      rewrite arith_plus_comm with ( a := 1).
      rewrite <- arith_plus_assoc.
      rewrite arith_plus_minus_assoc4.
      reflexivity.
      apply leb_plus_gen; assumption.

      apply leb_suc2 in H1.
      destruct H1 as [Hl | Hr].
        rewrite Hl in *; discriminate.

        rewrite Hr.
        rewrite <- one_suc at 2; simpl.
        rewrite arith_minus_refl; simpl.
        rewrite arith_plus_assoc.
        rewrite (arith_plus_comm 1 b).
        rewrite <- arith_plus_assoc.
        rewrite <- one_suc.
        simpl.
        rewrite arith_minus_exp.
        rewrite arith_plus_3.
        reflexivity.
Qed.

Lemma leb_minus_zero : forall a b : nat,
  Nat.leb b a = true ->
    a - b = 0 ->
      a = b.
Proof.
  intros a.
  induction a.
    intros  b H1 H2.
    rewrite leb_beq_zero in H1.
    rewrite (beq_nat_true _ _ H1).
    reflexivity.

    intros  b H1 H2.
    simpl in H2.
    case_eq b.
      intros H.
      rewrite H in H2.
      assumption.

      intros n H.
      rewrite H in *.
      rewrite IHa with (b:= n).
        reflexivity.

        simpl in *; assumption.

        assumption.
Qed.

Lemma arith_minus_exp3 : forall (a b : nat),
  Nat.leb b a = true ->
    Nat.leb 1 b = true ->
      a - (b - 1) = a - b + 1.
Proof.
  intros a b H1 H2.
  induction b.
    simpl in H2; discriminate.

    simpl.
    rewrite arith_minus_zero.
    rewrite one_suc.
    rewrite arith_minus_exp.
    rewrite arith_minus_plus.
      reflexivity.

      case_eq b.
        intros Hb.
        rewrite Hb in *.
        rewrite arith_minus_zero.
        assumption.

        intros n Hb.
        apply leb_minus with (i := S n) in H1.
        rewrite <- Hb in H1.
        rewrite one_suc in H1.
        rewrite arith_plus_3 in H1.
        rewrite <- Hb.
        assumption.
Qed.

Lemma arith_minus_exp2 : forall (c a b : nat),
  Nat.leb b a = true ->
    Nat.leb c b = true ->
      a - (b - c) = a - b + c.
Proof.
  intros c.
  induction c.
    intros a b H1 H2.
    rewrite arith_minus_zero.
    rewrite plus_zero.
    reflexivity.

    intros a b H1 H2.
    rewrite one_suc.
    rewrite arith_plus_comm.
    rewrite arith_minus_exp.
    rewrite IHc.
      rewrite <- arith_plus_assoc.
      rewrite arith_minus_exp3.
        reflexivity.

        assumption.
        case_eq b.
          intros Hb; rewrite Hb in *; simpl in *; discriminate.

          intros n Hb; simpl; reflexivity.

        case_eq b.
          intros Hb; simpl; reflexivity.

          intros n Hb.
          simpl.
          rewrite arith_minus_zero.
          rewrite leb_suc_l.
            reflexivity.

            rewrite <-Hb.
            assumption.

            apply leb_minus_pre in H2.
            simpl in H2.
            rewrite arith_minus_zero in H2; assumption.
Qed.


Lemma arith_minus_suc3 : forall (n m : nat),
  S n - S m = n - m.
Proof.
  simpl; reflexivity.
Qed.

Lemma leb_suc3 : forall (n m a : nat),
  Nat.leb (S n) (S m - a) = true ->
    Nat.leb a m = true ->
      Nat.leb n (m - a) = true.
Proof.
  intros n m a H1 H2. 
  induction a.
    rewrite arith_minus_zero in *.
    apply H1.

    rewrite one_suc.
    rewrite arith_minus_exp.
    assert (n = S n - 1) as H.
      simpl; rewrite arith_minus_zero;
      reflexivity.
    rewrite H.
    apply leb_minus_pre.
    simpl in *.
    assumption.
Qed.


Lemma leb_minus_rev : forall (i n : nat),
  Nat.leb i n = false ->
    Nat.leb (i - n) 0 = false.
Proof.
  induction i.
    intros n Hleb.
    simpl in Hleb; discriminate.

    intros n Hleb.
    simpl.
    case_eq n.
      intros Hn.
      simpl.
      reflexivity.

      intros m Hn.
      apply IHi.
      rewrite Hn in Hleb.
      simpl in Hleb.
      assumption.
Qed.


Lemma arith_plus_minus3 : forall (c a b : nat),
  Nat.leb c b = true ->
    (a + b) - c - (b - c) = a.
Proof.
  induction c;
    intros a b H.
    do 2 rewrite arith_minus_zero.
    rewrite arith_plus_comm.
    rewrite arith_plus_3.
    reflexivity.

    rewrite one_suc.
    rewrite (arith_plus_comm c 1).
    do 2 rewrite arith_minus_exp.
    rewrite <- arith_plus_minus_assoc2.
      rewrite IHc.
        reflexivity.

        apply leb_minus with (i := 1) in H.
        simpl in H.
        rewrite arith_minus_zero in H.
        assumption.

      case_eq b.
        intros Hb; rewrite Hb in *;
        simpl in *; discriminate.

        intros d Hb.
        simpl; reflexivity.
Qed.


Lemma not_beq_nat : forall (n : nat),
  ~(n = 0) -> beq_nat n 0 = false.
Proof.
  intros n H.
  unfold not in H.
  case_eq (beq_nat n 0); intros Hbeq.
    rewrite (beq_nat_true _ _ Hbeq) in *.
    specialize (H (eq_refl _)); contradiction.

    reflexivity.
Qed.


Lemma beq_nat_leb_f : forall (n m : nat),
  beq_nat (n - m) 0 = false -> Nat.leb m n = true.
Proof.
  intros n0 m.
  generalize n0; induction m.
    intros n  Hbeq.
    rewrite arith_minus_zero in *.
    induction n.
      simpl; reflexivity.

      simpl in Hbeq; reflexivity.

    intros n Hbeq.
    induction n.
      simpl in *; discriminate.

      simpl; apply IHm.
      simpl in *.
      assumption.
Qed.


Lemma eq_plus_zero : forall a b : nat,
  a + b = 0 -> a = 0.
Proof.
  induction a.
    reflexivity.

    intros b H.
    simpl in H.
    discriminate.
Qed.

Lemma arith_plus_minus_rearr : forall a b c d : nat,
  Nat.leb c a = true ->
    Nat.leb d b = true ->
      a + b - (c + d) = a - c + (b - d).
Proof.
  intros a b c d H1 H2.
  rewrite arith_minus_exp.
  rewrite <- (arith_plus_minus_assoc4 b a).
  rewrite (arith_plus_minus_assoc2 (a-c) b d).
    reflexivity.
    assumption.
    assumption.
Qed.

Lemma arith_minus_not_zero : forall (a b n : nat),
  a - b = S n -> ~ a = 0.
Proof.
  intros a b n H.
  induction a.
    simpl in *.
    discriminate.

    unfold not.
    intros H1.
    discriminate.
Qed.


Lemma leb_close : forall (c b :nat),
Nat.leb 1 ((b+1) - c) = true ->
  Nat.leb 1 (b - c) = true \/ b = c.
Proof.
  intros c.
  induction c.
    intros b Hleb.
    rewrite arith_minus_zero in *.
    destruct b.
      right; reflexivity.

      simpl; left; reflexivity.

    intros b Hleb.
    rewrite <- one_suc in Hleb.
    simpl  minus in Hleb.
    case_eq b.
      intros Hb.
      rewrite Hb in Hleb.
      simpl in *; discriminate.

      intros n Hb.
      rewrite Hb in Hleb.
      rewrite (one_suc n) in Hleb.
      simpl minus.
      specialize (IHc n Hleb).
      destruct IHc.
        left; assumption.

        right; rewrite H; reflexivity.
Qed.


Lemma arith_minus_suc2 : forall ( a b n : nat),
  a - b = S n -> a - (S b) = n.
Proof.
  intros a.
  induction a.
    intros b n H.
    simpl in *.
    inversion H.

    intros b n H.
    simpl in *.
    destruct b.
      inversion H.
      rewrite arith_minus_zero.
      reflexivity.

      apply IHa; assumption.
Qed.



Lemma leb_switch2 : forall (a b : nat),
  Nat.leb a b = true ->
    beq_nat a b = false ->
      Nat.leb b a = false.
Proof.
  double induction a b.
    simpl; intros; discriminate.

    intros n H1 H2.
    simpl in *; reflexivity.

    intros n H1 H2.
    simpl in *; discriminate.

    intros n H1 m H2 H3.
    simpl.
    simpl in *.
    apply H2.
    apply H3.
Qed.

Lemma leb_switch_t : forall a b : nat,
  Nat.leb a b = true ->
  beq_nat a b = true \/ Nat.leb b a = false.
Proof.
  induction a; intros b H.
    case_eq b.
      intros Hb; left; reflexivity.

      intros c Hb; right; reflexivity.

    case_eq b.
      intros Hb; rewrite Hb in *.
      simpl in H; discriminate.

      intros c Hb; rewrite Hb in *.
    specialize (IHa c).
    apply leb_minus with (i := 1) in H.
    simpl in H.
    do 2 rewrite arith_minus_zero in H.
    specialize (IHa H).
    destruct IHa as [H1 | H2].
      simpl; left; assumption.

      simpl; right; assumption.
Qed.


Lemma beq_nat_zero_minus : forall i j : nat,
  beq_nat (i - j) 0 = false ->
    beq_nat i 0 = false.
Proof.
  intros i j H.
  rewrite <- leb_beq_zero in H.
  rewrite <- leb_beq_zero.
  apply (contrapos_bool_tt _ _ (leb_minus j _ _ )).
  simpl; assumption.
Qed.


Lemma beq_nat_zero_f : forall n m : nat,
  beq_nat n 0 = false ->
    beq_nat (n + m) 0 = false.
Proof.
  intros n m H; induction m.
    rewrite plus_zero; assumption.

    rewrite one_suc.
    rewrite <- arith_plus_assoc.
    rewrite <- one_suc; simpl.
    reflexivity.
Qed.

Lemma eq_nat_zero : forall a b : nat,
  a + b = 0 -> a = 0.
Proof.
  induction a.
    reflexivity.

    intros b H.
    simpl in *.
    discriminate.
Qed.


Lemma arith_plus_suc : forall a b : nat,
  a + (S b) = S (a + b).
Proof.
  induction a; intros b.
    reflexivity.

    simpl in *.
    rewrite IHa.
    reflexivity.
Qed.

Lemma neq_beq_nat : forall Pn Qm : nat,
  ~ (Pred Pn) = (Pred Qm) ->
  beq_nat Pn Qm = false.
Proof.
  intros Pn Qm H.
  case_eq (beq_nat Pn Qm); intros Hbeq.
    rewrite (beq_nat_true _ _ Hbeq) in H.
    contradiction (H eq_refl).

    reflexivity.
Qed.
