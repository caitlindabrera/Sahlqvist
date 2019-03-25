Require Import pv_in.
Require Import PeanoNat Compare_dec Lia.

Definition occ_in_modal (phi : Modal) (i : nat) : Prop :=
i <> 0 /\ le i (length (pv_in phi)).

Lemma occ_in_modal_le : forall (phi : Modal) (i : nat),
  occ_in_modal phi i ->
    le i (length (pv_in phi)).
Proof. intros phi i [Hneq Hle]. assumption. Qed.

Lemma occ_in_modal_0 : forall (phi : Modal) (i : nat),
  occ_in_modal phi i -> i <> 0.
Proof.  intros phi i [Hneq Hleb]. assumption. Qed.

Lemma occ_in_modal_f : forall phi i,
    ~ occ_in_modal phi i -> (i = 0 \/ i > length (pv_in phi)).
Proof.
  intros phi i H.
  unfold gt. 
  destruct (Nat.eq_dec i 0) as [H2 | H2]. auto.
  destruct (lt_dec (length (pv_in phi)) i) as [?|H3]. auto.
  apply Nat.nlt_ge in H3. firstorder. 
Qed.

Lemma occ_in_modal_leb3 : forall (phi : Modal) (n : nat),
  n <> 0 -> le n (length (pv_in phi)) -> occ_in_modal phi n.
Proof. intros; constructor; assumption. Qed.

Lemma occ_in_modal_leb2 : forall (phi : Modal) (n : nat),
  occ_in_modal phi n -> (n <> 0 /\ le n (length (pv_in phi))).
Proof. intros phi n [Hneq Hleb]. auto. Qed.

Lemma occ_in_modal_mconj_l : forall (phi1 phi2 : Modal) (i : nat),
  occ_in_modal phi1 i -> 
    occ_in_modal (mconj phi1 phi2) i.
Proof.
  intros phi1 phi2 i [H1 H2]. constructor. assumption.
  simpl. rewrite app_length. lia.
Qed.

Lemma occ_in_modal_mdisj_l : forall (phi1 phi2 : Modal) (i : nat),
  occ_in_modal phi1 i -> 
    occ_in_modal (mdisj phi1 phi2) i.
Proof.
  intros phi1 phi2 i [H1 H2]. constructor. assumption.
  simpl. rewrite app_length. lia. 
Qed.

Lemma occ_in_modal_mimpl_l : forall (phi1 phi2 : Modal) (i : nat),
  occ_in_modal phi1 i -> 
    occ_in_modal (mimpl phi1 phi2) i.
Proof.
  intros phi1 phi2 i [H1 H2]. constructor. assumption.
  simpl. rewrite app_length. lia. 
Qed.

Lemma occ_in_modal_mconj_r : forall (phi1 phi2 : Modal) (i : nat),
  occ_in_modal phi2 i -> 
    occ_in_modal (mconj phi1 phi2) (length (pv_in phi1) + i).
Proof.
  intros phi1 phi2 i [Hneq Hleb]. constructor.
  intros H. destruct i; firstorder.
  simpl. rewrite app_length. lia.
Qed.

Lemma occ_in_modal_mdisj_r : forall (phi1 phi2 : Modal) (i : nat),
  occ_in_modal phi2 i -> 
    occ_in_modal (mdisj phi1 phi2) (length (pv_in phi1) + i).
Proof.
  intros phi1 phi2 i [Hneq Hleb]. constructor.
  intros H. destruct i; firstorder.
  simpl. rewrite app_length. lia.
Qed.

Lemma occ_in_modal_mimpl_r : forall (phi1 phi2 : Modal) (i : nat),
  occ_in_modal phi2 i -> 
    occ_in_modal (mimpl phi1 phi2) (length (pv_in phi1) + i).
Proof.
  intros phi1 phi2 i [Hneq Hleb]. constructor.
  intros H. destruct i; firstorder.
  simpl. rewrite app_length. lia.
Qed.

Lemma occ_in_modal_mconj : forall (phi1 phi2 : Modal) (i : nat),
  occ_in_modal (mconj phi1 phi2) i ->
    ~ occ_in_modal phi1 i ->
      occ_in_modal phi2 (i - length (pv_in phi1)).
Proof. 
  intros phi1 phi2 i [Heq1 Hleb1] H. constructor.
  apply occ_in_modal_f in H. destruct H as [H | H].
  contradiction. lia. simpl in Hleb1. 
  rewrite app_length in Hleb1. lia.
Qed.

Lemma occ_in_modal_mdisj : forall (phi1 phi2 : Modal) (i : nat),
  occ_in_modal (mdisj phi1 phi2) i ->
    ~ occ_in_modal phi1 i ->
      occ_in_modal phi2 (i - length (pv_in phi1)).
Proof. 
  intros phi1 phi2 i [Heq1 Hleb1] H. constructor.
  apply occ_in_modal_f in H. destruct H as [H | H].
  contradiction. lia. simpl in Hleb1. 
  rewrite app_length in Hleb1. lia.
Qed.

Lemma occ_in_modal_mimpl : forall (phi1 phi2 : Modal) (i : nat),
  occ_in_modal (mimpl phi1 phi2) i ->
    ~occ_in_modal phi1 i ->
      occ_in_modal phi2 (i - length (pv_in phi1)).
Proof. 
  intros phi1 phi2 i [Heq1 Hleb1] H. constructor.
  apply occ_in_modal_f in H. destruct H as [H | H].
  contradiction. lia. simpl in Hleb1. 
  rewrite app_length in Hleb1. lia.
Qed.

Lemma occ_in_modal_mneg : forall (phi : Modal) (i : nat),
  occ_in_modal (mneg phi) i <->
    occ_in_modal phi i.
Proof.
  intros phi i. split; intros [Heq Hleb]; constructor; auto.
Qed.

Lemma occ_in_modal_box : forall (phi : Modal) (i : nat),
  occ_in_modal (box phi) i <->
    occ_in_modal phi i.
Proof.
  intros phi i. split; intros [Heq Hleb]; constructor; auto.
Qed.

Lemma occ_in_modal_diam : forall (phi : Modal) (i : nat),
  occ_in_modal (diam phi) i <->
    occ_in_modal phi i.
Proof.
  intros phi i. split; intros [Heq Hleb]; constructor; auto.
Qed.

Lemma occ_in_modal_atom : forall (p : propvar) (i : nat),
  occ_in_modal (atom p) i -> i = 1.
Proof.
  intros p i [Heq Hleb]. simpl in *. firstorder.
Qed.

Lemma occ_in_modal_leb_minus : forall phi n m,
    occ_in_modal phi (n - m) -> n <=? m = false.
Proof.
  intros phi n m [H1 H2].
  apply Compare_dec.leb_iff_conv. firstorder.
Qed.

Lemma occ_in_modal_atom2 : forall p,
    occ_in_modal #p 1.
Proof.  intros p. constructor; auto. Qed.

Lemma if_then_else_f_t_t_f: forall (a : bool),
    (if a then false else true) = true -> a = false.
Proof. intros a. destruct a; auto. Qed.

Lemma occ_in_modal_mconj_r2 : forall phi1 phi2 i,
    occ_in_modal phi2 (i - length (pv_in phi1)) ->
    occ_in_modal (phi1 m∧ phi2) i.
Proof.
  intros phi1 phi2 i [H1 H2].
  constructor. destruct i; auto.
  simpl. rewrite app_length.
  rewrite  Nat.add_comm.
  apply Nat.le_sub_le_add_r. assumption.
Qed.

Lemma occ_in_modal_mdisj_r2 : forall phi1 phi2 i,
    occ_in_modal phi2 (i - length (pv_in phi1)) ->
    occ_in_modal (phi1 m∨ phi2) i.
Proof.
  intros phi1 phi2 i [H1 H2].
  constructor. destruct i; auto.
  simpl. rewrite app_length.
  rewrite  Nat.add_comm.
  apply Nat.le_sub_le_add_r. assumption.
Qed.

Lemma occ_in_modal_mimpl_r2 : forall phi1 phi2 i,
    occ_in_modal phi2 (i - length (pv_in phi1)) ->
    occ_in_modal (phi1 m→ phi2) i.
Proof.
  intros phi1 phi2 i [H1 H2].
  constructor. destruct i; auto.
  simpl. rewrite app_length.
  rewrite  Nat.add_comm.
  apply Nat.le_sub_le_add_r. assumption.
Qed.

Lemma occ_in_modal_dec : forall phi i,
    {occ_in_modal phi i} + {~ occ_in_modal phi i}.
Proof.
  induction phi; intros i;
    try   (destruct (IHphi i) as [IH | IH]; firstorder).

  destruct i. right. intros H. inversion H; contradiction.
  destruct i. left. constructor; auto.
  right. intros H. inversion H as [? H1].
  simpl in *. inversion H1 as [ | H3 H2]. inversion H2.

  destruct (IHphi1 i) as [IH1 | IH1].
  left. apply occ_in_modal_mconj_l. auto.
  destruct (IHphi2 (i - length (pv_in phi1))) as [IH2 | IH2].
  assert ( i = ( (length (pv_in phi1)) + (i - length (pv_in phi1)))) as Hass.
    firstorder.
  left. rewrite Hass. apply occ_in_modal_mconj_r. auto.
  right. intros H. apply occ_in_modal_mconj in H; auto.

  destruct (IHphi1 i) as [IH1 | IH1].
  left. apply occ_in_modal_mdisj_l. auto.
  destruct (IHphi2 (i - length (pv_in phi1))) as [IH2 | IH2].
  assert ( i = ( (length (pv_in phi1)) + (i - length (pv_in phi1)))) as Hass.
    firstorder.
  left. rewrite Hass. apply occ_in_modal_mdisj_r. auto.
  right. intros H. apply occ_in_modal_mdisj in H; auto.

  destruct (IHphi1 i) as [IH1 | IH1].
  left. apply occ_in_modal_mimpl_l. auto.
  destruct (IHphi2 (i - length (pv_in phi1))) as [IH2 | IH2].
  assert ( i = ( (length (pv_in phi1)) + (i - length (pv_in phi1)))) as Hass.
    firstorder.
  left. rewrite Hass. apply occ_in_modal_mimpl_r. auto.
  right. intros H. apply occ_in_modal_mimpl in H; auto.
Qed.