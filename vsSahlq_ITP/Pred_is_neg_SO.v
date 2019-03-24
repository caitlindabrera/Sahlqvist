Require Import occ_in_SO at_pred Pred_in_SO is_pos_neg_lemmas is_pos_neg_SO_lemmas.
Require Import Modal_syntax p_is_neg ST.
Require Import Compare_dec.

Definition Pred_is_neg_SO (alpha : SecOrder) (P : predicate) : Prop :=
 Pred_in_SO alpha P /\
 (forall i : nat, occ_in_SO alpha i -> P = at_pred (preds_in alpha) i -> is_neg_SO alpha i).


(*
Inductive Pred_is_neg_SO (alpha : SecOrder) (P : predicate) : Prop :=
| Pred_is_neg_y : Pred_in_SO alpha P  ->
    (forall i : nat, occ_in_SO alpha i -> P = at_pred (preds_in alpha) i -> is_neg_SO alpha i) -> Pred_is_neg_SO alpha P.
*)
Lemma P_is_neg_occ : forall (alpha : SecOrder) (P : predicate),
  Pred_is_neg_SO alpha P -> Pred_in_SO alpha P.
Proof. firstorder. Qed.

Lemma Pred_is_neg_SO_not_predSO : forall Q x,
~ Pred_is_neg_SO ($ Q x) Q.
Proof.
  intros Q x [H1 H2].
  assert (occ_in_SO ($ Q x) 1) as Hass.
    firstorder.
    specialize (H2 1 Hass eq_refl). destruct H2; firstorder.
Qed.

Lemma Pred_is_neg_SO_allFO  : forall (alpha : SecOrder) (x : FOvariable) (P : predicate),
  Pred_is_neg_SO (allFO x alpha) P <-> Pred_is_neg_SO alpha P.
Proof. firstorder. Qed.

Lemma Pred_is_neg_SO_exFO  : forall (alpha : SecOrder) (x : FOvariable) (P : predicate),
  Pred_is_neg_SO (exFO x alpha) P <-> Pred_is_neg_SO alpha P.
Proof. firstorder. Qed.

Lemma is_neg_SO_pre_ST_FOv : forall (phi : Modal) (x y : FOvariable)
                                (i : nat),
  is_neg_SO_pre (ST phi x) i = is_neg_SO_pre (ST phi y) i.
Proof.
  induction phi; intros [xn] [ym] i;
    try (  simpl; erewrite preds_in_ST_FOv;
           erewrite IHphi1; erewrite IHphi2; reflexivity); simpl;
      try (erewrite IHphi; reflexivity).
  destruct p; auto.
Qed.

Lemma is_neg_SO_ST_FOv : forall (phi : Modal) (x y : FOvariable)
                                (i : nat),
  is_neg_SO (ST phi x) i <-> is_neg_SO (ST phi y) i.
Proof.
  intros phi x y i; split; intros [H1 H2]; constructor.
  eapply occ_in_SO_ST_FOv. apply H1.
  erewrite is_neg_SO_pre_ST_FOv. apply H2.
  eapply occ_in_SO_ST_FOv. apply H1.
  erewrite is_neg_SO_pre_ST_FOv. apply H2.
Qed.

Lemma is_neg_SO_pre_box : forall (phi : Modal) (x : FOvariable)
                             (i : nat),
  i <> 0 ->
  is_neg_SO_pre (ST (box phi) x) i = is_neg_SO_pre (ST phi x) i.
Proof.
  intros phi [xn] i H. simpl. destruct i. contradiction. 
  simpl. apply is_neg_SO_pre_ST_FOv.
Qed.

Lemma is_neg_SO_box : forall (phi : Modal) (x : FOvariable)
                             (i : nat),
  is_neg_SO (ST (box phi) x) i <-> is_neg_SO (ST phi x) i.
Proof.
  intros. split; intros [H1 H2].
  rewrite is_neg_SO_pre_box in H2.  apply conj.
  apply occ_in_SO_box. auto. auto.
  firstorder.
  apply conj. apply occ_in_SO_box. auto.
  rewrite is_neg_SO_pre_box. auto. firstorder.
Qed.

Lemma is_neg_SO_pre_diam : forall (phi : Modal) (x : FOvariable)
                             (i : nat),
  i <> 0 ->
  is_neg_SO_pre (ST (diam phi) x) i = is_neg_SO_pre (ST phi x) i.
Proof.
  intros phi [xn] i H. simpl. destruct i. contradiction. 
  simpl. apply is_neg_SO_pre_ST_FOv.
Qed.

Lemma is_neg_SO_diam : forall (phi : Modal) (x : FOvariable)
                             (i : nat),
  is_neg_SO (ST (diam phi) x) i <-> is_neg_SO (ST phi x) i.
Proof.
  intros. split; intros [H1 H2].
  rewrite is_neg_SO_pre_diam in H2.  apply conj.
  apply occ_in_SO_box. auto. auto.
  firstorder.
  apply conj. apply occ_in_SO_box. auto.
  rewrite is_neg_SO_pre_diam. auto. firstorder.
Qed.

Lemma is_neg__ST : forall (phi : Modal) (x : FOvariable) (i : nat),
  is_neg phi i <-> is_neg_SO (ST phi x) i.
Proof.
  intros phi x i; split; intros H.
    destruct (pos_or_neg_SO (ST phi x) i) as [H1 | H1].
      apply occ_in_ST. apply is_neg_occ. auto.
      apply is_pos__ST in H1. apply is_neg_pos_t in H.
      contradiction. auto.

    destruct (is_pos_neg_or phi i) as [H1 | H1].
      eapply occ_in_ST. apply is_neg_SO_occ. apply H. 
      eapply is_pos__ST in H1. apply is_pos_neg_SO_t in H.
      contradiction (H H1). auto.
Qed. 

Lemma p_is_neg__SO : forall (phi : Modal) (x : FOvariable)
                            (p : propvar),
  p_is_neg phi p <-> Pred_is_neg_SO (ST phi x) (ST_pv p).
Proof.
  intros phi x p.
  split; intros [H1 H2].
    constructor. apply p_occ__ST. auto.

    intros i H3 H4. apply is_neg__ST. apply H2.
    eapply occ_in_ST. apply H3. rewrite <- at_pv_ST_nocon in H4.
    apply ST_pv_inj in H4. auto.

    constructor. eapply p_occ__ST. apply H1.

    intros i H3 H4. eapply is_neg__ST. apply H2.
    eapply occ_in_ST. apply H3. rewrite H4. 
    erewrite at_pv_ST_nocon. reflexivity.
Qed.

Lemma Pred_is_neg_SO_allSO : forall alpha P Q,
  Pred_in_SO alpha P ->
  Pred_is_neg_SO (allSO P alpha) Q ->
  Pred_is_neg_SO alpha Q.
Proof.
  intros alpha P Q Hpocc [H1 H2]. constructor. 
  + inversion H1; subst; auto. 
  + intros i Hocc Hat. assert (occ_in_SO (allSO P alpha) (S i)) as Hocc2.
    constructor; simpl; firstorder.
    eapply H2 in Hocc2. inversion Hocc2. constructor. auto.
    simpl in *. destruct P. destruct i; firstorder. simpl.
    destruct i. firstorder. firstorder.
Qed. 

Lemma Pred_is_neg_SO_exSO : forall alpha P Q,
  Pred_in_SO alpha P  ->
  Pred_is_neg_SO (exSO P alpha) Q ->
  Pred_is_neg_SO alpha Q.
Proof.
  intros alpha P Q Hpocc [H1 H2]. constructor. 
  + inversion H1; subst; auto. 
  + intros i Hocc Hat. assert (occ_in_SO (exSO P alpha) (S i)) as Hocc2.
    constructor; simpl; firstorder.
    eapply H2 in Hocc2. inversion Hocc2. constructor. auto.
    simpl in *. destruct P. destruct i; firstorder. simpl.
    destruct i. firstorder. firstorder.
Qed.

Lemma Pred_is_neg_SO_allSO_neq : forall alpha P Q,
  ~ P = Q ->
  Pred_is_neg_SO (allSO P alpha) Q ->
  Pred_is_neg_SO alpha Q.
Proof.
  intros alpha P Q Hneq [H1 H2].
  inversion H1. subst. contradiction.
  constructor. auto.
  intros i Hocc Hat. simpl in *.
  assert (occ_in_SO (allSO P alpha) (S i)) as Hpocc. apply occ_in_SO_allSO. auto.
  specialize (H2 _ Hpocc). simpl in *. destruct i. firstorder.
  rewrite PeanoNat.Nat.sub_0_r in *. apply H2 in Hat. 
  constructor. auto. inversion Hat. simpl in *. destruct P. auto.
Qed.

Lemma Pred_is_neg_SO_exSO_neq : forall alpha P Q,
  ~ P = Q ->
  Pred_is_neg_SO (exSO P alpha) Q ->
  Pred_is_neg_SO alpha Q.
Proof.
  intros alpha P Q Hneq [H1 H2].
  inversion H1. subst. contradiction.
  constructor. auto.
  intros i Hocc Hat. simpl in *.
  assert (occ_in_SO (exSO P alpha) (S i)) as Hpocc. apply occ_in_SO_exSO. auto.
  specialize (H2 _ Hpocc). simpl in *. destruct i. firstorder.
  rewrite PeanoNat.Nat.sub_0_r in *. apply H2 in Hat. 
  constructor. auto. inversion Hat. simpl in *. destruct P. auto.
Qed.