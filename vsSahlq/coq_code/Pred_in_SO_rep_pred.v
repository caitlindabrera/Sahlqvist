Require Export low_mods.
Require Import Rep_Pred_FOv.

Lemma Pred_in_SO_rep_pred : forall (alpha cond : SecOrder) (x : FOvariable)
                              (P P2 : predicate),
  FO_frame_condition cond = true ->
    Pred_in_SO (replace_pred alpha P x cond) P2 ->
      Pred_in_SO alpha P2.
Proof.
  intros alpha cond x P P2 Hunary HPocc.
  unfold Pred_in_SO in *.
  induction alpha; try (    apply IHalpha; auto); try auto;
    try (    simpl in *; apply in_app_or in HPocc;
    apply in_or_app; firstorder).

  simpl in *. destruct (predicate_dec P p).
    subst. rewrite preds_in_rep_FOv in HPocc.
    rewrite FO_frame_condition_preds_in in HPocc.
    firstorder.  auto.
    simpl in *. auto. 

    simpl in *. destruct (predicate_dec P p) as [H1 | H1].
    subst. right. firstorder.
    simpl in HPocc. destruct HPocc. auto.
    right. apply IHalpha. auto.

    simpl in *. destruct (predicate_dec P p) as [H1 | H1].
    subst. right. firstorder.
    simpl in HPocc. destruct HPocc. auto.
    right. apply IHalpha. auto.
Qed.

Lemma Pred_in_SO_rep_pred_f : forall (alpha cond : SecOrder) (x : FOvariable)
                                    (Q : predicate),
  FO_frame_condition cond = true ->
   ~ Pred_in_SO (replace_pred alpha Q x cond) Q.
Proof.
  intros alpha cond x Q Hcond.
  induction alpha; intros H; try contradiction.

  simpl in *. destruct (predicate_dec Q p) as [H1 | H1].
  subst. apply Pred_in_SO_FO_frame_condition in H. contradiction.
  apply rep_FOv_FO_frame_condition. auto.
  inversion H as [H2 | H2]; subst; contradiction.

  rewrite rep_pred_conjSO in H.
  apply Pred_in_SO_conjSO in H.
  destruct H; contradiction.

  rewrite rep_pred_disjSO in H.
  apply Pred_in_SO_conjSO in H.
  destruct H; contradiction.

  rewrite rep_pred_implSO in H.
  apply Pred_in_SO_conjSO in H.
  destruct H; contradiction.

  simpl in *. destruct (predicate_dec Q p) as [H1 | H1].
  subst. contradiction. inversion H as [H2 | H2].
  subst. contradiction.
  apply In_preds_in_rep_pred in H2.
  eapply Pred_in_SO_FO_frame_condition in H2. contradiction.
  auto.

  simpl in *. destruct (predicate_dec Q p) as [H1 | H1].
  subst. contradiction. inversion H as [H2 | H2].
  subst. contradiction.
  apply In_preds_in_rep_pred in H2.
  eapply Pred_in_SO_FO_frame_condition in H2. contradiction.
  auto.
Qed.