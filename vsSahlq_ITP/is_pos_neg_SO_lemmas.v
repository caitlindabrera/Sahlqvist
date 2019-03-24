Require Export low_mods is_pos_SO is_neg_SO.
Require Import ST is_pos.

Lemma is_pos_SO_dec : forall alpha i,
    {is_pos_SO alpha i} + {~is_pos_SO alpha i}.
Proof.
  intros alpha i. destruct (occ_in_SO_dec alpha i) as [H | H].
  destruct i. firstorder.
  case_eq (is_pos_SO_pre alpha (S i)); intros H2.
  left. constructor; auto. 
  right. intros H3. inversion H3 as [H4 H5]. rewrite H5 in *.
  discriminate.
  right. intros H2. firstorder.
Qed.

Lemma is_pos_SO_allFO : forall (alpha : SecOrder) (x : FOvariable) 
                               (i : nat),
  is_pos_SO (allFO x alpha) i <-> is_pos_SO alpha i.
Proof.
  intros alpha x i; split; intros [H1 H2]; destruct x as [xn];
  simpl in H2; constructor; firstorder.
Qed.

Lemma is_pos_SO_exFO : forall (alpha : SecOrder) (x : FOvariable) 
                               (i : nat),
  is_pos_SO (exFO x alpha) i <-> is_pos_SO alpha i.
Proof.
  intros alpha x i; split; intros [H1 H2]; destruct x as [xn];
  simpl in H2; constructor; firstorder.
Qed.

Lemma is_pos_SO_pre_conjSO_l : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_SO alpha1 i ->
    is_pos_SO_pre (conjSO alpha1 alpha2) i = is_pos_SO_pre alpha1 i.
Proof.
  intros alpha1 alpha2 i [H1 H2]. simpl. 
  if_then_else_dest_blind; auto. firstorder.
Qed.

Lemma is_pos_SO_conjSO_l : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_SO alpha1 i ->
    is_pos_SO (conjSO alpha1 alpha2) i <-> is_pos_SO alpha1 i.
Proof.
  intros alpha1 alpha2 i Hocc; split; intros [H1 H2]; constructor.
  auto. rewrite is_pos_SO_pre_conjSO_l in H2; auto.
  apply occ_in_SO_conjSO2. auto.
  rewrite is_pos_SO_pre_conjSO_l; auto.
Qed.

Lemma is_pos_SO_pre_disjSO_l : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_SO alpha1 i ->
    is_pos_SO_pre (disjSO alpha1 alpha2) i = is_pos_SO_pre alpha1 i.
Proof.
  intros alpha1 alpha2 i [H1 H2]. simpl. 
  if_then_else_dest_blind; auto. firstorder.
Qed.

Lemma is_pos_SO_disjSO_l : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_SO alpha1 i ->
    is_pos_SO (disjSO alpha1 alpha2) i <-> is_pos_SO alpha1 i.
Proof.
  intros alpha1 alpha2 i Hocc; split; intros [H1 H2]; constructor.
  auto. rewrite is_pos_SO_pre_disjSO_l in H2; auto.
  apply occ_in_SO_disjSO2. auto.
  rewrite is_pos_SO_pre_disjSO_l; auto.
Qed.

(* -------------------------------------------------------------------- *)

Lemma is_pos_SO_0 : forall (alpha : SecOrder),
  ~ is_pos_SO alpha 0.
Proof. firstorder. Qed.

Lemma is_pos_SO_not : forall alpha i,
    ~ is_pos_SO alpha i ->
    ~ occ_in_SO alpha i \/ is_pos_SO_pre alpha i = false.
Proof.
  intros alpha i H1.
  destruct (occ_in_SO_dec alpha i) as [H2 | H2].
  case_eq (is_pos_SO_pre alpha i); intros H3.
  all : firstorder.
Qed.

Lemma is_pos_SO_occ_f : forall (alpha : SecOrder) (i : nat),
  ~ occ_in_SO alpha i -> ~ is_pos_SO alpha i.
Proof. intros alpha i Hocc Hpos. firstorder. Qed.

Lemma is_pos_SO_occ : forall (alpha : SecOrder) (i : nat),
  is_pos_SO alpha i  -> occ_in_SO alpha i.
Proof. firstorder. Qed.


Lemma is_pos_SO_implSO_l_t : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_SO alpha1 i ->
    ~ is_pos_SO alpha1 i -> is_pos_SO (implSO alpha1 alpha2) i.
Proof.
  intros alpha1 alpha2 i H1 H2.
  apply is_pos_SO_not in H2. destruct H2. firstorder.
  constructor. constructor; simpl in *; firstorder.
  rewrite app_length. firstorder.
  simpl. rewrite H. simpl. if_then_else_dest_blind; firstorder.
Qed.

Lemma is_pos_SO_conjSO_r : forall (alpha1 alpha2 : SecOrder) (i : nat),
  ~ occ_in_SO alpha1 i ->
    occ_in_SO alpha2 (i - length (preds_in alpha1)) ->
      is_pos_SO (conjSO alpha1 alpha2) i <-> 
        is_pos_SO alpha2 (i - length( preds_in alpha1)).
Proof.
  intros alpha1 alpha2 i Hocc1 Hocc2; split; intros [H1 H2]; constructor.
  auto. simpl in H2. 
  if_then_else_dest_blind; auto; firstorder.
  auto. apply occ_in_SO_conjSO2. auto.
  simpl. rewrite H2.
  if_then_else_dest_blind; auto. firstorder.
Qed.

Lemma is_pos_SO_disjSO_r : forall (alpha1 alpha2 : SecOrder) (i : nat),
  ~ occ_in_SO alpha1 i ->
    occ_in_SO alpha2 (i - length (preds_in alpha1)) ->
      is_pos_SO (disjSO alpha1 alpha2) i <-> 
        is_pos_SO alpha2 (i - length( preds_in alpha1)).
Proof.
  intros alpha1 alpha2 i Hocc1 Hocc2; split; intros [H1 H2]; constructor.
  auto. simpl in H2. 
  if_then_else_dest_blind; auto; firstorder.
  auto. apply occ_in_SO_disjSO2. auto.
  simpl. rewrite H2.
  if_then_else_dest_blind; auto. firstorder.
Qed.

Lemma is_pos_SO_implSO_r : forall (alpha1 alpha2 : SecOrder) (i : nat),
  ~ occ_in_SO alpha1 i ->
    occ_in_SO alpha2 (i - length (preds_in alpha1)) ->
      is_pos_SO (implSO alpha1 alpha2) i <-> 
        is_pos_SO alpha2 (i - length( preds_in alpha1)).
Proof.
  intros alpha1 alpha2 i Hocc1 Hocc2; split; intros [H1 H2]; constructor.
  auto. simpl in H2. 
  if_then_else_dest_blind; auto; firstorder.
  auto. apply occ_in_SO_implSO2. auto.
  simpl. rewrite H2.
  if_then_else_dest_blind; auto. firstorder.
Qed.

Lemma is_pos_SO_negSO : forall (alpha : SecOrder) (i : nat),
  is_pos_SO (negSO alpha) i  ->
  ~ is_pos_SO alpha i.
Proof.
  intros alpha i [H1 H2] [H3 H4].
  simpl in *. rewrite H4 in *. discriminate.
Qed.

Lemma is_pos_SO_negSO2 : forall (alpha : SecOrder) (i : nat),
  occ_in_SO alpha i ->
    ~ is_pos_SO alpha i ->
      is_pos_SO (negSO alpha) i.
Proof.
  intros alpha i Hocc Hpos; constructor. apply occ_in_SO_negSO. auto.
  simpl. case_eq (is_pos_SO_pre alpha i); intros H; firstorder.
Qed.

Lemma is_pos_SO_implSO_r2 : forall (alpha1 alpha2 : SecOrder) (i : nat),
  ~ occ_in_SO alpha1 i  ->
  is_pos_SO (implSO alpha1 alpha2) i ->
  is_pos_SO alpha2 (i - (length (preds_in alpha1))).
Proof.
  intros alpha1 alpha2 i Hocc [H1 H2]; constructor.
  apply occ_in_SO_implSO2 in H1. firstorder.
  simpl in H2. 
  if_then_else_dest_blind; auto. firstorder.
Qed.

Lemma is_pos_SO_implSO_l2 : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_SO alpha1 i ->
  is_pos_SO (implSO alpha1 alpha2) i ->
  ~ is_pos_SO alpha1 i .
Proof.
  intros alpha1 alpha2 i Hocc [H1 H2] [H3 H4]. simpl in *.
  rewrite H4 in *. if_then_else_dest_blind; firstorder.
Qed.

Lemma is_pos_SO_implSO_l2_contra : forall (alpha1 alpha2 : SecOrder) (i : nat),
    occ_in_SO alpha1 i -> is_pos_SO alpha1 i -> ~ is_pos_SO (alpha1 SO→ alpha2) i.
Proof.
  intros alpha1 alpha2 i Hocc [H1 H2] [H3 H4].
  simpl in H4. rewrite H2 in *. if_then_else_dest_blind; firstorder.
Qed.


Lemma is_pos_SO_implSO_f : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_SO (implSO alpha1 alpha2) i ->
  ~ is_pos_SO (implSO alpha1 alpha2) i ->
  (occ_in_SO alpha1 i -> is_pos_SO alpha1 i) /\
  (occ_in_SO alpha2 (i - (length (preds_in alpha1))) ->
    ~ is_pos_SO alpha2 (i - (length (preds_in alpha1)))).
Proof.
  intros alpha1 alpha2 i Hocc Hpos; split; intros H.
  constructor. auto. pose proof (occ_in_SO_le _ _ H) as H2.
  apply is_pos_SO_not in Hpos.
  destruct Hpos as [H1 | H1]. firstorder.
  simpl in H1. if_then_else_dest_blind; auto.
  apply Bool.negb_false_iff in H1. auto.
  intros H2. apply occ_in_SO_le_minus in H.
  apply is_pos_SO_not in Hpos. destruct Hpos as [H3 | H3].
  auto. simpl in H3. if_then_else_dest_blind; auto. 
  inversion H2. rewrite H3 in *. firstorder.
Qed.

Lemma is_pos_SO_implSO_f2 : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_SO (implSO alpha1 alpha2) i ->
  ~ is_pos_SO (implSO alpha1 alpha2) i ->
  (occ_in_SO alpha1 i -> is_pos_SO alpha1 i) /\
  (~ occ_in_SO alpha1 i ->
    ~ is_pos_SO alpha2 (i - (length (preds_in alpha1)))).
Proof.
  intros alpha1 alpha2 i Hocc Hpos.
  split; intros H.
  apply is_pos_SO_implSO_f in Hocc. destruct Hocc as [H1 H2].
  apply H1. auto. auto.
  intros H2. apply is_pos_SO_not in Hpos.
  destruct Hpos as [H1 | H1]. auto.
  simpl in H1. inversion H2 as [H3 H4]. rewrite H4 in H1.
  apply occ_in_SO_implSO2 in Hocc. destruct Hocc as [H5 | H5].
  auto. apply occ_in_SO_le_minus in H5. 
  if_then_else_dest_blind; firstorder.
Qed.

Lemma is_pos_SO_exSO : forall (alpha : SecOrder) (Q : predicate) (i : nat),
  occ_in_SO alpha i ->
  is_pos_SO (exSO Q alpha) (S i) <-> is_pos_SO alpha i.
Proof.
  intros alpha Q i H; split; intros [H2 H3]; constructor.
  auto. simpl in H3. destruct Q. destruct i; firstorder.
  apply occ_in_SO_exSO. auto.
  simpl. destruct Q. destruct i; firstorder.
Qed.

Lemma is_pos_SO_allSO : forall (alpha : SecOrder) (Q : predicate) (i : nat),
  occ_in_SO alpha i ->
  is_pos_SO (allSO Q alpha) (S i) <-> is_pos_SO alpha i.
Proof.
  intros alpha Q i H; split; intros [H2 H3]; constructor.
  auto. simpl in H3. destruct Q. destruct i; firstorder.
  apply occ_in_SO_allSO. auto.
  simpl. destruct Q. destruct i; firstorder.
Qed.

(* -------------------------------------------------------------------- *)
(* ST lemmas *)

Lemma is_pos_SO_pre_ST_FOv : forall phi x y i,
    is_pos_SO_pre (ST phi x) i = is_pos_SO_pre (ST phi y) i.
Proof.
  induction phi; intros [xn] [ym] i;
    try (  simpl; erewrite preds_in_ST_FOv;
           erewrite IHphi1; erewrite IHphi2; reflexivity); simpl;
      try (erewrite IHphi; reflexivity).
  destruct p; auto.
Qed.

Lemma is_pos_SO_ST_FOv : forall (phi : Modal) (x y : FOvariable)
                                (i : nat),
  is_pos_SO (ST phi x) i <-> is_pos_SO (ST phi y) i.
Proof.
  intros phi x y i; split; intros [H1 H2]; constructor.
  eapply occ_in_SO_ST_FOv. apply H1.
  erewrite is_pos_SO_pre_ST_FOv. apply H2.
  eapply occ_in_SO_ST_FOv. apply H1.
  erewrite is_pos_SO_pre_ST_FOv. apply H2.
Qed.

Lemma is_pos_SO_pre_box : forall phi x i,
    occ_in_SO (ST phi x) i ->
    is_pos_SO_pre (ST (box phi) x) i = is_pos_SO_pre (ST phi x) i.
Proof.
  intros phi [xn] i [H1 H2]. simpl.
  destruct i. contradiction.
  simpl. 
  apply is_pos_SO_pre_ST_FOv.
Qed.

Lemma is_pos_SO_box : forall (phi : Modal) (x : FOvariable)
                             (i : nat),
  is_pos_SO (ST (box phi) x) i <-> is_pos_SO (ST phi x) i.
Proof.
  intros phi [xn] i; split; intros [H1 H2]; constructor.
  apply occ_in_SO_box. auto.
  rewrite <- is_pos_SO_pre_box. auto. apply occ_in_SO_box. auto.
  apply occ_in_SO_box. auto.
  rewrite is_pos_SO_pre_box. auto. apply occ_in_SO_box. auto.
  apply occ_in_SO_box. auto.
Qed.

Lemma is_pos_SO_pre_diam : forall phi x i,
    occ_in_SO (ST phi x) i ->
    is_pos_SO_pre (ST (diam phi) x) i = is_pos_SO_pre (ST phi x) i.
Proof.
  intros phi [xn] i [H1 H2]. simpl.
  destruct i. contradiction.
  simpl. 
  apply is_pos_SO_pre_ST_FOv.
Qed.

Lemma is_pos_SO_diam : forall (phi : Modal) (x : FOvariable)
                             (i : nat),
    is_pos_SO (ST (diam phi) x) i <-> is_pos_SO (ST phi x) i.
Proof.
  intros phi [xn] i; split; intros [H1 H2]; constructor.
  apply occ_in_SO_diam. auto.
  rewrite <- is_pos_SO_pre_diam. auto. apply occ_in_SO_diam. auto.
  apply occ_in_SO_diam. auto.
  rewrite is_pos_SO_pre_diam. auto. apply occ_in_SO_diam. auto.
  apply occ_in_SO_diam. auto.
Qed.

Lemma is_pos_pre_ST: forall phi x i,
    occ_in_modal phi i ->
    is_pos_pre phi i = is_pos_SO_pre (ST phi x) i.
Proof.
  induction phi; intros [xn] i [H1 H2].
  simpl; destruct i; destruct p; auto.
  simpl. erewrite IHphi. reflexivity. firstorder.
  
  simpl. rewrite <- pv_in__preds_in. simpl in H2. rewrite app_length in H2.
  destruct (le_dec i (length (pv_in phi1))) as [H4 | H4]. 
    apply IHphi1. constructor. auto. auto.    
    apply IHphi2. constructor. intros H5. firstorder. apply (Var 0).
    firstorder. apply (Var 0).

  simpl. rewrite <- pv_in__preds_in. simpl in H2. rewrite app_length in H2.
  destruct (le_dec i (length (pv_in phi1))) as [H4 | H4]. 
    apply IHphi1. constructor. auto. auto.    
    apply IHphi2. constructor. intros H5. firstorder. apply (Var 0).
    firstorder. apply (Var 0).

  simpl. rewrite <- pv_in__preds_in. simpl in H2. rewrite app_length in H2.
  unfold negb.
  destruct (le_dec i (length (pv_in phi1))) as [H4 | H4]. 
    rewrite <- IHphi1. auto. constructor. auto. auto.    
    rewrite <- IHphi2. auto. constructor. intros H5. firstorder. apply (Var 0).
    firstorder. apply (Var 0).

  simpl. destruct i. auto. simpl. apply IHphi. constructor.
  auto. simpl in *. auto.

  simpl. destruct i. contradiction. simpl. apply IHphi. constructor.
  auto. simpl in *. auto.
Qed.

Lemma is_pos__ST : forall (phi : Modal) (x : FOvariable) (i : nat),
  is_pos phi i <-> is_pos_SO (ST phi x) i.
Proof.
  intros phi x i; split; intros [H1 H2]; constructor.
  apply occ_in_ST. auto.
  rewrite <- is_pos_pre_ST; auto.
  apply occ_in_ST in H1. auto.
  erewrite is_pos_pre_ST. apply H2.
  eapply occ_in_ST. apply H1.
Qed.

(* --------------------------------------------------------- *)

Lemma is_neg_SO_occ : forall (alpha : SecOrder) (i : nat),
  is_neg_SO alpha i-> occ_in_SO alpha i.
Proof. firstorder. Qed.

Lemma is_neg_SO_dec : forall alpha i,
    {is_neg_SO alpha i} + {~is_neg_SO alpha i}.
Proof.
  intros alpha i. destruct (occ_in_SO_dec alpha i) as [H | H].
  case_eq (is_neg_SO_pre alpha i); intros H2. firstorder.
  right. intros [H4 H5]. rewrite H5 in *.
  discriminate.
  right. intros H2. firstorder.
Qed.

Lemma is_neg_SO_not : forall alpha i,
    ~ is_neg_SO alpha i ->
    ~ occ_in_SO alpha i \/ is_neg_SO_pre alpha i = false.
Proof.
  intros alpha i H1.
  destruct (occ_in_SO_dec alpha i) as [H2 | H2].
  case_eq (is_neg_SO_pre alpha i); intros H3.
  all : firstorder.
Qed.

(* -------------------------------------------------------------------- *)

Lemma is_neg_SO_occ_f : forall (alpha : SecOrder) (i : nat),
  ~ occ_in_SO alpha i -> ~is_neg_SO alpha i.
Proof. firstorder. Qed.

Lemma is_neg_SO_allFO : forall (alpha : SecOrder) (x : FOvariable) 
                               (i : nat),
  is_neg_SO (allFO x alpha) i <-> is_neg_SO alpha i.
Proof. firstorder. Qed.

Lemma is_neg_SO_exFO : forall (alpha : SecOrder) (x : FOvariable) 
                               (i : nat),
  is_neg_SO (exFO x alpha) i <-> is_neg_SO alpha i.
Proof. firstorder. Qed.

Lemma is_neg_SO_negSO : forall (alpha : SecOrder) (i : nat),
  is_neg_SO (negSO alpha) i ->
    ~ is_neg_SO alpha i.
Proof. 
  intros alpha i [H1 H2] [H3 H4].
  simpl in H2. rewrite H4 in *. discriminate.
Qed.

Lemma is_neg_SO_negSO2 : forall (alpha : SecOrder) (i : nat),
  occ_in_SO alpha i ->
    ~ is_neg_SO alpha i ->
      is_neg_SO (negSO alpha) i.
Proof.
  intros alpha i Hocc Hpos. apply is_neg_SO_not in Hpos.
  destruct Hpos. firstorder.
  constructor. firstorder. simpl. rewrite H. auto.
Qed.

Lemma is_neg_SO_conjSO_l : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_SO alpha1 i ->
    is_neg_SO (conjSO alpha1 alpha2) i <-> is_neg_SO alpha1 i.
Proof.
  intros alpha1 alpha2 i Hocc.
  simpl. split; intros [H1 H2].
  simpl in *. if_then_else_dest_blind; auto. 
  constructor; auto. firstorder.
  constructor. constructor. firstorder. simpl.
  rewrite app_length. firstorder. simpl.
  if_then_else_dest_blind; auto. firstorder.
Qed.

Lemma is_neg_SO_conjSO_r : forall (alpha1 alpha2 : SecOrder) (i : nat),
  ~occ_in_SO alpha1 i ->
    occ_in_SO alpha2 (i - length (preds_in alpha1)) ->
      is_neg_SO (conjSO alpha1 alpha2) i <->
        is_neg_SO alpha2 (i - length( preds_in alpha1)).
Proof.
  intros alpha1 alpha2 i Hocc1 Hocc2.
  simpl.
  assert (occ_in_SO (conjSO alpha1 alpha2) i) as H.
    apply occ_in_SO_conjSO2. auto.
  apply occ_in_SO_f in Hocc1. destruct Hocc1 as [Hocc1 | Hocc1].
    subst. contradiction (occ_in_SO_0 _ Hocc2).
    apply Gt.gt_not_le in Hocc1.
  split; intros [H1 H2]; constructor; auto;
    simpl in *;
    if_then_else_dest_blind; firstorder.
Qed.

Lemma is_neg_SO_disjSO_l : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_SO alpha1 i ->
    is_neg_SO (disjSO alpha1 alpha2) i <-> is_neg_SO alpha1 i.
Proof.
  intros alpha1 alpha2 i Hocc.
  simpl. split; intros [H1 H2].
  simpl in *. if_then_else_dest_blind; auto. 
  constructor; auto. firstorder.
  constructor. constructor. firstorder. simpl.
  rewrite app_length. firstorder. simpl.
  if_then_else_dest_blind; auto. firstorder.
Qed. 

Lemma is_neg_SO_implSO_l_t : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_SO alpha1 i ->
    is_neg_SO (implSO alpha1 alpha2) i -> ~ is_neg_SO alpha1 i.
Proof.
  intros alpha1 alpha2 i Hocc [H1 H2] [H3 H4].
  simpl in *. unfold negb in *.
  if_then_else_dest_blind; firstorder.
Qed.

Lemma is_neg_SO_disjSO_r : forall (alpha1 alpha2 : SecOrder) (i : nat),
  ~ occ_in_SO alpha1 i ->
    occ_in_SO alpha2 (i - length (preds_in alpha1)) ->
      is_neg_SO (disjSO alpha1 alpha2) i <->
        is_neg_SO alpha2 (i - length( preds_in alpha1)).
Proof.
  intros alpha1 alpha2 i Hocc1 Hocc2.
  simpl.
  assert (occ_in_SO (conjSO alpha1 alpha2) i) as H.
    apply occ_in_SO_conjSO2. auto.
  apply occ_in_SO_f in Hocc1. destruct Hocc1 as [Hocc1 | Hocc1].
    subst. contradiction (occ_in_SO_0 _ Hocc2).
    apply Gt.gt_not_le in Hocc1.
  split; intros [H1 H2]; constructor; auto;
    simpl in *;
    if_then_else_dest_blind; firstorder.
Qed.

Lemma is_neg_SO_implSO_r : forall (alpha1 alpha2 : SecOrder) (i : nat),
  ~ occ_in_SO alpha1 i ->
    occ_in_SO alpha2 (i - length (preds_in alpha1)) ->
      is_neg_SO (implSO alpha1 alpha2) i <-> 
        is_neg_SO alpha2 (i - length( preds_in alpha1)).
Proof.
  intros alpha1 alpha2 i Hocc1 Hocc2.
  simpl.
  assert (occ_in_SO (conjSO alpha1 alpha2) i) as H.
    apply occ_in_SO_conjSO2. auto.
  apply occ_in_SO_f in Hocc1. destruct Hocc1 as [Hocc1 | Hocc1].
    subst. contradiction (occ_in_SO_0 _ Hocc2).
    apply Gt.gt_not_le in Hocc1.
  split; intros [H1 H2]; constructor; auto;
    simpl in *;
    if_then_else_dest_blind; firstorder.
Qed.

Lemma is_neg_SO_implSO_l2 : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_SO alpha1 i ->
  is_neg_SO (implSO alpha1 alpha2) i ->
  ~ is_neg_SO alpha1 i.
Proof.
  intros alpha1 alpha2 i Hocc [H1 H2] [H3 H4].
  simpl in *. unfold negb in *.
  if_then_else_dest_blind; firstorder.
Qed.

Lemma is_neg_SO_0 : forall (alpha : SecOrder),
  ~ is_neg_SO alpha 0.
Proof. firstorder. Qed.

(* ------------------------------------------------- *)



Lemma pos_or_neg_SO_pre_eq_negb : forall (alpha : SecOrder) (i : nat),
  occ_in_SO alpha i ->
    is_pos_SO_pre alpha i = negb (is_neg_SO_pre alpha i).
Proof.
  induction alpha; intros i Hocc; try solve [firstorder].

    simpl. destruct i. firstorder.
    destruct i. firstorder. inversion Hocc. simpl in *.
    firstorder.

    simpl. rewrite IHalpha; firstorder.

    simpl; apply occ_in_SO_conjSO2_fwd in Hocc; unfold not in *;
    destruct Hocc; if_then_else_dest_blind; firstorder.

    simpl; apply occ_in_SO_disjSO2_fwd in Hocc; unfold not in *;
    destruct Hocc; if_then_else_dest_blind; firstorder.

    simpl; apply occ_in_SO_implSO2_fwd in Hocc; unfold not in *;
    destruct Hocc; if_then_else_dest_blind; firstorder;
    rewrite IHalpha1; firstorder.

    simpl in *. unfold negb. destruct i. firstorder.
    destruct i. auto. rewrite IHalpha. auto.
    eapply occ_in_SO_allSO_rev. apply Hocc.

    simpl in *. unfold negb. destruct i. firstorder.
    destruct i. auto. rewrite IHalpha. auto.
    eapply occ_in_SO_exSO_rev. apply Hocc.
Qed.

Lemma pos_or_neg_SO_pre : forall (alpha : SecOrder) (i : nat),
  occ_in_SO alpha i ->
    is_pos_SO_pre alpha i = true \/ is_neg_SO_pre alpha i = true.
Proof.
  intros alpha i Hocc. rewrite pos_or_neg_SO_pre_eq_negb.
  case_eq (is_neg_SO_pre alpha i); auto. auto.
Qed.

Lemma pos_or_neg_SO : forall (alpha : SecOrder) (i : nat),
  occ_in_SO alpha i ->
    is_pos_SO alpha i \/ is_neg_SO alpha i.
Proof.
  intros alpha i Hocc.
  destruct (pos_or_neg_SO_pre alpha i Hocc) as [H1 | H1].
  left. firstorder. right. firstorder.
Qed.

Lemma is_pos_neg_SO_t : forall (alpha : SecOrder) (i : nat),
  (is_pos_SO alpha i -> ~ is_neg_SO alpha i) /\
  (is_neg_SO alpha i -> ~ is_pos_SO alpha i).
Proof.
  intros alpha i. 
  destruct (occ_in_SO_dec alpha i) as [H1 | H1].
  split; intros [H2 H3] [H4 H5];
    rewrite pos_or_neg_SO_pre_eq_negb in *.
    rewrite H5 in H3. discriminate. auto.
    rewrite H3 in H5. discriminate. auto.

  split; intros [H2 H3] [H4 H5]; contradiction.
Qed.

Lemma is_pos_negSO : forall (alpha : SecOrder) (i : nat),
  is_pos_SO (negSO alpha) i ->
    is_neg_SO alpha i.
Proof.
  intros alpha i Hpos. pose proof Hpos as Hpos2.
  apply is_pos_SO_negSO in Hpos.
  pose proof (is_pos_SO_occ _ _ Hpos2) as H.
  apply (occ_in_SO_negSO alpha) in H.
  destruct (pos_or_neg_SO alpha i); auto. contradiction.
Qed.

Lemma is_neg_negSO : forall (alpha : SecOrder) (i : nat),
  is_neg_SO (negSO alpha) i ->
    is_pos_SO alpha i.
Proof.
  intros alpha i Hpos. pose proof Hpos as Hpos2.
  apply is_neg_SO_negSO in Hpos.
  pose proof (is_neg_SO_occ _ _ Hpos2) as H.
  apply (occ_in_SO_negSO alpha) in H.
  destruct (pos_or_neg_SO alpha i); auto. contradiction.
Qed.