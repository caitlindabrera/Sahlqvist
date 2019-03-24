Require Export is_pos_neg_SO_lemmas Pred_is_pos_SO Pred_is_neg_SO.
Require Export med_mods.

Lemma P_pos_negSO : forall (alpha : SecOrder) (P : predicate),
  Pred_is_pos_SO (negSO alpha) P -> Pred_is_neg_SO alpha P.
Proof. 
  intros alpha P [H1 H2]. constructor. firstorder.
  intros i Hocc Hat. apply H2 in Hat. apply is_pos_negSO. 
  auto.  firstorder.
Qed.

Lemma P_neg_negSO : forall (alpha : SecOrder) (P : predicate),
  Pred_is_neg_SO (negSO alpha) P -> Pred_is_pos_SO alpha P.
Proof. 
  intros alpha P [H1 H2]. constructor. firstorder.
  intros i Hocc Hat. apply H2 in Hat. apply is_neg_negSO. 
  auto.  firstorder.
Qed.

Lemma Pred_is_neg_SO_allFO  : forall (alpha : SecOrder) (x : FOvariable) (P : predicate),
  Pred_is_neg_SO (allFO x alpha) P <-> Pred_is_neg_SO alpha P.
Proof. firstorder. Qed.

Lemma Pred_is_neg_SO_exFO  : forall (alpha : SecOrder) (x : FOvariable) (P : predicate),
  Pred_is_neg_SO (exFO x alpha) P <-> Pred_is_neg_SO alpha P.
Proof. firstorder. Qed.

Lemma Pred_is_neg_SO_conjSO_l : forall (alpha1 alpha2 : SecOrder) 
                                    (P : predicate),
  Pred_in_SO alpha1 P ->
  Pred_is_neg_SO (conjSO alpha1 alpha2) P ->
  Pred_is_neg_SO alpha1 P.
Proof.
  intros alpha1 alpha2 P Hpocc [H1 H2].
  constructor. firstorder.
  intros i Hocc Hat. pose proof Hocc as Hocc'.
  eapply is_neg_SO_conjSO_l in Hocc.
  apply Hocc. apply H2. apply occ_in_SO_conjSO2. firstorder.
  simpl. rewrite at_pred_app_l;firstorder.
Qed.

Lemma Pred_is_neg_SO_conjSO_r : forall (alpha1 alpha2 : SecOrder) 
                                    (P : predicate),
  Pred_in_SO alpha2 P ->
  Pred_is_neg_SO (conjSO alpha1 alpha2) P ->
  Pred_is_neg_SO alpha2 P.
Proof.
  intros alpha1 alpha2 P Hpocc [H1 H2].
  constructor. firstorder.
  intros i Hocc Hat. pose proof Hocc as Hocc'.
  assert (i <> 0) as Hass2. firstorder.
  assert (i = i + length (preds_in alpha1) - length (preds_in alpha1)) as Hass.
    firstorder. rewrite Hass in *.
  eapply is_neg_SO_conjSO_r in Hocc. rewrite <- Hass in *.
  apply Hocc. apply H2. apply occ_in_SO_conjSO2. firstorder.
  simpl. rewrite PeanoNat.Nat.add_comm. rewrite at_pred_app_r. auto.
  destruct i; firstorder.
  rewrite PeanoNat.Nat.add_comm.
  apply occ_in_SO_preds_in. firstorder.
Qed.

Lemma Pred_is_neg_SO_disjSO_l : forall (alpha1 alpha2 : SecOrder) 
                                    (P : predicate),
  Pred_in_SO alpha1 P ->
  Pred_is_neg_SO (disjSO alpha1 alpha2) P ->
  Pred_is_neg_SO alpha1 P.
Proof.
  intros alpha1 alpha2 P Hpocc [H1 H2].
  constructor. firstorder.
  intros i Hocc Hat. pose proof Hocc as Hocc'.
  eapply is_neg_SO_disjSO_l in Hocc.
  apply Hocc. apply H2. apply occ_in_SO_disjSO2. firstorder.
  simpl. rewrite at_pred_app_l;firstorder.
Qed.

Lemma Pred_is_neg_SO_disjSO_r : forall (alpha1 alpha2 : SecOrder) 
                                    (P : predicate),
  Pred_in_SO alpha2 P ->
  Pred_is_neg_SO (disjSO alpha1 alpha2) P ->
  Pred_is_neg_SO alpha2 P.
Proof.
  intros alpha1 alpha2 P Hpocc [H1 H2].
  constructor. firstorder.
  intros i Hocc Hat. pose proof Hocc as Hocc'.
  assert (i <> 0) as Hass2. firstorder.
  assert (i = i + length (preds_in alpha1) - length (preds_in alpha1)) as Hass.
    firstorder. rewrite Hass in *.
  eapply is_neg_SO_disjSO_r in Hocc. rewrite <- Hass in *.
  apply Hocc. apply H2. apply occ_in_SO_disjSO2. firstorder.
  simpl. rewrite PeanoNat.Nat.add_comm. rewrite at_pred_app_r. auto.
  destruct i; firstorder.
  rewrite PeanoNat.Nat.add_comm.
  apply occ_in_SO_preds_in. firstorder.
Qed.

Lemma Pred_is_pos_SO_implSO_l : forall (alpha1 alpha2 : SecOrder) 
                                    (P : predicate),
  Pred_in_SO alpha1 P ->
  Pred_is_pos_SO (implSO alpha1 alpha2) P ->
  Pred_is_neg_SO alpha1 P.
Proof.
  intros alpha1 alpha2 P Hpocc [H1 H2].
  constructor. firstorder.
  intros i Hocc Hat. pose proof Hocc as Hocc'.
  eapply is_pos_SO_implSO_l2 in Hocc'. 
  pose proof (pos_or_neg_SO _ _ Hocc) as H3.
  destruct H3. contradiction. auto.
  apply H2. apply occ_in_SO_implSO2. auto.
  simpl. rewrite at_pred_app_l. auto. firstorder.
Qed.

Lemma Pred_is_neg_SO_implSO_l : forall (alpha1 alpha2 : SecOrder) 
                                    (P : predicate),
  Pred_in_SO alpha1 P ->
  Pred_is_neg_SO (implSO alpha1 alpha2) P ->
  Pred_is_pos_SO alpha1 P.
Proof.
  intros alpha1 alpha2 P Hpocc [H1 H2].
  constructor. firstorder.
  intros i Hocc Hat. pose proof Hocc as Hocc'.
  eapply is_neg_SO_implSO_l2 in Hocc'. 
  pose proof (pos_or_neg_SO _ _ Hocc) as H3.
  destruct H3. auto. contradiction.
  apply H2. apply occ_in_SO_implSO2. auto.
  simpl. rewrite at_pred_app_l. auto. firstorder.
Qed. 

Lemma Pred_is_pos_SO_implSO_r : forall (alpha1 alpha2 : SecOrder) 
                                    (P : predicate),
  Pred_in_SO alpha2 P  ->
  Pred_is_pos_SO (implSO alpha1 alpha2) P ->
  Pred_is_pos_SO alpha2 P.
Proof.
  intros alpha1 alpha2 P Hpocc [H1 H2].
  constructor. firstorder.
  intros i Hocc Hat. pose proof Hocc as Hocc'.
  assert (i <> 0) as Hass2. firstorder.
  assert (i = i + length (preds_in alpha1) - length (preds_in alpha1)) as Hass.
    firstorder. rewrite Hass in *.
  eapply is_pos_SO_implSO_r in Hocc. rewrite <- Hass in *.
  apply Hocc. apply H2. apply occ_in_SO_implSO2. firstorder.
  simpl. rewrite PeanoNat.Nat.add_comm. rewrite at_pred_app_r. auto.
  destruct i; firstorder.
  rewrite PeanoNat.Nat.add_comm.
  apply occ_in_SO_preds_in. firstorder.
Qed. 

Lemma Pred_is_neg_SO_implSO_r : forall (alpha1 alpha2 : SecOrder) 
                                    (P : predicate),
  Pred_in_SO alpha2 P ->
  Pred_is_neg_SO (implSO alpha1 alpha2) P ->
  Pred_is_neg_SO alpha2 P.
Proof.
  intros alpha1 alpha2 P Hpocc [H1 H2].
  constructor. firstorder.
  intros i Hocc Hat. pose proof Hocc as Hocc'.
  assert (i <> 0) as Hass2. firstorder.
  assert (i = i + length (preds_in alpha1) - length (preds_in alpha1)) as Hass.
    firstorder. rewrite Hass in *.
  eapply is_neg_SO_implSO_r in Hocc. rewrite <- Hass in *.
  apply Hocc. apply H2. apply occ_in_SO_implSO2. firstorder.
  simpl. rewrite PeanoNat.Nat.add_comm. rewrite at_pred_app_r. auto.
  destruct i; firstorder.
  rewrite PeanoNat.Nat.add_comm.
  apply occ_in_SO_preds_in. firstorder.
Qed.

Lemma is_neg_SO_allSO : forall (alpha : SecOrder) (P : predicate) (i : nat),
  occ_in_SO alpha i ->
  is_neg_SO (allSO P alpha) (S i) <-> is_neg_SO alpha i.
Proof.
  intros alpha P i Hocc; split; intros [H1 H2]; simpl in H2.
    destruct i. discriminate.  firstorder.
    
    constructor. apply occ_in_SO_allSO. auto.
    simpl. destruct i. firstorder. auto.
Qed.

Lemma is_neg_SO_exSO : forall (alpha : SecOrder) (P : predicate) (i : nat),
  occ_in_SO alpha i ->
  is_neg_SO (exSO P alpha) (S i) <-> is_neg_SO alpha i.
Proof.
  intros alpha P i Hocc; split; intros [H1 H2]; simpl in H2.
    destruct i. discriminate.  firstorder.
    
    constructor. apply occ_in_SO_exSO. auto.
    simpl. destruct i. firstorder. auto.
Qed.

Lemma Pred_is_neg_SO_allSO : forall (alpha : SecOrder) (P Q : predicate),
Pred_in_SO alpha P ->
Pred_is_neg_SO (allSO Q alpha) P -> Pred_is_neg_SO alpha P.
Proof.
  intros alpha P Q Hpocc [H1 H2]. 
  constructor. firstorder.
  intros i Hocc Hat. eapply is_neg_SO_allSO.
  auto. apply H2.  apply occ_in_SO_allSO. auto.
  simpl. destruct i. firstorder. auto.
Qed.

Lemma Pred_is_neg_SO_exSO : forall (alpha : SecOrder) (P Q : predicate),
Pred_in_SO alpha P ->
Pred_is_neg_SO (exSO Q alpha) P -> Pred_is_neg_SO alpha P.
Proof.
  intros alpha P Q Hpocc [H1 H2]. 
  constructor. firstorder.
  intros i Hocc Hat. eapply is_neg_SO_exSO.
  auto. apply H2.  apply occ_in_SO_exSO. auto.
  simpl. destruct i. firstorder. auto.
Qed.