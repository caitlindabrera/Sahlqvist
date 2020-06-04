Require Export med_mods is_pos_neg_SO_lemmas Pred_is_pos_SO.
Require Import Num_Occ Num_occ_l Indicies.

Lemma is_pos_rep_pred_predSO : forall (P Q : predicate)
                                 (cond : SecOrder) (x y : FOvariable)
                                (i : nat),
  FO_frame_condition cond = true ->
    occ_in_SO (replace_pred (predSO P y) Q x cond) i ->
      (is_pos_SO (predSO P y) (identify_rev (predSO P y) Q i) <->
        is_pos_SO (replace_pred (predSO P y) Q x cond) i).
Proof.
  intros P Q cond x y i Hcond Hocc.
  unfold identify_rev. simpl.
  simpl. destruct i. contradiction (occ_in_SO_0 _ Hocc).
  destruct (predicate_dec Q P) as [H1 | H1].
  apply FO_frame_condition_occ_in_SO in Hocc. contradiction.
  simpl. rewrite predicate_dec_l; auto.
  apply rep_FOv_FO_frame_condition. auto.

  destruct i. firstorder.
  inversion Hocc as [H2 H3]. simpl in *.
  if_then_else_dest_blind; simpl in *; firstorder.
Qed.

Lemma is_pos_rep_pred_relatSO : forall (Q : predicate)
                                 (cond : SecOrder) (x y1 y2 : FOvariable)
                                (i : nat),
  FO_frame_condition cond = true ->
    occ_in_SO (replace_pred (relatSO y1 y2) Q x cond) i ->
      (is_pos_SO (relatSO y1 y2) (identify_rev (relatSO y1 y2) Q i) <->
        is_pos_SO (replace_pred (relatSO y1 y2) Q x cond) i).
Proof.
  intros Q cond x y1 y2 i Hcond Hocc.
  unfold identify_rev. simpl in *.
  case_eq i; intros;
    split; intros H0; auto.
  contradiction (is_pos_SO_0 _ H0).
  inversion H0 as [H1 H2].
  contradiction (occ_in_SO_relatSO _ _ _ H1).
Qed.

Lemma is_pos_rep_pred_eqFO : forall (Q : predicate)
                                 (cond : SecOrder) (x y1 y2 : FOvariable)
                                (i : nat),
  FO_frame_condition cond = true ->
    occ_in_SO (replace_pred (eqFO y1 y2) Q x cond) i ->
      (is_pos_SO (eqFO y1 y2) (identify_rev (eqFO y1 y2) Q i) <->
        is_pos_SO (replace_pred (eqFO y1 y2) Q x cond) i).
Proof.
  intros Q cond x y1 y2 i Hcond Hocc.
  unfold identify_rev. simpl in *.
  case_eq i; intros;
    split; intros; auto.
    contradiction (is_pos_SO_0 _ H0).
  inversion H0 as [H1 H2].
  contradiction (occ_in_SO_eqFO _ _ _ H1).
Qed.

Lemma is_pos_rep_pred_allFO : forall (alpha : SecOrder) (Q : predicate)
                                 (cond : SecOrder) (x y: FOvariable)
                                (i : nat),
  (forall (Q : predicate) (cond : SecOrder) (x : FOvariable) (i : nat),
          FO_frame_condition cond = true ->
          occ_in_SO (replace_pred alpha Q x cond) i ->
          is_pos_SO alpha (identify_rev alpha Q i) <-> 
              is_pos_SO (replace_pred alpha Q x cond) i) ->
    FO_frame_condition cond = true ->
      (occ_in_SO (replace_pred (allFO y alpha) Q x cond) i) ->
        (is_pos_SO (allFO y alpha) (identify_rev (allFO y alpha) Q i) <->
         is_pos_SO (replace_pred (allFO y alpha) Q x cond) i).
Proof.
  intros alpha Q cond x y i IHalpha Hcond Hocc.
  unfold identify_rev in *.
  simpl preds_in in *.
  rewrite rep_pred_allFO in *.
  do 2 rewrite is_pos_SO_allFO.
  rewrite occ_in_SO_allFO in *.
  apply IHalpha; assumption.
Qed.

Lemma is_pos_rep_pred_exFO : forall (alpha : SecOrder) (Q : predicate)
                                 (cond : SecOrder) (x y: FOvariable)
                                (i : nat),
  (forall (Q : predicate) (cond : SecOrder) (x : FOvariable) (i : nat),
          FO_frame_condition cond = true ->
          occ_in_SO (replace_pred alpha Q x cond) i ->
          is_pos_SO alpha (identify_rev alpha Q i) <-> 
              is_pos_SO (replace_pred alpha Q x cond) i) ->
    FO_frame_condition cond = true ->
      (occ_in_SO (replace_pred (exFO y alpha) Q x cond) i) ->
        (is_pos_SO (exFO y alpha) (identify_rev (exFO y alpha) Q i) <->
         is_pos_SO (replace_pred (exFO y alpha) Q x cond) i).
Proof.
  intros alpha Q cond x y i IHalpha Hcond Hocc.
  unfold identify_rev in *; simpl preds_in in *.
  destruct y.
  rewrite rep_pred_exFO in *.
  do 2  rewrite is_pos_SO_exFO.
  apply IHalpha; auto. 
Qed.

Lemma is_pos_rep_pred_negSO : forall (alpha : SecOrder) (Q : predicate)
                                 (cond : SecOrder) (x: FOvariable)
                                (i : nat),
  (forall (Q : predicate) (cond : SecOrder) (x : FOvariable) (i : nat),
          FO_frame_condition cond = true ->
          occ_in_SO (replace_pred alpha Q x cond) i ->
          is_pos_SO alpha (identify_rev alpha Q i) <-> 
              is_pos_SO (replace_pred alpha Q x cond) i) ->
    FO_frame_condition cond = true ->
      (occ_in_SO (replace_pred (negSO alpha) Q x cond) i) ->
        (is_pos_SO (negSO alpha) (identify_rev (negSO alpha) Q i) <->
         is_pos_SO (replace_pred (negSO alpha) Q x cond) i).
Proof.
  intros alpha Q cond x i IHalpha Hcond Hocc.
  destruct Q as [Qm].
  rewrite rep_pred_negSO in Hocc.
  rewrite occ_in_SO_negSO in Hocc.
  unfold identify_rev in *.
  simpl preds_in in *.
  rewrite rep_pred_negSO.
  split; intros Hpos.
    apply is_pos_SO_negSO in Hpos.
    apply is_pos_SO_negSO2 ; try assumption.
    specialize (IHalpha (Pred Qm) cond x i Hcond Hocc).
    destruct IHalpha as [fwd rev].
    intros H. apply Hpos. apply rev. auto.

    apply is_pos_SO_negSO2; try assumption.
      apply occ_rep_pred2 in Hocc; try assumption.
    specialize (IHalpha (Pred Qm) cond x i Hcond Hocc).
    destruct IHalpha as [fwd rev].
    intros H. apply is_pos_SO_negSO in Hpos. apply Hpos.
    auto.
Qed.

Lemma is_pos_rep_pred_conjSO : forall (alpha1 alpha2 : SecOrder) (Q : predicate)
                                 (cond : SecOrder) (x: FOvariable)
                                (i : nat),
  (forall (Q : predicate) (cond : SecOrder) (x : FOvariable) (i : nat),
           FO_frame_condition cond = true ->
           occ_in_SO (replace_pred alpha1 Q x cond) i ->
           is_pos_SO alpha1 (identify_rev alpha1 Q i) <-> 
            is_pos_SO (replace_pred alpha1 Q x cond) i) ->
  (forall (Q : predicate) (cond : SecOrder) (x : FOvariable) (i : nat),
           FO_frame_condition cond = true ->
           occ_in_SO (replace_pred alpha2 Q x cond) i ->
           is_pos_SO alpha2 (identify_rev alpha2 Q i) <->
            is_pos_SO (replace_pred alpha2 Q x cond) i) ->
    FO_frame_condition cond = true ->
      occ_in_SO (replace_pred (conjSO alpha1 alpha2) Q x cond) i ->
        (is_pos_SO (conjSO alpha1 alpha2) (identify_rev (conjSO alpha1 alpha2) Q i) <->
        is_pos_SO (replace_pred (conjSO alpha1 alpha2) Q x cond) i).
Proof.
  intros alpha1 alpha2 Q cond x i IHalpha1 IHalpha2 Hcond Hocc.
  rewrite rep_pred_conjSO in *;  unfold identify_rev in *.
  simpl preds_in in *.
  pose proof (occ_in_SO_conjSO2_fwd2 _ _ _ Hocc) as Hocc'.
  destruct Hocc' as [Hocc' | Hocc'].
  + rewrite identify_rev_l_app2.
    rewrite is_pos_SO_conjSO_l; try assumption.
    rewrite is_pos_SO_conjSO_l; try assumption.
    apply IHalpha1; try assumption.
    apply occ_rep_pred2 in Hocc'; try assumption.
    pose proof (occ_in_SO_le _ _ Hocc') as H.
    rewrite preds_in_rep_pred in H; try assumption.
    rewrite num_occ__l. auto.
  + rewrite identify_rev_l_app_r.
    destruct Hocc' as [Hocc'l Hocc'r].
    pose proof Hocc'l as Hoccl.
    apply occ_in_SO_f in Hocc'l.
    destruct Hocc'l as [Hocc'l | Hocc'l].
      subst. contradiction (occ_in_SO_0 _ Hocc).
    rewrite preds_in_rep_pred in *; try assumption.
    unfold num_occ in *.
    rewrite length_ind in *.
    rewrite is_pos_SO_conjSO_r.
    rewrite is_pos_SO_conjSO_r; try assumption.
    rewrite preds_in_rep_pred in *; auto.
    rewrite num_occ_ind_l_rev.
    rewrite PeanoNat.Nat.add_sub.
    apply IHalpha2; auto.
      rewrite preds_in_rep_pred; try assumption.
      rewrite num_occ_ind_l_rev.
      assumption.

      apply occ_in_SO_excess. intros HH.
      case_eq (FO_frame_condition alpha2); intros Hun.
      rewrite (FO_frame_condition_preds_in _ Hun) in *.
      simpl in *.
      rewrite (rep_pred_FO_frame_condition alpha2) in *; try assumption.
      apply occ_in_SO_le in Hocc'r.
      apply occ_in_SO_f in Hoccl.
      destruct Hoccl as [Hoccl | Hoccl].
        subst. firstorder. 
      rewrite preds_in_rep_pred in Hoccl; try assumption.
      rewrite (FO_frame_condition_preds_in _ Hun) in *.
      simpl in *. apply Le.le_n_0_eq in Hocc'r.
      rewrite <- Hocc'r in *. lia.

      rewrite (id_rev_0 alpha2 Q (i - (length (preds_in alpha1) - 
              length (indicies_l_rev (preds_in alpha1) Q)))) in Hocc'r.
      contradiction  (occ_in_SO_0 _ Hocc'r). auto.
      unfold identify_rev.
      assumption.  

      rewrite PeanoNat.Nat.add_sub. 
      eapply occ_rep_pred2. apply Hcond. apply Hocc'r.
      firstorder. rewrite indicies_l_rev_app. rewrite app_length.
      rewrite map_length.
      do 2 rewrite <- num_occ_ind_l_rev. 
      pose proof (num_occ_preds_in alpha1 Q).
      pose proof (num_occ_preds_in alpha2 Q).
      apply occ_in_SO_le in Hocc. simpl in *. rewrite app_length in Hocc.
      do 2 (rewrite preds_in_rep_pred in Hocc; auto).
      lia.

    unfold gt. destruct Hocc' as [Hocc1 Hocc2].
    unfold lt. destruct i. contradiction (occ_in_SO_0 _ Hocc).
    apply Le.le_n_S. rewrite <- num_occ_ind_l_rev.
    erewrite <- preds_in_rep_pred with (x := x). 2 : apply Hcond.
    inversion Hocc2. firstorder.    
Qed.

Lemma is_pos_rep_pred_disjSO : forall (alpha1 alpha2 : SecOrder) (Q : predicate)
                                 (cond : SecOrder) (x: FOvariable)
                                (i : nat),
  (forall (Q : predicate) (cond : SecOrder) (x : FOvariable) (i : nat),
           FO_frame_condition cond = true ->
           occ_in_SO (replace_pred alpha1 Q x cond) i ->
           is_pos_SO alpha1 (identify_rev alpha1 Q i) <-> 
            is_pos_SO (replace_pred alpha1 Q x cond) i) ->
  (forall (Q : predicate) (cond : SecOrder) (x : FOvariable) (i : nat),
           FO_frame_condition cond = true ->
           occ_in_SO (replace_pred alpha2 Q x cond) i ->
           is_pos_SO alpha2 (identify_rev alpha2 Q i) <->
            is_pos_SO (replace_pred alpha2 Q x cond) i ) ->
    FO_frame_condition cond = true ->
      occ_in_SO (replace_pred (disjSO alpha1 alpha2) Q x cond) i ->
        (is_pos_SO (disjSO alpha1 alpha2) (identify_rev (disjSO alpha1 alpha2) Q i)  <->
        is_pos_SO (replace_pred (disjSO alpha1 alpha2) Q x cond) i).
Proof.
  intros alpha1 alpha2 Q cond x i IHalpha1 IHalpha2 Hcond Hocc.
  rewrite rep_pred_disjSO in *;  unfold identify_rev in *.
  simpl preds_in in *.
  pose proof (occ_in_SO_disjSO2_fwd2 _ _ _ Hocc) as Hocc'.
  destruct Hocc' as [Hocc' | Hocc'].
  + rewrite identify_rev_l_app2.
    rewrite is_pos_SO_disjSO_l; try assumption.
    rewrite is_pos_SO_disjSO_l; try assumption.
    apply IHalpha1; try assumption.
    apply occ_rep_pred2 in Hocc'; try assumption.
    pose proof (occ_in_SO_le _ _ Hocc') as H.
    rewrite preds_in_rep_pred in H; try assumption.
    rewrite num_occ__l. auto.
  + rewrite identify_rev_l_app_r.
    destruct Hocc' as [Hocc'l Hocc'r].
    pose proof Hocc'l as Hoccl.
    apply occ_in_SO_f in Hocc'l.
    destruct Hocc'l as [Hocc'l | Hocc'l].
      subst. contradiction (occ_in_SO_0 _ Hocc).
    rewrite preds_in_rep_pred in *; try assumption.
    unfold num_occ in *.
    rewrite length_ind in *.
    rewrite is_pos_SO_disjSO_r.
    rewrite is_pos_SO_disjSO_r; try assumption.
    rewrite preds_in_rep_pred in *; auto.
    rewrite num_occ_ind_l_rev.
    rewrite PeanoNat.Nat.add_sub.
    apply IHalpha2; auto.
      rewrite preds_in_rep_pred; try assumption.
      rewrite num_occ_ind_l_rev.
      assumption.

      apply occ_in_SO_excess. intros HH.
      case_eq (FO_frame_condition alpha2); intros Hun.
      rewrite (FO_frame_condition_preds_in _ Hun) in *.
      simpl in *.
      rewrite (rep_pred_FO_frame_condition alpha2) in *; try assumption.
      apply occ_in_SO_le in Hocc'r.
      apply occ_in_SO_f in Hoccl.
      destruct Hoccl as [Hoccl | Hoccl].
        subst. simpl in *. inversion Hocc'l.
      rewrite preds_in_rep_pred in Hoccl; try assumption.
      rewrite (FO_frame_condition_preds_in _ Hun) in *.
      simpl in *. apply Le.le_n_0_eq in Hocc'r.
      rewrite <- Hocc'r in *. lia.

      rewrite (id_rev_0 alpha2 Q (i - (length (preds_in alpha1) - 
              length (indicies_l_rev (preds_in alpha1) Q)))) in Hocc'r.
      contradiction  (occ_in_SO_0 _ Hocc'r). auto.
      unfold identify_rev.
      assumption. 

      rewrite PeanoNat.Nat.add_sub. 
      eapply occ_rep_pred2. apply Hcond. apply Hocc'r.
      firstorder. rewrite indicies_l_rev_app. rewrite app_length.
      rewrite map_length.
      do 2 rewrite <- num_occ_ind_l_rev. 
      pose proof (num_occ_preds_in alpha1 Q).
      pose proof (num_occ_preds_in alpha2 Q).
      apply occ_in_SO_le in Hocc. simpl in *. rewrite app_length in Hocc.
      do 2 (rewrite preds_in_rep_pred in Hocc; auto).
      lia.

    unfold gt. destruct Hocc' as [Hocc1 Hocc2].
    unfold lt. destruct i. contradiction (occ_in_SO_0 _ Hocc).
    apply Le.le_n_S. rewrite <- num_occ_ind_l_rev.
    erewrite <- preds_in_rep_pred with (x := x). 2 : apply Hcond.
    inversion Hocc2. firstorder.    
Qed.

Lemma is_pos_rep_pred_allSO : forall (alpha : SecOrder) (P Q : predicate)
                                 (cond : SecOrder) (x: FOvariable)
                                (i : nat),
  (forall (Q : predicate) (cond : SecOrder) (x : FOvariable) (i : nat),
          FO_frame_condition cond = true ->
          occ_in_SO (replace_pred alpha Q x cond) i ->
          is_pos_SO alpha (identify_rev alpha Q i) <-> 
              is_pos_SO (replace_pred alpha Q x cond) i ) ->
    FO_frame_condition cond = true ->
      (occ_in_SO (replace_pred (allSO P alpha) Q x cond) i) ->
        (is_pos_SO (allSO P alpha) (identify_rev (allSO P alpha) Q i) <->
         is_pos_SO (replace_pred (allSO P alpha) Q x cond) i).
Proof.
  intros alpha P Q cond x i IHalpha Hcond Hocc.
  case_eq i. intros H0. subst. firstorder.
  intros n Hn. rewrite <- Hn.
  rewrite rep_pred_allSO in *.
  unfold identify_rev.
  simpl preds_in.
  rewrite identify_rev_l_cons.
  destruct (predicate_dec Q P). subst Q.
  + split; intros HH.
    * apply (is_pos_SO_allSO alpha) in HH.
      apply IHalpha; auto.
      eapply occ_rep_pred2. apply Hcond. apply Hocc.
    * apply (is_pos_SO_allSO alpha). 
      eapply occ_rep_pred2. apply Hcond. apply HH.
      eapply IHalpha. 2 : apply Hocc. all : auto.
  + subst i. destruct n. 
    * simpl. rewrite identify_rev_l_0.
      split; intros HH. 
      ++ constructor; auto. 
      ++ constructor. apply occ_in_SO_allSO_1. auto.
    * simpl. apply occ_in_SO_allSO_rev in Hocc. 
      split; intros HH.
      ++ apply (is_pos_SO_allSO alpha) in HH.
         apply (is_pos_SO_allSO). auto. apply IHalpha; auto.
         apply occ_rep_pred2 in Hocc; auto.
      ++ apply is_pos_SO_allSO.
         apply occ_rep_pred2 in Hocc; auto.
         eapply IHalpha. 2 : apply Hocc. auto.
         apply (is_pos_SO_allSO (replace_pred alpha _ _ _)) in HH; auto.
  + firstorder.
Qed. 

Lemma is_pos_rep_pred_exSO : forall (alpha : SecOrder) (P Q : predicate)
                                 (cond : SecOrder) (x: FOvariable)
                                (i : nat),
  (forall (Q : predicate) (cond : SecOrder) (x : FOvariable) (i : nat),
          FO_frame_condition cond = true ->
          occ_in_SO (replace_pred alpha Q x cond) i ->
          is_pos_SO alpha (identify_rev alpha Q i) <-> 
              is_pos_SO (replace_pred alpha Q x cond) i) ->
    FO_frame_condition cond = true ->
      (occ_in_SO (replace_pred (exSO P alpha) Q x cond) i) ->
        (is_pos_SO (exSO P alpha) (identify_rev (exSO P alpha) Q i) <->
         is_pos_SO (replace_pred (exSO P alpha) Q x cond) i).
Proof.
  intros alpha P Q cond x i IHalpha Hcond Hocc.
  case_eq i. intros H0. subst. firstorder.
  intros n Hn. rewrite <- Hn.
  rewrite rep_pred_exSO in *.
  unfold identify_rev.
  simpl preds_in.
  rewrite identify_rev_l_cons.
  destruct (predicate_dec Q P). subst Q.
  + split; intros HH.
    * apply (is_pos_SO_exSO alpha) in HH.
      apply IHalpha; auto.
      eapply occ_rep_pred2. apply Hcond. apply Hocc.
    * apply (is_pos_SO_exSO alpha). 
      eapply occ_rep_pred2. apply Hcond. apply HH.
      eapply IHalpha. 2 : apply Hocc. all : auto.
  + subst i. destruct n. 
    * simpl. rewrite identify_rev_l_0.
      split; intros HH. 
      ++ constructor; auto. 
      ++ constructor. apply occ_in_SO_exSO_1. auto.
    * simpl. apply occ_in_SO_exSO_rev in Hocc. 
      split; intros HH.
      ++ apply (is_pos_SO_exSO alpha) in HH.
         apply (is_pos_SO_exSO). auto. apply IHalpha; auto.
         apply occ_rep_pred2 in Hocc; auto.
      ++ apply is_pos_SO_exSO.
         apply occ_rep_pred2 in Hocc; auto.
         eapply IHalpha. 2 : apply Hocc. auto.
         apply (is_pos_SO_exSO (replace_pred alpha _ _ _)) in HH; auto.
  + firstorder.
Qed. 

Lemma is_pos_rep_pred_implSO : forall (alpha1 alpha2 : SecOrder) (Q : predicate)
                                 (cond : SecOrder) (x : FOvariable)
                                (i : nat),
  (forall (Q : predicate) (cond : SecOrder) (x : FOvariable) (i : nat),
           FO_frame_condition cond = true ->
           occ_in_SO (replace_pred alpha1 Q x cond) i ->
           is_pos_SO alpha1 (identify_rev alpha1 Q i) <-> 
            is_pos_SO (replace_pred alpha1 Q x cond) i) ->
  (forall (Q : predicate) (cond : SecOrder) (x : FOvariable) (i : nat),
           FO_frame_condition cond = true ->
           occ_in_SO (replace_pred alpha2 Q x cond) i ->
           is_pos_SO alpha2 (identify_rev alpha2 Q i) <-> 
            is_pos_SO (replace_pred alpha2 Q x cond) i ) ->
  FO_frame_condition cond = true ->
  occ_in_SO (replace_pred (implSO alpha1 alpha2) Q x cond) i ->
    (is_pos_SO (implSO alpha1 alpha2) (identify_rev (implSO alpha1 alpha2) Q i) <->
    is_pos_SO (replace_pred (implSO alpha1 alpha2) Q x cond) i).
Proof.
  intros alpha1 alpha2 Q cond x i IHalpha1 IHalpha2 Hcond Hocc.
  rewrite rep_pred_implSO in *;  unfold identify_rev in *.
  simpl preds_in in *.
  pose proof (occ_in_SO_implSO2_fwd2 _ _ _ Hocc) as Hocc'.
  destruct Hocc' as [Hocc' | Hocc'].
  + rewrite identify_rev_l_app2.
    split; intros H;
     apply is_pos_SO_implSO_l2 in H; auto.
    ++ eapply is_pos_SO_implSO_l_t. auto.
       intros HH. apply IHalpha1 in HH. contradiction.
       auto. auto. 
    ++ eapply occ_rep_pred2. 2 : apply Hocc'.
       auto.
    ++ eapply is_pos_SO_implSO_l_t. eapply occ_rep_pred2.
       2 : apply Hocc'. auto. intros HH.
       eapply IHalpha1 in HH. contradiction (H HH).
       auto. auto.
    ++ destruct Hocc' as [Ha Hb]. rewrite preds_in_rep_pred in Hb; auto.
       rewrite num_occ__l. auto. 
  + rewrite identify_rev_l_app_r.
    destruct Hocc' as [Hocc'l Hocc'r].
    pose proof Hocc'l as Hoccl.
    apply occ_in_SO_f in Hocc'l.
    destruct Hocc'l as [Hocc'l | Hocc'l].
      subst. contradiction (occ_in_SO_0 _ Hocc).
    rewrite preds_in_rep_pred in *; try assumption.
    unfold num_occ in *.
    rewrite length_ind in *.
    case_eq i. intros H0. subst. firstorder.
    intros nn Hnn. rewrite <- Hnn.

    rewrite is_pos_SO_implSO_r.
    rewrite is_pos_SO_implSO_r. 
    rewrite preds_in_rep_pred in *; auto.
    rewrite num_occ_ind_l_rev.
    rewrite PeanoNat.Nat.add_sub.
    apply IHalpha2; auto. auto. 
      rewrite preds_in_rep_pred; try assumption.
      rewrite num_occ_ind_l_rev.
      assumption.

      apply occ_in_SO_excess. intros HH.
      case_eq (FO_frame_condition alpha2); intros Hun.
      rewrite (FO_frame_condition_preds_in _ Hun) in *.
      simpl in *.
      rewrite (rep_pred_FO_frame_condition alpha2) in *; try assumption.
      apply occ_in_SO_le in Hocc'r.
      apply occ_in_SO_f in Hoccl.
      destruct Hoccl as [Hoccl | Hoccl].
        subst. simpl in *. inversion Hocc'l.
      rewrite preds_in_rep_pred in Hoccl; try assumption.
      rewrite (FO_frame_condition_preds_in _ Hun) in *.
      simpl in *. apply Le.le_n_0_eq in Hocc'r.
      rewrite <- Hocc'r in *. lia.

      rewrite (id_rev_0 alpha2 Q (i - (length (preds_in alpha1) - 
              length (indicies_l_rev (preds_in alpha1) Q)))) in Hocc'r.
      contradiction  (occ_in_SO_0 _ Hocc'r). auto.
      unfold identify_rev.
      assumption. 

      rewrite PeanoNat.Nat.add_sub. 
      eapply occ_rep_pred2. apply Hcond. apply Hocc'r.
      firstorder. rewrite indicies_l_rev_app. rewrite app_length.
      rewrite map_length.
      do 2 rewrite <- num_occ_ind_l_rev. 
      pose proof (num_occ_preds_in alpha1 Q).
      pose proof (num_occ_preds_in alpha2 Q).
      apply occ_in_SO_le in Hocc. simpl in *. rewrite app_length in Hocc.
      do 2 (rewrite preds_in_rep_pred in Hocc; auto).
      lia.

    unfold gt. destruct Hocc' as [Hocc1 Hocc2].
    unfold lt. destruct i. contradiction (occ_in_SO_0 _ Hocc).
    apply Le.le_n_S. rewrite <- num_occ_ind_l_rev.
    erewrite <- preds_in_rep_pred with (x := x). 2 : apply Hcond.
    inversion Hocc2. firstorder.    
Qed.

Lemma is_pos_rep_pred : forall (alpha : SecOrder) (Q : predicate)
                                 (cond : SecOrder) (x : FOvariable)
                                (i : nat),
  FO_frame_condition cond = true ->
    occ_in_SO (replace_pred alpha Q x cond) i ->
      (is_pos_SO alpha (identify_rev alpha Q i) <->
        is_pos_SO (replace_pred alpha Q x cond) i).
Proof.
  induction alpha;
    intros Q cond x i Hcond Hocc.
    apply is_pos_rep_pred_predSO; assumption.
    apply is_pos_rep_pred_relatSO; assumption.
    apply is_pos_rep_pred_eqFO; assumption.
    apply is_pos_rep_pred_allFO; assumption.
    apply is_pos_rep_pred_exFO; assumption.
    apply is_pos_rep_pred_negSO; assumption.
    apply is_pos_rep_pred_conjSO; assumption.
    apply is_pos_rep_pred_disjSO; assumption.
    apply is_pos_rep_pred_implSO; assumption.
    apply is_pos_rep_pred_allSO; assumption.
    apply is_pos_rep_pred_exSO; assumption.
Qed.

Lemma P_is_pos_rep_pred : forall (alpha : SecOrder) (Q P : predicate)
                                 (cond : SecOrder) (x : FOvariable),
  FO_frame_condition cond = true ->
    Pred_in_SO (replace_pred alpha Q x cond) P ->
      Pred_is_pos_SO alpha P <->
        Pred_is_pos_SO (replace_pred alpha Q x cond) P.
Proof.
  intros alpha Q P cond x Hcond Hpocc.
  split ;intros H; inversion H as [H1 H2]; constructor; auto.
  + intros i Hocc Hat. apply is_pos_rep_pred; auto.
    apply H2; auto. eapply occ_in_SO_id_rev. 2:apply Hocc.
    auto. erewrite <- at_pred_rep_pred. apply Hat. auto. 
    auto. 
  + apply Pred_in_SO_rep_pred in Hpocc; auto.
  + intros i Hocc Hat. specialize (H2 (identify_fwd alpha Q i)).
    destruct (predicate_dec P Q) as [Heq | Hneq]. subst.
      apply Pred_in_SO_rep_pred_f in H1; auto. contradiction.
    destruct (occ_in_SO_dec (replace_pred alpha Q x cond) (identify_fwd alpha Q i)) as [Hd | Hd].
    ++ assert ( identify_fwd alpha Q i <> 0) as Hass.
         apply id_fwd_beq_nat; auto. rewrite <- Hat. auto.
       assert (Q <> at_pred (preds_in alpha) i) as Hass2.
         intros HH. subst Q. contradiction.
       erewrite <- identify_fwd_rev. eapply is_pos_rep_pred. apply Hcond.
       apply Hd. apply H2; auto. rewrite at_pred_rep_pred; auto. 
       rewrite identify_fwd_rev; auto. all : auto.
    ++ apply at_pred_occ_rep_pred in Hd; auto.
       rewrite Hd in Hat. contradiction.
Qed.
