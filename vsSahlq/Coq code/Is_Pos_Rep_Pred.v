Require Import SecOrder.
Require Import P_occurs_in_alpha.
Require Import ST_setup.
Require Import Correctness_ST.
Require Import Arith.EqNat my_bool Occ_In_Alpha.
Require Import List_machinery_impl My_List_Map.
Require Import Unary_Predless nList_egs Rep_Pred_FOv Indicies Identify.
Require Import pos_SO2 Num_Occ Bool my_bool P_occ_rep_pred at_pred List my_arith__my_leb_nat.

(* 
  Uniform_Mod_Lemmas10d
*)




Lemma is_pos_rep_pred_predSO : forall (P Q : predicate)
                                 (cond : SecOrder) (x y : FOvariable)
                                (i : nat),
  is_unary_predless cond = true ->
    occ_in_alpha (replace_pred (predSO P y) Q x cond) i = true ->
      (is_pos_SO (predSO P y) (identify_rev (predSO P y) Q i) = true <->
        is_pos_SO (replace_pred (predSO P y) Q x cond) i = true).
Proof.
  intros P Q cond x y i Hcond Hocc.
  destruct P as [Pn]; destruct Q as [Qm];
  destruct y as [ym]; destruct x as [xn].
  unfold identify_rev.
  simpl preds_in.
  simpl replace_pred.
  simpl identify_rev_l.
  simpl replace_pred in Hocc.
  case_eq (beq_nat Qm Pn); intros Hbeq; rewrite Hbeq in *.
    rewrite is_un_predless_occ_in_alpha in Hocc.
      discriminate.

      apply rep_FOv_is_unary_predless.
      assumption.

    case_eq i.
      intros Hi; rewrite Hi in *.
      simpl.
      split; intros; discriminate.

      intros j Hi; rewrite Hi in *.
      case_eq j.
        intros Hj; rewrite Hj in *.
        simpl.
        split; intros; reflexivity.

        intros k Hj; rewrite Hj in *.
        apply occ_in_alpha_predSO in Hocc.
        discriminate.
Qed.

Lemma is_pos_rep_pred_relatSO : forall (Q : predicate)
                                 (cond : SecOrder) (x y1 y2 : FOvariable)
                                (i : nat),
  is_unary_predless cond = true ->
    occ_in_alpha (replace_pred (relatSO y1 y2) Q x cond) i = true ->
      (is_pos_SO (relatSO y1 y2) (identify_rev (relatSO y1 y2) Q i) = true <->
        is_pos_SO (replace_pred (relatSO y1 y2) Q x cond) i = true).
Proof.
  intros Q cond x y1 y2 i Hcond Hocc.
  destruct x as [xn]; destruct y1 as [y1]; destruct y2 as [y2];
  destruct Q as [Qm].
  unfold identify_rev.
  simpl in *.
  case_eq i; intros;
  split; intros; assumption.
Qed.


Lemma is_pos_rep_pred_eqFO : forall (Q : predicate)
                                 (cond : SecOrder) (x y1 y2 : FOvariable)
                                (i : nat),
  is_unary_predless cond = true ->
    occ_in_alpha (replace_pred (eqFO y1 y2) Q x cond) i = true ->
      (is_pos_SO (eqFO y1 y2) (identify_rev (eqFO y1 y2) Q i) = true <->
        is_pos_SO (replace_pred (eqFO y1 y2) Q x cond) i = true).
Proof.
  intros Q cond x y1 y2 i Hcond Hocc.
  destruct x as [xn]; destruct y1 as [y1]; destruct y2 as [y2];
  destruct Q as [Qm].
  unfold identify_rev.
  simpl in *.
  case_eq i; intros;
  split; intros; assumption.
Qed.

Lemma is_pos_rep_pred_allFO : forall (alpha : SecOrder) (Q : predicate)
                                 (cond : SecOrder) (x y: FOvariable)
                                (i : nat),
  (forall (Q : predicate) (cond : SecOrder) (x : FOvariable) (i : nat),
          is_unary_predless cond = true ->
          occ_in_alpha (replace_pred alpha Q x cond) i = true ->
          is_pos_SO alpha (identify_rev alpha Q i) = true <-> 
              is_pos_SO (replace_pred alpha Q x cond) i = true) ->
    is_unary_predless cond = true ->
      (occ_in_alpha (replace_pred (allFO y alpha) Q x cond) i = true) ->
        (is_pos_SO (allFO y alpha) (identify_rev (allFO y alpha) Q i) = true <->
         is_pos_SO (replace_pred (allFO y alpha) Q x cond) i = true).
Proof.
  intros alpha Q cond x y i IHalpha Hcond Hocc.
  unfold identify_rev in *.
  simpl preds_in in *.
  rewrite rep_pred_allFO in *.
  do 2 rewrite is_pos_SO_allFO.
  rewrite occ_in_alpha_allFO in *.
  apply IHalpha; assumption.
Qed.

Lemma is_pos_rep_pred_exFO : forall (alpha : SecOrder) (Q : predicate)
                                 (cond : SecOrder) (x y: FOvariable)
                                (i : nat),
  (forall (Q : predicate) (cond : SecOrder) (x : FOvariable) (i : nat),
          is_unary_predless cond = true ->
          occ_in_alpha (replace_pred alpha Q x cond) i = true ->
          is_pos_SO alpha (identify_rev alpha Q i) = true <-> 
              is_pos_SO (replace_pred alpha Q x cond) i = true) ->
    is_unary_predless cond = true ->
      (occ_in_alpha (replace_pred (exFO y alpha) Q x cond) i = true) ->
        (is_pos_SO (exFO y alpha) (identify_rev (exFO y alpha) Q i) = true <->
         is_pos_SO (replace_pred (exFO y alpha) Q x cond) i = true).
Proof.
  intros alpha Q cond x y i IHalpha Hcond Hocc.
  unfold identify_rev in *; simpl preds_in in *.
  destruct y.
  rewrite rep_pred_exFO in *.
  do 2  rewrite is_pos_SO_exFO.
  apply IHalpha; assumption.
Qed.

Lemma is_pos_rep_pred_negSO : forall (alpha : SecOrder) (Q : predicate)
                                 (cond : SecOrder) (x: FOvariable)
                                (i : nat),
  (forall (Q : predicate) (cond : SecOrder) (x : FOvariable) (i : nat),
          is_unary_predless cond = true ->
          occ_in_alpha (replace_pred alpha Q x cond) i = true ->
          is_pos_SO alpha (identify_rev alpha Q i) = true <-> 
              is_pos_SO (replace_pred alpha Q x cond) i = true) ->
    is_unary_predless cond = true ->
      (occ_in_alpha (replace_pred (negSO alpha) Q x cond) i = true) ->
        (is_pos_SO (negSO alpha) (identify_rev (negSO alpha) Q i) = true <->
         is_pos_SO (replace_pred (negSO alpha) Q x cond) i = true).
Proof.
  intros alpha Q cond x i IHalpha Hcond Hocc.
  destruct Q as [Qm].
  rewrite rep_pred_negSO in Hocc.
  rewrite occ_in_alpha_negSO in Hocc.
  unfold identify_rev in *.
  simpl preds_in in *.
  rewrite rep_pred_negSO.
  split; intros Hpos.
    apply is_pos_SO_negSO in Hpos.
    apply is_pos_SO_negSO2 ; try assumption.
    specialize (IHalpha (Pred Qm) cond x i Hcond Hocc).
    destruct IHalpha as [fwd rev].
    apply contrapos_bool_tt in rev; try assumption.

    apply is_pos_SO_negSO2; try assumption.
      apply occ_rep_pred2 in Hocc; try assumption.
    specialize (IHalpha (Pred Qm) cond x i Hcond Hocc).
    destruct IHalpha as [fwd rev].
    apply contrapos_bool_tt in fwd; try assumption.
    apply is_pos_SO_negSO; assumption.
Qed.


Lemma is_pos_rep_pred_conjSO : forall (alpha1 alpha2 : SecOrder) (Q : predicate)
                                 (cond : SecOrder) (x: FOvariable)
                                (i : nat),
  (forall (Q : predicate) (cond : SecOrder) (x : FOvariable) (i : nat),
           is_unary_predless cond = true ->
           occ_in_alpha (replace_pred alpha1 Q x cond) i = true ->
           is_pos_SO alpha1 (identify_rev alpha1 Q i) = true <-> 
            is_pos_SO (replace_pred alpha1 Q x cond) i = true) ->
  (forall (Q : predicate) (cond : SecOrder) (x : FOvariable) (i : nat),
           is_unary_predless cond = true ->
           occ_in_alpha (replace_pred alpha2 Q x cond) i = true ->
           is_pos_SO alpha2 (identify_rev alpha2 Q i) = true <->
            is_pos_SO (replace_pred alpha2 Q x cond) i = true) ->
    is_unary_predless cond = true ->
      occ_in_alpha (replace_pred (conjSO alpha1 alpha2) Q x cond) i = true ->
        (is_pos_SO (conjSO alpha1 alpha2) (identify_rev (conjSO alpha1 alpha2) Q i) = true <->
        is_pos_SO (replace_pred (conjSO alpha1 alpha2) Q x cond) i = true).
Proof.
  intros alpha1 alpha2 Q cond x i IHalpha1 IHalpha2 Hcond Hocc.
  rewrite rep_pred_conjSO in *;  unfold identify_rev in *.
  simpl preds_in in *.
  pose proof (occ_in_alpha_conjSO2_fwd2 _ _ _ Hocc) as Hocc'.
  destruct Hocc' as [Hocc' | Hocc'].
  rewrite identify_rev_l_app.
  pose proof (occ_in_alpha_leb2 _ _ Hocc') as H.
  rewrite preds_in_rep_pred in H; try assumption.
  unfold num_occ in H; rewrite length_ind in H.
  destruct H as [Hocc1 Hocc2]; rewrite Hocc2.
  rewrite is_pos_SO_conjSO_l; try assumption.
  rewrite is_pos_SO_conjSO_l; try assumption.
    apply IHalpha1; try assumption.

  apply occ_rep_pred2 in Hocc'; try assumption.
  apply occ_in_alpha_leb2 in Hocc'; apply Hocc'.

  apply occ_in_alpha_leb2 in Hocc'.
  destruct Hocc' as [Hl Hr]; rewrite preds_in_rep_pred in Hr;
  try assumption.
  unfold num_occ in Hr;  rewrite length_ind in Hr.
  rewrite indicies_l_rev_app; rewrite app_length.
  rewrite list_map_length; rewrite arith_plus_minus_rearr.
    apply leb_plus_r.
    assumption.

    pose proof (num_occ_preds_in alpha1 Q) as H.
    rewrite num_occ_ind_l_rev in H.
    assumption.

    pose proof (num_occ_preds_in alpha2 Q) as H.
    rewrite num_occ_ind_l_rev in H.
    assumption.

  rewrite identify_rev_l_app.
  destruct Hocc' as [Hocc'l Hocc'r].
  pose proof Hocc'l as Hoccl.
  apply occ_in_alpha_f in Hocc'l.
  destruct Hocc'l as [Hocc'l | Hocc'l].
    rewrite (beq_nat_true _ _ Hocc'l) in *.
    simpl in *.
    rewrite occ_in_alpha_0 in Hocc'r.
    discriminate.

    rewrite preds_in_rep_pred in *; try assumption.
    unfold num_occ in *.
    rewrite length_ind in *.
    rewrite Hocc'l.
    rewrite is_pos_SO_conjSO_r.
    rewrite is_pos_SO_conjSO_r; try assumption.
    rewrite <- arith_plus_minus_assoc2; try assumption.
    rewrite arith_minus_refl.
    rewrite plus_zero.
    rewrite preds_in_rep_pred; try assumption.
    rewrite num_occ_ind_l_rev.
    apply IHalpha2; try assumption.
      apply leb_refl.
      rewrite preds_in_rep_pred; try assumption.
      rewrite num_occ_ind_l_rev.
      assumption.

    apply occ_in_alpha_excess.
    case_eq (beq_nat (identify_rev_l (preds_in alpha2) Q
            (i -  (length (preds_in alpha1) - 
              length (indicies_l_rev (preds_in alpha1) Q)))) 0);
    intros Hbeq.
    pose proof (beq_nat_true _ _ Hbeq) as H.
    case_eq (is_unary_predless alpha2); intros Hun.
      rewrite (un_predless_preds_in _ Hun) in *.
      simpl in *.
      rewrite (rep_pred_is_unary_predless alpha2) in *; try assumption.
      apply occ_in_alpha_leb2 in Hocc'r.
      apply occ_in_alpha_f in Hoccl.
      destruct Hoccl as [Hoccl | Hoccl].
        rewrite (beq_nat_true _ _ Hoccl) in *.
        simpl in *; rewrite occ_in_alpha_0 in *.
        discriminate.

        rewrite preds_in_rep_pred in Hoccl; try assumption.
        destruct Hocc'r as [Hl Hr].
        rewrite (un_predless_preds_in _ Hun) in *.
        simpl in Hr.
        rewrite leb_beq_zero in Hr.
        apply beq_nat_leb in Hr.
        unfold num_occ in Hoccl.
        rewrite length_ind in Hoccl.
        rewrite Hr in *.
        discriminate.

    rewrite (id_rev_0 alpha2 Q (i - (length (preds_in alpha1) - 
              length (indicies_l_rev (preds_in alpha1) Q)))) in Hocc'r.
    rewrite occ_in_alpha_0 in *.
    discriminate.
    assumption.
    unfold identify_rev.
    assumption.
    reflexivity.

  rewrite <- arith_plus_minus_assoc2.
  rewrite arith_minus_refl.
  rewrite plus_zero.
  apply (occ_rep_pred2 _ cond _ _ x); try assumption.
    apply leb_refl.

  case_eq (beq_nat i 0); intros Hbeq.
    rewrite (beq_nat_true _ _ Hbeq) in *.
    rewrite occ_in_alpha_0 in Hocc.
    discriminate.

    reflexivity.

    apply occ_in_alpha_leb2 in Hocc.
    destruct Hocc as [H1 H2].
    simpl in H2.
    rewrite app_length in H2.
    do 2 rewrite preds_in_rep_pred in H2; try assumption.
    do 2 rewrite num_occ_ind_l_rev in H2.
    rewrite indicies_l_rev_app.
    rewrite app_length. rewrite list_map_length.
    rewrite arith_plus_minus_rearr.
    assumption.

    pose proof (num_occ_preds_in alpha1 Q) as H.
    unfold num_occ in H.
    rewrite length_ind in H.
    assumption.

    pose proof (num_occ_preds_in alpha2 Q) as H.
    unfold num_occ in H.
    rewrite length_ind in H.
    assumption.
Qed.

Lemma is_pos_rep_pred_disjSO : forall (alpha1 alpha2 : SecOrder) (Q : predicate)
                                 (cond : SecOrder) (x: FOvariable)
                                (i : nat),
  (forall (Q : predicate) (cond : SecOrder) (x : FOvariable) (i : nat),
           is_unary_predless cond = true ->
           occ_in_alpha (replace_pred alpha1 Q x cond) i = true ->
           is_pos_SO alpha1 (identify_rev alpha1 Q i) = true <-> 
            is_pos_SO (replace_pred alpha1 Q x cond) i = true) ->
  (forall (Q : predicate) (cond : SecOrder) (x : FOvariable) (i : nat),
           is_unary_predless cond = true ->
           occ_in_alpha (replace_pred alpha2 Q x cond) i = true ->
           is_pos_SO alpha2 (identify_rev alpha2 Q i) = true <->
            is_pos_SO (replace_pred alpha2 Q x cond) i = true) ->
    is_unary_predless cond = true ->
      occ_in_alpha (replace_pred (disjSO alpha1 alpha2) Q x cond) i = true ->
        (is_pos_SO (disjSO alpha1 alpha2) (identify_rev (disjSO alpha1 alpha2) Q i) = true <->
        is_pos_SO (replace_pred (disjSO alpha1 alpha2) Q x cond) i = true).
Proof.
  intros alpha1 alpha2 Q cond x i IHalpha1 IHalpha2 Hcond Hocc.
  rewrite rep_pred_disjSO in *;  unfold identify_rev in *.
  simpl preds_in in *.
  pose proof (occ_in_alpha_conjSO2_fwd2 _ _ _ Hocc) as Hocc'.
  destruct Hocc' as [Hocc' | Hocc'].
  rewrite identify_rev_l_app.
  pose proof (occ_in_alpha_leb2 _ _ Hocc') as H.
  rewrite preds_in_rep_pred in H; try assumption.
  unfold num_occ in H; rewrite length_ind in H.
  destruct H as [Hocc1 Hocc2]; rewrite Hocc2.
  rewrite is_pos_SO_disjSO_l; try assumption.
  rewrite is_pos_SO_disjSO_l; try assumption.
    apply IHalpha1; try assumption.

  apply occ_rep_pred2 in Hocc'; try assumption.
  apply occ_in_alpha_leb2 in Hocc'; apply Hocc'.

  apply occ_in_alpha_leb2 in Hocc'.
  destruct Hocc' as [Hl Hr]; rewrite preds_in_rep_pred in Hr;
  try assumption.
  unfold num_occ in Hr;  rewrite length_ind in Hr.
  rewrite indicies_l_rev_app; rewrite app_length.
  rewrite list_map_length; rewrite arith_plus_minus_rearr.
    apply leb_plus_r.
    assumption.

    pose proof (num_occ_preds_in alpha1 Q) as H.
    rewrite num_occ_ind_l_rev in H.
    assumption.

    pose proof (num_occ_preds_in alpha2 Q) as H.
    rewrite num_occ_ind_l_rev in H.
    assumption.

  rewrite identify_rev_l_app.
  destruct Hocc' as [Hocc'l Hocc'r].
  pose proof Hocc'l as Hoccl.
  apply occ_in_alpha_f in Hocc'l.
  destruct Hocc'l as [Hocc'l | Hocc'l].
    rewrite (beq_nat_true _ _ Hocc'l) in *.
    simpl in *.
    rewrite occ_in_alpha_0 in Hocc'r.
    discriminate.

    rewrite preds_in_rep_pred in *; try assumption.
    unfold num_occ in *.
    rewrite length_ind in *.
    rewrite Hocc'l.
    rewrite is_pos_SO_disjSO_r.
    rewrite is_pos_SO_disjSO_r; try assumption.
    rewrite <- arith_plus_minus_assoc2; try assumption.
    rewrite arith_minus_refl.
    rewrite plus_zero.
    rewrite preds_in_rep_pred; try assumption.
    rewrite num_occ_ind_l_rev.
    apply IHalpha2; try assumption.
      apply leb_refl.
      rewrite preds_in_rep_pred; try assumption.
      rewrite num_occ_ind_l_rev.
      assumption.

    apply occ_in_alpha_excess.
    case_eq (beq_nat (identify_rev_l (preds_in alpha2) Q
            (i -  (length (preds_in alpha1) - 
              length (indicies_l_rev (preds_in alpha1) Q)))) 0);
    intros Hbeq.
    pose proof (beq_nat_true _ _ Hbeq) as H.
    case_eq (is_unary_predless alpha2); intros Hun.
      rewrite (un_predless_preds_in _ Hun) in *.
      simpl in *.
      rewrite (rep_pred_is_unary_predless alpha2) in *; try assumption.
      apply occ_in_alpha_leb2 in Hocc'r.
      apply occ_in_alpha_f in Hoccl.
      destruct Hoccl as [Hoccl | Hoccl].
        rewrite (beq_nat_true _ _ Hoccl) in *.
        simpl in *; rewrite occ_in_alpha_0 in *.
        discriminate.

        rewrite preds_in_rep_pred in Hoccl; try assumption.
        destruct Hocc'r as [Hl Hr].
        rewrite (un_predless_preds_in _ Hun) in *.
        simpl in Hr.
        rewrite leb_beq_zero in Hr.
        apply beq_nat_leb in Hr.
        unfold num_occ in Hoccl.
        rewrite length_ind in Hoccl.
        rewrite Hr in *.
        discriminate.

    rewrite (id_rev_0 alpha2 Q (i - (length (preds_in alpha1) - 
              length (indicies_l_rev (preds_in alpha1) Q)))) in Hocc'r.
    rewrite occ_in_alpha_0 in *.
    discriminate.
    assumption.
    unfold identify_rev.
    assumption.
    reflexivity.

  rewrite <- arith_plus_minus_assoc2.
  rewrite arith_minus_refl.
  rewrite plus_zero.
  apply (occ_rep_pred2 _ cond _ _ x); try assumption.
    apply leb_refl.

  case_eq (beq_nat i 0); intros Hbeq.
    rewrite (beq_nat_true _ _ Hbeq) in *.
    rewrite occ_in_alpha_0 in Hocc.
    discriminate.

    reflexivity.

    apply occ_in_alpha_leb2 in Hocc.
    destruct Hocc as [H1 H2].
    simpl in H2.
    rewrite app_length in H2.
    do 2 rewrite preds_in_rep_pred in H2; try assumption.
    do 2 rewrite num_occ_ind_l_rev in H2.
    rewrite indicies_l_rev_app.
    rewrite app_length. rewrite list_map_length.
    rewrite arith_plus_minus_rearr.
    assumption.

    pose proof (num_occ_preds_in alpha1 Q) as H.
    unfold num_occ in H.
    rewrite length_ind in H.
    assumption.

    pose proof (num_occ_preds_in alpha2 Q) as H.
    unfold num_occ in H.
    rewrite length_ind in H.
    assumption.
Qed.


Lemma is_pos_rep_pred_allSO : forall (alpha : SecOrder) (P Q : predicate)
                                 (cond : SecOrder) (x: FOvariable)
                                (i : nat),
  (forall (Q : predicate) (cond : SecOrder) (x : FOvariable) (i : nat),
          is_unary_predless cond = true ->
          occ_in_alpha (replace_pred alpha Q x cond) i = true ->
          is_pos_SO alpha (identify_rev alpha Q i) = true <-> 
              is_pos_SO (replace_pred alpha Q x cond) i = true) ->
    is_unary_predless cond = true ->
      (occ_in_alpha (replace_pred (allSO P alpha) Q x cond) i = true) ->
        (is_pos_SO (allSO P alpha) (identify_rev (allSO P alpha) Q i) = true <->
         is_pos_SO (replace_pred (allSO P alpha) Q x cond) i = true).
Proof.
  intros alpha P Q cond x i IHalpha Hcond Hocc.
  destruct P as [Pn]; destruct Q as [Qm].
  case_eq (beq_nat i 0); intros Hbeq.
    rewrite (beq_nat_true _ _ Hbeq) in *.
    rewrite occ_in_alpha_0 in Hocc.
    discriminate.
  rewrite rep_pred_allSO in *.
  simpl is_pos_SO.
  unfold identify_rev.
  simpl preds_in.
  rewrite identify_rev_l_cons.
  case_eq (beq_nat Pn Qm); intros Hbeq2.
    rewrite (beq_nat_true _ _ Hbeq2) in *.
    rewrite <- (beq_nat_refl Qm) in*.
    rewrite occ_in_alpha_allSO.
    simpl in *.
    rewrite arith_minus_zero.
    case_eq (is_unary_predless alpha); intros Hun.
      rewrite  rep_pred_is_unary_predless in Hocc; try assumption.
      rewrite is_un_predless_occ_in_alpha in Hocc; try assumption.
      discriminate.
    specialize (IHalpha _ _ _ _ Hcond Hocc).
    case_eq (beq_nat (identify_rev_l (preds_in alpha) (Pred Qm) i) 0); intros Hbeq3.
      pose proof (id_rev_0) as H.
      unfold identify_rev in H.
      specialize (H alpha (Pred Qm) i Hun (beq_nat_true _ _ Hbeq3)).
      rewrite H in *.
      rewrite occ_in_alpha_0 in Hocc.
      discriminate.

      pose proof occ_in_alpha_id_rev as H.
      unfold identify_rev in H.
      rewrite (H alpha cond (Pred Qm) i x); try assumption.
      case_eq (identify_rev_l (preds_in alpha) (Pred Qm) i).
        intros H2.
        pose proof id_rev_0 as H3. 
        unfold identify_rev in H3.
        rewrite (H3 alpha (Pred Qm) i Hun) in Hocc; try assumption.
        rewrite occ_in_alpha_0 in Hocc.
        discriminate.

        intros n H2.
        rewrite <- H2.
        apply IHalpha.

    rewrite beq_nat_comm.
    rewrite Hbeq2 in *.
    rewrite occ_in_alpha_allSO in *.
    case_eq i.
      intros Hi; rewrite Hi in *.
      rewrite occ_in_alpha_0 in Hocc.
      discriminate.

      intros j Hi; rewrite Hi in * .
      case_eq j.
        intros Hj; rewrite Hj in *.
        simpl.  
        split; intros; assumption.

        intros k Hj; rewrite Hj in *.
        simpl in *.
        rewrite arith_minus_zero.
        case_eq (is_unary_predless alpha); intros Hun.
          rewrite  rep_pred_is_unary_predless in Hocc; try assumption.
          rewrite is_un_predless_occ_in_alpha in Hocc; try assumption.
          discriminate.
        case_eq (identify_rev_l (preds_in alpha) (Pred Qm) (S k)).
          intros H.
          apply (id_rev_0 alpha (Pred Qm) (S k)) in H; try assumption.
          discriminate.

          intros n H.
          simpl.

          rewrite occ_in_alpha_allSO.
          simpl.
          rewrite Hocc.
          rewrite <- H.
          pose proof occ_in_alpha_id_rev as H2.
          unfold identify_rev in H2.
          rewrite (H2 alpha cond (Pred Qm) _ x); try assumption.
          apply IHalpha; try assumption.

    assumption.
Qed.


Lemma is_pos_rep_pred_exSO : forall (alpha : SecOrder) (P Q : predicate)
                                 (cond : SecOrder) (x: FOvariable)
                                (i : nat),
  (forall (Q : predicate) (cond : SecOrder) (x : FOvariable) (i : nat),
          is_unary_predless cond = true ->
          occ_in_alpha (replace_pred alpha Q x cond) i = true ->
          is_pos_SO alpha (identify_rev alpha Q i) = true <-> 
              is_pos_SO (replace_pred alpha Q x cond) i = true) ->
    is_unary_predless cond = true ->
      (occ_in_alpha (replace_pred (exSO P alpha) Q x cond) i = true) ->
        (is_pos_SO (exSO P alpha) (identify_rev (exSO P alpha) Q i) = true <->
         is_pos_SO (replace_pred (exSO P alpha) Q x cond) i = true).
Proof.
  intros alpha P Q cond x i IHalpha Hcond Hocc.
  destruct P as [Pn]; destruct Q as [Qm].
  case_eq (beq_nat i 0); intros Hbeq.
    rewrite (beq_nat_true _ _ Hbeq) in *.
    rewrite occ_in_alpha_0 in Hocc.
    discriminate.
  rewrite rep_pred_exSO in *.
  simpl is_pos_SO.
  unfold identify_rev.
  simpl preds_in.
  rewrite identify_rev_l_cons.
  case_eq (beq_nat Pn Qm); intros Hbeq2.
    rewrite (beq_nat_true _ _ Hbeq2) in *.
    rewrite <- (beq_nat_refl Qm) in*.
    rewrite occ_in_alpha_exSO.
    simpl in *.
    rewrite arith_minus_zero.
    case_eq (is_unary_predless alpha); intros Hun.
      rewrite  rep_pred_is_unary_predless in Hocc; try assumption.
      rewrite is_un_predless_occ_in_alpha in Hocc; try assumption.
      discriminate.
    specialize (IHalpha _ _ _ _ Hcond Hocc).
    case_eq (beq_nat (identify_rev_l (preds_in alpha) (Pred Qm) i) 0); intros Hbeq3.
      pose proof (id_rev_0) as H.
      unfold identify_rev in H.
      specialize (H alpha (Pred Qm) i Hun (beq_nat_true _ _ Hbeq3)).
      rewrite H in *.
      rewrite occ_in_alpha_0 in Hocc.
      discriminate.

      pose proof occ_in_alpha_id_rev as H.
      unfold identify_rev in H.
      rewrite (H alpha cond (Pred Qm) i x); try assumption.
      case_eq (identify_rev_l (preds_in alpha) (Pred Qm) i).
        intros H2.
        pose proof id_rev_0 as H3. 
        unfold identify_rev in H3.
        rewrite (H3 alpha (Pred Qm) i Hun) in Hocc; try assumption.
        rewrite occ_in_alpha_0 in Hocc.
        discriminate.

        intros n H2.
        rewrite <- H2.
        apply IHalpha.

    rewrite beq_nat_comm.
    rewrite Hbeq2 in *.
    rewrite occ_in_alpha_exSO in *.
    case_eq i.
      intros Hi; rewrite Hi in *.
      rewrite occ_in_alpha_0 in Hocc.
      discriminate.

      intros j Hi; rewrite Hi in * .
      case_eq j.
        intros Hj; rewrite Hj in *.
        simpl.  
        split; intros; assumption.

        intros k Hj; rewrite Hj in *.
        simpl in *.
        rewrite arith_minus_zero.
        case_eq (is_unary_predless alpha); intros Hun.
          rewrite  rep_pred_is_unary_predless in Hocc; try assumption.
          rewrite is_un_predless_occ_in_alpha in Hocc; try assumption.
          discriminate.
        case_eq (identify_rev_l (preds_in alpha) (Pred Qm) (S k)).
          intros H.
          apply (id_rev_0 alpha (Pred Qm) (S k)) in H; try assumption.
          discriminate.

          intros n H.
          simpl.

          rewrite occ_in_alpha_exSO.
          simpl.
          rewrite Hocc.
          rewrite <- H.
          pose proof occ_in_alpha_id_rev as H2.
          unfold identify_rev in H2.
          rewrite (H2 alpha cond (Pred Qm) _ x); try assumption.
          apply IHalpha; try assumption.

    assumption.
Qed.


Lemma is_pos_rep_pred_implSO : forall (alpha1 alpha2 : SecOrder) (Q : predicate)
                                 (cond : SecOrder) (x : FOvariable)
                                (i : nat),
  (forall (Q : predicate) (cond : SecOrder) (x : FOvariable) (i : nat),
           is_unary_predless cond = true ->
           occ_in_alpha (replace_pred alpha1 Q x cond) i = true ->
           is_pos_SO alpha1 (identify_rev alpha1 Q i) = true <-> 
            is_pos_SO (replace_pred alpha1 Q x cond) i = true) ->
  (forall (Q : predicate) (cond : SecOrder) (x : FOvariable) (i : nat),
           is_unary_predless cond = true ->
           occ_in_alpha (replace_pred alpha2 Q x cond) i = true ->
           is_pos_SO alpha2 (identify_rev alpha2 Q i) = true <-> 
            is_pos_SO (replace_pred alpha2 Q x cond) i = true) ->
  is_unary_predless cond = true ->
  occ_in_alpha (replace_pred (implSO alpha1 alpha2) Q x cond) i = true ->
    (is_pos_SO (implSO alpha1 alpha2) (identify_rev (implSO alpha1 alpha2) Q i) = true <->
    is_pos_SO (replace_pred (implSO alpha1 alpha2) Q x cond) i = true).
Proof.
  intros alpha1 alpha2 Q cond x i IHalpha1 IHalpha2 Hcond Hocc.
  rewrite rep_pred_implSO.
  split; intros H.
  case_eq (occ_in_alpha (replace_pred alpha1 Q x cond) i); intros Hocc2.
    rewrite id_rev_implSO_l with (cond := cond) (x := x) in H;
      try assumption.
    rewrite rep_pred_implSO in Hocc.
    pose proof is_pos_SO_implSO_l2.
    pose proof (occ_rep_pred2 _ _ _ _ _ Hcond Hocc2) as H2.
    pose proof (is_pos_SO_implSO_l2 _ _ _ H2 H) as H3.
    destruct (IHalpha1 Q cond x i Hcond Hocc2) as [fwd rev].
    pose proof (contrapos_bool_tt _ _ rev H3) as H4.
    simpl; rewrite H4; rewrite Hocc.
    apply occ_in_alpha_leb2 in Hocc2.
    destruct Hocc2 as [Ha Hb]; rewrite Hb.
    reflexivity.

    rewrite id_rev_implSO_r with (cond := cond) (x := x) in H;
      try assumption.
    rewrite rep_pred_implSO in Hocc.
    pose proof Hocc as Hocc3.
    pose proof (occ_in_alpha_implSO2_fwd _ _ _ Hocc) as H2.
    destruct H2 as [H2 | H2].
      rewrite H2 in *; discriminate.

      rewrite is_pos_SO_implSO_r; try assumption.
      apply IHalpha2; try assumption.

      rewrite is_pos_SO_implSO_r in H.
      rewrite arith_plus_comm in H.
      rewrite arith_plus_3 in H.
      assumption.

      rewrite arith_plus_comm.
      case_eq (beq_nat (identify_rev alpha2 Q 
              (i - length (preds_in (replace_pred alpha1 Q x cond))))
              0 ); intros Hbeq.
        apply occ_rep_pred2 in H2;
          try assumption.
        rewrite (beq_nat_true _ _ Hbeq) in *.
        rewrite occ_in_alpha_0 in *; discriminate.

      apply occ_in_alpha_preds_in; try assumption.

      rewrite arith_plus_comm.
      rewrite arith_plus_3.
      apply occ_rep_pred2 with (cond := cond) (x := x);
        try assumption.

    rewrite rep_pred_implSO in Hocc.
    apply occ_in_alpha_implSO2_fwd in Hocc.
    destruct Hocc as [Hocc | Hocc].
      rewrite Hocc in *; discriminate.

      assumption.

  case_eq (occ_in_alpha (replace_pred alpha1 Q x cond) i); intros Hocc2.
    rewrite id_rev_implSO_l with (cond := cond) (x := x);
      try assumption.
    rewrite rep_pred_implSO in Hocc.
    pose proof is_pos_SO_implSO_l2.
    pose proof (occ_rep_pred2 _ _ _ _ _ Hcond Hocc2) as H2.
    pose proof (is_pos_SO_implSO_l2 _ _ _ Hocc2 H) as H3.
    destruct (IHalpha1 Q cond x i Hcond Hocc2) as [fwd rev].
    pose proof (contrapos_bool_tt _ _ fwd H3) as H4.
    simpl;  rewrite H4.
    assert (occ_in_alpha (implSO alpha1 alpha2)
             (identify_rev alpha1 Q i) = true) as H5.
      apply occ_in_alpha_implSO2_rev.
      left; assumption.
    rewrite H5;  apply occ_in_alpha_leb2 in H2.
    destruct H2 as [Ha Hb];  rewrite Hb.
    reflexivity.

    rewrite rep_pred_implSO in Hocc.
    pose proof (occ_in_alpha_implSO2_fwd _ _ _ Hocc) as H2.
    destruct H2 as [H2 | H2].
      rewrite H2 in *; discriminate.
    rewrite is_pos_SO_implSO_r.
    rewrite id_rev_implSO_r with (cond := cond) (x := x);
      try assumption.
    rewrite arith_plus_comm.
    rewrite arith_plus_3.
    rewrite (IHalpha2 Q cond x _ Hcond);
      try assumption.
    rewrite is_pos_SO_implSO_r in H;
      try assumption.

    rewrite id_rev_implSO_r with (cond := cond) (x := x);
      try assumption.

    case_eq (beq_nat (identify_rev alpha2 Q 
          (i - length (preds_in (replace_pred alpha1 Q x cond)))) 0);
      intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq) in *.
      pose proof (beq_nat_true _ _ Hbeq) as Heq.
      apply id_rev_0 in Heq.
      rewrite Heq in *.
      rewrite occ_in_alpha_0 in *; discriminate.
        case_eq (is_unary_predless alpha2); intros Hun.
          rewrite rep_pred_is_unary_predless in H2;
          try assumption.
          rewrite is_un_predless_occ_in_alpha in H2;
          try assumption.
          discriminate.

          reflexivity.
      rewrite arith_plus_comm.
      apply occ_in_alpha_preds_in.
      assumption.

    rewrite id_rev_implSO_r with (cond := cond) (x := x);
      try assumption.
    rewrite arith_plus_comm.
    rewrite arith_plus_3.
    apply occ_rep_pred2 with (cond := cond) (x := x); 
    assumption.
Qed.

Lemma is_pos_rep_pred : forall (alpha : SecOrder) (Q : predicate)
                                 (cond : SecOrder) (x : FOvariable)
                                (i : nat),
  is_unary_predless cond = true ->
    occ_in_alpha (replace_pred alpha Q x cond) i = true ->
      (is_pos_SO alpha (identify_rev alpha Q i) = true <->
        is_pos_SO (replace_pred alpha Q x cond) i = true).
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
  is_unary_predless cond = true ->
    P_occurs_in_alpha (replace_pred alpha Q x cond) P = true->
      P_is_pos_SO alpha P <->
        P_is_pos_SO (replace_pred alpha Q x cond) P.
Proof.
  intros alpha Q P cond x Hcond Hpocc.
  unfold P_is_pos_SO.
  split; intros H;
    destruct H as [Ht Hf];
    apply conj.
      intros HPocc2 i Hocc Heq.
      destruct P as [Pn].
      apply is_pos_rep_pred; try assumption.
      apply Ht.
      case_eq (P_occurs_in_alpha alpha (Pred Pn));
        intros H; rewrite H in *.
        reflexivity.

        specialize (Hf (eq_refl _)).
        contradiction.

      apply (occ_rep_pred2 _ cond _ _ x);
        try assumption.

      rewrite <- at_pred_rep_pred with (cond := cond) (x := x);
      assumption.

      intros H.
      rewrite H in *.
      discriminate.

      intros HPocc2 i Hocc Heq.
      destruct P as [Pn]; destruct Q as [Qm].
      specialize (Ht Hpocc (identify_fwd alpha (Pred Qm) i)).
      pose proof is_pos_rep_pred as H1.
      pose proof identify_fwd_rev as H2.
      specialize (H2 alpha (Pred Qm) i).
      simpl in H2.


      case_eq (occ_in_alpha (replace_pred alpha (Pred Qm) x cond)
       (identify_fwd alpha (Pred Qm) i)); intros a3.

assert (identify_fwd alpha (Pred Qm) i <> 0) as a1.
        unfold not; intros H.
        rewrite H in a3.
        rewrite occ_in_alpha_0 in a3.
        discriminate.

assert (match at_pred (preds_in alpha) i with
     | Pred Rm => PeanoNat.Nat.eqb Qm Rm = false
                  end) as a2.

        destruct (at_pred (preds_in alpha) i) as [Rm].
        case_eq (beq_nat Qm Rm); intros Hbeq.
        rewrite <- Heq in Hbeq.
        rewrite (beq_nat_true _ _ Hbeq) in Hpocc.
        rewrite P_occ_in_alpha_rep_pred_f in Hpocc; try assumption.
          discriminate.

        reflexivity.

assert (match (at_pred (preds_in (replace_pred alpha (Pred Qm) x cond))
       (identify_fwd alpha (Pred Qm) i)) with Pred Rm => Pn = Rm end) as a4.
      rewrite at_pred_rep_pred; try assumption.
      rewrite identify_fwd_rev; assumption.

      rewrite <- (H2 a1 Hocc a2).
      apply (H1 _ _ _ _ _ Hcond a3).
      apply (Ht a3 a4).

        pose proof P_occ_in_alpha_rep_pred_f.
        pose proof at_pred_occ_rep_pred.
        pose proof (at_pred_occ_rep_pred _ _ _ _ _ Hcond Hocc a3).
        rewrite H3 in *.
        rewrite Heq in Hpocc.
        rewrite P_occ_in_alpha_rep_pred_f in Hpocc; try assumption.
        discriminate.

      intros; apply Hf.
      apply P_occ_rep_pred in Hpocc;
      try assumption.
      rewrite Hpocc in *.
      discriminate.
Qed.



