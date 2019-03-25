Require Export high_mods SO_facts1.
Require Import Correctness_ST Sahlqvist_Uniform_Pos.


Lemma instant_cons_empty_equiv_list2 : forall alpha beta W Iv Ip Ir,
  SOturnst W Iv Ip Ir (list_closed_SO (instant_cons_empty (implSO alpha beta))
                            (preds_in (instant_cons_empty (implSO alpha beta)))) ->
  SOturnst W Iv Ip Ir (list_closed_SO (instant_cons_empty (implSO alpha beta))
                            (preds_in (implSO alpha beta))).
Proof.
  intros alpha beta W Iv Ip Ir SOt.  apply uni__list_closed_SO.
  unfold uni_closed_SO.  assumption.
Qed.

Lemma uni_pos_SO_SOturnst_f_gen : forall beta l W Iv Ip Ir,
  SOQFree beta = true ->
  uniform_pos_SO beta ->
   SOturnst W Iv Ip Ir (replace_pred_l beta (list_rel_compl l (preds_in beta))
     (nlist_list _
        (nlist_var (length (list_rel_compl l (preds_in beta))) (Var 1)))
     (nlist_list _
        (nlist_empty (length (list_rel_compl l (preds_in beta)))))) ->
    SOturnst W Iv Ip Ir beta.
Proof. 
  intros beta l W Iv Ip Ir Hno Hun SOt.
  pose proof (step2_empty _ _ _ _ _ _ Hno Hun SOt) as H.
  apply list_closed_SO_pa_choose in H.
  assumption.
Qed.

Lemma uni_pos_SO_SOturnst_f_gen2 : forall beta l W Iv Ip Ir,
  SOQFree beta = true ->
  uniform_pos_SO beta ->
   SOturnst W Iv Ip Ir (replace_pred_l beta (list_rel_compl (preds_in beta) l)
     (nlist_list _
        (nlist_var (length (list_rel_compl (preds_in beta) l)) (Var 1)))
     (nlist_list _
        (nlist_empty (length (list_rel_compl (preds_in beta) l))))) ->
    SOturnst W Iv Ip Ir beta.
Proof.
  intros beta l W Iv Ip Ir Hno Hun SOt.
  pose proof (step2_empty _ _ _ _ _ _ Hno Hun SOt) as H.
  apply list_closed_SO_pa_choose in H.
  assumption.
Qed.

Lemma instant_cons_empty_equiv : forall alpha beta W Iv Ip Ir,
  SOQFree beta = true ->
  uniform_pos_SO beta ->
  SOturnst W Iv Ip Ir (instant_cons_empty (implSO alpha beta)) ->
  SOturnst W Iv Ip Ir (implSO alpha beta).
Proof.
  intros alpha beta W Iv Ip Ir Hno Hun.
  rewrite instant_cons_empty_implSO.
  simpl. intros H1 H2; specialize (H1 H2).
  apply uni_pos_SO_SOturnst_f_gen2 in H1; assumption.
Qed.

Lemma instant_cons_empty_equiv_list1 : forall l alpha beta W Iv Ip Ir,
  SOQFree beta = true ->
  uniform_pos_SO beta ->
  SOturnst W Iv Ip Ir (list_closed_SO (instant_cons_empty (implSO alpha beta)) l) ->
  SOturnst W Iv Ip Ir (list_closed_SO (implSO alpha beta) l).
Proof.
  induction l; intros alpha beta W Iv Ip Ir Hno Hun SOt.
    simpl in SOt.
    simpl list_closed_SO.
    apply instant_cons_empty_equiv; assumption.

    destruct a as [Pn].
    simpl list_closed_SO in *.
    rewrite SOturnst_allSO in *.
    intros pa.
    specialize (SOt pa).
    apply IHl; assumption.
Qed.

(* ----------------------------------------------- *)

Lemma list_closed_SO_instant_cons_empty : forall l alpha beta W Iv Ip Ir,
  incl (preds_in (implSO alpha beta)) l ->
  SOQFree (implSO alpha beta) = true ->
  SOturnst W Iv Ip Ir (list_closed_SO (implSO alpha beta) l) ->
  SOturnst W Iv Ip Ir (list_closed_SO (instant_cons_empty (implSO alpha beta)) l).
Proof.
  intros.
  unfold instant_cons_empty.
  simpl.
  destruct (nlist_list_ex (length (list_rel_compl 
       (preds_in beta) (preds_in alpha)))
      (list_rel_compl (preds_in beta) (preds_in alpha)) eq_refl)
    as [lP' HlP'].
  rewrite <- HlP'.
  rewrite length_nlist_list.
  apply list_closed_instant_one_f. 
  rewrite HlP'. simpl in H.
    apply incl_app_rev_r in H.
    apply incl_trans with (l2 := preds_in beta).
    apply is_in_pred_l_list_rel_compl.
    all:assumption.
Qed.

Lemma vsSahlq_pp_Lemma1 : forall alpha beta W Iv Ip Ir,
  SOQFree (implSO alpha beta) = true ->
  SOturnst W Iv Ip Ir (uni_closed_SO (implSO alpha beta)) ->
  SOturnst W Iv Ip Ir (list_closed_SO (instant_cons_empty (implSO alpha beta))
                        (preds_in (implSO alpha beta))).
Proof.
  unfold uni_closed_SO.
  unfold instant_cons_empty.
  simpl.
  intros.
  apply list_closed_SO_instant_cons_empty; try assumption.
    simpl. apply incl_refl.
Qed.

Lemma vsSahlq_pp_Lemma2 : forall alpha beta W Iv Ip Ir,
  SOturnst W Iv Ip Ir (list_closed_SO (instant_cons_empty (implSO alpha beta))
                        (preds_in (implSO alpha beta))) ->
  SOturnst W Iv Ip Ir (uni_closed_SO (instant_cons_empty (implSO alpha beta))).
Proof.
  intros alpha beta W Iv Ip Ir Sot.
  apply vsSahlq_pp_Lemma3 with (l := (preds_in (implSO alpha beta))).
    apply vsSahlq_pp_Lemma4.
    assumption.
Qed.

Lemma instant_cons_empty_equiv2_fwd : forall alpha beta W Iv Ip Ir,
  SOQFree (implSO alpha beta) = true ->
  SOturnst W Iv Ip Ir (uni_closed_SO (implSO alpha beta)) ->
  SOturnst W Iv Ip Ir (uni_closed_SO (instant_cons_empty (implSO alpha beta))).
Proof.
  intros alpha beta W Iv Ip Ir Hno SOt.
  apply vsSahlq_pp_Lemma2.
  apply vsSahlq_pp_Lemma1;
  assumption.
Qed.

Lemma instant_cons_empty_equiv2_rev : forall alpha beta W Iv Ip Ir,
  SOQFree beta = true ->
  uniform_pos_SO beta ->
  SOturnst W Iv Ip Ir (uni_closed_SO (instant_cons_empty (implSO alpha beta))) ->
  SOturnst W Iv Ip Ir (uni_closed_SO (implSO alpha beta)).
Proof.
  intros alpha beta W Iv Ip Ir Hno Hun SOt.
  unfold uni_closed_SO in *.
  pose proof instant_cons_empty_equiv_list1.
  apply instant_cons_empty_equiv_list2 in SOt.
  apply instant_cons_empty_equiv_list1; assumption.
Qed.

Lemma instant_cons_empty_equiv2 : forall alpha beta W Iv Ip Ir,
  SOQFree (implSO alpha beta) = true ->
  uniform_pos_SO beta ->
  SOturnst W Iv Ip Ir (uni_closed_SO (implSO alpha beta)) <->
  SOturnst W Iv Ip Ir (uni_closed_SO (instant_cons_empty (implSO alpha beta))).
Proof.
  intros. split; intros SOt.
    apply instant_cons_empty_equiv2_fwd; assumption.
    apply SOQFree_implSO_r in H.
    apply instant_cons_empty_equiv2_rev; assumption.
Qed.

Lemma instant_cons_empty_equiv2_list_closed_allFO : forall l alpha beta W Iv Ip Ir,
  SOQFree (implSO alpha beta) = true ->
  uniform_pos_SO beta ->
  SOturnst W Iv Ip Ir (uni_closed_SO (list_closed_allFO (implSO alpha beta) l)) <->
  SOturnst W Iv Ip Ir (uni_closed_SO (list_closed_allFO (instant_cons_empty (implSO alpha beta)) l)).
Proof.
  intros l alpha beta W Iv Ip Ir Hno Hun.
  split; intros SOt.
    apply equiv_uni_closed_SO_list_closed_allFO.
    apply equiv_list_closed_allFO with 
        (alpha := (uni_closed_SO (implSO alpha beta))).
      intros.
      apply instant_cons_empty_equiv2; assumption.
    apply equiv_uni_closed_SO_list_closed_allFO.
    assumption.

    apply equiv_uni_closed_SO_list_closed_allFO.
    apply equiv_list_closed_allFO with 
        (alpha := (uni_closed_SO (instant_cons_empty (implSO alpha beta)))).
      intros. split; intros H;
      apply instant_cons_empty_equiv2; assumption.
    apply equiv_uni_closed_SO_list_closed_allFO.
    assumption.
Qed.

Lemma instant_cons_empty_equiv2_list_closed__allFO : forall l alpha beta x W Iv Ip Ir,
  SOQFree (implSO alpha beta) = true ->
  uniform_pos_SO beta ->
  SOturnst W Iv Ip Ir (uni_closed_SO (allFO x (list_closed_allFO (implSO alpha beta) l))) <->
  SOturnst W Iv Ip Ir (uni_closed_SO (allFO x (list_closed_allFO (instant_cons_empty (implSO alpha beta)) l))).
Proof.
  intros l alpha beta [xn] W Iv Ip Ir.
  split; intros SOt;
    apply equiv_uni_closed_SO_allFO;
    apply equiv_uni_closed_SO_allFO in SOt;
    intros d; specialize (SOt d);
    apply instant_cons_empty_equiv2_list_closed_allFO;
    assumption.
Qed.

Lemma equiv_implSO_exFO : forall alpha beta x W Iv Ip Ir,
  SOturnst W Iv Ip Ir (implSO (exFO x alpha) beta) <->
  SOturnst W Iv Ip Ir (allFO (replace_FOv_max_conj_var alpha beta x)
                            (implSO (replace_FOv_max_conj alpha beta x) beta)).
Proof.
  intros alpha beta x W Iv Ip Ir.
  unfold replace_FOv_max_conj_var. unfold replace_FOv_max_conj.
  remember (max_FOv (conjSO beta (exFO x alpha))) as mx.
  assert ( (max_FOv (exFO x alpha)) <= mx) as Hleb.
    rewrite Heqmx.
    apply le_max_FOv_exFO_conjSO.
  destruct x as [xn].
  pose proof (exFO_rep_FOv_max_FOv alpha xn mx Hleb) as H.
  pose proof (equiv_implSO2 _ _ beta H) as H2.  clear H.
  split; intros SOt.
    apply H2 in SOt.
    apply equiv_impl_exFO.
      rewrite Heqmx. apply free_FO_max_FOv_f.
    assumption.

    apply H2.
    apply equiv_impl_exFO in SOt.
      assumption.
    rewrite Heqmx. apply free_FO_max_FOv_f.
Qed.

Lemma equiv3_3_struc2_ind_nlist' : forall n (lv : nlist n) alpha gamma,
  forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (implSO (list_closed_exFO alpha (nlist_list _ lv)) gamma) <->
  SOturnst W Iv Ip Ir (list_closed_allFO 
        (implSO (replace_FOv_A alpha gamma (nlist_list _ lv)) gamma)
                      (replace_FOv_A_list alpha gamma (nlist_list _ lv))).
Proof.
  induction n; intros lv alpha gamma.
    pose proof (nlist_nil2 lv) as Hnil.   
    rewrite Hnil.
    simpl.
    intros W Iv Ip Ir.
    apply iff_refl.

    destruct (nlist_cons2 _ lv) as [x [lvv Heq1]].
    pose proof (equiv_implSO_exFO (list_closed_exFO alpha (nlist_list _ lvv)) gamma x) as SOt.
    pose proof (list_closed_exFO_strip_exFO (nlist_list _ lvv) alpha 
      ((replace_FOv_max_conj (list_closed_exFO alpha (nlist_list n lvv)) gamma x))) as [Hs' [Hl' Heq]].
      apply same_struc_replace_FOv_max_conj.
    rewrite Heq in *.
    pose proof Hl' as Hl''.
    rewrite <- Heq in Hl''.
    symmetry in Hl''.
    rewrite length_nlist_list in Hl'' at 2.
    destruct (nlist_list_ex _ (strip_exFO_list (replace_FOv_max_conj (list_closed_exFO alpha (nlist_list n lvv)) gamma x)
            (length (nlist_list n lvv))) Hl'') as [ln' H2].
    intros W Iv Ip Ir.
    rewrite Heq1.
    simpl nlist_list.
    unfold replace_FOv_A in *.
    simpl replace_FOv_A_list_pre.
    unfold replace_FOv_A_list in *.
    simpl replace_FOv_A_pre.
    simpl replace_FOv_A_list_pre.
    rewrite list_closed_allFO_cons.
    rewrite list_closed_exFO_cons.
    specialize (IHn ln'  (strip_exFO
               (replace_FOv_max_conj (list_closed_exFO alpha (nlist_list n lvv)) gamma x)
               (length (nlist_list n lvv))) gamma).
    rewrite H2 in *.
    rewrite Hl'' in *.
    rewrite length_nlist_list at 3.
    rewrite length_nlist_list at 5.
    split; intros H.
      apply (equiv_allFO _ _ (IHn)).
      apply SOt in H.
      assumption.

      apply (equiv_allFO _ _ (IHn)) in H.
      apply SOt.
      assumption.
Qed.

Lemma equiv3_3_struc2_2' : forall lv alpha gamma,
  forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (implSO (list_closed_exFO alpha lv) gamma) <->
  SOturnst W Iv Ip Ir (list_closed_allFO 
        (implSO (replace_FOv_A alpha gamma lv) gamma)
                (replace_FOv_A_list alpha gamma lv)).
Proof.
  intros lv.
  destruct (nlist_list_ex (length lv) lv eq_refl).
  rewrite <- H.
  apply equiv3_3_struc2_ind_nlist'.
Qed.

Lemma list_closed_SO_instant_cons_empty2 : forall l alpha beta W Iv Ip Ir,
  incl (preds_in (implSO alpha beta)) l ->
  SOQFree (implSO alpha beta) = true ->
  SOturnst W Iv Ip Ir (list_closed_SO (implSO alpha beta) l) ->
  SOturnst W Iv Ip Ir (list_closed_SO (implSO alpha (instant_cons_empty' alpha beta)) l).
Proof.
  intros. rewrite <-instant_cons_empty__'.
  apply list_closed_SO_instant_cons_empty;
  assumption.
Qed.

Lemma equiv_replace_FOv_free_FO_f : forall alpha y z,
  free_FO alpha y = false ->
  free_FO alpha z = false ->
  ~ y = z->
  ~ var_in_SO alpha z -> forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir alpha <->
    SOturnst W Iv Ip Ir (replace_FOv alpha y z).
Proof.
  induction alpha; intros x y Hf1 Hf2 Hneq  Hocc W Iv Ip Ir;
    simpl in *.
  + dest_FOv_dec_blind; try discriminate. firstorder.
  + dest_FOv_dec_blind; try discriminate. firstorder.
  + dest_FOv_dec_blind; try discriminate. firstorder.
  + dest_FOv_dec_blind; subst; try contradiction.
    firstorder.
    pose proof (hopeful3_allFO alpha f y W Iv Ip Ir) as H.
    simpl in H. FOv_dec_l_rep. firstorder.
    split; intros SOt d. apply IHalpha; auto.
    firstorder. specialize (SOt d). apply IHalpha in SOt; auto.
    firstorder.
  + dest_FOv_dec_blind; subst; try contradiction.
    firstorder.
    pose proof (hopeful3_exFO alpha f y W Iv Ip Ir) as H.
    simpl in H. FOv_dec_l_rep. firstorder.
    split; intros [d SOt]; exists d. apply IHalpha; auto.
    firstorder. apply IHalpha in SOt; auto.
    firstorder.
  + split; intros H1 H2; eapply IHalpha in H2; auto;
      try solve[firstorder].  contradiction (H1 H2).
    auto. auto.
  + if_then_else_hyp_tzf. apply var_in_SO_conjSO_f in Hocc.
    split; intros [HH1 HH2]; apply conj; auto.
      apply IHalpha1; auto. firstorder.
      apply IHalpha2; auto. firstorder.
      apply IHalpha1 in HH1; auto. firstorder.
      apply IHalpha2 in HH2; auto. firstorder.
  + if_then_else_hyp_tzf. apply var_in_SO_conjSO_f in Hocc.
    split; (intros [HH1 | HH2]; [left | right]); auto.
      apply IHalpha1; auto. firstorder.
      apply IHalpha2; auto. firstorder.
      apply IHalpha1 in HH1; auto. firstorder.
      apply IHalpha2 in HH2; auto. firstorder.
  + if_then_else_hyp_tzf. apply var_in_SO_conjSO_f in Hocc.
    split; intros HH1 HH2; auto.
      apply IHalpha2; auto. firstorder. apply HH1.
      apply IHalpha1 in HH2; auto. firstorder.
      eapply IHalpha2. apply Hf1. apply Hf2. auto. firstorder.
      apply HH1. apply IHalpha1; firstorder.
  + split; intros SOt pa. apply IHalpha; auto.
    specialize (SOt pa). apply IHalpha in SOt; firstorder.
  + split; intros [pa SOt]; exists pa. apply IHalpha; auto.
    apply IHalpha in SOt; firstorder.
Qed.

Lemma kk10_nil : forall alpha x n a W Iv Ip Ir,
  closed_except alpha x ->
  a <> x ->
  S (max_FOv alpha) <= n ->
  <W Iv Ip Ir> ⊨ alpha <-> <W Iv Ip Ir> ⊨ replace_FOv alpha a (Var n).
Proof.
  intros until 0. intros [Hc1 Hc2] H1 H2. 
  destruct (FOvariable_dec a (Var n)). subst.
  + rewrite rep_FOv_rem. apply iff_refl.
  + apply equiv_replace_FOv_free_FO_f;
      try apply Hc2; auto.
    ++ intros Heq. rewrite Heq in Hc1.
       apply free_FO_var_in in Hc1. destruct a.
       apply var_in_SO_max_FOv_gen2 in Hc1.
       contradiction.
    ++ pose proof (var_in_SO_max_FOv_gen2 alpha n) as HH.
       firstorder.
Qed.
