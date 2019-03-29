Require Export vsSahlq_instant19.

Open Scope type_scope.



Lemma hopeful4_REV'_withex'_FULL : forall lP xn phi1 phi2,
  vsSahlq_ante phi1 = true ->
  uniform_pos phi2  ->
  is_in_pred_l (preds_in (ST (mimpl phi1 phi2) (Var xn))) lP = true ->
  existsT2 (lx : list FOvariable) (atm : SecOrder),
    (AT atm = true) *
    ((existsT rel,
      REL rel = true /\
      is_in_pred_l (preds_in (conjSO rel atm)) (preds_in (ST phi1 (Var xn))) = true /\
forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (replace_pred_l (list_closed_allFO (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))) (Var xn)))))) lx)
    lP (list_Var (length lP) (Var (new_FOv_pp_pre2 atm)))
    (vsS_syn_l (FOv_att_P_l (conjSO rel atm) lP) (Var (new_FOv_pp_pre2 atm)))) <->
  SOturnst W Iv Ip Ir (list_closed_SO (ST (mimpl phi1 phi2) (Var xn)) lP)) +

     (is_in_pred_l (preds_in atm) (preds_in (ST phi1 (Var xn))) = true /\
forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (replace_pred_l (list_closed_allFO (implSO atm
    (newnew_pre (instant_cons_empty' atm (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO atm (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn)))))) lx)
    lP (list_Var (length lP) (Var (new_FOv_pp_pre2 atm)))
    (vsS_syn_l (FOv_att_P_l atm lP) (Var (new_FOv_pp_pre2 atm)))) <->
  SOturnst W Iv Ip Ir (list_closed_SO (ST (mimpl phi1 phi2) (Var xn)) lP))).
Proof.
  intros lP xn phi1 phi2 Hvs Hun Hin0.
  destruct (vsS_preprocessing_Step1_pre_againTRY'_withex' _ _ (Var xn) Hvs Hun)
    as [lv [atm [HAT [Hex [ [rel [HREL [Hin SOt]]]  | [Hin SOt]  ]]]]].
    exists lv. exists atm.
    apply pair. assumption.
    left. exists rel. apply conj. assumption.
    apply conj. assumption.
    intros W Iv Ip Ir.  
split; intros H.
    apply hopeful3_REV with (alpha := (ST (mimpl phi1 phi2) (Var xn))) in H ;
      try assumption.
        apply lem_f3; assumption.
      apply uni_pos__SO. assumption.
      apply SOQFree_ST.

      apply att_allFO_x_ST.
      apply att_exFO_x_ST.
      apply closed_except_ST.
      apply x_occ_in_alpha_instant_cons_empty'.
        apply x_occ_in_alpha_ST.

      assert (is_in_pred_l 
          (preds_in (implSO (conjSO rel atm) (ST phi2 (Var xn)))) 
          (preds_in (implSO (ST phi1 (Var xn)) (ST phi2 (Var xn)))) = true) as HH1.
        simpl. apply is_in_pred_l_2app.
        apply Hin. apply is_in_pred_l_refl.
      apply (is_in_pred_l_trans _ _ _ HH1 Hin0).

      apply ex_P_occ_in_alpha_ST.

        apply hopeful3 with (alpha := (ST (mimpl phi1 phi2) (Var xn)));
      try assumption.
      apply uni_pos__SO. assumption.
      apply SOQFree_ST.

      apply att_allFO_x_ST.
      apply att_exFO_x_ST.
      apply closed_except_ST.
      apply x_occ_in_alpha_instant_cons_empty'.
        apply x_occ_in_alpha_ST.

      assert (is_in_pred_l 
          (preds_in (implSO (conjSO rel atm) (ST phi2 (Var xn)))) 
          (preds_in (implSO (ST phi1 (Var xn)) (ST phi2 (Var xn)))) = true) as HH1.
        simpl. apply is_in_pred_l_2app.
        apply Hin. apply is_in_pred_l_refl.
      apply (is_in_pred_l_trans _ _ _ HH1 Hin0).

      apply ex_P_occ_in_alpha_ST.

    exists lv. exists atm.
    apply pair. assumption.
    right.
    apply conj. assumption.
    intros W Iv Ip Ir.
split; intros H.
    apply hopeful3_REV_atm with (alpha := (ST (mimpl phi1 phi2) (Var xn))) in H;
      try assumption.
      apply lem_f3; assumption.

      apply uni_pos__SO. assumption.
      apply SOQFree_ST.

      apply att_allFO_x_ST.
      apply att_exFO_x_ST.
      apply closed_except_ST.
      apply x_occ_in_alpha_instant_cons_empty'.
        apply x_occ_in_alpha_ST.

      assert (is_in_pred_l 
          (preds_in (implSO atm (ST phi2 (Var xn)))) 
          (preds_in (implSO (ST phi1 (Var xn)) (ST phi2 (Var xn)))) = true) as HH1.
        simpl. apply is_in_pred_l_2app.
        apply Hin. apply is_in_pred_l_refl.
      apply (is_in_pred_l_trans _ _ _ HH1 Hin0).

      apply ex_P_occ_in_alpha_ST.

    apply hopeful3_atm with (alpha := (ST (mimpl phi1 phi2) (Var xn)));
      try assumption.
      apply uni_pos__SO. assumption.
      apply SOQFree_ST.

      apply att_allFO_x_ST.
      apply att_exFO_x_ST.
      apply closed_except_ST.
      apply x_occ_in_alpha_instant_cons_empty'.
        apply x_occ_in_alpha_ST.

      assert (is_in_pred_l 
          (preds_in (implSO atm (ST phi2 (Var xn)))) 
          (preds_in (implSO (ST phi1 (Var xn)) (ST phi2 (Var xn)))) = true) as HH1.
        simpl. apply is_in_pred_l_2app.
        apply Hin. apply is_in_pred_l_refl.
      apply (is_in_pred_l_trans _ _ _ HH1 Hin0).

      apply ex_P_occ_in_alpha_ST.
Defined.
 


Lemma hopeful4_REV'_withex'_FULL_allFO : forall lP xn phi1 phi2,
  vsSahlq_ante phi1 = true ->
  uniform_pos phi2  ->
  is_in_pred_l (preds_in (ST (mimpl phi1 phi2) (Var xn))) lP = true ->
  existsT2 lx atm,
    (AT atm = true) *
    ((existsT rel,
      REL rel = true /\
      is_in_pred_l (preds_in (conjSO rel atm)) (preds_in (ST phi1 (Var xn))) = true /\
forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (allFO (Var xn) (replace_pred_l (list_closed_allFO (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))) (Var xn)))))) lx)
    lP (list_Var (length lP) (Var (new_FOv_pp_pre2 atm)))
    (vsS_syn_l (FOv_att_P_l (conjSO rel atm) lP) (Var (new_FOv_pp_pre2 atm))))) <->
  SOturnst W Iv Ip Ir (allFO (Var xn) (list_closed_SO (ST (mimpl phi1 phi2) (Var xn)) lP))) +

     (is_in_pred_l (preds_in atm) (preds_in (ST phi1 (Var xn))) = true /\
forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (allFO (Var xn) (replace_pred_l (list_closed_allFO (implSO atm
    (newnew_pre (instant_cons_empty' atm (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO atm (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn)))))) lx)
    lP (list_Var (length lP) (Var (new_FOv_pp_pre2 atm)))
    (vsS_syn_l (FOv_att_P_l atm lP) (Var (new_FOv_pp_pre2 atm))))) <->
  SOturnst W Iv Ip Ir (allFO (Var xn) (list_closed_SO (ST (mimpl phi1 phi2) (Var xn)) lP)))).
Proof.
  intros lP xn phi1 phi2 H1 H2 H3.
  destruct (hopeful4_REV'_withex'_FULL lP xn phi1 phi2 H1 H2 H3) as [lx [atm [Hat [ [rel [Hrel [Hin SOt]]]| [Hin SOt] ]]]];
  exists lx; exists atm; apply pair; try assumption; [left | right].
    exists rel. apply conj. assumption. apply conj. assumption.
    intros.
    apply equiv_allFO with (W := W) (Iv := Iv) (Ip := Ip) (Ir := Ir) (x := (Var xn)) in SOt.
    assumption.


    apply conj. assumption. intros.
    apply equiv_allFO with (W := W) (Iv := Iv) (Ip := Ip) (Ir := Ir) (x := (Var xn)) in SOt.
    assumption.
Defined.

Lemma hopeful4_REV'_withex'_FULL_allFO_in : forall lP xn phi1 phi2,
  vsSahlq_ante phi1 = true ->
  uniform_pos phi2  ->
  is_in_pred_l (preds_in (ST (mimpl phi1 phi2) (Var xn))) lP = true ->
  existsT2 lx atm,
    (AT atm = true) *
    ((existsT rel,
      REL rel = true /\
      is_in_pred_l (preds_in (conjSO rel atm)) (preds_in (ST phi1 (Var xn))) = true /\
forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (allFO (Var xn) (replace_pred_l (list_closed_allFO (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))) (Var xn)))))) lx)
    lP (list_Var (length lP) (Var (new_FOv_pp_pre2 atm)))
    (vsS_syn_l (FOv_att_P_l (conjSO rel atm) lP) (Var (new_FOv_pp_pre2 atm))))) <->
  SOturnst W Iv Ip Ir (list_closed_SO (allFO (Var xn) (ST (mimpl phi1 phi2) (Var xn))) lP)) +

     (is_in_pred_l (preds_in atm) (preds_in (ST phi1 (Var xn))) = true /\
forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (allFO (Var xn) (replace_pred_l (list_closed_allFO (implSO atm
    (newnew_pre (instant_cons_empty' atm (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO atm (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn)))))) lx)
    lP (list_Var (length lP) (Var (new_FOv_pp_pre2 atm)))
    (vsS_syn_l (FOv_att_P_l atm lP) (Var (new_FOv_pp_pre2 atm))))) <->
  SOturnst W Iv Ip Ir (list_closed_SO (allFO (Var xn) (ST (mimpl phi1 phi2) (Var xn))) lP))).
Proof.
  intros lP xn phi1 phi2 H1 H2 H3.
  destruct (hopeful4_REV'_withex'_FULL_allFO lP xn phi1 phi2 H1 H2 H3) as [lx [atm [Hat [ [rel [Hrel [Hin SOt]]]| [Hin SOt] ]]]];
  exists lx; exists atm; apply pair; try assumption; [left | right].
    exists rel. apply conj. assumption. apply conj. assumption.
    intros. split; intros HH. apply equiv_list_closed_SO_allFO.
      apply SOt. assumption.

      apply equiv_list_closed_SO_allFO in HH. apply SOt. assumption.

    apply conj. assumption. intros.
    split; intros HH. apply equiv_list_closed_SO_allFO.
      apply SOt. assumption.

      apply equiv_list_closed_SO_allFO in HH. apply SOt. assumption.
Defined.

Lemma vsSahlq_full_SO_pre : forall xn phi1 phi2,
  vsSahlq_ante phi1 = true ->
  uniform_pos phi2  ->
  existsT2 lx atm,
    (AT atm = true) *
    ((existsT rel,
      REL rel = true /\
      is_in_pred_l (preds_in (conjSO rel atm)) (preds_in (ST phi1 (Var xn))) = true /\
forall W Iv Ip Ir,

  SOturnst W Iv Ip Ir (allFO (Var xn) (replace_pred_l (list_closed_allFO (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))) (Var xn)))))) lx)
    (preds_in (ST (mimpl phi1 phi2) (Var xn))) (list_Var (length (preds_in (ST (mimpl phi1 phi2) (Var xn)))) (Var (new_FOv_pp_pre2 atm)))
    (vsS_syn_l (FOv_att_P_l (conjSO rel atm) (preds_in (ST (mimpl phi1 phi2) (Var xn)))) (Var (new_FOv_pp_pre2 atm))))) <->
  SOturnst W Iv Ip Ir (uni_closed_SO (allFO (Var xn) (ST (mimpl phi1 phi2) (Var xn))))) +

     (is_in_pred_l (preds_in atm) (preds_in (ST phi1 (Var xn))) = true /\
forall W Iv Ip Ir,

  SOturnst W Iv Ip Ir (allFO (Var xn) (replace_pred_l (list_closed_allFO (implSO atm
    (newnew_pre (instant_cons_empty' atm (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO atm (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn)))))) lx)
    (preds_in (ST (mimpl phi1 phi2) (Var xn))) (list_Var (length (preds_in (ST (mimpl phi1 phi2) (Var xn)))) (Var (new_FOv_pp_pre2 atm)))
    (vsS_syn_l (FOv_att_P_l atm (preds_in (ST (mimpl phi1 phi2) (Var xn)))) (Var (new_FOv_pp_pre2 atm))))) <->
  SOturnst W Iv Ip Ir (uni_closed_SO (allFO (Var xn) (ST (mimpl phi1 phi2) (Var xn)))))).
Proof.
  intros xn phi1 phi2 H1 H2. unfold uni_closed_SO in *. unfold uni_closed_SO.
  apply hopeful4_REV'_withex'_FULL_allFO_in; try assumption.
  simpl. apply is_in_pred_l_refl.
Defined.

Lemma vsSahlq_full_SO : forall xn phi1 phi2,
  vsSahlq_ante phi1 = true ->
  uniform_pos phi2  ->
  existsT (alpha : SecOrder),
is_unary_predless alpha = true /\
forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir alpha <->
  SOturnst W Iv Ip Ir (uni_closed_SO (allFO (Var xn) (ST (mimpl phi1 phi2) (Var xn)))).
Proof.
  intros xn phi1 phi2 H1 H2.
  destruct (vsSahlq_full_SO_pre xn phi1 phi2 H1 H2) as  [lx [atm [Hat [[rel [Hrel [Hin SOt]]]| [Hin SOt] ]]]].
    exists (allFO (Var xn) (replace_pred_l
           (list_closed_allFO
              (implSO (conjSO rel atm)
                 (newnew_pre (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))
                    (rem_FOv
                       (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn))))
                       (Var xn))
                    (rev_seq
                       (S (Nat.max (max_FOv (implSO (conjSO rel atm) (ST phi2 (Var xn)))) xn))
                       (length
                          (rem_FOv
                             (FOvars_in
                                (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn))))
                             (Var xn)))))) lx) (preds_in (ST (mimpl phi1 phi2) (Var xn)))
           (list_Var (length (preds_in (ST (mimpl phi1 phi2) (Var xn))))
              (Var (new_FOv_pp_pre2 atm)))
           (vsS_syn_l (FOv_att_P_l (conjSO rel atm) (preds_in (ST (mimpl phi1 phi2) (Var xn))))
              (Var (new_FOv_pp_pre2 atm))))).
      apply conj.
apply is_un_predless_corresp; assumption.

      apply SOt.


    exists (allFO (Var xn) (replace_pred_l
           (list_closed_allFO
              (implSO atm
                 (newnew_pre (instant_cons_empty' atm (ST phi2 (Var xn)))
                    (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn))
                    (rev_seq (S (Nat.max (max_FOv (implSO atm (ST phi2 (Var xn)))) xn))
                       (length
                          (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn))))
                             (Var xn)))))) lx) (preds_in (ST (mimpl phi1 phi2) (Var xn)))
           (list_Var (length (preds_in (ST (mimpl phi1 phi2) (Var xn))))
              (Var (new_FOv_pp_pre2 atm)))
           (vsS_syn_l (FOv_att_P_l atm (preds_in (ST (mimpl phi1 phi2) (Var xn))))
              (Var (new_FOv_pp_pre2 atm))))).
      apply conj.
apply is_un_predless_corresp_atm; assumption.
      apply SOt.
Defined.



Theorem vsSahlq_full_Modal_sep : forall phi1 phi2,
  vsSahlq_ante phi1 = true ->
  uniform_pos phi2  ->
  existsT (alpha : SecOrder),
is_unary_predless alpha = true /\
forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir alpha <->
  mturnst_frame W Ir (mimpl phi1 phi2).
Proof.
  intros phi1 phi2 H1 H2.
  destruct (vsSahlq_full_SO 0 phi1 phi2 H1 H2) as [alpha [Hun SOt]].
  exists alpha. apply conj. assumption.
  intros. split; intros HH.
    apply (correctness_ST _ _ (Var 0) Iv Ip).
    apply SOt. assumption.

    apply SOt.
    apply (correctness_ST _ _ (Var 0) Iv Ip).
    assumption.
Defined.

Theorem vsSahlq_full_Modal : forall phi,
  vsSahlq phi ->
  existsT (alpha : SecOrder),
is_unary_predless alpha = true /\
forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir alpha <->
  mturnst_frame W Ir phi.
Proof.
  intros phi H. destruct phi; try contradiction.
  simpl in H. case_eq (vsSahlq_ante phi1); intros Hs;
    rewrite Hs in *. 2 : contradiction.
  apply vsSahlq_full_Modal_sep; assumption.
Defined.


(* Print All Dependencies vsSahlq_full_Modal. *)