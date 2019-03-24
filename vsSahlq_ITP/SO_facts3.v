Require Export high_mods SO_facts2.
Require Import vsS_syn_sem At.

Lemma pa_l_disj_base : forall lv x z W Iv Ip Ir,
  ~ In x lv ->
  pa_l_disj Iv lv (Iv z) <-> 
  SOturnst W Iv Ip Ir (replace_FOv (disj_l lv x) x z).
Proof.
  induction lv; intros x z W Iv Ip Ir Hin.
    simpl. destruct (FOvariable_dec x (Var 1)); firstorder.

    simpl in Hin. apply not_or_and in Hin. destruct Hin as [Hin1 Hin2].
    simpl. destruct lv. simpl. rewrite FOvariable_dec_refl.
    rewrite FOvariable_dec_r. firstorder. auto.
    remember (f :: lv) as lv'.
    simpl. rewrite FOvariable_dec_refl. rewrite FOvariable_dec_r.
    firstorder.
    simpl. right. eapply IHlv; auto. right. eapply IHlv. apply Hin2. apply H.
    auto.
Qed.

Lemma equiv_new_simpl1 : forall alpha P lv x W Iv Ip Ir,
  ~ In x lv ->
  SOQFree_P alpha P = true ->
  ~ ex_att_allFO_lvar alpha lv ->
  ~ ex_att_exFO_lvar alpha lv ->
    SOturnst W Iv (alt_Ip Ip (pa_l_disj Iv lv) P) Ir alpha <->
    SOturnst W Iv Ip Ir (replace_pred alpha P x (disj_l lv x)).
Proof.
   induction alpha; intros P lv x W Iv Ip Ir Hin HSO Hat1 Hat2; 
    try (solve [firstorder]).
    simpl. destruct (predicate_dec P p) as [Hbeq | Hbeq].
    subst. rewrite alt_Ip_eq. apply pa_l_disj_base. auto.
    rewrite alt_Ip_neq. simpl. firstorder. auto.

    apply ex_att_allFO_lvar_allFO_neg in Hat1. destruct Hat1 as [Hat1a Hat1b].
    apply ex_att_exFO_lvar_allFO_neg in Hat2.
    simpl in HSO.
    split; intros SOt d.
      apply IHalpha; try assumption.
      rewrite <- pa_l_disj_alt.
      apply SOt. assumption.

      specialize (SOt d).
      apply IHalpha in SOt; try assumption.
      rewrite <- pa_l_disj_alt in SOt.
      apply SOt. assumption.

      apply ex_att_allFO_lvar_exFO_neg in Hat1.
    apply ex_att_exFO_lvar_exFO_neg in Hat2.
    destruct Hat2 as [Hat2a Hat2b].
    split; intros [d SOt]; exists d.
      apply IHalpha; try assumption.
      rewrite <- pa_l_disj_alt.
      apply SOt. assumption.

      apply IHalpha in SOt; try assumption.
      rewrite <- pa_l_disj_alt in SOt.
      apply SOt. assumption.

    rewrite ex_att_allFO_lvar_negSO in Hat1.
    rewrite ex_att_exFO_lvar_negSO in Hat2.
    simpl in *. split; intros H1 H2;
    apply H1; apply (IHalpha P lv x
        W Iv Ip Ir Hin HSO); assumption.

    destruct (ex_att_allFO_lvar_conjSO_f _ _ _ Hat1)
      as [Hat1a Hat1b].
    destruct (ex_att_exFO_lvar_conjSO_f _ _ _ Hat2)
      as [Hat2a Hat2b].
    destruct (SOQFree_P_conjSO_t _ _ _ HSO)
      as [HSOa HSOb].
    simpl in *. split; intros [H1 H2];
      (apply conj;
        [apply (IHalpha1 P lv x
          W Iv Ip Ir Hin HSOa); assumption |
        apply (IHalpha2 P lv x
          W Iv Ip Ir Hin HSOb); assumption]).

    destruct (ex_att_allFO_lvar_disjSO_f _ _ _ Hat1)
      as [Hat1a Hat1b].
    destruct (ex_att_exFO_lvar_disjSO_f _ _ _ Hat2)
      as [Hat2a Hat2b].
    destruct (SOQFree_P_disjSO_t _ _ _ HSO)
      as [HSOa HSOb].
    simpl in *. split; (intros [H1 | H2];
      [left; apply (IHalpha1 P lv x
          W Iv Ip Ir Hin HSOa); assumption |
      right; apply (IHalpha2 P lv x
          W Iv Ip Ir Hin HSOb); assumption]).

    destruct (ex_att_allFO_lvar_implSO_f _ _ _ Hat1)
      as [Hat1a Hat1b].
    destruct (ex_att_exFO_lvar_implSO_f _ _ _ Hat2)
      as [Hat2a Hat2b].
    destruct (SOQFree_P_implSO_t _ _ _ HSO)
      as [HSOa HSOb].
    simpl in *. split; intros H1 H2;
      apply (IHalpha2 P lv x
          W Iv Ip Ir Hin HSOb); try assumption;
      apply H1; apply (IHalpha1 P lv x
          W Iv Ip Ir Hin HSOa); assumption.

    rewrite ex_att_allFO_lvar_allSO in Hat1.
    rewrite ex_att_exFO_lvar_allSO in Hat2.
    simpl in HSO.  destruct (predicate_dec P p) as [? | H].
      subst. discriminate.
    simpl replace_pred. rewrite predicate_dec_r.
    do 2 rewrite SOturnst_allSO.
    split; intros SOt pa.
      apply (IHalpha P lv x
          W Iv _ Ir Hin HSO); try assumption.
      rewrite alt_Ip_switch.
      apply SOt. auto.

      rewrite alt_Ip_switch.
      apply (IHalpha P lv x
          W Iv _ Ir Hin HSO); try assumption.
      apply SOt. auto. auto.

    rewrite ex_att_allFO_lvar_exSO in Hat1.
    rewrite ex_att_exFO_lvar_exSO in Hat2.
    simpl in HSO. destruct (predicate_dec P p). discriminate.
    simpl replace_pred. rewrite predicate_dec_r. 
    do 2 rewrite SOturnst_exSO.
    split; intros [pa SOt]; exists pa.
      apply (IHalpha P lv x
          W Iv _ Ir Hin HSO); try assumption.
      rewrite alt_Ip_switch.
      apply SOt. auto.

      rewrite alt_Ip_switch.
      apply (IHalpha P lv x
          W Iv _ Ir Hin HSO); try assumption.
      all : auto.
Qed.

Lemma equiv_new_simpl_try2_pre : forall lv x y W Iv Ip Ir,
  In x lv ->
  (SOturnst W Iv Ip Ir (replace_FOv (disj_l lv x) x y)).
Proof.
  induction lv; intros x y W Iv Ip Ir Hin.
    simpl in *. inversion Hin. 

    simpl in *. 
    destruct lv. simpl. destruct Hin. subst.
    do 2 rewrite  FOvariable_dec_refl.
    simpl. auto. inversion H.
    remember (f :: lv) as lv'.
    rewrite replace_FOv_disjSO. simpl.
    destruct Hin. subst.
    do 2 rewrite FOvariable_dec_refl.
    simpl. left. auto.
    rewrite FOvariable_dec_refl. right. apply IHlv. auto. 
Qed.

Lemma equiv_new_simpl_try2 : forall alpha P lv x W Iv Ip Ir,
  In x lv ->
  SOQFree_P alpha P = true ->
  ~ ex_att_allFO_lvar alpha lv  ->
  ~ ex_att_exFO_lvar alpha lv ->
    SOturnst W Iv (alt_Ip Ip pa_t P) Ir alpha <->
    SOturnst W Iv Ip Ir (replace_pred alpha P x (disj_l lv x)).
Proof.
  induction alpha; intros P lv x W Iv Ip Ir Hin HSO Hat1 Hat2;
    try (solve [firstorder]).

    simpl in *. destruct (predicate_dec P p). subst.
    rewrite alt_Ip_eq. unfold pa_t. split; intros H. 
    apply equiv_new_simpl_try2_pre. auto. auto.
    rewrite alt_Ip_neq. firstorder. auto.

    simpl replace_pred.
    simpl in HSO.
    destruct (ex_att_allFO_lvar_allFO_neg _ _ _ Hat1)
      as [Hat1a Hat1b].
    apply ex_att_exFO_lvar_allFO_neg in Hat2.
    split; intros SOt d;
      apply (IHalpha P lv x W _ Ip Ir); 
      try assumption; apply SOt.

    simpl replace_pred.
    simpl in HSO.
    destruct (ex_att_exFO_lvar_exFO_neg _ _ _ Hat2)
      as [Hat2a Hat2b].
    apply ex_att_allFO_lvar_exFO_neg in Hat1.
    split; intros [d SOt]; exists d;
      apply (IHalpha P lv x W _ Ip Ir); 
      try assumption; apply SOt.

    simpl in *.
    rewrite ex_att_allFO_lvar_negSO in Hat1.
    rewrite ex_att_exFO_lvar_negSO in Hat2.
    split; intros H1 H2; apply H1;
      apply (IHalpha P lv x W Iv Ip Ir); 
      assumption.

    destruct (ex_att_allFO_lvar_conjSO_f _ _ _ Hat1) as
      [Hat1a Hat1b].
    destruct (ex_att_exFO_lvar_conjSO_f _ _ _ Hat2) as
      [Hat2a Hat2b].
    destruct (SOQFree_P_conjSO_t _ _ _ HSO) as
      [HSOa HSOb].
    simpl.
    split; intros [H1 H2]; (apply conj;
      [apply (IHalpha1 P lv x W Iv Ip Ir); 
      assumption |
      apply (IHalpha2 P lv x W Iv Ip Ir); 
      assumption]).

    destruct (ex_att_allFO_lvar_disjSO_f _ _ _ Hat1) as
      [Hat1a Hat1b].
    destruct (ex_att_exFO_lvar_disjSO_f _ _ _ Hat2) as
      [Hat2a Hat2b].
    destruct (SOQFree_P_disjSO_t _ _ _ HSO) as
      [HSOa HSOb].
    simpl.
    split; (intros [H | H];
      [left; apply (IHalpha1 P lv x W Iv Ip Ir); 
      assumption |
      right; apply (IHalpha2 P lv x W Iv Ip Ir); 
      assumption]).

    destruct (ex_att_allFO_lvar_implSO_f _ _ _ Hat1) as
      [Hat1a Hat1b].
    destruct (ex_att_exFO_lvar_implSO_f _ _ _ Hat2) as
      [Hat2a Hat2b].
    destruct (SOQFree_P_implSO_t _ _ _ HSO) as
      [HSOa HSOb].
    simpl.
    split; intros H1 H2;
      apply (IHalpha2 P lv x W Iv Ip Ir);
      try assumption;
      apply H1;
      apply (IHalpha1 P lv x W Iv Ip Ir); 
      assumption.

    simpl in *. destruct (predicate_dec P p) as [H | H].
    discriminate.
    rewrite ex_att_allFO_lvar_allSO in Hat1.
    rewrite ex_att_exFO_lvar_allSO in Hat2.
    split; intros SOt pa.
      apply (IHalpha P lv x W Iv _ Ir); try assumption.
      rewrite alt_Ip_switch.
      apply SOt. auto.

      specialize (SOt pa).
      apply (IHalpha P lv x W Iv _ Ir) in SOt; try assumption.
      rewrite alt_Ip_switch in SOt.
      apply SOt. auto.

    simpl in *. destruct (predicate_dec P p) as [H | H].
    discriminate.
    rewrite ex_att_allFO_lvar_exSO in Hat1.
    rewrite ex_att_exFO_lvar_exSO in Hat2.
    split; intros [pa SOt]; exists pa.
      apply (IHalpha P lv x W Iv _ Ir); try assumption.
      rewrite alt_Ip_switch.
      apply SOt. auto.

      apply (IHalpha P lv x W Iv _ Ir) in SOt; try assumption.
      rewrite alt_Ip_switch in SOt.
      apply SOt. auto.
Qed.

Lemma equiv_new_simpl3 : forall alpha P lv x W Iv Ip Ir,
  SOQFree_P alpha P = true ->
  ~ ex_att_allFO_lvar alpha lv ->
  ~ ex_att_exFO_lvar alpha lv ->
    SOturnst W Iv (alt_Ip Ip (pa_l_disj_gen Iv lv x) P) Ir alpha <->
    SOturnst W Iv Ip Ir (replace_pred alpha P x (disj_l lv x)).
Proof.
  intros until 0. intros H2 H3 H4.
  destruct (in_dec (FOvariable_dec) x lv) as [H1| H1].
  split; intros H5.
  apply equiv_new_simpl_try2; auto.
    apply (SOturnst_equiv_Ip _ _ _ (alt_Ip Ip (pa_l_disj_gen Iv lv x) P)
                             (alt_Ip Ip pa_t P)). intros Q w.
    destruct (predicate_dec P Q). subst.
    do 2 rewrite alt_Ip_eq. apply pa_l_disj_gen_in_pat. auto.
    rewrite alt_Ip_neq. rewrite alt_Ip_neq. all : auto. apply iff_refl.

    apply equiv_new_simpl_try2 in H5; auto.
    apply (SOturnst_equiv_Ip _ _ _ (alt_Ip Ip (pa_l_disj_gen Iv lv x) P)
                             (alt_Ip Ip pa_t P)) in H5. auto. intros Q w.
    destruct (predicate_dec P Q). subst.
    do 2 rewrite alt_Ip_eq. apply pa_l_disj_gen_in_pat. auto.
    rewrite alt_Ip_neq. rewrite alt_Ip_neq. all : auto. apply iff_refl.

  split; intros H5.
    apply equiv_new_simpl1; auto.
    apply (SOturnst_equiv_Ip _ _ _  (alt_Ip Ip (pa_l_disj Iv lv) P) (alt_Ip Ip (pa_l_disj_gen Iv lv x) P)). intros Q w.
    destruct (predicate_dec P Q). subst.
    do 2 rewrite alt_Ip_eq. apply pa_l_disj_gen_not_in. auto.
    rewrite alt_Ip_neq. rewrite alt_Ip_neq. all : auto. apply iff_refl.

    apply equiv_new_simpl1 in H5; auto.
    apply (SOturnst_equiv_Ip _ _ _  (alt_Ip Ip (pa_l_disj Iv lv) P) (alt_Ip Ip (pa_l_disj_gen Iv lv x) P)). intros Q w.
    destruct (predicate_dec P Q). subst.
    do 2 rewrite alt_Ip_eq. apply pa_l_disj_gen_not_in. auto.
    rewrite alt_Ip_neq. rewrite alt_Ip_neq. all : auto. apply iff_refl.
Qed.

Lemma try3 : forall alpha beta a x P,
  (replace_pred (replace_pred alpha a x (disj_l (FOv_att_P beta a) x)) P x
     (disj_l (FOv_att_P beta P) x)) =
(replace_pred (replace_pred alpha P x (disj_l (FOv_att_P beta P) x)) a x
     (disj_l (FOv_att_P beta a) x)).
Proof.
  intros alpha beta P x Q.
  destruct (predicate_dec P Q). subst.
  rewrite rep_pred_Pred_in_SO_f; auto.
  apply Pred_in_SO_rep_pred_f.
  apply FO_frame_condition_disj_l. 
  rewrite (rep_pred_switch _ _ _ _ _ P Q); auto.
  apply FO_frame_condition_disj_l. apply FO_frame_condition_disj_l. 
Qed.

Lemma try2 : forall lP2 alpha beta P x,
  replace_pred (replace_pred_l  alpha lP2 (list_var (length lP2) x) 
      (vsS_syn_l (FOv_att_P_l beta lP2) x)) P x (disj_l (FOv_att_P beta P) x) =
  replace_pred_l (replace_pred alpha P x (disj_l (FOv_att_P beta P) x))
      lP2 (list_var (length lP2) x)  (vsS_syn_l (FOv_att_P_l beta lP2) x).
Proof.
  induction lP2; intros alpha beta P x. reflexivity.
  simpl. rewrite IHlP2. rewrite IHlP2. rewrite IHlP2.
  rewrite try3. reflexivity.
Qed.

Lemma lem_try18_pre_pre : forall l1 l2 a p f W Iv Ip Ir,
  ~ l1 = nil ->
  incl l1 l2  ->
  SOturnst W Iv (alt_Ip Ip (pa_l_disj_gen Iv l1 f) p) Ir (predSO p a) ->
  SOturnst W Iv (alt_Ip Ip (pa_l_disj_gen Iv l2 f) p) Ir (predSO p a).
Proof.
  intros l1 l2 y P x W Iv Ip Ir H1 H2 H3.
  simpl in *. rewrite alt_Ip_eq. rewrite alt_Ip_eq in H3.
  apply lem_try29 with (l1 := l1); assumption.
Qed.

Lemma lem_try18_pre : forall lx l1 l2 p f W Iv Ip Ir,
  ~ l1 = nil ->
  incl l1 l2 ->
  SOturnst W Iv (alt_Ip Ip (pa_l_disj_gen Iv l1 f) p) Ir 
      (passing_conj (passing_predSO_l p lx)) ->
  SOturnst W Iv (alt_Ip Ip (pa_l_disj_gen Iv l2 f) p) Ir 
      (passing_conj (passing_predSO_l p lx)).
Proof.
  induction lx; intros l1 l2 p f W Iv Ip Ir Hnil Hin SOt.
    simpl in *. reflexivity.

    simpl in *. case_eq (passing_predSO_l p lx).
      intros Hp. rewrite Hp in *.
      apply lem_try18_pre_pre with (l1 := l1); try assumption.

      intros beta lbeta Hlbeta. rewrite Hlbeta in *.
      rewrite <- Hlbeta in *. rewrite SOturnst_conjSO in *.
      apply conj. apply lem_try18_pre_pre with (l1 := l1); try assumption.
      apply SOt. 
      apply IHlx with (l1 := l1); try assumption. apply SOt.
Qed.

Lemma lemma17_pre : forall l P x W Iv Ip Ir w pa,
  ~ l = nil ->  ~ In x l ->
  SOturnst W Iv (alt_Ip Ip pa P) Ir (passing_conj (passing_predSO_l P l)) ->
  pa_l_disj_gen Iv l x w ->  pa w.
Proof.
  induction l; intros P x W Iv Ip Ir w pa Hnil Hin SOt CM. contradiction.
  simpl in *. case_eq (passing_predSO_l P l).
  + intros Hp. rewrite Hp in  *. destruct l. 2 : discriminate.
    simpl in *. rewrite alt_Ip_eq in SOt. inversion CM.
    subst w0. firstorder. subst w0. simpl in *. subst. auto.
  + intros beta lbeta Hlbeta.
    rewrite Hlbeta in *. rewrite <- Hlbeta in *.
    simpl in SOt. destruct SOt as [SOt1 SOt2].
    apply not_or_and in Hin. destruct Hin as [Hin1 Hin2].
    destruct l.
    ++ rewrite alt_Ip_eq in SOt1. inversion CM.
       subst. firstorder. simpl in *. subst. auto.
    ++ rewrite alt_Ip_eq in SOt1. remember (f :: l) as l'.
       inversion CM; subst w0; simpl in H. destruct H; subst;
       contradiction. apply not_or_and in H.
       simpl in H0. rewrite Heql' in *. rewrite <- Heql' in *.
       destruct H0. subst. auto.       
       eapply IHl in SOt2. apply SOt2. rewrite Heql'. discriminate.
       apply Hin2. 
       constructor 2. firstorder. auto.
Qed.

Lemma lemma17_again : forall lP llx P x W Iv Ip Ir pa w,
  ~ lP = nil ->
  length lP = length llx ->
  ex_nil_in_llv llx = false ->
  ~ In x (FOv_att_P (passing_conj (passing_predSO_ll lP llx)) P) ->
  Pred_in_SO (passing_conj (passing_predSO_ll lP llx)) P ->
  SOturnst W Iv (alt_Ip Ip pa P) Ir (passing_conj (passing_predSO_ll lP llx)) ->
  pa_l_disj_gen Iv (FOv_att_P (passing_conj (passing_predSO_ll lP llx)) P) x w ->
  pa w.
Proof.
  induction lP; intros llx P x W Iv Ip Ir pa w Hnil Hlength
      Hex Hin Hpocc SOt CM. contradiction.
  simpl in Hin.
  case_eq lP.
  + intros Hp. rewrite Hp in *.
    simpl in *. destruct llx. discriminate.
    destruct llx. 2 : discriminate. simpl in *.
    apply Pred_in_SO_passing_predSO_l in Hpocc. rewrite Hpocc in *.
    rewrite lem_try10 in CM.
    rewrite lem_try10 in Hin.
    apply lemma17_pre with (x := x) (w := w) in SOt ; try assumption.
    all : try (      destruct l; discriminate).
  + intros P' lP' HlP. destruct llx. discriminate.
    simpl in *. case_eq (passing_predSO_ll lP llx).
    ++ intros Hp. rewrite Hp in *. rewrite HlP in *. destruct llx; discriminate.
    ++ intros beta lbeta Hlbeta. rewrite Hlbeta in *. rewrite <- Hlbeta in *.
       simpl in *.
       case_eq l. intros Hl. rewrite Hl in *. discriminate.
       intros y ly Hl. assert (~ l = nil) as Hlnil.
       rewrite Hl. discriminate.
       rewrite Hl in Hex.
       inversion Hlength as [Hlength'].
       assert (~ lP = nil) as HlPnil.
       rewrite HlP. discriminate.
       * destruct (predicate_dec P a). subst.
         rewrite lem_try10 in *.
         remember (P' :: lP') as lP.
         remember (y :: ly) as ly'.
         ** destruct ((Pred_in_SO_dec (passing_conj (passing_predSO_ll lP llx)) a)).
            *** apply lemma18 in CM.
                destruct CM as [CM|CM].
                apply (lemma17_pre ly' a x _ Iv Ip Ir); try assumption.
                firstorder. firstorder.
                apply (IHlP llx a x W Iv Ip Ir pa w); try assumption. firstorder.
                apply SOt. assumption.
                apply lem10; try assumption.
                apply SOQFree__P. apply SOQFree_passing_predSO_ll.
            *** rewrite lem1 in CM. rewrite List.app_nil_r in CM.
                apply (lemma17_pre ly' a x _ Iv Ip Ir); try assumption.
                firstorder. firstorder. firstorder.
         ** rewrite lem1 in CM. simpl in CM.
            apply Pred_in_SO_conjSO in Hpocc.
            destruct Hpocc as [Hpocc | Hpocc]. apply lem_try35 in Hpocc. contradiction. 
            auto.
            apply (IHlP llx P x W Iv Ip Ir pa w); try assumption. firstorder.
            apply SOt. apply lem_try35. auto.
Qed.

Lemma AT_passing_conj_atm : forall lx P,
  ~ lx = nil ->
  AT (passing_conj_atm P lx) = true.
Proof.
  induction lx; intros [Pn] H.
    contradiction (H eq_refl).
  case_eq lx. intros Hlx. simpl. reflexivity.
  intros x lxx Hlx. rewrite <- Hlx.
  simpl. rewrite Hlx. rewrite <- Hlx.
  simpl. apply IHlx. rewrite Hlx. intros. discriminate.
Qed.

Lemma passing_predSO_ll_nil : forall l1 l2,
  passing_predSO_ll l1 l2 = nil ->
  ( (l1 = nil) \/ (l2 = nil) ).
Proof.
  induction l1; intros l2 H.
    left. reflexivity.
  
    simpl in H. destruct l2. right. reflexivity.
    discriminate.
Qed.

Lemma passing_conj_app : forall l1 l2,
  ~ l1 = nil ->
  ~ l2 = nil ->
  forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (passing_conj (app l1 l2)) <->
  SOturnst W Iv Ip Ir (conjSO (passing_conj l1) (passing_conj l2)).
Proof.
  induction l1; intros l2 H1 H2 W Iv Ip Ir.
    contradiction (H1 eq_refl).
  simpl. case_eq (app l1 l2).
    intros HH.

    apply app_eq_nil in HH. destruct HH. subst.
    contradiction (H2 eq_refl).

    intros beta l' H. case_eq l1.

      intros Hnil. rewrite <- H. rewrite Hnil.
      simpl. apply iff_refl.

      intros beta1 l1' Hl1.
      rewrite <- Hl1. rewrite <- H.
      do 2 rewrite SOturnst_conjSO in *.
      split; intros SOt;
        destruct SOt as [SOt1 SOt2].
        apply IHl1 in SOt2. destruct SOt2 as [SOt2 SOt3].
        apply conj. apply conj. all : try assumption.
        intros HH. rewrite Hl1 in *. discriminate.

        destruct SOt1 as [SOt1 SOt3].
        apply conj. assumption.
        apply IHl1.
        intros HH; rewrite HH in *; discriminate.
        all : try assumption.
        apply conj; assumption.
Qed.

Lemma preds_in_passing_conj_app: forall l1  l2,
  preds_in (passing_conj (app l1 l2)) =
  app (preds_in (passing_conj l1)) (preds_in (passing_conj l2)).
Proof.
  induction l1; intros l2. auto.
  simpl. case_eq l1. 
  + intros H1. simpl. case_eq l2. intros H2. 
    simpl. symmetry. apply List.app_nil_r.
      intros beta2 lbeta2 Hbeta2.
      rewrite <- Hbeta2.
      reflexivity.
  + intros beta1 lbeta1 Hbeta1.
    rewrite <- Hbeta1.
    simpl preds_in.
    assert (app l1 l2 = cons beta1 (app lbeta1 l2)) as Heq.
    rewrite Hbeta1. reflexivity.
    rewrite Heq. rewrite <- app_assoc. rewrite <- IHl1.
    rewrite <- Heq. reflexivity.
Qed. 

Lemma lem_try23 : forall lv P W Iv Ip1 Ip2 Ir pa,
  SOturnst W Iv (alt_Ip Ip1 pa P) Ir (passing_conj (passing_predSO_l P lv)) ->
  SOturnst W Iv (alt_Ip Ip2 pa P) Ir (passing_conj (passing_predSO_l P lv)).
Proof.  
  induction lv; intros P W Iv Ip1 Ip2 Ir pa SOt. auto.
  simpl passing_conj in *.
  case_eq (passing_predSO_l P lv).
  + intros H. rewrite H in *.
    simpl in *. rewrite alt_Ip_eq in *. auto.
  + intros beta lbeta Hlbeta.
    rewrite Hlbeta in *. rewrite <- Hlbeta in *.
    rewrite SOturnst_conjSO in *.
    apply conj. simpl in *. rewrite alt_Ip_eq in *.
      firstorder.
    apply IHlv with (Ip1 := Ip1).
    apply SOt.
Qed.

Lemma lem_try33 : forall lP beta gamma,
  in_in_FOvar_ll (FOv_att_P_l gamma lP) (FOv_att_P_l (conjSO beta gamma) lP).
Proof.
  induction lP; intros beta gamma. constructor.
  simpl in *. constructor.
  apply incl_appr. apply incl_refl.
  auto.
Qed.

Lemma lem118'_length : forall atm,
  AT atm = true ->
length (atm_passing_predSO_ll_lP atm) = length (atm_passing_predSO_ll_llx atm).
Proof.
  induction atm; intros Hat; try discriminate. reflexivity.
  simpl. do 2 rewrite List.app_length. rewrite IHatm1. rewrite IHatm2.
  reflexivity. apply AT_conjSO_r in Hat. assumption.
  apply AT_conjSO_l in Hat. assumption.
Qed.

Lemma lem118'_preds_in : forall atm,
  AT atm = true ->
  preds_in atm = (atm_passing_predSO_ll_lP atm).
Proof.
  induction atm; intros Hat; try discriminate.
    destruct p; destruct f. reflexivity.

    simpl. rewrite IHatm1. rewrite IHatm2.
    reflexivity.
  apply AT_conjSO_r in Hat. assumption.
  apply AT_conjSO_l in Hat. assumption.
Qed.

Lemma lem118'_not_nil : forall atm1,
AT atm1 = true ->
passing_predSO_ll (atm_passing_predSO_ll_lP atm1) (atm_passing_predSO_ll_llx atm1) <> nil.
Proof.
  induction atm1; intros Hat; try discriminate.
    simpl. rewrite passing_predSO_ll_app.
    intros H. apply app_eq_nil in H.  
    contradiction (IHatm1_1 (AT_conjSO_l _ _ Hat)).
    firstorder.
    apply lem118'_length.
    apply AT_conjSO_l in Hat. assumption.
Qed.

Lemma lem118'_equiv : forall atm W Iv Ip Ir,
  AT atm = true ->
  SOturnst W Iv Ip Ir atm <->
  SOturnst W Iv Ip Ir (passing_conj (passing_predSO_ll 
    (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm))).
Proof.
  induction atm; intros  W Iv Ip Ir Hat; try discriminate.    
    destruct p. destruct f. simpl. apply iff_refl.

    simpl.  rewrite passing_predSO_ll_app.
    rewrite passing_conj_app. simpl.
    pose proof (AT_conjSO_l _ _ Hat) as Hat1.
    pose proof (AT_conjSO_r _ _ Hat) as Hat2.
    split; intros SOt; apply conj.
      apply IHatm1. assumption.  apply SOt.

      apply IHatm2. assumption. apply SOt.

      apply IHatm1. assumption.  apply SOt.

      apply IHatm2. assumption. apply SOt.

      apply lem118'_not_nil. apply AT_conjSO_l in Hat.
      assumption.
      apply lem118'_not_nil. apply AT_conjSO_r in Hat.
      assumption.
      apply lem118'_length. apply AT_conjSO_l in Hat.
      assumption.
Qed.

Lemma FOv_att_P_passing_conj_app : forall l1 l2 P,
  FOv_att_P (passing_conj (app l1 l2)) P =
  app (FOv_att_P (passing_conj l1) P) (FOv_att_P (passing_conj l2) P).
Proof.
  induction l1; intros l2 P.
    simpl. reflexivity.

    simpl. case_eq l1. intros Hl1. simpl. destruct l2. simpl.
      rewrite List.app_nil_r. reflexivity.

      simpl in *. reflexivity.

      intros beta lbeta Hlbeta. rewrite <- Hlbeta.
      case_eq (app l1 l2). intros Hnil.
        rewrite Hlbeta in *. discriminate.

        intros gamma lgamma Hlgamma. rewrite <- Hlgamma.
        simpl. rewrite IHl1. rewrite app_assoc. reflexivity.
Qed.

Lemma FOv_att_P_atm_passing_predSO_ll_nil : forall atm1 P,
  AT atm1 = true ->
  ((FOv_att_P
     (passing_conj
        (passing_predSO_ll (atm_passing_predSO_ll_lP atm1)
           (atm_passing_predSO_ll_llx atm1))) P) = nil) <->
  (FOv_att_P atm1 P = nil).
Proof.
  induction atm1; intros [Pn] Hat; try discriminate.
    destruct p as [Qm]. destruct f as [xn].
    simpl in *. apply iff_refl.

    simpl. 
    pose proof (AT_conjSO_l _ _ Hat) as H1.
    pose proof (AT_conjSO_r _ _ Hat) as H2.
    destruct  (IHatm1_1 (Pred Pn) H1) as [Ha Hb].
    destruct  (IHatm1_2 (Pred Pn) H2) as [Hc Hd].
    rewrite passing_predSO_ll_app.
    rewrite FOv_att_P_passing_conj_app.
    simpl. split; intros H. 
      rewrite Ha. rewrite Hc. reflexivity.
        apply app_eq_nil in H. firstorder.
        apply app_eq_nil in H. firstorder.

      rewrite Hb. rewrite Hd. reflexivity.
        apply app_eq_nil in H. firstorder.
        apply app_eq_nil in H. firstorder.

        apply lem118'_length. apply AT_conjSO_l in Hat. assumption.
Qed.

Lemma lem118'_pa_l_disj_gen : forall atm P x (W : Set) (Iv : FOvariable -> W) w,
  AT atm = true ->
  pa_l_disj_gen Iv (FOv_att_P atm P) x w ->
  pa_l_disj_gen Iv  (FOv_att_P ( (passing_conj
           (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm)))) P)  
              x w.
Proof.
  induction atm; intros [Pn] [xn] W Iv w Hat H; try discriminate.
    destruct p as [Qm]. destruct f as [ym]. simpl in *. assumption.

    simpl in *. rewrite passing_predSO_ll_app.
    rewrite FOv_att_P_passing_conj_app.
    pose proof (AT_conjSO_l _ _ Hat) as H1.
    pose proof (AT_conjSO_r _ _ Hat) as H2.
    case_eq (FOv_att_P atm1 (Pred Pn)).
      intros Hf. rewrite Hf in *. simpl in *.
      apply FOv_att_P_atm_passing_predSO_ll_nil in Hf. rewrite Hf.
      simpl.
      case_eq (FOv_att_P atm2 (Pred Pn)).
        intros Hf'. rewrite Hf' in *. simpl in *.
        apply FOv_att_P_atm_passing_predSO_ll_nil in Hf'. rewrite Hf'.
        all : try assumption.

        intros x lx Hlx.
        apply IHatm2; assumption.

      intros x lx Hlx. 
      case_eq (FOv_att_P atm2 (Pred Pn)).
        intros Hf'. rewrite Hf' in *. 
        apply FOv_att_P_atm_passing_predSO_ll_nil in Hf'. rewrite Hf'.
        rewrite List.app_nil_r in *.
        all : try assumption. apply IHatm1; try assumption.

        intros y ly Hly.
        apply lemma18.
        intros HH.
        apply FOv_att_P_atm_passing_predSO_ll_nil with (atm1 := atm1) in HH.
        rewrite HH in *. discriminate. all : try assumption.

        intros HH.
        apply FOv_att_P_atm_passing_predSO_ll_nil with (atm1 := atm2) in HH.
        rewrite HH in *. discriminate. all : try assumption.

        apply lemma18 in H. destruct H as [H|H]; [left|right].
          apply IHatm1; assumption.
          apply IHatm2; assumption.

          rewrite Hlx. discriminate.
          rewrite Hly. discriminate.
          rewrite lem118'_length.
          reflexivity.
          apply AT_conjSO_l in Hat. assumption.
Qed.

Lemma lem118'_not_nil_lP : forall atm,
  AT atm = true ->
  ~ atm_passing_predSO_ll_lP atm = nil.
Proof.
  induction atm; try discriminate.
  intros H.
  simpl. intros H2.
  apply app_eq_nil in H2. apply IHatm1.
    apply AT_conjSO_l in H. assumption.
    firstorder.
Qed.

Lemma lem118'_not_nil_llx : forall atm,
  AT atm = true ->
  ~ atm_passing_predSO_ll_llx atm = nil.
Proof.
  induction atm; try discriminate.
  intros H.
  simpl. intros H2.
  apply app_eq_nil in H2. apply IHatm1.
    apply AT_conjSO_l in H. assumption.
    firstorder.
Qed.

Lemma lem118'_ex_nil_in_llv : forall atm,
  AT atm = true ->
  ex_nil_in_llv (atm_passing_predSO_ll_llx atm) = false.
Proof.
  induction atm; try (discriminate); intros Hat.
    reflexivity.

    simpl. apply ex_nil_in_llv_app_f. apply conj.
    apply IHatm1. apply AT_conjSO_l in Hat. assumption.
    apply IHatm2. apply AT_conjSO_r in Hat. assumption.
Qed.

Lemma Pred_in_SO_passing_conj_app_f : forall l1 l2 P,
  ~ l1 = nil ->
  ~ l2 = nil ->
  ~ Pred_in_SO (passing_conj (app l1 l2)) P <->
  ~ Pred_in_SO (passing_conj l1) P /\
  ~ Pred_in_SO (passing_conj l2) P.
Proof. 
  induction l1; intros l2 P H1 H2. contradiction.
  simpl. case_eq l1.
  + intros Hl1. simpl. case_eq l2. intros Hl2. subst. contradiction.
    intros beta lbeta Hl2. rewrite <- Hl2. split; intros H.
    apply Pred_in_SO_conjSO_f in H. assumption. 
    apply Pred_in_SO_conjSO_f in H. assumption. 
  + intros d ld Hl1. rewrite <- Hl1.
    assert (~ l1 = nil) as Hnil. rewrite Hl1. discriminate.
    case_eq (app l1 l2). intros Hl12. rewrite Hl1 in Hl12.
      discriminate.
    intros e le Hl12. rewrite <- Hl12.
    split; intros H.
    ++ apply Pred_in_SO_conjSO_f in H.
       destruct H as [Ha Hb].
       apply IHl1 in Hb. destruct Hb as [Hb1 Hb2].
       apply conj. apply Pred_in_SO_conjSO_f.
       apply conj. all : try assumption.
    ++ destruct H as [Ha Hb].
       apply Pred_in_SO_conjSO_f in Ha.
       destruct Ha as [Ha1 Ha2].
       apply Pred_in_SO_conjSO_f.
       apply conj. assumption. apply IHl1.
       all : try assumption.
       apply conj; assumption.
Qed.

Lemma Pred_in_SO_passing_conj_app : forall l1 l2 P,
  ~ l1 = nil ->
  ~ l2 = nil ->
  Pred_in_SO (passing_conj (app l1 l2)) P <->
  Pred_in_SO (passing_conj l1) P  \/
  Pred_in_SO (passing_conj l2) P.
Proof. 
  induction l1; intros l2 P H1 H2. contradiction.
  case_eq l1. 
  + intros Hl1. rewrite Hl1 in *.
    simpl. case_eq l2. intros Hl2. rewrite Hl2 in *.
        contradiction (H2 eq_refl).
    intros beta lbeta Hl2. rewrite <- Hl2.
    rewrite Pred_in_SO_conjSO. apply iff_refl.
  + intros beta lbeta Hl1. rewrite <- Hl1.
    simpl. case_eq (app l1 l2). intros Hl.
    rewrite Hl1 in *. discriminate.
    intros beta2 lbeta2 Hlbeta2. rewrite <- Hlbeta2.
    assert (~ l1 = nil) as Hnil1. rewrite Hl1. discriminate.
    rewrite Hl1. rewrite <- Hl1.
    rewrite Pred_in_SO_conjSO.
    rewrite Pred_in_SO_conjSO.
    split; intros H. destruct H.
    ++ left. left. assumption.
    ++ apply IHl1 in H. destruct H.
       left. right. assumption.
       right. assumption.
       all : try assumption.
    ++ destruct H. destruct H.
       left. assumption.
       right. apply IHl1; try assumption.
       left. assumption.
       right. apply IHl1; try assumption.
       right. assumption.
Qed.

Lemma lem118'_Pred_in_SO_gen : forall atm P,
AT atm = true ->
Pred_in_SO atm P <->
Pred_in_SO (passing_conj
     (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm)))
  P .
Proof.
  induction atm; intros P Hat; try discriminate;
    apply iff_refl; auto.
  pose proof (AT_conjSO_l _ _ Hat) as Hat1.
  pose proof (AT_conjSO_r _ _ Hat) as Hat2.
  simpl. destruct (Pred_in_SO_dec (conjSO atm1 atm2) P) as [Hpocc | Hpocc].
  + apply Pred_in_SO_conjSO in Hpocc.
    rewrite passing_predSO_ll_app. symmetry.
    split; intros HH.
    ++ apply Pred_in_SO_passing_conj_app in HH.
       destruct Hpocc; unfold Pred_in_SO; simpl; firstorder.
       apply lem118'_not_nil. assumption.
       apply lem118'_not_nil. assumption.
    ++ apply Pred_in_SO_passing_conj_app.
       apply lem118'_not_nil. assumption.
       apply lem118'_not_nil. assumption.
       destruct Hpocc as [H1 | H1].
       left. apply IHatm1; auto.
       right. apply IHatm2; auto.
    ++ apply lem118'_length. apply AT_conjSO_l in Hat.
       assumption.
  + apply Pred_in_SO_conjSO_f in Hpocc. symmetry.
    destruct Hpocc as [Hp1 Hp2]. rewrite IHatm1 in Hp1.
    rewrite IHatm2 in Hp2.
    rewrite passing_predSO_ll_app. 
    split; intros HH.
    ++ apply Pred_in_SO_passing_conj_app in HH.
       destruct HH. apply IHatm1 in H. unfold Pred_in_SO.
       simpl. firstorder. auto.
       apply IHatm2 in H. unfold Pred_in_SO.
       simpl. firstorder. auto.
       apply lem118'_not_nil. assumption.
       apply lem118'_not_nil. assumption.
    ++ apply Pred_in_SO_passing_conj_app.
      apply lem118'_not_nil. assumption.
      apply lem118'_not_nil. assumption.
      unfold Pred_in_SO in HH. simpl in HH.
      apply in_app_or in HH. destruct HH as [HH|HH].
      apply IHatm1 in HH. contradiction. auto.
      apply IHatm2 in HH. contradiction. auto.
    ++ apply lem118'_length. all : assumption.
    ++ auto. ++ auto.
Qed.

Lemma lem118'_Pred_in_SO : forall atm P,
AT atm = true ->
Pred_in_SO atm P ->
Pred_in_SO (passing_conj
     (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm)))
  P.
Proof.
  induction atm; intros P Hat Hpocc; try discriminate. auto.
  simpl. apply Pred_in_SO_conjSO in Hpocc.
  rewrite passing_predSO_ll_app.
  apply Pred_in_SO_passing_conj_app.
  apply lem118'_not_nil. apply AT_conjSO_l in Hat. assumption.
  apply lem118'_not_nil. apply AT_conjSO_r in Hat. assumption.
  destruct Hpocc. apply IHatm1 in H. left. assumption.
  apply AT_conjSO_l in Hat. assumption.
  apply IHatm2 in H. right. assumption.
  apply AT_conjSO_r in Hat. assumption.
  apply lem118'_length. apply AT_conjSO_l in Hat.
  assumption.
Qed.

Lemma is_in_FOvar_atm_passing_predSO_ll : forall atm P x,
  AT atm = true ->
  ~ In x (FOv_att_P atm P) ->
  ~ In x (FOv_att_P (passing_conj (passing_predSO_ll
      (atm_passing_predSO_ll_lP atm) 
      (atm_passing_predSO_ll_llx atm))) P).
Proof.
  induction atm; intros P x Hat Hin; try discriminate. auto.
  simpl in *. rewrite passing_predSO_ll_app. rewrite FOv_att_P_passing_conj_app.
  destruct (in_dec FOvariable_dec x (FOv_att_P atm1 P)). firstorder.
  if_then_else_hyp.
  intros Hin1. apply in_app_or in Hin1. destruct Hin1 as [Hin1 | Hin1].
  apply IHatm1 in Hin1; auto. 
  apply IHatm2 in Hin1; auto. firstorder.
  apply lem118'_length. apply AT_conjSO_l in Hat. assumption.
Qed.

Lemma lemma17' : forall atm P x W Iv Ip Ir pa w,
  AT atm = true ->
  Pred_in_SO atm P ->
  ~ In x (FOv_att_P atm P) ->
  SOturnst W Iv (alt_Ip Ip pa P) Ir atm ->
  pa_l_disj_gen Iv (FOv_att_P atm P) x w ->
  pa w.
Proof.
  intros atm P x W Iv Ip Ir pa w Hat Hpocc Hin SOt CM.
  apply lem118'_equiv in SOt.
  apply lem118'_pa_l_disj_gen in CM.
  apply (lemma17_again) with (Ip := Ip) (Ir := Ir) (pa := pa) in CM.
  assumption.
  apply lem118'_not_nil_lP. assumption.
  apply lem118'_length. assumption.
  apply lem118'_ex_nil_in_llv. assumption.
  apply is_in_FOvar_atm_passing_predSO_ll with (P := P); assumption.
  apply lem118'_Pred_in_SO; assumption.
  all : assumption.
Qed.

Lemma lemma_try4 : forall lP alpha P x W Iv Ip w,
  In P lP ->
  @alt_Ip_list W Ip 
    (vsS_pa_l Iv (FOv_att_P_l alpha lP) (list_var (length lP) x)) lP P w =
  alt_Ip Ip (pa_l_disj_gen Iv (FOv_att_P alpha P) x) P P w.
Proof.
  induction lP; intros alpha P x W Iv Ip w Hpocc. inversion Hpocc.
  simpl in *. destruct (predicate_dec P a). subst.
  repeat rewrite alt_Ip_eq. auto.
  destruct Hpocc. subst. firstorder.
  rewrite <- IHlP; auto. rewrite alt_Ip_neq; auto. 
Qed.
