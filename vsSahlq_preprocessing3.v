Add LoadPath "~/Nextcloud/Coq Files/Sahlqvist/Sahlq_Modules/vsSahlq local".

Require Import List.
Require Export vsSahlq_preprocessing2.

(* ---------------------------------------------------------------- *)



Lemma equiv_list_closed_SO : forall l alpha beta,
  (forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir alpha <-> SOturnst W Iv Ip Ir beta) ->
  forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir (list_closed_SO alpha l) <->
    SOturnst W Iv Ip Ir (list_closed_SO beta l).
Proof.
  induction l; intros alpha beta H W Iv Ip Ir.
    simpl in *. apply H.

    destruct a as [Pn].
    split; intros SOt pa.
      apply IHl with (alpha := alpha). assumption.
      apply SOt.

      apply IHl with (alpha := beta).
        intros; split; apply H; assumption.
      apply SOt.
Qed.

Lemma equiv_list_closed_SO_app_l : forall l alpha W Iv Ip Ir,
  SOturnst W Iv Ip Ir (list_closed_SO alpha (app l (preds_in alpha))) <->
  SOturnst W Iv Ip Ir (list_closed_SO alpha (preds_in alpha)).
Proof.
  induction l; intros alpha W Iv Ip Ir.
    simpl. apply bi_refl.

    simpl app. destruct a as [Pn].
    split; intros SOt.
      apply IHl.
      specialize (SOt (Ip (Pred Pn))).
      rewrite unaltered_fun in SOt.
      assumption.

      intros pa.
      apply IHl.
      pose proof (Ip_uni_closed W alpha Iv Ip 
        (altered_Ip Ip pa (Pred Pn))) as H2.
      apply H2. assumption.
Qed.

Lemma equiv_list_closed_SO_app_cons : forall l P alpha W Iv Ip Ir,
  SOturnst W Iv Ip Ir (list_closed_SO alpha (app l (cons P nil))) <->
  SOturnst W Iv Ip Ir (list_closed_SO alpha (cons P l)).
Proof.
  induction l; intros [Pn] alpha W Iv Ip Ir.
    simpl. apply bi_refl.

    destruct a as [Qm].
    simpl list_closed_SO.
    split; intros SOt.
      apply allSO_switch.
      intros pa.
      apply IHl. apply SOt.

      apply allSO_switch in SOt.
      intros pa.
      apply IHl. simpl list_closed_SO.
      specialize (SOt pa). assumption.
Qed.

Lemma list_closed_SO_app : forall l1 l2 alpha,
  list_closed_SO alpha (app l1 l2) = 
  list_closed_SO (list_closed_SO alpha l2) l1.
Proof.
  induction l1; intros l2 alpha.
    reflexivity.

    destruct a as [Pn].
    simpl.
    rewrite IHl1.
    reflexivity.
Qed.

Lemma app_cons_nil : forall {A : Type} l1 l2 (P : A),
  app l1 (cons P l2) = app (app l1 (cons P nil)) l2.
Proof.
  intros A l1; induction l1; intros l2 P.
    reflexivity.

    simpl.
    rewrite IHl1.
    reflexivity.
Qed.

Lemma app_cons_nil2 : forall {A : Type} l1 l2 (P : A),
  app l1 (app l2 (cons P nil)) = app (app l1 l2) (cons P nil).
Proof.
  intros A l1; induction l1; intros l2 P.
    reflexivity.

    simpl.
    rewrite IHl1.
    reflexivity.
Qed.

Lemma equiv_list_closed_SO_app : forall l1 l2 alpha W Iv Ip Ir,
  SOturnst W Iv Ip Ir (list_closed_SO alpha (app l1 l2)) <->
  SOturnst W Iv Ip Ir (list_closed_SO alpha (app l2 l1)).
Proof.
  induction l1; intros l2 alpha W Iv Ip Ir.
    simpl. rewrite app_nil_r. apply bi_refl.

    destruct a as [Pn]. simpl app.
    assert (app l2 (cons (Pred Pn) l1) = 
            app (app l2 (cons (Pred Pn) nil)) l1) as Heq.
      apply app_cons_nil.
    rewrite Heq.
    assert (app l1 (app l2 (cons (Pred Pn) nil)) =
            app (app l1 l2) (cons (Pred Pn) nil)) as Heq2.
      apply app_cons_nil2.
    split; intros SOt.
      apply IHl1.
      rewrite Heq2.
      apply equiv_list_closed_SO_app_cons.
      assumption.

      apply IHl1 in SOt.
      rewrite Heq2 in SOt.
      apply equiv_list_closed_SO_app_cons in SOt.
      assumption.
Qed.

Lemma equiv_list_closed_SO_app_r : forall l alpha W Iv Ip Ir,
  SOturnst W Iv Ip Ir (list_closed_SO alpha (app (preds_in alpha) l)) <->
  SOturnst W Iv Ip Ir (list_closed_SO alpha (preds_in alpha)).
Proof.
  intros l alpha W Iv Ip Ir.
  split; intros SOt.
    apply equiv_list_closed_SO_app in SOt.
    apply (equiv_list_closed_SO_app_l l alpha).
    assumption.

    apply equiv_list_closed_SO_app.
    apply (equiv_list_closed_SO_app_l l alpha).
    assumption.
Qed.

Lemma equiv_uni_closed_SO : forall alpha beta,
  (forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir alpha <-> SOturnst W Iv Ip Ir beta) ->
  forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir (uni_closed_SO alpha) <->
    SOturnst W Iv Ip Ir (uni_closed_SO beta).
Proof.
  intros alpha beta H W Iv Ip Ir.
  destruct (equiv_list_closed_SO (app (preds_in alpha) (preds_in beta))
      alpha beta H W Iv Ip Ir) as [fwd rev].
  unfold uni_closed_SO.
  split; intros SOt.
    apply equiv_list_closed_SO_app_l with (l := (preds_in alpha)).
    apply fwd.
    apply equiv_list_closed_SO_app_r.
    assumption.

    apply equiv_list_closed_SO_app_r with (l := (preds_in beta)).
    apply rev.
    apply equiv_list_closed_SO_app_l.
    assumption.
Qed.


(* ---------------------------------------------------------------- *)


(* Lemma uniform_pos_SO_instant_cons_empty_pre : forall l alpha beta,
  SOQFree (implSO alpha beta) = true ->
  uniform_pos_SO beta ->
  uniform_pos_SO (vsSahlq_dest_SO_cons (replace_pred_l (implSO alpha beta) l
        (nlist_list (length l) (nlist_Var1 (length l)))
        (nlist_list (length l) (nlist_empty (length l))))).
Proof.
  induction l; intros alpha beta Hno Hun.
    simpl. assumption.

    simpl.
    unfold uniform_pos_SO.
    intros P HPocc.
    rewrite vsSahlq_dest_SO_cons_rep_pred in *.
    pose proof HPocc as HPocc'.
    apply P_occ_rep_pred in HPocc; try reflexivity.

    specialize (IHl _ _ Hno Hun).
    unfold uniform_pos_SO in IHl.
    specialize (IHl P HPocc).
    apply P_is_pos_rep_pred; try assumption.
      reflexivity.
Qed. *)

(* Lemma uniform_pos_SO_instant_cons_empty : forall alpha beta,
  SOQFree (implSO alpha beta) = true ->
  uniform_pos_SO beta ->
  uniform_pos_SO (vsSahlq_dest_SO_cons (instant_cons_empty (implSO alpha beta))).
Proof.
  unfold instant_cons_empty.
  simpl.
  intros. apply uniform_pos_SO_instant_cons_empty_pre; assumption.
Qed. *)

Lemma equiv_impl_exFO : forall alpha beta x W Iv Ip Ir,
  free_FO beta x = false ->
  SOturnst W Iv Ip Ir (implSO (exFO x alpha) beta) <->
  SOturnst W Iv Ip Ir (allFO x (implSO alpha beta)).
Proof.
  intros alpha beta x W Iv Ip Ir Hfee.
  rewrite SOturnst_allFO.
  split; intros H.
    intros d SOt.
    assert (SOturnst W Iv Ip Ir (exFO x alpha)) as SOt'.
      rewrite SOturnst_exFO.
      exists d. assumption.
    specialize (H SOt').
    apply altered_Iv_equiv; assumption.

    intros SOt.
    rewrite SOturnst_exFO in SOt.
    destruct SOt as [d SOt].
    specialize (H d SOt).
    apply altered_Iv_equiv in H; assumption.
Qed.

Lemma equiv_implSO2 : forall alpha beta gamma,
  (forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir alpha <->
    SOturnst W Iv Ip Ir beta) ->
  forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir (implSO alpha gamma) <->
    SOturnst W Iv Ip Ir (implSO beta gamma).
Proof.
  intros alpha beta gamma H W Iv Ip Ir.
  simpl.
  split; intros H1 H2;
    apply H1;
    apply H;
    assumption.
Qed.


Lemma equiv_implSO_exFO : forall alpha beta x W Iv Ip Ir,
  SOturnst W Iv Ip Ir (implSO (exFO x alpha) beta) <->
  SOturnst W Iv Ip Ir (allFO (rename_FOv_max_conj_var alpha beta x)
                            (implSO (rename_FOv_max_conj alpha beta x) beta)).
Proof.
  intros alpha beta x W Iv Ip Ir.
  unfold rename_FOv_max_conj_var. unfold rename_FOv_max_conj.
  destruct x as [xn].
  remember (max_FOv (conjSO beta (exFO (Var xn) alpha))) as mx.
  assert (Nat.leb (max_FOv (exFO (Var xn) alpha)) mx = true) as Hleb.
    rewrite Heqmx.
    apply leb_max_FOv_exFO_conjSO.
  pose proof (exFO_rename_FOv_max_FOv alpha xn mx Hleb) as H.
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
        (implSO (rename_FOv_A alpha gamma (nlist_list _ lv)) gamma)
                      (rename_FOv_A_list alpha gamma (nlist_list _ lv))).
Proof.
  induction n; intros lv alpha gamma.
    pose proof (nlist_nil2 lv) as Hnil.   
    rewrite Hnil.
    simpl.
    intros W Iv Ip Ir.
    apply bi_refl.

    destruct (nlist_cons2 _ lv) as [x [lvv Heq1]].
    pose proof (equiv_implSO_exFO (list_closed_exFO alpha (nlist_list _ lvv)) gamma x) as SOt.
    pose proof (list_closed_exFO_strip_exFO (nlist_list _ lvv) alpha 
      ((rename_FOv_max_conj (list_closed_exFO alpha (nlist_list n lvv)) gamma x))) as [Hs' [Hl' Heq]].
      apply same_struc_rename_FOv_max_conj.
    rewrite Heq in *.
    pose proof Hl' as Hl''.
    rewrite <- Heq in Hl''.
    symmetry in Hl''.
    rewrite length_nlist_list in Hl'' at 2.
    destruct (nlist_list_ex _ (strip_exFO_list (rename_FOv_max_conj (list_closed_exFO alpha (nlist_list n lvv)) gamma x)
            (length (nlist_list n lvv))) Hl'') as [ln' H2].
    intros W Iv Ip Ir.
    rewrite Heq1.
    simpl nlist_list.
    unfold rename_FOv_A in *.
    simpl rename_FOv_A_list_pre.
    unfold rename_FOv_A_list in *.
    simpl rename_FOv_A_pre.
    simpl rename_FOv_A_list_pre.
    rewrite list_closed_allFO_cons.
    rewrite list_closed_exFO_cons.
    specialize (IHn ln'  (strip_exFO
               (rename_FOv_max_conj (list_closed_exFO alpha (nlist_list n lvv)) gamma x)
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
        (implSO (rename_FOv_A alpha gamma lv) gamma)
                (rename_FOv_A_list alpha gamma lv)).
Proof.
  intros lv.
  destruct (nlist_list_ex (length lv) lv eq_refl).
  rewrite <- H.
  apply equiv3_3_struc2_ind_nlist'.
Qed.

Lemma vsSahlq_ante_conjSO_exFO_relatSO : forall phi x,
  vsSahlq_ante phi = true ->
  conjSO_exFO_relatSO (ST phi x) = true.
Proof.
  induction phi; intros [xn] Hvs;
    try (simpl in *; discriminate).

    destruct p; reflexivity.

    apply vsSahlq_ante_mconj in Hvs.
    simpl.
    rewrite IHphi1. apply IHphi2.
    apply Hvs. apply Hvs.

    simpl in *.
    apply IHphi; assumption.
Qed.

Lemma SOturnst_trans : forall alpha beta gamma,
  (forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir alpha <->
    SOturnst W Iv Ip Ir beta) ->
  (forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir beta <->
    SOturnst W Iv Ip Ir gamma) ->
  forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir alpha <->
    SOturnst W Iv Ip Ir gamma.
Proof.
  intros alpha beta gamma H1 H2 W Iv Ip Ir.
  split; intros SOt.
    apply H2; apply H1; assumption.
    apply H1; apply H2; assumption.
Qed.

Lemma rename_FOv_A_rel_atm : forall lv rel atm beta,
  REL rel = true ->
  AT atm = true ->
  existsT2 rel' atm',
    rename_FOv_A (conjSO rel atm) beta lv =  conjSO rel' atm' /\
    REL rel' = true /\
    AT atm' = true.
Proof.
  induction lv; intros rel atm beta HREL HAT.
    unfold rename_FOv_A. simpl.
    exists rel. exists atm.
    apply conj. reflexivity.
    apply conj; assumption.

    destruct (IHlv _ _ beta HREL HAT) as [rel' [atm' [Heq [HREL' HAT']]]].
    unfold rename_FOv_A in *.
    simpl.
    pose proof (same_struc_rename_FOv_max_conj (list_closed_exFO (conjSO rel atm) lv) beta a).
    pose proof (same_struc_trans _ _ _ H (same_struc_rename_FOv_max_conj_list_closed_exFO
              _ _ _ _)) as H1.
    pose proof (same_struc_rename_FOv_max_conj (list_closed_exFO (conjSO rel atm) lv)
      beta a) as H2.
    apply same_struc_comm in H1.
    pose proof (same_struc_trans _ _ _ H1 H2) as H3.
    apply same_struc_strip_exFO with (n := (length lv)) in H3.
    pose proof (same_struc_trans _ _ _ (same_struc_strip_exFO_list_closed
      _ _) H3) as H4.
    pose proof (same_struc_trans _ _ _ (same_struc_rename_FOv_max_conj _ _ _)
      H4) as H5.
    pose proof (same_struc_trans _ _ _ H5 (same_struc_rename_FOv_A_pre
         (length lv)
(strip_exFO_list
       (rename_FOv_max_conj (list_closed_exFO (conjSO rel atm) lv) beta a)
       (length lv)) _ beta)) as H6.
    apply same_struc_comm in H6.
    destruct (same_struc_conjSO_ex _ _ _ H6) as [rel'' [atm'' H']].
    rewrite H' in H6.
    pose proof (same_struc_conjSO_l _ _ _ _ H6) as H7.
    apply same_struc_conjSO_r in H6.
    apply same_struc_comm in H6.
    apply same_struc_comm in H7.
    exists rel''. exists atm''.
    apply conj.
      assumption.
      apply conj.
        apply same_struc_REL with (alpha := rel); assumption.
        apply same_struc_AT with (alpha := atm); assumption.
Defined.

Lemma vsS_preprocessing_Step1_1 : forall phi1 phi2 rel atm x lv,
  vsSahlq_ante phi1 = true ->
  uniform_pos phi2 ->
  REL rel = true ->
  AT atm = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
      (Ir : W -> W -> Prop),
    SOturnst W Iv Ip Ir (ST phi1 x) <->
    SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv)) ->
exists lv0 : list FOvariable,
  (exists rel0 : SecOrder,
     REL rel0 = true /\
     ((exists atm0 : SecOrder,
         AT atm0 = true /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (ST (mimpl phi1 phi2) x) <->
          SOturnst W Iv Ip Ir
            (list_closed_allFO (implSO (conjSO rel0 atm0) (ST phi2 x)) lv0))) \/
      (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
         (Ir : W -> W -> Prop),
       SOturnst W Iv Ip Ir (ST (mimpl phi1 phi2) x) <->
       SOturnst W Iv Ip Ir (list_closed_allFO (implSO rel0 (ST phi2 x)) lv0)))) \/
  (exists atm0 : SecOrder,
     AT atm0 = true /\
     (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir (ST (mimpl phi1 phi2) x) <->
      SOturnst W Iv Ip Ir (list_closed_allFO (implSO atm0 (ST phi2 x)) lv0))).
Proof.
  intros phi1 phi2 rel atm x lv Hvsa Hun HREL HAT H.
  pose proof (equiv_implSO2 _ _ (ST phi2 x) H) as H1.
  pose proof (equiv3_3_struc2_2' lv (conjSO rel atm) (ST phi2 x)) as H2.
  pose proof (SOturnst_trans _ _ _ H1 H2) as H3.
  pose proof rename_FOv_A_rel_atm.
  destruct (rename_FOv_A_rel_atm lv rel atm (ST phi2 x) HREL HAT)
     as [rel' [atm' [H' [HREL' HAT']]]] .
  rewrite H' in *.
  exists (rename_FOv_A_list (conjSO rel atm) (ST phi2 x) lv).
  left.
  exists rel'.
  apply conj. assumption.
  left.
  exists atm'.
  apply conj. assumption.
  assumption.
Qed.


Lemma vsS_preprocessing_Step1_2 : forall phi1 phi2 rel x lv,
  vsSahlq_ante phi1 = true ->
  uniform_pos phi2 ->
  REL rel = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
      (Ir : W -> W -> Prop),
    SOturnst W Iv Ip Ir (ST phi1 x) <->
    SOturnst W Iv Ip Ir (list_closed_exFO rel lv)) ->
exists lv0 : list FOvariable,
  (exists rel0 : SecOrder,
     REL rel0 = true /\
     ((exists atm0 : SecOrder,
         AT atm0 = true /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (ST (mimpl phi1 phi2) x) <->
          SOturnst W Iv Ip Ir
            (list_closed_allFO (implSO (conjSO rel0 atm0) (ST phi2 x)) lv0))) \/
      (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
         (Ir : W -> W -> Prop),
       SOturnst W Iv Ip Ir (ST (mimpl phi1 phi2) x) <->
       SOturnst W Iv Ip Ir (list_closed_allFO (implSO rel0 (ST phi2 x)) lv0)))) \/
  (exists atm0 : SecOrder,
     AT atm0 = true /\
     (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir (ST (mimpl phi1 phi2) x) <->
      SOturnst W Iv Ip Ir (list_closed_allFO (implSO atm0 (ST phi2 x)) lv0))).
Proof.
  intros phi1 phi2 rel x lv Hvsa Hun HREL H.
  pose proof (equiv_implSO2 _ _ (ST phi2 x) H) as H1.
  pose proof (equiv3_3_struc2_2' lv rel (ST phi2 x)) as H2.
  pose proof (SOturnst_trans _ _ _ H1 H2) as H3.
  pose proof (same_struc_rename_FOv_A rel (ST phi2 x) lv) as H4.
  apply same_struc_comm in H4.
  apply same_struc_REL in H4. 2 : assumption.
  exists (rename_FOv_A_list rel (ST phi2 x) lv).
  left.
  exists (rename_FOv_A rel (ST phi2 x) lv).
  apply conj. assumption.
  right.
  assumption.
Qed.

Lemma vsS_preprocessing_Step1_3 : forall phi1 phi2 atm x lv,
  vsSahlq_ante phi1 = true ->
  uniform_pos phi2 ->
  AT atm = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
      (Ir : W -> W -> Prop),
    SOturnst W Iv Ip Ir (ST phi1 x) <->
    SOturnst W Iv Ip Ir (list_closed_exFO atm lv)) ->
exists lv0 : list FOvariable,
  (exists rel0 : SecOrder,
     REL rel0 = true /\
     ((exists atm0 : SecOrder,
         AT atm0 = true /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (ST (mimpl phi1 phi2) x) <->
          SOturnst W Iv Ip Ir
            (list_closed_allFO (implSO (conjSO rel0 atm0) (ST phi2 x)) lv0))) \/
      (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
         (Ir : W -> W -> Prop),
       SOturnst W Iv Ip Ir (ST (mimpl phi1 phi2) x) <->
       SOturnst W Iv Ip Ir (list_closed_allFO (implSO rel0 (ST phi2 x)) lv0)))) \/
  (exists atm0 : SecOrder,
     AT atm0 = true /\
     (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir (ST (mimpl phi1 phi2) x) <->
      SOturnst W Iv Ip Ir (list_closed_allFO (implSO atm0 (ST phi2 x)) lv0))).
Proof.
  intros phi1 phi2 atm x lv Hvsa Hun HAT H.
  pose proof (equiv_implSO2 _ _ (ST phi2 x) H) as H1.
  pose proof (equiv3_3_struc2_2' lv atm (ST phi2 x)) as H2.
  pose proof (SOturnst_trans _ _ _ H1 H2) as H3.
  pose proof (same_struc_rename_FOv_A atm (ST phi2 x) lv) as H4.
  apply same_struc_comm in H4.
  apply same_struc_AT in H4. 2 : assumption.
  exists (rename_FOv_A_list atm (ST phi2 x) lv).
  right.
  exists (rename_FOv_A atm (ST phi2 x) lv).
  apply conj. assumption.
  assumption.
Qed.

Lemma vsS_preprocessing_Step1_pre : forall phi1 phi2 x,
  vsSahlq_ante phi1 = true ->
  uniform_pos phi2  ->
  exists lv : list FOvariable,
    (exists rel : SecOrder,
     REL rel = true /\
     ((exists atm : SecOrder,
         AT atm = true /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (ST (mimpl phi1 phi2) x) <->
          SOturnst W Iv Ip Ir (list_closed_allFO (implSO (conjSO rel atm) (ST phi2 x)) lv))) \/
      (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
         (Ir : W -> W -> Prop),
       SOturnst W Iv Ip Ir (ST (mimpl phi1 phi2) x) <->
       SOturnst W Iv Ip Ir (list_closed_allFO (implSO rel (ST phi2 x)) lv)))) \/
  (exists atm : SecOrder,
     AT atm = true /\
     (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir (ST (mimpl phi1 phi2) x) <->
      SOturnst W Iv Ip Ir (list_closed_allFO (implSO atm (ST phi2 x)) lv))).
Proof.
  intros phi1 phi2 x Hvsa Hun.
  pose proof (preprocess_vsSahlq_ante (ST phi1 x)) as H1.
  specialize (H1 (vsSahlq_ante_conjSO_exFO_relatSO _ _ Hvsa)).
  destruct H1 as [lv [[rel [HREL [[atm [HAT H]] | H]]] | [atm [HAT H]]]].
    apply vsS_preprocessing_Step1_1 with (phi2 := phi2) in H; assumption.
    apply vsS_preprocessing_Step1_2 with (phi2 := phi2) in H; assumption.
    apply vsS_preprocessing_Step1_3 with (phi2 := phi2) in H; assumption.
Qed.

Lemma vsSahlq_dest_ex : forall phi,
  vsSahlq phi ->
  exists phi1 phi2,
    phi = mimpl phi1 phi2 /\ 
    vsSahlq_ante phi1 = true /\
    uniform_pos phi2.
Proof.
  destruct phi; intros Hvs;
    try (simpl in *; contradiction).  
  exists phi1. exists phi2.
  apply conj. reflexivity.
  simpl in *. 
  case_eq (vsSahlq_ante phi1); intro H; rewrite H in Hvs.
  apply conj. reflexivity. assumption. contradiction.
Qed.

Lemma vsSahlq_dest_implSO : forall phi x,
  vsSahlq phi ->
  (ST phi x) = implSO (vsSahlq_dest_SO_ante (ST phi x)) 
                      (vsSahlq_dest_SO_cons (ST phi x)).
Proof.
  intros phi x Hvs.
  destruct (vsSahlq_dest_ex phi Hvs) as [phi1 [phi2 [Heq [Hvsa Hun]]]].
  rewrite Heq.
  reflexivity.
Qed.

Fixpoint vsSahlq_dest_ante phi :=
  match phi with
  | atom p => phi
  | mneg psi => phi
  | mconj psi1 psi2 => phi
  | mdisj psi1 psi2 => phi
  | mimpl psi1 psi2 => psi1 (* ante *)
  | box psi => phi
  | diam psi => phi
  end.

(* Given a conditional, return the consequent. Don't care about other
   inputs. *)
Fixpoint vsSahlq_dest_cons phi :=
  match phi with
  | atom p => phi
  | mneg psi => phi
  | mconj psi1 psi2 => phi
  | mdisj psi1 psi2 => phi 
  | mimpl psi1 psi2 => psi2 (* cons *)
  | box psi => phi
  | diam psi => phi
  end.

Lemma vsSahlq_dest_cons__SO : forall phi x,
  vsSahlq_dest_SO_cons (ST phi x) = ST (vsSahlq_dest_cons phi) x.
Proof.
  induction phi; intros [xn]; try reflexivity.
    destruct p as [Pn]; reflexivity.
Qed.

Lemma vsSahlq_dest_ante__SO : forall phi x,
  vsSahlq_dest_SO_ante (ST phi x) = ST (vsSahlq_dest_ante phi) x.
Proof.
  induction phi; intros [xn]; try reflexivity.
    destruct p as [Pn]; reflexivity.
Qed.

Lemma vsSahlq_ante_dest : forall phi,
  vsSahlq phi ->
  vsSahlq_ante (vsSahlq_dest_ante phi) = true.
Proof.
  intros phi Hvs.
  destruct phi; try (simpl in *; contradiction).
  simpl in *.
  case_eq (vsSahlq_ante phi1); intros H; rewrite H in *.
    reflexivity. contradiction.
Qed.


Lemma vsSahlq_cons_dest : forall phi,
  vsSahlq phi ->
  uniform_pos (vsSahlq_dest_cons phi).
Proof.
  intros phi Hvs.
  destruct phi; try (simpl in *; contradiction).
  simpl in *.
  case_eq (vsSahlq_ante phi1); intros H; rewrite H in *.
    assumption. contradiction.
Qed.

Lemma vsS_preprocessing_Step1 : forall phi x,
  vsSahlq phi ->
  exists lv : list FOvariable,
    (exists rel : SecOrder,
     REL rel = true /\
     ((exists atm : SecOrder,
         AT atm = true /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (ST phi x) <->
          SOturnst W Iv Ip Ir (list_closed_allFO (implSO (conjSO rel atm) 
             (vsSahlq_dest_SO_cons (ST phi x))) lv))) \/
      (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
         (Ir : W -> W -> Prop),
       SOturnst W Iv Ip Ir (ST phi x) <->
       SOturnst W Iv Ip Ir (list_closed_allFO (implSO rel 
                    (vsSahlq_dest_SO_cons (ST phi x))) lv)))) \/
  (exists atm : SecOrder,
     AT atm = true /\
     (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir (ST phi x) <->
      SOturnst W Iv Ip Ir (list_closed_allFO (implSO atm (vsSahlq_dest_SO_cons (ST phi x))) lv))).
Proof.
  intros phi x Hvs.
  rewrite (vsSahlq_dest_implSO phi x).
  rewrite vsSahlq_dest_cons__SO.
  rewrite vsSahlq_dest_ante__SO.
  pose proof vsS_preprocessing_Step1_pre as H2. 
  simpl ST in H2.
  apply H2; try assumption.
    apply vsSahlq_ante_dest; assumption.
    apply vsSahlq_cons_dest; assumption.
  assumption.
Qed.


(* ----------- *)

Lemma vsS_preprocessing_Step2 : forall phi x,
  vsSahlq phi ->
  exists lv : list FOvariable,
    (exists rel : SecOrder,
     REL rel = true /\
     ((exists atm : SecOrder,
         AT atm = true /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (uni_closed_SO (allFO x (ST phi x))) <->
          SOturnst W Iv Ip Ir (uni_closed_SO (allFO x (list_closed_allFO (implSO (conjSO rel atm) 
             (vsSahlq_dest_SO_cons (ST phi x))) lv))))) \/
      (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
         (Ir : W -> W -> Prop),
       SOturnst W Iv Ip Ir (uni_closed_SO (allFO x (ST phi x))) <->
       SOturnst W Iv Ip Ir (uni_closed_SO (allFO x ((list_closed_allFO (implSO rel 
                    (vsSahlq_dest_SO_cons (ST phi x))) lv))))))) \/
  (exists atm : SecOrder,
     AT atm = true /\
     (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir (uni_closed_SO (allFO x (ST phi x))) <->
      SOturnst W Iv Ip Ir (uni_closed_SO (allFO x (list_closed_allFO (implSO atm (vsSahlq_dest_SO_cons (ST phi x))) lv))))).
Proof.
  intros phi x Hvs.
  destruct (vsS_preprocessing_Step1 phi x Hvs)
    as [lv [[rel [HREL [[atm [HAT H]] | H]]] | [atm [HAT H]]]];
    exists lv. left. exists rel.
    apply conj. assumption.
    left. exists atm.
    apply conj. assumption.
    apply equiv_uni_closed_SO.
    intros.
    apply equiv_allFO.
    assumption.

    left. exists rel.
    apply conj. assumption.
    right.
    apply equiv_uni_closed_SO.
    intros.
    apply equiv_allFO.
    assumption.

    right. exists atm.
    apply conj. assumption.
    apply equiv_uni_closed_SO.
    intros.
    apply equiv_allFO.
    assumption.
Qed.

Lemma REL_conjSO_l : forall rel1 rel2,
  REL (conjSO rel1 rel2) = true ->
  REL rel1 = true.
Proof.
  intros rel1 rel2 H.
  simpl in H.
  case_eq (REL rel1); intros H2.
    reflexivity.
    rewrite H2 in *; discriminate.
Qed.

Lemma REL_conjSO_r : forall rel1 rel2,
  REL (conjSO rel1 rel2) = true ->
  REL rel2 = true.
Proof.
  intros rel1 rel2 H.
  simpl in H.
  case_eq (REL rel2); intros H2.
    reflexivity.

    rewrite H2 in *.
    rewrite if_then_else_false in H.
    discriminate.
Qed.

Lemma AT_conjSO_l : forall rel1 rel2,
  AT (conjSO rel1 rel2) = true ->
  AT rel1 = true.
Proof.
  intros rel1 rel2 H.
  simpl in H.
  case_eq (AT rel1); intros H2.
    reflexivity.
    rewrite H2 in *; discriminate.
Qed.

Lemma AT_conjSO_r : forall rel1 rel2,
  AT (conjSO rel1 rel2) = true ->
  AT rel2 = true.
Proof.
  intros rel1 rel2 H.
  simpl in H.
  case_eq (AT rel2); intros H2.
    reflexivity.

    rewrite H2 in *.
    rewrite if_then_else_false in H.
    discriminate.
Qed.

Lemma SOQFree_rel : forall rel,
  REL rel = true ->
  SOQFree rel = true.
Proof.
  induction rel; intros H;
    try (simpl in *; discriminate).
    destruct f; destruct f0;
      reflexivity.

    simpl.
    pose proof (REL_conjSO_l _ _ H) as H2.
    apply REL_conjSO_r in H.
    rewrite IHrel1.
    apply IHrel2.
    all : assumption.
Qed.

Lemma SOQFree_atm : forall atm,
  AT atm = true ->
  SOQFree atm = true.
Proof.
  induction atm; intros H;
    try (simpl in *; discriminate).
    destruct f; destruct p;
      reflexivity.

    simpl.
    pose proof (AT_conjSO_l _ _ H) as H2.
    apply AT_conjSO_r in H.
    rewrite IHatm1.
    apply IHatm2.
    all : assumption.
Qed.

Lemma SOQFree_vsSahlq_dest_SO_cons : forall phi x,
  vsSahlq phi ->
SOQFree (vsSahlq_dest_SO_cons (ST phi x)) = true.
Proof.
  intros phi x Hvs.
  destruct (vsSahlq_dest_ex phi Hvs) as [phi1 [phi2 [Heq [Hvs1 Hun]]]].
  rewrite Heq.
  simpl.
  apply SOQFree_ST.
Qed.

Lemma SOQFree_vsS_pp_3_ra : forall phi rel atm x,
  REL rel = true ->
  AT atm = true ->
  vsSahlq phi ->
SOQFree (implSO (conjSO rel atm) (vsSahlq_dest_SO_cons (ST phi x))) = true.
Proof.
  intros phi rel atm [xn] HREL HAT Hvs.
  simpl.
  rewrite SOQFree_rel.
  rewrite SOQFree_atm.
  apply SOQFree_vsSahlq_dest_SO_cons.
  all : assumption.
Qed.

Lemma SOQFree_vsS_pp_3_r : forall phi rel x,
  REL rel = true ->
  vsSahlq phi ->
SOQFree (implSO rel (vsSahlq_dest_SO_cons (ST phi x))) = true.
Proof.
  intros phi rel [xn] HREL Hvs.
  simpl.
  rewrite SOQFree_rel.
  apply SOQFree_vsSahlq_dest_SO_cons.
  all :assumption.
Qed.

Lemma SOQFree_vsS_pp_3_a : forall phi atm x,
  AT atm = true ->
  vsSahlq phi ->
SOQFree (implSO atm (vsSahlq_dest_SO_cons (ST phi x))) = true.
Proof.
  intros phi atm [xn] HAT Hvs.
  simpl.
  rewrite SOQFree_atm.
  apply SOQFree_vsSahlq_dest_SO_cons.
  all :assumption.
Qed.

Lemma uniform_pos_SO_vsSahlq_dest_SO_cons: forall phi x,
  vsSahlq phi ->
  uniform_pos_SO (vsSahlq_dest_SO_cons (ST phi x)).
Proof.
  intros phi x Hvs.
  destruct (vsSahlq_dest_ex phi Hvs) as [phi1 [phi2 [Heq [Hvs1 Hun]]]].
  rewrite Heq.
  simpl.
  apply uni_pos__SO.
  assumption.
Qed.

Lemma vsS_preprocessing_Step3 : forall phi x,
  vsSahlq phi ->
  exists lv : list FOvariable,
    (exists rel : SecOrder,
     REL rel = true /\
     ((exists atm : SecOrder,
         AT atm = true /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (uni_closed_SO (allFO x (ST phi x))) <->
          SOturnst W Iv Ip Ir (uni_closed_SO (allFO x (list_closed_allFO (instant_cons_empty (implSO (conjSO rel atm) 
             (vsSahlq_dest_SO_cons (ST phi x)))) lv))))) \/
      (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
         (Ir : W -> W -> Prop),
       SOturnst W Iv Ip Ir (uni_closed_SO (allFO x (ST phi x))) <->
       SOturnst W Iv Ip Ir (uni_closed_SO (allFO x ((list_closed_allFO (instant_cons_empty (implSO rel 
                    (vsSahlq_dest_SO_cons (ST phi x)))) lv))))))) \/
  (exists atm : SecOrder,
     AT atm = true /\
     (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir (uni_closed_SO (allFO x (ST phi x))) <->
      SOturnst W Iv Ip Ir (uni_closed_SO (allFO x (list_closed_allFO (instant_cons_empty (implSO atm (vsSahlq_dest_SO_cons (ST phi x)))) lv))))).
Proof.
  intros phi x Hvs.
  destruct (vsS_preprocessing_Step2 phi x Hvs)
    as [lv [[rel [HREL [[atm [HAT H]] | H]]] | [atm [HAT H]]]];
    exists lv. left. exists rel.
    apply conj. assumption.
    left. exists atm.
    apply conj. assumption.
    intros W Iv Ip Ir.
    split; intros SOt.
      apply H in SOt.
      apply instant_cons_empty_equiv2_list_closed__allFO.
        apply SOQFree_vsS_pp_3_ra; assumption.
        apply uniform_pos_SO_vsSahlq_dest_SO_cons; assumption.
      assumption.

      apply H.
      apply instant_cons_empty_equiv2_list_closed__allFO.
        apply SOQFree_vsS_pp_3_ra; assumption.
        apply uniform_pos_SO_vsSahlq_dest_SO_cons; assumption.
      assumption.

    left. exists rel.
    apply conj. assumption.
    right.
    intros W Iv Ip Ir.
    split; intros SOt.
      apply H in SOt.
      apply instant_cons_empty_equiv2_list_closed__allFO.
        apply SOQFree_vsS_pp_3_r; assumption.
        apply uniform_pos_SO_vsSahlq_dest_SO_cons; assumption.
      assumption.

      apply H.
      apply instant_cons_empty_equiv2_list_closed__allFO.
        apply SOQFree_vsS_pp_3_r; assumption.
        apply uniform_pos_SO_vsSahlq_dest_SO_cons; assumption.
      assumption.

    right. exists atm.
    apply conj. assumption.
    intros W Iv Ip Ir.
    split; intros SOt.
      apply H in SOt.
      apply instant_cons_empty_equiv2_list_closed__allFO.
        apply SOQFree_vsS_pp_3_a; assumption.
        apply uniform_pos_SO_vsSahlq_dest_SO_cons; assumption.
      assumption.

      apply H.
      apply instant_cons_empty_equiv2_list_closed__allFO.
        apply SOQFree_vsS_pp_3_a; assumption.
        apply uniform_pos_SO_vsSahlq_dest_SO_cons; assumption.
      assumption.
Qed.

Definition corresp (phi : Modal) (alpha : SecOrder) : Prop :=
  forall (W : Set) (R : W -> W -> Prop) (Iv : FOvariable -> W)
         (Ip : predicate -> W -> Prop),
    mturnst_frame W R phi <-> SOturnst W Iv Ip R alpha.

