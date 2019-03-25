Require Export SO_semantics Modal_semantics ST.
Require Import preds_in nlist_sem Lia.

Lemma correct_ST_world_box : forall (W:Set) (R: W -> W -> Prop) (V: propvar -> W -> Prop) (phi:Modal), 
                               (forall (w:W) (x:FOvariable) (Iv: FOvariable -> W), 
       (mturnst W R V w phi) <-> (SOturnst W (alt_Iv Iv w x) (V_to_Ip W V) R (ST phi x))) 
                                  -> (forall (w:W) (x:FOvariable) (Iv: FOvariable -> W), 
          (mturnst W R V w (box phi)) <-> (SOturnst W (alt_Iv Iv w x) (V_to_Ip W V) R (ST (box phi) x))).
Proof.
  intros W R V phi IHphi w x Iv.
  apply conj; simpl; intros pf_mturnst d pf_relat;
    specialize (pf_mturnst d); rewrite alt_Iv_eq in *;
    (rewrite alt_Iv_neq in *; [|apply next_FOv_not]);
    eapply IHphi; apply pf_mturnst; rewrite alt_Iv_eq in *; auto.
Qed.

Lemma correct_ST_world_diam : forall (W:Set) (R: W -> W -> Prop) (V: propvar -> W -> Prop) (phi:Modal), 
                                 (forall (w:W) (x:FOvariable) (Iv: FOvariable -> W), 
      (mturnst W R V w phi) <-> (SOturnst W (alt_Iv Iv w x) (V_to_Ip W V) R (ST phi x))) 
                                   -> (forall (w:W) (x:FOvariable) (Iv: FOvariable -> W), 
         (mturnst W R V w (diam phi)) <-> (SOturnst W (alt_Iv Iv w x) (V_to_Ip W V) R (ST (diam phi) x))).
Proof.
  intros W R V phi IHphi w x Iv.
  apply conj; (simpl; intros [d [pf_mturnst pf_relat]];
    exists d; rewrite alt_Iv_eq in *;
    (rewrite alt_Iv_neq in *; [|apply next_FOv_not]);
    apply conj; [rewrite alt_Iv_eq in *|]; auto;
    eapply IHphi; apply pf_relat).
Qed.

Theorem correctness_ST_world : forall (W:Set) (R: W -> W -> Prop) (V: propvar -> W -> Prop) 
                                      (phi:Modal) (w:W) (x:FOvariable) (Iv: FOvariable -> W),
              (mturnst W R V w phi) <-> 
                    (SOturnst W (alt_Iv Iv w x) (V_to_Ip W V) R (ST phi x)).
Proof.
  induction phi; intros w x Iv.

  rewrite ST_atom_pred. simpl. rewrite alt_Iv_eq.
  apply V_to_Ip_ST_pv.
  simpl. split; intros H1 H2; apply H1;
           apply (IHphi _ x Iv); auto.

  simpl; split; intros [H1 H2];
  (apply conj; [apply (IHphi1 _ x Iv) | apply (IHphi2 _ x Iv)]); auto.

  simpl; split; (intros [H1 | H2];
    [left; apply (IHphi1 _ x Iv) | right; apply (IHphi2 _ x Iv)]); auto.

  simpl; split; intros H1 H2;
    (apply (IHphi2 _ x Iv); apply H1; apply (IHphi1 _ x Iv)); auto.

  apply correct_ST_world_box. auto.

  apply correct_ST_world_diam. auto.
Qed.

Theorem correctness_ST_model: forall (W:Set) (R: W -> W -> Prop) (V: propvar -> W -> Prop) 
                             (phi:Modal) (x:FOvariable) (Iv: FOvariable -> W),
                                 (mturnst_model W R V phi) <-> 
                                        (SOturnst W Iv (V_to_Ip W V) R (allFO x (ST phi x))).
Proof.
  intros. unfold mturnst_model.
  split; intros H w; eapply correctness_ST_world; apply H.
Qed.

Lemma nlist_list_closed_SO : forall (W : Set) (Iv : FOvariable -> W) 
                           (Ir: W -> W -> Prop) (alpha: SecOrder) (l : list predicate) 
                           (Ip: predicate -> W -> Prop),
     SOturnst W Iv Ip Ir (list_closed_SO alpha l) <->
   forall pa_l : (nlist_pa W (length l)),
      SOturnst W Iv (alt_Ip_list Ip (nlist_list_pa W (length l) pa_l) l) Ir alpha.
Proof.
  intros W Iv Ir alpha l.
  induction l.
    simpl.
    split.
      intros H pa_l.
      rewrite alt_Ip_list_nil.
      exact H.

      intros H.
      specialize (H (niln_pa W)).
      rewrite alt_Ip_list_nil in H.
      exact H.

    intros.
    split.
      intros.
      assert (exists (pa1 : W -> Prop) (pa_l1 : nlist_pa W (length l)), 
              (pa_l = consn_pa W (length l) pa1 pa_l1)).
         apply nlist_cons.
      destruct H0 as [pa1 [pa_l1 H0]].
      rewrite H0.
      simpl nlist_list_pa.
      simpl alt_Ip_list.
      assert (exists (pa : W -> Prop) (pa_l : nlist_pa W (length l)),
            (alt_Ip (alt_Ip_list Ip (nlist_list_pa W (length l) pa_l1) l) pa1 a) = 
            (alt_Ip_list (alt_Ip Ip pa a) (nlist_list_pa W (length l) pa_l) l)).
        apply alt_alt_list_1.
      destruct H1 as [pa2 [pa_l2 H1]].
      rewrite H1.
      apply IHl.
      simpl list_closed_SO in H.
      rewrite SOturnst_allSO in H.
      specialize (H pa2).
      exact H.

      intros.
      simpl list_closed_SO.
      rewrite SOturnst_allSO.
      intros.
      apply IHl.
      intros.
      simpl in H.
      assert (exists (pred_asgmt1 : W -> Prop) (pa_l1 : nlist_pa W (length l)),
           (alt_Ip (alt_Ip_list Ip (nlist_list_pa W (length l) pa_l1) l)
              pred_asgmt1 a) = 
           (alt_Ip_list (alt_Ip Ip pred_asgmt a) 
              (nlist_list_pa W (length l) pa_l) l)).
         apply alt_alt_list_2.
       destruct H0 as [pred_asgmt1 [pa_l1 H0]].
       rewrite <- H0.
       specialize (H (consn_pa W (length l) pred_asgmt1 pa_l1)).
       apply H.
Qed.

Lemma  nlist_list_closed_SO'  : forall (W : Set) (Iv : FOvariable -> W) 
                           (Ir: W -> W -> Prop) (alpha: SecOrder) (l : list predicate) 
                           (Ip: predicate -> W -> Prop),
     SOturnst W Iv Ip Ir (list_closed_SO alpha l) <->
   forall pa_l : (nlist (length l)),
      SOturnst W Iv (alt_Ip_list Ip (nlist_list (length l) pa_l) l) Ir alpha.
Proof.
  intros W Iv Ir alpha l.
  induction l.
    simpl.
    split.
      intros H pa_l.
      rewrite alt_Ip_list_nil.
      exact H.

      intros H.
      specialize (H (niln)).
      rewrite alt_Ip_list_nil in H.
      exact H.

    intros.
    split.
      intros.
      assert (exists (pa1 : W -> Prop) (pa_l1 : nlist (length l)), 
              (pa_l = consn (length l) pa1 pa_l1)).
         apply nlist_cons2.
      destruct H0 as [pa1 [pa_l1 H0]].
      rewrite H0.
      simpl nlist_list_pa.
      simpl alt_Ip_list.
      assert (exists (pa : W -> Prop) (pa_l : nlist (length l)),
            (alt_Ip (alt_Ip_list Ip (nlist_list (length l) pa_l1) l) pa1 a) = 
            (alt_Ip_list (alt_Ip Ip pa a) (nlist_list (length l) pa_l) l)).
        apply alt_alt_list_1'.
      destruct H1 as [pa2 [pa_l2 H1]].
      rewrite H1.
      apply IHl.
      simpl list_closed_SO in H.
      rewrite SOturnst_allSO in H.
      specialize (H pa2).
      exact H.

      intros.
      simpl list_closed_SO.
      rewrite SOturnst_allSO.
      intros.
      apply IHl.
      intros.
      simpl in H.
      assert (exists (pred_asgmt1 : W -> Prop) (pa_l1 : nlist (length l)),
           (alt_Ip (alt_Ip_list Ip (nlist_list (length l) pa_l1) l)
              pred_asgmt1 a) = 
           (alt_Ip_list (alt_Ip Ip pred_asgmt a) 
              (nlist_list (length l) pa_l) l)).
         apply alt_alt_list_2'.
       destruct H0 as [pred_asgmt1 [pa_l1 H0]].
       rewrite <- H0.
       specialize (H (consn (length l) pred_asgmt1 pa_l1)).
       apply H.
Qed.

Lemma same_preds_in : forall (W:Set)(alpha : SecOrder) (Ip Ip': predicate -> W -> Prop)
                             (Ir: W -> W -> Prop) (Iv : FOvariable -> W),
    same_Ip_list Ip Ip' (preds_in alpha) ->
     (SOturnst W Iv Ip Ir alpha -> SOturnst W Iv Ip' Ir alpha).
Proof.
  induction alpha; intros Ip Ip' Ir Iv H1 H2; simpl in *; auto.
  + inversion H1; subst. rewrite <- H3. auto. 
  + intros d. apply (IHalpha Ip); auto.
  + destruct H2 as [d H2]. exists d. 
    apply (IHalpha Ip); auto.
  + intros H3; apply H2. apply (IHalpha Ip'); auto.
    apply same_comm. auto.
  + destruct H2 as [H2 H3].
    apply same_app2 in H1. destruct H1 as [Ha Hb].
    apply conj; [apply (IHalpha1 Ip)| apply (IHalpha2 Ip)]; auto.
  + apply same_app2 in H1. destruct H1 as [Ha Hb].
    destruct H2 as [H2| H3]; [ left; apply (IHalpha1 Ip)|
      right; apply (IHalpha2 Ip)]; auto.
  + intros H3. apply same_app2 in H1. destruct H1 as [Ha Hb].
    apply (IHalpha2 Ip); auto. apply H2. apply (IHalpha1 Ip');
    auto. rewrite same_comm. auto.
  + intros pa. apply (IHalpha (alt_Ip Ip pa p)); auto.
    apply same_alt_rem. apply same_rem. inversion H1; auto. 
  + destruct H2 as [pa H2]. exists pa. 
    apply (IHalpha (alt_Ip Ip pa p)); auto.
    apply same_alt_rem. apply same_rem. inversion H1; auto. 
Qed.

Lemma same_preds_in_without : forall (W:Set) (l : list predicate)
                              (alpha : SecOrder) (Ip Ip': predicate -> W -> Prop)
                              (Ir: W -> W -> Prop) (Iv : FOvariable -> W),
    same_Ip_list Ip Ip' (list_pred_without (preds_in alpha) l) ->
     (SOturnst W Iv Ip Ir (list_closed_SO alpha l) -> 
         SOturnst W Iv Ip' Ir (list_closed_SO alpha l)).
Proof.
  induction l; intros; simpl in *. 
    apply same_preds_in with (Ip := Ip); auto.
  intros pa. specialize (H0 pa).
  apply IHl with (Ip := (alt_Ip Ip pa a)); auto.
  apply same_alt_rem.
  rewrite <- list_pred_without_rem.
  auto.
Qed.

(* For universally closed formulas, Ip doesn't matter. *)
Lemma Ip_uni_closed : forall (W:Set) (alpha : SecOrder) (Iv: FOvariable -> W)
                             (Ip Ip': predicate -> W -> Prop)
                             (Ir: W -> W -> Prop)  , 
     SOturnst W Iv Ip Ir (uni_closed_SO alpha) -> SOturnst W Iv Ip' Ir (uni_closed_SO alpha).
Proof.
  intros.  unfold uni_closed_SO in *.
  apply same_preds_in_without with (Ip := Ip); auto.
  rewrite list_pred_without_id. constructor.  
Qed.

Theorem correctness_ST : forall (W:Set) (R: W -> W -> Prop) (x:FOvariable) 
                        (Iv: FOvariable -> W) (Ip: predicate -> W -> Prop) 
                        (phi:Modal) ,
       (mturnst_frame W R phi) <-> 
                (SOturnst W Iv Ip R (uni_closed_SO (allFO x (ST phi x)))).
Proof.
  intros.
  unfold mturnst_frame.
  split.
    unfold uni_closed_SO.
    intros.
    apply nlist_list_closed_SO.
    intros.
    rewrite <- (Ip_V_Ip W) with (Ip := (alt_Ip_list Ip
                  (nlist_list_pa W (length (preds_in (allFO x (ST phi x)))) pa_l)
                  (preds_in (allFO x (ST phi x))))).
    apply correctness_ST_model.
    apply H.

    intros.
    apply (correctness_ST_model W R V phi x Iv).
    remember (preds_in (allFO x (ST phi x))) as l.
    assert (alt_Ip_list (V_to_Ip W V)
       (nlist_list_pa W (length l)
          (ineffective_pa_l W (V_to_Ip W V) (length l) (list_nlist l))) l = 
              V_to_Ip W V) as H0.
      rewrite Heql.
      apply ineffective_Ip2.
    rewrite <- H0.
    apply (nlist_list_closed_SO W Iv R (allFO x (ST phi x)) l (V_to_Ip W V)).
    rewrite Heql.
    pose proof (Ip_uni_closed W (allFO x (ST phi x)) Iv Ip (V_to_Ip W V) R H) as H1.
    apply H1.
Qed.

Theorem correctness_ST_loc : forall (W:Set) (R: W -> W -> Prop) (x:FOvariable) 
                        (Iv: FOvariable -> W) (Ip: predicate -> W -> Prop) (w : W)
                        (phi:Modal) ,
       (mturnst_frame_loc W R w phi) <-> 
                (SOturnst W (alt_Iv Iv w x) Ip R (uni_closed_SO (ST phi x))).
Proof.
  intros.
  unfold mturnst_frame.
  split.
    unfold uni_closed_SO.
    intros.
    apply nlist_list_closed_SO.
    intros.
    rewrite <- (Ip_V_Ip W) with (Ip := (alt_Ip_list Ip
                  (nlist_list_pa W (length (preds_in (ST phi x))) pa_l)
                  (preds_in (ST phi x)))).
    apply correctness_ST_world.
    apply H.

    intros. intros V.
    apply (correctness_ST_world W R V phi w x Iv).
    remember (preds_in (allFO x (ST phi x))) as l.
    assert (alt_Ip_list (V_to_Ip W V)
       (nlist_list_pa W (length l)
          (ineffective_pa_l W (V_to_Ip W V) (length l) (list_nlist(*_pred*) l))) l = 
              V_to_Ip W V) as H0.
      rewrite Heql.
      apply ineffective_Ip2.
    rewrite <- H0.
    apply (nlist_list_closed_SO W _ R (ST phi x) l (V_to_Ip W V)).
    rewrite Heql.
    pose proof (Ip_uni_closed W (ST phi x) _ Ip (V_to_Ip W V) R H) as H1.
    apply H1.
Qed.