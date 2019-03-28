Require Export med_mods SO_semantics.
Require Import ST nlist_sem_eg.

Lemma rep_pred_false_pa_f : forall (alpha : SecOrder) (W : Set)
                      (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
                    (Ir : W -> W -> Prop)  (Q : predicate),
  SOQFree alpha = true ->
    (SOturnst W Iv (alt_Ip Ip pa_f Q) Ir alpha <->
      SOturnst W Iv Ip Ir (replace_pred alpha Q (Var 1)
       (negSO (eqFO (Var 1) (Var 1))))).
Proof.
  induction alpha; intros W Iv Ip Ir Q HallSO; [|firstorder|firstorder| | | |  | | | | ];
    try (    simpl in *; apply Bool.andb_true_iff in HallSO;
             destruct HallSO as [SO1 SO2]);
    try discriminate.

    unfold pa_f. simpl in *. 
    FOv_dec_l_rep.
    destruct (predicate_dec Q p) as [H|H]. subst.
    rewrite alt_Ip_eq.
    simpl. firstorder.
    rewrite alt_Ip_neq; auto. firstorder.    
    
    simpl; split; (intros H d; apply IHalpha;
                   [eapply SOQFree_allFO; exact HallSO| apply H]).
    simpl; split; (intros [d H]; exists d; apply IHalpha;
                   [eapply SOQFree_exFO; exact HallSO| apply H]).

    simpl in *; split; intros H1 H2; apply H1; apply IHalpha; auto.

    split; (intros [H1 H2]; apply conj; [apply IHalpha1 | apply IHalpha2]); auto.

    split; (intros [H1| H2]; [left; apply IHalpha1 | right; apply IHalpha2]); auto.

    split; intros H1 H2; (apply IHalpha2; auto; apply H1; apply IHalpha1; auto).
Qed.

Lemma SOt_list_closed_SOQFree : forall (l : list predicate) (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
                    (Ir : W -> W -> Prop) (alpha : SecOrder) ,
  SOQFree alpha = true ->
    SOturnst W Iv Ip Ir (list_closed_SO alpha l) ->
      SOturnst W Iv Ip Ir (replace_pred_l alpha l
                          (nlist_list _ (nlist_var (length l) (Var 1)))
                          (nlist_list _ (nlist_empty (length l)))).
Proof.
  induction l.
    intros W Iv Ip Ir alpha Hquant HSOt.
    simpl in *.
    assumption.

    intros W Iv Ip Ir alpha Hquant HSOt.
    simpl.
    apply rep_pred_false_pa_f. 
      apply SOQFree_rep_pred_l_nlist.
      assumption.

      apply IHl.
        assumption.

        simpl list_closed_SO in HSOt.
        rewrite SOturnst_allSO in HSOt.
        apply HSOt.
Qed.

Lemma instant_uni_closed : forall (phi : Modal) (D : Set) (Iv:FOvariable -> D)
                               (Ip: predicate -> D -> Prop) (Ir: D -> D -> Prop)
                               (x : FOvariable),
  (SOturnst D Iv Ip Ir (uni_closed_SO (allFO x (ST phi x))) ->
    (SOturnst D Iv Ip Ir (replace_pred_l (allFO x (ST phi x))
          (preds_in (allFO x (ST phi x)))
          (nlist_list _ (nlist_var (length (preds_in (ST phi x))) (Var 1)))
          (nlist_list _ (nlist_empty (length (preds_in (ST phi x)))) )))).
Proof.
  intros.
  unfold uni_closed_SO in H.
  assert (SOQFree (allFO x (ST phi x)) = true) as H2.
    simpl SOQFree.
    destruct x.
    apply SOQFree_ST.
  apply SOt_list_closed_SOQFree in H;  assumption.
Qed.

Lemma SOt_alt_SOQFree_t : forall (alpha : SecOrder) (W : Set)
                      (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
                    (Ir : W -> W -> Prop)  (Q : predicate),
  SOQFree alpha = true ->
    (SOturnst W Iv (alt_Ip Ip pa_t Q) Ir alpha <->
      SOturnst W Iv Ip Ir (replace_pred alpha Q (Var 1)
       (eqFO (Var 1) (Var 1)))).
Proof.
  induction alpha; intros W Iv Ip Ir Q HallSO;
    try solve [firstorder];
    try (  apply andb_prop in HallSO; destruct HallSO as [Hall1 Hall2]);
    try discriminate.

  simpl in *. FOv_dec_l_rep. 
  destruct (predicate_dec Q p) as [H | H]. subst.
  simpl. split; intros H. auto. rewrite alt_Ip_eq.
  firstorder.

  simpl. rewrite alt_Ip_neq; firstorder.

  simpl. split; intros H d; apply IHalpha; auto.
  
  simpl. split; intros [d H]; exists d; apply IHalpha; auto.

  simpl. split; intros H1 H2; apply H1; apply IHalpha; auto.
  
  split; (intros [H1 H2]; apply conj; [apply IHalpha1|apply IHalpha2]); auto.

  split; (intros [H1 | H2]; [left; apply IHalpha1 | right; apply IHalpha2]); auto.

  split; (intros H1 H2; apply IHalpha2; try auto; apply H1; apply IHalpha1; auto).
Qed.

Lemma SOt_list_closed_SOQFree_t : forall (l : list predicate) (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
                    (Ir : W -> W -> Prop) (alpha : SecOrder) ,
  SOQFree alpha = true ->
    SOturnst W Iv Ip Ir (list_closed_SO alpha l) ->
      SOturnst W Iv Ip Ir (replace_pred_l alpha l
                          (nlist_list _ (nlist_var (length l) (Var 1)))
                          (nlist_list _ (nlist_full (length l)))).
Proof.
  induction l.
    intros W Iv Ip Ir alpha Hquant HSOt.
    simpl in *.
    assumption.

    intros W Iv Ip Ir alpha Hquant HSOt.
    simpl.
    apply SOt_alt_SOQFree_t.
      apply SOQFree_rep_pred_l_t.
      assumption.

      apply IHl.
        assumption.

        simpl list_closed_SO in HSOt.
        rewrite SOturnst_allSO in HSOt.
        apply HSOt.
Qed.

Lemma instant_uni_closed_t : forall (phi : Modal) (D : Set) (Iv:FOvariable -> D)
                               (Ip: predicate -> D -> Prop) (Ir: D -> D -> Prop)
                               (x : FOvariable),
  (SOturnst D Iv Ip Ir (uni_closed_SO (allFO x (ST phi x))) ->
    (SOturnst D Iv Ip Ir (replace_pred_l (allFO x (ST phi x))
          (preds_in (allFO x (ST phi x)))
          (nlist_list _ (nlist_var (length (preds_in (ST phi x))) (Var 1)))
          (nlist_list _ (nlist_full (length (preds_in (ST phi x)))) )))).
Proof.
  intros.
  unfold uni_closed_SO in H.
  assert (SOQFree (allFO x (ST phi x)) = true) as H2.
    simpl SOQFree.
    destruct x.
    apply SOQFree_ST.
  apply SOt_list_closed_SOQFree_t in H; assumption.
Qed.


Lemma rep_pred_false_pa_t : forall (alpha : SecOrder)  (W : Set) (Iv : FOvariable -> W)
                    (Ip : predicate -> W -> Prop)
                    (Ir : W -> W -> Prop)
                    (P : predicate),
  SOQFree alpha = true ->
  SOturnst W Iv Ip Ir (replace_pred alpha P (Var 1)
                          (eqFO (Var 1) (Var 1))) <->
  SOturnst W Iv (alt_Ip Ip pa_t P) Ir alpha.
Proof.
  induction alpha; intros W Iv Ip Ir P noSO; try solve [firstorder];
try discriminate;
try (simpl in noSO; unfold andb in noSO; destruct_andb_t_simpl noSO noSO2; simpl).

simpl. FOv_dec_l_rep.
 destruct (predicate_dec P p) as [H1 | H1].
 subst. rewrite alt_Ip_eq. firstorder.
rewrite alt_Ip_neq; firstorder. 

simpl; split; intros H d; apply IHalpha; auto.

simpl; split; intros [d H]; exists d; apply IHalpha; auto.

simpl; split; intros H1 H2; apply H1; apply IHalpha; auto.

split; (intros [H1 H2];
apply conj; [apply IHalpha1| apply IHalpha2]; auto).

split; (intros [H1 | H2]; [left; apply IHalpha1| right; apply IHalpha2]; auto).

split; intros H1 H2; apply IHalpha2; try auto;
 apply H1; apply IHalpha1; auto.
Qed.
