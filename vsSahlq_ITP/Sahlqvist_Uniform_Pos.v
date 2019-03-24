Require Export SO_sem_mods high_mods.
Require Import SO_facts1 Monotonicity_SO Correctness_ST uniform SO_facts_syn.

Lemma step1_empty : forall (W : Set) (Iv : FOvariable -> W)
                    (Ip : predicate -> W -> Prop)
                    (Ir : W -> W -> Prop)
                    (alpha : SecOrder) (P : predicate),
  SOQFree alpha = true ->
  Pred_is_pos_SO alpha P ->
  SOturnst W Iv Ip Ir (replace_pred alpha P (Var 1)
                          (negSO (eqFO (Var 1) (Var 1)))) ->
    forall pa : W -> Prop,
      SOturnst W Iv (alt_Ip Ip pa P) Ir alpha.
Proof.
  intros W Iv Ip Ir alpha P SOQFree Hpos SOt pa.
  apply rep_pred_false_pa_f in SOt; auto. 
  apply mono_pos; auto.
Qed.

Lemma step2_empty : forall (l : list predicate)
                    (W : Set) (Iv : FOvariable -> W)
                    (Ip : predicate -> W -> Prop)
                    (Ir : W -> W -> Prop)
                    (alpha : SecOrder),
  SOQFree alpha = true ->
  uniform_pos_SO alpha ->
    (SOturnst W Iv Ip Ir (replace_pred_l alpha l
          (nlist_list _ (nlist_var (length l) (Var 1)))
          (nlist_list _ (nlist_empty (length l))))) ->
  forall pa_l : nlist_pa W (length l),
    SOturnst W Iv (alt_Ip_list Ip
     (nlist_list_pa W (length l) pa_l) l) Ir alpha.
Proof.
  induction l; intros W Iv Ip Ir alpha Hno Huni SOt pa_l;
    simpl in *. rewrite alt_Ip_list_nil. auto.
  destruct (nlist_cons W (length l) pa_l) as [pa [pa_l' Heq]].
  rewrite Heq in *. simpl in *.
  destruct (Pred_in_SO_dec alpha a) as [HPocc | HPocc].
  - apply step1_empty; auto. 
    apply IHl; auto.
    + apply SOQFree_rep_pred_empty. auto.
    + apply uni_pos_rep_pred; auto.
    + rewrite rep_pred__l_switch_empty; auto.
  - apply P_not_occ_alt. auto.
    apply IHl; auto.
    rewrite rep_pred_Pred_in_SO_f in SOt. auto.
    apply P_occ_rep_pred_l_empty; auto.
Qed.

Lemma step3_empty : forall (W : Set) (Iv : FOvariable -> W)
                    (Ip : predicate -> W -> Prop)
                    (Ir : W -> W -> Prop)
                    (alpha : SecOrder),
  SOQFree alpha = true ->
  uniform_pos_SO alpha ->
    (SOturnst W Iv Ip Ir (replace_pred_l alpha (preds_in alpha)
          (nlist_list _ (nlist_var (length (preds_in alpha)) (Var 1)))
          (nlist_list _ (nlist_empty (length (preds_in alpha)))))) ->
  SOturnst W Iv Ip Ir (uni_closed_SO alpha).
Proof.
  intros. unfold uni_closed_SO.
  apply nlist_list_closed_SO.
  apply step2_empty; auto.
Qed.

Lemma Sahlqvist_uniform_pos_pre : forall (phi : Modal) (x : FOvariable),
  uniform_pos phi ->
    exists (alpha : SecOrder),
      (forall (D : Set) (Iv:FOvariable -> D) (Ip: predicate -> D -> Prop)
             (Ir: D -> D -> Prop),
      SOturnst D Iv Ip Ir (uni_closed_SO (allFO x (ST phi x))) <->
        SOturnst D Iv Ip Ir alpha) /\
      FO_frame_condition alpha = true.
Proof.
  intros phi x Hun.
  exists (replace_pred_l (allFO x (ST phi x))
          (preds_in (allFO x (ST phi x)))
          (nlist_list _ (nlist_var (length (preds_in (ST phi x))) (Var 1)))
          (nlist_list _ (nlist_empty (length (preds_in (ST phi x)))) )).
  apply conj.
  + intros D Iv Ip Ir.
    apply conj. apply instant_uni_closed; auto.
    simpl; intros H.
    apply step3_empty. apply SOQFree_ST.
    apply uni_pos_SO_allFO. apply uni_pos__SO ; auto.
    auto.
  + rewrite rep_pred_l_allFO. simpl.
    apply FO_frame_condition_rep_pred_l.
    apply FO_frame_condition_l_empty.
Defined.

Lemma Sahlqvist_uniform_pos : forall (phi : Modal),
  uniform_pos phi ->
    exists (alpha : SecOrder),
    ((forall (W : Set) (R : W -> W -> Prop) (Iv : FOvariable -> W)
           (Ip : predicate -> W -> Prop),
    mturnst_frame W R phi <-> SOturnst W Iv Ip R alpha) /\
    FO_frame_condition alpha = true).
Proof.
  intros phi Hpos.
  destruct (Sahlqvist_uniform_pos_pre phi (Var 1) Hpos) as [alpha H].
  exists alpha. apply conj; [|apply H].
  intros W R Iv Ip. split; intros H2.
  apply H. apply correctness_ST; auto.
  apply H in H2. apply correctness_ST in H2. auto.
Defined.