Require Export low_mods.
Require Import Num_Occ Rep_Pred_FOv Indicies.

Fixpoint num_occ_l2_pre (alpha : SecOrder) (l : list predicate) : nat :=
  match l with
  | nil => 0
  | cons P l' => num_occ alpha P + num_occ_l2_pre alpha l'
  end.

Definition num_occ_l2 (alpha : SecOrder) (l : list predicate) : nat := 
    num_occ_l2_pre alpha (nodup predicate_dec l).

Lemma num_occ_l2_0 : forall (alpha : SecOrder),
  num_occ_l2 alpha nil = 0.
Proof. induction alpha; reflexivity. Qed.

Lemma num_occ_l2_cons_nil : forall (alpha : SecOrder) (P : predicate),
  num_occ_l2 alpha (cons P nil) = num_occ alpha P.
Proof. intros. unfold num_occ_l2. simpl. firstorder. Qed.

Lemma num_occ_l2_cons_same : forall (alpha : SecOrder) (P : predicate) (l : list predicate),
  num_occ_l2 alpha (cons P (cons P l)) = num_occ_l2 alpha (cons P l).
Proof.
  intros alpha P l. unfold num_occ_l2.
  simpl. destruct (predicate_dec P P). 
  auto. contradiction.
Qed.

Lemma num_occ_l2_cons_in : forall (alpha : SecOrder) (l : list predicate) (P : predicate),
  In P l ->
  num_occ_l2 alpha (cons P l) = num_occ_l2 alpha l. 
Proof.
  intros alpha l P H. unfold num_occ_l2. simpl.
  destruct (in_dec predicate_dec P l). auto.
  contradiction.
Qed.
 
Lemma num_occ_l2_cons_not_in : forall (alpha : SecOrder) (l : list predicate) (P : predicate),
  ~ In P l ->
  num_occ_l2 alpha (cons P l) = num_occ alpha P + num_occ_l2 alpha l. 
Proof.
  intros alpha l P H. unfold num_occ_l2. simpl.
  destruct (in_dec predicate_dec P l). contradiction.
  simpl. auto.
Qed.

Lemma num_occ_l2_allFO: forall (alpha : SecOrder) (x : FOvariable) (l : list predicate),
  num_occ_l2 (allFO x alpha) l = num_occ_l2 alpha l.
Proof.
  intros. unfold num_occ_l2.
  induction l. reflexivity.
  simpl. destruct (in_dec predicate_dec a l) as [Hocc | Hocc]. auto.
  simpl. rewrite num_occ_allFO. rewrite IHl. auto.
Qed.

Lemma num_occ_l2_exFO: forall (alpha : SecOrder) (x : FOvariable) (l : list predicate),
  num_occ_l2 (exFO x alpha) l = num_occ_l2 alpha l.
Proof.
  intros. unfold num_occ_l2.
  induction l. reflexivity.
  simpl. destruct (in_dec predicate_dec a l) as [Hocc | Hocc]. auto.
  simpl. rewrite num_occ_exFO. rewrite IHl. auto.
Qed.

Lemma num_occ_l2_negSO: forall (alpha : SecOrder) (l : list predicate),
  num_occ_l2 (negSO alpha) l = num_occ_l2 alpha l.
Proof.
  intros. unfold num_occ_l2.
  induction l. reflexivity.
  simpl. destruct (in_dec predicate_dec a l) as [Hocc | Hocc]. auto.
  simpl. rewrite IHl. auto.
Qed. 

Lemma num_occ_l2_conjSO : forall (alpha1 alpha2 : SecOrder) (l : list predicate),
  num_occ_l2 (conjSO alpha1 alpha2) l = num_occ_l2 alpha1 l + num_occ_l2 alpha2 l.
Proof.
  intros. induction l; unfold num_occ_l2 in *. reflexivity.
  simpl. destruct (in_dec (predicate_dec) a l).
  + rewrite IHl. auto.
  + simpl. rewrite IHl. rewrite num_occ_conjSO.  lia.    
Qed.

Lemma num_occ_l2_disjSO : forall (alpha1 alpha2 : SecOrder) (l : list predicate),
  num_occ_l2 (disjSO alpha1 alpha2) l = num_occ_l2 alpha1 l + num_occ_l2 alpha2 l.
Proof.
  intros. induction l; unfold num_occ_l2 in *. reflexivity.
  simpl. destruct (in_dec (predicate_dec) a l).
  + rewrite IHl. auto.
  + simpl. rewrite IHl. rewrite num_occ_disjSO.  lia.    
Qed. 

Lemma num_occ_l2_implSO : forall (alpha1 alpha2 : SecOrder) (l : list predicate),
  num_occ_l2 (implSO alpha1 alpha2) l = num_occ_l2 alpha1 l + num_occ_l2 alpha2 l.
Proof.
  intros. induction l; unfold num_occ_l2 in *. reflexivity.
  simpl. destruct (in_dec (predicate_dec) a l).
  + rewrite IHl. auto.
  + simpl. rewrite IHl. rewrite num_occ_implSO.  lia.    
Qed.

Lemma num_occ_l2_allSO : forall (alpha : SecOrder) (P : predicate) (l : list predicate),
(  In P l ->
  num_occ_l2 (allSO P alpha) l = num_occ_l2 alpha l + 1) /\
(  ~ In P l ->
  num_occ_l2 (allSO P alpha) l = num_occ_l2 alpha l).
Proof.
  intros alpha P l. revert alpha P.
  induction l; intros alpha P. simpl. firstorder.
  destruct (IHl alpha P) as [IH1 IH2].
  split; intros Hin. simpl in*.
  destruct (in_dec predicate_dec a l). 
    rewrite num_occ_l2_cons_in; auto.
    rewrite num_occ_l2_cons_in; auto.    
    apply IHl. destruct Hin; subst; firstorder. 
   
    rewrite num_occ_l2_cons_not_in; auto.
    rewrite num_occ_l2_cons_not_in; auto.
    destruct Hin. subst. 
    rewrite IH2. rewrite num_occ_allSO. rewrite predicate_dec_l; auto.
    lia. auto.

    rewrite IH1; auto. rewrite num_occ_allSO. destruct (predicate_dec P a).
    subst. firstorder. lia.

    simpl in Hin. 
    destruct (in_dec predicate_dec a l).
      rewrite num_occ_l2_cons_in; auto.
      rewrite num_occ_l2_cons_in; auto.

      rewrite num_occ_l2_cons_not_in; auto.
      rewrite num_occ_l2_cons_not_in; auto.
      rewrite IH2; auto. rewrite num_occ_allSO.
      rewrite predicate_dec_r;auto.
Qed.

Lemma num_occ_l2_exSO : forall (alpha : SecOrder) (P : predicate) (l : list predicate),
(  In P l ->
  num_occ_l2 (exSO P alpha) l = num_occ_l2 alpha l + 1) /\
(  ~ In P l ->
  num_occ_l2 (exSO P alpha) l = num_occ_l2 alpha l).
Proof.
  intros alpha P l. revert alpha P.
  induction l; intros alpha P. simpl. firstorder.
  destruct (IHl alpha P) as [IH1 IH2].
  split; intros Hin. simpl in*.
  destruct (in_dec predicate_dec a l). 
    rewrite num_occ_l2_cons_in; auto.
    rewrite num_occ_l2_cons_in; auto.    
    apply IHl. destruct Hin; subst; firstorder. 
   
    rewrite num_occ_l2_cons_not_in; auto.
    rewrite num_occ_l2_cons_not_in; auto.
    destruct Hin. subst. 
    rewrite IH2. rewrite num_occ_exSO. rewrite predicate_dec_l; auto.
    lia. auto.

    rewrite IH1; auto. rewrite num_occ_exSO. destruct (predicate_dec P a).
    subst. firstorder. lia.

    simpl in Hin.
    destruct (in_dec predicate_dec a l).
      rewrite num_occ_l2_cons_in; auto.
      rewrite num_occ_l2_cons_in; auto.

      rewrite num_occ_l2_cons_not_in; auto.
      rewrite num_occ_l2_cons_not_in; auto.
      rewrite IH2; auto. rewrite num_occ_exSO.
      rewrite predicate_dec_r;auto.
Qed.

Lemma num_occ_l2_allSO_in : forall (alpha : SecOrder) (P : predicate) (l : list predicate),
  In P l ->
  num_occ_l2 (allSO P alpha) l = num_occ_l2 alpha l + 1.
Proof.  intros alpha P l. apply num_occ_l2_allSO. Qed. 

Lemma num_occ_l2_allSO_not_in : forall (alpha : SecOrder) (P : predicate) (l : list predicate),
  ~ In P l ->
  num_occ_l2 (allSO P alpha) l = num_occ_l2 alpha l.
Proof.  intros alpha P l. apply num_occ_l2_allSO. Qed. 

Lemma num_occ_l2_exSO_in : forall (alpha : SecOrder) (P : predicate) (l : list predicate),
  In P l ->
  num_occ_l2 (exSO P alpha) l = num_occ_l2 alpha l + 1.
Proof.  intros alpha P l. apply num_occ_l2_exSO. Qed. 

Lemma num_occ_l2_exSO_not_in : forall (alpha : SecOrder) (P : predicate) (l : list predicate),
  ~ In P l ->
  num_occ_l2 (exSO P alpha) l = num_occ_l2 alpha l.
Proof.  intros alpha P l. apply num_occ_l2_exSO. Qed. 


Lemma num_occ_l2_app_l : forall (alpha : SecOrder) (l : list predicate),
num_occ_l2 alpha (app l (preds_in alpha)) = num_occ_l2 alpha (preds_in alpha).
Proof.
  intros alpha l. induction l. reflexivity.
  simpl.  destruct (in_dec predicate_dec a (l ++ (preds_in alpha))) as [Hocc | Hocc].
    rewrite num_occ_l2_cons_in; auto.

    rewrite num_occ_l2_cons_not_in; auto.
    rewrite IHl. rewrite num_occ_not_in; firstorder.
Qed. 

Lemma num_occ_l2_cons_switch : forall (alpha : SecOrder) (P Q : predicate) (l : list predicate),
  num_occ_l2 alpha (cons P (cons Q l)) = num_occ_l2 alpha (cons Q (cons P l)).
Proof.
  intros. destruct (in_dec predicate_dec P (Q :: l)) as [H1 | H1].
  rewrite num_occ_l2_cons_in; auto. simpl in H1.
  destruct (predicate_dec Q P). 
  + subst. destruct (in_dec predicate_dec P l) as [H2 | H2].
    rewrite num_occ_l2_cons_in; auto. rewrite num_occ_l2_cons_in. 
    rewrite num_occ_l2_cons_in; auto. firstorder.
    rewrite num_occ_l2_cons_not_in. rewrite num_occ_l2_cons_in.
    rewrite num_occ_l2_cons_not_in. all : auto. 
  + destruct H1. firstorder. destruct (in_dec predicate_dec Q l).
    rewrite num_occ_l2_cons_in. rewrite num_occ_l2_cons_in.
    rewrite num_occ_l2_cons_in. all : auto. simpl. firstorder.
    rewrite num_occ_l2_cons_not_in; auto.
    rewrite num_occ_l2_cons_not_in. rewrite num_occ_l2_cons_in.
    all : auto. simpl. firstorder.
  + simpl in *. rewrite num_occ_l2_cons_not_in. 
    destruct (in_dec predicate_dec Q l). rewrite num_occ_l2_cons_in; auto.
    rewrite num_occ_l2_cons_in; auto. rewrite num_occ_l2_cons_not_in; auto.
    simpl. firstorder. rewrite num_occ_l2_cons_not_in.
    rewrite num_occ_l2_cons_not_in. rewrite num_occ_l2_cons_not_in.
    all : firstorder.
Qed.

Lemma num_occ_l2_app_cons : forall (alpha : SecOrder) (l1 l2 : list predicate)
                                   (P : predicate),
num_occ_l2 alpha (app l1 (cons P l2)) = num_occ_l2 alpha (cons P (app l1 l2)).
Proof.
  intros. induction l1. reflexivity.  simpl.
  rewrite num_occ_l2_cons_switch.
  destruct (in_dec predicate_dec a (l1 ++ l2)) as [H | H].
  + rewrite num_occ_l2_cons_in. rewrite num_occ_l2_cons_in.
    apply IHl1. simpl. firstorder. 
    apply in_app_iff in H. apply in_app_iff. destruct H; auto.
    right. simpl. firstorder.
  + destruct (predicate_dec a P). subst. rewrite num_occ_l2_cons_in.
    rewrite num_occ_l2_cons_in. auto. simpl. firstorder. firstorder. 
    rewrite num_occ_l2_cons_not_in.     rewrite num_occ_l2_cons_not_in. 
    rewrite IHl1. auto. simpl. firstorder. intros H2. apply H.
    apply in_or_app. apply in_app_or in H2. firstorder.
    subst. contradiction.
Qed.

Lemma num_occ_l2_app : forall l1 l2 alpha,
num_occ_l2 alpha (l1 ++ l2) = num_occ_l2 alpha (l2 ++ l1).
Proof.
  induction l1; intros l2 alpha. simpl. rewrite app_nil_r. auto.
  simpl. destruct (in_dec predicate_dec a (l1 ++ l2)) as [H | H].
  + rewrite num_occ_l2_cons_in. rewrite IHl1. rewrite num_occ_l2_app_cons.
    rewrite num_occ_l2_cons_in. auto.
    apply in_app_iff. apply in_app_iff in H. firstorder. auto.
  + rewrite num_occ_l2_cons_not_in. rewrite IHl1. 
    rewrite num_occ_l2_app_cons. rewrite num_occ_l2_cons_not_in. auto.
    intros H2. apply in_app_iff in H2. firstorder. auto.
Qed.

Lemma num_occ_l2_app_r : forall (alpha : SecOrder) (l : list predicate),
num_occ_l2 alpha (app (preds_in alpha) l) = num_occ_l2 alpha (preds_in alpha).
Proof. intros. rewrite num_occ_l2_app. apply num_occ_l2_app_l. Qed.       

Lemma num_occ_l2_preds_in : forall alpha : SecOrder,
  num_occ_l2 alpha (preds_in alpha) = length (preds_in alpha).
Proof.
  induction alpha; simpl; unfold num_occ; simpl;
    try reflexivity; simpl.

    unfold num_occ_l2. simpl. rewrite num_occ_predSO.
    rewrite predicate_dec_l. lia. tauto. 

    rewrite num_occ_l2_allFO.
    assumption.

    rewrite num_occ_l2_exFO.
    assumption.

    rewrite num_occ_l2_negSO.
    assumption.

    rewrite app_length.
    rewrite <- IHalpha1.
    rewrite <- IHalpha2.
    rewrite num_occ_l2_conjSO.
    rewrite num_occ_l2_app_l.
    rewrite num_occ_l2_app_r.
    reflexivity.

    rewrite app_length.
    rewrite <- IHalpha1.
    rewrite <- IHalpha2.
    rewrite num_occ_l2_disjSO.
    rewrite num_occ_l2_app_l.
    rewrite num_occ_l2_app_r.
    reflexivity.
    
    rewrite app_length.
    rewrite <- IHalpha1.
    rewrite <- IHalpha2.
    rewrite num_occ_l2_implSO.
    rewrite num_occ_l2_app_l.
    rewrite num_occ_l2_app_r.
    reflexivity.

    rewrite num_occ_l2_allSO_in.
    simpl. destruct (in_dec predicate_dec p (preds_in alpha)).
    rewrite num_occ_l2_cons_in.  rewrite IHalpha. firstorder. auto.
    rewrite num_occ_l2_cons_not_in. rewrite IHalpha.
      rewrite num_occ_not_in. firstorder. all : auto. simpl. firstorder.

    rewrite num_occ_l2_exSO_in.
    simpl. destruct (in_dec predicate_dec p (preds_in alpha)).
    rewrite num_occ_l2_cons_in.  rewrite IHalpha. firstorder. auto.
    rewrite num_occ_l2_cons_not_in. rewrite IHalpha.
      rewrite num_occ_not_in. firstorder. all : auto. simpl. firstorder.
Qed.

Lemma FO_frame_condition_rep_pred_l_pre : forall 
                          (l : list predicate)
                          (alpha : SecOrder)
                          (l1: nlist (length l))
                          (l2 : nlist (length l)),
FO_frame_condition_l (nlist_list _ l2) = true ->
length (preds_in (replace_pred_l alpha l
                (nlist_list _ l1)
                (nlist_list _ l2))) =  length (preds_in alpha) - num_occ_l2 alpha l.
Proof.
  intros l. induction l; intros alpha l1 l2 Hun; simpl in *.
  rewrite num_occ_l2_0.  lia.
  destruct (nlist_cons2 _ l1) as [x [l1' H1]].
  destruct (nlist_cons2 _ l2) as [beta [l2' H2]].
  rewrite H1 in *; rewrite H2 in *.
  simpl in *.
  case_eq (FO_frame_condition beta); intros Hun2; rewrite Hun2 in *.
    rewrite preds_in_rep_pred; try assumption.
    destruct (in_dec predicate_dec a l) as [Hocc | Hocc]. 
      rewrite num_occ_l2_cons_in; auto.
      rewrite IHl; try assumption.
      rewrite num_occ__in_l_t; try assumption. lia.

      rewrite num_occ_l2_cons_not_in; auto.
      rewrite IHl; try assumption.
      rewrite num_occ__in_l_f; try assumption. lia.

    discriminate.
Qed.

Lemma FO_frame_condition_rep_pred_l : forall (alpha : SecOrder)
                          (l1: nlist (length (preds_in alpha)))
                          (l2 : nlist (length (preds_in alpha))),
FO_frame_condition_l (nlist_list _ l2) = true ->
FO_frame_condition (replace_pred_l alpha (preds_in alpha)
                (nlist_list _ l1)
                (nlist_list _ l2)) = true.
Proof.
  pose proof FO_frame_condition_rep_pred_l_pre as H2.
  intros alpha l1 l2 H.
  specialize (H2 (preds_in alpha) alpha l1 l2 H).
  rewrite num_occ_l2_preds_in in H2.
  apply FO_frame_condition_preds_in2. lia.
Qed.
