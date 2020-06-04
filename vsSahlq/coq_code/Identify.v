Require Export low_mods.
Require Import Num_Occ Indicies Num_occ_l Rep_Pred_FOv.

Fixpoint identify_fwd (alpha : SecOrder) (P : predicate) (i : nat) : nat :=
  if occ_in_SO_dec alpha i then
  match alpha with
    predSO Q x => if predicate_dec P Q then 0 else i
  | relatSO _ _  => 0
  | eqFO _ _ => 0
  | allFO x beta => identify_fwd beta P i
  | exFO x beta => identify_fwd beta P i
  | negSO beta => identify_fwd beta P i
  | conjSO beta1 beta2 => if occ_in_SO_dec beta1 i
                               then identify_fwd beta1 P i
                               else identify_fwd beta2 P 
                                        (i - (length (preds_in beta1)))
                                      + (length (preds_in beta1))
                                      - num_occ beta1 P
  | disjSO beta1 beta2 => if occ_in_SO_dec beta1 i
                               then identify_fwd beta1 P i
                               else identify_fwd beta2 P 
                                        (i - (length (preds_in beta1)))
                                      + (length (preds_in beta1))
                                      - num_occ beta1 P
  | implSO beta1 beta2 => if occ_in_SO_dec beta1 i
                               then identify_fwd beta1 P i
                               else identify_fwd beta2 P 
                                        (i - (length (preds_in beta1)))
                                      + (length (preds_in beta1))
                                      - num_occ beta1 P
  | allSO Q beta => if predicate_dec P Q
                               then identify_fwd beta P (i - 1)
                               else identify_fwd beta P (i - 1) + 1
  | exSO Q beta => if predicate_dec P Q
                               then identify_fwd beta P (i - 1)
                               else identify_fwd beta P (i - 1) + 1
  end else i.

Lemma identify_fwd_0 : forall (alpha : SecOrder) (P :predicate),
  identify_fwd alpha P 0 = 0.
Proof. 
  induction alpha; intros P; simpl;
    rewrite occ_in_SO_dec_r; auto;
    apply occ_in_SO_0. 
Qed. 

Fixpoint identify_rev_l (l : list predicate) (P : predicate) (i : nat)
                                          : nat :=

  match i, l with
  | 0, _ => 0
  | _, nil => 0
  | S j, cons Q l' =>
    1 + if predicate_dec P Q then identify_rev_l l' P i else identify_rev_l l' P j 
end.

Lemma identify_rev_l_0 : forall (l : list predicate) (P : predicate),
  identify_rev_l l P 0 = 0.
Proof. intros. induction l; auto. Qed.

Lemma identify_rev_l_cons : forall (l : list predicate) (P Q : predicate)
                                   (i : nat),
  ~ i = 0 ->
  identify_rev_l (cons Q l) P i = 1 + 
if predicate_dec P Q then identify_rev_l l P i else identify_rev_l l P (pred i).
Proof. intros ? ? ?  i. destruct i. contradiction. auto. Qed.

Lemma identify_rev_l_cons_S0 : forall (l : list predicate)
                                      (P Q : predicate),
~ P = Q ->  identify_rev_l (cons Q l) P 1 = 1.
Proof.
  intros l P Q Hbeq.  simpl. rewrite predicate_dec_r.
  rewrite identify_rev_l_0. all : auto.
Qed.

Lemma identify_rev_l_app_S0 : forall (l1 l2 : list predicate)
                                     (P : predicate),
~ (length l1 - (length (indicies_l_rev l1 P))) = 0 ->
    identify_rev_l (app l1 l2) P 1 = identify_rev_l l1 P 1.
Proof.
  induction l1; intros l2 P Hleb. contradiction.
  case_eq l1. intros Hnil. subst. simpl in *. 
    destruct (predicate_dec P a). rewrite predicate_dec_l in Hleb.
    contradiction. auto.
    rewrite identify_rev_l_0. auto.
  intros PP lPP HlPP. rewrite <- HlPP.
  simpl. destruct (predicate_dec P a). subst a.
  simpl in Hleb. rewrite predicate_dec_l in Hleb. simpl in Hleb.
  rewrite IHl1; auto. auto.
  do 2 rewrite identify_rev_l_0. auto.
Qed.

Lemma identify_rev_l_app_1_cons : forall ( l2 : list predicate)
                                         (P Q : predicate) (i : nat),
  ~ i = 0 ->
    i <= (length (cons Q nil) - 
          (length (indicies_l_rev (cons Q nil) P))) ->
      identify_rev_l (cons Q l2) P i = 1.
Proof.
  intros l2 P Q i Hbeq Hleb.
  rewrite identify_rev_l_cons in *.
  rewrite indicies_l_rev_cons in *.
  destruct i. contradiction. 
  simpl in *. destruct (predicate_dec P Q).
  rewrite predicate_dec_l in Hleb; auto. simpl in *. lia. 
  rewrite predicate_dec_r in Hleb; auto. simpl in *. 
  destruct i. rewrite identify_rev_l_0. auto. lia. auto. 
Qed.

Lemma identify_rev_l_app_l : forall (l1 l2 : list predicate) (P : predicate)
                                   (i : nat),
  ~ i = 0 ->
  i <= (length l1 + length l2 - (length 
                            (indicies_l_rev (app l1 l2) P))) ->
  i <= ((length l1) - (length (indicies_l_rev l1 P))) ->
             identify_rev_l (app l1 l2) P i = identify_rev_l l1 P i.
Proof.
  induction l1; intros  l2 P i Hbeq Hleb1 Hleb2.
    simpl in *. apply Nat.le_0_r in Hleb2.
    contradiction.

    simpl app.
    rewrite identify_rev_l_cons;
    try rewrite identify_rev_l_cons; try assumption.
    destruct (predicate_dec P a) as [Hbeq2 | Hbeq2]. subst. 
      rewrite IHl1; simpl in *.
        reflexivity. assumption.

        rewrite predicate_dec_l in Hleb1; auto.
        rewrite predicate_dec_l in Hleb2; auto.

      simpl in *. rewrite predicate_dec_r in Hleb1; auto.
      rewrite predicate_dec_r in Hleb2; auto.
      destruct i. lia. destruct i. simpl.
      do 2 rewrite identify_rev_l_0. auto.
      rewrite IHl1; auto. simpl. auto.
      simpl. destruct (length (indicies_l_rev (l1 ++ l2) P)). lia. lia. 
      simpl. destruct (length (indicies_l_rev l1 P) ); lia.
Qed.

Lemma identify_rev_l_app_r_1 : forall (l1 l2 : list predicate) (P : predicate),
  ~ (length l1 + length l2 - (length 
                            (indicies_l_rev (app l1 l2) P))) = 0 ->
   ((length l1) - (length (indicies_l_rev l1 P))) = 0 ->
             identify_rev_l (app l1 l2) P 1 = 
                 (identify_rev_l l2 P (1 - ((length l1) - 
                                      (length (indicies_l_rev l1 P))))) +
                  (length l1).
Proof.
  induction l1; intros l2 P Hleb1 Hleb2; simpl in *. auto.
  destruct (predicate_dec P a). subst.
  + rewrite predicate_dec_l in *; auto.
    simpl in *. firstorder.
  + rewrite predicate_dec_r in *; auto.
    rewrite identify_rev_l_0.
    case_eq (length (indicies_l_rev l1 P)).
    intros H; rewrite H in *. lia.
    intros n' H; rewrite H in *. 
    case_eq (length l1 - n').
    ++ intros H2; rewrite H2 in *. 
       rewrite indicies_l_rev_app in Hleb1.
       rewrite app_length in Hleb1.
       rewrite map_length in Hleb1.
       rewrite H in Hleb1.
       simpl in Hleb1.
       assert (n' = S n' - 1) as Hn. lia.
       rewrite Hn in H2.
       rewrite <- H in H2.
       pose proof (le_indicies_l_rev l1 P).
       rewrite H in *.  lia.
    ++ intros m H2; rewrite H2 in *; discriminate.
Qed.

Lemma identify_rev_l_app_r : forall (l1 l2 : list predicate) (P : predicate)
                                   (i : nat),
  ~ i = 0 ->
  i <= (length l1 + length l2 - (length 
                            (indicies_l_rev (app l1 l2) P))) ->
  i > ((length l1) - (length (indicies_l_rev l1 P))) ->
             identify_rev_l (app l1 l2) P i = 
                 (identify_rev_l l2 P (i - ((length l1) - 
                                      (length (indicies_l_rev l1 P))))) +
                  (length l1).
Proof.
  induction l1; intros l2 P i Hbeq Hleb1 Hleb2.
    simpl in *. rewrite Nat.sub_0_r. lia.
  destruct i. contradiction. simpl in *.
  destruct i. simpl in *.
  destruct (predicate_dec P a). rewrite predicate_dec_l in *; auto.
  + subst. simpl in *. rewrite IHl1; simpl; auto; lia. 
  + rewrite predicate_dec_r in *; auto.
    rewrite identify_rev_l_0. apply Gt.gt_le_S in Hleb2.
    apply Le.le_S_n in Hleb2.
    case_eq (length (indicies_l_rev l1 P)). intros Hnil; rewrite Hnil in *.
    inversion Hleb2.
    intros m Hm. rewrite Hm in *. apply Nat.le_0_r in Hleb2.
    rewrite Hleb2. pose proof (le_indicies_l_rev l1 P) as H2. lia.
  + destruct (predicate_dec P a). rewrite predicate_dec_l in *; auto.
    simpl in *. case_eq (length l1 - length (indicies_l_rev l1 P)).
      rewrite IHl1; auto. intros Hnil. rewrite Hnil in *. firstorder.
    intros m Hm. rewrite Hm in *. destruct m. rewrite IHl1; auto.
    rewrite Hm. firstorder. lia.
    rewrite IHl1; auto. rewrite Hm. firstorder.  lia.

    rewrite predicate_dec_r in *. case_eq (length (indicies_l_rev l1 P)).
    intros Hnil. rewrite Hnil in *. rewrite IHl1; auto. rewrite Hnil.
    simpl. destruct (length l1); firstorder. 
    destruct (length (indicies_l_rev (l1 ++ l2) P)); lia.  lia.

      intros m Hm. rewrite Hm in *.
      case_eq (length l1 -m). intros Hnil. rewrite Hnil in *.
      pose proof (le_indicies_l_rev l1 P) as H. lia.

      intros s Hs. rewrite Hs in *. simpl. destruct s.
      rewrite IHl1; auto. rewrite Hm. 
      case_eq (length l1 - S m). firstorder. intros. lia.

      destruct (length (indicies_l_rev (l1 ++ l2) P)); lia.
      lia. rewrite IHl1; auto. rewrite Hm.
      apply Nat.add_sub_eq_nz in Hs. rewrite <- Hs.
      simpl. rewrite Nat.add_succ_r. simpl.
      rewrite Minus.minus_plus. lia. auto.
      destruct ( length (indicies_l_rev (l1 ++ l2) P)); lia.
      lia.
      all : auto.
Qed.

(* --------------------------------------------------------------------- *)

Definition identify_rev (alpha : SecOrder) (P : predicate) (i : nat) : nat :=
  identify_rev_l (preds_in alpha) P i.

Lemma identify_rev_allFO : forall (alpha : SecOrder) (x : FOvariable) (P : predicate) (i : nat),
  identify_rev (allFO x alpha) P i = identify_rev alpha P i.
Proof. auto. Qed.

Lemma identify_rev_exFO : forall (alpha : SecOrder) (x : FOvariable) (P : predicate) (i : nat),
  identify_rev (exFO x alpha) P i = identify_rev alpha P i.
Proof. auto. Qed.

Lemma identify_rev_negSO : forall (alpha : SecOrder) (P : predicate) (i : nat),
  identify_rev (negSO alpha) P i = identify_rev alpha P i.
Proof. auto. Qed.

Lemma identify_rev_predSO : forall (P Q : predicate) (x : FOvariable) (i : nat),
  i <> 0 ->  identify_rev (predSO P x) Q i = 1.
Proof.
  intros P Q x i Hbeq. unfold identify_rev.
  simpl. destruct i.  contradiction. 
  destruct i; if_then_else_dest_blind; auto.
Qed.

(* --------------------------------------------------------- *)


Lemma identify_rev_l_app2 : forall (l1 l2 : list predicate)
                                    (P : predicate) (i : nat),
  i <= ((length l1)- (num_occ_l l1 P)) ->
    identify_rev_l (app l1 l2) P i = identify_rev_l l1 P i.
Proof.
  induction l1; intros l2 P i H; simpl in *.
  + destruct i; firstorder. apply identify_rev_l_0.
  + destruct i. auto.
    destruct (predicate_dec P a). subst. auto.
    rewrite IHl1; auto.
    destruct (num_occ_l l1 P); lia.
Qed.

(* ----------------------------------------------------------------------------- *)

Lemma le_id_fwd_allSO : forall (alpha : SecOrder) (P Q : predicate) (i : nat),
  (forall (i : nat),occ_in_SO alpha i  ->
        (identify_fwd alpha P i) <= (length (preds_in alpha) - num_occ alpha P)) ->
    occ_in_SO (allSO Q alpha) i ->
        (identify_fwd (allSO Q alpha) P i) <= (length (preds_in (allSO Q alpha)) 
              - num_occ (allSO Q alpha) P).
Proof. 
  intros alpha P Q i IHalpha H. simpl.
  rewrite num_occ_allSO.  rewrite occ_in_SO_dec_l; auto.
  destruct i. rewrite identify_fwd_0. inversion H. lia.
  destruct i. simpl. rewrite identify_fwd_0. 
    dest_pred_dec P Q. lia.
    simpl. case_eq (num_occ alpha P). intros H2.
    lia. intros m H2.
    pose proof (num_occ_preds_in alpha P) as H3. lia.
    dest_pred_dec P Q.
    simpl. apply IHalpha. inversion H. constructor. lia. 
    simpl in *. lia.

  case_eq (num_occ alpha P). intros Hnum. rewrite Hnum in *. simpl.
  assert ((identify_fwd alpha P ( S i) + 1) = (S (identify_fwd alpha P (S i)))) as H2.
    lia.  simpl.

  rewrite H2. apply Le.le_n_S. apply occ_in_SO_allSO_rev in H. apply IHalpha in H.
  firstorder.
  intros m Hm. rewrite Hm in *.
  simpl in *. apply occ_in_SO_allSO_rev in H.
  pose proof H as H'. apply IHalpha in H.
  apply Le.le_n_S in H. 
    pose proof (num_occ_preds_in alpha P) as H2. lia.
Qed.

Lemma le_id_fwd_exSO : forall (alpha : SecOrder) (P Q : predicate) (i : nat),
  (forall (i : nat),occ_in_SO alpha i  ->
        (identify_fwd alpha P i) <= (length (preds_in alpha) - num_occ alpha P)) ->
    occ_in_SO (exSO Q alpha) i ->
        (identify_fwd (exSO Q alpha) P i) <= (length (preds_in (exSO Q alpha)) 
              - num_occ (exSO Q alpha) P).
Proof. 
  intros alpha P Q i IHalpha H. simpl.
  rewrite num_occ_exSO.  rewrite occ_in_SO_dec_l; auto.
  destruct i. rewrite identify_fwd_0. firstorder. simpl. 
  destruct i. simpl. rewrite identify_fwd_0. 
    dest_pred_dec P Q. lia.
    simpl. case_eq (num_occ alpha P). intros H2.
    lia. intros m H2.
    pose proof (num_occ_preds_in alpha P) as H3. lia.
    dest_pred_dec P Q.
    simpl. apply IHalpha. firstorder. 
  case_eq (num_occ alpha P). intros Hnum. rewrite Hnum in *.
  assert ((identify_fwd alpha P ( S i - 0) + 1) = (S (identify_fwd alpha P (S i)))) as H2.
    rewrite Nat.sub_0_r. firstorder. 
  rewrite H2. apply Le.le_n_S. apply occ_in_SO_exSO_rev in H. apply IHalpha in H.
  lia.

  intros m Hm. rewrite Hm in *.
  simpl in *. apply occ_in_SO_exSO_rev in H.
  pose proof H as H'. apply IHalpha in H.
  apply Le.le_n_S in H. 
    pose proof (num_occ_preds_in alpha P) as H2. lia.
Qed.

(* ------------------------------------------ *)

Lemma le_id_fwd : forall (alpha : SecOrder) (P : predicate) (i : nat),
  occ_in_SO alpha i ->
    (identify_fwd alpha P i) <= (length (preds_in alpha) - (num_occ alpha P)).
Proof.
  induction alpha; intros P i Hocc;
    try solve [  simpl; rewrite occ_in_SO_dec_l; [| auto];
  firstorder].

  simpl. rewrite occ_in_SO_dec_l. 2 : auto.
  apply occ_in_SO_predSO in Hocc. subst.
  rewrite num_occ_predSO. dest_pred_dec P p.

  simpl. rewrite occ_in_SO_dec_l; auto.
  apply occ_in_SO_conjSO2_fwd2 in Hocc. destruct Hocc as [H | [H1 H2]].
    rewrite occ_in_SO_dec_l; auto.
  rewrite app_length. rewrite num_occ_conjSO.
  apply IHalpha1 with (P := P) in H.
  pose proof (num_occ_preds_in alpha2 P) as H2. lia.

  rewrite occ_in_SO_dec_r; auto.
  rewrite app_length. rewrite num_occ_conjSO.
  apply IHalpha2 with (P := P) in H2.
  pose proof (num_occ_preds_in alpha1 P) as H3.
  pose proof (num_occ_preds_in alpha2 P) as H4.
  apply Le.le_trans with (m := (length (preds_in alpha2) - num_occ alpha2 P) +
                               (length (preds_in alpha1) - num_occ alpha1 P)).
  clear - H2 H3 H4. lia.
  clear - H2 H3 H4. lia.

  simpl. rewrite occ_in_SO_dec_l; auto.
  apply occ_in_SO_disjSO2_fwd2 in Hocc. destruct Hocc as [H | [H1 H2]].
    rewrite occ_in_SO_dec_l; auto.
  rewrite app_length. rewrite num_occ_disjSO.
  apply IHalpha1 with (P := P) in H.
  pose proof (num_occ_preds_in alpha2 P) as H2. lia.

  rewrite occ_in_SO_dec_r; auto.
  rewrite app_length. rewrite num_occ_disjSO.
  apply IHalpha2 with (P := P) in H2.
  pose proof (num_occ_preds_in alpha1 P) as H3.
  pose proof (num_occ_preds_in alpha2 P) as H4.
  apply Le.le_trans with (m := (length (preds_in alpha2) - num_occ alpha2 P) +
                               (length (preds_in alpha1) - num_occ alpha1 P)).
  clear - H2 H3 H4. lia.
  clear - H2 H3 H4. lia.

  simpl. rewrite occ_in_SO_dec_l; auto.
  apply occ_in_SO_implSO2_fwd2 in Hocc. destruct Hocc as [H | [H1 H2]].
    rewrite occ_in_SO_dec_l; auto.
  rewrite app_length. rewrite num_occ_implSO.
  apply IHalpha1 with (P := P) in H.
  pose proof (num_occ_preds_in alpha2 P) as H2. lia.

  rewrite occ_in_SO_dec_r; auto.
  rewrite app_length. rewrite num_occ_implSO.
  apply IHalpha2 with (P := P) in H2.
  pose proof (num_occ_preds_in alpha1 P) as H3.
  pose proof (num_occ_preds_in alpha2 P) as H4.
  apply Le.le_trans with (m := (length (preds_in alpha2) - num_occ alpha2 P) +
                               (length (preds_in alpha1) - num_occ alpha1 P)).
  clear - H2 H3 H4. lia.
  clear - H2 H3 H4. lia.

  apply le_id_fwd_allSO; auto.
  apply le_id_fwd_exSO; auto.
Qed.

Lemma identify_fwd_rev_predSO : forall (P Q : predicate) (x : FOvariable) (i : nat),
  ~((identify_fwd (predSO Q x) P i) = 0) ->
    occ_in_SO (predSO Q x) i ->
      identify_rev (predSO Q x) P (identify_fwd (predSO Q x) P i) =  i.
Proof.
  intros P Q x i Hid Hocc; simpl in *.
  rewrite occ_in_SO_dec_l in *; auto.
  unfold identify_rev;  simpl in *.
  destruct (predicate_dec P Q).  contradiction.
  apply occ_in_SO_predSO in Hocc. subst. auto.
Qed.

Lemma id_fwd_beq_nat_conjSO : forall (alpha1 alpha2 : SecOrder) (n : nat) (P : predicate),
  (forall (n : nat) (P : predicate),
           occ_in_SO alpha1 n  ->
           ~ P = at_pred (preds_in alpha1) n ->
      ~ (identify_fwd alpha1 P n) = 0) ->
  (forall (n : nat) (P : predicate),
           occ_in_SO alpha2 n ->
          ~  P =  at_pred (preds_in alpha2) n  ->
          ~ (identify_fwd alpha2 P n) = 0) ->
    occ_in_SO (conjSO alpha1 alpha2) n ->
    ~ P = at_pred (preds_in (conjSO alpha1 alpha2)) n ->
    ~ (identify_fwd (conjSO alpha1 alpha2) P n) = 0.
Proof.
  intros alpha1 alpha2 n P IHalpha1 IHalpha2 Hocc Hbeq; simpl in *.
    rewrite occ_in_SO_dec_l; auto.
    pose proof (occ_in_SO_conjSO2_fwd2 _ _ _ Hocc) as H.
    destruct H.
      rewrite occ_in_SO_dec_l; auto.
      rewrite at_pred_occ_l in Hbeq; try assumption.
      apply IHalpha1; assumption. 

      destruct H as [H1 H2].
      rewrite at_pred_occ_r in Hbeq; try assumption.
      rewrite occ_in_SO_dec_r; auto.

      eapply IHalpha2 with (P := P) in H2. pose proof (num_occ_preds_in alpha1 P) as H.
      clear -H2 H. lia. auto.
Qed.

Lemma id_fwd_beq_nat_disjSO : forall (alpha1 alpha2 : SecOrder) (n : nat) (P : predicate),
  (forall (n : nat) (P : predicate),
           occ_in_SO alpha1 n  ->
           ~ P = at_pred (preds_in alpha1) n ->
      ~ (identify_fwd alpha1 P n) = 0) ->
  (forall (n : nat) (P : predicate),
           occ_in_SO alpha2 n ->
          ~  P =  at_pred (preds_in alpha2) n  ->
          ~ (identify_fwd alpha2 P n) = 0) ->
    occ_in_SO (disjSO alpha1 alpha2) n ->
    ~ P = at_pred (preds_in (disjSO alpha1 alpha2)) n ->
    ~ (identify_fwd (disjSO alpha1 alpha2) P n) = 0.
Proof.
  intros alpha1 alpha2 n P IHalpha1 IHalpha2 Hocc Hbeq; simpl in *.
    rewrite occ_in_SO_dec_l. 2 : auto.
    pose proof (occ_in_SO_disjSO2_fwd2 _ _ _ Hocc) as H.
    destruct H.
      rewrite occ_in_SO_dec_l; auto.
      rewrite at_pred_occ_l in Hbeq; try assumption.
      apply IHalpha1; assumption. 

      destruct H as [H1 H2].
      rewrite at_pred_occ_r in Hbeq; try assumption.
      rewrite occ_in_SO_dec_r; auto.

      eapply IHalpha2 with (P := P) in H2. pose proof (num_occ_preds_in alpha1 P) as H.
      clear -H2 H. lia. auto.
Qed.

Lemma id_fwd_beq_nat_implSO : forall (alpha1 alpha2 : SecOrder) (n : nat) (P : predicate),
  (forall (n : nat) (P : predicate),
           occ_in_SO alpha1 n  ->
           ~ P = at_pred (preds_in alpha1) n ->
      ~ (identify_fwd alpha1 P n) = 0) ->
  (forall (n : nat) (P : predicate),
           occ_in_SO alpha2 n ->
          ~  P =  at_pred (preds_in alpha2) n  ->
          ~ (identify_fwd alpha2 P n) = 0) ->
    occ_in_SO (implSO alpha1 alpha2) n ->
    ~ P = at_pred (preds_in (implSO alpha1 alpha2)) n ->
    ~ (identify_fwd (implSO alpha1 alpha2) P n) = 0.
Proof.
  intros alpha1 alpha2 n P IHalpha1 IHalpha2 Hocc Hbeq; simpl in *.
    rewrite occ_in_SO_dec_l. 2 : auto.
    pose proof (occ_in_SO_implSO2_fwd2 _ _ _ Hocc) as H.
    destruct H.
      rewrite occ_in_SO_dec_l; auto.
      rewrite at_pred_occ_l in Hbeq; try assumption.
      apply IHalpha1; assumption. 

      destruct H as [H1 H2].
      rewrite at_pred_occ_r in Hbeq; try assumption.
      rewrite occ_in_SO_dec_r; auto.

      eapply IHalpha2 with (P := P) in H2. pose proof (num_occ_preds_in alpha1 P) as H.
      clear -H2 H. lia. auto.
Qed.

Lemma id_fwd_beq_nat_allSO : forall (alpha : SecOrder) (n : nat) (P Q : predicate),
  (forall (n : nat) (P : predicate),
     occ_in_SO alpha n -> ~ P = at_pred (preds_in alpha) n ->
  ~(identify_fwd alpha P n) = 0)  ->
    occ_in_SO (allSO Q alpha) n ->
       ~P = at_pred (preds_in (allSO Q alpha)) n ->
       ~ identify_fwd (allSO Q alpha) P n = 0.
Proof.
  intros alpha n P Q IHalpha Hocc Hbeq. simpl in *.
  rewrite occ_in_SO_dec_l; auto.
  case_eq n.
    intros Hn; rewrite Hn in *.
    contradiction (occ_in_SO_0 _ Hocc).

    intros m Hn; rewrite Hn in *.
    destruct m. simpl in *.
    rewrite predicate_dec_r. lia. auto.

    apply occ_in_SO_allSO_rev in Hocc.
    simpl in Hbeq. destruct (predicate_dec P Q).
    simpl. apply IHalpha; auto.
    simpl. lia.
Qed.

Lemma id_fwd_beq_nat_exSO : forall (alpha : SecOrder) (n : nat) (P Q : predicate),
  (forall (n : nat) (P : predicate),
     occ_in_SO alpha n -> ~ P = at_pred (preds_in alpha) n ->
  ~(identify_fwd alpha P n) = 0)  ->
    occ_in_SO (exSO Q alpha) n ->
       ~P = at_pred (preds_in (exSO Q alpha)) n ->
       ~ identify_fwd (exSO Q alpha) P n = 0.
Proof.
  intros alpha n P Q IHalpha Hocc Hbeq. simpl in *.
  rewrite occ_in_SO_dec_l; auto.
  case_eq n.
    intros Hn; rewrite Hn in *.
    contradiction (occ_in_SO_0 _ Hocc).

    intros m Hn; rewrite Hn in *.
    destruct m. simpl in *.
    rewrite predicate_dec_r. lia. auto.

    apply occ_in_SO_exSO_rev in Hocc.
    simpl in Hbeq. destruct (predicate_dec P Q).
    simpl. apply IHalpha; auto.
    simpl. lia.
Qed.

Lemma id_fwd_beq_nat : forall (alpha : SecOrder) (n : nat) (P : predicate),
  occ_in_SO alpha n ->
  ~ at_pred (preds_in alpha) n = P ->
  ~ (identify_fwd alpha P n) = 0.
Proof.
  induction alpha;
    intros n P Hocc Hbeq;
    try (apply id_fwd_beq_nat_conjSO; auto);
    try (apply id_fwd_beq_nat_allSO; auto).

    simpl in *. rewrite occ_in_SO_dec_l.
    case_eq n.
      intros Hn; rewrite Hn in *.
      apply occ_in_SO_predSO in Hocc.
      discriminate.

      intros m Hn; rewrite Hn in *.
      case_eq m.
      intros Hm; rewrite Hm in *. subst.
      rewrite predicate_dec_r. lia. auto. 

        intros j Hm; rewrite Hm in *.
        apply occ_in_SO_predSO in Hocc.
        simpl in *; discriminate.
        auto.

    contradiction (occ_in_SO_relatSO _ _ _ Hocc).
    contradiction (occ_in_SO_eqFO _ _ _ Hocc).

    simpl in *. rewrite occ_in_SO_dec_l; auto.
    simpl in *. rewrite occ_in_SO_dec_l; auto.
    simpl in *. rewrite occ_in_SO_dec_l; auto.
    apply id_fwd_beq_nat_disjSO; auto.
    apply id_fwd_beq_nat_implSO; auto.
    apply id_fwd_beq_nat_exSO; auto.
Qed.

Lemma id_fwd_not_conjSO  : forall (alpha1 alpha2 : SecOrder) (n : nat) (P : predicate),
  (forall (n : nat) (P : predicate),
   ~ P = at_pred (preds_in alpha1) n ->
      ~ n = 0 ->  occ_in_SO alpha1 n ->
          identify_fwd alpha1 P n <> 0) ->
    (forall (n : nat) (P : predicate),
      ~P = at_pred (preds_in alpha2) n ->
       ~ n = 0 ->  occ_in_SO alpha2 n ->
            identify_fwd alpha2 P n <> 0) ->
    ~ P = at_pred (preds_in (conjSO alpha1 alpha2)) n ->
      ~ n = 0 ->
        occ_in_SO (conjSO alpha1 alpha2) n ->
          identify_fwd (conjSO alpha1 alpha2) P n <> 0.
Proof.
  intros alpha1 alpha2 n P IHalpha1 IHalpha2 Hbeq1 Hbeq2 Hocc.
  simpl. rewrite occ_in_SO_dec_l; auto.
  destruct (occ_in_SO_dec alpha1 n). apply IHalpha1; auto.
  simpl in Hbeq1. rewrite at_pred_app_l in Hbeq1. auto.
  firstorder. rewrite <- Nat.add_sub_assoc.
    destruct ( length (preds_in alpha1) - num_occ alpha1 P). 
    rewrite Nat.add_0_r. apply IHalpha2.
    simpl in Hbeq1. 
    assert (n =  (length (preds_in alpha1) + (n - length (preds_in alpha1)))) as Hass.
      firstorder.
    rewrite Hass in Hbeq1. rewrite at_pred_app_r in Hbeq1.
    auto. firstorder. firstorder. 
    apply occ_in_SO_conjSO2 in Hocc. firstorder.
    lia. apply num_occ_preds_in.
Qed.

Lemma id_fwd_not_disjSO  : forall (alpha1 alpha2 : SecOrder) (n : nat) (P : predicate),
  (forall (n : nat) (P : predicate),
    ~ P = at_pred (preds_in alpha1) n ->
    ~ n = 0 ->  occ_in_SO alpha1 n ->
          identify_fwd alpha1 P n <> 0) ->
    (forall (n : nat) (P : predicate),
     ~ P = at_pred (preds_in alpha2) n ->
     ~ n = 0 ->  occ_in_SO alpha2 n ->
            identify_fwd alpha2 P n <> 0) ->
    ~ P = at_pred (preds_in (disjSO alpha1 alpha2)) n ->
    ~ n = 0 ->  occ_in_SO (disjSO alpha1 alpha2) n ->
          identify_fwd (disjSO alpha1 alpha2) P n <> 0.
Proof.
  intros alpha1 alpha2 n P IHalpha1 IHalpha2 Hbeq1 Hbeq2 Hocc.
  simpl. rewrite occ_in_SO_dec_l; auto.
  destruct (occ_in_SO_dec alpha1 n). apply IHalpha1; auto.
  simpl in Hbeq1. rewrite at_pred_app_l in Hbeq1. auto.
  firstorder. rewrite <- Nat.add_sub_assoc.
    destruct ( length (preds_in alpha1) - num_occ alpha1 P). 
    rewrite Nat.add_0_r. apply IHalpha2.
    simpl in Hbeq1. 
    assert (n =  (length (preds_in alpha1) + (n - length (preds_in alpha1)))) as Hass.
      firstorder.
    rewrite Hass in Hbeq1. rewrite at_pred_app_r in Hbeq1.
    auto. firstorder. firstorder. 
    apply occ_in_SO_disjSO2 in Hocc. firstorder.
    lia. apply num_occ_preds_in.
Qed.

Lemma id_fwd_not_implSO  : forall (alpha1 alpha2 : SecOrder) (n : nat) (P : predicate),
  (forall (n : nat) (P : predicate),
    ~ P = at_pred (preds_in alpha1) n ->
    ~ n = 0 ->  occ_in_SO alpha1 n ->
          identify_fwd alpha1 P n <> 0) ->
    (forall (n : nat) (P : predicate),
     ~ P = at_pred (preds_in alpha2) n ->
     ~ n = 0 ->  occ_in_SO alpha2 n ->
            identify_fwd alpha2 P n <> 0) ->
    ~ P = at_pred (preds_in (implSO alpha1 alpha2)) n ->
    ~ n = 0 ->  occ_in_SO (implSO alpha1 alpha2) n ->
          identify_fwd (implSO alpha1 alpha2) P n <> 0.
Proof.
  intros alpha1 alpha2 n P IHalpha1 IHalpha2 Hbeq1 Hbeq2 Hocc.
  simpl. rewrite occ_in_SO_dec_l; auto.
  destruct (occ_in_SO_dec alpha1 n). apply IHalpha1; auto.
  simpl in Hbeq1. rewrite at_pred_app_l in Hbeq1. auto.
  firstorder. rewrite <- Nat.add_sub_assoc.
    destruct ( length (preds_in alpha1) - num_occ alpha1 P). 
    rewrite Nat.add_0_r. apply IHalpha2.
    simpl in Hbeq1. 
    assert (n =  (length (preds_in alpha1) + (n - length (preds_in alpha1)))) as Hass.
      firstorder.
    rewrite Hass in Hbeq1. rewrite at_pred_app_r in Hbeq1.
    auto. firstorder. firstorder. 
    apply occ_in_SO_implSO2 in Hocc. firstorder.
    lia. apply num_occ_preds_in.
Qed.

Lemma id_fwd_not_allSO  : forall (alpha : SecOrder) (n : nat) (P Q : predicate),
  (forall (n : nat) (P : predicate),
    ~ P = at_pred (preds_in alpha) n ->
    ~ n = 0 ->  occ_in_SO alpha n ->
          identify_fwd alpha P n <> 0) ->
    ~ P = at_pred (preds_in (allSO Q alpha)) n ->
    ~ n = 0 ->  occ_in_SO (allSO Q alpha) n ->
          identify_fwd (allSO Q alpha) P n <> 0.
Proof.
  intros alpha n P Q IHalpha Hbeq1 Hbeq2 Hocc.
  simpl in *. destruct n. contradiction (occ_in_SO_0 _ Hocc).
  rewrite occ_in_SO_dec_l; auto.
  destruct n. rewrite predicate_dec_r; auto. lia.
  simpl in Hbeq1. apply occ_in_SO_allSO_rev in Hocc.
  destruct (predicate_dec P Q). simpl. apply IHalpha; auto.
  lia.
Qed.

Lemma id_fwd_not_exSO  : forall (alpha : SecOrder) (n : nat) (P Q : predicate),
  (forall (n : nat) (P : predicate),
    ~ P = at_pred (preds_in alpha) n ->
    ~ n = 0 ->  occ_in_SO alpha n ->
          identify_fwd alpha P n <> 0) ->
    ~ P = at_pred (preds_in (exSO Q alpha)) n ->
    ~ n = 0 ->  occ_in_SO (exSO Q alpha) n ->
          identify_fwd (exSO Q alpha) P n <> 0.
Proof.
  intros alpha n P Q IHalpha Hbeq1 Hbeq2 Hocc.
  simpl in *. destruct n. contradiction (occ_in_SO_0 _ Hocc).
  rewrite occ_in_SO_dec_l; auto.
  destruct n. rewrite predicate_dec_r; auto. lia.
  simpl in Hbeq1. apply occ_in_SO_exSO_rev in Hocc.
  destruct (predicate_dec P Q). simpl. apply IHalpha; auto.
  lia.
Qed.

Lemma id_fwd_not  : forall (alpha : SecOrder) (n : nat) (P : predicate),
  ~ P = at_pred (preds_in alpha) n -> ~ n = 0 ->
      occ_in_SO alpha n ->
        identify_fwd alpha P n <> 0.
Proof.
  induction alpha;  intros n P Hbeq1 Hbeq2 Hocc;
    try (  simpl in *; rewrite occ_in_SO_dec_l; auto;
  apply IHalpha; firstorder).

  simpl in *. rewrite occ_in_SO_dec_l; auto.
  simpl in *. apply occ_in_SO_predSO in Hocc.
  subst. rewrite predicate_dec_r; auto.

  contradiction (occ_in_SO_relatSO _ _ _ Hocc).
  contradiction (occ_in_SO_eqFO _ _ _ Hocc).

  apply id_fwd_not_conjSO; auto.
  apply id_fwd_not_disjSO; auto.
  apply id_fwd_not_implSO; auto.
  apply id_fwd_not_allSO; auto.
  apply id_fwd_not_exSO; auto.
Qed.

Lemma ind_l_rev_app_length : forall (l1 l2 : list _) (P : predicate),
  length (indicies_l_rev (app l1 l2) P) =
    (length (indicies_l_rev l1 P)) +
      length (indicies_l_rev l2 P).
Proof.
  intros.
  rewrite indicies_l_rev_app.
  rewrite app_length.
  rewrite map_length.
  reflexivity.
Qed.

Lemma identify_fwd_rev_conjSO: forall (alpha1 alpha2 : SecOrder) (P : predicate) (i : nat),
  (forall (P : predicate) (i : nat),
     identify_fwd alpha1 P i <> 0 ->
       occ_in_SO alpha1 i ->
     ~  P = at_pred (preds_in alpha1) i ->
           identify_rev alpha1 P (identify_fwd alpha1 P i) = i) ->
   (forall (P : predicate) (i : nat),
     identify_fwd alpha2 P i <> 0 ->
       occ_in_SO alpha2 i ->
     ~  P = at_pred (preds_in alpha2) i ->
    identify_rev alpha2 P (identify_fwd alpha2 P i) = i) ->
      identify_fwd (conjSO alpha1 alpha2) P i <> 0 ->
        occ_in_SO (conjSO alpha1 alpha2) i ->
     ~  P = at_pred (preds_in (conjSO alpha1 alpha2)) i ->
       identify_rev (conjSO alpha1 alpha2) P
         (identify_fwd (conjSO alpha1 alpha2) P i) = i.
Proof.
  intros alpha1 alpha2 P i IHalpha1 IHalpha2 Hid Hocc Hbeq.
  pose proof (occ_in_SO_conjSO2_fwd2 _ _ _ Hocc) as H.
  destruct H as [Hocc2 | Hocc2].
    unfold identify_rev.
    simpl in Hid; simpl. occ_in_SO_fill.
    rewrite identify_rev_l_app_l; auto.
      apply IHalpha1; auto. simpl in Hbeq.
      rewrite at_pred_app_l in Hbeq; auto.
      inversion Hocc2. auto.

      rewrite ind_l_rev_app_length.
      do 2 rewrite <- num_occ_ind_l_rev.
      pose proof (le_id_fwd alpha1 P i Hocc2).
      pose proof (num_occ_preds_in alpha2 P) as H2.
      apply (Le.le_trans _ _ _ H).  clear -H2 H.  lia.
      rewrite <- num_occ_ind_l_rev.
      apply le_id_fwd; auto.  all : auto.

      assert (at_pred (preds_in alpha2) (i - length (preds_in alpha1)) <> P) as Hbeq2.
        assert (i = length (preds_in alpha1) + (i - length (preds_in alpha1))) as Hass.
            clear -Hocc2. destruct Hocc2 as [Hocc2a Hocc2b]. 
            pose proof (occ_in_SO_f alpha1 i Hocc2a).
            pose proof (occ_in_SO_0 alpha2). firstorder. 
            
        rewrite Hass in Hbeq. simpl in Hbeq. rewrite at_pred_app_r in Hbeq; auto.
         destruct Hocc2 as [Hocc2a Hocc2b]. 
            pose proof (occ_in_SO_f alpha1 i Hocc2a).
            pose proof (occ_in_SO_0 alpha2). firstorder.
      simpl. simpl in Hid. destruct Hocc2 as [H2 H3].  occ_in_SO_fill. 
      unfold identify_rev. simpl.
      rewrite identify_rev_l_app_r.
      rewrite <- Nat.add_sub_assoc in Hid.
      case_eq (length (preds_in alpha1) -
        num_occ alpha1 P). intros Hnil. rewrite Hnil in *.
        rewrite Nat.add_0_r in *.
        apply IHalpha2 in Hid. unfold identify_rev in Hid.
        rewrite <- num_occ_ind_l_rev.
        case_eq (i - length (preds_in alpha1)). intros Hnil2.
        rewrite Hnil2 in *.  contradiction (occ_in_SO_0 _ H3).
        intros m Hm. rewrite Hm in *. 
        apply Nat.add_sub_eq_nz in Hm. subst.
        rewrite Hnil. rewrite Nat.sub_0_r.
        rewrite <- Nat.add_sub_assoc. rewrite Hnil.
        rewrite Nat.add_0_r. clear -Hid. lia.

        apply num_occ_preds_in.
        all : auto.

        intros m Hm. case_eq (identify_fwd alpha2 P  (i - length (preds_in alpha1))).
        intros Hnil.  rewrite Hnil in *. simpl in *.
        apply id_fwd_beq_nat in Hnil; auto. contradiction.

        intros s Hs. rewrite <- Hs. rewrite <- num_occ_ind_l_rev.
        assert ( (identify_fwd alpha2 P (i - length (preds_in alpha1)) + length (preds_in alpha1) -
                 num_occ alpha1 P - (length (preds_in alpha1) - num_occ alpha1 P)) =
                 identify_fwd alpha2 P (i - length (preds_in alpha1))) as Hass2. 
        clear -Hid Hs.
        pose proof (num_occ_preds_in alpha1 P).
        pose proof (num_occ_preds_in alpha2 P).  lia.
        rewrite Hass2 in *. specialize (IHalpha2 P (i - length (preds_in alpha1))).
        clear IHalpha1 Hid Hocc Hbeq H2 Hass2. rewrite Hs in *. apply IHalpha2 in H3; auto.
        unfold identify_rev in H3. clear - Hs H3.
        case_eq (i - length (preds_in alpha1)). intros Hnil.
          rewrite Hnil in *. rewrite identify_fwd_0 in Hs. discriminate.
        intros m Hm. lia.

      apply num_occ_preds_in. rewrite indicies_l_rev_app.
      rewrite app_length. rewrite map_length.
      unfold identify_rev in *. do 2 rewrite <- num_occ_ind_l_rev.

      pose proof (num_occ_preds_in alpha1 P) as H4.
      pose proof (num_occ_preds_in alpha2 P) as H5.
      pose proof (le_id_fwd alpha2 P (i - length (preds_in alpha1)) H3).
      clear -H4 H5 H. lia.

      unfold gt. unfold lt. rewrite <- num_occ_ind_l_rev.
      pose proof (num_occ_preds_in alpha1 P).
      case_eq (identify_fwd alpha2 P (i - length (preds_in alpha1))).
        intros Hnil. rewrite Hnil in *.
        apply id_fwd_beq_nat in Hnil. contradiction.
        auto. firstorder.

        intros m Hm.  lia. 
Qed.

Lemma identify_fwd_rev_disjSO: forall (alpha1 alpha2 : SecOrder) (P : predicate) (i : nat),
  (forall (P : predicate) (i : nat),
     identify_fwd alpha1 P i <> 0 ->
       occ_in_SO alpha1 i ->
     ~  P = at_pred (preds_in alpha1) i ->
           identify_rev alpha1 P (identify_fwd alpha1 P i) = i) ->
   (forall (P : predicate) (i : nat),
     identify_fwd alpha2 P i <> 0 ->
       occ_in_SO alpha2 i ->
     ~  P = at_pred (preds_in alpha2) i ->
    identify_rev alpha2 P (identify_fwd alpha2 P i) = i) ->
      identify_fwd (disjSO alpha1 alpha2) P i <> 0 ->
        occ_in_SO (disjSO alpha1 alpha2) i ->
     ~  P = at_pred (preds_in (disjSO alpha1 alpha2)) i ->
       identify_rev (disjSO alpha1 alpha2) P
         (identify_fwd (disjSO alpha1 alpha2) P i) = i.
Proof.
  intros alpha1 alpha2 P i IHalpha1 IHalpha2 Hid Hocc Hbeq.
  pose proof (occ_in_SO_disjSO2_fwd2 _ _ _ Hocc) as H.
  destruct H as [Hocc2 | Hocc2].
    unfold identify_rev.
    simpl in Hid; simpl. occ_in_SO_fill.
    rewrite identify_rev_l_app_l; auto.
      apply IHalpha1; auto. simpl in Hbeq.
      rewrite at_pred_app_l in Hbeq; auto.
      firstorder.

      rewrite ind_l_rev_app_length.
      do 2 rewrite <- num_occ_ind_l_rev.
      pose proof (le_id_fwd alpha1 P i Hocc2).
      pose proof (num_occ_preds_in alpha2 P) as H2.
      apply (Le.le_trans _ _ _ H).  clear -H2 H.  lia.
      rewrite <- num_occ_ind_l_rev.
      apply le_id_fwd; auto.  all : auto.

      assert (at_pred (preds_in alpha2) (i - length (preds_in alpha1)) <> P) as Hbeq2.
        assert (i = length (preds_in alpha1) + (i - length (preds_in alpha1))) as Hass.
            clear -Hocc2. firstorder.
        rewrite Hass in Hbeq. simpl in Hbeq. rewrite at_pred_app_r in Hbeq; auto.
        firstorder.
      simpl. simpl in Hid. destruct Hocc2 as [H2 H3].  occ_in_SO_fill. 
      unfold identify_rev. simpl.
      rewrite identify_rev_l_app_r.
      rewrite <- Nat.add_sub_assoc in Hid.
      case_eq (length (preds_in alpha1) -
        num_occ alpha1 P). intros Hnil. rewrite Hnil in *.
        rewrite Nat.add_0_r in *.
        apply IHalpha2 in Hid. unfold identify_rev in Hid.
        rewrite <- num_occ_ind_l_rev.
        case_eq (i - length (preds_in alpha1)). intros Hnil2.
        rewrite Hnil2 in *.  contradiction (occ_in_SO_0 _ H3).
        intros m Hm. rewrite Hm in *. 
        apply Nat.add_sub_eq_nz in Hm. subst.
        rewrite Hnil. rewrite Nat.sub_0_r.
        rewrite <- Nat.add_sub_assoc. rewrite Hnil.
        rewrite Nat.add_0_r. clear -Hid. lia.

        apply num_occ_preds_in.
        all : auto.

        intros m Hm. case_eq (identify_fwd alpha2 P  (i - length (preds_in alpha1))).
        intros Hnil.  rewrite Hnil in *. simpl in *.
        apply id_fwd_beq_nat in Hnil; auto. contradiction.

        intros s Hs. rewrite <- Hs. rewrite <- num_occ_ind_l_rev.
        assert ( (identify_fwd alpha2 P (i - length (preds_in alpha1)) + length (preds_in alpha1) -
                 num_occ alpha1 P - (length (preds_in alpha1) - num_occ alpha1 P)) =
                 identify_fwd alpha2 P (i - length (preds_in alpha1))) as Hass2. 
        clear -Hid Hs.
        pose proof (num_occ_preds_in alpha1 P).
        pose proof (num_occ_preds_in alpha2 P).  lia.
        rewrite Hass2 in *. specialize (IHalpha2 P (i - length (preds_in alpha1))).
        clear IHalpha1 Hid Hocc Hbeq H2 Hass2. rewrite Hs in *. apply IHalpha2 in H3; auto.
        unfold identify_rev in H3. clear - Hs H3.
        case_eq (i - length (preds_in alpha1)). intros Hnil.
          rewrite Hnil in *. rewrite identify_fwd_0 in Hs. discriminate.
        intros m Hm. lia.

      apply num_occ_preds_in. rewrite indicies_l_rev_app.
      rewrite app_length. rewrite map_length.
      unfold identify_rev in *. do 2 rewrite <- num_occ_ind_l_rev.

      pose proof (num_occ_preds_in alpha1 P) as H4.
      pose proof (num_occ_preds_in alpha2 P) as H5.
      pose proof (le_id_fwd alpha2 P (i - length (preds_in alpha1)) H3).
      clear -H4 H5 H. lia.

      unfold gt. unfold lt. rewrite <- num_occ_ind_l_rev.
      pose proof (num_occ_preds_in alpha1 P).
      case_eq (identify_fwd alpha2 P (i - length (preds_in alpha1))).
        intros Hnil. rewrite Hnil in *.
        apply id_fwd_beq_nat in Hnil. contradiction.
        auto. firstorder. 

        intros m Hm. lia.
Qed.

Lemma identify_fwd_rev_implSO: forall (alpha1 alpha2 : SecOrder) (P : predicate) (i : nat),
  (forall (P : predicate) (i : nat),
     identify_fwd alpha1 P i <> 0 ->
       occ_in_SO alpha1 i ->
     ~  P = at_pred (preds_in alpha1) i ->
           identify_rev alpha1 P (identify_fwd alpha1 P i) = i) ->
   (forall (P : predicate) (i : nat),
     identify_fwd alpha2 P i <> 0 ->
       occ_in_SO alpha2 i ->
     ~  P = at_pred (preds_in alpha2) i ->
    identify_rev alpha2 P (identify_fwd alpha2 P i) = i) ->
      identify_fwd (implSO alpha1 alpha2) P i <> 0 ->
        occ_in_SO (implSO alpha1 alpha2) i ->
     ~  P = at_pred (preds_in (implSO alpha1 alpha2)) i ->
       identify_rev (implSO alpha1 alpha2) P
         (identify_fwd (implSO alpha1 alpha2) P i) = i.
Proof.
  intros alpha1 alpha2 P i IHalpha1 IHalpha2 Hid Hocc Hbeq.
  pose proof (occ_in_SO_implSO2_fwd2 _ _ _ Hocc) as H.
  destruct H as [Hocc2 | Hocc2].
    unfold identify_rev.
    simpl in Hid; simpl. occ_in_SO_fill.
    rewrite identify_rev_l_app_l; auto.
      apply IHalpha1; auto. simpl in Hbeq.
      rewrite at_pred_app_l in Hbeq; auto.
      firstorder.

      rewrite ind_l_rev_app_length.
      do 2 rewrite <- num_occ_ind_l_rev.
      pose proof (le_id_fwd alpha1 P i Hocc2).
      pose proof (num_occ_preds_in alpha2 P) as H2.
      apply (Le.le_trans _ _ _ H).  clear -H2 H.  lia.
      rewrite <- num_occ_ind_l_rev.
      apply le_id_fwd; auto.  all : auto.

      assert (at_pred (preds_in alpha2) (i - length (preds_in alpha1)) <> P) as Hbeq2.
        assert (i = length (preds_in alpha1) + (i - length (preds_in alpha1))) as Hass.
            clear -Hocc2. firstorder.
        rewrite Hass in Hbeq. simpl in Hbeq. rewrite at_pred_app_r in Hbeq; auto.
        firstorder.
      simpl. simpl in Hid. destruct Hocc2 as [H2 H3].  occ_in_SO_fill. 
      unfold identify_rev. simpl.
      rewrite identify_rev_l_app_r.
      rewrite <- Nat.add_sub_assoc in Hid.
      case_eq (length (preds_in alpha1) -
        num_occ alpha1 P). intros Hnil. rewrite Hnil in *.
        rewrite Nat.add_0_r in *.
        apply IHalpha2 in Hid. unfold identify_rev in Hid.
        rewrite <- num_occ_ind_l_rev.
        case_eq (i - length (preds_in alpha1)). intros Hnil2.
        rewrite Hnil2 in *.  contradiction (occ_in_SO_0 _ H3).
        intros m Hm. rewrite Hm in *. 
        apply Nat.add_sub_eq_nz in Hm. subst.
        rewrite Hnil. rewrite Nat.sub_0_r.
        rewrite <- Nat.add_sub_assoc. rewrite Hnil.
        rewrite Nat.add_0_r. clear -Hid. lia.

        apply num_occ_preds_in.
        all : auto.

        intros m Hm. case_eq (identify_fwd alpha2 P  (i - length (preds_in alpha1))).
        intros Hnil.  rewrite Hnil in *. simpl in *.
        apply id_fwd_beq_nat in Hnil; auto. contradiction.

        intros s Hs. rewrite <- Hs. rewrite <- num_occ_ind_l_rev.
        assert ( (identify_fwd alpha2 P (i - length (preds_in alpha1)) + length (preds_in alpha1) -
                 num_occ alpha1 P - (length (preds_in alpha1) - num_occ alpha1 P)) =
                 identify_fwd alpha2 P (i - length (preds_in alpha1))) as Hass2. 
        clear -Hid Hs.
        pose proof (num_occ_preds_in alpha1 P).
        pose proof (num_occ_preds_in alpha2 P).  lia.
        rewrite Hass2 in *. specialize (IHalpha2 P (i - length (preds_in alpha1))).
        clear IHalpha1 Hid Hocc Hbeq H2 Hass2. rewrite Hs in *. apply IHalpha2 in H3; auto.
        unfold identify_rev in H3. clear - Hs H3.
        case_eq (i - length (preds_in alpha1)). intros Hnil.
          rewrite Hnil in *. rewrite identify_fwd_0 in Hs. discriminate.
        intros m Hm. lia.

      apply num_occ_preds_in. rewrite indicies_l_rev_app.
      rewrite app_length. rewrite map_length.
      unfold identify_rev in *. do 2 rewrite <- num_occ_ind_l_rev.

      pose proof (num_occ_preds_in alpha1 P) as H4.
      pose proof (num_occ_preds_in alpha2 P) as H5.
      pose proof (le_id_fwd alpha2 P (i - length (preds_in alpha1)) H3).
      clear -H4 H5 H. lia.

      unfold gt. unfold lt. rewrite <- num_occ_ind_l_rev.
      pose proof (num_occ_preds_in alpha1 P).
      case_eq (identify_fwd alpha2 P (i - length (preds_in alpha1))).
        intros Hnil. rewrite Hnil in *.
        apply id_fwd_beq_nat in Hnil. contradiction.
        auto. firstorder. 

        intros m Hm. lia.
Qed.

Lemma identify_fwd_rev_allSO : forall (alpha : SecOrder) (P Q : predicate) (i : nat),
  (forall (P : predicate) (i : nat),
          identify_fwd alpha P i <> 0 ->
          occ_in_SO alpha i  ->
          P <> at_pred (preds_in alpha) i -> 
          identify_rev alpha P (identify_fwd alpha P i) = i) ->
    identify_fwd (allSO Q alpha) P i <> 0 ->
      occ_in_SO (allSO Q alpha) i  ->
        P <> at_pred (preds_in (allSO Q alpha)) i ->
            identify_rev (allSO Q alpha) P 
               (identify_fwd (allSO Q alpha) P i) = i.
Proof.
  intros alpha P Q i IHalpha Hid Hocc Hbeq.  simpl.
  simpl in *.  occ_in_SO_fill. unfold identify_rev in *. simpl. 
  destruct i. contradiction (occ_in_SO_0 _ Hocc).
  destruct (predicate_dec P Q).  
    destruct i. simpl in *. rewrite identify_fwd_0 in *. contradiction.
    apply occ_in_SO_allSO_rev in Hocc.
    simpl. case_eq (identify_fwd alpha P (S i)). intros Hnil.
      apply id_fwd_not in Hnil; auto. contradiction.

      intros m Hm. rewrite <- Hm. 
      rewrite IHalpha; auto. 

    destruct i. simpl in *. rewrite identify_fwd_0 in *. simpl.
    rewrite identify_rev_l_0. auto.
    apply occ_in_SO_allSO_rev in Hocc.
    simpl. rewrite Nat.add_1_r.  rewrite IHalpha; auto.
    apply id_fwd_not; auto. 
Qed. 

Lemma identify_fwd_rev_exSO : forall (alpha : SecOrder) (P Q : predicate) (i : nat),
  (forall (P : predicate) (i : nat),
          identify_fwd alpha P i <> 0 ->
          occ_in_SO alpha i  ->
          P <> at_pred (preds_in alpha) i -> 
          identify_rev alpha P (identify_fwd alpha P i) = i) ->
    identify_fwd (exSO Q alpha) P i <> 0 ->
      occ_in_SO (exSO Q alpha) i  ->
        P <> at_pred (preds_in (exSO Q alpha)) i ->
            identify_rev (exSO Q alpha) P 
               (identify_fwd (exSO Q alpha) P i) = i.
Proof.
  intros alpha P Q i IHalpha Hid Hocc Hbeq.  simpl.
  simpl in *.  occ_in_SO_fill. unfold identify_rev in *. simpl. 
  destruct i. contradiction (occ_in_SO_0 _ Hocc).
  destruct (predicate_dec P Q).  
    destruct i. simpl in *. rewrite identify_fwd_0 in *. contradiction.
    apply occ_in_SO_exSO_rev in Hocc.
    simpl. case_eq (identify_fwd alpha P (S i)). intros Hnil.
      apply id_fwd_not in Hnil; auto. contradiction.

      intros m Hm. rewrite <- Hm. 
      rewrite IHalpha; auto. 

    destruct i. simpl in *. rewrite identify_fwd_0 in *. simpl.
    rewrite identify_rev_l_0. auto.
    apply occ_in_SO_exSO_rev in Hocc.
    simpl. rewrite Nat.add_1_r.  rewrite IHalpha; auto.
    apply id_fwd_not; auto. 
Qed. 


Lemma identify_fwd_rev : forall (alpha : SecOrder) (P : predicate) (i : nat),
  ~((identify_fwd alpha P i) = 0) ->
    occ_in_SO alpha i ->
      P <>  at_pred (preds_in alpha) i ->
        identify_rev alpha P (identify_fwd alpha P i) =  i.
Proof.
  induction alpha; intros P i Hid Hocc Hbeq.
    apply identify_fwd_rev_predSO; auto.
    apply occ_in_SO_relatSO in Hocc; contradiction.
    apply occ_in_SO_eqFO in Hocc; contradiction.

    simpl in *. occ_in_SO_fill. rewrite identify_rev_allFO.
    apply IHalpha; auto.  

    simpl in *. occ_in_SO_fill. rewrite identify_rev_exFO.
    apply IHalpha; auto.  

    simpl in *. occ_in_SO_fill. apply IHalpha; auto.
 
    apply identify_fwd_rev_conjSO; auto.
    apply identify_fwd_rev_disjSO; auto.
    apply identify_fwd_rev_implSO; auto.
    apply identify_fwd_rev_allSO; auto.
    apply identify_fwd_rev_exSO; auto.
Qed.  

(* ---------------------------------------------------------------------- *)

Lemma occ_rep_pred2_predSO : forall (cond: SecOrder) (P Q : predicate)
                            (i : nat) (x y: FOvariable),
  FO_frame_condition cond = true ->
    occ_in_SO (replace_pred (predSO P y) Q x cond) i  ->
      occ_in_SO (predSO P y) (identify_rev (predSO P y) Q i). 
Proof.
  intros cond P Q i x y Hun Hocc. simpl in *.
  destruct i. contradiction (occ_in_SO_0 _ Hocc).
  rewrite identify_rev_predSO; firstorder.
Qed.

Lemma occ_rep_pred2_relatSO : forall (cond: SecOrder) (Q : predicate)
                            (i : nat) (x1 x2 y: FOvariable),
  FO_frame_condition cond = true ->
    occ_in_SO (replace_pred (relatSO x1 x2) Q y cond) i ->
      occ_in_SO (relatSO x1 x2) (identify_rev (relatSO x1 x2) Q i).
Proof.
  intros cond Q i x1 x2 y Hun Hocc.
  rewrite rep_pred_relatSO in Hocc.
  contradiction (occ_in_SO_relatSO _ _ _ Hocc).
Qed.

Lemma occ_rep_pred2_eqFO : forall (cond: SecOrder) (Q : predicate)
                            (i : nat) (x1 x2 y: FOvariable),
  FO_frame_condition cond = true ->
    occ_in_SO (replace_pred (eqFO x1 x2) Q y cond) i ->
      occ_in_SO (eqFO x1 x2) (identify_rev (eqFO x1 x2) Q i).
Proof.
  intros cond Q i x1 x2 y Hun Hocc.
  rewrite rep_pred_eqFO in Hocc.
  contradiction (occ_in_SO_eqFO _ _ _ Hocc).
Qed.

Lemma id_rev_conjSO_l : forall (alpha1 alpha2 cond : SecOrder)
                             (Q : predicate) (x : FOvariable) (i : nat),
  FO_frame_condition cond = true ->
    occ_in_SO (replace_pred alpha1 Q x cond) i ->
      (identify_rev (conjSO alpha1 alpha2) Q i) =
         identify_rev alpha1 Q i.
Proof.
  intros alpha1 alpha2 cond Q x i Hun Hocc.
  unfold identify_rev.  simpl.
  pose proof (num_occ_preds_in) as Hl.

  unfold num_occ in Hl.
  inversion Hocc as [Hocc1 Hocc2].
  rewrite preds_in_rep_pred in Hocc2; auto.
  rewrite num_occ_ind_l_rev in Hocc2.
  rewrite identify_rev_l_app_l; auto.
  rewrite indicies_l_rev_app.
  rewrite app_length. rewrite map_length.
  pose proof (le_indicies_l_rev (preds_in alpha2) Q).
  lia.
Qed.

Lemma id_rev_disjSO_l : forall (alpha1 alpha2 cond : SecOrder)
                             (Q : predicate) (x : FOvariable) (i : nat),
  FO_frame_condition cond = true ->
    occ_in_SO (replace_pred alpha1 Q x cond) i ->
      (identify_rev (disjSO alpha1 alpha2) Q i) =
         identify_rev alpha1 Q i.
Proof.
  intros alpha1 alpha2 cond Q x i Hun Hocc.
  unfold identify_rev.  simpl.
  pose proof (num_occ_preds_in) as Hl.
  unfold num_occ in Hl.
  inversion Hocc as [Hocc1 Hocc2].
  rewrite preds_in_rep_pred in Hocc2; auto.
  rewrite num_occ_ind_l_rev in Hocc2.
  rewrite identify_rev_l_app_l; auto.
  rewrite indicies_l_rev_app.
  rewrite app_length. rewrite map_length.
  pose proof (le_indicies_l_rev (preds_in alpha2) Q).
  lia.
Qed.

Lemma id_rev_implSO_l : forall (alpha1 alpha2 cond : SecOrder)
                             (Q : predicate) (x : FOvariable) (i : nat),
  FO_frame_condition cond = true ->
    occ_in_SO (replace_pred alpha1 Q x cond) i ->
      (identify_rev (implSO alpha1 alpha2) Q i) =
         identify_rev alpha1 Q i.
Proof.
  intros alpha1 alpha2 cond Q x i Hun Hocc.
  unfold identify_rev.  simpl.
  pose proof (num_occ_preds_in) as Hl.
  unfold num_occ in Hl.
  inversion Hocc as [Hocc1 Hocc2].
  rewrite preds_in_rep_pred in Hocc2; auto.
  rewrite num_occ_ind_l_rev in Hocc2.
  rewrite identify_rev_l_app_l; auto.
  rewrite indicies_l_rev_app.
  rewrite app_length. rewrite map_length.
  pose proof (le_indicies_l_rev (preds_in alpha2) Q).
  lia.
Qed.

Lemma id_rev_conjSO_r : forall (alpha1 alpha2 cond : SecOrder)
                             (Q : predicate) (x : FOvariable) (i : nat),
  FO_frame_condition cond = true ->
    ~ occ_in_SO (replace_pred alpha1 Q x cond) i ->
      occ_in_SO (replace_pred alpha2 Q x cond)
         (i - length (preds_in (replace_pred alpha1 Q x cond))) ->
      (identify_rev (conjSO alpha1 alpha2) Q i) =
         identify_rev alpha2 Q 
            (i - length (preds_in (replace_pred alpha1 Q x cond)))
             + length (preds_in alpha1).
Proof.
  intros alpha1 alpha2 cond Q x i Hun Hocc1 Hocc2.
  unfold identify_rev.  simpl.
  destruct i. contradiction (occ_in_SO_0 _ Hocc2).
  pose proof (num_occ_preds_in) as Hl.
  unfold num_occ in Hl.
  destruct Hocc2 as [H1 H2]. rewrite preds_in_rep_pred in *.
  rewrite num_occ_ind_l_rev. all : auto.
  rewrite identify_rev_l_app_r.  lia. all : auto.
  
  rewrite indicies_l_rev_app. rewrite app_length.
  rewrite map_length. do 2 rewrite <- num_occ_ind_l_rev.  
  pose proof (num_occ_preds_in alpha1 Q).
  pose proof (num_occ_preds_in alpha2 Q).
  rewrite preds_in_rep_pred in H2; auto.
  lia. unfold gt. unfold lt.
  rewrite <- num_occ_ind_l_rev. lia.
Qed.

Lemma id_rev_implSO_r : forall (alpha1 alpha2 cond : SecOrder)
                             (Q : predicate) (x : FOvariable) (i : nat),
  FO_frame_condition cond = true ->
    ~ occ_in_SO (replace_pred alpha1 Q x cond) i ->
      occ_in_SO (replace_pred alpha2 Q x cond)
         (i - length (preds_in (replace_pred alpha1 Q x cond))) ->
      (identify_rev (implSO alpha1 alpha2) Q i) =
         identify_rev alpha2 Q 
            (i - length (preds_in (replace_pred alpha1 Q x cond)))
             + length (preds_in alpha1).
Proof.
  intros alpha1 alpha2 cond Q x i Hun Hocc1 Hocc2.
  unfold identify_rev.  simpl.
  destruct i. contradiction (occ_in_SO_0 _ Hocc2).
  pose proof (num_occ_preds_in) as Hl.
  unfold num_occ in Hl.
  destruct Hocc2 as [H1 H2]. rewrite preds_in_rep_pred in *.
  rewrite num_occ_ind_l_rev. all : auto.
  rewrite identify_rev_l_app_r.  lia. all : auto.
  
  rewrite indicies_l_rev_app. rewrite app_length.
  rewrite map_length. do 2 rewrite <- num_occ_ind_l_rev.  
  pose proof (num_occ_preds_in alpha1 Q).
  pose proof (num_occ_preds_in alpha2 Q).
  rewrite preds_in_rep_pred in H2; auto.
  lia. unfold gt. unfold lt.
  rewrite <- num_occ_ind_l_rev. lia.
Qed.

Lemma id_rev_disjSO_r : forall (alpha1 alpha2 cond : SecOrder)
                             (Q : predicate) (x : FOvariable) (i : nat),
  FO_frame_condition cond = true ->
    ~ occ_in_SO (replace_pred alpha1 Q x cond) i ->
      occ_in_SO (replace_pred alpha2 Q x cond)
         (i - length (preds_in (replace_pred alpha1 Q x cond))) ->
      (identify_rev (disjSO alpha1 alpha2) Q i) =
         identify_rev alpha2 Q 
            (i - length (preds_in (replace_pred alpha1 Q x cond)))
             + length (preds_in alpha1).
Proof.
  intros alpha1 alpha2 cond Q x i Hun Hocc1 Hocc2.
  unfold identify_rev.  simpl.
  destruct i. contradiction (occ_in_SO_0 _ Hocc2).
  pose proof (num_occ_preds_in) as Hl.
  unfold num_occ in Hl.
  destruct Hocc2 as [H1 H2]. rewrite preds_in_rep_pred in *.
  rewrite num_occ_ind_l_rev. all : auto.
  rewrite identify_rev_l_app_r.  lia. all : auto.
  
  rewrite indicies_l_rev_app. rewrite app_length.
  rewrite map_length. do 2 rewrite <- num_occ_ind_l_rev.  
  pose proof (num_occ_preds_in alpha1 Q).
  pose proof (num_occ_preds_in alpha2 Q).
  rewrite preds_in_rep_pred in H2; auto.
  lia. unfold gt. unfold lt.
  rewrite <- num_occ_ind_l_rev. lia.
Qed.

Lemma occ_rep_pred2_conjSO : forall (alpha1 alpha2 cond : SecOrder)
                                    (Q : predicate) (i : nat)
                                    (x : FOvariable),
  (forall (cond : SecOrder) (Q : predicate) (i : nat) (x : FOvariable),
           FO_frame_condition cond = true ->
           occ_in_SO (replace_pred alpha1 Q x cond) i ->
           occ_in_SO alpha1 (identify_rev alpha1 Q i) ) ->
  (forall (cond : SecOrder) (Q : predicate) (i : nat) (x : FOvariable),
           FO_frame_condition cond = true ->
           occ_in_SO (replace_pred alpha2 Q x cond) i ->
           occ_in_SO alpha2 (identify_rev alpha2 Q i)) ->
    FO_frame_condition cond = true ->
      occ_in_SO (replace_pred (conjSO alpha1 alpha2) Q x cond) i ->
        occ_in_SO (conjSO alpha1 alpha2) 
           (identify_rev (conjSO alpha1 alpha2) Q i).
Proof.
  intros alpha1 alpha2 cond Q i x IHalpha1 IHalpha2 Hun Hocc.
  rewrite rep_pred_conjSO in Hocc.
  apply occ_in_SO_conjSO2_fwd2 in Hocc.
  destruct Hocc.
    rewrite (id_rev_conjSO_l _ _ cond _ x); try assumption.
      rewrite occ_in_SO_conjSO2; try assumption.
        left.
        apply (IHalpha1 cond _ _ x); assumption.

    destruct H as [H1 H2].
    apply occ_in_SO_conjSO2_rev.
    right.
    rewrite (id_rev_conjSO_r _ _ cond _ x); try assumption.
    pose proof (IHalpha2 cond Q _ x Hun H2).
    firstorder.
Qed.

Lemma occ_rep_pred2_disjSO : forall (alpha1 alpha2 cond : SecOrder)
                                    (Q : predicate) (i : nat)
                                    (x : FOvariable),
  (forall (cond : SecOrder) (Q : predicate) (i : nat) (x : FOvariable),
           FO_frame_condition cond = true ->
           occ_in_SO (replace_pred alpha1 Q x cond) i ->
           occ_in_SO alpha1 (identify_rev alpha1 Q i)) ->
  (forall (cond : SecOrder) (Q : predicate) (i : nat) (x : FOvariable),
           FO_frame_condition cond = true ->
           occ_in_SO (replace_pred alpha2 Q x cond) i ->
           occ_in_SO alpha2 (identify_rev alpha2 Q i)) ->
    FO_frame_condition cond = true ->
      occ_in_SO (replace_pred (disjSO alpha1 alpha2) Q x cond) i ->
        occ_in_SO (disjSO alpha1 alpha2) 
           (identify_rev (disjSO alpha1 alpha2) Q i).
Proof.
  intros alpha1 alpha2 cond Q i x IHalpha1 IHalpha2 Hun Hocc.
  rewrite rep_pred_disjSO in Hocc.
  apply occ_in_SO_disjSO2_fwd2 in Hocc.
  destruct Hocc.
    rewrite (id_rev_disjSO_l _ _ cond _ x); try assumption.
      rewrite occ_in_SO_disjSO2; left; try assumption.
        apply (IHalpha1 cond _ _ x); assumption.

    destruct H as [H1 H2].
    apply occ_in_SO_disjSO2_rev.
    right.
    rewrite (id_rev_disjSO_r _ _ cond _ x); try assumption.
    pose proof (IHalpha2 cond Q _ x Hun H2).
    firstorder.
Qed.

Lemma occ_rep_pred2_implSO : forall (alpha1 alpha2 cond : SecOrder)
                                    (Q : predicate) (i : nat)
                                    (x : FOvariable),
  (forall (cond : SecOrder) (Q : predicate) (i : nat) (x : FOvariable),
           FO_frame_condition cond = true ->
           occ_in_SO (replace_pred alpha1 Q x cond) i ->
           occ_in_SO alpha1 (identify_rev alpha1 Q i)) ->
  (forall (cond : SecOrder) (Q : predicate) (i : nat) (x : FOvariable),
           FO_frame_condition cond = true ->
           occ_in_SO (replace_pred alpha2 Q x cond) i ->
           occ_in_SO alpha2 (identify_rev alpha2 Q i)) ->
    FO_frame_condition cond = true ->
      occ_in_SO (replace_pred (implSO alpha1 alpha2) Q x cond) i ->
        occ_in_SO (implSO alpha1 alpha2) 
           (identify_rev (implSO alpha1 alpha2) Q i).
Proof.
  intros alpha1 alpha2 cond Q i x IHalpha1 IHalpha2 Hun Hocc.
  rewrite rep_pred_implSO in Hocc.
  apply occ_in_SO_implSO2_fwd2 in Hocc.
  destruct Hocc.
    rewrite (id_rev_implSO_l _ _ cond _ x); try assumption.
      rewrite occ_in_SO_implSO2; left; try assumption.
        apply (IHalpha1 cond _ _ x); assumption.

    destruct H as [H1 H2].
    apply occ_in_SO_implSO2_rev.
    right.
    rewrite (id_rev_implSO_r _ _ cond _ x); try assumption.
    pose proof (IHalpha2 cond Q _ x Hun H2).
    firstorder.
Qed.

Lemma occ_rep_pred2_allSO : forall (alpha cond : SecOrder) (P Q : predicate)
                                    (x : FOvariable) (i : nat),
    (forall (cond : SecOrder) (Q : predicate) (i : nat) (x : FOvariable),
          FO_frame_condition cond = true ->
          occ_in_SO (replace_pred alpha Q x cond) i ->
          occ_in_SO alpha (identify_rev alpha Q i)) ->
    FO_frame_condition cond = true ->
      (occ_in_SO (replace_pred (allSO P alpha) Q x cond) i) ->
        (occ_in_SO (allSO P alpha) 
              (identify_rev (allSO P alpha) Q i)).
Proof.
  intros alpha cond P Q x i IHalpha Hun Hocc.
  unfold identify_rev; simpl.
  rewrite rep_pred_allSO in Hocc.
  destruct i. contradiction (occ_in_SO_0 _ Hocc).
  destruct (predicate_dec Q P). apply occ_in_SO_allSO.
  apply IHalpha in Hocc; auto.
  destruct i. rewrite identify_rev_l_0. constructor; simpl; firstorder.
  apply occ_in_SO_allSO. apply occ_in_SO_allSO_rev in Hocc.
  apply IHalpha in Hocc; auto.
Qed.

Lemma occ_rep_pred2_exSO : forall (alpha cond : SecOrder) (P Q : predicate)
                                    (x : FOvariable) (i : nat),
    (forall (cond : SecOrder) (Q : predicate) (i : nat) (x : FOvariable),
          FO_frame_condition cond = true ->
          occ_in_SO (replace_pred alpha Q x cond) i ->
          occ_in_SO alpha (identify_rev alpha Q i)) ->
    FO_frame_condition cond = true ->
      (occ_in_SO (replace_pred (exSO P alpha) Q x cond) i) ->
        (occ_in_SO (exSO P alpha) 
              (identify_rev (exSO P alpha) Q i)).
Proof.
  intros alpha cond P Q x i IHalpha Hun Hocc.
  unfold identify_rev; simpl.
  rewrite rep_pred_exSO in Hocc.
  destruct i. contradiction (occ_in_SO_0 _ Hocc).
  destruct (predicate_dec Q P). apply occ_in_SO_exSO.
  apply IHalpha in Hocc; auto.
  destruct i. rewrite identify_rev_l_0. constructor; simpl; firstorder.
  apply occ_in_SO_exSO. apply occ_in_SO_exSO_rev in Hocc.
  apply IHalpha in Hocc; auto.
Qed.

Lemma occ_rep_pred2 : forall (alpha cond: SecOrder) (Q : predicate)
                            (i : nat) (x : FOvariable),
  FO_frame_condition cond = true ->
    occ_in_SO (replace_pred alpha Q x cond) i ->
      occ_in_SO alpha (identify_rev alpha Q i). 
Proof.
  induction alpha;
    intros cond Q i x Hun Hocc.
    apply (occ_rep_pred2_predSO cond _ _ _ x); assumption.
    apply (occ_rep_pred2_relatSO cond _ _ _ _ x); assumption.
    apply (occ_rep_pred2_eqFO cond _ _ _ _ x); assumption.

    rewrite identify_rev_allFO.
    rewrite rep_pred_allFO in Hocc.
    rewrite occ_in_SO_allFO in *.
    apply (IHalpha cond _ _ x); assumption.

    rewrite identify_rev_exFO.
    rewrite rep_pred_exFO in Hocc.
    rewrite occ_in_SO_exFO in *.
    apply (IHalpha cond _ _ x); assumption.

    rewrite rep_pred_negSO in Hocc.
    rewrite identify_rev_negSO.
    rewrite occ_in_SO_negSO in *.
    apply (IHalpha cond _ _ x); assumption.

    apply (occ_rep_pred2_conjSO _ _ cond _ _ x); assumption.
    apply (occ_rep_pred2_disjSO _ _ cond _ _ x); assumption.
    apply (occ_rep_pred2_implSO _ _ cond _ _ x); assumption.
    apply (occ_rep_pred2_allSO _ cond _ _ x); assumption.
    apply (occ_rep_pred2_exSO _ cond _ _ x); assumption.
Qed.

(* --------------------------------------------------------------------- *)

Lemma id_rev_0 : forall (alpha : SecOrder) (Q : predicate ) (i : nat),
  FO_frame_condition alpha = false ->
  identify_rev alpha Q i = 0 ->
    i = 0.
Proof.
  unfold identify_rev.
  intros alpha Q i Hun Hid.
 apply FO_frame_condition_preds_in_f in Hun.
  case_eq i.
    reflexivity.

    intros j Hi; rewrite Hi in *.
    case_eq (preds_in alpha).
      intros H; rewrite H in *.
      simpl in *.
      unfold not in Hun; specialize (Hun (eq_refl _)).
      contradiction.

      intros P l Hl.
      rewrite Hl in *.
      simpl in *.
      destruct P as [Pn]; destruct Q as [Qm].
      discriminate.
Qed.

Lemma id_rev_l_not_nil : forall l i Q,
    l <> nil ->
    i <> 0 ->
    identify_rev_l l Q i <> 0.
Proof.
  induction l; intros i Q H2 H3 H4. firstorder.
  simpl in *. destruct i. firstorder.
  destruct (predicate_dec Q a); discriminate.
Qed.

Lemma id_rev_1_pre : forall l i Q,
    identify_rev_l l Q i = 1 ->
    i <> 0 ->
    i <= length l - length (indicies_l_rev l Q) ->
    i = 0 \/ i = 1.
Proof.
  induction l; intros i Q H1 H2 H3. firstorder.
  simpl in *. destruct i. lia.
  destruct i. lia.
  destruct (predicate_dec Q a). subst.
  rewrite predicate_dec_l in H3. simpl in *.
  inversion H1 as [H4].
  destruct l. simpl in *. inversion H3.
  simpl in H4. discriminate. auto.
  rewrite predicate_dec_r in H3; auto.
  inversion H1 as [H4].
  case_eq (length (indicies_l_rev l Q)).
  intros Hnil. rewrite Hnil in *.
  apply length_zero_iff_nil in Hnil.
  apply id_rev_l_not_nil in H4; auto. contradiction.
  destruct l. simpl in *. lia. firstorder.
  intros mm Hmm. rewrite Hmm in H3.
  apply id_rev_l_not_nil in H4; auto. firstorder.
  destruct l; discriminate.
Qed.

Lemma id_rev_1 : forall (alpha cond: SecOrder) (i : nat) (Q : predicate) (x : FOvariable),
  FO_frame_condition cond = true ->
    occ_in_SO (replace_pred alpha Q x cond) i ->
      identify_rev alpha Q i = 1 -> i = 0 \/ i = 1.
Proof.
  intros alpha cond i Q x H1 H2 H3.
  inversion H2 as [H4 H5].
  rewrite preds_in_rep_pred in H5; auto.
  unfold num_occ in H5.
  rewrite length_ind in H5.
  apply id_rev_1_pre in H5; auto.
Qed.

Lemma id_rev_le_predSO : forall (P Q : predicate) (x : FOvariable) (i : nat),
  i <= (length (preds_in (predSO P x)) - num_occ (predSO P x) Q) ->
  i <= (identify_rev (predSO P x) Q i).
Proof.
  unfold identify_rev.  intros P Q x i Hleb.
  simpl identify_rev_l.  simpl in Hleb.
  rewrite num_occ_predSO in Hleb.
  case_eq i. lia.
  intros j Hi. rewrite Hi in *.
  dest_pred_dec P Q. lia.
Qed.

Lemma id_rev_le_conjSO : forall (alpha1 alpha2 : SecOrder) (Q : predicate)
                                    (i : nat),
  (forall (Q : predicate) (i : nat),
           i <= (length (preds_in alpha1) - num_occ alpha1 Q) ->
           i <= (identify_rev_l (preds_in alpha1) Q i)) ->
  (forall (Q : predicate) (i : nat),
           i <= (length (preds_in alpha2) - num_occ alpha2 Q) ->
           i <= (identify_rev_l (preds_in alpha2) Q i)) ->
  i <= (length (preds_in (conjSO alpha1 alpha2)) - 
                  num_occ (conjSO alpha1 alpha2) Q) ->
  i <= (identify_rev_l (preds_in (conjSO alpha1 alpha2)) Q i).
Proof.
  intros alpha1 alpha2 Q i IHalpha1 IHalpha2 Hleb.
  destruct i. lia.
  simpl in *. rewrite app_length in Hleb. rewrite num_occ_conjSO in Hleb.
  destruct (Compare_dec.le_dec (S i) (length (preds_in alpha1) - num_occ alpha1 Q))
           as [H1 | H1].
    rewrite identify_rev_l_app_l; auto.  rewrite indicies_l_rev_app.
    rewrite app_length. rewrite map_length. do 2 rewrite <- num_occ_ind_l_rev.
    lia. rewrite <- num_occ_ind_l_rev. lia.

    rewrite identify_rev_l_app_r.  rewrite <- num_occ_ind_l_rev.
    assert(S i - (length (preds_in alpha1) - (num_occ alpha1 Q)) <= length (preds_in alpha2) - (num_occ alpha2 Q)) as Hass. lia.
    apply IHalpha2 in Hass. lia. auto.
    rewrite indicies_l_rev_app. rewrite app_length. rewrite map_length.
    do 2 rewrite <- num_occ_ind_l_rev. lia.
    rewrite <- num_occ_ind_l_rev. lia.
Qed.

Lemma id_rev_le_allSO : forall (alpha : SecOrder) (P Q : predicate)
                                    (i : nat),
  (forall (Q : predicate) (i : nat),
          i <= (length (preds_in alpha) - num_occ alpha Q) ->
          i <= (identify_rev_l (preds_in alpha) Q i)) ->
      i <= (length (preds_in (allSO P alpha)) - num_occ (allSO P alpha) Q) ->
      i <= (identify_rev_l (preds_in (allSO P alpha)) Q i).
Proof.
  intros alpha P Q i IHalpha Hleb.  simpl in *.
  rewrite num_occ_allSO in Hleb. destruct i. auto.
  dest_pred_dec P Q. case_eq (num_occ alpha Q).
  intros Hnil. rewrite Hnil in *. apply le_n_S.
  apply IHalpha; auto.  rewrite Hnil. lia.
  intros m Hm. apply le_n_S. rewrite Hm in Hleb.
  apply IHalpha; auto. lia.
Qed.

Lemma id_rev_le : forall (alpha : SecOrder) (Q : predicate)
                              (i : nat),
  i <= (length (preds_in alpha) - num_occ alpha Q) ->
  i <= (identify_rev alpha Q i).
Proof.
  induction alpha; unfold identify_rev; intros Q i Hleb;
    try (simpl in *; lia);
    try (  simpl in *; apply IHalpha; auto).

  eapply id_rev_le_predSO. apply Hleb.
  apply id_rev_le_conjSO; assumption.
  apply id_rev_le_conjSO; assumption.
  apply id_rev_le_conjSO; assumption.
  apply id_rev_le_allSO; assumption.
  apply id_rev_le_allSO; assumption.
Qed.

Lemma length_ind_l_rev : forall (l : list predicate) (Q : predicate),
  (length (indicies_l_rev l Q))  <= (length l).
Proof.
  induction l; intros Q. auto.
  cbn. specialize (IHl Q).
  destruct (predicate_dec a Q); simpl;  lia.
Qed.

Lemma id_rev_preds_in_l : forall (l : list predicate) (Q : predicate) (i : nat),
  i <> 0 ->
    i <= (length l - length (indicies_l_rev l Q)) ->
   (identify_rev_l l Q i) <= (length l).
Proof.
  induction l; intros Q i Hbeq Hleb.   simpl in *. lia.
  rewrite identify_rev_l_cons.  simpl length in *.
  dest_pred_dec a Q; simpl in *. specialize (IHl _ _ Hbeq Hleb); lia.
  destruct i. contradiction. simpl. destruct i.
  apply le_n_S.
  case_eq (length (indicies_l_rev l Q)). intros Hnil. rewrite Hnil in *.
    rewrite identify_rev_l_0. lia.
    intros m Hm. rewrite Hm in *. rewrite identify_rev_l_0. lia.
  apply le_n_S. apply IHl; auto.
  case_eq (length (indicies_l_rev l Q)). intros Hnil. rewrite Hnil in *.
    lia.
    intros m Hm. rewrite Hm in *. lia. auto.
Qed. 

Lemma id_rev_preds_in : forall (alpha : SecOrder) (Q : predicate) (i : nat),
  i <= (length (preds_in alpha) - num_occ alpha Q)  ->
  (identify_rev alpha Q i) <= (length (preds_in alpha)).
Proof.
  intros alpha Q i Hleb. unfold identify_rev. 
  destruct i. rewrite identify_rev_l_0. lia.
  unfold num_occ in Hleb. rewrite length_ind in Hleb. 
  apply id_rev_preds_in_l; auto.
Qed.

Lemma occ_in_SO_id_rev : forall (alpha cond : SecOrder) (Q : predicate) (i : nat)
                                (x : FOvariable),
  FO_frame_condition cond = true ->
    occ_in_SO (replace_pred alpha Q x cond) i ->
      occ_in_SO alpha (identify_rev alpha Q i).
Proof.
  intros alpha cond Q i x Hcond Hocc.
  case_eq (FO_frame_condition alpha); intros Hun.
    rewrite rep_pred_FO_frame_condition in Hocc; try assumption.
    apply FO_frame_condition_occ_in_SO in Hocc; try assumption.
    contradiction.
  destruct Hocc as [H1 H2].
  constructor.
    intros H. apply id_rev_0 in H. contradiction. auto.
    
    apply id_rev_preds_in. rewrite preds_in_rep_pred in H2;
    auto.
Qed. 

(* ------------------------------------------------------------------------------------ *)

Lemma at_pred_rep_pred_conjSO : forall (alpha1 alpha2 cond : SecOrder)
                                (Q : predicate) (x : FOvariable)
                                (i : nat),
  (forall (cond : SecOrder) (Q : predicate) (x : FOvariable) (i : nat),
           FO_frame_condition cond = true ->
           occ_in_SO (replace_pred alpha1 Q x cond) i ->
           at_pred (preds_in (replace_pred alpha1 Q x cond)) i =
           at_pred (preds_in alpha1) (identify_rev alpha1 Q i)) ->
  (forall (cond : SecOrder) (Q : predicate) (x : FOvariable) (i : nat),
           FO_frame_condition cond = true ->
           occ_in_SO (replace_pred alpha2 Q x cond) i ->
           at_pred (preds_in (replace_pred alpha2 Q x cond)) i =
           at_pred (preds_in alpha2) (identify_rev alpha2 Q i)) ->
    FO_frame_condition cond = true ->
      occ_in_SO (replace_pred (conjSO alpha1 alpha2) 
              Q x cond) i ->
      at_pred (preds_in (replace_pred (conjSO alpha1 alpha2) 
                    Q x cond)) i =
        at_pred (preds_in (conjSO alpha1 alpha2))
                    (identify_rev (conjSO alpha1 alpha2) Q i).
Proof.
  intros alpha1 alpha2 cond Q x i IHalpha1 IHalpha2 Hcond
    Hocc.
  unfold identify_rev in *; simpl. simpl in Hocc.
  apply occ_in_SO_conjSO2_fwd2 in Hocc.
  destruct Hocc as [Hocc | [Hocc1 Hocc2]].
    pose proof Hocc as Hocc'.
    destruct Hocc as [Hbeq Hleb].
    rewrite preds_in_rep_pred in Hleb;
    try assumption.
    unfold num_occ in Hleb; rewrite length_ind in Hleb.
    rewrite identify_rev_l_app_l; auto.
    rewrite at_pred_app_l.
    rewrite at_pred_app_l. apply IHalpha1; auto.
      pose proof id_rev_preds_in as H.
      unfold identify_rev in H.
      apply H.
        unfold num_occ; rewrite length_ind.
        assumption.

        rewrite preds_in_rep_pred;
        try assumption.
        unfold num_occ; rewrite length_ind.
        assumption.

        rewrite indicies_l_rev_app.
        pose proof (num_occ_preds_in alpha2 Q) as H1.
        rewrite num_occ_ind_l_rev in H1.
        rewrite app_length. rewrite map_length.
        lia.

      pose proof (occ_in_SO_f _ _ Hocc1) as H.
      destruct H as [H | H].  subst. simpl in *.
        contradiction (occ_in_SO_0 _ Hocc2).

        rewrite preds_in_rep_pred in H;
        try assumption.
        unfold num_occ in H.
        rewrite length_ind in H.
        apply Gt.gt_not_le in H. 
        rewrite identify_rev_l_app_r; auto.
        
        rewrite Nat.add_comm.
        rewrite at_pred_app_r.
        rewrite <- IHalpha2 with (cond := cond) (x := x);
        try assumption.
        assert (i = length (preds_in (replace_pred alpha1 Q x cond)) 
                    + (i - length (preds_in 
                         (replace_pred alpha1 Q x cond)))) as H2.
          rewrite preds_in_rep_pred. pose proof (num_occ_preds_in alpha1 Q).
          unfold num_occ; rewrite length_ind.
          lia. auto.
        rewrite H2 at 1; rewrite at_pred_app_r.
        rewrite preds_in_rep_pred; try assumption.
        unfold num_occ; rewrite length_ind.
        reflexivity.

        intros H3. rewrite H3 in *.
        rewrite preds_in_rep_pred in H2. unfold num_occ in H2.
        rewrite length_ind in H2. rewrite H2 in H. lia. auto. auto.
        
        rewrite preds_in_rep_pred in Hocc2;
          try assumption.
        unfold num_occ in Hocc2.
        rewrite length_ind in Hocc2.
        assumption.

        intros H2.
        case_eq (FO_frame_condition alpha2); intros Hun.
            eapply FO_frame_condition_occ_in_SO in Hocc2. contradiction.
            rewrite rep_pred_FO_frame_condition; assumption.
        eapply id_rev_0 in H2; auto. apply H. lia. lia. 

        rewrite indicies_l_rev_app. rewrite app_length.
        rewrite map_length. pose proof (num_occ_preds_in alpha2 Q) as H2.
        rewrite num_occ_ind_l_rev in H2. inversion Hocc2 as [Ha Hb].
        do 2 rewrite preds_in_rep_pred in Hb. do 2 rewrite num_occ_ind_l_rev in Hb.
        apply Nat.le_sub_le_add_l in Hb; auto.
                apply (Le.le_trans _ _ _ Hb).
                pose proof (num_occ_preds_in alpha1 Q) as HH1.
                pose proof (num_occ_preds_in alpha2 Q) as HH2.
                rewrite num_occ_ind_l_rev in HH1.
                rewrite num_occ_ind_l_rev in HH2.
                clear -HH1 HH2. lia. 
                all : auto. lia.
Qed.

Lemma at_pred_rep_pred_disjSO : forall (alpha1 alpha2 cond : SecOrder)
                                (Q : predicate) (x : FOvariable)
                                (i : nat),
  (forall (cond : SecOrder) (Q : predicate) (x : FOvariable) (i : nat),
           FO_frame_condition cond = true ->
           occ_in_SO (replace_pred alpha1 Q x cond) i ->
           at_pred (preds_in (replace_pred alpha1 Q x cond)) i =
           at_pred (preds_in alpha1) (identify_rev alpha1 Q i)) ->
  (forall (cond : SecOrder) (Q : predicate) (x : FOvariable) (i : nat),
           FO_frame_condition cond = true ->
           occ_in_SO (replace_pred alpha2 Q x cond) i ->
           at_pred (preds_in (replace_pred alpha2 Q x cond)) i =
           at_pred (preds_in alpha2) (identify_rev alpha2 Q i)) ->
    FO_frame_condition cond = true ->
      occ_in_SO (replace_pred (disjSO alpha1 alpha2) 
              Q x cond) i ->
      at_pred (preds_in (replace_pred (disjSO alpha1 alpha2) 
                    Q x cond)) i =
        at_pred (preds_in (disjSO alpha1 alpha2))
                    (identify_rev (disjSO alpha1 alpha2) Q i).
Proof.
  intros alpha1 alpha2 cond Q x i IHalpha1 IHalpha2 Hcond
    Hocc.
  unfold identify_rev in *; simpl. simpl in Hocc.
  apply occ_in_SO_disjSO2_fwd2 in Hocc.
  destruct Hocc as [Hocc | [Hocc1 Hocc2]].
    pose proof Hocc as Hocc'.
    destruct Hocc as [Hbeq Hleb].
    rewrite preds_in_rep_pred in Hleb;
    try assumption.
    unfold num_occ in Hleb; rewrite length_ind in Hleb.
    rewrite identify_rev_l_app_l; auto.
    rewrite at_pred_app_l.
    rewrite at_pred_app_l. apply IHalpha1; auto.
      pose proof id_rev_preds_in as H.
      unfold identify_rev in H.
      apply H.
        unfold num_occ; rewrite length_ind.
        assumption.

        rewrite preds_in_rep_pred;
        try assumption.
        unfold num_occ; rewrite length_ind.
        assumption.

        rewrite indicies_l_rev_app.
        pose proof (num_occ_preds_in alpha2 Q) as H1.
        rewrite num_occ_ind_l_rev in H1.
        rewrite app_length. rewrite map_length.
        lia.

      pose proof (occ_in_SO_f _ _ Hocc1) as H.
      destruct H as [H | H].  subst. simpl in *.
        contradiction (occ_in_SO_0 _ Hocc2).

        rewrite preds_in_rep_pred in H;
        try assumption.
        unfold num_occ in H.
        rewrite length_ind in H.
        apply Gt.gt_not_le in H. 
        rewrite identify_rev_l_app_r; auto.
        
        rewrite Nat.add_comm.
        rewrite at_pred_app_r.
        rewrite <- IHalpha2 with (cond := cond) (x := x);
        try assumption.
        assert (i = length (preds_in (replace_pred alpha1 Q x cond)) 
                    + (i - length (preds_in 
                         (replace_pred alpha1 Q x cond)))) as H2.
          rewrite preds_in_rep_pred. pose proof (num_occ_preds_in alpha1 Q).
          unfold num_occ; rewrite length_ind.
          lia. auto.
        rewrite H2 at 1; rewrite at_pred_app_r.
        rewrite preds_in_rep_pred; try assumption.
        unfold num_occ; rewrite length_ind.
        reflexivity.

        intros H3. rewrite H3 in *.
        rewrite preds_in_rep_pred in H2. unfold num_occ in H2.
        rewrite length_ind in H2. rewrite H2 in H. lia. auto. auto.
        
        rewrite preds_in_rep_pred in Hocc2;
          try assumption.
        unfold num_occ in Hocc2.
        rewrite length_ind in Hocc2.
        assumption.

        intros H2.
        case_eq (FO_frame_condition alpha2); intros Hun.
            eapply FO_frame_condition_occ_in_SO in Hocc2. contradiction.
            rewrite rep_pred_FO_frame_condition; assumption.
        eapply id_rev_0 in H2; auto. apply H. lia. lia. 

        rewrite indicies_l_rev_app. rewrite app_length.
        rewrite map_length. pose proof (num_occ_preds_in alpha2 Q) as H2.
        rewrite num_occ_ind_l_rev in H2. inversion Hocc2 as [Ha Hb].
        do 2 rewrite preds_in_rep_pred in Hb. do 2 rewrite num_occ_ind_l_rev in Hb.
        apply Nat.le_sub_le_add_l in Hb; auto.
                apply (Le.le_trans _ _ _ Hb).
                pose proof (num_occ_preds_in alpha1 Q) as HH1.
                pose proof (num_occ_preds_in alpha2 Q) as HH2.
                rewrite num_occ_ind_l_rev in HH1.
                rewrite num_occ_ind_l_rev in HH2.
                clear -HH1 HH2. lia. 
                all : auto. lia.
Qed.

Lemma at_pred_rep_pred_implSO : forall (alpha1 alpha2 cond : SecOrder)
                                (Q : predicate) (x : FOvariable)
                                (i : nat),
  (forall (cond : SecOrder) (Q : predicate) (x : FOvariable) (i : nat),
           FO_frame_condition cond = true ->
           occ_in_SO (replace_pred alpha1 Q x cond) i ->
           at_pred (preds_in (replace_pred alpha1 Q x cond)) i =
           at_pred (preds_in alpha1) (identify_rev alpha1 Q i)) ->
  (forall (cond : SecOrder) (Q : predicate) (x : FOvariable) (i : nat),
           FO_frame_condition cond = true ->
           occ_in_SO (replace_pred alpha2 Q x cond) i ->
           at_pred (preds_in (replace_pred alpha2 Q x cond)) i =
           at_pred (preds_in alpha2) (identify_rev alpha2 Q i)) ->
    FO_frame_condition cond = true ->
      occ_in_SO (replace_pred (implSO alpha1 alpha2) 
              Q x cond) i ->
      at_pred (preds_in (replace_pred (implSO alpha1 alpha2) 
                    Q x cond)) i =
        at_pred (preds_in (implSO alpha1 alpha2))
                    (identify_rev (implSO alpha1 alpha2) Q i).
Proof.
  intros alpha1 alpha2 cond Q x i IHalpha1 IHalpha2 Hcond
    Hocc.
  unfold identify_rev in *; simpl. simpl in Hocc.
  apply occ_in_SO_implSO2_fwd2 in Hocc.
  destruct Hocc as [Hocc | [Hocc1 Hocc2]].
    pose proof Hocc as Hocc'.
    destruct Hocc as [Hbeq Hleb].
    rewrite preds_in_rep_pred in Hleb;
    try assumption.
    unfold num_occ in Hleb; rewrite length_ind in Hleb.
    rewrite identify_rev_l_app_l; auto.
    rewrite at_pred_app_l.
    rewrite at_pred_app_l. apply IHalpha1; auto.
      pose proof id_rev_preds_in as H.
      unfold identify_rev in H.
      apply H.
        unfold num_occ; rewrite length_ind.
        assumption.

        rewrite preds_in_rep_pred;
        try assumption.
        unfold num_occ; rewrite length_ind.
        assumption.

        rewrite indicies_l_rev_app.
        pose proof (num_occ_preds_in alpha2 Q) as H1.
        rewrite num_occ_ind_l_rev in H1.
        rewrite app_length. rewrite map_length.
        lia.

      pose proof (occ_in_SO_f _ _ Hocc1) as H.
      destruct H as [H | H].  subst. simpl in *.
        contradiction (occ_in_SO_0 _ Hocc2).

        rewrite preds_in_rep_pred in H;
        try assumption.
        unfold num_occ in H.
        rewrite length_ind in H.
        apply Gt.gt_not_le in H. 
        rewrite identify_rev_l_app_r; auto.
        
        rewrite Nat.add_comm.
        rewrite at_pred_app_r.
        rewrite <- IHalpha2 with (cond := cond) (x := x);
        try assumption.
        assert (i = length (preds_in (replace_pred alpha1 Q x cond)) 
                    + (i - length (preds_in 
                         (replace_pred alpha1 Q x cond)))) as H2.
          rewrite preds_in_rep_pred. pose proof (num_occ_preds_in alpha1 Q).
          unfold num_occ; rewrite length_ind.
          lia. auto.
        rewrite H2 at 1; rewrite at_pred_app_r.
        rewrite preds_in_rep_pred; try assumption.
        unfold num_occ; rewrite length_ind.
        reflexivity.

        intros H3. rewrite H3 in *.
        rewrite preds_in_rep_pred in H2. unfold num_occ in H2.
        rewrite length_ind in H2. rewrite H2 in H. lia. auto. auto.
        
        rewrite preds_in_rep_pred in Hocc2;
          try assumption.
        unfold num_occ in Hocc2.
        rewrite length_ind in Hocc2.
        assumption.

        intros H2.
        case_eq (FO_frame_condition alpha2); intros Hun.
            eapply FO_frame_condition_occ_in_SO in Hocc2. contradiction.
            rewrite rep_pred_FO_frame_condition; assumption.
        eapply id_rev_0 in H2; auto. apply H. lia. lia. 

        rewrite indicies_l_rev_app. rewrite app_length.
        rewrite map_length. pose proof (num_occ_preds_in alpha2 Q) as H2.
        rewrite num_occ_ind_l_rev in H2. inversion Hocc2 as [Ha Hb].
        do 2 rewrite preds_in_rep_pred in Hb. do 2 rewrite num_occ_ind_l_rev in Hb.
        apply Nat.le_sub_le_add_l in Hb; auto.
                apply (Le.le_trans _ _ _ Hb).
                pose proof (num_occ_preds_in alpha1 Q) as HH1.
                pose proof (num_occ_preds_in alpha2 Q) as HH2.
                rewrite num_occ_ind_l_rev in HH1.
                rewrite num_occ_ind_l_rev in HH2.
                clear -HH1 HH2. lia. 
                all : auto. lia.
Qed.

Lemma at_pred_rep_pred_allSO : forall (alpha cond : SecOrder)
                                (P Q : predicate) (x : FOvariable)
                                (i : nat),
  (forall (cond : SecOrder) (Q : predicate) (x : FOvariable) (i : nat),
          FO_frame_condition cond = true ->
          occ_in_SO (replace_pred alpha Q x cond) i ->
          at_pred (preds_in (replace_pred alpha Q x cond)) i =
          at_pred (preds_in alpha) (identify_rev alpha Q i)) ->
      FO_frame_condition cond = true ->
        occ_in_SO (replace_pred (allSO P alpha) Q x cond) i ->
      at_pred (preds_in (replace_pred (allSO P alpha) Q x cond)) i =
         at_pred (preds_in (allSO P alpha)) 
             (identify_rev (allSO P alpha) Q i).
Proof.
  intros alpha cond P Q x i IHalpha Hcond Hocc.
  rewrite rep_pred_allSO in *.
  unfold identify_rev in *.
  simpl preds_in in *. simpl.
  destruct (predicate_dec Q P) as [H | H].
    subst. simpl. 
    destruct i. contradiction (occ_in_SO_0 _ Hocc).
    rewrite IHalpha; try assumption.
    case_eq (FO_frame_condition alpha); intros Hun.
      eapply FO_frame_condition_occ_in_SO in Hocc. contradiction.
        rewrite rep_pred_FO_frame_condition; assumption.

    case_eq (identify_rev_l (preds_in alpha) P (S i)).
      intros H.
      pose proof id_rev_0 as H2.
      unfold identify_rev in H2.
      rewrite (H2 _ _ _ Hun H) in  Hocc.
      contradiction (occ_in_SO_0 _ Hocc).

      intros n H. reflexivity.

   simpl preds_in. destruct i. contradiction (occ_in_SO_0 _ Hocc).
   simpl. destruct i. rewrite identify_rev_l_0. reflexivity.

        apply occ_in_SO_allSO_rev in Hocc.
        case_eq (FO_frame_condition alpha); intros Hun.
          eapply FO_frame_condition_occ_in_SO in Hocc. contradiction.
            rewrite rep_pred_FO_frame_condition;
            assumption.

          simpl. rewrite IHalpha; try assumption.
          case_eq (identify_rev_l (preds_in alpha) Q (S i)).
            intros H2.
            pose proof (id_rev_0 _ _ _ Hun H2) as H2'.
            discriminate.

        auto.
Qed.

Lemma at_pred_rep_pred_exSO : forall (alpha cond : SecOrder)
                                (P Q : predicate) (x : FOvariable)
                                (i : nat),
  (forall (cond : SecOrder) (Q : predicate) (x : FOvariable) (i : nat),
          FO_frame_condition cond = true ->
          occ_in_SO (replace_pred alpha Q x cond) i ->
          at_pred (preds_in (replace_pred alpha Q x cond)) i =
          at_pred (preds_in alpha) (identify_rev alpha Q i)) ->
      FO_frame_condition cond = true ->
        occ_in_SO (replace_pred (exSO P alpha) Q x cond) i ->
      at_pred (preds_in (replace_pred (exSO P alpha) Q x cond)) i =
         at_pred (preds_in (exSO P alpha)) 
             (identify_rev (exSO P alpha) Q i).
Proof.
  intros alpha cond P Q x i IHalpha Hcond Hocc.
  rewrite rep_pred_exSO in *.
  unfold identify_rev in *.
  simpl preds_in in *. simpl.
  destruct (predicate_dec Q P) as [H | H].
    subst. simpl. 
    destruct i. contradiction (occ_in_SO_0 _ Hocc).
    rewrite IHalpha; try assumption.
    case_eq (FO_frame_condition alpha); intros Hun.
      eapply FO_frame_condition_occ_in_SO in Hocc. contradiction.
        rewrite rep_pred_FO_frame_condition; assumption.

    case_eq (identify_rev_l (preds_in alpha) P (S i)).
      intros H.
      pose proof id_rev_0 as H2.
      unfold identify_rev in H2.
      rewrite (H2 _ _ _ Hun H) in  Hocc.
      contradiction (occ_in_SO_0 _ Hocc).

      intros n H. reflexivity.

   simpl preds_in. destruct i. contradiction (occ_in_SO_0 _ Hocc).
   simpl. destruct i. rewrite identify_rev_l_0. reflexivity.

        apply occ_in_SO_exSO_rev in Hocc.
        case_eq (FO_frame_condition alpha); intros Hun.
          eapply FO_frame_condition_occ_in_SO in Hocc. contradiction.
            rewrite rep_pred_FO_frame_condition;
            assumption.

          simpl. rewrite IHalpha; try assumption.
          case_eq (identify_rev_l (preds_in alpha) Q (S i)).
            intros H2.
            pose proof (id_rev_0 _ _ _ Hun H2) as H2'.
            discriminate.

        auto.
Qed.

Lemma at_pred_rep_pred : forall (alpha cond : SecOrder)
                                (Q : predicate) (x : FOvariable)
                                (i : nat),
  FO_frame_condition cond = true ->
    occ_in_SO (replace_pred alpha Q x cond) i ->
    at_pred (preds_in (replace_pred alpha Q x cond)) i 
     = at_pred (preds_in alpha) (identify_rev alpha Q i).
Proof.
  induction alpha;
    intros cond Q x i Hcond Hocc;
    try reflexivity;
    try (    simpl in *; unfold identify_rev in *;
    simpl preds_in; apply IHalpha; try assumption). 

    unfold identify_rev.
    simpl preds_in.
    rewrite identify_rev_l_cons.
    simpl identify_rev_l.
    simpl in Hocc.
    destruct (predicate_dec Q p) as [H1|H1].
      simpl. destruct i. contradiction (occ_in_SO_0 _ Hocc).
      simpl. eapply FO_frame_condition_occ_in_SO in Hocc.
      contradiction. apply rep_FOv_FO_frame_condition.
      auto.

      destruct i. contradiction (occ_in_SO_0 _ Hocc).
      simpl. destruct i. auto. inversion Hocc. simpl in *. lia.
      destruct Hocc as [H2 H3]. lia. 

    apply at_pred_rep_pred_conjSO; assumption.
    apply at_pred_rep_pred_disjSO; assumption.
    apply at_pred_rep_pred_implSO; assumption.
    apply at_pred_rep_pred_allSO; assumption.
    apply at_pred_rep_pred_exSO; assumption.
Qed.

Lemma at_pred_occ_id_fwd_conjSO : forall (alpha1 alpha2 : SecOrder) (i : nat) (Q : predicate),
  (forall (i : nat) (Q : predicate),
           occ_in_SO alpha1 i -> 
           identify_fwd alpha1 Q i = 0 ->
           at_pred (preds_in alpha1) i = Q) ->
  (forall (i : nat) (Q : predicate),
           occ_in_SO alpha2 i -> 
           identify_fwd alpha2 Q i = 0 -> 
           at_pred (preds_in alpha2) i = Q) ->
  occ_in_SO (conjSO alpha1 alpha2) i ->
  identify_fwd (conjSO alpha1 alpha2) Q i = 0 ->
  at_pred (preds_in (conjSO alpha1 alpha2)) i = Q.
Proof.
  intros alpha1 alpha2 i Q IHalpha1 IHalpha2 Hocc Hid.
    simpl in *. rewrite occ_in_SO_dec_l in Hid.
    apply occ_in_SO_conjSO2_fwd2 in Hocc.
    destruct Hocc as [Hocc | Hocc].
      rewrite occ_in_SO_dec_l in Hid.
      rewrite at_pred_app_l.
        apply IHalpha1; assumption. inversion Hocc; lia. auto.

      destruct Hocc as [Hl Hr].
      rewrite occ_in_SO_dec_r in Hid.
      assert (i - length (preds_in alpha1) + length (preds_in alpha1) = i) as H.
        inversion Hr. lia.

      rewrite <- H. rewrite Nat.add_comm.
      rewrite at_pred_app_r.
        apply IHalpha2; try assumption.
        rewrite <- Nat.add_sub_assoc in Hid. lia.

          apply num_occ_preds_in.
          inversion Hr; lia. all : auto.
Qed.

Lemma at_pred_occ_id_fwd_disjSO : forall (alpha1 alpha2 : SecOrder) (i : nat) (Q : predicate),
  (forall (i : nat) (Q : predicate),
           occ_in_SO alpha1 i -> 
           identify_fwd alpha1 Q i = 0 ->
           at_pred (preds_in alpha1) i = Q) ->
  (forall (i : nat) (Q : predicate),
           occ_in_SO alpha2 i -> 
           identify_fwd alpha2 Q i = 0 -> 
           at_pred (preds_in alpha2) i = Q) ->
  occ_in_SO (disjSO alpha1 alpha2) i ->
  identify_fwd (disjSO alpha1 alpha2) Q i = 0 ->
  at_pred (preds_in (disjSO alpha1 alpha2)) i = Q.
Proof.
  intros alpha1 alpha2 i Q IHalpha1 IHalpha2 Hocc Hid.
    simpl in *. rewrite occ_in_SO_dec_l in Hid.
    apply occ_in_SO_disjSO2_fwd2 in Hocc.
    destruct Hocc as [Hocc | Hocc].
      rewrite occ_in_SO_dec_l in Hid.
      rewrite at_pred_app_l.
        apply IHalpha1; assumption. inversion Hocc; lia. auto.

      destruct Hocc as [Hl Hr].
      rewrite occ_in_SO_dec_r in Hid.
      assert (i - length (preds_in alpha1) + length (preds_in alpha1) = i) as H.
        inversion Hr. lia.

      rewrite <- H. rewrite Nat.add_comm.
      rewrite at_pred_app_r.
        apply IHalpha2; try assumption.
        rewrite <- Nat.add_sub_assoc in Hid. lia.

          apply num_occ_preds_in.
          inversion Hr; lia. all : auto.
Qed.

Lemma at_pred_occ_id_fwd_implSO : forall (alpha1 alpha2 : SecOrder) (i : nat) (Q : predicate),
  (forall (i : nat) (Q : predicate),
           occ_in_SO alpha1 i -> 
           identify_fwd alpha1 Q i = 0 ->
           at_pred (preds_in alpha1) i = Q) ->
  (forall (i : nat) (Q : predicate),
           occ_in_SO alpha2 i -> 
           identify_fwd alpha2 Q i = 0 -> 
           at_pred (preds_in alpha2) i = Q) ->
  occ_in_SO (implSO alpha1 alpha2) i ->
  identify_fwd (implSO alpha1 alpha2) Q i = 0 ->
  at_pred (preds_in (implSO alpha1 alpha2)) i = Q.
Proof.
  intros alpha1 alpha2 i Q IHalpha1 IHalpha2 Hocc Hid.
    simpl in *. rewrite occ_in_SO_dec_l in Hid.
    apply occ_in_SO_implSO2_fwd2 in Hocc.
    destruct Hocc as [Hocc | Hocc].
      rewrite occ_in_SO_dec_l in Hid.
      rewrite at_pred_app_l.
        apply IHalpha1; assumption. inversion Hocc; lia. auto.

      destruct Hocc as [Hl Hr].
      rewrite occ_in_SO_dec_r in Hid.
      assert (i - length (preds_in alpha1) + length (preds_in alpha1) = i) as H.
        inversion Hr. lia.

      rewrite <- H. rewrite Nat.add_comm.
      rewrite at_pred_app_r.
        apply IHalpha2; try assumption.
        rewrite <- Nat.add_sub_assoc in Hid. lia.

          apply num_occ_preds_in.
          inversion Hr; lia. all : auto.
Qed.  

Lemma at_pred_occ_id_fwd_allSO : forall (alpha : SecOrder) (i : nat) (Q P : predicate),
  (forall (i : nat) (Q : predicate),
          occ_in_SO alpha i -> 
          identify_fwd alpha Q i = 0 -> 
          at_pred (preds_in alpha) i = Q) ->
   occ_in_SO (allSO P alpha) i ->
   identify_fwd (allSO P alpha) Q i = 0 ->
   at_pred (preds_in (allSO P alpha)) i = Q.
Proof.
  intros alpha i Q P IHalpha Hocc Hid. simpl preds_in in *.
  simpl in Hid. rewrite occ_in_SO_dec_l in Hid.
  simpl. destruct i. contradiction (occ_in_SO_0 _ Hocc).
  destruct i. simpl in *. destruct (predicate_dec Q P). auto. lia.
  simpl in *. apply IHalpha. apply occ_in_SO_allSO_rev in Hocc. auto.
  destruct (predicate_dec Q P); lia. auto.
Qed. 

Lemma at_pred_occ_id_fwd_exSO : forall (alpha : SecOrder) (i : nat) (Q P : predicate),
  (forall (i : nat) (Q : predicate),
          occ_in_SO alpha i -> 
          identify_fwd alpha Q i = 0 -> 
          at_pred (preds_in alpha) i = Q) ->
   occ_in_SO (exSO P alpha) i ->
   identify_fwd (exSO P alpha) Q i = 0 ->
   at_pred (preds_in (exSO P alpha)) i = Q.
Proof.
  intros alpha i Q P IHalpha Hocc Hid. simpl preds_in in *.
  simpl in Hid. rewrite occ_in_SO_dec_l in Hid.
  simpl. destruct i. contradiction (occ_in_SO_0 _ Hocc).
  destruct i. simpl in *. destruct (predicate_dec Q P). auto. lia.
  simpl in *. apply IHalpha. apply occ_in_SO_exSO_rev in Hocc. auto.
  destruct (predicate_dec Q P); lia. auto.
Qed. 

Lemma at_pred_occ_id_fwd : forall (alpha : SecOrder) (i : nat) (Q : predicate),
  occ_in_SO alpha i  ->
    identify_fwd alpha Q i = 0 ->
      at_pred (preds_in alpha) i = Q.
Proof.
  induction alpha; intros i Q Hocc Hid;
    try (apply at_pred_occ_id_fwd_conjSO; assumption);
    try (apply at_pred_occ_id_fwd_disjSO; assumption);
    try (apply at_pred_occ_id_fwd_implSO; assumption);
    try (apply at_pred_occ_id_fwd_allSO; assumption);
    try (apply at_pred_occ_id_fwd_exSO; assumption);
    simpl in *; rewrite occ_in_SO_dec_l in Hid; auto.

    apply occ_in_SO_predSO in Hocc; auto.
    rewrite Hocc in *. destruct (predicate_dec Q p); auto; lia.
    auto.

    contradiction (occ_in_SO_relatSO _ _ _ Hocc).
    contradiction (occ_in_SO_eqFO _ _ _ Hocc).
Qed.

Lemma at_pred_occ_rep_pred_predSO : forall (cond : SecOrder) (i : nat) (x y: FOvariable)
                                    (P Q : predicate),
  FO_frame_condition cond = true ->
  occ_in_SO (predSO P y) i ->
  ~ occ_in_SO (replace_pred (predSO P y) Q x cond) (identify_fwd (predSO P y) Q i) ->
  at_pred (preds_in (predSO P y)) i = Q.
Proof.
  intros cond i x y P Q Hcond Hocc1 Hocc2.
  apply at_pred_occ_id_fwd; try assumption.
  simpl in *; rewrite occ_in_SO_dec_l in *; auto.
  apply occ_in_SO_predSO in Hocc1. subst.
  destruct (predicate_dec Q P). auto.
  apply occ_in_SO_f in Hocc2. simpl in *. firstorder.
Qed.

Lemma at_pred_occ_rep_pred_conjSO : forall (alpha1 alpha2 cond : SecOrder) (i : nat) (x: FOvariable)
                                    (Q : predicate),
  (forall (cond : SecOrder) (i : nat) (x : FOvariable) (Q : predicate),
           FO_frame_condition cond = true ->
           occ_in_SO alpha1 i  ->
           ~ occ_in_SO (replace_pred alpha1 Q x cond) (identify_fwd alpha1 Q i) ->
           at_pred (preds_in alpha1) i = Q) ->
  (forall (cond : SecOrder) (i : nat) (x : FOvariable) (Q : predicate),
           FO_frame_condition cond = true ->
           occ_in_SO alpha2 i ->
           ~ occ_in_SO (replace_pred alpha2 Q x cond) (identify_fwd alpha2 Q i) ->
           at_pred (preds_in alpha2) i = Q) ->
  FO_frame_condition cond = true ->
  occ_in_SO (conjSO alpha1 alpha2) i ->
  ~ occ_in_SO (replace_pred (conjSO alpha1 alpha2) Q x cond)
          (identify_fwd (conjSO alpha1 alpha2) Q i) ->
  at_pred (preds_in (conjSO alpha1 alpha2)) i = Q.
Proof.
  intros alpha1 alpha2 cond i x Q IHalpha1 IHalpha2 Hcond Hocc1 Hocc2.
  simpl in *; rewrite occ_in_SO_dec_l in Hocc2;
  apply occ_in_SO_conjSO2_fwd2 in Hocc1.
  apply occ_in_SO_f in Hocc2.
  destruct Hocc1 as [Hocc1 | Hocc1].
    rewrite occ_in_SO_dec_l in Hocc2.
    destruct Hocc2.
      rewrite at_pred_app_l.
        apply at_pred_occ_id_fwd; auto. firstorder.

        rewrite at_pred_app_l.
          apply IHalpha1 with (cond := cond) (x := x);
            try assumption.
          intros [H1 H2].
          simpl in H.
          rewrite app_length in H.
          lia. inversion Hocc1. lia. auto.

    destruct Hocc1 as [Hl Hr].
    assert (i - length (preds_in alpha1) + length (preds_in alpha1) = i).
      firstorder.

      destruct (occ_in_SO_f _ _ Hl) as [H1 | H2]. subst.
        contradiction (occ_in_SO_0 _ Hr).

    rewrite <- H. rewrite Nat.add_comm.     
    rewrite at_pred_app_r.
    destruct Hocc2 as [Hocc2 | Hocc2].
      rewrite <- Nat.add_sub_assoc in Hocc2.
      rewrite occ_in_SO_dec_r in Hocc2.
        apply at_pred_occ_id_fwd; try assumption.

        lia. auto.

        apply num_occ_preds_in.

      rewrite occ_in_SO_dec_r in Hocc2.
      apply IHalpha2 with (cond := cond) (x := x); try assumption.
        intros Hocc3.  simpl in Hocc2.        
        rewrite app_length in Hocc2.
        rewrite preds_in_rep_pred in Hocc2; try assumption.
        rewrite <- Nat.add_sub_assoc in Hocc2.
        firstorder.

          apply num_occ_preds_in. auto. firstorder. auto.
          apply occ_in_SO_conjSO2. clear -Hocc1. firstorder.
Qed.

Lemma at_pred_occ_rep_pred_disjSO : forall (alpha1 alpha2 cond : SecOrder) (i : nat) (x: FOvariable)
                                    (Q : predicate),
  (forall (cond : SecOrder) (i : nat) (x : FOvariable) (Q : predicate),
           FO_frame_condition cond = true ->
           occ_in_SO alpha1 i  ->
           ~ occ_in_SO (replace_pred alpha1 Q x cond) (identify_fwd alpha1 Q i) ->
           at_pred (preds_in alpha1) i = Q) ->
  (forall (cond : SecOrder) (i : nat) (x : FOvariable) (Q : predicate),
           FO_frame_condition cond = true ->
           occ_in_SO alpha2 i ->
           ~ occ_in_SO (replace_pred alpha2 Q x cond) (identify_fwd alpha2 Q i) ->
           at_pred (preds_in alpha2) i = Q) ->
  FO_frame_condition cond = true ->
  occ_in_SO (disjSO alpha1 alpha2) i ->
  ~ occ_in_SO (replace_pred (disjSO alpha1 alpha2) Q x cond)
          (identify_fwd (disjSO alpha1 alpha2) Q i) ->
  at_pred (preds_in (disjSO alpha1 alpha2)) i = Q.
Proof.
  intros alpha1 alpha2 cond i x Q IHalpha1 IHalpha2 Hcond Hocc1 Hocc2.
  simpl in *; rewrite occ_in_SO_dec_l in Hocc2;
  apply occ_in_SO_disjSO2_fwd2 in Hocc1.
  apply occ_in_SO_f in Hocc2.
  destruct Hocc1 as [Hocc1 | Hocc1].
    rewrite occ_in_SO_dec_l in Hocc2.
    destruct Hocc2.
      rewrite at_pred_app_l.
        apply at_pred_occ_id_fwd; auto. firstorder.

        rewrite at_pred_app_l.
          apply IHalpha1 with (cond := cond) (x := x);
            try assumption.
          intros [H1 H2].
          simpl in H.
          rewrite app_length in H.
          lia. inversion Hocc1. lia. auto.

    destruct Hocc1 as [Hl Hr].
    assert (i - length (preds_in alpha1) + length (preds_in alpha1) = i).
      firstorder. 

      destruct (occ_in_SO_f _ _ Hl) as [H1 | H2]. subst.
        contradiction (occ_in_SO_0 _ Hr).

    rewrite <- H. rewrite Nat.add_comm.     
    rewrite at_pred_app_r.
    destruct Hocc2 as [Hocc2 | Hocc2].
      rewrite <- Nat.add_sub_assoc in Hocc2.
      rewrite occ_in_SO_dec_r in Hocc2.
        apply at_pred_occ_id_fwd; try assumption.

        lia. auto.

        apply num_occ_preds_in.

      rewrite occ_in_SO_dec_r in Hocc2.
      apply IHalpha2 with (cond := cond) (x := x); try assumption.
        intros Hocc3.  simpl in Hocc2.        
        rewrite app_length in Hocc2.
        rewrite preds_in_rep_pred in Hocc2; try assumption.
        rewrite <- Nat.add_sub_assoc in Hocc2.
        firstorder.

          apply num_occ_preds_in. auto. firstorder. auto.
          apply occ_in_SO_disjSO2. clear -Hocc1. firstorder.
Qed.

Lemma at_pred_occ_rep_pred_implSO : forall (alpha1 alpha2 cond : SecOrder) (i : nat) (x: FOvariable)
                                    (Q : predicate),
  (forall (cond : SecOrder) (i : nat) (x : FOvariable) (Q : predicate),
           FO_frame_condition cond = true ->
           occ_in_SO alpha1 i  ->
           ~ occ_in_SO (replace_pred alpha1 Q x cond) (identify_fwd alpha1 Q i) ->
           at_pred (preds_in alpha1) i = Q) ->
  (forall (cond : SecOrder) (i : nat) (x : FOvariable) (Q : predicate),
           FO_frame_condition cond = true ->
           occ_in_SO alpha2 i ->
           ~ occ_in_SO (replace_pred alpha2 Q x cond) (identify_fwd alpha2 Q i) ->
           at_pred (preds_in alpha2) i = Q) ->
  FO_frame_condition cond = true ->
  occ_in_SO (implSO alpha1 alpha2) i ->
  ~ occ_in_SO (replace_pred (implSO alpha1 alpha2) Q x cond)
          (identify_fwd (implSO alpha1 alpha2) Q i) ->
  at_pred (preds_in (implSO alpha1 alpha2)) i = Q.
Proof.
  intros alpha1 alpha2 cond i x Q IHalpha1 IHalpha2 Hcond Hocc1 Hocc2.
  simpl in *; rewrite occ_in_SO_dec_l in Hocc2;
  apply occ_in_SO_implSO2_fwd2 in Hocc1.
  apply occ_in_SO_f in Hocc2.
  destruct Hocc1 as [Hocc1 | Hocc1].
    rewrite occ_in_SO_dec_l in Hocc2.
    destruct Hocc2.
      rewrite at_pred_app_l.
        apply at_pred_occ_id_fwd; auto. firstorder.

        rewrite at_pred_app_l.
          apply IHalpha1 with (cond := cond) (x := x);
            try assumption.
          intros [H1 H2].
          simpl in H.
          rewrite app_length in H.
          lia. inversion Hocc1. lia. auto.

    destruct Hocc1 as [Hl Hr].
    assert (i - length (preds_in alpha1) + length (preds_in alpha1) = i).
      firstorder. 

      destruct (occ_in_SO_f _ _ Hl) as [H1 | H2]. subst.
        contradiction (occ_in_SO_0 _ Hr).

    rewrite <- H. rewrite Nat.add_comm.     
    rewrite at_pred_app_r.
    destruct Hocc2 as [Hocc2 | Hocc2].
      rewrite <- Nat.add_sub_assoc in Hocc2.
      rewrite occ_in_SO_dec_r in Hocc2.
        apply at_pred_occ_id_fwd; try assumption.

        lia. auto.

        apply num_occ_preds_in.

      rewrite occ_in_SO_dec_r in Hocc2.
      apply IHalpha2 with (cond := cond) (x := x); try assumption.
        intros Hocc3.  simpl in Hocc2.        
        rewrite app_length in Hocc2.
        rewrite preds_in_rep_pred in Hocc2; try assumption.
        rewrite <- Nat.add_sub_assoc in Hocc2.
        firstorder.

          apply num_occ_preds_in. auto. firstorder. auto.
          apply occ_in_SO_implSO2. clear -Hocc1. firstorder.
Qed.

Lemma at_pred_occ_rep_pred_allSO : forall (alpha cond : SecOrder) (i : nat) (x : FOvariable)
                                    (P Q : predicate),
  (forall (cond : SecOrder) (i : nat) (x : FOvariable) (Q : predicate),
          FO_frame_condition cond = true ->
          occ_in_SO alpha i ->
          ~ occ_in_SO (replace_pred alpha Q x cond) (identify_fwd alpha Q i) ->
          at_pred (preds_in alpha) i = Q) ->
  FO_frame_condition cond = true ->
  occ_in_SO (allSO P alpha) i ->
  ~ occ_in_SO (replace_pred (allSO P alpha) Q x cond) (identify_fwd (allSO P alpha) Q i) ->
  at_pred (preds_in (allSO P alpha)) i = Q.
Proof.
  intros alpha cond i x P Q IHalpha Hcond Hocc1 Hocc2.
  rewrite rep_pred_allSO in Hocc2.
  simpl preds_in in *.
  case_eq i.
    intros Hi; rewrite Hi in *.
    contradiction (occ_in_SO_0 _ Hocc1).

    intros j Hi; rewrite Hi in *.
    case_eq j.
      intros Hj; rewrite Hj in *.
      simpl in *. destruct (predicate_dec Q P) as [H1 | H1].
      subst. reflexivity.
      rewrite occ_in_SO_dec_l in Hocc2.
      rewrite identify_fwd_0 in Hocc2. simpl in Hocc2.
      destruct Hocc1 as [H2 H3].
      contradiction (Hocc2 (occ_in_SO_allSO_1 _ _)).
      auto. auto.

      intros k Hj; rewrite Hj in *.
      simpl in *. rewrite occ_in_SO_dec_l in Hocc2.     
      destruct (predicate_dec Q P) as [H1 | H1]. subst.
      eapply IHalpha. apply Hcond. eapply occ_in_SO_allSO_rev.
      apply Hocc1. apply Hocc2. 

      eapply (IHalpha cond _ x Q). apply Hcond. eapply occ_in_SO_allSO_rev.
      apply Hocc1. intros H.
      apply Hocc2. apply (occ_in_SO_allSO _ P) in H.
      rewrite Nat.add_1_r. auto. auto.
Qed.

Lemma at_pred_occ_rep_pred_exSO : forall (alpha cond : SecOrder) (i : nat) (x : FOvariable)
                                    (P Q : predicate),
  (forall (cond : SecOrder) (i : nat) (x : FOvariable) (Q : predicate),
          FO_frame_condition cond = true ->
          occ_in_SO alpha i ->
          ~ occ_in_SO (replace_pred alpha Q x cond) (identify_fwd alpha Q i)  ->
          at_pred (preds_in alpha) i = Q) ->
  FO_frame_condition cond = true ->
  occ_in_SO (exSO P alpha) i ->
  ~ occ_in_SO (replace_pred (exSO P alpha) Q x cond) (identify_fwd (exSO P alpha) Q i) ->
  at_pred (preds_in (exSO P alpha)) i = Q.
Proof.
  intros alpha cond i x P Q IHalpha Hcond Hocc1 Hocc2.
  rewrite rep_pred_exSO in Hocc2.
  simpl preds_in in *.
  case_eq i.
    intros Hi; rewrite Hi in *.
    contradiction (occ_in_SO_0 _ Hocc1).

    intros j Hi; rewrite Hi in *.
    case_eq j.
      intros Hj; rewrite Hj in *.
      simpl in *. destruct (predicate_dec Q P) as [H1 | H1].
      subst. reflexivity.
      rewrite occ_in_SO_dec_l in Hocc2.
      rewrite identify_fwd_0 in Hocc2. simpl in Hocc2.
      destruct Hocc1 as [H2 H3].
      contradiction (Hocc2 (occ_in_SO_exSO_1 _ _)).
      auto. auto.

      intros k Hj; rewrite Hj in *.
      simpl in *. rewrite occ_in_SO_dec_l in Hocc2.     
      destruct (predicate_dec Q P) as [H1 | H1]. subst.
      eapply IHalpha. apply Hcond. eapply occ_in_SO_exSO_rev.
      apply Hocc1. apply Hocc2. 

      eapply (IHalpha cond _ x Q). apply Hcond. eapply occ_in_SO_exSO_rev.
      apply Hocc1. intros H.
      apply Hocc2. apply (occ_in_SO_exSO _ P) in H.
      rewrite Nat.add_1_r. auto. auto.
Qed.


Lemma at_pred_occ_rep_pred : forall (alpha cond : SecOrder) (i : nat) (x : FOvariable)
                                    (Q : predicate),
  FO_frame_condition cond = true ->
    occ_in_SO alpha i ->
      ~ occ_in_SO (replace_pred alpha Q x cond) (identify_fwd alpha Q i) ->
        at_pred (preds_in alpha) i = Q.
Proof.
  induction alpha; intros  cond i x Q Hcond Hocc1 Hocc2;
  destruct Q as [Qm]; try destruct f.

    apply at_pred_occ_rep_pred_predSO with (cond := cond) (x := x); assumption.

    contradiction (occ_in_SO_relatSO _ _ _ Hocc1).
    contradiction (occ_in_SO_eqFO _ _ _ Hocc1).

    simpl in *. rewrite occ_in_SO_dec_l in Hocc2.
    rewrite occ_in_SO_allFO in *.
    apply (IHalpha _ _ _ _ Hcond Hocc1 Hocc2). auto.

    simpl in *. rewrite occ_in_SO_dec_l in Hocc2.
    rewrite occ_in_SO_exFO in *.
    apply (IHalpha _ _ _ _ Hcond Hocc1 Hocc2). auto.

    simpl in *. rewrite occ_in_SO_dec_l in Hocc2.
    rewrite occ_in_SO_negSO in *.
    apply (IHalpha _ _ _ _ Hcond Hocc1 Hocc2). auto.

    apply at_pred_occ_rep_pred_conjSO with (cond := cond) (x := x); assumption.
    apply at_pred_occ_rep_pred_disjSO with (cond := cond) (x := x); assumption.
    apply at_pred_occ_rep_pred_implSO with (cond := cond) (x := x); assumption.
    apply at_pred_occ_rep_pred_allSO with (cond := cond) (x := x); assumption.
    apply at_pred_occ_rep_pred_exSO with (cond := cond) (x := x); assumption.
Qed.