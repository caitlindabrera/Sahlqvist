Require Export base_mods preds_in FO_frame_condition Pred_in_SO.

Definition occ_in_SO (alpha : SecOrder) (i : nat) : Prop :=
 i <> 0 /\ le i (length (preds_in alpha)).

(*
Inductive occ_in_SO (alpha : SecOrder) (i : nat) : Prop :=
| occ_SO : i <> 0 -> le i (length (preds_in alpha)) ->
           occ_in_SO alpha i.
*)

Lemma occ_in_SO_dec : forall alpha i,
    {occ_in_SO alpha i} + {~ occ_in_SO alpha i}.
Proof.
  intros alpha i. destruct i. right.
  intros H. firstorder.
  destruct (Compare_dec.le_dec (S i) (length (preds_in alpha))).
  left. constructor;  firstorder.
  right. intros H. firstorder.
Qed.

Lemma occ_in_SO_dec_l : forall {T : Type} alpha i (x y : T),
  occ_in_SO alpha i ->
  (if occ_in_SO_dec alpha i then x else y) = x.
Proof.
  intros T alpha i x y H.
  destruct (occ_in_SO_dec alpha i) as [H1 | H1].
  auto. contradiction.
Qed.

Lemma occ_in_SO_dec_r : forall {T : Type} alpha i (x y : T),
  ~ occ_in_SO alpha i ->
  (if occ_in_SO_dec alpha i then x else y) = y.
Proof.
  intros T alpha i x y H.
  destruct (occ_in_SO_dec alpha i) as [H1 | H1].
  contradiction. auto.
Qed.

Lemma occ_in_SO_allFO : forall (alpha : SecOrder) (x : FOvariable)
                                  (i : nat),
  occ_in_SO (allFO x alpha) i <-> occ_in_SO alpha i.
Proof.
  intros. split; intros HH; destruct HH as [HH1 HH2];
            constructor; auto.
Qed.

Lemma occ_in_SO_exFO : forall (alpha : SecOrder) (x : FOvariable)
                                  (i : nat),
  occ_in_SO (exFO x alpha) i <-> occ_in_SO alpha i.
Proof.
  intros. split; intros HH; destruct HH as [HH1 HH2];
            constructor; auto.
Qed.

Lemma occ_in_SO_negSO : forall (alpha : SecOrder) (i : nat),
  occ_in_SO (negSO alpha) i <-> occ_in_SO alpha i.
Proof.
  intros. split; intros HH; destruct HH as [HH1 HH2];
            constructor; auto.
Qed.

Lemma occ_in_SO_conjSO2_fwd : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_SO (conjSO alpha1 alpha2) i  ->
    occ_in_SO alpha1 i \/ 
      occ_in_SO alpha2 (i - (length(preds_in alpha1))).
Proof.
  intros ? ? ? [H1 H2]. simpl in H2.
  rewrite app_length in H2.
  destruct (le_le_S_dec i (length (preds_in alpha1)))
    as [H3 | H4].
  left. constructor; auto.
  right. constructor; firstorder.
Qed.

Lemma occ_in_SO_conjSO2_fwd2 : forall (alpha1 alpha2 : SecOrder) (i : nat),
    occ_in_SO (conjSO alpha1 alpha2) i ->
    occ_in_SO alpha1 i  \/
    (~ occ_in_SO alpha1 i  /\
       occ_in_SO alpha2 (i - length (preds_in alpha1))).
Proof.
  intros alpha1 alpha2 i Hocc.
  pose proof (occ_in_SO_conjSO2_fwd _ _ _ Hocc) as H.
  firstorder.
Qed.

Lemma occ_in_SO_conjSO2_rev : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_SO alpha1 i \/ 
    occ_in_SO alpha2 (i - (length(preds_in alpha1))) ->
      occ_in_SO (conjSO alpha1 alpha2) i .
Proof.
  intros. destruct H as [H | H];
            destruct H as [H1 H2]; constructor; try (solve [firstorder]);
              simpl; rewrite app_length; firstorder.
Qed.

Lemma occ_in_SO_conjSO2 : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_SO (conjSO alpha1 alpha2) i <->
    occ_in_SO alpha1 i \/ 
      occ_in_SO alpha2 (i - (length(preds_in alpha1))).
Proof.
  intros. split; intros H;
    [apply occ_in_SO_conjSO2_fwd | apply occ_in_SO_conjSO2_rev];
    assumption.
Qed.

Lemma occ_in_SO_disjSO2_fwd : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_SO (disjSO alpha1 alpha2) i  ->
    occ_in_SO alpha1 i \/ 
      occ_in_SO alpha2 (i - (length(preds_in alpha1))).
Proof.
  intros ? ? ? [H1 H2]. simpl in H2.
  rewrite app_length in H2.
  destruct (le_le_S_dec i (length (preds_in alpha1)))
    as [H3 | H4].
  left. constructor; auto.
  right. constructor; firstorder.
Qed.

Lemma occ_in_SO_disjSO2_fwd2 : forall (alpha1 alpha2 : SecOrder) (i : nat),
    occ_in_SO (disjSO alpha1 alpha2) i ->
    occ_in_SO alpha1 i  \/
    (~ occ_in_SO alpha1 i  /\
       occ_in_SO alpha2 (i - length (preds_in alpha1))).
Proof.
  intros alpha1 alpha2 i Hocc.
  pose proof (occ_in_SO_disjSO2_fwd _ _ _ Hocc) as H.
  firstorder.
Qed.

Lemma occ_in_SO_disjSO2_rev : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_SO alpha1 i \/ 
    occ_in_SO alpha2 (i - (length(preds_in alpha1))) ->
      occ_in_SO (disjSO alpha1 alpha2) i .
Proof.
  intros. destruct H as [H | H];
            destruct H as [H1 H2]; constructor; try (solve [firstorder]);
              simpl; rewrite app_length; firstorder.
Qed.

Lemma occ_in_SO_disjSO2 : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_SO (disjSO alpha1 alpha2) i <->
    occ_in_SO alpha1 i \/ 
      occ_in_SO alpha2 (i - (length(preds_in alpha1))).
Proof.
  intros. split; intros H;
    [apply occ_in_SO_disjSO2_fwd | apply occ_in_SO_disjSO2_rev];
    assumption.
Qed.

Lemma occ_in_SO_implSO2_fwd : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_SO (implSO alpha1 alpha2) i  ->
    occ_in_SO alpha1 i \/ 
      occ_in_SO alpha2 (i - (length(preds_in alpha1))).
Proof.
  intros ? ? ? [H1 H2]. simpl in H2.
  rewrite app_length in H2.
  destruct (le_le_S_dec i (length (preds_in alpha1)))
    as [H3 | H4].
  left. constructor; auto.
  right. constructor; firstorder.
Qed.

Lemma occ_in_SO_implSO2_fwd2 : forall (alpha1 alpha2 : SecOrder) (i : nat),
    occ_in_SO (implSO alpha1 alpha2) i ->
    occ_in_SO alpha1 i  \/
    (~ occ_in_SO alpha1 i  /\
       occ_in_SO alpha2 (i - length (preds_in alpha1))).
Proof.
  intros alpha1 alpha2 i Hocc.
  pose proof (occ_in_SO_implSO2_fwd _ _ _ Hocc) as H.
  firstorder.
Qed.

Lemma occ_in_SO_implSO2_rev : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_SO alpha1 i \/ 
    occ_in_SO alpha2 (i - (length(preds_in alpha1))) ->
      occ_in_SO (implSO alpha1 alpha2) i .
Proof.
  intros. destruct H as [H | H];
            destruct H as [H1 H2]; constructor; try (solve [firstorder]);
              simpl; rewrite app_length; firstorder.
Qed.

Lemma occ_in_SO_implSO2 : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_SO (implSO alpha1 alpha2) i <->
    occ_in_SO alpha1 i \/ 
      occ_in_SO alpha2 (i - (length(preds_in alpha1))).
Proof.
  intros. split; intros H;
    [apply occ_in_SO_implSO2_fwd | apply occ_in_SO_implSO2_rev];
    assumption.
Qed.

Lemma occ_in_SO_relatSO : forall (x y : FOvariable) (i : nat),
  ~ occ_in_SO (relatSO x y) i.
Proof. intros ? ? i H. firstorder. Qed.

Lemma occ_in_SO_eqFO : forall (x y : FOvariable) (i : nat),
  ~ occ_in_SO (eqFO x y) i.
Proof. intros ? ? ? H. firstorder. Qed.

Lemma  occ_in_SO_predSO : forall (P : predicate) (x : FOvariable) (i : nat),
  occ_in_SO (predSO P x) i -> i = 1.
Proof.  intros P x i [H1 H2]. simpl in *. firstorder. Qed.

Lemma occ_in_SO_allSO : forall alpha P i,
    occ_in_SO alpha i ->
    occ_in_SO (allSO P alpha) (S i).
Proof.
  intros alpha P i [H1 H2].
  constructor; simpl; firstorder.
Qed.

Lemma occ_in_SO_allSO_rev : forall alpha P k,
occ_in_SO (allSO P alpha) (S (S k)) ->
occ_in_SO alpha (S k).
Proof.
  intros alpha P k [H1 H2].
  constructor. auto.
  simpl in *. firstorder.
Qed.

Lemma occ_in_SO_exSO_rev : forall alpha P k,
occ_in_SO (exSO P alpha) (S (S k)) ->
occ_in_SO alpha (S k).
Proof.
  intros alpha P k [H1 H2].
  constructor. auto.
  simpl in *. firstorder.
Qed.

Lemma occ_in_SO_exSO : forall alpha P i,
    occ_in_SO alpha i ->
    occ_in_SO (exSO P alpha) (S i).
Proof.
  intros alpha P i [H1 H2].
  constructor; simpl; firstorder.
Qed.

Lemma occ_in_SO_allSO_1 : forall alpha P,
  occ_in_SO (allSO P alpha) 1.
Proof.
  intros alpha P. constructor.
  auto. cbn. lia.
Qed.

Lemma occ_in_SO_exSO_1 : forall alpha P,
  occ_in_SO (exSO P alpha) 1.
Proof.
  intros alpha P. constructor.
  auto. cbn. lia.
Qed.

Lemma occ_in_SO_0 : forall (alpha : SecOrder),
  ~ occ_in_SO alpha 0.
Proof. intros alpha H. firstorder. Qed.


Lemma occ_in_SO_le3 : forall (alpha : SecOrder) (i n : nat),
  occ_in_SO alpha (i - n)  ->  n <= i.
Proof.
  intros alpha i n Hocc. destruct Hocc as [H1 H2]. firstorder.
Qed.

Lemma occ_in_SO_le : forall alpha i,
    occ_in_SO alpha i ->
    i <= (length (preds_in alpha)).
Proof.
  intros alpha i H. firstorder. 
Qed.

Lemma occ_in_SO_le_minus : forall alpha1 alpha2 i,
    occ_in_SO alpha2 (i - length (preds_in alpha1)) ->
    ~ i <= (length (preds_in alpha1)).
Proof.
  intros alpha1 alpha2 i Hocc H.
  inversion Hocc as [H1 H2]. firstorder.
Qed.

Lemma occ_in_SO_predSO_FOv : forall (P : predicate) (x y : FOvariable)
                                (i : nat),
  occ_in_SO (predSO P x) i <-> occ_in_SO (predSO P y) i.
Proof. split; intros [H1 H2]; constructor; auto. Qed.

Lemma FO_frame_condition_occ_in_SO : forall (alpha : SecOrder) ( i : nat),
  FO_frame_condition alpha = true ->
    ~ occ_in_SO alpha i.
Proof.
  intros alpha i Hun [H1 H2]. rewrite FO_frame_condition_preds_in in H2;
                                firstorder.
Qed.

Lemma occ_in_SO_f : forall (alpha : SecOrder) (n : nat),
  ~ occ_in_SO alpha n -> n = 0 \/ n > (length (preds_in alpha)).
Proof.
  intros alpha n Hocc. destruct n.
  left. auto.
  right. apply not_le. intros H.
  assert (S n <> 0) as H2. auto. firstorder.
Qed.

Lemma occ_in_SO_excess : forall (alpha : SecOrder) (n : nat),
  n <> 0 ->
   ~ occ_in_SO alpha (n + length (preds_in alpha)).
Proof. intros alpha n Hbeq [H1 H2]. firstorder. Qed.

Lemma occ_in_SO_preds_in : forall (alpha : SecOrder) (n : nat),
  n <> 0 ->
  ~ occ_in_SO alpha ((length (preds_in alpha)) + n).
Proof.
  intros alpha n Hbeq H. rewrite Nat.add_comm in H.
  apply occ_in_SO_excess in H; auto.
Qed.