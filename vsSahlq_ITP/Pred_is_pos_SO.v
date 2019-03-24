Require Export med_mods is_pos_neg_SO_lemmas.
Require Import Modal_syntax p_is_pos ST.

Definition Pred_is_pos_SO (alpha : SecOrder) (P : predicate) : Prop :=
Pred_in_SO alpha P  /\
(forall i : nat, occ_in_SO alpha i -> P = at_pred (preds_in alpha) i -> is_pos_SO alpha i).

(*
Inductive Pred_is_pos_SO (alpha : SecOrder) (P : predicate) : Prop :=
| Pred_is_pos_y : Pred_in_SO alpha P  ->
    (forall i : nat, occ_in_SO alpha i -> P = at_pred (preds_in alpha) i -> is_pos_SO alpha i) -> Pred_is_pos_SO alpha P.
 *)

Lemma Pred_is_pos__in_SO : forall alpha P,
  Pred_is_pos_SO alpha P -> Pred_in_SO alpha P.
Proof. firstorder. Qed.

Lemma Pred_is_pos_SO_allFO  : forall (alpha : SecOrder) (x : FOvariable) (P : predicate),
  Pred_is_pos_SO (allFO x alpha) P <-> Pred_is_pos_SO alpha P.
Proof.
  intros alpha x P; split; intros [H1 H2];
  constructor. erewrite Pred_in_SO_allFO. apply H1.
  intros i H3 H4. rewrite <- is_pos_SO_allFO.
  apply H2. apply occ_in_SO_allFO. auto.
  auto.

  rewrite <- Pred_in_SO_allFO. auto.
  intros i H3 H4. rewrite is_pos_SO_allFO. apply H2.
  erewrite <- occ_in_SO_allFO. apply H3. auto.
Qed.

Lemma Pred_is_pos_SO_exFO  : forall (alpha : SecOrder) (x : FOvariable) (P : predicate),
  Pred_is_pos_SO (exFO x alpha) P <-> Pred_is_pos_SO alpha P.
Proof.
  intros alpha x P; split; intros [H1 H2];
  constructor. erewrite Pred_in_SO_exFO. apply H1.
  intros i H3 H4. rewrite <- is_pos_SO_exFO.
  apply H2. apply occ_in_SO_exFO. auto.
  auto.

  rewrite <- Pred_in_SO_exFO. auto.
  intros i H3 H4. rewrite is_pos_SO_exFO. apply H2.
  erewrite <- occ_in_SO_exFO. apply H3. auto.
Qed.

Lemma Pred_is_pos_SO_conjSO_l : forall (alpha1 alpha2 : SecOrder) 
                                    (P : predicate),
  Pred_in_SO alpha1 P ->
  Pred_is_pos_SO (conjSO alpha1 alpha2) P ->
  Pred_is_pos_SO alpha1 P.
Proof.
  intros alpha1 alpha2 P Hpocc [Hpos1 Hpos2]. constructor.
  auto. intros i Hocc Hat. pose proof Hocc as H.
  eapply or_introl in Hocc. eapply occ_in_SO_conjSO2_rev in Hocc.
  apply Hpos2 in Hocc. apply (is_pos_SO_conjSO_l alpha1 alpha2 i) in Hocc;
                         auto. simpl. rewrite at_pred_app_l; firstorder.
Qed.

Lemma Pred_is_pos_SO_conjSO_r : forall (alpha1 alpha2 : SecOrder) 
                                    (P : predicate),
  Pred_in_SO alpha2 P  ->
  Pred_is_pos_SO (conjSO alpha1 alpha2) P ->
  Pred_is_pos_SO alpha2 P.
Proof.
  intros alpha1 alpha2 P Hpocc [Hpos1 Hpos2].
  constructor. auto. intros i Hocc Hat.
  assert (i = (i + length (preds_in alpha1) - length (preds_in alpha1)))
    as Hass. firstorder.
  rewrite Hass in *. 
  apply is_pos_SO_conjSO_r. intros H2.
  rewrite PeanoNat.Nat.add_sub in Hocc.
  all : try (solve [firstorder]).
  apply Hpos2.
  apply occ_in_SO_conjSO2_rev. right. auto.
  simpl. rewrite PeanoNat.Nat.add_comm. rewrite at_pred_app_r.
  rewrite PeanoNat.Nat.add_sub in Hat. auto.
  destruct i. simpl in *. rewrite PeanoNat.Nat.sub_diag in Hocc.
  all : firstorder.
Qed.

Lemma Pred_is_pos_SO_disjSO_l : forall (alpha1 alpha2 : SecOrder) 
                                    (P : predicate),
  Pred_in_SO alpha1 P ->
  Pred_is_pos_SO (disjSO alpha1 alpha2) P ->
  Pred_is_pos_SO alpha1 P.
Proof.
  intros alpha1 alpha2 P Hpocc [Hpos1 Hpos2]. constructor.
  auto. intros i Hocc Hat. pose proof Hocc as H.
  eapply or_introl in Hocc. eapply occ_in_SO_disjSO2_rev in Hocc.
  apply Hpos2 in Hocc. apply (is_pos_SO_disjSO_l alpha1 alpha2 i) in Hocc;
                         auto. simpl. rewrite at_pred_app_l; firstorder.
Qed.

Lemma Pred_is_pos_SO_disjSO_r : forall (alpha1 alpha2 : SecOrder) 
                                    (P : predicate),
  Pred_in_SO alpha2 P  ->
  Pred_is_pos_SO (disjSO alpha1 alpha2) P ->
  Pred_is_pos_SO alpha2 P.
Proof.
  intros alpha1 alpha2 P Hpocc [Hpos1 Hpos2].
  constructor. auto. intros i Hocc Hat.
  assert (i = (i + length (preds_in alpha1) - length (preds_in alpha1)))
    as Hass. firstorder.
  rewrite Hass in *. 
  apply is_pos_SO_disjSO_r. intros H2.
  rewrite PeanoNat.Nat.add_sub in Hocc.
  all : try (solve [firstorder]).
  apply Hpos2.
  apply occ_in_SO_disjSO2_rev. right. auto.
  simpl. rewrite PeanoNat.Nat.add_comm. rewrite at_pred_app_r.
  rewrite PeanoNat.Nat.add_sub in Hat. auto.
  destruct i. simpl in *. rewrite PeanoNat.Nat.sub_diag in Hocc.
  all : firstorder.
Qed.

Lemma Pred_is_pos_SO_allSO : forall (alpha : SecOrder) (P Q : predicate),
Pred_in_SO alpha P ->
Pred_is_pos_SO (allSO Q alpha) P -> Pred_is_pos_SO alpha P.
Proof.
  intros alpha P Q Hpocc [H1 H2]; constructor. firstorder.
  intros i Hocc Hat. eapply is_pos_SO_allSO. auto. apply H2.
  firstorder. all : try solve [simpl; firstorder].
  simpl. destruct i; firstorder.
Qed.

Lemma Pred_is_pos_SO_exSO : forall (alpha : SecOrder) (P Q : predicate),
Pred_in_SO alpha P ->
Pred_is_pos_SO (exSO Q alpha) P -> Pred_is_pos_SO alpha P.
Proof.
  intros alpha P Q Hpocc [H1 H2]; constructor. firstorder.
  intros i Hocc Hat. eapply is_pos_SO_exSO. auto.
  apply H2. firstorder. all : try solve [simpl; firstorder].
  simpl. destruct i; firstorder.
Qed.

Lemma p_is_pos__SO : forall (phi : Modal) (x : FOvariable)
                            (p : propvar),
  p_is_pos phi p <-> Pred_is_pos_SO (ST phi x) (ST_pv p).
Proof.
  intros phi x p; split; intros [H1 H2].
  constructor. apply p_occ__ST. auto.
  intros i Hocc Hat. apply is_pos__ST. apply H2.
  rewrite occ_in_ST. apply Hocc.
  rewrite <- at_pv_ST_nocon in Hat.
  apply ST_pv_inj in Hat. auto.
  
  constructor. apply p_occ__ST in H1. auto.
  intros i Hocc Hat. apply (is_pos__ST phi x i). apply H2.
  rewrite occ_in_ST in Hocc. apply Hocc.
  rewrite <- at_pv_ST_nocon. subst. auto.
Qed.

Lemma Pred_is_pos_SO_allSO_neq : forall alpha P Q,
  ~ P = Q ->
  Pred_is_pos_SO (allSO P alpha) Q ->
  Pred_is_pos_SO alpha Q.
Proof.
  intros alpha P Q Hneq [H1 H2].
  inversion H1. subst. contradiction.
  constructor. auto.
  intros i Hocc Hat. simpl in *.
  assert (occ_in_SO (allSO P alpha) (S i)) as Hpocc. apply occ_in_SO_allSO. auto.
  specialize (H2 _ Hpocc). simpl in *. destruct i. firstorder.
  rewrite PeanoNat.Nat.sub_0_r in *. apply H2 in Hat. 
  constructor. auto. inversion Hat. simpl in *. destruct P. auto.
Qed.

Lemma Pred_is_pos_SO_exSO_neq : forall alpha P Q,
  ~ P = Q ->
  Pred_is_pos_SO (exSO P alpha) Q ->
  Pred_is_pos_SO alpha Q.
Proof.
  intros alpha P Q Hneq [H1 H2].
  inversion H1. subst. contradiction.
  constructor. auto.
  intros i Hocc Hat. simpl in *.
  assert (occ_in_SO (exSO P alpha) (S i)) as Hpocc. apply occ_in_SO_exSO. auto.
  specialize (H2 _ Hpocc). simpl in *. destruct i. firstorder.
  rewrite PeanoNat.Nat.sub_0_r in *. apply H2 in Hat. 
  constructor. auto. inversion Hat. simpl in *. destruct P. auto.
Qed.