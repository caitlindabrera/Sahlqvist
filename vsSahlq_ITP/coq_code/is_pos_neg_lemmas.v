Require Export pv_in is_pos is_neg occ_in_modal.
Require Import Compare_dec Lia.
Require Import ltac_gen.

(* is_pos lemmas *)

Lemma is_pos_occ : forall (phi : Modal) (i : nat),
  is_pos phi i -> occ_in_modal phi i.
Proof.
  intros phi i Hpos. inversion Hpos. assumption.
Qed.

Lemma is_pos_notin : forall (phi : Modal) (i : nat),
  is_pos phi i  -> le i (length (pv_in phi)).
Proof.
  intros phi i H. inversion H.
  apply occ_in_modal_le. auto.
Qed.

Lemma is_pos_atom : forall (q : propvar) (i : nat),
  is_pos (atom q) i -> i = 1. 
Proof.
  intros q i [[H1 H3] H2]. simpl in *.
  firstorder.
Qed.

Lemma is_pos_mneg : forall (psi : Modal) (i : nat),
  is_pos (mneg psi) i -> ~ (is_pos psi i) .
Proof.
  intros psi i [H1 H2] [H3 H4].
  simpl in H2. destruct (is_pos_pre psi i);
  discriminate.
Qed.

Lemma is_pos_mneg2 : forall (psi : Modal) (i : nat),
  ~ is_pos psi i ->
    occ_in_modal psi i ->
      is_pos (mneg psi) i.
Proof.
  intros phi i Hpos Hocc. constructor. apply occ_in_modal_mneg. auto.
  simpl. case_eq (is_pos_pre phi i); intros Hpos2.
  pose proof (occ_pos _ _ Hocc Hpos2). auto.
  reflexivity.
Qed.

Lemma is_pos_mconj_l : forall (phi1 phi2 : Modal) (i : nat),
  is_pos (mconj phi1 phi2) i ->
    ( occ_in_modal phi1 i -> is_pos phi1 i).
Proof.
  intros phi1 phi2 i [H1 H2] Hocc.
  simpl in H2. constructor. auto.
  apply occ_in_modal_le in Hocc. 
  if_then_else_dest_blind; auto.
Qed.

Lemma is_pos_mconj_r : forall (phi1 phi2 : Modal) (i : nat),
  is_pos (mconj phi1 phi2) i ->
    (le (length (pv_in phi1) + 1) i) ->
      is_pos phi2 (i - (length (pv_in phi1))).
Proof.
  intros phi1 phi2 i [H1 H2] Hocc.
  simpl in H2.
  if_then_else_dest_blind; auto. firstorder.
  constructor; auto.
  inversion H1 as [H3 H4].
  constructor. simpl in *. rewrite app_length in H4.
  intros H. firstorder. 
  simpl in H4. rewrite app_length in H4.
  firstorder.
Qed.

Lemma is_pos_mdisj_l : forall (phi1 phi2 : Modal) (i : nat),
  is_pos (mdisj phi1 phi2) i ->
  ( occ_in_modal phi1 i ->  (is_pos phi1 i)).
Proof.
  intros phi1 phi2 i [H1 H2] Hocc.
  simpl in H2. constructor. auto.
  apply occ_in_modal_le in Hocc.
  if_then_else_dest_blind; auto.
Qed.

Lemma is_pos_mdisj_r : forall (phi1 phi2 : Modal) (i : nat),
  is_pos (mdisj phi1 phi2) i ->
    ((length (pv_in phi1) + 1) <= i) ->
      is_pos phi2 (i - (length (pv_in phi1))).
Proof.
  intros phi1 phi2 i [H1 H2] Hocc.
  simpl in H2.
  if_then_else_dest_blind; auto. firstorder.
  constructor; auto.
  inversion H1 as [H3 H4].
  constructor. simpl in *. rewrite app_length in H4.
  intros H. firstorder. 
  simpl in H4. rewrite app_length in H4.
  firstorder.
Qed.

Lemma is_pos_mconj : forall (phi1 phi2 : Modal) (i : nat),
  is_pos (mconj phi1 phi2) i ->
    ( occ_in_modal phi1 i ->  (is_pos phi1 i)) /\
    ((le (length (pv_in phi1) + 1) i) ->
       is_pos phi2 (i - (length (pv_in phi1)))).
Proof.
  intros phi1 phi2 i Hpos.
  pose proof is_pos_mconj_l.
  pose proof is_pos_mconj_r.
  firstorder.
Qed.

Lemma is_pos_mdisj : forall (phi1 phi2 : Modal) (i : nat),
  is_pos (mdisj phi1 phi2) i ->
    ( occ_in_modal phi1 i ->  (is_pos phi1 i)) /\
    (( (length (pv_in phi1) + 1) <= i) ->
       is_pos phi2 (i - (length (pv_in phi1)))).
Proof.
  intros phi1 phi2 i Hpos.
  pose proof is_pos_mconj_l.
  pose proof is_pos_mconj_r.
  firstorder.
Qed.

Lemma is_pos_box : forall (phi : Modal) (i : nat),
  is_pos (box phi) i <-> is_pos phi i.
Proof.
  split; intros [H1 H2];
    (constructor; [apply occ_in_modal_box|]; auto).
Qed.

Lemma is_pos_diam : forall (phi : Modal) (i : nat),
  is_pos (diam phi) i <-> is_pos phi i.
Proof.
  split; intros [H1 H2];
    (constructor; [apply occ_in_modal_diam|]; auto).
Qed.

(* ------------------------------------------------------------ *)

(* is_neg lemmas *)

Lemma is_neg_occ : forall (phi : Modal) (i : nat),
    is_neg phi i -> occ_in_modal phi i.
Proof.
  intros phi i Hpos. inversion Hpos. assumption.
Qed.

Lemma is_neg_mneg : forall (psi : Modal) (i : nat),
  is_neg (mneg psi) i -> ~(is_neg psi i).
Proof.
  intros psi i [H1 H2] [H3 H4].
  simpl in H2. destruct (is_neg_pre psi i);
  discriminate.
Qed.

Lemma is_neg_mneg2 : forall (psi : Modal) (i : nat),
  ~ is_neg psi i ->
    occ_in_modal psi i ->
      is_neg (mneg psi) i.
Proof.
  intros phi i Hpos Hocc. constructor. apply occ_in_modal_mneg. auto.
  simpl. case_eq (is_neg_pre phi i); intros Hpos2.
  pose proof (occ_neg _ _ Hocc Hpos2). auto.
  reflexivity.
Qed.

Lemma is_neg_box : forall (phi : Modal) (i : nat),
    is_neg (box phi) i <-> is_neg phi i.
Proof.
  split; intros [H1 H2];
    (constructor; [apply occ_in_modal_box|]; auto).
Qed.

Lemma is_neg_diam: forall (phi : Modal) (i : nat),
    is_neg (diam phi) i <-> is_neg phi i.
Proof.
  split; intros [H1 H2];
    (constructor; [apply occ_in_modal_diam|]; auto).
Qed.

Lemma is_neg_0 : forall (phi : Modal),
  ~ is_neg phi 0.
Proof. intros phi [H1 H2]. firstorder. Qed.

(* --------------------------------------------------------------- *)

Lemma is_pos_atom2 : forall p,
    is_pos #p 1.
Proof.
  intros p. constructor. apply occ_in_modal_atom2.
  auto.
Qed.

Lemma is_pos_neg_pre_not_tf: forall phi i,
    occ_in_modal phi i ->
    ~ (is_pos_pre phi i = true /\ is_neg_pre phi i = true) /\
    ~ (is_pos_pre phi i = false /\ is_neg_pre phi i = false).
Proof.
  induction phi; intros i Hocc.
  - apply occ_in_modal_atom in Hocc. subst. simpl.
    apply conj; intros [H1 H2]; discriminate.
  - apply (occ_in_modal_mneg phi) in Hocc. simpl.
    destruct (IHphi i Hocc) as [H1 H2].
    destruct (is_pos_pre phi i); destruct (is_neg_pre phi i);
      firstorder.
  - destruct (occ_in_modal_dec phi1 i) as [Hocc1 | Hocc1].
    pose proof (IHphi1 _ Hocc1) as Hocc2. destruct Hocc2 as [H1 H2].
    inversion Hocc1 as [H3 H4]. 
    simpl. if_then_else_dest_blind; auto. 
    apply occ_in_modal_mconj in Hocc. simpl.
    apply occ_in_modal_f in Hocc1. destruct Hocc1 as [H1 | H1].
    subst. inversion Hocc. contradiction.
    if_then_else_dest_blind; auto; firstorder. auto.
  - destruct (occ_in_modal_dec phi1 i) as [Hocc1 | Hocc1].
    pose proof (IHphi1 _ Hocc1) as Hocc2. destruct Hocc2 as [H1 H2].
    inversion Hocc1 as [H3 H4]. 
    simpl. if_then_else_dest_blind; auto. 
    apply occ_in_modal_mdisj in Hocc. simpl.
    apply occ_in_modal_f in Hocc1. destruct Hocc1 as [H1 | H1].
    subst. inversion Hocc. contradiction.
    if_then_else_dest_blind; auto; firstorder. auto.
  - destruct (occ_in_modal_dec phi1 i) as [Hocc1 | Hocc1].
    pose proof (IHphi1 _ Hocc1) as Hocc2. destruct Hocc2 as [H1 H2].
    inversion Hocc1 as [H3 H4].
    simpl. unfold negb. 
    if_then_else_dest_blind; auto; firstorder.
    apply occ_in_modal_f in Hocc1. destruct Hocc1 as [H1 | H1].
    subst. inversion Hocc. contradiction.
    apply Gt.gt_not_le in H1. simpl.
    if_then_else_dest_blind; auto.
    assert (occ_in_modal phi2 (i - length (pv_in phi1))).
      inversion Hocc. simpl in *. rewrite app_length in *. 
      constructor; firstorder.
    apply conj; apply IHphi2; auto.
  - simpl. apply IHphi. apply occ_in_modal_box. auto.
  - simpl. apply IHphi. apply occ_in_modal_diam. auto.
Qed.

Lemma is_pos_neg_pre_not_t: forall phi i,
    occ_in_modal phi i ->
    ~ (is_pos_pre phi i = true /\ is_neg_pre phi i = true).
Proof.
  intros phi i Hocc. apply is_pos_neg_pre_not_tf. auto.
Qed.
  
Lemma is_pos_neg_pre_not_f: forall phi i,
    occ_in_modal phi i ->
    ~ (is_pos_pre phi i = false /\ is_neg_pre phi i = false).
Proof.
  intros phi i Hocc. apply is_pos_neg_pre_not_tf. auto.
Qed. 

Lemma is_pos_neg_not: forall phi i,
    ~ (is_pos phi i /\ is_neg phi i).
Proof.
  intros phi i [[H1 H2] [H4 H3]].
  apply (is_pos_neg_pre_not_t phi i); auto.
Qed.

Lemma is_pos_mconj_l2 : forall phi1 phi2 i,
    is_pos phi1 i ->
    is_pos (phi1 m∧ phi2) i.
Proof.
  intros phi1 phi2 i [H1 H2].
  constructor. apply occ_in_modal_mconj_l. auto.
  simpl. rewrite H2. inversion H1 as [H3 H4].
  if_then_else_dest_blind; auto.
Qed.

Lemma is_pos_mdisj_l2 : forall phi1 phi2 i,
    is_pos phi1 i ->
    is_pos (phi1 m∨ phi2) i.
Proof.
  intros phi1 phi2 i [H1 H2].
  constructor. apply occ_in_modal_mdisj_l. auto.
  simpl. rewrite H2. inversion H1 as [H3 H4].
  if_then_else_dest_blind; auto.
Qed.

Lemma is_pos_mimpl_l2 : forall phi1 phi2 i,
    is_pos phi1 i ->
    ~ is_pos (phi1 m→ phi2) i.
Proof.
  intros phi1 phi2 i [H1 H2] [H5 H6].
  simpl in H6. rewrite H2 in H6. inversion H1  as [H7 H8].
  if_then_else_dest_blind; auto. unfold negb in *. 
  discriminate.
Qed.

Lemma is_pos_mconj_r2 : forall phi1 phi2 i,
    is_pos phi2 (i - length (pv_in phi1)) ->
    is_pos (phi1 m∧ phi2) i.
Proof.
  intros phi1 phi2 i [H1 H2]. pose proof H1 as H1'.
  apply occ_in_modal_mconj_r2 in H1.
  constructor. auto.
  simpl.  rewrite H2. if_then_else_dest_blind; auto.
  inversion H1'. firstorder.
Qed.

Lemma is_pos_mdisj_r2 : forall phi1 phi2 i,
    is_pos phi2 (i - length (pv_in phi1)) ->
    is_pos (phi1 m∨ phi2) i.
Proof.
  intros phi1 phi2 i [H1 H2]. pose proof H1 as H1'.
  apply occ_in_modal_mdisj_r2 in H1.
  constructor. auto.
  simpl.  rewrite H2. if_then_else_dest_blind; auto.
  inversion H1'. firstorder.
Qed.

Lemma is_pos_mimpl_l : forall phi1 phi2 i,
    occ_in_modal phi1 i ->
    ~ is_pos phi1 i ->
    is_pos (phi1 m→ phi2) i.
Proof.
  intros phi1 phi2 i H1 H3.
  constructor. apply occ_in_modal_mimpl_l. auto.
  simpl. inversion H1 as [H2 H4].
  if_then_else_dest_blind; auto; firstorder.
Qed.

Lemma is_pos_mimpl_r : forall phi1 phi2 i,
    is_pos phi2 (i - length (pv_in phi1)) ->
    is_pos (phi1 m→ phi2) i.
Proof.
  intros phi1 phi2 i [H1 H2].
  constructor. apply occ_in_modal_mimpl_r2. auto.
  simpl. unfold negb. if_then_else_dest_blind; auto. 
  firstorder.
Qed.

Lemma is_pos_mimpl_r2 : forall phi1 phi2 i,
    is_pos (phi1 m→ phi2) i ->
    occ_in_modal phi2 (i - length (pv_in phi1)) ->
    is_pos phi2  (i - length (pv_in phi1)).
Proof.
  intros phi1 phi2 i [H1 H2] H3.
  constructor. auto.
  simpl in H2. if_then_else_dest_blind; auto.
  firstorder.
Qed.

Lemma is_pos_dec_occ : forall phi i,
    occ_in_modal phi i -> {is_pos phi i} + {~ is_pos phi i}.
Proof.
  induction phi; intros i Hocc.
  - apply occ_in_modal_atom in Hocc. subst.
    left. apply is_pos_atom2.
  - apply  (occ_in_modal_mneg phi) in Hocc.
    destruct (IHphi _ Hocc) as [H | H].
    right. intros H2. apply is_pos_mneg in H2.
    contradiction.
    left. apply is_pos_mneg2; auto.
  - destruct (occ_in_modal_dec phi1 i) as [H1 | H1].
    destruct (IHphi1 _ H1) as [H2 | H2].
    left. apply is_pos_mconj_l2. auto.
    right. intros H3. apply is_pos_mconj_l in H3.
    contradiction.  auto.
    apply occ_in_modal_mconj in Hocc.
    destruct (IHphi2 _ Hocc) as [H2 | H2]. left.
    apply is_pos_mconj_r2. auto.
    right. intros H3. apply is_pos_mconj_r in H3. auto.
    apply occ_in_modal_f in H1. destruct H1 as [H4| H4].
    subst. firstorder. apply Gt.gt_le_S in H4. firstorder.
    auto.
  - destruct (occ_in_modal_dec phi1 i) as [H1 | H1].
    destruct (IHphi1 _ H1) as [H2 | H2].
    left. apply is_pos_mdisj_l2. auto.
    right. intros H3. apply is_pos_mdisj_l in H3.
    contradiction.  auto.
    apply occ_in_modal_mdisj in Hocc.
    destruct (IHphi2 _ Hocc) as [H2 | H2]. left.
    apply is_pos_mdisj_r2. auto.
    right. intros H3. apply is_pos_mdisj_r in H3. auto.
    apply occ_in_modal_f in H1. destruct H1 as [H4| H4].
    subst. firstorder. apply Gt.gt_le_S in H4. firstorder.
    auto.
  - destruct (occ_in_modal_dec phi1 i) as [H1 | H1].
    destruct (IHphi1 _ H1) as [H2 | H2].
    right. apply is_pos_mimpl_l2. auto.
    left. apply is_pos_mimpl_l; auto.
    apply occ_in_modal_mimpl in Hocc.
    apply IHphi2 in Hocc. destruct Hocc as [H3 | H3].
    left. apply is_pos_mimpl_r. auto.
    right. intros H4. pose proof (is_pos_occ _ _ H4) as H5.
    apply occ_in_modal_mimpl in H5.
    apply is_pos_mimpl_r2 in H4. all : auto.
  - apply (occ_in_modal_box phi) in Hocc.
    apply IHphi in Hocc. destruct Hocc as [H1 | H1].
    left. apply is_pos_box. auto.
    right. intros H2. apply (is_pos_box phi) in H2.
    auto.
  - apply (occ_in_modal_diam phi) in Hocc.
    apply IHphi in Hocc. destruct Hocc as [H1 | H1].
    left. apply is_pos_diam. auto.
    right. intros H2. apply (is_pos_diam phi) in H2.
    auto.
Qed.

Lemma is_pos_dec : forall phi i, {is_pos phi i} + {~ is_pos phi i}.
Proof.
  intros phi i. destruct (occ_in_modal_dec phi i) as [H|H].
  2 : (right; intros H2; apply is_pos_occ in H2; contradiction).
  apply is_pos_dec_occ. auto.
Qed.

Lemma is_pos_neg_pre_f_t : forall (phi : Modal) (i : nat),
  occ_in_modal phi i ->
  (is_pos_pre phi i = false  -> is_neg_pre phi i = true) /\
  (is_pos_pre phi i = true -> is_neg_pre phi i = false).
Proof.
  induction phi; intros i Hocc.
  - apply occ_in_modal_atom in Hocc. subst. simpl. auto.
  - apply (occ_in_modal_mneg phi) in Hocc. simpl.
    apply IHphi in Hocc. destruct Hocc as [H1 H2].
    destruct (is_pos_pre phi i); destruct (is_neg_pre phi  i);
      firstorder.
  - destruct (occ_in_modal_dec phi1 i) as [H1 | H1].
    pose proof (IHphi1 _ H1) as H2. simpl.
    inversion H1 as [H3 H4]. if_then_else_dest_blind; auto.
    contradiction.

    apply occ_in_modal_mconj in Hocc. pose proof (IHphi2 _ Hocc) as H2.
    inversion Hocc as [H3 H4]. simpl. apply occ_in_modal_f in H1.
    destruct H1. subst. contradiction. apply Gt.gt_not_le in H.
    if_then_else_dest_blind; auto. firstorder. auto.
  - destruct (occ_in_modal_dec phi1 i) as [H1 | H1].
    pose proof (IHphi1 _ H1) as H2. simpl.
    inversion H1 as [H3 H4]. if_then_else_dest_blind; auto.
    contradiction.

    apply occ_in_modal_mdisj in Hocc. pose proof (IHphi2 _ Hocc) as H2.
    inversion Hocc as [H3 H4]. simpl. apply occ_in_modal_f in H1.
    destruct H1. subst. contradiction. apply Gt.gt_not_le in H.
    if_then_else_dest_blind; auto. firstorder. auto.
  - destruct (occ_in_modal_dec phi1 i) as [H1 | H1].
    pose proof (IHphi1 _ H1) as H2. simpl.
    inversion H1 as [H3 H4]. unfold negb. 
    if_then_else_dest_blind; auto; firstorder.

    apply occ_in_modal_mimpl in Hocc. pose proof (IHphi2 _ Hocc) as H2.
    inversion Hocc as [H3 H4]. simpl. apply occ_in_modal_f in H1.
    destruct H1. subst. contradiction. apply Gt.gt_not_le in H.
    unfold negb. if_then_else_dest_blind; auto; firstorder. auto.
  - simpl. apply IHphi. apply occ_in_modal_box. auto.
  - simpl. apply IHphi. apply occ_in_modal_diam. auto.
Qed.
  
Lemma is_pos_neg_f_t : forall (phi : Modal) (i : nat),
  occ_in_modal phi i ->
  (~ is_pos phi i  -> is_neg phi i) /\
  (is_pos phi i -> ~ is_neg phi i).
Proof.
  intros phi i Hocc. destruct (is_pos_neg_pre_f_t phi i Hocc) as [H1 H2].
  split; intros H.
  constructor. auto.
  apply H1. case_eq (is_pos_pre phi i); intros H3.
  contradiction (H (occ_pos _ _ Hocc H3)).
  reflexivity.

  intros H3. apply (is_pos_neg_not phi i). auto.
Qed.

Lemma is_pos_neg_iff : forall phi i,
    occ_in_modal phi i ->
    is_pos phi i <-> ~ is_neg phi i.
Proof.
  intros phi i  H. split; intros H2.
  intros H3. apply (is_pos_neg_not phi i).
  auto.
  destruct (is_pos_dec phi i) as [H3 | H3]. auto.
  apply is_pos_neg_f_t in H3. firstorder.
  auto.
Qed.

Lemma is_pos_neg_f : forall (phi : Modal) (i : nat),
  occ_in_modal phi i ->
  (~ is_pos phi i -> is_neg phi i).
Proof.
  intros phi i Hocc Hpos.
  apply is_pos_neg_f_t; assumption.
Qed.

Lemma is_pos_neg_t : forall (phi : Modal) (i : nat),
  (is_pos phi i -> ~is_neg phi i).
Proof.
  intros phi i Hpos.
  pose proof (is_pos_occ _ _ Hpos) as Hocc.
  apply is_pos_neg_f_t; assumption.
Qed.

Lemma is_neg_pos_f : forall (phi : Modal) (i : nat),
  occ_in_modal phi i ->
  (~ is_neg phi i -> is_pos phi i).
Proof.
  intros phi i Hocc Hpos.
  destruct (is_pos_dec phi i) as [H1 | H1]. auto.
  apply is_pos_neg_f in H1; firstorder.
Qed. 

Lemma is_neg_pos_t : forall (phi : Modal) (i : nat),
  (is_neg phi i -> ~ is_pos phi i).
Proof.
  intros phi i H1 H2. apply (is_pos_neg_not phi i).
  auto.
Qed.

(* ------------------------------------------------------- *)

Lemma is_pos_neg_or : forall (phi : Modal) (i : nat),
  occ_in_modal phi i ->
  is_pos phi i  \/ is_neg phi i.
Proof.
  intros phi i H.
  destruct (is_pos_dec phi i). auto.
  right. apply is_pos_neg_f; auto.
Qed.

Lemma is_pos_neg_mimpl_l : forall (phi1 phi2 : Modal) (i : nat),
  is_pos (mimpl phi1 phi2) i ->
  occ_in_modal phi1 i -> is_neg phi1 i.
Proof.
  intros phi1 phi2 i Hpos Hocc.
  destruct (is_pos_neg_or phi1 i Hocc) as [H1|H1].
  apply is_pos_mimpl_l2 with (phi2 := phi2)  in H1.
  contradiction (H1 Hpos). auto.
Qed.

(* ---------------------------------------------------------------------------- *)
(* is_neg lemmas *)

Lemma is_neg_notin : forall (phi : Modal) (i : nat),
  is_neg phi i  -> le i (length (pv_in phi)).
Proof.
  intros phi i H. inversion H.
  apply occ_in_modal_le. auto.
Qed.

Lemma is_neg_atom : forall (q : propvar) (i : nat),
  is_neg (atom q) i -> i = 1. 
Proof.
  intros q i [[H1 H3] H2]. simpl in *.
  firstorder.
Qed.

Lemma is_neg_mconj_l : forall (phi1 phi2 : Modal) (i : nat),
  is_neg (mconj phi1 phi2) i ->
    ( occ_in_modal phi1 i -> is_neg phi1 i).
Proof.
  intros phi1 phi2 i [H1 H2] Hocc.
  simpl in H2. constructor. auto.
  apply occ_in_modal_le in Hocc.
  if_then_else_dest_blind; auto.
Qed.

Lemma is_neg_mconj_r : forall (phi1 phi2 : Modal) (i : nat),
  is_neg (mconj phi1 phi2) i ->
    (le (length (pv_in phi1) + 1) i) ->
      is_neg phi2 (i - (length (pv_in phi1))).
Proof.
  intros phi1 phi2 i [H1 H2] Hocc.
  simpl in H2. if_then_else_dest_blind; simpl in *;
                 auto; firstorder.
  simpl in *. rewrite app_length in *. firstorder.
Qed.

Lemma is_neg_mdisj_l : forall (phi1 phi2 : Modal) (i : nat),
  is_neg (mdisj phi1 phi2) i ->
  ( occ_in_modal phi1 i ->  (is_neg phi1 i)).
Proof.
  intros phi1 phi2 i [H1 H2] Hocc.
  simpl in H2. constructor. auto.
  apply occ_in_modal_le in Hocc.
  if_then_else_dest_blind; auto.
Qed.

Lemma is_neg_mdisj_r : forall (phi1 phi2 : Modal) (i : nat),
  is_neg (mdisj phi1 phi2) i ->
    ((length (pv_in phi1) + 1) <= i) ->
      is_neg phi2 (i - (length (pv_in phi1))).
Proof.
  intros phi1 phi2 i [H1 H2] Hocc.
  simpl in H2. if_then_else_dest_blind; simpl in *;
                 auto; firstorder.
  simpl in *. rewrite app_length in *. firstorder.
Qed.

Lemma is_neg_mconj : forall (phi1 phi2 : Modal) (i : nat),
  is_neg (mconj phi1 phi2) i ->
    ( occ_in_modal phi1 i ->  (is_neg phi1 i)) /\
    ((le (length (pv_in phi1) + 1) i) ->
       is_neg phi2 (i - (length (pv_in phi1)))).
Proof.
  intros phi1 phi2 i Hpos.
  apply conj.
    apply is_neg_mconj_l with (phi2 := phi2); exact Hpos.

    apply is_neg_mconj_r with (phi1 := phi1); exact Hpos.
Qed.

Lemma is_neg_mdisj : forall (phi1 phi2 : Modal) (i : nat),
  is_neg (mdisj phi1 phi2) i ->
    ( occ_in_modal phi1 i ->  (is_neg phi1 i)) /\
    (( (length (pv_in phi1) + 1) <= i) ->
       is_neg phi2 (i - (length (pv_in phi1)))).
Proof.
  intros phi1 phi2 i Hpos.
  apply conj.
    apply is_neg_mdisj_l with (phi2 := phi2); exact Hpos.

    apply is_neg_mdisj_r with (phi1 := phi1); exact Hpos.
Qed.

(* --------------------------------------------------------------- *)
Lemma is_neg_atom2 : forall p,
    ~ is_neg #p 1.
Proof. intros p H. inversion H. firstorder. Qed.

Lemma is_neg_mconj_l2 : forall phi1 phi2 i,
    is_neg phi1 i ->
    is_neg (phi1 m∧ phi2) i.
Proof.
  intros phi1 phi2 i [H1 H2].
  constructor. apply occ_in_modal_mconj_l. auto.
  simpl. rewrite H2. inversion H1 as [H3 H4].
  if_then_else_dest_blind; auto.
Qed.

Lemma is_neg_mdisj_l2 : forall phi1 phi2 i,
    is_neg phi1 i ->
    is_neg (phi1 m∨ phi2) i.
Proof.
  intros phi1 phi2 i [H1 H2].
  constructor. apply occ_in_modal_mdisj_l. auto.
  simpl. rewrite H2. inversion H1 as [H3 H4].
  if_then_else_dest_blind; auto.
Qed.

Lemma is_neg_mimpl_l2 : forall phi1 phi2 i,
    is_neg phi1 i ->
    ~ is_neg (phi1 m→ phi2) i.
Proof.
  intros phi1 phi2 i [H1 H2] [H5 H6].
  simpl in H6. rewrite H2 in H6. inversion H1  as [H7 H8].
  if_then_else_dest_blind; auto. unfold negb in *.
  firstorder.
Qed.

Lemma is_neg_mconj_r2 : forall phi1 phi2 i,
    is_neg phi2 (i - length (pv_in phi1)) ->
    is_neg (phi1 m∧ phi2) i.
Proof.
  intros phi1 phi2 i [H1 H2]. pose proof H1 as H1'.
  apply occ_in_modal_mconj_r2 in H1.
  constructor. auto.
  simpl.  rewrite H2. if_then_else_dest_blind; auto.
  firstorder.
Qed.

Lemma is_neg_mdisj_r2 : forall phi1 phi2 i,
    is_neg phi2 (i - length (pv_in phi1)) ->
    is_neg (phi1 m∨ phi2) i.
Proof.
  intros phi1 phi2 i [H1 H2]. pose proof H1 as H1'.
  apply occ_in_modal_mdisj_r2 in H1.
  constructor. auto.
  simpl.  rewrite H2. if_then_else_dest_blind; firstorder.
Qed.

Lemma is_neg_mimpl_l : forall phi1 phi2 i,
    occ_in_modal phi1 i ->
    ~ is_neg phi1 i ->
    is_neg (phi1 m→ phi2) i.
Proof.
  intros phi1 phi2 i H1 H3.
  constructor. apply occ_in_modal_mimpl_l. auto.
  simpl. inversion H1 as [H2 H4].
  if_then_else_dest_blind; firstorder.
Qed.

Lemma is_neg_mimpl_r : forall phi1 phi2 i,
    is_neg phi2 (i - length (pv_in phi1)) ->
    is_neg (phi1 m→ phi2) i.
Proof.
  intros phi1 phi2 i [H1 H2].
  constructor. apply occ_in_modal_mimpl_r2. auto.
  simpl. if_then_else_dest_blind; firstorder.
Qed.

Lemma is_neg_mimpl_r2 : forall phi1 phi2 i,
    is_neg (phi1 m→ phi2) i ->
    occ_in_modal phi2 (i - length (pv_in phi1)) ->
    is_neg phi2  (i - length (pv_in phi1)).
Proof.
  intros phi1 phi2 i [H1 H2] H3.
  constructor. auto. simpl in *.
  if_then_else_dest_blind; firstorder.
Qed.

Lemma is_neg_dec_occ : forall phi i,
    occ_in_modal phi i -> {is_neg phi i} + {~ is_neg phi i}.
Proof.
  induction phi; intros i Hocc.
  - apply occ_in_modal_atom in Hocc. subst.
    right. apply is_neg_atom2.
  - apply  (occ_in_modal_mneg phi) in Hocc.
    destruct (IHphi _ Hocc) as [H | H].
    right. intros H2. apply is_neg_mneg in H2.
    contradiction.
    left. apply is_neg_mneg2; auto.
  - destruct (occ_in_modal_dec phi1 i) as [H1 | H1].
    destruct (IHphi1 _ H1) as [H2 | H2].
    left. apply is_neg_mconj_l2. auto.
    right. intros H3. apply is_neg_mconj_l in H3.
    contradiction.  auto.
    apply occ_in_modal_mconj in Hocc.
    destruct (IHphi2 _ Hocc) as [H2 | H2]. left.
    apply is_neg_mconj_r2. auto.
    right. intros H3. apply is_neg_mconj_r in H3. auto.
    apply occ_in_modal_f in H1. destruct H1 as [H4| H4].
    subst. firstorder. apply Gt.gt_le_S in H4. firstorder.
    auto.
  - destruct (occ_in_modal_dec phi1 i) as [H1 | H1].
    destruct (IHphi1 _ H1) as [H2 | H2].
    left. apply is_neg_mdisj_l2. auto.
    right. intros H3. apply is_neg_mdisj_l in H3.
    contradiction.  auto.
    apply occ_in_modal_mdisj in Hocc.
    destruct (IHphi2 _ Hocc) as [H2 | H2]. left.
    apply is_neg_mdisj_r2. auto.
    right. intros H3. apply is_neg_mdisj_r in H3. auto.
    apply occ_in_modal_f in H1. destruct H1 as [H4| H4].
    subst. firstorder. apply Gt.gt_le_S in H4. firstorder.
    auto.
  - destruct (occ_in_modal_dec phi1 i) as [H1 | H1].
    destruct (IHphi1 _ H1) as [H2 | H2].
    right. apply is_neg_mimpl_l2. auto.
    left. apply is_neg_mimpl_l; auto.
    apply occ_in_modal_mimpl in Hocc.
    apply IHphi2 in Hocc. destruct Hocc as [H3 | H3].
    left. apply is_neg_mimpl_r. auto.
    right. intros H4. pose proof (is_neg_occ _ _ H4) as H5.
    apply occ_in_modal_mimpl in H5.
    apply is_neg_mimpl_r2 in H4. all : auto.
  - apply (occ_in_modal_box phi) in Hocc.
    apply IHphi in Hocc. destruct Hocc as [H1 | H1].
    left. apply is_neg_box. auto.
    right. intros H2. apply (is_neg_box phi) in H2.
    auto.
  - apply (occ_in_modal_diam phi) in Hocc.
    apply IHphi in Hocc. destruct Hocc as [H1 | H1].
    left. apply is_neg_diam. auto.
    right. intros H2. apply (is_neg_diam phi) in H2.
    auto.
Qed.

Lemma is_neg_dec : forall phi i, {is_neg phi i} + {~ is_neg phi i}.
Proof.
  intros phi i. destruct (occ_in_modal_dec phi i) as [H|H].
  2 : (right; intros H2; apply is_neg_occ in H2; contradiction).
  apply is_neg_dec_occ. auto.
Qed.

Lemma is_neg_pos_pre_f_t : forall (phi : Modal) (i : nat),
  occ_in_modal phi i ->
  (is_neg_pre phi i = false  -> is_pos_pre phi i = true) /\
  (is_neg_pre phi i = true -> is_pos_pre phi i = false).
Proof.
  intros phi i Hocc.
  case_eq (is_pos_pre phi i); intros H2; split; try auto;
    intros H3; apply is_pos_neg_pre_f_t in H2; try rewrite H2 in *; auto.
Qed.

Lemma is_neg_pos_f_t : forall (phi : Modal) (i : nat),
  occ_in_modal phi i ->
  (~ is_neg phi i  -> is_pos phi i) /\
  (is_neg phi i -> ~ is_pos phi i).
Proof.
  intros phi i Hocc.
  destruct (is_pos_neg_f_t phi i Hocc) as [H1 H2].
  destruct (is_pos_dec phi i) as [H3 | H3];
    split; intros H4; try auto.
  contradiction (is_pos_neg_not phi i). auto.
  apply H1 in H3. contradiction.
Qed.

Lemma is_neg_pos_iff : forall phi i,
    occ_in_modal phi i ->
    is_neg phi i <-> ~ is_pos phi i.
Proof.
  intros phi i  H. split; intros H2.
  intros H3. apply (is_pos_neg_not phi i).
  auto.
  destruct (is_neg_dec phi i) as [H3 | H3]. auto.
  apply is_neg_pos_f_t in H3. firstorder.
  auto.
Qed.

(* ------------------------------------------------------- *)

Lemma is_neg_pos_mimpl_l : forall (phi1 phi2 : Modal) (i : nat),
  is_neg (mimpl phi1 phi2) i ->
  occ_in_modal phi1 i -> is_pos phi1 i.
Proof.
  intros phi1 phi2 i Hpos Hocc.
  destruct (is_pos_neg_or phi1 i Hocc) as [H1|H1]. auto.
  apply is_neg_mimpl_l2 with (phi2 := phi2)  in H1.
  firstorder.
Qed.