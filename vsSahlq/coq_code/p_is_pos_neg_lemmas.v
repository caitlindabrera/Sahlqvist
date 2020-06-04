Require Export p_is_pos p_is_neg is_pos_neg_lemmas.
Require Import Lia.


(* p_is_pos lemmas *)

Lemma p_is_pos_notin : forall (phi : Modal) (p : propvar),
  p_is_pos phi p -> pv_in_modal phi p.
Proof.
  intros phi p H_pos.  inversion H_pos as [Hpv Hpos]. 
  destruct (pv_in_modal_dec phi p) as [Hdec | Hdec].
  assumption. contradiction.
Qed.

Lemma p_is_pos_atom : forall (p q : propvar),
  p_is_pos (atom q) p -> p = q.
Proof.
  intros p q [Hpv Hpos].
  apply pv_in_modal_atom. assumption.
Qed.
    
Lemma p_is_pos_mneg : forall (phi : Modal) (p : propvar),
    p_is_pos (mneg phi) p -> ~ p_is_pos phi p .
Proof.
  intros phi q [Hpv Hpos] [Hpv2 Hpos2].
  (* Left it here *)
  simpl in *. apply  pv_in_modal_occ_in_modal in Hpv2.
  destruct Hpv2 as [i [H1 H2]].
  pose proof (Hpos2 i H1 H2).
  apply occ_in_modal_mneg in H1.
  pose proof (Hpos i H1 H2) as H0.
  apply is_pos_mneg in H0. auto.
Qed.

Lemma p_is_pos_mconj2l: forall (phi1 phi2 : Modal) (p : propvar),
  p_is_pos (mconj phi1 phi2) p -> 
    pv_in_modal phi1 p ->
      p_is_pos phi1 p.
Proof.
  intros phi1 phi2 p Hpos Hocc.
  constructor. auto.
  inversion Hpos as [H1 H2].
  intros i Hocc2 Hat.
  pose proof (occ_in_modal_mconj_l phi1 phi2 i Hocc2) as Hocc3.
  apply H2 in Hocc3. apply is_pos_mconj_l in Hocc3; auto.
  simpl. rewrite at_pv_app_l. auto.
  apply occ_in_modal_le. auto.
Qed.

Lemma p_is_pos_mconj2r: forall (phi1 phi2 : Modal) (p : propvar),
  p_is_pos (mconj phi1 phi2) p -> 
    pv_in_modal phi2 p ->
      p_is_pos phi2 p.
Proof.
  intros phi1 phi2 p Hpos Hpocc.
  destruct Hpos as [Hpocct Hpoccf].
  constructor. assumption.
  intros i Hocc Hat.
  assert (i = (i + (length (pv_in phi1)) - (length (pv_in phi1)))) as Heq.
    firstorder.
  rewrite Heq in *. 
  apply is_pos_mconj_r. apply Hpoccf.
  apply occ_in_modal_mconj_r2.
  auto.
  simpl. rewrite PeanoNat.Nat.add_comm. rewrite at_pv_app_r.
  rewrite PeanoNat.Nat.add_sub in Hat. auto.
  destruct i. rewrite PeanoNat.Nat.add_sub in Hocc.
  contradiction (occ_in_modal_0 _ _ Hocc). all: try auto.
  destruct i. rewrite PeanoNat.Nat.add_sub in Hocc.
  contradiction (occ_in_modal_0 _ _ Hocc). all: try auto.
  lia.
Qed.

Lemma p_is_pos_mdisj2l: forall (phi1 phi2 : Modal) (p : propvar),
  p_is_pos (mdisj phi1 phi2) p -> 
    pv_in_modal phi1 p ->
    p_is_pos phi1 p.
Proof.
  intros phi1 phi2 p Hpos Hocc.
  constructor. auto.
  inversion Hpos as [H1 H2].
  intros i Hocc2 Hat.
  pose proof (occ_in_modal_mdisj_l phi1 phi2 i Hocc2) as Hocc3.
  apply H2 in Hocc3. apply is_pos_mdisj_l in Hocc3; auto.
  simpl. rewrite at_pv_app_l. auto.
  apply occ_in_modal_le. auto.
Qed.

Lemma p_is_pos_mdisj2r: forall (phi1 phi2 : Modal) (p : propvar),
  p_is_pos (mdisj phi1 phi2) p -> 
    pv_in_modal phi2 p ->
    p_is_pos phi2 p.
Proof.
  intros phi1 phi2 p Hpos Hpocc.
  destruct Hpos as [Hpocct Hpoccf].
  constructor. assumption.
  intros i Hocc Hat.
  assert (i = (i + (length (pv_in phi1)) - (length (pv_in phi1)))) as Heq.
    firstorder.
  rewrite Heq in *. 
  apply is_pos_mdisj_r. apply Hpoccf.
  apply occ_in_modal_mdisj_r2.
  auto.
  simpl. rewrite PeanoNat.Nat.add_comm. rewrite at_pv_app_r.
  rewrite PeanoNat.Nat.add_sub in Hat. auto. 
  destruct i. rewrite PeanoNat.Nat.add_sub in Hocc.
  contradiction (occ_in_modal_0 _ _ Hocc). all : auto. 
  destruct i. rewrite PeanoNat.Nat.add_sub in Hocc.
  contradiction (occ_in_modal_0 _ _ Hocc). all: try auto.
  lia.
Qed.

Lemma p_is_pos_mimpl2l: forall (phi1 phi2 : Modal) (p : propvar),
  p_is_pos (mimpl phi1 phi2) p -> 
    pv_in_modal phi1 p ->
    p_is_neg phi1 p.
Proof.
  intros phi1 phi2 p Hpos Hocc.
  constructor. auto.
  inversion Hpos as [H1 H2].
  intros i Hocc2 Hat.
  pose proof (occ_in_modal_mimpl_l phi1 phi2 i Hocc2) as Hocc3.
  apply H2 in Hocc3. apply is_pos_neg_mimpl_l in Hocc3; auto.
  simpl. rewrite at_pv_app_l. auto.
  apply occ_in_modal_le. all : auto.
Qed.

Lemma p_is_pos_mimpl2r: forall (phi1 phi2 : Modal) (p : propvar),
  p_is_pos (mimpl phi1 phi2) p -> 
    pv_in_modal phi2 p ->
    p_is_pos phi2 p.
Proof.
  intros phi1 phi2 p Hpos Hpocc.
  destruct Hpos as [Hpocct Hpoccf].
  constructor. assumption.
  intros i Hocc Hat.
  assert (i = (i + (length (pv_in phi1)) - (length (pv_in phi1)))) as Heq.
    firstorder.
  rewrite Heq in *.
  apply is_pos_mimpl_r2. apply Hpoccf.
  apply occ_in_modal_mimpl_r2.
  auto.
  simpl. rewrite PeanoNat.Nat.add_comm. rewrite at_pv_app_r.
  rewrite PeanoNat.Nat.add_sub in Hat. auto.
  destruct i. rewrite PeanoNat.Nat.add_sub in Hocc.
  contradiction (occ_in_modal_0 _ _ Hocc). all: try auto.
Qed.

Lemma p_is_pos_box : forall (phi : Modal) (p : propvar),
  p_is_pos (box phi) p -> p_is_pos phi p.
Proof.
  intros phi p H.
  destruct H as [H1 H2].
  constructor. rewrite (pv_in_modal_box phi) in H1. auto.
  intros i Hocc Hat.
  apply is_pos_box. apply H2. apply (occ_in_modal_box phi). all : auto.
Qed.

Lemma p_is_pos_dia : forall (phi : Modal) (p : propvar),
    p_is_pos (dia phi) p -> p_is_pos phi p.
Proof.
  intros phi p H.
  destruct H as [H1 H2].
  constructor. rewrite (pv_in_modal_dia phi) in H1. auto.
  intros i Hocc Hat.
  apply is_pos_dia. apply H2. apply (occ_in_modal_dia phi). all : auto.
Qed.

(* ---------------------------------------------------------------------------- *)
(* p_is_neg lemmas *)

Lemma p_is_neg_notin : forall (phi : Modal) (p : propvar),
  p_is_neg phi p -> pv_in_modal phi p.
Proof. intros. firstorder. Qed.

Lemma p_is_neg_atom : forall (p q : propvar),
  p_is_neg (atom q) p -> p = q.
Proof.
  intros p q H. destruct H as [H1 H2].
  apply pv_in_modal_atom. auto.
Qed.

Lemma p_is_neg_mconj2l: forall (phi1 phi2 : Modal) (p : propvar),
  p_is_neg (mconj phi1 phi2) p -> 
    pv_in_modal phi1 p ->
      p_is_neg phi1 p.
Proof.
  intros phi1 phi2 p Hpos Hocc.
  constructor. auto.
  inversion Hpos as [H1 H2].
  intros i Hocc2 Hat.
  pose proof (occ_in_modal_mconj_l phi1 phi2 i Hocc2) as Hocc3.
  apply H2 in Hocc3. apply is_neg_mconj_l in Hocc3; auto.
  simpl. rewrite at_pv_app_l. auto.
  apply occ_in_modal_le. auto.
Qed.

Lemma p_is_neg_mconj2r: forall (phi1 phi2 : Modal) (p : propvar),
  p_is_neg (mconj phi1 phi2) p -> 
    pv_in_modal phi2 p ->
      p_is_neg phi2 p.
Proof.
  intros phi1 phi2 p Hpos Hpocc.
  destruct Hpos as [Hpocct Hpoccf].
  constructor. assumption.
  intros i Hocc Hat.
  assert (i = (i + (length (pv_in phi1)) - (length (pv_in phi1)))) as Heq.
    firstorder.
  rewrite Heq in *. 
  apply is_neg_mconj_r. apply Hpoccf.
  apply occ_in_modal_mconj_r2.
  auto.
  simpl. rewrite PeanoNat.Nat.add_comm. rewrite at_pv_app_r.
  rewrite PeanoNat.Nat.add_sub in Hat. auto.
  destruct i. rewrite PeanoNat.Nat.add_sub in Hocc.
  contradiction (occ_in_modal_0 _ _ Hocc). all: try auto.
  destruct i. rewrite PeanoNat.Nat.add_sub in Hocc.
  contradiction (occ_in_modal_0 _ _ Hocc). all: try auto.
  lia.
Qed.

Lemma p_is_neg_mdisj2l: forall (phi1 phi2 : Modal) (p : propvar),
  p_is_neg (mdisj phi1 phi2) p -> 
    pv_in_modal phi1 p ->
    p_is_neg phi1 p.
Proof.
  intros phi1 phi2 p Hpos Hocc.
  constructor. auto.
  inversion Hpos as [H1 H2].
  intros i Hocc2 Hat.
  pose proof (occ_in_modal_mdisj_l phi1 phi2 i Hocc2) as Hocc3.
  apply H2 in Hocc3. apply is_neg_mdisj_l in Hocc3; auto.
  simpl. rewrite at_pv_app_l. auto.
  apply occ_in_modal_le. auto.
Qed.

Lemma p_is_neg_mdisj2r: forall (phi1 phi2 : Modal) (p : propvar),
  p_is_neg (mdisj phi1 phi2) p -> 
    pv_in_modal phi2 p ->
    p_is_neg phi2 p.
Proof.
  intros phi1 phi2 p Hpos Hpocc.
  destruct Hpos as [Hpocct Hpoccf].
  constructor. assumption.
  intros i Hocc Hat.
  assert (i = (i + (length (pv_in phi1)) - (length (pv_in phi1)))) as Heq.
    firstorder.
  rewrite Heq in *. 
  apply is_neg_mdisj_r. apply Hpoccf.
  apply occ_in_modal_mdisj_r2.
  auto.
  simpl. rewrite PeanoNat.Nat.add_comm. rewrite at_pv_app_r.
  rewrite PeanoNat.Nat.add_sub in Hat. auto.
  destruct i. rewrite PeanoNat.Nat.add_sub in Hocc.
  contradiction (occ_in_modal_0 _ _ Hocc). all: try auto.
  destruct i. rewrite PeanoNat.Nat.add_sub in Hocc.
  contradiction (occ_in_modal_0 _ _ Hocc). all: lia.
Qed.

Lemma p_is_neg_mimpl2l: forall (phi1 phi2 : Modal) (p : propvar),
  p_is_neg (mimpl phi1 phi2) p -> 
    pv_in_modal phi1 p ->
    p_is_pos phi1 p.
Proof.
  intros phi1 phi2 p Hpos Hocc.
  constructor. auto.
  inversion Hpos as [H1 H2].
  intros i Hocc2 Hat.
  pose proof (occ_in_modal_mimpl_l phi1 phi2 i Hocc2) as Hocc3.
  apply H2 in Hocc3. apply is_neg_pos_mimpl_l in Hocc3; auto.
  simpl. rewrite at_pv_app_l. auto.
  apply occ_in_modal_le. all : auto.
Qed.

Lemma p_is_neg_mimpl2r: forall (phi1 phi2 : Modal) (p : propvar),
  p_is_neg (mimpl phi1 phi2) p -> 
    pv_in_modal phi2 p ->
    p_is_neg phi2 p.
Proof.
  intros phi1 phi2 p Hpos Hpocc.
  destruct Hpos as [Hpocct Hpoccf].
  constructor. assumption.
  intros i Hocc Hat.
  assert (i = (i + (length (pv_in phi1)) - (length (pv_in phi1)))) as Heq.
    firstorder.
  rewrite Heq in *.
  apply is_neg_mimpl_r2. apply Hpoccf.
  apply occ_in_modal_mimpl_r2.
  auto.
  simpl. rewrite PeanoNat.Nat.add_comm. rewrite at_pv_app_r.
  rewrite PeanoNat.Nat.add_sub in Hat. auto.
  destruct i. rewrite PeanoNat.Nat.add_sub in Hocc.
  contradiction (occ_in_modal_0 _ _ Hocc). all: try auto.
Qed.

Lemma p_is_neg_box : forall (phi : Modal) (p : propvar),
  p_is_neg (box phi) p -> p_is_neg phi p.
Proof.
  intros phi p H.
  destruct H as [H1 H2].
  constructor. rewrite (pv_in_modal_box phi) in H1. auto.
  intros i Hocc Hat.
  apply is_neg_box. apply H2. apply (occ_in_modal_box phi). all : auto.
Qed.

Lemma p_is_neg_dia : forall (phi : Modal) (p : propvar),
  p_is_neg (dia phi) p -> p_is_neg phi p.
Proof.
  intros phi p H.
  destruct H as [H1 H2].
  constructor. rewrite (pv_in_modal_dia phi) in H1. auto.
  intros i Hocc Hat.
  apply is_neg_dia. apply H2. apply (occ_in_modal_dia phi). all : auto.
Qed.

(* ---------------------------------------------------------------------------- *)
(* p_is_pos and p_is_neg relationship *)

Lemma p_is_pos_neg : forall (phi : Modal) (p : propvar),
  p_is_pos (mneg phi) p -> p_is_neg phi p.
Proof.
  intros phi p Hpos.
  destruct Hpos as [H1 H2].
  constructor. apply (pv_in_modal_mneg phi) in H1. auto.
  intros i Hocc Hat. apply is_pos_neg_f. auto.
  apply is_pos_mneg. apply H2. apply (occ_in_modal_mneg phi).
  all : auto.
Qed.

Lemma p_is_neg_pos : forall (phi : Modal) (p : propvar),
  p_is_neg (mneg phi) p -> p_is_pos phi p.
Proof.
  intros phi p Hpos.
  destruct Hpos as [H1 H2].
  constructor. apply (pv_in_modal_mneg phi) in H1. auto.
  intros i Hocc Hat. apply is_neg_pos_f. auto.
  apply is_neg_mneg. apply H2. apply (occ_in_modal_mneg phi).
  all : auto.
Qed.