Require Import pv_in occ_in_modal at_pv.
Require Import Arith.EqNat List.

Definition pv_in_modal (phi : Modal) (p : propvar) : Prop :=
  In p (pv_in phi).

Lemma pv_in_modal_dec : forall phi p,
    {pv_in_modal phi p} + {~ pv_in_modal phi p}.
Proof.
  intros phi p. unfold pv_in_modal.
  apply in_dec. apply propvar_dec.
Qed.

Lemma pv_in_modal_atom : forall p q,
    pv_in_modal (#q) p -> p = q.
Proof.
  unfold pv_in_modal. simpl.
  intros p q H. firstorder.
Qed.

Lemma pv_in_modal_mneg : forall (phi : Modal) (p : propvar),
  pv_in_modal (mneg phi) p <->
    pv_in_modal phi p.
Proof.
  split; intros H; unfold pv_in_modal in *;
    simpl in *; exact H.
Qed.

Lemma pv_in_modal_mconj : forall (phi1 phi2 : Modal) (p : propvar),
  pv_in_modal (mconj phi1 phi2) p <->
    pv_in_modal phi1 p \/ pv_in_modal phi2 p.
Proof.
  split; intros H; unfold pv_in_modal in *; simpl in *;
    [apply in_app_or in H | apply in_or_app in H]; assumption.
Qed.

Lemma pv_in_modal_mdisj : forall (phi1 phi2 : Modal) (p : propvar),
  pv_in_modal (mdisj phi1 phi2) p  <->
    pv_in_modal phi1 p \/ pv_in_modal phi2 p.
Proof.
  split; intros H; unfold pv_in_modal in *; simpl in *;
    [apply in_app_or in H | apply in_or_app in H]; assumption.
Qed.

Lemma pv_in_modal_mimpl : forall (phi1 phi2 : Modal) (p : propvar),
  pv_in_modal (mimpl phi1 phi2) p <->
    pv_in_modal phi1 p \/ pv_in_modal phi2 p.
Proof.
  split; intros H; unfold pv_in_modal in *; simpl in *;
    [apply in_app_or in H | apply in_or_app in H]; assumption.
Qed.

Lemma pv_in_modal_box : forall (phi : Modal) (p : propvar),
  pv_in_modal (box phi) p <->
  pv_in_modal phi p.
Proof. split; intros H; unfold pv_in_modal in *;  assumption. Qed.

Lemma pv_in_modal_diam : forall (phi : Modal) (p : propvar),
  pv_in_modal (diam phi) p <->
    pv_in_modal phi p.
Proof. split; intros H; unfold pv_in_modal in *; assumption. Qed.

Lemma pv_in_modal_occ_in_modal : forall phi q,
    pv_in_modal phi q ->
    exists i, occ_in_modal phi i /\ q = at_pv (pv_in phi) i.
Proof.
  induction phi; intros q H.
  - apply pv_in_modal_atom in H.  subst.
    exists 1. firstorder.
  - pose proof (proj1 (pv_in_modal_mneg phi q) H) as H2.
    apply IHphi in H2. destruct H2 as [i [H2 H3]].
    exists i. split.
    apply (occ_in_modal_mneg phi). auto.
    simpl. auto.
  - apply pv_in_modal_mconj in H. destruct H as [H | H].
    apply IHphi1 in H. destruct H as [i [H1 H2]].
    exists i. split. apply occ_in_modal_mconj_l. auto.
    simpl. subst. rewrite at_pv_app_l. auto.
    inversion H1. auto.
    apply IHphi2 in H. destruct H as [i [H1 H2]].
    exists (i + length (pv_in phi1)). split.
    apply occ_in_modal_mconj_r2. firstorder.
    simpl. rewrite PeanoNat.Nat.add_comm.
    rewrite at_pv_app_r. auto.
    apply occ_in_modal_0 in H1. destruct i; firstorder.
  - apply pv_in_modal_mconj in H. destruct H as [H | H].
    apply IHphi1 in H. destruct H as [i [H1 H2]].
    exists i. split. apply occ_in_modal_mdisj_l. auto.
    simpl. subst. rewrite at_pv_app_l. auto.
    inversion H1. auto.
    apply IHphi2 in H. destruct H as [i [H1 H2]].
    exists (i + length (pv_in phi1)). split.
    apply occ_in_modal_mdisj_r2. firstorder.
    simpl. rewrite PeanoNat.Nat.add_comm.
    rewrite at_pv_app_r. auto.
    apply occ_in_modal_0 in H1. destruct i; firstorder.
  - apply pv_in_modal_mconj in H. destruct H as [H | H].
    apply IHphi1 in H. destruct H as [i [H1 H2]].
    exists i. split. apply occ_in_modal_mimpl_l. auto.
    simpl. subst. rewrite at_pv_app_l. auto.
    inversion H1. auto.
    apply IHphi2 in H. destruct H as [i [H1 H2]].
    exists (i + length (pv_in phi1)). split.
    apply occ_in_modal_mimpl_r2. firstorder.
    simpl. rewrite PeanoNat.Nat.add_comm.
    rewrite at_pv_app_r. auto.
    apply occ_in_modal_0 in H1. destruct i; firstorder.
  - pose proof (proj1 (pv_in_modal_box phi q) H) as H2.
    apply IHphi in H2. destruct H2 as [i [H3 H4]].
    subst. exists i.
    split. apply occ_in_modal_box. auto. reflexivity. 
  - pose proof (proj1 (pv_in_modal_diam phi q) H) as H2.
    apply IHphi in H2. destruct H2 as [i [H3 H4]].
    subst. exists i.
    split. apply occ_in_modal_diam. auto. reflexivity.
Qed.


