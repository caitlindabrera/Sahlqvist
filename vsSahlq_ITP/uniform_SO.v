Require Export med_mods Pred_is_pos_SO Pred_is_neg_SO.
Require Import ST uniform.

Definition uniform_pos_SO (alpha : SecOrder) : Prop :=
forall (P : predicate), Pred_in_SO alpha P -> Pred_is_pos_SO alpha P.

Definition uniform_neg_SO (alpha : SecOrder) : Prop :=
forall (P : predicate), Pred_in_SO alpha P -> Pred_is_neg_SO alpha P.


(*
Inductive uniform_pos_SO (alpha : SecOrder) : Prop :=
| uni_pos_SO_y : (forall (P : predicate), Pred_in_SO alpha P -> 
                          Pred_is_pos_SO alpha P) -> uniform_pos_SO alpha.

Inductive uniform_neg_SO (alpha : SecOrder) : Prop :=
| uni_neg_SO_y : (forall (P : predicate), Pred_in_SO alpha P -> 
                          Pred_is_neg_SO alpha P) -> uniform_neg_SO alpha.
 *)

Lemma uni_pos__SO : forall (phi : Modal) (x : FOvariable),
  uniform_pos phi <-> uniform_pos_SO (ST phi x).
Proof.
  intros phi x.  unfold uniform_pos; unfold uniform_pos_SO.
  split; intros H [n] H2.
    apply (p_is_pos__SO phi x (pv n)).
    apply H. change (Pred n) with (ST_pv (pv n)) in H2.
    apply p_occ__ST in H2. auto.

    apply (p_is_pos__SO phi x (pv n)).
    apply H. apply p_occ__ST. auto.
Qed.

Lemma uni_neg__SO : forall (phi : Modal) (x : FOvariable),
  uniform_neg phi <-> uniform_neg_SO (ST phi x).
Proof.
  intros phi x.  unfold uniform_pos; unfold uniform_pos_SO.
  split; intros H [n] H2.
    apply (p_is_neg__SO phi x (pv n)).
    apply H. change (Pred n) with (ST_pv (pv n)) in H2.
    apply p_occ__ST in H2. auto.

    apply (p_is_neg__SO phi x (pv n)).
    apply H. apply p_occ__ST. auto.
Qed.

Lemma uni_pos_SO_allFO : forall (alpha : SecOrder) (x : FOvariable),
    uniform_pos_SO (allFO x alpha) <-> uniform_pos_SO alpha.
Proof.
  intros alpha x; unfold uniform_pos_SO;
    split; intros H [n] H2;
    eapply Pred_is_pos_SO_allFO; apply H.
  rewrite <- Pred_in_SO_allFO.  auto.
  rewrite <- Pred_in_SO_allFO in H2. apply H2.
  Unshelve. apply x.
Qed.

Lemma uni_neg_SO_allFO : forall (alpha : SecOrder) (x : FOvariable),
  uniform_neg_SO (allFO x alpha) <-> uniform_neg_SO alpha.
Proof.
  intros alpha x; unfold uniform_pos_SO;
    split; intros H [n] H2;
    eapply Pred_is_neg_SO_allFO; apply H.
  rewrite <- Pred_in_SO_allFO.  auto.
  erewrite Pred_in_SO_allFO. apply H2.
  Unshelve. apply x.
Qed.