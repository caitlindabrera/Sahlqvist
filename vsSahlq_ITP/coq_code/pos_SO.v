Require Export med_mods Pred_is_pos_SO Pred_is_neg_SO.
Require Import ST uniform.

Definition pos_SO (alpha : SecOrder) : Prop :=
forall (P : predicate), Pred_in_SO alpha P -> Pred_is_pos_SO alpha P.

Definition neg_SO (alpha : SecOrder) : Prop :=
forall (P : predicate), Pred_in_SO alpha P -> Pred_is_neg_SO alpha P.


(*
Inductive uniform_pos_SO (alpha : SecOrder) : Prop :=
| uni_pos_SO_y : (forall (P : predicate), Pred_in_SO alpha P -> 
                          Pred_is_pos_SO alpha P) -> uniform_pos_SO alpha.

Inductive uniform_neg_SO (alpha : SecOrder) : Prop :=
| uni_neg_SO_y : (forall (P : predicate), Pred_in_SO alpha P -> 
                          Pred_is_neg_SO alpha P) -> uniform_neg_SO alpha.
 *)

Lemma pos__SO : forall (phi : Modal) (x : FOvariable),
  pos phi <-> pos_SO (ST phi x).
Proof.
  intros phi x.  unfold pos; unfold pos_SO.
  split; intros H [n] H2.
    apply (p_is_pos__SO phi x (pv n)).
    apply H. change (Pred n) with (ST_pv (pv n)) in H2.
    apply p_occ__ST in H2. auto.

    apply (p_is_pos__SO phi x (pv n)).
    apply H. apply p_occ__ST. auto.
Qed.

Lemma neg__SO : forall (phi : Modal) (x : FOvariable),
  neg phi <-> neg_SO (ST phi x).
Proof.
  intros phi x. split; intros H [n] H2.
    apply (p_is_neg__SO phi x (pv n)).
    apply H. change (Pred n) with (ST_pv (pv n)) in H2.
    apply p_occ__ST in H2. auto.

    apply (p_is_neg__SO phi x (pv n)).
    apply H. apply p_occ__ST. auto.
Qed.

Lemma pos_SO_allFO : forall (alpha : SecOrder) (x : FOvariable),
    pos_SO (allFO x alpha) <-> pos_SO alpha.
Proof.
  intros alpha x; unfold pos_SO;
    split; intros H [n] H2;
    eapply Pred_is_pos_SO_allFO; apply H.
  rewrite <- Pred_in_SO_allFO.  auto.
  rewrite <- Pred_in_SO_allFO in H2. apply H2.
  Unshelve. apply x.
Qed.

Lemma neg_SO_allFO : forall (alpha : SecOrder) (x : FOvariable),
  neg_SO (allFO x alpha) <-> neg_SO alpha.
Proof.
  intros alpha x; unfold pos_SO;
    split; intros H [n] H2;
    eapply Pred_is_neg_SO_allFO; apply H.
  rewrite <- Pred_in_SO_allFO.  auto.
  erewrite Pred_in_SO_allFO. apply H2.
  Unshelve. apply x.
Qed.