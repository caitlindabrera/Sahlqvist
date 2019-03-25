Require Export low_mods.

Fixpoint REL (alpha : SecOrder) : bool :=
  match alpha with
  | relatSO _ _ => true
  | conjSO alpha1 alpha2 => if REL alpha1 then REL alpha2 else false
  | _ => false
  end.

Lemma REL_conjSO_l : forall rel1 rel2,
  REL (conjSO rel1 rel2) = true ->
  REL rel1 = true.
Proof.
  intros rel1 rel2 H. simpl in H.
  if_then_else_dest_blind; auto.
Qed.

Lemma REL_conjSO_r : forall rel1 rel2,
  REL (conjSO rel1 rel2) = true ->
  REL rel2 = true.
Proof.
  intros rel1 rel2 H. simpl in H.
  if_then_else_dest_blind; auto.
  discriminate.
Qed.

Lemma preds_in_rel  : forall rel,
  REL rel = true ->
  preds_in rel = nil.
Proof.
  induction rel; intros H; try (simpl in *; discriminate).
    destruct f; destruct f0; reflexivity.

    simpl in *. rewrite IHrel1. rewrite IHrel2.
    reflexivity. 
      apply REL_conjSO_r in H. assumption.
      apply REL_conjSO_l in H. assumption.
Qed.

Lemma P_occurs_in_rel : forall rel P,
  REL rel = true -> ~ Pred_in_SO rel P .
Proof.
  induction rel; intros P Hrel; try discriminate.
  firstorder.
  pose proof (REL_conjSO_l _ _ Hrel).
  pose proof (REL_conjSO_r _ _ Hrel).
  apply Pred_in_SO_conjSO_f. firstorder. 
Qed.