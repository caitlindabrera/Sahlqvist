Require Export low_mods.

Fixpoint AT (alpha : SecOrder) : bool :=
  match alpha with
  | predSO _ _ => true
  | conjSO alpha1 alpha2 => if AT alpha1 then AT alpha2 else false
  | _ => false
  end.

Lemma AT_conjSO_l : forall rel1 rel2,
  AT (conjSO rel1 rel2) = true ->
  AT rel1 = true.
Proof.
  intros rel1 rel2 H. simpl in H.
  if_then_else_dest_blind; auto.
Qed.

Lemma AT_conjSO_r : forall rel1 rel2,
  AT (conjSO rel1 rel2) = true ->
  AT rel2 = true.
Proof.
  intros rel1 rel2 H. simpl in H.
  if_then_else_dest_blind; auto.
  discriminate.
Qed.
