Require Export base_mods preds_in occ_in_SO.

Fixpoint at_pred (l : list predicate) (i : nat) : predicate :=
  match l with
  | nil => (Pred 1)
  | cons q l' => match i with
                 | S 0 => q
                 | 0 => Pred 1
                 | _ => at_pred l' (i-1)
                 end
  end.

Lemma at_pred_0 : forall (l : list predicate),
  at_pred l 0 = Pred 1.
Proof.
  intros.
  induction l.
    simpl; reflexivity.

    simpl; reflexivity.
Qed.

Lemma at_pred_cons_1 : forall (l : list predicate) (P : predicate)
                            (j : nat),
  at_pred (cons P l) 1 = P.
Proof.
  intros; reflexivity.
Qed.

Lemma at_pred_cons : forall (l : list predicate) (P : predicate)
                            (j : nat),
  at_pred (cons P l) (S (S j)) = at_pred l (S j).
Proof.
  intros; reflexivity.
Qed.


Lemma at_pred_app_cons : forall (l1 l2 : list predicate) (p : predicate),
  at_pred (app l1 (cons p l2)) (length l1 + 1) = p.
Proof.
  intros; induction l1.
  simpl; reflexivity.
  simpl in *.
  rewrite <- plus_n_Sm. simpl.
  rewrite plus_n_Sm. assumption.
Qed.

Lemma at_pred_app_l : forall (l1 l2 : list predicate) (i : nat),
  i <= (length l1) -> at_pred (app l1 l2) i = at_pred l1 i.
Proof.
  induction l1.  simpl in *.
    induction l2; simpl in *; try reflexivity;  intros i H.
      destruct i; auto.  contradiction (PeanoNat.Nat.nle_succ_0 _ H).

      simpl app. intros l2 i H.
      case_eq i.  intros Hi. simpl. auto.

      simpl. intros n Hi.  rewrite IHl1. auto. simpl in H.
      lia.
Qed.

Lemma at_pred_app_r : forall (l1 l2 : list predicate) (i : nat),
  i <> 0 ->
    at_pred (app l1 l2) (length l1 + i) = at_pred l2 i.
Proof.
  intros l1 l2 i H. induction l1. reflexivity.
  simpl.  case_eq (length l1 + i).
    intros H_eq. rewrite H_eq in IHl1. destruct l1.
    simpl in H_eq. subst. contradiction.
    discriminate.

    intros n H2.  simpl in *. rewrite <- H2; exact IHl1.
Qed.

Lemma at_pred_occ_l : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_SO alpha1 i ->
    at_pred (app (preds_in alpha1) (preds_in alpha2)) i
    = at_pred (preds_in alpha1) i.
Proof.
  intros alpha1 alpha2 i [H1 H2].
  rewrite at_pred_app_l; firstorder.
Qed.

Lemma at_pred_occ_r : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_SO alpha2 (i - (length (preds_in (alpha1)))) ->
    at_pred (app (preds_in alpha1) (preds_in alpha2)) i
    = at_pred (preds_in alpha2) (i - (length (preds_in alpha1))).
Proof.
  intros alpha1 alpha2 i [H1 H2].
  assert (i = length (preds_in alpha1) + (i - length (preds_in alpha1))) as H3.
    firstorder.
  rewrite H3.
  rewrite at_pred_app_r.   rewrite <- H3. auto. auto.
Qed.