Require Export base_mods max_min.

Fixpoint rev_seq start length : list nat :=
  match length with
  | 0 => nil
  | S n => cons (start + n) (rev_seq start n)
  end.

Lemma rev_seq_nil : forall m n,
  rev_seq n m = nil -> m = 0.
Proof. induction m; intros; auto. simpl in *. discriminate. Qed.

Inductive decr_strict : list nat -> Prop :=
| decr_strict_nil : decr_strict nil
| decr_strict_cons n ln: (max_l ln) < n -> decr_strict ln -> decr_strict (n :: ln).

Lemma max_l_rev_seq : forall m n,
  max_l (rev_seq n (S m)) = (n + m).
Proof.
  induction m; intros n; simpl in *. lia.
  rewrite IHm. lia.
Qed.

Lemma min_l_rev_seq : forall m n,
  min_l (rev_seq n (S m)) = n.
Proof.
  induction m; intros n. simpl. lia.
  simpl. case_eq (rev_seq n m). intros H.
    apply rev_seq_nil in H. subst. lia.
  intros a la Ha. rewrite <- Ha. simpl in IHm.
  specialize (IHm n). rewrite Ha in *.
  rewrite <- Ha in *. rewrite IHm. lia.
Qed.

Lemma decr_strict_rev_seq : forall m n,
  decr_strict (rev_seq (S n) m).
Proof.
  induction m; intros n. simpl. constructor.
  simpl. constructor; auto. simpl.
  destruct m. simpl. lia.
  rewrite max_l_rev_seq. lia.
Qed.
