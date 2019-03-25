Require Export SO_syntax nlist_syn List.

Fixpoint nlist_full (n : nat) : nlist n :=
  match n with
  | 0 => niln
  | S m => consn _ (eqFO (Var 1) (Var 1)) (nlist_full m)
  end.

Fixpoint nlist_empty (n : nat) : nlist n :=
  match n with
  | 0 => niln
  | S m => consn _ (negSO (eqFO (Var 1) (Var 1))) (nlist_empty m)
  end.

Fixpoint nlist_var (n : nat) (x : FOvariable) : nlist n :=
  match n with
  | 0 => niln
  | S m => consn _ x (nlist_var m x)
  end.

Lemma nlist_var_length : forall n x,
  length (nlist_list _ (nlist_var n x)) = n.
Proof. induction n; intros x; simpl; auto. Qed.

Fixpoint list_var (n : nat) (x : FOvariable) : list FOvariable :=
  match n with
  | 0 => nil
  | S m => cons x (list_var m x)
  end.

Lemma repeat_list_var : forall n x,
  list_var n x = repeat x n.
Proof.
  induction n; intros x; simpl; auto.
  rewrite IHn. auto.
Qed.

Lemma list_var_length : forall n x,
  length (list_var n x) = n.
Proof. induction n; intros x; simpl; auto. Qed.

Lemma not_in_list_var : forall l x,
    (forall y : FOvariable, x <> y -> ~ In y l) ->
    exists n, l  = list_var n x.
Proof.
  induction l; intros x H. exists 0. auto.
  simpl in *. destruct (FOvariable_dec x a).
  subst. edestruct IHl as [m Hm].
  intros yy HH1 HH2. eapply H. apply HH1. firstorder.
  subst. exists (S m). auto.
  firstorder.
Qed.

Lemma nlist_empty_nil : forall {A : Type} (l2:list A),
  nlist_list _ (nlist_empty (length l2)) = nil ->
  l2 = nil.
Proof. induction l2; auto. intros. discriminate. Qed.

Fixpoint nlist_P n (P : predicate) : nlist n :=
  match n with
  | 0 => niln
  | S m => consn _ P (nlist_P m P)
  end.

Lemma nlist_P_plus : forall n m P,
  nlist_list _ (nlist_P (n + m) P) = app (nlist_list _ (nlist_P n P))
                                       (nlist_list _ (nlist_P m P)).
Proof.
  induction n; intros m P; auto.
  simpl; rewrite IHn. auto.
Qed.

Lemma is_in_pred_nlist_P : forall n P,
  In P (nlist_list (S n) (nlist_P (S n) P)).
Proof.  intros. simpl. firstorder. Qed.
