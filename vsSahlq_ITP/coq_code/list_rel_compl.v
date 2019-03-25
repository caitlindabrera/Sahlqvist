Require Export SO_syntax.
Require Import List.

(* Returns a list of preds that in l2 but not l1 (relative complement). *)
Fixpoint list_rel_compl (l2 l1 : list predicate) : list predicate :=
  match l2 with
  | nil => nil
  | cons P l2' => if in_predicate_dec P l1 then list_rel_compl l2' l1
                  else cons P (list_rel_compl l2' l1)
  end.

Lemma list_rel_compl_nil : forall l,
  list_rel_compl l nil = l.
Proof.
  induction l. auto. simpl. 
  rewrite IHl. destruct (in_predicate_dec a nil); firstorder.
Qed.

Lemma list_rel_compl_contains : forall l2 l1,
  (forall P, In P l2 -> In P l1 ) ->
  list_rel_compl l2 l1 = nil.
Proof.
  induction l2; intros l1 H.
    reflexivity.

    simpl in *.
    destruct (in_predicate_dec a l1) as [H1 | H1].
    apply IHl2. intros P H2. apply H. auto.
    firstorder.
Qed.

Lemma list_rel_compl_refl : forall l,
  list_rel_compl l l = nil.
Proof.
  intros l.
  apply list_rel_compl_contains.
  intros P H.
  assumption.
Qed.

Lemma list_rel_compl_cons_cons : forall l l2 P,
  list_rel_compl  l2 (cons P (cons P l)) = list_rel_compl  l2 (cons P l).
Proof.
  intros l l2. revert l.
  induction l2; intros l P. auto.
  simpl. destruct (in_predicate_dec a (P :: P :: l)) as [H1 | H1];
  destruct (in_predicate_dec a (P :: l)) as [H2 | H2].
  apply IHl2. 
  simpl in *. destruct H1. firstorder.
  destruct H; firstorder.
  simpl in H2. destruct H2.  subst. firstorder.
  firstorder. rewrite IHl2. auto.
Qed.

Lemma list_rel_compl_is_in_f : forall l1 l2 P,
  ~ In P l1 ->
  list_rel_compl (cons P l2) l1 = cons P (list_rel_compl l2 l1).
Proof.
  intros l1 l2 P Hin. simpl. destruct (in_predicate_dec P l1); firstorder.
Qed.

Lemma is_in_pred_l_list_rel_compl : forall l2 l1,
  incl (list_rel_compl l2 l1) l2.
Proof.
  induction l2; intros l1; simpl in *. firstorder.
  destruct (in_predicate_dec a l1);[|
  apply incl_cons; firstorder];
  apply incl_tl; auto.
Qed.

Lemma list_rel_compl_app : forall l1 l2 l,
  list_rel_compl (app l1 l2) l =
  app (list_rel_compl l1 l) (list_rel_compl l2 l).
Proof.
  induction l1; intros l2 l. auto.
  simpl. destruct (in_predicate_dec a l). apply IHl1.
  simpl. rewrite IHl1. auto.
Qed.

Lemma want12 : forall l1 l2 P,
  In P l1 -> ~ In P l2 ->  In P (list_rel_compl l1 l2).
Proof.
  induction l1; intros l2 P H1 H2. contradiction.
  simpl in *.  destruct (predicate_dec a P). subst.
  subst. rewrite in_predicate_dec_r; auto.
  simpl. firstorder.  destruct H1. firstorder.
  destruct (in_predicate_dec a l2); [|simpl; right];
    apply IHl1; auto.
Qed.

Lemma want11 : forall l1 l2 l P,
In P (list_rel_compl l1 l) /\ In P l2 -> In P (list_rel_compl l2 l).
Proof.
  induction l1; intros l2 l P [H1 H2]. contradiction.
  simpl in *. destruct (in_predicate_dec a l). apply IHl1; auto.
  simpl in H1. destruct H1. subst. apply want12; auto.
  apply IHl1; auto.
Qed.

