Require Export List.

Section InclLems.

  Variable A : Type.
  
  Lemma incl_rcons_not : forall l1 l2 (P : A),
      ~ In P l1 ->  incl l1 (cons P l2) -> incl l1 l2.
  Proof.
    unfold incl. intros l1 l2 P H1 H2 Q H3.
    specialize (H2 Q H3). simpl in H2.
    destruct H2. subst. contradiction. auto.
  Qed.

  Lemma incl_rcons : forall l1 l2 (P : A),
      incl l1 l2 -> incl l1 (cons P l2).
  Proof. intros. apply incl_tl. auto. Qed.

  Lemma incl_lcons : forall l1 l2 (P : A),
      incl (cons P l1) l2 -> incl l1 l2.
  Proof.
    unfold incl. intros l1 l2 P H1 Q H2.
    apply H1. simpl. firstorder.
  Qed.

  Lemma incl_app_rev_r : forall (l1 l2 l : list A),
      incl (app l1 l2) l -> incl l2 l.
  Proof.
    unfold incl. intros l1 l2 l H1 Q H2.
    apply H1. apply in_or_app. firstorder.
  Qed.

  Lemma incl_app_rev_l : forall (l1 l2 l : list A),
      incl (app l1 l2) l -> incl l1 l.
  Proof.
    unfold incl. intros l1 l2 l H1 Q H2.
    apply H1. apply in_or_app. firstorder.
  Qed.

  Lemma incl_lcons_f : forall (A_dec : forall (a b : A), {a = b} + {a <> b})
                              l l2 (P : A),
      ~ incl (P :: l) l2 ->
      (In P l2 /\ ~ incl l l2) \/ ~ In P l2.
  Proof.
    intros A_dec l l2 P H. unfold incl in *.
    destruct (in_dec A_dec P l2). left. apply conj; auto. 
    intros H2. apply H. intros a Ha. simpl in Ha.
    destruct Ha; subst; auto. firstorder.
  Qed.

  Lemma incl_hd : forall l l2 (P : A),
      incl (P :: l) l2 -> In P l2.
  Proof.
    intros l l2 P H1. specialize (H1 P).
    simpl in *. apply H1. firstorder.
  Qed.

  Lemma incl_nil : forall (l : list A), incl nil l.
  Proof.  intros l P H. inversion H. Qed.

  Lemma incl_rcons_l_f : forall (A_dec : forall (a b : A), {a = b} + {a <> b}) l1 l2 (P : A),
      ~ incl l1 l2 -> incl l1 (cons P l2) -> In P l1 /\ ~ In P l2.
  Proof.
    induction l1; intros l2 P H1 H2.
    contradiction (H1 (incl_nil _)).  
    apply incl_lcons_f in H1; auto.
    destruct (A_dec a P) as [H3 | H3]. subst. 
    simpl in *. firstorder.
    simpl. firstorder.
  Qed.

  Lemma incl_rcons_f : forall l1 l2 (P : A),
      ~ incl l1 (cons P l2) -> ~ incl l1 l2.
  Proof.
    intros l1 l2 P H1 H2. apply H1.
    apply incl_rcons. auto.
  Qed.

  Lemma incl_trans : forall (l1 l2 l3 : list A),
      incl l1 l2 ->  incl l2 l3 ->  incl l1 l3.
  Proof.
    intros l1 l2 l3 H1 H2 P H3. 
    unfold incl in *. auto.
  Qed.

  Lemma incl_app_gen : forall (l1 l2 l3 l4 : list A),
      incl l1 l3 -> incl l2 l4 ->
      incl (l1 ++ l2) (l3 ++ l4).
  Proof.
    intros l1 l2 l3 l4 H1 H2 P H3.
    apply in_app_or in H3. apply in_or_app.
    destruct H3 as [H3 | H3].
    left. apply H1. auto.
    right. apply H2. auto.
  Qed.

  Lemma incl_cons_cons : forall (l1 l2 : list A) x,
      incl l1 l2 -> incl (x :: l1) (x :: l2).
  Proof.
    intros l1 l2 x H1 y H2.
    simpl in *. firstorder.
  Qed.

  Lemma incl_nil_r : forall (l : list A),  incl l nil -> l = nil.
  Proof.
    induction l; intros H. auto.
    specialize (H a). simpl in *. firstorder.
  Qed.

  Lemma in_incl : forall (l1 l2 : list A) x,
      In x l1 -> incl l1 l2 -> In x l2.
  Proof.  intros. auto. Qed. 

  Lemma incl_dec : forall (A_dec : forall (a b : A), {a = b} + {a <> b}) (l1 l2 : list A),
      {incl l1 l2} + {~ incl l1 l2}.
  Proof.
    induction l1; intros l2. firstorder.
    destruct (in_dec A_dec a l2).
    + destruct (IHl1 l2) as [IH | IH];
        firstorder. 
    + right. intros HH. apply n. firstorder.
  Qed.

  Lemma incl_app_rearr1 : forall (l1 l2 l3 l4 l : list A),
      incl ( (l1 ++ l2) ++ l3 ++ l4 ) l <->
      incl ( (l1 ++ l3) ++ (l2 ++ l4) ) l.
  Proof.
    intros l1 l2 l3 l4 l. split; intros H P H2; apply H;
                            repeat (apply in_app_or in H2; destruct H2 as [H2 | H2]);
                            firstorder.
  Qed.

  Lemma incl_app_rear2 : forall (l1 l2 l3 l : list A),
      incl ( (l1 ++ l2) ++ l3 ) l <->
      incl ( l2 ++ (l1 ++ l3) ) l.
  Proof.
    intros l1 l2 l3 l; split; intros H1 P H2; apply H1;
      repeat (firstorder; apply in_app_or in H2;
              destruct H2 as [H2 | H2]; firstorder).
  Qed.

End InclLems.