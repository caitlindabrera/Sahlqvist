Require Export base_mods SO_syntax ltac_SO.

Open Scope SO_scope.

(* List of predicates in given SecOrder formula. *)
Fixpoint preds_in (α:SecOrder) : list predicate :=
  match α with
    predSO P _ => cons P nil
  | relatSO _ _ => nil
  | eqFO _ _ => nil
  | allFO _ β => preds_in β
  | exFO _ β => preds_in β
  | negSO β => preds_in β
  | conjSO β1 β2 => (preds_in β1) ++ (preds_in β2)
  | disjSO β1 β2 => (preds_in β1) ++ (preds_in β2)
  | implSO β1 β2 => (preds_in β1) ++ (preds_in β2)
  | allSO P β => P :: (preds_in β)
  | exSO P β => P :: (preds_in β)
  end.

(* Function that quantifies over the predicates in the given list. *)
Fixpoint list_closed_SO (α:SecOrder) (l: list predicate) : SecOrder :=
  match l with
    nil => α
  | cons P ls => allSO P (list_closed_SO α ls)
  end.

(* Universally closes SO formulas. *)
Definition uni_closed_SO (alpha:SecOrder) : SecOrder :=
  list_closed_SO alpha (preds_in alpha).

Definition rem_pred l P := remove predicate_dec P l.

Lemma rem_pred_app : forall l1 l2 P,
  rem_pred (app l1 l2) P =
  app (rem_pred l1 P) (rem_pred l2 P).
Proof.
  induction l1; intros l2 P. auto. simpl. 
  rewrite IHl1. destruct (predicate_dec P a); auto.
Qed.

Lemma is_in_pred_rem_pred_eq : forall l P,
  ~ In P (rem_pred l P).
Proof.
  induction l; intros P. auto.
  simpl. destruct (predicate_dec P a); firstorder.
Qed.

Lemma jj13 : forall l P Q,
    ~ P = Q ->
  In P (rem_pred l Q) <-> In P l.
Proof.
  induction l; intros P Q Hbeq. firstorder.
  simpl. destruct (predicate_dec Q a). subst.
    split; intros. firstorder. apply IHl. auto. 
    destruct H. subst. firstorder. firstorder.

    simpl. firstorder.
Qed.

Lemma rem_pred_not_in : forall l P,
  ~ In P l -> rem_pred l P = l.
Proof.
  induction l; intros P H. auto.
  simpl in *. rewrite predicate_dec_r. rewrite IHl.
  all : firstorder.
Qed.

Lemma in_rem_pred : forall lP P Q,
  ~ P = Q ->  In Q (rem_pred lP P) <-> In Q lP.
Proof.
  induction lP; intros P Q Hneq. firstorder.
  simpl in *. specialize (IHlP _ _ Hneq).
  destruct (predicate_dec P a); subst; simpl; firstorder.
Qed.

Lemma incl_rem_pred : forall l1 l2 P,
  incl l1 l2 ->  incl (rem_pred l1 P) (rem_pred l2 P).
Proof.
  induction l1; intros l2 P H. firstorder.
  simpl in *. destruct (predicate_dec P a); subst. 
  + apply incl_lcons in H. auto. 
  + apply incl_cons. apply incl_hd in H.
    apply in_rem_pred; auto.
    apply incl_lcons in H. auto.
Qed.

Lemma rem_pred_cons_same : forall l P,
  rem_pred (cons P l) P = rem_pred l P.
Proof. intros l P. simpl. pred_dec_l_rep. Qed.

Lemma incl_rem_pred_cons : forall l1 l2 P Q,
  incl l1 (cons Q l2) ->
  incl (rem_pred l1 P) (cons Q (rem_pred l2 P)).
Proof.
  induction l1; intros l2 P Q H; simpl in *. 
  if_then_else_hyp_dep. firstorder.
  destruct (predicate_dec P a); subst.
  + apply incl_lcons in H. auto.
  + pose proof (incl_hd _ _ _ _ H) as H2. 
    apply incl_cons. simpl in *. destruct H2. firstorder.
    right. apply in_rem_pred; auto.
    apply IHl1; auto. simpl in *. 
    pose proof ( in_rem_pred). firstorder.
Qed.

Lemma incl_rem_pred_l : forall l P,
  incl (rem_pred l P) l.
Proof.
  induction l; intros P. firstorder.
  simpl. destruct (predicate_dec P a). subst. 
  firstorder. apply incl_cons_cons. auto.
Qed.

Fixpoint cap_pred_empty l1 l2 : bool :=
  match l1 with
  | nil => true
  | cons P l1' => if in_predicate_dec P l2 then false
                    else cap_pred_empty l1' l2
  end.

Fixpoint cap_pred l1 l2 :=
  match l1 with
  | nil => nil
  | cons P l1' => if in_predicate_dec P l2 then cons P (cap_pred l1' l2)
          else cap_pred l1' l2
  end.


Lemma in_cap_pred : forall l2 l1 P,
  ~ In P l1 ->  ~ In P (cap_pred l2 l1).
Proof.
  induction l2; intros l1 P H. auto.
  simpl. destruct (in_predicate_dec a l1).
  simpl. intros [H2 | H2]. subst. contradiction. 
  apply IHl2 in H. contradiction.
  apply IHl2. auto.
Qed.

Lemma in_pred_cap_pred : forall l1 l2 P,
  In P l1 -> In P l2 -> In P (cap_pred l1 l2).
Proof.
  induction l1; intros l2 P H1 H2. contradiction.
  simpl in *. destruct (predicate_dec a P). subst.
  destruct (in_predicate_dec P l2); firstorder.
  destruct H1. firstorder. destruct (in_predicate_dec a l2); firstorder.
Qed.

Lemma in_pred_cap_pred_t : forall l1 l2 P,
  In P (cap_pred l1 l2) ->  (In P l1 /\ In P l2).
Proof.
  induction l1; intros l2 P H. contradiction.
  simpl in *. destruct (in_predicate_dec a l2) as [H2 | H2].
  simpl in H. destruct H. subst. firstorder. apply IHl1 in H.
  firstorder. apply IHl1 in H. firstorder.
Qed.

Lemma in_pred_cap_pred_f : forall l1 l2 P,
  ~ In P (cap_pred l1 l2) ->  ~ In P l1  \/ ~ In P l2.
Proof.
  induction l1; intros l2 P H. auto.
  simpl in *. destruct (in_predicate_dec a l2);
  simpl in *; specialize (IHl1 l2 P).  firstorder.
  firstorder. destruct (predicate_dec a P).
  subst. firstorder. firstorder.
Qed.   

Lemma in_pred_cap_pred_f1 : forall l1 l2 P,
  ~ In P l1 -> ~ In P (cap_pred l1 l2).
Proof.
  induction l1; intros l2 P H. auto.
  simpl in *. destruct (in_predicate_dec a l2).
  simpl. specialize (IHl1 l2 P). firstorder. firstorder.
Qed.

Lemma in_pred_cap_pred_f2 : forall l1 l2 P,
  ~ In P l2 -> ~ In P (cap_pred l1 l2).
Proof.
  induction l1; intros l2 P H. auto.
  simpl in *. destruct (in_predicate_dec a l2).
  simpl. destruct (predicate_dec a P); 
  subst; firstorder. auto.
Qed.

Lemma cap_pred_comm : forall l1 l2 P,
  In P (cap_pred l1 l2) <-> In P (cap_pred l2 l1).
Proof.
  intros. split; intros H;  apply in_pred_cap_pred_t in H;
   apply in_pred_cap_pred; firstorder.
Qed.

Lemma lem_b1 : forall lP alpha1 alpha2,
~ lP = nil ->
incl lP (preds_in (conjSO alpha1 alpha2)) ->
cap_pred lP (preds_in alpha1) = nil ->
~ cap_pred lP (preds_in alpha2) = nil.
Proof.
  induction lP; intros alpha1 alpha2 HlP Hin Hcap. contradiction.
  simpl in *. destruct (in_predicate_dec a (preds_in alpha1)). discriminate.
  destruct (in_predicate_dec a (preds_in alpha2)). firstorder.
  apply incl_hd in Hin. apply in_app_or in Hin. firstorder.
Qed.

Lemma lem_b1_l : forall lP alpha1 alpha2,
~ lP = nil ->
incl lP (preds_in (conjSO alpha1 alpha2)) ->
cap_pred lP (preds_in alpha2) = nil ->
~ cap_pred lP (preds_in alpha1) = nil.
Proof.
  induction lP; intros alpha1 alpha2 HlP Hin Hcap. contradiction.
  simpl in *. destruct (in_predicate_dec a (preds_in alpha1)). discriminate.
  destruct (in_predicate_dec a (preds_in alpha2)). discriminate.
  apply incl_hd in Hin. apply in_app_or in Hin. firstorder.
Qed. 

Lemma incl_cap_pred : forall lP l1 l2,
incl lP (app l1 l2) -> cap_pred lP l1 = nil ->
incl lP l2 .
Proof.
  induction lP; intros l1 l2 Hin Hcap. firstorder.
  simpl in *. 
  destruct (in_predicate_dec a l1). discriminate.
  apply incl_cons. apply incl_hd in Hin.
  apply in_app_or in Hin. firstorder.
  apply incl_lcons in Hin. firstorder.
Qed.

Lemma incl_cap_pred_l : forall lP l1 l2,
incl lP (app l1 l2)  ->
cap_pred lP l2 = nil ->
incl lP l1.
Proof.
  induction lP; intros l1 l2 Hin Hcap. firstorder.
  simpl in *. 
  destruct (in_predicate_dec a l2). discriminate.
  apply incl_cons. apply incl_hd in Hin.
  apply in_app_or in Hin. firstorder.
  apply incl_lcons in Hin. firstorder.
Qed.

Lemma incl_cap_pred_f : forall lP l1 l2,
~ lP = nil ->
incl lP (app l1 l2) ->
cap_pred lP l1 = nil ->
~ incl lP l1.
Proof.
  induction lP; intros l1 l2 Hnot Hin Hcap. contradiction.
  simpl in *. 
  destruct (in_predicate_dec a l1). discriminate.
  destruct lP. firstorder.
  intros HH. apply incl_lcons in HH. generalize HH.
  eapply IHlP; auto. discriminate. 
  apply incl_lcons in Hin. apply Hin.
Qed.

Lemma incl_cap_pred_f_l : forall lP l1 l2,
~ lP = nil ->
incl lP (app l1 l2) ->
cap_pred lP l2 = nil ->
~ incl lP l2.
Proof.
  induction lP; intros l1 l2 Hnot Hin Hcap. contradiction.
  simpl in *. 
  destruct (in_predicate_dec a l2). discriminate. 
  destruct lP. firstorder.
  intros HH. apply incl_lcons in HH. generalize HH.
  eapply IHlP; auto. discriminate. 
  apply incl_lcons in Hin. apply Hin.  
Qed.

Lemma incl_cap_pred_add : forall l1 l2 l3,
  incl l2 l3  ->
  incl (cap_pred l1 l2) l3.
Proof.
  induction l1; intros l2 l3 Hin1. firstorder. 
  simpl. destruct (in_predicate_dec a l2); auto. simpl.
  eapply in_incl in i. 2 : apply Hin1.
  apply incl_cons; auto. 
Qed.

Lemma rem_pred_nil : forall lP P,
  rem_pred lP P = nil ->
  exists n, lP = repeat P n.
Proof.
  induction lP; intros P Hrem. exists 0. auto.
  simpl in *. destruct (predicate_dec P a). 2 : discriminate.
  subst. apply IHlP in Hrem. destruct Hrem as [mm Hmm].
  exists (S mm). simpl. rewrite Hmm. auto.
Qed.