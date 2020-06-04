Require Import preds_in List Lia.

(* Takes in a list of predicates and returns a list of reverse indicies at which Q occurs in l. *)
Fixpoint indicies_l_rev (l : list predicate) (Q : predicate) : list nat :=
  match l with 
  | nil => nil
  | cons P l' => if predicate_dec P Q then cons (length l) (indicies_l_rev l' Q)
                                      else indicies_l_rev l' Q
  end.

Lemma indicies_l_rev_cons : forall (l : list predicate) (P Q : predicate),
  indicies_l_rev (cons P l) Q
  = if predicate_dec P Q then cons (length (cons P l)) (indicies_l_rev l Q)
                                      else indicies_l_rev l Q.
Proof. auto. Qed.

Lemma indicies_l_rev_app : forall (l1 l2 : list predicate) (Q : predicate),
    indicies_l_rev (app l1 l2) Q 
  = app (map (fun n:nat => length l2 + n) (indicies_l_rev l1 Q))
                   (indicies_l_rev l2 Q).
Proof.
  induction l1; intros l2 Q. auto.
  simpl. destruct (predicate_dec a Q). subst. simpl. rewrite IHl1.
  rewrite app_length. rewrite PeanoNat.Nat.add_comm.
  rewrite PeanoNat.Nat.add_succ_r.  auto.
  apply IHl1.
Qed.

(* -------------------------------------------------------------------------- *)

(* Takes in a list of predicates and returns a list of indicies at which Q occurs in l. *)
Definition indicies (alpha :SecOrder) (Q : predicate) : list nat :=
  map (fun n:nat => length (preds_in alpha) + 1 - n)
           (indicies_l_rev (preds_in alpha) Q).


Lemma indicies_conjSO : forall (alpha1 alpha2 : SecOrder) (P : predicate),
  indicies (conjSO alpha1 alpha2) P
  = app (map (fun n:nat => length (preds_in alpha1) + 1 - n)
                (indicies_l_rev (preds_in alpha1) P))
        (map (fun n:nat => length (preds_in alpha1 ++ preds_in alpha2) + 1 - n)
                (indicies_l_rev (preds_in alpha2) P)).
Proof.
  intros. unfold indicies. simpl.
  rewrite indicies_l_rev_app.
  rewrite map_app. rewrite map_map.
  rewrite app_length. 
  assert (forall a b l, 
             map (fun x : nat => a + b + 1 - (b + x)) l = 
             map (fun x : nat => a + 1 - x) l) as Hass.  
  intros. apply map_ext. intros. lia. rewrite Hass. auto.
Qed.

Lemma indicies_disjSO : forall (alpha1 alpha2 : SecOrder) (P : predicate),
  indicies (disjSO alpha1 alpha2) P
  = app (map (fun n:nat => length (preds_in alpha1) + 1 - n)
                (indicies_l_rev (preds_in alpha1) P))
        (map (fun n:nat => length (preds_in alpha1 ++ preds_in alpha2) + 1 - n)
                (indicies_l_rev (preds_in alpha2) P)).
Proof.
  intros. unfold indicies. simpl.
  rewrite indicies_l_rev_app.
  rewrite map_app. rewrite map_map.
  rewrite app_length.
  assert (forall a b l, 
             map (fun x : nat => a + b + 1 - (b + x)) l = 
             map (fun x : nat => a + 1 - x) l) as Hass.
  intros. apply map_ext. firstorder. rewrite Hass. auto.
Qed.

Lemma le_indicies_l_rev : forall (l : list predicate) (P : predicate),
  (length (indicies_l_rev l P)) <= (length l).
Proof.
  induction l; intros P. firstorder.
  simpl. destruct (predicate_dec a P); simpl; firstorder.
Qed.

Lemma length_ind : forall (alpha : SecOrder) (P : predicate),
  length (indicies (alpha) P) = length (indicies_l_rev (preds_in alpha) P).
Proof.
  intros; unfold indicies.
  rewrite map_length. auto.
Qed.

Lemma indicies_l_rev_not_in : forall l P,
~ In P l ->  length (indicies_l_rev l P) = 0.
Proof.
  induction l; intros P H. auto.
  simpl. rewrite predicate_dec_r. 2 : firstorder.
  apply IHl; firstorder.
Qed.