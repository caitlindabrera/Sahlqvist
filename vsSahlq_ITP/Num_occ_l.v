Require Export low_mods.
Require Import Num_Occ Indicies.

Fixpoint num_occ_l (l : list predicate) (P : predicate) : nat :=
  match l with
  | nil => 0
  | cons Q l' => if predicate_dec P Q then 1 + num_occ_l l' P
                                   else num_occ_l l' P
  end.

Lemma num_occ_l_app : forall (l1 l2 : list predicate) (P : predicate),
  num_occ_l (app l1 l2) P = num_occ_l l1 P + num_occ_l l2 P.
Proof.
  induction l1.  intros. reflexivity.
  intros l2 P. simpl. rewrite IHl1. 
  destruct (predicate_dec P a); lia.
Qed.

Lemma leb_num_occ : forall (alpha : SecOrder) (P : predicate),
  (num_occ_l (preds_in alpha) P) <= (length (preds_in alpha)).
Proof.
  intros alpha P.
  induction alpha; simpl; auto;
  try (destruct (predicate_dec P p); auto);
  try (  rewrite num_occ_l_app; rewrite app_length; lia);
  lia.
Qed.

Lemma leb_id_fwd_plus : forall (alpha1 alpha2: SecOrder) (P : predicate) 
                                    (n: nat),
   n <=
      (length (preds_in alpha1) - num_occ_l (preds_in alpha1) P) ->
   n <=
      (length (preds_in alpha1) + length (preds_in alpha2) -
        (num_occ_l (preds_in alpha1) P + 
           num_occ_l (preds_in alpha2) P)).
Proof.
  intros alpha1 alpha2 P n Hleb.
  pose proof (leb_num_occ alpha2 P). firstorder.
Qed.

Lemma num_occ_l_ind_l_rev : forall l P,
  num_occ_l l P = length (indicies_l_rev l P).
Proof.
  induction l; intros P. auto.
  simpl in *. dest_pred_dec a P. simpl.
  firstorder. 
Qed.

Lemma num_occ__l : forall (alpha : SecOrder) (P : predicate),
  (num_occ_l (preds_in alpha) P) = (num_occ alpha P).
Proof.
  intros. unfold num_occ.
  unfold indicies. rewrite map_length.
  apply num_occ_l_ind_l_rev.
Qed.
