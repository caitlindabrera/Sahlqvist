Require Export low_mods.
Require Import Indicies Rep_Pred_FOv.


Definition num_occ (alpha : SecOrder) (Q : predicate) : nat :=
  length (indicies alpha Q).

Lemma num_occ_conjSO2 : forall (alpha1 alpha2 : SecOrder) (Q : predicate),
  num_occ (conjSO alpha1 alpha2) Q =  (length (indicies alpha1 Q)) +
                                       (length (indicies alpha2 Q)).
Proof.
  intros.
  unfold num_occ.
  rewrite indicies_conjSO.
  rewrite app_length.
  unfold indicies.
  do 3 rewrite map_length.
  reflexivity.
Qed.

Lemma num_occ_disjSO2 : forall (alpha1 alpha2 : SecOrder) (Q : predicate),
  num_occ (disjSO alpha1 alpha2) Q =  (length (indicies alpha1 Q)) +
                                       (length (indicies alpha2 Q)).
Proof.
  intros.
  unfold num_occ.
  rewrite indicies_disjSO.
  rewrite app_length.
  unfold indicies.
  do 3 rewrite map_length.
  reflexivity.
Qed.

Lemma num_occ_predSO : forall (P Q : predicate) (x : FOvariable),
  num_occ (predSO P x) Q = if predicate_dec P Q then 1 else 0.
Proof.
  intros. unfold num_occ.  unfold indicies.
  simpl. destruct (predicate_dec P Q); subst; auto.
Qed.

Lemma num_occ_allSO : forall (alpha : SecOrder) (P Q : predicate),
  num_occ (allSO P alpha) Q = if predicate_dec P Q then 1 + num_occ alpha Q
                              else num_occ alpha Q.
Proof.
  intros. unfold num_occ. unfold indicies. do 2 rewrite map_length.
  destruct (predicate_dec P Q). subst.
  simpl. rewrite predicate_dec_l; auto. 
  simpl. rewrite predicate_dec_r; auto. 
Qed.

Lemma num_occ_exSO : forall (alpha : SecOrder) (P Q : predicate),
  num_occ (exSO P alpha) Q = if predicate_dec P Q then 1 + num_occ alpha Q
                              else num_occ alpha Q.
Proof.
  intros. unfold num_occ. unfold indicies. do 2 rewrite map_length.
  destruct (predicate_dec P Q). subst.
  simpl. rewrite predicate_dec_l; auto. 
  simpl. rewrite predicate_dec_r; auto. 
Qed.

Lemma num_occ_exSO_eq : forall (alpha : SecOrder) (Q : predicate),
  num_occ (exSO Q alpha) Q = 1 + num_occ alpha Q.
Proof.
  intros alpha Q. unfold num_occ. unfold indicies.
  simpl. rewrite predicate_dec_l; auto.
  do 2  rewrite map_length. simpl. auto.
Qed.

Lemma num_occ_exSO_not_eq : forall (alpha : SecOrder) (P Q : predicate),
P <> Q ->
  num_occ (exSO P alpha) Q =  num_occ alpha Q.
Proof.
  intros alpha P Q H. unfold num_occ. unfold indicies.
  simpl. rewrite predicate_dec_r; auto.
  do 2  rewrite map_length. auto.
Qed.

Lemma num_occ_not_in : forall (alpha : SecOrder) (P : predicate),
 ~ In P (preds_in alpha) -> num_occ alpha P = 0.
Proof.
  intros alpha P Hocc. unfold num_occ. rewrite length_ind.
  apply indicies_l_rev_not_in. auto.
Qed.

(* ---------------------------------------------------------  *)

Fixpoint num_occ_diff_l (l : list nat) (i : nat) : nat :=
  if in_dec Nat.eq_dec i l then 0 else
  match l with
  | nil => 0
  | cons n l' => if le_le_S_dec n i 
                    then 1 + num_occ_diff_l l' i
                    else num_occ_diff_l l' i
  end.

Lemma num_occ_diff_l_defn : forall (l : list nat) (i : nat),
  num_occ_diff_l l i =
  if in_dec Nat.eq_dec i l then 0 else
  match l with
  | nil => 0
  | cons n l' => if le_le_S_dec n i 
                    then 1 + num_occ_diff_l l' i
                    else num_occ_diff_l l' i
  end.
Proof. induction l; auto. Qed.

Lemma num_occ_diff_l_cons : forall (l : list nat) (a i : nat),
  num_occ_diff_l (cons a l) i =
  if in_dec Nat.eq_dec i (a::l) then 0 else
 if le_le_S_dec a i 
                    then 1 + num_occ_diff_l l i
                    else num_occ_diff_l l i.
Proof. auto. Qed.

Lemma num_occ_diff_l_app : forall (l1 l2 : list nat) (i : nat),
  ~ In i l1 -> ~ In i l2 ->
      num_occ_diff_l (app l1 l2) i =
        (num_occ_diff_l l1 i) + (num_occ_diff_l l2 i).
Proof.
  induction l1; intros l2 i H1 H2. auto.
  rewrite num_occ_diff_l_cons.
  destruct (in_dec _ i (a :: l1)). contradiction.
  simpl app. rewrite num_occ_diff_l_cons.
  destruct (in_dec Nat.eq_dec i (a :: l1 ++ l2)) as [H4 | H4].
  simpl in H4. destruct H4 as [H4 | H4]. firstorder.
  apply in_app_or in H4. firstorder.
  rewrite IHl1; auto.
  destruct (le_le_S_dec a i); firstorder. firstorder.
Qed.

Definition num_occ_diff (alpha : SecOrder) (Q : predicate) (i : nat)
                                              : nat :=
  num_occ_diff_l (indicies alpha Q) i.


Lemma num_occ_diff_relatSO : forall ( x y : FOvariable)
                                   (Q : predicate) (i : nat),
  num_occ_diff (relatSO x y) Q i = 0.
Proof.
  intros x y Q i.
  unfold num_occ_diff.
  unfold indicies.
  destruct x; destruct y.
  simpl.
  reflexivity.
Qed.

Lemma num_occ_diff_eqFO : forall ( x y : FOvariable)
                                   (Q : predicate) (i : nat),
  num_occ_diff (eqFO x y) Q i = 0.
Proof.
  intros x y Q i.
  unfold num_occ_diff.
  unfold indicies.
  destruct x; destruct y.
  simpl.
  reflexivity.
Qed.


Lemma num_occ_diff_allFO : forall (alpha : SecOrder) (x : FOvariable)
                                  (Q : predicate) (i : nat),
  num_occ_diff (allFO x alpha) Q i = 
    num_occ_diff alpha Q i.
Proof.
  intros.
  unfold num_occ_diff.
  unfold num_occ_diff_l.
  reflexivity.
Qed.

Lemma num_occ_diff_exFO : forall (alpha : SecOrder) (x : FOvariable)
                                  (Q : predicate) (i : nat),
  num_occ_diff (exFO x alpha) Q i = 
    num_occ_diff alpha Q i.
Proof.
  intros.
  unfold num_occ_diff.
  unfold num_occ_diff_l.
  unfold indicies.
  simpl.
  destruct x.
  reflexivity.
Qed.

Lemma num_occ_diff_negSO : forall (alpha : SecOrder)
                                  (Q : predicate) (i : nat),
  num_occ_diff (negSO alpha) Q i = 
    num_occ_diff alpha Q i.
Proof.
  intros.
  unfold num_occ_diff.
  unfold num_occ_diff_l.
  unfold indicies.
  simpl.
  reflexivity.
Qed.

(* ------------------------------------------------------------- *)



Lemma num_occ_diff_l_nil : forall (l : list nat),
  (num_occ_diff_l l 0) = 0.
Proof.
  induction l. auto.  destruct a. auto.
  simpl. rewrite IHl. 
  if_then_else_dest_blind; auto.
Qed.

Lemma num_occ_diff_nil : forall (alpha : SecOrder) (P : predicate),
  (num_occ_diff alpha P 0) = 0.
Proof.
  intros. unfold num_occ_diff.
  apply num_occ_diff_l_nil.
Qed.


(* ------------------------------------------------------------- *)


Lemma num_occ_relatSO : forall (x y : FOvariable) (Q : predicate),
   num_occ (relatSO x y) Q = 0.
Proof.
  intros.
  destruct x; destruct y; destruct Q.
  unfold num_occ.
  unfold indicies.
  simpl.
  reflexivity.
Qed.


Lemma num_occ_eqFO : forall (x y : FOvariable) (Q : predicate),
   num_occ (eqFO x y) Q = 0.
Proof.
  intros.
  destruct x; destruct y; destruct Q.
  unfold num_occ.
  unfold indicies.
  simpl.
  reflexivity.
Qed.



Lemma num_occ_negSO : forall (alpha : SecOrder) (P : predicate),
  num_occ (negSO alpha) P = num_occ alpha P.
Proof.
   intros.
  unfold num_occ.
  unfold indicies.
  simpl.
  reflexivity.
Qed.

Lemma num_occ_allFO : forall (alpha : SecOrder) (x : FOvariable)
                             (P : predicate),
  num_occ (allFO x alpha) P = num_occ alpha P.
Proof.
   intros.
  unfold num_occ.
  unfold indicies.
  simpl.
  reflexivity.
Qed.

Lemma num_occ_exFO : forall (alpha : SecOrder) (x : FOvariable)
                             (P : predicate),
  num_occ (exFO x alpha) P = num_occ alpha P.
Proof.
   intros.
  unfold num_occ.
  unfold indicies.
  simpl.
  destruct x.
  reflexivity.
Qed.

Lemma num_occ_conjSO : forall (alpha1 alpha2 : SecOrder)
                             (P : predicate),
  num_occ (conjSO alpha1 alpha2) P = num_occ alpha1 P + num_occ alpha2 P.
Proof.
   intros.
  unfold num_occ.
  unfold indicies.
  simpl.
  rewrite app_length.
  rewrite map_length.
  rewrite map_length.
  rewrite map_length.
  rewrite indicies_l_rev_app.
  rewrite app_length.
  rewrite map_length.
  reflexivity.
Qed.

Lemma num_occ_disjSO : forall (alpha1 alpha2 : SecOrder)
                             (P : predicate),
  num_occ (disjSO alpha1 alpha2) P = num_occ alpha1 P + num_occ alpha2 P.
Proof.
   intros.
  unfold num_occ.
  unfold indicies.
  simpl.
  rewrite app_length.
  rewrite map_length.
  rewrite map_length.
  rewrite map_length.
  rewrite indicies_l_rev_app.
  rewrite app_length.
  rewrite map_length.
  reflexivity.
Qed.

Lemma num_occ_implSO : forall (alpha1 alpha2 : SecOrder)
                             (P : predicate),
  num_occ (implSO alpha1 alpha2) P = num_occ alpha1 P + num_occ alpha2 P.
Proof.
   intros.
  unfold num_occ.
  unfold indicies.
  simpl.
  rewrite app_length.
  rewrite map_length.
  rewrite map_length.
  rewrite map_length.
  rewrite indicies_l_rev_app.
  rewrite app_length.
  rewrite map_length.
  reflexivity.
Qed.

Lemma num_occ_preds_in : forall (alpha : SecOrder) (P : predicate),
  (num_occ alpha P) <= (length (preds_in alpha)).
Proof.
  intros alpha P. unfold num_occ. unfold indicies.
  rewrite map_length. apply le_indicies_l_rev.
Qed.

Lemma  num_occ_ind_l_rev : forall (alpha : SecOrder) (P : predicate),
  num_occ alpha P = length (indicies_l_rev (preds_in alpha) P).
Proof.
  intros alpha P.
  unfold num_occ.
  unfold indicies.
  rewrite map_length.
  reflexivity.
Qed.

Lemma num_occ_rep_pred : forall alpha cond P x,
FO_frame_condition cond = true ->
num_occ (replace_pred alpha P x cond) P = 0.
Proof.
  intros alpha cond P x Hcond.
  unfold num_occ.
  rewrite length_ind.
  induction alpha;
    simpl in *; try reflexivity;
    try assumption;
    try (rewrite indicies_l_rev_app; rewrite app_length;
    rewrite map_length;
    rewrite IHalpha1; rewrite IHalpha2;
    reflexivity).
    destruct (predicate_dec P p) as [H1 | H1].
      subst. rewrite preds_in_rep_FOv.
      rewrite FO_frame_condition_preds_in; auto.

      simpl. rewrite predicate_dec_r; auto.

    destruct (predicate_dec P p) as [H1 | H1].
      subst. rewrite IHalpha. reflexivity. simpl.
      rewrite predicate_dec_r; auto.

    destruct (predicate_dec P p) as [H1 | H1]; auto.
    simpl. rewrite predicate_dec_r; auto.
Qed.

Lemma num_occ_rep_pred_0 : forall (alpha cond : SecOrder) (P Q : predicate)
                                  (x : FOvariable),
FO_frame_condition cond = true ->
num_occ alpha P = 0 ->
num_occ (replace_pred alpha Q x cond) P = 0.
Proof.
  induction alpha; intros cond P Q x Hcond Hnum;
  unfold num_occ in *; rewrite length_ind in *;
  simpl in *; auto;
    try (simpl in *;
    specialize (IHalpha cond P Q x Hcond);
    do 2 rewrite length_ind in *;
    apply IHalpha; auto);
try (    rewrite indicies_l_rev_app in *;
    rewrite app_length in *;
    rewrite map_length in *;
    do 2 rewrite <- length_ind in *;
    rewrite IHalpha1; [rewrite IHalpha2| |]; auto;
    firstorder).

    destruct (predicate_dec Q p) as [H1 | H1].
    inversion H1. subst.  
      apply rep_FOv_FO_frame_condition with (x := x) (y := f) in Hcond.
      apply FO_frame_condition_preds_in in Hcond.
      rewrite Hcond. auto. auto.

    destruct (predicate_dec p P). subst. discriminate.
    destruct (predicate_dec Q p). subst. unfold indicies in IHalpha.
    erewrite <- IHalpha. rewrite map_length. reflexivity. auto. 
    rewrite map_length. auto.
    simpl. rewrite predicate_dec_r. unfold indicies in IHalpha.
    erewrite <- IHalpha. rewrite map_length. reflexivity. auto.
    rewrite map_length. auto. auto.
    
    destruct (predicate_dec p P). subst. discriminate.
    destruct (predicate_dec Q p). subst. unfold indicies in IHalpha.
    erewrite <- IHalpha. rewrite map_length. reflexivity. auto. 
    rewrite map_length. auto.
    simpl. rewrite predicate_dec_r. unfold indicies in IHalpha.
    erewrite <- IHalpha. rewrite map_length. reflexivity. auto.
    rewrite map_length. auto. auto.
Qed.

Lemma num_occ_rep_pred__l_0 : forall (alpha : SecOrder) l l1 l2 P Q x cond,
FO_frame_condition_l l2 = true ->
FO_frame_condition cond = true ->
num_occ (replace_pred_l alpha l l1 l2) P = 0 ->
num_occ (replace_pred (replace_pred_l alpha l l1 l2) Q x cond) P = 0.
Proof.
  intros alpha l l1 l2 P Q x cond Hun1 Hun2 Hnum.
  apply num_occ_rep_pred_0; assumption.
Qed.

Lemma num_occ_rep_pred2 : forall (alpha cond : SecOrder) 
                                 (P Q : predicate) (x : FOvariable),
FO_frame_condition cond = true ->
~ P = Q ->
num_occ (replace_pred alpha P x cond) Q =
num_occ alpha Q.
Proof.
  intros alpha cond P Q x Hcond Hbeq. unfold num_occ.
  do 2 rewrite length_ind.
  induction alpha;
    try reflexivity;
    try (    simpl; assumption);
    try (simpl; do 2 rewrite indicies_l_rev_app;
    do 2 rewrite app_length;
    do 2 rewrite map_length;
    rewrite IHalpha1;
    rewrite IHalpha2;
    reflexivity);

    simpl. destruct (predicate_dec P p). subst. rewrite predicate_dec_r; auto.
    rewrite preds_in_rep_FOv; rewrite FO_frame_condition_preds_in; auto. auto.

    simpl. destruct (predicate_dec P p). subst. rewrite predicate_dec_r; auto.
    simpl. destruct (predicate_dec p Q). subst. simpl. rewrite IHalpha. auto.
    apply IHalpha.

    simpl. destruct (predicate_dec P p). subst. rewrite predicate_dec_r; auto.
    simpl. destruct (predicate_dec p Q). subst. simpl. rewrite IHalpha. auto.
    apply IHalpha.
Qed.

(* ----------------------------------------------------------------------- *)

Lemma preds_in_rep_pred_allSO : forall (alpha cond : SecOrder) (P Q : predicate)
                                 (x : FOvariable),
  (length (preds_in (replace_pred alpha Q x cond)) =
          length (preds_in alpha) -
          length (indicies_l_rev (preds_in alpha) Q)) ->
    length (preds_in (replace_pred (allSO P alpha) Q x cond)) =
      length (preds_in (allSO P alpha)) -
        length (indicies_l_rev (preds_in (allSO P alpha)) Q).
Proof.
  intros alpha cond P Q x IHalpha. simpl.
  dest_pred_dec P Q. simpl. rewrite IHalpha.
  case_eq (length (indicies_l_rev (preds_in alpha) Q)).
    intros Hnil. lia.
  intros m Hm. rewrite Minus.minus_Sn_m. lia. 
  rewrite <- Hm. apply le_indicies_l_rev.
Qed.

Lemma preds_in_rep_pred_exSO : forall (alpha cond : SecOrder) (P Q : predicate)
                                 (x : FOvariable),
  (length (preds_in (replace_pred alpha Q x cond)) =
          length (preds_in alpha) -
          length (indicies_l_rev (preds_in alpha) Q)) ->
    length (preds_in (replace_pred (exSO P alpha) Q x cond)) =
      length (preds_in (exSO P alpha)) -
        length (indicies_l_rev (preds_in (exSO P alpha)) Q).
Proof.
  intros alpha cond P Q x IHalpha. simpl.
  dest_pred_dec P Q. simpl. rewrite IHalpha.
  case_eq (length (indicies_l_rev (preds_in alpha) Q)).
    intros Hnil. lia.
  intros m Hm. rewrite Minus.minus_Sn_m. lia. 
  rewrite <- Hm. apply le_indicies_l_rev.
Qed. 

Lemma preds_in_rep_pred : forall (alpha cond : SecOrder) (Q : predicate)
                                 (x : FOvariable),
  FO_frame_condition cond = true ->
    (length (preds_in (replace_pred alpha Q x cond)))
      = length (preds_in alpha) - num_occ alpha Q.
Proof.
  intros alpha cond Q x Hcond.
  unfold num_occ.
  rewrite length_ind.
  induction alpha; try reflexivity; try auto.

  simpl. dest_pred_dec Q p. simpl. rewrite preds_in_rep_FOv.
  rewrite FO_frame_condition_preds_in; auto.

  simpl. do 2 rewrite app_length.
  rewrite indicies_l_rev_app. rewrite app_length. rewrite map_length.
  rewrite IHalpha1. rewrite IHalpha2. do 2 rewrite <- num_occ_ind_l_rev.
  pose proof (num_occ_preds_in alpha1 Q).
  pose proof (num_occ_preds_in alpha2 Q). lia.

  simpl. do 2 rewrite app_length.
  rewrite indicies_l_rev_app. rewrite app_length. rewrite map_length.
  rewrite IHalpha1. rewrite IHalpha2. do 2 rewrite <- num_occ_ind_l_rev.
  pose proof (num_occ_preds_in alpha1 Q).
  pose proof (num_occ_preds_in alpha2 Q). lia.

  simpl. do 2 rewrite app_length.
  rewrite indicies_l_rev_app. rewrite app_length. rewrite map_length.
  rewrite IHalpha1. rewrite IHalpha2. do 2 rewrite <- num_occ_ind_l_rev.
  pose proof (num_occ_preds_in alpha1 Q).
  pose proof (num_occ_preds_in alpha2 Q). lia.

  apply preds_in_rep_pred_allSO; auto.
  apply preds_in_rep_pred_exSO; auto.
Qed.

(* ----------------------------------------------------------------------- *)

Lemma num_occ__in_l_t : forall l alpha a l1 l2,
FO_frame_condition_l (nlist_list _ l2) = true ->
In a l ->
(num_occ (replace_pred_l alpha l (nlist_list (length l) l1) (nlist_list (length l) l2)) a) = 0.
Proof.
  induction l; intros  alpha P l1 l2 Hun Hocc. contradiction.
  destruct (nlist_cons2 _ l1) as [x [l1' H1]].
  destruct (nlist_cons2 _ l2) as [beta [l2' H2]].
  rewrite H1 in *.
  rewrite H2 in *.
  simpl in *.
  destruct (predicate_dec P a). subst.
    apply num_occ_rep_pred.
    case_eq (FO_frame_condition beta); intros H.
      reflexivity.
      rewrite H in *; discriminate.
      destruct Hocc as [? | Hocc]. subst. contradiction.

    specialize (IHl alpha P l1' l2').
    case_eq (FO_frame_condition beta); intros Hbeta;
      rewrite Hbeta in *; try discriminate.
    specialize (IHl Hun Hocc).
    apply num_occ_rep_pred__l_0; assumption.
Qed.

Lemma num_occ__in_l_f : forall alpha l a l1' l2',
FO_frame_condition_l (nlist_list _ l2') = true ->
~ In a l ->
num_occ (replace_pred_l alpha l (nlist_list (length l) l1') 
    (nlist_list (length l) l2')) a = num_occ alpha a.
Proof.
  intros alpha l.
  induction l; intros P l1 l2 Hun Hocc.
    simpl in *.
    reflexivity.

    destruct (nlist_cons2 _ l1) as [x [l1' H1]].
    destruct (nlist_cons2 _ l2) as [beta [l2' H2]].
    rewrite H1 in *. rewrite H2 in *.
    simpl in *. destruct (predicate_dec a P). firstorder.
    specialize (IHl P l1' l2').
    case_eq (FO_frame_condition beta); intros Hbeta;
      rewrite Hbeta in *; try discriminate.
      specialize (IHl Hun).
      rewrite num_occ_rep_pred2; auto.
Qed.