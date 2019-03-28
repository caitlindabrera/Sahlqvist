Require Export base_mods nlist_syn_eg.
Require Import preds_in Pred_in_SO.

Fixpoint SOQFree (α : SecOrder) : bool :=
  match α with
    predSO _ _  => true
  | relatSO _ _ =>  true
  | eqFO _ _    => true
  | allFO _ β => SOQFree β
  | exFO _ β  => SOQFree β
  | negSO β   => SOQFree β
  | conjSO β1 β2 => andb (SOQFree β1) (SOQFree β2)
  | disjSO β1 β2 => andb (SOQFree β1) (SOQFree β2)
  | implSO β1 β2 => andb (SOQFree β1) (SOQFree β2)
(*
if SOQFree β1 then SOQFree β2 else false
*)
  | allSO _ _ => false
  | exSO _ _  => false
  end.

Fixpoint SOQFree_l (l : list SecOrder) : bool :=
  match l with
  | nil => true
  | cons alpha l' => if SOQFree alpha then SOQFree_l l' else false
  end.

Fixpoint SOQFree_P alpha P : bool :=
  match alpha with
    predSO _ _ => true 
  | relatSO _ _ => true
  | eqFO _ _ => true 
  | allFO _ beta => SOQFree_P beta P
  | exFO _ beta => SOQFree_P beta P
  | negSO beta => SOQFree_P beta P
  | conjSO beta1 beta2 => andb (SOQFree_P beta1 P) (SOQFree_P beta2 P)
  | disjSO beta1 beta2 => andb (SOQFree_P beta1 P) (SOQFree_P beta2 P)
  | implSO beta1 beta2 => andb (SOQFree_P beta1 P) (SOQFree_P beta2 P)
  | allSO Q beta => if predicate_dec P Q then false else
      SOQFree_P beta P
  | exSO Q beta => if predicate_dec P Q then false else
      SOQFree_P beta P
  end.

Fixpoint FOQFree (alpha : SecOrder) : bool :=
  match alpha with
    predSO _ _ => true
  | relatSO _ _  =>  true
  | eqFO _ _ => true
  | allFO _ beta => false
  | exFO _ beta => false
  | negSO beta => FOQFree beta
  | conjSO beta1 beta2 => if FOQFree beta1 then FOQFree beta2 else false
  | disjSO beta1 beta2 => if FOQFree beta1 then FOQFree beta2 else false
  | implSO beta1 beta2 => if FOQFree beta1 then FOQFree beta2 else false
  | allSO _ beta => FOQFree beta 
  | exSO _ beta => FOQFree beta
  end.

Fixpoint FO_frame_condition (α : SecOrder) : bool :=
  match α with
    predSO _ _  => false
  | relatSO _ _ => true
  | eqFO _ _    => true
  | allFO _ β => FO_frame_condition β
  | exFO _ β  => FO_frame_condition β
  | negSO β   => FO_frame_condition β
  | conjSO β1 β2 => andb (FO_frame_condition β1) (FO_frame_condition β2)
  | disjSO β1 β2 => andb (FO_frame_condition β1) (FO_frame_condition β2)
  | implSO β1 β2 => andb (FO_frame_condition β1) (FO_frame_condition β2)
  | allSO _ β => false
  | exSO _ β  => false
  end.

(* -------------------------------------------------------------------- *)

Lemma FO_frame_condition_predSO : forall (P : predicate)
                                        (x : FOvariable),
  FO_frame_condition (predSO P x) = false.
Proof. auto. Qed.

Lemma FO_frame_condition_conjSO_l: forall (alpha1 alpha2 : SecOrder),
  FO_frame_condition (conjSO alpha1 alpha2) = true ->
    FO_frame_condition alpha1 = true.
Proof.
  simpl. intros alpha1 alpha2 H. unfold andb in *.
  if_then_else_dest_blind; auto.
Qed.

Lemma FO_frame_condition_conjSO_r: forall (alpha1 alpha2 : SecOrder),
  FO_frame_condition (conjSO alpha1 alpha2) = true ->
    FO_frame_condition alpha2 = true.
Proof.
  simpl. intros alpha1 alpha2 H. unfold andb in *.
  if_then_else_dest_blind; auto. discriminate.
Qed.

Lemma FO_frame_condition_preds_in2 : forall alpha : SecOrder,
  length (preds_in alpha) = 0 <-> FO_frame_condition alpha = true.
Proof.
  intros.
  induction alpha;
    try destruct p; try destruct f;
    try destruct f0;
    simpl;
    try (split; intros; discriminate);
    try (split; intros; reflexivity);
    try assumption;
    try (rewrite List.app_length;
    case_eq (FO_frame_condition alpha1); intros H1;
      [apply IHalpha1 in H1; rewrite H1;
      simpl; assumption |
      case_eq (length (preds_in alpha1));
        [intros H;  apply IHalpha1 in H;
        rewrite H in *; discriminate |
        intros n H; simpl;
        split; intros; discriminate]]).
Qed.

Lemma FO_frame_condition_preds_in : forall (cond : SecOrder),
  FO_frame_condition cond = true ->
    (preds_in cond = nil).
Proof.
  intros cond Hun.
  induction cond;
    try (destruct p; destruct f; simpl in *; discriminate);
    try (destruct f; destruct f0; simpl; reflexivity);
    try (destruct f; simpl in *; apply IHcond; assumption);
    try (simpl in *; apply IHcond; assumption);
    try (pose proof (FO_frame_condition_conjSO_l _ _ Hun) as Hun1;
         pose proof (FO_frame_condition_conjSO_r _ _ Hun) as Hun2);
    try (pose proof (FO_frame_condition_disjSO_l _ _ Hun) as Hun1;
         pose proof (FO_frame_condition_disjSO_r _ _ Hun) as Hun2);
    try (pose proof (FO_frame_condition_implSO_l _ _ Hun) as Hun1;
         pose proof (FO_frame_condition_implSO_r _ _ Hun) as Hun2);
    try (simpl in *; rewrite IHcond1; try rewrite IHcond2; try reflexivity;
        assumption);
    destruct p; simpl in *; discriminate.
Qed.

Lemma FO_frame_condition_preds_in_f : forall (alpha : SecOrder),
  FO_frame_condition alpha = false -> ~ (length (preds_in alpha) = 0).
Proof.
  intros alpha H. unfold not; intros H2. 
  induction alpha; try discriminate; simpl in *;
    try (apply IHalpha; auto);
    (rewrite app_length in H2; unfold andb in *; if_then_else_dest_blind;
   [apply IHalpha2 | apply IHalpha1]; firstorder).
Qed.


(* -------------------------------------------------------------------- *)


Lemma SOQFree_allFO : forall (alpha : SecOrder) (x : FOvariable),
  SOQFree (allFO x alpha) = true -> (SOQFree alpha = true).
Proof.
  intros alpha x H. assumption.
Qed.

Lemma SOQFree_allFO2 : forall (alpha : SecOrder) (x : FOvariable),
  (SOQFree alpha = true) -> SOQFree (allFO x alpha) = true. 
Proof.
  intros alpha x H.
  simpl.
  destruct x as [xn].
  assumption.
Qed.

Lemma SOQFree_exFO : forall (alpha : SecOrder) (x : FOvariable),
  SOQFree (exFO x alpha) = true -> (SOQFree alpha = true).
Proof.
  intros alpha x H.
  simpl in H.
  destruct x as [xn].
  case_eq (SOQFree alpha); intros H2; rewrite H2 in *;
    [reflexivity | discriminate].
Qed.

Lemma SOQFree_conjSO_l : forall (alpha1 alpha2 : SecOrder),
  SOQFree (conjSO alpha1 alpha2) = true -> (SOQFree alpha1 = true).
Proof.
  intros alpha1 alpha2 H.
  simpl in H.
  case_eq (SOQFree alpha1); intros H2; rewrite H2 in *;
    [reflexivity | discriminate].
Qed.

Lemma SOQFree_conjSO_r : forall (alpha1 alpha2 : SecOrder),
  SOQFree (conjSO alpha1 alpha2) = true -> (SOQFree alpha2 = true).
Proof.
  intros alpha1 alpha2 H.
  simpl in H.
  case_eq (SOQFree alpha1); intros H2; rewrite H2 in *;
    [case_eq (SOQFree alpha2); intros H3;
      [reflexivity | rewrite H3 in *]; 
      discriminate | discriminate].
Qed.

Lemma SOQFree_disjSO_l : forall (alpha1 alpha2 : SecOrder),
  SOQFree (disjSO alpha1 alpha2) = true -> (SOQFree alpha1 = true).
Proof.
  intros alpha1 alpha2 H.
  simpl in H.
  case_eq (SOQFree alpha1); intros H2; rewrite H2 in *;
    [reflexivity | discriminate].
Qed.

Lemma SOQFree_disjSO_r : forall (alpha1 alpha2 : SecOrder),
  SOQFree (disjSO alpha1 alpha2) = true -> (SOQFree alpha2 = true).
Proof.
  intros alpha1 alpha2 H.
  simpl in H.
  case_eq (SOQFree alpha1); intros H2; rewrite H2 in *;
    [case_eq (SOQFree alpha2); intros H3;
      [reflexivity | rewrite H3 in *]; 
      discriminate | discriminate].
Qed.

Lemma SOQFree_implSO_l : forall (alpha1 alpha2 : SecOrder),
  SOQFree (implSO alpha1 alpha2) = true -> (SOQFree alpha1 = true).
Proof.
  intros alpha1 alpha2 H.
  simpl in H.
  case_eq (SOQFree alpha1); intros H2; rewrite H2 in *;
    [reflexivity | discriminate].
Qed.

Lemma SOQFree_implSO_r : forall (alpha1 alpha2 : SecOrder),
  SOQFree (implSO alpha1 alpha2) = true -> (SOQFree alpha2 = true).
Proof.
  intros alpha1 alpha2 H.
  simpl in H.
  case_eq (SOQFree alpha1); intros H2; rewrite H2 in *;
    [case_eq (SOQFree alpha2); intros H3;
      [reflexivity | rewrite H3 in *]; 
      discriminate | discriminate].
Qed.

(* -------------------------------------------------------------------- *)

Lemma FO_frame_condition_SOQFree : forall alpha,
  FO_frame_condition alpha = true ->
  SOQFree alpha = true.
Proof.
  intros alpha Hun.
  induction alpha;
    try destruct p; try destruct f;
    try destruct f0;
    try reflexivity;
    try (simpl in *;
    apply IHalpha;
    assumption);
    try (simpl in *;
    case_eq (FO_frame_condition alpha1); intros Hun1;
      rewrite Hun1 in *; try discriminate;
      rewrite IHalpha1;
        [apply IHalpha2;
        assumption |
        reflexivity]);
     simpl in *; discriminate.
Qed.

Lemma Pred_in_SO_FO_frame_condition : forall beta P,
  FO_frame_condition beta = true ->
  ~ Pred_in_SO beta P.
Proof.
  induction beta; intros P H1 H2; try discriminate;
    try (solve [firstorder]);
  try (apply Pred_in_SO_conjSO in H2; destruct H2 as [H2 | H2];
  [apply FO_frame_condition_conjSO_l in H1; apply IHbeta1 in H2; auto|
   apply FO_frame_condition_conjSO_r in H1; apply IHbeta2 in H2; auto]).
Qed.

(* ------------------------------------------------- *)

Lemma SOQFree_P_conjSO_l : forall (alpha1 alpha2 : SecOrder) P,
  SOQFree_P (conjSO alpha1 alpha2) P = true -> (SOQFree_P alpha1 P = true).
Proof.
  intros alpha1 alpha2 [Pn] H.
  simpl in H.
  case_eq (SOQFree_P alpha1 (Pred Pn)); intros H2; rewrite H2 in *;
    [reflexivity | discriminate].
Qed.

Lemma SOQFree_P_conjSO_r : forall (alpha1 alpha2 : SecOrder) P,
  SOQFree_P (conjSO alpha1 alpha2) P = true -> (SOQFree_P alpha2 P = true).
Proof.
  intros alpha1 alpha2 [Pn] H.
  simpl in H.
  case_eq (SOQFree_P alpha1 (Pred Pn)); intros H2; rewrite H2 in *;
    [case_eq (SOQFree_P alpha2 (Pred Pn)); intros H3;
      [reflexivity | rewrite H3 in *]; 
      discriminate | discriminate].
Qed.

Lemma SOQFree_P_conjSO_t : forall alpha1 alpha2 P,
  SOQFree_P (conjSO alpha1 alpha2) P = true ->
  SOQFree_P alpha1 P = true /\
  SOQFree_P alpha2 P = true.
Proof.
  intros alpha1 alpha2 [Pn] Hno.
  simpl in Hno.
  case_eq (SOQFree_P alpha1 (Pred Pn)); intros Hno1;
    rewrite Hno1 in Hno.
    apply conj. reflexivity. assumption.
    discriminate.
Qed.

Lemma SOQFree_P_disjSO_t : forall alpha1 alpha2 P,
  SOQFree_P (disjSO alpha1 alpha2) P = true ->
  SOQFree_P alpha1 P = true /\
  SOQFree_P alpha2 P = true.
Proof.
  intros alpha1 alpha2 [Pn] Hno.
  simpl in Hno.
  case_eq (SOQFree_P alpha1 (Pred Pn)); intros Hno1;
    rewrite Hno1 in Hno.
    apply conj. reflexivity. assumption.
    discriminate.
Qed.

Lemma SOQFree_P_implSO_t : forall alpha1 alpha2 P,
  SOQFree_P (implSO alpha1 alpha2) P = true ->
  SOQFree_P alpha1 P = true /\
  SOQFree_P alpha2 P = true.
Proof.
  intros alpha1 alpha2 [Pn] Hno.
  simpl in Hno.
  case_eq (SOQFree_P alpha1 (Pred Pn)); intros Hno1;
    rewrite Hno1 in Hno.
    apply conj. reflexivity. assumption.
    discriminate.
Qed.

Lemma SOQFree__P : forall alpha P,
  SOQFree alpha = true ->
  SOQFree_P alpha P = true.
Proof.
  induction alpha; intros P H; simpl in *; unfold andb in *; auto;
    try discriminate;
  try (destruct_andb_t; rewrite IHalpha1; auto; 
       try discriminate; rewrite IHalpha2; auto).
Qed.

(* ------------------------------------------------- *)

Lemma FOQFree_conjSO_l : forall (alpha1 alpha2 : SecOrder),
  FOQFree (conjSO alpha1 alpha2) = true -> (FOQFree alpha1 = true).
Proof.
  intros alpha1 alpha2 H.
  simpl in H.
  case_eq (FOQFree alpha1); intros H2; rewrite H2 in *;
    [reflexivity | discriminate].
Qed.

Lemma FOQFree_conjSO_r : forall (alpha1 alpha2 : SecOrder),
  FOQFree (conjSO alpha1 alpha2) = true -> (FOQFree alpha2 = true).
Proof.
  intros alpha1 alpha2 H.
  simpl in H.
  case_eq (FOQFree alpha1); intros H2; rewrite H2 in *;
    [case_eq (FOQFree alpha2); intros H3;
      [reflexivity | rewrite H3 in *]; 
      discriminate | discriminate].
Qed.

Lemma SOQFree_l_empty : forall n,
  SOQFree_l (nlist_list _ (nlist_empty n)) = true.
Proof.
  induction n. reflexivity.
  simpl. assumption.
Qed.

Fixpoint free_SO (alpha : SecOrder) (P : predicate)  : bool :=
  match alpha with
    predSO Q y => if predicate_dec P Q then true else false
  | relatSO _ _ => false
  | eqFO _ _ => false
  | allFO y beta => free_SO beta P
  | exFO y beta => free_SO beta P
  | negSO beta => free_SO beta P
  | conjSO beta1 beta2 => if free_SO beta1 P then true
                             else free_SO beta2 P
  | disjSO beta1 beta2 => if free_SO beta1 P then true
                             else free_SO beta2 P
  | implSO beta1 beta2 => if free_SO beta1 P then true
                             else free_SO beta2 P
  | allSO Q beta => if predicate_dec P Q 
                       then false else free_SO beta P
  | exSO Q beta => if predicate_dec P Q 
                       then false else free_SO beta P 
  end.