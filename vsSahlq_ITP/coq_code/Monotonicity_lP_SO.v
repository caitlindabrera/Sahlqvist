Require Import SO_semantics Pred_in_SO.
Require Import Pred_is_pos_neg_SO nlist_sem_eg.
Require Import Correctness_ST SO_facts1 Monotonicity_SO.
Require Import FunctionalExtensionality.


(*
Require Export high_mods SO_sem_mods.
Require Import FunctionalExtensionality.
Require Import Monotonicity_SO SO_facts1 Correctness_ST.
*)

Definition Ip_extends_l (W : Set) (Ip Ip' : predicate -> W -> Prop) 
                     (lP : list predicate) :=
forall P,
  (In P lP ->  (forall (w : W), (Ip P w) -> (Ip' P w))) /\
  (~ In P lP ->  (Ip P = Ip' P)).

Lemma Ip_extends_l_refl : forall lP W Ip,
  Ip_extends_l W Ip Ip lP.
Proof.
  unfold Ip_extends_l.
  intros lP W Ip P. apply conj.
    intros H w H2. assumption.

    reflexivity.
Qed.

Definition alpha_upward_monotone_lP (alpha : SecOrder) (lP : list predicate) :=
    forall (W : Set) (Iv : FOvariable -> W) (R : W -> W -> Prop)
           (Ip Ip' : predicate -> W -> Prop),
   Ip_extends_l W Ip Ip' lP
      -> (SOturnst W Iv Ip R alpha) ->
                          (SOturnst W Iv Ip' R alpha).

Definition alpha_downward_monotone_lP (alpha : SecOrder) (lP : list predicate) :=
    forall (W : Set) (Iv : FOvariable -> W) (R : W -> W -> Prop)
           (Ip Ip' : predicate -> W -> Prop),
   Ip_extends_l W Ip' Ip lP
      -> (SOturnst W Iv Ip R alpha) ->
                          (SOturnst W Iv Ip' R alpha).

Fixpoint lP_is_pos_SO alpha lP :=
  match lP with 
  | nil => False
  | cons P nil => (Pred_is_pos_SO alpha P)
  | cons P lP' => (Pred_is_pos_SO alpha P) /\ (lP_is_pos_SO alpha lP')
  end.

Fixpoint lP_is_neg_SO alpha lP :=
  match lP with 
  | nil => False
  | cons P nil => Pred_is_neg_SO alpha P
  | cons P lP' => (Pred_is_neg_SO alpha P) /\ (lP_is_neg_SO alpha lP')
  end.

Lemma Pred_is_neg_SO_predSO : forall P Q x,
  ~(Pred_is_neg_SO (predSO P x) Q).
Proof.
  intros P Q x H. inversion H. unfold Pred_in_SO in *.
  simpl in *. destruct H0. subst.
  specialize (H1 1). simpl in *.
  assert (occ_in_SO (predSO Q x) 1) as HH. firstorder.
  apply H1 in HH; auto. inversion HH. simpl in *. discriminate.
  contradiction.
Qed.

Lemma lPred_is_neg_SO_predSO : forall lP P x,
  ~ (lP_is_neg_SO (predSO P x) lP).
Proof.
  induction lP; intros P x. firstorder.
  intros H. simpl in *. destruct lP.
  contradiction (Pred_is_neg_SO_predSO _ _ _ H).
  destruct H as [H1 H2]. contradiction (IHlP _ _ H2).
Qed.

Lemma monotonicity_lP_SO_predSO : forall p f,
forall lP : list predicate,
(lP_is_pos_SO (predSO p f) lP -> alpha_upward_monotone_lP (predSO p f) lP) /\
(lP_is_neg_SO (predSO p f) lP -> alpha_downward_monotone_lP (predSO p f) lP).
Proof.
  intros p f lP. simpl in *. apply conj. intros H2. destruct lP.
    contradiction.
    simpl in *. unfold alpha_upward_monotone_lP.
     unfold alpha_upward_monotone_lP . intros until 0.
      intros H3 H4. simpl in *. 
      unfold Ip_extends_l in H3. specialize (H3 p).
      destruct H3 as [H3a H3b].
      destruct (in_dec predicate_dec p (cons p0 lP)).
      apply H3a; auto. rewrite <- H3b; auto.

    intros H2.
    contradiction (lPred_is_neg_SO_predSO _ _ _ H2).
Qed.

Lemma monotonicity_lP_SO_relatSO : forall f f0,
forall lP : list predicate,
(lP_is_pos_SO (relatSO f f0) lP -> alpha_upward_monotone_lP (relatSO f f0) lP) /\
(lP_is_neg_SO (relatSO f f0) lP -> alpha_downward_monotone_lP (relatSO f f0) lP).
Proof.
  unfold alpha_upward_monotone_lP.
  unfold alpha_downward_monotone_lP.
  intros. simpl. destruct f as [xn]. destruct f0 as [ym].
  apply conj; intros; assumption.
Qed.

Lemma monotonicity_lP_SO_eqFO : forall f f0,
forall lP : list predicate,
(lP_is_pos_SO (eqFO f f0) lP -> alpha_upward_monotone_lP (eqFO f f0) lP) /\
(lP_is_neg_SO (eqFO f f0) lP -> alpha_downward_monotone_lP (eqFO f f0) lP).
Proof.
  unfold alpha_upward_monotone_lP.
  unfold alpha_downward_monotone_lP.
  intros. simpl. destruct f as [xn]. destruct f0 as [ym].
  apply conj; intros; assumption.
Qed.

Lemma down_lP_allFO : forall (alpha: SecOrder) x (lP : list predicate),
  alpha_downward_monotone_lP alpha lP ->
    alpha_downward_monotone_lP (allFO x alpha) lP.
Proof.
  intros alpha x lP H.
  unfold alpha_downward_monotone_lP in *.
  intros W Iv R Ip Ip' H1 H2. rewrite SOturnst_allFO in *. intros d.
  apply H with (Ip := Ip). assumption. apply H2.
Qed.

Lemma up_lP_allFO : forall (alpha: SecOrder) x (lP : list predicate),
  alpha_upward_monotone_lP alpha lP ->
    alpha_upward_monotone_lP (allFO x alpha) lP.
Proof.
  intros alpha x lP H.
  unfold alpha_upward_monotone_lP in *.
  intros W Iv R Ip Ip' H1 H2. rewrite SOturnst_allFO in *. intros d.
  apply H with (Ip := Ip). assumption. apply H2.
Qed.


Lemma down_lP_exFO : forall (alpha: SecOrder) x (lP : list predicate),
  alpha_downward_monotone_lP alpha lP ->
    alpha_downward_monotone_lP (exFO x alpha) lP.
Proof.
  intros alpha x lP H.
  unfold alpha_downward_monotone_lP in *.
  intros W Iv R Ip Ip' H1 H2. rewrite SOturnst_exFO in *.
  destruct H2 as [d H2]. exists d.
  apply H with (Ip := Ip). assumption. apply H2.
Qed.

Lemma up_lP_exFO : forall (alpha: SecOrder) x (lP : list predicate),
  alpha_upward_monotone_lP alpha lP ->
    alpha_upward_monotone_lP (exFO x alpha) lP.
Proof.
  intros alpha x lP H.
  unfold alpha_upward_monotone_lP in *.
  intros W Iv R Ip Ip' H1 H2. rewrite SOturnst_exFO in *.
  destruct H2 as [d H2]. exists d.
  apply H with (Ip := Ip). assumption. apply H2.
Qed.

Lemma lP_is_pos_SO_allFO : forall lP alpha x,
  lP_is_pos_SO (allFO x alpha) lP ->
  lP_is_pos_SO alpha lP.
Proof.
  induction lP; intros alpha x H.
    simpl in *. contradiction.

    simpl in *. destruct lP. apply Pred_is_pos_SO_allFO in H. assumption.
    destruct H as [H1 H2].
    apply Pred_is_pos_SO_allFO in H1.
    apply conj. assumption. apply IHlP  with (x := x) ; assumption.
Qed.

Lemma lPred_is_neg_SO_allFO : forall lP alpha x,
  lP_is_neg_SO (allFO x alpha) lP ->
  lP_is_neg_SO alpha lP.
Proof.
  induction lP; intros alpha x H.
    simpl in *. contradiction.

    simpl in *. 
destruct lP. apply Pred_is_neg_SO_allFO in H. assumption.
destruct H as [H1 H2].
    apply Pred_is_neg_SO_allFO in H1.
    apply conj. assumption. apply IHlP  with (x := x) ; assumption.
Qed.

Lemma lP_is_pos_SO_exFO : forall lP alpha x,
  lP_is_pos_SO (exFO x alpha) lP ->
  lP_is_pos_SO alpha lP.
Proof.
  induction lP; intros alpha x H.
    simpl in *. contradiction.

    simpl in *. destruct lP. apply Pred_is_pos_SO_exFO in H. assumption.
    destruct H as [H1 H2].
    apply Pred_is_pos_SO_exFO in H1.
    apply conj. assumption. apply IHlP  with (x := x) ; assumption.
Qed.

Lemma lP_is_neg_SO_exFO : forall lP alpha x,
  lP_is_neg_SO (exFO x alpha) lP ->
  lP_is_neg_SO alpha lP.
Proof.
  induction lP; intros alpha x H.
    simpl in *. contradiction.

    simpl in *. 
destruct lP. apply Pred_is_neg_SO_exFO in H. assumption.
destruct H as [H1 H2].
    apply Pred_is_neg_SO_exFO in H1.
    apply conj. assumption. apply IHlP  with (x := x) ; assumption.
Qed.

Lemma monotonicity_lP_SO_allFO : forall (alpha : SecOrder) f,

(forall lP : list predicate,
          (lP_is_pos_SO alpha lP -> alpha_upward_monotone_lP alpha lP) /\
          (lP_is_neg_SO alpha lP -> alpha_downward_monotone_lP alpha lP)) ->
forall lP : list predicate,
(lP_is_pos_SO (allFO f alpha) lP -> alpha_upward_monotone_lP (allFO f alpha) lP) /\
(lP_is_neg_SO (allFO f alpha) lP -> alpha_downward_monotone_lP (allFO f alpha) lP).
Proof.
  intros alpha x IHalpha lP .
  apply conj; intros H3.
    apply up_lP_allFO. apply lP_is_pos_SO_allFO in H3.
    apply IHalpha; assumption.

    apply down_lP_allFO. apply lPred_is_neg_SO_allFO in H3.
    apply IHalpha; assumption.
Qed.

Lemma monotonicity_lP_SO_exFO : forall (alpha : SecOrder) f,
(forall lP : list predicate,
          (lP_is_pos_SO alpha lP -> alpha_upward_monotone_lP alpha lP) /\
          (lP_is_neg_SO alpha lP -> alpha_downward_monotone_lP alpha lP)) ->
forall lP : list predicate,
(lP_is_pos_SO (exFO f alpha) lP -> alpha_upward_monotone_lP (exFO f alpha) lP) /\
(lP_is_neg_SO (exFO f alpha) lP -> alpha_downward_monotone_lP (exFO f alpha) lP).
Proof.
  intros alpha x IHalpha lP.
  apply conj; intros H3.
    apply up_lP_exFO. apply lP_is_pos_SO_exFO in H3.
    apply IHalpha; assumption.

    apply down_lP_exFO. apply lP_is_neg_SO_exFO in H3.
    apply IHalpha; assumption.
Qed.

Lemma lPred_is_pos_SO_negSO : forall lP alpha,
  lP_is_pos_SO (negSO alpha) lP ->
  lP_is_neg_SO alpha lP.
Proof.
  induction lP; intros alpha H.
    simpl in *. contradiction.

    simpl in *. destruct lP.
    apply P_pos_negSO in H. assumption.
    destruct H as [H1 H2].
    apply P_pos_negSO in H1. apply conj. assumption.
    apply IHlP. assumption.
Qed.

Lemma lPred_is_neg_SO_negSO : forall lP alpha,
  lP_is_neg_SO (negSO alpha) lP ->
  lP_is_pos_SO alpha lP.
Proof.
  induction lP; intros alpha H.
    simpl in *. contradiction.

    simpl in *. destruct lP. apply P_neg_negSO. assumption.
    destruct H as [H1 H2].
    apply P_neg_negSO in H1. apply conj. assumption.
    apply IHlP. assumption.
Qed.

Lemma alpha_downward_monotone_lP_negSO : forall lP alpha,
  alpha_upward_monotone_lP alpha lP ->
  alpha_downward_monotone_lP (negSO alpha) lP.
Proof.
  intros lP alpha H.
  unfold alpha_upward_monotone_lP in H.
  unfold alpha_downward_monotone_lP.
  intros W Iv Ir Ip Ip' H1 H2. specialize (H W Iv Ir Ip' Ip).
  intros SOt. apply H2. apply H; assumption.
Qed.

Lemma alpha_upward_monotone_lP_negSO : forall lP alpha,
  alpha_downward_monotone_lP alpha lP ->
  alpha_upward_monotone_lP (negSO alpha) lP.
Proof.
  intros lP alpha H.
  unfold alpha_downward_monotone_lP in H.
  unfold alpha_upward_monotone_lP.
  intros W Iv Ir Ip Ip' H1 H2. specialize (H W Iv Ir Ip' Ip).
  intros SOt. apply H2. apply H; assumption.
Qed.

Lemma monotonicity_lP_SO_negSO : forall (alpha : SecOrder),
( forall lP : list predicate,
          (lP_is_pos_SO alpha lP -> alpha_upward_monotone_lP alpha lP) /\
          (lP_is_neg_SO alpha lP -> alpha_downward_monotone_lP alpha lP)) ->
forall lP : list predicate,
(lP_is_pos_SO (negSO alpha) lP -> alpha_upward_monotone_lP (negSO alpha) lP) /\
(lP_is_neg_SO (negSO alpha) lP -> alpha_downward_monotone_lP (negSO alpha) lP).
Proof.
  intros alpha IHalpha lP.
  destruct (IHalpha lP) as [IH1 IH2].
  apply conj; intros H3.
    apply lPred_is_pos_SO_negSO in H3. apply alpha_upward_monotone_lP_negSO.
    apply IH2. assumption.

    apply lPred_is_neg_SO_negSO in H3. apply alpha_downward_monotone_lP_negSO.
    apply IH1. assumption.
Qed.

Lemma lPred_is_pos_SO_is_in_pred_t : forall lP alpha,
  lP_is_pos_SO alpha lP -> incl lP (preds_in alpha).
Proof.
  induction lP. firstorder.
  intros alpha Hpos. simpl in *.
  destruct lP. apply incl_cons; firstorder. 
  apply incl_cons; firstorder.
Qed.

Lemma lPred_is_neg_SO_is_in_pred_t : forall lP alpha,
  lP_is_neg_SO alpha lP -> incl lP (preds_in alpha).
Proof.
  induction lP. firstorder.
  intros alpha Hpos. simpl in *.
  destruct lP; apply incl_cons; firstorder.
Qed.

Lemma alpha_upward_monotone_lP_conjSO_fwd : forall lP alpha1 alpha2,
  alpha_upward_monotone_lP alpha1 lP ->
  alpha_upward_monotone_lP alpha2 lP ->
  alpha_upward_monotone_lP (conjSO alpha1 alpha2) lP .
Proof.
  unfold alpha_upward_monotone_lP. intros lP alpha1 alpha2 H1 H2
    W Iv R Ip Ip' Hext SOt.
  simpl in *. destruct SOt as [SOt1 SOt2].
  apply conj.
    apply H1 with (Ip := Ip); assumption.
    apply H2 with (Ip := Ip); assumption.
Qed.

Lemma alpha_upward_monotone_lP_implSO_fwd : forall lP alpha1 alpha2,
  alpha_downward_monotone_lP alpha1 lP ->
  alpha_upward_monotone_lP alpha2 lP ->
  alpha_upward_monotone_lP (implSO alpha1 alpha2) lP .
Proof.
  unfold alpha_upward_monotone_lP. unfold alpha_downward_monotone_lP.
  intros lP alpha1 alpha2 H1 H2
    W Iv R Ip Ip' Hext SOt SOt2.
  apply H2 with (Ip := Ip). assumption.
  apply SOt. apply H1 with (Ip := Ip'); assumption.
Qed.

Lemma alpha_upward_monotone_lP_disjSO_fwd : forall lP alpha1 alpha2,
  alpha_upward_monotone_lP alpha1 lP ->
  alpha_upward_monotone_lP alpha2 lP ->
  alpha_upward_monotone_lP (disjSO alpha1 alpha2) lP .
Proof.
  unfold alpha_upward_monotone_lP. intros lP alpha1 alpha2 H1 H2
    W Iv R Ip Ip' Hext SOt.
  simpl in *. destruct SOt as [SOt1 | SOt2].
    left.
    apply H1 with (Ip := Ip); assumption.

    right.
    apply H2 with (Ip := Ip); assumption.
Qed.

Lemma alpha_downward_monotone_lP_conjSO_fwd : forall lP alpha1 alpha2,
  alpha_downward_monotone_lP alpha1 lP ->
  alpha_downward_monotone_lP alpha2 lP ->
  alpha_downward_monotone_lP (conjSO alpha1 alpha2) lP .
Proof.
  unfold alpha_upward_monotone_lP. intros lP alpha1 alpha2 H1 H2
    W Iv R Ip Ip' Hext SOt.
  simpl in *. destruct SOt as [SOt1 SOt2].
  apply conj.
    apply H1 with (Ip := Ip); assumption.
    apply H2 with (Ip := Ip); assumption.
Qed.

Lemma alpha_downward_monotone_lP_implSO_fwd : forall lP alpha1 alpha2,
  alpha_upward_monotone_lP alpha1 lP ->
  alpha_downward_monotone_lP alpha2 lP ->
  alpha_downward_monotone_lP (implSO alpha1 alpha2) lP .
Proof.
  unfold alpha_upward_monotone_lP. unfold alpha_downward_monotone_lP.
  intros lP alpha1 alpha2 H1 H2
    W Iv R Ip Ip' Hext SOt SOt2.
  apply H2 with (Ip := Ip). assumption.
  apply SOt. apply H1 with (Ip := Ip'); assumption.
Qed.

Lemma alpha_downward_monotone_lP_disjSO_fwd : forall lP alpha1 alpha2,
  alpha_downward_monotone_lP alpha1 lP ->
  alpha_downward_monotone_lP alpha2 lP ->
  alpha_downward_monotone_lP (disjSO alpha1 alpha2) lP .
Proof.
  unfold alpha_upward_monotone_lP. intros lP alpha1 alpha2 H1 H2
    W Iv R Ip Ip' Hext SOt.
  simpl in *. destruct SOt as [SOt1 | SOt2].
    left.
    apply H1 with (Ip := Ip); assumption.

    right.
    apply H2 with (Ip := Ip); assumption.
Qed.

Lemma alpha_upward_monotone_lP_nil : forall alpha,
  alpha_upward_monotone_lP alpha nil.
Proof.
  unfold alpha_upward_monotone_lP.
  intros until 0. intros Hext SOt.
  unfold Ip_extends_l in Hext. simpl in *.
assert (forall P, Ip P = Ip' P) as Hsame.
   intros P. apply Hext. firstorder.
assert (Ip = Ip') as Heq.
   apply functional_extensionality. assumption. 
  rewrite <- Heq. assumption.
Qed.

Lemma alpha_downward_monotone_lP_nil : forall alpha,
  alpha_downward_monotone_lP alpha nil.
Proof.
  unfold alpha_downward_monotone_lP.
  intros until 0. intros Hext SOt.
  unfold Ip_extends_l in Hext. simpl in *.
assert (forall P, Ip' P = Ip P) as Hsame.
   intros P. apply Hext. firstorder.
assert (Ip' = Ip) as Heq.
   apply functional_extensionality. assumption. 
  rewrite Heq. assumption.
Qed. 

Lemma lPred_is_pos_SO_conjSO_cap_pred_l : forall lP alpha1 alpha2,
  ~ (cap_pred lP (preds_in alpha1)) = nil ->
  lP_is_pos_SO (conjSO alpha1 alpha2) lP ->
  lP_is_pos_SO alpha1 (cap_pred lP (preds_in alpha1)).
Proof.
  induction lP; intros alpha1 alpha2 Hnil Hpos. contradiction.
  simpl in *. case_eq lP. intros HlP. subst.
  destruct (in_predicate_dec a (preds_in alpha1)).
    simpl. apply Pred_is_pos_SO_conjSO_l in Hpos; assumption.
    contradiction.
  intros Q lQ HlP. rewrite <- HlP.    
  destruct (in_predicate_dec a (preds_in alpha1)).
  + rewrite HlP in Hpos.
    rewrite <- HlP in Hpos. simpl.
    destruct Hpos as [Hp1 Hp2].
    case_eq (cap_pred lP (preds_in alpha1)).
    ++ intros H. apply Pred_is_pos_SO_conjSO_l in Hp1; auto. 
    ++ intros R lR Hcap. apply conj.
       apply Pred_is_pos_SO_conjSO_l in Hp1; auto.
       rewrite <- Hcap. apply IHlP with (alpha2 := alpha2);
                          try assumption.
       intros H. rewrite H in *. discriminate.
  + rewrite HlP in Hpos. rewrite <- HlP in Hpos.
    destruct Hpos as [Hp1 Hp2].
    apply IHlP with (alpha2 := alpha2); assumption.
Qed.

Lemma lPred_is_pos_SO_disjSO_cap_pred_l : forall lP alpha1 alpha2,
  ~ (cap_pred lP (preds_in alpha1)) = nil ->
  lP_is_pos_SO (disjSO alpha1 alpha2) lP ->
  lP_is_pos_SO alpha1 (cap_pred lP (preds_in alpha1)).
Proof.
  induction lP; intros alpha1 alpha2 Hnil Hpos. contradiction.
  simpl in *. case_eq lP. intros HlP. rewrite HlP in *.
  simpl in *. destruct (in_predicate_dec a (preds_in alpha1)).
    simpl in *. apply Pred_is_pos_SO_disjSO_l in Hpos; auto.
      contradiction.
  intros Q lQ HlP. rewrite <- HlP.    
  destruct (in_predicate_dec a (preds_in alpha1)).
  + simpl. rewrite HlP in Hpos.
    rewrite <- HlP in Hpos. simpl.
    destruct Hpos as [Hp1 Hp2].
    case_eq (cap_pred lP (preds_in alpha1)).
        intros H. apply Pred_is_pos_SO_disjSO_l in Hp1; auto.
    intros R lR Hcap. apply conj.
    apply Pred_is_pos_SO_disjSO_l in Hp1; auto.
    rewrite <- Hcap. apply IHlP with (alpha2 := alpha2); auto.
    intros H. rewrite H in *. discriminate.
  + rewrite HlP in Hpos. rewrite <- HlP in Hpos.
    destruct Hpos as [Hp1 Hp2].
    apply IHlP with (alpha2 := alpha2); assumption.
Qed.

Lemma lPred_is_pos_SO_implSO_cap_pred_l : forall lP alpha1 alpha2,
  ~ (cap_pred lP (preds_in alpha1)) = nil ->
  lP_is_pos_SO (implSO alpha1 alpha2) lP ->
  lP_is_neg_SO alpha1 (cap_pred lP (preds_in alpha1)).
Proof.
  induction lP; intros alpha1 alpha2 Hnil Hpos. contradiction.
  simpl in *. case_eq lP. intros HlP. rewrite HlP in *.
  destruct (in_predicate_dec a (preds_in alpha1)).
      apply Pred_is_pos_SO_implSO_l in Hpos; try assumption.
      simpl in *. contradiction.
  intros Q lQ HlP. rewrite <- HlP.    
  destruct (in_predicate_dec a (preds_in alpha1)).
  + rewrite HlP in Hpos.
    rewrite <- HlP in Hpos. simpl.
    destruct Hpos as [Hp1 Hp2].
    case_eq (cap_pred lP (preds_in alpha1)).  intros H.
      apply Pred_is_pos_SO_implSO_l in Hp1; auto.
    intros R lR Hcap. apply conj.
    apply Pred_is_pos_SO_implSO_l in Hp1; auto.  
    rewrite <- Hcap. apply IHlP with (alpha2 := alpha2);
                       try assumption.
    intros H. rewrite H in *. discriminate.
  + rewrite HlP in Hpos. rewrite <- HlP in Hpos.
    destruct Hpos as [Hp1 Hp2].
    apply IHlP with (alpha2 := alpha2); assumption.
Qed. 

Lemma lPred_is_neg_SO_implSO_cap_pred_l : forall lP alpha1 alpha2,
  ~ (cap_pred lP (preds_in alpha1)) = nil ->
  lP_is_neg_SO (implSO alpha1 alpha2) lP ->
  lP_is_pos_SO alpha1 (cap_pred lP (preds_in alpha1)).
Proof.
  induction lP; intros alpha1 alpha2 Hnil Hpos. contradiction.
  simpl in *. case_eq lP. intros HlP. rewrite HlP in *.
  destruct (in_predicate_dec a (preds_in alpha1)).
      apply Pred_is_neg_SO_implSO_l in Hpos; auto. firstorder.
  intros Q lQ HlP. rewrite <- HlP.    
  destruct (in_predicate_dec a (preds_in alpha1)).
  + rewrite HlP in Hpos. rewrite <- HlP in Hpos. simpl.
    destruct Hpos as [Hp1 Hp2].
    case_eq (cap_pred lP (preds_in alpha1)). intros H.
      apply Pred_is_neg_SO_implSO_l in Hp1; auto.
    intros R lR Hcap. apply conj.
    apply Pred_is_neg_SO_implSO_l in Hp1; auto. 
    rewrite <- Hcap. apply IHlP with (alpha2 := alpha2);
                       try assumption.
    intros H. rewrite H in *. discriminate.
  + rewrite HlP in Hpos. rewrite <- HlP in Hpos.
    destruct Hpos as [Hp1 Hp2].
    apply IHlP with (alpha2 := alpha2); assumption.
Qed. 

Lemma lPred_is_neg_SO_conjSO_cap_pred_l : forall lP alpha1 alpha2,
  ~ (cap_pred lP (preds_in alpha1)) = nil ->
  lP_is_neg_SO (conjSO alpha1 alpha2) lP ->
  lP_is_neg_SO alpha1 (cap_pred lP (preds_in alpha1)).
Proof.
  induction lP; intros alpha1 alpha2 Hnil Hpos. contradiction.
  simpl in *. case_eq lP. intros HlP. rewrite HlP in *.
  destruct (in_predicate_dec a (preds_in alpha1)).
      apply Pred_is_neg_SO_conjSO_l in Hpos; assumption. firstorder.

    intros Q lQ HlP. rewrite <- HlP.    
    destruct (in_predicate_dec a (preds_in alpha1)).
      rewrite HlP in Hpos. rewrite <- HlP in Hpos. simpl.
      destruct Hpos as [Hp1 Hp2].
      case_eq (cap_pred lP (preds_in alpha1)).
        intros H.
        apply Pred_is_neg_SO_conjSO_l in Hp1.  assumption. firstorder.

        intros R lR Hcap. apply conj.
          apply Pred_is_neg_SO_conjSO_l in Hp1.  assumption. firstorder.

          rewrite <- Hcap. apply IHlP with (alpha2 := alpha2);
          try assumption.
          intros H. rewrite H in *. discriminate.

      rewrite HlP in Hpos. rewrite <- HlP in Hpos.
      destruct Hpos as [Hp1 Hp2].
      apply IHlP with (alpha2 := alpha2); assumption.
Qed.

Lemma lPred_is_neg_SO_disjSO_cap_pred_l : forall lP alpha1 alpha2,
  ~ (cap_pred lP (preds_in alpha1)) = nil ->
  lP_is_neg_SO (disjSO alpha1 alpha2) lP ->
  lP_is_neg_SO alpha1 (cap_pred lP (preds_in alpha1)).
Proof.
  induction lP; intros alpha1 alpha2 Hnil Hpos.
    simpl in *. contradiction.

    simpl in *. case_eq lP. intros HlP. rewrite HlP in *.
    destruct (in_predicate_dec a (preds_in alpha1)).
      apply Pred_is_neg_SO_disjSO_l in Hpos; assumption. firstorder.

    intros Q lQ HlP. rewrite <- HlP.    
    destruct (in_predicate_dec a (preds_in alpha1)).
      rewrite HlP in Hpos. rewrite <- HlP in Hpos. simpl.
      destruct Hpos as [Hp1 Hp2].
      case_eq (cap_pred lP (preds_in alpha1)).
        intros H.
        apply Pred_is_neg_SO_disjSO_l in Hp1.  assumption. firstorder.

        intros R lR Hcap. apply conj.
          apply Pred_is_neg_SO_disjSO_l in Hp1.  assumption. firstorder.

          rewrite <- Hcap. apply IHlP with (alpha2 := alpha2);
          try assumption.
          intros H. rewrite H in *. discriminate.

      rewrite HlP in Hpos. rewrite <- HlP in Hpos.
      destruct Hpos as [Hp1 Hp2].
      apply IHlP with (alpha2 := alpha2); assumption.
Qed.


Lemma lP_is_down_SO_conjSO_cap_pred_l : forall lP alpha1 alpha2,
  ~ (cap_pred lP (preds_in alpha1)) = nil ->
  lP_is_neg_SO (conjSO alpha1 alpha2) lP ->
  lP_is_neg_SO alpha1 (cap_pred lP (preds_in alpha1)).
Proof.
  induction lP; intros alpha1 alpha2 Hnil Hpos.
    simpl in *. contradiction.

    simpl in *. case_eq lP. intros HlP. rewrite HlP in *.
    destruct (in_predicate_dec a (preds_in alpha1)).
      apply Pred_is_neg_SO_conjSO_l in Hpos; assumption. firstorder.

    intros Q lQ HlP. rewrite <- HlP.    
    destruct (in_predicate_dec a (preds_in alpha1)).
      rewrite HlP in Hpos. rewrite <- HlP in Hpos. simpl.
      destruct Hpos as [Hp1 Hp2].
      case_eq (cap_pred lP (preds_in alpha1)).
        intros H.
        apply Pred_is_neg_SO_conjSO_l in Hp1.  assumption. firstorder.

        intros R lR Hcap. apply conj.
          apply Pred_is_neg_SO_conjSO_l in Hp1.  assumption. firstorder.

          rewrite <- Hcap. apply IHlP with (alpha2 := alpha2);
          try assumption.
          intros H. rewrite H in *. discriminate.

      rewrite HlP in Hpos. rewrite <- HlP in Hpos.
      destruct Hpos as [Hp1 Hp2].
      apply IHlP with (alpha2 := alpha2); assumption.
Qed.

Lemma lP_is_down_SO_implSO_cap_pred_l : forall lP alpha1 alpha2,
  ~ (cap_pred lP (preds_in alpha1)) = nil ->
  lP_is_neg_SO (implSO alpha1 alpha2) lP ->
  lP_is_pos_SO alpha1 (cap_pred lP (preds_in alpha1)).
Proof.
  induction lP; intros alpha1 alpha2 Hnil Hpos.
    simpl in *. contradiction.

    simpl in *. case_eq lP. intros HlP. rewrite HlP in *.
    destruct (in_predicate_dec a (preds_in alpha1)).
      apply Pred_is_neg_SO_implSO_l in Hpos; try assumption. firstorder.

    intros Q lQ HlP. rewrite <- HlP.    
    destruct (in_predicate_dec a (preds_in alpha1)).
      rewrite HlP in Hpos. rewrite <- HlP in Hpos. simpl.
      destruct Hpos as [Hp1 Hp2].
      case_eq (cap_pred lP (preds_in alpha1)).
        intros H.
        apply Pred_is_neg_SO_implSO_l in Hp1.  assumption. firstorder.

        intros R lR Hcap. apply conj.
          apply Pred_is_neg_SO_implSO_l in Hp1.  assumption. firstorder.

          rewrite <- Hcap. apply IHlP with (alpha2 := alpha2);
          try assumption.
          intros H. rewrite H in *. discriminate.

      rewrite HlP in Hpos. rewrite <- HlP in Hpos.
      destruct Hpos as [Hp1 Hp2].
      apply IHlP with (alpha2 := alpha2); assumption.
Qed.


Lemma lP_is_down_SO_disjSO_cap_pred_l : forall lP alpha1 alpha2,
  ~ (cap_pred lP (preds_in alpha1)) = nil ->
  lP_is_neg_SO (disjSO alpha1 alpha2) lP ->
  lP_is_neg_SO alpha1 (cap_pred lP (preds_in alpha1)).
Proof.
  induction lP; intros alpha1 alpha2 Hnil Hpos.
    simpl in *. contradiction.

    simpl in *. case_eq lP. intros HlP. rewrite HlP in *.
    destruct (in_predicate_dec a (preds_in alpha1)).
      apply Pred_is_neg_SO_disjSO_l in Hpos; try assumption. firstorder.

    intros Q lQ HlP. rewrite <- HlP.    
    destruct (in_predicate_dec a (preds_in alpha1)).
      rewrite HlP in Hpos. rewrite <- HlP in Hpos. simpl.
      destruct Hpos as [Hp1 Hp2].
      case_eq (cap_pred lP (preds_in alpha1)).
        intros H.
        apply Pred_is_neg_SO_disjSO_l in Hp1.  assumption. firstorder.

        intros R lR Hcap. apply conj.
          apply Pred_is_neg_SO_disjSO_l in Hp1.  assumption. firstorder.

          rewrite <- Hcap. apply IHlP with (alpha2 := alpha2);
          try assumption.
          intros H. rewrite H in *. discriminate.

      rewrite HlP in Hpos. rewrite <- HlP in Hpos.
      destruct Hpos as [Hp1 Hp2].
      apply IHlP with (alpha2 := alpha2); assumption.
Qed.

Lemma lPred_is_pos_SO_conjSO_cap_pred_r : forall lP alpha1 alpha2,
  ~ (cap_pred lP (preds_in alpha2)) = nil ->
  lP_is_pos_SO (conjSO alpha1 alpha2) lP ->
  lP_is_pos_SO alpha2 (cap_pred lP (preds_in alpha2)).
Proof.
  induction lP; intros alpha1 alpha2 Hnil Hpos.
    simpl in *. contradiction.

    simpl in *. case_eq lP. intros HlP. rewrite HlP in *.
    destruct (in_predicate_dec a (preds_in alpha2)).
      apply Pred_is_pos_SO_conjSO_r in Hpos; assumption. firstorder.

    intros Q lQ HlP. rewrite <- HlP.    
    destruct (in_predicate_dec a (preds_in alpha2)).
      rewrite HlP in Hpos. rewrite <- HlP in Hpos. simpl.
      destruct Hpos as [Hp1 Hp2].
      case_eq (cap_pred lP (preds_in alpha2)).
        intros H.
        apply Pred_is_pos_SO_conjSO_r in Hp1.  assumption. firstorder.

        intros R lR Hcap. apply conj.
          apply Pred_is_pos_SO_conjSO_r in Hp1.  assumption. firstorder.

          rewrite <- Hcap. apply IHlP with (alpha1 := alpha1);
          try assumption.
          intros H. rewrite H in *. discriminate.

      rewrite HlP in Hpos. rewrite <- HlP in Hpos.
      destruct Hpos as [Hp1 Hp2].
      apply IHlP with (alpha1 := alpha1); assumption.
Qed.

Lemma lPred_is_pos_SO_disjSO_cap_pred_r : forall lP alpha1 alpha2,
  ~ (cap_pred lP (preds_in alpha2)) = nil ->
  lP_is_pos_SO (disjSO alpha1 alpha2) lP ->
  lP_is_pos_SO alpha2 (cap_pred lP (preds_in alpha2)).
Proof.
  induction lP; intros alpha1 alpha2 Hnil Hpos.
    simpl in *. contradiction.

    simpl in *. case_eq lP. intros HlP. rewrite HlP in *.
    destruct (in_predicate_dec a (preds_in alpha2)).
      apply Pred_is_pos_SO_disjSO_r in Hpos; assumption. firstorder.

    intros Q lQ HlP. rewrite <- HlP.    
    destruct (in_predicate_dec a (preds_in alpha2)).
      rewrite HlP in Hpos. rewrite <- HlP in Hpos. simpl.
      destruct Hpos as [Hp1 Hp2].
      case_eq (cap_pred lP (preds_in alpha2)).
        intros H.
        apply Pred_is_pos_SO_disjSO_r in Hp1.  assumption. firstorder.

        intros R lR Hcap. apply conj.
          apply Pred_is_pos_SO_disjSO_r in Hp1.  assumption. firstorder.

          rewrite <- Hcap. apply IHlP with (alpha1 := alpha1);
          try assumption.
          intros H. rewrite H in *. discriminate.

      rewrite HlP in Hpos. rewrite <- HlP in Hpos.
      destruct Hpos as [Hp1 Hp2].
      apply IHlP with (alpha1 := alpha1); assumption.
Qed.

Lemma lPred_is_pos_SO_implSO_cap_pred_r : forall lP alpha1 alpha2,
  ~ (cap_pred lP (preds_in alpha2)) = nil ->
  lP_is_pos_SO (implSO alpha1 alpha2) lP ->
  lP_is_pos_SO alpha2 (cap_pred lP (preds_in alpha2)).
Proof.
  induction lP; intros alpha1 alpha2 Hnil Hpos.
    simpl in *. contradiction.

    simpl in *. case_eq lP. intros HlP. rewrite HlP in *.
    destruct (in_predicate_dec a (preds_in alpha2)).
      apply Pred_is_pos_SO_implSO_r in Hpos; assumption. firstorder.

    intros Q lQ HlP. rewrite <- HlP.    
    destruct (in_predicate_dec a (preds_in alpha2)).
      rewrite HlP in Hpos. rewrite <- HlP in Hpos. simpl.
      destruct Hpos as [Hp1 Hp2].
      case_eq (cap_pred lP (preds_in alpha2)).
        intros H.
        apply Pred_is_pos_SO_implSO_r in Hp1.  assumption. firstorder.

        intros R lR Hcap. apply conj.
          apply Pred_is_pos_SO_implSO_r in Hp1.  assumption. firstorder.

          rewrite <- Hcap. apply IHlP with (alpha1 := alpha1);
          try assumption.
          intros H. rewrite H in *. discriminate.

      rewrite HlP in Hpos. rewrite <- HlP in Hpos.
      destruct Hpos as [Hp1 Hp2].
      apply IHlP with (alpha1 := alpha1); assumption.
Qed.

Lemma lPred_is_neg_SO_conjSO_cap_pred_r : forall lP alpha1 alpha2,
  ~ (cap_pred lP (preds_in alpha2)) = nil ->
  lP_is_neg_SO (conjSO alpha1 alpha2) lP ->
  lP_is_neg_SO alpha2 (cap_pred lP (preds_in alpha2)).
Proof.
  induction lP; intros alpha1 alpha2 Hnil Hpos.
    simpl in *. contradiction.

    simpl in *. case_eq lP. intros HlP. rewrite HlP in *.
    destruct (in_predicate_dec a (preds_in alpha2)).
      apply Pred_is_neg_SO_conjSO_r in Hpos; assumption. firstorder.

    intros Q lQ HlP. rewrite <- HlP.
    destruct (in_predicate_dec a (preds_in alpha2)).
      rewrite HlP in Hpos. rewrite <- HlP in Hpos. simpl.
      destruct Hpos as [Hp1 Hp2].
      case_eq (cap_pred lP (preds_in alpha2)).
        intros H.
        apply Pred_is_neg_SO_conjSO_r in Hp1.  assumption. firstorder.

        intros R lR Hcap. apply conj.
          apply Pred_is_neg_SO_conjSO_r in Hp1.  assumption. firstorder.
          rewrite <- Hcap. apply IHlP with (alpha1 := alpha1);
          try assumption.
          intros H. rewrite H in *. discriminate.

      rewrite HlP in Hpos. rewrite <- HlP in Hpos.
      destruct Hpos as [Hp1 Hp2].
      apply IHlP with (alpha1 := alpha1); assumption.
Qed.

Lemma lPred_is_neg_SO_implSO_cap_pred_r : forall lP alpha1 alpha2,
  ~ (cap_pred lP (preds_in alpha2)) = nil ->
  lP_is_neg_SO (implSO alpha1 alpha2) lP ->
  lP_is_neg_SO alpha2 (cap_pred lP (preds_in alpha2)).
Proof.
  induction lP; intros alpha1 alpha2 Hnil Hpos.
    simpl in *. contradiction.

    simpl in *. case_eq lP. intros HlP. rewrite HlP in *.
    destruct (in_predicate_dec a (preds_in alpha2)).
      apply Pred_is_neg_SO_implSO_r in Hpos; assumption. firstorder.

    intros Q lQ HlP. rewrite <- HlP.
    destruct (in_predicate_dec a (preds_in alpha2)).
      rewrite HlP in Hpos. rewrite <- HlP in Hpos. simpl.
      destruct Hpos as [Hp1 Hp2].
      case_eq (cap_pred lP (preds_in alpha2)).
        intros H.
        apply Pred_is_neg_SO_implSO_r in Hp1.  assumption. firstorder.

        intros R lR Hcap. apply conj.
          apply Pred_is_neg_SO_implSO_r in Hp1.  assumption. firstorder.
          rewrite <- Hcap. apply IHlP with (alpha1 := alpha1);
          try assumption.
          intros H. rewrite H in *. discriminate.

      rewrite HlP in Hpos. rewrite <- HlP in Hpos.
      destruct Hpos as [Hp1 Hp2].
      apply IHlP with (alpha1 := alpha1); assumption.
Qed.

Lemma lPred_is_neg_SO_disjSO_cap_pred_r : forall lP alpha1 alpha2,
  ~ (cap_pred lP (preds_in alpha2)) = nil ->
  lP_is_neg_SO (disjSO alpha1 alpha2) lP ->
  lP_is_neg_SO alpha2 (cap_pred lP (preds_in alpha2)).
Proof.
  induction lP; intros alpha1 alpha2 Hnil Hpos.
    simpl in *. contradiction.

    simpl in *. case_eq lP. intros HlP. rewrite HlP in *.
    destruct (in_predicate_dec a (preds_in alpha2)).
      apply Pred_is_neg_SO_disjSO_r in Hpos; assumption. firstorder.

    intros Q lQ HlP. rewrite <- HlP.
    destruct (in_predicate_dec a (preds_in alpha2)).
      rewrite HlP in Hpos. rewrite <- HlP in Hpos. simpl.
      destruct Hpos as [Hp1 Hp2].
      case_eq (cap_pred lP (preds_in alpha2)).
        intros H.
        apply Pred_is_neg_SO_disjSO_r in Hp1.  assumption. firstorder.

        intros R lR Hcap. apply conj.
          apply Pred_is_neg_SO_disjSO_r in Hp1.  assumption. firstorder.
          rewrite <- Hcap. apply IHlP with (alpha1 := alpha1);
          try assumption.
          intros H. rewrite H in *. discriminate.

      rewrite HlP in Hpos. rewrite <- HlP in Hpos.
      destruct Hpos as [Hp1 Hp2].
      apply IHlP with (alpha1 := alpha1); assumption.
Qed.

Lemma lem_b7 : forall lP P W Ip1 Ip2,
  Ip_extends_l W Ip1 Ip2 (cons P lP) ->
  Ip_extends_l W (alt_Ip Ip1 (Ip2 P) P) Ip2 lP.
Proof.
  unfold Ip_extends_l.
  intros lP P W Ip1 Ip2 Hext Q.
  simpl in *.
  apply conj; intros Hpocc.
  + intros w Halt. 
    destruct (predicate_dec P Q). subst.
    rewrite alt_Ip_eq in Halt. auto.
    rewrite alt_Ip_neq in Halt; auto. apply Hext; firstorder.
  + destruct (predicate_dec P Q). subst.
    rewrite alt_Ip_eq. auto.
    rewrite alt_Ip_neq; auto. 
    pose proof (Hext Q). destruct H as [H1 H2].
    apply H2. firstorder.
Qed.

Lemma lem_b7_down : forall lP P W Ip1 Ip2,
  Ip_extends_l W Ip2 Ip1 (cons P lP) ->
  Ip_extends_l W Ip2 (alt_Ip Ip1 (Ip2 P) P) lP.
Proof.
  unfold Ip_extends_l.
  intros lP P W Ip1 Ip2 Hext Q.
  simpl in *.
  apply conj; intros Hpocc.
  + intros w Halt. 
    destruct (predicate_dec P Q). subst.
    rewrite alt_Ip_eq. auto.
    rewrite alt_Ip_neq; auto. apply Hext; firstorder.
  + destruct (predicate_dec P Q). subst.
    rewrite alt_Ip_eq. auto.
    rewrite alt_Ip_neq; auto. 
    pose proof (Hext Q). destruct H as [H1 H2].
    apply H2. firstorder.
Qed.

Lemma lem_b8 : forall lP P W Ip1 Ip2,
  Ip_extends_l W Ip1 Ip2 (cons P lP) ->
  Ip_extends_l W Ip1 (alt_Ip Ip1 (Ip2 P) P) (cons P nil).
Proof.
  intros lP P W Ip1 Ip2 Hext Q.
  specialize (Hext Q). destruct Hext as [H1 H2].
  simpl in *. 
  apply conj; intros Hpoc.  intros w H.
  +  destruct Hpoc. subst. rewrite alt_Ip_eq. apply H1.
    firstorder. auto. contradiction.
  + rewrite alt_Ip_neq. auto. firstorder.
Qed.

Lemma lem_b8_down : forall lP P W Ip1 Ip2,
  Ip_extends_l W Ip2 Ip1 (cons P lP) ->
  Ip_extends_l W (alt_Ip Ip1 (Ip2 P) P) Ip1 (cons P nil).
Proof.
  intros lP P W Ip1 Ip2 Hext Q.
  specialize (Hext Q). destruct Hext as [H1 H2].
  simpl in *. 
  apply conj; intros Hpoc.  intros w H.
  +  destruct Hpoc. subst. rewrite alt_Ip_eq in H. apply H1.
    firstorder. auto. contradiction.
  + rewrite alt_Ip_neq. auto. firstorder.
Qed.

Lemma lem_b6 : forall lP P alpha,
  alpha_upward_monotone_lP alpha (cons P nil) ->
  alpha_upward_monotone_lP alpha lP ->
  alpha_upward_monotone_lP alpha (cons P lP).
Proof.
  unfold alpha_upward_monotone_lP.
  intros lP P alpha H1 H2 W Iv Ir Ip1 Ip2 Hext SOt.
  apply H2 with (Ip := (alt_Ip Ip1 (Ip2 P) P)).
    apply lem_b7. assumption.
  apply H1 with (Ip := Ip1).
    apply lem_b8 with (lP := lP). all : assumption.
Qed.

Lemma lem_b6_down : forall lP P alpha,
  alpha_downward_monotone_lP alpha (cons P nil) ->
  alpha_downward_monotone_lP alpha lP ->
  alpha_downward_monotone_lP alpha (cons P lP).
Proof.
  unfold alpha_upward_monotone_lP.
  intros lP P alpha H1 H2 W Iv Ir Ip1 Ip2 Hext SOt.
  apply H2 with (Ip := (alt_Ip Ip1 (Ip2 P) P)).
    apply lem_b7_down. assumption.

  apply H1 with (Ip := Ip1).
    apply lem_b8_down with (lP := lP). all : assumption.
Qed.

Lemma lem_b10_down : forall alpha P,
  ~ In P (preds_in alpha)  ->
  alpha_downward_monotone_lP alpha (cons P nil).
Proof.
  intros alpha P Hin.
  unfold alpha_upward_monotone_lP.
  intros W Iv Ir Ip1 Ip2 Hext SOt.
  unfold Ip_extends_l in Hext.
assert (Ip2 = alt_Ip Ip1 (Ip2 P) P) as H.
    apply functional_extensionality. intros Q.
    unfold alt_Ip. destruct (predicate_dec P Q); subst. 
    auto. apply Hext. firstorder.

    rewrite H. 

apply P_not_occ_alt. firstorder.
    firstorder.
Qed.

Lemma lem_b10 : forall alpha P,
  ~ In P (preds_in alpha) ->
  alpha_upward_monotone_lP alpha (cons P nil).
Proof.
  intros alpha P Hin.
  unfold alpha_upward_monotone_lP.
  intros W Iv Ir Ip1 Ip2 Hext SOt.
  unfold Ip_extends_l in Hext.
assert (Ip2 = alt_Ip Ip1 (Ip2 P) P) as H.
    apply functional_extensionality. intros Q.
    unfold alt_Ip. destruct (predicate_dec P Q); subst. 
    auto. specialize (Hext Q). destruct Hext as [H1 H2].
    firstorder. firstorder. 
    rewrite H. apply P_not_occ_alt. firstorder.
    firstorder.
Qed.

Lemma lem_b3 : forall lP P alpha,
  ~ In P (preds_in alpha) ->
  alpha_upward_monotone_lP alpha lP ->  
  alpha_upward_monotone_lP alpha (cons P lP).
Proof.
  intros lP P alpha Hin Hup.
  apply lem_b6. apply lem_b10.
  all : assumption.
Qed.

Lemma lem_b3_down : forall lP P alpha,
  ~ In P (preds_in alpha) ->
  alpha_downward_monotone_lP alpha lP ->  
  alpha_downward_monotone_lP alpha (cons P lP).
Proof.
  intros lP P alpha Hin Hup.
  apply lem_b6_down. apply lem_b10_down.
  all : assumption.
Qed.

Lemma lem_b4 : forall lP  P alpha,
  alpha_upward_monotone_lP alpha (cons P lP) ->
  alpha_upward_monotone_lP alpha (cons P nil).
Proof.
  intros lP P alpha H.
  unfold alpha_upward_monotone_lP in *.
  intros W Iv Ir Ip Ip' Hext SOt.
  apply H with (Ip := Ip).
  unfold Ip_extends_l in *. intros Q. apply conj.
    intros H1 w H2.
    simpl in *. destruct (predicate_dec P Q).
      subst. apply Hext. firstorder. auto.

      specialize (Hext Q). 
      destruct Hext as [Hext1 Hext2]. rewrite <- Hext2. auto. 
      firstorder. firstorder. auto.
Qed.

Lemma lem_b4_down : forall lP  P alpha,
  alpha_downward_monotone_lP alpha (cons P lP) ->
  alpha_downward_monotone_lP alpha (cons P nil).
Proof.
  intros lP P alpha H.
  unfold alpha_upward_monotone_lP in *.
  intros W Iv Ir Ip Ip' Hext SOt.
  apply H with (Ip := Ip).
  unfold Ip_extends_l in *. intros Q. apply conj.
    intros H1 w H2.
    simpl in *. destruct (predicate_dec P Q).
      subst. apply Hext. firstorder. auto.

      specialize (Hext Q). 
      destruct Hext as [Hext1 Hext2]. rewrite <- Hext2. auto. 
      firstorder. firstorder. auto.
Qed.

Lemma lem_b4_2 : forall lP  P alpha,
  alpha_upward_monotone_lP alpha (cons P lP) ->
  alpha_upward_monotone_lP alpha lP.
Proof.
  intros lP P alpha H.
  unfold alpha_upward_monotone_lP in *.
  intros W Iv Ir Ip Ip' Hext SOt.
  apply H with (Ip := Ip).
  unfold Ip_extends_l in *. intros Q. apply conj.
    intros H1 w H2. simpl in *. 
    destruct (predicate_dec P Q). subst.
    destruct (Hext Q) as [H3 H4]. 
    destruct (in_dec predicate_dec Q lP).
    apply H3; auto. rewrite <- H4; auto.
    destruct H1. firstorder. apply Hext; auto.

    intros Hpocc. apply Hext. firstorder. auto.
Qed.

Lemma lem_b4_2_down : forall lP  P alpha,
  alpha_downward_monotone_lP alpha (cons P lP) ->
  alpha_downward_monotone_lP alpha lP.
Proof.
  intros lP P alpha H.
  unfold alpha_upward_monotone_lP in *.
  intros W Iv Ir Ip Ip' Hext SOt.
  apply H with (Ip := Ip).
  unfold Ip_extends_l in *. intros Q. apply conj.
    intros H1 w H2. simpl in *. 
    destruct (predicate_dec P Q). subst.
    destruct (Hext Q) as [H3 H4]. 
    destruct (in_dec predicate_dec Q lP).
    apply H3; auto. rewrite <- H4; auto.
    destruct H1. firstorder. apply Hext; auto.

    intros Hpocc. apply Hext. firstorder. auto.
Qed.

Lemma up_mono_cap_pred : forall lP l alpha,
  incl (preds_in alpha) l ->
  alpha_upward_monotone_lP alpha (cap_pred lP l ) ->
  alpha_upward_monotone_lP alpha lP.
Proof.
  induction lP; intros l alpha Hin Hup. auto.
  simpl in *. destruct (in_predicate_dec a l).
  pose proof (lem_b4_2 _ _ _ Hup) as H2.
  pose proof (lem_b4 _ _ _ Hup) as H3.
  apply lem_b6. auto.  
  apply IHlP with (l := l); assumption.

  apply lem_b3. intros H. apply n. eapply in_incl. 
  apply H. auto.
  apply IHlP with (l := l); assumption.
Qed.

Lemma down_mono_cap_pred : forall lP l alpha,
  incl (preds_in alpha) l  ->
  alpha_downward_monotone_lP alpha (cap_pred lP l ) ->
  alpha_downward_monotone_lP alpha lP.
Proof.
  induction lP; intros l alpha Hin Hup. auto.
  simpl in *. destruct (in_predicate_dec a l).
  pose proof (lem_b4_2_down _ _ _ Hup) as H2.
  pose proof (lem_b4_down _ _ _ Hup) as H3.
  apply lem_b6_down. auto.  
  apply IHlP with (l := l); assumption.

  apply lem_b3_down. intros H. apply n. eapply in_incl.
  apply H. auto.
  apply IHlP with (l := l); assumption.
Qed.

Lemma lem_b9 : forall lP alpha,
  cap_pred lP (preds_in alpha) = nil ->
  alpha_upward_monotone_lP alpha lP.
Proof.
  induction lP; intros alpha Hcap.
    apply alpha_upward_monotone_lP_nil.
  simpl in *. destruct (in_predicate_dec a (preds_in alpha)).
  discriminate.
  apply lem_b6. apply lem_b10. assumption.
  apply IHlP. assumption.
Qed.

Lemma lem_b9_down : forall lP alpha,
  cap_pred lP (preds_in alpha) = nil ->
  alpha_downward_monotone_lP alpha lP.
Proof.
  induction lP; intros alpha Hcap.
    apply alpha_downward_monotone_lP_nil.
  simpl in *. destruct (in_predicate_dec a (preds_in alpha)).
  discriminate.
  apply lem_b6_down. apply lem_b10_down. assumption.
  apply IHlP. assumption.
Qed. 

Lemma monotonicity_lP_SO_conjSO : forall (alpha1 alpha2 : SecOrder),
 (forall lP : list predicate,
           (lP_is_pos_SO alpha1 lP -> alpha_upward_monotone_lP alpha1 lP) /\
           (lP_is_neg_SO alpha1 lP -> alpha_downward_monotone_lP alpha1 lP)) ->
 (forall lP : list predicate,
           (lP_is_pos_SO alpha2 lP -> alpha_upward_monotone_lP alpha2 lP) /\
           (lP_is_neg_SO alpha2 lP -> alpha_downward_monotone_lP alpha2 lP)) ->
forall lP : list predicate,
(lP_is_pos_SO (conjSO alpha1 alpha2) lP ->
 alpha_upward_monotone_lP (conjSO alpha1 alpha2) lP) /\
(lP_is_neg_SO (conjSO alpha1 alpha2) lP ->
 alpha_downward_monotone_lP (conjSO alpha1 alpha2) lP).
Proof.
  intros alpha1 alpha2 IH1 IH2 lP.
  apply conj; intros Hpos.
     case_eq lP.
      intros HlP; rewrite HlP in *. apply alpha_upward_monotone_lP_nil.
    intros P' lP' HlP. rewrite <- HlP.
    assert (~ lP = nil) as Hnil.
      rewrite HlP. discriminate.

    case_eq (cap_pred lP (preds_in alpha1)).
      intros Hc1.
      pose proof (lPred_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc.  
      pose proof (lPred_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc2.  
      pose proof (lPred_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc3.  
      apply lem_b1 in Hpoc. simpl in Hpoc2.
      apply incl_cap_pred in Hpoc2.
      all : try assumption.

      pose proof (incl_cap_pred_f _ _ _ Hnil Hpoc3 Hc1).
      apply alpha_upward_monotone_lP_conjSO_fwd.
        apply lem_b9. assumption.
        apply up_mono_cap_pred with (l := (preds_in alpha2)).
          apply incl_refl.
        apply IH2. apply lPred_is_pos_SO_conjSO_cap_pred_r in Hpos;
          assumption.

      intros Q2 lQ2 Hcap2.
    case_eq (cap_pred lP (preds_in alpha2)).
      intros Hc1.
      pose proof (lPred_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc.  
      pose proof (lPred_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc2.  
      pose proof (lPred_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc3.  
      apply lem_b1_l in Hpoc. simpl in Hpoc2.
      apply incl_cap_pred_l in Hpoc2.
      all : try assumption.

      pose proof (incl_cap_pred_f_l _ _ _ Hnil Hpoc3 Hc1).
      apply alpha_upward_monotone_lP_conjSO_fwd.
        
        apply up_mono_cap_pred with (l := (preds_in alpha1)).
          apply incl_refl.
        apply IH1. apply lPred_is_pos_SO_conjSO_cap_pred_l in Hpos;
          assumption.

        apply lem_b9. assumption.

      intros Q3 lQ3 HlQ3. 
      pose proof (lPred_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc.  
      pose proof (lPred_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc2.  
      pose proof (lPred_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc3.
      assert (~ (cap_pred lP (preds_in alpha1) = nil)) as H1.
        rewrite Hcap2. discriminate.
      assert (~ (cap_pred lP (preds_in alpha2) = nil)) as H2.
        rewrite HlQ3. discriminate.

      apply alpha_upward_monotone_lP_conjSO_fwd.
        apply up_mono_cap_pred with (l := (preds_in alpha1)).
          apply incl_refl.
        apply IH1. apply lPred_is_pos_SO_conjSO_cap_pred_l in Hpos;
        assumption.

        apply up_mono_cap_pred with (l := (preds_in alpha2)).
          apply incl_refl.
        apply IH2. apply lPred_is_pos_SO_conjSO_cap_pred_r in Hpos;
        assumption.


     case_eq lP.
      intros HlP; rewrite HlP in *. apply alpha_downward_monotone_lP_nil.
    intros P' lP' HlP. rewrite <- HlP.
    assert (~ lP = nil) as Hnil.
      rewrite HlP. discriminate.

    case_eq (cap_pred lP (preds_in alpha1)).
      intros Hc1.
      pose proof (lPred_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc.  
      pose proof (lPred_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc2.  
      pose proof (lPred_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc3.  
      apply lem_b1 in Hpoc. simpl in Hpoc2.
      apply incl_cap_pred in Hpoc2.
      all : try assumption.

      pose proof (incl_cap_pred_f _ _ _ Hnil Hpoc3 Hc1).
      apply alpha_downward_monotone_lP_conjSO_fwd.
        apply lem_b9_down. assumption.
        apply down_mono_cap_pred with (l := (preds_in alpha2)).
          apply incl_refl.
        apply IH2. apply lPred_is_neg_SO_conjSO_cap_pred_r in Hpos;
          assumption.

      intros Q2 lQ2 Hcap2.
    case_eq (cap_pred lP (preds_in alpha2)).
      intros Hc1.
      pose proof (lPred_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc.  
      pose proof (lPred_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc2.  
      pose proof (lPred_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc3.  
      apply lem_b1_l in Hpoc. simpl in Hpoc2.
      apply incl_cap_pred_l in Hpoc2.
      all : try assumption.

      pose proof (incl_cap_pred_f_l _ _ _ Hnil Hpoc3 Hc1).
      apply alpha_downward_monotone_lP_conjSO_fwd.
        
        apply down_mono_cap_pred with (l := (preds_in alpha1)).
          apply incl_refl.
        apply IH1. apply lP_is_down_SO_conjSO_cap_pred_l in Hpos;
          assumption.

        apply lem_b9_down. assumption.

      intros Q3 lQ3 HlQ3. 
      pose proof (lPred_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc.  
      pose proof (lPred_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc2.  
      pose proof (lPred_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc3.
      assert (~ (cap_pred lP (preds_in alpha1) = nil)) as H1.
        rewrite Hcap2. discriminate.
      assert (~ (cap_pred lP (preds_in alpha2) = nil)) as H2.
        rewrite HlQ3. discriminate.

      apply alpha_downward_monotone_lP_conjSO_fwd.
        apply down_mono_cap_pred with (l := (preds_in alpha1)).
          apply incl_refl.
        apply IH1. apply lPred_is_neg_SO_conjSO_cap_pred_l in Hpos;
        assumption.

        apply down_mono_cap_pred with (l := (preds_in alpha2)).
          apply incl_refl.
        apply IH2. apply lPred_is_neg_SO_conjSO_cap_pred_r in Hpos;
        assumption.
Qed.


(* ----------- *)

Lemma monotonicity_lP_SO_disjSO : forall (alpha1 alpha2 : SecOrder),
 (forall lP : list predicate,
           (lP_is_pos_SO alpha1 lP -> alpha_upward_monotone_lP alpha1 lP) /\
           (lP_is_neg_SO alpha1 lP -> alpha_downward_monotone_lP alpha1 lP)) ->
 (forall lP : list predicate,
           (lP_is_pos_SO alpha2 lP -> alpha_upward_monotone_lP alpha2 lP) /\
           (lP_is_neg_SO alpha2 lP -> alpha_downward_monotone_lP alpha2 lP)) ->
forall lP : list predicate,
(lP_is_pos_SO (disjSO alpha1 alpha2) lP ->
 alpha_upward_monotone_lP (disjSO alpha1 alpha2) lP) /\
(lP_is_neg_SO (disjSO alpha1 alpha2) lP ->
 alpha_downward_monotone_lP (disjSO alpha1 alpha2) lP).
Proof.
  intros alpha1 alpha2 IH1 IH2 lP.
  apply conj; intros Hpos.
     case_eq lP.
      intros HlP; rewrite HlP in *. apply alpha_upward_monotone_lP_nil.
    intros P' lP' HlP. rewrite <- HlP.
    assert (~ lP = nil) as Hnil.
      rewrite HlP. discriminate.

    case_eq (cap_pred lP (preds_in alpha1)).
      intros Hc1.
      pose proof (lPred_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc.  
      pose proof (lPred_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc2.  
      pose proof (lPred_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc3.  
      apply lem_b1 in Hpoc. simpl in Hpoc2.
      apply incl_cap_pred in Hpoc2.
      all : try assumption.

      pose proof (incl_cap_pred_f _ _ _ Hnil Hpoc3 Hc1).
      apply alpha_upward_monotone_lP_disjSO_fwd.
        apply lem_b9. assumption.
        apply up_mono_cap_pred with (l := (preds_in alpha2)).
          apply incl_refl.
        apply IH2. apply lPred_is_pos_SO_disjSO_cap_pred_r in Hpos;
          assumption.

      intros Q2 lQ2 Hcap2.
    case_eq (cap_pred lP (preds_in alpha2)).
      intros Hc1.
      pose proof (lPred_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc.  
      pose proof (lPred_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc2.  
      pose proof (lPred_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc3.  
      apply lem_b1_l in Hpoc. simpl in Hpoc2.
      apply incl_cap_pred_l in Hpoc2.
      all : try assumption.

      pose proof (incl_cap_pred_f_l _ _ _ Hnil Hpoc3 Hc1).
      apply alpha_upward_monotone_lP_disjSO_fwd.
        
        apply up_mono_cap_pred with (l := (preds_in alpha1)).
          apply incl_refl.
        apply IH1. apply lPred_is_pos_SO_disjSO_cap_pred_l in Hpos;
          assumption.

        apply lem_b9. assumption.

      intros Q3 lQ3 HlQ3. 
      pose proof (lPred_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc.  
      pose proof (lPred_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc2.  
      pose proof (lPred_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc3.
      assert (~ (cap_pred lP (preds_in alpha1) = nil)) as H1.
        rewrite Hcap2. discriminate.
      assert (~ (cap_pred lP (preds_in alpha2) = nil)) as H2.
        rewrite HlQ3. discriminate.

      apply alpha_upward_monotone_lP_disjSO_fwd.
        apply up_mono_cap_pred with (l := (preds_in alpha1)).
          apply incl_refl.
        apply IH1. apply lPred_is_pos_SO_disjSO_cap_pred_l in Hpos;
        assumption.

        apply up_mono_cap_pred with (l := (preds_in alpha2)).
          apply incl_refl.
        apply IH2. apply lPred_is_pos_SO_disjSO_cap_pred_r in Hpos;
        assumption.


     case_eq lP.
      intros HlP; rewrite HlP in *. apply alpha_downward_monotone_lP_nil.
    intros P' lP' HlP. rewrite <- HlP.
    assert (~ lP = nil) as Hnil.
      rewrite HlP. discriminate.

    case_eq (cap_pred lP (preds_in alpha1)).
      intros Hc1.
      pose proof (lPred_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc.  
      pose proof (lPred_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc2.  
      pose proof (lPred_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc3.  
      apply lem_b1 in Hpoc. simpl in Hpoc2.
      apply incl_cap_pred in Hpoc2.
      all : try assumption.

      pose proof (incl_cap_pred_f _ _ _ Hnil Hpoc3 Hc1).
      apply alpha_downward_monotone_lP_disjSO_fwd.
        apply lem_b9_down. assumption.
        apply down_mono_cap_pred with (l := (preds_in alpha2)).
          apply incl_refl.
        apply IH2. apply lPred_is_neg_SO_disjSO_cap_pred_r in Hpos;
          assumption.

      intros Q2 lQ2 Hcap2.
    case_eq (cap_pred lP (preds_in alpha2)).
      intros Hc1.
      pose proof (lPred_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc.  
      pose proof (lPred_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc2.  
      pose proof (lPred_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc3.  
      apply lem_b1_l in Hpoc. simpl in Hpoc2.
      apply incl_cap_pred_l in Hpoc2.
      all : try assumption.

      pose proof (incl_cap_pred_f_l _ _ _ Hnil Hpoc3 Hc1).
      apply alpha_downward_monotone_lP_disjSO_fwd.
        
        apply down_mono_cap_pred with (l := (preds_in alpha1)).
          apply incl_refl.
        apply IH1. apply lP_is_down_SO_disjSO_cap_pred_l in Hpos;
          assumption.

        apply lem_b9_down. assumption.

      intros Q3 lQ3 HlQ3. 
      pose proof (lPred_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc.  
      pose proof (lPred_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc2.  
      pose proof (lPred_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc3.
      assert (~ (cap_pred lP (preds_in alpha1) = nil)) as H1.
        rewrite Hcap2. discriminate.
      assert (~ (cap_pred lP (preds_in alpha2) = nil)) as H2.
        rewrite HlQ3. discriminate.

      apply alpha_downward_monotone_lP_disjSO_fwd.
        apply down_mono_cap_pred with (l := (preds_in alpha1)).
          apply incl_refl.
        apply IH1. apply lPred_is_neg_SO_disjSO_cap_pred_l in Hpos;
        assumption.

        apply down_mono_cap_pred with (l := (preds_in alpha2)).
          apply incl_refl.
        apply IH2. apply lPred_is_neg_SO_disjSO_cap_pred_r in Hpos;
        assumption.
Qed.

Lemma monotonicity_lP_SO_implSO : forall (alpha1 alpha2 : SecOrder),
 (forall lP : list predicate,
           (lP_is_pos_SO alpha1 lP -> alpha_upward_monotone_lP alpha1 lP) /\
           (lP_is_neg_SO alpha1 lP -> alpha_downward_monotone_lP alpha1 lP)) ->
 (forall lP : list predicate,
           (lP_is_pos_SO alpha2 lP -> alpha_upward_monotone_lP alpha2 lP) /\
           (lP_is_neg_SO alpha2 lP -> alpha_downward_monotone_lP alpha2 lP)) ->
forall lP : list predicate,
(lP_is_pos_SO (implSO alpha1 alpha2) lP ->
 alpha_upward_monotone_lP (implSO alpha1 alpha2) lP) /\
(lP_is_neg_SO (implSO alpha1 alpha2) lP ->
 alpha_downward_monotone_lP (implSO alpha1 alpha2) lP).
Proof.
  intros alpha1 alpha2 IH1 IH2 lP.
  apply conj; intros Hpos.
     case_eq lP.
      intros HlP; rewrite HlP in *. apply alpha_upward_monotone_lP_nil.
    intros P' lP' HlP. rewrite <- HlP.
    assert (~ lP = nil) as Hnil.
      rewrite HlP. discriminate.

    case_eq (cap_pred lP (preds_in alpha1)).
      intros Hc1.
      pose proof (lPred_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc.  
      pose proof (lPred_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc2.  
      pose proof (lPred_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc3.  
      apply lem_b1 in Hpoc. simpl in Hpoc2.
      apply incl_cap_pred in Hpoc2.
      all : try assumption.

      pose proof (incl_cap_pred_f _ _ _ Hnil Hpoc3 Hc1).
      apply alpha_upward_monotone_lP_implSO_fwd.
        apply lem_b9_down. assumption.
        apply up_mono_cap_pred with (l := (preds_in alpha2)).
          apply incl_refl.
        apply IH2. apply lPred_is_pos_SO_implSO_cap_pred_r in Hpos;
          assumption.

      intros Q2 lQ2 Hcap2.
    case_eq (cap_pred lP (preds_in alpha2)).
      intros Hc1.
      pose proof (lPred_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc.  
      pose proof (lPred_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc2.  
      pose proof (lPred_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc3.  
      apply lem_b1_l in Hpoc. simpl in Hpoc2.
      apply incl_cap_pred_l in Hpoc2.
      all : try assumption.

      pose proof (incl_cap_pred_f_l _ _ _ Hnil Hpoc3 Hc1).
      apply alpha_upward_monotone_lP_implSO_fwd.
        
        apply down_mono_cap_pred with (l := (preds_in alpha1)).
          apply incl_refl.
        apply IH1. apply lPred_is_pos_SO_implSO_cap_pred_l in Hpos;
          assumption.

        apply lem_b9. assumption.

      intros Q3 lQ3 HlQ3. 
      pose proof (lPred_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc.  
      pose proof (lPred_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc2.  
      pose proof (lPred_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc3.
      assert (~ (cap_pred lP (preds_in alpha1) = nil)) as H1.
        rewrite Hcap2. discriminate.
      assert (~ (cap_pred lP (preds_in alpha2) = nil)) as H2.
        rewrite HlQ3. discriminate.

      apply alpha_upward_monotone_lP_implSO_fwd.
        apply down_mono_cap_pred with (l := (preds_in alpha1)).
          apply incl_refl.
        apply IH1. apply lPred_is_pos_SO_implSO_cap_pred_l in Hpos;
        assumption.

        apply up_mono_cap_pred with (l := (preds_in alpha2)).
          apply incl_refl.
        apply IH2. apply lPred_is_pos_SO_implSO_cap_pred_r in Hpos;
        assumption.


     case_eq lP.
      intros HlP; rewrite HlP in *. apply alpha_downward_monotone_lP_nil.
    intros P' lP' HlP. rewrite <- HlP.
    assert (~ lP = nil) as Hnil.
      rewrite HlP. discriminate.

    case_eq (cap_pred lP (preds_in alpha1)).
      intros Hc1.
      pose proof (lPred_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc.  
      pose proof (lPred_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc2.  
      pose proof (lPred_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc3.  
      apply lem_b1 in Hpoc. simpl in Hpoc2.
      apply incl_cap_pred in Hpoc2.
      all : try assumption.

      pose proof (incl_cap_pred_f _ _ _ Hnil Hpoc3 Hc1).
      apply alpha_downward_monotone_lP_implSO_fwd.
        apply lem_b9. assumption.
        apply down_mono_cap_pred with (l := (preds_in alpha2)).
          apply incl_refl.
        apply IH2. apply lPred_is_neg_SO_implSO_cap_pred_r in Hpos;
          assumption.

      intros Q2 lQ2 Hcap2.
    case_eq (cap_pred lP (preds_in alpha2)).
      intros Hc1.
      pose proof (lPred_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc.  
      pose proof (lPred_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc2.  
      pose proof (lPred_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc3.  
      apply lem_b1_l in Hpoc. simpl in Hpoc2.
      apply incl_cap_pred_l in Hpoc2.
      all : try assumption.

      pose proof (incl_cap_pred_f_l _ _ _ Hnil Hpoc3 Hc1).
      apply alpha_downward_monotone_lP_implSO_fwd.
        
        apply up_mono_cap_pred with (l := (preds_in alpha1)).
          apply incl_refl.
        apply IH1. apply lP_is_down_SO_implSO_cap_pred_l in Hpos;
          assumption.

        apply lem_b9_down. assumption.

      intros Q3 lQ3 HlQ3. 
      pose proof (lPred_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc.  
      pose proof (lPred_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc2.  
      pose proof (lPred_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc3.
      assert (~ (cap_pred lP (preds_in alpha1) = nil)) as H1.
        rewrite Hcap2. discriminate.
      assert (~ (cap_pred lP (preds_in alpha2) = nil)) as H2.
        rewrite HlQ3. discriminate.

      apply alpha_downward_monotone_lP_implSO_fwd.
        apply up_mono_cap_pred with (l := (preds_in alpha1)).
          apply incl_refl.
        apply IH1. apply lPred_is_neg_SO_implSO_cap_pred_l in Hpos;
        assumption.

        apply down_mono_cap_pred with (l := (preds_in alpha2)).
          apply incl_refl.
        apply IH2. apply lPred_is_neg_SO_implSO_cap_pred_r in Hpos;
        assumption.
Qed.

Lemma lem_bb : forall lP W Ip Ip' pa Q,
Ip_extends_l W Ip Ip' lP ->
Ip_extends_l W (alt_Ip Ip pa Q) (alt_Ip Ip' pa Q) lP.
Proof.
  unfold Ip_extends_l. intros lP W Ip Ip' pa P H Q.
  apply conj; intros Hpocc.
  + intros w Halt. simpl in *. 
    destruct (predicate_dec P Q). subst.
    rewrite alt_Ip_eq in *. auto.
    rewrite alt_Ip_neq in *. apply H. all : auto. 
  + destruct (predicate_dec P Q). subst. 
    do 2 rewrite alt_Ip_eq. auto.
    rewrite alt_Ip_neq.  rewrite alt_Ip_neq. apply H.
    all : auto.
Qed. 

Lemma up_allSO_lP : forall lP (alpha : SecOrder) ( Q: predicate),
    ((alpha_upward_monotone_lP alpha lP) ->
     (alpha_upward_monotone_lP (allSO Q alpha) lP)).
Proof.
  intros lP alpha Q Hmono.
  unfold alpha_upward_monotone_lP in *.
  intros W Iv R Ip Ip' Ipext SOt.
  rewrite SOturnst_allSO.
  rewrite SOturnst_allSO in SOt. intros pa.
  specialize (SOt pa).
  apply Hmono with (Ip := (alt_Ip Ip pa Q)).
    apply lem_bb. all : assumption.
Qed.

Lemma up_exSO_lP : forall lP (alpha : SecOrder) ( Q: predicate),
    ((alpha_upward_monotone_lP alpha lP) ->
     (alpha_upward_monotone_lP (exSO Q alpha) lP)).
Proof.
  intros lP alpha Q Hmono.
  unfold alpha_upward_monotone_lP in *.
  intros W Iv R Ip Ip' Ipext SOt.
  rewrite SOturnst_exSO.
  rewrite SOturnst_exSO in SOt. destruct SOt as [pa SOt].
  exists pa.
  apply Hmono with (Ip := (alt_Ip Ip pa Q)).
    apply lem_bb. all : assumption.
Qed.

Lemma down_allSO_lP : forall lP (alpha : SecOrder) ( Q: predicate),
    ((alpha_downward_monotone_lP alpha lP) ->
     (alpha_downward_monotone_lP (allSO Q alpha) lP)).
Proof.
  intros lP alpha Q Hmono.
  unfold alpha_downward_monotone_lP in *.
  intros W Iv R Ip Ip' Ipext SOt.
  rewrite SOturnst_allSO.
  rewrite SOturnst_allSO in SOt. intros pa.
  specialize (SOt pa).
  apply Hmono with (Ip := (alt_Ip Ip pa Q)).
    apply lem_bb. all : assumption.
Qed.

Lemma down_exSO_lP : forall lP (alpha : SecOrder) ( Q: predicate),
    ((alpha_downward_monotone_lP alpha lP) ->
     (alpha_downward_monotone_lP (exSO Q alpha) lP)).
Proof.
  intros lP alpha Q Hmono.
  unfold alpha_downward_monotone_lP in *.
  intros W Iv R Ip Ip' Ipext SOt.
  rewrite SOturnst_exSO.
  rewrite SOturnst_exSO in SOt. destruct SOt as [pa SOt]. exists pa.
  apply Hmono with (Ip := (alt_Ip Ip pa Q)).
    apply lem_bb. all : assumption.
Qed.

Lemma lPred_is_pos_SO_allSO : forall lP P alpha,
  ~ In P lP ->
  lP_is_pos_SO (allSO P alpha) lP ->
  lP_is_pos_SO alpha lP.
Proof.
  induction lP; intros P alpha Hin Hpos. contradiction.
  simpl in *.  destruct lP.
  + apply Pred_is_pos_SO_allSO_neq in Hpos; auto.
  + remember (p :: lP) as lP'. destruct Hpos as [H1 H2].
    apply conj. apply Pred_is_pos_SO_allSO_neq in H1; auto.
    eapply IHlP; auto. 2 : apply H2. firstorder.
Qed.

Lemma lPred_is_pos_SO_exSO : forall lP P alpha,
  ~ In P lP ->
  lP_is_pos_SO (exSO P alpha) lP ->
  lP_is_pos_SO alpha lP.
Proof.
  induction lP; intros P alpha Hin Hpos. contradiction.
  simpl in *.  destruct lP.
  + apply Pred_is_pos_SO_exSO_neq in Hpos; auto.
  + remember (p :: lP) as lP'. destruct Hpos as [H1 H2].
    apply conj. apply Pred_is_pos_SO_exSO_neq in H1; auto.
    eapply IHlP; auto. 2 : apply H2. firstorder.
Qed. 

Lemma lPred_is_neg_SO_allSO : forall lP P alpha,
  ~ In P lP ->
  lP_is_neg_SO (allSO P alpha) lP ->
  lP_is_neg_SO alpha lP.
Proof.
  induction lP; intros P alpha Hin Hpos. contradiction.
  simpl in *.  destruct lP.
  + apply Pred_is_neg_SO_allSO_neq in Hpos; auto.
  + remember (p :: lP) as lP'. destruct Hpos as [H1 H2].
    apply conj. apply Pred_is_neg_SO_allSO_neq in H1; auto.
    eapply IHlP; auto. 2 : apply H2. firstorder.
Qed.

Lemma lPred_is_neg_SO_exSO : forall lP P alpha,
  ~ In P lP ->
  lP_is_neg_SO (exSO P alpha) lP ->
  lP_is_neg_SO alpha lP.
Proof.
  induction lP; intros P alpha Hin Hpos. contradiction.
  simpl in *.  destruct lP.
  + apply Pred_is_neg_SO_exSO_neq in Hpos; auto.
  + remember (p :: lP) as lP'. destruct Hpos as [H1 H2].
    apply conj. apply Pred_is_neg_SO_exSO_neq in H1; auto.
    eapply IHlP; auto. 2 : apply H2. firstorder.
Qed. 

Lemma mono_lem1 : forall lP P alpha,
  ~ (rem_pred lP P) = nil ->
  lP_is_pos_SO (allSO P alpha) lP ->
  lP_is_pos_SO alpha (rem_pred lP P).
Proof.
  induction lP; intros P alpha Hnil H. contradiction.
  simpl in *. destruct lP. 
  + destruct (predicate_dec P a). contradiction.
    simpl. apply Pred_is_pos_SO_allSO_neq in H.
    assumption. intros HH. inversion HH as [HH']. rewrite HH' in *.
    contradiction.
  + remember (p :: lP) as lP'. destruct H as [H1 H2]. 
    destruct (predicate_dec P a). subst. apply IHlP; auto.
    simpl. case_eq (rem_pred lP' P). intros Hnil2. 
    apply Pred_is_pos_SO_allSO_neq in H1; auto.
    intros R l Hrem.
    remember (cons R l) as t.
    rewrite <- Hrem.
    apply conj. apply Pred_is_pos_SO_allSO_neq in H1; auto.
    apply IHlP. rewrite Hrem. rewrite Heqt. intros. discriminate.
    firstorder.
Qed.

Lemma mono_lem1_exSO : forall lP P alpha,
  ~ (rem_pred lP P) = nil ->
  lP_is_pos_SO (exSO P alpha) lP ->
  lP_is_pos_SO alpha (rem_pred lP P).
Proof.
  induction lP; intros P alpha Hnil H. contradiction.
  simpl in *. destruct lP. 
  + destruct (predicate_dec P a). contradiction.
    simpl. apply Pred_is_pos_SO_exSO_neq in H.
    assumption. intros HH. inversion HH as [HH']. rewrite HH' in *.
    contradiction.
  + remember (p :: lP) as lP'. destruct H as [H1 H2]. 
    destruct (predicate_dec P a). subst. apply IHlP; auto.
    simpl. case_eq (rem_pred lP' P). intros Hnil2. 
    apply Pred_is_pos_SO_exSO_neq in H1; auto.
    intros R l Hrem.
    remember (cons R l) as t.
    rewrite <- Hrem.
    apply conj. apply Pred_is_pos_SO_exSO_neq in H1; auto.
    apply IHlP. rewrite Hrem. rewrite Heqt. intros. discriminate.
    firstorder.
Qed.

Lemma down_mono_lem1 : forall lP P alpha,
  ~ (rem_pred lP P) = nil ->
  lP_is_neg_SO (allSO P alpha) lP ->
  lP_is_neg_SO alpha (rem_pred lP P).
Proof.
  induction lP; intros P alpha Hnil H. contradiction.
  simpl in *. destruct lP. 
  + destruct (predicate_dec P a). contradiction.
    simpl. apply Pred_is_neg_SO_allSO_neq in H.
    assumption. intros HH. inversion HH as [HH']. rewrite HH' in *.
    contradiction.
  + remember (p :: lP) as lP'. destruct H as [H1 H2]. 
    destruct (predicate_dec P a). subst. apply IHlP; auto.
    simpl. case_eq (rem_pred lP' P). intros Hnil2. 
    apply Pred_is_neg_SO_allSO_neq in H1; auto.
    intros R l Hrem.
    remember (cons R l) as t.
    rewrite <- Hrem.
    apply conj. apply Pred_is_neg_SO_allSO_neq in H1; auto.
    apply IHlP. rewrite Hrem. rewrite Heqt. intros. discriminate.
    firstorder.
Qed.

Lemma down_mono_lem1_exSO : forall lP P alpha,
  ~ (rem_pred lP P) = nil ->
  lP_is_neg_SO (exSO P alpha) lP ->
  lP_is_neg_SO alpha (rem_pred lP P).
Proof.
  induction lP; intros P alpha Hnil H. contradiction.
  simpl in *. destruct lP. 
  + destruct (predicate_dec P a). contradiction.
    simpl. apply Pred_is_neg_SO_exSO_neq in H.
    assumption. intros HH. inversion HH as [HH']. rewrite HH' in *.
    contradiction.
  + remember (p :: lP) as lP'. destruct H as [H1 H2]. 
    destruct (predicate_dec P a). subst. apply IHlP; auto.
    simpl. case_eq (rem_pred lP' P). intros Hnil2. 
    apply Pred_is_neg_SO_exSO_neq in H1; auto.
    intros R l Hrem.
    remember (cons R l) as t.
    rewrite <- Hrem.
    apply conj. apply Pred_is_neg_SO_exSO_neq in H1; auto.
    apply IHlP. rewrite Hrem. rewrite Heqt. intros. discriminate.
    firstorder.
Qed.

Lemma lem_Ip_extends_rem_pred : forall lP P W Ip Ip' pa,
  Ip_extends_l W Ip Ip' lP ->
  Ip_extends_l W (alt_Ip Ip pa P) (alt_Ip Ip' pa P) (rem_pred lP P).
Proof.
  intros lP P W Ip Ip' pa H Q.
  specialize (H Q). destruct H as [H1 H2].
  apply conj. intros Hpocc w Halt. 
  + destruct (predicate_dec P Q). subst. rewrite alt_Ip_eq in *. auto.
    rewrite alt_Ip_neq in *; auto. apply H1; auto.
    apply in_rem_pred in Hpocc; auto.
  + intros H. destruct (predicate_dec P Q). subst.
    do 2 rewrite alt_Ip_eq; auto. rewrite alt_Ip_neq; auto. 
    rewrite alt_Ip_neq; auto. apply H2. intros HH. apply  H.
    apply in_rem_pred; auto.
Qed.

Lemma mono_lem2 : forall lP P alpha,
  In P lP ->
  alpha_upward_monotone_lP alpha (rem_pred lP P) ->
  alpha_upward_monotone_lP (allSO P alpha) lP.
Proof.
  intros lP P alpha Hin H.
  unfold alpha_upward_monotone_lP in *. intros W Iv Ir Ip Ip' Hext SOt.
  rewrite SOturnst_allSO in *. intros pa. specialize (SOt pa).
  apply H with (Ip := (alt_Ip Ip pa P)).
  apply lem_Ip_extends_rem_pred. assumption.
    assumption.
Qed.

Lemma mono_lem2_exSO : forall lP P alpha,
  In P lP ->
  alpha_upward_monotone_lP alpha (rem_pred lP P) ->
  alpha_upward_monotone_lP (exSO P alpha) lP.
Proof.
  intros lP P alpha Hin H.
  unfold alpha_upward_monotone_lP in *. intros W Iv Ir Ip Ip' Hext SOt.
  rewrite SOturnst_exSO in *. destruct SOt as [pa SOt]. exists pa.
  apply H with (Ip := (alt_Ip Ip pa P)).
  apply lem_Ip_extends_rem_pred. assumption.
    assumption.
Qed.

Lemma down_mono_lem2 : forall lP P alpha,
  In P lP ->
  alpha_downward_monotone_lP alpha (rem_pred lP P) ->
  alpha_downward_monotone_lP (allSO P alpha) lP.
Proof.
  intros lP P alpha Hin H.
  unfold alpha_downward_monotone_lP in *. intros W Iv Ir Ip Ip' Hext SOt.
  rewrite SOturnst_allSO in *. intros pa. specialize (SOt pa).
  apply H with (Ip := (alt_Ip Ip pa P)).
  apply lem_Ip_extends_rem_pred. assumption.
    assumption.
Qed.

Lemma down_mono_lem2_exSO : forall lP P alpha,
  In P lP ->
  alpha_downward_monotone_lP alpha (rem_pred lP P) ->
  alpha_downward_monotone_lP (exSO P alpha) lP.
Proof.
  intros lP P alpha Hin H.
  unfold alpha_downward_monotone_lP in *. intros W Iv Ir Ip Ip' Hext SOt.
  rewrite SOturnst_exSO in *. destruct SOt as [pa SOt]. exists pa.
  apply H with (Ip := (alt_Ip Ip pa P)).
  apply lem_Ip_extends_rem_pred. assumption.
    assumption.
Qed.

Lemma lPred_is_pos_SO_allSO2 : forall lP P alpha,
  Pred_in_SO alpha P ->
  lP_is_pos_SO (allSO P alpha) lP ->
  lP_is_pos_SO alpha lP.
Proof.
  induction lP; intros P alpha Hin Hpos. contradiction.
  simpl in *. destruct lP.
  destruct (predicate_dec P a); subst.
  apply Pred_is_pos_SO_allSO in Hpos; auto. 
  apply Pred_is_pos_SO_allSO_neq in Hpos; auto. 
  destruct Hpos as [H1 H2].
  apply conj.
  destruct (predicate_dec P a); subst.
  apply Pred_is_pos_SO_allSO in H1; auto. 
  apply Pred_is_pos_SO_allSO_neq in H1; auto.
  firstorder.
Qed.

Lemma lPred_is_pos_SO_exSO2 : forall lP P alpha,
  Pred_in_SO alpha P ->
  lP_is_pos_SO (exSO P alpha) lP ->
  lP_is_pos_SO alpha lP.
Proof.
  induction lP; intros P alpha Hin Hpos. contradiction.
  simpl in *. destruct lP.
  destruct (predicate_dec P a); subst.
  apply Pred_is_pos_SO_exSO in Hpos; auto. 
  apply Pred_is_pos_SO_exSO_neq in Hpos; auto. 
  destruct Hpos as [H1 H2].
  apply conj.
  destruct (predicate_dec P a); subst.
  apply Pred_is_pos_SO_exSO in H1; auto. 
  apply Pred_is_pos_SO_exSO_neq in H1; auto.
  firstorder.
Qed.

Lemma lPred_is_neg_SO_allSO2 : forall lP P alpha,
  Pred_in_SO alpha P  ->
  lP_is_neg_SO (allSO P alpha) lP ->
  lP_is_neg_SO alpha lP.
Proof.
  induction lP; intros P alpha Hin Hpos. contradiction.
  simpl in *. destruct lP.
  destruct (predicate_dec P a); subst.
  apply Pred_is_neg_SO_allSO in Hpos; auto. 
  apply Pred_is_neg_SO_allSO_neq in Hpos; auto. 
  destruct Hpos as [H1 H2].
  apply conj.
  destruct (predicate_dec P a); subst.
  apply Pred_is_neg_SO_allSO in H1; auto. 
  apply Pred_is_neg_SO_allSO_neq in H1; auto.
  firstorder.
Qed.

Lemma lPred_is_neg_SO_exSO2 : forall lP P alpha,
  Pred_in_SO alpha P ->
  lP_is_neg_SO (exSO P alpha) lP ->
  lP_is_neg_SO alpha lP.
Proof.
  induction lP; intros P alpha Hin Hpos. contradiction.
  simpl in *. destruct lP.
  destruct (predicate_dec P a); subst.
  apply Pred_is_neg_SO_exSO in Hpos; auto. 
  apply Pred_is_neg_SO_exSO_neq in Hpos; auto. 
  destruct Hpos as [H1 H2].
  apply conj.
  destruct (predicate_dec P a); subst.
  apply Pred_is_neg_SO_exSO in H1; auto. 
  apply Pred_is_neg_SO_exSO_neq in H1; auto.
  firstorder.
Qed.

Lemma lem_bb3 : forall n P W Ip Ip',
Ip_extends_l W Ip Ip' (repeat P (S n)) <->
Ip_extends W Ip Ip' P.
Proof.
  unfold Ip_extends_l.
  intros n P W Ip Ip'. split; intros H.
  + constructor. intros w Hw. apply H. simpl. firstorder.
    auto. intros Q Hneq. 
    specialize (H Q). destruct H as [H1 H2]. apply H2.
    apply in_repeat_nocc. auto.
  + intros Q. split; intros H2. intros w H3. inversion H; auto.
    destruct (predicate_dec P Q). subst. apply H0. auto.
    rewrite <- H1; auto.  apply H. firstorder.
Qed.

Lemma alpha_upward_monotone_lP_repeat : forall alpha P n,
  alpha_upward_monotone_lP alpha (repeat P (S n)) <->
  alpha_upward_monotone_P alpha P.
Proof.
  intros alpha P n. unfold alpha_upward_monotone_lP.
  unfold alpha_upward_monotone_P.
  split ;intros H W Iv Ir Ip Ip' Hext SOt;
    apply H with (Ip := Ip); try assumption.
    apply lem_bb3. assumption.
    apply lem_bb3 in Hext. assumption.
Qed.

Lemma alpha_downward_monotone_lP_repeat : forall alpha P n,
  alpha_downward_monotone_lP alpha (repeat P (S n)) <->
  alpha_downward_monotone_P alpha P.
Proof.
  intros alpha P n. unfold alpha_upward_monotone_lP.
  unfold alpha_upward_monotone_P.
  split ;intros H W Iv Ir Ip Ip' Hext SOt;
    apply H with (Ip := Ip); try assumption.
    apply lem_bb3. assumption.
    apply lem_bb3 in Hext. assumption.
Qed.

Lemma alpha_upward_monotone_P_allSO_nocc : forall alpha P,
  ~ Pred_in_SO alpha P ->
  alpha_upward_monotone_P (allSO P alpha) P.
Proof.
  unfold alpha_upward_monotone_P. intros alpha P Hpocc W Iv Ir Ip Ip' Hext SOt.
  rewrite SOturnst_allSO in *. intros pa. specialize (SOt pa).
  apply P_not_occ_alt. assumption.
  apply P_not_occ_alt in SOt. 2: assumption.
  apply lem_bb2 with (P := P) (Ip := Ip); assumption.
Qed.

Lemma alpha_upward_monotone_P_exSO_nocc : forall alpha P,
  ~ Pred_in_SO alpha P ->  alpha_upward_monotone_P (exSO P alpha) P.
Proof.
  unfold alpha_upward_monotone_P. intros alpha P Hpocc W Iv Ir Ip Ip' Hext SOt.
  rewrite SOturnst_exSO in *. destruct SOt as [pa SOt]. exists pa.
  apply P_not_occ_alt. assumption.
  apply P_not_occ_alt in SOt. 2: assumption.
  apply lem_bb2 with (P := P) (Ip := Ip); assumption.
Qed.

Lemma alpha_downward_monotone_P_allSO_nocc : forall alpha P,
  ~ Pred_in_SO alpha P ->  alpha_downward_monotone_P (allSO P alpha) P.
Proof.
  unfold alpha_downward_monotone_P. intros alpha P Hpocc W Iv Ir Ip Ip' Hext SOt.
  rewrite SOturnst_allSO in *. intros pa. specialize (SOt pa).
  apply P_not_occ_alt. assumption.
  apply P_not_occ_alt in SOt. 2: assumption.
  apply lem_bb2_2 with (P := P) (Ip := Ip); assumption.
Qed.

Lemma alpha_downward_monotone_P_exSO_nocc : forall alpha P,
  ~ Pred_in_SO alpha P ->  alpha_downward_monotone_P (exSO P alpha) P.
Proof.
  unfold alpha_downward_monotone_P. intros alpha P Hpocc W Iv Ir Ip Ip' Hext SOt.
  rewrite SOturnst_exSO in *.
  destruct SOt as [pa SOt]. exists pa.
  apply P_not_occ_alt. assumption.
  apply P_not_occ_alt in SOt. 2: assumption.
  apply lem_bb2_2 with (P := P) (Ip := Ip); assumption.
Qed.

Lemma monotonicity_lP_SO_allSO : forall (alpha : SecOrder) p,
  (forall lP : list predicate,
          (lP_is_pos_SO alpha lP -> alpha_upward_monotone_lP alpha lP) /\
          (lP_is_neg_SO alpha lP -> alpha_downward_monotone_lP alpha lP)) ->
forall lP : list predicate,
(lP_is_pos_SO (allSO p alpha) lP -> alpha_upward_monotone_lP (allSO p alpha) lP) /\
(lP_is_neg_SO (allSO p alpha) lP -> alpha_downward_monotone_lP (allSO p alpha) lP).
Proof.
  intros alpha P H lP.
  apply conj; intros H2.
  + destruct (in_dec predicate_dec P lP). 
    destruct (in_dec predicate_dec P (preds_in alpha)).
    ++ apply up_allSO_lP. apply H. apply lPred_is_pos_SO_allSO2 in H2. auto.
       firstorder.
    ++ case_eq ((rem_pred lP P)).
       intros Hrem. apply rem_pred_nil in Hrem; try assumption.
       destruct Hrem as [m Hrem]. destruct m. rewrite Hrem in *. 
       simpl. apply alpha_upward_monotone_lP_nil.
       rewrite Hrem.
       apply alpha_upward_monotone_lP_repeat.
       apply alpha_upward_monotone_P_allSO_nocc. assumption.

       intros P' lP' HlP'.
       destruct (H (rem_pred lP P)) as [Hpos Hneg].
       apply mono_lem2. assumption. apply Hpos.
       apply mono_lem1. rewrite HlP'. discriminate. assumption.      
    ++ apply up_allSO_lP. apply H. apply lPred_is_pos_SO_allSO in H2.
        all : try assumption.

  + destruct (in_dec predicate_dec P lP). 
    destruct (in_dec predicate_dec P (preds_in alpha)).
    ++ apply down_allSO_lP. apply H. apply lPred_is_neg_SO_allSO2 in H2;
          assumption.
    ++ case_eq ((rem_pred lP P)).
       intros Hrem. apply rem_pred_nil in Hrem; try assumption.
       destruct Hrem as [m Hrem]. destruct m. rewrite Hrem in *. 
       simpl. apply alpha_downward_monotone_lP_nil.
       rewrite Hrem.
       apply alpha_downward_monotone_lP_repeat.
       apply alpha_downward_monotone_P_allSO_nocc. assumption.

       intros P' lP' HlP'.
       destruct (H (rem_pred lP P)) as [Hpos Hneg].
       apply down_mono_lem2. assumption. apply Hneg.
       apply down_mono_lem1. rewrite HlP'. discriminate. assumption.
    ++ apply down_allSO_lP. apply H. apply lPred_is_neg_SO_allSO in H2.
       all : try assumption.
Qed.

Lemma monotonicity_lP_SO_exSO : forall (alpha : SecOrder) p,
  (forall lP : list predicate,
          (lP_is_pos_SO alpha lP -> alpha_upward_monotone_lP alpha lP) /\
          (lP_is_neg_SO alpha lP -> alpha_downward_monotone_lP alpha lP)) ->
forall lP : list predicate,
(lP_is_pos_SO (exSO p alpha) lP -> alpha_upward_monotone_lP (exSO p alpha) lP) /\
(lP_is_neg_SO (exSO p alpha) lP -> alpha_downward_monotone_lP (exSO p alpha) lP).
Proof.
  intros alpha P H lP.
  apply conj; intros H2.
  + destruct (in_dec predicate_dec P lP). 
    destruct (in_dec predicate_dec P (preds_in alpha)).
    ++ apply up_exSO_lP. apply H. apply lPred_is_pos_SO_exSO2 in H2. auto.
       firstorder.
    ++ case_eq ((rem_pred lP P)).
       intros Hrem. apply rem_pred_nil in Hrem; try assumption.
       destruct Hrem as [m Hrem]. destruct m. rewrite Hrem in *. 
       simpl. apply alpha_upward_monotone_lP_nil.
       rewrite Hrem.
       apply alpha_upward_monotone_lP_repeat.
       apply alpha_upward_monotone_P_exSO_nocc. assumption.

       intros P' lP' HlP'.
       destruct (H (rem_pred lP P)) as [Hpos Hneg].
       apply mono_lem2_exSO. assumption. apply Hpos.
       apply mono_lem1_exSO. rewrite HlP'. discriminate. assumption.      
    ++ apply up_exSO_lP. apply H. apply lPred_is_pos_SO_exSO in H2.
        all : try assumption.

  + destruct (in_dec predicate_dec P lP). 
    destruct (in_dec predicate_dec P (preds_in alpha)).
    ++ apply down_exSO_lP. apply H. apply lPred_is_neg_SO_exSO2 in H2;
          assumption.
    ++ case_eq ((rem_pred lP P)).
       intros Hrem. apply rem_pred_nil in Hrem; try assumption.
       destruct Hrem as [m Hrem]. destruct m. rewrite Hrem in *. 
       simpl. apply alpha_downward_monotone_lP_nil.
       rewrite Hrem.
       apply alpha_downward_monotone_lP_repeat.
       apply alpha_downward_monotone_P_exSO_nocc. assumption.

       intros P' lP' HlP'.
       destruct (H (rem_pred lP P)) as [Hpos Hneg].
       apply down_mono_lem2_exSO. assumption. apply Hneg.
       apply down_mono_lem1_exSO. rewrite HlP'. discriminate. assumption.
    ++ apply down_exSO_lP. apply H. apply lPred_is_neg_SO_exSO in H2.
       all : try assumption.
Qed.

Lemma monotonicity_lP_SO : forall (alpha : SecOrder) (lP : list predicate),
    ((lP_is_pos_SO alpha lP -> alpha_upward_monotone_lP alpha lP) /\
    (lP_is_neg_SO alpha lP -> alpha_downward_monotone_lP alpha lP)).
Proof.
  induction alpha.
    apply monotonicity_lP_SO_predSO.
    apply monotonicity_lP_SO_relatSO.
    apply monotonicity_lP_SO_eqFO.
    apply monotonicity_lP_SO_allFO; assumption.
    apply monotonicity_lP_SO_exFO; assumption.
    apply monotonicity_lP_SO_negSO; assumption.
    apply monotonicity_lP_SO_conjSO ; assumption.
    apply monotonicity_lP_SO_disjSO ; assumption.
    apply monotonicity_lP_SO_implSO ; assumption.
    apply monotonicity_lP_SO_allSO ; assumption.
    apply monotonicity_lP_SO_exSO ; assumption.
Qed.