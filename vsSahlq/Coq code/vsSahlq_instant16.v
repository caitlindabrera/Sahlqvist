Require Export vsSahlq_instant15.

(* ---------------------------------------------------------- *)

Lemma  alt_Ip_rel : forall rel W Iv Ip1 Ip2 Ir,
  REL rel = true ->
  SOturnst W Iv Ip1 Ir rel =
  SOturnst W Iv Ip2 Ir rel.
Proof.
  induction rel; intros W Iv Ip1 Ip2 Ir Hrel; try discriminate.
    reflexivity. 

    simpl. rewrite IHrel1 with (Ip2 := Ip2).
    rewrite IHrel2 with (Ip2 := Ip2).
    reflexivity. apply REL_conjSO_r in Hrel. assumption.
    apply REL_conjSO_l in Hrel. assumption.
Qed.

Definition Ip_extends_l (W : Set) (Ip Ip' : predicate -> W -> Prop) 
                     (lP : list predicate) :=
forall P,
  (P_occurs_in_l lP P = true ->
    (forall (w : W), (Ip P w) -> (Ip' P w))) /\
  (P_occurs_in_l lP P = false ->
      (Ip P = Ip' P)).

Lemma Ip_extends_l_refl : forall lP W Ip,
  Ip_extends_l W Ip Ip lP.
Proof.
  unfold Ip_extends_l.
  intros lP W Ip P. apply conj.
    intros H w H2. assumption.

    reflexivity.
Qed.

Fixpoint ex_FOvar_x_ll x llx :=
  match llx with
  | nil => false
  | cons lx llx' => if is_in_FOvar x lx then true else ex_FOvar_x_ll x llx'
  end.

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

(* --------------------------------------------------------------- *)

Fixpoint lP_is_pos_SO alpha lP :=
  match lP with 
  | nil => False
  | cons P nil => (P_is_pos_SO alpha P)
  | cons P lP' => (P_is_pos_SO alpha P) /\ (lP_is_pos_SO alpha lP')
  end.

Fixpoint lP_is_neg_SO alpha lP :=
  match lP with 
  | nil => False
  | cons P nil => P_is_neg_SO alpha P
  | cons P lP' => (P_is_neg_SO alpha P) /\ (lP_is_neg_SO alpha lP')
  end.

Lemma P_is_neg_SO_predSO : forall P Q x,
  ~(P_is_neg_SO (predSO P x) Q).
Proof.
  intros [Pn] [Qm] [xn] H.
  unfold P_is_neg_SO in H.
  unfold P_occurs_in_alpha in H.
  simpl in *. destruct H as [H1 H2].
  case_eq (beq_nat Qm Pn); intros Hbeq; rewrite Hbeq in *.
    specialize (H1 eq_refl 1). simpl in *.
    unfold occ_in_alpha in H1. simpl in *.
    rewrite (beq_nat_true _ _ Hbeq) in *.
    discriminate (H1 eq_refl eq_refl).

    apply H2. reflexivity.
Qed.

Lemma lP_is_neg_SO_predSO : forall lP P x,
  ~ (lP_is_neg_SO (predSO P x) lP).
Proof.
  induction lP; intros [Pn] [xn].
    simpl. intros H. contradiction.

    intros H. simpl in *. destruct lP.
      contradiction (P_is_neg_SO_predSO _ _ _ H).

      destruct H as [H1 H2]. contradiction (IHlP _ _ H2).
Qed.

Lemma monotonicity_lP_SO'_predSO : forall p f,
forall lP : list predicate,
(lP_is_pos_SO (predSO p f) lP -> alpha_upward_monotone_lP (predSO p f) lP) /\
(lP_is_neg_SO (predSO p f) lP -> alpha_downward_monotone_lP (predSO p f) lP).
Proof.
  intros p f lP.
    destruct p as [Pn]; destruct f. simpl in *.
    apply conj. intros H2.
    destruct lP.

 contradiction.
    simpl in *. unfold alpha_upward_monotone_lP.
     unfold alpha_upward_monotone_lP . intros until 0.
      intros H3 H4. simpl in *. 
      unfold Ip_extends_l in H3. specialize (H3 (Pred Pn)).
      destruct H3 as [H3a H3b].
      case_eq (P_occurs_in_l (cons p lP) (Pred Pn));
        intros Hpocc.
        apply H3a; assumption.

        rewrite <- H3b; assumption.

    intros H2.
    contradiction (lP_is_neg_SO_predSO _ _ _ H2).
Qed.

Lemma monotonicity_lP_SO'_relatSO : forall f f0,
forall lP : list predicate,
(lP_is_pos_SO (relatSO f f0) lP -> alpha_upward_monotone_lP (relatSO f f0) lP) /\
(lP_is_neg_SO (relatSO f f0) lP -> alpha_downward_monotone_lP (relatSO f f0) lP).
Proof.
  unfold alpha_upward_monotone_lP.
  unfold alpha_downward_monotone_lP.
  intros. simpl. destruct f as [xn]. destruct f0 as [ym].
  apply conj; intros; assumption.
Qed.

Lemma monotonicity_lP_SO'_eqFO : forall f f0,
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

    simpl in *. destruct lP. apply P_is_pos_SO_allFO in H. assumption.
    destruct H as [H1 H2].
    apply P_is_pos_SO_allFO in H1.
    apply conj. assumption. apply IHlP  with (x := x) ; assumption.
Qed.

Lemma lP_is_neg_SO_allFO : forall lP alpha x,
  lP_is_neg_SO (allFO x alpha) lP ->
  lP_is_neg_SO alpha lP.
Proof.
  induction lP; intros alpha x H.
    simpl in *. contradiction.

    simpl in *. 
destruct lP. apply P_is_neg_SO_allFO in H. assumption.
destruct H as [H1 H2].
    apply P_is_neg_SO_allFO in H1.
    apply conj. assumption. apply IHlP  with (x := x) ; assumption.
Qed.

Lemma lP_is_pos_SO_exFO : forall lP alpha x,
  lP_is_pos_SO (exFO x alpha) lP ->
  lP_is_pos_SO alpha lP.
Proof.
  induction lP; intros alpha x H.
    simpl in *. contradiction.

    simpl in *. destruct lP. apply P_is_pos_SO_exFO in H. assumption.
    destruct H as [H1 H2].
    apply P_is_pos_SO_exFO in H1.
    apply conj. assumption. apply IHlP  with (x := x) ; assumption.
Qed.

Lemma lP_is_neg_SO_exFO : forall lP alpha x,
  lP_is_neg_SO (exFO x alpha) lP ->
  lP_is_neg_SO alpha lP.
Proof.
  induction lP; intros alpha x H.
    simpl in *. contradiction.

    simpl in *. 
destruct lP. apply P_is_neg_SO_exFO in H. assumption.
destruct H as [H1 H2].
    apply P_is_neg_SO_exFO in H1.
    apply conj. assumption. apply IHlP  with (x := x) ; assumption.
Qed.

Lemma monotonicity_lP_SO'_allFO : forall (alpha : SecOrder) f,

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

    apply down_lP_allFO. apply lP_is_neg_SO_allFO in H3.
    apply IHalpha; assumption.
Qed.

Lemma monotonicity_lP_SO'_exFO : forall (alpha : SecOrder) f,
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

Lemma lP_is_pos_SO_negSO : forall lP alpha,
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

Lemma lP_is_neg_SO_negSO : forall lP alpha,
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

Lemma monotonicity_lP_SO'_negSO : forall (alpha : SecOrder),
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
    apply lP_is_pos_SO_negSO in H3. apply alpha_upward_monotone_lP_negSO.
    apply IH2. assumption.

    apply lP_is_neg_SO_negSO in H3. apply alpha_downward_monotone_lP_negSO.
    apply IH1. assumption.
Qed.

Lemma P_occ_in_l_is_in_pred_equiv :  forall l (P : predicate),
  is_in_pred P l = P_occurs_in_l l P.
Proof.
  induction l; intros [Pn]. reflexivity.
  simpl. rewrite IHl. destruct a. reflexivity.
Qed.

Lemma P_occ_in_alpha_is_in_pred_equiv :  forall (alpha : SecOrder) (P : predicate),
  is_in_pred P (preds_in alpha) = P_occurs_in_alpha alpha P.
Proof.
  unfold P_occurs_in_alpha.
  intros. apply P_occ_in_l_is_in_pred_equiv.
Qed.

Lemma lP_is_pos_SO_is_in_pred_t : forall lP alpha,
  lP_is_pos_SO alpha lP -> is_in_pred_l lP (preds_in alpha) = true.
Proof.
  induction lP. simpl. reflexivity.
  intros alpha Hpos. simpl in *.
  destruct lP. simpl.
    rewrite P_occ_in_alpha_is_in_pred_equiv.
    rewrite  P_is_pos_occ. reflexivity.
    assumption.

    
    rewrite P_occ_in_alpha_is_in_pred_equiv.
    rewrite  P_is_pos_occ. apply IHlP. 
    all : apply Hpos.
Qed.

Lemma lP_is_neg_SO_is_in_pred_t : forall lP alpha,
  lP_is_neg_SO alpha lP -> is_in_pred_l lP (preds_in alpha) = true.
Proof.
  induction lP. simpl. reflexivity.
  intros alpha Hpos. simpl in *.
  destruct lP. simpl.
    rewrite P_occ_in_alpha_is_in_pred_equiv.
    rewrite  P_is_neg_occ. reflexivity.
    assumption.

    
    rewrite P_occ_in_alpha_is_in_pred_equiv.
    rewrite  P_is_neg_occ. apply IHlP. 
    all : apply Hpos.
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
   intros P. apply Hext. reflexivity.
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
   intros P. apply Hext. reflexivity.
assert (Ip' = Ip) as Heq.
   apply functional_extensionality. assumption. 
  rewrite Heq. assumption.
Qed. 

Lemma lP_is_pos_SO_conjSO_cap_pred_l : forall lP alpha1 alpha2,
  ~ (cap_pred lP (preds_in alpha1)) = nil ->
  lP_is_pos_SO (conjSO alpha1 alpha2) lP ->
  lP_is_pos_SO alpha1 (cap_pred lP (preds_in alpha1)).
Proof.
  induction lP; intros alpha1 alpha2 Hnil Hpos.
    simpl in *. contradiction.

    simpl in *. case_eq lP. intros HlP. rewrite HlP in *.
    case_eq (is_in_pred a (preds_in alpha1)); intros Hin2.
      simpl. rewrite P_occ_in_l_is_in_pred_equiv in Hin2.
      apply P_is_pos_SO_conjSO_l in Hpos; assumption.

      rewrite Hin2 in Hnil. simpl in *. contradiction (Hnil eq_refl).

    intros Q lQ HlP. rewrite <- HlP.    
    case_eq (is_in_pred a (preds_in alpha1)); intros Hin1;
      rewrite Hin1 in *. rewrite HlP in Hpos.
      rewrite <- HlP in Hpos. simpl.
      destruct Hpos as [Hp1 Hp2].
      case_eq (cap_pred lP (preds_in alpha1)).
        intros H.
        apply P_is_pos_SO_conjSO_l in Hp1.  assumption. 
        rewrite P_occ_in_l_is_in_pred_equiv in Hin1.
        apply Hin1.

        intros R lR Hcap. apply conj.
          apply P_is_pos_SO_conjSO_l in Hp1.  assumption. 
          rewrite P_occ_in_l_is_in_pred_equiv in Hin1.
          apply Hin1.

          rewrite <- Hcap. apply IHlP with (alpha2 := alpha2);
          try assumption.
          intros H. rewrite H in *. discriminate.

      rewrite HlP in Hpos. rewrite <- HlP in Hpos.
      destruct Hpos as [Hp1 Hp2].
      apply IHlP with (alpha2 := alpha2); assumption.
Qed.

Lemma lP_is_pos_SO_disjSO_cap_pred_l : forall lP alpha1 alpha2,
  ~ (cap_pred lP (preds_in alpha1)) = nil ->
  lP_is_pos_SO (disjSO alpha1 alpha2) lP ->
  lP_is_pos_SO alpha1 (cap_pred lP (preds_in alpha1)).
Proof.
  induction lP; intros alpha1 alpha2 Hnil Hpos.
    simpl in *. contradiction.

    simpl in *. case_eq lP. intros HlP. rewrite HlP in *.
    case_eq (is_in_pred a (preds_in alpha1)); intros Hin2.
      simpl. rewrite P_occ_in_l_is_in_pred_equiv in Hin2.
      apply P_is_pos_SO_conjSO_l in Hpos; assumption.

      rewrite Hin2 in Hnil. simpl in *. contradiction (Hnil eq_refl).

    intros Q lQ HlP. rewrite <- HlP.    
    case_eq (is_in_pred a (preds_in alpha1)); intros Hin1;
      rewrite Hin1 in *. rewrite HlP in Hpos.
      rewrite <- HlP in Hpos. simpl.
      destruct Hpos as [Hp1 Hp2].
      case_eq (cap_pred lP (preds_in alpha1)).
        intros H.
        apply P_is_pos_SO_conjSO_l in Hp1.  assumption. 
        rewrite P_occ_in_l_is_in_pred_equiv in Hin1.
        apply Hin1.

        intros R lR Hcap. apply conj.
          apply P_is_pos_SO_conjSO_l in Hp1.  assumption. 
          rewrite P_occ_in_l_is_in_pred_equiv in Hin1.
          apply Hin1.

          rewrite <- Hcap. apply IHlP with (alpha2 := alpha2);
          try assumption.
          intros H. rewrite H in *. discriminate.

      rewrite HlP in Hpos. rewrite <- HlP in Hpos.
      destruct Hpos as [Hp1 Hp2].
      apply IHlP with (alpha2 := alpha2); assumption.
Qed.

Lemma lP_is_pos_SO_implSO_cap_pred_l : forall lP alpha1 alpha2,
  ~ (cap_pred lP (preds_in alpha1)) = nil ->
  lP_is_pos_SO (implSO alpha1 alpha2) lP ->
  lP_is_neg_SO alpha1 (cap_pred lP (preds_in alpha1)).
Proof.
  induction lP; intros alpha1 alpha2 Hnil Hpos.
    simpl in *. contradiction.

    simpl in *. case_eq lP. intros HlP. rewrite HlP in *.
    case_eq (is_in_pred a (preds_in alpha1)); intros Hin2.
      simpl. rewrite P_occ_in_l_is_in_pred_equiv in Hin2.
      apply P_is_pos_SO_implSO_l in Hpos; try assumption.

      rewrite Hin2 in Hnil. simpl in *. contradiction (Hnil eq_refl).

    intros Q lQ HlP. rewrite <- HlP.    
    case_eq (is_in_pred a (preds_in alpha1)); intros Hin1;
      rewrite Hin1 in *. rewrite HlP in Hpos.
      rewrite <- HlP in Hpos. simpl.
      destruct Hpos as [Hp1 Hp2].
      case_eq (cap_pred lP (preds_in alpha1)).
        intros H.
        apply P_is_pos_SO_implSO_l in Hp1.  assumption. 
        rewrite P_occ_in_l_is_in_pred_equiv in Hin1.
        apply Hin1.

        intros R lR Hcap. apply conj.
          apply P_is_pos_SO_implSO_l in Hp1.  assumption. 
          rewrite P_occ_in_l_is_in_pred_equiv in Hin1.
          apply Hin1.

          rewrite <- Hcap. apply IHlP with (alpha2 := alpha2);
          try assumption.
          intros H. rewrite H in *. discriminate.

      rewrite HlP in Hpos. rewrite <- HlP in Hpos.
      destruct Hpos as [Hp1 Hp2].
      apply IHlP with (alpha2 := alpha2); assumption.
Qed. 

Lemma lP_is_neg_SO_implSO_cap_pred_l : forall lP alpha1 alpha2,
  ~ (cap_pred lP (preds_in alpha1)) = nil ->
  lP_is_neg_SO (implSO alpha1 alpha2) lP ->
  lP_is_pos_SO alpha1 (cap_pred lP (preds_in alpha1)).
Proof.
  induction lP; intros alpha1 alpha2 Hnil Hpos.
    simpl in *. contradiction.

    simpl in *. case_eq lP. intros HlP. rewrite HlP in *.
    case_eq (is_in_pred a (preds_in alpha1)); intros Hin2.
      simpl. rewrite P_occ_in_l_is_in_pred_equiv in Hin2.
      apply P_is_neg_SO_implSO_l in Hpos; try assumption.

      rewrite Hin2 in Hnil. simpl in *. contradiction (Hnil eq_refl).

    intros Q lQ HlP. rewrite <- HlP.    
    case_eq (is_in_pred a (preds_in alpha1)); intros Hin1;
      rewrite Hin1 in *. rewrite HlP in Hpos.
      rewrite <- HlP in Hpos. simpl.
      destruct Hpos as [Hp1 Hp2].
      case_eq (cap_pred lP (preds_in alpha1)).
        intros H.
        apply P_is_neg_SO_implSO_l in Hp1.  assumption. 
        rewrite P_occ_in_l_is_in_pred_equiv in Hin1.
        apply Hin1.

        intros R lR Hcap. apply conj.
          apply P_is_neg_SO_implSO_l in Hp1.  assumption. 
          rewrite P_occ_in_l_is_in_pred_equiv in Hin1.
          apply Hin1.

          rewrite <- Hcap. apply IHlP with (alpha2 := alpha2);
          try assumption.
          intros H. rewrite H in *. discriminate.

      rewrite HlP in Hpos. rewrite <- HlP in Hpos.
      destruct Hpos as [Hp1 Hp2].
      apply IHlP with (alpha2 := alpha2); assumption.
Qed. 


Lemma lP_is_neg_SO_conjSO_cap_pred_l : forall lP alpha1 alpha2,
  ~ (cap_pred lP (preds_in alpha1)) = nil ->
  lP_is_neg_SO (conjSO alpha1 alpha2) lP ->
  lP_is_neg_SO alpha1 (cap_pred lP (preds_in alpha1)).
Proof.
  induction lP; intros alpha1 alpha2 Hnil Hpos.
    simpl in *. contradiction.

    simpl in *. case_eq lP. intros HlP. rewrite HlP in *.
    case_eq (is_in_pred a (preds_in alpha1)); intros Hin2.
      simpl. rewrite P_occ_in_l_is_in_pred_equiv in Hin2.
      apply P_is_neg_SO_conjSO_l in Hpos; assumption.

      rewrite Hin2 in Hnil. simpl in *. contradiction (Hnil eq_refl).

    intros Q lQ HlP. rewrite <- HlP.    
    case_eq (is_in_pred a (preds_in alpha1)); intros Hin1;
      rewrite Hin1 in *. rewrite HlP in Hpos.
      rewrite <- HlP in Hpos. simpl.
      destruct Hpos as [Hp1 Hp2].
      case_eq (cap_pred lP (preds_in alpha1)).
        intros H.
        apply P_is_neg_SO_conjSO_l in Hp1.  assumption. 
        rewrite P_occ_in_l_is_in_pred_equiv in Hin1.
        apply Hin1.

        intros R lR Hcap. apply conj.
          apply P_is_neg_SO_conjSO_l in Hp1.  assumption. 
          rewrite P_occ_in_l_is_in_pred_equiv in Hin1.
          apply Hin1.

          rewrite <- Hcap. apply IHlP with (alpha2 := alpha2);
          try assumption.
          intros H. rewrite H in *. discriminate.

      rewrite HlP in Hpos. rewrite <- HlP in Hpos.
      destruct Hpos as [Hp1 Hp2].
      apply IHlP with (alpha2 := alpha2); assumption.
Qed.

Lemma lP_is_neg_SO_disjSO_cap_pred_l : forall lP alpha1 alpha2,
  ~ (cap_pred lP (preds_in alpha1)) = nil ->
  lP_is_neg_SO (disjSO alpha1 alpha2) lP ->
  lP_is_neg_SO alpha1 (cap_pred lP (preds_in alpha1)).
Proof.
  induction lP; intros alpha1 alpha2 Hnil Hpos.
    simpl in *. contradiction.

    simpl in *. case_eq lP. intros HlP. rewrite HlP in *.
    case_eq (is_in_pred a (preds_in alpha1)); intros Hin2.
      simpl. rewrite P_occ_in_l_is_in_pred_equiv in Hin2.
      apply P_is_neg_SO_conjSO_l in Hpos; assumption.

      rewrite Hin2 in Hnil. simpl in *. contradiction (Hnil eq_refl).

    intros Q lQ HlP. rewrite <- HlP.    
    case_eq (is_in_pred a (preds_in alpha1)); intros Hin1;
      rewrite Hin1 in *. rewrite HlP in Hpos.
      rewrite <- HlP in Hpos. simpl.
      destruct Hpos as [Hp1 Hp2].
      case_eq (cap_pred lP (preds_in alpha1)).
        intros H.
        apply P_is_neg_SO_conjSO_l in Hp1.  assumption. 
        rewrite P_occ_in_l_is_in_pred_equiv in Hin1.
        apply Hin1.

        intros R lR Hcap. apply conj.
          apply P_is_neg_SO_conjSO_l in Hp1.  assumption. 
          rewrite P_occ_in_l_is_in_pred_equiv in Hin1.
          apply Hin1.

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
    case_eq (is_in_pred a (preds_in alpha1)); intros Hin2.
      simpl. rewrite P_occ_in_l_is_in_pred_equiv in Hin2.
      apply P_is_neg_SO_conjSO_l in Hpos; assumption.

      rewrite Hin2 in Hnil. simpl in *. contradiction (Hnil eq_refl).

    intros Q lQ HlP. rewrite <- HlP.    
    case_eq (is_in_pred a (preds_in alpha1)); intros Hin1;
      rewrite Hin1 in *. rewrite HlP in Hpos.
      rewrite <- HlP in Hpos. simpl.
      destruct Hpos as [Hp1 Hp2].
      case_eq (cap_pred lP (preds_in alpha1)).
        intros H.
        apply P_is_neg_SO_conjSO_l in Hp1.  assumption. 
        rewrite P_occ_in_l_is_in_pred_equiv in Hin1.
        apply Hin1.

        intros R lR Hcap. apply conj.
          apply P_is_neg_SO_conjSO_l in Hp1.  assumption. 
          rewrite P_occ_in_l_is_in_pred_equiv in Hin1.
          apply Hin1.

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
    case_eq (is_in_pred a (preds_in alpha1)); intros Hin2.
      simpl. rewrite P_occ_in_l_is_in_pred_equiv in Hin2.
      apply P_is_neg_SO_implSO_l in Hpos; try assumption.

      rewrite Hin2 in Hnil. simpl in *. contradiction (Hnil eq_refl).

    intros Q lQ HlP. rewrite <- HlP.    
    case_eq (is_in_pred a (preds_in alpha1)); intros Hin1;
      rewrite Hin1 in *. rewrite HlP in Hpos.
      rewrite <- HlP in Hpos. simpl.
      destruct Hpos as [Hp1 Hp2].
      case_eq (cap_pred lP (preds_in alpha1)).
        intros H.
        apply P_is_neg_SO_implSO_l in Hp1.  assumption. 
        rewrite P_occ_in_l_is_in_pred_equiv in Hin1.
        apply Hin1.

        intros R lR Hcap. apply conj.
          apply P_is_neg_SO_implSO_l in Hp1.  assumption. 
          rewrite P_occ_in_l_is_in_pred_equiv in Hin1.
          apply Hin1.

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
    case_eq (is_in_pred a (preds_in alpha1)); intros Hin2.
      simpl. rewrite P_occ_in_l_is_in_pred_equiv in Hin2.
      apply P_is_neg_SO_conjSO_l in Hpos; assumption.

      rewrite Hin2 in Hnil. simpl in *. contradiction (Hnil eq_refl).

    intros Q lQ HlP. rewrite <- HlP.    
    case_eq (is_in_pred a (preds_in alpha1)); intros Hin1;
      rewrite Hin1 in *. rewrite HlP in Hpos.
      rewrite <- HlP in Hpos. simpl.
      destruct Hpos as [Hp1 Hp2].
      case_eq (cap_pred lP (preds_in alpha1)).
        intros H.
        apply P_is_neg_SO_conjSO_l in Hp1.  assumption. 
        rewrite P_occ_in_l_is_in_pred_equiv in Hin1.
        apply Hin1.

        intros R lR Hcap. apply conj.
          apply P_is_neg_SO_conjSO_l in Hp1.  assumption. 
          rewrite P_occ_in_l_is_in_pred_equiv in Hin1.
          apply Hin1.

          rewrite <- Hcap. apply IHlP with (alpha2 := alpha2);
          try assumption.
          intros H. rewrite H in *. discriminate.

      rewrite HlP in Hpos. rewrite <- HlP in Hpos.
      destruct Hpos as [Hp1 Hp2].
      apply IHlP with (alpha2 := alpha2); assumption.
Qed.


Lemma lP_is_pos_SO_conjSO_cap_pred_r : forall lP alpha1 alpha2,
  ~ (cap_pred lP (preds_in alpha2)) = nil ->
  lP_is_pos_SO (conjSO alpha1 alpha2) lP ->
  lP_is_pos_SO alpha2 (cap_pred lP (preds_in alpha2)).
Proof.
  induction lP; intros alpha1 alpha2 Hnil Hpos.
    simpl in *. contradiction.

    simpl in *. case_eq lP. intros HlP. rewrite HlP in *.
    case_eq (is_in_pred a (preds_in alpha2)); intros Hin2.
      simpl. rewrite P_occ_in_l_is_in_pred_equiv in Hin2.
      apply P_is_pos_SO_conjSO_r in Hpos; assumption.

      rewrite Hin2 in Hnil. simpl in *. contradiction (Hnil eq_refl).

    intros Q lQ HlP. rewrite <- HlP.    
    case_eq (is_in_pred a (preds_in alpha2)); intros Hin1;
      rewrite Hin1 in *. rewrite HlP in Hpos.
      rewrite <- HlP in Hpos. simpl.
      destruct Hpos as [Hp1 Hp2].
      case_eq (cap_pred lP (preds_in alpha2)).
        intros H.
        apply P_is_pos_SO_conjSO_r in Hp1.  assumption. 
        rewrite P_occ_in_l_is_in_pred_equiv in Hin1.
        apply Hin1.

        intros R lR Hcap. apply conj.
          apply P_is_pos_SO_conjSO_r in Hp1.  assumption. 
          rewrite P_occ_in_l_is_in_pred_equiv in Hin1.
          apply Hin1.

          rewrite <- Hcap. apply IHlP with (alpha1 := alpha1);
          try assumption.
          intros H. rewrite H in *. discriminate.

      rewrite HlP in Hpos. rewrite <- HlP in Hpos.
      destruct Hpos as [Hp1 Hp2].
      apply IHlP with (alpha1 := alpha1); assumption.
Qed.

Lemma lP_is_pos_SO_disjSO_cap_pred_r : forall lP alpha1 alpha2,
  ~ (cap_pred lP (preds_in alpha2)) = nil ->
  lP_is_pos_SO (disjSO alpha1 alpha2) lP ->
  lP_is_pos_SO alpha2 (cap_pred lP (preds_in alpha2)).
Proof.
  induction lP; intros alpha1 alpha2 Hnil Hpos.
    simpl in *. contradiction.

    simpl in *. case_eq lP. intros HlP. rewrite HlP in *.
    case_eq (is_in_pred a (preds_in alpha2)); intros Hin2.
      simpl. rewrite P_occ_in_l_is_in_pred_equiv in Hin2.
      apply P_is_pos_SO_conjSO_r in Hpos; assumption.

      rewrite Hin2 in Hnil. simpl in *. contradiction (Hnil eq_refl).

    intros Q lQ HlP. rewrite <- HlP.    
    case_eq (is_in_pred a (preds_in alpha2)); intros Hin1;
      rewrite Hin1 in *. rewrite HlP in Hpos.
      rewrite <- HlP in Hpos. simpl.
      destruct Hpos as [Hp1 Hp2].
      case_eq (cap_pred lP (preds_in alpha2)).
        intros H.
        apply P_is_pos_SO_conjSO_r in Hp1.  assumption. 
        rewrite P_occ_in_l_is_in_pred_equiv in Hin1.
        apply Hin1.

        intros R lR Hcap. apply conj.
          apply P_is_pos_SO_conjSO_r in Hp1.  assumption. 
          rewrite P_occ_in_l_is_in_pred_equiv in Hin1.
          apply Hin1.

          rewrite <- Hcap. apply IHlP with (alpha1 := alpha1);
          try assumption.
          intros H. rewrite H in *. discriminate.

      rewrite HlP in Hpos. rewrite <- HlP in Hpos.
      destruct Hpos as [Hp1 Hp2].
      apply IHlP with (alpha1 := alpha1); assumption.
Qed.

Lemma lP_is_pos_SO_implSO_cap_pred_r : forall lP alpha1 alpha2,
  ~ (cap_pred lP (preds_in alpha2)) = nil ->
  lP_is_pos_SO (implSO alpha1 alpha2) lP ->
  lP_is_pos_SO alpha2 (cap_pred lP (preds_in alpha2)).
Proof.
  induction lP; intros alpha1 alpha2 Hnil Hpos.
    simpl in *. contradiction.

    simpl in *. case_eq lP. intros HlP. rewrite HlP in *.
    case_eq (is_in_pred a (preds_in alpha2)); intros Hin2.
      simpl. rewrite P_occ_in_l_is_in_pred_equiv in Hin2.
      apply P_is_pos_SO_implSO_r in Hpos; assumption.

      rewrite Hin2 in Hnil. simpl in *. contradiction (Hnil eq_refl).

    intros Q lQ HlP. rewrite <- HlP.    
    case_eq (is_in_pred a (preds_in alpha2)); intros Hin1;
      rewrite Hin1 in *. rewrite HlP in Hpos.
      rewrite <- HlP in Hpos. simpl.
      destruct Hpos as [Hp1 Hp2].
      case_eq (cap_pred lP (preds_in alpha2)).
        intros H.
        apply P_is_pos_SO_implSO_r in Hp1.  assumption. 
        rewrite P_occ_in_l_is_in_pred_equiv in Hin1.
        apply Hin1.

        intros R lR Hcap. apply conj.
          apply P_is_pos_SO_implSO_r in Hp1.  assumption. 
          rewrite P_occ_in_l_is_in_pred_equiv in Hin1.
          apply Hin1.

          rewrite <- Hcap. apply IHlP with (alpha1 := alpha1);
          try assumption.
          intros H. rewrite H in *. discriminate.

      rewrite HlP in Hpos. rewrite <- HlP in Hpos.
      destruct Hpos as [Hp1 Hp2].
      apply IHlP with (alpha1 := alpha1); assumption.
Qed.


Lemma lP_is_neg_SO_conjSO_cap_pred_r : forall lP alpha1 alpha2,
  ~ (cap_pred lP (preds_in alpha2)) = nil ->
  lP_is_neg_SO (conjSO alpha1 alpha2) lP ->
  lP_is_neg_SO alpha2 (cap_pred lP (preds_in alpha2)).
Proof.
  induction lP; intros alpha1 alpha2 Hnil Hpos.
    simpl in *. contradiction.

    simpl in *. case_eq lP. intros HlP. rewrite HlP in *.
    case_eq (is_in_pred a (preds_in alpha2)); intros Hin2.
      simpl. rewrite P_occ_in_l_is_in_pred_equiv in Hin2.
      apply P_is_neg_SO_conjSO_r in Hpos; assumption.

      rewrite Hin2 in Hnil. simpl in *. contradiction (Hnil eq_refl).

    intros Q lQ HlP. rewrite <- HlP.    
    case_eq (is_in_pred a (preds_in alpha2)); intros Hin1;
      rewrite Hin1 in *. rewrite HlP in Hpos.
      rewrite <- HlP in Hpos. simpl.
      destruct Hpos as [Hp1 Hp2].
      case_eq (cap_pred lP (preds_in alpha2)).
        intros H.
        apply P_is_neg_SO_conjSO_r in Hp1.  assumption. 
        rewrite P_occ_in_l_is_in_pred_equiv in Hin1.
        apply Hin1.

        intros R lR Hcap. apply conj.
          apply P_is_neg_SO_conjSO_r in Hp1.  assumption. 
          rewrite P_occ_in_l_is_in_pred_equiv in Hin1.
          apply Hin1.

          rewrite <- Hcap. apply IHlP with (alpha1 := alpha1);
          try assumption.
          intros H. rewrite H in *. discriminate.

      rewrite HlP in Hpos. rewrite <- HlP in Hpos.
      destruct Hpos as [Hp1 Hp2].
      apply IHlP with (alpha1 := alpha1); assumption.
Qed.

Lemma lP_is_neg_SO_implSO_cap_pred_r : forall lP alpha1 alpha2,
  ~ (cap_pred lP (preds_in alpha2)) = nil ->
  lP_is_neg_SO (implSO alpha1 alpha2) lP ->
  lP_is_neg_SO alpha2 (cap_pred lP (preds_in alpha2)).
Proof.
  induction lP; intros alpha1 alpha2 Hnil Hpos.
    simpl in *. contradiction.

    simpl in *. case_eq lP. intros HlP. rewrite HlP in *.
    case_eq (is_in_pred a (preds_in alpha2)); intros Hin2.
      simpl. rewrite P_occ_in_l_is_in_pred_equiv in Hin2.
      apply P_is_neg_SO_implSO_r in Hpos; assumption.

      rewrite Hin2 in Hnil. simpl in *. contradiction (Hnil eq_refl).

    intros Q lQ HlP. rewrite <- HlP.    
    case_eq (is_in_pred a (preds_in alpha2)); intros Hin1;
      rewrite Hin1 in *. rewrite HlP in Hpos.
      rewrite <- HlP in Hpos. simpl.
      destruct Hpos as [Hp1 Hp2].
      case_eq (cap_pred lP (preds_in alpha2)).
        intros H.
        apply P_is_neg_SO_implSO_r in Hp1.  assumption. 
        rewrite P_occ_in_l_is_in_pred_equiv in Hin1.
        apply Hin1.

        intros R lR Hcap. apply conj.
          apply P_is_neg_SO_implSO_r in Hp1.  assumption. 
          rewrite P_occ_in_l_is_in_pred_equiv in Hin1.
          apply Hin1.

          rewrite <- Hcap. apply IHlP with (alpha1 := alpha1);
          try assumption.
          intros H. rewrite H in *. discriminate.

      rewrite HlP in Hpos. rewrite <- HlP in Hpos.
      destruct Hpos as [Hp1 Hp2].
      apply IHlP with (alpha1 := alpha1); assumption.
Qed.

Lemma lP_is_neg_SO_disjSO_cap_pred_r : forall lP alpha1 alpha2,
  ~ (cap_pred lP (preds_in alpha2)) = nil ->
  lP_is_neg_SO (disjSO alpha1 alpha2) lP ->
  lP_is_neg_SO alpha2 (cap_pred lP (preds_in alpha2)).
Proof.
  induction lP; intros alpha1 alpha2 Hnil Hpos.
    simpl in *. contradiction.

    simpl in *. case_eq lP. intros HlP. rewrite HlP in *.
    case_eq (is_in_pred a (preds_in alpha2)); intros Hin2.
      simpl. rewrite P_occ_in_l_is_in_pred_equiv in Hin2.
      apply P_is_neg_SO_conjSO_r in Hpos; assumption.

      rewrite Hin2 in Hnil. simpl in *. contradiction (Hnil eq_refl).

    intros Q lQ HlP. rewrite <- HlP.    
    case_eq (is_in_pred a (preds_in alpha2)); intros Hin1;
      rewrite Hin1 in *. rewrite HlP in Hpos.
      rewrite <- HlP in Hpos. simpl.
      destruct Hpos as [Hp1 Hp2].
      case_eq (cap_pred lP (preds_in alpha2)).
        intros H.
        apply P_is_neg_SO_conjSO_r in Hp1.  assumption. 
        rewrite P_occ_in_l_is_in_pred_equiv in Hin1.
        apply Hin1.

        intros R lR Hcap. apply conj.
          apply P_is_neg_SO_conjSO_r in Hp1.  assumption. 
          rewrite P_occ_in_l_is_in_pred_equiv in Hin1.
          apply Hin1.

          rewrite <- Hcap. apply IHlP with (alpha1 := alpha1);
          try assumption.
          intros H. rewrite H in *. discriminate.

      rewrite HlP in Hpos. rewrite <- HlP in Hpos.
      destruct Hpos as [Hp1 Hp2].
      apply IHlP with (alpha1 := alpha1); assumption.
Qed.


Lemma lem_b1 : forall lP alpha1 alpha2,
~ lP = nil ->
is_in_pred_l lP (preds_in (conjSO alpha1 alpha2)) = true ->
cap_pred lP (preds_in alpha1) = nil ->
~ cap_pred lP (preds_in alpha2) = nil.
Proof.
  induction lP; intros alpha1 alpha2 HlP Hin Hcap.
    simpl in *. contradiction (HlP eq_refl).

    simpl in *. case_eq (is_in_pred a (preds_in alpha1));
      intros Hin2; rewrite Hin2 in *.
      rewrite is_in_pred_app_l in Hin. 2 : assumption.
      discriminate.

      case_eq (is_in_pred a (preds_in alpha2)); intros Hin3.
        discriminate.
      rewrite P_occ_in_l_is_in_pred_equiv in *.
      assert (P_occurs_in_l (app (preds_in alpha1) (preds_in alpha2)) a = false)
        as Hf.
        apply P_occurs_in_l_app_f. apply conj; assumption.

      rewrite Hf in *. discriminate.
Qed.

Lemma lem_b1_l : forall lP alpha1 alpha2,
~ lP = nil ->
is_in_pred_l lP (preds_in (conjSO alpha1 alpha2)) = true ->
cap_pred lP (preds_in alpha2) = nil ->
~ cap_pred lP (preds_in alpha1) = nil.
Proof.
  induction lP; intros alpha1 alpha2 HlP Hin Hcap.
    simpl in *. contradiction (HlP eq_refl).

    simpl in *. case_eq (is_in_pred a (preds_in alpha2));
      intros Hin2; rewrite Hin2 in *.
      rewrite is_in_pred_app_r in Hin. 2 : assumption.
      discriminate.

      case_eq (is_in_pred a (preds_in alpha1)); intros Hin3.
        discriminate.
      rewrite P_occ_in_l_is_in_pred_equiv in *.
      assert (P_occurs_in_l (app (preds_in alpha1) (preds_in alpha2)) a = false)
        as Hf.
        apply P_occurs_in_l_app_f. apply conj; assumption.

      rewrite Hf in *. discriminate.
Qed.

Lemma is_in_pred_l_cap_pred : forall lP l1 l2,
is_in_pred_l lP (app l1 l2) = true ->
cap_pred lP l1 = nil ->
is_in_pred_l lP l2 = true.
Proof.
  induction lP; intros l1 l2 Hin Hcap.
    simpl in *. reflexivity.

    simpl in *. case_eq (is_in_pred a l1); intros Hin1;
      rewrite Hin1 in *. discriminate.
    case_eq (is_in_pred a (app l1 l2)); intros Hin3;
      rewrite Hin3 in *. 2 : discriminate.
    case_eq (is_in_pred a l2); intros Hin2.
      apply IHlP with (l1 := l1); assumption.

      rewrite P_occ_in_l_is_in_pred_equiv in *.
      apply P_occurs_in_l_app in Hin3. rewrite Hin1 in Hin3.
      rewrite Hin2 in Hin3. destruct Hin3; discriminate.
Qed.

Lemma is_in_pred_l_cap_pred_l : forall lP l1 l2,
is_in_pred_l lP (app l1 l2) = true ->
cap_pred lP l2 = nil ->
is_in_pred_l lP l1 = true.
Proof.
  induction lP; intros l1 l2 Hin Hcap.
    simpl in *. reflexivity.

    simpl in *. case_eq (is_in_pred a l2); intros Hin1;
      rewrite Hin1 in *. discriminate.
    case_eq (is_in_pred a (app l1 l2)); intros Hin3;
      rewrite Hin3 in *. 2 : discriminate.
    case_eq (is_in_pred a l1); intros Hin2.
      apply IHlP with (l2 := l2); assumption.

      rewrite P_occ_in_l_is_in_pred_equiv in *.
      apply P_occurs_in_l_app in Hin3. rewrite Hin1 in Hin3.
      rewrite Hin2 in Hin3. destruct Hin3; discriminate.
Qed.

Lemma is_in_pred_l_cap_pred_f : forall lP l1 l2,
~ lP = nil ->
is_in_pred_l lP (app l1 l2) = true ->
cap_pred lP l1 = nil ->
is_in_pred_l lP l1 = false.
Proof.
  induction lP; intros l1 l2 Hnil Hin Hcap.
    simpl in *. contradiction (Hnil eq_refl).

    simpl in *. case_eq (is_in_pred a l1); intros Hin1;
      rewrite Hin1 in *. discriminate.
    reflexivity.
Qed.

Lemma is_in_pred_l_cap_pred_f_l : forall lP l1 l2,
~ lP = nil ->
is_in_pred_l lP (app l1 l2) = true ->
cap_pred lP l2 = nil ->
is_in_pred_l lP l2 = false.
Proof.
  induction lP; intros l1 l2 Hnil Hin Hcap.
    simpl in *. contradiction (Hnil eq_refl).

    simpl in *. case_eq (is_in_pred a l2); intros Hin1;
      rewrite Hin1 in *. discriminate.
    reflexivity.
Qed.

Lemma lem_b7 : forall lP P W Ip1 Ip2,
  Ip_extends_l W Ip1 Ip2 (cons P lP) ->
  Ip_extends_l W (alt_Ip Ip1 (Ip2 P) P) Ip2 lP.
Proof.
  unfold Ip_extends_l.
  intros lP [Pn] W Ip1 Ip2 Hext [Qm].
  simpl in *.
  apply conj; intros Hpocc.
    intros w Halt. rewrite beq_nat_comm in Halt.
    case_eq (beq_nat Qm Pn); intros Hbeq; rewrite Hbeq in *.
      rewrite (beq_nat_true _ _ Hbeq) in *.
      assumption.

      apply Hext. rewrite Hbeq. assumption. assumption.

    case_eq (beq_nat Pn Qm); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq).
      reflexivity.

      apply Hext. rewrite beq_nat_comm. rewrite Hbeq.
      assumption.
Qed.

Lemma lem_b7_down : forall lP P W Ip1 Ip2,
  Ip_extends_l W Ip2 Ip1 (cons P lP) ->
  Ip_extends_l W Ip2 (alt_Ip Ip1 (Ip2 P) P) lP.
Proof.
  unfold Ip_extends_l.
  intros lP [Pn] W Ip1 Ip2 Hext [Qm].
  simpl in *.
  apply conj; intros Hpocc.
    intros w Halt.
  rewrite beq_nat_comm.
    case_eq (beq_nat Qm Pn); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq) in *.
      assumption.

      apply Hext. rewrite Hbeq. assumption. assumption.

    case_eq (beq_nat Pn Qm); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq).
      reflexivity.

      apply Hext. rewrite beq_nat_comm. rewrite Hbeq.
      assumption.
Qed.

Lemma lem_b8 : forall lP P W Ip1 Ip2,
  Ip_extends_l W Ip1 Ip2 (cons P lP) ->
  Ip_extends_l W Ip1 (alt_Ip Ip1 (Ip2 P) P) (cons P nil).
Proof.
  intros lP [Pn] W Ip1 Ip2 Hext [Qm].
  specialize (Hext (Pred Qm)). destruct Hext as [H1 H2].
  simpl in *. rewrite (beq_nat_comm Qm Pn) in *.
  apply conj; intros Hpoc.
    intros w H. simpl in *.
    case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *.
      rewrite (beq_nat_true _ _ Hbeq) in *.
      apply H1. reflexivity. all : try assumption.

    case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *.
      discriminate.
      reflexivity.
Qed.

Lemma lem_b8_down : forall lP P W Ip1 Ip2,
  Ip_extends_l W Ip2 Ip1 (cons P lP) ->
  Ip_extends_l W (alt_Ip Ip1 (Ip2 P) P) Ip1 (cons P nil).
Proof.
  intros lP [Pn] W Ip1 Ip2 Hext [Qm].
  specialize (Hext (Pred Qm)). destruct Hext as [H1 H2].
  simpl in *. rewrite (beq_nat_comm Qm Pn) in *.
  apply conj; intros Hpoc.
    intros w H. simpl in *.
    case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *.
      rewrite (beq_nat_true _ _ Hbeq) in *.
      apply H1. reflexivity. all : try assumption.

    case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *.
      discriminate.
      reflexivity.
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
  is_in_pred P (preds_in alpha) = false ->
  alpha_downward_monotone_lP alpha (cons P nil).
Proof.
  intros alpha P Hin.
  unfold alpha_upward_monotone_lP.
  intros W Iv Ir Ip1 Ip2 Hext SOt.
  unfold Ip_extends_l in Hext.
assert (Ip2 = alt_Ip Ip1 (Ip2 P) P) as H.
    destruct P as [Pn]. apply functional_extensionality.
    intros [Qm]. simpl.
    case_eq (beq_nat Pn Qm); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq). reflexivity.

     
      apply Hext. simpl. rewrite beq_nat_comm.
      rewrite Hbeq. reflexivity.

    rewrite H. apply P_not_occ_alt.
    rewrite P_occ_in_l_is_in_pred_equiv in Hin.
    all : assumption.
Qed.

Lemma lem_b10 : forall alpha P,
  is_in_pred P (preds_in alpha) = false ->
  alpha_upward_monotone_lP alpha (cons P nil).
Proof.
  intros alpha P Hin.
  unfold alpha_upward_monotone_lP.
  intros W Iv Ir Ip1 Ip2 Hext SOt.
  unfold Ip_extends_l in Hext.
assert (Ip2 = alt_Ip Ip1 (Ip2 P) P) as H.
    destruct P as [Pn]. apply functional_extensionality.
    intros [Qm]. simpl.
    case_eq (beq_nat Pn Qm); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq). reflexivity.

      symmetry.
      apply Hext. simpl. rewrite beq_nat_comm.
      rewrite Hbeq. reflexivity.

    rewrite H. apply P_not_occ_alt.
    rewrite P_occ_in_l_is_in_pred_equiv in Hin.
    all : assumption.
Qed.

Lemma lem_b3 : forall lP P alpha,
  is_in_pred P (preds_in alpha) = false ->
  alpha_upward_monotone_lP alpha lP ->  
  alpha_upward_monotone_lP alpha (cons P lP).
Proof.
  intros lP P alpha Hin Hup.
  apply lem_b6. apply lem_b10.
  all : assumption.
Qed.

Lemma lem_b3_down : forall lP P alpha,
  is_in_pred P (preds_in alpha) = false ->
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
    simpl in *. destruct Q as [Qm]. destruct P as [Pn].
    case_eq (beq_nat Qm Pn); intros Hbeq; rewrite Hbeq in *.
      specialize (Hext (Pred Pn)). simpl in *.
      rewrite <- beq_nat_refl in *. destruct Hext as [Hext1 Hext2].
      rewrite (beq_nat_true _ _ Hbeq) in *. apply Hext1; assumption.

      specialize (Hext (Pred Qm)). simpl in *. rewrite Hbeq in *.
      destruct Hext as [Hext1 Hext2]. specialize (Hext2 eq_refl). 
      rewrite Hext2 in *. assumption.

    intros Hpocc.
    simpl in *. destruct Q as [Qm]. destruct P as [Pn].
    case_eq (beq_nat Qm Pn); intros Hbeq; rewrite Hbeq in *.
      discriminate.

      specialize (Hext (Pred Qm)). simpl in *. rewrite Hbeq in *.
      destruct Hext as [Hext1 Hext2]. apply Hext2. reflexivity.

  assumption.
Qed.

Lemma lem_b4_down : forall lP  P alpha,
  alpha_downward_monotone_lP alpha (cons P lP) ->
  alpha_downward_monotone_lP alpha (cons P nil).
Proof.
  intros lP P alpha H.
  unfold alpha_downward_monotone_lP in *.
  intros W Iv Ir Ip Ip' Hext SOt.
  apply H with (Ip := Ip).
  unfold Ip_extends_l in *. intros Q. apply conj.
    intros H1 w H2.
    simpl in *. destruct Q as [Qm]. destruct P as [Pn].
    case_eq (beq_nat Qm Pn); intros Hbeq; rewrite Hbeq in *.
      specialize (Hext (Pred Pn)). simpl in *.
      rewrite <- beq_nat_refl in *. destruct Hext as [Hext1 Hext2].
      rewrite (beq_nat_true _ _ Hbeq) in *. apply Hext1; assumption.

      specialize (Hext (Pred Qm)). simpl in *. rewrite Hbeq in *.
      destruct Hext as [Hext1 Hext2]. specialize (Hext2 eq_refl). 
      rewrite Hext2 in *. assumption.

    intros Hpocc.
    simpl in *. destruct Q as [Qm]. destruct P as [Pn].
    case_eq (beq_nat Qm Pn); intros Hbeq; rewrite Hbeq in *.
      discriminate.

      specialize (Hext (Pred Qm)). simpl in *. rewrite Hbeq in *.
      destruct Hext as [Hext1 Hext2]. apply Hext2. reflexivity.

  assumption.
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
    intros H1 w H2.
    simpl in *. destruct Q as [Qm]. destruct P as [Pn].
    case_eq (beq_nat Qm Pn); intros Hbeq; rewrite Hbeq in *.
      rewrite (beq_nat_true _ _ Hbeq) in *.
      specialize (Hext (Pred Pn)). simpl in *.
      destruct Hext as [Hext1 Hext2]. 
      case_eq (P_occurs_in_l lP (Pred Pn)); intros Hpoc.
        apply Hext1; assumption.
        rewrite <- Hext2; assumption.

      specialize (Hext (Pred Qm)). simpl in *.
      destruct Hext as [Hext1 Hext2].
      case_eq (P_occurs_in_l lP (Pred Qm)); intros Hpoc.
        specialize (Hext1 Hpoc). apply Hext1. assumption. 
        rewrite Hext2 in *; assumption.

    intros Hpocc.
    simpl in *. destruct Q as [Qm]. destruct P as [Pn].
    case_eq (beq_nat Qm Pn); intros Hbeq; rewrite Hbeq in *.
      discriminate.

      specialize (Hext (Pred Qm)). simpl in *.
      destruct Hext as [Hext1 Hext2]. apply Hext2.
      assumption.
  assumption.
Qed.

Lemma lem_b4_2_down : forall lP  P alpha,
  alpha_downward_monotone_lP alpha (cons P lP) ->
  alpha_downward_monotone_lP alpha lP.
Proof.
  intros lP P alpha H.
  unfold alpha_downward_monotone_lP in *.
  intros W Iv Ir Ip Ip' Hext SOt.
  apply H with (Ip := Ip).
  unfold Ip_extends_l in *. intros Q. apply conj.
    intros H1 w H2.
    simpl in *. destruct Q as [Qm]. destruct P as [Pn].
    case_eq (beq_nat Qm Pn); intros Hbeq; rewrite Hbeq in *.
      rewrite (beq_nat_true _ _ Hbeq) in *.
      specialize (Hext (Pred Pn)). simpl in *.
      destruct Hext as [Hext1 Hext2]. 
      case_eq (P_occurs_in_l lP (Pred Pn)); intros Hpoc.
        apply Hext1; assumption.
        rewrite <- Hext2; assumption.

      specialize (Hext (Pred Qm)). simpl in *.
      destruct Hext as [Hext1 Hext2].
      case_eq (P_occurs_in_l lP (Pred Qm)); intros Hpoc.
        specialize (Hext1 Hpoc). apply Hext1. assumption. 
        rewrite Hext2 in *; assumption.

    intros Hpocc.
    simpl in *. destruct Q as [Qm]. destruct P as [Pn].
    case_eq (beq_nat Qm Pn); intros Hbeq; rewrite Hbeq in *.
      discriminate.

      specialize (Hext (Pred Qm)). simpl in *.
      destruct Hext as [Hext1 Hext2]. apply Hext2.
      assumption.
  assumption.
Qed.

Lemma up_mono_cap_pred : forall lP l alpha,
  is_in_pred_l (preds_in alpha) l = true ->
  alpha_upward_monotone_lP alpha (cap_pred lP l ) ->
  alpha_upward_monotone_lP alpha lP.
Proof.
  induction lP; intros l alpha Hin Hup.
    simpl in *. assumption.

    simpl in *. case_eq (is_in_pred a l);
      intros Hin2; rewrite Hin2 in *.

      pose proof (lem_b4_2 _ _ _ Hup) as H2.
      pose proof (lem_b4 _ _ _ Hup) as H3.
      apply lem_b6. assumption.
      apply IHlP with (l := l); assumption.

      apply lem_b3.
      case_eq (is_in_pred a (preds_in alpha));
        intros Hin3. rewrite is_in_pred_l_tft with (P := a) in Hin.
        discriminate. assumption. assumption. reflexivity.

        apply IHlP with (l := l); assumption.
Qed.

Lemma down_mono_cap_pred : forall lP l alpha,
  is_in_pred_l (preds_in alpha) l = true ->
  alpha_downward_monotone_lP alpha (cap_pred lP l ) ->
  alpha_downward_monotone_lP alpha lP.
Proof.
  induction lP; intros l alpha Hin Hup.
    simpl in *. assumption.

    simpl in *. case_eq (is_in_pred a l);
      intros Hin2; rewrite Hin2 in *.

      pose proof (lem_b4_2_down _ _ _ Hup) as H2.
      pose proof (lem_b4_down _ _ _ Hup) as H3.
      apply lem_b6_down. assumption.
      apply IHlP with (l := l); assumption.

      apply lem_b3_down.
      case_eq (is_in_pred a (preds_in alpha));
        intros Hin3. rewrite is_in_pred_l_tft with (P := a) in Hin.
        discriminate. assumption. assumption. reflexivity.

        apply IHlP with (l := l); assumption.
Qed.

Lemma lem_b9 : forall lP alpha,
  cap_pred lP (preds_in alpha) = nil ->
  alpha_upward_monotone_lP alpha lP.
Proof.
  induction lP; intros alpha Hcap.
    apply alpha_upward_monotone_lP_nil.

    simpl in *. case_eq (is_in_pred a (preds_in alpha));
      intros Hin; rewrite Hin in *. discriminate.
    apply lem_b6. apply lem_b10. assumption.

    apply IHlP. assumption.
Qed.


Lemma lem_b9_down : forall lP alpha,
  cap_pred lP (preds_in alpha) = nil ->
  alpha_downward_monotone_lP alpha lP.
Proof.
  induction lP; intros alpha Hcap.
    apply alpha_downward_monotone_lP_nil.

    simpl in *. case_eq (is_in_pred a (preds_in alpha));
      intros Hin; rewrite Hin in *. discriminate.
    apply lem_b6_down. apply lem_b10_down. assumption.

    apply IHlP. assumption.
Qed.

Lemma monotonicity_lP_SO'_conjSO : forall (alpha1 alpha2 : SecOrder),
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
      pose proof (lP_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc.  
      pose proof (lP_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc2.  
      pose proof (lP_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc3.  
      apply lem_b1 in Hpoc. simpl in Hpoc2.
      apply is_in_pred_l_cap_pred in Hpoc2.
      all : try assumption.

      pose proof (is_in_pred_l_cap_pred_f _ _ _ Hnil Hpoc3 Hc1).
      apply alpha_upward_monotone_lP_conjSO_fwd.
        apply lem_b9. assumption.
        apply up_mono_cap_pred with (l := (preds_in alpha2)).
          apply is_in_pred_l_refl.
        apply IH2. apply lP_is_pos_SO_conjSO_cap_pred_r in Hpos;
          assumption.

      intros Q2 lQ2 Hcap2.
    case_eq (cap_pred lP (preds_in alpha2)).
      intros Hc1.
      pose proof (lP_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc.  
      pose proof (lP_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc2.  
      pose proof (lP_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc3.  
      apply lem_b1_l in Hpoc. simpl in Hpoc2.
      apply is_in_pred_l_cap_pred_l in Hpoc2.
      all : try assumption.

      pose proof (is_in_pred_l_cap_pred_f_l _ _ _ Hnil Hpoc3 Hc1).
      apply alpha_upward_monotone_lP_conjSO_fwd.
        
        apply up_mono_cap_pred with (l := (preds_in alpha1)).
          apply is_in_pred_l_refl.
        apply IH1. apply lP_is_pos_SO_conjSO_cap_pred_l in Hpos;
          assumption.

        apply lem_b9. assumption.

      intros Q3 lQ3 HlQ3. 
      pose proof (lP_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc.  
      pose proof (lP_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc2.  
      pose proof (lP_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc3.
      assert (~ (cap_pred lP (preds_in alpha1) = nil)) as H1.
        rewrite Hcap2. discriminate.
      assert (~ (cap_pred lP (preds_in alpha2) = nil)) as H2.
        rewrite HlQ3. discriminate.

      apply alpha_upward_monotone_lP_conjSO_fwd.
        apply up_mono_cap_pred with (l := (preds_in alpha1)).
          apply is_in_pred_l_refl.
        apply IH1. apply lP_is_pos_SO_conjSO_cap_pred_l in Hpos;
        assumption.

        apply up_mono_cap_pred with (l := (preds_in alpha2)).
          apply is_in_pred_l_refl.
        apply IH2. apply lP_is_pos_SO_conjSO_cap_pred_r in Hpos;
        assumption.


     case_eq lP.
      intros HlP; rewrite HlP in *. apply alpha_downward_monotone_lP_nil.
    intros P' lP' HlP. rewrite <- HlP.
    assert (~ lP = nil) as Hnil.
      rewrite HlP. discriminate.

    case_eq (cap_pred lP (preds_in alpha1)).
      intros Hc1.
      pose proof (lP_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc.  
      pose proof (lP_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc2.  
      pose proof (lP_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc3.  
      apply lem_b1 in Hpoc. simpl in Hpoc2.
      apply is_in_pred_l_cap_pred in Hpoc2.
      all : try assumption.

      pose proof (is_in_pred_l_cap_pred_f _ _ _ Hnil Hpoc3 Hc1).
      apply alpha_downward_monotone_lP_conjSO_fwd.
        apply lem_b9_down. assumption.
        apply down_mono_cap_pred with (l := (preds_in alpha2)).
          apply is_in_pred_l_refl.
        apply IH2. apply lP_is_neg_SO_conjSO_cap_pred_r in Hpos;
          assumption.

      intros Q2 lQ2 Hcap2.
    case_eq (cap_pred lP (preds_in alpha2)).
      intros Hc1.
      pose proof (lP_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc.  
      pose proof (lP_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc2.  
      pose proof (lP_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc3.  
      apply lem_b1_l in Hpoc. simpl in Hpoc2.
      apply is_in_pred_l_cap_pred_l in Hpoc2.
      all : try assumption.

      pose proof (is_in_pred_l_cap_pred_f_l _ _ _ Hnil Hpoc3 Hc1).
      apply alpha_downward_monotone_lP_conjSO_fwd.
        
        apply down_mono_cap_pred with (l := (preds_in alpha1)).
          apply is_in_pred_l_refl.
        apply IH1. apply lP_is_down_SO_conjSO_cap_pred_l in Hpos;
          assumption.

        apply lem_b9_down. assumption.

      intros Q3 lQ3 HlQ3. 
      pose proof (lP_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc.  
      pose proof (lP_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc2.  
      pose proof (lP_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc3.
      assert (~ (cap_pred lP (preds_in alpha1) = nil)) as H1.
        rewrite Hcap2. discriminate.
      assert (~ (cap_pred lP (preds_in alpha2) = nil)) as H2.
        rewrite HlQ3. discriminate.

      apply alpha_downward_monotone_lP_conjSO_fwd.
        apply down_mono_cap_pred with (l := (preds_in alpha1)).
          apply is_in_pred_l_refl.
        apply IH1. apply lP_is_neg_SO_conjSO_cap_pred_l in Hpos;
        assumption.

        apply down_mono_cap_pred with (l := (preds_in alpha2)).
          apply is_in_pred_l_refl.
        apply IH2. apply lP_is_neg_SO_conjSO_cap_pred_r in Hpos;
        assumption.
Qed.


(* ----------- *)

Lemma monotonicity_lP_SO'_disjSO : forall (alpha1 alpha2 : SecOrder),
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
      pose proof (lP_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc.  
      pose proof (lP_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc2.  
      pose proof (lP_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc3.  
      apply lem_b1 in Hpoc. simpl in Hpoc2.
      apply is_in_pred_l_cap_pred in Hpoc2.
      all : try assumption.

      pose proof (is_in_pred_l_cap_pred_f _ _ _ Hnil Hpoc3 Hc1).
      apply alpha_upward_monotone_lP_disjSO_fwd.
        apply lem_b9. assumption.
        apply up_mono_cap_pred with (l := (preds_in alpha2)).
          apply is_in_pred_l_refl.
        apply IH2. apply lP_is_pos_SO_disjSO_cap_pred_r in Hpos;
          assumption.

      intros Q2 lQ2 Hcap2.
    case_eq (cap_pred lP (preds_in alpha2)).
      intros Hc1.
      pose proof (lP_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc.  
      pose proof (lP_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc2.  
      pose proof (lP_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc3.  
      apply lem_b1_l in Hpoc. simpl in Hpoc2.
      apply is_in_pred_l_cap_pred_l in Hpoc2.
      all : try assumption.

      pose proof (is_in_pred_l_cap_pred_f_l _ _ _ Hnil Hpoc3 Hc1).
      apply alpha_upward_monotone_lP_disjSO_fwd.
        
        apply up_mono_cap_pred with (l := (preds_in alpha1)).
          apply is_in_pred_l_refl.
        apply IH1. apply lP_is_pos_SO_disjSO_cap_pred_l in Hpos;
          assumption.

        apply lem_b9. assumption.

      intros Q3 lQ3 HlQ3. 
      pose proof (lP_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc.  
      pose proof (lP_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc2.  
      pose proof (lP_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc3.
      assert (~ (cap_pred lP (preds_in alpha1) = nil)) as H1.
        rewrite Hcap2. discriminate.
      assert (~ (cap_pred lP (preds_in alpha2) = nil)) as H2.
        rewrite HlQ3. discriminate.

      apply alpha_upward_monotone_lP_disjSO_fwd.
        apply up_mono_cap_pred with (l := (preds_in alpha1)).
          apply is_in_pred_l_refl.
        apply IH1. apply lP_is_pos_SO_disjSO_cap_pred_l in Hpos;
        assumption.

        apply up_mono_cap_pred with (l := (preds_in alpha2)).
          apply is_in_pred_l_refl.
        apply IH2. apply lP_is_pos_SO_disjSO_cap_pred_r in Hpos;
        assumption.


     case_eq lP.
      intros HlP; rewrite HlP in *. apply alpha_downward_monotone_lP_nil.
    intros P' lP' HlP. rewrite <- HlP.
    assert (~ lP = nil) as Hnil.
      rewrite HlP. discriminate.

    case_eq (cap_pred lP (preds_in alpha1)).
      intros Hc1.
      pose proof (lP_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc.  
      pose proof (lP_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc2.  
      pose proof (lP_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc3.  
      apply lem_b1 in Hpoc. simpl in Hpoc2.
      apply is_in_pred_l_cap_pred in Hpoc2.
      all : try assumption.

      pose proof (is_in_pred_l_cap_pred_f _ _ _ Hnil Hpoc3 Hc1).
      apply alpha_downward_monotone_lP_disjSO_fwd.
        apply lem_b9_down. assumption.
        apply down_mono_cap_pred with (l := (preds_in alpha2)).
          apply is_in_pred_l_refl.
        apply IH2. apply lP_is_neg_SO_disjSO_cap_pred_r in Hpos;
          assumption.

      intros Q2 lQ2 Hcap2.
    case_eq (cap_pred lP (preds_in alpha2)).
      intros Hc1.
      pose proof (lP_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc.  
      pose proof (lP_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc2.  
      pose proof (lP_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc3.  
      apply lem_b1_l in Hpoc. simpl in Hpoc2.
      apply is_in_pred_l_cap_pred_l in Hpoc2.
      all : try assumption.

      pose proof (is_in_pred_l_cap_pred_f_l _ _ _ Hnil Hpoc3 Hc1).
      apply alpha_downward_monotone_lP_disjSO_fwd.
        
        apply down_mono_cap_pred with (l := (preds_in alpha1)).
          apply is_in_pred_l_refl.
        apply IH1. apply lP_is_down_SO_disjSO_cap_pred_l in Hpos;
          assumption.

        apply lem_b9_down. assumption.

      intros Q3 lQ3 HlQ3. 
      pose proof (lP_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc.  
      pose proof (lP_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc2.  
      pose proof (lP_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc3.
      assert (~ (cap_pred lP (preds_in alpha1) = nil)) as H1.
        rewrite Hcap2. discriminate.
      assert (~ (cap_pred lP (preds_in alpha2) = nil)) as H2.
        rewrite HlQ3. discriminate.

      apply alpha_downward_monotone_lP_disjSO_fwd.
        apply down_mono_cap_pred with (l := (preds_in alpha1)).
          apply is_in_pred_l_refl.
        apply IH1. apply lP_is_neg_SO_disjSO_cap_pred_l in Hpos;
        assumption.

        apply down_mono_cap_pred with (l := (preds_in alpha2)).
          apply is_in_pred_l_refl.
        apply IH2. apply lP_is_neg_SO_disjSO_cap_pred_r in Hpos;
        assumption.
Qed.

Lemma monotonicity_lP_SO'_implSO : forall (alpha1 alpha2 : SecOrder),
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
      pose proof (lP_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc.  
      pose proof (lP_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc2.  
      pose proof (lP_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc3.  
      apply lem_b1 in Hpoc. simpl in Hpoc2.
      apply is_in_pred_l_cap_pred in Hpoc2.
      all : try assumption.

      pose proof (is_in_pred_l_cap_pred_f _ _ _ Hnil Hpoc3 Hc1).
      apply alpha_upward_monotone_lP_implSO_fwd.
        apply lem_b9_down. assumption.
        apply up_mono_cap_pred with (l := (preds_in alpha2)).
          apply is_in_pred_l_refl.
        apply IH2. apply lP_is_pos_SO_implSO_cap_pred_r in Hpos;
          assumption.

      intros Q2 lQ2 Hcap2.
    case_eq (cap_pred lP (preds_in alpha2)).
      intros Hc1.
      pose proof (lP_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc.  
      pose proof (lP_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc2.  
      pose proof (lP_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc3.  
      apply lem_b1_l in Hpoc. simpl in Hpoc2.
      apply is_in_pred_l_cap_pred_l in Hpoc2.
      all : try assumption.

      pose proof (is_in_pred_l_cap_pred_f_l _ _ _ Hnil Hpoc3 Hc1).
      apply alpha_upward_monotone_lP_implSO_fwd.
        
        apply down_mono_cap_pred with (l := (preds_in alpha1)).
          apply is_in_pred_l_refl.
        apply IH1. apply lP_is_pos_SO_implSO_cap_pred_l in Hpos;
          assumption.

        apply lem_b9. assumption.

      intros Q3 lQ3 HlQ3. 
      pose proof (lP_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc.  
      pose proof (lP_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc2.  
      pose proof (lP_is_pos_SO_is_in_pred_t _ _ Hpos) as Hpoc3.
      assert (~ (cap_pred lP (preds_in alpha1) = nil)) as H1.
        rewrite Hcap2. discriminate.
      assert (~ (cap_pred lP (preds_in alpha2) = nil)) as H2.
        rewrite HlQ3. discriminate.

      apply alpha_upward_monotone_lP_implSO_fwd.
        apply down_mono_cap_pred with (l := (preds_in alpha1)).
          apply is_in_pred_l_refl.
        apply IH1. apply lP_is_pos_SO_implSO_cap_pred_l in Hpos;
        assumption.

        apply up_mono_cap_pred with (l := (preds_in alpha2)).
          apply is_in_pred_l_refl.
        apply IH2. apply lP_is_pos_SO_implSO_cap_pred_r in Hpos;
        assumption.


     case_eq lP.
      intros HlP; rewrite HlP in *. apply alpha_downward_monotone_lP_nil.
    intros P' lP' HlP. rewrite <- HlP.
    assert (~ lP = nil) as Hnil.
      rewrite HlP. discriminate.

    case_eq (cap_pred lP (preds_in alpha1)).
      intros Hc1.
      pose proof (lP_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc.  
      pose proof (lP_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc2.  
      pose proof (lP_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc3.  
      apply lem_b1 in Hpoc. simpl in Hpoc2.
      apply is_in_pred_l_cap_pred in Hpoc2.
      all : try assumption.

      pose proof (is_in_pred_l_cap_pred_f _ _ _ Hnil Hpoc3 Hc1).
      apply alpha_downward_monotone_lP_implSO_fwd.
        apply lem_b9. assumption.
        apply down_mono_cap_pred with (l := (preds_in alpha2)).
          apply is_in_pred_l_refl.
        apply IH2. apply lP_is_neg_SO_implSO_cap_pred_r in Hpos;
          assumption.

      intros Q2 lQ2 Hcap2.
    case_eq (cap_pred lP (preds_in alpha2)).
      intros Hc1.
      pose proof (lP_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc.  
      pose proof (lP_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc2.  
      pose proof (lP_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc3.  
      apply lem_b1_l in Hpoc. simpl in Hpoc2.
      apply is_in_pred_l_cap_pred_l in Hpoc2.
      all : try assumption.

      pose proof (is_in_pred_l_cap_pred_f_l _ _ _ Hnil Hpoc3 Hc1).
      apply alpha_downward_monotone_lP_implSO_fwd.
        
        apply up_mono_cap_pred with (l := (preds_in alpha1)).
          apply is_in_pred_l_refl.
        apply IH1. apply lP_is_down_SO_implSO_cap_pred_l in Hpos;
          assumption.

        apply lem_b9_down. assumption.

      intros Q3 lQ3 HlQ3. 
      pose proof (lP_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc.  
      pose proof (lP_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc2.  
      pose proof (lP_is_neg_SO_is_in_pred_t _ _ Hpos) as Hpoc3.
      assert (~ (cap_pred lP (preds_in alpha1) = nil)) as H1.
        rewrite Hcap2. discriminate.
      assert (~ (cap_pred lP (preds_in alpha2) = nil)) as H2.
        rewrite HlQ3. discriminate.

      apply alpha_downward_monotone_lP_implSO_fwd.
        apply up_mono_cap_pred with (l := (preds_in alpha1)).
          apply is_in_pred_l_refl.
        apply IH1. apply lP_is_neg_SO_implSO_cap_pred_l in Hpos;
        assumption.

        apply down_mono_cap_pred with (l := (preds_in alpha2)).
          apply is_in_pred_l_refl.
        apply IH2. apply lP_is_neg_SO_implSO_cap_pred_r in Hpos;
        assumption.
Qed.

Lemma lem_bb : forall lP W Ip Ip' pa Q,
Ip_extends_l W Ip Ip' lP ->
Ip_extends_l W (alt_Ip Ip pa Q) (alt_Ip Ip' pa Q) lP.
Proof.
  unfold Ip_extends_l. intros lP W Ip Ip' pa [Pn] H [Qm].
  apply conj; intros Hpocc.
    intros w Halt. simpl in *. case_eq (beq_nat Pn Qm); intros Hbeq;
      rewrite Hbeq in *. assumption.
    apply H; assumption.

    simpl. destruct (H (Pred Qm)) as [H1 H2].
    rewrite H2. reflexivity. assumption.
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

Lemma P_is_pos_SO_allSO_neq : forall alpha P Q,
  ~ P = Q ->
  P_is_pos_SO (allSO P alpha) Q ->
  P_is_pos_SO alpha Q.
Proof.
  unfold P_is_pos_SO. intros alpha [Pn] [Qm] Hneq [H1 H2].
  apply conj; intros Hpocc.
    intros i Hocc Hat. simpl in *.
    unfold P_occurs_in_alpha in *. simpl in *.
    rewrite beq_nat_comm in *.
    rewrite neq_beq_nat in *; try assumption.
    specialize (H1 Hpocc (S i)). rewrite occ_in_alpha_allSO in H1.
    simpl in *. destruct i. simpl in *. rewrite occ_in_alpha_0 in Hocc.
      discriminate.
    simpl in H1. rewrite Hocc in *. specialize (H1 eq_refl Hat).
    assumption.

    unfold P_occurs_in_alpha in *. simpl in *.
    rewrite beq_nat_comm in *.
    rewrite neq_beq_nat in *; try assumption.
    apply H2. assumption.
Qed.

Lemma P_is_pos_SO_exSO_neq : forall alpha P Q,
  ~ P = Q ->
  P_is_pos_SO (exSO P alpha) Q ->
  P_is_pos_SO alpha Q.
Proof.
  unfold P_is_pos_SO. intros alpha [Pn] [Qm] Hneq [H1 H2].
  apply conj; intros Hpocc.
    intros i Hocc Hat. simpl in *.
    unfold P_occurs_in_alpha in *. simpl in *.
    rewrite beq_nat_comm in *.
    rewrite neq_beq_nat in *; try assumption.
    specialize (H1 Hpocc (S i)). rewrite occ_in_alpha_exSO in H1.
    simpl in *. destruct i. simpl in *. rewrite occ_in_alpha_0 in Hocc.
      discriminate.
    simpl in H1. rewrite Hocc in *. specialize (H1 eq_refl Hat).
    assumption.

    unfold P_occurs_in_alpha in *. simpl in *.
    rewrite beq_nat_comm in *.
    rewrite neq_beq_nat in *; try assumption.
    apply H2. assumption.
Qed.

Lemma P_is_neg_SO_allSO_neq : forall alpha P Q,
  ~ P = Q ->
  P_is_neg_SO (allSO P alpha) Q ->
  P_is_neg_SO alpha Q.
Proof.
  unfold P_is_pos_SO. intros alpha [Pn] [Qm] Hneq [H1 H2].
  apply conj; intros Hpocc.
    intros i Hocc Hat. simpl in *.
    unfold P_occurs_in_alpha in *. simpl in *.
    rewrite beq_nat_comm in *.
    rewrite neq_beq_nat in *; try assumption.
    specialize (H1 Hpocc (S i)). rewrite occ_in_alpha_allSO in H1.
    simpl in *. destruct i. simpl in *. rewrite occ_in_alpha_0 in Hocc.
      discriminate.
    simpl in H1. rewrite Hocc in *. specialize (H1 eq_refl Hat).
    assumption.

    unfold P_occurs_in_alpha in *. simpl in *.
    rewrite beq_nat_comm in *.
    rewrite neq_beq_nat in *; try assumption.
    apply H2. assumption.
Qed.

Lemma P_is_neg_SO_exSO_neq : forall alpha P Q,
  ~ P = Q ->
  P_is_neg_SO (exSO P alpha) Q ->
  P_is_neg_SO alpha Q.
Proof.
  unfold P_is_pos_SO. intros alpha [Pn] [Qm] Hneq [H1 H2].
  apply conj; intros Hpocc.
    intros i Hocc Hat. simpl in *.
    unfold P_occurs_in_alpha in *. simpl in *.
    rewrite beq_nat_comm in *.
    rewrite neq_beq_nat in *; try assumption.
    specialize (H1 Hpocc (S i)). rewrite occ_in_alpha_exSO in H1.
    simpl in *. destruct i. simpl in *. rewrite occ_in_alpha_0 in Hocc.
      discriminate.
    simpl in H1. rewrite Hocc in *. specialize (H1 eq_refl Hat).
    assumption.

    unfold P_occurs_in_alpha in *. simpl in *.
    rewrite beq_nat_comm in *.
    rewrite neq_beq_nat in *; try assumption.
    apply H2. assumption.
Qed.

Lemma lP_is_pos_SO_allSO : forall lP P alpha,
is_in_pred P lP = false ->
  lP_is_pos_SO (allSO P alpha) lP ->
  lP_is_pos_SO alpha lP.
Proof.
  induction lP; intros [Pn] alpha Hin Hpos.
    simpl in *. contradiction.

    simpl in *. destruct a as [Qm]. destruct lP.
      simpl in *. case_eq (beq_nat Pn Qm); intros Hbeq;
        rewrite Hbeq in *. discriminate.
      apply P_is_pos_SO_allSO_neq in Hpos. assumption.
      intros HH. inversion HH as [HHH]. rewrite HHH in *.
      rewrite <- beq_nat_refl in *. discriminate.

    destruct Hpos as [Hpos Hpos2].
    apply conj. case_eq (beq_nat Pn Qm); intros Hbeq;
        rewrite Hbeq in *. discriminate.
      apply P_is_pos_SO_allSO_neq in Hpos. assumption.
      intros HH. inversion HH as [HHH]. rewrite HHH in *.
      rewrite <- beq_nat_refl in *. discriminate.

      apply IHlP in Hpos2. assumption.
      case_eq (beq_nat Pn Qm); intros Hbeq;
        rewrite Hbeq in *. discriminate. assumption.
Qed.


Lemma lP_is_pos_SO_exSO : forall lP P alpha,
is_in_pred P lP = false ->
  lP_is_pos_SO (exSO P alpha) lP ->
  lP_is_pos_SO alpha lP.
Proof.
  induction lP; intros [Pn] alpha Hin Hpos.
    simpl in *. contradiction.

    simpl in *. destruct a as [Qm]. destruct lP.
      simpl in *. case_eq (beq_nat Pn Qm); intros Hbeq;
        rewrite Hbeq in *. discriminate.
      apply P_is_pos_SO_exSO_neq in Hpos. assumption.
      intros HH. inversion HH as [HHH]. rewrite HHH in *.
      rewrite <- beq_nat_refl in *. discriminate.

    destruct Hpos as [Hpos Hpos2].
    apply conj. case_eq (beq_nat Pn Qm); intros Hbeq;
        rewrite Hbeq in *. discriminate.
      apply P_is_pos_SO_exSO_neq in Hpos. assumption.
      intros HH. inversion HH as [HHH]. rewrite HHH in *.
      rewrite <- beq_nat_refl in *. discriminate.

      apply IHlP in Hpos2. assumption.
      case_eq (beq_nat Pn Qm); intros Hbeq;
        rewrite Hbeq in *. discriminate. assumption.
Qed.

Lemma lP_is_neg_SO_allSO : forall lP P alpha,
is_in_pred P lP = false ->
  lP_is_neg_SO (allSO P alpha) lP ->
  lP_is_neg_SO alpha lP.
Proof.
  induction lP; intros [Pn] alpha Hin Hpos.
    simpl in *. contradiction.

    simpl in *. destruct a as [Qm]. destruct lP.
      simpl in *. case_eq (beq_nat Pn Qm); intros Hbeq;
        rewrite Hbeq in *. discriminate.
      apply P_is_neg_SO_allSO_neq in Hpos. assumption.
      intros HH. inversion HH as [HHH]. rewrite HHH in *.
      rewrite <- beq_nat_refl in *. discriminate.

    destruct Hpos as [Hpos Hpos2].
    apply conj. case_eq (beq_nat Pn Qm); intros Hbeq;
        rewrite Hbeq in *. discriminate.
      apply P_is_neg_SO_allSO_neq in Hpos. assumption.
      intros HH. inversion HH as [HHH]. rewrite HHH in *.
      rewrite <- beq_nat_refl in *. discriminate.

      apply IHlP in Hpos2. assumption.
      case_eq (beq_nat Pn Qm); intros Hbeq;
        rewrite Hbeq in *. discriminate. assumption.
Qed.

Lemma lP_is_neg_SO_exSO : forall lP P alpha,
is_in_pred P lP = false ->
  lP_is_neg_SO (exSO P alpha) lP ->
  lP_is_neg_SO alpha lP.
Proof.
  induction lP; intros [Pn] alpha Hin Hpos.
    simpl in *. contradiction.

    simpl in *. destruct a as [Qm]. destruct lP.
      simpl in *. case_eq (beq_nat Pn Qm); intros Hbeq;
        rewrite Hbeq in *. discriminate.
      apply P_is_neg_SO_exSO_neq in Hpos. assumption.
      intros HH. inversion HH as [HHH]. rewrite HHH in *.
      rewrite <- beq_nat_refl in *. discriminate.

    destruct Hpos as [Hpos Hpos2].
    apply conj. case_eq (beq_nat Pn Qm); intros Hbeq;
        rewrite Hbeq in *. discriminate.
      apply P_is_neg_SO_exSO_neq in Hpos. assumption.
      intros HH. inversion HH as [HHH]. rewrite HHH in *.
      rewrite <- beq_nat_refl in *. discriminate.

      apply IHlP in Hpos2. assumption.
      case_eq (beq_nat Pn Qm); intros Hbeq;
        rewrite Hbeq in *. discriminate. assumption.
Qed.

Lemma mono_lem1 : forall lP P alpha,
  ~ (rem_pred lP P) = nil ->
  lP_is_pos_SO (allSO P alpha) lP ->
  lP_is_pos_SO alpha (rem_pred lP P).
Proof.
  induction lP; intros [Pn] alpha Hnil H.
    simpl in *. contradiction.

    simpl in *. destruct a as [Qm].
    destruct lP. case_eq (beq_nat Pn Qm); intros Hbeq;
      rewrite Hbeq in *. contradiction (Hnil eq_refl).
      simpl. apply P_is_pos_SO_allSO_neq in H.
      assumption. intros HH. inversion HH as [HH']. rewrite HH' in *.
        rewrite <- beq_nat_refl in Hbeq. discriminate.

      destruct H as [H1 H2].
      case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *.
        apply IHlP; try assumption.

        case_eq (rem_pred (p :: lP) (Pred Pn)).
          intros Hnil2. simpl. apply P_is_pos_SO_allSO_neq in H1.
          assumption. intros HH. inversion HH as [HH']. rewrite HH' in *.
              rewrite <- beq_nat_refl in Hbeq. discriminate.

          intros R l Hrem.
          remember (cons R l) as t. simpl.
          rewrite Heqt. rewrite <- Heqt.  rewrite <- Hrem.
          apply conj. 
            simpl. apply P_is_pos_SO_allSO_neq in H1.
            assumption. intros HH. inversion HH as [HH']. rewrite HH' in *.
              rewrite <- beq_nat_refl in Hbeq. discriminate.

            apply IHlP. rewrite Hrem. rewrite Heqt. discriminate.
            assumption.
Qed.

Lemma mono_lem1_exSO : forall lP P alpha,
  ~ (rem_pred lP P) = nil ->
  lP_is_pos_SO (exSO P alpha) lP ->
  lP_is_pos_SO alpha (rem_pred lP P).
Proof.
  induction lP; intros [Pn] alpha Hnil H.
    simpl in *. contradiction.

    simpl in *. destruct a as [Qm].
    destruct lP. case_eq (beq_nat Pn Qm); intros Hbeq;
      rewrite Hbeq in *. contradiction (Hnil eq_refl).
      simpl. apply P_is_pos_SO_exSO_neq in H.
      assumption. intros HH. inversion HH as [HH']. rewrite HH' in *.
        rewrite <- beq_nat_refl in Hbeq. discriminate.

      destruct H as [H1 H2].
      case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *.
        apply IHlP; try assumption.

        case_eq (rem_pred (p :: lP) (Pred Pn)).
          intros Hnil2. simpl. apply P_is_pos_SO_exSO_neq in H1.
          assumption. intros HH. inversion HH as [HH']. rewrite HH' in *.
              rewrite <- beq_nat_refl in Hbeq. discriminate.

          intros R l Hrem.
          remember (cons R l) as t. simpl.
          rewrite Heqt. rewrite <- Heqt.  rewrite <- Hrem.
          apply conj. 
            simpl. apply P_is_pos_SO_exSO_neq in H1.
            assumption. intros HH. inversion HH as [HH']. rewrite HH' in *.
              rewrite <- beq_nat_refl in Hbeq. discriminate.

            apply IHlP. rewrite Hrem. rewrite Heqt. discriminate.
            assumption.
Qed.

Lemma down_mono_lem1 : forall lP P alpha,
  ~ (rem_pred lP P) = nil ->
  lP_is_neg_SO (allSO P alpha) lP ->
  lP_is_neg_SO alpha (rem_pred lP P).
Proof.
  induction lP; intros [Pn] alpha Hnil H.
    simpl in *. contradiction.

    simpl in *. destruct a as [Qm].
    destruct lP. case_eq (beq_nat Pn Qm); intros Hbeq;
      rewrite Hbeq in *. contradiction (Hnil eq_refl).
      simpl. apply P_is_neg_SO_allSO_neq in H.
      assumption. intros HH. inversion HH as [HH']. rewrite HH' in *.
        rewrite <- beq_nat_refl in Hbeq. discriminate.

      destruct H as [H1 H2].
      case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *.
        apply IHlP; try assumption.

        case_eq (rem_pred (p :: lP) (Pred Pn)).
          intros Hnil2. simpl. apply P_is_neg_SO_allSO_neq in H1.
          assumption. intros HH. inversion HH as [HH']. rewrite HH' in *.
              rewrite <- beq_nat_refl in Hbeq. discriminate.

          intros R l Hrem.
          remember (cons R l) as t. simpl.
          rewrite Heqt. rewrite <- Heqt.  rewrite <- Hrem.
          apply conj. 
            simpl. apply P_is_neg_SO_allSO_neq in H1.
            assumption. intros HH. inversion HH as [HH']. rewrite HH' in *.
              rewrite <- beq_nat_refl in Hbeq. discriminate.

            apply IHlP. rewrite Hrem. rewrite Heqt. discriminate.
            assumption.
Qed.

Lemma down_mono_lem1_exSO : forall lP P alpha,
  ~ (rem_pred lP P) = nil ->
  lP_is_neg_SO (exSO P alpha) lP ->
  lP_is_neg_SO alpha (rem_pred lP P).
Proof.
  induction lP; intros [Pn] alpha Hnil H.
    simpl in *. contradiction.

    simpl in *. destruct a as [Qm].
    destruct lP. case_eq (beq_nat Pn Qm); intros Hbeq;
      rewrite Hbeq in *. contradiction (Hnil eq_refl).
      simpl. apply P_is_neg_SO_exSO_neq in H.
      assumption. intros HH. inversion HH as [HH']. rewrite HH' in *.
        rewrite <- beq_nat_refl in Hbeq. discriminate.

      destruct H as [H1 H2].
      case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *.
        apply IHlP; try assumption.

        case_eq (rem_pred (p :: lP) (Pred Pn)).
          intros Hnil2. simpl. apply P_is_neg_SO_exSO_neq in H1.
          assumption. intros HH. inversion HH as [HH']. rewrite HH' in *.
              rewrite <- beq_nat_refl in Hbeq. discriminate.

          intros R l Hrem.
          remember (cons R l) as t. simpl.
          rewrite Heqt. rewrite <- Heqt.  rewrite <- Hrem.
          apply conj. 
            simpl. apply P_is_neg_SO_exSO_neq in H1.
            assumption. intros HH. inversion HH as [HH']. rewrite HH' in *.
              rewrite <- beq_nat_refl in Hbeq. discriminate.

            apply IHlP. rewrite Hrem. rewrite Heqt. discriminate.
            assumption.
Qed.


Lemma P_occ_in_l_rem_pred : forall lP P Q,
  ~ P = Q ->
  P_occurs_in_l (rem_pred lP P) Q = 
  P_occurs_in_l lP Q.
Proof.
  induction lP; intros [Pn] [Qm] Hneq.
    simpl in *. reflexivity.

    simpl in *. specialize (IHlP _ _ Hneq).
    destruct a as [Rn]. case_eq (beq_nat Pn Rn); 
      intros Hbeq.  rewrite <- (beq_nat_true _ _ Hbeq).
      rewrite beq_nat_comm. rewrite neq_beq_nat; assumption.

      simpl. rewrite IHlP. reflexivity.
Qed.

Lemma lem_Ip_extends_rem_pred : forall lP P W Ip Ip' pa,
  Ip_extends_l W Ip Ip' lP ->
  Ip_extends_l W (alt_Ip Ip pa P) (alt_Ip Ip' pa P) (rem_pred lP P).
Proof.
  intros lP P W Ip Ip' pa H.
  unfold Ip_extends_l in *. intros [Qm].
  specialize (H (Pred Qm)). destruct H as [H1 H2].
  apply conj. intros Hpocc w Halt. destruct P as [Pn].
    simpl in *. case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *.
      assumption. apply H1.
      rewrite P_occ_in_l_rem_pred in Hpocc. assumption.
      intros HH. inversion HH as [HH']. rewrite HH' in *.
        rewrite <- beq_nat_refl in Hbeq. discriminate.

      assumption.

 destruct P as [Pn]. intros Hpocc.
    simpl in *. case_eq (beq_nat Pn Qm); intros Hbeq. reflexivity. apply H2.
    rewrite P_occ_in_l_rem_pred in Hpocc. assumption.
      intros HH. inversion HH as [HH']. rewrite HH' in *.
        rewrite <- beq_nat_refl in Hbeq. discriminate.
Qed.

Lemma mono_lem2 : forall lP P alpha,
  is_in_pred P lP = true ->
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
  is_in_pred P lP = true ->
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
  is_in_pred P lP = true ->
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
  is_in_pred P lP = true ->
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

Lemma P_is_pos_SO_allSO_occ : forall alpha P Q,
  P_occurs_in_alpha alpha P = true ->
  P_is_pos_SO (allSO P alpha) Q ->
  P_is_pos_SO alpha Q.
Proof.
  unfold P_is_pos_SO. intros alpha [Pn] [Qm] Hpocc [H1 H2].
  apply conj; intros Hpocc2.
    intros i Hocc Hat.
    unfold P_occurs_in_alpha in *. simpl in *.
    case_eq (beq_nat Qm Pn); intros Hbeq; rewrite Hbeq in *.
      unfold occ_in_alpha in *. simpl in*.
      specialize (H1 eq_refl (S i)). simpl in *.
      destruct i. simpl in *. discriminate.
      simpl in *. rewrite Hocc in *. apply (H1 eq_refl Hat).

      specialize (H1 Hpocc2 (S i)). destruct i. 
        rewrite occ_in_alpha_0 in Hocc. discriminate.
      simpl in *. rewrite occ_in_alpha_allSO in H1.
      simpl in *. rewrite Hocc in *. specialize (H1 eq_refl Hat).
      assumption.

    apply H2. unfold P_occurs_in_alpha in *. simpl in *.
    case_eq (beq_nat Qm Pn); intros Hbeq; rewrite Hbeq in *.
      rewrite (beq_nat_true _ _ Hbeq) in *. rewrite Hpocc2 in *.
      discriminate.
  
      assumption.
Qed.

Lemma P_is_pos_SO_exSO_occ : forall alpha P Q,
  P_occurs_in_alpha alpha P = true ->
  P_is_pos_SO (exSO P alpha) Q ->
  P_is_pos_SO alpha Q.
Proof.
  unfold P_is_pos_SO. intros alpha [Pn] [Qm] Hpocc [H1 H2].
  apply conj; intros Hpocc2.
    intros i Hocc Hat.
    unfold P_occurs_in_alpha in *. simpl in *.
    case_eq (beq_nat Qm Pn); intros Hbeq; rewrite Hbeq in *.
      unfold occ_in_alpha in *. simpl in*.
      specialize (H1 eq_refl (S i)). simpl in *.
      destruct i. simpl in *. discriminate.
      simpl in *. rewrite Hocc in *. apply (H1 eq_refl Hat).

      specialize (H1 Hpocc2 (S i)). destruct i. 
        rewrite occ_in_alpha_0 in Hocc. discriminate.
      simpl in *. rewrite occ_in_alpha_exSO in H1.
      simpl in *. rewrite Hocc in *. specialize (H1 eq_refl Hat).
      assumption.

    apply H2. unfold P_occurs_in_alpha in *. simpl in *.
    case_eq (beq_nat Qm Pn); intros Hbeq; rewrite Hbeq in *.
      rewrite (beq_nat_true _ _ Hbeq) in *. rewrite Hpocc2 in *.
      discriminate.
  
      assumption.
Qed.

Lemma P_is_neg_SO_allSO_occ : forall alpha P Q,
  P_occurs_in_alpha alpha P = true ->
  P_is_neg_SO (allSO P alpha) Q ->
  P_is_neg_SO alpha Q.
Proof.
  unfold P_is_pos_SO. intros alpha [Pn] [Qm] Hpocc [H1 H2].
  apply conj; intros Hpocc2.
    intros i Hocc Hat.
    unfold P_occurs_in_alpha in *. simpl in *.
    case_eq (beq_nat Qm Pn); intros Hbeq; rewrite Hbeq in *.
      unfold occ_in_alpha in *. simpl in*.
      specialize (H1 eq_refl (S i)). simpl in *.
      destruct i. simpl in *. discriminate.
      simpl in *. rewrite Hocc in *. apply (H1 eq_refl Hat).

      specialize (H1 Hpocc2 (S i)). destruct i. 
        rewrite occ_in_alpha_0 in Hocc. discriminate.
      simpl in *. rewrite occ_in_alpha_allSO in H1.
      simpl in *. rewrite Hocc in *. specialize (H1 eq_refl Hat).
      assumption.

    apply H2. unfold P_occurs_in_alpha in *. simpl in *.
    case_eq (beq_nat Qm Pn); intros Hbeq; rewrite Hbeq in *.
      rewrite (beq_nat_true _ _ Hbeq) in *. rewrite Hpocc2 in *.
      discriminate.
  
      assumption.
Qed.

Lemma P_is_neg_SO_exSO_occ : forall alpha P Q,
  P_occurs_in_alpha alpha P = true ->
  P_is_neg_SO (exSO P alpha) Q ->
  P_is_neg_SO alpha Q.
Proof.
  unfold P_is_pos_SO. intros alpha [Pn] [Qm] Hpocc [H1 H2].
  apply conj; intros Hpocc2.
    intros i Hocc Hat.
    unfold P_occurs_in_alpha in *. simpl in *.
    case_eq (beq_nat Qm Pn); intros Hbeq; rewrite Hbeq in *.
      unfold occ_in_alpha in *. simpl in*.
      specialize (H1 eq_refl (S i)). simpl in *.
      destruct i. simpl in *. discriminate.
      simpl in *. rewrite Hocc in *. apply (H1 eq_refl Hat).

      specialize (H1 Hpocc2 (S i)). destruct i. 
        rewrite occ_in_alpha_0 in Hocc. discriminate.
      simpl in *. rewrite occ_in_alpha_exSO in H1.
      simpl in *. rewrite Hocc in *. specialize (H1 eq_refl Hat).
      assumption.

    apply H2. unfold P_occurs_in_alpha in *. simpl in *.
    case_eq (beq_nat Qm Pn); intros Hbeq; rewrite Hbeq in *.
      rewrite (beq_nat_true _ _ Hbeq) in *. rewrite Hpocc2 in *.
      discriminate.
  
      assumption.
Qed.

Lemma lP_is_pos_SO_allSO2 : forall lP P alpha,
P_occurs_in_alpha alpha P = true ->
  lP_is_pos_SO (allSO P alpha) lP ->
  lP_is_pos_SO alpha lP.
Proof.
  induction lP; intros [Pn] alpha Hin Hpos.
    simpl in *. contradiction.

    simpl in *. destruct a as [Qm]. destruct lP.
      apply P_is_pos_SO_allSO_occ in Hpos; assumption.

      destruct Hpos as [H1 H2].
      apply conj.
        apply P_is_pos_SO_allSO_occ in H1; assumption.

        apply IHlP in H2; assumption.
Qed.

Lemma lP_is_pos_SO_exSO2 : forall lP P alpha,
P_occurs_in_alpha alpha P = true ->
  lP_is_pos_SO (exSO P alpha) lP ->
  lP_is_pos_SO alpha lP.
Proof.
  induction lP; intros [Pn] alpha Hin Hpos.
    simpl in *. contradiction.

    simpl in *. destruct a as [Qm]. destruct lP.
      apply P_is_pos_SO_exSO_occ in Hpos; assumption.

      destruct Hpos as [H1 H2].
      apply conj.
        apply P_is_pos_SO_exSO_occ in H1; assumption.

        apply IHlP in H2; assumption.
Qed.

Lemma lP_is_neg_SO_allSO2 : forall lP P alpha,
P_occurs_in_alpha alpha P = true ->
  lP_is_neg_SO (allSO P alpha) lP ->
  lP_is_neg_SO alpha lP.
Proof.
  induction lP; intros [Pn] alpha Hin Hpos.
    simpl in *. contradiction.

    simpl in *. destruct a as [Qm]. destruct lP.
      apply P_is_neg_SO_allSO_occ in Hpos; assumption.

      destruct Hpos as [H1 H2].
      apply conj.
        apply P_is_neg_SO_allSO_occ in H1; assumption.

        apply IHlP in H2; assumption.
Qed.

Lemma lP_is_neg_SO_exSO2 : forall lP P alpha,
P_occurs_in_alpha alpha P = true ->
  lP_is_neg_SO (exSO P alpha) lP ->
  lP_is_neg_SO alpha lP.
Proof.
  induction lP; intros [Pn] alpha Hin Hpos.
    simpl in *. contradiction.

    simpl in *. destruct a as [Qm]. destruct lP.
      apply P_is_neg_SO_exSO_occ in Hpos; assumption.

      destruct Hpos as [H1 H2].
      apply conj.
        apply P_is_neg_SO_exSO_occ in H1; assumption.

        apply IHlP in H2; assumption.
Qed.

Lemma rem_pred_nil : forall lP P,
  rem_pred lP P = nil ->
  exists n,
  lP = constant_l P n.
Proof.
  induction lP; intros [Pn] Hrem.
    exists 0. reflexivity.

    simpl in *. destruct a as [Qm]. case_eq (beq_nat Pn Qm);
      intros Hbeq; rewrite Hbeq in *. 
      destruct (IHlP (Pred Pn) Hrem) as [n IH].
      exists (S n). rewrite IH. simpl.
      rewrite (beq_nat_true _ _ Hbeq). reflexivity.

      discriminate.
Qed.

Lemma P_occ_in_l_constant_l_nocc  :forall n P Q,
  ~ P = Q ->
  P_occurs_in_l (constant_l P (S n)) Q = false.
Proof.
  induction n; intros [Pn] [Qm] Hneq.
    case_eq (beq_nat Qm Pn); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq) in *.
      contradiction (Hneq eq_refl).
    simpl. rewrite Hbeq. reflexivity.

    specialize (IHn (Pred Pn) (Pred Qm) Hneq).
    simpl in *.
    case_eq (beq_nat Qm Pn); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq) in *.
      contradiction (Hneq eq_refl).
    simpl. rewrite Hbeq in *. assumption.
Qed.

Lemma P_occ_in_l_constant_l_occ : forall n P Q,
  P_occurs_in_l (constant_l P (S n)) Q = true ->
  P = Q.
Proof.
  induction n; intros [Pn] [Qm] H.
    simpl in *. case_eq (beq_nat Qm Pn); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq).
      reflexivity.

      rewrite Hbeq in H. discriminate.

    simpl in *. case_eq (beq_nat Qm Pn); intros Hbeq;
      rewrite Hbeq in *. rewrite (beq_nat_true _ _ Hbeq).
      reflexivity.

      apply IHn. rewrite Hbeq. assumption.
Qed.

Lemma lem_bb3 : forall n P W Ip Ip',
Ip_extends_l W Ip Ip' (constant_l P (S n)) <->
Ip_extends W Ip Ip' P.
Proof.
  unfold Ip_extends. unfold Ip_extends_l.
  intros n [Pn] W Ip Ip'. split; intros H.
    apply conj. intros w H2. apply H.
      simpl. rewrite <- beq_nat_refl. reflexivity.
      assumption.

      intros [Qm] Hneq. destruct (H (Pred Qm)) as [H1 H2].
      apply H2. apply P_occ_in_l_constant_l_nocc.
        intros HH. inversion HH as [HH']. rewrite HH' in *.
        contradiction (Hneq eq_refl).

    intros [Qm]. destruct H as [H1 H2].
    apply conj. intros Hpocc w H3.
      apply P_occ_in_l_constant_l_occ in Hpocc. rewrite Hpocc in *.
      apply H1. assumption.

      intros Hpocc2. apply (H2 (Pred Qm)).
      intros H. rewrite H in *. simpl in Hpocc2.
        rewrite <- beq_nat_refl in *. discriminate.
Qed.

Lemma alpha_upward_monotone_lP_constant_l : forall alpha P n,
  alpha_upward_monotone_lP alpha (constant_l P (S n)) <->
  alpha_upward_monotone_P alpha P.
Proof.
  intros alpha P n. unfold alpha_upward_monotone_lP.
  unfold alpha_upward_monotone_P.
  split ;intros H W Iv Ir Ip Ip' Hext SOt;
    apply H with (Ip := Ip); try assumption.
    apply lem_bb3. assumption.
    apply lem_bb3 in Hext. assumption.
Qed.

Lemma alpha_downward_monotone_lP_constant_l : forall alpha P n,
  alpha_downward_monotone_lP alpha (constant_l P (S n)) <->
  alpha_downward_monotone_P alpha P.
Proof.
  intros alpha P n. unfold alpha_upward_monotone_lP.
  unfold alpha_upward_monotone_P.
  split ;intros H W Iv Ir Ip Ip' Hext SOt;
    apply H with (Ip := Ip); try assumption.
    apply lem_bb3. assumption.
    apply lem_bb3 in Hext. assumption.
Qed.

Lemma Ip_extends_same_Ip_list : forall l W Ip Ip' P,
  Ip_extends W Ip Ip' P ->
P_occurs_in_l l P = false ->
same_Ip_list W Ip Ip' l.
Proof.
  induction l; intros W Ip Ip' P Hext Hpocc.
    simpl in *. exact I.

    simpl in *. destruct P as [Pn]. destruct a as [Qm].
    case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *.
      discriminate.
    apply conj. unfold Ip_extends in Hext.
      destruct Hext as [H1 H2]. specialize (H2 (Pred Qm)).
      simpl in H2. apply H2.
      intros H; rewrite H in *. rewrite <- beq_nat_refl in *.
      discriminate.

      apply IHl with (P := (Pred Pn)); assumption.
Qed.

Lemma lem_bb2 : forall alpha P W Iv Ip Ip' Ir,
P_occurs_in_alpha alpha P = false ->
Ip_extends W Ip Ip' P ->
SOturnst W Iv Ip Ir alpha ->
SOturnst W Iv Ip' Ir alpha.
Proof.
  intros.
  apply same_preds_in with (Ip := Ip).
  apply Ip_extends_same_Ip_list with (P := P).
  all : assumption.
Qed.

Lemma same_Ip_list_comm: forall l W Ip Ip',
  same_Ip_list W Ip Ip' l <->
  same_Ip_list W Ip' Ip l.
Proof.
  induction l; intros W Iv Ip'.
    apply iff_refl.

    simpl. split ;intros H; (apply conj;
      [symmetry; apply H | apply IHl; apply H]).
Qed.

Lemma lem_bb2_2 : forall alpha P W Iv Ip Ip' Ir,
P_occurs_in_alpha alpha P = false ->
Ip_extends W Ip' Ip P ->
SOturnst W Iv Ip Ir alpha ->
SOturnst W Iv Ip' Ir alpha.
Proof.
  intros.
  apply same_preds_in with (Ip := Ip).

  rewrite same_Ip_list_comm.
  apply Ip_extends_same_Ip_list with (P := P).
  all : try assumption.
Qed.

Lemma alpha_upward_monotone_P_allSO_nocc : forall alpha P,
  P_occurs_in_alpha alpha P = false ->
  alpha_upward_monotone_P (allSO P alpha) P.
Proof.
  unfold alpha_upward_monotone_P. intros alpha P Hpocc W Iv Ir Ip Ip' Hext SOt.
  rewrite SOturnst_allSO in *. intros pa. specialize (SOt pa).
  apply P_not_occ_alt. assumption.
  apply P_not_occ_alt in SOt. 2: assumption.
  apply lem_bb2 with (P := P) (Ip := Ip); assumption.
Qed.

Lemma alpha_upward_monotone_P_exSO_nocc : forall alpha P,
  P_occurs_in_alpha alpha P = false ->
  alpha_upward_monotone_P (exSO P alpha) P.
Proof.
  unfold alpha_upward_monotone_P. intros alpha P Hpocc W Iv Ir Ip Ip' Hext SOt.
  rewrite SOturnst_exSO in *. destruct SOt as [pa SOt]. exists pa.
  apply P_not_occ_alt. assumption.
  apply P_not_occ_alt in SOt. 2: assumption.
  apply lem_bb2 with (P := P) (Ip := Ip); assumption.
Qed.

Lemma alpha_downward_monotone_P_allSO_nocc : forall alpha P,
  P_occurs_in_alpha alpha P = false ->
  alpha_downward_monotone_P (allSO P alpha) P.
Proof.
  unfold alpha_downward_monotone_P. intros alpha P Hpocc W Iv Ir Ip Ip' Hext SOt.
  rewrite SOturnst_allSO in *. intros pa. specialize (SOt pa).
  apply P_not_occ_alt. assumption.
  apply P_not_occ_alt in SOt. 2: assumption.
  apply lem_bb2_2 with (P := P) (Ip := Ip); assumption.
Qed.

Lemma alpha_downward_monotone_P_exSO_nocc : forall alpha P,
  P_occurs_in_alpha alpha P = false ->
  alpha_downward_monotone_P (exSO P alpha) P.
Proof.
  unfold alpha_downward_monotone_P. intros alpha P Hpocc W Iv Ir Ip Ip' Hext SOt.
  rewrite SOturnst_exSO in *.
  destruct SOt as [pa SOt]. exists pa.
  apply P_not_occ_alt. assumption.
  apply P_not_occ_alt in SOt. 2: assumption.
  apply lem_bb2_2 with (P := P) (Ip := Ip); assumption.
Qed.

Lemma monotonicity_lP_SO'_allSO : forall (alpha : SecOrder) p,
  (forall lP : list predicate,
          (lP_is_pos_SO alpha lP -> alpha_upward_monotone_lP alpha lP) /\
          (lP_is_neg_SO alpha lP -> alpha_downward_monotone_lP alpha lP)) ->
forall lP : list predicate,
(lP_is_pos_SO (allSO p alpha) lP -> alpha_upward_monotone_lP (allSO p alpha) lP) /\
(lP_is_neg_SO (allSO p alpha) lP -> alpha_downward_monotone_lP (allSO p alpha) lP).
Proof.
  intros alpha P H lP.
  apply conj; intros H2.
    case_eq (is_in_pred P lP); intros Hin.
      case_eq (P_occurs_in_alpha alpha P); intros Hpocc.
        apply up_allSO_lP. apply H. apply lP_is_pos_SO_allSO2 in H2;
          assumption.

      case_eq ((rem_pred lP P)).
        intros Hrem. apply rem_pred_nil in Hrem; try assumption.
        destruct Hrem as [n Hrem]. destruct n. rewrite Hrem in *. 
        simpl. apply alpha_upward_monotone_lP_nil.
        rewrite Hrem.
        apply alpha_upward_monotone_lP_constant_l.
        apply alpha_upward_monotone_P_allSO_nocc. assumption.

      intros P' lP' HlP'.
        destruct (H (rem_pred lP P)) as [Hpos Hneg].
        apply mono_lem2. assumption. apply Hpos.
        apply mono_lem1. rewrite HlP'. discriminate. assumption.

        apply up_allSO_lP. apply H. apply lP_is_pos_SO_allSO in H2.
        all : try assumption.

    case_eq (is_in_pred P lP); intros Hin.
      case_eq (P_occurs_in_alpha alpha P); intros Hpocc.
        apply down_allSO_lP. apply H. apply lP_is_neg_SO_allSO2 in H2;
          assumption.

      case_eq ((rem_pred lP P)).
        intros Hrem. apply rem_pred_nil in Hrem; try assumption.
        destruct Hrem as [n Hrem]. destruct n. rewrite Hrem in *. 
        simpl. apply alpha_downward_monotone_lP_nil.
        rewrite Hrem.
        apply alpha_downward_monotone_lP_constant_l.
        apply alpha_downward_monotone_P_allSO_nocc. assumption.

      intros P' lP' HlP'.
        destruct (H (rem_pred lP P)) as [Hpos Hneg].
        apply down_mono_lem2. assumption. apply Hneg.
        apply down_mono_lem1. rewrite HlP'. discriminate. assumption.

        apply down_allSO_lP. apply H. apply lP_is_neg_SO_allSO in H2.
        all : try assumption.

Qed.

Lemma monotonicity_lP_SO'_exSO : forall (alpha : SecOrder) p,
  (forall lP : list predicate,
          (lP_is_pos_SO alpha lP -> alpha_upward_monotone_lP alpha lP) /\
          (lP_is_neg_SO alpha lP -> alpha_downward_monotone_lP alpha lP)) ->
forall lP : list predicate,
(lP_is_pos_SO (exSO p alpha) lP -> alpha_upward_monotone_lP (exSO p alpha) lP) /\
(lP_is_neg_SO (exSO p alpha) lP -> alpha_downward_monotone_lP (exSO p alpha) lP).
Proof.
  intros alpha P H lP.
  apply conj; intros H2.
    case_eq (is_in_pred P lP); intros Hin.
      case_eq (P_occurs_in_alpha alpha P); intros Hpocc.
        apply up_exSO_lP. apply H. apply lP_is_pos_SO_exSO2 in H2;
          assumption.

      case_eq ((rem_pred lP P)).
        intros Hrem. apply rem_pred_nil in Hrem; try assumption.
        destruct Hrem as [n Hrem]. destruct n. rewrite Hrem in *. 
        simpl. apply alpha_upward_monotone_lP_nil.
        rewrite Hrem.
        apply alpha_upward_monotone_lP_constant_l.
        apply alpha_upward_monotone_P_exSO_nocc. assumption.

      intros P' lP' HlP'.
        destruct (H (rem_pred lP P)) as [Hpos Hneg].
        apply mono_lem2_exSO. assumption. apply Hpos.
        apply mono_lem1_exSO. rewrite HlP'. discriminate. assumption.

        apply up_exSO_lP. apply H. apply lP_is_pos_SO_exSO in H2.
        all : try assumption.

    case_eq (is_in_pred P lP); intros Hin.
      case_eq (P_occurs_in_alpha alpha P); intros Hpocc.
        apply down_exSO_lP. apply H. apply lP_is_neg_SO_exSO2 in H2;
          assumption.

      case_eq ((rem_pred lP P)).
        intros Hrem. apply rem_pred_nil in Hrem; try assumption.
        destruct Hrem as [n Hrem]. destruct n. rewrite Hrem in *. 
        simpl. apply alpha_downward_monotone_lP_nil.
        rewrite Hrem.
        apply alpha_downward_monotone_lP_constant_l.
        apply alpha_downward_monotone_P_exSO_nocc. assumption.

      intros P' lP' HlP'.
        destruct (H (rem_pred lP P)) as [Hpos Hneg].
        apply down_mono_lem2_exSO. assumption. apply Hneg.
        apply down_mono_lem1_exSO. rewrite HlP'. discriminate. assumption.

        apply down_exSO_lP. apply H. apply lP_is_neg_SO_exSO in H2.
        all : try assumption.

Qed.

Lemma monotonicity_lP_SO' : forall (alpha : SecOrder) (lP : list predicate),
    ((lP_is_pos_SO alpha lP -> alpha_upward_monotone_lP alpha lP) /\
    (lP_is_neg_SO alpha lP -> alpha_downward_monotone_lP alpha lP)).
Proof.
  induction alpha.
    apply monotonicity_lP_SO'_predSO.
    apply monotonicity_lP_SO'_relatSO.
    apply monotonicity_lP_SO'_eqFO.
    apply monotonicity_lP_SO'_allFO; assumption.
    apply monotonicity_lP_SO'_exFO; assumption.
    apply monotonicity_lP_SO'_negSO; assumption.
    apply monotonicity_lP_SO'_conjSO ; assumption.
    apply monotonicity_lP_SO'_disjSO ; assumption.
    apply monotonicity_lP_SO'_implSO ; assumption.
    apply monotonicity_lP_SO'_allSO ; assumption.
    apply monotonicity_lP_SO'_exSO ; assumption.
Qed.
