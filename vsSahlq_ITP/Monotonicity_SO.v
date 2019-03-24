Require Import SO_semantics Pred_in_SO.
Require Import Pred_is_pos_neg_SO nlist_sem_eg.
Require Import Correctness_ST.

Inductive Ip_extends (W : Set) (Ip Ip' : predicate -> W -> Prop) 
          (P : predicate) : Type :=
  | Ip_ext : (forall (w : W), (Ip P w) -> (Ip' P w)) ->
             (forall (Q : predicate), P <> Q -> (Ip Q = Ip' Q)) ->
             Ip_extends W Ip Ip' P.

Definition alpha_upward_monotone_P (alpha : SecOrder) (P : predicate) :=
    forall (W : Set) (Iv : FOvariable -> W) (R : W -> W -> Prop)
           (Ip Ip' : predicate -> W -> Prop),
   Ip_extends W Ip Ip' P
      -> (SOturnst W Iv Ip R alpha) ->
                          (SOturnst W Iv Ip' R alpha).

Definition alpha_downward_monotone_P (alpha : SecOrder) (P : predicate) :=
    forall (W : Set) (Iv : FOvariable -> W) (R : W -> W -> Prop)
           (Ip Ip' : predicate -> W -> Prop),
   Ip_extends W Ip' Ip P
      -> (SOturnst W Iv Ip R alpha) ->
                          (SOturnst W Iv Ip' R alpha).

(* ---------------------------------------------------------------------------- *)

Lemma Ip_ext_alt_Ip : forall (W : Set) (Ip Ip' : predicate -> W -> Prop)
                             (pa : W -> Prop) (P Q : predicate),
  Ip_extends W Ip Ip' P ->
  Ip_extends W (alt_Ip Ip pa Q) (alt_Ip Ip' pa Q) P.
Proof.
  intros W Ip Ip' pa P Q Ipext.
  destruct Ipext as [Ipext1 Ipext2].
  constructor. intros w H1.
    destruct (predicate_dec Q P) as [H2 | H2].
    subst. rewrite alt_Ip_eq. rewrite alt_Ip_eq in H1.
    auto. rewrite alt_Ip_neq. rewrite alt_Ip_neq in H1.
    apply Ipext1. all : auto.

    intros R H1. destruct (predicate_dec Q R) as [H2 | H2].
    subst. do 2  rewrite alt_Ip_eq. auto.
    rewrite alt_Ip_neq. rewrite alt_Ip_neq. apply Ipext2.
    all : auto.
Qed.

Lemma Ip_ext_pa_f : forall (W : Set) 
                    (Ip : predicate -> W -> Prop)
                    (P : predicate)
                    (pa : W -> Prop),
  Ip_extends W (alt_Ip Ip pa_f P) (alt_Ip Ip pa P) P.
Proof.
  intros W Ip P pa. constructor.
    intros w H.
    unfold pa_f in *.
    rewrite alt_Ip_eq in *. contradiction.

    intros Q H. rewrite alt_Ip_neq. rewrite alt_Ip_neq.
    all : auto.
Qed.

Lemma Ip_extends_same_Ip_list : forall l W Ip Ip' P,
  Ip_extends W Ip Ip' P ->
  ~ In P l -> same_Ip_list Ip Ip' l.
Proof.
  induction l; intros W Ip Ip' P Hext Hpocc. constructor.
  simpl in *. apply not_or_and in Hpocc. 
  inversion Hext. destruct Hext as [H1 H2]. 
  specialize (H2 a). constructor. 
  + apply H2; auto. firstorder.
  + eapply IHl. constructor. apply H. apply H0. apply Hpocc.
Qed.

Lemma same_Ip_list_comm: forall l (W : Set) (Ip Ip' : predicate -> W -> Prop),
  same_Ip_list Ip Ip' l <->
  same_Ip_list Ip' Ip l.
Proof.
  induction l; intros W Iv Ip'.
  split; intros; constructor.
  simpl. split; (intros H; inversion H; subst; constructor;
      [auto | apply IHl; auto]).
Qed.

(* ---------------------------------------------------------------------------- *)

Lemma lem_bb2 : forall alpha P W Iv Ip Ip' Ir,
~ Pred_in_SO alpha P ->
Ip_extends W Ip Ip' P ->
SOturnst W Iv Ip Ir alpha ->
SOturnst W Iv Ip' Ir alpha.
Proof.
  intros.
  apply same_preds_in with (Ip := Ip).
  apply Ip_extends_same_Ip_list with (P := P).
  all : assumption.
Qed.

Lemma lem_bb2_2 : forall alpha P W Iv Ip Ip' Ir,
~ Pred_in_SO alpha P ->
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

Lemma up_not_occ_SO : forall (alpha : SecOrder) (P : predicate),
  ~ Pred_in_SO alpha P ->
    (alpha_upward_monotone_P alpha P /\ alpha_downward_monotone_P alpha P).
Proof.
  intros alpha P H.
  unfold alpha_upward_monotone_P. 
  unfold alpha_downward_monotone_P.
  apply conj; intros until 0.
    apply lem_bb2; auto.
    apply lem_bb2_2; auto.
Qed.

(* -------------------------------------------------------------------- *)

Lemma up_negSO : forall (alpha: SecOrder) (P : predicate),
  alpha_upward_monotone_P alpha P ->
    alpha_downward_monotone_P (negSO alpha) P.
Proof.
  intros alpha P H.
  destruct (Pred_in_SO_dec (negSO alpha) P) as [Hocc|Hocc];
     [ | apply up_not_occ_SO; exact Hocc].
  unfold alpha_upward_monotone_P in *.
  intros W Iv Ir Ip Ip' Ipext.
  simpl in *.
  unfold not; intros SOt' H2; apply SOt'.
  apply H with (Ip := Ip'); assumption.
Qed.

Lemma up_conjSO12 : forall (alpha1 alpha2 : SecOrder) (P : predicate),
  alpha_upward_monotone_P alpha1 P ->
    alpha_upward_monotone_P alpha2 P ->
      alpha_upward_monotone_P (conjSO alpha1 alpha2) P.
Proof.
  intros alpha1 alpha2 P H1 H2.
  destruct (Pred_in_SO_dec (conjSO alpha1 alpha2) P) as [Hocc|Hocc];
    [ | apply up_not_occ_SO; exact Hocc].
  unfold alpha_upward_monotone_P in *.
  intros W Iv Ir Ip Ip' Ipext SOt.
  simpl in *.
  apply conj; [apply H1 with (Ip := Ip) | apply H2 with (Ip := Ip)];
   try apply SOt; try assumption.
Qed.

Lemma up_disjSO12 : forall (alpha1 alpha2 : SecOrder) (P : predicate),
  alpha_upward_monotone_P alpha1 P ->
    alpha_upward_monotone_P alpha2 P ->
      alpha_upward_monotone_P (disjSO alpha1 alpha2) P.
Proof.
  intros alpha1 alpha2 P H1 H2.
  destruct (Pred_in_SO_dec (disjSO alpha1 alpha2) P) as [Hocc|Hocc];
    [ | apply up_not_occ_SO; exact Hocc].
  unfold alpha_upward_monotone_P in *.
  intros W Iv Ir Ip Ip' Ipext SOt.
  simpl in *.
  destruct SOt as [SOt | SOt];
    [left ;apply H1 with (Ip := Ip) |
    right ; apply H2 with (Ip := Ip)]; assumption.
Qed. 

Lemma up_implSO12 : forall (alpha1 alpha2 : SecOrder) (P : predicate),
  alpha_downward_monotone_P alpha1 P ->
    alpha_upward_monotone_P alpha2 P ->
      alpha_upward_monotone_P (implSO alpha1 alpha2) P.
Proof.
  intros alpha1 alpha2 P H1 H2.
  destruct (Pred_in_SO_dec (implSO alpha1 alpha2) P) as [Hocc|Hocc];
    [ | apply up_not_occ_SO; exact Hocc].
  unfold alpha_upward_monotone_P in *.
  intros W Iv Ir Ip Ip' Ipext SOt.
  simpl in *; intros H.
  apply H2 with (Ip := Ip); try assumption.
  apply SOt.
  apply H1 with (Ip := Ip'); assumption.
Qed. 

Lemma up_allFO : forall (alpha : SecOrder) (x : FOvariable)
                         (P : predicate),
    ((alpha_upward_monotone_P alpha P) ->
     (alpha_upward_monotone_P (allFO x alpha) P)).
Proof.
  intros alpha x P Hmono.
  unfold alpha_upward_monotone_P in *.
  intros W Iv R Ip Ip' Ipext SOt.
  simpl in *.
  destruct x as [xn]; intros d.
  specialize (SOt d).
  specialize (Hmono W (alt_Iv Iv d (Var xn)) R Ip Ip' Ipext).
  apply Hmono.
  assumption.
Qed.

Lemma up_exFO : forall (alpha : SecOrder) (x : FOvariable)
                         (P : predicate),
    ((alpha_upward_monotone_P alpha P) ->
     (alpha_upward_monotone_P (exFO x alpha) P)).
Proof.
  intros alpha x P Hmono.
  unfold alpha_upward_monotone_P in *.
  intros W Iv R Ip Ip' Ipext SOt.
  simpl in *.
  destruct x as [xn]; destruct SOt as [d SOt].
  exists d.
  specialize (Hmono W (alt_Iv Iv d (Var xn)) R Ip Ip' Ipext).
  apply Hmono.
  assumption.
Qed.

Lemma up_allSO : forall (alpha : SecOrder) (P Q: predicate),
    ((alpha_upward_monotone_P alpha P) ->
     (alpha_upward_monotone_P (allSO Q alpha) P)).
Proof.
  intros alpha P Q Hmono.
  unfold alpha_upward_monotone_P in *.
  intros W Iv R Ip Ip' Ipext SOt.
  simpl in *.
  destruct Q as [Qm]; destruct P as [Pn].
  intros pa.
  specialize (SOt pa).
  specialize (Hmono W Iv R (alt_Ip Ip pa (Pred Qm))
        (alt_Ip Ip' pa (Pred Qm))).
  apply Hmono.
  apply Ip_ext_alt_Ip; assumption.

  assumption.
Qed.

Lemma up_exSO : forall (alpha : SecOrder) (P Q: predicate),
    ((alpha_upward_monotone_P alpha P) ->
     (alpha_upward_monotone_P (exSO Q alpha) P)).
Proof.
  intros alpha P Q Hmono.
  unfold alpha_upward_monotone_P in *.
  intros W Iv R Ip Ip' Ipext SOt.
  simpl in *.
  destruct Q as [Qm]; destruct P as [Pn].
  destruct SOt as [pa SOt].
  exists pa.
  specialize (Hmono W Iv R (alt_Ip Ip pa (Pred Qm))
        (alt_Ip Ip' pa (Pred Qm))).
  apply Hmono.
  apply Ip_ext_alt_Ip; assumption.

  assumption.
Qed.

(* -------------------------------------------------------------------- *)

Lemma down_negSO : forall (alpha: SecOrder) (P : predicate),
  alpha_downward_monotone_P alpha P ->
    alpha_upward_monotone_P (negSO alpha) P.
Proof.
  intros alpha P H.
  destruct (Pred_in_SO_dec (negSO alpha) P) as [Hocc|Hocc];
    [ | apply up_not_occ_SO; exact Hocc].
  unfold alpha_upward_monotone_P in *.
  intros W Iv Ir Ip Ip' Ipext.
  simpl in *.
  unfold not; intros SOt' H2; apply SOt'.
  apply H with (Ip := Ip'); assumption.
Qed.

Lemma down_conjSO12 : forall (alpha1 alpha2 : SecOrder) (P : predicate),
  alpha_downward_monotone_P alpha1 P ->
    alpha_downward_monotone_P alpha2 P ->
      alpha_downward_monotone_P (conjSO alpha1 alpha2) P.
Proof.
  intros alpha1 alpha2 P H1 H2.
  destruct (Pred_in_SO_dec (conjSO alpha1 alpha2) P) as [Hocc|Hocc];
    [ | apply up_not_occ_SO; exact Hocc].
  unfold alpha_upward_monotone_P in *.
  intros W Iv Ir Ip Ip' Ipext SOt.
  simpl in *.
  apply conj; [apply H1 with (Ip := Ip) | apply H2 with (Ip := Ip)];
   try apply SOt; try assumption.
Qed.

Lemma down_disjSO12 : forall (alpha1 alpha2 : SecOrder) (P : predicate),
  alpha_downward_monotone_P alpha1 P ->
    alpha_downward_monotone_P alpha2 P ->
      alpha_downward_monotone_P (disjSO alpha1 alpha2) P.
Proof.
  intros alpha1 alpha2 P H1 H2.
  destruct (Pred_in_SO_dec (disjSO alpha1 alpha2) P) as [Hocc|Hocc];
    [ | apply up_not_occ_SO; exact Hocc].
  unfold alpha_downward_monotone_P in *.
  intros W Iv Ir Ip Ip' Ipext SOt.
  simpl in *.
  destruct SOt as [SOt | SOt];
    [left ;apply H1 with (Ip := Ip) |
    right ; apply H2 with (Ip := Ip)]; try assumption.
Qed. 

Lemma down_implSO12 : forall (alpha1 alpha2 : SecOrder) (P : predicate),
  alpha_upward_monotone_P alpha1 P ->
    alpha_downward_monotone_P alpha2 P ->
      alpha_downward_monotone_P (implSO alpha1 alpha2) P.
Proof.
  intros alpha1 alpha2 P H1 H2.
  destruct (Pred_in_SO_dec (implSO alpha1 alpha2) P) as [Hocc|Hocc];
    [ | apply up_not_occ_SO; exact Hocc].
  unfold alpha_upward_monotone_P in *.
  intros W Iv Ir Ip Ip' Ipext SOt.
  simpl in *; intros H.
  apply H2 with (Ip := Ip); try assumption.
  apply SOt.
  apply H1 with (Ip := Ip'); assumption.
Qed.

Lemma down_allFO : forall (alpha : SecOrder) (x : FOvariable)
                         (P : predicate),
    ((alpha_downward_monotone_P alpha P) ->
     (alpha_downward_monotone_P (allFO x alpha) P)).
Proof.
  intros alpha x P Hmono.
  unfold alpha_downward_monotone_P in *.
  intros W Iv R Ip Ip' Ipext SOt.
  simpl in *.
  destruct x as [xn]; intros d.
  specialize (SOt d).
  specialize (Hmono W (alt_Iv Iv d (Var xn)) R Ip Ip' Ipext).
  apply Hmono.
  assumption.
Qed. 

Lemma down_exFO : forall (alpha : SecOrder) (x : FOvariable)
                         (P : predicate),
    ((alpha_downward_monotone_P alpha P) ->
     (alpha_downward_monotone_P (exFO x alpha) P)).
Proof.
  intros alpha x P Hmono.
  unfold alpha_downward_monotone_P in *.
  intros W Iv R Ip Ip' Ipext SOt.
  simpl in *.
  destruct x as [xn]; destruct SOt as [d SOt];
  exists d.
  specialize (Hmono W (alt_Iv Iv d (Var xn)) R Ip Ip' Ipext).
  apply Hmono.
  assumption.
Qed. 

Lemma down_allSO : forall (alpha : SecOrder) (P Q: predicate),
    ((alpha_downward_monotone_P alpha P) ->
     (alpha_downward_monotone_P (allSO Q alpha) P)).
Proof.
  intros alpha P Q Hmono.
  unfold alpha_downward_monotone_P in *.
  intros W Iv R Ip Ip' Ipext SOt.
  simpl in *.
  destruct Q as [Qm]; destruct P as [Pn].
  intros pa.
  specialize (SOt pa).
  specialize (Hmono W Iv R (alt_Ip Ip pa (Pred Qm))
        (alt_Ip  Ip' pa (Pred Qm))).
  apply Hmono.
  apply Ip_ext_alt_Ip; assumption.

  assumption.
Qed.

Lemma down_exSO : forall (alpha : SecOrder) (P Q: predicate),
    ((alpha_downward_monotone_P alpha P) ->
     (alpha_downward_monotone_P (exSO Q alpha) P)).
Proof.
  intros alpha P Q Hmono.
  unfold alpha_downward_monotone_P in *.
  intros W Iv R Ip Ip' Ipext SOt.
  simpl in *.
  destruct Q as [Qm]; destruct P as [Pn].
  destruct SOt as [pa SOt].
  exists pa.
  specialize (Hmono W Iv R (alt_Ip Ip pa (Pred Qm))
        (alt_Ip Ip' pa (Pred Qm))).
  apply Hmono.
  apply Ip_ext_alt_Ip; assumption.

  assumption.
Qed.

(* ------------------------------------------------------------- *)

Lemma monotonicity_SO_predSO : forall (P Q : predicate) (x : FOvariable),
  Pred_in_SO (predSO Q x) P ->
  (Pred_is_pos_SO (predSO Q x) P -> alpha_upward_monotone_P (predSO Q x) P) /\
  (Pred_is_neg_SO (predSO Q x) P -> alpha_downward_monotone_P (predSO Q x) P).
Proof.
  intros P Q x HPocc.
  apply conj; intros H.
    unfold alpha_upward_monotone_P.
    intros W Iv R Ip Ip' Ipext SOt.
    simpl in *.
    destruct Ipext as [Ha Hb].
    destruct (predicate_dec P Q) as [H2 | H2].
      subst. apply Ha. auto.

      rewrite <- Hb; auto.

    unfold alpha_downward_monotone_P.
    intros W Iv R Ip Ip' Ipext SOt.
    simpl in *.
    destruct Ipext as [Ha Hb].
    destruct (predicate_dec P Q) as [H2 | H2].
      subst. contradiction (Pred_is_neg_SO_not_predSO _ _ H).

      rewrite Hb; auto.
Qed.

Lemma monotonicity_SO_relatSO : forall (P: predicate) (x y : FOvariable),
  Pred_in_SO (relatSO x y) P  ->
  (Pred_is_pos_SO (relatSO x y) P -> alpha_upward_monotone_P (relatSO x y) P) /\
  (Pred_is_neg_SO (relatSO x y) P -> alpha_downward_monotone_P (relatSO x y) P).
Proof. firstorder. Qed.

Lemma monotonicity_SO_eqFO : forall (P: predicate) (x y : FOvariable),
  Pred_in_SO (eqFO x y) P ->
  (Pred_is_pos_SO (eqFO x y) P -> alpha_upward_monotone_P (eqFO x y) P) /\
  (Pred_is_neg_SO (eqFO x y) P -> alpha_downward_monotone_P (eqFO x y) P).
Proof. firstorder. Qed.

Lemma monotonicity_SO_allFO : forall (alpha : SecOrder) (P: predicate)
                                     (x : FOvariable),
  (Pred_in_SO alpha P ->
          (Pred_is_pos_SO alpha P -> alpha_upward_monotone_P alpha P) /\
          (Pred_is_neg_SO alpha P -> alpha_downward_monotone_P alpha P)) ->
  Pred_in_SO (allFO x alpha) P ->
    (Pred_is_pos_SO (allFO x alpha) P -> alpha_upward_monotone_P (allFO x alpha) P) /\
    (Pred_is_neg_SO (allFO x alpha) P -> alpha_downward_monotone_P (allFO x alpha) P).
Proof.
  intros alpha P x IHalpha HPocc.
  rewrite <- Pred_in_SO_allFO with (x := x) in HPocc.
  specialize (IHalpha HPocc).
  apply conj; intros H.
    rewrite Pred_is_pos_SO_allFO in H.
    apply up_allFO; apply IHalpha;
      assumption.

    rewrite Pred_is_neg_SO_allFO in H.
    apply down_allFO; apply IHalpha;
      assumption.
Qed.

Lemma monotonicity_SO_exFO : forall (alpha : SecOrder) (P: predicate)
                                     (x : FOvariable),
  (Pred_in_SO alpha P ->
          (Pred_is_pos_SO alpha P -> alpha_upward_monotone_P alpha P) /\
          (Pred_is_neg_SO alpha P -> alpha_downward_monotone_P alpha P)) ->
  Pred_in_SO (exFO x alpha) P ->
    (Pred_is_pos_SO (exFO x alpha) P -> alpha_upward_monotone_P (exFO x alpha) P) /\
    (Pred_is_neg_SO (exFO x alpha) P -> alpha_downward_monotone_P (exFO x alpha) P).
Proof.
  intros alpha P x IHalpha HPocc.
  rewrite <- Pred_in_SO_exFO with (x := x) in HPocc.
  specialize (IHalpha HPocc).
  apply conj; intros H.
    rewrite Pred_is_pos_SO_exFO in H.
    apply up_exFO; apply IHalpha;
      assumption.

    rewrite Pred_is_neg_SO_exFO in H.
    apply down_exFO; apply IHalpha;
      assumption.
Qed.

Lemma monotonicity_SO_negSO : forall (alpha : SecOrder) (P: predicate),
    (Pred_in_SO alpha P ->
          (Pred_is_pos_SO alpha P -> alpha_upward_monotone_P alpha P) /\
          (Pred_is_neg_SO alpha P -> alpha_downward_monotone_P alpha P)) ->
     Pred_in_SO (negSO alpha) P ->
    ((Pred_is_pos_SO (negSO alpha) P -> alpha_upward_monotone_P (negSO alpha) P) /\
     (Pred_is_neg_SO (negSO alpha) P -> alpha_downward_monotone_P (negSO alpha) P)).
Proof.
  intros alpha P IHalpha Hpocc.
  rewrite <- Pred_in_SO_negSO in Hpocc.
  specialize (IHalpha Hpocc).
  split; intros H.
    apply down_negSO.
    apply IHalpha.
    apply P_pos_negSO.
    assumption.

    apply up_negSO.
    apply IHalpha.
    apply P_neg_negSO.
    assumption.
Qed.

Lemma monotonicity_SO_conjSO : forall (alpha1 alpha2 : SecOrder) (P: predicate),
  (Pred_in_SO alpha1 P ->
           (Pred_is_pos_SO alpha1 P -> alpha_upward_monotone_P alpha1 P) /\
           (Pred_is_neg_SO alpha1 P -> alpha_downward_monotone_P alpha1 P)) ->
  (Pred_in_SO alpha2 P ->
           (Pred_is_pos_SO alpha2 P -> alpha_upward_monotone_P alpha2 P) /\
           (Pred_is_neg_SO alpha2 P -> alpha_downward_monotone_P alpha2 P)) ->
  Pred_in_SO (conjSO alpha1 alpha2) P ->
  (Pred_is_pos_SO (conjSO alpha1 alpha2) P ->
   alpha_upward_monotone_P (conjSO alpha1 alpha2) P) /\
  (Pred_is_neg_SO (conjSO alpha1 alpha2) P ->
   alpha_downward_monotone_P (conjSO alpha1 alpha2) P).
Proof.
  intros alpha1 alpha2 P IHalpha1 IHalpha2 Hpocc.
  apply conj; intros H; [apply up_conjSO12| apply down_conjSO12].
    destruct (Pred_in_SO_dec alpha1 P) as [Hpocc1 | Hpocc1].
      apply IHalpha1; auto.
      eapply Pred_is_pos_SO_conjSO_l. auto. apply H.
      apply up_not_occ_SO. auto.

    destruct (Pred_in_SO_dec alpha2 P) as [Hpocc2 | Hpocc2].
      apply IHalpha2; auto.
      eapply Pred_is_pos_SO_conjSO_r. auto. apply H.
      apply up_not_occ_SO. auto.

    destruct (Pred_in_SO_dec alpha1 P) as [Hpocc1 | Hpocc1].
      apply IHalpha1; auto.
      eapply Pred_is_neg_SO_conjSO_l. auto. apply H.
      apply up_not_occ_SO. auto.

    destruct (Pred_in_SO_dec alpha2 P) as [Hpocc2 | Hpocc2].  
      apply IHalpha2; auto.
      eapply Pred_is_neg_SO_conjSO_r. auto. apply H.
      apply up_not_occ_SO. auto.
Qed.

Lemma monotonicity_SO_disjSO : forall (alpha1 alpha2 : SecOrder) (P: predicate),
  (Pred_in_SO alpha1 P  ->
           (Pred_is_pos_SO alpha1 P -> alpha_upward_monotone_P alpha1 P) /\
           (Pred_is_neg_SO alpha1 P -> alpha_downward_monotone_P alpha1 P)) ->
  (Pred_in_SO alpha2 P ->
           (Pred_is_pos_SO alpha2 P -> alpha_upward_monotone_P alpha2 P) /\
           (Pred_is_neg_SO alpha2 P -> alpha_downward_monotone_P alpha2 P)) ->
  Pred_in_SO (disjSO alpha1 alpha2) P ->
  (Pred_is_pos_SO (disjSO alpha1 alpha2) P ->
   alpha_upward_monotone_P (disjSO alpha1 alpha2) P) /\
  (Pred_is_neg_SO (disjSO alpha1 alpha2) P ->
   alpha_downward_monotone_P (disjSO alpha1 alpha2) P).
Proof.
  intros alpha1 alpha2 P IHalpha1 IHalpha2 Hpocc.
  apply conj; intros H; [apply up_disjSO12| apply down_disjSO12].
    destruct (Pred_in_SO_dec alpha1 P) as [Hpocc1 | Hpocc1].
      apply IHalpha1; auto.
      eapply Pred_is_pos_SO_disjSO_l. auto. apply H.
      apply up_not_occ_SO. auto.

    destruct (Pred_in_SO_dec alpha2 P) as [Hpocc2 | Hpocc2].
      apply IHalpha2; auto.
      eapply Pred_is_pos_SO_disjSO_r. auto. apply H.
      apply up_not_occ_SO. auto.

    destruct (Pred_in_SO_dec alpha1 P) as [Hpocc1 | Hpocc1].
      apply IHalpha1; auto.
      eapply Pred_is_neg_SO_disjSO_l. auto. apply H.
      apply up_not_occ_SO. auto.

    destruct (Pred_in_SO_dec alpha2 P) as [Hpocc2 | Hpocc2].  
      apply IHalpha2; auto.
      eapply Pred_is_neg_SO_disjSO_r. auto. apply H.
      apply up_not_occ_SO. auto.
Qed.

Lemma monotonicity_SO_implSO : forall (alpha1 alpha2 : SecOrder) (P: predicate),
  (Pred_in_SO alpha1 P ->
           (Pred_is_pos_SO alpha1 P -> alpha_upward_monotone_P alpha1 P) /\
           (Pred_is_neg_SO alpha1 P -> alpha_downward_monotone_P alpha1 P)) ->
  (Pred_in_SO alpha2 P ->
           (Pred_is_pos_SO alpha2 P -> alpha_upward_monotone_P alpha2 P) /\
           (Pred_is_neg_SO alpha2 P -> alpha_downward_monotone_P alpha2 P)) ->
  Pred_in_SO (implSO alpha1 alpha2) P ->
  (Pred_is_pos_SO (implSO alpha1 alpha2) P ->
   alpha_upward_monotone_P (implSO alpha1 alpha2) P) /\
  (Pred_is_neg_SO (implSO alpha1 alpha2) P ->
   alpha_downward_monotone_P (implSO alpha1 alpha2) P).
Proof.
  intros alpha1 alpha2 P IHalpha1 IHalpha2 Hpocc.
  apply conj; intros H; [apply up_implSO12| apply down_implSO12].
    destruct (Pred_in_SO_dec alpha1 P) as [Hpocc1 | Hpocc1].
      apply IHalpha1; auto.
      eapply Pred_is_pos_SO_implSO_l. auto. apply H.
      apply up_not_occ_SO. auto.

    destruct (Pred_in_SO_dec alpha2 P) as [Hpocc2 | Hpocc2].
      apply IHalpha2; auto.
      eapply Pred_is_pos_SO_implSO_r. auto. apply H.
      apply up_not_occ_SO. auto.

    destruct (Pred_in_SO_dec alpha1 P) as [Hpocc1 | Hpocc1].
      apply IHalpha1; auto.
      eapply Pred_is_neg_SO_implSO_l. auto. apply H.
      apply up_not_occ_SO. auto.

    destruct (Pred_in_SO_dec alpha2 P) as [Hpocc2 | Hpocc2].  
      apply IHalpha2; auto.
      eapply Pred_is_neg_SO_implSO_r. auto. apply H.
      apply up_not_occ_SO. auto.
Qed.

Lemma monotonicity_SO_allSO : forall (alpha : SecOrder) (P Q: predicate),
  (Pred_in_SO alpha P ->
          (Pred_is_pos_SO alpha P -> alpha_upward_monotone_P alpha P) /\
          (Pred_is_neg_SO alpha P -> alpha_downward_monotone_P alpha P)) ->
  Pred_in_SO (allSO Q alpha) P ->
  (Pred_is_pos_SO (allSO Q alpha) P -> alpha_upward_monotone_P (allSO Q alpha) P) /\
  (Pred_is_neg_SO (allSO Q alpha) P -> alpha_downward_monotone_P (allSO Q alpha) P).
Proof.
  intros alpha P Q IHalpha Hpocc.
  destruct P as [Pn]; destruct Q as [Qm].
  apply conj; intros H.
    apply up_allSO. destruct (Pred_in_SO_dec alpha (Pred Pn)) as [Hpocc2 | Hpocc2].
      apply IHalpha; try assumption.
      apply Pred_is_pos_SO_allSO in H; assumption.

      apply up_not_occ_SO.  assumption.

    apply down_allSO. destruct (Pred_in_SO_dec alpha (Pred Pn)) as [Hpocc2 | Hpocc2].
      apply IHalpha; try assumption.
      apply Pred_is_neg_SO_allSO in H; assumption.

      apply up_not_occ_SO.  assumption.
Qed.

Lemma monotonicity_SO_exSO : forall (alpha : SecOrder) (P Q: predicate),
  (Pred_in_SO alpha P ->
          (Pred_is_pos_SO alpha P -> alpha_upward_monotone_P alpha P) /\
          (Pred_is_neg_SO alpha P -> alpha_downward_monotone_P alpha P)) ->
  Pred_in_SO (allSO Q alpha) P ->
  (Pred_is_pos_SO (exSO Q alpha) P -> alpha_upward_monotone_P (exSO Q alpha) P) /\
  (Pred_is_neg_SO (exSO Q alpha) P -> alpha_downward_monotone_P (exSO Q alpha) P).
Proof.
  intros alpha P Q IHalpha Hpocc.
  destruct P as [Pn]; destruct Q as [Qm].
  apply conj; intros H.
    apply up_exSO. destruct (Pred_in_SO_dec alpha (Pred Pn)) as [Hpocc2 | Hpocc2].
      apply IHalpha; try assumption.
      apply Pred_is_pos_SO_exSO in H; assumption.

      apply up_not_occ_SO.  assumption.

    apply down_exSO. destruct (Pred_in_SO_dec alpha (Pred Pn)) as [Hpocc2 | Hpocc2].
      apply IHalpha; try assumption.
      apply Pred_is_neg_SO_exSO in H; assumption.

      apply up_not_occ_SO.  assumption.
Qed.

Lemma monotonicity_SO : forall (alpha : SecOrder) (P : predicate),
  Pred_in_SO alpha P ->
    (Pred_is_pos_SO alpha P ->
      alpha_upward_monotone_P alpha P) /\
    (Pred_is_neg_SO alpha P ->
      alpha_downward_monotone_P alpha P).
Proof.
  intros alpha P.
  induction alpha.
    apply monotonicity_SO_predSO.
    apply monotonicity_SO_relatSO.
    apply monotonicity_SO_eqFO.
    apply monotonicity_SO_allFO; assumption. 
    apply monotonicity_SO_exFO; assumption.
    apply monotonicity_SO_negSO; assumption.
    apply monotonicity_SO_conjSO; assumption.
    apply monotonicity_SO_disjSO; assumption.
    apply monotonicity_SO_implSO; assumption.
    apply monotonicity_SO_allSO; assumption.
    apply monotonicity_SO_exSO; assumption.
Qed.


Lemma mono_pos : forall (W : Set) (Iv : FOvariable -> W)
                    (Ip : predicate -> W -> Prop)
                    (Ir : W -> W -> Prop)
                    (alpha : SecOrder) (P : predicate)
                    (pa : W -> Prop),
  Pred_is_pos_SO alpha P ->
  SOturnst W Iv (alt_Ip Ip pa_f P) Ir alpha ->
  SOturnst W Iv (alt_Ip Ip pa P) Ir alpha.
Proof.
  intros W Iv Ip Ir alpha P pa Hpos Hf.
  pose proof monotonicity_SO as H.
  unfold alpha_upward_monotone_P in H.
  pose proof (Pred_is_pos__in_SO _ _ Hpos) as H2.
  specialize (H alpha P H2). destruct H as [Ha Hb].
  apply Ha with (Ip := (alt_Ip Ip pa_f P)); auto.
  apply Ip_ext_pa_f.
Qed.
