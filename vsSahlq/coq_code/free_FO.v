Require Export low_mods.
Require Import Rep_Pred_FOv.

Fixpoint free_FO (alpha : SecOrder) (x : FOvariable)  : bool :=
  match alpha with
    predSO P y => if FOvariable_dec x y then true else false
  | relatSO y1 y2 => if FOvariable_dec x y1 then true else
                       if FOvariable_dec x y2 then true else false
  | eqFO y1 y2 => if FOvariable_dec x y1 then true else
                       if FOvariable_dec x y2 then true else false
  | allFO y beta =>  if FOvariable_dec x y then false else free_FO beta x
  | exFO y beta => if FOvariable_dec x y then false else free_FO beta x
  | negSO beta => free_FO beta x
  | conjSO beta1 beta2 => if free_FO beta1 x then true
                             else free_FO beta2 x
  | disjSO beta1 beta2 => if free_FO beta1 x then true
                             else free_FO beta2 x
  | implSO beta1 beta2 => if free_FO beta1 x then true
                             else free_FO beta2 x
  | allSO P beta => free_FO beta x
  | exSO P beta => free_FO beta x
  end.

Fixpoint no_free_FO_l (alpha : SecOrder) (l : list FOvariable) :=
  match l with
  | nil => true
  | cons x l' => if free_FO alpha x then false else no_free_FO_l alpha l'
  end.

Inductive closed_except alpha x : Prop :=
  | closed_except_y : free_FO alpha x = true ->
      (forall y, ~ x = y -> free_FO alpha y = false) -> closed_except alpha x.

Lemma free_FO_conjSO : forall alpha1 alpha2 x,
  free_FO (conjSO alpha1 alpha2) x = false ->
  (free_FO alpha1 x = false) /\ (free_FO alpha2 x = false).
Proof.
  intros alpha1 alpha2 x Hfree.
    simpl in Hfree.
    case_eq (free_FO alpha1 x); intros H1;
      rewrite H1 in *. discriminate.
    apply conj. reflexivity. assumption.
Qed.

Lemma free_FO_max_FOv_f_pre2_relatSO : forall f f0 n,
(max_FOv (relatSO f f0)) <=  n ->
free_FO (relatSO f f0) (Var (S n)) = false.
Proof.
  intros [m1] [m2] n Hleb.  simpl in *.
  pose proof (Nat.max_lub_l _ _ _ Hleb).
  pose proof (Nat.max_lub_r _ _ _ Hleb).
  rewrite FOvariable_dec_r; auto.
  rewrite FOvariable_dec_r; auto.
  intros HH. inversion HH. lia.
  intros HH. inversion HH. lia.
Qed.

Lemma free_FO_max_FOv_f_pre2_allFO : forall gamma f n, 
  (forall n : nat,
          (max_FOv gamma) <= n -> 
          free_FO gamma (Var (S n)) = false) ->
(max_FOv (allFO f gamma)) <= n ->
free_FO (allFO f gamma) (Var (S n)) = false.
Proof.
  intros gamma [xn] n IHalpha Hleb.
  unfold max_FOv in *. simpl in *.
  rewrite FOvariable_dec_r. apply IHalpha. lia. 
  apply FOv_not. lia.
Qed.

Lemma free_FO_max_FOv_f_pre2_conjSO : forall gamma1 gamma2 n,
  (forall n : nat,
            (max_FOv gamma1) <= n ->
           free_FO gamma1 (Var (S n)) = false) ->
  (forall n : nat,
            (max_FOv gamma2) <= n  ->
           free_FO gamma2 (Var (S n)) = false) ->
(max_FOv (conjSO gamma1 gamma2)) <= n ->
free_FO (conjSO gamma1 gamma2) (Var (S n)) = false.
Proof.
  intros gamma1 gamm2 n IHgamma1 IHgamma2 Hleb.
  simpl in *. unfold max_FOv in *. simpl in *.
  rewrite max_FOv_l_app in *.  
  rewrite IHgamma1. apply IHgamma2. lia. lia.
Qed.

Lemma free_FO_max_FOv_f_pre2 : forall gamma n,
   (max_FOv gamma) <= n ->
  free_FO gamma (Var (S n)) = false.
Proof.
  induction gamma; intros n Hleb;
    try (    simpl in *; apply IHgamma; assumption).
    destruct f as [m].    simpl in *.
    rewrite FOvariable_dec_r. auto. apply FOv_not. 
    unfold max_FOv in *. simpl in *. lia.

    apply free_FO_max_FOv_f_pre2_relatSO; assumption.
    apply free_FO_max_FOv_f_pre2_relatSO; assumption.
    apply free_FO_max_FOv_f_pre2_allFO; assumption.
    apply free_FO_max_FOv_f_pre2_allFO; assumption.
    apply free_FO_max_FOv_f_pre2_conjSO; assumption.
    apply free_FO_max_FOv_f_pre2_conjSO; assumption.
    apply free_FO_max_FOv_f_pre2_conjSO; assumption.
Qed.

Lemma free_FO_max_FOv_f : forall alpha gamma x,
free_FO gamma (Var (S (max_FOv (conjSO gamma (exFO x alpha))))) = false.
Proof. 
  intros. apply free_FO_max_FOv_f_pre2. 
  apply le_max_FOv_conjSO_l. 
Qed.

Lemma var_in_SO_free_FO : forall alpha x,
  ~ var_in_SO alpha x ->  free_FO alpha x = false.
Proof.
  induction alpha; intros x Hocc; unfold var_in_SO in *;
    simpl in *; auto;
  try (apply Decidable.not_or in Hocc; 
       if_then_else_dest_blind; auto; subst; firstorder);
  try (rewrite IHalpha1; [rewrite IHalpha2; auto |];
    intros HH; apply Hocc; apply in_or_app; auto).
Qed. 

Lemma free_FO_rep_FOv2 : forall alpha x y,
  free_FO alpha x = false ->
  free_FO alpha y = false ->
  free_FO (replace_FOv alpha x y) y = false.
Proof.
  induction alpha; intros x y H1 H2; simpl in *;
    try solve [apply IHalpha; auto].
  + destruct (FOvariable_dec x f). discriminate.
    simpl. auto.
  + destruct (FOvariable_dec x f). discriminate.
    destruct (FOvariable_dec x f0). discriminate. auto.
  + destruct (FOvariable_dec x f). discriminate.
    destruct (FOvariable_dec x f0). discriminate. auto.

  + destruct (FOvariable_dec x f). simpl. subst.
    FOv_dec_l_rep. simpl. destruct (FOvariable_dec y f). auto.
    apply IHalpha; auto.
  + destruct (FOvariable_dec x f). simpl. subst.
    FOv_dec_l_rep. simpl. destruct (FOvariable_dec y f). auto.
    apply IHalpha; auto.
  + if_then_else_hyp_tzf. rewrite IHalpha1; auto; apply IHalpha2; auto.
  + if_then_else_hyp_tzf. rewrite IHalpha1; auto; apply IHalpha2; auto.
  + if_then_else_hyp_tzf. rewrite IHalpha1; auto; apply IHalpha2; auto.
Qed.


Lemma kk16 : forall alpha x y z,
  ~ x = y ->
  ~ x = z ->
  free_FO alpha x =
  free_FO (replace_FOv alpha y z) x.
Proof.
  induction alpha; intros x y z Hneq1 Hneq2; simpl in *;
    try (apply IHalpha; auto).
  + dest_FOv_dec_blind; simpl; dest_FOv_dec_blind;
             auto; subst; firstorder.
  + dest_FOv_dec_blind; simpl; dest_FOv_dec_blind; auto;
      subst; firstorder.
  + dest_FOv_dec_blind; simpl; dest_FOv_dec_blind; auto;
      subst; firstorder.
  + dest_FOv_dec_blind; simpl; dest_FOv_dec_blind; auto;
      subst; firstorder.
  + dest_FOv_dec_blind; simpl; dest_FOv_dec_blind; auto;
      subst; firstorder.
  + rewrite <- IHalpha1. rewrite <- IHalpha2. all : auto.
  + rewrite <- IHalpha1. rewrite <- IHalpha2. all : auto.
  + rewrite <- IHalpha1. rewrite <- IHalpha2. all : auto.
Qed.

Lemma kk18 : forall alpha x y z,
  ~ z = x ->
  ~ z = y ->
  free_FO alpha z = false ->
  free_FO (replace_FOv alpha x y) z = false.
Proof.
  induction alpha; intros x y z H1 H2 Hf; simpl in *.
  + dest_FOv_dec_blind; try discriminate; simpl;
      dest_FOv_dec_blind; subst; firstorder.
  + dest_FOv_dec_blind; try discriminate; simpl;
      dest_FOv_dec_blind; subst; firstorder.
  + dest_FOv_dec_blind; try discriminate; simpl;
      dest_FOv_dec_blind; subst; firstorder.
  + dest_FOv_dec_blind; try discriminate; simpl;
      dest_FOv_dec_blind; subst; firstorder.
  + dest_FOv_dec_blind; try discriminate; simpl;
      dest_FOv_dec_blind; subst; firstorder.
  + dest_FOv_dec_blind; try discriminate; simpl;
      dest_FOv_dec_blind; subst; firstorder.
  + if_then_else_hyp_tzf. rewrite IHalpha1; auto; rewrite IHalpha2; auto.
  + if_then_else_hyp_tzf. rewrite IHalpha1; auto; rewrite IHalpha2; auto.
  + if_then_else_hyp_tzf. rewrite IHalpha1; auto; rewrite IHalpha2; auto.
  + apply IHalpha; auto.
  + apply IHalpha; auto.
Qed.

Lemma free_FO_rep_FOv_same : forall alpha x y,
  ~ x = y -> free_FO (replace_FOv alpha x y) x = false.
Proof.
  intros. apply var_in_SO_free_FO.
  apply var_in_SO_rep_FOv. assumption.
Qed.

Lemma kk15  : forall alpha x y z,
  ~ x = y ->
  ~ x = z ->
  closed_except alpha x ->
  closed_except (replace_FOv alpha y z) x.
Proof.
  intros alpha x y z Hneq1 Hneq2 [Hc1 Hc2]. 
  constructor. rewrite <- kk16; auto.
  intros u Hneq3.
  destruct (FOvariable_dec z u). subst.
    apply free_FO_rep_FOv2; auto.
  destruct (FOvariable_dec y z). subst.
    rewrite rep_FOv_rem. auto.
  destruct (FOvariable_dec y u). subst.
    apply free_FO_rep_FOv_same; auto.
  apply kk18; auto.
Qed.

Lemma free_FO_var_in : forall alpha x,
  free_FO alpha x = true ->  var_in_SO alpha x.
Proof.
  intros alpha x H.
  destruct (in_dec FOvariable_dec x (FOvars_in alpha)) as [H2 | H2].
  auto.  apply var_in_SO_free_FO in H2. rewrite H in *. discriminate.
Qed.

Lemma kk19_1 : forall alpha x,
  closed_except alpha x -> var_in_SO alpha x.
Proof.
  intros alpha x [H1 H2]. apply free_FO_var_in. auto.
Qed.

Lemma aa14 : forall alpha x y,
  closed_except alpha x ->
  ~ x = y ->
  free_FO alpha y = false.
Proof. intros alpha x y [Hc1 Hc2] Hneq. auto. Qed.

Lemma free_FO_rep_pred : forall alpha x P,
  free_FO alpha x =
  free_FO (replace_pred alpha P (Var 1)
     (negSO (eqFO (Var 1) (Var 1)))) x.
Proof.
  induction alpha; intros x P; simpl in *;
    try solve [dest_FOv_dec_blind; auto].
    + dest_FOv_dec_blind; destruct (predicate_dec P p); subst;
        simpl; dest_FOv_dec_blind; auto; try contradiction.
    + rewrite <- IHalpha1; rewrite <- IHalpha2; auto.
    + rewrite <- IHalpha1; rewrite <- IHalpha2; auto.
    + rewrite <- IHalpha1; rewrite <- IHalpha2; auto.
    + destruct (predicate_dec P p); simpl; apply IHalpha.
    + destruct (predicate_dec P p); simpl; apply IHalpha.
Qed.

Lemma kk12 : forall alpha x y,
  closed_except alpha x ->
  closed_except (replace_pred alpha y (Var 1) 
    (negSO (eqFO (Var 1) (Var 1)))) x.
Proof.
  intros alpha [xn] [ym] [H1 H2]. 
  constructor. rewrite <- free_FO_rep_pred. auto.
  intros [zn] Hneq.  rewrite <- free_FO_rep_pred.
  auto.
Qed.

Lemma kk11: forall lP beta x,
closed_except beta x ->
closed_except
  (replace_pred_l beta lP
     (nlist_list (length lP) (nlist_var _ (Var 1)))
     (nlist_list (length lP) (nlist_empty _))) x.
Proof.
  induction lP; intros beta x H; simpl; auto.
  apply kk12. auto.
Qed.