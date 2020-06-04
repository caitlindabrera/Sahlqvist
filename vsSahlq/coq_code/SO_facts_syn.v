Require Export med_mods.
Require Import Rel At ST pos_SO vsSahlq_setup Is_Pos_Rep_Pred.

Lemma pos_rep_pred : forall (alpha : SecOrder) (P : predicate)
                                (cond : SecOrder) (x : FOvariable),
  FO_frame_condition cond = true ->
    pos_SO alpha ->
      pos_SO (replace_pred alpha P x cond).
Proof.
  intros alpha P cond x Hunary Huni.
  intros Q HQ.  apply P_is_pos_rep_pred; auto.
  apply Huni. apply Pred_in_SO_rep_pred in HQ; auto.
Qed.

Lemma FOv_att_P_REL : forall rel P,
  REL rel = true ->
  FOv_att_P rel P = nil.
Proof.
  induction rel; intros P H; try (discriminate). reflexivity.
  simpl in *.
  case_eq (REL rel1); intros H2; rewrite H2 in *. 2 : discriminate.
  simpl in *. rewrite IHrel1. rewrite IHrel2. all : try reflexivity.
  assumption.
Qed.

Lemma FOv_att_P_l_conjSO_rel : forall lP rel atm,
  REL rel = true ->
  FOv_att_P_l (conjSO rel atm) lP =
  FOv_att_P_l atm lP.
Proof.
  induction lP; intros rel atm Hrel. reflexivity.
  simpl. rewrite FOv_att_P_REL. 
  rewrite IHlP. reflexivity.  
  all : assumption.
Qed.

Lemma pos_SO_rep_pred_l : forall lP n beta,
  pos_SO beta ->
  pos_SO (replace_pred_l beta lP (nlist_list _ (nlist_var n (Var 1)))
      (nlist_list _ (nlist_empty n))).
Proof.
  induction lP; intros n beta Hun.
    simpl. assumption.

    simpl. destruct n. simpl. assumption.
    simpl. apply pos_rep_pred. reflexivity.
    apply IHlP. assumption.
Qed.

Lemma lem1 : forall alpha P,
  ~ Pred_in_SO alpha P ->  FOv_att_P alpha P = nil.
Proof.
  induction alpha; intros P H; unfold Pred_in_SO in *;
    auto; simpl in *; try solve [apply IHalpha; auto].
  + simpl in *. if_then_else_dest_blind; firstorder.
    apply except. firstorder.
  + rewrite IHalpha1; firstorder; apply IHalpha2;
    firstorder.
  + rewrite IHalpha1; firstorder; apply IHalpha2;
    firstorder.
  + rewrite IHalpha1; firstorder; apply IHalpha2;
    firstorder.
Qed.

Lemma lem10 : forall alpha P,
  SOQFree_P alpha P = true ->
  Pred_in_SO alpha P ->
  ~(FOv_att_P alpha P = nil).
Proof.
  induction alpha; intros P Hno H; unfold Pred_in_SO in *;
    simpl in *; try contradiction;
      try solve [ apply IHalpha; auto].
  + destruct H. subst. pred_dec_l_rep. firstorder. contradiction.
  + apply in_app_or in H. unfold andb in *. if_then_else_hyp.
    intros HH; apply app_eq_nil in HH. firstorder.
  + apply in_app_or in H. unfold andb in *. if_then_else_hyp.
    intros HH; apply app_eq_nil in HH. firstorder.
  + apply in_app_or in H. unfold andb in *. if_then_else_hyp.
    intros HH; apply app_eq_nil in HH. firstorder.
  + if_then_else_hyp_dep. destruct H. auto.
    apply IHalpha; auto.
  + if_then_else_hyp_dep. destruct H. auto.
    apply IHalpha; auto.
Qed.

Lemma closed_except_ST : forall phi x,
  closed_except (ST phi x) x.
Proof.
  induction phi; intros x; simpl.
  + destruct p. simpl. FOv_dec_l_rep.
    constructor; simpl; auto. FOv_dec_l_rep.
    intros y Hy.
    rewrite FOvariable_dec_r; auto.
  + firstorder.
  + destruct (IHphi1 x) as [IH1 IH1'].
    destruct (IHphi2 x) as [IH2 IH2'].
    constructor; intros; simpl. rewrite IH1. auto. 
    rewrite IH1'; auto.
  + destruct (IHphi1 x) as [IH1 IH1'].
    destruct (IHphi2 x) as [IH2 IH2'].
    constructor; intros; simpl. rewrite IH1. auto. 
    rewrite IH1'; auto.
  + destruct (IHphi1 x) as [IH1 IH1'].
    destruct (IHphi2 x) as [IH2 IH2'].
    constructor; intros; simpl. rewrite IH1. auto. 
    rewrite IH1'; auto.
  + constructor. simpl. FOv_dec_l_rep. rewrite FOvariable_dec_r. auto.
    pose proof next_FOv_not. auto.
    intros y Hy. simpl.
    destruct (FOvariable_dec y (next_FOv x)). auto.
    rewrite FOvariable_dec_r; auto. firstorder. 
  + constructor. simpl. FOv_dec_l_rep. rewrite FOvariable_dec_r. auto.
    pose proof next_FOv_not. auto.
    intros y Hy. simpl.
    destruct (FOvariable_dec y (next_FOv x)). auto.
    rewrite FOvariable_dec_r; auto. firstorder. 
Qed.


Lemma FO_frame_condition_list_closed_allFO : forall lx alpha,
  FO_frame_condition (list_closed_allFO alpha lx) =
  FO_frame_condition alpha.
Proof.
  induction lx; intros alpha.
    simpl. reflexivity.

    simpl. destruct a. apply IHlx.
Qed.

Lemma FO_frame_condition_preds_in_rev : forall alpha,
preds_in alpha = nil ->
FO_frame_condition alpha = true.
Proof.
  intros alpha H.
  case_eq (FO_frame_condition alpha); intros H2.
    reflexivity.

    apply FO_frame_condition_preds_in_f in H2.
    rewrite H in H2. simpl in *.
    contradiction (H2 eq_refl).
Qed.

Lemma jj9_gen : forall alpha x P cond,
  FO_frame_condition cond = true ->
  preds_in (replace_pred alpha P x cond) =
  rem_pred (preds_in alpha) P.
Proof.
  induction alpha; intros x P cond Hun;
    try solve [    dest_FOv_blind; auto].

  + simpl. destruct (predicate_dec P p); simpl; auto.
    rewrite preds_in_rep_FOv. 
    apply FO_frame_condition_preds_in. auto. 
  + dest_FOv_blind; simpl; apply IHalpha; auto.
  + dest_FOv_blind; simpl; apply IHalpha; auto.
  + simpl. apply IHalpha; auto.
  + simpl. rewrite rem_pred_app.
    rewrite IHalpha1; auto. rewrite IHalpha2; auto.
  + simpl. rewrite rem_pred_app.
    rewrite IHalpha1; auto. rewrite IHalpha2; auto.
  + simpl. rewrite rem_pred_app.
    rewrite IHalpha1; auto. rewrite IHalpha2; auto.
  + simpl. destruct (predicate_dec P p); simpl; auto.
    rewrite IHalpha; auto. 
  + simpl. destruct (predicate_dec P p); simpl; auto.
    rewrite IHalpha; auto. 
Qed.


Lemma please3 : forall l alpha P x cond ,
  FO_frame_condition cond = true ->
  incl (preds_in alpha) l ->
  incl (preds_in (replace_pred alpha P x cond)) (rem_pred l P).
Proof.
  intros l alpha P x cond Hun H1 Q H2.
  destruct (predicate_dec P Q); subst.
  + apply In_preds_in_rep_pred in H2. 
    rewrite (FO_frame_condition_preds_in cond) in H2; auto.
    firstorder.
  + apply preds_in_rep_pred_In in H2.
    rewrite (FO_frame_condition_preds_in cond) in H2; auto.
    apply in_rem_pred; auto.  apply H1.
    rewrite app_nil_r in H2. auto.
Qed.

Lemma please4 : forall l alpha P x cond ,
  FO_frame_condition cond = true ->
  incl (preds_in alpha) (cons P l) ->
  incl (preds_in (replace_pred alpha P x cond)) l.
Proof.
  intros l alpha P x cond Hun Hin.
  apply (please3 _ alpha P x cond) in Hin.
  rewrite rem_pred_cons_same in Hin.
  apply (incl_trans _ _ _ _ Hin (incl_rem_pred_l _ _)).
  assumption.
Qed.

Lemma preds_in_rename_FOv : forall alpha x y,
  preds_in (replace_FOv alpha x y) = preds_in alpha.
Proof.
  induction alpha; intros x y;
    try solve [simpl; dest_FOv_dec_blind; simpl; auto];
    try (simpl; rewrite IHalpha1; rewrite IHalpha2; auto);
    (simpl; rewrite IHalpha; auto).
Qed.

Lemma preds_in_strip_exFO : forall alpha n,
  preds_in (strip_exFO alpha n) = preds_in alpha.
Proof.
  induction alpha; intros n; try (destruct n; reflexivity).
  destruct f. simpl. destruct n.  reflexivity. 
  apply IHalpha.
Qed.

Lemma preds_in_list_closed_exFO : forall l alpha,
  preds_in (list_closed_exFO alpha l) = preds_in alpha.
Proof.
  induction l; intros alpha.
    simpl. reflexivity.

    simpl. destruct a. apply IHl.
Qed.


Lemma aa22_pre_1_pre : forall cond x z,  
  (forall y : FOvariable, var_in_SO cond y -> x = y) ->
  (forall y : FOvariable, var_in_SO (replace_FOv cond x z) y -> z = y).
Proof.
  induction cond; intros x z H y H2; simpl in *;
    try solve [(eapply IHcond; firstorder)].
  + dest_FOv_dec_blind; subst. inversion H2; auto.
    contradiction.  inversion H2. subst. firstorder.
    firstorder.
  + dest_FOv_dec_blind; subst; inversion H2;
    subst; try contradiction; try firstorder.
  + dest_FOv_dec_blind; subst; inversion H2;
    subst; try contradiction; try firstorder.
  + dest_FOv_dec_blind; subst; inversion H2;
      subst; try contradiction; try solve [firstorder].
    eapply IHcond. intros yy HH. apply H. firstorder. auto. 
  + dest_FOv_dec_blind; subst; inversion H2;
      subst; try contradiction; try solve [firstorder].
    eapply IHcond. intros yy HH. apply H. firstorder. auto. 
  + pose proof (var_in_SO_conjSO cond1 cond2).
    apply var_in_SO_conjSO in H2. destruct H2 as [H3 | H3].
    ++ eapply IHcond1; auto. intros yy HH. apply H.
       apply var_in_SO_conjSO. auto. auto.
    ++ eapply IHcond2; auto. intros yy HH. apply H.
       apply var_in_SO_conjSO. auto. auto.
  + pose proof (var_in_SO_conjSO cond1 cond2).
    apply var_in_SO_conjSO in H2. destruct H2 as [H3 | H3].
    ++ eapply IHcond1; auto. intros yy HH. apply H.
       apply var_in_SO_conjSO. auto. auto.
    ++ eapply IHcond2; auto. intros yy HH. apply H.
       apply var_in_SO_conjSO. auto. auto.       
  + pose proof (var_in_SO_conjSO cond1 cond2).
    apply var_in_SO_conjSO in H2. destruct H2 as [H3 | H3].
    ++ eapply IHcond1; auto. intros yy HH. apply H.
       apply var_in_SO_conjSO. auto. auto.
    ++ eapply IHcond2; auto. intros yy HH. apply H.
       apply var_in_SO_conjSO. auto. auto.
Qed.

Lemma aa22_pre_1 : forall cond x z,  
  (forall y : FOvariable, x <> y -> ~ var_in_SO cond y) ->
  (forall y : FOvariable, z <> y ->
     ~ var_in_SO (replace_FOv cond x z) y).
Proof.
  intros cond x z H1 y H2 H3.
  apply aa22_pre_1_pre in H3. contradiction.
  clear H3.
  intros yy HH. destruct (FOvariable_dec x yy). auto.
  apply H1 in HH. contradiction. auto.
Qed.

Lemma var_in_SO_rep_FOv : forall cond x y,
  var_in_SO cond x ->  var_in_SO (replace_FOv cond x y) y.
Proof.
  intros cond x y H. unfold var_in_SO in *. rewrite rep__ren_list.
  apply in_rename_FOv_list_2. auto.
Qed.

Lemma aa22_pre : forall cond xn ym,
  var_in_SO cond (Var xn) ->
  (forall y : FOvariable, Var xn <> y -> ~ var_in_SO cond y) ->
(max_FOv (replace_FOv cond (Var xn) (Var ym))) <= ym.
Proof.
  intros cond xn ym Hocc Hnocc.
  pose proof (aa22_pre_1 cond (Var xn) (Var ym) Hnocc) as H.
  apply var_in_SO_rep_FOv with (y := (Var ym)) in Hocc.
  rewrite (aa22_pre_2 _ ym); try assumption. lia.
Qed.

Lemma aa22 : forall beta P x cond,
  var_in_SO cond x ->
  (forall y, ~ x = y -> ~ var_in_SO cond y) ->
  (max_FOv (replace_pred beta P x cond)) <= (max_FOv beta).
Proof.
  induction beta; intros P x cond Hocc Hnocc; auto; simpl in *.
  + destruct (predicate_dec P p); auto. dest_FOv_blind.
    rewrite max_FOv_predSO. simpl. apply aa22_pre; auto.
  + dest_FOv_blind. rewrite max_FOv_allFO. simpl. 
    apply PeanoNat.Nat.max_le_compat_l. auto.
  + dest_FOv_blind. rewrite max_FOv_exFO. simpl. 
    apply PeanoNat.Nat.max_le_compat_l. auto.
  + apply IHbeta; auto.
  + do 2 rewrite max_FOv_conjSO. 
    apply PeanoNat.Nat.max_le_compat. apply IHbeta1; auto.
    apply IHbeta2; auto.
  + do 2 rewrite max_FOv_disjSO. 
    apply PeanoNat.Nat.max_le_compat. apply IHbeta1; auto.
    apply IHbeta2; auto.
  + do 2 rewrite max_FOv_implSO. 
    apply PeanoNat.Nat.max_le_compat. apply IHbeta1; auto.
    apply IHbeta2; auto.
  + destruct (predicate_dec P p); simpl; apply IHbeta; auto.
  + destruct (predicate_dec P p); simpl; apply IHbeta; auto.
Qed.

Lemma   aa21 : forall lP lx lcond beta,
   var_in_SO_l lcond lx ->
   var_not_in_SO_l lcond lx ->
  (max_FOv (replace_pred_l beta lP lx lcond)) <= (max_FOv beta).
Proof.
  induction lP; intros lx lcond beta Hocc Hnocc. firstorder.
  destruct lx. firstorder. 
  destruct lcond.  firstorder.
  simpl in *. inversion Hocc. subst. inversion Hnocc. subst.
  apply (PeanoNat.Nat.le_trans _ (max_FOv (replace_pred_l beta lP lx lcond))).
  apply aa22; auto.   apply IHlP; auto.
Qed.

Lemma aa25 : forall n,
  var_in_SO_l (nlist_list n (nlist_empty _))
                   (nlist_list n (nlist_var _ (Var 1))).
Proof. induction n; simpl; constructor; firstorder. Qed.

Lemma aa26 : forall n,
  var_not_in_SO_l (nlist_list n (nlist_empty _ ))
                    (nlist_list n (nlist_var _ (Var 1))).
Proof. induction n; simpl; constructor; firstorder. Qed.

Lemma rep_pred_l_list_closed_allFO : forall l lP lx lcond alpha,
  replace_pred_l (list_closed_allFO alpha l) lP lx lcond =
  list_closed_allFO (replace_pred_l alpha lP lx lcond) l.
Proof.
  induction l; intros lP lx lcond alpha.
    simpl. reflexivity.

    simpl. rewrite <- IHl. rewrite rep_pred_l_allFO.
    reflexivity.
Qed.


Lemma calc_cons_SO_ST : forall phi x,
  calc_cons_SO (ST phi x) = ST (calc_cons_modal phi) x.
Proof.
  induction phi; intros [xn]; try reflexivity.
    destruct p as [Pn]; reflexivity.
Qed.

Lemma calc_ante_SO_ST : forall phi x,
  calc_ante_SO (ST phi x) = ST (calc_ante_modal phi) x.
Proof.
  induction phi; intros [xn]; try reflexivity.
    destruct p as [Pn]; reflexivity.
Qed.
Lemma SOQFree_rel : forall rel,
  REL rel = true ->
  SOQFree rel = true.
Proof.
  induction rel; intros H;
    try (simpl in *; discriminate).
    destruct f; destruct f0;
      reflexivity.

    simpl.
    pose proof (REL_conjSO_l _ _ H) as H2.
    apply REL_conjSO_r in H.
    rewrite IHrel1.
    apply IHrel2.
    all : assumption.
Qed.

Lemma SOQFree_atm : forall atm,
  AT atm = true ->
  SOQFree atm = true.
Proof.
  induction atm; intros H;
    try (simpl in *; discriminate).
    destruct f; destruct p;
      reflexivity.

    simpl.
    pose proof (AT_conjSO_l _ _ H) as H2.
    apply AT_conjSO_r in H.
    rewrite IHatm1.
    apply IHatm2.
    all : assumption.
Qed.

Lemma SOQFree_calc_cons_SO_ST : forall phi x,
  vsSahlq phi ->
SOQFree (calc_cons_SO (ST phi x)) = true.
Proof.
  intros phi x Hvs.
  destruct (vsSahlq_dest_ex phi Hvs) as [phi1 [phi2 [Heq [Hvs1 Hun]]]].
  rewrite Heq.
  simpl.
  apply SOQFree_ST.
Qed.

Lemma SOQFree_vsS_pp_3_ra : forall phi rel atm x,
  REL rel = true ->
  AT atm = true ->
  vsSahlq phi ->
SOQFree (implSO (conjSO rel atm) (calc_cons_SO (ST phi x))) = true.
Proof.
  intros phi rel atm [xn] HREL HAT Hvs.
  simpl.
  rewrite SOQFree_rel.
  rewrite SOQFree_atm.
  apply SOQFree_calc_cons_SO_ST.
  all : assumption.
Qed.

Lemma SOQFree_vsS_pp_3_r : forall phi rel x,
  REL rel = true ->
  vsSahlq phi ->
SOQFree (implSO rel (calc_cons_SO (ST phi x))) = true.
Proof.
  intros phi rel [xn] HREL Hvs.
  simpl.
  rewrite SOQFree_rel.
  apply SOQFree_calc_cons_SO_ST.
  all :assumption.
Qed.

Lemma SOQFree_vsS_pp_3_a : forall phi atm x,
  AT atm = true ->
  vsSahlq phi ->
SOQFree (implSO atm (calc_cons_SO (ST phi x))) = true.
Proof.
  intros phi atm [xn] HAT Hvs.
  simpl.
  rewrite SOQFree_atm.
  apply SOQFree_calc_cons_SO_ST.
  all :assumption.
Qed.

Lemma pos_SO_calc_cons_SO: forall phi x,
  vsSahlq phi ->
  pos_SO (calc_cons_SO (ST phi x)).
Proof.
  intros phi x Hvs.
  destruct (vsSahlq_dest_ex phi Hvs) as [phi1 [phi2 [Heq [Hvs1 Hun]]]].
  rewrite Heq.
  simpl. apply pos__SO.
  assumption.
Qed.

Lemma list_closed_SO_app : forall l1 l2 alpha,
  list_closed_SO alpha (app l1 l2) = 
  list_closed_SO (list_closed_SO alpha l2) l1.
Proof.
  induction l1; intros l2 alpha.
    reflexivity.

    destruct a as [Pn].
    simpl.
    rewrite IHl1.
    reflexivity.
Qed.
Lemma preds_in_list_closed_allFO : forall l alpha,
  preds_in (list_closed_allFO alpha l) = preds_in alpha.
Proof.
  induction l; intros alpha.
    reflexivity.

    simpl.
    apply IHl.
Qed.

Lemma att_allFO_var_ST_gen : forall phi n m,
  n <= m ->
  ~ att_allFO_var (ST phi (Var m)) (Var n).
Proof.
  induction phi; intros n m H1 H2; simpl in *;
    try solve [inversion H2; subst; firstorder].
  + destruct p. inversion H2.
  + inversion H2; subst; try lia;
    inversion H4; subst. lia. inversion H5.
    apply IHphi in H5; auto. lia.
  + inversion H2; subst; try lia.
    inversion H4; subst. inversion H5. 
    apply IHphi in H5; auto. lia.
Qed.

Lemma att_allFO_var_ST : forall phi x,
  ~ att_allFO_var (ST phi x) x.
Proof. intros phi [xn]. apply att_allFO_var_ST_gen. lia. Qed.

Lemma att_exFO_var_ST_gen : forall phi n m,
  n <= m ->
  ~ att_exFO_var (ST phi (Var m)) (Var n).
Proof.
  induction phi; intros n m H1 H2; simpl in *;
    try solve [inversion H2; subst; firstorder].
  + destruct p. inversion H2.
  + inversion H2; subst; try lia;
    inversion H4; subst. inversion H5.
    apply IHphi in H5; auto. lia.
  + inversion H2; subst; try lia.
    inversion H4; subst. lia.
    inversion H4; subst. inversion H5. 
    apply IHphi in H5; auto. lia.
Qed.

Lemma att_exFO_var_ST : forall phi x,
  ~ att_exFO_var (ST phi x) x.
Proof. intros phi [xn]. apply att_exFO_var_ST_gen. lia. Qed.


Lemma preds_in_replace_FOv_max_conj : forall alpha beta x,
  preds_in (replace_FOv_max_conj alpha beta x) =
  preds_in alpha.
Proof.
  unfold replace_FOv_max_conj.
  intros. rewrite preds_in_rename_FOv.
  reflexivity.
Qed.

Lemma rep_pred_l_list_rel_compl : forall l2 alpha,
  replace_pred_l alpha (list_rel_compl l2 (preds_in alpha))
    (nlist_list _ (nlist_var (length (list_rel_compl l2 (preds_in alpha))) (Var 1)))
    (nlist_list _ (nlist_empty (length (list_rel_compl l2 (preds_in alpha))))) =
  alpha.
Proof.
  induction l2; intros alpha. auto.
  simpl. destruct (in_predicate_dec a (preds_in alpha)) as [H1 | H1].
  apply IHl2. simpl.  rewrite IHl2. rewrite rep_pred_not_in; auto.
Qed.

Lemma closed_except_inst_cons_empty' : forall beta alpha x,
  closed_except beta x ->
  closed_except (instant_cons_empty' alpha beta) x.
Proof.
  unfold instant_cons_empty'.
  intros. apply kk11. assumption.
Qed.

Lemma list_rel_compl_nlist_P_cons : forall n P,
  list_rel_compl  (nlist_list n (nlist_P _ P)) (cons P nil) = nil.
Proof.
  induction n; intros P.  reflexivity.
  simpl. destruct (in_predicate_dec P (P :: nil)); auto.
  firstorder.
Qed.

Lemma list_rel_compl_P : forall n1 n2 P,
  list_rel_compl (nlist_list (S n2) (nlist_P _ P)) (nlist_list (S n1) (nlist_P _ P)) = nil.
Proof.  
  intros n1 n2. revert n1.
  induction n2; intros n1 P. simpl.
  destruct (in_predicate_dec P (P :: nlist_list n1 (nlist_P n1 P))); firstorder.
  simpl in *. specialize (IHn2 n1 P).
  destruct (in_predicate_dec P (P :: nlist_list n1 (nlist_P n1 P))).
  apply IHn2. firstorder.
Qed.

Lemma instant_cons_empty_implSO : forall alpha beta,
  instant_cons_empty (implSO alpha beta) =
    implSO alpha
  (replace_pred_l beta (list_rel_compl (preds_in beta) (preds_in alpha))
     (nlist_list _
        (nlist_var (length (list_rel_compl  (preds_in beta) (preds_in alpha))) (Var 1)))
     (nlist_list _
        (nlist_empty (length (list_rel_compl  (preds_in beta) (preds_in alpha)))))).
Proof.
  intros alpha beta. unfold instant_cons_empty. simpl.
  rewrite rep_pred_l_implSO. rewrite rep_pred_l_list_rel_compl. auto.
Qed.

Lemma instant_cons_empty_nil : forall alpha beta,
  preds_in alpha = nil ->
  preds_in beta = nil ->
  instant_cons_empty (implSO alpha beta) = implSO alpha beta.
Proof.
  intros alpha beta H1 H2. unfold instant_cons_empty.  
  simpl.  rewrite H1.  rewrite H2. auto.
Qed.

Lemma list_rel_compl_is_in_t : forall l1 l2 P,
  In P l1 ->
  list_rel_compl (cons P l2) l1 = list_rel_compl l2 l1.
Proof.
  induction l1; intros l2 P Hin. firstorder.
  simpl in *. destruct Hin. subst.
  pose proof (@in_predicate_dec_l (list predicate) P (P :: l1)).
  rewrite H. firstorder. firstorder.
  destruct (in_predicate_dec P (a :: l1)) as [H1 | H1]. firstorder.
  simpl in H1. apply not_or_and in H1.
  destruct H1. contradiction.
Qed.

Lemma incl_rep_pred_allSO : forall alpha P x cond Q,
  (forall (P : predicate) (x : FOvariable) (cond : SecOrder),
          FO_frame_condition cond = true ->
          incl (preds_in (replace_pred alpha P x cond)) (preds_in alpha)) ->
  FO_frame_condition cond = true ->
  incl (preds_in (replace_pred (allSO Q alpha) P x cond))
  (preds_in (allSO Q alpha)).
Proof.
  intros alpha P x cond Q IHalpha Hun.
    simpl. destruct (predicate_dec P Q). subst. 
    simpl. apply incl_rcons. auto.
    simpl. apply incl_cons. firstorder.
    apply incl_rcons. auto.
Qed.

Lemma incl_rep_pred_exSO : forall alpha P x cond Q,
  (forall (P : predicate) (x : FOvariable) (cond : SecOrder),
          FO_frame_condition cond = true ->
          incl (preds_in (replace_pred alpha P x cond)) (preds_in alpha)) ->
  FO_frame_condition cond = true ->
incl (preds_in (replace_pred (exSO Q alpha) P x cond))
  (preds_in (exSO Q alpha)).
Proof.
  intros alpha P x cond Q IHalpha Hun.
    simpl. destruct (predicate_dec P Q). subst. 
    simpl. apply incl_rcons. auto.
    simpl. apply incl_cons. firstorder.
    apply incl_rcons. auto.
Qed.

Lemma incl_rep_pred : forall alpha P x cond,
  FO_frame_condition cond = true ->
  incl (preds_in (replace_pred alpha P x cond)) 
               (preds_in alpha).
Proof.
  induction alpha; intros P x cond Hun; auto;
    try solve [firstorder];
    try (    simpl; apply incl_app_gen; auto).

    simpl. destruct (predicate_dec P p). subst.
    rewrite preds_in_rep_FOv. apply FO_frame_condition_preds_in in Hun.
    rewrite Hun. firstorder.
    simpl. apply incl_refl. 

    apply incl_rep_pred_allSO; auto.
    apply incl_rep_pred_exSO; auto.
Qed.

Lemma incl_rep_pred_l : forall lP lv lcond alpha,
  FO_frame_condition_l lcond = true ->
  incl (preds_in (replace_pred_l alpha lP lv lcond))
               (preds_in alpha).
Proof.
  induction lP; intros lv lcond alpha Hun. apply incl_refl.
  simpl. destruct lv. apply incl_refl.
  destruct lcond. apply incl_refl.
  simpl in Hun. case_eq (FO_frame_condition s); intros Hun1;
    rewrite Hun1 in *. 
    pose proof (incl_rep_pred (replace_pred_l alpha lP lv lcond)
                                    a f s Hun1) as H. 
    specialize (IHlP lv lcond alpha Hun).
    apply incl_trans with (l2 := (preds_in (replace_pred_l alpha lP lv lcond)));
          assumption. discriminate.
Qed.

Lemma vsSahlq_pp_Lemma4 : forall alpha beta,
  incl (preds_in (instant_cons_empty (implSO alpha beta)))
               (preds_in (implSO alpha beta)).
Proof.
  intros alpha beta.
  unfold instant_cons_empty.  simpl.
  apply incl_rep_pred_l.
  apply FO_frame_condition_l_empty_n.
Qed.

Lemma max_FOv_l_ren_FOv_list : forall l x ym,
    In x l ->
    max_FOv_l (rename_FOv_list l x (Var ym)) <= Init.Nat.max (max_FOv_l l) ym.
Proof.
  induction l; intros [xn] ym H. simpl. firstorder.
  destruct a as [zn]. simpl in H.
  rewrite rename_FOv_list_cons. destruct H.
  rewrite FOvariable_dec_l; auto. simpl.
  destruct (in_dec FOvariable_dec (Var xn) l). 
  specialize (IHl _ ym i). lia.
  rewrite rename_FOv_list_not_in.  lia. auto.
  destruct (FOvariable_dec (Var xn) (Var zn)) as [H1 | H1].
  inversion H1. subst. simpl. apply IHl with (ym := ym) in H.
  firstorder. lia. simpl.  apply IHl with (ym := ym) in H. lia.
Qed.
  
Lemma max_FOv_rep_FOv2 : forall alpha x ym,
  var_in_SO alpha x ->
 (max_FOv (replace_FOv alpha x (Var ym))) <= (max (max_FOv alpha) ym).
Proof.
  intros alpha x ym H. unfold max_FOv.
  rewrite rep__ren_list.
  apply max_FOv_l_ren_FOv_list. firstorder.
Qed.

Lemma le_max_FOv_replace_FOv : forall alpha x n,
  (max_FOv (replace_FOv alpha x (Var n))) <=
          (max (max_FOv alpha) n) .
Proof.
  intros alpha x n. unfold max_FOv. 
  rewrite rep__ren_list. 
  destruct (in_dec FOvariable_dec x (FOvars_in alpha)).
  apply max_FOv_l_ren_FOv_list.  auto.
  rewrite rename_FOv_list_not_in; auto. lia.
Qed.

Lemma list_rel_compl_rem_pred : forall l2 l P,
  list_rel_compl l2 (cons P l) =
  rem_pred (list_rel_compl l2 l) P.
Proof.
  induction l2; intros l P. auto.
  simpl. destruct (in_predicate_dec a (P :: l)) as [H | H].
  simpl in H. destruct H. subst.
  destruct (in_predicate_dec a l). apply IHl2.
  simpl. rewrite predicate_dec_l. apply IHl2. auto.
  rewrite in_predicate_dec_l. apply IHl2. auto.
  simpl in H. apply not_or_and in H. rewrite in_predicate_dec_r.
  simpl. rewrite predicate_dec_r. rewrite IHl2. auto.
  all : firstorder.
Qed.

Lemma jj9 : forall alpha x y z P,
  preds_in (replace_pred alpha P x (negSO (eqFO y z))) =
  rem_pred (preds_in alpha) P.
Proof.
  induction alpha; intros x y z P; simpl; auto;
  try (  rewrite IHalpha1; rewrite IHalpha2; rewrite rem_pred_app; auto).
  + dest_FOv_dec_blind; destruct (predicate_dec P p); auto.
  + destruct (predicate_dec P p); simpl; rewrite IHalpha; auto.
  + destruct (predicate_dec P p); simpl; rewrite IHalpha; auto.
Qed.



Lemma  jj10 : forall l2 l1,
  incl (list_rel_compl  l2 l1) l2.
Proof.
  induction l2; intros l1; simpl. firstorder.
  destruct (in_predicate_dec a l1). 
  apply incl_rcons. auto.
  apply incl_cons_cons. auto.
Qed.


Lemma jj12 : forall l1 l2 P,
  In P l1 ->
  ~ In P (list_rel_compl l2 l1) .
Proof.
  induction l1; intros l2 P H; auto.
  simpl in *. destruct H; subst. 
  + rewrite list_rel_compl_rem_pred.
    apply is_in_pred_rem_pred_eq. 
  + intros H2. rewrite list_rel_compl_rem_pred in H2.
    apply IHl1 with (l2 := l2) in H. 
    destruct (predicate_dec P a). subst.
    apply is_in_pred_rem_pred_eq in H2. auto.
    apply jj13 in H2. contradiction.  auto.
Qed.

Lemma jj11 : forall l2 l1,
  list_rel_compl l2 (list_rel_compl l2 l1) = cap_pred l2 l1.
Proof.
  induction l2; intros l1. auto.
  simpl. destruct (in_predicate_dec a l1) as [H2 | H2]. 
  +  rewrite IHl2. destruct (in_dec predicate_dec a l1).  
     apply jj12 with (l2 := l2) in H2.
     rewrite in_predicate_dec_r; auto.
     contradiction.
  +  rewrite list_rel_compl_rem_pred. rewrite IHl2.
     rewrite in_predicate_dec_l. destruct (in_dec predicate_dec a l1).
     firstorder. apply rem_pred_not_in. apply in_cap_pred. auto.
     firstorder.
Qed.

Lemma sumtin : forall l2 lb l beta,
  incl (preds_in beta) lb ->
  cap_pred_empty l2 (preds_in (replace_pred_l beta (list_rel_compl lb l)
      (nlist_list _ (nlist_var (length (list_rel_compl lb l)) (Var 1)))
      (nlist_list _ (nlist_empty (length (list_rel_compl lb l)))))) = true ->
  replace_pred_l 
    (replace_pred_l beta (list_rel_compl lb l)
      (nlist_list _ (nlist_var (length (list_rel_compl lb l)) (Var 1)))
      (nlist_list _ (nlist_empty (length (list_rel_compl lb l)))))
    l2
    (nlist_list (length l2) (nlist_var (length l2) (Var 1)))
    (nlist_list (length l2) (nlist_empty (length l2))) =
    (replace_pred_l beta (list_rel_compl lb l)
      (nlist_list _ (nlist_var (length (list_rel_compl lb l)) (Var 1)))
      (nlist_list _ (nlist_empty (length (list_rel_compl lb l))))).
Proof.
  induction l2; intros lb l beta H1 H2. auto.
  simpl in *. destruct (in_dec predicate_dec a 
           (preds_in
              (replace_pred_l beta (list_rel_compl lb l)
                 (nlist_list (length (list_rel_compl lb l))
                    (nlist_var (length (list_rel_compl lb l)) (Var 1)))
                 (nlist_list (length (list_rel_compl lb l))
                    (nlist_empty (length (list_rel_compl lb l))))))).
    rewrite in_predicate_dec_l in H2. discriminate. auto.
  rewrite in_predicate_dec_r in H2; auto.
  rewrite IHl2; try assumption.  rewrite rep_pred_not_in. 
  all : auto.
Qed.

Lemma jj8 : forall l beta,
  incl l (preds_in beta) ->
  preds_in (replace_pred_l beta l
      (nlist_list _ (nlist_var (length l) (Var 1)))
      (nlist_list _ (nlist_empty (length l)))) =
  list_rel_compl (preds_in beta) l.
Proof.
  induction l; intros beta H; simpl in *.
    rewrite list_rel_compl_nil. auto.
  pose proof (incl_lcons _ _ _ _ H).
  rewrite list_rel_compl_rem_pred. rewrite jj9. 
  rewrite IHl; auto.
Qed.

Lemma jj7 : forall l beta P,
  ~ In P l ->
  ~ In P (preds_in (replace_pred_l beta 
      (list_rel_compl (preds_in beta) l)
          (nlist_list (length (list_rel_compl (preds_in beta) l))
             (nlist_var (length (list_rel_compl (preds_in beta) l)) (Var 1)))
          (nlist_list (length (list_rel_compl (preds_in beta) l))
             (nlist_empty (length (list_rel_compl (preds_in beta) l)))))).
Proof.
  induction l; intros beta P H H2.
  + rewrite list_rel_compl_nil in H2.
    rewrite FO_frame_condition_preds_in in H2. assumption.
    apply FO_frame_condition_rep_pred_l.
    apply FO_frame_condition_l_empty_n.
  + simpl in *. rewrite jj8 in H2.
    rewrite jj11 in H2. rewrite cap_pred_comm in H2. simpl in H2.
    destruct (in_predicate_dec a (preds_in beta)).
    ++ simpl in *. destruct H2 as [H2 | H2]. firstorder. 
       apply in_pred_cap_pred_f1 in H2; auto. 
    ++ apply in_pred_cap_pred_f1 in H2; auto. 
    ++ apply jj10.
Qed.

Lemma jj6 : forall lb1 la beta2,
cap_pred_empty (list_rel_compl lb1 la)
  (preds_in
     (replace_pred_l beta2 (list_rel_compl (preds_in beta2) la)
        (nlist_list (length (list_rel_compl (preds_in beta2) la))
           (nlist_var (length (list_rel_compl (preds_in beta2) la)) (Var 1)))
        (nlist_list (length (list_rel_compl (preds_in beta2) la))
           (nlist_empty (length (list_rel_compl (preds_in beta2) la)))))) =
true.
Proof.
  induction lb1; intros la beta2. auto.
  simpl. destruct (in_predicate_dec a la). apply IHlb1.
  simpl. rewrite IHlb1. rewrite in_predicate_dec_r. auto.
  apply jj7. auto.
Qed.

Lemma instant_cons_empty'_conjSO : forall alpha beta1 beta2,
  instant_cons_empty' alpha (conjSO beta1 beta2) =
  conjSO (instant_cons_empty' alpha beta1) (instant_cons_empty' alpha beta2).
Proof.
  intros. unfold instant_cons_empty'.
  rewrite rep_pred_l_conjSO. simpl.
  rewrite list_rel_compl_app.
  do 2 rewrite rep_pred_l_app.
  rewrite rep_pred_l_switch.
  rewrite sumtin.
  rewrite sumtin. reflexivity.
  apply incl_refl.
  apply jj6. apply incl_refl.
  apply jj6.
Qed.

Lemma instant_cons_empty'_disjSO : forall alpha beta1 beta2,
  instant_cons_empty' alpha (disjSO beta1 beta2) =
  disjSO (instant_cons_empty' alpha beta1) (instant_cons_empty' alpha beta2).
Proof.
  intros. unfold instant_cons_empty'.
  rewrite rep_pred_l_disjSO. simpl.
  rewrite list_rel_compl_app.
  do 2 rewrite rep_pred_l_app.
  rewrite rep_pred_l_switch.
  rewrite sumtin.
  rewrite sumtin. reflexivity.
  apply incl_refl.
  apply jj6.  apply incl_refl.
  apply jj6.
Qed.

Lemma instant_cons_empty'_implSO : forall alpha beta1 beta2,
  instant_cons_empty' alpha (implSO beta1 beta2) =
  implSO (instant_cons_empty' alpha beta1) (instant_cons_empty' alpha beta2).
Proof.
  intros. unfold instant_cons_empty'.
  rewrite rep_pred_l_implSO. simpl.
  rewrite list_rel_compl_app.
  do 2 rewrite rep_pred_l_app.
  rewrite rep_pred_l_switch.
  rewrite sumtin.
  rewrite sumtin. reflexivity.
  apply incl_refl.
  apply jj6.  apply incl_refl.
  apply jj6.
Qed.

Lemma free_FO_instant_cons_empty'_f : forall beta alpha y,
  SOQFree beta = true  ->
  free_FO beta y = false ->
  free_FO (instant_cons_empty' alpha beta) y = false.
Proof.
  induction beta; intros alpha x Hno H; auto.
    simpl in *.  unfold instant_cons_empty'.
    simpl. destruct (in_predicate_dec p (preds_in alpha)). 
    simpl. auto. simpl. rewrite predicate_dec_l.
    FOv_dec_l_rep. simpl. repeat rewrite H. auto. auto.

    rewrite instant_cons_empty'_allFO. simpl in *.
    destruct (FOvariable_dec x f). auto. apply IHbeta; auto.

    rewrite instant_cons_empty'_exFO. simpl in *.
    destruct (FOvariable_dec x f). auto. apply IHbeta; auto.

    rewrite instant_cons_empty'_negSO.
    simpl in *. apply IHbeta; assumption.

    rewrite instant_cons_empty'_conjSO.
    simpl in *. case_eq (SOQFree beta1);
      intros H2; rewrite H2 in *. 2 : discriminate.
    case_eq (free_FO beta1 x); intros H3;
      rewrite H3 in H. discriminate.
    rewrite IHbeta1. apply IHbeta2. all : try assumption.
    reflexivity.

    rewrite instant_cons_empty'_disjSO.
    simpl in *. case_eq (SOQFree beta1);
      intros H2; rewrite H2 in *. 2 : discriminate.
    case_eq (free_FO beta1 x); intros H3;
      rewrite H3 in H. discriminate.
    rewrite IHbeta1. apply IHbeta2. all : try assumption.
    reflexivity.

    rewrite instant_cons_empty'_implSO.
    simpl in *. case_eq (SOQFree beta1);
      intros H2; rewrite H2 in *. 2 : discriminate.
    case_eq (free_FO beta1 x); intros H3;
      rewrite H3 in H. discriminate.
    rewrite IHbeta1. apply IHbeta2. all : try assumption.
    reflexivity.

    simpl in *. destruct p. discriminate.

    simpl in *. destruct p. discriminate.
Qed.

Lemma want9 : forall l2 l1 beta1,
  (forall P,
    In P l2 /\  In P (preds_in beta1) ->  In P l1) ->
  replace_pred_l beta1 (app l1 l2) 
      (nlist_list (length l1 + length l2) (nlist_var (length l1 + length l2) (Var 1)))
      (nlist_list (length l1 + length l2) (nlist_empty (length l1 + length l2))) =
  replace_pred_l beta1 l1 (nlist_list (length l1) (nlist_var _ (Var 1)))
      (nlist_list (length l1) (nlist_empty _)).
Proof.
  induction l2; intros l1 beta1 H.
  + simpl. rewrite app_nil_r. rewrite Nat.add_0_r. auto.
  + pose proof (rep_pred_l_app beta1 l1 (cons a l2)) as H2.
    simpl in *. rewrite app_length in H2. simpl in H2. rewrite H2.
    destruct (in_dec predicate_dec a l2).
    ++ destruct (nlist_list_ex (length l2) l2 eq_refl) as [lP H4].
      rewrite <- H4.
      rewrite length_nlist_list.
      rewrite rep_pred__l_is_in.
      rewrite H4.
      pose proof (rep_pred_l_app beta1 l1 l2) as H5.
      rewrite <- H5. rewrite app_length. simpl.
      apply IHl2. firstorder. rewrite H4. auto.
      apply FO_frame_condition_l_empty_n. auto.
    ++ rewrite Rep_Pred_FOv.rep_pred__l_switch_empty.
      pose proof (rep_pred_l_app beta1 l1 l2) as H5.
      rewrite <- H5. rewrite app_length. simpl.
      rewrite IHl2.
      specialize (H a). destruct a as [Qm]. simpl.
      destruct (in_dec predicate_dec (Pred Qm) l1).
      destruct (nlist_list_ex (length l1) l1 eq_refl) as [lP H4].
      rewrite <- H4.
      rewrite length_nlist_list.
      rewrite rep_pred__l_is_in. reflexivity.
      rewrite H4. assumption.
      apply FO_frame_condition_l_empty_n. auto.
      rewrite <- Rep_Pred_FOv.rep_pred__l_switch_empty.
      destruct (in_dec predicate_dec (Pred Qm) (preds_in beta1)).
      firstorder. rewrite rep_pred_Pred_in_SO_f; auto.
      firstorder.
Qed.

Lemma kk1 : forall beta alpha y,
  In y (FOvars_in alpha) ->  In y (FOvars_in beta)  ->
  In y (FOvars_in (instant_cons_empty' alpha beta)).
Proof.
  unfold instant_cons_empty'.
  induction beta; intros alpha y H1 H2; simpl in *.
  + destruct (in_predicate_dec p (preds_in alpha)).
    firstorder. simpl. FOv_dec_l_rep.  pred_dec_l_rep.  firstorder.
  + firstorder. + firstorder.
  + rewrite rep_pred_l_allFO. firstorder.
  + rewrite rep_pred_l_exFO. firstorder.
  + rewrite rep_pred_l_negSO. firstorder. 
  + rewrite list_rel_compl_app. rewrite rep_pred_l_conjSO. 
    simpl. rewrite app_length. rewrite want9. rewrite <- app_length.
    rewrite rep_pred_l_app. rewrite rep_pred_l_switch.
    rewrite <- rep_pred_l_app. rewrite app_length. rewrite want9.
    apply in_or_app. apply in_app_or in H2.
    destruct H2; auto.  apply want11. apply want11.
  + rewrite list_rel_compl_app. rewrite rep_pred_l_disjSO. 
    simpl. rewrite app_length. rewrite want9. rewrite <- app_length.
    rewrite rep_pred_l_app. rewrite rep_pred_l_switch.
    rewrite <- rep_pred_l_app. rewrite app_length. rewrite want9.
    apply in_or_app. apply in_app_or in H2.
    destruct H2; auto.  apply want11. apply want11.
  + rewrite list_rel_compl_app. rewrite rep_pred_l_implSO. 
    simpl. rewrite app_length. rewrite want9. rewrite <- app_length.
    rewrite rep_pred_l_app. rewrite rep_pred_l_switch.
    rewrite <- rep_pred_l_app. rewrite app_length. rewrite want9.
    apply in_or_app. apply in_app_or in H2.
    destruct H2; auto.  apply want11. apply want11.
  + destruct (in_predicate_dec p (preds_in alpha)); rewrite kk2. firstorder.
    simpl. apply kk6. auto.
  + destruct (in_predicate_dec p (preds_in alpha)); rewrite kk2_exSO. firstorder.
    simpl. apply kk6. auto.
Qed.

Lemma kk8 : forall lP beta x,
  ~ In x (FOvars_in beta) ->
  ~ In x (FOvars_in
   (replace_pred_l beta lP (nlist_list (length lP) (nlist_var _ (Var 1)))
      (nlist_list (length lP) (nlist_empty _)))).
Proof.
  induction lP; intros beta x H. auto.
  simpl in *. intros H2. apply IHlP in H.
  apply kk5 in H2. contradiction (H H2). 
Qed.

Lemma kk7 : forall beta alpha a,
  ~ In a (FOvars_in beta) ->
  ~ In a (FOvars_in (instant_cons_empty' alpha beta)).
Proof.  unfold instant_cons_empty'. intros. apply kk8; auto. Qed.

Lemma var_in_SO_instant_cons_empty' : forall beta alpha x,
  var_in_SO beta x -> var_in_SO (instant_cons_empty' alpha beta) x.
Proof.
  unfold instant_cons_empty'.  intros. 
  apply var_in_SO_instant_cons_empty'_pre. auto.
Qed.

Lemma max_FOv_rep_pred : forall alpha P x,
  max_FOv (replace_pred alpha P x (negSO (eqFO x x))) = 
  max_FOv alpha.
Proof.
  intros alpha P x. unfold max_FOv. 
  apply max_FOv_l_in_eq. apply kk5. apply kk6.
Qed.

Lemma max_FOv_instant_cons_empty'_pre: forall l beta,
max_FOv
  (replace_pred_l beta l (nlist_list (length l) (nlist_var _ (Var 1)))
          (nlist_list (length l) (nlist_empty _))) =
max_FOv beta.
Proof. 
  induction l; intros beta. auto.
  simpl. rewrite max_FOv_rep_pred. apply IHl.
Qed.

Lemma max_FOv_instant_cons_empty': forall beta alpha,
  (max_FOv (instant_cons_empty' alpha beta)) =
  max_FOv beta.
Proof.
  unfold instant_cons_empty'. intros.
  apply max_FOv_instant_cons_empty'_pre.
Qed.

Lemma kk19_2 : forall alpha xn,
  var_in_SO alpha (Var xn) -> xn <= (max_FOv alpha).
Proof.
  intros alpha x H. unfold var_in_SO in H.
  unfold max_FOv. apply want19_pre. auto.
Qed.

Lemma kk19 : forall alpha xn,
  closed_except alpha (Var xn) -> ~(S (max_FOv alpha)) <= xn.
Proof.
  intros alpha xn H.
  apply PeanoNat.Nat.nle_gt. unfold lt.
  apply le_n_S. apply kk19_2. apply free_FO_var_in.
  firstorder.
Qed.

Lemma var_in_SO_max_FOv_gen2 : forall beta n,
  var_in_SO beta (Var n) -> ~ (S (max_FOv beta)) <= n.
Proof.
  intros beta n H1 H2. unfold var_in_SO in H1.
  unfold max_FOv in H2. apply want19_pre in H1.
  firstorder.
Qed.

Lemma aa18_pre : forall l x n,
 S (max_FOv_l l) <= n ->
  (In x l -> max_FOv_l (rename_FOv_list l x (Var n)) = n) /\
  (~ In x l ->
   max_FOv_l (rename_FOv_list l x (Var n)) = max_FOv_l l).
Proof.
  intros l x n H. apply conj; intros H2.
  + apply PeanoNat.Nat.le_antisymm.
    apply (PeanoNat.Nat.le_trans _ _ _ ( max_FOv_l_ren_FOv_list _ _ _ H2)).
    lia. eapply in_rename_FOv_list_2 in H2. eapply want19_pre in H2. 
    apply H2.
  + rewrite rename_FOv_list_not_in; auto. 
Qed.

Lemma aa18 : forall alpha x n,
  (S (max_FOv alpha)) <= n ->
  (var_in_SO alpha x ->
    max_FOv (replace_FOv alpha x (Var n)) = n) /\
  (~ var_in_SO alpha x ->
    max_FOv (replace_FOv alpha x (Var n)) = max_FOv alpha).
Proof.
  intros alpha x n H. unfold var_in_SO.
  unfold max_FOv in *. rewrite rep__ren_list.
  apply aa18_pre. auto.
Qed.

Lemma aa18_t : forall alpha x n,
  (S (max_FOv alpha)) <= n ->
  var_in_SO alpha x ->
    max_FOv (replace_FOv alpha x (Var n)) = n.
Proof. intros. apply aa18; assumption. Qed.

Lemma aa17 : forall alpha ln n x,
  closed_except alpha x ->
  (S (max_FOv alpha)) <= (min_l ln) ->
  (S (max_l ln)) <= n ->
  free_FO alpha (Var n) = false.
Proof.
  intros alpha ln n x Hc H1 H2.
  apply var_in_SO_free_FO.
  intros H3. apply var_in_SO_max_FOv_gen2 in H3.
  apply H3. pose proof (le_min__max_l ln). lia.
Qed.
Lemma aa20: forall alpha beta,
(max_FOv (instant_cons_empty' alpha beta)) <= (max_FOv (implSO alpha beta)).
Proof.
  intros alpha beta.  unfold instant_cons_empty'.
  apply (PeanoNat.Nat.le_trans _ (max_FOv beta)).
  + apply aa21. apply aa25. apply aa26.
  + rewrite max_FOv_implSO. lia.
Qed.

Lemma instant_cons_empty__' : forall alpha beta,
  instant_cons_empty (implSO alpha beta) =
  implSO alpha (instant_cons_empty' alpha beta).
Proof.
  intros alpha beta.
  unfold instant_cons_empty.
  unfold instant_cons_empty'.
  simpl. rewrite rep_pred_l_implSO.
  rewrite rep_pred_l_list_rel_compl.
  auto.
Qed.

Lemma something3 : forall beta alpha,
  incl (preds_in (instant_cons_empty' alpha beta))
    (preds_in beta).
Proof.
  intros beta alpha.
  unfold instant_cons_empty'.
  rewrite jj8; apply jj10.
Qed.

Lemma preds_in_replace_FOv_A_pre: forall  n l alpha beta,
  preds_in (replace_FOv_A_pre alpha beta l n) =
  preds_in alpha.
Proof.
  induction n; intros l alpha beta. 
    simpl. reflexivity.

    simpl. destruct l. reflexivity.
    rewrite IHn.
    rewrite preds_in_strip_exFO.
    rewrite preds_in_replace_FOv_max_conj.
    apply preds_in_list_closed_exFO.
Qed.

Lemma preds_in_replace_FOv_A : forall l alpha beta,
  preds_in (replace_FOv_A alpha beta l)  = 
  preds_in alpha.
Proof.
  induction l; intros alpha beta; unfold replace_FOv_A.
    simpl. reflexivity.
  
    simpl. rewrite preds_in_replace_FOv_A_pre.
    rewrite preds_in_strip_exFO.
    rewrite preds_in_replace_FOv_max_conj.
    apply preds_in_list_closed_exFO.
Qed. 
