Require Export high_mods SO_sem_mods.
Require Import vsSahlq_proof1 vsSahlq_proof2.
Require Import Monotonicity_lP_SO newnew.
Require Import SO_facts3 Correctness_ST consistent vsS_syn_sem uniform.

Open Scope type_scope.

Fixpoint first_occ_P_n lP P n : nat :=
  match lP with
  | nil => 0
  | cons Q lP' => if predicate_dec P Q then n else first_occ_P_n lP' P (S n)
  end.

Definition first_occ_P lP P := first_occ_P_n lP P 1.

Lemma lem_d35 : forall lP n (l : list FOvariable) llx P l2,
  @at_gen _ l2 (first_occ_P_n lP P (S (S n))) (cons l llx) =
    @at_gen _ l2 (first_occ_P_n lP P (S n)) llx.
Proof.
  induction lP; intros n l llx P l2. reflexivity.
  simpl. destruct (predicate_dec P a); auto.
Qed.

Lemma lem_d35_gen : forall {A : Type} lP n (l : A) llx P l2,
  @at_gen _ l2 (first_occ_P_n lP P (S (S n))) (cons l llx) =
    @at_gen _ l2 (first_occ_P_n lP P (S n)) llx.
Proof.
  induction lP; intros n l llx P l2. reflexivity.
  simpl. destruct (predicate_dec P a); auto.
Qed.

Lemma lem_d44 : forall lP P n,
  ~ In P lP ->
  indicies_l2_pre lP P n = nil.
Proof.
  induction lP; intros P n Hin. auto.
  simpl in *. rewrite predicate_dec_r. apply IHlP; firstorder.
  firstorder.
Qed.

Lemma lem_d28 : forall l P Q W Iv Ip Ir pa,
  ~ P = Q ->
  SOturnst W Iv (alt_Ip Ip pa Q) Ir
    (passing_conj (passing_predSO_l P l)) <->
  SOturnst W Iv Ip Ir (passing_conj (passing_predSO_l P l)).
Proof.
  induction l; intros P Q W Iv Ip Ir  pa Hneq.
    simpl. apply iff_refl.
  simpl passing_conj. case_eq (passing_predSO_l P l).
  + intros Hp. simpl. rewrite alt_Ip_neq. apply iff_refl. 
    auto. 
  + intros beta lbeta Hp. rewrite <- Hp.
    split; intros [H1 H2]; apply conj.
    ++ simpl in *. rewrite alt_Ip_neq in H1; auto.
    ++ simpl in *. fold SOturnst. auto.
       eapply IHl. apply Hneq. apply H2.
    ++ rewrite alt_Ip_neq; auto.
    ++ fold SOturnst. apply IHl; auto.
Qed.

Lemma lem_d29 : forall l2 l3 lP lx P a W Iv Ip Ir,
in_in_FOvar_ll ( l3) (l2) ->
 consistent_lP_lx (lP) (lx) ->
 consistent_lP_llv (lP) (l3) ->
 consistent_lP_llv (lP) (l2) ->
 ex_nil_in_llv (l3) = false ->
SOturnst W Iv (alt_Ip_list Ip (vsS_pa_l Iv l3 lx) lP) Ir
        (passing_conj (passing_predSO_l P a)) ->
SOturnst W Iv (alt_Ip_list Ip (vsS_pa_l Iv l2 lx) lP) Ir
  (passing_conj (passing_predSO_l P a)).
Proof.
  induction l2; intros l3 lP lx P l W Iv Ip Ir Hin Hcon1 Hcon2
                       Hcon3 Hex SOt; simpl in *.
    destruct l3. assumption. inversion Hin.
  destruct lx. simpl in *. destruct l3; assumption.
  simpl in *. destruct lP. rewrite alt_Ip_list_nil in SOt.
      assumption.
  destruct l3. inversion Hin. simpl in *.
  inversion Hin. subst.
  destruct (predicate_dec P p); subst. 
  + apply lem_try23 with (Ip1 := Ip).
    apply lem_try23 with (Ip2 := Ip) in SOt.
    apply lem_try18_pre with (l1 := l0).
    destruct l0; discriminate. all : auto.
  + apply lem_d28; auto. 
    apply lem_d28 in SOt. apply IHl2 with (l3 := l3); auto.
    inversion Hin. auto. 
    apply consistent_lP_lx_cons_rem_gen in Hcon1. assumption.
    apply consistent_lP_llv_cons_rem_gen in Hcon2. assumption.
    apply consistent_lP_llv_cons_rem_gen in Hcon3. assumption.
    destruct l0. discriminate. assumption. all : auto.
Qed.

Lemma lem_try18''_tryinggenlP : forall l l2 l1 lP lP0 lx W Ip Ir Iv ,
   consistent_lP_lx lP lx ->
  consistent_lP_llv lP l1 -> 
  consistent_lP_llv lP l2 -> 
  length lP = length l1 ->
  length lP = length l2 ->
  length lP = length lx ->
  in_in_FOvar_ll l1 l2 ->
  ex_nil_in_llv l1 = false ->
  length lP0 = length l ->
  incl lP0 lP  ->
   SOturnst W Iv (alt_Ip_list Ip (vsS_pa_l Iv l1 lx) lP) Ir 
      (passing_conj (passing_predSO_ll lP0 l)) ->
  SOturnst W Iv (alt_Ip_list Ip (vsS_pa_l Iv l2 lx) lP) Ir 
      (passing_conj (passing_predSO_ll lP0 l)).
Proof.
  induction l; intros l2 l1 lP lP0 lx W Ip Ir Iv Hcon1 Hcon2 Hcon3 Hlength1 
      Hlength2 Hlength3 Hin Hnil Hlength Hin2 SOt.
    destruct lP0; simpl in *; reflexivity.

    destruct lP0. simpl in *. reflexivity.
    simpl in *. case_eq (passing_predSO_ll lP0 l).
      intros Hp. rewrite Hp in *.
      apply passing_predSO_ll_nil in Hp.
      destruct Hp as [Hp | Hp].
        rewrite Hp in *. destruct l2.
        destruct l1.
        simpl in *. assumption. inversion Hin.
        destruct lx. simpl in *. destruct l1. assumption.   
        simpl in *. assumption.
        simpl in *. if_then_else_hyp_dep.
   destruct lP. simpl in *. destruct p. discriminate.
   destruct (predicate_dec p p0). subst.
      destruct l1. discriminate. simpl vsS_pa_l in SOt.
      rewrite alt_Ip_list_cons in SOt.
      apply lem_try18_pre with (l1 := l1).
        destruct l1; discriminate. simpl in Hin.
        inversion Hin. subst. auto.
        apply lem_try23 with 
          (Ip1 := (alt_Ip_list Ip (vsS_pa_l Iv l3 lx) lP)).
        assumption.

        apply lem_d28.
intros HH. inversion HH as [HH']. rewrite HH' in *. contradiction.

        destruct l1. discriminate. simpl vsS_pa_l in SOt.
        rewrite alt_Ip_list_cons in SOt.
        apply lem_d28 in SOt.
        apply lem_d29 with (l3 := l3). inversion Hin. subst. auto.
          apply consistent_lP_lx_cons_rem_gen in Hcon1. assumption.
          apply consistent_lP_llv_cons_rem_gen in Hcon2. assumption.
          apply consistent_lP_llv_cons_rem_gen in Hcon3. assumption.
          simpl in Hnil. destruct l1. discriminate. assumption. assumption.
intros HH. inversion HH as [HH']. rewrite HH' in *. contradiction.

        apply lem_d29 with (l3 := l1); assumption.

(* -- *)

intros beta lbeta Hp. rewrite Hp in *. rewrite <- Hp in *.
 simpl in *. destruct SOt as [SOt1 SOt2]. apply conj.
  apply lem_d29 with (l3 := l1); assumption.

  apply IHl with (l1 := l1); try assumption.
  inversion Hlength. reflexivity. apply incl_lcons in Hin2. auto. 
Qed.

Lemma lem_try9_tryinggenlP : forall lP lx llx0 lP0 W Iv Ip Ir beta gamma,
  ex_nil_in_llv (FOv_att_P_l gamma lP) = false ->
  consistent_lP_lx lP lx ->
  length lP = length lx ->
  length lP0 = length llx0 ->
  incl lP0 lP  ->
  SOturnst W Iv (alt_Ip_list Ip (vsS_pa_l Iv (FOv_att_P_l gamma lP) lx) lP) Ir
      (passing_conj (passing_predSO_ll lP0 llx0)) ->
  SOturnst W Iv (alt_Ip_list Ip (vsS_pa_l Iv (FOv_att_P_l (conjSO beta gamma) lP) lx) lP) Ir
      (passing_conj (passing_predSO_ll lP0 llx0)).
Proof.
  intros until 0. intros Hun Hcon Hlength1 Hlength2 Hin SOt.
  apply lem_try18''_tryinggenlP with (l1 := FOv_att_P_l gamma lP); try assumption.
  apply consistent_lP_llv_FOv_att_P_l.
  apply consistent_lP_llv_FOv_att_P_l.
  apply length_FOv_att_P_l. apply length_FOv_att_P_l.
  apply lem_try33.
Qed.

Lemma is_in_in_FOvar_ll_FOv_att_P_l_conjSO_l : forall lP alpha beta,
  in_in_FOvar_ll (FOv_att_P_l alpha lP) (FOv_att_P_l (conjSO alpha beta) lP).
Proof.
  induction lP; intros alpha beta. constructor. 
  simpl. constructor 2. apply incl_appl.
  apply incl_refl. auto.
Qed.

Lemma lem_try9_tryinggenlP_l : forall lP lx llx0 lP0 W Iv Ip Ir beta gamma,
  ex_nil_in_llv (FOv_att_P_l beta lP) = false ->
  consistent_lP_lx lP lx ->
  length lP = length lx ->
  length lP0 = length llx0 ->
  incl lP0 lP ->
  SOturnst W Iv (alt_Ip_list Ip (vsS_pa_l Iv (FOv_att_P_l beta lP) lx) lP) Ir
      (passing_conj (passing_predSO_ll lP0 llx0)) ->
  SOturnst W Iv (alt_Ip_list Ip (vsS_pa_l Iv (FOv_att_P_l (conjSO beta gamma) lP) lx) lP) Ir
      (passing_conj (passing_predSO_ll lP0 llx0)).
Proof.
  intros until 0. intros  Hcon Hlength1 Hlength2 Hin SOt.
  apply lem_try18''_tryinggenlP with (l1 := FOv_att_P_l beta lP); try assumption.
  apply consistent_lP_llv_FOv_att_P_l.
  apply consistent_lP_llv_FOv_att_P_l.
  apply length_FOv_att_P_l. apply length_FOv_att_P_l.
  apply is_in_in_FOvar_ll_FOv_att_P_l_conjSO_l.
Qed.

Lemma cap_pred_nil : forall l,
  cap_pred l nil = nil.
Proof.
  induction l. reflexivity.
  simpl. destruct (in_predicate_dec a nil);
  firstorder. 
Qed.

Lemma incl_cap_pred_incl : forall l3 l2 l1,
  incl l1 l2  ->
  incl l3 (cap_pred l2 l1) <->
  incl l3 l1.
Proof.
  induction l3; intros l2 l1 Hin. firstorder. 
  simpl. split; intros H; (apply incl_cons; [apply incl_hd in H| ]).
  apply in_pred_cap_pred_t in H. firstorder.
  apply incl_lcons in H. apply IHl3 in Hin; auto. 
  apply Hin; auto.
  apply in_pred_cap_pred; auto. apply IHl3; auto.
  apply incl_lcons in H. auto. 
Qed.

Lemma lem_d61' : forall atm atm2 lP lP2 x  (W : Set) Iv Ip Ir (pa2 : W -> Prop),
  incl lP (preds_in atm) ->
  incl (preds_in atm) lP ->
  incl lP lP2 ->
  AT atm = true ->
  AT atm2 = true ->
  SOturnst W Iv (alt_Ip_list Ip
    (vsS_pa_l Iv (FOv_att_P_l atm2 lP) (list_var (length lP) x)) lP) Ir atm ->
  SOturnst W Iv (alt_Ip_list Ip 
    (vsS_pa_l Iv (FOv_att_P_l atm2 lP2) (list_var (length lP2) x)) lP2) Ir atm.
Proof.
  induction atm; intros atm0 lP lP2 x W Iv Ip Ir pa2 Hin1 Hin2 Hin3 Hat Hat0 SOt; try discriminate.
  + simpl in *. if_then_else_hyp_dep.
    rewrite lemma_try4; auto. rewrite lemma_try4 in SOt; auto.
    destruct (in_dec predicate_dec p lP2). auto. apply incl_hd in Hin2. auto.
    apply incl_hd in Hin2. auto. apply incl_hd in Hin2. eapply in_incl. apply Hin2. auto.
  + pose proof (AT_conjSO_l _ _ Hat).
    pose proof (AT_conjSO_r _ _ Hat).
    simpl in *. destruct SOt as [SOt1 SOt2].
    pose proof (incl_app_rev_r _ _ _ _ Hin2) as Hin2a.
    pose proof (incl_app_rev_l _ _ _ _ Hin2) as Hin2b.
    apply conj. apply IHatm1 with (lP := cap_pred lP (preds_in atm1)); try assumption.
      apply incl_cap_pred_add. apply incl_refl.
      rewrite incl_cap_pred_incl. apply incl_refl.
        assumption.
      apply incl_cap_pred_add.
      apply (incl_trans _ _ _ _ Hin2b Hin3 ).

      apply lem_a21; assumption.

apply IHatm2 with (lP := cap_pred lP (preds_in atm2)); try assumption.
      apply incl_cap_pred_add. apply incl_refl.
      rewrite incl_cap_pred_incl. apply incl_refl.
        assumption.
      apply incl_cap_pred_add.
      apply (incl_trans _ _ _ _ Hin2a Hin3 ).

      apply lem_a21; assumption.
Qed.

Lemma lem_d58 : forall lP2 lx2 lP lx P x y,
  length lP = length lx ->
  length lP2 = length lx2 ->
  In P lP2 ->
  consistent_lP_lx (cons P (app lP2 lP)) (cons x (app lx2 lx)) ->
  @at_gen _ y (first_occ_P lP2 P) lx2 = x.
Proof.
  induction lP2; intros lx2 lP lx P x y Hl1 Hl2 Hin1 Hcon. 
    inversion Hin1.
  destruct lx2. discriminate. simpl in *.
  unfold first_occ_P. simpl in *.
  destruct (predicate_dec P a); subst; simpl.
  + apply lem_try26 in Hcon. auto. 
  + rewrite lem_d35_gen. apply IHlP2 with (lP := lP) (lx := lx);
    auto. destruct Hin1. subst. contradiction. auto. 
    apply consistent_lP_lx_cons_rem in Hcon. assumption.
Qed.

Fixpoint cap_pred_lx l1 l2 (lx : list FOvariable) :=
  match l1, lx with
  | nil, _ => nil
  | _, nil => nil
  | cons P l1', cons x lx' => if in_predicate_dec P l2 then cons x (cap_pred_lx l1' l2 lx')
          else cap_pred_lx l1' l2 lx'
  end.

Lemma lem_d61 : forall lP lx lP2,
  length lP = length lx ->
length (cap_pred lP lP2) = length (cap_pred_lx lP lP2 lx).
Proof.
  induction lP; intros lx lP2 H.
    simpl in *. reflexivity.

    simpl in *. destruct lx. discriminate.
    inversion H. dest_in_pred_dec_blind.
      simpl. rewrite IHlP with (lx := lx).
      reflexivity. assumption.

      apply IHlP. assumption.
Qed.

Lemma lem_g1 : forall lP2 lP1 P Q lx2 lx1 f b n,
length lP2 = length lx2 ->
 ind_FOv (indicies_l2 (lP2 ++ P :: lP1) Q) (lx2 ++ f :: lx1) =
       repeat b n ->
  ind_FOv (indicies_l2 (app (cons P lP2) lP1) Q) (app (cons f lx2) lx1) = repeat b n.
Proof.
  induction lP2; intros lP1 P Q lx2 lx1 f b n Hl Hind.
    simpl. destruct lx2. simpl in *.  assumption.
    discriminate.

    destruct lx2. discriminate.
    inversion Hl as [Hl'].
    unfold indicies_l2 in *. simpl in *.
    
    destruct (predicate_dec Q P);
    destruct (predicate_dec Q a); simpl in *; subst.
    + destruct n. discriminate.
      inversion Hind as [[H1 H2]]; subst.
      rewrite ind_FOv_ind_l2_pre_cons in H2. apply IHlP2 in H2.
      rewrite predicate_dec_l in H2; auto.  simpl in *.
      rewrite ind_FOv_ind_l2_pre_cons in *. 
      destruct n. discriminate.
      inversion H2 as [[H3 H4]]; subst.
      rewrite ind_FOv_ind_l2_pre_cons.
      rewrite H4. reflexivity. auto.
    + simpl. do 2 rewrite ind_FOv_ind_l2_pre_cons in *.
      apply IHlP2 in Hind. pred_dec_l_rep. simpl in *.
      destruct n. discriminate. inversion Hind. subst.
      rewrite ind_FOv_ind_l2_pre_cons in H1. rewrite H1. auto. auto.
    + simpl in *. rewrite ind_FOv_ind_l2_pre_cons in Hind.
      do 2 rewrite ind_FOv_ind_l2_pre_cons. destruct n. discriminate.
      inversion Hind as [[H1 H2]].
      apply IHlP2 in H2.  rewrite predicate_dec_r in H2. subst.
      rewrite ind_FOv_ind_l2_pre_cons in H2. rewrite H2. auto.
      auto. auto.
    + simpl in *. rewrite ind_FOv_ind_l2_pre_cons in Hind.
      do 2 rewrite ind_FOv_ind_l2_pre_cons.
      apply IHlP2 in Hind. rewrite predicate_dec_r in Hind.
      rewrite ind_FOv_ind_l2_pre_cons in Hind. rewrite Hind.
      all : auto.
Qed.

Lemma lem_f2 : forall lP1 lP2 lx1 lx2 Q b n,
length lP1 = length lx1 ->
length lP2 = length lx2 ->
ind_FOv (indicies_l2 (app lP2 lP1) Q) (app lx2 lx1) = repeat b n ->
ind_FOv (indicies_l2 (lP1 ++ lP2) Q) (lx1 ++ lx2) = repeat b n.
Proof.
  induction lP1; intros lP2 lx1 lx2 Q b n Hl1 Hl2 Hind.
    destruct lx1. simpl in *. do 2 rewrite List.app_nil_r in Hind.
    assumption.
    discriminate.

    destruct lx1. discriminate.
    simpl in *. inversion Hl1 as [Hl1'].
    unfold indicies_l2 in*. simpl in *.
    destruct (predicate_dec Q a). subst. simpl.
    rewrite ind_FOv_ind_l2_pre_cons. 
    apply lem_g1 in Hind. unfold indicies_l2 in *. simpl in Hind.
    pred_dec_l_rep. simpl in *. rewrite ind_FOv_ind_l2_pre_cons in Hind. 
    destruct n. discriminate. inversion Hind. apply IHlP1 in H1. 
    rewrite H1. all : auto. 

    rewrite ind_FOv_ind_l2_pre_cons. apply IHlP1; try assumption.
    apply lem_g1 in Hind. unfold indicies_l2 in *. simpl in *.
    rewrite predicate_dec_r in Hind; auto. 
    rewrite ind_FOv_ind_l2_pre_cons in Hind.
    assumption. assumption.
Qed.

Lemma lem_d70_pre_pre_pre : forall lP lx Q a n,
length lP = length lx ->
  ind_FOv (indicies_l2 ( lP) Q) ( lx) = repeat a n ->
exists  (n' : nat),
  ind_FOv (indicies_l2 ((lP ++ lP)%list) Q) ((lx ++ lx)%list) = repeat a n'.
Proof.
  induction lP; intros lx Q b n Hl Hind. exists 0. auto.
  simpl. unfold indicies_l2 in *. simpl in *.
  destruct (predicate_dec Q a); subst.
  + simpl in *. destruct lx. discriminate.
    simpl. destruct n. discriminate. inversion Hind as [[H1 H2]].
    rewrite ind_FOv_ind_l2_pre_cons in *.
    simpl in Hind.
    inversion Hl as [Hl'].
    destruct (IHlP _ _ _ _ Hl' H2) as [n' H'].
    exists (S (S n')).
    pose proof lem_f2 as H. unfold indicies_l2 in H.
    rewrite H with (b := b) (n := (S (n'))); try assumption. reflexivity.
    simpl. pred_dec_l_rep. simpl.
    rewrite ind_FOv_ind_l2_pre_cons. rewrite H'. auto.
  + destruct lx. discriminate.
    inversion Hl as [Hl'].
    rewrite ind_FOv_ind_l2_pre_cons in Hind.
    simpl in *. destruct (IHlP _ _ _ _ Hl' Hind) as [n' H].
    exists n'. pose proof lem_f2 as H2.
    unfold indicies_l2 in H2. rewrite ind_FOv_ind_l2_pre_cons.
    apply H2; try assumption. simpl.  rewrite predicate_dec_r; auto.
    rewrite ind_FOv_ind_l2_pre_cons. assumption.
Qed.

Lemma lem_d70_pre_pre : forall lP lx P Q f a n,
length lP = length lx ->
  ind_FOv (indicies_l2 (P :: lP) Q) (f :: lx) = repeat a n ->
exists  (n' : nat),
  ind_FOv (indicies_l2 (P :: (lP ++ lP)%list) Q) (f :: (lx ++ lx)%list) = repeat a n'.
Proof.
  intros lP lx P Q f a n Hl Hind.
  unfold indicies_l2 in *. simpl in *.
  destruct (predicate_dec Q P); subst.
  + simpl in *. destruct n. discriminate.
    simpl in Hind . inversion Hind as [[H1 H2]].
    rewrite ind_FOv_ind_l2_pre_cons in *.
    apply lem_d70_pre_pre_pre in H2. unfold indicies_l2 in H2.
    destruct H2 as [n' H2']. exists (S n').
    rewrite H2'. reflexivity. assumption.
  + rewrite ind_FOv_ind_l2_pre_cons in *.
    apply lem_d70_pre_pre_pre in Hind. unfold indicies_l2 in *.
    apply Hind. assumption.
Qed.

Lemma lem_d70_pre : forall lP lx P f Q,
 length lP = length lx ->
consistent_lP_lx_P (P :: lP) (f :: lx) Q ->
consistent_lP_lx_P (P :: (lP ++ lP)%list) (f :: (lx ++ lx)%list) Q.
Proof.
  intros lP lx P f Q Hl Hcon.
  unfold consistent_lP_lx_P in *.
  unfold is_constant in *.
  destruct Hcon as [a [n H]].
  exists a. 
  apply lem_d70_pre_pre in H.
  destruct H as [n' H'].
  exists n'. all : assumption.
Qed.

Lemma lem_d70 : forall lP lx P f,
 length lP = length lx ->
consistent_lP_lx (P :: lP) (f :: lx) ->
consistent_lP_lx (P :: (lP ++ lP)%list) (f :: (lx ++ lx)%list).
Proof.
  intros until 0. intros H1 H2 Q.
  apply lem_d70_pre. assumption. apply H2.
Qed.

Lemma lem_a26' : forall (lP : list predicate) (Q : predicate) (atm : SecOrder) 
  (W : Set) (Iv : FOvariable -> W) lx (x : FOvariable) (pa2 : W -> Prop),
  length lP = length lx ->
  consistent_lP_lx lP lx ->
exists (n : nat),
  @ind_gen (W -> Prop) pa2 (indicies_l2_pre lP Q 0)
    (vsS_pa_l Iv (FOv_att_P_l atm lP) lx) = 
  repeat (pa_l_disj_gen Iv (FOv_att_P atm Q) (@at_gen _ x (first_occ_P lP Q) lx)) n.
Proof.
  induction lP; intros Q atm W Iv lx x pa2 Hl Hcon. exists 0. auto.
  simpl. destruct lx. discriminate.
  inversion Hl as [Hl'].
  simpl. destruct (IHlP Q atm W Iv lx x pa2 Hl'
                        (consistent_lP_lx_cons_rem_gen _ _ _ _ Hcon)) as [n H].
  destruct (predicate_dec Q a). simpl in *.
  + exists (S n). simpl. rewrite ind_gen_pre_cons. rewrite H.
    unfold first_occ_P in *. simpl in *.  subst. pred_dec_l_rep.
    auto. simpl. destruct (in_dec predicate_dec a lP).
    pose proof lem_d58 as H2. unfold first_occ_P in H2.
    rewrite H2 with (lP := lP) (lx := lx) (x := f); auto. 
    apply lem_d70; assumption.
    rewrite lem_d44 in H. simpl in *. destruct n. 2 : discriminate.
    simpl. reflexivity. assumption.
  + exists n. rewrite ind_gen_pre_cons.
    unfold first_occ_P. simpl. rewrite predicate_dec_r; auto.
    rewrite lem_d35_gen. assumption.
Qed.

Lemma lem_a25' : forall lP Q atm W Iv lx pa2 (x : FOvariable),
  length lP = length lx ->
  consistent_lP_lx lP lx ->
  @consistent_lP_lpa_P W pa2 lP 
    (vsS_pa_l Iv (FOv_att_P_l atm lP) 
      lx) Q.
Proof.
  unfold consistent_lP_lpa_P. unfold is_constant.
  unfold indicies_l2.
  intros lP Q atm W Iv lx pa2 x H1 H2.
   exists (pa_l_disj_gen Iv (FOv_att_P atm Q) (@at_gen _ x (first_occ_P lP Q) lx)).
  apply lem_a26'; assumption.
Qed.

Lemma lem_a27' : forall lP atm W Iv lx pa2,
  length lP = length lx ->
  consistent_lP_lx lP lx ->
  @consistent_lP_lpa W pa2 lP 
    (vsS_pa_l Iv (FOv_att_P_l atm lP) 
      lx).
Proof.
  unfold consistent_lP_lpa. intros.
  apply lem_a25'; try assumption. apply (Var 1). 
Qed.

Lemma lem_a31' : forall lP l Q (W : Set) Iv atm lx (x : FOvariable) (pa2 : W -> Prop),
length lP = length lx ->
consistent_lP_lx lP lx ->
exists (n : nat),
   @ind_gen _ pa2 (indicies_l2_pre (cap_pred lP l) Q 0)
     (vsS_pa_l Iv (FOv_att_P_l atm (cap_pred lP l))
       (cap_pred_lx lP l lx)) = 
   repeat (pa_l_disj_gen Iv (FOv_att_P atm Q) (@at_gen _ x (first_occ_P lP Q) lx)) n.
Proof.
  induction lP; intros l Q W Iv atm lx x pa2 Hl Hcon. exists 0. auto.
  simpl. destruct lx. discriminate. inversion Hl as [Hl'].
  destruct (IHlP l Q W Iv atm lx f pa2 Hl') as [n H].
  apply consistent_lP_lx_cons_rem_gen in Hcon. assumption.
  destruct (in_predicate_dec a l).
  + destruct (predicate_dec Q a); subst.
    ++ simpl. pred_dec_l_rep. simpl. rewrite ind_gen_pre_cons.
       exists (S n).  rewrite H. 
       unfold first_occ_P. simpl. 
       simpl. pose proof lem_d58 as H2. unfold first_occ_P in H2.
       pred_dec_l_rep. simpl.
       destruct (in_predicate_dec a lP).
       rewrite H2 with (lP := lP) (lx := lx) (x := f); try assumption.
       reflexivity.        
       apply lem_d70; assumption.

       rewrite (lem_d44 (cap_pred lP l) a) in *. simpl in *.
       destruct n. 2 : discriminate.
       simpl. reflexivity. 
       apply in_pred_cap_pred_f1. assumption.
    ++ destruct (IHlP l Q W Iv atm lx x pa2 Hl') as [n' H'].
       apply consistent_lP_lx_cons_rem_gen in Hcon. assumption.
       exists n'. simpl. rewrite predicate_dec_r; auto.
       simpl. rewrite ind_gen_pre_cons.
       unfold first_occ_P in *. simpl. rewrite predicate_dec_r; auto.
       rewrite lem_d35_gen. rewrite H'. reflexivity.
  + simpl. unfold first_occ_P. simpl.
    destruct (predicate_dec Q a); subst.
    ++ rewrite (lem_d44 (cap_pred lP l) a) in *.
       simpl in *. exists 0. reflexivity.
       apply in_cap_pred. assumption.
       apply in_cap_pred. assumption.
    ++ rewrite lem_d35_gen. unfold first_occ_P in IHlP.
       apply IHlP; try assumption. apply consistent_lP_lx_cons_rem_gen in Hcon.
       assumption.
Qed.

Lemma lem_a30' : forall lP l Q (W : Set) Iv atm lx (pa2 : W -> Prop) (x : FOvariable),
length lP = length lx ->
consistent_lP_lx lP lx ->
is_constant (@ind_gen _ pa2 (indicies_l2 (cap_pred lP l) Q)
  (vsS_pa_l Iv (FOv_att_P_l atm (cap_pred lP l)) 
  (cap_pred_lx lP l lx))).
Proof.
  unfold is_constant.
  unfold indicies_l2.
  intros. exists (pa_l_disj_gen Iv (FOv_att_P atm Q) (@at_gen _ x (first_occ_P lP Q) lx)).
  apply lem_a31'; assumption.
Qed.
 
Lemma lem_a29' : forall lP Q l atm (W : Set) Iv pa2 lx ,
length lP = length lx ->
consistent_lP_lx lP lx ->
@consistent_lP_lpa_P W pa2 (cap_pred lP l)
 (vsS_pa_l Iv (FOv_att_P_l atm (cap_pred lP l))
        (cap_pred_lx lP l lx)) Q.
Proof.
  unfold consistent_lP_lpa_P.
  intros.
  apply lem_a30'; try assumption.
  apply (Var 1).
Qed.

 Lemma lem_a28' : forall lP l atm (W : Set) Iv pa2 lx ,
length lP = length lx ->
consistent_lP_lx lP lx ->
@consistent_lP_lpa W pa2 (cap_pred lP l)
 (vsS_pa_l Iv (FOv_att_P_l atm (cap_pred lP l))
        (cap_pred_lx lP l lx)).
Proof.
  unfold consistent_lP_lpa.
  intros. apply lem_a29'; assumption.
Qed. 

Lemma lem_a21'' : forall lP atm beta lx W Iv Ip Ir,
AT atm = true ->
length lP = length lx ->
consistent_lP_lx lP lx ->
SOturnst W Iv (alt_Ip_list Ip
   (vsS_pa_l Iv (FOv_att_P_l atm lP) lx) lP) Ir beta <->
SOturnst W Iv
  (alt_Ip_list Ip
     (vsS_pa_l Iv (FOv_att_P_l atm (cap_pred lP (preds_in beta)))
        (cap_pred_lx lP (preds_in beta) lx))
     (cap_pred lP (preds_in beta))) Ir beta.
Proof.
  induction lP; intros atm beta lx W Iv Ip Ir Hat Hl Hcon.
    simpl in *. apply iff_refl.  
  + destruct lx. discriminate.
    inversion Hl. simpl in *.
    destruct (in_predicate_dec a (preds_in beta)).
    ++ simpl. rewrite alt_Ip__list_consistent_lP_lpa with (pa2 := pa_t).
       rewrite alt_Ip__list_consistent_lP_lpa with (pa2 := pa_t).
       apply IHlP; auto.
       apply consistent_lP_lx_cons_rem_gen in Hcon. assumption.

       pose proof (lem_a28' (cons a lP) (preds_in beta) atm W Iv pa_t (cons f lx)) as HH.
       simpl in HH. rewrite in_predicate_dec_l in HH.
       simpl in *. rewrite in_predicate_dec_l in HH. apply HH; assumption.
       all:auto.
       pose proof (lem_a27' (cons a lP) atm W Iv(cons f lx)) as H. simpl in H.
       apply H; assumption.

    ++ split; intros SOt.
      apply P_not_occ_alt in SOt. apply IHlP; try assumption.
apply consistent_lP_lx_cons_rem_gen in Hcon. assumption. auto.

      apply P_not_occ_alt. auto.
 apply IHlP; try assumption.
apply consistent_lP_lx_cons_rem_gen in Hcon. assumption.
Qed.

Lemma lem_d62 : forall lP P x y W Iv Ip,
In P lP ->
@alt_Ip_list W Ip
  (vsS_pa_l Iv (FOv_att_P_l (predSO P x) lP)
     (list_var (length lP) y)) lP P (Iv x).
Proof.
  induction lP; intros P x y W Iv Ip Hin. inversion Hin. 
  simpl in *. destruct (predicate_dec a P); subst.
  + rewrite alt_Ip_eq.
    destruct (FOvariable_dec x y). constructor. firstorder.
    constructor 2. firstorder. simpl. auto.
  + destruct Hin. contradiction. rewrite alt_Ip_neq.
    apply IHlP; auto. auto.
Qed.

Lemma lem118'_incl : forall atm1,
AT atm1 = true ->
incl (atm_passing_predSO_ll_lP atm1) (preds_in atm1).
Proof.
  induction atm1; intros Hat; try discriminate.
  simpl. destruct (in_predicate_dec p (p :: nil)); firstorder.
  pose proof (AT_conjSO_l _ _ Hat).
  pose proof (AT_conjSO_r _ _ Hat).
  simpl. apply incl_app_gen; auto.
Qed.

Lemma ex_nil_in_llv_app_f_FOv_att_P_l : forall l1 l2 alpha,
  ex_nil_in_llv (FOv_att_P_l alpha l1) = false ->
  ex_nil_in_llv (FOv_att_P_l alpha l2) = false ->
  ex_nil_in_llv (FOv_att_P_l alpha (app l1 l2)) = false.
Proof.
  induction l1; intros l2 alpha H1 H2.
    simpl. assumption.

    simpl. case_eq (FOv_att_P alpha a).
      intros H. simpl in H1. rewrite H in *. discriminate.

      intros x lx Hlx.  simpl in H1. rewrite Hlx in H1.
      apply IHl1; assumption.
Qed.

Lemma lem_try40_l : forall lP beta gamma,
  ex_nil_in_llv (FOv_att_P_l beta lP) = false ->
  ex_nil_in_llv (FOv_att_P_l (conjSO beta gamma) lP) = false.
Proof.
  induction lP; intros beta gamma Hex.
    simpl in *. reflexivity.

    simpl in *.
    case_eq (FOv_att_P beta a). intros Hg. rewrite Hg in *.
      discriminate.

      intros x lx Hlx. rewrite <- Hlx.
      case_eq (app (FOv_att_P beta a) (FOv_att_P gamma a)).
        intros H. apply app_eq_nil in H. rewrite Hlx in *.
        destruct H. discriminate.

        intros y ly Hly.
        apply IHlP. rewrite Hlx in Hex. assumption.
Qed.

Lemma ex_nil_in_llv_FOv_att_P_l_AT : forall atm,
AT atm = true ->
ex_nil_in_llv (FOv_att_P_l atm (preds_in atm)) = false.
Proof.
  induction atm; intros Hat; try discriminate.
  simpl. rewrite predicate_dec_l; auto.
  pose proof (AT_conjSO_l _ _ Hat).
  pose proof (AT_conjSO_r _ _ Hat).
  simpl. apply ex_nil_in_llv_app_f_FOv_att_P_l.
  apply lem_try40_l. apply IHatm1. assumption.
  apply lem_try40. apply IHatm2. assumption.
Qed.

Lemma hopeful9'_further' : forall atm lP x (y:FOvariable) (W : Set) Iv Ip Ir (pa2 : W -> Prop),
  AT atm = true ->
incl (preds_in atm) lP ->
SOturnst W Iv
  (alt_Ip_list Ip
     (vsS_pa_l Iv (FOv_att_P_l atm lP) (list_var (length lP) x)) lP) Ir
  atm.
Proof.
  induction atm; intros lP x y W Iv Ip Ir pa2 Hat Hin; try discriminate.
  + simpl in *. apply incl_hd in Hin. apply lem_d62. auto.
  + pose proof (AT_conjSO_l _ _ Hat) as Hat1.
    pose proof (AT_conjSO_r _ _ Hat) as Hat2.
    simpl. apply conj.
    apply lem_d61' with (lP := (preds_in atm1)). apply pa_t.
    apply incl_refl.
    apply incl_refl.
    simpl in Hin. apply incl_app_rev_l in Hin. all: auto. 
    apply lem118'_equiv; try assumption.
    apply lem_try9_tryinggenlP_l.
    apply ex_nil_in_llv_FOv_att_P_l_AT. assumption.
    apply consistent_lP_lx_list_var.
    rewrite list_var_length. reflexivity.

apply lem118'_length. assumption.

apply lem118'_incl. assumption.

      apply (lem118'_equiv atm1). assumption.
      apply IHatm1; try assumption.
apply incl_refl.

      apply lem_d61' with (lP := (preds_in atm2)). apply pa_t.
apply incl_refl.
apply incl_refl.


simpl in Hin. apply incl_app_rev_r in Hin. all: auto.

      apply lem118'_equiv; try assumption.
      apply lem_try9_tryinggenlP.

apply ex_nil_in_llv_FOv_att_P_l_AT. assumption.

apply consistent_lP_lx_list_var.

rewrite list_var_length. reflexivity.

apply lem118'_length. assumption.

apply lem118'_incl. assumption.

      apply (lem118'_equiv atm2). assumption.
      apply IHatm2; try assumption.
apply incl_refl.
Qed.

Lemma incl_preds_in_passing_predSO_l : forall lx lP P,
  ~ lx = nil ->
  incl (preds_in (passing_conj (passing_predSO_l P lx))) lP <->
  In P lP.
Proof.
  induction lx; intros lP P Hnil. contradiction.
  simpl in *. case_eq (passing_predSO_l P lx).
  + intros Hp. simpl in *. split; intros H.
    apply incl_hd in H. auto. apply incl_cons; auto. firstorder.
  + intros beta lbeta Hp. rewrite <- Hp.
    simpl. split; intros H. apply incl_hd in H. auto. 
    apply incl_cons. auto. apply IHlx. destruct lx; discriminate.
    auto.
Qed.

Lemma incl_preds_in_passing_predSO_l2 : forall l0 l a,
 ~ l0 = nil -> ~ In a l <->
~ incl (preds_in (passing_conj (passing_predSO_l a l0))) l.
Proof.
  intros l1 l2 P H1. split; intros H2 H3; apply H2.
  apply incl_preds_in_passing_predSO_l in H3; auto.
  apply incl_preds_in_passing_predSO_l; auto.
Qed.

Lemma incl_preds_in_passing_predSO_ll : forall lP llx l,
  length lP = length llx ->
  ex_nil_in_llv llx = false ->
  incl (preds_in (passing_conj (passing_predSO_ll lP llx))) l <->
  incl lP l.
Proof.
  induction lP; intros llx l Hl Hex. reflexivity.
  simpl in *. destruct llx. discriminate.
  simpl. case_eq (passing_predSO_ll lP llx).
    intros Hp. destruct (in_predicate_dec a l). 
      destruct lP. 2 : (destruct llx; discriminate).
      destruct l0. simpl. split; intros HH.
      apply incl_cons; firstorder. firstorder.
      rewrite incl_preds_in_passing_predSO_l; auto.
      split; intros HH. apply incl_cons; auto. firstorder.
      auto. discriminate.

      destruct l0. simpl in *. discriminate.
      split; intros HH.
      apply incl_preds_in_passing_predSO_l2 in HH; auto. 
      contradiction. discriminate.
      apply incl_hd in HH. contradiction.

    intros beta lbeta Hp. rewrite <- Hp. simpl.
    inversion Hl as [Hl'].
    simpl in Hex. destruct l0. discriminate.
    split; intros HH. pose proof (incl_app_rev_l _ _ _ _ HH) as HH1. 
    pose proof (incl_app_rev_r _ _ _ _ HH) as HH2.
    simpl in HH1. destruct (passing_predSO_l a l0);
    simpl in *; apply incl_hd in HH1; apply incl_cons; auto.
    apply IHlP in HH2; auto.     apply IHlP in HH2; auto.

    apply incl_app. apply incl_preds_in_passing_predSO_l.
    discriminate. apply incl_hd in HH. auto.
    apply IHlP; auto. apply incl_lcons in HH. auto.
Qed.

Lemma lem_d71 : forall lP2 l x,
(cap_pred_lx lP2 l (list_var (length lP2) x)) =
  list_var (length (cap_pred lP2 l)) x.
Proof.
  induction lP2; intros l x. reflexivity.
  simpl. destruct (in_predicate_dec a l);
           simpl; rewrite IHlP2; auto.
Qed.

Lemma lem_a20_mono'' : forall lP lP2 llx2 W Iv Ip Ir pa_l beta atm x pa2,
  atm = passing_conj (passing_predSO_ll lP2 llx2) ->
  ~ lP2 = nil ->
ex_nil_in_llv llx2 = false ->
ex_FOvar_var_ll x (FOv_att_P_l atm lP) = false ->
~ cap_pred lP (preds_in beta) = nil ->
  length lP2 = length llx2 ->
  @consistent_lP_lpa W pa2 lP pa_l ->
  length lP = length pa_l ->
  SOturnst W Iv (alt_Ip_list Ip pa_l lP) Ir atm ->
  uniform_pos_SO beta ->
  incl (preds_in beta) (preds_in atm) ->
SOturnst W Iv
        (alt_Ip_list Ip
           (vsS_pa_l Iv (FOv_att_P_l atm lP) (list_var (length lP) x)) lP)
        Ir beta ->
SOturnst W Iv (alt_Ip_list Ip pa_l lP) Ir beta.
Proof.
  intros lP lP2 llx W Iv Ip Ir lpa beta atm x pa2 HAT Hnil Hex Hex2 Hcap Hlength Hcon Hlength2 SOt Hun Hin1 SOt2.
  pose proof (monotonicity_lP_SO beta (cap_pred lP (preds_in beta))) as H.
   assert ((forall P : predicate, In P (cap_pred lP (preds_in beta)) ->
     Pred_in_SO beta P) )
    as remembertoassume.
    intros P Hin3. apply in_pred_cap_pred_t in Hin3. firstorder. 

  apply (lem_a19 lP _ _ _ _ lpa beta pa2); auto.
     destruct H as [H1 H2]. clear H2.
    assert (lP_is_pos_SO beta (cap_pred lP (preds_in beta))) as HlPpos.
      apply lP_is_pos_SO_uni; try assumption.

    unfold alpha_upward_monotone_lP in H1.
    specialize (H1 HlPpos W Iv Ir (alt_Ip_list Ip
            (vsS_pa_l Iv (FOv_att_P_l atm (cap_pred lP (preds_in beta))) 
            (list_var (length (cap_pred lP (preds_in beta))) x))
            (cap_pred lP (preds_in beta)))
     (alt_Ip_list Ip (cap_pred_lpa lpa lP (preds_in beta))
     (cap_pred lP (preds_in beta)))).

    apply H1.  

    assert (~ llx = nil) as Hnil2.
      destruct llx. destruct lP2. contradiction (Hnil eq_refl).
      discriminate. discriminate.
    assert (AT atm = true) as HAT2.
      rewrite HAT. apply AT_passing_predSO_ll; try assumption.

    apply lemma_try7_again with (Ir := Ir) (pa2 := pa2) (lP0 := lP) (pa_l0 := lpa).
    all : try assumption.

    apply incl_cap_pred_add. assumption.

     apply lem_a23. assumption.
    apply incl_cap_pred_refl.

    apply consistent_lP_lpa_cap_pred_lpa_app. assumption. assumption.

    apply length_cap_pred__lpa. assumption.

    apply consistent_lP_lpa_cap_pred. assumption. assumption.

    apply lem_a21; try assumption.
    rewrite HAT. apply AT_passing_predSO_ll.
      assumption.
      destruct llx. destruct lP2. contradiction (Hnil eq_refl). discriminate.
      discriminate. assumption.

Qed.


Lemma hopeful8_lP_again_mono_tryinggenlP: forall lP lP2 rel atm beta x llx W Iv Ip Ir pa2,
  incl lP lP2  ->
  REL rel = true ->
  atm = (passing_conj (passing_predSO_ll lP llx)) ->
  incl (preds_in beta) (preds_in (conjSO rel atm)) ->
  incl lP (preds_in (conjSO rel atm)) ->
  ex_FOvar_var_ll x (FOv_att_P_l atm lP2) = false ->
  length lP = length llx ->
  ex_nil_in_llv llx = false ->
  uniform_pos_SO beta ->
SOturnst W Iv (alt_Ip_list Ip
  (vsS_pa_l Iv (FOv_att_P_l (conjSO rel atm) lP2) (list_var (length lP2) x)) lP2) Ir
  (implSO (conjSO rel atm) beta) ->
  (forall pa_l,
      length lP2 = length pa_l ->
      @consistent_lP_lpa _ pa2 lP2 pa_l ->
    SOturnst W Iv (alt_Ip_list Ip pa_l lP2) Ir (implSO (conjSO rel atm) beta)).
Proof.
   intros lP lP2 rel atm beta  x llx2 W Iv Ip Ir pa2 Hin3 HREL HAT Hin1 Hin2 Hex Hl1 Hex2 Hun SOt pa_l Hnil Hcon SOt1.
  case_eq lP2. intros HlP; rewrite HlP in *. simpl in *. 
    rewrite alt_Ip_list_nil in *. apply SOt. assumption.
  intros P lP' HlP. rewrite <- HlP.
  rewrite SOturnst_implSO in SOt.
  rewrite SOturnst_conjSO in *.
  destruct SOt1 as [SOt1 SOt2].
  rewrite alt_Ip_rel with (Ip2 := Ip)  in SOt1 .
  rewrite alt_Ip_rel with (Ip2 := Ip) in SOt.
  assert (~ Pred_in_SO rel P) as Hpocc. apply P_occurs_in_rel. auto.
  assert (SOturnst W Iv Ip Ir rel /\
      SOturnst W Iv
        (alt_Ip_list Ip
           (vsS_pa_l Iv (FOv_att_P_l (conjSO rel atm) lP2) (list_var (length lP2) x)) lP2)
        Ir atm) as Hass.
    apply conj. assumption.
      rewrite FOv_att_P_l_conjSO_rel. 2 : assumption.
      rewrite HAT.

case_eq lP.
  intros Hp. simpl. reflexivity.
intros P'' lP'' HlP''. rewrite <- HlP''.
assert (AT (passing_conj (passing_predSO_ll lP llx2)) = true) as Hass.
  apply AT_passing_predSO_ll. rewrite HlP''. discriminate.
  rewrite HlP'' in *. destruct llx2; discriminate.
  assumption.
apply lem_a21''; try assumption.
 rewrite list_var_length. reflexivity.

   apply consistent_lP_lx_list_var.

  rewrite lem_d71.
apply hopeful9'_further'; try assumption.

  rewrite incl_cap_pred_incl.
  apply incl_refl.
  rewrite incl_preds_in_passing_predSO_ll; assumption.

  specialize (SOt Hass). clear Hass. simpl in Hin1.
  simpl in *. rewrite (preds_in_rel rel) in *. simpl in *.
  rewrite FOv_att_P_l_conjSO_rel in SOt.
  case_eq (cap_pred lP2 (preds_in beta)).
    intros Hcap.
    apply alt_Ip_list_cap_pred_nil. assumption.
    apply alt_Ip_list_cap_pred_nil in SOt; assumption.

    intros Q lQ HlQ. 
case_eq lP.
  intros Hp. rewrite Hp in *. simpl in *.
  destruct llx2. simpl in *. rewrite HAT in *.
  simpl in *. apply incl_nil_r in Hin1.
  rewrite Hin1 in *.  rewrite cap_pred_nil in HlQ. discriminate.
  discriminate.
intros P'' lP'' HlP''.
  apply lem_a20_mono'' with (llx2 := llx2) (atm := atm) (x := x) (pa2 := pa2) (lP2 := lP).
all : try assumption.
rewrite HlP''. discriminate.

 rewrite HlQ. discriminate.
Qed.

Lemma hopeful8_lP_again_mono_tryinggenlP_atm: forall lP lP2 atm beta x llx W Iv Ip Ir pa2,
  incl lP lP2  ->
  atm = (passing_conj (passing_predSO_ll lP llx)) ->
  incl (preds_in beta) (preds_in atm) ->
  incl lP (preds_in atm) ->
  ex_FOvar_var_ll x (FOv_att_P_l atm lP2) = false ->
  length lP = length llx ->
  ex_nil_in_llv llx = false ->
  uniform_pos_SO beta ->
SOturnst W Iv (alt_Ip_list Ip
  (vsS_pa_l Iv (FOv_att_P_l atm lP2) (list_var (length lP2) x)) lP2) Ir
  (implSO atm beta) ->
  (forall pa_l,
      length lP2 = length pa_l ->
      @consistent_lP_lpa _ pa2 lP2 pa_l ->
    SOturnst W Iv (alt_Ip_list Ip pa_l lP2) Ir (implSO atm beta)).
Proof.
   intros lP lP2 atm beta  x llx2 W Iv Ip Ir pa2 Hin3 HAT Hin1 Hin2 Hex Hl1 Hex2 Hun SOt pa_l Hnil Hcon SOt1.
  case_eq lP2. intros HlP; rewrite HlP in *. simpl in *. 
    rewrite alt_Ip_list_nil in *. apply SOt. assumption.
  intros P lP' HlP. rewrite <- HlP.
  rewrite SOturnst_implSO in SOt.
  assert (
      SOturnst W Iv
        (alt_Ip_list Ip
           (vsS_pa_l Iv (FOv_att_P_l atm lP2) (list_var (length lP2) x)) lP2)
        Ir atm) as Hass.
      rewrite HAT.

case_eq lP.
  intros Hp. simpl. reflexivity.
intros P'' lP'' HlP''. rewrite <- HlP''.
assert (AT (passing_conj (passing_predSO_ll lP llx2)) = true) as Hass.
  apply AT_passing_predSO_ll. rewrite HlP''. discriminate.
  rewrite HlP'' in *. destruct llx2; discriminate.
  assumption.
apply lem_a21''; try assumption.
 rewrite list_var_length. reflexivity.

   apply consistent_lP_lx_list_var.

  rewrite lem_d71.
apply hopeful9'_further'; try assumption.

  rewrite incl_cap_pred_incl.
  apply incl_refl.
  rewrite incl_preds_in_passing_predSO_ll; assumption.

  specialize (SOt Hass). clear Hass. simpl in Hin1.
  simpl in *.
  case_eq (cap_pred lP2 (preds_in beta)).
    intros Hcap.
    apply alt_Ip_list_cap_pred_nil. assumption.
    apply alt_Ip_list_cap_pred_nil in SOt; assumption.

    intros Q lQ HlQ. 
case_eq lP.
  intros Hp. rewrite Hp in *. simpl in *.
  destruct llx2. simpl in *. rewrite HAT in *.
  simpl in *. apply incl_nil_r in Hin1.
  rewrite Hin1 in *.  rewrite cap_pred_nil in HlQ. discriminate.
  discriminate.
intros P'' lP'' HlP''.
  apply lem_a20_mono'' with (llx2 := llx2) (atm := atm) (x := x) (pa2 := pa2) (lP2 := lP).
all : try assumption.
rewrite HlP''. discriminate.

 rewrite HlQ. discriminate.
Qed.

Lemma vsSahlq_instant_aim1_fwd4_REV_mono_tryinggenlP : forall lP lP2 beta rel atm y xn llx2 (W : Set) Iv Ip Ir (pa2 : W -> Prop),
incl lP2 lP  ->
  REL rel = true ->
    atm = passing_conj (passing_predSO_ll lP2 llx2) ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  ~ att_allFO_var beta (Var xn) ->
  ~ att_exFO_var beta (Var xn) ->
  closed_except beta (Var xn) ->
  length lP2 = length llx2 ->
  ~ lP2 = nil ->
ex_nil_in_llv llx2 = false ->
ex_FOvar_var_ll y (FOv_att_P_l atm lP) = false -> 
  var_in_SO (instant_cons_empty' (conjSO rel atm) beta) (Var xn) ->
  SOturnst W Iv Ip Ir (replace_pred_l (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)  
      (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) beta)) xn))
        (length       (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)))))))
    lP (list_var (length lP) y)
    (vsS_syn_l (FOv_att_P_l (conjSO rel atm) lP) y)) ->
  SOturnst W Iv Ip Ir (list_closed_SO (implSO (conjSO rel atm)
              (instant_cons_empty' (conjSO rel atm) beta)) lP).
Proof.
  intros lP lP2 beta rel atm y xn llx2 W Iv Ip Ir pa2 Hin0 Hrel Hat Hun Hno Hat1 Hat2 Hc Hlength Hnil Hex1 Hex Hocc SOt.

assert (AT atm = true) as Hat'.
  rewrite Hat. apply AT_passing_predSO_ll. assumption.
  intros HH. rewrite HH in *. destruct lP2. contradiction (Hnil eq_refl).
  discriminate. assumption.

  apply (equiv_new_simpl3_lP _ _ _ _ _ _ _ _ pa_f) in SOt.
  apply nlist_list_closed_SO. intros pa_l. rewrite Hat in *.

pose proof (alt_Ip_list_consistent_lP_lpa' lP W Ip (nlist_list_pa W (length lP) pa_l) pa2)
  as Halt.
rewrite length_nlist_list_pa in Halt. specialize (Halt eq_refl).
destruct Halt as [lpa' [Hcon [Hl2 Halt]]].
rewrite Halt.

  apply hopeful8_lP_again_mono_tryinggenlP with (lP := lP2) (x := y) (llx := llx2) (pa2 := pa2); try assumption;
    try reflexivity; try rewrite <- Hat in *.

    rewrite Hat. simpl. rewrite (preds_in_rel rel). simpl.
    rewrite lem_is_in4. unfold instant_cons_empty'.
    simpl. rewrite (preds_in_rel rel). simpl.
    rewrite list_rel_compl_passing_predSO_ll. apply lem_is_in.
    all : try assumption.

    rewrite Hat. simpl. rewrite (preds_in_rel rel). simpl.
    rewrite lem_is_in4. apply incl_refl.
    all : try assumption.

    rewrite Hat. unfold instant_cons_empty'. simpl.
    rewrite (preds_in_rel rel). simpl.
    rewrite list_rel_compl_passing_predSO_ll.

    apply uniform_pos_SO_rep_pred_l. assumption.


all : try assumption.

intros SOt2.
specialize (SOt SOt2).
assert (closed_except (instant_cons_empty' (conjSO rel atm) beta) (Var xn)) as Hprobs.
  apply closed_except_inst_cons_empty'. assumption.

case_eq ((length (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) ))).
  intros Hl.
  apply List.length_zero_iff_nil in Hl. rewrite Hl in *. simpl in *. assumption.

  intros n Hl.
pose proof (kk10 (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) )
  (rev_seq (S (Nat.max (max_FOv (implSO (conjSO rel atm) beta)) xn))
              (length (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) beta))))) 
  (instant_cons_empty' (conjSO rel atm) beta) (Var xn) Hprobs (is_in_FOvar_rem_FOv_f _ _)) as H1.
apply H1 in SOt. assumption.

  rewrite Hl.
  rewrite min_l_rev_seq.
  pose proof (aa20 (conjSO rel atm) beta) as H3. lia.

  apply decr_strict_rev_seq.

  rewrite <- length_FOv_att_P_l. reflexivity.

simpl. rewrite (SOQFree_rel rel). rewrite (SOQFree_atm atm).
apply SOQFree_newnew_pre. unfold instant_cons_empty'.
apply SOQFree_rep_pred_l. simpl.
apply SOQFree_l_empty. all : try assumption.

apply consistent_lP_llv_FOv_att_P_l.

intros P. 
destruct (@lem1a_pre W lP Iv (conjSO rel atm) y P) as [n HH].
exists (pa_l_disj_gen Iv (FOv_att_P (conjSO rel atm) P) y).
exists n. (*  exists (pa_l_disj_gen Iv (FOv_att_P (conjSO rel atm) P) y). *)
rewrite ind_pa_gen in HH.
assumption.

apply ex_att_allFO_llvar_implSO.
apply lem_a32; assumption.
rewrite max_FOv_implSO. rewrite max_FOv_conjSO.
apply lem2; try assumption.

apply ex_att_exFO_llvar_implSO.
apply lem_a33; assumption.
rewrite max_FOv_implSO. rewrite max_FOv_conjSO.
apply lem4a; try assumption.
Qed.

Lemma lem_a32_atm : forall lP atm,
AT atm = true ->
~ ex_att_allFO_llvar atm (FOv_att_P_l atm lP).
Proof.
  induction lP; intros atm Hat H. inversion H.
  simpl in *. inversion H; subst.
  apply ex_att_allFO_lv_AT in H2; auto.
  apply IHlP in H2; auto.
Qed.

Lemma lem_a33_atm : forall lP atm,
AT atm = true ->
~ ex_att_exFO_llvar atm (FOv_att_P_l atm lP).
Proof.
  induction lP; intros atm Hat H. inversion H.
  simpl in *. inversion H; subst.
  apply ex_att_exFO_lvar_AT in H2; auto.
  firstorder.
Qed.

Lemma vsSahlq_instant_aim1_fwd4_REV_mono_tryinggenlP_atm : forall lP lP2 beta atm y xn llx2 (W : Set) Iv Ip Ir (pa2 : W -> Prop),
incl lP2 lP  ->
    atm = passing_conj (passing_predSO_ll lP2 llx2) ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  ~ att_allFO_var beta (Var xn)  ->
  ~ att_exFO_var beta (Var xn) ->
  closed_except beta (Var xn) ->
  length lP2 = length llx2 ->
  ~ lP2 = nil ->
ex_nil_in_llv llx2 = false ->
ex_FOvar_var_ll y (FOv_att_P_l atm lP) = false -> 
  var_in_SO (instant_cons_empty' atm beta) (Var xn)  ->
  SOturnst W Iv Ip Ir (replace_pred_l (implSO
    atm
    (newnew_pre (instant_cons_empty' atm beta)  
      (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta)))
      (rev_seq (S (max (max_FOv (implSO atm beta)) xn))
        (length       (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta)))))))
    lP (list_var (length lP) y)
    (vsS_syn_l (FOv_att_P_l atm lP) y)) ->
  SOturnst W Iv Ip Ir (list_closed_SO (implSO atm
              (instant_cons_empty' atm beta)) lP).
Proof.
  intros lP lP2 beta atm y xn llx2 W Iv Ip Ir pa2 Hin0 Hat Hun Hno Hat1 Hat2 Hc Hlength Hnil Hex1 Hex Hocc SOt.

assert (AT atm = true) as Hat'.
  rewrite Hat. apply AT_passing_predSO_ll. assumption.
  intros HH. rewrite HH in *. destruct lP2. contradiction (Hnil eq_refl).
  discriminate. assumption.

  apply (equiv_new_simpl3_lP _ _ _ _ _ _ _ _ pa_f) in SOt.
  apply nlist_list_closed_SO. intros pa_l. rewrite Hat in *.

pose proof (alt_Ip_list_consistent_lP_lpa' lP W Ip (nlist_list_pa W (length lP) pa_l) pa2)
  as Halt.
rewrite length_nlist_list_pa in Halt. specialize (Halt eq_refl).
destruct Halt as [lpa' [Hcon [Hl2 Halt]]].
rewrite Halt.


  apply hopeful8_lP_again_mono_tryinggenlP_atm with (lP := lP2) (x := y) (llx := llx2) (pa2 := pa2); try assumption;
    try reflexivity; try rewrite <- Hat in *.

    rewrite Hat. simpl.
    rewrite lem_is_in4. unfold instant_cons_empty'.
    simpl. 
    rewrite list_rel_compl_passing_predSO_ll. apply lem_is_in.
    all : try assumption.

    rewrite Hat. simpl.
    rewrite lem_is_in4. apply incl_refl.
    all : try assumption.

    rewrite Hat. unfold instant_cons_empty'. simpl.
    rewrite list_rel_compl_passing_predSO_ll.

    apply uniform_pos_SO_rep_pred_l. assumption.


all : try assumption.

intros SOt2.
specialize (SOt SOt2).
assert (closed_except (instant_cons_empty' atm beta) (Var xn)) as Hprobs.
  apply closed_except_inst_cons_empty'. assumption.

case_eq ((length (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta))))).
  intros Hl.
  apply List.length_zero_iff_nil in Hl. rewrite Hl in *. simpl in *. assumption.

  intros n Hl.
pose proof (kk10 (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta)))
  (rev_seq (S (Nat.max (max_FOv (implSO atm beta)) xn))
              (length (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta))))) 
  (instant_cons_empty' atm beta) (Var xn) Hprobs (is_in_FOvar_rem_FOv_f _ _)) as H1.
apply H1 in SOt. assumption.

  rewrite Hl.
  rewrite min_l_rev_seq.
  pose proof (aa20 atm beta) as H3. lia.

  apply decr_strict_rev_seq.

  rewrite <- length_FOv_att_P_l. reflexivity.

simpl. rewrite (SOQFree_atm atm).
apply SOQFree_newnew_pre. unfold instant_cons_empty'.
apply SOQFree_rep_pred_l. simpl.
apply SOQFree_l_empty. all : try assumption.

apply consistent_lP_llv_FOv_att_P_l.

intros P. 
destruct (@lem1a_pre W lP Iv atm y P) as [n HH].
exists (pa_l_disj_gen Iv (FOv_att_P atm P) y). exists n.
rewrite ind_pa_gen in HH. 
assumption.

apply ex_att_allFO_llvar_implSO.
apply lem_a32_atm; assumption.

rewrite max_FOv_implSO. 
apply lem2_atm; try assumption.

apply ex_att_exFO_llvar_implSO.
apply lem_a33_atm; assumption.

rewrite max_FOv_implSO.
apply lem4a_atm; try assumption.
Qed.


(* ---------------------- *)

Lemma list_closed_SO_instant_cons_empty2_REV : forall l alpha beta W Iv Ip Ir,
  incl (preds_in (implSO alpha beta)) l  ->
  SOQFree (implSO alpha beta) = true ->
  uniform_pos_SO beta ->
SOQFree beta = true ->
  SOturnst W Iv Ip Ir (list_closed_SO (implSO alpha (instant_cons_empty' alpha beta)) l) ->
  SOturnst W Iv Ip Ir (list_closed_SO (implSO alpha beta) l).
Proof.
  intros until 0. intros H1 H2 H4 H5 H3.
  apply nlist_list_closed_SO'. intros pa_l.
  pose proof (nlist_list_closed_SO' W Iv Ir (implSO alpha (instant_cons_empty' alpha beta)) l Ip) as [fwd rev].
  specialize (fwd H3 pa_l). clear rev.
   rewrite <-instant_cons_empty__' in fwd.
  apply instant_cons_empty_equiv; try assumption.
Qed.

Lemma vsSahlq_instant_aim1_fwd4_closer_REV : forall lP lP2 llx2 beta rel atm y xn W Iv Ip Ir,
  REL rel = true ->
    atm = passing_conj (passing_predSO_ll lP2 llx2) ->
length lP2 = length llx2 ->
lP2 <> nil ->
ex_nil_in_llv llx2 = false ->
ex_FOvar_var_ll y (FOv_att_P_l atm lP) = false ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  ~ att_allFO_var beta (Var xn) ->
  ~ att_exFO_var beta (Var xn) ->
  closed_except beta (Var xn) ->
  var_in_SO (instant_cons_empty' (conjSO rel atm) beta) (Var xn) ->
  incl (preds_in (implSO (conjSO rel atm) beta)) lP  ->
  SOturnst W Iv Ip Ir (replace_pred_l (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)  
      (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) beta)) xn))
        (length       (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)))))))
    lP (list_var (length lP) y)
    (vsS_syn_l (FOv_att_P_l (conjSO rel atm) lP) y)) ->
  SOturnst W Iv Ip Ir (list_closed_SO (implSO (conjSO rel atm) beta) lP).
Proof.
  intros lP lP2 llx2 beta rel atm y xn W Iv Ip Ir Hrel Hat Hl Hnil Hex Hex2 Hun Hno Hat1 Hat2 Hc Hocc Hin SOt.
assert (AT atm = true) as Hass.
  rewrite Hat. apply AT_passing_predSO_ll; try assumption.
  destruct llx2; destruct lP2; try discriminate.
  contradiction (Hnil eq_refl). 

  apply vsSahlq_instant_aim1_fwd4_REV_mono_tryinggenlP with (lP2 := lP2) (llx2 := llx2) in SOt; try assumption.
  apply list_closed_SO_instant_cons_empty2_REV; try assumption.

  simpl. rewrite Hno.
  rewrite SOQFree_rel.
  rewrite SOQFree_atm.
  reflexivity. all: try assumption.

  apply pa_t.

    rewrite <- incl_preds_in_passing_predSO_ll with (llx := llx2).
    simpl in Hin. rewrite (preds_in_rel rel Hrel) in Hin. simpl in *.
    apply incl_app_rev_l in Hin.
    rewrite <- Hat. all : assumption.
Qed.

Lemma vsSahlq_instant_aim1_fwd4_closer_REV_atm : forall lP lP2 llx2 beta atm y xn W Iv Ip Ir,
    atm = passing_conj (passing_predSO_ll lP2 llx2) ->
length lP2 = length llx2 ->
lP2 <> nil ->
ex_nil_in_llv llx2 = false ->
ex_FOvar_var_ll y (FOv_att_P_l atm lP) = false ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  ~ att_allFO_var beta (Var xn) ->
  ~ att_exFO_var beta (Var xn) ->
  closed_except beta (Var xn) ->
  var_in_SO (instant_cons_empty' atm beta) (Var xn) ->
  incl (preds_in (implSO atm beta)) lP ->
  SOturnst W Iv Ip Ir (replace_pred_l (implSO
    atm
    (newnew_pre (instant_cons_empty' atm beta)  
      (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta)))
      (rev_seq (S (max (max_FOv (implSO atm beta)) xn))
        (length       (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta)) )))))
    lP (list_var (length lP) y)
    (vsS_syn_l (FOv_att_P_l atm lP) y)) ->
  SOturnst W Iv Ip Ir (list_closed_SO (implSO atm beta) lP).
Proof.
  intros lP lP2 llx2 beta atm y xn W Iv Ip Ir Hat Hl Hnil Hex Hex2 Hun Hno Hat1 Hat2 Hc Hocc Hin SOt.
assert (AT atm = true) as Hass.
  rewrite Hat. apply AT_passing_predSO_ll; try assumption.
  destruct llx2; destruct lP2; try discriminate.
  contradiction (Hnil eq_refl). 

  apply vsSahlq_instant_aim1_fwd4_REV_mono_tryinggenlP_atm with (lP2 := lP2) (llx2 := llx2) in SOt; try assumption.
  apply list_closed_SO_instant_cons_empty2_REV; try assumption.

  simpl. rewrite Hno.
  rewrite SOQFree_atm.
  reflexivity. all: try assumption.

  apply pa_t.

    rewrite <- incl_preds_in_passing_predSO_ll with (llx := llx2).
    simpl in Hin. simpl in *.
    apply incl_app_rev_l in Hin.
    rewrite <- Hat. all : assumption.
Qed.

Lemma vsSahlq_instant_aim1_fwd4_closer2_REV : forall lx lP lP2 llx2 beta rel atm y xn W Iv Ip Ir,
  REL rel = true ->
    atm = passing_conj (passing_predSO_ll lP2 llx2) ->
length lP2 = length llx2 ->
lP2 <> nil ->
ex_nil_in_llv llx2 = false ->
ex_FOvar_var_ll y (FOv_att_P_l atm lP) = false ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  ~ att_allFO_var beta (Var xn) ->
  ~ att_exFO_var beta (Var xn) ->
  closed_except beta (Var xn) ->

  var_in_SO (instant_cons_empty' (conjSO rel atm) beta) (Var xn) ->
  incl (preds_in (implSO (conjSO rel atm) beta)) lP  ->
  SOturnst W Iv Ip Ir (replace_pred_l (list_closed_allFO (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)  
      (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) beta)) xn))
        (length       (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) beta))))))) lx)
    lP (list_var (length lP) y)
    (vsS_syn_l (FOv_att_P_l (conjSO rel atm) lP) y)) ->
  SOturnst W Iv Ip Ir (list_closed_SO (list_closed_allFO
      (implSO (conjSO rel atm) beta) lx) lP).

Proof.
  intros lx lP lP2 llx2 beta rel atm y xn W Iv Ip Ir Hrel Hat Hl Hnil Hex Hex2 Hun Hno Hat1 Hat2 Hc Hocc Hin SOt. 
  rewrite rep_pred_l_list_closed_allFO in SOt.
  pose proof equiv_list_closed_allFO.
  apply (impl_list_closed_allFO _ _ (list_closed_SO (implSO (conjSO rel atm) beta) lP)) in SOt.
    apply equiv_list_closed_SO_list_closed_allFO.
    assumption.
    intros.
    apply vsSahlq_instant_aim1_fwd4_closer_REV with (lP2 := lP2) (llx2 := llx2) in H0.
    all : try assumption.
Qed.

Lemma vsSahlq_instant_aim1_fwd4_closer2_REV_atm : forall lx lP lP2 llx2 beta atm y xn W Iv Ip Ir,
    atm = passing_conj (passing_predSO_ll lP2 llx2) ->
length lP2 = length llx2 ->
lP2 <> nil ->
ex_nil_in_llv llx2 = false ->
ex_FOvar_var_ll y (FOv_att_P_l atm lP) = false ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  ~ att_allFO_var beta (Var xn) ->
  ~ att_exFO_var beta (Var xn) ->
  closed_except beta (Var xn) ->

  var_in_SO (instant_cons_empty' atm beta) (Var xn) ->
  incl (preds_in (implSO atm beta)) lP  ->
  SOturnst W Iv Ip Ir (replace_pred_l (list_closed_allFO (implSO
    atm
    (newnew_pre (instant_cons_empty' atm beta)  
      (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta)))
      (rev_seq (S (max (max_FOv (implSO atm beta)) xn))
        (length       (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta))))))) lx)
    lP (list_var (length lP) y)
    (vsS_syn_l (FOv_att_P_l atm lP) y)) ->
  SOturnst W Iv Ip Ir (list_closed_SO (list_closed_allFO
      (implSO atm beta) lx) lP).

Proof.
  intros lx lP lP2 llx2 beta atm y xn W Iv Ip Ir Hat Hl Hnil Hex Hex2 Hun Hno Hat1 Hat2 Hc Hocc Hin SOt. 
  rewrite rep_pred_l_list_closed_allFO in SOt.
  pose proof equiv_list_closed_allFO.
  apply (impl_list_closed_allFO _ _ (list_closed_SO (implSO atm beta) lP)) in SOt.
    apply equiv_list_closed_SO_list_closed_allFO.
    assumption.
    intros.
    apply vsSahlq_instant_aim1_fwd4_closer_REV_atm with (lP2 := lP2) (llx2 := llx2) in H0.
    all : try assumption.
Qed.


Lemma lem_e1 : forall atm rel beta lx lP W Iv Ip Ir,
  REL rel = true ->
  AT atm = true ->
  SOturnst W Iv Ip Ir (list_closed_SO (list_closed_allFO (implSO (conjSO rel atm) beta) lx) lP) <->
  SOturnst W Iv Ip Ir (list_closed_SO (list_closed_allFO (implSO 
    (conjSO rel (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm))))
    beta) lx) lP).
Proof.
  intros atm rel beta lx lP W Iv Ip Ir Hrel Hat.
  apply equiv_list_closed_SO. intros W1 Iv1 Ip1 Ir1.
  apply equiv_list_closed_allFO. intros W2 Iv2 Ip2 Ir2.
  split; intros SOt [H1 H2];
    apply SOt; simpl in *; apply conj. assumption.
    apply lem118'_equiv; assumption.

    assumption. apply (lem118'_equiv atm); assumption.
Qed.

Lemma lem_e1_atm : forall atm beta lx lP W Iv Ip Ir,
  AT atm = true ->
  SOturnst W Iv Ip Ir (list_closed_SO (list_closed_allFO (implSO atm beta) lx) lP) <->
  SOturnst W Iv Ip Ir (list_closed_SO (list_closed_allFO (implSO 
    (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm)))
    beta) lx) lP).
Proof.
  intros atm beta lx lP W Iv Ip Ir Hat.
  apply equiv_list_closed_SO. intros W1 Iv1 Ip1 Ir1.
  apply equiv_list_closed_allFO. intros W2 Iv2 Ip2 Ir2.
  split; intros SOt H1;
    apply SOt; simpl in *. 
    apply lem118'_equiv; assumption.

    apply (lem118'_equiv atm); assumption.
Qed.

Lemma lem118'_is_in_pred : forall atm P,
  AT atm = true ->
  In P (preds_in (passing_conj (passing_predSO_ll
      (atm_passing_predSO_ll_lP atm)
      (atm_passing_predSO_ll_llx atm)))) <->
  In P (preds_in atm).
Proof.
  induction atm; intros P Hat; try discriminate. firstorder.
  pose proof (AT_conjSO_l _ _ Hat).
  pose proof (AT_conjSO_r _ _ Hat).
  simpl. rewrite passing_predSO_ll_app.
  rewrite preds_in_passing_conj_app.
  split; intros HH; apply in_app_or in HH;
    apply in_or_app; firstorder.
  apply lem118'_length. assumption.
Qed.

Lemma lem_e4 : forall l atm,
AT atm = true ->
list_rel_compl l (preds_in
    (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm)))) =
list_rel_compl l (preds_in atm).
Proof.
  induction l; intros atm Hat. auto.
  simpl.
  destruct (in_predicate_dec a (preds_in atm)).
  + rewrite in_predicate_dec_l. apply IHl; auto.
    apply lem118'_is_in_pred; auto.
  + rewrite in_predicate_dec_r. rewrite IHl; auto.
    intros HH. apply (lem118'_is_in_pred atm) in HH; auto.
Qed.

Lemma lem_e3 : forall atm rel beta,
  AT atm = true ->
  REL rel = true ->
  instant_cons_empty' (conjSO rel 
    (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm)
        (atm_passing_predSO_ll_llx atm)))) beta =
  instant_cons_empty' (conjSO rel atm) beta.
Proof.
  intros atm rel beta Hat Hrel.
  unfold instant_cons_empty'. simpl.
  rewrite (preds_in_rel rel Hrel). simpl.
  rewrite lem_e4. reflexivity.
  assumption.
Qed.

Lemma lem_e3_atm : forall atm beta,
  AT atm = true ->
  instant_cons_empty' (
    (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm)
        (atm_passing_predSO_ll_llx atm)))) beta =
  instant_cons_empty' atm beta.
Proof.
  intros atm beta Hat.
  unfold instant_cons_empty'. simpl.
  rewrite lem_e4. reflexivity.
  assumption.
Qed.

Lemma lem_e9 : forall atm a,
AT atm = true ->
incl (FOv_att_P  (passing_conj
              (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm)))
           a) (FOv_att_P atm a).
Proof.
  induction atm; intros P Hat; try discriminate.
  + simpl.  apply incl_refl. 
  + simpl in *. if_then_else_hyp.
    rewrite passing_predSO_ll_app.
    rewrite FOv_att_P_passing_conj_app.
    apply incl_app. apply incl_appl. apply IHatm1. auto.
    apply incl_appr. apply IHatm2. auto. 
    apply lem118'_length. auto. 
Qed.

Lemma lem_e11 : forall atm a,
AT atm = true ->
incl (FOv_att_P atm a) (FOv_att_P  (passing_conj
              (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm)))
           a) .
Proof.
  induction atm; intros P Hat; try discriminate.
  + apply incl_refl.   
  + simpl in *. if_then_else_hyp.
    rewrite passing_predSO_ll_app.
    rewrite FOv_att_P_passing_conj_app.
    apply incl_app. apply incl_appl. apply IHatm1. auto.
    apply incl_appr. apply IHatm2. auto. 
    apply lem118'_length. auto. 
Qed.

Lemma lem_e8 : forall lP atm ,
  AT atm = true ->
  in_in_FOvar_ll (FOv_att_P_l (passing_conj (passing_predSO_ll
    (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm))) lP)
(FOv_att_P_l atm lP).
Proof.
  induction lP; intros atm Hat. simpl. constructor.
  simpl in *. constructor. apply lem_e9. auto.
  apply IHlP. auto.
Qed.

Lemma lem_e10 : forall lP atm ,
  AT atm = true ->
  in_in_FOvar_ll (FOv_att_P_l atm lP)
    (FOv_att_P_l (passing_conj (passing_predSO_ll
    (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm))) lP).
Proof.
  induction lP; intros atm Hat. constructor.
  simpl in *. constructor. apply lem_e11. auto.
  apply IHlP. auto.
Qed.

Lemma lem_e15' : forall l2  x y W Iv Ip Ir ,
In x l2 ->
SOturnst W Iv Ip Ir (replace_FOv (disj_l l2 x) x y).
Proof.
  induction l2; intros x y W Iv Ip Ir  H2. inversion H2.
  simpl in *. destruct l2. simpl. destruct H2; subst;
  FOv_dec_l_rep. simpl. auto. inversion H.
  remember (f :: l2) as l2'. simpl. FOv_dec_l_rep.
  destruct (FOvariable_dec x a). subst. firstorder.
  destruct H2. subst. contradiction.
  simpl. right. apply IHl2. auto.
Qed.

Lemma lem_e18' : forall l2 x y z W Iv Ip Ir,
In z l2 -> 
~ x = z ->
SOturnst W Iv Ip Ir (eqFO y z) ->
SOturnst W Iv Ip Ir (replace_FOv (disj_l l2 x) x y).
Proof.
  induction l2; intros x y z W Iv IP Ir H2 Hneq SOt. inversion H2.
  simpl in *. destruct l2. simpl. FOv_dec_l_rep.
  + destruct (FOvariable_dec x a). firstorder.
    simpl. destruct H2. subst. auto. contradiction.
  + remember (f :: l2) as l2'. simpl.
    FOv_dec_l_rep. destruct (FOvariable_dec x a).
    subst. firstorder.
    simpl. destruct H2. subst a. firstorder.
    right. eapply IHl2. apply H. all : auto.
Qed.

Lemma lem_e14 : forall l1 l2 x y W Iv Ip Ir,
incl l1 l2  ->
~ l1 = nil ->
SOturnst W Iv Ip Ir (replace_FOv (disj_l l1 x) x y) ->
SOturnst W Iv Ip Ir (replace_FOv (disj_l l2 x) x y).
Proof.
  induction l1; intros l2 x y W Iv Ip Ir H1 H2 SOt. contradiction.
  simpl in *. pose proof (incl_hd _ _ _ _ H1). 
  apply incl_lcons in H1.
  destruct l1. simpl in *. FOv_dec_l_rep.
  + destruct (FOvariable_dec x a); subst. apply lem_e15'; auto.
    apply lem_e18' with (z := a); auto.
  + remember (f :: l1) as l1'.  simpl in *.
    FOv_dec_l_rep. destruct SOt as [SOt1 | SOt2].
    ++ destruct (FOvariable_dec x a). subst. apply lem_e15'.
       auto. apply lem_e18' with (z := a); auto.
    ++ apply IHl1; try assumption. subst. discriminate.
Qed.

Lemma lem_e20 : forall l x y lP lx lcond W Iv Ip Ir,
  SOturnst W Iv Ip Ir (replace_pred_l (replace_FOv (disj_l l x) x y)
      lP lx lcond) <->
  SOturnst W Iv Ip Ir (replace_FOv (disj_l l x) x y).
Proof.
  induction l; intros x y lP lx lcond W Iv Ip Ir.
  + simpl.  dest_FOv_dec_blind; simpl; 
    rewrite rep_pred_l_eqFO; apply iff_refl.
  + simpl. destruct l. simpl. FOv_dec_l_rep.
    ++ dest_FOv_dec_blind; subst; simpl;
       rewrite rep_pred_l_eqFO; apply iff_refl.
    ++ rewrite replace_FOv_disjSO. rewrite rep_pred_l_disjSO.
       split; intros [H1 | H2].
       simpl. FOv_dec_l_rep. 
       destruct (FOvariable_dec x a). firstorder.
       simpl in H1. FOv_dec_l_rep. rewrite FOvariable_dec_r in H1.
       rewrite rep_pred_l_eqFO in H1. simpl in H1. left. firstorder. auto.
       right. apply (IHl x y lP lx lcond); assumption.

       left. simpl in *. FOv_dec_l_rep. dest_FOv_dec_blind;
       rewrite rep_pred_l_eqFO. firstorder. auto.
       right. apply IHl. auto.
Qed.

Lemma lem_e27 : forall alpha P x cond,
  FO_frame_condition alpha = true ->
  replace_pred alpha P x cond = alpha.
Proof.
  induction alpha; intros [Pn] x cond H.
    destruct p as [Qm]. destruct f. discriminate.

    simpl. destruct f. destruct f0.
    reflexivity.

    simpl. destruct f. destruct f0.
    reflexivity.

    simpl in *. destruct f. rewrite IHalpha.
      reflexivity. assumption.

    simpl in *. destruct f. rewrite IHalpha.
      reflexivity. assumption.

    simpl in *. rewrite IHalpha. reflexivity. assumption.

    simpl. rewrite IHalpha1. rewrite IHalpha2. reflexivity.
      apply (FO_frame_condition_conjSO_r _ _ H).
      apply (FO_frame_condition_conjSO_l _ _ H).

    simpl. rewrite IHalpha1. rewrite IHalpha2. reflexivity.
      apply (FO_frame_condition_conjSO_r _ _ H).
      apply (FO_frame_condition_conjSO_l _ _ H).

    simpl. rewrite IHalpha1. rewrite IHalpha2. reflexivity.
      apply (FO_frame_condition_conjSO_r _ _ H).
      apply (FO_frame_condition_conjSO_l _ _ H).

    destruct p. discriminate.
    destruct p. discriminate.
Qed.

Lemma lem_e26 : forall lP lx lcond alpha,
  FO_frame_condition alpha = true ->
  replace_pred_l alpha lP lx lcond = alpha.
Proof.
  induction lP; intros lx lcond alpha H. reflexivity.
  destruct lx. reflexivity.
  destruct lcond. reflexivity.
  simpl. rewrite IHlP. apply lem_e27.
  all : assumption.
Qed.

Lemma FO_frame_condition_l_vsS_syn_l : forall l x,
FO_frame_condition_l (vsS_syn_l l x) = true.
Proof.
  induction l; intros [xn]. reflexivity.
  simpl. rewrite IHl. rewrite FO_frame_condition_disj_l.
  reflexivity.
Qed.

Lemma lem_e19 : forall lP l1 l2 P y x W Iv Ip Ir,
in_in_FOvar_ll l1 l2 ->
in_in_FOvar_ll l2 l1 ->
consistent_lP_llv lP l1 ->
consistent_lP_llv lP l2 ->
  SOturnst W Iv Ip Ir (replace_pred_l (predSO P y) lP
      (list_var (length lP) x) (vsS_syn_l l1 x)) <->
  SOturnst W Iv Ip Ir (replace_pred_l (predSO P y) lP
      (list_var (length lP) x) (vsS_syn_l l2 x)).
Proof.
  induction lP; intros l1 l2 P y x W Iv Ip Ir Hin1 Hin2 Hcon1 Hcon2.
    simpl in *. apply iff_refl.

    simpl in *. case_eq l1.
      intros Hl1. simpl. destruct l2. simpl.
      apply iff_refl. rewrite Hl1 in *. inversion Hin2. 

      intros la l1' Hl1. rewrite <- Hl1.
      case_eq (vsS_syn_l l1 x). intros H. rewrite Hl1 in H.
        discriminate.
      intros beta lbeta Hlbeta.
      case_eq l2. intros Hl2. rewrite Hl2 in *. rewrite Hl1 in *.
        inversion Hin1.
      intros lb l2' Hl2. rewrite <- Hl2.
      case_eq (vsS_syn_l l2 x). intros H. rewrite Hl2 in H. discriminate.
      intros gamma lgamma Hlgamma.
      rewrite Hl1 in *. rewrite Hl2 in *.
      simpl in *. 

      destruct (incl_dec _ FOvariable_dec la lb). 
      inversion Hlbeta as [[H1a H1b]].
      inversion Hlgamma as [[H2a H2b]].
      rewrite rep_pred__l_consistent.
      rewrite rep_pred__l_consistent. simpl. 
      destruct (predicate_dec a P). 
        rewrite lem_e26.
        rewrite lem_e26.
        split; intros H.
          destruct la. destruct lb. simpl in *. auto.
          simpl in H1a. subst beta.
          inversion Hin2. subst. apply incl_hd in H3. firstorder.          
          apply lem_e14 with (l1 := (cons f la)); try assumption.
            discriminate.
          destruct la. destruct lb. simpl in *.
          destruct x. assumption. 
          inversion Hin2. subst. apply incl_hd in H3. firstorder.
          destruct lb. inversion Hin1. subst. apply incl_hd in H3. 
          firstorder. 

          apply lem_e14 with (l1 := (cons f0 lb)); try assumption.
          apply incl_cons. simpl. inversion Hin2. subst.
          pose proof (incl_hd _ _ _ _ H3) as HH.
          simpl in *. auto.
          inversion Hin2. subst. apply incl_lcons in H3. auto.
            discriminate.

          apply rep_FOv_FO_frame_condition.
          apply FO_frame_condition_disj_l. 
          apply rep_FOv_FO_frame_condition.
          apply FO_frame_condition_disj_l. 

      simpl. 
      apply IHlP; auto.
        apply consistent_lP_llv_cons in Hcon1. inversion Hin1.
          subst. auto.
        apply consistent_lP_llv_cons in Hcon2. inversion Hin2.
          subst. auto. 
        apply consistent_lP_llv_cons in Hcon1. inversion Hin1.
          subst. auto.
        apply consistent_lP_llv_cons in Hcon2. inversion Hin2.
          subst. auto. 

        apply FO_frame_condition_l_vsS_syn_l.
        apply FO_frame_condition_disj_l. 
        apply consistent_lP_llv__lcond_cons. assumption.
        apply (consistent_lP_lx_list_var (cons a lP)).

        apply FO_frame_condition_l_vsS_syn_l.
        apply FO_frame_condition_disj_l.

        apply consistent_lP_llv__lcond_cons. assumption.
        apply (consistent_lP_lx_list_var (cons a lP)).

        inversion Hin1. subst.  contradiction.
Qed.

Lemma lem_e12 : forall alpha lP l1 l2 x W Iv Ip Ir,
  SOQFree alpha = true ->
  in_in_FOvar_ll l1 l2 ->
  in_in_FOvar_ll l2 l1 ->
  consistent_lP_llv lP l1 ->
  consistent_lP_llv lP l2 ->
  SOturnst W Iv Ip Ir (replace_pred_l alpha lP (list_var (length lP) x)
      (vsS_syn_l l1 x)) <->
  SOturnst W Iv Ip Ir (replace_pred_l alpha lP (list_var (length lP) x)
      (vsS_syn_l l2 x)).
Proof.
  induction alpha; intros lP l1 l2 x W Iv Ip Ir Hno Hin1 Hin2 Hcon1 con2.
    destruct p as [Pn]. destruct f as [xn].
    apply (lem_e19 _ l1 l2); assumption.

    rewrite rep_pred_l_relatSO.
    rewrite rep_pred_l_relatSO. apply iff_refl. simpl.

    rewrite rep_pred_l_eqFO.
    rewrite rep_pred_l_eqFO. apply iff_refl. simpl.

    do 2 rewrite rep_pred_l_allFO.
    do 2 rewrite SOturnst_allFO. simpl in Hno.
    destruct f.
    split; intros SOt d; apply (IHalpha _ l1 l2);
      try assumption; apply SOt.

    do 2 rewrite rep_pred_l_exFO.
    do 2 rewrite SOturnst_exFO. simpl in Hno.
    destruct f.
    split; intros [d SOt]; exists d; apply (IHalpha _ l1 l2);
      try assumption; apply SOt.

    do 2 rewrite rep_pred_l_negSO. simpl.
    simpl in Hno. split; intros H1 H2;
      apply H1; apply (IHalpha _ l1 l2); assumption.

    do 2 rewrite rep_pred_l_conjSO. simpl.
    pose proof (SOQFree_conjSO_l _ _ Hno) as Hno1.
    pose proof (SOQFree_conjSO_r _ _ Hno) as Hno2.
    split; (intros [H1 H2]; apply conj; [apply (IHalpha1 _ l1 l2) |
      apply (IHalpha2 _ l1 l2)]); assumption.

    do 2 rewrite rep_pred_l_disjSO. simpl.
    pose proof (SOQFree_conjSO_l _ _ Hno) as Hno1.
    pose proof (SOQFree_conjSO_r _ _ Hno) as Hno2.
    split; (intros [H1 | H2]; [left; apply (IHalpha1 _ l1 l2) |
      right; apply (IHalpha2 _ l1 l2)]); assumption.

    do 2 rewrite rep_pred_l_implSO. simpl.
    pose proof (SOQFree_conjSO_l _ _ Hno) as Hno1.
    pose proof (SOQFree_conjSO_r _ _ Hno) as Hno2.
    split; intros H1 H2; apply (IHalpha2 _ l1 l2); 
      try assumption; apply H1; apply (IHalpha1 _ l1 l2); 
      assumption.

    destruct p. discriminate.
    destruct p. discriminate.
Qed.

Lemma lem_e5 : forall lP atm rel alpha x W Iv Ip Ir,
  REL rel = true ->
  AT atm = true ->
SOQFree alpha = true ->
  SOturnst W Iv Ip Ir (replace_pred_l alpha lP (list_var (length lP) x)
    (vsS_syn_l (FOv_att_P_l (conjSO rel 
      (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm)
        (atm_passing_predSO_ll_llx atm))))lP) x)) <->
  SOturnst W Iv Ip Ir (replace_pred_l alpha lP (list_var (length lP) x)
    (vsS_syn_l (FOv_att_P_l (conjSO rel atm) lP) x)).
Proof.
  intros lP atm rel alpha x W Iv Ip Ir Hrel Hat Hno.
  rewrite (FOv_att_P_l_conjSO_rel _ rel); try assumption.
  rewrite (FOv_att_P_l_conjSO_rel _ rel); try assumption.
  apply lem_e12. assumption. apply lem_e8. assumption.
  apply lem_e10. assumption. apply consistent_lP_llv_FOv_att_P_l.  
  apply consistent_lP_llv_FOv_att_P_l.
Qed.

Lemma lem_e5_atm : forall lP atm alpha x W Iv Ip Ir,
  AT atm = true ->
SOQFree alpha = true ->
  SOturnst W Iv Ip Ir (replace_pred_l alpha lP (list_var (length lP) x)
    (vsS_syn_l (FOv_att_P_l (
      (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm)
        (atm_passing_predSO_ll_llx atm))))lP) x)) <->
  SOturnst W Iv Ip Ir (replace_pred_l alpha lP (list_var (length lP) x)
    (vsS_syn_l (FOv_att_P_l (atm) lP) x)).
Proof.
  intros lP atm alpha x W Iv Ip Ir Hat Hno.
  apply lem_e12. assumption. apply lem_e8. assumption.
  apply lem_e10. assumption. apply consistent_lP_llv_FOv_att_P_l.  
  apply consistent_lP_llv_FOv_att_P_l.
Qed.

Lemma max_FOv_passing_conj_app : forall l1 l2,
  ~ l1 = nil -> 
  ~ l2 = nil ->
  max_FOv (passing_conj (app l1 l2)) =
  max (max_FOv (passing_conj l1)) (max_FOv (passing_conj l2)).
Proof.
  induction l1; intros l2 H1 H2. 
    contradiction (H1 eq_refl).
    simpl. case_eq l1.
      intros Hl1. simpl. destruct l2. contradiction (H2 eq_refl).
      simpl. unfold max_FOv. simpl. rewrite max_FOv_l_app. lia.

      intros beta lbeta Hl1. rewrite <- Hl1.
      case_eq (app l1 l2). intros H. rewrite Hl1 in *. discriminate.
      intros gamma lgamma Hlgamma. rewrite <- Hlgamma.
      destruct l2. contradiction (H2 eq_refl).
      simpl. rewrite max_FOv_conjSO. rewrite IHl1. 
      unfold max_FOv. simpl. rewrite max_FOv_l_app. lia.
      subst. discriminate. discriminate.
Qed.

Lemma lem118'_max_FOv : forall atm,
 AT atm = true ->
  max_FOv (passing_conj (passing_predSO_ll 
    (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm))) =
  max_FOv atm.
Proof.
  induction atm; intros Hat; try discriminate.
    destruct p as [Pn]. destruct f as [xn]. reflexivity.

    simpl in *.
    pose proof (AT_conjSO_l _ _ Hat).
    pose proof (AT_conjSO_r _ _ Hat).
 rewrite passing_predSO_ll_app.
    rewrite max_FOv_passing_conj_app.
    rewrite IHatm1. rewrite IHatm2. rewrite max_FOv_conjSO. auto. 
    all : try assumption.
      apply lem118'_not_nil. assumption.
      apply lem118'_not_nil. assumption.

      apply lem118'_length. assumption.
Qed.

Lemma rep_pred_REL : forall rel P x cond,
  REL rel = true ->
  (replace_pred rel P x cond) = rel.
Proof.
  induction rel; intros P x cond Hrel; try discriminate.
    destruct f. destruct f0. destruct P. simpl. reflexivity.

    simpl. destruct P. rewrite IHrel1. rewrite IHrel2. reflexivity.
    apply (REL_conjSO_r _ _ Hrel).
    apply (REL_conjSO_l _ _ Hrel).
Qed.

Lemma rep_pred_l_REL : forall lP  rel lx lcond,
  REL rel = true ->
  (replace_pred_l rel lP lx lcond) = rel.
Proof.
  induction lP; intros rel lx lcond Hrel.
    reflexivity.

    destruct lx. reflexivity.
    destruct lcond. reflexivity.
    simpl. rewrite IHlP. apply rep_pred_REL.
    all : assumption.
Qed.

Lemma rep_pred__l_is_in2 : forall lP  (alpha : SecOrder) lx lcond (P : predicate) 
      (x : FOvariable) (cond : SecOrder),
    length lP = length lx ->
    length lP = length lcond ->
    In P lP ->
    FO_frame_condition_l lcond = true ->
    FO_frame_condition cond = true ->
    replace_pred (replace_pred_l alpha lP lx lcond) P x cond =
    replace_pred_l alpha lP lx lcond.
Proof.
  intros lP alpha lx lcond P x cond Hl1 Hl2 Hin Hun1 Hin2.
  symmetry in Hl1.
  symmetry in Hl2.
  destruct (nlist_list_ex (length lP) lP eq_refl) as [l1 H1].
  destruct (nlist_list_ex (length lP) lx Hl1) as [n2 H2].
  destruct (nlist_list_ex (length lP) lcond Hl2) as [n3 H3].
  rewrite <- H1 in *.
  rewrite <- H2.
  rewrite <- H3 in *.
  apply rep_pred__l_is_in; try assumption.
Qed.

Lemma lem_e24 : forall l1 l2 x y W Iv Ip Ir,
  ~ l1 = nil ->
  ~ l2 = nil ->
  SOturnst W Iv Ip Ir (replace_FOv (disj_l (app l1 l2) x) x y) <->
  SOturnst W Iv Ip Ir (disjSO (replace_FOv (disj_l l1 x) x y)
    (replace_FOv (disj_l l2 x) x y)).
Proof.
  induction l1; intros l2 x y W Iv Ip Ir Hnil1 Hnil2. contradiction (Hnil1 eq_refl).
  simpl. case_eq l1. intros Hl1. destruct l2. contradiction (Hnil2 eq_refl).
    simpl. apply iff_refl.

    intros z lz Hl1. rewrite <- Hl1.
    case_eq (app l1 l2).
rewrite Hl1. discriminate.

      intros z' lz' Hl12. rewrite <- Hl12.
      do 2 rewrite replace_FOv_disjSO.
      do 2 rewrite SOturnst_disjSO.
      split; intros [H | H].
        left. left. assumption.

        apply IHl1 in H. rewrite SOturnst_disjSO in H.
        destruct H as [H | H].
          left. right. assumption.
          right. assumption.

          rewrite Hl1. discriminate. assumption.

        destruct H as [H|H].
          left. assumption.

          right.
          apply IHl1. rewrite Hl1. discriminate. assumption.
          simpl. left. assumption.

          right. apply IHl1. rewrite Hl1. discriminate. assumption.
          simpl. right. assumption.
Qed.

Lemma SOQFree_P_passing_conj_app : forall l1 l2 P,
~ l1 = nil ->
~ l2 = nil ->
  SOQFree_P (passing_conj l1) P = true ->
  SOQFree_P (passing_conj l2) P = true ->
  SOQFree_P (passing_conj (app l1 l2)) P = true.
Proof.
  induction l1; intros l2 [Pn] Hnil1 Hnil2 H1 H2. contradiction (Hnil1 eq_refl).
  simpl in *. destruct l1. simpl in *.
    case_eq l2. intros Hl2. rewrite Hl2 in *. contradiction (Hnil2 eq_refl).
    intros beta lbeta Hl2. rewrite <- Hl2. simpl. rewrite H1. assumption.

    simpl. simpl in H1. simpl in IHl1.
 case_eq (SOQFree_P a (Pred Pn));
      intros Hno; rewrite Hno in *.
      apply IHl1; try assumption. discriminate.

      discriminate.
Qed.

Lemma SOQFree_P_atm_passing_predSO_ll : forall atm P,
  AT atm = true ->
  SOQFree_P atm P = true ->
  SOQFree_P (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm))) P = true.
Proof.
  induction atm; intros [Pn] Hat Hno; try discriminate.
    destruct p as [Qm]. simpl in *. reflexivity.

    pose proof (AT_conjSO_l _ _ Hat) as Hata.
    pose proof (AT_conjSO_r _ _ Hat) as Hatb.
    pose proof (SOQFree_P_conjSO_l _ _ _ Hno) as Hnoa.
    pose proof (SOQFree_P_conjSO_r _ _ _ Hno) as Hnob.
    simpl. rewrite passing_predSO_ll_app.
    apply SOQFree_P_passing_conj_app.
      apply lem118'_not_nil. assumption.
      apply lem118'_not_nil. assumption.
      apply IHatm1; assumption.
      apply IHatm2; assumption.
      apply lem118'_length. assumption.
Qed.

Lemma lem_e23 : forall atm atm2 Q y x W Iv Ip Ir,
 AT atm = true ->
 atm2 = passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm)) ->
SOturnst W Iv Ip Ir (replace_FOv (disj_l (FOv_att_P atm2 Q) y) y x) <->
SOturnst W Iv Ip Ir (replace_FOv (disj_l (FOv_att_P atm Q) y) y x).
Proof.
  induction atm; intros atm0 Q y x W Iv Ip Ir Hat1 Hat2; try discriminate.
  + simpl in *. rewrite Hat2. destruct (predicate_dec Q p).
    simpl. FOv_dec_l_rep. rewrite predicate_dec_l. simpl.
    FOv_dec_l_rep. apply iff_refl. auto.
    simpl. rewrite predicate_dec_r; auto. simpl. apply iff_refl.
  + simpl in *. if_then_else_hyp.
    assert (SOQFree_P atm1 Q = true) as Hass1.
      apply SOQFree__P. apply SOQFree_atm. assumption.
    assert (SOQFree_P atm2 Q = true) as Hass2.
      apply SOQFree__P. apply SOQFree_atm. assumption.
    subst.
    rewrite passing_predSO_ll_app. rewrite FOv_att_P_passing_conj_app.
      2 : (apply lem118'_length; try assumption).
    destruct (Pred_in_SO_dec atm1 Q) as [Hin1|Hin1].
    destruct (Pred_in_SO_dec atm2 Q) as [Hin2|Hin2].
    split ;intros H2. apply lem_e24 in H2. apply lem_e24.
        apply lem10; assumption.
        apply lem10; assumption.

      simpl in *. destruct H2 as [H1 | H2].
        left. apply (IHatm1 (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm1) (atm_passing_predSO_ll_llx atm1)))); auto.
        right. apply (IHatm2 (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm2) (atm_passing_predSO_ll_llx atm2)))); auto.
        apply lem10.
          apply SOQFree_P_atm_passing_predSO_ll; assumption.
          rewrite <- lem118'_Pred_in_SO_gen; assumption.
        apply lem10.
          apply SOQFree_P_atm_passing_predSO_ll; assumption.
          rewrite <- lem118'_Pred_in_SO_gen; assumption.

apply lem_e24 in H2. apply lem_e24.
        apply lem10.
          apply SOQFree_P_atm_passing_predSO_ll; assumption.
          rewrite <- lem118'_Pred_in_SO_gen; assumption.
        apply lem10.
          apply SOQFree_P_atm_passing_predSO_ll; assumption.
          rewrite <- lem118'_Pred_in_SO_gen; assumption.
      simpl in *. destruct H2 as [H1 | H2].
        left. apply (IHatm1 (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm1) (atm_passing_predSO_ll_llx atm1)))); auto.
        right. apply (IHatm2 (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm2) (atm_passing_predSO_ll_llx atm2)))); auto.

        apply lem10; assumption.
        apply lem10; assumption.

        rewrite (lem1 atm2); try assumption. rewrite List.app_nil_r.
        rewrite (lem1 (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm2)
            (atm_passing_predSO_ll_llx atm2)))). rewrite List.app_nil_r.
        apply IHatm1. all : auto.
        rewrite <- lem118'_Pred_in_SO_gen; assumption.


        rewrite (lem1 atm1); try assumption.
        rewrite (lem1 (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm1)
            (atm_passing_predSO_ll_llx atm1)))).
        simpl.
        apply IHatm2. all : auto.
        rewrite <- lem118'_Pred_in_SO_gen; assumption.
Qed.  

Lemma lem_e22_pre_predSO : forall lP atm atm2 p f y W Iv Ip Ir,
 AT atm = true ->
 atm2 = passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm)) ->
SOturnst W Iv Ip Ir (replace_pred_l (predSO p f) lP (list_var (length lP) y) (vsS_syn_l (FOv_att_P_l atm2 lP) y)) <->
SOturnst W Iv Ip Ir (replace_pred_l (predSO p f) lP (list_var (length lP) y) (vsS_syn_l (FOv_att_P_l atm lP) y)).
Proof.
  induction lP; intros atm atm2 P x y W Iv Ip Ir Hat1 Hat2.
    simpl in *. apply iff_refl.

    assert (length lP = length (list_var (length lP) y)) as Hass1.
        symmetry. apply list_var_length.
    assert (length lP = length (vsS_syn_l (FOv_att_P_l atm2 lP) y)) as Hass2.
        rewrite <- length_vsS_syn_l.
        apply length_FOv_att_P_l.
    assert (length lP = length (vsS_syn_l (FOv_att_P_l atm lP) y)) as Hass3.
        rewrite <- length_vsS_syn_l.
        apply length_FOv_att_P_l.
    simpl. destruct (in_predicate_dec a lP).
      rewrite rep_pred__l_is_in2.
      rewrite rep_pred__l_is_in2.
      apply IHlP; assumption.
        all : try assumption.
        apply FO_frame_condition_l_vsS_syn_l.
        apply FO_frame_condition_disj_l.
        apply FO_frame_condition_l_vsS_syn_l.
        apply FO_frame_condition_disj_l.

      rewrite rep_pred__l_switch; try assumption.
      rewrite rep_pred__l_switch; try assumption.
      simpl. destruct (predicate_dec a P).
        split; intros H. apply lem_e20.
          apply lem_e20 in H.
          apply (lem_e23 atm atm2); assumption.

apply lem_e20.
          apply lem_e20 in H.
          apply (lem_e23 atm atm2); assumption.

        apply IHlP; assumption.
        apply FO_frame_condition_disj_l.
        apply FO_frame_condition_l_vsS_syn_l.
        apply FO_frame_condition_disj_l.
        apply FO_frame_condition_l_vsS_syn_l.
Qed.

Lemma lem_e22_pre : forall atm0 lP atm atm2 y W Iv Ip Ir,
  AT atm = true ->
  AT atm0 = true ->
  atm2 = passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm)
            (atm_passing_predSO_ll_llx atm)) ->
  SOturnst W Iv Ip Ir (replace_pred_l atm0 lP (list_var (length lP) y)
    (vsS_syn_l (FOv_att_P_l atm2 lP) y)) <->
  SOturnst W Iv Ip Ir (replace_pred_l atm0 lP (list_var (length lP) y)
    (vsS_syn_l (FOv_att_P_l atm lP) y)).
Proof.
  induction atm0; intros lP atm atm2 y W Iv Ip Ir Hat1 Hat2 Hat3; try discriminate.
    apply lem_e22_pre_predSO; assumption.

    do 2 rewrite rep_pred_l_conjSO.
    pose proof (AT_conjSO_l _ _ Hat2) as Hat2a.
    pose proof (AT_conjSO_r _ _ Hat2) as Hat2b.
    simpl. split; intros [H1 H2]; (apply conj;
      [apply (IHatm0_1 lP atm atm2) | apply (IHatm0_2 lP atm atm2) ]);
      assumption.
Qed.

Lemma lem_e25 : forall l1 lP lx lcond l2 W Iv Ip Ir,
l1 <> nil ->
l2 <> nil ->
  SOturnst W Iv Ip Ir (replace_pred_l (passing_conj (app l1 l2)) lP lx lcond) <->
  SOturnst W Iv Ip Ir (conjSO (replace_pred_l (passing_conj l1) lP lx lcond)
    (replace_pred_l (passing_conj l2) lP lx lcond)).
Proof.
  induction l1; intros lP lx lcond l2 W Iv Ip Ir Hnil1 Hnil2.
    contradiction (Hnil1 eq_refl).

    simpl. case_eq l1. intros Hl1. simpl. destruct l2. contradiction (Hnil2 eq_refl).
      rewrite rep_pred_l_conjSO. rewrite SOturnst_conjSO. apply iff_refl.
    intros beta lbeta Hl1. rewrite <- Hl1.
    assert (~ l1 = nil) as Hass. rewrite Hl1. discriminate.
    case_eq (app l1 l2).
      intros Hnil. rewrite Hl1 in Hnil. discriminate.
    intros gamma lgamma Hlgamma. rewrite <- Hlgamma.
    rewrite rep_pred_l_conjSO.
    rewrite rep_pred_l_conjSO.
    simpl. split; intros [H1 H2]; apply conj.
      apply conj. assumption. apply (IHl1 _ _ _ l2); try assumption.
      apply (IHl1 _ _ _ l2); try assumption.

      apply H1.
      destruct H1 as [H1 H3]. apply IHl1; try assumption.
      simpl. apply conj; assumption.
Qed.

Lemma lem_e22_pre2 : forall atm atm0 atm2 lP y W Iv Ip Ir,
  atm2 =passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm)) ->
  AT atm0 = true ->
  AT atm = true ->
  SOturnst W Iv Ip Ir (replace_pred_l atm2 lP (list_var (length lP) y) (vsS_syn_l (FOv_att_P_l atm0 lP) y)) <->
  SOturnst W Iv Ip Ir (replace_pred_l atm lP (list_var (length lP) y) (vsS_syn_l (FOv_att_P_l atm0 lP) y)).
Proof.
  induction atm; intros atm0 atm3 lP y W Iv Ip Ir Hat1 Hat2 Hat3; try discriminate.
    rewrite Hat1. simpl in *. apply iff_refl.

    pose proof (AT_conjSO_l _ _ Hat3) as Hata.
    pose proof (AT_conjSO_r _ _ Hat3) as Hatb.
    simpl in Hat1. rewrite passing_predSO_ll_app in Hat1.
      2 : (apply lem118'_length; assumption).
    rewrite Hat1. rewrite rep_pred_l_conjSO. simpl.
    split; intros H. apply lem_e25 in H. simpl in H.
      destruct H as [H1 H2].
      apply conj. apply (IHatm1 _ (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm1) (atm_passing_predSO_ll_llx atm1))));
      try assumption.
      reflexivity.

      apply (IHatm2 _ (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm2) (atm_passing_predSO_ll_llx atm2))));
      try assumption.
      reflexivity.
        apply lem118'_not_nil. assumption.
        apply lem118'_not_nil. assumption.
 apply lem_e25.
        apply lem118'_not_nil. assumption.
        apply lem118'_not_nil. assumption.

 simpl. 
      destruct H as [H1 H2].
      apply conj. apply (IHatm1 _ (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm1) (atm_passing_predSO_ll_llx atm1))));
      try assumption.
      reflexivity.

      apply (IHatm2 _ (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm2) (atm_passing_predSO_ll_llx atm2))));
      try assumption.
      reflexivity.
Qed.

Lemma lem_e22 : forall lP atm atm2  y W Iv Ip Ir,
  AT atm = true ->
  atm2 = passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm)
            (atm_passing_predSO_ll_llx atm)) ->
  SOturnst W Iv Ip Ir (replace_pred_l atm2 lP (list_var (length lP) y)
    (vsS_syn_l (FOv_att_P_l atm2 lP) y)) <->
  SOturnst W Iv Ip Ir (replace_pred_l atm lP (list_var (length lP) y)
    (vsS_syn_l (FOv_att_P_l atm lP) y)).
Proof.
  intros until 0. intros Hat1 Hat2.
  split ;intros H. apply (lem_e22_pre _ _ atm atm2);
    try assumption.
    apply (lem_e22_pre2 atm atm2 atm2); try assumption.
    rewrite Hat2. apply AT_passing_predSO_ll.
      apply lem118'_not_nil_lP. assumption.
      apply lem118'_not_nil_llx. assumption.
      apply lem118'_ex_nil_in_llv. assumption.

apply (lem_e22_pre _ _ atm atm2);
    try assumption.
    rewrite Hat2. apply AT_passing_predSO_ll.
      apply lem118'_not_nil_lP. assumption.
      apply lem118'_not_nil_llx. assumption.
      apply lem118'_ex_nil_in_llv. assumption.
    apply (lem_e22_pre2 atm atm atm2); try assumption.
Qed.

Lemma SOQFree_FO_frame_condition : forall beta P x cond,
  FO_frame_condition cond = true ->
  SOQFree beta = true ->
  SOQFree (replace_pred beta P x cond) = true.
Proof.
  intros until 0. intros Hun Hno.
  apply SOQFree_rep_pred. assumption.
  apply FO_frame_condition_SOQFree. assumption.
Qed.

Lemma SOQFree_FO_frame_condition_l : forall lP lx lcond beta,
  FO_frame_condition_l lcond = true ->
  SOQFree beta = true ->
  SOQFree (replace_pred_l beta lP lx lcond) = true.
Proof.
  induction lP; intros lx lcond beta Hun Hno.
    simpl. assumption.

    destruct lx. simpl. assumption. 
    destruct lcond. assumption.
    simpl in *. case_eq (FO_frame_condition s);
      intros Hun2; rewrite Hun2 in *. 2 : discriminate.
    apply SOQFree_FO_frame_condition. assumption.
    apply IHlP; assumption.
Qed.

Lemma SOQFree_instant_cons_empty' : forall beta alpha,
  SOQFree beta = true ->
  SOQFree (instant_cons_empty' alpha beta) = true.
Proof.
  unfold instant_cons_empty'.
  intros beta alpha Hno. apply SOQFree_FO_frame_condition_l.
  apply FO_frame_condition_l_empty_n. auto.
Qed.

Lemma lem_e2 : forall lP beta rel atm y xn W1 Iv1 Ip1 Ir1,
  REL rel = true ->
  AT atm = true -> 
ex_FOvar_var_ll y (FOv_att_P_l atm lP) = false ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  ~ att_allFO_var beta (Var xn)  ->
  ~ att_exFO_var beta (Var xn) ->
  closed_except beta (Var xn) ->

  var_in_SO (instant_cons_empty' (conjSO rel atm) beta) (Var xn) ->
  incl (preds_in (implSO (conjSO rel atm) beta)) lP ->
SOturnst W1 Iv1 Ip1 Ir1 (replace_pred_l  (implSO (conjSO rel atm)
        (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)
           (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)))
           (rev_seq (S (Nat.max (max_FOv (implSO (conjSO rel atm) beta)) xn))
              (length (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) beta))))))) lP
     (list_var (length lP) y) (vsS_syn_l (FOv_att_P_l (conjSO rel atm) lP) y)) <->
SOturnst W1 Iv1 Ip1 Ir1 (replace_pred_l (implSO (conjSO rel (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm))))
        (newnew_pre (instant_cons_empty'
              (conjSO rel (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm))))
              beta)
           (rem_FOv (Var xn) (FOvars_in  (instant_cons_empty'  (conjSO rel
              (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm)))) beta))
              )
           (rev_seq (S (Nat.max (max_FOv (implSO (conjSO rel
                             (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm))))
                          beta)) xn))
              (length (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel
                             (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm))))
                          beta))))))) lP (list_var (length lP) y)
     (vsS_syn_l (FOv_att_P_l (conjSO rel (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm))))
           lP) y)).
Proof.
  intros lP beta rel atm y xn W Iv Ip Ir Hrel Hat Hex2 Hun Hno Hat1 Hat2 Hc Hocc Hin.
  rewrite lem_e3.
  do 2 rewrite rep_pred_l_implSO.
  do 2 rewrite rep_pred_l_conjSO.
  all : try assumption.
  split ;intros SOt [H1 H2].
    simpl in SOt. apply lem_e5; try assumption.
      apply SOQFree_newnew_pre.
      apply SOQFree_instant_cons_empty'. assumption.
    simpl.

    rewrite max_FOv_implSO.
    rewrite max_FOv_conjSO.
    rewrite lem118'_max_FOv.
    rewrite max_FOv_implSO in SOt.
    rewrite max_FOv_conjSO in SOt.
    apply SOt. apply conj.
      rewrite rep_pred_l_REL; try assumption.
      rewrite rep_pred_l_REL in H1; try assumption.

      rewrite FOv_att_P_l_conjSO_rel.
      rewrite FOv_att_P_l_conjSO_rel in H2.
      all : try assumption.

      apply lem_e22 with (atm2 :=
        (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) 
        (atm_passing_predSO_ll_llx atm))) ); try assumption.
      reflexivity.

    simpl in SOt. apply lem_e5; try assumption.
      apply SOQFree_newnew_pre.
      apply SOQFree_instant_cons_empty'. assumption.
    simpl.

    rewrite max_FOv_implSO in SOt.
    rewrite max_FOv_conjSO in SOt.
    rewrite lem118'_max_FOv in SOt.
    rewrite max_FOv_implSO.
    rewrite max_FOv_conjSO.
    apply SOt. apply conj.
      rewrite rep_pred_l_REL; try assumption.
      rewrite rep_pred_l_REL in H1; try assumption.

      rewrite FOv_att_P_l_conjSO_rel.
      rewrite FOv_att_P_l_conjSO_rel in H2.
      all : try assumption.

      apply lem_e22 with (atm := atm) (atm2 :=
        (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) 
        (atm_passing_predSO_ll_llx atm))) ); try assumption.
      reflexivity.
Qed.

Lemma lem_e2_atm : forall lP beta atm y xn W1 Iv1 Ip1 Ir1,
  AT atm = true -> 
ex_FOvar_var_ll y (FOv_att_P_l atm lP) = false ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  ~ att_allFO_var beta (Var xn) ->
  ~ att_exFO_var beta (Var xn) ->
  closed_except beta (Var xn) ->

  var_in_SO (instant_cons_empty' atm beta) (Var xn) ->
  incl (preds_in (implSO atm beta)) lP ->
SOturnst W1 Iv1 Ip1 Ir1 (replace_pred_l  (implSO atm
        (newnew_pre (instant_cons_empty' atm beta)
           (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta)))
           (rev_seq (S (Nat.max (max_FOv (implSO atm beta)) xn))
              (length (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta))))))) lP
     (list_var (length lP) y) (vsS_syn_l (FOv_att_P_l atm lP) y)) <->
SOturnst W1 Iv1 Ip1 Ir1 (replace_pred_l (implSO ( (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm))))
        (newnew_pre (instant_cons_empty'
              ((passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm))))
              beta)
           (rem_FOv (Var xn) (FOvars_in  (instant_cons_empty'  (
              (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm)))) beta))
              )
           (rev_seq (S (Nat.max (max_FOv (implSO (
                             (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm))))
                          beta)) xn))
              (length (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (
                             (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm))))
                          beta))))))) lP (list_var (length lP) y)
     (vsS_syn_l (FOv_att_P_l ((passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm))))
           lP) y)).
Proof.
  intros lP beta atm y xn W Iv Ip Ir Hat Hex2 Hun Hno Hat1 Hat2 Hc Hocc Hin.
  rewrite lem_e3_atm.
  do 2 rewrite rep_pred_l_implSO.
  all : try assumption.
  split ;intros SOt H2.
    simpl in SOt. apply lem_e5_atm; try assumption.
      apply SOQFree_newnew_pre.
      apply SOQFree_instant_cons_empty'. assumption.
    simpl.

    rewrite max_FOv_implSO.
    rewrite lem118'_max_FOv.
    rewrite max_FOv_implSO in SOt.
    apply SOt.

      apply lem_e22 with (atm2 :=
        (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) 
        (atm_passing_predSO_ll_llx atm))) ); try assumption.
      reflexivity. assumption.

    simpl in SOt. apply lem_e5_atm; try assumption.
      apply SOQFree_newnew_pre.
      apply SOQFree_instant_cons_empty'. assumption.
    simpl.

    rewrite max_FOv_implSO in SOt.
    rewrite lem118'_max_FOv in SOt.
    rewrite max_FOv_implSO.
    apply SOt.

      apply lem_e22 with (atm := atm) (atm2 :=
        (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) 
        (atm_passing_predSO_ll_llx atm))) ); try assumption.
      reflexivity. assumption.
Qed.

Lemma is_in_FOvar_atm_passing_predSO_ll_gen : forall atm P x,
  AT atm = true ->
  In x (FOv_att_P (passing_conj (passing_predSO_ll
      (atm_passing_predSO_ll_lP atm) 
      (atm_passing_predSO_ll_llx atm))) P) <->
  In x (FOv_att_P atm P).
Proof.
  induction atm; intros P x Hat; try discriminate. firstorder.
  simpl in *. if_then_else_hyp. 
  rewrite passing_predSO_ll_app. rewrite FOv_att_P_passing_conj_app.
  split; intros HH; apply in_app_or in HH; apply in_or_app;
    firstorder.  
  apply lem118'_length. auto.
Qed.

Lemma lem118'_ex_FOvar_var_ll  : forall lP atm y,
  AT atm = true ->
  ex_FOvar_var_ll y (FOv_att_P_l (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm)
      (atm_passing_predSO_ll_llx atm))) lP) =
  ex_FOvar_var_ll y (FOv_att_P_l atm lP).
Proof.
  induction lP; intros atm y Hat. reflexivity.
  simpl. rewrite IHlP.
  destruct (    in_dec FOvariable_dec y
      (FOv_att_P
         (passing_conj
            (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm))) a));
destruct (in_dec FOvariable_dec y (FOv_att_P atm a)); auto. 
    apply (is_in_FOvar_atm_passing_predSO_ll_gen atm) in i. contradiction. auto.
    apply (is_in_FOvar_atm_passing_predSO_ll_gen atm) in i. contradiction. auto.
    auto.
Qed.

Lemma lem118'_x_occ_instant_cons_empty' : forall atm rel beta x,
AT atm = true ->
REL rel = true ->
var_in_SO
  (instant_cons_empty'
     (conjSO rel (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm))))
     beta) x = 
var_in_SO (instant_cons_empty' (conjSO rel atm) beta) x .
Proof.
  unfold instant_cons_empty'. simpl.
  intros atm rel beta x Hat Hrel.
  rewrite (preds_in_rel rel Hrel). simpl.
  rewrite list_rel_compl_passing_predSO_ll. 
  rewrite <- lem118'_preds_in.
  reflexivity.
  assumption.
  apply lem118'_length. assumption.
  apply lem118'_ex_nil_in_llv. assumption.
Qed.

Lemma lem118'_x_occ_instant_cons_empty'_atm : forall atm beta x,
AT atm = true ->
var_in_SO
  (instant_cons_empty'
     ((passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm))))
     beta) x = 
var_in_SO (instant_cons_empty' atm beta) x .
Proof.
  unfold instant_cons_empty'. simpl.
  intros atm beta x Hat.
  rewrite list_rel_compl_passing_predSO_ll. 
  rewrite <- lem118'_preds_in.
  reflexivity.
  assumption.
  apply lem118'_length. assumption.
  apply lem118'_ex_nil_in_llv. assumption.
Qed.

Lemma vsSahlq_instant_aim1_fwd4_closer2_REV_gen : forall lx lP beta rel atm y xn W Iv Ip Ir,
  REL rel = true ->
  AT atm = true -> 
ex_FOvar_var_ll y (FOv_att_P_l atm lP) = false ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  ~ att_allFO_var beta (Var xn) ->
  ~ att_exFO_var beta (Var xn) ->
  closed_except beta (Var xn) ->

  var_in_SO (instant_cons_empty' (conjSO rel atm) beta) (Var xn) ->
  incl (preds_in (implSO (conjSO rel atm) beta)) lP ->
  SOturnst W Iv Ip Ir (replace_pred_l (list_closed_allFO (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)  
      (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) beta)) xn))
        (length       (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) beta))))))) lx)
    lP (list_var (length lP) y)
    (vsS_syn_l (FOv_att_P_l (conjSO rel atm) lP) y)) ->
  SOturnst W Iv Ip Ir (list_closed_SO (list_closed_allFO
      (implSO (conjSO rel atm) beta) lx) lP).
Proof.
  intros lx lP beta rel atm y xn W Iv Ip Ir Hrel Hat Hex2 Hun Hno Hat1 Hat2 Hc Hocc Hin SOt.
  apply lem_e1; try assumption.
  apply vsSahlq_instant_aim1_fwd4_closer2_REV with (lP2 := (atm_passing_predSO_ll_lP atm))
    (llx2 :=(atm_passing_predSO_ll_llx atm)) (y := y) (xn := xn); try assumption.
    reflexivity. apply lem118'_length. assumption.
    apply lem118'_not_nil_lP. assumption.
    apply lem118'_ex_nil_in_llv. assumption.
    rewrite lem118'_ex_FOvar_var_ll; assumption.
    rewrite lem118'_x_occ_instant_cons_empty'; assumption.

    simpl in *. rewrite (preds_in_rel rel Hrel) in *. simpl in *.
    pose proof Hin as Hin'.
    apply incl_app_rev_l in Hin.
    apply incl_app_rev_r in Hin'.
    apply incl_app.
    rewrite incl_preds_in_passing_predSO_ll.
    apply (incl_trans _ _ _ _ (lem118'_incl atm Hat)); auto.
    apply lem118'_length. assumption.
    apply lem118'_ex_nil_in_llv. assumption.
    auto.

    rewrite rep_pred_l_list_closed_allFO in *.
    apply (equiv_list_closed_allFO ((replace_pred_l
              (implSO (conjSO rel atm)
                 (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)
                    (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)))
                    (rev_seq (S (Nat.max (max_FOv (implSO (conjSO rel atm) beta)) xn))
                       (length
                          (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) beta))
                             ))))) lP (list_var (length lP) y)
              (vsS_syn_l (FOv_att_P_l (conjSO rel atm) lP) y)))).
    intros W1 Iv1 Ip1 Ir1.
    apply lem_e2; assumption.
    assumption.
Qed.

Lemma vsSahlq_instant_aim1_fwd4_closer2_REV_gen_atm : forall lx lP beta atm y xn W Iv Ip Ir,
  AT atm = true -> 
ex_FOvar_var_ll y (FOv_att_P_l atm lP) = false ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  ~ att_allFO_var beta (Var xn) ->
  ~ att_exFO_var beta (Var xn) ->
  closed_except beta (Var xn) ->

  var_in_SO (instant_cons_empty' atm beta) (Var xn) ->
  incl (preds_in (implSO atm beta)) lP ->
  SOturnst W Iv Ip Ir (replace_pred_l (list_closed_allFO (implSO
    atm
    (newnew_pre (instant_cons_empty' atm beta)  
      (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta)))
      (rev_seq (S (max (max_FOv (implSO atm beta)) xn))
        (length       (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta))))))) lx)
    lP (list_var (length lP) y)
    (vsS_syn_l (FOv_att_P_l atm lP) y)) ->
  SOturnst W Iv Ip Ir (list_closed_SO (list_closed_allFO
      (implSO atm beta) lx) lP).

Proof.
  intros lx lP beta atm y xn W Iv Ip Ir Hat Hex2 Hun Hno Hat1 Hat2 Hc Hocc Hin SOt.
  apply lem_e1_atm; try assumption.
  apply vsSahlq_instant_aim1_fwd4_closer2_REV_atm with (lP2 := (atm_passing_predSO_ll_lP atm))
    (llx2 :=(atm_passing_predSO_ll_llx atm)) (y := y) (xn := xn); try assumption.
    reflexivity. apply lem118'_length. assumption.
    apply lem118'_not_nil_lP. assumption.
    apply lem118'_ex_nil_in_llv. assumption.
    rewrite lem118'_ex_FOvar_var_ll; assumption.
    rewrite lem118'_x_occ_instant_cons_empty'_atm; assumption.

    simpl in *.
    pose proof Hin as Hin'.
    apply incl_app_rev_l in Hin.
    apply incl_app_rev_r in Hin'.
    apply incl_app. rewrite incl_preds_in_passing_predSO_ll.
    apply (incl_trans _ _ _ _ (lem118'_incl atm Hat)); auto.
    apply lem118'_length. assumption.
    apply lem118'_ex_nil_in_llv. assumption. auto.


    rewrite rep_pred_l_list_closed_allFO in *.
    apply (equiv_list_closed_allFO ((replace_pred_l
              (implSO atm
                 (newnew_pre (instant_cons_empty' atm beta)
                    (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta)))
                    (rev_seq (S (Nat.max (max_FOv (implSO atm beta)) xn))
                       (length
                          (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta))
                             ))))) lP (list_var (length lP) y)
              (vsS_syn_l (FOv_att_P_l atm lP) y)))).
    intros W1 Iv1 Ip1 Ir1.
    apply lem_e2_atm; assumption.
    assumption.
Qed.

(* ---------------------------- *)

Lemma hopeful3_REV : forall lx lP beta alpha rel atm y xn W Iv Ip Ir,
  REL rel = true ->
  AT atm = true ->
ex_FOvar_var_ll y (FOv_att_P_l atm lP) = false ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  ~ att_allFO_var beta (Var xn) ->
  ~ att_exFO_var beta (Var xn) ->
  closed_except beta (Var xn) ->
  var_in_SO (instant_cons_empty' (conjSO rel atm) beta) (Var xn) ->
  incl (preds_in (implSO (conjSO rel atm) beta)) lP ->
  (exists P, Pred_in_SO alpha P) ->
 (forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir alpha <-> SOturnst W Iv Ip Ir (list_closed_allFO (implSO (conjSO rel atm) beta) lx)) ->
  SOturnst W Iv Ip Ir (replace_pred_l (list_closed_allFO (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)  
      (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) beta)) xn))
        (length       (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) beta))))))) lx)
    lP (list_var (length lP) y)
    (vsS_syn_l (FOv_att_P_l (conjSO rel atm) lP) y)) ->
  SOturnst W Iv Ip Ir (list_closed_SO alpha lP).
Proof.
  intros lx lP beta alpha rel atm Hex y xn W Iv Ip Ir HREL HAT Hun Hno Hat1 Hat2
    Hc Hocc Hin Hpocc Hequiv SOt.
  apply vsSahlq_instant_aim1_fwd4_closer2_REV_gen in SOt; try assumption.
  pose proof (equiv_list_closed_SO lP  _ _ Hequiv) as H.
  apply H.
  assumption.
Qed.

Lemma hopeful3_REV_atm : forall lx lP beta alpha atm y xn W Iv Ip Ir,
  AT atm = true ->
ex_FOvar_var_ll y (FOv_att_P_l atm lP) = false ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  ~ att_allFO_var beta (Var xn) ->
  ~ att_exFO_var beta (Var xn) ->
  closed_except beta (Var xn) ->
  var_in_SO (instant_cons_empty' atm beta) (Var xn) ->
  incl (preds_in (implSO atm beta)) lP ->
  (exists P, Pred_in_SO alpha P) ->
 (forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir alpha <-> SOturnst W Iv Ip Ir (list_closed_allFO (implSO atm beta) lx)) ->
  SOturnst W Iv Ip Ir (replace_pred_l (list_closed_allFO (implSO
    atm
    (newnew_pre (instant_cons_empty' atm beta)  
      (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta)))
      (rev_seq (S (max (max_FOv (implSO atm beta)) xn))
        (length       (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta))))))) lx)
    lP (list_var (length lP) y)
    (vsS_syn_l (FOv_att_P_l atm lP) y)) ->
  SOturnst W Iv Ip Ir (list_closed_SO alpha lP).
Proof.
  intros lx lP beta alpha atm Hex y xn W Iv Ip Ir HAT Hun Hno Hat1 Hat2
    Hc Hocc Hin Hpocc Hequiv SOt.
  apply vsSahlq_instant_aim1_fwd4_closer2_REV_gen_atm in SOt; try assumption.
  pose proof (equiv_list_closed_SO lP  _ _ Hequiv) as H.
  apply H.
  assumption.
Qed.

Definition new_FOv_pp_pre2  (alpha : SecOrder)  : nat := 
  S (max_FOv alpha).

Lemma lem_f7 : forall alpha n,
  AT alpha = true ->
   (max_FOv alpha) <= n ->
  ~ In (Var (S n)) (FOvars_in alpha) .
Proof.
  intros alpha n H1 H2 H3. apply want19_pre in H3.
  unfold max_FOv in H2. lia.
Qed.

Lemma lem_f1'' : forall alpha,
AT alpha = true ->
  ~ In (Var (S (max_FOv alpha))) (FOvars_in alpha).
Proof.
  intros alpha Hat. apply lem_f7. assumption. lia. 
Qed.

Lemma replace_FOv_A_rel_atm : forall lv rel atm beta,
  REL rel = true ->
  AT atm = true ->
  existsT2 rel' atm',
    replace_FOv_A (conjSO rel atm) beta lv =  conjSO rel' atm' /\
    REL rel' = true /\
    AT atm' = true.
Proof.
  induction lv; intros rel atm beta HREL HAT.
    unfold replace_FOv_A. simpl.
    exists rel. exists atm.
    apply conj. reflexivity.
    apply conj; assumption.

    destruct (IHlv _ _ beta HREL HAT) as [rel' [atm' [Heq [HREL' HAT']]]].
    unfold replace_FOv_A in *.
    simpl.
    pose proof (same_struc_replace_FOv_max_conj (list_closed_exFO (conjSO rel atm) lv) beta a).
    pose proof (same_struc_trans _ _ _ H (same_struc_replace_FOv_max_conj_list_closed_exFO
              _ _ _ _)) as H1.
    pose proof (same_struc_replace_FOv_max_conj (list_closed_exFO (conjSO rel atm) lv)
      beta a) as H2.
    apply same_struc_comm in H1.
    pose proof (same_struc_trans _ _ _ H1 H2) as H3.
    apply same_struc_strip_exFO with (n := (length lv)) in H3.
    pose proof (same_struc_trans _ _ _ (same_struc_strip_exFO_list_closed
      _ _) H3) as H4.
    pose proof (same_struc_trans _ _ _ (same_struc_replace_FOv_max_conj _ _ _)
      H4) as H5.
    pose proof (same_struc_trans _ _ _ H5 (same_struc_replace_FOv_A_pre
         (length lv)
(strip_exFO_list
       (replace_FOv_max_conj (list_closed_exFO (conjSO rel atm) lv) beta a)
       (length lv)) _ beta)) as H6.
    apply same_struc_comm in H6.
    destruct (same_struc_conjSO_ex _ _ _ H6) as [rel'' [atm'' H']].
    rewrite H' in H6.
    pose proof (same_struc_conjSO_l _ _ _ _ H6) as H7.
    apply same_struc_conjSO_r in H6.
    apply same_struc_comm in H6.
    apply same_struc_comm in H7.
    exists rel''. exists atm''.
    apply conj.
      assumption.
      apply conj.
        apply same_struc_REL with (alpha := rel); assumption.
        apply same_struc_AT with (alpha := atm); assumption.
Defined.


Lemma vsS_preprocessing_Step1_1_againTRY'_withex'' : forall phi1 phi2 rel atm x lv,
  vsSahlq_ante phi1 ->
  uniform_pos phi2 ->
  REL rel = true ->
  AT atm = true ->
          incl (preds_in (conjSO rel atm)) (preds_in (ST phi1 x)) ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
      (Ir : W -> W -> Prop),
    SOturnst W Iv Ip Ir (ST phi1 x) <->
    SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv)) ->
existsT2 lv0 : list FOvariable,
     ((existsT2 atm0 : SecOrder,
         (AT atm0 = true) *
((~ In (Var (new_FOv_pp_pre2 atm0)) (FOvars_in atm0)) *
  ((existsT rel0 : SecOrder,
     REL rel0 = true /\
          incl (preds_in (conjSO rel0 atm0)) (preds_in (ST phi1 x)) /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (ST (mimpl phi1 phi2) x) <->
          SOturnst W Iv Ip Ir
            (list_closed_allFO (implSO (conjSO rel0 atm0) (ST phi2 x)) lv0))) +
       (incl (preds_in atm0) (preds_in (ST phi1 x)) /\
      forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir (ST (mimpl phi1 phi2) x) <->
      SOturnst W Iv Ip Ir (list_closed_allFO (implSO atm0 (ST phi2 x)) lv0)))))).
Proof.
  intros phi1 phi2 rel atm x lv Hvsa Hun HREL HAT Hin H.
  pose proof (equiv_implSO2 _ _ (ST phi2 x) H) as H1.
  pose proof (equiv3_3_struc2_2' lv (conjSO rel atm) (ST phi2 x)) as H2.
  pose proof (SOturnst_trans _ _ _ H1 H2) as H3.
  pose proof replace_FOv_A_rel_atm.
  destruct (replace_FOv_A_rel_atm lv rel atm (ST phi2 x) HREL HAT)
     as [rel' [atm' [H' [HREL' HAT']]]] .
  rewrite H' in *.
  exists (replace_FOv_A_list (conjSO rel atm) (ST phi2 x) lv).
  exists atm'.
  apply pair. assumption. apply pair.
unfold new_FOv_pp_pre2.

apply (lem_f1'' atm'); try assumption.
  left.
  exists rel'.
  apply conj. assumption.
  apply conj. 2: assumption.
    rewrite <- H'.
    rewrite preds_in_replace_FOv_A.
    assumption.
Defined.

Lemma vsS_preprocessing_Step1_3_againTRY'_withex' : forall phi1 phi2 atm x lv,
  vsSahlq_ante phi1 ->
  uniform_pos phi2 ->
  AT atm = true ->
  incl (preds_in (atm)) (preds_in (ST phi1 x))  ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
      (Ir : W -> W -> Prop),
    SOturnst W Iv Ip Ir (ST phi1 x) <->
    SOturnst W Iv Ip Ir (list_closed_exFO atm lv)) ->
existsT2 lv0 : list FOvariable,
   (existsT2 atm0 : SecOrder,
       (AT atm0 = true) *
((~ In (Var (new_FOv_pp_pre2 atm0)) (FOvars_in atm0)) *

    ((existsT rel0 : SecOrder,
       REL rel0 = true /\
      incl (preds_in (conjSO rel0 atm0)) (preds_in (ST phi1 x)) /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (ST (mimpl phi1 phi2) x) <->
          SOturnst W Iv Ip Ir
            (list_closed_allFO (implSO (conjSO rel0 atm0) (ST phi2 x)) lv0))) +
     (incl (preds_in atm0) (preds_in (ST phi1 x)) /\
     forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir (ST (mimpl phi1 phi2) x) <->
      SOturnst W Iv Ip Ir (list_closed_allFO (implSO atm0 (ST phi2 x)) lv0))))).
Proof.
  intros phi1 phi2 atm x lv Hvsa Hun HAT Hin H.
  pose proof (equiv_implSO2 _ _ (ST phi2 x) H) as H1.
  pose proof (equiv3_3_struc2_2' lv atm (ST phi2 x)) as H2.
  pose proof (SOturnst_trans _ _ _ H1 H2) as H3.
  pose proof (same_struc_replace_FOv_A atm (ST phi2 x) lv) as H4.
  apply same_struc_comm in H4.
  apply same_struc_AT in H4. 2 : assumption.
  exists (replace_FOv_A_list atm (ST phi2 x) lv).
  exists (replace_FOv_A atm (ST phi2 x) lv).
  apply pair. assumption.
  apply pair.
   unfold new_FOv_pp_pre2. 
    apply (lem_f1'' ). assumption.

  right.
  apply conj.
    rewrite preds_in_replace_FOv_A. assumption.
  assumption.
Defined.

Lemma vsS_preprocessing_Step1_pre_againTRY'_withex' : forall phi1 phi2 x,
  vsSahlq_ante phi1 ->
  uniform_pos phi2  ->
  existsT2 lv : list FOvariable,
   (existsT2 atm : SecOrder,
       (AT atm = true) *
((~ In (Var (new_FOv_pp_pre2 atm)) (FOvars_in atm)) *
    ((existsT rel : SecOrder,
     REL rel = true /\
          incl (preds_in (conjSO rel atm)) (preds_in (ST phi1 x)) /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (ST (mimpl phi1 phi2) x) <->
          SOturnst W Iv Ip Ir (list_closed_allFO (implSO (conjSO rel atm) (ST phi2 x)) lv))) +

    (incl (preds_in atm) (preds_in (ST phi1 x)) /\
      forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir (ST (mimpl phi1 phi2) x) <->
      SOturnst W Iv Ip Ir (list_closed_allFO (implSO atm (ST phi2 x)) lv))))).
Proof.
  intros phi1 phi2 x Hvsa Hun.
  pose proof (preprocess_vsSahlq_ante_againTRY (ST phi1 x)
      (vsSahlq_ante_conjSO_exFO_relatSO _ _ Hvsa) (ex_P_ST phi1 x)) as H1.
  destruct H1 as [lv [atm [HAT [ [rel [HREL [Hin H]]] | [Hin H] ]]]].
  
    apply vsS_preprocessing_Step1_1_againTRY'_withex'' with (phi2 := phi2) in H; try assumption.
    apply vsS_preprocessing_Step1_3_againTRY'_withex' with (phi2 := phi2) in H; try assumption.
Defined.

Lemma lem_f4 : forall atm x P,
AT atm = true ->
  ~ In x (FOvars_in atm)->
~ In x (FOv_att_P atm P) .
Proof.
  intros atm x P H1 H2 H3. apply H2.
  pose proof (incl_FOv_att_P atm P) as H4.
  eapply in_incl. apply H3. auto.
Qed.

Lemma lem_f3 : forall lP atm x,
AT atm = true ->
  ~ In x (FOvars_in atm) ->
ex_FOvar_var_ll x (FOv_att_P_l atm lP) = false.
Proof.
  induction lP; intros atm x Hat H. auto.
  simpl in *. destruct (in_dec FOvariable_dec x (FOv_att_P atm a)).
  eapply lem_f4 in H. contradiction (H i). auto. auto.
Qed.

Lemma hopeful4_REV'_withex'_FULL : forall lP xn phi1 phi2,
  vsSahlq_ante phi1 ->
  uniform_pos phi2  ->
  incl (preds_in (ST (mimpl phi1 phi2) (Var xn))) lP  ->
  existsT2 (lx : list FOvariable) (atm : SecOrder),
    (AT atm = true) *
    ((existsT rel,
      REL rel = true /\
      incl (preds_in (conjSO rel atm)) (preds_in (ST phi1 (Var xn)))  /\
forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (replace_pred_l (list_closed_allFO (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))  
      (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn))))))))) lx)
    lP (list_var (length lP) (Var (new_FOv_pp_pre2 atm)))
    (vsS_syn_l (FOv_att_P_l (conjSO rel atm) lP) (Var (new_FOv_pp_pre2 atm)))) <->
  SOturnst W Iv Ip Ir (list_closed_SO (ST (mimpl phi1 phi2) (Var xn)) lP)) +

     (incl (preds_in atm) (preds_in (ST phi1 (Var xn))) /\
forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (replace_pred_l (list_closed_allFO (implSO atm
    (newnew_pre (instant_cons_empty' atm (ST phi2 (Var xn)))  
      (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))))
      (rev_seq (S (max (max_FOv (implSO atm (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn))))))))) lx)
    lP (list_var (length lP) (Var (new_FOv_pp_pre2 atm)))
    (vsS_syn_l (FOv_att_P_l atm lP) (Var (new_FOv_pp_pre2 atm)))) <->
  SOturnst W Iv Ip Ir (list_closed_SO (ST (mimpl phi1 phi2) (Var xn)) lP))).
Proof.
  intros lP xn phi1 phi2 Hvs Hun Hin0.
  destruct (vsS_preprocessing_Step1_pre_againTRY'_withex' _ _ (Var xn) Hvs Hun)
    as [lv [atm [HAT [Hex [ [rel [HREL [Hin SOt]]]  | [Hin SOt]  ]]]]].
    exists lv. exists atm.
    apply pair. assumption.
    left. exists rel. apply conj. assumption.
    apply conj. assumption.
    intros W Iv Ip Ir.  
split; intros H.
    apply hopeful3_REV with (alpha := (ST (mimpl phi1 phi2) (Var xn))) in H ;
      try assumption.
        apply lem_f3; assumption.
      apply uni_pos__SO. assumption.
      apply SOQFree_ST. 

      apply att_allFO_var_ST.
      apply att_exFO_var_ST.
      apply closed_except_ST.
      apply var_in_SO_instant_cons_empty'.
        apply x_occ_in_alpha_ST.

      assert (incl 
          (preds_in (implSO (conjSO rel atm) (ST phi2 (Var xn)))) 
          (preds_in (implSO (ST phi1 (Var xn)) (ST phi2 (Var xn)))) ) as HH1.
        simpl. apply incl_app_gen. 
        apply Hin. apply incl_refl.
      apply (incl_trans _ _ _ _ HH1 Hin0).

      apply ex_P_occ_in_alpha_ST.
        apply hopeful3 with (alpha := (ST (mimpl phi1 phi2) (Var xn)));
      try assumption.
      apply uni_pos__SO. assumption.
      apply SOQFree_ST.

      apply att_allFO_var_ST.
      apply att_exFO_var_ST.
      apply closed_except_ST.
      apply var_in_SO_instant_cons_empty'.
        apply x_occ_in_alpha_ST.

      assert (incl 
          (preds_in (implSO (conjSO rel atm) (ST phi2 (Var xn)))) 
          (preds_in (implSO (ST phi1 (Var xn)) (ST phi2 (Var xn))))) as HH1.
        simpl. apply incl_app_gen.
        apply Hin. apply incl_refl.
      apply (incl_trans _ _ _ _ HH1 Hin0).

      apply ex_P_occ_in_alpha_ST.

    exists lv. exists atm.
    apply pair. assumption.
    right.
    apply conj. assumption.
    intros W Iv Ip Ir.
split; intros H.
    apply hopeful3_REV_atm with (alpha := (ST (mimpl phi1 phi2) (Var xn))) in H;
      try assumption.
      apply lem_f3; assumption.

      apply uni_pos__SO. assumption.
      apply SOQFree_ST.

      apply att_allFO_var_ST.
      apply att_exFO_var_ST.
      apply closed_except_ST.
      apply var_in_SO_instant_cons_empty'.
        apply x_occ_in_alpha_ST.

      assert (incl 
          (preds_in (implSO atm (ST phi2 (Var xn)))) 
          (preds_in (implSO (ST phi1 (Var xn)) (ST phi2 (Var xn)))) ) as HH1.
        simpl. apply incl_app_gen.
        apply Hin. apply incl_refl.
      apply (incl_trans _ _ _ _ HH1 Hin0).

      apply ex_P_occ_in_alpha_ST.

    apply hopeful3_atm with (alpha := (ST (mimpl phi1 phi2) (Var xn)));
      try assumption.
      apply uni_pos__SO. assumption.
      apply SOQFree_ST.

      apply att_allFO_var_ST.
      apply att_exFO_var_ST.
      apply closed_except_ST.
      apply var_in_SO_instant_cons_empty'.
        apply x_occ_in_alpha_ST.

      assert (incl 
          (preds_in (implSO atm (ST phi2 (Var xn)))) 
          (preds_in (implSO (ST phi1 (Var xn)) (ST phi2 (Var xn)))) ) as HH1.
        simpl. apply incl_app_gen.
        apply Hin. apply incl_refl.
      apply (incl_trans _ _ _ _ HH1 Hin0).

      apply ex_P_occ_in_alpha_ST.
Defined.
 


Lemma hopeful4_REV'_withex'_FULL_allFO : forall lP xn phi1 phi2,
  vsSahlq_ante phi1 ->
  uniform_pos phi2  ->
  incl (preds_in (ST (mimpl phi1 phi2) (Var xn))) lP  ->
  existsT2 lx atm,
    (AT atm = true) *
    ((existsT rel,
      REL rel = true /\
      incl (preds_in (conjSO rel atm)) (preds_in (ST phi1 (Var xn)))  /\
forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (allFO (Var xn) (replace_pred_l (list_closed_allFO (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))  
      (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn))))))))) lx)
    lP (list_var (length lP) (Var (new_FOv_pp_pre2 atm)))
    (vsS_syn_l (FOv_att_P_l (conjSO rel atm) lP) (Var (new_FOv_pp_pre2 atm))))) <->
  SOturnst W Iv Ip Ir (allFO (Var xn) (list_closed_SO (ST (mimpl phi1 phi2) (Var xn)) lP))) +

     (incl (preds_in atm) (preds_in (ST phi1 (Var xn)))  /\
forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (allFO (Var xn) (replace_pred_l (list_closed_allFO (implSO atm
    (newnew_pre (instant_cons_empty' atm (ST phi2 (Var xn)))  
      (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))))
      (rev_seq (S (max (max_FOv (implSO atm (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn))))))))) lx)
    lP (list_var (length lP) (Var (new_FOv_pp_pre2 atm)))
    (vsS_syn_l (FOv_att_P_l atm lP) (Var (new_FOv_pp_pre2 atm))))) <->
  SOturnst W Iv Ip Ir (allFO (Var xn) (list_closed_SO (ST (mimpl phi1 phi2) (Var xn)) lP)))).
Proof.
  intros lP xn phi1 phi2 H1 H2 H3.
  destruct (hopeful4_REV'_withex'_FULL lP xn phi1 phi2 H1 H2 H3) as [lx [atm [Hat [ [rel [Hrel [Hin SOt]]]| [Hin SOt] ]]]];
  exists lx; exists atm; apply pair; try assumption; [left | right].
    exists rel. apply conj. assumption. apply conj. assumption.
    intros.
    apply equiv_allFO with (W := W) (Iv := Iv) (Ip := Ip) (Ir := Ir) (x := (Var xn)) in SOt.
    assumption.


    apply conj. assumption. intros.
    apply equiv_allFO with (W := W) (Iv := Iv) (Ip := Ip) (Ir := Ir) (x := (Var xn)) in SOt.
    assumption.
Defined.

Lemma hopeful4_REV'_withex'_FULL_allFO_in : forall lP xn phi1 phi2,
  vsSahlq_ante phi1 ->
  uniform_pos phi2  ->
  incl (preds_in (ST (mimpl phi1 phi2) (Var xn))) lP ->
  existsT2 lx atm,
    (AT atm = true) *
    ((existsT rel,
      REL rel = true /\
      incl (preds_in (conjSO rel atm)) (preds_in (ST phi1 (Var xn))) /\
forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (allFO (Var xn) (replace_pred_l (list_closed_allFO (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))  
      (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn))))))))) lx)
    lP (list_var (length lP) (Var (new_FOv_pp_pre2 atm)))
    (vsS_syn_l (FOv_att_P_l (conjSO rel atm) lP) (Var (new_FOv_pp_pre2 atm))))) <->
  SOturnst W Iv Ip Ir (list_closed_SO (allFO (Var xn) (ST (mimpl phi1 phi2) (Var xn))) lP)) +

     (incl (preds_in atm) (preds_in (ST phi1 (Var xn))) /\
forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (allFO (Var xn) (replace_pred_l (list_closed_allFO (implSO atm
    (newnew_pre (instant_cons_empty' atm (ST phi2 (Var xn)))  
      (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) )
      (rev_seq (S (max (max_FOv (implSO atm (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (Var xn)(FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn))))))))) lx)
    lP (list_var (length lP) (Var (new_FOv_pp_pre2 atm)))
    (vsS_syn_l (FOv_att_P_l atm lP) (Var (new_FOv_pp_pre2 atm))))) <->
  SOturnst W Iv Ip Ir (list_closed_SO (allFO (Var xn) (ST (mimpl phi1 phi2) (Var xn))) lP))).
Proof.
  intros lP xn phi1 phi2 H1 H2 H3.
  destruct (hopeful4_REV'_withex'_FULL_allFO lP xn phi1 phi2 H1 H2 H3) as [lx [atm [Hat [ [rel [Hrel [Hin SOt]]]| [Hin SOt] ]]]];
  exists lx; exists atm; apply pair; try assumption; [left | right].
    exists rel. apply conj. assumption. apply conj. assumption.
    intros. split; intros HH. apply equiv_list_closed_SO_allFO.
      apply SOt. assumption.

      apply equiv_list_closed_SO_allFO in HH. apply SOt. assumption.

    apply conj. assumption. intros.
    split; intros HH. apply equiv_list_closed_SO_allFO.
      apply SOt. assumption.

      apply equiv_list_closed_SO_allFO in HH. apply SOt. assumption.
Defined.

Lemma vsSahlq_full_SO_pre : forall xn phi1 phi2,
  vsSahlq_ante phi1 ->
  uniform_pos phi2  ->
  existsT2 lx atm,
    (AT atm = true) *
    ((existsT rel,
      REL rel = true /\
      incl (preds_in (conjSO rel atm)) (preds_in (ST phi1 (Var xn))) /\
forall W Iv Ip Ir,

  SOturnst W Iv Ip Ir (allFO (Var xn) (replace_pred_l (list_closed_allFO (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))  
      (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn))))))))) lx)
    (preds_in (ST (mimpl phi1 phi2) (Var xn))) (list_var (length (preds_in (ST (mimpl phi1 phi2) (Var xn)))) (Var (new_FOv_pp_pre2 atm)))
    (vsS_syn_l (FOv_att_P_l (conjSO rel atm) (preds_in (ST (mimpl phi1 phi2) (Var xn)))) (Var (new_FOv_pp_pre2 atm))))) <->
  SOturnst W Iv Ip Ir (uni_closed_SO (allFO (Var xn) (ST (mimpl phi1 phi2) (Var xn))))) +

     (incl (preds_in atm) (preds_in (ST phi1 (Var xn)))  /\
forall W Iv Ip Ir,

  SOturnst W Iv Ip Ir (allFO (Var xn) (replace_pred_l (list_closed_allFO (implSO atm
    (newnew_pre (instant_cons_empty' atm (ST phi2 (Var xn)))  
      (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))))
      (rev_seq (S (max (max_FOv (implSO atm (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn))))))))) lx)
    (preds_in (ST (mimpl phi1 phi2) (Var xn))) (list_var (length (preds_in (ST (mimpl phi1 phi2) (Var xn)))) (Var (new_FOv_pp_pre2 atm)))
    (vsS_syn_l (FOv_att_P_l atm (preds_in (ST (mimpl phi1 phi2) (Var xn)))) (Var (new_FOv_pp_pre2 atm))))) <->
  SOturnst W Iv Ip Ir (uni_closed_SO (allFO (Var xn) (ST (mimpl phi1 phi2) (Var xn)))))).
Proof.
  intros xn phi1 phi2 H1 H2. unfold uni_closed_SO in *. unfold uni_closed_SO.
  apply hopeful4_REV'_withex'_FULL_allFO_in; try assumption.
  simpl. apply incl_refl.
Defined.

Lemma vsSahlq_full_SO : forall xn phi1 phi2,
  vsSahlq_ante phi1 ->
  uniform_pos phi2  ->
  existsT (alpha : SecOrder),
FO_frame_condition alpha = true /\
forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir alpha <->
  SOturnst W Iv Ip Ir (uni_closed_SO (allFO (Var xn) (ST (mimpl phi1 phi2) (Var xn)))).
Proof.
  intros xn phi1 phi2 H1 H2.
  destruct (vsSahlq_full_SO_pre xn phi1 phi2 H1 H2) as  [lx [atm [Hat [[rel [Hrel [Hin SOt]]]| [Hin SOt] ]]]].
    exists (allFO (Var xn) (replace_pred_l
           (list_closed_allFO
              (implSO (conjSO rel atm)
                 (newnew_pre (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))
                    (rem_FOv (Var xn)
                       (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))))
                    (rev_seq
                       (S (Nat.max (max_FOv (implSO (conjSO rel atm) (ST phi2 (Var xn)))) xn))
                       (length
                          (rem_FOv (Var xn)
                             (FOvars_in
                                (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn))))
                             ))))) lx) (preds_in (ST (mimpl phi1 phi2) (Var xn)))
           (list_var (length (preds_in (ST (mimpl phi1 phi2) (Var xn))))
              (Var (new_FOv_pp_pre2 atm)))
           (vsS_syn_l (FOv_att_P_l (conjSO rel atm) (preds_in (ST (mimpl phi1 phi2) (Var xn))))
              (Var (new_FOv_pp_pre2 atm))))).
      apply conj.
apply FO_frame_condition_corresp; assumption.

      apply SOt.


    exists (allFO (Var xn) (replace_pred_l
           (list_closed_allFO
              (implSO atm
                 (newnew_pre (instant_cons_empty' atm (ST phi2 (Var xn)))
                    (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))))
                    (rev_seq (S (Nat.max (max_FOv (implSO atm (ST phi2 (Var xn)))) xn))
                       (length
                          (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn))))
                             ))))) lx) (preds_in (ST (mimpl phi1 phi2) (Var xn)))
           (list_var (length (preds_in (ST (mimpl phi1 phi2) (Var xn))))
              (Var (new_FOv_pp_pre2 atm)))
           (vsS_syn_l (FOv_att_P_l atm (preds_in (ST (mimpl phi1 phi2) (Var xn))))
              (Var (new_FOv_pp_pre2 atm))))).
      apply conj.
apply FO_frame_condition_corresp_atm; assumption.
      apply SOt.
Defined.