Add LoadPath "~/Nextcloud/Coq Files/Sahlqvist/Sahlq_Modules/vsSahlq local".

Require Export vsSahlq_instant17.

(* ---------------------------------------------------------- *)

Open Scope type_scope.

Fixpoint first_occ_P_n lP P n : nat :=
  match lP with
  | nil => 0
  | cons Q lP' => match P, Q with Pred Pn, Pred Qm =>
    if beq_nat Pn Qm then n else first_occ_P_n lP' P (S n)
  end end.

Definition first_occ_P lP P := first_occ_P_n lP P 1.

Lemma lem_d35 : forall lP n (l : list FOvariable) llx P l2,
  @at_gen _ l2 (first_occ_P_n lP P (S (S n))) (cons l llx) =
    @at_gen _ l2 (first_occ_P_n lP P (S n)) llx.
Proof.
  induction lP; intros n l llx [Pn] l2. reflexivity.
  simpl. destruct a as [Qm]. case_eq (beq_nat Pn Qm); intros Hbeq.
    simpl. destruct n; reflexivity.

    apply IHlP.
Qed.

Lemma lem_d35_gen : forall {A : Type} lP n (l : A) llx P l2,
  @at_gen _ l2 (first_occ_P_n lP P (S (S n))) (cons l llx) =
    @at_gen _ l2 (first_occ_P_n lP P (S n)) llx.
Proof.
  induction lP; intros n l llx [Pn] l2. reflexivity.
  simpl. destruct a as [Qm]. case_eq (beq_nat Pn Qm); intros Hbeq.
    simpl. destruct n; reflexivity.

    apply IHlP.
Qed.

Lemma lem_d44 : forall lP P n,
  is_in_pred P lP = false ->
  indicies_l2_pre lP P n = nil.
Proof.
  induction lP; intros [Pn] n Hin.
    simpl in *. reflexivity.

    simpl in *. destruct a as [Qm].
    case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *.
      discriminate.
    apply IHlP. assumption.
Qed.

Lemma lem_d51 : forall l1 l2 P,
  is_in_pred_l l1 l2 = true ->
  is_in_pred P l2 = false ->
  is_in_pred P l1 = false.
Proof.
  induction l1; intros l2 [Pn] H1 H2.
    simpl in *. reflexivity.

    simpl in *. destruct a as [Qm].
    case_eq (is_in_pred (Pred Qm) l2); intros H;    
      rewrite H in *. 2 : discriminate.
    case_eq (beq_nat Pn Qm);
      intros Hbeq. rewrite (beq_nat_true _ _ Hbeq) in *.
      rewrite H in *. discriminate.

      apply IHl1 with (l2 := l2); assumption.
Qed.

Lemma lem_d28 : forall l P Q W Iv Ip Ir pa,
  ~ P = Q ->
  SOturnst W Iv (altered_Ip Ip pa Q) Ir
    (passing_conj (passing_predSO_l P l)) <->
  SOturnst W Iv Ip Ir (passing_conj (passing_predSO_l P l)).
Proof.
  induction l; intros [Pn] [Qm] W Iv Ip Ir  pa Hneq.
    simpl. apply bi_refl.

    simpl passing_conj. case_eq (passing_predSO_l (Pred Pn) l).
      intros Hp. destruct a as [xn]. simpl. rewrite (beq_nat_comm).
      rewrite neq_beq_nat. apply bi_refl. assumption.

      intros beta lbeta Hp. rewrite <- Hp.
      destruct a as [xn]. do 2 rewrite SOturnst_conjSO.
      split; intros [H1 H2]; apply conj.
        simpl in *. rewrite beq_nat_comm in H1. rewrite neq_beq_nat in H1.
        assumption. assumption.

        apply (IHl (Pred Pn) (Pred Qm) W Iv Ip Ir pa Hneq).
        assumption.

      simpl in *. rewrite beq_nat_comm. rewrite neq_beq_nat; assumption.

        apply (IHl (Pred Pn) (Pred Qm) W Iv Ip Ir pa Hneq).
        assumption.
Qed.

Lemma lem_d29 : forall l2 l3 lP lx P a W Iv Ip Ir,
is_in_in_FOvar_ll ( l3) (l2) = true ->
 consistent_lP_lx (lP) (lx) ->
 consistent_lP_llv (lP) (l3) ->
 consistent_lP_llv (lP) (l2) ->
ex_nil_in_llv (l3) = false ->
SOturnst W Iv (altered_Ip_list Ip (vsS_pa_l Iv l3 lx) lP) Ir
        (passing_conj (passing_predSO_l P a)) ->
SOturnst W Iv (altered_Ip_list Ip (vsS_pa_l Iv l2 lx) lP) Ir
  (passing_conj (passing_predSO_l P a)).
Proof.
  induction l2; intros l3 lP lx P l W Iv Ip Ir Hin Hcon1 Hcon2 Hcon3 Hex SOt.
    simpl in *. destruct l3. assumption. discriminate.

    simpl in *. destruct lx. simpl in *. destruct l3; assumption.
    simpl in *. destruct lP. rewrite altered_Ip_list_nil in SOt.
      assumption.
    destruct l3. discriminate.
    simpl in *.
    case_eq (is_in_FOvar_l l0 a); intros Hin2; rewrite Hin2 in *.
      2 : discriminate.
    destruct p as [Qm]. destruct P as [Pn].
    case_eq (beq_nat Pn Qm); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq) in *.
      apply lem_try23 with (Ip1 := Ip).
      apply lem_try23 with (Ip2 := Ip) in SOt.
      apply lem_try18_pre with (l1 := l0).
        destruct l0; discriminate.

      assumption. assumption.

      assert (~ Pred Pn = Pred Qm) as Hneq.
        intros HH. inversion HH as [HH'].
        rewrite HH' in *. rewrite <- beq_nat_refl in *. discriminate.
      apply lem_d28. assumption.

      apply lem_d28 in SOt. apply IHl2 with (l3 := l3).
      all : try assumption.
      apply consistent_lP_lx_cons_rem_gen in Hcon1. assumption.
      apply consistent_lP_llv_cons_rem_gen in Hcon2. assumption.
      apply consistent_lP_llv_cons_rem_gen in Hcon3. assumption.
      destruct l0. discriminate. assumption.
Qed.

Lemma lem_try18''_tryinggenlP : forall l l2 l1 lP lP0 lx W Ip Ir Iv ,
   consistent_lP_lx lP lx ->
  consistent_lP_llv lP l1 -> 
  consistent_lP_llv lP l2 -> 
  length lP = length l1 ->
  length lP = length l2 ->
  length lP = length lx ->
  is_in_in_FOvar_ll l1 l2 = true ->
  ex_nil_in_llv l1 = false ->
  length lP0 = length l ->
  is_in_pred_l lP0 lP = true ->
   SOturnst W Iv (altered_Ip_list Ip (vsS_pa_l Iv l1 lx) lP) Ir 
      (passing_conj (passing_predSO_ll lP0 l)) ->
  SOturnst W Iv (altered_Ip_list Ip (vsS_pa_l Iv l2 lx) lP) Ir 
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
        simpl in *. assumption. discriminate.
        destruct lx. simpl in *. destruct l1. assumption.   
        simpl in *. assumption.
        simpl in *.
case_eq (is_in_pred p lP); intros Hin3; rewrite Hin3 in *.
    2 : discriminate.
   destruct lP. simpl in *. destruct p. discriminate.
    destruct p as [Pn]. destruct p0 as [Qm].
    case_eq (beq_nat Pn Qm); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq) in *.
      destruct l1. discriminate. simpl vsS_pa_l in SOt.
      rewrite altered_Ip_list_cons in SOt.
      apply lem_try18_pre with (l1 := l1).
        destruct l1; discriminate. simpl in Hin.
        case_eq (is_in_FOvar_l l1 l0); intros Hin6.
          reflexivity. rewrite Hin6 in *. discriminate.
        apply lem_try23 with 
          (Ip1 := (altered_Ip_list Ip (vsS_pa_l Iv l3 lx) lP)).
        assumption.

        apply lem_d28.
intros HH. inversion HH as [HH']. rewrite HH' in *. rewrite <- beq_nat_refl in *.
discriminate.

        destruct l1. discriminate. simpl vsS_pa_l in SOt.
        rewrite altered_Ip_list_cons in SOt.
        apply lem_d28 in SOt.
        apply lem_d29 with (l3 := l3).
          simpl in Hin. case_eq (is_in_FOvar_l l1 l0 );
            intros Hin6; rewrite Hin6 in *. 2 : discriminate.
          assumption. 
          apply consistent_lP_lx_cons_rem_gen in Hcon1. assumption.
          apply consistent_lP_llv_cons_rem_gen in Hcon2. assumption.
          apply consistent_lP_llv_cons_rem_gen in Hcon3. assumption.
          simpl in Hnil. destruct l1. discriminate. assumption. assumption.
intros HH. inversion HH as [HH']. rewrite HH' in *. rewrite <- beq_nat_refl in *.
discriminate.

        apply lem_d29 with (l3 := l1); assumption.

(* -- *)

intros beta lbeta Hp. rewrite Hp in *. rewrite <- Hp in *.
 simpl in *. destruct SOt as [SOt1 SOt2]. apply conj.
  apply lem_d29 with (l3 := l1); assumption.

  apply IHl with (l1 := l1); try assumption.
  inversion Hlength. reflexivity.
  case_eq (is_in_pred p lP); intros H; rewrite H in *.
    assumption. discriminate.
Qed.

Lemma lem_try9_tryinggenlP : forall lP lx llx0 lP0 W Iv Ip Ir beta gamma,
  ex_nil_in_llv (FOv_att_P_l gamma lP) = false ->
  consistent_lP_lx lP lx ->
  length lP = length lx ->
  length lP0 = length llx0 ->
  is_in_pred_l lP0 lP = true ->
  SOturnst W Iv (altered_Ip_list Ip (vsS_pa_l Iv (FOv_att_P_l gamma lP) lx) lP) Ir
      (passing_conj (passing_predSO_ll lP0 llx0)) ->
  SOturnst W Iv (altered_Ip_list Ip (vsS_pa_l Iv (FOv_att_P_l (conjSO beta gamma) lP) lx) lP) Ir
      (passing_conj (passing_predSO_ll lP0 llx0)).
Proof.
  intros until 0. intros Hun Hcon Hlength1 Hlength2 Hin SOt.
  apply lem_try18''_tryinggenlP with (l1 := FOv_att_P_l gamma lP); try assumption.
  apply consistent_lP_llv_FOv_att_P_l.
  apply consistent_lP_llv_FOv_att_P_l.
  apply length_FOv_att_P_l. apply length_FOv_att_P_l.
  apply lem_try33.
Qed.

Lemma is_in_FOvar_l_app_l1 : forall l1 l2 l3,
  is_in_FOvar_l l1 l3 = true ->
  is_in_FOvar_l l1 (app l3 l2) = true.
Proof.
  induction l1; intros l2 l3 H.
    reflexivity.

    simpl in *. case_eq (is_in_FOvar a l3);
      intros H2; rewrite H2 in *;
      rewrite is_in_FOvar_app;
      rewrite H2.
      apply IHl1; assumption.

      discriminate.
Qed.

Lemma is_in_in_FOvar_ll_FOv_att_P_l_conjSO_l : forall lP alpha beta,
  is_in_in_FOvar_ll (FOv_att_P_l alpha lP) (FOv_att_P_l (conjSO alpha beta) lP)  = true.
Proof.
  induction lP; intros alpha beta. reflexivity.
  simpl. rewrite IHlP. rewrite is_in_FOvar_l_app_l1. reflexivity.
  apply is_in_FOvar_l_refl.
Qed.

Lemma lem_try9_tryinggenlP_l : forall lP lx llx0 lP0 W Iv Ip Ir beta gamma,
  ex_nil_in_llv (FOv_att_P_l beta lP) = false ->
  consistent_lP_lx lP lx ->
  length lP = length lx ->
  length lP0 = length llx0 ->
  is_in_pred_l lP0 lP = true ->
  SOturnst W Iv (altered_Ip_list Ip (vsS_pa_l Iv (FOv_att_P_l beta lP) lx) lP) Ir
      (passing_conj (passing_predSO_ll lP0 llx0)) ->
  SOturnst W Iv (altered_Ip_list Ip (vsS_pa_l Iv (FOv_att_P_l (conjSO beta gamma) lP) lx) lP) Ir
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
  destruct a. simpl. assumption.
Qed.

Lemma is_in_pred_l_cap_pred_is_in_pred_l : forall l3 l2 l1,
  is_in_pred_l l1 l2 = true ->
  is_in_pred_l l3 (cap_pred l2 l1) =
  is_in_pred_l l3 l1.
Proof.
  induction l3; intros l2 l1 Hin. reflexivity.
  simpl. case_eq (is_in_pred a l1); intros Hin2.
    rewrite (is_in_pred_cap_pred l2 l1).
      apply IHl3. assumption.
      case_eq (is_in_pred a l2); intros Hin3.
        reflexivity.
      rewrite is_in_pred_l_tft with (P := a) in Hin.
      all : try assumption.

    rewrite is_in_cap_pred. reflexivity. assumption.
Qed.

Lemma lem_d61' : forall atm atm2 lP lP2 x  (W : Set) Iv Ip Ir (pa2 : W -> Prop),
  is_in_pred_l lP (preds_in atm) = true ->
  is_in_pred_l (preds_in atm) lP = true ->
  is_in_pred_l lP lP2 = true ->
  AT atm = true ->
  AT atm2 = true ->
  SOturnst W Iv (altered_Ip_list Ip
    (vsS_pa_l Iv (FOv_att_P_l atm2 lP) (list_Var (length lP) x)) lP) Ir atm ->
  SOturnst W Iv (altered_Ip_list Ip 
    (vsS_pa_l Iv (FOv_att_P_l atm2 lP2) (list_Var (length lP2) x)) lP2) Ir atm.
Proof.
  induction atm; intros atm0 lP lP2 x W Iv Ip Ir pa2 Hin1 Hin2 Hin3 Hat Hat0 SOt; try discriminate.
    simpl in *. destruct p as [Pn]. destruct f as [xn].
    simpl in *. case_eq (is_in_pred (Pred Pn) lP);
      intros Hin4; rewrite Hin4 in *. 2 : discriminate.
    rewrite lemma_try4. rewrite lemma_try4 in SOt. simpl in *.
    rewrite <- beq_nat_refl in *.  assumption.
    rewrite <- P_occ_in_l_is_in_pred_equiv. assumption.
    rewrite <- P_occ_in_l_is_in_pred_equiv.
    case_eq (is_in_pred (Pred Pn) lP2); intros Hin5.
      reflexivity.
    apply lem_d51 with (P := (Pred Pn)) in Hin3. rewrite Hin3 in *.
      discriminate.
      assumption.

    pose proof (AT_conjSO_l _ _ Hat).
    pose proof (AT_conjSO_r _ _ Hat).
    simpl in *. destruct SOt as [SOt1 SOt2].
    pose proof (is_in_pred_l_app_r _ _ _ Hin2).
    rewrite is_in_pred_l_app_comm_l in Hin2.
    apply is_in_pred_l_app_r in Hin2.
    apply conj. apply IHatm1 with (lP := cap_pred lP (preds_in atm1)); try assumption.
      apply is_in_pred_l_cap_pred_add. apply is_in_pred_l_refl.
      rewrite is_in_pred_l_cap_pred_is_in_pred_l. apply is_in_pred_l_refl.
        assumption.
      apply is_in_pred_l_cap_pred_add.
      apply (is_in_pred_l_trans (preds_in atm1) lP lP2).
        assumption.
        assumption.

      apply lem_a21; assumption.

apply IHatm2 with (lP := cap_pred lP (preds_in atm2)); try assumption.
      apply is_in_pred_l_cap_pred_add. apply is_in_pred_l_refl.
      rewrite is_in_pred_l_cap_pred_is_in_pred_l. apply is_in_pred_l_refl.
        assumption.
      apply is_in_pred_l_cap_pred_add.
      apply (is_in_pred_l_trans (preds_in atm2) lP lP2);
        assumption.

      apply lem_a21; assumption.
Qed.

Lemma lem_d58 : forall lP2 lx2 lP lx P x y,
  length lP = length lx ->
  length lP2 = length lx2 ->
  is_in_pred P lP2 = true ->
  consistent_lP_lx (cons P (app lP2 lP)) (cons x (app lx2 lx)) ->
  @at_gen _ y (first_occ_P lP2 P) lx2 = x.
Proof.
  induction lP2; intros lx2 lP lx [Pn] x y Hl1 Hl2 Hin1 Hcon.
    discriminate.

    destruct lx2. discriminate. simpl in *.
    destruct a as [Qm]. unfold first_occ_P. simpl in *.
    case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *.
      simpl in *. rewrite (beq_nat_true _ _ Hbeq) in *.
      apply lem_try26 in Hcon. rewrite Hcon. reflexivity.

      rewrite lem_d35_gen. apply IHlP2 with (lP := lP) (lx := lx);
        try assumption. inversion Hl2. reflexivity.
        apply consistent_lP_lx_cons_rem in Hcon. assumption.
Qed.

Fixpoint cap_pred_lx l1 l2 (lx : list FOvariable) :=
  match l1, lx with
  | nil, _ => nil
  | _, nil => nil
  | cons P l1', cons x lx' => if is_in_pred P l2 then cons x (cap_pred_lx l1' l2 lx')
          else cap_pred_lx l1' l2 lx'
  end.

Lemma lem_d61 : forall lP lx lP2,
  length lP = length lx ->
length (cap_pred lP lP2) = length (cap_pred_lx lP lP2 lx).
Proof.
  induction lP; intros lx lP2 H.
    simpl in *. reflexivity.

    simpl in *. destruct lx. discriminate.
    inversion H.
    case_eq (is_in_pred a lP2); intros Hin.
      simpl. rewrite IHlP with (lx := lx).
      reflexivity. assumption.

      apply IHlP. assumption.
Qed.

Lemma lem_g1 : forall lP2 lP1 P Q lx2 lx1 f b n,
length lP2 = length lx2 ->
 ind_FOv (indicies_l2 (lP2 ++ P :: lP1) Q) (lx2 ++ f :: lx1) =
       constant_l b n ->
  ind_FOv (indicies_l2 (app (cons P lP2) lP1) Q) (app (cons f lx2) lx1) = constant_l b n.
Proof.
  induction lP2; intros lP1 [Pn] [Qm] lx2 lx1 f b n Hl Hind.
    simpl. destruct lx2. simpl in *.  assumption.
    discriminate.

    destruct lx2. discriminate.
    inversion Hl as [Hl'].
    unfold indicies_l2 in *. simpl in *.
    destruct a as [Rn]. case_eq (beq_nat Qm Pn);
      intros Hbeq. case_eq (beq_nat Qm Rn);
        intros Hbeq2; rewrite Hbeq2 in *.
          simpl in *. destruct n. discriminate.
          inversion Hind as [[H1 H2]].
          rewrite ind_FOv_ind_l2_pre_cons in H2. apply IHlP2 in H2.
          rewrite Hbeq in H2. simpl in *. rewrite ind_FOv_ind_l2_pre_cons in H2.
          destruct n. discriminate.
          inversion H2 as [[H3 H4]].
          do 2 rewrite ind_FOv_ind_l2_pre_cons. 
          rewrite H4. reflexivity.
          all : try assumption.

          simpl. do 2 rewrite ind_FOv_ind_l2_pre_cons in *.
          apply IHlP2 in Hind.
          rewrite Hbeq in Hind. simpl in *. rewrite ind_FOv_ind_l2_pre_cons in Hind.
          all : try assumption.

        case_eq (beq_nat Qm Rn); intros Hbeq2; rewrite Hbeq2 in *.
          simpl in *. rewrite ind_FOv_ind_l2_pre_cons in Hind.
          do 2 rewrite ind_FOv_ind_l2_pre_cons. destruct n. discriminate.
          inversion Hind as [[H1 H2]].
          apply IHlP2 in H2. rewrite Hbeq in H2.
          rewrite ind_FOv_ind_l2_pre_cons in H2.
          rewrite H2. reflexivity.
          all : try assumption.

          simpl in *. rewrite ind_FOv_ind_l2_pre_cons in Hind.
          do 2 rewrite ind_FOv_ind_l2_pre_cons.
          apply IHlP2 in Hind. rewrite Hbeq in Hind.
          rewrite ind_FOv_ind_l2_pre_cons in Hind.
          all :assumption.
Qed.

Lemma lem_f2 : forall lP1 lP2 lx1 lx2 Q b n,
length lP1 = length lx1 ->
length lP2 = length lx2 ->
ind_FOv (indicies_l2 (app lP2 lP1) Q) (app lx2 lx1) = constant_l b n ->
ind_FOv (indicies_l2 (lP1 ++ lP2) Q) (lx1 ++ lx2) = constant_l b n.
Proof.
  induction lP1; intros lP2 lx1 lx2 Q b n Hl1 Hl2 Hind.
    destruct lx1. simpl in *. do 2 rewrite List.app_nil_r in Hind.
    assumption.
    discriminate.

    destruct lx1. discriminate.
    simpl in *. inversion Hl1 as [Hl1'].
    destruct a as [Pn]. destruct Q as [Qm]. unfold indicies_l2 in*.
    simpl in *.
    case_eq (beq_nat Qm Pn); intros Hbeq. simpl. rewrite ind_FOv_ind_l2_pre_cons.
      apply lem_g1 in Hind. unfold indicies_l2 in *. simpl in Hind.
      rewrite Hbeq in Hind. simpl in Hind. rewrite ind_FOv_ind_l2_pre_cons in Hind.
      destruct n. discriminate. inversion Hind as [[H1 H2]].
      apply IHlP1 in H2. rewrite H2. reflexivity.
      all : try assumption.

      rewrite ind_FOv_ind_l2_pre_cons. apply IHlP1; try assumption.
      apply lem_g1 in Hind. unfold indicies_l2 in *. simpl in *.
      rewrite Hbeq in Hind. rewrite ind_FOv_ind_l2_pre_cons in Hind.
      assumption. assumption.
Qed.

Lemma lem_d70_pre_pre_pre : forall lP lx Q a n,
length lP = length lx ->
  ind_FOv (indicies_l2 ( lP) Q) ( lx) = constant_l a n ->
exists  (n' : nat),
  ind_FOv (indicies_l2 ((lP ++ lP)%list) Q) ((lx ++ lx)%list) = constant_l a n'.
Proof.
  induction lP; intros lx Q b n Hl Hind.
    simpl. exists 0. reflexivity.

    simpl. destruct a as [Pn]. destruct Q as [Qm].
    unfold indicies_l2 in *. simpl in *.
    case_eq (beq_nat Qm Pn); intros Hbeq; rewrite Hbeq in *.
      simpl in *. destruct lx. discriminate.
      simpl. destruct n. discriminate. inversion Hind as [[H1 H2]].
      rewrite ind_FOv_ind_l2_pre_cons in *.
      simpl in Hind.
      inversion Hl as [Hl'].
      destruct (IHlP _ _ _ _ Hl' H2) as [n' H'].
      exists (S (S n')).
      pose proof lem_f2 as H. unfold indicies_l2 in H.
      rewrite H with (b := b) (n := (S (n'))); try assumption. reflexivity.
      simpl. rewrite Hbeq. simpl. rewrite ind_FOv_ind_l2_pre_cons. rewrite H'.
      reflexivity.

      destruct lx. discriminate.
      inversion Hl as [Hl'].
      rewrite ind_FOv_ind_l2_pre_cons in Hind.
      simpl in *. destruct (IHlP _ _ _ _ Hl' Hind) as [n' H].
      exists n'. pose proof lem_f2 as H2.
      unfold indicies_l2 in H2. rewrite ind_FOv_ind_l2_pre_cons.
      apply H2; try assumption. simpl. rewrite Hbeq.
      rewrite ind_FOv_ind_l2_pre_cons. assumption.
Qed.

Lemma lem_d70_pre_pre : forall lP lx P Q f a n,
length lP = length lx ->
  ind_FOv (indicies_l2 (P :: lP) Q) (f :: lx) = constant_l a n ->
exists  (n' : nat),
  ind_FOv (indicies_l2 (P :: (lP ++ lP)%list) Q) (f :: (lx ++ lx)%list) = constant_l a n'.
Proof.
  intros lP lx [Pn] [Qm] f a n Hl Hind.
  unfold indicies_l2 in *. simpl in *.
  case_eq (beq_nat Qm Pn); intros Hbeq; rewrite Hbeq in *.
    simpl in *. destruct n. discriminate.
    simpl in Hind . inversion Hind as [[H1 H2]].
    rewrite ind_FOv_ind_l2_pre_cons in *.
    apply lem_d70_pre_pre_pre in H2. unfold indicies_l2 in H2.
    destruct H2 as [n' H2']. exists (S n').
    rewrite H2'. reflexivity.
    assumption.

    rewrite ind_FOv_ind_l2_pre_cons in *.
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
  constant_l (CM_pa2_l_gen Iv (fun2 atm Q) (@at_gen _ x (first_occ_P lP Q) lx)) n.
Proof.
  induction lP; intros [Qm] atm W Iv lx x pa2 Hl Hcon.
    simpl. exists 0. reflexivity.

    simpl. destruct a as [Pn]. simpl.
    destruct lx. discriminate.
    inversion Hl as [Hl'].
    simpl. destruct (IHlP (Pred Qm) atm W Iv lx x pa2 Hl' (consistent_lP_lx_cons_rem_gen _ _ _ _ Hcon)) as [n H].
    case_eq (beq_nat Qm Pn); intros Hbeq.
      exists (S n). simpl. rewrite ind_gen_pre_cons. rewrite H.
      rewrite (beq_nat_true _ _ Hbeq).
      unfold first_occ_P in *. simpl in *. rewrite <- beq_nat_refl.

    case_eq (is_in_pred (Pred Qm) lP); intros Hin.
        simpl.
pose proof lem_d58 as H2. unfold first_occ_P in H2.
rewrite H2 with (lP := lP) (lx := lx) (x := f). reflexivity. assumption. assumption.
      rewrite (beq_nat_true _ _ Hbeq) in *.
      assumption.

      apply lem_d70; assumption.

      rewrite lem_d44 in H. simpl in *. destruct n. 2 : discriminate.
      simpl. reflexivity. assumption.

      exists n. rewrite ind_gen_pre_cons.
      unfold first_occ_P. simpl. rewrite Hbeq. rewrite lem_d35_gen. assumption.
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
   exists (CM_pa2_l_gen Iv (fun2 atm Q) (@at_gen _ x (first_occ_P lP Q) lx)).
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
   constant_l (CM_pa2_l_gen Iv (fun2 atm Q) (@at_gen _ x (first_occ_P lP Q) lx)) n.
Proof.
  induction lP; intros l Q W Iv atm lx x pa2 Hl Hcon.
    simpl. exists 0. reflexivity.

    simpl. destruct Q as [Qm]. destruct a as [Pn].
    destruct lx. discriminate. inversion Hl as [Hl'].
    destruct (IHlP l (Pred Qm) W Iv atm lx f pa2 Hl') as [n H].
    apply consistent_lP_lx_cons_rem_gen in Hcon. assumption.
    case_eq (is_in_pred (Pred Pn) l); intros Hin.
      simpl. case_eq (beq_nat Qm Pn); intros Hbeq.
        simpl. rewrite ind_gen_pre_cons.
        exists (S n).

 rewrite H. rewrite (beq_nat_true _ _ Hbeq).
        unfold first_occ_P. simpl. rewrite <- beq_nat_refl.
        simpl. pose proof lem_d58 as H2. unfold first_occ_P in H2.
        case_eq (is_in_pred (Pred Pn) lP); intros Hin2.
          rewrite H2 with (lP := lP) (lx := lx) (x := f); try assumption.
            reflexivity.

apply lem_d70; assumption.

          rewrite (lem_d44 (cap_pred lP l) (Pred Qm)) in *. simpl in *.
          destruct n. 2 : discriminate.
          simpl. reflexivity. rewrite (beq_nat_true _ _ Hbeq) in *.
          apply is_in_pred_cap_pred_f1. assumption.

    destruct (IHlP l (Pred Qm) W Iv atm lx x pa2 Hl') as [n' H'].
    apply consistent_lP_lx_cons_rem_gen in Hcon. assumption.
        exists n'. rewrite ind_gen_pre_cons.
        unfold first_occ_P in *. simpl. rewrite Hbeq.
        rewrite lem_d35_gen. rewrite H'. reflexivity.

      simpl. unfold first_occ_P. simpl. 
      case_eq (beq_nat Qm Pn); intros Hbeq.
        rewrite (beq_nat_true _ _ Hbeq) in *.
        rewrite (lem_d44 (cap_pred lP l) (Pred Pn)) in *.
        simpl in *. exists 0. reflexivity.
        apply is_in_cap_pred. assumption.
        apply is_in_cap_pred. assumption.
        apply is_in_cap_pred. assumption.

        rewrite lem_d35_gen. unfold first_occ_P in IHlP.
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
  intros. exists (CM_pa2_l_gen Iv (fun2 atm Q) (@at_gen _ x (first_occ_P lP Q) lx)).
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
SOturnst W Iv (altered_Ip_list Ip
   (vsS_pa_l Iv (FOv_att_P_l atm lP) lx) lP) Ir beta <->
SOturnst W Iv
  (altered_Ip_list Ip
     (vsS_pa_l Iv (FOv_att_P_l atm (cap_pred lP (preds_in beta)))
        (cap_pred_lx lP (preds_in beta) lx))
     (cap_pred lP (preds_in beta))) Ir beta.
Proof.
  induction lP; intros atm beta lx W Iv Ip Ir Hat Hl Hcon.
    simpl in *. apply bi_refl.
  
    destruct lx. discriminate.
    inversion Hl.
    simpl in *. case_eq (is_in_pred a (preds_in beta));
      intros Hin2. simpl.
      rewrite altered_Ip__list_consistent_lP_lpa with (pa2 := pa_t).
      rewrite altered_Ip__list_consistent_lP_lpa with (pa2 := pa_t).
      apply IHlP; try assumption.
      apply consistent_lP_lx_cons_rem_gen in Hcon. assumption.

pose proof (lem_a28' (cons a lP) (preds_in beta) atm W Iv pa_t (cons f lx)) as HH.
simpl in HH. rewrite Hin2 in *. simpl in *. apply HH; assumption.
      pose proof (lem_a27' (cons a lP) atm W Iv(cons f lx)) as H. simpl in H.
      apply H; assumption.

      split; intros SOt.
      apply P_not_occ_alt in SOt. apply IHlP; try assumption.
apply consistent_lP_lx_cons_rem_gen in Hcon. assumption.
      rewrite P_occ_in_alpha_is_in_pred_equiv in Hin2. assumption.

      apply P_not_occ_alt.
      rewrite P_occ_in_alpha_is_in_pred_equiv in Hin2. assumption.
 apply IHlP; try assumption.
apply consistent_lP_lx_cons_rem_gen in Hcon. assumption.
Qed.

Lemma lem_d62 : forall lP P x y W Iv Ip,
is_in_pred P lP = true ->
@altered_Ip_list W Ip
  (vsS_pa_l Iv (FOv_att_P_l (predSO P x) lP)
     (list_Var (length lP) y)) lP P (Iv x).
Proof.
  induction lP; intros [Pn] [xn] [ym] W Iv Ip Hin. discriminate.
  simpl in *. destruct a as [Qm]. simpl. rewrite (beq_nat_comm) in Hin. 
  case_eq (beq_nat Qm Pn);
    intros Hbeq; rewrite Hbeq in *.
    unfold CM_pa2_l_gen. simpl.
    case_eq (beq_nat ym xn); intros Hbeq2.
      unfold pa_t. exact I.

      reflexivity.

    apply IHlP. assumption.
Qed.

Lemma lem118'_is_in_pred_l : forall atm1,
AT atm1 = true ->
is_in_pred_l (atm_passing_predSO_ll_lP atm1) (preds_in atm1) = true.
Proof.
  induction atm1; intros Hat; try discriminate.
    destruct p. destruct f. simpl. rewrite <- beq_nat_refl.
    reflexivity.

    pose proof (AT_conjSO_l _ _ Hat).
    pose proof (AT_conjSO_r _ _ Hat).
    simpl. apply is_in_pred_l_2app.
      apply IHatm1_1. assumption.
      apply IHatm1_2. assumption.
Qed.

Lemma ex_nil_in_llv_app_f_FOv_att_P_l : forall l1 l2 alpha,
  ex_nil_in_llv (FOv_att_P_l alpha l1) = false ->
  ex_nil_in_llv (FOv_att_P_l alpha l2) = false ->
  ex_nil_in_llv (FOv_att_P_l alpha (app l1 l2)) = false.
Proof.
  induction l1; intros l2 alpha H1 H2.
    simpl. assumption.

    simpl. case_eq (fun2 alpha a).
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
    case_eq (fun2 beta a). intros Hg. rewrite Hg in *.
      discriminate.

      intros x lx Hlx. rewrite <- Hlx.
      case_eq (app (fun2 beta a) (fun2 gamma a)).
        intros H.
        apply app_rnil_l in H. rewrite H in *. discriminate.

        intros y ly Hly.
        apply IHlP. rewrite Hlx in Hex. assumption.
Qed.

Lemma ex_nil_in_llv_FOv_att_P_l_AT : forall atm,
AT atm = true ->
ex_nil_in_llv (FOv_att_P_l atm (preds_in atm)) = false.
Proof.
  induction atm; intros Hat; try discriminate.
    destruct p. destruct f. simpl. rewrite <- beq_nat_refl.
    reflexivity.

    pose proof (AT_conjSO_l _ _ Hat).
    pose proof (AT_conjSO_r _ _ Hat).
    simpl. apply ex_nil_in_llv_app_f_FOv_att_P_l.
      apply lem_try40_l. apply IHatm1. assumption.
      apply lem_try40. apply IHatm2. assumption.
Qed.

Lemma hopeful9'_further' : forall atm lP x (y:FOvariable) (W : Set) Iv Ip Ir (pa2 : W -> Prop),
  AT atm = true ->
is_in_pred_l (preds_in atm) lP = true ->
SOturnst W Iv
  (altered_Ip_list Ip
     (vsS_pa_l Iv (FOv_att_P_l atm lP) (list_Var (length lP) x)) lP) Ir
  atm.
Proof.
  induction atm; intros lP x y W Iv Ip Ir pa2 Hat Hin; try discriminate.
    destruct p as [Pn]. destruct f as [xn]. simpl in *.
    case_eq (is_in_pred (Pred Pn) lP); intros Hin2; rewrite Hin2 in *.
      2 : discriminate.
    apply lem_d62. assumption.

    pose proof (AT_conjSO_l _ _ Hat) as Hat1.
    pose proof (AT_conjSO_r _ _ Hat) as Hat2.
    simpl. apply conj.
      apply lem_d61' with (lP := (preds_in atm1)). apply pa_t.
apply is_in_pred_l_refl.
apply is_in_pred_l_refl.

simpl in Hin. rewrite is_in_pred_l_app_comm_l in Hin.
apply is_in_pred_l_app_r in Hin. assumption.
assumption. assumption.

      apply lem118'_equiv; try assumption.
      apply lem_try9_tryinggenlP_l.
        apply ex_nil_in_llv_FOv_att_P_l_AT. assumption.


apply consistent_lP_lx_list_Var.

rewrite length_list_Var. reflexivity.

apply lem118'_length. assumption.

apply lem118'_is_in_pred_l. assumption.

      apply (lem118'_equiv atm1). assumption.
      apply IHatm1; try assumption.
apply is_in_pred_l_refl.

      apply lem_d61' with (lP := (preds_in atm2)). apply pa_t.
apply is_in_pred_l_refl.
apply is_in_pred_l_refl.


simpl in Hin.
apply is_in_pred_l_app_r in Hin. assumption.
assumption.
assumption.

      apply lem118'_equiv; try assumption.
      apply lem_try9_tryinggenlP.

apply ex_nil_in_llv_FOv_att_P_l_AT. assumption.

apply consistent_lP_lx_list_Var.

rewrite length_list_Var. reflexivity.

apply lem118'_length. assumption.

apply lem118'_is_in_pred_l. assumption.

      apply (lem118'_equiv atm2). assumption.
      apply IHatm2; try assumption.
apply is_in_pred_l_refl.
Qed.

Lemma is_in_pred_l_preds_in_passing_predSO_l : forall lx lP P,
  ~ lx = nil ->
  is_in_pred_l (preds_in (passing_conj (passing_predSO_l P lx))) lP =
  is_in_pred P lP.
Proof.
  induction lx; intros lP [Pn] Hnil.
    contradiction (Hnil eq_refl).

    destruct a as [Qm].
    simpl in *. case_eq (passing_predSO_l (Pred Pn) lx).
      intros Hp. simpl in *. case_eq (is_in_pred (Pred Pn) lP);
        intros Hin; reflexivity.

      intros beta lbeta Hp. rewrite <- Hp.
      simpl. case_eq (is_in_pred (Pred Pn) lP); intros Hin.
        2: reflexivity.
      destruct lx. reflexivity.
      rewrite IHlx. assumption. discriminate.
Qed.

Lemma is_in_pred_l_preds_in_passing_predSO_l2 : forall l0 l a,
is_in_pred a l = false ->
~ l0 = nil ->
is_in_pred_l (preds_in (passing_conj (passing_predSO_l a l0))) l = false.
Proof.
  induction l0; intros l [Pn] Hin Hnil. contradiction (Hnil eq_refl).
  simpl. case_eq (passing_predSO_l (Pred Pn) l0).
    intros Hp. simpl. destruct a. simpl. rewrite Hin. reflexivity.

    intros beta lbeta Hp. rewrite <- Hp.
    simpl in *. destruct a. simpl. rewrite Hin. reflexivity.
Qed.

Lemma is_in_pred_l_app_if : forall l1 l2 lP,
  is_in_pred_l (app l1 l2) lP =
  if is_in_pred_l l1 lP then is_in_pred_l l2 lP else false.
Proof.
  induction l1; intros l2 lP.
    simpl. reflexivity.

    simpl. case_eq (is_in_pred a lP); intros Hin.
      apply IHl1. reflexivity.
Qed.

Lemma is_in_pred_l_preds_in_passing_predSO_ll : forall lP llx l,
  length lP = length llx ->
  ex_nil_in_llv llx = false ->
  is_in_pred_l (preds_in (passing_conj (passing_predSO_ll lP llx))) l =
  is_in_pred_l lP l.
Proof.
  induction lP; intros llx l Hl Hex. reflexivity.
  simpl in *. destruct llx. discriminate.
  simpl. case_eq (passing_predSO_ll lP llx).
    intros Hp. case_eq (is_in_pred a l); intros Hin.
      destruct lP. 2 : (destruct llx; discriminate).
      destruct l0. reflexivity.
      rewrite is_in_pred_l_preds_in_passing_predSO_l. rewrite Hin.
      reflexivity. discriminate.

      destruct l0. simpl in *. discriminate.
      apply is_in_pred_l_preds_in_passing_predSO_l2. assumption.
      discriminate.

    intros beta lbeta Hp. rewrite <- Hp. simpl.
    inversion Hl as [Hl'].
    simpl in Hex. destruct l0. discriminate.
    case_eq (is_in_pred a l); intros Hin;
      rewrite is_in_pred_l_app_if. rewrite IHlP.
      rewrite is_in_pred_l_preds_in_passing_predSO_l.
      rewrite Hin. reflexivity. discriminate. assumption.
      assumption.

      rewrite is_in_pred_l_preds_in_passing_predSO_l2. reflexivity.
      assumption. discriminate.
Qed.

Lemma lem_d71 : forall lP2 l x,
(cap_pred_lx lP2 l (list_Var (length lP2) x)) =
  list_Var (length (cap_pred lP2 l)) x.
Proof.
  induction lP2; intros l x. reflexivity.
  simpl. case_eq (is_in_pred a l); intros Hin.
    simpl. rewrite IHlP2. reflexivity.

    apply IHlP2.
Qed.

Lemma lem_a20_mono'' : forall lP lP2 llx2 W Iv Ip Ir pa_l beta atm x pa2,
  atm = passing_conj (passing_predSO_ll lP2 llx2) ->
  ~ lP2 = nil ->
ex_nil_in_llv llx2 = false ->
ex_FOvar_x_ll x (FOv_att_P_l atm lP) = false ->
~ cap_pred lP (preds_in beta) = nil ->
  length lP2 = length llx2 ->
  @consistent_lP_lpa W pa2 lP pa_l ->
  length lP = length pa_l ->
  SOturnst W Iv (altered_Ip_list Ip pa_l lP) Ir atm ->
  uniform_pos_SO beta ->
  is_in_pred_l (preds_in beta) (preds_in atm) = true ->
SOturnst W Iv
        (altered_Ip_list Ip
           (vsS_pa_l Iv (FOv_att_P_l atm lP) (list_Var (length lP) x)) lP)
        Ir beta ->
SOturnst W Iv (altered_Ip_list Ip pa_l lP) Ir beta.
Proof.
  intros lP lP2 llx W Iv Ip Ir lpa beta atm x pa2 HAT Hnil Hex Hex2 Hcap Hlength Hcon Hlength2 SOt Hun Hin1 SOt2.
  pose proof (monotonicity_lP_SO' beta (cap_pred lP (preds_in beta))) as H.
   assert ((forall P : predicate, is_in_pred P (cap_pred lP (preds_in beta)) = true ->
     P_occurs_in_alpha beta P = true) )
    as remembertoassume.
    intros P Hin3. apply is_in_pred_cap_pred_t in Hin3. destruct Hin3 as [H1 H2].
    rewrite <- P_occ_in_alpha_is_in_pred_equiv. assumption.

  apply (lem_a19 lP _ _ _ _ lpa beta pa2). assumption. assumption.
     destruct H as [H1 H2]. clear H2.
    assert (lP_is_pos_SO beta (cap_pred lP (preds_in beta))) as HlPpos.
      apply lP_is_pos_SO_uni; try assumption.

    unfold alpha_upward_monotone_lP in H1.
    specialize (H1 HlPpos W Iv Ir (altered_Ip_list Ip
            (vsS_pa_l Iv (FOv_att_P_l atm (cap_pred lP (preds_in beta))) 
            (list_Var (length (cap_pred lP (preds_in beta))) x))
            (cap_pred lP (preds_in beta)))
     (altered_Ip_list Ip (cap_pred_lpa lpa lP (preds_in beta))
     (cap_pred lP (preds_in beta)))).

    apply H1.  

    assert (~ llx = nil) as Hnil2.
      destruct llx. destruct lP2. contradiction (Hnil eq_refl).
      discriminate. discriminate.
    assert (AT atm = true) as HAT2.
      rewrite HAT. apply AT_passing_predSO_ll; try assumption.

    apply lemma_try7_again with (Ir := Ir) (pa2 := pa2) (lP0 := lP) (pa_l0 := lpa).
    all : try assumption.

    apply is_in_pred_l_cap_pred_add. assumption.

     apply lem_a23. assumption.

    apply is_in_pred_l_cap_pred_refl.

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
  is_in_pred_l lP lP2 = true ->
  REL rel = true ->
  atm = (passing_conj (passing_predSO_ll lP llx)) ->
  is_in_pred_l (preds_in beta) (preds_in (conjSO rel atm)) = true ->
  is_in_pred_l lP (preds_in (conjSO rel atm)) = true ->
  ex_FOvar_x_ll x (FOv_att_P_l atm lP2) = false ->
  length lP = length llx ->
  ex_nil_in_llv llx = false ->
  uniform_pos_SO beta ->
SOturnst W Iv (altered_Ip_list Ip
  (vsS_pa_l Iv (FOv_att_P_l (conjSO rel atm) lP2) (list_Var (length lP2) x)) lP2) Ir
  (implSO (conjSO rel atm) beta) ->
  (forall pa_l,
      length lP2 = length pa_l ->
      @consistent_lP_lpa _ pa2 lP2 pa_l ->
    SOturnst W Iv (altered_Ip_list Ip pa_l lP2) Ir (implSO (conjSO rel atm) beta)).
Proof.
   intros lP lP2 rel atm beta  x llx2 W Iv Ip Ir pa2 Hin3 HREL HAT Hin1 Hin2 Hex Hl1 Hex2 Hun SOt pa_l Hnil Hcon SOt1.
  case_eq lP2. intros HlP; rewrite HlP in *. simpl in *. 
    rewrite altered_Ip_list_nil in *. apply SOt. assumption.
  intros P lP' HlP. rewrite <- HlP.
  rewrite SOturnst_implSO in SOt.
  rewrite SOturnst_conjSO in *.
  destruct SOt1 as [SOt1 SOt2].
  rewrite altered_Ip_rel with (Ip2 := Ip)  in SOt1 .
  rewrite altered_Ip_rel with (Ip2 := Ip) in SOt.
      assert (P_occurs_in_alpha rel P = false) as Hpocc.
        apply P_occurs_in_rel. assumption.
  assert (SOturnst W Iv Ip Ir rel /\
      SOturnst W Iv
        (altered_Ip_list Ip
           (vsS_pa_l Iv (FOv_att_P_l (conjSO rel atm) lP2) (list_Var (length lP2) x)) lP2)
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
 rewrite length_list_Var. reflexivity.

   apply consistent_lP_lx_list_Var.

  rewrite lem_d71.
apply hopeful9'_further'; try assumption.

  rewrite is_in_pred_l_cap_pred_is_in_pred_l.
  apply is_in_pred_l_refl.
  rewrite is_in_pred_l_preds_in_passing_predSO_ll; assumption.

  specialize (SOt Hass). clear Hass. simpl in Hin1.
  simpl in *. rewrite (preds_in_rel rel) in *. simpl in *.
  rewrite FOv_att_P_l_conjSO_rel in SOt.
  case_eq (cap_pred lP2 (preds_in beta)).
    intros Hcap.
    apply altered_Ip_list_cap_pred_nil. assumption.
    apply altered_Ip_list_cap_pred_nil in SOt; assumption.

    intros Q lQ HlQ. 
case_eq lP.
  intros Hp. rewrite Hp in *. simpl in *.
  destruct llx2. simpl in *. rewrite HAT in *.
  simpl in *. apply is_in_pred_l_nil in Hin1.
  rewrite Hin1 in *.  rewrite cap_pred_nil in HlQ. discriminate.
  discriminate.
intros P'' lP'' HlP''.
  apply lem_a20_mono'' with (llx2 := llx2) (atm := atm) (x := x) (pa2 := pa2) (lP2 := lP).
all : try assumption.
rewrite HlP''. discriminate.

 rewrite HlQ. discriminate.
Qed.

Lemma hopeful8_lP_again_mono_tryinggenlP_atm: forall lP lP2 atm beta x llx W Iv Ip Ir pa2,
  is_in_pred_l lP lP2 = true ->
  atm = (passing_conj (passing_predSO_ll lP llx)) ->
  is_in_pred_l (preds_in beta) (preds_in atm) = true ->
  is_in_pred_l lP (preds_in atm) = true ->
  ex_FOvar_x_ll x (FOv_att_P_l atm lP2) = false ->
  length lP = length llx ->
  ex_nil_in_llv llx = false ->
  uniform_pos_SO beta ->
SOturnst W Iv (altered_Ip_list Ip
  (vsS_pa_l Iv (FOv_att_P_l atm lP2) (list_Var (length lP2) x)) lP2) Ir
  (implSO atm beta) ->
  (forall pa_l,
      length lP2 = length pa_l ->
      @consistent_lP_lpa _ pa2 lP2 pa_l ->
    SOturnst W Iv (altered_Ip_list Ip pa_l lP2) Ir (implSO atm beta)).
Proof.
   intros lP lP2 atm beta  x llx2 W Iv Ip Ir pa2 Hin3 HAT Hin1 Hin2 Hex Hl1 Hex2 Hun SOt pa_l Hnil Hcon SOt1.
  case_eq lP2. intros HlP; rewrite HlP in *. simpl in *. 
    rewrite altered_Ip_list_nil in *. apply SOt. assumption.
  intros P lP' HlP. rewrite <- HlP.
  rewrite SOturnst_implSO in SOt.
  assert (
      SOturnst W Iv
        (altered_Ip_list Ip
           (vsS_pa_l Iv (FOv_att_P_l atm lP2) (list_Var (length lP2) x)) lP2)
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
 rewrite length_list_Var. reflexivity.

   apply consistent_lP_lx_list_Var.

  rewrite lem_d71.
apply hopeful9'_further'; try assumption.

  rewrite is_in_pred_l_cap_pred_is_in_pred_l.
  apply is_in_pred_l_refl.
  rewrite is_in_pred_l_preds_in_passing_predSO_ll; assumption.

  specialize (SOt Hass). clear Hass. simpl in Hin1.
  simpl in *.
  case_eq (cap_pred lP2 (preds_in beta)).
    intros Hcap.
    apply altered_Ip_list_cap_pred_nil. assumption.
    apply altered_Ip_list_cap_pred_nil in SOt; assumption.

    intros Q lQ HlQ. 
case_eq lP.
  intros Hp. rewrite Hp in *. simpl in *.
  destruct llx2. simpl in *. rewrite HAT in *.
  simpl in *. apply is_in_pred_l_nil in Hin1.
  rewrite Hin1 in *.  rewrite cap_pred_nil in HlQ. discriminate.
  discriminate.
intros P'' lP'' HlP''.
  apply lem_a20_mono'' with (llx2 := llx2) (atm := atm) (x := x) (pa2 := pa2) (lP2 := lP).
all : try assumption.
rewrite HlP''. discriminate.

 rewrite HlQ. discriminate.
Qed.

Lemma vsSahlq_instant_aim1_fwd4_REV_mono_tryinggenlP : forall lP lP2 beta rel atm y xn llx2 (W : Set) Iv Ip Ir (pa2 : W -> Prop),
is_in_pred_l lP2 lP = true ->
  REL rel = true ->
    atm = passing_conj (passing_predSO_ll lP2 llx2) ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  attached_allFO_x beta (Var xn) = false ->
  attached_exFO_x beta (Var xn) = false ->
  closed_except beta (Var xn) ->
  length lP2 = length llx2 ->
  ~ lP2 = nil ->
ex_nil_in_llv llx2 = false ->
ex_FOvar_x_ll y (FOv_att_P_l atm lP) = false -> 
  x_occ_in_alpha (instant_cons_empty' (conjSO rel atm) beta) (Var xn) = true ->
  SOturnst W Iv Ip Ir (replace_pred_l (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)  
      (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) beta)) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))))))
    lP (list_Var (length lP) y)
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

pose proof (altered_Ip_list_consistent_lP_lpa' lP W Ip (nlist_list_pa W (length lP) pa_l) pa2)
  as Halt.
rewrite length_nlist_list_pa in Halt. specialize (Halt eq_refl).
destruct Halt as [lpa' [Hcon [Hl2 Halt]]].
rewrite Halt.

  apply hopeful8_lP_again_mono_tryinggenlP with (lP := lP2) (x := y) (llx := llx2) (pa2 := pa2); try assumption;
    try reflexivity; try rewrite <- Hat in *.

    rewrite Hat. simpl. rewrite (preds_in_rel rel). simpl.
    rewrite lem_is_in4. unfold instant_cons_empty'.
    simpl. rewrite (preds_in_rel rel). simpl.
    rewrite list_pred_not_in_passing_predSO_ll. apply lem_is_in.
    all : try assumption.

    rewrite Hat. simpl. rewrite (preds_in_rel rel). simpl.
    rewrite lem_is_in4. apply is_in_pred_l_refl.
    all : try assumption.

    rewrite Hat. unfold instant_cons_empty'. simpl.
    rewrite (preds_in_rel rel). simpl.
    rewrite list_pred_not_in_passing_predSO_ll.

    apply uniform_pos_SO_rep_pred_l. assumption.


all : try assumption.

intros SOt2.
specialize (SOt SOt2).
assert (closed_except (instant_cons_empty' (conjSO rel atm) beta) (Var xn)) as Hprobs.
  apply closed_except_inst_cons_empty'. assumption.

case_eq ((length (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn)))).
  intros Hl.
  apply List.length_zero_iff_nil in Hl. rewrite Hl in *. simpl in *. assumption.

  intros n Hl.
pose proof (kk10 (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
  (rev_seq (S (Nat.max (max_FOv (implSO (conjSO rel atm) beta)) xn))
              (length (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn)))) 
  (instant_cons_empty' (conjSO rel atm) beta) (Var xn) Hprobs (is_in_FOvar_rem_FOv_same _ _)) as H1.
apply H1 in SOt. assumption.

  rewrite Hl.
  rewrite min_l_rev_seq.
  pose proof (aa20 (conjSO rel atm) beta) as H3.
  apply leb_max_suc3. assumption.

  apply decr_strict_rev_seq.

  rewrite <- length_FOv_att_P_l. reflexivity.

simpl. rewrite (SOQFree_rel rel). rewrite (SOQFree_atm atm).
apply SOQFree_newnew_pre. unfold instant_cons_empty'.
apply SOQFree_rep_pred_l. simpl.
apply SOQFree_l_empty. all : try assumption.

apply consistent_lP_llv_FOv_att_P_l.

intros P. 
destruct (@lem1a_pre W lP Iv (conjSO rel atm) y P) as [n HH].
exists (CM_pa2_l_gen Iv (fun2 (conjSO rel atm) P) y).
exists n. (*  exists (CM_pa2_l_gen Iv (fun2 (conjSO rel atm) P) y). *)
rewrite ind_pa_gen in HH.
assumption.

apply ex_att_allFO_llv_implSO.
apply lem_a32; assumption.

apply lem2; try assumption.

apply ex_att_exFO_llv_implSO.
apply lem_a33; assumption.

apply lem4a; try assumption.
Qed.

Lemma lem_a32_atm : forall lP atm,
AT atm = true ->
ex_attached_allFO_llv atm (FOv_att_P_l atm lP) = false.
Proof.
  induction lP; intros atm Hat. reflexivity.

  simpl. rewrite IHlP. rewrite ex_att_allFO_lv_AT.
  reflexivity. all : assumption.
Qed.

Lemma lem_a33_atm : forall lP atm,
AT atm = true ->
ex_attached_exFO_llv atm (FOv_att_P_l atm lP) = false.
Proof.
  induction lP; intros atm Hat. reflexivity.

  simpl. rewrite ex_att_exFO_lv_AT. apply IHlP.
  all : try assumption.
Qed.

Lemma vsSahlq_instant_aim1_fwd4_REV_mono_tryinggenlP_atm : forall lP lP2 beta atm y xn llx2 (W : Set) Iv Ip Ir (pa2 : W -> Prop),
is_in_pred_l lP2 lP = true ->
    atm = passing_conj (passing_predSO_ll lP2 llx2) ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  attached_allFO_x beta (Var xn) = false ->
  attached_exFO_x beta (Var xn) = false ->
  closed_except beta (Var xn) ->
  length lP2 = length llx2 ->
  ~ lP2 = nil ->
ex_nil_in_llv llx2 = false ->
ex_FOvar_x_ll y (FOv_att_P_l atm lP) = false -> 
  x_occ_in_alpha (instant_cons_empty' atm beta) (Var xn) = true ->
  SOturnst W Iv Ip Ir (replace_pred_l (implSO
    atm
    (newnew_pre (instant_cons_empty' atm beta)  
      (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn))
      (rev_seq (S (max (max_FOv (implSO atm beta)) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn))))))
    lP (list_Var (length lP) y)
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

pose proof (altered_Ip_list_consistent_lP_lpa' lP W Ip (nlist_list_pa W (length lP) pa_l) pa2)
  as Halt.
rewrite length_nlist_list_pa in Halt. specialize (Halt eq_refl).
destruct Halt as [lpa' [Hcon [Hl2 Halt]]].
rewrite Halt.


  apply hopeful8_lP_again_mono_tryinggenlP_atm with (lP := lP2) (x := y) (llx := llx2) (pa2 := pa2); try assumption;
    try reflexivity; try rewrite <- Hat in *.

    rewrite Hat. simpl.
    rewrite lem_is_in4. unfold instant_cons_empty'.
    simpl. 
    rewrite list_pred_not_in_passing_predSO_ll. apply lem_is_in.
    all : try assumption.

    rewrite Hat. simpl.
    rewrite lem_is_in4. apply is_in_pred_l_refl.
    all : try assumption.

    rewrite Hat. unfold instant_cons_empty'. simpl.
    rewrite list_pred_not_in_passing_predSO_ll.

    apply uniform_pos_SO_rep_pred_l. assumption.


all : try assumption.

intros SOt2.
specialize (SOt SOt2).
assert (closed_except (instant_cons_empty' atm beta) (Var xn)) as Hprobs.
  apply closed_except_inst_cons_empty'. assumption.

case_eq ((length (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn)))).
  intros Hl.
  apply List.length_zero_iff_nil in Hl. rewrite Hl in *. simpl in *. assumption.

  intros n Hl.
pose proof (kk10 (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn))
  (rev_seq (S (Nat.max (max_FOv (implSO atm beta)) xn))
              (length (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn)))) 
  (instant_cons_empty' atm beta) (Var xn) Hprobs (is_in_FOvar_rem_FOv_same _ _)) as H1.
apply H1 in SOt. assumption.

  rewrite Hl.
  rewrite min_l_rev_seq.
  pose proof (aa20 atm beta) as H3.
  apply leb_max_suc3. assumption.

  apply decr_strict_rev_seq.

  rewrite <- length_FOv_att_P_l. reflexivity.

simpl. rewrite (SOQFree_atm atm).
apply SOQFree_newnew_pre. unfold instant_cons_empty'.
apply SOQFree_rep_pred_l. simpl.
apply SOQFree_l_empty. all : try assumption.

apply consistent_lP_llv_FOv_att_P_l.

intros P. 
destruct (@lem1a_pre W lP Iv atm y P) as [n HH].
exists (CM_pa2_l_gen Iv (fun2 atm P) y). exists n.
rewrite ind_pa_gen in HH. 
assumption.

apply ex_att_allFO_llv_implSO.
apply lem_a32_atm; assumption.

apply lem2_atm; try assumption.

apply ex_att_exFO_llv_implSO.
apply lem_a33_atm; assumption.

apply lem4a_atm; try assumption.
Qed.


(* ---------------------- *)

Lemma list_closed_SO_instant_cons_empty2_REV : forall l alpha beta W Iv Ip Ir,
  is_in_pred_l (preds_in (implSO alpha beta)) l = true ->
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
ex_FOvar_x_ll y (FOv_att_P_l atm lP) = false ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  attached_allFO_x beta (Var xn) = false ->
  attached_exFO_x beta (Var xn) = false ->
  closed_except beta (Var xn) ->
  x_occ_in_alpha (instant_cons_empty' (conjSO rel atm) beta) (Var xn) = true ->
  is_in_pred_l (preds_in (implSO (conjSO rel atm) beta)) lP = true ->
  SOturnst W Iv Ip Ir (replace_pred_l (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)  
      (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) beta)) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))))))
    lP (list_Var (length lP) y)
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

    rewrite <- is_in_pred_l_preds_in_passing_predSO_ll with (llx := llx2).
    simpl in Hin. rewrite (preds_in_rel rel Hrel) in Hin. simpl in *.
    rewrite is_in_pred_l_app_comm_l in Hin.
    apply is_in_pred_l_app_r in Hin.
    rewrite <- Hat. all : assumption.
Qed.

Lemma vsSahlq_instant_aim1_fwd4_closer_REV_atm : forall lP lP2 llx2 beta atm y xn W Iv Ip Ir,
    atm = passing_conj (passing_predSO_ll lP2 llx2) ->
length lP2 = length llx2 ->
lP2 <> nil ->
ex_nil_in_llv llx2 = false ->
ex_FOvar_x_ll y (FOv_att_P_l atm lP) = false ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  attached_allFO_x beta (Var xn) = false ->
  attached_exFO_x beta (Var xn) = false ->
  closed_except beta (Var xn) ->
  x_occ_in_alpha (instant_cons_empty' atm beta) (Var xn) = true ->
  is_in_pred_l (preds_in (implSO atm beta)) lP = true ->
  SOturnst W Iv Ip Ir (replace_pred_l (implSO
    atm
    (newnew_pre (instant_cons_empty' atm beta)  
      (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn))
      (rev_seq (S (max (max_FOv (implSO atm beta)) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn))))))
    lP (list_Var (length lP) y)
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

    rewrite <- is_in_pred_l_preds_in_passing_predSO_ll with (llx := llx2).
    simpl in Hin. simpl in *.
    rewrite is_in_pred_l_app_comm_l in Hin.
    apply is_in_pred_l_app_r in Hin.
    rewrite <- Hat. all : assumption.
Qed.

Lemma vsSahlq_instant_aim1_fwd4_closer2_REV : forall lx lP lP2 llx2 beta rel atm y xn W Iv Ip Ir,
  REL rel = true ->
    atm = passing_conj (passing_predSO_ll lP2 llx2) ->
length lP2 = length llx2 ->
lP2 <> nil ->
ex_nil_in_llv llx2 = false ->
ex_FOvar_x_ll y (FOv_att_P_l atm lP) = false ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  attached_allFO_x beta (Var xn) = false ->
  attached_exFO_x beta (Var xn) = false ->
  closed_except beta (Var xn) ->

  x_occ_in_alpha (instant_cons_empty' (conjSO rel atm) beta) (Var xn) = true ->
  is_in_pred_l (preds_in (implSO (conjSO rel atm) beta)) lP = true ->
  SOturnst W Iv Ip Ir (replace_pred_l (list_closed_allFO (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)  
      (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) beta)) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn)))))) lx)
    lP (list_Var (length lP) y)
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
ex_FOvar_x_ll y (FOv_att_P_l atm lP) = false ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  attached_allFO_x beta (Var xn) = false ->
  attached_exFO_x beta (Var xn) = false ->
  closed_except beta (Var xn) ->

  x_occ_in_alpha (instant_cons_empty' atm beta) (Var xn) = true ->
  is_in_pred_l (preds_in (implSO atm beta)) lP = true ->
  SOturnst W Iv Ip Ir (replace_pred_l (list_closed_allFO (implSO
    atm
    (newnew_pre (instant_cons_empty' atm beta)  
      (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn))
      (rev_seq (S (max (max_FOv (implSO atm beta)) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn)))))) lx)
    lP (list_Var (length lP) y)
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
  is_in_pred P (preds_in (passing_conj (passing_predSO_ll
      (atm_passing_predSO_ll_lP atm)
      (atm_passing_predSO_ll_llx atm)))) = 
  is_in_pred P (preds_in atm).
Proof.
  induction atm; intros [Pn] Hat; try discriminate.
    destruct p as [Qm]; destruct f. simpl in *.
    reflexivity.

    pose proof (AT_conjSO_l _ _ Hat).
    pose proof (AT_conjSO_r _ _ Hat).
    simpl. rewrite is_in_pred_app_if.
    rewrite passing_predSO_ll_app.
    rewrite preds_in_passing_conj_app.
    rewrite is_in_pred_app_if.
    rewrite IHatm1. rewrite IHatm2. reflexivity.
    all : try assumption.
    apply lem118'_length. assumption.
Qed.

Lemma lem_e4 : forall l atm,
AT atm = true ->
list_pred_not_in  (preds_in
    (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm)))) l =
list_pred_not_in (preds_in atm) l.
Proof.
  induction l; intros atm Hat. reflexivity.
  simpl. rewrite lem118'_is_in_pred.
  case_eq (is_in_pred a (preds_in atm)); intros Hin.
    apply IHl. assumption.

    rewrite IHl. reflexivity. all : assumption.
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
is_in_FOvar_l (fun2  (passing_conj
              (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm)))
           a) (fun2 atm a) = true.
Proof.
  induction atm; intros [Pn] Hat; try discriminate.
    destruct p as [Qm]. destruct f. simpl.
    case_eq (beq_nat Pn Qm); intros Hbeq. simpl.
      rewrite <- beq_nat_refl. reflexivity. reflexivity.

    simpl. rewrite passing_predSO_ll_app.
    rewrite fun2_passing_conj_app.
    apply is_in_FOvar_l_app. apply IHatm1.
      apply (AT_conjSO_l _ _ Hat).
      apply IHatm2. apply (AT_conjSO_r _ _ Hat).

      apply lem118'_length. apply (AT_conjSO_l _ _ Hat).
Qed.

Lemma lem_e11 : forall atm a,
AT atm = true ->
is_in_FOvar_l (fun2 atm a) (fun2  (passing_conj
              (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm)))
           a)  = true.
Proof.
  induction atm; intros [Pn] Hat; try discriminate.
    destruct p as [Qm]. destruct f. simpl.
    case_eq (beq_nat Pn Qm); intros Hbeq. simpl.
      rewrite <- beq_nat_refl. reflexivity. reflexivity.

    simpl. rewrite passing_predSO_ll_app.
    rewrite fun2_passing_conj_app.
    apply is_in_FOvar_l_app. apply IHatm1.
      apply (AT_conjSO_l _ _ Hat).
      apply IHatm2. apply (AT_conjSO_r _ _ Hat).

      apply lem118'_length. apply (AT_conjSO_l _ _ Hat).
Qed.


Lemma lem_e8 : forall lP atm ,
  AT atm = true ->
  is_in_in_FOvar_ll (FOv_att_P_l (passing_conj (passing_predSO_ll
    (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm))) lP)
(FOv_att_P_l atm lP) = true.
Proof.
  induction lP; intros atm Hat.
    simpl. reflexivity.

    simpl in *. rewrite lem_e9.  apply IHlP. 
    all : assumption.
Qed.


Lemma lem_e10 : forall lP atm ,
  AT atm = true ->
  is_in_in_FOvar_ll (FOv_att_P_l atm lP)
    (FOv_att_P_l (passing_conj (passing_predSO_ll
    (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm))) lP)
 = true.
Proof.
  induction lP; intros atm Hat.
    simpl. reflexivity.

    simpl in *. rewrite lem_e11.  apply IHlP. 
    all : assumption.
Qed.

Lemma lem_e15' : forall l2  x y W Iv Ip Ir ,
is_in_FOvar x l2 = true ->
SOturnst W Iv Ip Ir (replace_FOv (fun1 l2 x) x y).
Proof.
  induction l2; intros  [xn] [ym] W Iv Ip Ir  H2.
    simpl in *. discriminate.

    simpl in *. destruct a as [un].
    destruct l2. simpl in *.
      rewrite <- beq_nat_refl.
      case_eq (beq_nat xn un); intros Hbeq; rewrite Hbeq in *.
        reflexivity. discriminate.

      rewrite replace_FOv_disjSO. rewrite SOturnst_disjSO.
      case_eq (beq_nat xn un); intros Hbeq; rewrite Hbeq in *.
        left. rewrite (beq_nat_true _ _ Hbeq).
        simpl. rewrite <- beq_nat_refl. reflexivity.
      right. apply IHl2. assumption.
Qed.

Lemma lem_e18' : forall l2 xn ym zn W Iv Ip Ir,
is_in_FOvar (Var zn) l2 = true -> 
PeanoNat.Nat.eqb xn zn = false ->
SOturnst W Iv Ip Ir (eqFO (Var ym) (Var zn)) ->
SOturnst W Iv Ip Ir (replace_FOv (fun1 l2 (Var xn)) (Var xn) (Var ym)).
Proof.
  induction l2; intros xn ym zn W Iv IP Ir H2 Hbeq.
    simpl in *. discriminate.

    simpl in *. destruct a as [un]. 
    destruct l2. case_eq (beq_nat zn un); intros Hbeq2;
      rewrite Hbeq2 in *. 2 : discriminate.
    simpl. rewrite <- beq_nat_refl. rewrite (beq_nat_true _ _ Hbeq2) in Hbeq.
    rewrite Hbeq. intros. rewrite <- (beq_nat_true _ _ Hbeq2). assumption.

    rewrite replace_FOv_disjSO. rewrite SOturnst_disjSO.
    intros H. simpl. rewrite <- beq_nat_refl. 
    case_eq (beq_nat zn un); intros Hbeq2; rewrite Hbeq2 in *.
      left. rewrite (beq_nat_true _ _ Hbeq2) in Hbeq. rewrite Hbeq.
      rewrite (beq_nat_true _ _ Hbeq2) in H. assumption.

      right. apply IHl2 with (zn := zn); try assumption.
Qed.

Lemma lem_e14 : forall l1 l2 x y W Iv Ip Ir,
is_in_FOvar_l l1 l2 = true ->
~ l1 = nil ->
SOturnst W Iv Ip Ir (replace_FOv (fun1 l1 x) x y) ->
SOturnst W Iv Ip Ir (replace_FOv (fun1 l2 x) x y).
Proof.
  induction l1; intros l2 [xn] [ym] W Iv Ip Ir H1 H2 SOt.
    contradiction (H2 eq_refl).

    simpl in *. case_eq (is_in_FOvar a l2); intros Hin;
      rewrite Hin in *. 2 : discriminate.
    destruct a as [zn]. destruct l1. simpl in *.
      rewrite <- beq_nat_refl in *.
      case_eq (beq_nat xn zn); intros Hbeq; rewrite Hbeq in *.
        rewrite (beq_nat_true _ _ Hbeq) in *.
        apply lem_e15'. assumption.

        apply lem_e18' with (zn := zn); try assumption.

      rewrite replace_FOv_disjSO in SOt. rewrite SOturnst_disjSO in SOt.
      destruct SOt as [SOt1 | SOt2].
        simpl in SOt1. rewrite <- beq_nat_refl in SOt1.
        case_eq (beq_nat xn zn); intros Hbeq; rewrite Hbeq in *.
          rewrite (beq_nat_true _ _ Hbeq) in *. apply lem_e15'.
          assumption.

          apply lem_e18' with (zn := zn); try assumption.

        apply IHl1; try assumption. discriminate.
Qed.

Lemma lem_e20 : forall l x y lP lx lcond W Iv Ip Ir,
  SOturnst W Iv Ip Ir (replace_pred_l (replace_FOv (fun1 l x) x y)
      lP lx lcond) <->
  SOturnst W Iv Ip Ir (replace_FOv (fun1 l x) x y).
Proof.
  induction l; intros x y lP lx lcond W Iv Ip Ir.
    simpl. destruct x as [xn].
    case_eq (beq_nat xn 1); intros Hbeq;
      rewrite rep_pred_l_eqFO; apply bi_refl.

    simpl. destruct l. simpl.
    destruct x as [xn]. destruct a as [ym].
    rewrite <- beq_nat_refl. case_eq (beq_nat xn ym);
      intros Hbeq; rewrite rep_pred_l_eqFO; apply bi_refl.

    rewrite replace_FOv_disjSO. rewrite rep_pred_l_disjSO.
    split; intros [H1 | H2].
      left. destruct x as [xn]. destruct a as [zn]. destruct y as [ym].
      simpl in *. rewrite <- beq_nat_refl in *.
      case_eq (beq_nat xn zn); intros Hbeq; rewrite Hbeq in *;
        rewrite rep_pred_l_eqFO in H1; assumption.

      right. apply (IHl x y lP lx lcond); assumption.

      left. destruct x as [xn]. destruct a as [zn]. destruct y as [ym].
      simpl in *. rewrite <- beq_nat_refl in *.
      case_eq (beq_nat xn zn); intros Hbeq; rewrite Hbeq in *;
        rewrite rep_pred_l_eqFO; assumption.

      right. apply (IHl x y lP lx lcond); assumption.
Qed.

Lemma lem_e27 : forall alpha P x cond,
  is_unary_predless alpha = true ->
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
      apply (is_unary_predless_conjSO_r _ _ H).
      apply (is_unary_predless_conjSO_l _ _ H).

    simpl. rewrite IHalpha1. rewrite IHalpha2. reflexivity.
      apply (is_unary_predless_conjSO_r _ _ H).
      apply (is_unary_predless_conjSO_l _ _ H).

    simpl. rewrite IHalpha1. rewrite IHalpha2. reflexivity.
      apply (is_unary_predless_conjSO_r _ _ H).
      apply (is_unary_predless_conjSO_l _ _ H).

    destruct p. discriminate.
    destruct p. discriminate.
Qed.

Lemma lem_e26 : forall lP lx lcond alpha,
  is_unary_predless alpha = true ->
  replace_pred_l alpha lP lx lcond = alpha.
Proof.
  induction lP; intros lx lcond alpha H. reflexivity.
  destruct lx. reflexivity.
  destruct lcond. reflexivity.
  simpl. rewrite IHlP. apply lem_e27.
  all : assumption.
Qed.

Lemma is_unary_predless_l_vsS_syn_l : forall l x,
is_unary_predless_l (vsS_syn_l l x) = true.
Proof.
  induction l; intros [xn]. reflexivity.
  simpl. rewrite IHl. rewrite un_predless_fun1.
  reflexivity.
Qed.

Lemma lem_e19 : forall lP l1 l2 P y x W Iv Ip Ir,
is_in_in_FOvar_ll l1 l2 = true ->
is_in_in_FOvar_ll l2 l1 = true ->
consistent_lP_llv lP l1 ->
consistent_lP_llv lP l2 ->
  SOturnst W Iv Ip Ir (replace_pred_l (predSO P y) lP
      (list_Var (length lP) x) (vsS_syn_l l1 x)) <->
  SOturnst W Iv Ip Ir (replace_pred_l (predSO P y) lP
      (list_Var (length lP) x) (vsS_syn_l l2 x)).
Proof.
  induction lP; intros l1 l2 [Pn] y x W Iv Ip Ir Hin1 Hin2 Hcon1 Hcon2.
    simpl in *. destruct y as [ym]. apply bi_refl.

    simpl in *. destruct y as [ym]. case_eq l1.
      intros Hl1. simpl. destruct l2. simpl.
      apply bi_refl. rewrite Hl1 in *. discriminate.

      intros la l1' Hl1. rewrite <- Hl1.
      case_eq (vsS_syn_l l1 x). intros H. rewrite Hl1 in H.
        discriminate.
      intros beta lbeta Hlbeta.
      case_eq l2. intros Hl2. rewrite Hl2 in *. rewrite Hl1 in *.
        discriminate.
      intros lb l2' Hl2. rewrite <- Hl2.
      case_eq (vsS_syn_l l2 x). intros H. rewrite Hl2 in H. discriminate.
      intros gamma lgamma Hlgamma.
      rewrite Hl1 in *. rewrite Hl2 in *.
      simpl in *. case_eq (is_in_FOvar_l la lb); intros Hina;
        rewrite Hina in *. 2 : discriminate.
      case_eq (is_in_FOvar_l lb la); intros Hinb; rewrite Hinb in *.  
        2 : discriminate.
      inversion Hlbeta as [[H1a H1b]].
      inversion Hlgamma as [[H2a H2b]].
      rewrite rep_pred__l_consistent.
      rewrite rep_pred__l_consistent. 
      destruct a as [Qm].
      case_eq (beq_nat Pn Qm); intros Hbeq.
        rewrite (beq_nat_true _ _ Hbeq) in *.
        simpl. rewrite <- beq_nat_refl.
        rewrite lem_e26.
        rewrite lem_e26.
        split; intros H.
          destruct la. destruct lb. simpl in *.
          destruct x. assumption. discriminate.
          destruct lb. discriminate.
          apply lem_e14 with (l1 := (cons f la)); try assumption.
            discriminate.
          destruct la. destruct lb. simpl in *.
          destruct x. assumption. discriminate.
          destruct lb. discriminate.
          apply lem_e14 with (l1 := (cons f0 lb)); try assumption.
            discriminate.

          apply rep_FOv_is_unary_predless.
          apply un_predless_fun1. 
          apply rep_FOv_is_unary_predless.
          apply un_predless_fun1. 

      simpl. rewrite beq_nat_comm. rewrite Hbeq.
      apply IHlP; try assumption.
        apply consistent_lP_llv_cons in Hcon1. assumption.
        apply consistent_lP_llv_cons in Hcon2. assumption.

        apply is_unary_predless_l_vsS_syn_l.
        apply un_predless_fun1. 
        apply consistent_lP_llv__lcond_cons. assumption.
        apply (consistent_lP_lx_list_Var (cons a lP)).

        apply is_unary_predless_l_vsS_syn_l.
        apply un_predless_fun1.

        apply consistent_lP_llv__lcond_cons. assumption.
        apply (consistent_lP_lx_list_Var (cons a lP)).
Qed.

Lemma lem_e12 : forall alpha lP l1 l2 x W Iv Ip Ir,
  SOQFree alpha = true ->
  is_in_in_FOvar_ll l1 l2 = true ->
  is_in_in_FOvar_ll l2 l1 = true ->
  consistent_lP_llv lP l1 ->
  consistent_lP_llv lP l2 ->
  SOturnst W Iv Ip Ir (replace_pred_l alpha lP (list_Var (length lP) x)
      (vsS_syn_l l1 x)) <->
  SOturnst W Iv Ip Ir (replace_pred_l alpha lP (list_Var (length lP) x)
      (vsS_syn_l l2 x)).
Proof.
  induction alpha; intros lP l1 l2 x W Iv Ip Ir Hno Hin1 Hin2 Hcon1 con2.
    destruct p as [Pn]. destruct f as [xn].
    apply (lem_e19 _ l1 l2); assumption.

    rewrite rep_pred_l_relatSO.
    rewrite rep_pred_l_relatSO. apply bi_refl. simpl.

    rewrite rep_pred_l_eqFO.
    rewrite rep_pred_l_eqFO. apply bi_refl. simpl.

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
  SOturnst W Iv Ip Ir (replace_pred_l alpha lP (list_Var (length lP) x)
    (vsS_syn_l (FOv_att_P_l (conjSO rel 
      (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm)
        (atm_passing_predSO_ll_llx atm))))lP) x)) <->
  SOturnst W Iv Ip Ir (replace_pred_l alpha lP (list_Var (length lP) x)
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
  SOturnst W Iv Ip Ir (replace_pred_l alpha lP (list_Var (length lP) x)
    (vsS_syn_l (FOv_att_P_l (
      (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm)
        (atm_passing_predSO_ll_llx atm))))lP) x)) <->
  SOturnst W Iv Ip Ir (replace_pred_l alpha lP (list_Var (length lP) x)
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
      simpl. reflexivity.

      intros beta lbeta Hl1. rewrite <- Hl1.
      case_eq (app l1 l2). intros H. rewrite Hl1 in *. discriminate.
      intros gamma lgamma Hlgamma. rewrite <- Hlgamma.
      destruct l2. contradiction (H2 eq_refl).
      simpl. rewrite IHl1. rewrite PeanoNat.Nat.max_assoc. reflexivity.
      rewrite Hl1. discriminate.
      discriminate.
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
    rewrite IHatm1. rewrite IHatm2. reflexivity.
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
    is_in_pred P lP = true ->
    is_unary_predless_l lcond = true ->
    is_unary_predless cond = true ->
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
  SOturnst W Iv Ip Ir (replace_FOv (fun1 (app l1 l2) x) x y) <->
  SOturnst W Iv Ip Ir (disjSO (replace_FOv (fun1 l1 x) x y)
    (replace_FOv (fun1 l2 x) x y)).
Proof.
  induction l1; intros l2 x y W Iv Ip Ir Hnil1 Hnil2. contradiction (Hnil1 eq_refl).
  simpl. case_eq l1. intros Hl1. destruct l2. contradiction (Hnil2 eq_refl).
    simpl. destruct x as [xn]. destruct y as [ym]. rewrite <- beq_nat_refl.
    destruct a as [zn]. apply bi_refl.

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
SOturnst W Iv Ip Ir (replace_FOv (fun1 (fun2 atm2 Q) y) y x) <->
SOturnst W Iv Ip Ir (replace_FOv (fun1 (fun2 atm Q) y) y x).
Proof.
  induction atm; intros atm0 [Qm] [ym] [xn] W Iv Ip Ir Hat1 Hat2; try discriminate.
    destruct p as [Pn]. destruct f as [zn]. simpl in *. rewrite Hat2.
    case_eq (beq_nat Qm Pn); intros Hbeq. simpl. rewrite Hbeq.
      simpl. rewrite <- beq_nat_refl. apply bi_refl.

      simpl. rewrite Hbeq. simpl. apply bi_refl.

    simpl in *. rewrite Hat2.
    pose proof (AT_conjSO_l _ _ Hat1) as Hata.
    pose proof (AT_conjSO_r _ _ Hat1) as Hatb.
    assert (SOQFree_P atm1 (Pred Qm) = true) as Hass1.
      apply SOQFree__P. apply SOQFree_atm. assumption.
    assert (SOQFree_P atm2 (Pred Qm) = true) as Hass2.
      apply SOQFree__P. apply SOQFree_atm. assumption.
    rewrite passing_predSO_ll_app. rewrite fun2_passing_conj_app.
      2 : (apply lem118'_length; try assumption).
    case_eq (P_occurs_in_alpha atm1 (Pred Qm)); intros Hpocc1.
    case_eq (P_occurs_in_alpha atm2 (Pred Qm)); intros Hpocc2.
    split ;intros H. apply lem_e24 in H. apply lem_e24.
        apply lem10; assumption.
        apply lem10; assumption.

      simpl in *. destruct H as [H1 | H2].
        left. apply (IHatm1 (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm1) (atm_passing_predSO_ll_llx atm1)))); try assumption.
        reflexivity.
        right. apply (IHatm2 (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm2) (atm_passing_predSO_ll_llx atm2)))); try assumption.
        reflexivity.
        apply lem10.
          apply SOQFree_P_atm_passing_predSO_ll; assumption.
          rewrite <- lem118'_P_occurs_in_alpha_gen; assumption.
        apply lem10.
          apply SOQFree_P_atm_passing_predSO_ll; assumption.
          rewrite <- lem118'_P_occurs_in_alpha_gen; assumption.

apply lem_e24 in H. apply lem_e24.
        apply lem10.
          apply SOQFree_P_atm_passing_predSO_ll; assumption.
          rewrite <- lem118'_P_occurs_in_alpha_gen; assumption.
        apply lem10.
          apply SOQFree_P_atm_passing_predSO_ll; assumption.
          rewrite <- lem118'_P_occurs_in_alpha_gen; assumption.
      simpl in *. destruct H as [H1 | H2].
        left. apply (IHatm1 (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm1) (atm_passing_predSO_ll_llx atm1)))); try assumption.
        reflexivity.
        right. apply (IHatm2 (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm2) (atm_passing_predSO_ll_llx atm2)))); try assumption.
        reflexivity.

        apply lem10; assumption.
        apply lem10; assumption.

        rewrite (lem1 atm2); try assumption. rewrite List.app_nil_r.
        rewrite (lem1 (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm2)
            (atm_passing_predSO_ll_llx atm2)))). rewrite List.app_nil_r.
        apply IHatm1. all : try assumption. reflexivity.
        rewrite <- lem118'_P_occurs_in_alpha_gen; assumption.


        rewrite (lem1 atm1); try assumption.
        rewrite (lem1 (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm1)
            (atm_passing_predSO_ll_llx atm1)))).
        simpl.
        apply IHatm2. all : try assumption. reflexivity.
        rewrite <- lem118'_P_occurs_in_alpha_gen; assumption.

Qed.  

Lemma lem_e22_pre_predSO : forall lP atm atm2 p f y W Iv Ip Ir,
 AT atm = true ->
 atm2 = passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm)) ->
SOturnst W Iv Ip Ir (replace_pred_l (predSO p f) lP (list_Var (length lP) y) (vsS_syn_l (FOv_att_P_l atm2 lP) y)) <->
SOturnst W Iv Ip Ir (replace_pred_l (predSO p f) lP (list_Var (length lP) y) (vsS_syn_l (FOv_att_P_l atm lP) y)).
Proof.
  induction lP; intros atm atm2 [Pn] [xn] [ym] W Iv Ip Ir Hat1 Hat2.
    simpl in *. apply bi_refl.

    assert (length lP = length (list_Var (length lP) (Var ym))) as Hass1.
        symmetry. apply length_list_Var.
    assert (length lP = length (vsS_syn_l (FOv_att_P_l atm2 lP) (Var ym))) as Hass2.
        rewrite <- length_vsS_syn_l.
        apply length_FOv_att_P_l.
    assert (length lP = length (vsS_syn_l (FOv_att_P_l atm lP) (Var ym))) as Hass3.
        rewrite <- length_vsS_syn_l.
        apply length_FOv_att_P_l.
    simpl. case_eq (is_in_pred a lP); intros Hin. 
      rewrite rep_pred__l_is_in2.
      rewrite rep_pred__l_is_in2.
      apply IHlP; assumption.
        all : try assumption.
        apply un_predless_l_vsS_syn_l.
        apply un_predless_fun1.
        apply un_predless_l_vsS_syn_l.
        apply un_predless_fun1.

      rewrite rep_pred__l_switch; try assumption.
      rewrite rep_pred__l_switch; try assumption.
      destruct a as [Qm]. simpl.
      case_eq (beq_nat Qm Pn); intros Hbeq.
        split; intros H. apply lem_e20.
          apply lem_e20 in H.
          apply (lem_e23 atm atm2); assumption.

apply lem_e20.
          apply lem_e20 in H.
          apply (lem_e23 atm atm2); assumption.

        apply IHlP; assumption.
        apply un_predless_fun1.
        apply un_predless_l_vsS_syn_l.
        apply un_predless_fun1.
        apply un_predless_l_vsS_syn_l.
Qed.

Lemma lem_e22_pre : forall atm0 lP atm atm2 y W Iv Ip Ir,
  AT atm = true ->
  AT atm0 = true ->
  atm2 = passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm)
            (atm_passing_predSO_ll_llx atm)) ->
  SOturnst W Iv Ip Ir (replace_pred_l atm0 lP (list_Var (length lP) y)
    (vsS_syn_l (FOv_att_P_l atm2 lP) y)) <->
  SOturnst W Iv Ip Ir (replace_pred_l atm0 lP (list_Var (length lP) y)
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
      rewrite rep_pred_l_conjSO. rewrite SOturnst_conjSO. apply bi_refl.
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
  SOturnst W Iv Ip Ir (replace_pred_l atm2 lP (list_Var (length lP) y) (vsS_syn_l (FOv_att_P_l atm0 lP) y)) <->
  SOturnst W Iv Ip Ir (replace_pred_l atm lP (list_Var (length lP) y) (vsS_syn_l (FOv_att_P_l atm0 lP) y)).
Proof.
  induction atm; intros atm0 atm3 lP y W Iv Ip Ir Hat1 Hat2 Hat3; try discriminate.
    rewrite Hat1. simpl in *. apply bi_refl.

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
  SOturnst W Iv Ip Ir (replace_pred_l atm2 lP (list_Var (length lP) y)
    (vsS_syn_l (FOv_att_P_l atm2 lP) y)) <->
  SOturnst W Iv Ip Ir (replace_pred_l atm lP (list_Var (length lP) y)
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

Lemma SOQFree_is_unary_predless : forall beta P x cond,
  is_unary_predless cond = true ->
  SOQFree beta = true ->
  SOQFree (replace_pred beta P x cond) = true.
Proof.
  intros until 0. intros Hun Hno.
  apply SOQFree_rep_pred. assumption.
  apply un_predless_SOQFree. assumption.
Qed.

Lemma SOQFree_is_unary_predless_l : forall lP lx lcond beta,
  is_unary_predless_l lcond = true ->
  SOQFree beta = true ->
  SOQFree (replace_pred_l beta lP lx lcond) = true.
Proof.
  induction lP; intros lx lcond beta Hun Hno.
    simpl. assumption.

    destruct lx. simpl. assumption. 
    destruct lcond. assumption.
    simpl in *. case_eq (is_unary_predless s);
      intros Hun2; rewrite Hun2 in *. 2 : discriminate.
    apply SOQFree_is_unary_predless. assumption.
    apply IHlP; assumption.
Qed.

Lemma SOQFree_instant_cons_empty' : forall beta alpha,
  SOQFree beta = true ->
  SOQFree (instant_cons_empty' alpha beta) = true.
Proof.
  unfold instant_cons_empty'.
  intros beta alpha Hno. apply SOQFree_is_unary_predless_l.
  apply is_unary_predless_l_nlist_empty.
  assumption.
Qed.

Lemma lem_e2 : forall lP beta rel atm y xn W1 Iv1 Ip1 Ir1,
  REL rel = true ->
  AT atm = true -> 
ex_FOvar_x_ll y (FOv_att_P_l atm lP) = false ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  attached_allFO_x beta (Var xn) = false ->
  attached_exFO_x beta (Var xn) = false ->
  closed_except beta (Var xn) ->

  x_occ_in_alpha (instant_cons_empty' (conjSO rel atm) beta) (Var xn) = true ->
  is_in_pred_l (preds_in (implSO (conjSO rel atm) beta)) lP = true ->
SOturnst W1 Iv1 Ip1 Ir1 (replace_pred_l  (implSO (conjSO rel atm)
        (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)
           (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
           (rev_seq (S (Nat.max (max_FOv (implSO (conjSO rel atm) beta)) xn))
              (length (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn)))))) lP
     (list_Var (length lP) y) (vsS_syn_l (FOv_att_P_l (conjSO rel atm) lP) y)) <->
SOturnst W1 Iv1 Ip1 Ir1 (replace_pred_l (implSO (conjSO rel (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm))))
        (newnew_pre (instant_cons_empty'
              (conjSO rel (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm))))
              beta)
           (rem_FOv (FOvars_in  (instant_cons_empty'  (conjSO rel
              (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm)))) beta))
              (Var xn))
           (rev_seq (S (Nat.max (max_FOv (implSO (conjSO rel
                             (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm))))
                          beta)) xn))
              (length (rem_FOv(FOvars_in (instant_cons_empty' (conjSO rel
                             (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm))))
                          beta)) (Var xn)))))) lP (list_Var (length lP) y)
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

    rewrite lem118'_max_FOv.
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

    rewrite lem118'_max_FOv in SOt.
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
ex_FOvar_x_ll y (FOv_att_P_l atm lP) = false ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  attached_allFO_x beta (Var xn) = false ->
  attached_exFO_x beta (Var xn) = false ->
  closed_except beta (Var xn) ->

  x_occ_in_alpha (instant_cons_empty' atm beta) (Var xn) = true ->
  is_in_pred_l (preds_in (implSO atm beta)) lP = true ->
SOturnst W1 Iv1 Ip1 Ir1 (replace_pred_l  (implSO atm
        (newnew_pre (instant_cons_empty' atm beta)
           (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn))
           (rev_seq (S (Nat.max (max_FOv (implSO atm beta)) xn))
              (length (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn)))))) lP
     (list_Var (length lP) y) (vsS_syn_l (FOv_att_P_l atm lP) y)) <->
SOturnst W1 Iv1 Ip1 Ir1 (replace_pred_l (implSO ( (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm))))
        (newnew_pre (instant_cons_empty'
              ((passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm))))
              beta)
           (rem_FOv (FOvars_in  (instant_cons_empty'  (
              (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm)))) beta))
              (Var xn))
           (rev_seq (S (Nat.max (max_FOv (implSO (
                             (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm))))
                          beta)) xn))
              (length (rem_FOv(FOvars_in (instant_cons_empty' (
                             (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm))))
                          beta)) (Var xn)))))) lP (list_Var (length lP) y)
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

    rewrite lem118'_max_FOv.
    apply SOt.

      apply lem_e22 with (atm2 :=
        (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) 
        (atm_passing_predSO_ll_llx atm))) ); try assumption.
      reflexivity. assumption.

    simpl in SOt. apply lem_e5_atm; try assumption.
      apply SOQFree_newnew_pre.
      apply SOQFree_instant_cons_empty'. assumption.
    simpl.

    rewrite lem118'_max_FOv in SOt.
    apply SOt.

      apply lem_e22 with (atm := atm) (atm2 :=
        (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) 
        (atm_passing_predSO_ll_llx atm))) ); try assumption.
      reflexivity. assumption.
Qed.

Lemma is_in_FOvar_atm_passing_predSO_ll_gen : forall atm P x,
  AT atm = true ->
  is_in_FOvar x (fun2 (passing_conj (passing_predSO_ll
      (atm_passing_predSO_ll_lP atm) 
      (atm_passing_predSO_ll_llx atm))) P) = 
  is_in_FOvar x (fun2 atm P).
Proof.
  induction atm; intros [Pn] [xn] Hat; try discriminate.
    destruct p as [Qm]. destruct f as [ym].
    simpl in *. reflexivity.

    simpl. rewrite passing_predSO_ll_app. rewrite fun2_passing_conj_app.
    do 2 rewrite is_in_FOvar_app in *.
    rewrite IHatm1. rewrite IHatm2. reflexivity.
    apply AT_conjSO_r in Hat. assumption.
    apply AT_conjSO_l in Hat. assumption.
    apply lem118'_length. apply AT_conjSO_l in Hat. assumption.
Qed.

Lemma lem118'_ex_FOvar_x_ll  : forall lP atm y,
  AT atm = true ->
  ex_FOvar_x_ll y (FOv_att_P_l (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm)
      (atm_passing_predSO_ll_llx atm))) lP) =
  ex_FOvar_x_ll y (FOv_att_P_l atm lP).
Proof.
  induction lP; intros atm y Hat. reflexivity.
  simpl. rewrite IHlP.
  rewrite is_in_FOvar_atm_passing_predSO_ll_gen. reflexivity.
  all : assumption.
Qed.

Lemma lem118'_x_occ_instant_cons_empty' : forall atm rel beta x,
AT atm = true ->
REL rel = true ->
x_occ_in_alpha
  (instant_cons_empty'
     (conjSO rel (passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm))))
     beta) x = 
x_occ_in_alpha (instant_cons_empty' (conjSO rel atm) beta) x .
Proof.
  unfold instant_cons_empty'. simpl.
  intros atm rel beta x Hat Hrel.
  rewrite (preds_in_rel rel Hrel). simpl.
  rewrite list_pred_not_in_passing_predSO_ll. 
  rewrite <- lem118'_preds_in.
  reflexivity.
  assumption.
  apply lem118'_length. assumption.
  apply lem118'_ex_nil_in_llv. assumption.
Qed.

Lemma lem118'_x_occ_instant_cons_empty'_atm : forall atm beta x,
AT atm = true ->
x_occ_in_alpha
  (instant_cons_empty'
     ((passing_conj (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm))))
     beta) x = 
x_occ_in_alpha (instant_cons_empty' atm beta) x .
Proof.
  unfold instant_cons_empty'. simpl.
  intros atm beta x Hat.
  rewrite list_pred_not_in_passing_predSO_ll. 
  rewrite <- lem118'_preds_in.
  reflexivity.
  assumption.
  apply lem118'_length. assumption.
  apply lem118'_ex_nil_in_llv. assumption.
Qed.

Lemma vsSahlq_instant_aim1_fwd4_closer2_REV_gen : forall lx lP beta rel atm y xn W Iv Ip Ir,
  REL rel = true ->
  AT atm = true -> 
ex_FOvar_x_ll y (FOv_att_P_l atm lP) = false ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  attached_allFO_x beta (Var xn) = false ->
  attached_exFO_x beta (Var xn) = false ->
  closed_except beta (Var xn) ->

  x_occ_in_alpha (instant_cons_empty' (conjSO rel atm) beta) (Var xn) = true ->
  is_in_pred_l (preds_in (implSO (conjSO rel atm) beta)) lP = true ->
  SOturnst W Iv Ip Ir (replace_pred_l (list_closed_allFO (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)  
      (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) beta)) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn)))))) lx)
    lP (list_Var (length lP) y)
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
    rewrite lem118'_ex_FOvar_x_ll; assumption.
    rewrite lem118'_x_occ_instant_cons_empty'; assumption.

    simpl in *. rewrite (preds_in_rel rel Hrel) in *. simpl in *.
    rewrite is_in_pred_l_app_if.
    pose proof Hin as Hin'.
    rewrite is_in_pred_l_app_comm_l in Hin.
    apply is_in_pred_l_app_r in Hin.
    apply is_in_pred_l_app_r in Hin'.
    rewrite is_in_pred_l_preds_in_passing_predSO_ll.
    rewrite (is_in_pred_l_trans _ _ _ (lem118'_is_in_pred_l atm Hat)).
    assumption. assumption.
    apply lem118'_length. assumption.
    apply lem118'_ex_nil_in_llv. assumption.


    rewrite rep_pred_l_list_closed_allFO in *.
    apply (equiv_list_closed_allFO ((replace_pred_l
              (implSO (conjSO rel atm)
                 (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)
                    (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
                    (rev_seq (S (Nat.max (max_FOv (implSO (conjSO rel atm) beta)) xn))
                       (length
                          (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta))
                             (Var xn)))))) lP (list_Var (length lP) y)
              (vsS_syn_l (FOv_att_P_l (conjSO rel atm) lP) y)))).
    intros W1 Iv1 Ip1 Ir1.
    apply lem_e2; assumption.
    assumption.
Qed.

Lemma vsSahlq_instant_aim1_fwd4_closer2_REV_gen_atm : forall lx lP beta atm y xn W Iv Ip Ir,
  AT atm = true -> 
ex_FOvar_x_ll y (FOv_att_P_l atm lP) = false ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  attached_allFO_x beta (Var xn) = false ->
  attached_exFO_x beta (Var xn) = false ->
  closed_except beta (Var xn) ->

  x_occ_in_alpha (instant_cons_empty' atm beta) (Var xn) = true ->
  is_in_pred_l (preds_in (implSO atm beta)) lP = true ->
  SOturnst W Iv Ip Ir (replace_pred_l (list_closed_allFO (implSO
    atm
    (newnew_pre (instant_cons_empty' atm beta)  
      (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn))
      (rev_seq (S (max (max_FOv (implSO atm beta)) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn)))))) lx)
    lP (list_Var (length lP) y)
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
    rewrite lem118'_ex_FOvar_x_ll; assumption.
    rewrite lem118'_x_occ_instant_cons_empty'_atm; assumption.

    simpl in *.
    rewrite is_in_pred_l_app_if.
    pose proof Hin as Hin'.
    rewrite is_in_pred_l_app_comm_l in Hin.
    apply is_in_pred_l_app_r in Hin.
    apply is_in_pred_l_app_r in Hin'.
    rewrite is_in_pred_l_preds_in_passing_predSO_ll.
    rewrite (is_in_pred_l_trans _ _ _ (lem118'_is_in_pred_l atm Hat)).
    assumption. assumption.
    apply lem118'_length. assumption.
    apply lem118'_ex_nil_in_llv. assumption.


    rewrite rep_pred_l_list_closed_allFO in *.
    apply (equiv_list_closed_allFO ((replace_pred_l
              (implSO atm
                 (newnew_pre (instant_cons_empty' atm beta)
                    (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn))
                    (rev_seq (S (Nat.max (max_FOv (implSO atm beta)) xn))
                       (length
                          (rem_FOv (FOvars_in (instant_cons_empty' atm beta))
                             (Var xn)))))) lP (list_Var (length lP) y)
              (vsS_syn_l (FOv_att_P_l atm lP) y)))).
    intros W1 Iv1 Ip1 Ir1.
    apply lem_e2_atm; assumption.
    assumption.
Qed.

(* ---------------------------- *)

Lemma hopeful3_REV : forall lx lP beta alpha rel atm y xn W Iv Ip Ir,
  REL rel = true ->
  AT atm = true ->
ex_FOvar_x_ll y (FOv_att_P_l atm lP) = false ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  attached_allFO_x beta (Var xn) = false ->
  attached_exFO_x beta (Var xn) = false ->
  closed_except beta (Var xn) ->
  x_occ_in_alpha (instant_cons_empty' (conjSO rel atm) beta) (Var xn) = true ->
  is_in_pred_l (preds_in (implSO (conjSO rel atm) beta)) lP = true ->
  (exists P, P_occurs_in_alpha alpha P = true) ->
 (forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir alpha <-> SOturnst W Iv Ip Ir (list_closed_allFO (implSO (conjSO rel atm) beta) lx)) ->
  SOturnst W Iv Ip Ir (replace_pred_l (list_closed_allFO (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)  
      (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) beta)) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn)))))) lx)
    lP (list_Var (length lP) y)
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
ex_FOvar_x_ll y (FOv_att_P_l atm lP) = false ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  attached_allFO_x beta (Var xn) = false ->
  attached_exFO_x beta (Var xn) = false ->
  closed_except beta (Var xn) ->
  x_occ_in_alpha (instant_cons_empty' atm beta) (Var xn) = true ->
  is_in_pred_l (preds_in (implSO atm beta)) lP = true ->
  (exists P, P_occurs_in_alpha alpha P = true) ->
 (forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir alpha <-> SOturnst W Iv Ip Ir (list_closed_allFO (implSO atm beta) lx)) ->
  SOturnst W Iv Ip Ir (replace_pred_l (list_closed_allFO (implSO
    atm
    (newnew_pre (instant_cons_empty' atm beta)  
      (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn))
      (rev_seq (S (max (max_FOv (implSO atm beta)) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn)))))) lx)
    lP (list_Var (length lP) y)
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
  Nat.leb (max_FOv alpha) n = true ->
  is_in_FOvar (Var (S n)) (FOvars_in alpha) = false.
Proof.
  induction alpha; intros n Hat Hleb; try discriminate.
    destruct p. destruct f as [m]. simpl in *.
    destruct m. reflexivity. case_eq (beq_nat n m); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq) in *. 
      rewrite my_arith__my_leb_nat.leb_suc_f in Hleb. discriminate.

      reflexivity.

    simpl.
    rewrite is_in_FOvar_app. rewrite IHalpha1. apply IHalpha2.
      apply (AT_conjSO_r _ _ Hat).
      simpl in Hleb. apply leb_max in Hleb.
      apply Hleb.

      apply (AT_conjSO_l _ _ Hat).
      simpl in Hleb. apply leb_max in Hleb.
      apply Hleb.
Qed.

Lemma lem_f1'' : forall alpha,
AT alpha = true ->
  is_in_FOvar (Var (S (max_FOv alpha))) (FOvars_in alpha) = false.
Proof.
  intros alpha Hat. apply lem_f7. assumption. apply leb_refl.
Qed.


Lemma vsS_preprocessing_Step1_1_againTRY'_withex'' : forall phi1 phi2 rel atm x lv,
  vsSahlq_ante phi1 = true ->
  uniform_pos phi2 ->
  REL rel = true ->
  AT atm = true ->
          is_in_pred_l (preds_in (conjSO rel atm)) (preds_in (ST phi1 x)) = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
      (Ir : W -> W -> Prop),
    SOturnst W Iv Ip Ir (ST phi1 x) <->
    SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv)) ->
existsT2 lv0 : list FOvariable,
     ((existsT2 atm0 : SecOrder,
         (AT atm0 = true) *
((is_in_FOvar (Var (new_FOv_pp_pre2 atm0)) (FOvars_in atm0) = false) *
  ((existsT rel0 : SecOrder,
     REL rel0 = true /\
          is_in_pred_l (preds_in (conjSO rel0 atm0)) (preds_in (ST phi1 x)) = true /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (ST (mimpl phi1 phi2) x) <->
          SOturnst W Iv Ip Ir
            (list_closed_allFO (implSO (conjSO rel0 atm0) (ST phi2 x)) lv0))) +
       (is_in_pred_l (preds_in atm0) (preds_in (ST phi1 x)) = true /\
      forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir (ST (mimpl phi1 phi2) x) <->
      SOturnst W Iv Ip Ir (list_closed_allFO (implSO atm0 (ST phi2 x)) lv0)))))).
Proof.
  intros phi1 phi2 rel atm x lv Hvsa Hun HREL HAT Hin H.
  pose proof (equiv_implSO2 _ _ (ST phi2 x) H) as H1.
  pose proof (equiv3_3_struc2_2' lv (conjSO rel atm) (ST phi2 x)) as H2.
  pose proof (SOturnst_trans _ _ _ H1 H2) as H3.
  pose proof rename_FOv_A_rel_atm.
  destruct (rename_FOv_A_rel_atm lv rel atm (ST phi2 x) HREL HAT)
     as [rel' [atm' [H' [HREL' HAT']]]] .
  rewrite H' in *.
  exists (rename_FOv_A_list (conjSO rel atm) (ST phi2 x) lv).
  exists atm'.
  apply pair. assumption. apply pair.
unfold new_FOv_pp_pre2.

apply (lem_f1'' atm'); try assumption.
  left.
  exists rel'.
  apply conj. assumption.
  apply conj. 2: assumption.
    rewrite <- H'.
    rewrite preds_in_rename_FOv_A.
    assumption.
Defined.

Lemma vsS_preprocessing_Step1_3_againTRY'_withex' : forall phi1 phi2 atm x lv,
  vsSahlq_ante phi1 = true ->
  uniform_pos phi2 ->
  AT atm = true ->
  is_in_pred_l (preds_in (atm)) (preds_in (ST phi1 x)) = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
      (Ir : W -> W -> Prop),
    SOturnst W Iv Ip Ir (ST phi1 x) <->
    SOturnst W Iv Ip Ir (list_closed_exFO atm lv)) ->
existsT2 lv0 : list FOvariable,
   (existsT2 atm0 : SecOrder,
       (AT atm0 = true) *
((is_in_FOvar (Var (new_FOv_pp_pre2 atm0)) (FOvars_in atm0) = false) *

    ((existsT rel0 : SecOrder,
       REL rel0 = true /\
      is_in_pred_l (preds_in (conjSO rel0 atm0)) (preds_in (ST phi1 x)) = true /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (ST (mimpl phi1 phi2) x) <->
          SOturnst W Iv Ip Ir
            (list_closed_allFO (implSO (conjSO rel0 atm0) (ST phi2 x)) lv0))) +
     (is_in_pred_l (preds_in atm0) (preds_in (ST phi1 x)) = true /\
     forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir (ST (mimpl phi1 phi2) x) <->
      SOturnst W Iv Ip Ir (list_closed_allFO (implSO atm0 (ST phi2 x)) lv0))))).
Proof.
  intros phi1 phi2 atm x lv Hvsa Hun HAT Hin H.
  pose proof (equiv_implSO2 _ _ (ST phi2 x) H) as H1.
  pose proof (equiv3_3_struc2_2' lv atm (ST phi2 x)) as H2.
  pose proof (SOturnst_trans _ _ _ H1 H2) as H3.
  pose proof (same_struc_rename_FOv_A atm (ST phi2 x) lv) as H4.
  apply same_struc_comm in H4.
  apply same_struc_AT in H4. 2 : assumption.
  exists (rename_FOv_A_list atm (ST phi2 x) lv).
  exists (rename_FOv_A atm (ST phi2 x) lv).
  apply pair. assumption.
  apply pair.
   unfold new_FOv_pp_pre2. 
    apply (lem_f1'' ). assumption.

  right.
  apply conj.
    rewrite preds_in_rename_FOv_A. assumption.
  assumption.
Defined.

Lemma vsS_preprocessing_Step1_pre_againTRY'_withex' : forall phi1 phi2 x,
  vsSahlq_ante phi1 = true ->
  uniform_pos phi2  ->
  existsT2 lv : list FOvariable,
   (existsT2 atm : SecOrder,
       (AT atm = true) *
((is_in_FOvar (Var (new_FOv_pp_pre2 atm)) (FOvars_in atm) = false) *
    ((existsT rel : SecOrder,
     REL rel = true /\
          is_in_pred_l (preds_in (conjSO rel atm)) (preds_in (ST phi1 x)) = true /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (ST (mimpl phi1 phi2) x) <->
          SOturnst W Iv Ip Ir (list_closed_allFO (implSO (conjSO rel atm) (ST phi2 x)) lv))) +

    (is_in_pred_l (preds_in atm) (preds_in (ST phi1 x)) = true /\
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
  is_in_FOvar x (FOvars_in atm) = false ->
is_in_FOvar x (fun2 atm P) = false.
Proof.
  induction atm; intros [xn] [Pn] Hat Hin; try discriminate.
    destruct p as [Qm]. destruct f as [ym]. simpl in *.
    case_eq (beq_nat Pn Qm); intros Hbeq.
      simpl. case_eq (beq_nat xn ym); intros Hbeq2;
        rewrite Hbeq2 in *. discriminate.

        reflexivity.
      reflexivity.

    pose proof (AT_conjSO_l _ _ Hat).
    pose proof (AT_conjSO_r _ _ Hat).
    simpl in Hin.
    rewrite is_in_FOvar_app in Hin. 
    case_eq (is_in_FOvar (Var xn) (FOvars_in atm1));
      intros Hin1; rewrite Hin1 in *. discriminate.
    simpl. rewrite is_in_FOvar_app. rewrite IHatm1.
    rewrite IHatm2. reflexivity.
    all : assumption.
Qed.

Lemma lem_f3 : forall lP atm x,
AT atm = true ->
  is_in_FOvar x (FOvars_in atm) = false ->
ex_FOvar_x_ll x (FOv_att_P_l atm lP) = false.
Proof.
  induction lP; intros atm x Hat H.
    simpl in *. reflexivity.

    simpl in *. rewrite lem_f4. apply IHlP.
    all : try assumption.
Qed.