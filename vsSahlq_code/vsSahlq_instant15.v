Require Export vsSahlq_instant13.

(* ---------------------------------------------------------- *)

Fixpoint passing_conj lalpha : SecOrder :=
  match lalpha with
  | nil => eqFO (Var 1) (Var 1)
  | cons alpha nil => alpha
  | cons alpha lalpha' => conjSO alpha (passing_conj lalpha')
  end.

Fixpoint passing_conj_atm P lx : SecOrder :=
  match lx with
  | nil => eqFO (Var 1) (Var 1)
  | cons x nil => predSO P x
  | cons x lx' => conjSO (predSO P x) (passing_conj_atm P lx')
  end.

Fixpoint passing_predSO_l P lx : list SecOrder :=
  match lx with
  | nil => nil
  | cons x lx' => cons (predSO P x) (passing_predSO_l P lx')
  end .

Fixpoint passing_predSO_ll lP llx : list SecOrder :=
  match lP, llx with
  | nil, _ => nil
  | _, nil => nil
  | cons P lP', cons lx llx' => cons (passing_conj (passing_predSO_l P lx))
                         (passing_predSO_ll lP' llx')
  end .

Lemma lem4 : forall lx P,
passing_conj_atm P lx =
passing_conj (passing_predSO_l P lx).
Proof.
  induction lx; intros P. reflexivity.
  simpl. destruct lx. simpl. reflexivity.
  simpl in *. rewrite IHlx. reflexivity.
Qed.

Lemma lem11_l : forall {A : Type} (l1 l2 : list A),
  ~ (l1 = nil) ->
  ~ (app l1 l2 = nil).
Proof.
  intros A. induction l1; intros l2 H.
    contradiction (H eq_refl).

    discriminate.
Qed.

Lemma lem11_r : forall {A : Type} (l1 l2 : list A),
  ~ (l2 = nil) ->
  ~ (app l1 l2 = nil).
Proof.
  intros A. induction l2; intros Hnil.
    contradiction (Hnil eq_refl).

    destruct l1; discriminate.
Qed.

Lemma lem10 : forall alpha P,
  SOQFree_P alpha P = true ->
  P_occurs_in_alpha alpha P = true ->
  ~(fun2 alpha P = nil).
Proof.
  induction alpha; intros [Pn] Hno H.
    unfold P_occurs_in_alpha in H.
    simpl in *. destruct p as [Qm].
    destruct f as [xn]. simpl in *.
    case_eq (beq_nat Pn Qm); intros Hbeq;
      rewrite Hbeq in *. intros. all : try discriminate.

(*     unfold P_occurs_in_alpha in H. destruct f. destruct f0.
    simpl in *. discriminate.

    unfold P_occurs_in_alpha in H. destruct f. destruct f0.
    simpl in *. discriminate.
 *)
    unfold P_occurs_in_alpha in H. destruct f.
    simpl in *. apply IHalpha. assumption. apply H.

    unfold P_occurs_in_alpha in H. destruct f.
    simpl in *. apply IHalpha. assumption. apply H.
  
    simpl in *. apply IHalpha. assumption.
    rewrite P_occurs_in_alpha_negSO.
    assumption.

    simpl. apply P_occurs_in_alpha_conjSO in H.
    apply SOQFree_P_conjSO_t in Hno. destruct Hno as [Ha Hb].
    destruct H as [H1 | H2].
      apply lem11_l. apply IHalpha1; assumption.

      apply lem11_r. apply IHalpha2; assumption.

    simpl. apply P_occurs_in_alpha_conjSO in H.
    apply SOQFree_P_disjSO_t in Hno. destruct Hno as [Ha Hb].
    destruct H as [H1 | H2].
      apply lem11_l. apply IHalpha1; assumption.

      apply lem11_r. apply IHalpha2; assumption.

    simpl. apply P_occurs_in_alpha_conjSO in H.
    apply SOQFree_P_implSO_t in Hno. destruct Hno as [Ha Hb].
    destruct H as [H1 | H2].
      apply lem11_l. apply IHalpha1; assumption.

      apply lem11_r. apply IHalpha2; assumption.

    unfold P_occurs_in_alpha in H.
    destruct p as [Qm]. simpl in *.
    case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *.
      discriminate.
    apply IHalpha; assumption.

    unfold P_occurs_in_alpha in H.
    destruct p as [Qm]. simpl in *.
    case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *.
      discriminate.
    apply IHalpha; assumption.
Qed.

Lemma AT_passing_conj_atm : forall lx P,
  ~ lx = nil ->
  AT (passing_conj_atm P lx) = true.
Proof.
  induction lx; intros [Pn] H.
    contradiction (H eq_refl).
  case_eq lx. intros Hlx. simpl. reflexivity.
  intros x lxx Hlx. rewrite <- Hlx.
  simpl. rewrite Hlx. rewrite <- Hlx.
  simpl. apply IHlx. rewrite Hlx. intros. discriminate.
Qed.

Lemma passing_predSO_ll_nil : forall l1 l2,
  passing_predSO_ll l1 l2 = nil ->
  ( (l1 = nil) \/ (l2 = nil) ).
Proof.
  induction l1; intros l2 H.
    left. reflexivity.
  
    simpl in H. destruct l2. right. reflexivity.
    discriminate.
Qed.

Lemma lem1 : forall alpha P,
  P_occurs_in_alpha alpha P = false ->
  fun2 alpha P = nil.
Proof.
  induction alpha; intros [Pn] H.
    unfold P_occurs_in_alpha in *.
    destruct p as [Qm]. destruct f. simpl in *.
    case_eq (beq_nat Pn Qm); intros Hbeq;
      rewrite Hbeq in *. discriminate. reflexivity.

    unfold P_occurs_in_alpha in *. simpl in *.
    reflexivity.

    unfold P_occurs_in_alpha in *. simpl in *.
    reflexivity.

    unfold P_occurs_in_alpha in *. simpl in *.
    apply IHalpha. assumption.

    unfold P_occurs_in_alpha in *. destruct f. simpl in *.
    apply IHalpha. assumption.

    unfold P_occurs_in_alpha in *. simpl in *.
    apply IHalpha. assumption.

    apply P_occurs_in_alpha_conjSO_f in H.
    simpl. rewrite IHalpha1. rewrite IHalpha2.
    all : try apply H. reflexivity.

    apply P_occurs_in_alpha_conjSO_f in H.
    simpl. rewrite IHalpha1. rewrite IHalpha2.
    all : try apply H. reflexivity.

    apply P_occurs_in_alpha_conjSO_f in H.
    simpl. rewrite IHalpha1. rewrite IHalpha2.
    all : try apply H. reflexivity.

    destruct p as [Qm].
    unfold P_occurs_in_alpha in *. simpl in *.
    case_eq (beq_nat Pn Qm); intros Hbeq;
      rewrite Hbeq in *. discriminate.
      apply IHalpha. assumption.

    destruct p as [Qm].
    unfold P_occurs_in_alpha in *. simpl in *.
    case_eq (beq_nat Pn Qm); intros Hbeq;
      rewrite Hbeq in *. discriminate.
      apply IHalpha. assumption.
Qed.

Lemma passing_conj_app : forall l1 l2,
  ~ l1 = nil ->
  ~ l2 = nil ->
  forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (passing_conj (app l1 l2)) <->
  SOturnst W Iv Ip Ir (conjSO (passing_conj l1) (passing_conj l2)).
Proof.
  induction l1; intros l2 H1 H2 W Iv Ip Ir.
    contradiction (H1 eq_refl).
  simpl. case_eq (app l1 l2).
    intros HH.      
    apply app_rnil_r in HH. rewrite HH in H2.
    contradiction (H2 eq_refl).

    intros beta l' H. case_eq l1.

      intros Hnil. rewrite <- H. rewrite Hnil.
      simpl. apply bi_refl.

      intros beta1 l1' Hl1.
      rewrite <- Hl1. rewrite <- H.
      do 2 rewrite SOturnst_conjSO in *.
      split; intros SOt;
        destruct SOt as [SOt1 SOt2].
        apply IHl1 in SOt2. destruct SOt2 as [SOt2 SOt3].
        apply conj. apply conj. all : try assumption.
        intros HH. rewrite Hl1 in *. discriminate.

        destruct SOt1 as [SOt1 SOt3].
        apply conj. assumption.
        apply IHl1.
        intros HH; rewrite HH in *; discriminate.
        all : try assumption.
        apply conj; assumption.
Qed.

Lemma preds_in_passing_conj_app: forall l1  l2,
  preds_in (passing_conj (app l1 l2)) =
  app (preds_in (passing_conj l1)) (preds_in (passing_conj l2)).
Proof.
  induction l1; intros l2.
    simpl. reflexivity.
 
    simpl app.
    case_eq l1. intros H1.
      simpl. case_eq l2. intros H2. 
      simpl. symmetry. apply List.app_nil_r.

      intros beta2 lbeta2 Hbeta2.
      rewrite <- Hbeta2.
      reflexivity.

      intros beta1 lbeta1 Hbeta1.
      rewrite <- Hbeta1.
      simpl preds_in.
      assert (app l1 l2 = cons beta1 (app lbeta1 l2)) as Heq.
        rewrite Hbeta1. reflexivity.
      rewrite Heq. rewrite app_assoc. rewrite <- IHl1.
      rewrite <- Heq. reflexivity.
Qed. 

Fixpoint is_in_in_FOvar_ll (l1 l2 : list (list FOvariable)) : bool :=
  match l1, l2 with 
  | nil, nil => true
  | nil, _ => false 
  | _, nil => false 
  | cons x1 l1', cons x2 l2' => if is_in_FOvar_l x1 x2 then is_in_in_FOvar_ll l1' l2' else false
  end.

Lemma lem_try23 : forall lv P W Iv Ip1 Ip2 Ir pa,
  SOturnst W Iv (altered_Ip Ip1 pa P) Ir (passing_conj (passing_predSO_l P lv)) ->
  SOturnst W Iv (altered_Ip Ip2 pa P) Ir (passing_conj (passing_predSO_l P lv)).
Proof.  
  induction lv; intros [Pn] W Iv Ip1 Ip2 Ir pa SOt.
    simpl in *. reflexivity.

    destruct a as [Qm].
    simpl passing_conj in *.
    case_eq (passing_predSO_l (Pred Pn) lv).
      intros H. rewrite H in *.
      simpl in *. rewrite <- beq_nat_refl in *. assumption.

      intros beta lbeta Hlbeta.
      rewrite Hlbeta in *. rewrite <- Hlbeta in *.
      rewrite SOturnst_conjSO in *.
      apply conj.
        simpl in *. rewrite <- beq_nat_refl in *.
        apply SOt.

        apply IHlv with (Ip1 := Ip1).
        apply SOt.
Qed.

Lemma is_constant_nil : forall {A : Type} (a : A),
  is_constant (@nil A).
Proof.
  intros A a. unfold is_constant. exists a. exists 0.
  reflexivity.
Qed.

Lemma lem_c8 : forall lP1 lP2 lx1 lx2 n P Q R x y z,
  length lP1 = length lx1 ->
  ind_FOv (indicies_l2 (app lP1 (cons P (cons Q lP2))) R)
          (app lx1 (cons x (cons y lx2))) = constant_l z n ->
  exists m,
  ind_FOv (indicies_l2 (app lP1 (cons Q (cons P lP2))) R)
          (app lx1 (cons y (cons x lx2))) = constant_l z m.
Proof.
  induction lP1; intros lP2 lx1 lx2 n [Pn] [Qm] [Rn] x y z Hlength H.
    simpl in *. symmetry in Hlength.
    apply List.length_zero_iff_nil in Hlength.
    rewrite Hlength in *. unfold indicies_l2 in *. simpl  in *.
    case_eq (beq_nat Rn Qm); intros Hbeq; rewrite Hbeq in *;
      case_eq (beq_nat Rn Pn); intros Hbeq2; rewrite Hbeq2 in *;
        simpl in *. exists n. destruct n. discriminate. destruct n.
        discriminate. inversion H. rewrite H3. reflexivity.

        all : try (rewrite ind_FOv_ind_l2_pre_cons in *;
        rewrite ind_FOv_ind_l2_pre_cons in *;
        exists n; assumption).

    destruct a as [Sn]. simpl in *. unfold indicies_l2 in *.
    simpl in *. case_eq (beq_nat Rn Sn); intros Hbeq;
      rewrite Hbeq in *.
      simpl in *. destruct lx1. discriminate.
      simpl in *. rewrite ind_FOv_ind_l2_pre_cons in *.
      destruct n. discriminate.
      inversion H as [[Ha Hb]].
      inversion Hlength as [Hlength'].
      destruct (IHlP1 _ _ _ _ _ _ _ _ _ _ Hlength' Hb) as [m Hm].
      exists (S m). rewrite Hm. reflexivity.

      destruct lx1. discriminate. simpl in *.
      rewrite ind_FOv_ind_l2_pre_cons in *.
      inversion Hlength as [Hlength'].
      destruct (IHlP1 _ _ _ _ _ _ _ _ _ _  Hlength' H) as [m Hm].
      exists m. assumption.
Qed.

Lemma ind_llv_ind_l2_pre_cons : forall lP n lcond Q alpha,
  ind_llv (indicies_l2_pre lP Q (S n)) (cons alpha lcond) =
  ind_llv (indicies_l2_pre lP Q n) lcond.
Proof.
  induction lP; intros n lcond Q alpha.
    reflexivity.

    simpl. destruct Q as [Pn]; destruct a as [Qm].
    case_eq (beq_nat Pn Qm); intros Hbeq.
      simpl. destruct n; rewrite IHlP; reflexivity.
      rewrite IHlP. reflexivity.
Qed.

Lemma consistent_lP_lx_P_cons_switch_gen : forall lP0 lx0 lP lx P Q R x y,
  length lP0 = length lx0 ->
  consistent_lP_lx_P (app lP0 (cons P (cons Q lP))) (app lx0 (cons x (cons y lx))) R ->
  consistent_lP_lx_P (app lP0 (cons Q (cons P lP))) (app lx0 (cons y (cons x lx))) R.
Proof.
  intros until 0. intros Hlength Hcon.
  unfold consistent_lP_lx_P in *.
  unfold is_constant in *. destruct Hcon as [a [n H]].
  exists a.
  apply (lem_c8 lP0 lP lx0 lx n P Q R x y a Hlength). assumption.
Qed.

Lemma consistent_lP_lx_cons_switch_gen : forall lP0 lx0 lP lx P Q x y,
  length lP0 = length lx0 ->
  consistent_lP_lx (app lP0 (cons P (cons Q lP))) (app lx0 (cons x (cons y lx))) ->
  consistent_lP_lx (app lP0 (cons Q (cons P lP))) (app lx0 (cons y (cons x lx))).
Proof.
  intros until 0. intros Hlength Hcon.
  unfold consistent_lP_lx in *. intros R.
  apply consistent_lP_lx_P_cons_switch_gen.
  assumption. apply Hcon.
Qed.

Lemma lem_try26  : forall l l' P x y,
  consistent_lP_lx (cons P (cons P l)) (cons x (cons y l')) ->
  x = y.
Proof.
  induction l; intros l' [Pn] x y H.
    unfold consistent_lP_lx in H.
    unfold consistent_lP_lx_P in H.
    specialize (H (Pred Pn)). unfold indicies_l2 in H.
    simpl in *. rewrite <- beq_nat_refl in *. 
    simpl in *. unfold is_constant in H.
    destruct H as [z [n H]].
    destruct n. discriminate.
    destruct n. discriminate.
    simpl in *. inversion H. reflexivity.

    destruct l'.
      unfold consistent_lP_lx in *. pose proof H as H'.
      specialize (H a). unfold consistent_lP_lx_P in H. unfold indicies_l2 in *.
      simpl in *. destruct a as [Qm].
      case_eq (beq_nat Qm Pn); intros Hbeq; rewrite Hbeq in *;
        rewrite <- beq_nat_refl in *; simpl in *.
        unfold is_constant in H. destruct H as [z [n H]]. destruct n. discriminate.
        destruct n. discriminate. simpl in *. inversion H. reflexivity.

        unfold is_constant in H. destruct H as [z [n H]].
        destruct n. discriminate. simpl in *. inversion H as [[H1 H2]].
        destruct l. simpl in *.
  
        simpl in *. apply (IHl nil (Pred Pn) x y).
        intros P. unfold consistent_lP_lx_P in *.
        unfold is_constant in *. specialize (H' P).
        destruct H' as [x' [n' H']].
        unfold indicies_l2 in *. simpl in *. destruct P as [Rn].
        case_eq (beq_nat Rn Pn); intros Hbeq2; rewrite Hbeq2 in *.
          rewrite (beq_nat_true _ _ Hbeq2) in H'. rewrite beq_nat_comm in H'.
          rewrite Hbeq in H'. simpl in H'.

          simpl in *. exists x'. exists n'. assumption.

          simpl. exists (Var 1). exists 0. reflexivity.

          rewrite ind_FOv_ind_l2_pre_cons in *.
          rewrite ind_FOv_ind_l2_pre_cons in H2.
          simpl in *.
          destruct p as [Rn].
          specialize (H' (Pred Pn)).
          unfold consistent_lP_lx_P in H'. unfold indicies_l2 in H'. simpl in H'.
          rewrite (beq_nat_comm Pn Qm) in *. rewrite Hbeq in *.
          rewrite <- beq_nat_refl in *. simpl in *. unfold is_constant in H'.
          destruct H' as [u [un Hun]]. destruct un. discriminate.
          destruct un. discriminate. inversion Hun. reflexivity.

        apply (IHl l' (Pred Pn) x y).
        assert (cons (Pred Pn) (cons (Pred Pn) (cons a l)) =
                app (cons (Pred Pn) nil) (cons (Pred Pn) (cons a l))) as H2.
          reflexivity.
        assert (cons x (cons y (cons f l')) =
                app (cons x nil) (cons y (cons f l'))) as H3.
          reflexivity.
        rewrite H2 in H. rewrite H3 in H.
        apply consistent_lP_lx_cons_switch_gen in H.
        simpl in H.
        apply consistent_lP_lx_cons_rem in H. assumption.

        reflexivity.
Qed.

Lemma consistent_lP_lx_cons_rem_gen : forall lP lx P x,
  consistent_lP_lx (cons P lP) (cons x lx) ->
  consistent_lP_lx lP lx.
Proof.
  intros until 0. intros H.
  unfold consistent_lP_lx in *.
  unfold consistent_lP_lx_P in *.
  unfold indicies_l2 in *.
  intros Q. specialize (H Q).
  unfold is_constant in *.
  simpl in *. destruct P as [Pn]. destruct Q as [Qm].
  destruct H as [y [n H]].
  case_eq (beq_nat Qm Pn); intros Hbeq; rewrite Hbeq in *.
    simpl in *. destruct n. discriminate.
    inversion H as [[H1 H2]].
    rewrite ind_FOv_ind_l2_pre_cons in *.
    exists y. exists n. assumption.

    rewrite ind_FOv_ind_l2_pre_cons in *.
    exists y. exists n. assumption.
Qed.

Lemma consistent_lP_llv_cons_rem_gen : forall lP lx P x,
  consistent_lP_llv (cons P lP) (cons x lx) ->
  consistent_lP_llv lP lx.
Proof.
  intros until 0. intros H.
  unfold consistent_lP_llv in *.
  unfold consistent_lP_llv_P in *.
  unfold indicies_l2 in *.
  intros Q. specialize (H Q).
  unfold is_constant in *.
  simpl in *. destruct P as [Pn]. destruct Q as [Qm].
  destruct H as [y [n H]].
  case_eq (beq_nat Qm Pn); intros Hbeq; rewrite Hbeq in *.
    simpl in *. destruct n. discriminate.
    inversion H as [[H1 H2]].
    rewrite ind_llv_ind_l2_pre_cons in *.
    exists y. exists n. assumption.

    rewrite ind_llv_ind_l2_pre_cons in *.
    exists y. exists n. assumption.
Qed.

Lemma is_in_FO_var : forall l x,
  is_in_FOvar x l = is_in_var x l.
Proof.
  induction l; intros [xn].
    reflexivity.

    destruct a as [zn]. simpl. rewrite IHl.
    reflexivity.
Qed.

Lemma lem_try24 : forall l x (W : Set) (Iv : FOvariable -> W),
  is_in_FOvar x l = true ->
  CM_pa2_l Iv l (Iv x).
Proof.
  induction l; intros x W Iv H.
    simpl in *. discriminate.

    simpl in *. destruct x as [xn]. destruct a as [ym].
    case_eq (beq_nat xn ym); intros Hbeq; rewrite Hbeq in *.
      rewrite (beq_nat_true _ _ Hbeq).
      destruct l; [|left]; reflexivity.

      destruct l. discriminate.
      right. apply IHl. assumption.
Qed.

Lemma lem_try29 : forall l1 l2 x {W : Set} (w:W) Iv,
  ~ l1 = nil ->
  is_in_FOvar_l l1 l2 = true ->
  CM_pa2_l_gen Iv l1 x w ->
  CM_pa2_l_gen Iv l2 x w.
Proof.
  induction l1; intros l2 [xn] W w Iv Hnil Hin HCM.
    contradiction (Hnil eq_refl).

    simpl in *. case_eq (is_in_FOvar a l2); intros Hin2;
      rewrite Hin2 in *. 2 : discriminate.

      unfold CM_pa2_l_gen in *. simpl in *.
      destruct a as [ym]. rewrite <- is_in_FO_var.
      case_eq (beq_nat xn ym); intros Hbeq; rewrite Hbeq in *.
        rewrite (beq_nat_true _ _ Hbeq) in *.
        rewrite Hin2. assumption.

        case_eq (is_in_FOvar (Var xn) l2); intros Hin3.
          unfold pa_t. exact I.
        case_eq l1. intros Hnil2. rewrite Hnil2 in *. simpl in *.
          rewrite HCM. apply lem_try24. assumption.
        intros f l1' Hl1.
        case_eq (is_in_var (Var xn) l1); intros Hin4; rewrite Hin4 in *.
          specialize (IHl1 l2 (Var xn) W w Iv).
          rewrite Hin4 in *. rewrite <- is_in_FO_var in IHl1.
          rewrite Hin3 in IHl1. apply IHl1; try assumption.
            rewrite Hl1. intros H. discriminate.

          rewrite Hl1 in HCM. destruct HCM as [H|H].
            rewrite H. apply lem_try24. assumption.

          specialize (IHl1 l2 (Var xn) W w Iv).
          rewrite Hin4 in *. rewrite <- is_in_FO_var in IHl1.
          rewrite Hin3 in IHl1. apply IHl1; try assumption.
            rewrite Hl1. intros. discriminate.

            rewrite Hl1. assumption.
Qed.

Lemma lem_try18_pre_pre : forall l1 l2 a p f W Iv Ip Ir,
  ~ l1 = nil ->
  is_in_FOvar_l l1 l2 = true ->
  SOturnst W Iv (altered_Ip Ip (CM_pa2_l_gen Iv l1 f) p) Ir (predSO p a) ->
  SOturnst W Iv (altered_Ip Ip (CM_pa2_l_gen Iv l2 f) p) Ir (predSO p a).
Proof.
  intros l1 l2 [ym] [Pn] [xn] W Iv Ip Ir H1 H2 H3.
  simpl in *. rewrite <- beq_nat_refl in *.
  apply lem_try29 with (l1 := l1); assumption.
Qed.

Lemma lem_try18_pre : forall lx l1 l2 p f W Iv Ip Ir,
  ~ l1 = nil ->
  is_in_FOvar_l l1 l2 = true ->
  SOturnst W Iv (altered_Ip Ip (CM_pa2_l_gen Iv l1 f) p) Ir 
      (passing_conj (passing_predSO_l p lx)) ->
  SOturnst W Iv (altered_Ip Ip (CM_pa2_l_gen Iv l2 f) p) Ir 
      (passing_conj (passing_predSO_l p lx)).
Proof.
  induction lx; intros l1 l2 p f W Iv Ip Ir Hnil Hin SOt.
    simpl in *. reflexivity.

    simpl in *. case_eq (passing_predSO_l p lx).
      intros Hp. rewrite Hp in *.
      apply lem_try18_pre_pre with (l1 := l1); try assumption.

      intros beta lbeta Hlbeta. rewrite Hlbeta in *.
      rewrite <- Hlbeta in *. rewrite SOturnst_conjSO in *.
      apply conj. apply lem_try18_pre_pre with (l1 := l1); try assumption.
      apply SOt. 
      apply IHlx with (l1 := l1); try assumption. apply SOt.
Qed.

Lemma lem_try35 : forall l P Q,
~ P = Q ->
P_occurs_in_alpha (passing_conj (passing_predSO_l Q l)) P = false.
Proof.
  induction l; intros [Pn] [Qm] Hneq; unfold P_occurs_in_alpha in *.
    reflexivity.

    simpl.
    destruct l. simpl in *. destruct a as [Rn]. simpl.
      rewrite neq_beq_nat. reflexivity.
      assumption.

      simpl. destruct a as [Rn]. simpl. rewrite neq_beq_nat.
      apply (IHl (Pred Pn) (Pred Qm)).
      all : assumption.
Qed.

Fixpoint ex_nil_in_llv (llv : list (list FOvariable)) : bool :=
  match llv with
  | nil => false
  | cons nil llv => true
  | cons (cons v lv) llv' => ex_nil_in_llv llv'
  end.

Lemma lem_try33 : forall lP beta gamma,
  is_in_in_FOvar_ll (FOv_att_P_l gamma lP) (FOv_att_P_l (conjSO beta gamma) lP) = true.
Proof.
  induction lP; intros beta gamma.
    reflexivity.
  simpl in *. rewrite IHlP. 
  rewrite is_in_FOvar_l_app_r1. reflexivity.
  apply is_in_FOvar_l_refl.
Qed.

Lemma lem_try10 : forall l P,
  fun2 (passing_conj (passing_predSO_l P l)) P = l.
Proof.
  induction l; intros [Pn].
    reflexivity.

    simpl.
    case_eq l. intros Hnil. simpl. rewrite <- beq_nat_refl.
      reflexivity.
    intros x lx Hlx.
    rewrite <- Hlx.
    rewrite Hlx at 1. simpl.
    rewrite <- beq_nat_refl.
    rewrite IHl. reflexivity.
Qed.

Lemma lem_try40 : forall lP beta gamma,
  ex_nil_in_llv (FOv_att_P_l gamma lP) = false ->
  ex_nil_in_llv (FOv_att_P_l (conjSO beta gamma) lP) = false.
Proof.
  induction lP; intros beta gamma Hex.
    simpl in *. reflexivity.

    simpl in *.
    case_eq (fun2 gamma a). intros Hg. rewrite Hg in *.
      discriminate.

      intros x lx Hlx. rewrite <- Hlx.
      case_eq (app (fun2 beta a) (fun2 gamma a)).
        intros H.
        apply app_rnil_r in H. rewrite H in *. discriminate.

        intros y ly Hly.
        apply IHlP. rewrite Hlx in Hex. assumption.
Qed.