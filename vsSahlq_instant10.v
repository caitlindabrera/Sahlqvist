Add LoadPath "~/Nextcloud/Coq Files/Sahlqvist/Sahlq_Modules/vsSahlq local".

Require Export vsSahlq_instant9.

(* ------------------------------   *)

Lemma is_in_FOvar_cons_f : forall l x y,
  is_in_FOvar x (cons y l) = false ->
  is_in_FOvar x l = false /\ ~ x = y.
Proof.
  induction l; intros [xn] [ym] H.
    simpl in *. case_eq (beq_nat xn ym); intros Hbeq;
      rewrite Hbeq in *. discriminate.
    apply conj. reflexivity.
    apply beq_nat_false_FOv. assumption.

    simpl in *. destruct a as [zn].
    case_eq (beq_nat xn zn); intros Hbeq2;
      rewrite Hbeq2 in *.
      rewrite if_then_else_true in H. discriminate.

      case_eq (beq_nat xn ym); intros Hbeq3;
        rewrite Hbeq3 in *. discriminate.
        apply conj. assumption.
        apply beq_nat_false_FOv.
        assumption.
Qed.

Lemma kk16 : forall alpha x y z,
  ~ x = y ->
  ~ x = z ->
  free_FO alpha x =
  free_FO (rename_FOv alpha y z) x.
Proof.
  induction alpha; intros [xn] [ym] [zn] Hneq1 Hneq2.
    destruct p; destruct f as [un]. simpl.
    case_eq (beq_nat ym un); intros Hbeq.
      simpl. rewrite (neq_beq_nat_FOv xn zn).
      rewrite <- (beq_nat_true _ _ Hbeq).
      apply neq_beq_nat_FOv. all : try assumption.

      simpl. reflexivity.

    destruct f as [u1]; destruct f0 as [u2]. simpl.
    case_eq (beq_nat xn u1); intros Hbeq;
      case_eq (beq_nat ym u1); intros Hbeq2.
        rewrite <- (beq_nat_true _ _ Hbeq2) in Hbeq.
        rewrite (beq_nat_true _ _ Hbeq) in Hneq1.
        contradiction (Hneq1 eq_refl).

        case_eq (beq_nat ym u2); intros Hbeq3;
          simpl; rewrite Hbeq; reflexivity.

      case_eq (beq_nat xn u2); intros Hbeq3;
        case_eq (beq_nat ym u2); intros Hbeq4.
          rewrite <- (beq_nat_true _ _ Hbeq3) in Hbeq4.
          rewrite (beq_nat_true _ _ Hbeq4) in Hneq1.
          contradiction (Hneq1 eq_refl).

          simpl. rewrite neq_beq_nat_FOv. symmetry.
          all : try assumption.

          simpl. rewrite neq_beq_nat_FOv. reflexivity.
          assumption.

          simpl. rewrite Hbeq3. rewrite neq_beq_nat_FOv.
          reflexivity. assumption.

          case_eq (beq_nat ym u2); intros Hbeq3.
            simpl. rewrite Hbeq.
            rewrite <- (beq_nat_true _ _ Hbeq3).
            rewrite neq_beq_nat_FOv. 
            rewrite neq_beq_nat_FOv.  reflexivity.
            all : try assumption. simpl. rewrite Hbeq.
            reflexivity.

    destruct f as [u1]; destruct f0 as [u2]. simpl.
    case_eq (beq_nat xn u1); intros Hbeq;
      case_eq (beq_nat ym u1); intros Hbeq2.
        rewrite <- (beq_nat_true _ _ Hbeq2) in Hbeq.
        rewrite (beq_nat_true _ _ Hbeq) in Hneq1.
        contradiction (Hneq1 eq_refl).

        case_eq (beq_nat ym u2); intros Hbeq3;
          simpl; rewrite Hbeq; reflexivity.

      case_eq (beq_nat xn u2); intros Hbeq3;
        case_eq (beq_nat ym u2); intros Hbeq4.
          rewrite <- (beq_nat_true _ _ Hbeq3) in Hbeq4.
          rewrite (beq_nat_true _ _ Hbeq4) in Hneq1.
          contradiction (Hneq1 eq_refl).

          simpl. rewrite neq_beq_nat_FOv. symmetry.
          all : try assumption.

          simpl. rewrite neq_beq_nat_FOv. reflexivity.
          assumption.

          simpl. rewrite Hbeq3. rewrite neq_beq_nat_FOv.
          reflexivity. assumption.

          case_eq (beq_nat ym u2); intros Hbeq3.
            simpl. rewrite Hbeq.
            rewrite <- (beq_nat_true _ _ Hbeq3).
            rewrite neq_beq_nat_FOv. 
            rewrite neq_beq_nat_FOv.  reflexivity.
            all : try assumption. simpl. rewrite Hbeq.
            reflexivity.

      destruct f as [un]. simpl.
      case_eq (beq_nat xn un); intros Hbeq;
        case_eq (beq_nat un ym); intros Hbeq2.
          rewrite (beq_nat_true _ _ Hbeq) in Hneq1.
          rewrite (beq_nat_true _ _ Hbeq2) in Hneq1.
          contradiction (Hneq1 eq_refl).

          simpl. rewrite Hbeq. reflexivity.

        simpl. rewrite neq_beq_nat_FOv.
        apply (IHalpha (Var xn) (Var ym) (Var zn)).
          all : try assumption.

        simpl. rewrite Hbeq. 
        apply (IHalpha (Var xn) (Var ym) (Var zn)).
          all : try assumption.

      destruct f as [un]. simpl.
      case_eq (beq_nat xn un); intros Hbeq;
        case_eq (beq_nat un ym); intros Hbeq2.
          rewrite (beq_nat_true _ _ Hbeq) in Hneq1.
          rewrite (beq_nat_true _ _ Hbeq2) in Hneq1.
          contradiction (Hneq1 eq_refl).

          simpl. rewrite Hbeq. reflexivity.

        simpl. rewrite neq_beq_nat_FOv.
        apply (IHalpha (Var xn) (Var ym) (Var zn)).
          all : try assumption.

        simpl. rewrite Hbeq. 
        apply (IHalpha (Var xn) (Var ym) (Var zn)).
          all : try assumption.

      simpl in *. apply (IHalpha (Var xn) (Var ym) (Var zn)).
      all : try assumption.

    simpl. rewrite (IHalpha1 (Var xn) (Var ym) (Var zn)).
    rewrite (IHalpha2 (Var xn) (Var ym) (Var zn)).
    reflexivity. all : try assumption.

    simpl. rewrite (IHalpha1 (Var xn) (Var ym) (Var zn)).
    rewrite (IHalpha2 (Var xn) (Var ym) (Var zn)).
    reflexivity. all : try assumption.

    simpl. rewrite (IHalpha1 (Var xn) (Var ym) (Var zn)).
    rewrite (IHalpha2 (Var xn) (Var ym) (Var zn)).
    reflexivity. all : try assumption.

    simpl. apply (IHalpha (Var xn) (Var ym) (Var zn)).
    all : try assumption.

    simpl. apply (IHalpha (Var xn) (Var ym) (Var zn)).
    all : try assumption.
Qed.

Lemma rename_FOv_same : forall alpha x,
  rename_FOv alpha x x = alpha.
Proof.
  induction alpha; intros [xn].
    destruct f as [ym].
    simpl. case_eq (beq_nat xn ym); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq). all : try reflexivity.

    destruct f as [y1]; destruct f0 as [y2].
    simpl in *. case_eq (beq_nat xn y1);
      intros Hbeq.
      case_eq (beq_nat xn y2); intros Hbeq2;
        rewrite (beq_nat_true _ _ Hbeq) in *.
        rewrite (beq_nat_true _ _ Hbeq2). 
        all : try reflexivity.

      case_eq (beq_nat xn y2); intros Hbeq2.
        rewrite (beq_nat_true _ _ Hbeq2). 
        all : try reflexivity.


    destruct f as [y1]; destruct f0 as [y2].
    simpl in *. case_eq (beq_nat xn y1);
      intros Hbeq.
      case_eq (beq_nat xn y2); intros Hbeq2;
        rewrite (beq_nat_true _ _ Hbeq) in *.
        rewrite (beq_nat_true _ _ Hbeq2). 
        all : try reflexivity.

      case_eq (beq_nat xn y2); intros Hbeq2.
        rewrite (beq_nat_true _ _ Hbeq2). 
        all : try reflexivity.

    destruct f as [ym]. simpl in *.
    specialize (IHalpha (Var xn)). simpl in IHalpha.
    rewrite IHalpha.
    case_eq (beq_nat ym xn); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq). all : try reflexivity.

    destruct f as [ym]. simpl in *.
    specialize (IHalpha (Var xn)). simpl in IHalpha.
    rewrite IHalpha.
    case_eq (beq_nat ym xn); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq). all : try reflexivity.


    simpl in *. unfold rename_FOv in IHalpha.
    rewrite (IHalpha (Var xn)). reflexivity.

    simpl. unfold rename_FOv in *.
    rewrite (IHalpha1 (Var xn)). rewrite (IHalpha2 (Var xn)).
    reflexivity.

    simpl. unfold rename_FOv in *.
    rewrite (IHalpha1 (Var xn)). rewrite (IHalpha2 (Var xn)).
    reflexivity.

    simpl. unfold rename_FOv in *.
    rewrite (IHalpha1 (Var xn)). rewrite (IHalpha2 (Var xn)).
    reflexivity.

    destruct p. simpl. unfold rename_FOv in IHalpha.
    rewrite (IHalpha (Var xn)). reflexivity.

    destruct p. simpl. unfold rename_FOv in IHalpha.
    rewrite (IHalpha (Var xn)). reflexivity.

Qed.

Lemma kk18 : forall alpha x y z,
  ~ z = x ->
  ~ z = y ->
  free_FO alpha z = false ->
  free_FO (rename_FOv alpha x y) z = false.
Proof.
  induction alpha; intros [xn] [ym] [zn] H1 H2 Hf.
    destruct p as [Pn]; destruct f as [un].
    simpl. case_eq (beq_nat xn un); intros Hbeq;
      simpl in *. apply neq_beq_nat_FOv.
      all : try assumption.

    destruct f as [u1]; destruct f0 as [u2].
    simpl in *. case_eq (beq_nat xn u1); intros Hbeq;
      case_eq (beq_nat xn u2); intros Hbeq2;
        simpl.
        rewrite neq_beq_nat_FOv. reflexivity.
        assumption.

        rewrite (neq_beq_nat_FOv zn ym). 2 : assumption.
        case_eq (beq_nat zn u2); intros Hbeq3;
          rewrite Hbeq3 in *. rewrite if_then_else_true in Hf.
          discriminate. reflexivity.

        case_eq (beq_nat zn u1); intros Hbeq3;
          rewrite Hbeq3 in *. discriminate.
        apply neq_beq_nat_FOv. assumption.

        case_eq (beq_nat zn u1); intros Hbeq3;
          rewrite Hbeq3 in *. discriminate.
        assumption.

    destruct f as [u1]; destruct f0 as [u2].
    simpl in *. case_eq (beq_nat xn u1); intros Hbeq;
      case_eq (beq_nat xn u2); intros Hbeq2;
        simpl.
        rewrite neq_beq_nat_FOv. reflexivity.
        assumption.

        rewrite (neq_beq_nat_FOv zn ym). 2 : assumption.
        case_eq (beq_nat zn u2); intros Hbeq3;
          rewrite Hbeq3 in *. rewrite if_then_else_true in Hf.
          discriminate. reflexivity.

        case_eq (beq_nat zn u1); intros Hbeq3;
          rewrite Hbeq3 in *. discriminate.
        apply neq_beq_nat_FOv. assumption.

        case_eq (beq_nat zn u1); intros Hbeq3;
          rewrite Hbeq3 in *. discriminate.
        assumption.

      destruct f as [un].
      simpl in *. case_eq (beq_nat zn un); intros Hbeq;
        rewrite Hbeq in *;
        case_eq (beq_nat un xn); intros Hbeq2; simpl.
          rewrite (beq_nat_true _ _ Hbeq) in H1.
          rewrite (beq_nat_true _ _ Hbeq2) in H1.
          contradiction (H1 eq_refl).

          rewrite Hbeq. reflexivity.

          rewrite neq_beq_nat_FOv. 2 : assumption.
          apply (IHalpha (Var xn) (Var ym)); assumption.

          rewrite Hbeq. apply (IHalpha (Var xn) (Var ym));
          assumption.

      destruct f as [un].
      simpl in *. case_eq (beq_nat zn un); intros Hbeq;
        rewrite Hbeq in *;
        case_eq (beq_nat un xn); intros Hbeq2; simpl.
          rewrite (beq_nat_true _ _ Hbeq) in H1.
          rewrite (beq_nat_true _ _ Hbeq2) in H1.
          contradiction (H1 eq_refl).

          rewrite Hbeq. reflexivity.

          rewrite neq_beq_nat_FOv. 2 : assumption.
          apply (IHalpha (Var xn) (Var ym)); assumption.

          rewrite Hbeq. apply (IHalpha (Var xn) (Var ym));
          assumption.

      simpl in *. apply (IHalpha (Var xn) (Var ym));
          assumption.

      apply free_FO_conjSO in Hf. destruct Hf.
      simpl. rewrite (IHalpha1 (Var xn) (Var ym)).
      apply (IHalpha2 (Var xn) (Var ym)).
      all : try assumption.

      apply free_FO_conjSO in Hf. destruct Hf.
      simpl. rewrite (IHalpha1 (Var xn) (Var ym)).
      apply (IHalpha2 (Var xn) (Var ym)).
      all : try assumption.

      apply free_FO_conjSO in Hf. destruct Hf.
      simpl. rewrite (IHalpha1 (Var xn) (Var ym)).
      apply (IHalpha2 (Var xn) (Var ym)).
      all : try assumption.

      destruct p as [Pn]. simpl in *.
      apply (IHalpha (Var xn) (Var ym)); assumption.

      destruct p as [Pn]. simpl in *.
      apply (IHalpha (Var xn) (Var ym)); assumption.
Qed.

Lemma kk15  : forall alpha x y z,
  ~ x = y ->
  ~ x = z ->
  closed_except alpha x ->
  closed_except (rename_FOv alpha y z) x.
Proof.
  unfold closed_except.
  intros alpha x y z Hneq1 Hneq2 Hc. 
  destruct Hc as [Hc1 Hc2].
  apply conj.
    rewrite <- kk16; assumption.

    intros u Hneq3.
    destruct z as [zn]; destruct u as [un].
    case_eq (beq_nat zn un); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq).
      apply free_FO_rename_FOv2;
        (apply Hc2; assumption).

      destruct y as [ym].
      case_eq (beq_nat ym zn); intros Hbeq2.
        rewrite (beq_nat_true _ _ Hbeq2).
        rewrite rename_FOv_same. apply Hc2.
        assumption.

        case_eq (beq_nat ym un); intros Hbeq3.
          rewrite (beq_nat_true _ _ Hbeq3).
          apply free_FO_rename_FOv_same.
          apply beq_nat_false_FOv.
          rewrite <- (beq_nat_true _ _ Hbeq3).
          assumption.

          apply kk18.
            apply beq_nat_false_FOv.
            rewrite beq_nat_comm. assumption.

            apply beq_nat_false_FOv.
            rewrite beq_nat_comm. assumption.

          apply Hc2. assumption.
Qed.

Lemma kk19_1 : forall alpha x,
  closed_except alpha x ->
  x_occ_in_alpha alpha x = true.
Proof.
  unfold closed_except.
  intros alpha x [H1 H2].
  apply (contrapos_bool_ff _ _ (x_occ_in_free_FO _ _)).
  assumption.
Qed.

Lemma free_FO_x_occ : forall alpha x,
  free_FO alpha x = true ->
  x_occ_in_alpha alpha x = true.
Proof.
  intros. 
  apply (contrapos_bool_ff _ _ (x_occ_in_free_FO _ _)).
  assumption.
Qed.

Lemma kk19_2 : forall alpha xn,
  x_occ_in_alpha alpha (Var xn) = true ->
  Nat.leb xn (max_FOv alpha) = true.
Proof.
  induction alpha; intros xn Hocc.
    destruct p; destruct f. simpl in *.
    apply beq__leb.  assumption.

    destruct f as [y1]; destruct f0 as [y2].
    simpl in *. case_eq (beq_nat xn y1);
      intros H; rewrite H in Hocc.
      rewrite (beq_nat_true _ _ H).
      apply leb_max_suc3.
      apply leb_refl.

      rewrite (beq_nat_true _ _ Hocc).
      rewrite max_comm.
      apply leb_max_suc3.
      apply leb_refl.

    destruct f as [y1]; destruct f0 as [y2].
    simpl in *. case_eq (beq_nat xn y1);
      intros H; rewrite H in Hocc.
      rewrite (beq_nat_true _ _ H).
      apply leb_max_suc3.
      apply leb_refl.

      rewrite (beq_nat_true _ _ Hocc).
      rewrite max_comm.
      apply leb_max_suc3.
      apply leb_refl.

    destruct f as [ym]. simpl in *.
    case_eq (beq_nat xn ym); intros Hbeq;
      rewrite Hbeq in *.
      rewrite (beq_nat_true _ _ Hbeq).
      apply leb_max_suc3.
      apply leb_refl.

      rewrite max_comm.
      apply leb_max_suc3.
      apply IHalpha. assumption.

    destruct f as [ym]. simpl in *.
    case_eq (beq_nat xn ym); intros Hbeq;
      rewrite Hbeq in *.
      rewrite (beq_nat_true _ _ Hbeq).
      apply leb_max_suc3.
      apply leb_refl.

      rewrite max_comm.
      apply leb_max_suc3.
      apply IHalpha. assumption.

    simpl in *. apply IHalpha.
    assumption.

    simpl in *. case_eq (x_occ_in_alpha alpha1 (Var xn));
      intros Hocc1; rewrite Hocc1 in *.
      apply leb_max_suc3.
      apply IHalpha1. assumption.

      rewrite max_comm.
      apply leb_max_suc3.
      apply IHalpha2. assumption.

    simpl in *. case_eq (x_occ_in_alpha alpha1 (Var xn));
      intros Hocc1; rewrite Hocc1 in *.
      apply leb_max_suc3.
      apply IHalpha1. assumption.

      rewrite max_comm.
      apply leb_max_suc3.
      apply IHalpha2. assumption.

    simpl in *. case_eq (x_occ_in_alpha alpha1 (Var xn));
      intros Hocc1; rewrite Hocc1 in *.
      apply leb_max_suc3.
      apply IHalpha1. assumption.

      rewrite max_comm.
      apply leb_max_suc3.
      apply IHalpha2. assumption.

    simpl in *. apply IHalpha; assumption.

    simpl in *. apply IHalpha; assumption.
Qed.

Lemma kk19 : forall alpha xn,
  closed_except alpha (Var xn) ->
  Nat.leb (S (max_FOv alpha)) xn = false.
Proof.
  intros alpha xn H.
  rewrite one_suc. apply leb_notswitch.
  apply kk19_2. apply kk19_1. assumption.
Qed.

Lemma min_l_cons : forall l n,
  min_l (cons n l) = n \/
  min_l (cons n l) = (min_l l).
Proof.
  induction l; intros n.
    simpl. left. reflexivity.

    simpl. case_eq l.
      intros Hl. apply min_or.

      intros m l' Hl.
      rewrite <- Hl.
      pose proof (IHl n) as IHl1.
      pose proof (IHl a) as IHl2.
      simpl in *. rewrite Hl in *.
      rewrite <- Hl in *.
      destruct IHl2 as [IHl2' | IHl2'];
        rewrite IHl2'.
        apply min_or.

        apply IHl1.
Qed.

Lemma min_l_leb_cons2 : forall l n,
  min_l (cons n l) = min_l l ->
  Nat.leb (min_l l) n = true.
Proof.
  induction l; intros n Hmin.
    simpl in *. reflexivity.

    simpl in *. case_eq l.
      intros Hl. rewrite Hl in *.
      rewrite <- Hmin.
      apply leb_min_l.

      intros n' l' Hl.
      rewrite Hl in *.
      rewrite <- Hl in *.
      destruct (min_or a (min_l l)) as [H | H].
        rewrite H.
        rewrite min_comm in Hmin.
        apply leb_min in Hmin.
        rewrite H in Hmin.
        assumption.

        rewrite H in Hmin.
        rewrite H. apply IHl.
        assumption.
Qed.

Lemma min_l_leb_cons1 : forall ln n,
  ~ ln = nil ->
  min_l (cons n ln) = n ->
  Nat.leb n (min_l ln) = true.
Proof.
  induction ln; intros n Hnil Hmin.
    simpl in *. contradiction (Hnil eq_refl).

    simpl in *. case_eq ln.
      intros Hl. rewrite Hl in *.
      rewrite <- Hmin.
      rewrite min_comm.
      apply leb_min_l.

      intros n' l' Hl.
      rewrite Hl in *.
      rewrite <- Hl in *.
      destruct (min_or a (min_l ln)) as [H | H].
        rewrite H.
        apply leb_min in Hmin.
        rewrite H in Hmin.
        assumption.

        rewrite H in Hmin.
        rewrite H.
        destruct ln. simpl in *. discriminate.
        apply IHln. intros H'. discriminate.
        assumption.
Qed.

Lemma kk14'  : forall lx ln x alpha,
is_in_FOvar x lx = false ->
closed_except alpha x ->
Nat.leb (S (max_FOv alpha)) (min_l ln) = true ->
closed_except (newnew_pre alpha lx ln) x.
Proof.
  induction lx; intros ln [xn] alpha Hin Hc Hleb.
    simpl. assumption.

    simpl in *. destruct a as [ym].
    destruct ln. assumption.
    case_eq (beq_nat xn ym); intros Hbeq;
      rewrite Hbeq in *. discriminate.
    case_eq (min_l (cons n ln)).
      intros Hmn; rewrite Hmn in *. discriminate.
    intros m Hmn.
      case_eq (beq_nat xn n); intros Hbeq2.
        apply kk19 in Hc.

        rewrite (beq_nat_true _ _ Hbeq2) in *.
        rewrite Hmn in Hleb.
        destruct (min_l_cons ln n) as [H1 | H2].
          rewrite H1 in Hmn. rewrite Hmn in Hc.
          simpl in Hc. rewrite Hc in Hleb.
          discriminate.

          rewrite H2 in Hmn.
          apply min_l_leb_cons2 in H2.
          rewrite Hmn in H2.
          destruct n. simpl in *. discriminate.
          simpl in H2. simpl in Hc.
          rewrite (leb_trans _ _ _ Hleb H2)in Hc.
          discriminate.

        apply kk15; try assumption.
          apply beq_nat_false_FOv.
          assumption.

          apply beq_nat_false_FOv.
          assumption.
        case_eq ln.
          intros Hln. rewrite newnew_pre_nil.
          assumption.
        intros n' l' Hln. rewrite <- Hln.
        apply IHlx; try assumption.
          rewrite Hmn in Hleb.
          destruct (min_l_cons  ln n) as [H1 | H2].
            rewrite H1 in Hmn.
            pose proof H1 as H1'.
            apply min_l_leb_cons1 in H1.
            case_eq (min_l ln). intros Hmn2.
              rewrite Hmn2 in H1. rewrite Hmn in H1.
              simpl in *. discriminate.

              intros mn Hmn2. rewrite Hmn2 in H1.
              rewrite Hmn in H1. simpl in H1.
              apply leb_trans with (j := m);
              assumption.

              intros H. rewrite H in Hln. discriminate.

            rewrite H2 in Hmn. rewrite Hmn.
            assumption.
Qed.

Lemma x_occ_in_alpha_max_FOv_gen2 : forall beta n,
  x_occ_in_alpha beta (Var n) = true ->
  Nat.leb (S (max_FOv beta)) n = false.
Proof.
  induction beta; intros n Hocc.
    destruct p; destruct f as [m].
    rewrite one_suc.
    apply leb_notswitch.
    simpl in *.
    rewrite (beq_nat_true _ _ Hocc).
    apply leb_refl.

    destruct f as [m1]; destruct f0 as [m2].
    simpl in *. case_eq (beq_nat n m1);
      intros Hbeq1; rewrite Hbeq1 in *.
      rewrite (beq_nat_true _ _ Hbeq1).
      destruct m1. reflexivity.
      rewrite max_comm. apply leb_max_suc.

      rewrite (beq_nat_true _ _ Hocc).
      destruct m2. reflexivity.
      apply leb_max_suc.


    destruct f as [m1]; destruct f0 as [m2].
    simpl in *. case_eq (beq_nat n m1);
      intros Hbeq1; rewrite Hbeq1 in *.
      rewrite (beq_nat_true _ _ Hbeq1).
      destruct m1. reflexivity.
      rewrite max_comm. apply leb_max_suc.

      rewrite (beq_nat_true _ _ Hocc).
      destruct m2. reflexivity.
      apply leb_max_suc.

    destruct f as [m]. simpl in Hocc.
    case_eq (beq_nat n m); intros Hbeq;
      rewrite Hbeq in *. rewrite (beq_nat_true _ _ Hbeq).
      simpl. destruct m. reflexivity.
      rewrite max_comm. apply leb_max_suc.

      simpl max_FOv. rewrite PeanoNat.Nat.succ_max_distr.
      case_eq (Nat.leb (PeanoNat.Nat.max (S m) (S (max_FOv beta))) n);
        intros H. 2 : reflexivity.
      apply leb_max in H. destruct H as [H1 H2].
      rewrite IHbeta in H2. discriminate.
      assumption.

    destruct f as [m]. simpl in Hocc.
    case_eq (beq_nat n m); intros Hbeq;
      rewrite Hbeq in *. rewrite (beq_nat_true _ _ Hbeq).
      simpl. destruct m. reflexivity.
      rewrite max_comm. apply leb_max_suc.

      simpl max_FOv. rewrite PeanoNat.Nat.succ_max_distr.
      case_eq (Nat.leb (PeanoNat.Nat.max (S m) (S (max_FOv beta))) n);
        intros H. 2 : reflexivity.
      apply leb_max in H. destruct H as [H1 H2].
      rewrite IHbeta in H2. discriminate.
      assumption.

    simpl in *. apply IHbeta. assumption.

    simpl in Hocc. 
    simpl max_FOv.
    rewrite PeanoNat.Nat.succ_max_distr.
    case_eq (x_occ_in_alpha beta1 (Var n));
      intros Hocc1; rewrite Hocc1 in *.
      case_eq (Nat.leb (PeanoNat.Nat.max (S (max_FOv beta1)) (S (max_FOv beta2))) n);
        intros Hleb. 2 : reflexivity.
      apply leb_max in Hleb. destruct Hleb as [H1 H2].
      rewrite IHbeta1 in H1. discriminate. assumption.

      case_eq (Nat.leb (PeanoNat.Nat.max (S (max_FOv beta1)) (S (max_FOv beta2))) n);
        intros Hleb. 2 : reflexivity.
      apply leb_max in Hleb. destruct Hleb as [H1 H2].
      rewrite IHbeta2 in H2. discriminate. assumption.

    simpl in Hocc. 
    simpl max_FOv.
    rewrite PeanoNat.Nat.succ_max_distr.
    case_eq (x_occ_in_alpha beta1 (Var n));
      intros Hocc1; rewrite Hocc1 in *.
      case_eq (Nat.leb (PeanoNat.Nat.max (S (max_FOv beta1)) (S (max_FOv beta2))) n);
        intros Hleb. 2 : reflexivity.
      apply leb_max in Hleb. destruct Hleb as [H1 H2].
      rewrite IHbeta1 in H1. discriminate. assumption.

      case_eq (Nat.leb (PeanoNat.Nat.max (S (max_FOv beta1)) (S (max_FOv beta2))) n);
        intros Hleb. 2 : reflexivity.
      apply leb_max in Hleb. destruct Hleb as [H1 H2].
      rewrite IHbeta2 in H2. discriminate. assumption.

    simpl in Hocc. 
    simpl max_FOv.
    rewrite PeanoNat.Nat.succ_max_distr.
    case_eq (x_occ_in_alpha beta1 (Var n));
      intros Hocc1; rewrite Hocc1 in *.
      case_eq (Nat.leb (PeanoNat.Nat.max (S (max_FOv beta1)) (S (max_FOv beta2))) n);
        intros Hleb. 2 : reflexivity.
      apply leb_max in Hleb. destruct Hleb as [H1 H2].
      rewrite IHbeta1 in H1. discriminate. assumption.

      case_eq (Nat.leb (PeanoNat.Nat.max (S (max_FOv beta1)) (S (max_FOv beta2))) n);
        intros Hleb. 2 : reflexivity.
      apply leb_max in Hleb. destruct Hleb as [H1 H2].
      rewrite IHbeta2 in H2. discriminate. assumption.

    destruct p. simpl in *. apply IHbeta. assumption.

    destruct p. simpl in *. apply IHbeta. assumption.
Qed.

Lemma equiv_rename_FOv_free_FO_f : forall alpha y z,
  free_FO alpha y = false ->
  free_FO alpha z = false ->
  ~ y = z->
  x_occ_in_alpha alpha z = false ->
  forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir alpha <->
    SOturnst W Iv Ip Ir (rename_FOv alpha y z).
Proof.
  induction alpha; intros [xn] [ym] Hf1 Hf2 Hneq  Hocc W Iv Ip Ir.
    destruct p; destruct f as [zn].
    simpl in *. rewrite Hf1. simpl. apply bi_refl.

    destruct f as [z1]; destruct f0 as [z2].
    simpl in *. case_eq (beq_nat xn z1); intros Hbeq1;
      rewrite Hbeq1 in *. discriminate.
    case_eq (beq_nat ym z1); intros Hbeq2;
      rewrite Hbeq2 in *. discriminate.
    rewrite Hf1. simpl. apply bi_refl.

    destruct f as [z1]; destruct f0 as [z2].
    simpl in *. case_eq (beq_nat xn z1); intros Hbeq1;
      rewrite Hbeq1 in *. discriminate.
    case_eq (beq_nat ym z1); intros Hbeq2;
      rewrite Hbeq2 in *. discriminate.
    rewrite Hf1. simpl. apply bi_refl.

    destruct f as [un]. simpl in Hf1. simpl in Hf2.
    case_eq (beq_nat xn un); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq).
      simpl in Hocc. case_eq (beq_nat ym un);
        intros Hbeq4; rewrite Hbeq4 in *. discriminate.
      split; intros SOt.
        apply hopeful3_allFO; assumption.

        apply hopeful3_allFO in SOt; assumption.

      simpl rename_FOv. rewrite beq_nat_comm. rewrite Hbeq.
      rewrite Hbeq in Hf1.
      case_eq (beq_nat ym un); intros Hbeq2;
        rewrite Hbeq2 in *. simpl in Hocc.
        rewrite Hbeq2 in Hocc. discriminate.
      simpl in Hocc. rewrite Hbeq2 in Hocc.
      split; intros SOt d.
        apply (IHalpha (Var xn) (Var ym));
        try assumption. apply SOt.

        apply (IHalpha (Var xn) (Var ym));
        try assumption. apply SOt.

    destruct f as [un]. simpl in Hf1. simpl in Hf2.
    case_eq (beq_nat xn un); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq).
      simpl in Hocc. case_eq (beq_nat ym un);
        intros Hbeq4; rewrite Hbeq4 in *. discriminate.
      split; intros SOt.
        apply hopeful3_exFO; assumption.

        apply hopeful3_exFO in SOt; assumption.

      simpl rename_FOv. rewrite beq_nat_comm. rewrite Hbeq.
      rewrite Hbeq in Hf1.
      case_eq (beq_nat ym un); intros Hbeq2;
        rewrite Hbeq2 in *. simpl in Hocc.
        rewrite Hbeq2 in Hocc. discriminate.
      simpl in Hocc. rewrite Hbeq2 in Hocc.
      split; intros [d SOt]; exists d.
        apply (IHalpha (Var xn) (Var ym));
        assumption.

        apply (IHalpha (Var xn) (Var ym));
        assumption.

    simpl in *. split; intros SOt1 SOt2;
    apply SOt1; apply (IHalpha (Var xn) (Var ym)); assumption.

    apply free_FO_conjSO in Hf1.
    apply free_FO_conjSO in Hf2.
    apply x_occ_in_alpha_conjSO in Hocc.
    destruct Hf1. destruct Hf2. destruct Hocc.
    simpl. split; intros [H1' H2']; apply conj.
      apply (IHalpha1 (Var xn) (Var ym)); assumption.
      apply (IHalpha2 (Var xn) (Var ym)); assumption.

      apply (IHalpha1 (Var xn) (Var ym)); assumption.
      apply (IHalpha2 (Var xn) (Var ym)); assumption.

    apply free_FO_conjSO in Hf1.
    apply free_FO_conjSO in Hf2.
    apply x_occ_in_alpha_conjSO in Hocc.
    destruct Hf1. destruct Hf2. destruct Hocc.
    simpl. split; (intros [H1' | H2']; [left | right]).
      apply (IHalpha1 (Var xn) (Var ym)); assumption.
      apply (IHalpha2 (Var xn) (Var ym)); assumption.

      apply (IHalpha1 (Var xn) (Var ym)); assumption.
      apply (IHalpha2 (Var xn) (Var ym)); assumption.

    apply free_FO_conjSO in Hf1.
    apply free_FO_conjSO in Hf2.
    apply x_occ_in_alpha_conjSO in Hocc.
    destruct Hf1. destruct Hf2. destruct Hocc.
    simpl. split; intros H1' H2'. 
      apply (IHalpha2 (Var xn) (Var ym)); try assumption.
      apply H1'.
      apply (IHalpha1 (Var xn) (Var ym)); assumption.

      apply (IHalpha2 (Var xn) (Var ym)); try assumption.
      apply H1'.
      apply (IHalpha1 (Var xn) (Var ym)); assumption.

    destruct p. simpl in *.
    split; intros SOt pa.
      apply (IHalpha (Var xn) (Var ym)); try assumption.
      apply SOt.

      apply (IHalpha (Var xn) (Var ym)); try assumption.
      apply SOt.

    destruct p. simpl in *.
    split; intros [pa SOt]; exists pa;
      apply (IHalpha (Var xn) (Var ym)); assumption.
Qed.

Fixpoint decr_strict ln : bool :=
  match ln with
  | nil => true 
  | cons n ln' => if Nat.leb (S(max_l ln')) n then decr_strict ln' else false
  end.

Lemma decr_strict_defn : forall ln n,
  decr_strict (cons n ln) = 
  if Nat.leb (S(max_l ln)) n then decr_strict ln else false.
Proof.
  reflexivity.
Qed.

Lemma aa18 : forall alpha x n,
  Nat.leb (S (max_FOv alpha)) n = true ->
  (x_occ_in_alpha alpha x = true ->
    max_FOv (rename_FOv alpha x (Var n)) = n) /\
  (x_occ_in_alpha alpha x = false ->
    max_FOv (rename_FOv alpha x (Var n)) = max_FOv alpha).
Proof.
  induction alpha; intros [xn] n Hleb; apply conj; intros Hocc.
    destruct p; destruct f as [ym].
    simpl in *. rewrite Hocc. reflexivity.

    destruct p; destruct f as [ym].
    simpl in *. rewrite Hocc. reflexivity.

    destruct f as [z1]; destruct f0 as [z2]. simpl. simpl in Hocc.
    case_eq (beq_nat xn z1); intros Hbeq1; rewrite Hbeq1 in *.
      case_eq (beq_nat xn z2); intros Hbeq2. apply max_refl. 
      simpl max_FOv in Hleb.
      simpl. rewrite PeanoNat.Nat.succ_max_distr in Hleb.
      apply leb_max in Hleb. destruct Hleb as [H1 H2].
      apply leb_max_l. apply leb_suc_l. assumption.

      rewrite Hocc. simpl. simpl max_FOv in Hleb.
      simpl. rewrite PeanoNat.Nat.succ_max_distr in Hleb.
      apply leb_max in Hleb. destruct Hleb as [H1 H2].
      rewrite max_comm.
      apply leb_max_l. apply leb_suc_l. assumption.

    destruct f as [z1]; destruct f0 as [z2]. simpl. simpl in Hocc.
    case_eq (beq_nat xn z1); intros Hbeq1; rewrite Hbeq1 in *.
      discriminate. rewrite Hocc. simpl. reflexivity.

    destruct f as [z1]; destruct f0 as [z2]. simpl. simpl in Hocc.
    case_eq (beq_nat xn z1); intros Hbeq1; rewrite Hbeq1 in *.
      case_eq (beq_nat xn z2); intros Hbeq2. apply max_refl. 
      simpl max_FOv in Hleb.
      simpl. rewrite PeanoNat.Nat.succ_max_distr in Hleb.
      apply leb_max in Hleb. destruct Hleb as [H1 H2].
      apply leb_max_l. apply leb_suc_l. assumption.

      rewrite Hocc. simpl. simpl max_FOv in Hleb.
      simpl. rewrite PeanoNat.Nat.succ_max_distr in Hleb.
      apply leb_max in Hleb. destruct Hleb as [H1 H2].
      rewrite max_comm.
      apply leb_max_l. apply leb_suc_l. assumption.

    destruct f as [z1]; destruct f0 as [z2]. simpl. simpl in Hocc.
    case_eq (beq_nat xn z1); intros Hbeq1; rewrite Hbeq1 in *.
      discriminate. rewrite Hocc. simpl. reflexivity.

    destruct f as [zn]. simpl. simpl in Hocc. rewrite beq_nat_comm in Hocc.
    case_eq (beq_nat zn xn); intros Hbeq; rewrite Hbeq in *.
 simpl.
      destruct (IHalpha (Var xn) n) as [IH1 IH2].
      simpl max_FOv in Hleb. rewrite PeanoNat.Nat.succ_max_distr in Hleb;
        apply leb_max in Hleb. apply Hleb.
      case_eq (x_occ_in_alpha alpha (Var xn));
        intros Hocc2; unfold rename_FOv in *.
        rewrite (IH1). apply max_refl. assumption.

        rewrite IH2. simpl max_FOv in Hleb. 
        rewrite PeanoNat.Nat.succ_max_distr in Hleb;
        apply leb_max in Hleb. apply leb_max_l.
        apply leb_suc_l. apply Hleb. assumption.

        simpl. unfold rename_FOv in IHalpha.
        destruct (IHalpha (Var xn) n) as [IH1 IH2].
          simpl max_FOv in Hleb; rewrite PeanoNat.Nat.succ_max_distr in Hleb;
          apply leb_max in Hleb. apply Hleb.

          rewrite IH1. rewrite max_comm. apply leb_max_l.
          apply leb_suc_l.
          simpl max_FOv in Hleb; rewrite PeanoNat.Nat.succ_max_distr in Hleb;
          apply leb_max in Hleb. apply Hleb. assumption.

        simpl in Hocc. destruct f as [ym]. case_eq (beq_nat xn ym);
          intros Hbeq; rewrite Hbeq in *. discriminate.
        simpl. rewrite beq_nat_comm. rewrite Hbeq. unfold rename_FOv in *.
        simpl. destruct (IHalpha (Var xn) n) as [IH1 IH2].
          simpl max_FOv in Hleb; rewrite PeanoNat.Nat.succ_max_distr in Hleb;
          apply leb_max in Hleb. apply Hleb.

          rewrite IH2. reflexivity. assumption.

    destruct f as [zn]. simpl. simpl in Hocc. rewrite beq_nat_comm in Hocc.
    case_eq (beq_nat zn xn); intros Hbeq; rewrite Hbeq in *.
 simpl.

      destruct (IHalpha (Var xn) n) as [IH1 IH2].
      simpl max_FOv in Hleb. rewrite PeanoNat.Nat.succ_max_distr in Hleb;
        apply leb_max in Hleb. apply Hleb.
      case_eq (x_occ_in_alpha alpha (Var xn));
        intros Hocc2; unfold rename_FOv in *.
        rewrite (IH1). apply max_refl. assumption.

        rewrite IH2. simpl max_FOv in Hleb. 
        rewrite PeanoNat.Nat.succ_max_distr in Hleb;
        apply leb_max in Hleb. apply leb_max_l.
        apply leb_suc_l. apply Hleb. assumption.

        simpl. unfold rename_FOv in IHalpha.
        destruct (IHalpha (Var xn) n) as [IH1 IH2].
          simpl max_FOv in Hleb; rewrite PeanoNat.Nat.succ_max_distr in Hleb;
          apply leb_max in Hleb. apply Hleb.

          rewrite IH1. rewrite max_comm. apply leb_max_l.
          apply leb_suc_l.
          simpl max_FOv in Hleb; rewrite PeanoNat.Nat.succ_max_distr in Hleb;
          apply leb_max in Hleb. apply Hleb. assumption.

        simpl in Hocc. destruct f as [ym]. case_eq (beq_nat xn ym);
          intros Hbeq; rewrite Hbeq in *. discriminate.
        simpl. rewrite beq_nat_comm. rewrite Hbeq. unfold rename_FOv in *.
        simpl. destruct (IHalpha (Var xn) n) as [IH1 IH2].
          simpl max_FOv in Hleb; rewrite PeanoNat.Nat.succ_max_distr in Hleb;
          apply leb_max in Hleb. apply Hleb.

          rewrite IH2. reflexivity. assumption.

    simpl in *. unfold rename_FOv in IHalpha. 
    apply (IHalpha (Var xn)); assumption.

    simpl in *. unfold rename_FOv in IHalpha. 
    apply (IHalpha (Var xn)); assumption.

    rewrite rename_FOv_conjSO. simpl max_FOv.
    simpl max_FOv in Hleb. simpl in Hocc. unfold rename_FOv in *.
    simpl max_FOv in Hleb; rewrite PeanoNat.Nat.succ_max_distr in Hleb;
    apply leb_max in Hleb.
    destruct (IHalpha1 (Var xn) n) as [IH1a IH1b]. apply Hleb.
    destruct (IHalpha2 (Var xn) n) as [IH2a IH2b]. apply Hleb.
    case_eq (x_occ_in_alpha alpha1 (Var xn)); intros Hocc1;
      rewrite Hocc1 in Hocc.
    rewrite IH1a.
      case_eq (x_occ_in_alpha alpha2 (Var xn)); intros Hocc2.
        rewrite IH2a. apply max_refl. assumption.

        rewrite IH2b. apply leb_max_l. apply leb_suc_l.
        apply Hleb. all : try assumption.

      rewrite IH1b. rewrite IH2a. rewrite max_comm. 
      apply leb_max_l. apply leb_suc_l. apply Hleb.
      all : try assumption.

    apply x_occ_in_alpha_conjSO in Hocc.
    simpl.  
    simpl max_FOv in Hleb. simpl in Hocc. unfold rename_FOv in *.
    simpl max_FOv in Hleb; rewrite PeanoNat.Nat.succ_max_distr in Hleb;
    apply leb_max in Hleb.
    destruct (IHalpha1 (Var xn) n) as [IH1a IH1b]. apply Hleb.
    destruct (IHalpha2 (Var xn) n) as [IH2a IH2b]. apply Hleb.
    rewrite IH1b. rewrite IH2b. reflexivity. all : try apply Hocc.

    rewrite rename_FOv_disjSO. simpl max_FOv.
    simpl max_FOv in Hleb. simpl in Hocc. unfold rename_FOv in *.
    simpl max_FOv in Hleb; rewrite PeanoNat.Nat.succ_max_distr in Hleb;
    apply leb_max in Hleb.
    destruct (IHalpha1 (Var xn) n) as [IH1a IH1b]. apply Hleb.
    destruct (IHalpha2 (Var xn) n) as [IH2a IH2b]. apply Hleb.
    case_eq (x_occ_in_alpha alpha1 (Var xn)); intros Hocc1;
      rewrite Hocc1 in Hocc.
    rewrite IH1a.
      case_eq (x_occ_in_alpha alpha2 (Var xn)); intros Hocc2.
        rewrite IH2a. apply max_refl. assumption.

        rewrite IH2b. apply leb_max_l. apply leb_suc_l.
        apply Hleb. all : try assumption.

      rewrite IH1b. rewrite IH2a. rewrite max_comm. 
      apply leb_max_l. apply leb_suc_l. apply Hleb.
      all : try assumption.

    apply x_occ_in_alpha_conjSO in Hocc.
    simpl.  
    simpl max_FOv in Hleb. simpl in Hocc. unfold rename_FOv in *.
    simpl max_FOv in Hleb; rewrite PeanoNat.Nat.succ_max_distr in Hleb;
    apply leb_max in Hleb.
    destruct (IHalpha1 (Var xn) n) as [IH1a IH1b]. apply Hleb.
    destruct (IHalpha2 (Var xn) n) as [IH2a IH2b]. apply Hleb.
    rewrite IH1b. rewrite IH2b. reflexivity. all : try apply Hocc.

    rewrite rename_FOv_implSO. simpl max_FOv.
    simpl max_FOv in Hleb. simpl in Hocc. unfold rename_FOv in *.
    simpl max_FOv in Hleb; rewrite PeanoNat.Nat.succ_max_distr in Hleb;
    apply leb_max in Hleb.
    destruct (IHalpha1 (Var xn) n) as [IH1a IH1b]. apply Hleb.
    destruct (IHalpha2 (Var xn) n) as [IH2a IH2b]. apply Hleb.
    case_eq (x_occ_in_alpha alpha1 (Var xn)); intros Hocc1;
      rewrite Hocc1 in Hocc.
    rewrite IH1a.
      case_eq (x_occ_in_alpha alpha2 (Var xn)); intros Hocc2.
        rewrite IH2a. apply max_refl. assumption.

        rewrite IH2b. apply leb_max_l. apply leb_suc_l.
        apply Hleb. all : try assumption.

      rewrite IH1b. rewrite IH2a. rewrite max_comm. 
      apply leb_max_l. apply leb_suc_l. apply Hleb.
      all : try assumption.

    apply x_occ_in_alpha_conjSO in Hocc.
    simpl.  
    simpl max_FOv in Hleb. simpl in Hocc. unfold rename_FOv in *.
    simpl max_FOv in Hleb; rewrite PeanoNat.Nat.succ_max_distr in Hleb;
    apply leb_max in Hleb.
    destruct (IHalpha1 (Var xn) n) as [IH1a IH1b]. apply Hleb.
    destruct (IHalpha2 (Var xn) n) as [IH2a IH2b]. apply Hleb.
    rewrite IH1b. rewrite IH2b. reflexivity. all : try apply Hocc.

    destruct p. simpl. simpl in Hocc. unfold rename_FOv in *.
    simpl max_FOv in Hleb.
    destruct (IHalpha (Var xn) n Hleb) as [IH1 IH2].
    apply IH1. assumption.

    destruct p. simpl. simpl in Hocc. unfold rename_FOv in *.
    simpl max_FOv in Hleb.
    destruct (IHalpha (Var xn) n Hleb) as [IH1 IH2].
    apply IH2. assumption.

    destruct p. simpl. simpl in Hocc. unfold rename_FOv in *.
    simpl max_FOv in Hleb.
    destruct (IHalpha (Var xn) n Hleb) as [IH1 IH2].
    apply IH1. assumption.

    destruct p. simpl. simpl in Hocc. unfold rename_FOv in *.
    simpl max_FOv in Hleb.
    destruct (IHalpha (Var xn) n Hleb) as [IH1 IH2].
    apply IH2. assumption.
Qed.

Lemma aa18_t : forall alpha x n,
  Nat.leb (S (max_FOv alpha)) n = true ->
  x_occ_in_alpha alpha x = true ->
    max_FOv (rename_FOv alpha x (Var n)) = n.
Proof.
  intros. apply aa18; assumption.
Qed.

Lemma min_l_switch : forall l n m,
  min_l (cons n (cons m l)) =
  min_l (cons m (cons n l)).
Proof.
  intros. simpl. destruct l.
    apply min_comm.

    rewrite PeanoNat.Nat.min_assoc.
    rewrite (min_comm n m).
    rewrite PeanoNat.Nat.min_assoc. reflexivity.
Qed.

Lemma min_l_cons2 : forall l n,
  ~ l = nil ->
  min_l (cons n l) = min n (min_l l).
Proof.
  intros l n Heq.
  simpl. destruct l. contradiction (Heq eq_refl).
  simpl. reflexivity.
Qed.

Lemma aa2 : forall ln n,
Nat.leb (min_l (cons n ln)) n = true.
Proof.
  induction ln; intros n.
    simpl. apply leb_refl.

    rewrite min_l_switch. remember (cons n ln) as t.
    specialize (IHln n). rewrite <- Heqt in IHln.
    simpl. rewrite Heqt. rewrite <- Heqt.
    rewrite min_comm.
    apply leb_min_l2. assumption.
Qed.

Lemma leb_max_FOv_rename_FOv : forall alpha x n,
  Nat.leb (max_FOv (rename_FOv alpha x (Var n)))
          (max (max_FOv alpha) n) = true.
Proof.
  intros alpha x n.
  case_eq (x_occ_in_alpha alpha x); intros Hocc.
    apply max_FOv_rename_FOv2. assumption.

    rewrite rename_FOv_not_occ. 2 : assumption.
    apply leb_max_suc3.
    apply leb_refl.
Qed.

Lemma aa3' : forall lx ln alpha,
  length lx = length ln ->
  Nat.leb (S (max_FOv alpha)) (min_l ln) = true ->
  Nat.leb (max_FOv (newnew_pre alpha lx ln))
          (max (max_FOv alpha) (max_l ln)) = true.
Proof.
  induction lx; intros ln alpha Hl Hleb.
    simpl in *. symmetry in Hl.
    apply List.length_zero_iff_nil in Hl. rewrite Hl in *.
    simpl in *. discriminate.

    simpl. destruct ln. discriminate.
    simpl. case_eq ln. intros Hln;
      rewrite Hln in *.
      rewrite newnew_pre_nil.
      rewrite PeanoNat.Nat.max_0_r.
      case_eq (x_occ_in_alpha alpha a);
        intros Hocc.
        rewrite aa18_t; try assumption.
        rewrite max_comm.
        apply leb_max_suc3. apply leb_refl.

        rewrite rename_FOv_not_occ.
        rewrite max_comm.
        apply leb_max_suc3.
        simpl in Hleb. destruct n.
          discriminate.
        apply leb_suc_r. all : try assumption.

      intros m lm Hln. rewrite <- Hln.
      case_eq (x_occ_in_alpha (newnew_pre alpha lx ln) a);
        intros H.
        apply (leb_trans _  
          (max (max_FOv (newnew_pre alpha lx ln)) n)).

          apply leb_max_FOv_rename_FOv.

        rewrite (max_comm n _).
        rewrite PeanoNat.Nat.max_assoc.
        apply leb_max_max. apply IHlx.
          simpl in Hl. inversion Hl. reflexivity.

          simpl min_l in Hleb. rewrite Hln in Hleb.
          rewrite <- Hln in Hleb.
          apply leb_min_r in Hleb.
          apply Hleb.

        rewrite rename_FOv_not_occ.
        rewrite max_comm.
        apply leb_max_suc3.
        destruct n. rewrite Hln in Hleb.
          simpl in *. discriminate.
        apply (leb_trans _  (Nat.max (max_FOv alpha) (max_l ln))).
        apply IHlx; try assumption.
          simpl in Hl. inversion Hl. reflexivity.
          rewrite Hln in *.
          rewrite min_l_cons2 in Hleb.
          apply leb_min_r in Hleb.
          apply Hleb.
            intros. discriminate.
  
            apply leb_max_max.
 rewrite <- leb_defn_suc.
            
            apply (leb_trans _ (min_l (S n :: ln))).
              assumption.
            apply (leb_trans _ (S n)). apply aa2.
            apply leb_suc_r. apply leb_refl.

        assumption.
Qed.

Lemma leb_min__max_l : forall l,
  Nat.leb (min_l l) (max_l l) = true.
Proof.
  induction l.
    reflexivity.

    simpl. destruct l. simpl.
      rewrite PeanoNat.Nat.max_0_r. apply leb_refl.

      apply leb_min_max. assumption.
Qed.

Lemma aa : forall ln lx alpha n,
  length lx = length ln ->
  Nat.leb (S (max_FOv alpha)) (min_l ln) = true ->
  Nat.leb (S (max_l ln)) n = true ->
  Nat.leb (S(max_FOv (newnew_pre alpha lx ln))) n = true.
Proof.
  intros ln lx alpha n Hl H1 H2.
  apply (leb_trans _ ((S (Nat.max (max_FOv alpha) (max_l ln))))).
    apply aa3'; assumption.

  destruct (max_or (max_FOv alpha) (max_l ln)) as [H | H];
    rewrite H. all : try assumption.
    pose proof (leb_trans _ _ _ H1 (leb_min__max_l _)) as H'.
    apply leb_suc_r in H'.
    apply (leb_trans _ _ _ H' H2).
Qed.

Lemma aa10' : forall {A B : Type}   (lx : list A) (ln : list B),
  Nat.leb (length lx) (length ln) = true ->
  exists ln1 ln2,
    length lx = length ln1 /\
    ln = app ln1 ln2.
Proof.
  intros A B; induction lx; intros ln Hleb.
    simpl in *.
    exists nil. exists ln.
    apply conj; reflexivity.

    simpl length in Hleb.
    destruct ln. simpl in *. discriminate.
    simpl in Hleb.
    destruct (IHlx ln Hleb) as [ln1 [ln2 [H1 H2]]].
    exists (cons b ln1). exists ln2.
    simpl. apply conj. rewrite H1. reflexivity.
    rewrite H2. reflexivity.
Qed.

Lemma aa11' : forall {A B : Type}  (ln : list B) (lx : list A),
  (exists ln1 ln2,
    length lx = length ln1 /\
    ln = app ln1 ln2) \/
  (exists lx1 lx2,
    length ln = length lx1 /\
    lx = app lx1 lx2).
Proof.
  intros A B ln lx.
  destruct (leb_or (length lx) (length ln));
    [left | right]; apply aa10'; assumption.
Qed.

Lemma newnew_pre_extra_n : forall lx l1 l2 alpha,
  length lx = length l1 ->
  newnew_pre alpha lx (app l1 l2) = newnew_pre alpha lx l1.
Proof.
  induction lx; intros l1 l2 alpha Heq.
    reflexivity.

    destruct l1. simpl in *. discriminate.
    simpl. rewrite IHlx. reflexivity.
    simpl in *. inversion Heq. reflexivity.
Qed.

Lemma newnew_pre_extra_x : forall ln l1 l2 alpha,
  length ln = length l1 ->
  newnew_pre alpha (app l1 l2) ln = newnew_pre alpha l1 ln.
Proof.
  induction ln; intros l1 l2 alpha Heq.
    do 2 rewrite newnew_pre_nil. reflexivity.

    destruct l1. simpl in *. discriminate.
    simpl. rewrite IHln. reflexivity.
    simpl in *. inversion Heq. reflexivity.
Qed.

Lemma aa14 : forall alpha x y,
  closed_except alpha x ->
  ~ x = y ->
  free_FO alpha y = false.
Proof.
  intros alpha x y Hc Hneq.
  unfold closed_except in Hc.
  apply Hc.
  assumption.
Qed.

Lemma is_in_FOvar_app_l : forall l1 l2 x,
  is_in_FOvar x (app l1 l2) = false ->
  is_in_FOvar x l1 = false.
Proof.
  induction l1; intros l2 x H.
    reflexivity.

    simpl in *.
    destruct x as [xn]; destruct a as [ym]. 
    simpl in H.
    case_eq (beq_nat xn ym); intros Hbeq;
      rewrite Hbeq in *. discriminate.
    apply (IHl1 l2). assumption.
Qed.

Lemma min_l_app : forall l1 l2,
  ~ l1 = nil ->
  ~ l2 = nil ->
  min_l (app l1 l2) =
  min (min_l l1) (min_l l2).
Proof.
  induction l1; intros l2 Hneq1 Hneq2.
    contradiction (Hneq1 eq_refl).

    simpl app.
    case_eq l1. intros Hl. simpl.
      destruct l2. contradiction (Hneq2 eq_refl).
      reflexivity.

    intros m l1' Hl1; rewrite <- Hl1.
    assert (~ l1 = nil) as H. 
      intros H2. rewrite H2 in Hl1. discriminate.
    rewrite min_l_cons2.
    rewrite min_l_cons2.
    rewrite IHl1.
    rewrite PeanoNat.Nat.min_assoc.
    reflexivity.
    all : try assumption.
    rewrite Hl1. intros. discriminate.
Qed.


Lemma max_l_app : forall l1 l2,
  max_l (app l1 l2) = max (max_l l1) (max_l l2).
Proof.
  induction l1; intros l2.
    reflexivity.

    simpl. rewrite IHl1.
    rewrite PeanoNat.Nat.max_assoc.
    reflexivity.
Qed.

Lemma aa15 : forall n l1 l2,
  ~ l1 = nil ->
  Nat.leb n (min_l (app l1 l2)) = true ->
  Nat.leb n (min_l l1) = true.
Proof.
  intros n l1 l2 Hneq H.
  destruct l1. contradiction (Hneq eq_refl).
  destruct l2. rewrite List.app_nil_r in H. assumption.
  rewrite min_l_app in H.
  apply leb_min_r in H.
  apply H.
    intros. discriminate.

    intros. discriminate.
Qed.

Lemma aa16 : forall l1 l2 n,
  Nat.leb (S (max_l (app l1 l2))) n = true ->
  Nat.leb (S (max_l l1)) n = true.
Proof.
  intros l1 l2 n H.
  rewrite max_l_app in H.
  rewrite PeanoNat.Nat.succ_max_distr in H.
  apply leb_max in H.
  apply H.
Qed.

Lemma aa17 : forall alpha ln n x,
  closed_except alpha x ->
  Nat.leb (S (max_FOv alpha)) (min_l ln) = true ->
  Nat.leb (S (max_l ln)) n = true ->
  free_FO alpha (Var n) = false.
Proof.
  intros alpha ln n x Hc H1 H2.
  apply x_occ_in_free_FO.
  apply (contrapos_bool_tf _ _ (x_occ_in_alpha_max_FOv_gen2 _ _ )).
  apply (leb_trans _ (min_l ln)). assumption.
  apply (leb_trans _  (max_l ln)).
  apply leb_min__max_l.
  apply leb_suc_l. assumption.
Qed.

Lemma kk10 : forall lx ln alpha x,
  closed_except alpha x ->
  is_in_FOvar x lx = false ->
  Nat.leb (S (max_FOv alpha)) (min_l ln) = true ->
  decr_strict ln = true ->
  forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir alpha <->
  SOturnst W Iv Ip Ir (newnew_pre alpha lx ln).
Proof.
  induction lx; intros ln alpha x Hc Hin Hleb Hd W Iv Ip Ir.
    simpl. apply bi_refl.

    simpl. destruct ln. apply bi_refl.
    apply is_in_FOvar_cons_f in Hin.
    destruct Hin.
    pose proof (neq_comm _ _ H0) as H0'.
    case_eq ln. intros Hln. rewrite newnew_pre_nil.
      rewrite Hln in Hleb. simpl min_l in Hleb.
      unfold closed_except in Hc.
      destruct Hc as [Hc1 Hc2].
      destruct a as [an]. case_eq (beq_nat an n); intros Hbeq0.
        rewrite (beq_nat_true _ _ Hbeq0).
        rewrite rename_FOv_same. apply bi_refl.
      apply equiv_rename_FOv_free_FO_f;
        try apply Hc2. apply not_eq_sym. assumption.

        intros Heq. rewrite Heq in Hc1.
        apply free_FO_x_occ in Hc1.
        apply x_occ_in_alpha_max_FOv_gen2 in Hc1.
        rewrite Hc1 in Hleb.
        discriminate.

        apply beq_nat_false_FOv. assumption.

        pose proof (x_occ_in_alpha_max_FOv_gen2 alpha n) as HH.
        apply (contrapos_bool_tf _ _ HH). assumption.

      intros m ln' Hln. rewrite <- Hln.
      assert (Nat.leb (S (max_FOv alpha)) (min_l ln) = true) as Hleb2.
        destruct (min_l_cons ln n) as [H2 | H2].
          rewrite H2 in Hleb.
          apply min_l_leb_cons1 in H2.
          apply (leb_trans _ _ _ Hleb H2).
            rewrite Hln. intros. discriminate.

          rewrite H2 in Hleb. assumption.

    split; intros SOt.
      rewrite decr_strict_defn in Hd.
      case_eq (Nat.leb (S(max_l ln)) n);
      intros Hleb3; rewrite Hleb3 in *. 2 : discriminate.

      destruct a as [an]. case_eq (beq_nat an n); intros Hbeq.
        rewrite (beq_nat_true _ _ Hbeq). rewrite rename_FOv_same.
        apply (IHlx ln alpha x Hc H); try assumption.

destruct (aa11' ln lx) as [[ln1 [ln2 [H1 H2]]] | [lx1 [lx2 [H1 H2]]]].
rewrite H2. rewrite newnew_pre_extra_n. 2 : assumption.

      case_eq lx. intros Hlx. simpl. destruct x as [xn].

pose proof  (equiv_rename_FOv_free_FO_f alpha (Var an) (Var n)).
unfold rename_FOv in H3.
        apply H3; try assumption.
        apply aa14 with (x := (Var xn));
        try assumption.
          apply (aa17 _ ln n (Var xn)); assumption.

          apply beq_nat_false_FOv. assumption.

          apply (contrapos_bool_tf _ _ (x_occ_in_alpha_max_FOv_gen2 _ _ )).
          apply (leb_trans _ (min_l ln)). assumption.
          apply (leb_trans _ (max_l ln)). apply leb_min__max_l.
          apply leb_suc_l. assumption.

        intros y lx' Hlx. rewrite <- Hlx.
      assert (x_occ_in_alpha (newnew_pre alpha lx ln1) (Var n) = false) as
        Has. destruct n. simpl in *. discriminate.
        apply x_occ_in_alpha_max_FOv_gen.
        rewrite <- leb_defn_suc.
pose proof aa. apply aa; try assumption.
          apply (aa15 _ _ ln2).
            intros H'. rewrite H' in H1. simpl in H1.
            rewrite Hlx in H1. discriminate.
          rewrite <- H2. assumption.

          apply (aa16 ln1 ln2). rewrite <- H2. assumption.

      apply equiv_rename_FOv_free_FO_f.
      pose proof (kk14' lx ln1) as H3.
      apply aa14 with (x := x).
      apply H3; try assumption.

          apply (aa15 _ _ ln2). 
            intros H'. rewrite H' in H1. simpl in H1.
            rewrite Hlx in H1. discriminate.
          rewrite <- H2. assumption.

        intros H'; rewrite H' in *.
        contradiction (H0 eq_refl).

      apply x_occ_in_free_FO. assumption.

      apply beq_nat_false_FOv. assumption.

      assumption. rewrite <- (newnew_pre_extra_n lx ln1 ln2).
      rewrite <- H2. apply (IHlx ln alpha x).
        all: try assumption. 
(* -- *)

rewrite H2. rewrite newnew_pre_extra_x. 2 : assumption.

      assert (x_occ_in_alpha (newnew_pre alpha lx1 ln) (Var n) = false) as
        Has. destruct n. simpl in *. discriminate.
        apply x_occ_in_alpha_max_FOv_gen.
        rewrite <- leb_defn_suc. apply aa; try assumption.
          symmetry. assumption.
      

      apply equiv_rename_FOv_free_FO_f.
      pose proof (kk14' lx1 ln) as H3.
      apply aa14 with (x := x).
      apply H3; try assumption.

        apply (is_in_FOvar_app_l _ lx2). rewrite <- H2.
        assumption.

        intros H'; rewrite H' in *.
        contradiction (H0 eq_refl).

      apply x_occ_in_free_FO. assumption.

      apply beq_nat_false_FOv. assumption.

      assumption. rewrite <- (newnew_pre_extra_x _ _ lx2).
      rewrite <- H2. apply (IHlx ln alpha x).
        all: try assumption.

(* -- *)

      rewrite decr_strict_defn in Hd.
      case_eq (Nat.leb (S(max_l ln)) n);
      intros Hleb3; rewrite Hleb3 in *. 2 : discriminate.

      destruct a as [an]. case_eq (beq_nat an n); intros Hbeq.
        rewrite (beq_nat_true _ _ Hbeq) in *. rewrite rename_FOv_same in *.
        apply (IHlx ln alpha x Hc H); try assumption.

destruct (aa11' ln lx) as [[ln1 [ln2 [H1 H2]]] | [lx1 [lx2 [H1 H2]]]].
rewrite H2 in *. rewrite newnew_pre_extra_n in *. 2 : assumption.
      case_eq lx. intros Hlx. simpl. destruct x as [xn]. rewrite Hlx in *.

pose proof  (equiv_rename_FOv_free_FO_f alpha (Var an) (Var n)).
unfold rename_FOv in H3.
        apply H3; try assumption.
        apply aa14 with (x := (Var xn));
        try assumption.
          rewrite <- H2 in *.
          apply (aa17 _ ln n (Var xn)); try assumption.

          apply beq_nat_false_FOv. assumption.

          apply (contrapos_bool_tf _ _ (x_occ_in_alpha_max_FOv_gen2 _ _ )).
          apply (leb_trans _ (min_l ln)). rewrite H2. assumption.
          apply (leb_trans _ (max_l ln)). apply leb_min__max_l.
          apply leb_suc_l. rewrite H2. assumption.

        intros y lx' Hlx.

      assert (x_occ_in_alpha (newnew_pre alpha lx ln1) (Var n) = false) as
        Has. destruct n. simpl in *. discriminate.
        apply x_occ_in_alpha_max_FOv_gen.
        rewrite <- leb_defn_suc. apply aa; try assumption.

          apply (aa15 _ _ ln2).
            intros H'. rewrite H' in H1. simpl in H1.
            rewrite Hlx in H1. discriminate.
          assumption.

          apply (aa16 ln1 ln2). assumption.

      apply equiv_rename_FOv_free_FO_f in SOt.
rewrite <- (newnew_pre_extra_n _ ln1 ln2) in SOt.
      rewrite <- H2 in *. apply (IHlx ln alpha x) in SOt.
        all: try assumption. 

      pose proof (kk14' lx ln1) as H4.
      apply aa14 with (x := x).
      apply H4; try assumption.

          apply (aa15 _ _ ln2).
            intros H'. rewrite H' in H1. simpl in H1.
            rewrite Hlx in H1. discriminate.
          assumption.

        intros H'; rewrite H' in *.
        contradiction (H0 eq_refl).

      apply x_occ_in_free_FO. assumption.

      apply beq_nat_false_FOv. assumption.

(* -- *)

rewrite H2 in *. rewrite newnew_pre_extra_x in *. 2 : assumption.

      assert (x_occ_in_alpha (newnew_pre alpha lx1 ln) (Var n) = false) as
        Has. destruct n. simpl in *. discriminate.
        apply x_occ_in_alpha_max_FOv_gen.
        rewrite <- leb_defn_suc. apply aa; try assumption.
          symmetry. assumption.
      

      apply equiv_rename_FOv_free_FO_f in SOt.
rewrite <- (newnew_pre_extra_x _ _ lx2) in SOt.
      rewrite <- H2 in *. apply (IHlx ln alpha x).
        all: try assumption. 
 
      pose proof (kk14' lx1 ln) as H4.
      apply aa14 with (x := x).
      apply H4; try assumption.

        apply (is_in_FOvar_app_l lx1 lx2).
        assumption.

        intros H'; rewrite H' in *.
        contradiction (H0 eq_refl).

      apply x_occ_in_free_FO. assumption.
      apply beq_nat_false_FOv. assumption.

Qed.

Lemma is_in_FOvar_rem_FOv_same : forall alpha x,
  is_in_FOvar x (rem_FOv alpha x) = false.
Proof.
  induction alpha; intros [xn].
    simpl. reflexivity.

    simpl. destruct a as [ym]. 
    case_eq (beq_nat xn ym); intros Hbeq.
      apply IHalpha.
  
      simpl. rewrite Hbeq. apply IHalpha.
Qed.

Lemma free_FO_rep_pred : forall alpha x P,
  free_FO alpha x =
  free_FO (replace_pred alpha P (Var 1)
     (negSO (eqFO (Var 1) (Var 1)))) x.
Proof.
  induction alpha; intros [xn] [Pn].
    destruct p as [Qm]; destruct f as [zn]. simpl.
    case_eq (beq_nat Pn Qm); intros Hbeq;
      simpl. case_eq (beq_nat xn zn); reflexivity.
      reflexivity.

    destruct f; destruct f0. reflexivity.

    destruct f; destruct f0. reflexivity.

    destruct f as [ym]. simpl.
    case_eq (beq_nat xn ym); intros Hbeq.
      reflexivity.
      apply IHalpha.

    destruct f as [ym]. simpl.
    case_eq (beq_nat xn ym); intros Hbeq.
      reflexivity.
      apply IHalpha.

    simpl in *. apply IHalpha.

    simpl in *. rewrite <- IHalpha1.
    rewrite <- IHalpha2. reflexivity.

    simpl in *. rewrite <- IHalpha1.
    rewrite <- IHalpha2. reflexivity.

    simpl in *. rewrite <- IHalpha1.
    rewrite <- IHalpha2. reflexivity.

    destruct p as [Qm]. simpl.
    case_eq (beq_nat Pn Qm); intros Hbeq.
      apply IHalpha. simpl. apply IHalpha.

    destruct p as [Qm]. simpl.
    case_eq (beq_nat Pn Qm); intros Hbeq.
      apply IHalpha. simpl. apply IHalpha.
Qed.

Lemma kk12 : forall alpha x y,
  closed_except alpha x ->
  closed_except (replace_pred alpha y (Var 1) 
    (negSO (eqFO (Var 1) (Var 1)))) x.
Proof.
  intros alpha [xn] [ym] H.
  unfold closed_except  in *.
  destruct H as [H1 H2].
  apply conj.
    rewrite <- free_FO_rep_pred.
    assumption.

    intros [zn] Hneq.
    rewrite <- free_FO_rep_pred.
    apply H2. assumption.
Qed.

Lemma kk11: forall lP beta x,
closed_except beta x ->
closed_except
  (replace_pred_l beta lP
     (nlist_list (length lP) (nlist_Var1 _))
     (nlist_list (length lP) (nlist_empty _))) x.
Proof.
  induction lP; intros beta x H.
    simpl. assumption.

    simpl.
    apply kk12. apply IHlP.
    assumption.
Qed.

Lemma closed_except_inst_cons_empty' : forall beta alpha x,
  closed_except beta x ->
  closed_except (instant_cons_empty' alpha beta) x.
Proof.
  unfold instant_cons_empty'.
  intros. apply kk11. assumption.
Qed.

Lemma max_l_rev_seq : forall m n,
  max_l (rev_seq n (S m)) = (n + m).
Proof.
  induction m; intros n.
    simpl. destruct n; reflexivity.

    simpl in *. rewrite IHm. 
    rewrite <- plus_n_Sm.
    apply max_suc_l.
Qed.

Lemma decr_strict_rev_seq : forall m n,
  decr_strict (rev_seq (S n) m) = true.
Proof.
  induction m; intros n.
    reflexivity.

    simpl. rewrite IHm.
    destruct m. simpl. reflexivity.
    rewrite max_l_rev_seq. rewrite <- plus_n_Sm.
    rewrite <- plus_Sn_m. rewrite leb_refl.
    reflexivity.
Qed.

Lemma aa22_pre_1 : forall cond x z,
  
  (forall y : FOvariable, x <> y -> x_occ_in_alpha cond y = false) ->
  (forall y : FOvariable, z <> y ->
     x_occ_in_alpha (replace_FOv cond x z) y = false).
Proof.
  induction cond; intros [xn] [zn] H [ym] Hneq.
    destruct p as [Pn]; destruct f as [un].
    simpl in *. case_eq (beq_nat xn un); intros Hbeq;
      simpl. rewrite beq_nat_comm. apply neq_beq_nat_FOv.
      assumption.

      specialize (H (Var un)). simpl in *. rewrite <- beq_nat_refl in H.
      discriminate (H (beq_nat_false_FOv _ _ Hbeq)).  

    destruct f as [u1]; destruct f0 as [u2].
    simpl in *. case_eq (beq_nat xn u1); intros Hbeq1.
      case_eq (beq_nat xn u2); intros Hbeq2;
        simpl; apply FOv_neq_switch in Hneq;
        rewrite neq_beq_nat_FOv. reflexivity.
        assumption.

        case_eq (beq_nat ym u2); intros Hbeq3.
          2 : reflexivity.
        specialize (H (Var u2)). simpl in  *.
        rewrite <- beq_nat_refl in H. rewrite if_then_else_true in H.
        discriminate (H (beq_nat_false_FOv _ _ Hbeq2)).
        assumption.

      case_eq (beq_nat xn u2); intros Hbeq2; simpl.
        specialize (H (Var u1)). simpl in *. rewrite <- beq_nat_refl in H.
        discriminate (H (beq_nat_false_FOv _ _ Hbeq1)).

        case_eq (beq_nat ym u1); intros Hbeq3.
          rewrite <- (beq_nat_true _ _ Hbeq3) in Hbeq1.
          specialize (H (Var ym)). simpl in H.
          rewrite Hbeq3 in *. discriminate (H (beq_nat_false_FOv _ _ Hbeq1)).

          case_eq (beq_nat ym u2); intros Hbeq4.
            rewrite <- (beq_nat_true _ _ Hbeq4) in Hbeq2.
            specialize (H (Var ym)). simpl in H.
            rewrite Hbeq3 in *. rewrite Hbeq4 in H.
            discriminate (H (beq_nat_false_FOv _ _ Hbeq2)).

            reflexivity.

    destruct f as [u1]; destruct f0 as [u2].
    simpl in *. case_eq (beq_nat xn u1); intros Hbeq1.
      case_eq (beq_nat xn u2); intros Hbeq2;
        simpl; apply FOv_neq_switch in Hneq;
        rewrite neq_beq_nat_FOv. reflexivity.
        assumption.

        case_eq (beq_nat ym u2); intros Hbeq3.
          2 : reflexivity.
        specialize (H (Var u2)). simpl in  *.
        rewrite <- beq_nat_refl in H. rewrite if_then_else_true in H.
        discriminate (H (beq_nat_false_FOv _ _ Hbeq2)).
        assumption.

      case_eq (beq_nat xn u2); intros Hbeq2; simpl.
        specialize (H (Var u1)). simpl in *. rewrite <- beq_nat_refl in H.
        discriminate (H (beq_nat_false_FOv _ _ Hbeq1)).

        case_eq (beq_nat ym u1); intros Hbeq3.
          rewrite <- (beq_nat_true _ _ Hbeq3) in Hbeq1.
          specialize (H (Var ym)). simpl in H.
          rewrite Hbeq3 in *. discriminate (H (beq_nat_false_FOv _ _ Hbeq1)).

          case_eq (beq_nat ym u2); intros Hbeq4.
            rewrite <- (beq_nat_true _ _ Hbeq4) in Hbeq2.
            specialize (H (Var ym)). simpl in H.
            rewrite Hbeq3 in *. rewrite Hbeq4 in H.
            discriminate (H (beq_nat_false_FOv _ _ Hbeq2)).

            reflexivity.

    destruct f as [un]. simpl.
    case_eq (beq_nat xn un); intros Hbeq; simpl;
      pose proof Hneq as Hneq'.
      apply neq_beq_nat_FOv in Hneq. rewrite beq_nat_comm.
      rewrite Hneq. apply IHcond.
        intros [vn] Hneq2.
        specialize (H (Var vn) Hneq2). simpl in H.
        case_eq (beq_nat vn un); intros Hbeq2;
          rewrite Hbeq2 in H. discriminate.
        all : try assumption.

      case_eq (beq_nat ym un); intros Hbeq2.
        rewrite <- (beq_nat_true _ _ Hbeq2) in Hbeq.
        apply beq_nat_false_FOv in Hbeq.
        specialize (H (Var ym) Hbeq). simpl in H.
        rewrite Hbeq2 in H. discriminate.

        apply IHcond. intros [vn] Hneq2.
        specialize (H (Var vn) Hneq2). simpl in H.  
        case_eq (beq_nat vn un); intros Hbeq3;
          rewrite Hbeq3 in *. discriminate.
        all : try assumption.

    destruct f as [un]. simpl.
    case_eq (beq_nat xn un); intros Hbeq; simpl;
      pose proof Hneq as Hneq'.
      apply neq_beq_nat_FOv in Hneq. rewrite beq_nat_comm.
      rewrite Hneq. apply IHcond.
        intros [vn] Hneq2.
        specialize (H (Var vn) Hneq2). simpl in H.
        case_eq (beq_nat vn un); intros Hbeq2;
          rewrite Hbeq2 in H. discriminate.
        all : try assumption.

      case_eq (beq_nat ym un); intros Hbeq2.
        rewrite <- (beq_nat_true _ _ Hbeq2) in Hbeq.
        apply beq_nat_false_FOv in Hbeq.
        specialize (H (Var ym) Hbeq). simpl in H.
        rewrite Hbeq2 in H. discriminate.

        apply IHcond. intros [vn] Hneq2.
        specialize (H (Var vn) Hneq2). simpl in H.  
        case_eq (beq_nat vn un); intros Hbeq3;
          rewrite Hbeq3 in *. discriminate.
        all : try assumption.

    simpl in *. apply IHcond; assumption.

    simpl.
    rewrite IHcond1. apply IHcond2.
      intros [vn] Hneq2.  specialize (H (Var vn) Hneq2).
      apply x_occ_in_alpha_conjSO in H. apply H. assumption.

      intros [vn] Hneq2.  specialize (H (Var vn) Hneq2).
      apply x_occ_in_alpha_conjSO in H. apply H. assumption.


    simpl.
    rewrite IHcond1. apply IHcond2.
      intros [vn] Hneq2.  specialize (H (Var vn) Hneq2).
      apply x_occ_in_alpha_conjSO in H. apply H. assumption.

      intros [vn] Hneq2.  specialize (H (Var vn) Hneq2).
      apply x_occ_in_alpha_conjSO in H. apply H. assumption.

    simpl.
    rewrite IHcond1. apply IHcond2.
      intros [vn] Hneq2.  specialize (H (Var vn) Hneq2).
      apply x_occ_in_alpha_conjSO in H. apply H. assumption.

      intros [vn] Hneq2.  specialize (H (Var vn) Hneq2).
      apply x_occ_in_alpha_conjSO in H. apply H. assumption.

    destruct p. simpl in *. apply IHcond; assumption.

    destruct p. simpl in *. apply IHcond; assumption.
Qed.


Lemma aa22_pre_2_pre : forall cond xn,
  (forall y : FOvariable, Var xn <> y -> x_occ_in_alpha cond y = false) ->
  (x_occ_in_alpha cond (Var xn) = true ->  max_FOv cond = xn) /\
  (x_occ_in_alpha cond (Var xn) = false -> max_FOv cond = 0).
Proof.
  induction cond; intros xn Hnocc; apply conj; intros Hocc.
    destruct p; destruct f as [ym].
    simpl in *. rewrite (beq_nat_true _ _  Hocc).
    reflexivity.

    destruct p; destruct f as [ym].
    simpl in *. specialize (Hnocc (Var ym) (beq_nat_false_FOv _ _ Hocc)).
    simpl in *. rewrite <- beq_nat_refl in Hnocc. discriminate.

    destruct f as [y1]; destruct f0 as [y2].
    simpl in *. case_eq (beq_nat xn y1); intros Hbeq;
      rewrite Hbeq in *.
      case_eq (beq_nat xn y2); intros Hbeq2.
        rewrite <- (beq_nat_true _ _ Hbeq).
        rewrite (beq_nat_true _ _ Hbeq2).
        apply max_refl.

        specialize (Hnocc (Var y2) (beq_nat_false_FOv _ _ Hbeq2)).
        simpl in Hnocc. rewrite <- beq_nat_refl in Hnocc.
        rewrite if_then_else_true in Hnocc. discriminate.

        specialize (Hnocc (Var y1) (beq_nat_false_FOv _ _ Hbeq)).
        simpl in Hnocc. rewrite <- beq_nat_refl in Hnocc.
        discriminate.

    destruct f as [y1]; destruct f0 as [y2].
    simpl in *. case_eq (beq_nat xn y1); intros Hbeq;
      rewrite Hbeq in *. discriminate.

        specialize (Hnocc (Var y1) (beq_nat_false_FOv _ _ Hbeq)).
        simpl in Hnocc. rewrite <- beq_nat_refl in Hnocc.
        discriminate.

    destruct f as [y1]; destruct f0 as [y2].
    simpl in *. case_eq (beq_nat xn y1); intros Hbeq;
      rewrite Hbeq in *.
      case_eq (beq_nat xn y2); intros Hbeq2.
        rewrite <- (beq_nat_true _ _ Hbeq).
        rewrite (beq_nat_true _ _ Hbeq2).
        apply max_refl.

        specialize (Hnocc (Var y2) (beq_nat_false_FOv _ _ Hbeq2)).
        simpl in Hnocc. rewrite <- beq_nat_refl in Hnocc.
        rewrite if_then_else_true in Hnocc. discriminate.

        specialize (Hnocc (Var y1) (beq_nat_false_FOv _ _ Hbeq)).
        simpl in Hnocc. rewrite <- beq_nat_refl in Hnocc.
        discriminate.

    destruct f as [y1]; destruct f0 as [y2].
    simpl in *. case_eq (beq_nat xn y1); intros Hbeq;
      rewrite Hbeq in *. discriminate.

        specialize (Hnocc (Var y1) (beq_nat_false_FOv _ _ Hbeq)).
        simpl in Hnocc. rewrite <- beq_nat_refl in Hnocc.
        discriminate.

    destruct f as [ym]. simpl in *.
    destruct (IHcond xn) as [IH1 IH2].
      intros [zn] Hneq2. specialize (Hnocc (Var zn) Hneq2).
      simpl in Hnocc. case_eq (beq_nat zn ym);
      intros Hbeq2; rewrite Hbeq2 in *. discriminate.

      assumption.
    case_eq (beq_nat xn ym); intros Hbeq; rewrite Hbeq in *.
      case_eq (x_occ_in_alpha cond (Var xn)); intros Hocc1.
        rewrite IH1. rewrite (beq_nat_true _ _ Hbeq).
        apply max_refl. assumption.

        rewrite IH2. rewrite (beq_nat_true _ _ Hbeq).
        rewrite max_comm. reflexivity. assumption.

      specialize (Hnocc (Var ym) (beq_nat_false_FOv _ _ Hbeq)).
      simpl in *. rewrite <- beq_nat_refl in Hnocc.
      discriminate.

    destruct f as [ym]. simpl in *.
    destruct (IHcond xn) as [IH1 IH2].
      intros [zn] Hneq2. specialize (Hnocc (Var zn) Hneq2).
      simpl in Hnocc. case_eq (beq_nat zn ym);
      intros Hbeq2; rewrite Hbeq2 in *. discriminate.

      assumption.
    case_eq (beq_nat xn ym); intros Hbeq; rewrite Hbeq in *.
      discriminate.

      specialize (Hnocc (Var ym) (beq_nat_false_FOv _ _ Hbeq)).
      simpl in *. rewrite <- beq_nat_refl in Hnocc.
      discriminate.

    destruct f as [ym]. simpl in *.
    destruct (IHcond xn) as [IH1 IH2].
      intros [zn] Hneq2. specialize (Hnocc (Var zn) Hneq2).
      simpl in Hnocc. case_eq (beq_nat zn ym);
      intros Hbeq2; rewrite Hbeq2 in *. discriminate.

      assumption.
    case_eq (beq_nat xn ym); intros Hbeq; rewrite Hbeq in *.
      case_eq (x_occ_in_alpha cond (Var xn)); intros Hocc1.
        rewrite IH1. rewrite (beq_nat_true _ _ Hbeq).
        apply max_refl. assumption.

        rewrite IH2. rewrite (beq_nat_true _ _ Hbeq).
        rewrite max_comm. reflexivity. assumption.

      specialize (Hnocc (Var ym) (beq_nat_false_FOv _ _ Hbeq)).
      simpl in *. rewrite <- beq_nat_refl in Hnocc.
      discriminate.

    destruct f as [ym]. simpl in *.
    destruct (IHcond xn) as [IH1 IH2].
      intros [zn] Hneq2. specialize (Hnocc (Var zn) Hneq2).
      simpl in Hnocc. case_eq (beq_nat zn ym);
      intros Hbeq2; rewrite Hbeq2 in *. discriminate.

      assumption.
    case_eq (beq_nat xn ym); intros Hbeq; rewrite Hbeq in *.
      discriminate.

      specialize (Hnocc (Var ym) (beq_nat_false_FOv _ _ Hbeq)).
      simpl in *. rewrite <- beq_nat_refl in Hnocc.
      discriminate.

    simpl in *. apply IHcond; assumption.
    simpl in *. apply (IHcond xn); assumption.

    simpl in *.
    destruct (IHcond1 xn) as [IH1 IH2].
      intros [zn] Hneq2. specialize (Hnocc (Var zn) Hneq2).
      simpl in Hnocc. case_eq (x_occ_in_alpha cond1 (Var zn));
      intros Hocc1; rewrite Hocc1 in Hnocc. discriminate. reflexivity.
    destruct (IHcond2 xn) as [IH1a IH2a].
      intros [zn] Hneq2. specialize (Hnocc (Var zn) Hneq2).
      simpl in Hnocc. case_eq (x_occ_in_alpha cond1 (Var zn));
      intros Hocc1; rewrite Hocc1 in Hnocc. discriminate. assumption.
    case_eq (x_occ_in_alpha cond1 (Var xn));
      intros Hocc1; rewrite Hocc1 in *. rewrite IH1.
      case_eq (x_occ_in_alpha cond2 (Var xn)); intros Hocc2.
        rewrite IH1a. apply max_refl. assumption.

        rewrite IH2a. rewrite max_comm. reflexivity. assumption.
        reflexivity.

      rewrite IH2. rewrite IH1a. reflexivity. assumption. reflexivity.

    simpl in *.
    destruct (IHcond1 xn) as [IH1 IH2].
      intros [zn] Hneq2. specialize (Hnocc (Var zn) Hneq2).
      simpl in Hnocc. case_eq (x_occ_in_alpha cond1 (Var zn));
      intros Hocc1; rewrite Hocc1 in Hnocc. discriminate. reflexivity.
    destruct (IHcond2 xn) as [IH1a IH2a].
      intros [zn] Hneq2. specialize (Hnocc (Var zn) Hneq2).
      simpl in Hnocc. case_eq (x_occ_in_alpha cond1 (Var zn));
      intros Hocc1; rewrite Hocc1 in Hnocc. discriminate. assumption.
    case_eq (x_occ_in_alpha cond1 (Var xn));
      intros Hocc1; rewrite Hocc1 in *. discriminate. 

      rewrite IH2. rewrite IH2a. reflexivity. assumption. reflexivity.

    simpl in *.
    destruct (IHcond1 xn) as [IH1 IH2].
      intros [zn] Hneq2. specialize (Hnocc (Var zn) Hneq2).
      simpl in Hnocc. case_eq (x_occ_in_alpha cond1 (Var zn));
      intros Hocc1; rewrite Hocc1 in Hnocc. discriminate. reflexivity.
    destruct (IHcond2 xn) as [IH1a IH2a].
      intros [zn] Hneq2. specialize (Hnocc (Var zn) Hneq2).
      simpl in Hnocc. case_eq (x_occ_in_alpha cond1 (Var zn));
      intros Hocc1; rewrite Hocc1 in Hnocc. discriminate. assumption.
    case_eq (x_occ_in_alpha cond1 (Var xn));
      intros Hocc1; rewrite Hocc1 in *. rewrite IH1.
      case_eq (x_occ_in_alpha cond2 (Var xn)); intros Hocc2.
        rewrite IH1a. apply max_refl. assumption.

        rewrite IH2a. rewrite max_comm. reflexivity. assumption.
        reflexivity.

      rewrite IH2. rewrite IH1a. reflexivity. assumption. reflexivity.

    simpl in *.
    destruct (IHcond1 xn) as [IH1 IH2].
      intros [zn] Hneq2. specialize (Hnocc (Var zn) Hneq2).
      simpl in Hnocc. case_eq (x_occ_in_alpha cond1 (Var zn));
      intros Hocc1; rewrite Hocc1 in Hnocc. discriminate. reflexivity.
    destruct (IHcond2 xn) as [IH1a IH2a].
      intros [zn] Hneq2. specialize (Hnocc (Var zn) Hneq2).
      simpl in Hnocc. case_eq (x_occ_in_alpha cond1 (Var zn));
      intros Hocc1; rewrite Hocc1 in Hnocc. discriminate. assumption.
    case_eq (x_occ_in_alpha cond1 (Var xn));
      intros Hocc1; rewrite Hocc1 in *. discriminate. 

      rewrite IH2. rewrite IH2a. reflexivity. assumption. reflexivity.

    simpl in *.
    destruct (IHcond1 xn) as [IH1 IH2].
      intros [zn] Hneq2. specialize (Hnocc (Var zn) Hneq2).
      simpl in Hnocc. case_eq (x_occ_in_alpha cond1 (Var zn));
      intros Hocc1; rewrite Hocc1 in Hnocc. discriminate. reflexivity.
    destruct (IHcond2 xn) as [IH1a IH2a].
      intros [zn] Hneq2. specialize (Hnocc (Var zn) Hneq2).
      simpl in Hnocc. case_eq (x_occ_in_alpha cond1 (Var zn));
      intros Hocc1; rewrite Hocc1 in Hnocc. discriminate. assumption.
    case_eq (x_occ_in_alpha cond1 (Var xn));
      intros Hocc1; rewrite Hocc1 in *. rewrite IH1.
      case_eq (x_occ_in_alpha cond2 (Var xn)); intros Hocc2.
        rewrite IH1a. apply max_refl. assumption.

        rewrite IH2a. rewrite max_comm. reflexivity. assumption.
        reflexivity.

      rewrite IH2. rewrite IH1a. reflexivity. assumption. reflexivity.

    simpl in *.
    destruct (IHcond1 xn) as [IH1 IH2].
      intros [zn] Hneq2. specialize (Hnocc (Var zn) Hneq2).
      simpl in Hnocc. case_eq (x_occ_in_alpha cond1 (Var zn));
      intros Hocc1; rewrite Hocc1 in Hnocc. discriminate. reflexivity.
    destruct (IHcond2 xn) as [IH1a IH2a].
      intros [zn] Hneq2. specialize (Hnocc (Var zn) Hneq2).
      simpl in Hnocc. case_eq (x_occ_in_alpha cond1 (Var zn));
      intros Hocc1; rewrite Hocc1 in Hnocc. discriminate. assumption.
    case_eq (x_occ_in_alpha cond1 (Var xn));
      intros Hocc1; rewrite Hocc1 in *. discriminate. 

      rewrite IH2. rewrite IH2a. reflexivity. assumption. reflexivity.

    destruct p. simpl in *. apply IHcond; assumption.
    destruct p. simpl in *. apply (IHcond xn); assumption.

    destruct p. simpl in *. apply IHcond; assumption.
    destruct p. simpl in *. apply (IHcond xn); assumption.
Qed.

Lemma aa22_pre_2 : forall cond xn,
  (forall y : FOvariable, Var xn <> y -> x_occ_in_alpha cond y = false) ->
  (x_occ_in_alpha cond (Var xn) = true ->  max_FOv cond = xn).
Proof.
  intros. apply aa22_pre_2_pre; assumption.
Qed.

Lemma x_occ_in_alpha_rep_FOv : forall cond x y,
  x_occ_in_alpha cond x = true ->
  x_occ_in_alpha (replace_FOv cond x y) y = true.
Proof.
  induction cond; intros [xn] [ym] Hocc.
    destruct p as [Pn]; destruct f as [zn]. simpl in *.
    rewrite Hocc. simpl. symmetry. apply beq_nat_refl.

    destruct f as [z1]; destruct f0 as [z2].
    simpl in *. case_eq (beq_nat xn z2); intros Hbeq2;
      rewrite Hbeq2 in Hocc;
      case_eq (beq_nat xn z1); intros Hbeq1; rewrite Hbeq1 in *;
        simpl; try rewrite <- beq_nat_refl; try reflexivity.
        rewrite if_then_else_true. reflexivity.

        discriminate.

    destruct f as [z1]; destruct f0 as [z2].
    simpl in *. case_eq (beq_nat xn z2); intros Hbeq2;
      rewrite Hbeq2 in Hocc;
      case_eq (beq_nat xn z1); intros Hbeq1; rewrite Hbeq1 in *;
        simpl; try rewrite <- beq_nat_refl; try reflexivity.
        rewrite if_then_else_true. reflexivity.

        discriminate.

    destruct f as [zn]. simpl in *. case_eq (beq_nat xn zn);
      intros Hbeq; rewrite Hbeq in *.
      simpl. rewrite <- beq_nat_refl. reflexivity.
      simpl. case_eq (beq_nat ym zn); intros Hbeq2.
        reflexivity.
      apply IHcond. assumption.

    destruct f as [zn]. simpl in *. case_eq (beq_nat xn zn);
      intros Hbeq; rewrite Hbeq in *.
      simpl. rewrite <- beq_nat_refl. reflexivity.
      simpl. case_eq (beq_nat ym zn); intros Hbeq2.
        reflexivity.
      apply IHcond. assumption.

    simpl in *. apply IHcond. assumption.

    simpl in *. case_eq (x_occ_in_alpha cond1 (Var xn));
      intros Hocc1; rewrite Hocc1 in *.
      rewrite IHcond1. reflexivity. assumption.

      rewrite IHcond2. rewrite if_then_else_true.
      reflexivity. assumption.

    simpl in *. case_eq (x_occ_in_alpha cond1 (Var xn));
      intros Hocc1; rewrite Hocc1 in *.
      rewrite IHcond1. reflexivity. assumption.

      rewrite IHcond2. rewrite if_then_else_true.
      reflexivity. assumption.

    simpl in *. case_eq (x_occ_in_alpha cond1 (Var xn));
      intros Hocc1; rewrite Hocc1 in *.
      rewrite IHcond1. reflexivity. assumption.

      rewrite IHcond2. rewrite if_then_else_true.
      reflexivity. assumption.

    destruct p as [Qm]. simpl in *. apply IHcond.
    assumption.

    destruct p as [Qm]. simpl in *. apply IHcond.
    assumption.
Qed.

Lemma aa22_pre : forall cond xn ym,
  x_occ_in_alpha cond (Var xn) = true ->
  (forall y : FOvariable, Var xn <> y -> x_occ_in_alpha cond y = false) ->
Nat.leb (max_FOv (replace_FOv cond (Var xn) (Var ym))) ym = true.
Proof.
  intros cond xn ym Hocc Hnocc.
  pose proof (aa22_pre_1 cond (Var xn) (Var ym) Hnocc) as H.
  apply x_occ_in_alpha_rep_FOv with (y := (Var ym)) in Hocc.
  rewrite (aa22_pre_2 _ ym); try assumption.
  apply leb_refl.
Qed.

Lemma aa22 : forall beta P x cond,
  x_occ_in_alpha cond x = true ->
  (forall y, ~ x = y -> x_occ_in_alpha cond y = false) ->
  Nat.leb (max_FOv (replace_pred beta P x cond))
          (max_FOv beta) = true.
Proof.
  induction beta; intros [Pn] [xn] cond Hocc Hnocc.
    destruct p as [Qm]; destruct f as [ym].
    simpl. case_eq (beq_nat Pn Qm); intros Hbeq.
      apply aa22_pre; assumption.

      simpl in *. apply leb_refl.

    destruct f as [y1]; destruct f0 as [y2].
    simpl in *. apply leb_refl.

    destruct f as [y1]; destruct f0 as [y2].
    simpl in *. apply leb_refl.

    destruct f as [zn]; simpl.
    rewrite (max_comm zn).
    rewrite (max_comm zn). apply leb_max_max.
    apply IHbeta; assumption.

    destruct f as [zn]; simpl.
    rewrite (max_comm zn).
    rewrite (max_comm zn). apply leb_max_max.
    apply IHbeta; assumption.

    simpl in *. apply IHbeta; assumption.

    simpl. apply leb_max_max_gen. apply IHbeta1; assumption.
    apply IHbeta2; assumption.

    simpl. apply leb_max_max_gen. apply IHbeta1; assumption.
    apply IHbeta2; assumption.

    simpl. apply leb_max_max_gen. apply IHbeta1; assumption.
    apply IHbeta2; assumption.

    destruct p as [Qm]. simpl. case_eq (beq_nat Pn Qm); intros Hbeq.
      apply IHbeta; assumption.

      simpl. apply IHbeta; assumption.

    destruct p as [Qm]. simpl. case_eq (beq_nat Pn Qm); intros Hbeq.
      apply IHbeta; assumption.

      simpl. apply IHbeta; assumption.
Qed.

Fixpoint x_occ_in_alpha_l lcond lx : bool :=
  match lx, lcond with
  | nil, _ => true
  | _, nil => true
  | cons x lx', cons cond lcond' => if x_occ_in_alpha cond x then
      (x_occ_in_alpha_l lcond' lx') else false
  end.

Fixpoint x_nocc_in_alpha_l lcond lx : Prop :=
  match lx, lcond with
  | nil, _ => True
  | _, nil => True
  | cons x lx', cons cond lcond' => 
      (forall y, ~ x = y -> (x_occ_in_alpha cond y = false)) /\
      (x_nocc_in_alpha_l lcond' lx')
  end.

Lemma   aa21 : forall lP lx lcond beta,
   x_occ_in_alpha_l lcond lx = true ->
   x_nocc_in_alpha_l lcond lx ->
  Nat.leb (max_FOv (replace_pred_l beta lP lx lcond))
          (max_FOv beta) = true.
Proof.
  induction lP; intros lx lcond beta Hocc Hnocc.
    simpl. apply leb_refl.

    destruct lx. simpl. apply leb_refl.
    destruct lcond. simpl. apply leb_refl.
    simpl.
    simpl in Hocc. case_eq (x_occ_in_alpha s f);
      intros Hocc2; rewrite Hocc2 in *. 2 : discriminate.
    simpl in Hnocc. destruct Hnocc as [Hn1 Hn2].
    apply (leb_trans _ (max_FOv (replace_pred_l beta lP lx lcond))).
    apply aa22; try assumption.
    apply IHlP; assumption.
Qed.

Lemma aa25 : forall n,
  x_occ_in_alpha_l (nlist_list n (nlist_empty _))
                   (nlist_list n (nlist_Var1 _)) = true.
Proof.
  induction n.
    reflexivity.

    simpl. apply IHn.
Qed.

Lemma aa26 : forall n,
  x_nocc_in_alpha_l (nlist_list n (nlist_empty _ ))
                    (nlist_list n (nlist_Var1 _)).
Proof.
  induction n.
    reflexivity.

    simpl. apply conj.
    intros [ym] Heq.
    rewrite beq_nat_comm. rewrite neq_beq_nat_FOv.
    reflexivity. assumption.
    apply IHn.
Qed.


Lemma aa20: forall alpha beta,
Nat.leb (max_FOv (instant_cons_empty' alpha beta))
  (max_FOv (implSO alpha beta)) = true.
Proof.
  intros alpha beta.
  unfold instant_cons_empty'.
  apply (leb_trans _ (max_FOv beta)).
  apply aa21.
    apply aa25.
    apply aa26.
  simpl. rewrite max_comm. apply leb_max_suc3.
  apply leb_refl.
Qed.