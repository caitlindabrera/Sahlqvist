Require Import my_arith__my_leb_nat my_bool Coq.Lists.List.
Require Export vsSahlq_instant3 vsSahlq_instant_pre_to_be_sorted.

(*  ----------------------------------------------- *)

Definition instant_cons_empty' alpha beta : SecOrder :=
  replace_pred_l beta (list_pred_not_in (preds_in alpha)
                                         (preds_in beta))
          (nlist_list _ (nlist_Var1 (length
              (list_pred_not_in (preds_in alpha)
                                (preds_in beta)))))
          (nlist_list _ (nlist_empty (length 
              (list_pred_not_in (preds_in alpha)
                                (preds_in beta))))).

Lemma ex_att_allFO_lv_conjSO_f_rev : forall lv alpha1 alpha2,
 (ex_attached_allFO_lv alpha1 lv = false) ->
 (ex_attached_allFO_lv alpha2 lv = false) ->
  ex_attached_allFO_lv (conjSO alpha1 alpha2) lv = false.
Proof.
  induction lv; intros alpha1 alpha2 Ha Hb.
    simpl in *. reflexivity.

    simpl in *.
    case_eq (attached_allFO_x alpha1 a); intros H1;
      simpl in Ha; rewrite H1 in Ha. discriminate.
    case_eq (attached_allFO_x alpha2 a); intros H2;
      rewrite H2 in Hb. discriminate.
    apply IHlv; assumption.
Qed.

Lemma  att_allFO_x_REL : forall rel x,
  REL rel = true ->
  attached_allFO_x rel x = false.
Proof.
  induction rel; intros [xn] H; try
    reflexivity;
    try (simpl in *; discriminate).

    simpl in *.
    case_eq (REL rel1); intros H1; rewrite H1 in H.
      2 : discriminate.
    rewrite IHrel1. apply IHrel2.
    all : assumption.
Qed.

Lemma ex_att_allFO_lv_REL : forall lv rel,
  REL rel = true ->
  ex_attached_allFO_lv rel lv = false.
Proof.
  induction lv; intros rel Hrel.
    simpl. reflexivity.

    simpl. rewrite att_allFO_x_REL.
    apply IHlv. all: assumption.
Qed.


Lemma  att_allFO_x_AT : forall atm x,
  AT atm = true ->
  attached_allFO_x atm x = false.
Proof.
  induction atm; intros [xn] H; try
    reflexivity;
    try (simpl in *; discriminate).

    simpl in *.
    case_eq (AT atm1); intros H1; rewrite H1 in H.
      2 : discriminate.
    rewrite IHatm1. apply IHatm2.
    all : assumption.
Qed.

Lemma ex_att_allFO_lv_AT : forall lv atm,
  AT atm = true ->
  ex_attached_allFO_lv atm lv = false.
Proof.
  induction lv; intros rel Hrel.
    simpl. reflexivity.

    simpl. rewrite att_allFO_x_AT.
    apply IHlv. all: assumption.
Qed.

Fixpoint is_in_FOvar (x : FOvariable) (l : list FOvariable) : bool :=
  match l with
  | nil => false
  | cons y l => match x, y with Var xn, Var ym =>
     if beq_nat xn ym then true else (is_in_FOvar x l)
  end end.

Lemma is_in_FOvar_app : forall l1 l2 x,
  is_in_FOvar x (app l1 l2) =
  if is_in_FOvar x l1 then true else is_in_FOvar x l2.
Proof.
  induction l1; intros l2 [xn].
    simpl. reflexivity.

    simpl. destruct a as [ym].
    case_eq (beq_nat xn ym); intros Hbeq.
      reflexivity.
      apply IHl1.
Qed.

Fixpoint rename_FOv_list (l : list FOvariable) x y : list FOvariable :=
  match l with
  | nil => nil
  | cons z l' =>
  match x, z with Var xn, Var zn => 
    if beq_nat xn zn then cons y (rename_FOv_list l' x y) else cons z (rename_FOv_list l' x y)
  end end.

Lemma rename_FOv_list_app : forall l1 l2 x y,
  rename_FOv_list (app l1 l2) x y =
  app (rename_FOv_list l1 x y) (rename_FOv_list l2 x y).
Proof.
  induction l1; intros l2 [xn] [ym].
    simpl. reflexivity.

    simpl. destruct a as [zn].
    case_eq (beq_nat xn zn); intros Hbeq; simpl;
      rewrite IHl1; reflexivity.
Qed.

Lemma is_in_FOvar_rename : forall l x y,
  ~ x = y ->
  is_in_FOvar x (rename_FOv_list l x y) = false.
Proof.
  induction l; intros [xn] [ym] Hneq.
    reflexivity.

    simpl. destruct a as [zn].
    pose proof Hneq as Hneq'.
    apply FOvar_neq in Hneq.
    case_eq (beq_nat xn zn); intros Hbeq. simpl.
      rewrite Hneq. apply IHl. assumption.

      simpl. rewrite Hbeq. apply IHl.
      assumption.
Qed.

Lemma rename_FOv_list_refl : forall l x,
  rename_FOv_list l x x = l.
Proof.
  induction l; intros [xn].
    reflexivity.

    destruct a as [ym].
    simpl.
    case_eq (beq_nat xn ym); intros Hbeq.
      rewrite IHl. rewrite (beq_nat_true _ _ Hbeq).
      reflexivity.

      rewrite IHl. reflexivity.
Qed.

Fixpoint FOvars_in alpha : list FOvariable :=
  match alpha with
    predSO P x => cons x nil
  | relatSO x y => cons x (cons y nil)
  | eqFO x y => cons x (cons y nil)
  | allFO x beta => cons x (FOvars_in beta)
  | exFO x beta => cons x (FOvars_in beta)
  | negSO beta => FOvars_in beta
  | conjSO beta1 beta2 => app (FOvars_in beta1) (FOvars_in beta2)
  | disjSO beta1 beta2 => app (FOvars_in beta1) (FOvars_in beta2)
  | implSO beta1 beta2 => app (FOvars_in beta1) (FOvars_in beta2)
  | allSO P beta => FOvars_in beta
  | exSO P beta => FOvars_in beta
  end.

Lemma hmm1 : forall alpha xn ym,
 (FOvars_in (rename_FOv_n alpha xn ym)) =
  rename_FOv_list (FOvars_in alpha) (Var xn) (Var ym).
Proof.  
  induction alpha; intros xn ym.
    destruct p; destruct f as [zn]. simpl.
    case_eq (beq_nat xn zn); intros Hbeq;
       reflexivity.

    destruct f as [z1]; destruct f0 as [z2].
    simpl. case_eq (beq_nat xn z1); intros Hbeq1;
      case_eq (beq_nat xn z2); intros Hbeq2;
        reflexivity.

    destruct f as [z1]; destruct f0 as [z2].
    simpl. case_eq (beq_nat xn z1); intros Hbeq1;
      case_eq (beq_nat xn z2); intros Hbeq2;
        reflexivity.

    destruct f as [zn]. simpl.
    rewrite (beq_nat_comm zn xn).
    case_eq (beq_nat xn zn); intros Hbeq;
      simpl; rewrite IHalpha;
      reflexivity.

    destruct f as [zn]. simpl.
    rewrite (beq_nat_comm zn xn).
    case_eq (beq_nat xn zn); intros Hbeq;
      simpl; rewrite IHalpha;
      reflexivity.

    simpl in *. apply IHalpha.

    simpl. rewrite IHalpha1.
    rewrite IHalpha2. rewrite rename_FOv_list_app.
    reflexivity.

    simpl. rewrite IHalpha1.
    rewrite IHalpha2. rewrite rename_FOv_list_app.
    reflexivity.

    simpl. rewrite IHalpha1.
    rewrite IHalpha2. rewrite rename_FOv_list_app.
    reflexivity.

    simpl in *. apply IHalpha.

    simpl in *. apply IHalpha.
Qed.

Definition closed_except (alpha : SecOrder) (x : FOvariable) : Prop :=
  free_FO alpha x = true /\
  forall y, ~ x = y -> free_FO alpha y = false.

Lemma hopeful4 : forall alpha x y W Iv Ip Ir d,
  x_occ_in_alpha alpha y = false ->
  SOturnst W (altered_Iv Iv d y) Ip Ir (rename_FOv alpha x y) <->
  SOturnst W (altered_Iv Iv d x) Ip Ir alpha.
Proof.
  induction alpha; intros [xn] [ym] W Iv Ip Ir d Hocc.
    destruct p; destruct f as [zn].
    simpl. case_eq (beq_nat xn zn);
      intros Hbeq; simpl. rewrite <- beq_nat_refl.
      apply iff_refl.
      simpl in Hocc. rewrite Hocc.
      apply iff_refl.

    destruct f as [z1]; destruct f0 as [z2].
    simpl rename_FOv.
    simpl in Hocc.
    case_eq (beq_nat ym z1); intros Hbeq;
      rewrite Hbeq in *. discriminate.
    case_eq (beq_nat xn z1); intros Hbeq3.
      rewrite (beq_nat_true _  _ Hbeq3).
      case_eq (beq_nat z1 z2); intros Hbeq2.
        rewrite (beq_nat_true _ _ Hbeq2).
        simpl. do 2 rewrite <- beq_nat_refl.
        apply iff_refl.

        simpl. rewrite <- beq_nat_refl.
        rewrite Hbeq2. rewrite Hocc.
        rewrite <- beq_nat_refl. apply iff_refl.

      case_eq (beq_nat xn z2); intros Hbeq2.
        rewrite (beq_nat_true _ _ Hbeq2).
        simpl. rewrite Hbeq. 
        do 2 rewrite <- beq_nat_refl.
        rewrite <- (beq_nat_true _ _ Hbeq2).
        rewrite Hbeq3. apply iff_refl.

        simpl. rewrite Hocc. rewrite Hbeq.
        rewrite Hbeq2. rewrite Hbeq3.
        apply iff_refl.

    destruct f as [z1]; destruct f0 as [z2].
    simpl rename_FOv.
    simpl in Hocc.
    case_eq (beq_nat ym z1); intros Hbeq;
      rewrite Hbeq in *. discriminate.
    case_eq (beq_nat xn z1); intros Hbeq3.
      rewrite (beq_nat_true _  _ Hbeq3).
      case_eq (beq_nat z1 z2); intros Hbeq2.
        rewrite (beq_nat_true _ _ Hbeq2).
        simpl. do 2 rewrite <- beq_nat_refl.
        apply iff_refl.

        simpl. rewrite <- beq_nat_refl.
        rewrite Hbeq2. rewrite Hocc.
        rewrite <- beq_nat_refl. apply iff_refl.

      case_eq (beq_nat xn z2); intros Hbeq2.
        rewrite (beq_nat_true _ _ Hbeq2).
        simpl. rewrite Hbeq. 
        do 2 rewrite <- beq_nat_refl.
        rewrite <- (beq_nat_true _ _ Hbeq2).
        rewrite Hbeq3. apply iff_refl.

        simpl. rewrite Hocc. rewrite Hbeq.
        rewrite Hbeq2. rewrite Hbeq3.
        apply iff_refl.

    destruct f as [zn]. simpl in Hocc.
    case_eq (beq_nat ym zn); intros Hbeq; 
      rewrite Hbeq in *. discriminate.
    simpl rename_FOv.
    case_eq (beq_nat zn xn); intros Hbeq2.
      split ;intros SOt d2;
        specialize (SOt d2);
        rewrite (beq_nat_true _ _ Hbeq2) in *;
        rewrite altered_Iv_eq in *;
        apply (IHalpha (Var xn) (Var ym) W _ Ip Ir d2 Hocc);
        apply SOt.

      assert (~Var ym = Var zn) as Hneq.
        intros H. inversion H as [H'].
        rewrite H' in Hbeq. rewrite <- beq_nat_refl in Hbeq.
        discriminate.
      assert (~Var xn = Var zn) as Hneq2.
        intros H. inversion H as [H'].
        rewrite H' in Hbeq2. rewrite <- beq_nat_refl in Hbeq2.
        discriminate.
      split; intros SOt d2; specialize (SOt d2);
        rewrite altered_Iv_switch in *.
        apply (IHalpha (Var xn) (Var ym) W _ Ip Ir _ Hocc).
        all : try assumption. 

        apply beq_nat_false in Hbeq.
        apply (IHalpha (Var xn) (Var ym) W _ Ip Ir _ Hocc).
        assumption.

    destruct f as [zn]. simpl in Hocc.
    case_eq (beq_nat ym zn); intros Hbeq; 
      rewrite Hbeq in *. discriminate.
    simpl rename_FOv.
    case_eq (beq_nat zn xn); intros Hbeq2.
      split ;intros SOt; destruct SOt as [d2 SOt];
        exists d2;
        rewrite (beq_nat_true _ _ Hbeq2) in *;
        rewrite altered_Iv_eq in *;
        apply (IHalpha (Var xn) (Var ym) W _ Ip Ir d2 Hocc);
        apply SOt.

      assert (~Var ym = Var zn) as Hneq.
        intros H. inversion H as [H'].
        rewrite H' in Hbeq. rewrite <- beq_nat_refl in Hbeq.
        discriminate.
      assert (~Var xn = Var zn) as Hneq2.
        intros H. inversion H as [H'].
        rewrite H' in Hbeq2. rewrite <- beq_nat_refl in Hbeq2.
        discriminate.
      split; intros SOt; destruct SOt as [d2 SOt];
        exists d2;
        rewrite altered_Iv_switch in *.
        apply (IHalpha (Var xn) (Var ym) W _ Ip Ir _ Hocc).
        all : try assumption. 

        apply beq_nat_false in Hbeq.
        apply (IHalpha (Var xn) (Var ym) W _ Ip Ir _ Hocc).
        assumption.

    rewrite rename_FOv_negSO.
    do 2 rewrite SOturnst_negSO.
    split; intros SOt H; apply SOt;
      apply (IHalpha (Var xn) (Var ym) W Iv Ip Ir d); assumption.

    rewrite rename_FOv_conjSO.
    do 2 rewrite SOturnst_conjSO.
    destruct (x_occ_in_alpha_conjSO _ _ _ Hocc) as [H1 H2].
    split; intros [SOt1 SOt2]; apply conj.
      apply (IHalpha1 (Var xn) (Var ym) W Iv Ip Ir d); assumption.
      apply (IHalpha2 (Var xn) (Var ym) W Iv Ip Ir d); assumption.
      apply (IHalpha1 (Var xn) (Var ym) W Iv Ip Ir d); assumption.
      apply (IHalpha2 (Var xn) (Var ym) W Iv Ip Ir d); assumption.

    rewrite rename_FOv_disjSO.
    do 2 rewrite SOturnst_disjSO.
    destruct (x_occ_in_alpha_conjSO _ _ _ Hocc) as [H1 H2].
    split; (intros [SOt1 | SOt2]; [left | right]).
      apply (IHalpha1 (Var xn) (Var ym) W Iv Ip Ir d); assumption.
      apply (IHalpha2 (Var xn) (Var ym) W Iv Ip Ir d); assumption.
      apply (IHalpha1 (Var xn) (Var ym) W Iv Ip Ir d); assumption.
      apply (IHalpha2 (Var xn) (Var ym) W Iv Ip Ir d); assumption.

    rewrite rename_FOv_implSO.
    do 2 rewrite SOturnst_implSO.
    destruct (x_occ_in_alpha_conjSO _ _ _ Hocc) as [H1 H2].
    split; intros SOt1 SOt2. 
      apply (IHalpha2 (Var xn) (Var ym) W Iv Ip Ir d); try assumption.
      apply SOt1.
      apply (IHalpha1 (Var xn) (Var ym) W Iv Ip Ir d); assumption.
      apply (IHalpha2 (Var xn) (Var ym) W Iv Ip Ir d); try assumption.
      apply SOt1.
      apply (IHalpha1 (Var xn) (Var ym) W Iv Ip Ir d); assumption.

    destruct p. simpl in Hocc.
    split; intros SOt pa;
      specialize (SOt pa);
      apply (IHalpha (Var xn) (Var ym) W Iv _ Ir d); assumption.

    destruct p. simpl in Hocc.
    split; intros [pa SOt]; exists pa;
      apply (IHalpha (Var xn) (Var ym) W Iv _ Ir d); assumption.
Qed.

Lemma hopeful3_allFO : forall alpha x y W Iv Ip Ir,
  x_occ_in_alpha alpha y = false ->
  SOturnst W Iv Ip Ir (rename_FOv (allFO x alpha) x y) <->
  SOturnst W Iv Ip Ir (allFO x alpha).
Proof.
  intros alpha [xn] [ym] W Iv Ip Ir Hocc.
  simpl rename_FOv. rewrite <- beq_nat_refl.
  do 2 rewrite SOturnst_allFO.
  split; intros SOt d; specialize (SOt d);
    apply (hopeful4 _ (Var xn) (Var ym));
    assumption.
Qed. 

Lemma hopeful3_exFO : forall alpha x y W Iv Ip Ir,
  x_occ_in_alpha alpha y = false ->
  SOturnst W Iv Ip Ir (rename_FOv (exFO x alpha) x y) <->
  SOturnst W Iv Ip Ir (exFO x alpha).
Proof.
  intros alpha [xn] [ym] W Iv Ip Ir Hocc.
  simpl rename_FOv. rewrite <- beq_nat_refl.
  do 2 rewrite SOturnst_exFO.
  split; intros [d SOt]; exists d;
    apply (hopeful4 _ (Var xn) (Var ym));
    assumption.
Qed.

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

Fixpoint rev_seq start length : list nat :=
  match length with
  | 0 => nil
  | S n => cons (start + n) (rev_seq start n)
  end.

Fixpoint newnew_pre alpha lv ln : SecOrder :=
  match lv, ln with
  | nil, _ => alpha
  | _, nil => alpha
  | cons x lv', cons n ln' =>
    rename_FOv (newnew_pre alpha lv' ln') x (Var n)
  end.

Fixpoint rem_FOv l x :=
  match l with
  | nil => nil
  | cons y l' => match x, y with Var xn, Var ym =>
    if beq_nat xn ym then rem_FOv l' x else cons y (rem_FOv l' x)
  end end.

Lemma x_occ_in_rename_FOv : forall alpha x y,
  ~ x = y ->
  x_occ_in_alpha (rename_FOv alpha x y) x = false.
Proof.
  induction alpha; intros [xn] [ym] Heq.
    destruct f as [zn].
    simpl. case_eq (beq_nat xn zn); intros Hbeq.
    simpl.  apply neq_beq_nat_FOv. assumption.

    simpl. assumption.

    destruct f as [z1]; destruct f0 as [z2].
    simpl. case_eq (beq_nat xn z1); intros H1.
      case_eq (beq_nat xn z2); intros H2;
        simpl; rewrite neq_beq_nat_FOv. reflexivity.
        all : try assumption.

      case_eq (beq_nat xn z2); intros H2;
        simpl; rewrite neq_beq_nat_FOv.
        apply neq_beq_nat_FOv. assumption.
        apply beq_nat_false_FOv. all : try assumption.
        apply beq_nat_false_FOv. all : try assumption.

    destruct f as [z1]; destruct f0 as [z2].
    simpl. case_eq (beq_nat xn z1); intros H1.
      case_eq (beq_nat xn z2); intros H2;
        simpl; rewrite neq_beq_nat_FOv. reflexivity.
        all : try assumption.

      case_eq (beq_nat xn z2); intros H2;
        simpl; rewrite neq_beq_nat_FOv.
        apply neq_beq_nat_FOv. assumption.
        apply beq_nat_false_FOv. all : try assumption.
        apply beq_nat_false_FOv. all : try assumption.

    destruct f as [zn]. simpl. case_eq (beq_nat zn xn); intros Hbeq;
      simpl. rewrite neq_beq_nat_FOv.
      apply (IHalpha (Var xn) (Var ym)).
      all : try assumption.

      rewrite beq_nat_comm. rewrite Hbeq.
      apply (IHalpha (Var xn) (Var ym)).
      assumption.

    destruct f as [zn]. simpl. case_eq (beq_nat zn xn); intros Hbeq;
      simpl. rewrite neq_beq_nat_FOv.
      apply (IHalpha (Var xn) (Var ym)).
      all : try assumption.

      rewrite beq_nat_comm. rewrite Hbeq.
      apply (IHalpha (Var xn) (Var ym)).
      assumption.

    simpl. apply (IHalpha (Var xn) (Var ym)). assumption.

    simpl. unfold rename_FOv in *.
    specialize (IHalpha1 (Var xn) (Var ym) Heq).
    specialize (IHalpha2 (Var xn) (Var ym) Heq).
    rewrite IHalpha1. apply IHalpha2.

    simpl. unfold rename_FOv in *.
    specialize (IHalpha1 (Var xn) (Var ym) Heq).
    specialize (IHalpha2 (Var xn) (Var ym) Heq).
    rewrite IHalpha1. apply IHalpha2.

    simpl. unfold rename_FOv in *.
    specialize (IHalpha1 (Var xn) (Var ym) Heq).
    specialize (IHalpha2 (Var xn) (Var ym) Heq).
    rewrite IHalpha1. apply IHalpha2.

    simpl. apply (IHalpha (Var xn) (Var ym)). assumption.

    simpl. apply (IHalpha (Var xn) (Var ym)). assumption.
Qed.

Lemma x_occ_in_free_FO : forall alpha x,
  x_occ_in_alpha alpha x = false ->
  free_FO alpha x = false.
Proof.
  induction alpha; intros [xn] Hocc.
    destruct f as [ym]. assumption.

    destruct f as [y1]; destruct f0 as [y2].
    assumption.

    destruct f as [y1]; destruct f0 as [y2].
    assumption.

    destruct f as [ym]. simpl in *.
    case_eq (beq_nat xn ym); intros Hbeq.
      reflexivity.

      apply IHalpha. rewrite Hbeq in Hocc.
      assumption.

    destruct f as [ym]. simpl in *.
    case_eq (beq_nat xn ym); intros Hbeq.
      reflexivity.

      apply IHalpha. rewrite Hbeq in Hocc.
      assumption.

    simpl in *. apply IHalpha.
    assumption.

    destruct (x_occ_in_alpha_conjSO _ _ _ Hocc).
    simpl. rewrite IHalpha1. apply IHalpha2.
    all : try assumption.

    destruct (x_occ_in_alpha_conjSO _ _ _ Hocc).
    simpl. rewrite IHalpha1. apply IHalpha2.
    all : try assumption.

    destruct (x_occ_in_alpha_conjSO _ _ _ Hocc).
    simpl. rewrite IHalpha1. apply IHalpha2.
    all : try assumption.

    simpl in *. apply IHalpha. assumption.

    simpl in *. apply IHalpha. assumption.
Qed.

Lemma free_FO_rename_FOv_same : forall alpha x y,
  ~ x = y ->
  free_FO (rename_FOv alpha x y) x = false.
Proof.
  intros.
  apply x_occ_in_free_FO.
  apply x_occ_in_rename_FOv.
  assumption.
Qed.

Lemma rename_FOv_not_occ : forall alpha x y,
  x_occ_in_alpha alpha x = false ->
  rename_FOv alpha x y = alpha.
Proof.
  induction alpha; intros [xn] [ym] Hocc.
    destruct p; destruct f. simpl in *.
    rewrite Hocc. reflexivity.

    destruct f as [z1]; destruct f0 as [z2].
    simpl in *. case_eq (beq_nat xn z1); intros Hbeq;
      rewrite Hbeq in *. discriminate.
    rewrite Hocc. reflexivity.

    destruct f as [z1]; destruct f0 as [z2].
    simpl in *. case_eq (beq_nat xn z1); intros Hbeq;
      rewrite Hbeq in *. discriminate.
    rewrite Hocc. reflexivity.

    destruct f as [zn]. simpl in *.
    case_eq (beq_nat xn zn); intros Hbeq;
      rewrite Hbeq in *. discriminate.
    rewrite beq_nat_comm. rewrite Hbeq.
    unfold rename_FOv in *.
    rewrite (IHalpha (Var xn) (Var ym)).
    reflexivity. assumption.

    destruct f as [zn]. simpl in *.
    case_eq (beq_nat xn zn); intros Hbeq;
      rewrite Hbeq in *. discriminate.
    rewrite beq_nat_comm. rewrite Hbeq.
    unfold rename_FOv in *.
    rewrite (IHalpha (Var xn) (Var ym)).
    reflexivity. assumption.

    simpl in *. unfold rename_FOv in *.
    rewrite (IHalpha (Var xn) (Var ym)). 
    reflexivity. assumption.

    apply x_occ_in_alpha_conjSO in Hocc.
    unfold rename_FOv in *. simpl.
    rewrite (IHalpha1 (Var xn) (Var ym)). 
    rewrite (IHalpha2 (Var xn) (Var ym)).
    reflexivity. all : try apply Hocc.

    apply x_occ_in_alpha_conjSO in Hocc.
    unfold rename_FOv in *. simpl.
    rewrite (IHalpha1 (Var xn) (Var ym)). 
    rewrite (IHalpha2 (Var xn) (Var ym)).
    reflexivity. all : try apply Hocc.

    apply x_occ_in_alpha_conjSO in Hocc.
    unfold rename_FOv in *. simpl.
    rewrite (IHalpha1 (Var xn) (Var ym)). 
    rewrite (IHalpha2 (Var xn) (Var ym)).
    reflexivity. all : try apply Hocc.

    simpl in *. unfold rename_FOv in *.
    rewrite (IHalpha (Var xn) (Var ym)). 
    reflexivity. assumption.

    simpl in *. unfold rename_FOv in *.
    rewrite (IHalpha (Var xn) (Var ym)). 
    reflexivity. assumption.
Qed.

Lemma max_FOv_rename_FOv2 : forall alpha x ym,
  x_occ_in_alpha alpha x = true ->
  Nat.leb (max_FOv (rename_FOv alpha x (Var ym)))
          (max (max_FOv alpha) ym) = true.
Proof.
  induction alpha; intros [xn] ym Hocc.
    simpl in *. destruct f as [zn].
    case_eq (beq_nat xn zn); intros Hbeq;
      simpl. rewrite max_comm.
      apply leb_max_suc3. apply leb_refl.

      apply leb_max_suc3. apply leb_refl.


    destruct f as [z1]; destruct f0 as [z2].
    simpl in *. case_eq (beq_nat xn z1); intros Hbeq;
      rewrite Hbeq in *;
      case_eq (beq_nat xn z2); intros Hbeq2;
        simpl. rewrite max_refl.
        rewrite max_comm.
        apply leb_max_suc3. apply leb_refl.

        rewrite (max_comm z1 z2).
        rewrite (max_comm _ ym).
        rewrite PeanoNat.Nat.max_assoc.
        apply leb_max_suc3. apply leb_refl.

        rewrite (max_comm (max z1 z2) ym).
        rewrite PeanoNat.Nat.max_assoc.
        rewrite (max_comm z1 ym).
        apply leb_max_suc3. apply leb_refl.

        apply leb_max_suc3. apply leb_refl.

    destruct f as [z1]; destruct f0 as [z2].
    simpl in *. case_eq (beq_nat xn z1); intros Hbeq;
      rewrite Hbeq in *;
      case_eq (beq_nat xn z2); intros Hbeq2;
        simpl. rewrite max_refl.
        rewrite max_comm.
        apply leb_max_suc3. apply leb_refl.

        rewrite (max_comm z1 z2).
        rewrite (max_comm _ ym).
        rewrite PeanoNat.Nat.max_assoc.
        apply leb_max_suc3. apply leb_refl.

        rewrite (max_comm (max z1 z2) ym).
        rewrite PeanoNat.Nat.max_assoc.
        rewrite (max_comm z1 ym).
        apply leb_max_suc3. apply leb_refl.

        apply leb_max_suc3. apply leb_refl.

    destruct f as [zn]. simpl in *.
    rewrite beq_nat_comm.
    case_eq (beq_nat xn zn); intros Hbeq;
      rewrite Hbeq in *.  
      case_eq (x_occ_in_alpha alpha (Var xn)); intros Hocc2.
        simpl.
        destruct (max_or ym (max_FOv (rename_FOv_n alpha xn ym)))
          as [H | H]; rewrite H.
          rewrite max_comm.
          apply leb_max_suc3. apply leb_refl.

          rewrite <-  PeanoNat.Nat.max_assoc.
          rewrite max_comm.
          apply leb_max_suc3. apply (IHalpha (Var xn)).
          assumption.

          simpl. rewrite <- rename_FOv__n.
          rewrite (rename_FOv_not_occ).
            rewrite <- PeanoNat.Nat.max_assoc.
            rewrite max_comm. rewrite (max_comm zn _).
            apply leb_max_suc3. apply leb_refl.
            assumption.

        simpl.
        destruct (max_or zn (max_FOv (rename_FOv_n alpha xn ym)))
          as [H | H]; rewrite H.
          rewrite <- PeanoNat.Nat.max_assoc.
          apply leb_max_suc3. apply leb_refl.

          rewrite <- PeanoNat.Nat.max_assoc.
          rewrite max_comm.
          apply leb_max_suc3.
          apply (IHalpha (Var xn)).
          assumption.

    destruct f as [zn]. simpl in *.
    rewrite beq_nat_comm.
    case_eq (beq_nat xn zn); intros Hbeq;
      rewrite Hbeq in *.  
      case_eq (x_occ_in_alpha alpha (Var xn)); intros Hocc2.
        simpl.
        destruct (max_or ym (max_FOv (rename_FOv_n alpha xn ym)))
          as [H | H]; rewrite H.
          rewrite max_comm.
          apply leb_max_suc3. apply leb_refl.

          rewrite <-  PeanoNat.Nat.max_assoc.
          rewrite max_comm.
          apply leb_max_suc3. apply (IHalpha (Var xn)).
          assumption.

          simpl. rewrite <- rename_FOv__n.
          rewrite (rename_FOv_not_occ).
            rewrite <- PeanoNat.Nat.max_assoc.
            rewrite max_comm. rewrite (max_comm zn _).
            apply leb_max_suc3. apply leb_refl.
            assumption.

        simpl.
        destruct (max_or zn (max_FOv (rename_FOv_n alpha xn ym)))
          as [H | H]; rewrite H.
          rewrite <- PeanoNat.Nat.max_assoc.
          apply leb_max_suc3. apply leb_refl.

          rewrite <- PeanoNat.Nat.max_assoc.
          rewrite max_comm.
          apply leb_max_suc3.
          apply (IHalpha (Var xn)).
          assumption.

    simpl in *. apply (IHalpha (Var xn)). assumption.

    simpl in Hocc.
    case_eq (x_occ_in_alpha alpha1 (Var xn)); intros Hocc1;
      rewrite Hocc1 in *.
      simpl.
      case_eq (x_occ_in_alpha alpha2 (Var xn)); intros Hocc2.
        rewrite max_max.
        apply leb_max_max_gen.
          apply (IHalpha1 (Var xn)). assumption.

          apply (IHalpha2 (Var xn)). assumption.

        rewrite <- rename_FOv__n with (alpha := alpha2).
        rewrite (rename_FOv_not_occ alpha2 (Var xn)).
        rewrite (max_comm _ ym).
        rewrite PeanoNat.Nat.max_assoc.
        rewrite (max_comm ym _).
        apply leb_max_max_gen.
          apply (IHalpha1 (Var xn)). assumption.
          apply leb_refl. assumption.

      simpl.
      rewrite <- rename_FOv__n with (alpha := alpha1).
      rewrite (rename_FOv_not_occ alpha1 (Var xn)).
      rewrite <- PeanoNat.Nat.max_assoc.
      apply leb_max_max_gen.
        apply leb_refl.
        apply (IHalpha2 (Var xn)). all : try assumption.

    simpl in Hocc.
    case_eq (x_occ_in_alpha alpha1 (Var xn)); intros Hocc1;
      rewrite Hocc1 in *.
      simpl.
      case_eq (x_occ_in_alpha alpha2 (Var xn)); intros Hocc2.
        rewrite max_max.
        apply leb_max_max_gen.
          apply (IHalpha1 (Var xn)). assumption.

          apply (IHalpha2 (Var xn)). assumption.

        rewrite <- rename_FOv__n with (alpha := alpha2).
        rewrite (rename_FOv_not_occ alpha2 (Var xn)).
        rewrite (max_comm _ ym).
        rewrite PeanoNat.Nat.max_assoc.
        rewrite (max_comm ym _).
        apply leb_max_max_gen.
          apply (IHalpha1 (Var xn)). assumption.
          apply leb_refl. assumption.

      simpl.
      rewrite <- rename_FOv__n with (alpha := alpha1).
      rewrite (rename_FOv_not_occ alpha1 (Var xn)).
      rewrite <- PeanoNat.Nat.max_assoc.
      apply leb_max_max_gen.
        apply leb_refl.
        apply (IHalpha2 (Var xn)). all : try assumption.

    simpl in Hocc.
    case_eq (x_occ_in_alpha alpha1 (Var xn)); intros Hocc1;
      rewrite Hocc1 in *.
      simpl.
      case_eq (x_occ_in_alpha alpha2 (Var xn)); intros Hocc2.
        rewrite max_max.
        apply leb_max_max_gen.
          apply (IHalpha1 (Var xn)). assumption.

          apply (IHalpha2 (Var xn)). assumption.

        rewrite <- rename_FOv__n with (alpha := alpha2).
        rewrite (rename_FOv_not_occ alpha2 (Var xn)).
        rewrite (max_comm _ ym).
        rewrite PeanoNat.Nat.max_assoc.
        rewrite (max_comm ym _).
        apply leb_max_max_gen.
          apply (IHalpha1 (Var xn)). assumption.
          apply leb_refl. assumption.

      simpl.
      rewrite <- rename_FOv__n with (alpha := alpha1).
      rewrite (rename_FOv_not_occ alpha1 (Var xn)).
      rewrite <- PeanoNat.Nat.max_assoc.
      apply leb_max_max_gen.
        apply leb_refl.
        apply (IHalpha2 (Var xn)). all : try assumption.

    simpl in *. apply (IHalpha (Var xn)). assumption.

    simpl in *. apply (IHalpha (Var xn)). assumption.
Qed.

Lemma free_FO_rename_FOv2 : forall alpha x y,
  free_FO alpha x = false ->
  free_FO alpha y = false ->
  free_FO (rename_FOv alpha x y) y = false.
Proof.
  induction alpha; intros [xn] [ym] H1 H2.
    destruct p; destruct f as [zn].
    simpl in *.
    rewrite H1. simpl. apply H2.

    destruct f as [z1]; destruct f0 as [z2].
    simpl in *. case_eq (beq_nat xn z1); intros Hbeq;
      rewrite Hbeq in *. discriminate.
    case_eq (beq_nat xn z2); intros Hbeq2;
      rewrite Hbeq2 in *. discriminate.
    simpl in *. case_eq (beq_nat ym z1); intros Hbeq3;
      rewrite Hbeq3 in *. discriminate.
    case_eq (beq_nat ym z2); intros Hbeq4;
      rewrite Hbeq4 in *. discriminate.
    reflexivity.

    destruct f as [z1]; destruct f0 as [z2].
    simpl in *. case_eq (beq_nat xn z1); intros Hbeq;
      rewrite Hbeq in *. discriminate.
    case_eq (beq_nat xn z2); intros Hbeq2;
      rewrite Hbeq2 in *. discriminate.
    simpl in *. case_eq (beq_nat ym z1); intros Hbeq3;
      rewrite Hbeq3 in *. discriminate.
    case_eq (beq_nat ym z2); intros Hbeq4;
      rewrite Hbeq4 in *. discriminate.
    reflexivity.

    destruct f as [zn]. simpl in *. 
    rewrite beq_nat_comm.
    case_eq (beq_nat xn zn); intros Hbeq;
      rewrite Hbeq in *.
      simpl. rewrite <- beq_nat_refl.
      reflexivity.

      simpl. case_eq (beq_nat ym zn) ;intros Hbeq2;
      rewrite Hbeq2 in *. reflexivity.    
        apply (IHalpha (Var xn) (Var ym));  
        assumption.

    destruct f as [zn]. simpl in *. 
    rewrite beq_nat_comm.
    case_eq (beq_nat xn zn); intros Hbeq;
      rewrite Hbeq in *.
      simpl. rewrite <- beq_nat_refl.
      reflexivity.

      simpl. case_eq (beq_nat ym zn) ;intros Hbeq2;
      rewrite Hbeq2 in *. reflexivity.    
        apply (IHalpha (Var xn) (Var ym));  
        assumption.

    simpl in *. 
    apply (IHalpha (Var xn) (Var ym));
    assumption.

    simpl in *. case_eq (free_FO alpha1 (Var xn));
      intros H3; rewrite H3 in *. discriminate.
    case_eq (free_FO alpha2 (Var xn)); intros H4;
      rewrite H4 in *. discriminate.
    simpl in *. case_eq (free_FO alpha1 (Var ym));
      intros H5; rewrite H5 in *. discriminate.
    case_eq (free_FO alpha2 (Var ym)); intros H6;
      rewrite H6 in *. discriminate.
    unfold rename_FOv in *.
    rewrite (IHalpha1 (Var xn) (Var ym)).
    apply (IHalpha2 (Var xn) (Var ym)).
    all : try assumption.

    simpl in *. case_eq (free_FO alpha1 (Var xn));
      intros H3; rewrite H3 in *. discriminate.
    case_eq (free_FO alpha2 (Var xn)); intros H4;
      rewrite H4 in *. discriminate.
    simpl in *. case_eq (free_FO alpha1 (Var ym));
      intros H5; rewrite H5 in *. discriminate.
    case_eq (free_FO alpha2 (Var ym)); intros H6;
      rewrite H6 in *. discriminate.
    unfold rename_FOv in *.
    rewrite (IHalpha1 (Var xn) (Var ym)).
    apply (IHalpha2 (Var xn) (Var ym)).
    all : try assumption.

    simpl in *. case_eq (free_FO alpha1 (Var xn));
      intros H3; rewrite H3 in *. discriminate.
    case_eq (free_FO alpha2 (Var xn)); intros H4;
      rewrite H4 in *. discriminate.
    simpl in *. case_eq (free_FO alpha1 (Var ym));
      intros H5; rewrite H5 in *. discriminate.
    case_eq (free_FO alpha2 (Var ym)); intros H6;
      rewrite H6 in *. discriminate.
    unfold rename_FOv in *.
    rewrite (IHalpha1 (Var xn) (Var ym)).
    apply (IHalpha2 (Var xn) (Var ym)).
    all : try assumption.

    simpl in *. 
    apply (IHalpha (Var xn) (Var ym));
    assumption.

    simpl in *. 
    apply (IHalpha (Var xn) (Var ym));
    assumption.
Qed.

Fixpoint is_in_FOvar_l l1 l2 : bool :=
  match l1 with
  | nil => true
  | cons x l1' => 
      if is_in_FOvar x l2 then is_in_FOvar_l l1' l2 else false
  end.

Lemma is_in__FOvar : forall l1 l2 x,
  is_in_FOvar_l l1 l2 = true ->
  is_in_FOvar x l1 = true ->
  is_in_FOvar x l2 = true.
Proof.
  induction l1; intros l2 [xn] H1 H2.
    simpl in *. discriminate.

    simpl in *. destruct a as [ym].
    case_eq (is_in_FOvar (Var ym) l2); intros H3;
      rewrite H3 in H1. 2 : discriminate.
    case_eq (beq_nat xn ym); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq) in *. assumption.
    rewrite Hbeq in H2. apply IHl1; assumption.
Qed.

Lemma att_allFO_instant_cons_empty'_pre : forall beta P x y ,
  attached_allFO_x beta y = false ->
attached_allFO_x
  (replace_pred beta P x (negSO (eqFO x x))) y = false.
Proof.
  induction beta; intros [Pn] [ym] [xn] Hat.
    destruct p as [Qm]; destruct f as [zn]. simpl in *.
    rewrite <- beq_nat_refl. case_eq (beq_nat Pn Qm);
      intros Hbeq; reflexivity.

    destruct f as [z1]; destruct f0 as [z2].
    reflexivity.

    destruct f as [z1]; destruct f0 as [z2].
    reflexivity.

    destruct f as [zn]. simpl in *.
    case_eq (beq_nat xn zn); intros Hbeq;
      rewrite Hbeq in *. discriminate.
      apply IHbeta. assumption.

    destruct f as [zn]. simpl in *.
    apply IHbeta. assumption.

    simpl in *. apply IHbeta; assumption.

    simpl in *. case_eq (attached_allFO_x beta1 (Var xn));
      intros H1; rewrite H1 in *. discriminate.
      rewrite IHbeta1. apply IHbeta2. all : try assumption.

    simpl in *. case_eq (attached_allFO_x beta1 (Var xn));
      intros H1; rewrite H1 in *. discriminate.
      rewrite IHbeta1. apply IHbeta2. all : try assumption.

    simpl in *. case_eq (attached_allFO_x beta1 (Var xn));
      intros H1; rewrite H1 in *. discriminate.
      rewrite IHbeta1. apply IHbeta2. all : try assumption.

    destruct p as [Qm]. simpl in *.
    case_eq (beq_nat Pn Qm); intros Hbeq; simpl;
      apply IHbeta; assumption.

    destruct p as [Qm]. simpl in *.
    case_eq (beq_nat Pn Qm); intros Hbeq; simpl;
      apply IHbeta; assumption.
Qed.

Lemma att_allFO_instant_cons_empty'_pre_l : forall l beta x,
  attached_allFO_x beta x = false ->
attached_allFO_x
  (replace_pred_l beta l
     (nlist_list (length l) (nlist_Var1 _))
     (nlist_list (length l) (nlist_empty _))) x = false.
Proof.
  induction l; intros beta x H.
    simpl. assumption.

    simpl. apply att_allFO_instant_cons_empty'_pre.
    apply IHl. assumption.
Qed.

Lemma att_allFO_instant_cons_empty' : forall beta alpha x,
  attached_allFO_x beta x = false ->
  attached_allFO_x (instant_cons_empty' alpha beta) x = false.
Proof.
  intros beta alpha x H.
  unfold instant_cons_empty'.
  apply att_allFO_instant_cons_empty'_pre_l.
  assumption.
Qed.

Lemma instant_cons_empty'_allFO : forall alpha beta y,
  instant_cons_empty' alpha (allFO y beta) = 
  allFO y (instant_cons_empty' alpha beta).
Proof.
  intros.
  unfold instant_cons_empty'.
  rewrite rep_pred_l_allFO.
  reflexivity.
Qed.

Lemma instant_cons_empty'_exFO : forall alpha beta y,
  instant_cons_empty' alpha (exFO y beta) = 
  exFO y (instant_cons_empty' alpha beta).
Proof.
  intros. destruct y.
  unfold instant_cons_empty'.
  rewrite rep_pred_l_exFO.
  reflexivity.
Qed.

Lemma instant_cons_empty'_negSO : forall alpha beta,
  instant_cons_empty' alpha (negSO beta) = 
  negSO (instant_cons_empty' alpha beta).
Proof.
  intros.
  unfold instant_cons_empty'.
  rewrite rep_pred_l_negSO.
  reflexivity.
Qed.

Lemma list_pred_not_in_app : forall l1 l2 l,
  list_pred_not_in l (app l1 l2) =
  app (list_pred_not_in l l1) (list_pred_not_in l l2).
Proof.
  induction l1; intros l2 l.
    reflexivity.

    simpl. case_eq (is_in_pred a l);
      intros Hin. apply IHl1.

      rewrite IHl1. reflexivity.
Qed.

Fixpoint cap_pred_empty l1 l2 : bool :=
  match l1 with
  | nil => true
  | cons P l1' => if is_in_pred P l2 then false
                    else cap_pred_empty l1' l2
  end.

Fixpoint rem_pred l P : list predicate :=
  match l with
  | nil => nil
  | cons Q l' => match P, Q with Pred Pn, Pred Qm =>
      if beq_nat Pn Qm then rem_pred l' P else
        cons Q (rem_pred l' P)
      end
  end.

Lemma list_pred_not_in_rem_pred : forall l2 l P,
  list_pred_not_in (cons P l) l2 =
  rem_pred (list_pred_not_in l l2) P.
Proof.
  induction l2; intros l [Pn].
    reflexivity.

    simpl. destruct a as [Qm].
    case_eq (beq_nat Qm Pn); intros Hbeq;
      case_eq (is_in_pred (Pred Qm) l);
        intros Hin. apply IHl2.

        simpl. rewrite beq_nat_comm.
        rewrite Hbeq.
        apply IHl2.

        apply IHl2.

        simpl. rewrite beq_nat_comm.
        rewrite Hbeq. rewrite IHl2.
        reflexivity.
Qed.

Lemma rem_pred_app : forall l1 l2 P,
  rem_pred (app l1 l2) P =
  app (rem_pred l1 P) (rem_pred l2 P).
Proof.
  induction l1; intros l2 [Pn].
    reflexivity.

    simpl. destruct a as [Qm].
    case_eq (beq_nat Pn Qm); intros Hbeq;
      rewrite IHl1; reflexivity.
Qed.

Lemma jj9 : forall alpha x y z P,
  preds_in (replace_pred alpha P x (negSO (eqFO y z))) =
  rem_pred (preds_in alpha) P.
Proof.
  induction alpha; intros [xn] [ym] [zn] [Pn].
    destruct p as [Qm]; destruct f. simpl.
    case_eq (beq_nat Pn Qm); intros Hbeq.
      simpl. case_eq (beq_nat xn ym);
        case_eq (beq_nat xn zn).
        all : try reflexivity.

    destruct f; destruct f0; reflexivity.

    destruct f; destruct f0; reflexivity.

    destruct f as [u1].
    simpl. apply IHalpha.

    destruct f as [u1].
    simpl. apply IHalpha.

    simpl. apply IHalpha.

    simpl. rewrite IHalpha1.
    rewrite IHalpha2.
    rewrite rem_pred_app. reflexivity.

    simpl. rewrite IHalpha1.
    rewrite IHalpha2.
    rewrite rem_pred_app. reflexivity.

    simpl. rewrite IHalpha1.
    rewrite IHalpha2.
    rewrite rem_pred_app. reflexivity.

    destruct p as [Qm].
    simpl in *. case_eq (beq_nat Pn Qm); intros Hbeq.
      apply IHalpha.

      simpl. rewrite IHalpha. reflexivity.

    destruct p as [Qm].
    simpl in *. case_eq (beq_nat Pn Qm); intros Hbeq.
      apply IHalpha.

      simpl. rewrite IHalpha. reflexivity.
Qed.

Lemma jj8 : forall l beta,
  is_in_pred_l l (preds_in beta) = true ->
  preds_in (replace_pred_l beta l
      (nlist_list _ (nlist_Var1 (length l)))
      (nlist_list _ (nlist_empty (length l)))) =
  list_pred_not_in l (preds_in beta).
Proof.
  induction l; intros beta H.
    simpl in *.
    rewrite list_pred_not_in_nil.
    reflexivity.

    simpl in *.
    case_eq (is_in_pred a (preds_in beta));
      intros H2; rewrite H2 in *.  2 : discriminate.
    rewrite list_pred_not_in_rem_pred.
    rewrite jj9.
    rewrite IHl. reflexivity.
    assumption.
Qed.

Lemma  jj10 : forall l2 l1,
  is_in_pred_l (list_pred_not_in l1 l2) l2 = true.
Proof.
  induction l2; intros l1.
    reflexivity.

    simpl. case_eq (is_in_pred a l1); intros Hin.
      apply is_in_pred_l2.
      apply IHl2.

      destruct a as [Qm].
      simpl. rewrite <- beq_nat_refl.
      apply is_in_pred_l2. apply IHl2.
Qed.

Fixpoint cap_pred l1 l2 :=
  match l1 with
  | nil => nil
  | cons P l1' => if is_in_pred P l2 then cons P (cap_pred l1' l2)
          else cap_pred l1' l2
  end.

Lemma is_in_pred_rem_pred_eq : forall l P,
  is_in_pred P (rem_pred l P) = false.
Proof.
  induction l; intros [Pn].
    reflexivity.

    destruct a as [Qm].
    simpl. case_eq (beq_nat Pn Qm); intros Hbeq.
      apply IHl.

      simpl. rewrite Hbeq. apply IHl.
Qed.

Lemma jj13 : forall l P Q,
  match P, Q with Pred Pn, Pred Qm =>
    beq_nat Pn Qm = false
  end ->
  is_in_pred P (rem_pred l Q) = 
  is_in_pred P l.
Proof.
  induction l; intros [Pn] [Qm] Hbeq.
    reflexivity.

    simpl. destruct a as [Rn].
    case_eq (beq_nat Qm Rn); intros Hbeq2.
      rewrite <- (beq_nat_true _ _ Hbeq2).
      rewrite Hbeq. apply IHl.
      assumption.

      simpl. case_eq (beq_nat Pn Rn); intros Hbeq3.
        reflexivity.
        apply IHl. assumption.
Qed.

Lemma jj12 : forall l1 l2 P,
  is_in_pred P l1 = true ->
  is_in_pred P (list_pred_not_in l1 l2) = false.
Proof.
  induction l1; intros l2 [Pn] H.
    simpl in *. discriminate.

    simpl in *. destruct a as [Qm].
    rewrite list_pred_not_in_rem_pred.
    case_eq (beq_nat Pn Qm); intros Hbeq;
      rewrite Hbeq in *.
      rewrite (beq_nat_true _ _ Hbeq).
      rewrite is_in_pred_rem_pred_eq.
      reflexivity.

      rewrite jj13.
      apply IHl1. all : assumption.
Qed.

Lemma rem_pred_not_in : forall l P,
  is_in_pred P l = false ->
  rem_pred l P = l.
Proof.
  induction l; intros [Pn] H.
    reflexivity.

    destruct a as [Qm]. simpl in *.
    case_eq (beq_nat Pn Qm); intros Hbeq;
      rewrite Hbeq in *. discriminate.
    rewrite IHl. reflexivity.
    assumption.
Qed.

Lemma is_in_cap_pred : forall l2 l1 P,
  is_in_pred P l1 = false ->
  is_in_pred P (cap_pred l2 l1) = false.
Proof.
  induction l2; intros l1 [Pn] H.
    reflexivity.

    simpl. case_eq (is_in_pred a l1); intros H2.
      destruct a as [Qm]. simpl.
      case_eq (beq_nat Pn Qm); intros Hbeq2.
        rewrite (beq_nat_true _ _ Hbeq2) in H.
        rewrite H in H2. discriminate.

        apply IHl2. assumption.

      apply IHl2. assumption.
Qed.

Lemma jj11 : forall l2 l1,
  list_pred_not_in (list_pred_not_in l1 l2) l2 =
  cap_pred l2 l1.
Proof.
  induction l2; intros l1.
    reflexivity.

    simpl. case_eq (is_in_pred a l1); intros H2.
      apply jj12 with (l2 := l2) in H2.
      rewrite H2.
      rewrite IHl2. reflexivity.

      simpl. destruct a as [Pn].
      rewrite <- beq_nat_refl.
      rewrite list_pred_not_in_rem_pred.
      rewrite IHl2.
      apply rem_pred_not_in.
      apply is_in_cap_pred. assumption.
Qed.

Lemma is_in_pred_cap_pred : forall l1 l2 P,
  is_in_pred P l1 = true ->
  is_in_pred P l2 = true ->
  is_in_pred P (cap_pred l1 l2) = true.
Proof.
  induction l1; intros l2 [Pn] H1 H2.
    simpl in *. discriminate.

    destruct a as [Qm].
    simpl in *.
    case_eq (beq_nat Pn Qm); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq) in *.
      rewrite H2.
      simpl. rewrite <- beq_nat_refl.
      reflexivity.

      rewrite Hbeq in H1.
      case_eq (is_in_pred (Pred Qm) l2); intros H3.
        simpl. rewrite Hbeq. apply IHl1; assumption.

        apply IHl1; assumption.
Qed.

Lemma is_in_pred_cap_pred_t : forall l1 l2 P,
  is_in_pred P (cap_pred l1 l2) = true ->
  (is_in_pred P l1 = true /\
  is_in_pred P l2 = true).
Proof.
  induction l1; intros l2 [Pn] H.
    simpl in *. discriminate.

    simpl in *.
    case_eq (is_in_pred a l2); intros H2;
      rewrite H2 in *.
      destruct a as [Qm]. simpl in *.
      case_eq (beq_nat Pn Qm); intros Hbeq;
        rewrite Hbeq in *.
        apply conj. reflexivity.
        rewrite (beq_nat_true _ _ Hbeq).
        assumption.

        apply IHl1.
        assumption.

      destruct a as [Qm].
      case_eq (beq_nat Pn Qm); intros Hbeq.
        apply conj. reflexivity.
        apply IHl1. assumption.

        apply IHl1. assumption.
Qed.

Lemma is_in_pred_cap_pred_f : forall l1 l2 P,
  is_in_pred P (cap_pred l1 l2) = false ->
  is_in_pred P l1 = false \/ is_in_pred P l2 = false.
Proof.
  induction l1; intros l2 [Pn] H.
    simpl in *. left. reflexivity.

    simpl in *. destruct a as [Qm]. 
    case_eq (is_in_pred (Pred Qm) l2); intros H2;
      rewrite H2 in H. simpl in H.
      case_eq (beq_nat Pn Qm); intros Hbeq;
        rewrite Hbeq in *. discriminate.
      apply IHl1. assumption.

      case_eq (beq_nat Pn Qm); intros Hbeq.
        rewrite (beq_nat_true _ _ Hbeq).
        right. assumption.

        apply IHl1. assumption.
Qed.

Lemma is_in_pred_cap_pred_f1 : forall l1 l2 P,
  is_in_pred P l1 = false ->
  is_in_pred P (cap_pred l1 l2) = false.
Proof.
  induction l1; intros l2 [Pn] H.
    simpl in *. reflexivity.

    simpl in *. destruct a as [Qm]. 
    case_eq (is_in_pred (Pred Qm) l2); intros H2.
      simpl.
      case_eq (beq_nat Pn Qm); intros Hbeq;
        rewrite Hbeq in *. discriminate.
      apply IHl1. assumption.

      case_eq (beq_nat Pn Qm); intros Hbeq.
        rewrite Hbeq in *. discriminate.

        rewrite Hbeq in H. apply IHl1.
        assumption.
Qed.

Lemma is_in_pred_cap_pred_f2 : forall l1 l2 P,
  is_in_pred P l2 = false ->
  is_in_pred P (cap_pred l1 l2) = false.
Proof.
  induction l1; intros l2 [Pn] H.
    simpl in *. reflexivity.

    simpl in *. destruct a as [Qm]. 
    case_eq (is_in_pred (Pred Qm) l2); intros H2.
      simpl.
      case_eq (beq_nat Pn Qm); intros Hbeq.
        rewrite (beq_nat_true _ _ Hbeq) in H.
        rewrite H2 in H. discriminate.
      apply IHl1. assumption.

      apply IHl1. assumption.
Qed.

Lemma cap_pred_comm : forall l1 l2 P,
  is_in_pred P (cap_pred l1 l2) =
  is_in_pred P (cap_pred l2 l1).
Proof.
  intros.
  case_eq (is_in_pred P (cap_pred l1 l2));
    intros H.
    apply is_in_pred_cap_pred_t in H.
    destruct H as [H1 H2].
    symmetry. apply is_in_pred_cap_pred;
    assumption.

    apply is_in_pred_cap_pred_f in H.
    destruct H as [H1 | H2].
      symmetry. apply is_in_pred_cap_pred_f2.
      assumption.
      symmetry. apply is_in_pred_cap_pred_f1.
      assumption.
Qed.

Lemma jj7 : forall l beta P,
  is_in_pred P l = false ->
  is_in_pred P (preds_in (replace_pred_l beta 
      (list_pred_not_in l (preds_in beta))
          (nlist_list (length (list_pred_not_in l (preds_in beta)))
             (nlist_Var1 (length (list_pred_not_in l (preds_in beta)))))
          (nlist_list (length (list_pred_not_in l (preds_in beta)))
             (nlist_empty (length (list_pred_not_in l (preds_in beta))))))) = false.
Proof.
  induction l; intros beta [Pn] H.  
    rewrite list_pred_not_in_nil.
    rewrite un_predless_preds_in. assumption.
    apply is_un_predless_rep_pred_l.
    apply un_predless_l_empty_n.

    destruct a as [Qm]. simpl in *.
    case_eq (beq_nat Pn Qm); intros Hbeq; 
      rewrite Hbeq in *. discriminate.

      rewrite jj8. rewrite jj11.
      rewrite cap_pred_comm.
      simpl.
      case_eq (is_in_pred (Pred Qm) (preds_in beta));
        intros H2.
        simpl. rewrite Hbeq.
        apply is_in_pred_cap_pred_f1.
        assumption.

        apply is_in_pred_cap_pred_f1.
        assumption.

    apply jj10.
Qed.

Lemma jj6 : forall lb1 la beta2,
cap_pred_empty (list_pred_not_in la lb1)
  (preds_in
     (replace_pred_l beta2 (list_pred_not_in la (preds_in beta2))
        (nlist_list (length (list_pred_not_in la (preds_in beta2)))
           (nlist_Var1 (length (list_pred_not_in la (preds_in beta2)))))
        (nlist_list (length (list_pred_not_in la (preds_in beta2)))
           (nlist_empty (length (list_pred_not_in la (preds_in beta2))))))) =
true.
Proof.
  induction lb1; intros la beta2.
    reflexivity.

    destruct a as [Pn]. simpl.
    case_eq (is_in_pred (Pred Pn) la); intros Hin.
      apply IHlb1.

      simpl. rewrite IHlb1.
      rewrite jj7. reflexivity.
      assumption.
Qed.

Lemma sumtin : forall l2 lb l beta,
  is_in_pred_l (preds_in beta) lb = true ->
  cap_pred_empty l2 (preds_in (replace_pred_l beta (list_pred_not_in l lb)
      (nlist_list _ (nlist_Var1 (length (list_pred_not_in l lb))))
      (nlist_list _ (nlist_empty (length (list_pred_not_in l lb)))))) = true ->
  replace_pred_l 
    (replace_pred_l beta (list_pred_not_in l lb)
      (nlist_list _ (nlist_Var1 (length (list_pred_not_in l lb))))
      (nlist_list _ (nlist_empty (length (list_pred_not_in l lb)))))
    l2
    (nlist_list (length l2) (nlist_Var1 (length l2)))
    (nlist_list (length l2) (nlist_empty (length l2))) =
    (replace_pred_l beta (list_pred_not_in l lb)
      (nlist_list _ (nlist_Var1 (length (list_pred_not_in l lb))))
      (nlist_list _ (nlist_empty (length (list_pred_not_in l lb))))).
Proof.
  induction l2; intros lb l beta H1 H2.
    simpl in *. reflexivity.

    simpl. destruct a as [Qm].
    simpl in *.
    case_eq (is_in_pred (Pred Qm) 
         (preds_in
            (replace_pred_l beta (list_pred_not_in l lb)
               (nlist_list (length (list_pred_not_in l lb))
                  (nlist_Var1 (length (list_pred_not_in l lb))))
               (nlist_list (length (list_pred_not_in l lb))
                  (nlist_empty (length (list_pred_not_in l lb)))))));
      intros H3; rewrite H3 in *. discriminate.

    rewrite IHl2; try assumption.
    rewrite rep_pred_not_in. reflexivity.
    assumption.
Qed.

Lemma instant_cons_empty'_conjSO : forall alpha beta1 beta2,
  instant_cons_empty' alpha (conjSO beta1 beta2) =
  conjSO (instant_cons_empty' alpha beta1) (instant_cons_empty' alpha beta2).
Proof.
  intros. unfold instant_cons_empty'.
  rewrite rep_pred_l_conjSO. simpl.
  rewrite list_pred_not_in_app.
  do 2 rewrite rep_pred_l_app.
  rewrite rep_pred_l_switch.
  rewrite sumtin.
  rewrite sumtin. reflexivity.

    apply is_in_pred_l_refl.

    apply jj6.
    apply is_in_pred_l_refl.

    apply jj6.
Qed.

Lemma instant_cons_empty'_disjSO : forall alpha beta1 beta2,
  instant_cons_empty' alpha (disjSO beta1 beta2) =
  disjSO (instant_cons_empty' alpha beta1) (instant_cons_empty' alpha beta2).
Proof.
  intros. unfold instant_cons_empty'.
  rewrite rep_pred_l_disjSO. simpl.
  rewrite list_pred_not_in_app.
  do 2 rewrite rep_pred_l_app.
  rewrite rep_pred_l_switch.
  rewrite sumtin.
  rewrite sumtin. reflexivity.

    apply is_in_pred_l_refl.

    apply jj6.
    apply is_in_pred_l_refl.

    apply jj6.
Qed.

Lemma instant_cons_empty'_implSO : forall alpha beta1 beta2,
  instant_cons_empty' alpha (implSO beta1 beta2) =
  implSO (instant_cons_empty' alpha beta1) (instant_cons_empty' alpha beta2).
Proof.
  intros. unfold instant_cons_empty'.
  rewrite rep_pred_l_implSO. simpl.
  rewrite list_pred_not_in_app.
  do 2 rewrite rep_pred_l_app.
  rewrite rep_pred_l_switch.
  rewrite sumtin.
  rewrite sumtin. reflexivity.

    apply is_in_pred_l_refl.

    apply jj6.
    apply is_in_pred_l_refl.

    apply jj6.
Qed.

Lemma free_FO_instant_cons_empty'_f : forall beta alpha y,
  SOQFree beta = true  ->
  free_FO beta y = false ->
  free_FO (instant_cons_empty' alpha beta) y = false.
Proof.
  induction beta; intros alpha [xn] Hno H.
    destruct p as [Pn]; destruct f as [ym].
    simpl in *.
    unfold instant_cons_empty'.
    simpl. case_eq (is_in_pred (Pred Pn) (preds_in alpha));
      intros H2.
      simpl. assumption.
      simpl. rewrite <- beq_nat_refl.
      simpl. rewrite H. reflexivity.

    destruct f as [ym]; destruct f0 as [zn]. simpl in *.
    assumption.

    destruct f as [ym]; destruct f0 as [zn]. simpl in *.
    assumption.

    destruct f as [ym]. simpl in *.
    rewrite instant_cons_empty'_allFO.
    simpl.
    case_eq (beq_nat xn ym); intros Hbeq;
      rewrite Hbeq in *. reflexivity.
      apply IHbeta; assumption.

    destruct f as [ym]. simpl in *.
    rewrite instant_cons_empty'_exFO.
    simpl.
    case_eq (beq_nat xn ym); intros Hbeq;
      rewrite Hbeq in *. reflexivity.
      apply IHbeta; assumption.

    rewrite instant_cons_empty'_negSO.
    simpl in *. apply IHbeta; assumption.

    rewrite instant_cons_empty'_conjSO.
    simpl in *. case_eq (SOQFree beta1);
      intros H2; rewrite H2 in *. 2 : discriminate.
    case_eq (free_FO beta1 (Var xn)); intros H3;
      rewrite H3 in H. discriminate.
    rewrite IHbeta1. apply IHbeta2. all : try assumption.
    reflexivity.

    rewrite instant_cons_empty'_disjSO.
    simpl in *. case_eq (SOQFree beta1);
      intros H2; rewrite H2 in *. 2 : discriminate.
    case_eq (free_FO beta1 (Var xn)); intros H3;
      rewrite H3 in H. discriminate.
    rewrite IHbeta1. apply IHbeta2. all : try assumption.
    reflexivity.

    rewrite instant_cons_empty'_implSO.
    simpl in *. case_eq (SOQFree beta1);
      intros H2; rewrite H2 in *. 2 : discriminate.
    case_eq (free_FO beta1 (Var xn)); intros H3;
      rewrite H3 in H. discriminate.
    rewrite IHbeta1. apply IHbeta2. all : try assumption.
    reflexivity.

    simpl in *. destruct p. discriminate.

    simpl in *. destruct p. discriminate.
Qed.

Fixpoint max_l l : nat :=
  match l with  
  | nil => 0
  | cons n l' => max n (max_l l')
  end.

Fixpoint min_l l : nat :=
  match l with  
  | nil => 0
  | cons n nil => n
  | cons n l' => min n (min_l l')
  end.

Lemma rename_FOv_att_allFO: forall alpha x y z,
  attached_allFO_x alpha x = false ->
  ~z = x ->
  attached_allFO_x (rename_FOv alpha y z) x = false.
Proof.
  induction alpha; intros [xn] [ym] [zn] Hat Hneq.
    simpl in *. destruct f as [un].   
    case_eq (beq_nat ym un); intros Hbeq;
      reflexivity.

    destruct f as [un]. destruct f0 as [wn].
    simpl in *. case_eq (beq_nat ym un); intros Hbeq;
      case_eq (beq_nat ym wn); intros Hbeq2;
        reflexivity.

    destruct f as [un]. destruct f0 as [wn].
    simpl in *. case_eq (beq_nat ym un); intros Hbeq;
      case_eq (beq_nat ym wn); intros Hbeq2;
        reflexivity.

    destruct f as [un]. simpl in *.
    case_eq (beq_nat xn un); intros Hbeq3;
      rewrite Hbeq3 in *. discriminate.
    case_eq (beq_nat un ym); intros Hbeq.
      simpl. rewrite beq_nat_comm.
      rewrite FOvar_neq. unfold rename_FOv in IHalpha.
      apply (IHalpha (Var xn) (Var ym) (Var zn)).
      all : try assumption.

      simpl. rewrite Hbeq3.
      apply (IHalpha (Var xn) (Var ym) (Var zn)); assumption.

    destruct f as [un]. simpl in *.
    case_eq (beq_nat un ym); intros Hbeq.
      simpl.
      apply (IHalpha (Var xn) (Var ym) (Var zn)).
      all : try assumption.

      simpl.
      apply (IHalpha (Var xn) (Var ym) (Var zn)); assumption.

    simpl in *. apply (IHalpha (Var xn) (Var ym) (Var zn)); assumption.

    simpl in *. case_eq (attached_allFO_x alpha1 (Var xn));
      intros Hat2; rewrite Hat2 in *. discriminate.
    unfold rename_FOv in *.
    rewrite (IHalpha1 (Var xn) (Var ym) (Var zn)).
    apply (IHalpha2 (Var xn) (Var ym) (Var zn)).
    all : try assumption.

    simpl in *. case_eq (attached_allFO_x alpha1 (Var xn));
      intros Hat2; rewrite Hat2 in *. discriminate.
    unfold rename_FOv in *.
    rewrite (IHalpha1 (Var xn) (Var ym) (Var zn)).
    apply (IHalpha2 (Var xn) (Var ym) (Var zn)).
    all : try assumption.

    simpl in *. case_eq (attached_allFO_x alpha1 (Var xn));
      intros Hat2; rewrite Hat2 in *. discriminate.
    unfold rename_FOv in *.
    rewrite (IHalpha1 (Var xn) (Var ym) (Var zn)).
    apply (IHalpha2 (Var xn) (Var ym) (Var zn)).
    all : try assumption.

    destruct p; simpl in *. apply (IHalpha (Var xn) (Var ym) (Var zn));
    assumption.

    destruct p; simpl in *. apply (IHalpha (Var xn) (Var ym) (Var zn));
    assumption.
Qed.

Lemma newnew_pre_nil : forall l alpha,
  newnew_pre alpha l nil = alpha.
Proof.
  induction l; intros alpha;
    reflexivity.
Qed.

Lemma rev_seq_nil : forall m n,
  rev_seq n m = nil -> m = 0.
Proof.
  induction m; intros n H.
    reflexivity.

    simpl in H. discriminate.
Qed.

Lemma min_l_rev_seq : forall m n,
  min_l (rev_seq n (S m)) = n.
Proof.
  induction m; intros n.
    simpl in *. apply plus_zero.

    simpl. case_eq (rev_seq n m). intros H.
      apply rev_seq_nil in H. rewrite H.
      rewrite <- one_suc.
      rewrite plus_zero.
      apply min_suc.

      intros n' l Heq.
      rewrite <- Heq.
      specialize (IHm n).
      simpl in IHm. rewrite Heq in IHm.
      rewrite <- Heq in IHm.
      rewrite IHm.
      apply min_plus_l.
Qed.

Lemma want9 : forall l2 l1 beta1,
  (forall P,
    is_in_pred P l2 = true /\
    is_in_pred P (preds_in beta1) = true ->
      is_in_pred P l1 = true) ->
  replace_pred_l beta1 (app l1 l2) 
      (nlist_list (length l1 + length l2) (nlist_Var1 (length l1 + length l2)))
      (nlist_list (length l1 + length l2) (nlist_empty (length l1 + length l2))) =
  replace_pred_l beta1 l1 (nlist_list (length l1) (nlist_Var1 _))
      (nlist_list (length l1) (nlist_empty _)).
Proof.
  induction l2; intros l1 beta1 H.
    simpl. rewrite app_nil_r.
    rewrite plus_zero. reflexivity.

    pose proof (rep_pred_l_app beta1 l1 (cons a l2)) as H2.
    simpl in *. rewrite app_length in H2. simpl in H2. rewrite H2.
    case_eq (is_in_pred a l2); intros H3.
      destruct (nlist_list_ex (length l2) l2 eq_refl) as [lP H4].
      rewrite <- H4.
      rewrite length_nlist_list.
      rewrite rep_pred__l_is_in.
      rewrite H4.
      pose proof (rep_pred_l_app beta1 l1 l2) as H5.
      rewrite <- H5. rewrite app_length. simpl.
      apply IHl2.
        intros [Pn] H6.
        specialize (H (Pred Pn)). simpl in H.
        destruct a as [Qm].
        case_eq (beq_nat Pn Qm); intros Hbeq;
          rewrite Hbeq in *.
          apply H. apply conj. reflexivity.
          apply H6.

          apply H. apply H6.
          rewrite H4. assumption.

          apply un_predless_l_empty_n.

          reflexivity.

        rewrite Rep_Pred_FOv.rep_pred__l_switch_empty.
      pose proof (rep_pred_l_app beta1 l1 l2) as H5.
      rewrite <- H5. rewrite app_length. simpl.
      rewrite IHl2.
        specialize (H a). destruct a as [Qm].
        rewrite <- beq_nat_refl in H.
        
    case_eq (is_in_pred (Pred Qm) l1); intros H6.
      destruct (nlist_list_ex (length l1) l1 eq_refl) as [lP H4].
      rewrite <- H4.
      rewrite length_nlist_list.
      rewrite rep_pred__l_is_in. reflexivity.
      rewrite H4. assumption.

          apply un_predless_l_empty_n.

          reflexivity.

        rewrite <- Rep_Pred_FOv.rep_pred__l_switch_empty.
        case_eq (is_in_pred (Pred Qm) (preds_in beta1)); intros H8.
          rewrite H8 in *. rewrite H6 in H.
          assert (true = true /\ true = true) as H9.
            apply conj; reflexivity.
          discriminate (H H9).

          rewrite P_occ_rep_pred_f. reflexivity.
unfold P_occurs_in_alpha.
          apply P_occ_in_l_is_in_pred.
          assumption.

          intros [Pn] H6.
          apply H. destruct a as [Qm].
          apply conj.
            case_eq (beq_nat Pn Qm); intros Hbeq.
              reflexivity.
  
              all : apply H6.
Qed.

Lemma want12 : forall l1 l2 P,
  is_in_pred P l1 = true ->
  is_in_pred P l2 = false ->
  is_in_pred P (list_pred_not_in l2 l1) = true.
Proof.
  induction l1; intros l2 [Pn] H1 H2.
    simpl in *. discriminate.

    simpl in *. destruct a as [Qm].
    case_eq (beq_nat Pn Qm); intros Hbeq;
      rewrite Hbeq in *.
      rewrite <- (beq_nat_true _ _ Hbeq)  in *.
      rewrite H2.
      simpl. rewrite <- beq_nat_refl. reflexivity.

      case_eq (is_in_pred (Pred Qm) l2); intros H3.
        apply IHl1; assumption.

        simpl. rewrite Hbeq.
        apply IHl1; assumption.
Qed.

Lemma want11 : forall l1 l2 l P,
is_in_pred P (list_pred_not_in l l1) = true /\
is_in_pred P l2 = true ->
is_in_pred P (list_pred_not_in l l2) = true.
Proof.
  induction l1; intros l2 l [Pn] [H1 H2].
    simpl in *. discriminate.

    simpl in *. destruct a as [Qm].
    case_eq (is_in_pred (Pred Qm) l); intros H3;
      rewrite H3 in *.
      apply IHl1. apply conj; assumption.

      simpl in *.
      case_eq (beq_nat Pn Qm); intros Hbeq;
        rewrite Hbeq in *.
        rewrite (beq_nat_true _ _ Hbeq) in *.
        apply want12; assumption.

        apply IHl1. apply conj; assumption.
Qed.

Lemma want13 : forall l x y,
  ~ x = y ->
  is_in_FOvar y (rem_FOv l x) =
  is_in_FOvar y l.
Proof.
  induction l; intros [xn] [ym] Hneq.
    reflexivity.

    simpl in *. destruct a as [zn].
    case_eq (beq_nat xn zn); intros Hbeq;
      case_eq (beq_nat ym zn); intros Hbeq2.
        apply neq_beq_nat_FOv in Hneq.
        rewrite (beq_nat_true _ _ Hbeq) in Hneq.
        rewrite beq_nat_comm in Hneq.
        rewrite Hneq in Hbeq2. discriminate.

        apply IHl. assumption.

        simpl. rewrite Hbeq2. reflexivity.

        simpl. rewrite Hbeq2. apply IHl.
        assumption.
Qed.

Lemma is_in_FOvar_rename_FOv_list : forall l x y z,
  ~ x = y ->
  ~ x = z ->
  ~ y = z ->
  is_in_FOvar x (rename_FOv_list l y z) =
  is_in_FOvar x l.
Proof.
  induction l; intros [xn] [ym] [zn] H1 H2 H3.
    reflexivity.

    destruct a as [un]. simpl in  *.
    case_eq (beq_nat ym un); intros Hbeq.
      simpl. pose proof (neq_beq_nat_FOv _ _ H2) as H'.
      rewrite H'. case_eq (beq_nat xn un); intros Hbeq2.
        rewrite (beq_nat_true _ _ Hbeq) in H1.
        rewrite (beq_nat_true _ _ Hbeq2) in H1.
        contradiction (H1 eq_refl).

        apply IHl; assumption.

      simpl. case_eq (beq_nat xn un); intros Hbeq2.
        reflexivity.
        apply IHl; assumption.
Qed.

Lemma want16 : forall l beta n xn ym,
  ~ (Var xn) = (Var ym) ->
  free_FO beta (Var ym) = false ->
  Nat.leb ym n = true ->
  is_in_FOvar (Var ym) l = true ->
  is_in_FOvar (Var ym) (FOvars_in
      (newnew_pre beta (rem_FOv l (Var xn))
        (rev_seq (S n)
        (length (rem_FOv l (Var xn)))))) = false.
Proof.
  induction l; intros beta n xn ym Hneq Hfree Hleb Hin2.
    simpl in *. discriminate.

    simpl in *. destruct a as [zn].
    case_eq (beq_nat xn zn); intros Hbeq.
      case_eq (beq_nat ym zn); intros Hbeq2;
        rewrite Hbeq2 in *.
        rewrite (beq_nat_true _ _ Hbeq2) in Hneq.
        rewrite (beq_nat_true _ _ Hbeq) in Hneq.
        contradiction (Hneq eq_refl).

        apply IHl; assumption.

      simpl. rewrite hmm1.
      case_eq (beq_nat ym zn); intros Hbeq2;
        rewrite Hbeq2 in Hin2.
        rewrite <- (beq_nat_true _ _ Hbeq2) in *.
        case_eq (beq_nat ym (S (n + length (rem_FOv l (Var xn)))));
          intros Hbeq3.
          rewrite (beq_nat_true _ _ Hbeq3) in Hleb.
          rewrite <- plus_Sn_m in Hleb.
          apply leb_plus_r with (m := (length (rem_FOv l (Var xn))))
            in Hleb.
          rewrite <- leb_plus in Hleb.
          rewrite leb_suc_f in Hleb.
          discriminate.

          apply is_in_FOvar_rename.
          intros H. inversion H as [H'].
          rewrite H' in Hbeq3.
          rewrite <- beq_nat_refl in Hbeq3.
          discriminate.

        simpl.
        case_eq (beq_nat zn (S (n + length (rem_FOv l (Var xn)))));
          intros Hbeq3. rewrite (beq_nat_true _ _ Hbeq3).
          rewrite rename_FOv_list_refl.
          apply IHl; try assumption.
       
        rewrite is_in_FOvar_rename_FOv_list.
        apply IHl. all : try assumption.
          apply beq_nat_false_FOv. assumption.
          intros H; inversion H as [H'].
          rewrite H' in Hleb.
          rewrite <- plus_Sn_m in Hleb.
          apply leb_plus_r with (m := (length (rem_FOv l (Var xn))))
            in Hleb.
          rewrite <- leb_plus in Hleb.
          rewrite leb_suc_f in Hleb.
          discriminate.

          intros H. inversion H as [H'].
          rewrite H' in Hbeq3.
          rewrite <- beq_nat_refl in Hbeq3.
          discriminate.

Qed.

Lemma want19 : forall alpha ym,
  is_in_FOvar (Var ym) (FOvars_in alpha) = true ->
  Nat.leb ym (max_FOv alpha) = true.
Proof.
  induction alpha; intros xn H.
    destruct p as [Pn]; destruct f as [ym]. simpl in *.
    case_eq (beq_nat xn ym); intros Hbeq;
      rewrite Hbeq in *. 2: discriminate.
      rewrite (beq_nat_true _ _ Hbeq).
      apply leb_refl.

    destruct f as [y1]; destruct f0 as [y2].
    simpl in * . case_eq (beq_nat xn y1); intros Hbeq;
      rewrite Hbeq in *.
      rewrite <- (beq_nat_true _ _ Hbeq).
      apply leb_max_suc3. apply leb_refl.

      case_eq (beq_nat xn y2); intros Hbeq2;
        rewrite Hbeq2 in *. 2 : discriminate.
      rewrite <- (beq_nat_true _ _ Hbeq2).
      rewrite max_comm.
      apply leb_max_suc3. apply leb_refl.

    destruct f as [y1]; destruct f0 as [y2].
    simpl in * . case_eq (beq_nat xn y1); intros Hbeq;
      rewrite Hbeq in *.
      rewrite <- (beq_nat_true _ _ Hbeq).
      apply leb_max_suc3. apply leb_refl.

      case_eq (beq_nat xn y2); intros Hbeq2;
        rewrite Hbeq2 in *. 2 : discriminate.
      rewrite <- (beq_nat_true _ _ Hbeq2).
      rewrite max_comm.
      apply leb_max_suc3. apply leb_refl.

    destruct f as [ym]. simpl in *.
    case_eq (beq_nat xn ym); intros Hbeq; 
      rewrite Hbeq in *. rewrite (beq_nat_true _ _ Hbeq).
      apply leb_max_suc3. apply leb_refl.

      rewrite max_comm.
      apply leb_max_suc3.
      apply IHalpha. assumption.

    destruct f as [ym]. simpl in *.
    case_eq (beq_nat xn ym); intros Hbeq; 
      rewrite Hbeq in *. rewrite (beq_nat_true _ _ Hbeq).
      apply leb_max_suc3. apply leb_refl.

      rewrite max_comm.
      apply leb_max_suc3.
      apply IHalpha. assumption.

    simpl in *. apply IHalpha. assumption.

    simpl in *. rewrite is_in_FOvar_app in H.
    case_eq (is_in_FOvar (Var xn) (FOvars_in alpha1));
      intros H1; rewrite H1 in H.
      apply leb_max_suc3. apply IHalpha1.
      assumption.

      rewrite max_comm.
      apply leb_max_suc3.
      apply IHalpha2. assumption.

    simpl in *. rewrite is_in_FOvar_app in H.
    case_eq (is_in_FOvar (Var xn) (FOvars_in alpha1));
      intros H1; rewrite H1 in H.
      apply leb_max_suc3. apply IHalpha1.
      assumption.

      rewrite max_comm.
      apply leb_max_suc3.
      apply IHalpha2. assumption.

    simpl in *. rewrite is_in_FOvar_app in H.
    case_eq (is_in_FOvar (Var xn) (FOvars_in alpha1));
      intros H1; rewrite H1 in H.
      apply leb_max_suc3. apply IHalpha1.
      assumption.

      rewrite max_comm.
      apply leb_max_suc3.
      apply IHalpha2. assumption.

    destruct p. simpl in *. apply IHalpha.
    assumption.

    destruct p. simpl in *. apply IHalpha.
    assumption.
Qed.

Lemma kk4 : forall beta P x cond,
  replace_pred (allSO P beta) P x cond =
  replace_pred beta P x cond.
Proof.
  intros. simpl. destruct P as [Pn].
  rewrite <- beq_nat_refl. reflexivity.
Qed.

Lemma kk4_exSO : forall beta P x cond,
  replace_pred (exSO P beta) P x cond =
  replace_pred beta P x cond.
Proof.
  intros. simpl. destruct P as [Pn].
  rewrite <- beq_nat_refl. reflexivity.
Qed.

Lemma kk3 : forall lP beta P,
(FOvars_in (replace_pred_l (allSO P beta) lP
               (nlist_list (length lP) (nlist_Var1 (length lP)))
               (nlist_list (length lP) (nlist_empty (length lP))))) =
(FOvars_in (replace_pred_l beta lP
               (nlist_list (length lP) (nlist_Var1 (length lP)))
               (nlist_list (length lP) (nlist_empty (length lP))))).
Proof.
  induction lP; intros beta [Pn].
    simpl. reflexivity.

    simpl in *. destruct a as [Qm].
    rewrite <- Rep_Pred_FOv.rep_pred__l_switch_empty.
    case_eq (beq_nat Pn Qm); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq).
      rewrite kk4.
      rewrite Rep_Pred_FOv.rep_pred__l_switch_empty.
      reflexivity.

      simpl. rewrite beq_nat_comm. rewrite Hbeq.
      rewrite IHlP.
      rewrite Rep_Pred_FOv.rep_pred__l_switch_empty.
      reflexivity.
Qed.

Lemma kk3_exSO : forall lP beta P,
(FOvars_in (replace_pred_l (exSO P beta) lP
               (nlist_list (length lP) (nlist_Var1 (length lP)))
               (nlist_list (length lP) (nlist_empty (length lP))))) =
(FOvars_in (replace_pred_l beta lP
               (nlist_list (length lP) (nlist_Var1 (length lP)))
               (nlist_list (length lP) (nlist_empty (length lP))))).
Proof.
  induction lP; intros beta [Pn].
    simpl. reflexivity.

    simpl in *. destruct a as [Qm].
    rewrite <- Rep_Pred_FOv.rep_pred__l_switch_empty.
    case_eq (beq_nat Pn Qm); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq).
      rewrite kk4_exSO.
      rewrite Rep_Pred_FOv.rep_pred__l_switch_empty.
      reflexivity.

      simpl. rewrite beq_nat_comm. rewrite Hbeq.
      rewrite IHlP.
      rewrite Rep_Pred_FOv.rep_pred__l_switch_empty.
      reflexivity.
Qed.

Lemma kk2 : forall lP beta P y,
  is_in_FOvar y (FOvars_in (replace_pred_l (allSO P beta) lP
      (nlist_list (length lP) (nlist_Var1 _))
      (nlist_list (length lP) (nlist_empty _)))) =
  is_in_FOvar y (FOvars_in (replace_pred_l  beta lP
      (nlist_list (length lP) (nlist_Var1 _))
      (nlist_list (length lP) (nlist_empty _)))).
Proof.
  intros. rewrite kk3.
  reflexivity.
Qed.

Lemma kk2_exSO : forall lP beta P y,
  is_in_FOvar y (FOvars_in (replace_pred_l (exSO P beta) lP
      (nlist_list (length lP) (nlist_Var1 _))
      (nlist_list (length lP) (nlist_empty _)))) =
  is_in_FOvar y (FOvars_in (replace_pred_l  beta lP
      (nlist_list (length lP) (nlist_Var1 _))
      (nlist_list (length lP) (nlist_empty _)))).
Proof.
  intros. rewrite kk3_exSO.
  reflexivity.
Qed.

Lemma is_in_FOvar_l_trans : forall l1 l2 l3,
  is_in_FOvar_l l1 l2 = true ->
  is_in_FOvar_l l2 l3 = true ->
  is_in_FOvar_l l1 l3 = true.
Proof.
  induction l1; intros l2 l3 H1 H2.
    reflexivity.

    simpl in *. case_eq (is_in_FOvar a l2);
      intros H; rewrite H in *.
      rewrite (is_in__FOvar _ _ _ H2 H).
      apply IHl1 with (l2 := l2); assumption.
      discriminate.
Qed.

Lemma is_in_FOvar_l_cons_r2 : forall l1 l2 x,
  is_in_FOvar_l l1 l2 = true ->
  is_in_FOvar_l l1 (cons x l2) = true.
Proof.
  induction l1; intros l2 [xn] H.
    reflexivity.

    destruct a as [ym].
    simpl in *. case_eq (is_in_FOvar (Var ym) l2);
      intros H2; rewrite H2 in*. 2 :discriminate.
    rewrite if_then_else_true. apply IHl1.
    assumption.
Qed.

Lemma is_in_FOvar_l_app_r1 : forall l1 l2 l3,
  is_in_FOvar_l l1 l2 = true ->
  is_in_FOvar_l l1 (app l3 l2) = true.
Proof.
  induction l1; intros l2 l3 H.
    reflexivity.

    simpl in *. case_eq (is_in_FOvar a l2);
      intros H2; rewrite H2 in *;
      rewrite is_in_FOvar_app;
      rewrite H2. rewrite if_then_else_true.
      apply IHl1; assumption.

      discriminate.
Qed.

Lemma is_in_FOvar_l_app : forall l1 l2 l3 l4,
  is_in_FOvar_l l1 l2 = true ->
  is_in_FOvar_l l3 l4 = true ->
  is_in_FOvar_l (app l1 l3) (app l2 l4) = true.
Proof.
  induction l1; intros l2 l3 l4 H1 H2.
    simpl. apply is_in_FOvar_l_app_r1.
    apply H2.

    simpl in *. case_eq (is_in_FOvar a l2);
      intros H; rewrite H in *;
      rewrite is_in_FOvar_app;
      rewrite H. apply IHl1; assumption.
      discriminate.
Qed.


Lemma is_in_FOvar_l_refl : forall l,
  is_in_FOvar_l l l = true.
Proof.
  induction l.
    reflexivity.

    simpl. destruct a as [xn]. rewrite <- beq_nat_refl.
    apply is_in_FOvar_l_cons_r2. assumption.
Qed.

Lemma kk5 : forall alpha P x,
  is_in_FOvar_l (FOvars_in (replace_pred alpha P x (negSO (eqFO x x))))
  (FOvars_in alpha) = true.
Proof.
  induction alpha; intros [Pn] [xn].
    destruct p as [Qm]. destruct f as [ym].
    simpl. rewrite <- beq_nat_refl.
    case_eq (beq_nat Pn Qm); intros Hbeq;
      simpl; rewrite <- beq_nat_refl;
      reflexivity.

    destruct f as [y1]; destruct f0 as [y2]. simpl.
    do 2rewrite <- beq_nat_refl.
    case_eq (beq_nat y2 y1); intros Hbeq; reflexivity.

    destruct f as [y1]; destruct f0 as [y2]. simpl.
    do 2rewrite <- beq_nat_refl.
    case_eq (beq_nat y2 y1); intros Hbeq; reflexivity.

    destruct f as [ym]. simpl. rewrite <- beq_nat_refl.
    apply is_in_FOvar_l_trans with (l2 := FOvars_in alpha).
      apply IHalpha. apply is_in_FOvar_l_cons_r2.
      apply is_in_FOvar_l_refl.


    destruct f as [ym]. simpl. rewrite <- beq_nat_refl.
    apply is_in_FOvar_l_trans with (l2 := FOvars_in alpha).
      apply IHalpha. apply is_in_FOvar_l_cons_r2.
      apply is_in_FOvar_l_refl.

    simpl. apply IHalpha.

    simpl. apply is_in_FOvar_l_app.
      apply IHalpha1. apply IHalpha2.

    simpl. apply is_in_FOvar_l_app.
      apply IHalpha1. apply IHalpha2.

    simpl. apply is_in_FOvar_l_app.
      apply IHalpha1. apply IHalpha2.

    simpl. destruct p as [Qm].
    case_eq (beq_nat Pn Qm); intros Hbeq.
      apply IHalpha.
      simpl. apply IHalpha.

    simpl. destruct p as [Qm].
    case_eq (beq_nat Pn Qm); intros Hbeq.
      apply IHalpha.
      simpl. apply IHalpha.
Qed.

Lemma kk6 : forall alpha P x,
  is_in_FOvar_l (FOvars_in alpha)
    (FOvars_in (replace_pred alpha P x (negSO (eqFO x x))))
   = true.
Proof.
  induction alpha; intros [Pn] [xn].
    destruct p as [Qm]. destruct f as [ym].
    simpl. rewrite <- beq_nat_refl.
    case_eq (beq_nat Pn Qm); intros Hbeq;
      simpl; rewrite <- beq_nat_refl;
      reflexivity.

    destruct f as [y1]; destruct f0 as [y2]. simpl.
    do 2rewrite <- beq_nat_refl.
    case_eq (beq_nat y2 y1); intros Hbeq; reflexivity.

    destruct f as [y1]; destruct f0 as [y2]. simpl.
    do 2rewrite <- beq_nat_refl.
    case_eq (beq_nat y2 y1); intros Hbeq; reflexivity.

    destruct f as [ym]. simpl. rewrite <- beq_nat_refl.
    apply is_in_FOvar_l_trans with (l2 := FOvars_in alpha).
    apply is_in_FOvar_l_refl. apply is_in_FOvar_l_cons_r2.
    apply IHalpha.

    destruct f as [ym]. simpl. rewrite <- beq_nat_refl.
    apply is_in_FOvar_l_trans with (l2 := FOvars_in alpha).
    apply is_in_FOvar_l_refl. apply is_in_FOvar_l_cons_r2.
    apply IHalpha.

    simpl. apply IHalpha.

    simpl. apply is_in_FOvar_l_app.
      apply IHalpha1. apply IHalpha2.

    simpl. apply is_in_FOvar_l_app.
      apply IHalpha1. apply IHalpha2.

    simpl. apply is_in_FOvar_l_app.
      apply IHalpha1. apply IHalpha2.

    simpl. destruct p as [Qm].
    case_eq (beq_nat Pn Qm); intros Hbeq.
      apply IHalpha.
      simpl. apply IHalpha.

    simpl. destruct p as [Qm].
    case_eq (beq_nat Pn Qm); intros Hbeq.
      apply IHalpha.
      simpl. apply IHalpha.
Qed.


Lemma kk1 : forall beta alpha y,
  is_in_FOvar y (FOvars_in alpha) = true ->
  is_in_FOvar y (FOvars_in beta) = true ->
  is_in_FOvar y (FOvars_in (instant_cons_empty' alpha beta)) = true.
Proof.
  unfold instant_cons_empty'.
  induction beta; intros alpha [ym] H1 H2.
    destruct p as [Pn]; destruct f as [xn].
    simpl. case_eq (is_in_pred (Pred Pn) (preds_in alpha));
      intros Hin. simpl in *. assumption.

      simpl. rewrite <- beq_nat_refl. simpl in *.
      case_eq (beq_nat ym xn); intros Hbeq;
        rewrite Hbeq in *. reflexivity.
        discriminate.

    destruct f as [x1]; destruct f0 as [x2].
    simpl in *. assumption.

    destruct f as [x1]; destruct f0 as [x2].
    simpl in *. assumption.

    destruct f as [xn]. simpl in *.
    rewrite rep_pred_l_allFO.
    simpl. case_eq (beq_nat ym xn); intros Hbeq;
      rewrite Hbeq in *. reflexivity.
      apply IHbeta; assumption.

    destruct f as [xn]. simpl in *.
    rewrite rep_pred_l_exFO.
    simpl. case_eq (beq_nat ym xn); intros Hbeq;
      rewrite Hbeq in *. reflexivity.
      apply IHbeta; assumption.

    simpl in *. rewrite rep_pred_l_negSO.
    simpl. apply IHbeta; assumption.

    simpl in *. rewrite list_pred_not_in_app.
    rewrite rep_pred_l_conjSO. rewrite app_length. 
    simpl.
    rewrite want9. rewrite <- app_length.
    rewrite rep_pred_l_app.
    rewrite rep_pred_l_switch.
    rewrite <- rep_pred_l_app.
    rewrite app_length.
    rewrite want9.
    rewrite is_in_FOvar_app in *.
    case_eq (is_in_FOvar (Var ym) (FOvars_in beta1)); intros Ha;
      rewrite Ha in *.
      rewrite IHbeta1; try assumption.

      rewrite IHbeta2; try assumption.
      rewrite if_then_else_true. reflexivity.
      apply want11. apply want11.

    simpl in *. rewrite list_pred_not_in_app.
    rewrite rep_pred_l_disjSO. rewrite app_length. 
    simpl.
    rewrite want9. rewrite <- app_length.
    rewrite rep_pred_l_app.
    rewrite rep_pred_l_switch.
    rewrite <- rep_pred_l_app.
    rewrite app_length.
    rewrite want9.
    rewrite is_in_FOvar_app in *.
    case_eq (is_in_FOvar (Var ym) (FOvars_in beta1)); intros Ha;
      rewrite Ha in *.
      rewrite IHbeta1; try assumption.

      rewrite IHbeta2; try assumption.
      rewrite if_then_else_true. reflexivity.
      apply want11. apply want11.

    simpl in *. rewrite list_pred_not_in_app.
    rewrite rep_pred_l_implSO. rewrite app_length. 
    simpl.
    rewrite want9. rewrite <- app_length.
    rewrite rep_pred_l_app.
    rewrite rep_pred_l_switch.
    rewrite <- rep_pred_l_app.
    rewrite app_length.
    rewrite want9.
    rewrite is_in_FOvar_app in *.
    case_eq (is_in_FOvar (Var ym) (FOvars_in beta1)); intros Ha;
      rewrite Ha in *.
      rewrite IHbeta1; try assumption.

      rewrite IHbeta2; try assumption.
      rewrite if_then_else_true. reflexivity.
      apply want11. apply want11.

    destruct p as [Pn]. simpl.
    simpl in *.
    case_eq (is_in_pred (Pred Pn) (preds_in alpha)); intros Ha.
      rewrite kk2. apply IHbeta; assumption.

      rewrite kk2.  simpl. apply is_in__FOvar with 
        (l1 := (FOvars_in (replace_pred_l beta (list_pred_not_in (preds_in alpha) (preds_in beta))
           (nlist_list (length (list_pred_not_in (preds_in alpha) (preds_in beta)))
              (nlist_Var1 (length (list_pred_not_in (preds_in alpha) (preds_in beta)))))
           (nlist_list (length (list_pred_not_in (preds_in alpha) (preds_in beta)))
              (nlist_empty (length (list_pred_not_in (preds_in alpha) (preds_in beta)))))))).
      apply kk6. apply IHbeta; assumption.

    destruct p as [Pn]. simpl.
    simpl in *.
    case_eq (is_in_pred (Pred Pn) (preds_in alpha)); intros Ha.
      rewrite kk2_exSO. apply IHbeta; assumption.

      rewrite kk2_exSO.  simpl. apply is_in__FOvar with 
        (l1 := (FOvars_in (replace_pred_l beta (list_pred_not_in (preds_in alpha) (preds_in beta))
           (nlist_list (length (list_pred_not_in (preds_in alpha) (preds_in beta)))
              (nlist_Var1 (length (list_pred_not_in (preds_in alpha) (preds_in beta)))))
           (nlist_list (length (list_pred_not_in (preds_in alpha) (preds_in beta)))
              (nlist_empty (length (list_pred_not_in (preds_in alpha) (preds_in beta)))))))).
      apply kk6. apply IHbeta; assumption.
Qed.

Lemma want15 : forall beta xn a alpha,
  free_FO beta a = false ->
  is_in_FOvar a (FOvars_in beta) = true ->
  SOQFree beta = true ->
  attached_allFO_x alpha (Var xn) = false ->
  ~ (Var xn) = a ->
  is_in_FOvar a (FOvars_in alpha) = true ->
  is_in_FOvar a (FOvars_in
    (newnew_pre (instant_cons_empty' alpha beta)
       (rem_FOv (FOvars_in (instant_cons_empty' alpha beta)) (Var xn))
       (rev_seq (S (Nat.max (Nat.max (max_FOv alpha) (max_FOv beta)) xn))
          (length
             (rem_FOv (FOvars_in (instant_cons_empty' alpha beta)) (Var xn))))))
      = false.
Proof.
  intros beta xn [ym] alpha Hfree Hin3 Hno Hat Hneq Hin2.
  apply want16; try assumption.
    apply free_FO_instant_cons_empty'_f; try assumption.

    apply leb_max_suc3.
    apply leb_max_suc3.
    apply want19. assumption.
    apply kk1; assumption.
Qed.

Lemma kk8 : forall lP beta x,
  is_in_FOvar x (FOvars_in beta) = false ->
  is_in_FOvar x (FOvars_in
   (replace_pred_l beta lP (nlist_list (length lP) (nlist_Var1 _))
      (nlist_list (length lP) (nlist_empty _)))) = false.
Proof.
  induction lP; intros beta x H.
    simpl. assumption.

    simpl. 
    case_eq (is_in_FOvar x
  (FOvars_in
     (replace_pred
        (replace_pred_l beta lP (nlist_list (length lP) (nlist_Var1 (length lP)))
           (nlist_list (length lP) (nlist_empty (length lP)))) a 
        (Var 1) (negSO (eqFO (Var 1) (Var 1)))))); intros H2.
      2 : reflexivity.
    apply is_in__FOvar with (l2 := FOvars_in (replace_pred_l beta lP
                (nlist_list (length lP) (nlist_Var1 (length lP)))
                (nlist_list (length lP) (nlist_empty (length lP)))))  in H2.
      rewrite IHlP in H2. discriminate.
      assumption.

      apply kk5.
Qed.

Lemma kk7 : forall beta alpha a,
  is_in_FOvar a (FOvars_in beta) = false ->
  is_in_FOvar a (FOvars_in (instant_cons_empty' alpha beta)) = false.
Proof.
  intros beta alpha [Pn] H.
  unfold instant_cons_empty'.
  apply kk8.  
  assumption.
Qed.

Lemma is_in_FOvar_att_allFO_x : forall alpha x,
  is_in_FOvar x (FOvars_in alpha) = false ->
  attached_allFO_x alpha x = false.
Proof.
  induction alpha; intros [xn] H; try reflexivity.

    destruct f as [ym]. simpl in *.
    case_eq (beq_nat xn ym); intros Hbeq;
      rewrite Hbeq in *. discriminate.
      apply IHalpha. assumption.

    destruct f as [ym]. simpl in *.
    case_eq (beq_nat xn ym); intros Hbeq;
      rewrite Hbeq in *. discriminate.
      apply IHalpha. assumption.

    simpl in *. apply IHalpha; assumption.

    simpl in *. rewrite is_in_FOvar_app in H.
    case_eq (is_in_FOvar (Var xn) (FOvars_in alpha1));
      intros Hin; rewrite Hin in *. discriminate.
    rewrite IHalpha1. apply IHalpha2.
    all : try assumption.

    simpl in *. rewrite is_in_FOvar_app in H.
    case_eq (is_in_FOvar (Var xn) (FOvars_in alpha1));
      intros Hin; rewrite Hin in *. discriminate.
    rewrite IHalpha1. apply IHalpha2.
    all : try assumption.

    simpl in *. rewrite is_in_FOvar_app in H.
    case_eq (is_in_FOvar (Var xn) (FOvars_in alpha1));
      intros Hin; rewrite Hin in *. discriminate.
    rewrite IHalpha1. apply IHalpha2.
    all : try assumption.

    destruct p. simpl in *.
    apply IHalpha. assumption.

    destruct p. simpl in *.
    apply IHalpha. assumption.
Qed.

Lemma want14 : forall l beta xn a alpha,
  SOQFree beta = true ->
  free_FO beta a = false ->
  ~ Var xn = a ->
  is_in_FOvar a (FOvars_in beta) = true ->
  is_in_FOvar_l l (FOvars_in alpha) = true ->
  attached_allFO_x alpha (Var xn) = false ->
  is_in_FOvar a (FOvars_in alpha) = true ->
 attached_allFO_x
    (newnew_pre (instant_cons_empty' alpha beta)
       (rem_FOv (FOvars_in (instant_cons_empty' alpha beta)) (Var xn))
       (rev_seq (S (Nat.max (Nat.max (max_FOv alpha) (max_FOv beta)) xn))
          (length
             (rem_FOv (FOvars_in (instant_cons_empty' alpha beta)) (Var xn)))))
    a = false.
Proof.
  intros l beta xn [ym] alpha Hno Hfree Hin Hneq Hin3 Hat Hin2.
  apply is_in_FOvar_att_allFO_x.
  apply want15; try assumption.
Qed.

Lemma aa23 : forall l alpha x n,
  ~ l = nil ->
  x_occ_in_alpha alpha x = true ->
  is_in_FOvar x l = false ->
  attached_allFO_x alpha x = false ->
  Nat.leb (max_FOv alpha) n = true ->
  attached_allFO_x (newnew_pre alpha l
    (rev_seq (S n) (length l))) x = false.
Proof.
  induction l; intros alpha x n Hnil Hocc Hin Hat Hleb.
    simpl. assumption.

    simpl. simpl in Hin. destruct x as [xn].
    destruct a as [ym]. case_eq (beq_nat xn ym);
      intros Hbeq; rewrite Hbeq in *. discriminate.
    case_eq l. intros Hnil2. rewrite Hnil2 in *. simpl.
      rewrite <- plus_n_O.
      rewrite <- rename_FOv__n.
      apply rename_FOv_att_allFO; try assumption.
      apply x_occ_in_alpha_max_FOv_gen in Hleb.
      intros H. rewrite H in *. rewrite Hleb in *.
      discriminate.

      intros z l' Heq. assert (~ l = nil) as HH.
        intros HH2. rewrite HH2 in Heq. discriminate.
      specialize (IHl _ _ n HH Hocc Hin Hat Hleb).
      apply rename_FOv_att_allFO. rewrite <- Heq. apply IHl.
      rewrite <- Heq.
      intros H. inversion H as [H'].
      rewrite <- H' in Hocc.
      rewrite x_occ_in_alpha_max_FOv_gen in Hocc.
        discriminate.
      apply (leb_trans _ n). assumption.
      apply leb_plus_r. apply leb_refl.
Qed.

Lemma x_occ_in_alpha_instant_cons_empty'_pre_pre : forall beta P x y,
  x_occ_in_alpha beta x = true ->
  x_occ_in_alpha (replace_pred beta P y (negSO (eqFO y y ))) x = true.
Proof.
  induction beta; intros [Pn] [xn] [ym] Hocc.
    destruct p as [Qm]; destruct f as [zn].
    simpl in *. rewrite <- beq_nat_refl.
    case_eq (beq_nat Pn Qm); intros Hbeq;   
      simpl; rewrite Hocc; reflexivity.

    destruct f as [z1]; destruct f0 as [z2].
    simpl in *. assumption.

    destruct f as [z1]; destruct f0 as [z2].
    simpl in *. assumption.

    destruct f as [zn]. simpl in *. case_eq (beq_nat xn zn);
      intros Hbeq; rewrite Hbeq in *. reflexivity.
    apply IHbeta. assumption.

    destruct f as [zn]. simpl in *. case_eq (beq_nat xn zn);
      intros Hbeq; rewrite Hbeq in *. reflexivity.
    apply IHbeta. assumption.

    simpl in *. apply IHbeta. assumption.

    simpl in *. case_eq (x_occ_in_alpha beta1 (Var xn)); intros H;
      rewrite H in *. rewrite IHbeta1. reflexivity. assumption.

      rewrite IHbeta2. rewrite if_then_else_true. reflexivity.
      assumption.

    simpl in *. case_eq (x_occ_in_alpha beta1 (Var xn)); intros H;
      rewrite H in *. rewrite IHbeta1. reflexivity. assumption.

      rewrite IHbeta2. rewrite if_then_else_true. reflexivity.
      assumption.

    simpl in *. case_eq (x_occ_in_alpha beta1 (Var xn)); intros H;
      rewrite H in *. rewrite IHbeta1. reflexivity. assumption.

      rewrite IHbeta2. rewrite if_then_else_true. reflexivity.
      assumption.

    destruct p as [Qm]. simpl in *.
    case_eq (beq_nat Pn Qm); intros Hbeq; simpl;
      apply IHbeta; assumption.

    destruct p as [Qm]. simpl in *.
    case_eq (beq_nat Pn Qm); intros Hbeq; simpl;
      apply IHbeta; assumption.
Qed.

Lemma x_occ_in_alpha_instant_cons_empty'_pre : forall l beta x,
x_occ_in_alpha beta x = true ->
x_occ_in_alpha
  (replace_pred_l beta l (nlist_list (length l) (nlist_Var1 _))
        (nlist_list (length l) (nlist_empty _))) x = true.
Proof.
  induction l; intros beta x Hocc.
    simpl. assumption.

    simpl. apply x_occ_in_alpha_instant_cons_empty'_pre_pre.
    apply IHl. assumption.
Qed.

Lemma x_occ_in_alpha_instant_cons_empty' : forall beta alpha x,
  x_occ_in_alpha beta x = true ->
  x_occ_in_alpha (instant_cons_empty' alpha beta) x = true.
Proof.
  unfold instant_cons_empty'.
  intros. apply x_occ_in_alpha_instant_cons_empty'_pre.
  assumption.
Qed.

Lemma is_in_FOvar_rem_FOv_f : forall l x,
  is_in_FOvar x (rem_FOv l x) = false.
Proof.
  induction l; intros [xn].
    simpl. reflexivity.

    simpl. destruct a as [ym].
    case_eq (beq_nat xn ym); intros Hbeq.
      apply IHl.

      simpl. rewrite Hbeq. apply IHl.
Qed. 

Lemma max_FOv_rep_pred : forall alpha P x,
  max_FOv (replace_pred alpha P x (negSO (eqFO x x))) = 
  max_FOv alpha.
Proof.
  induction alpha; intros [Pn] [xn].
    destruct p as [Qm]; destruct f as [ym].
    simpl. rewrite <- beq_nat_refl.
    case_eq (beq_nat Pn Qm); intros Hbeq;
      simpl. apply max_refl. reflexivity.

    destruct f as [y1]; destruct f0 as [y2].
    reflexivity.

    destruct f as [y1]; destruct f0 as [y2].
    reflexivity.

    destruct f as [ym].
    simpl. rewrite IHalpha. reflexivity.

    destruct f as [ym].
    simpl. rewrite IHalpha. reflexivity.

    simpl in *. apply IHalpha.

    simpl in *. rewrite IHalpha1. rewrite IHalpha2.
    reflexivity.

    simpl in *. rewrite IHalpha1. rewrite IHalpha2.
    reflexivity.

    simpl in *. rewrite IHalpha1. rewrite IHalpha2.
    reflexivity.

    destruct p as [Qm]. simpl.
    case_eq (beq_nat Pn Qm); intros H; simpl;
      apply IHalpha.

    destruct p as [Qm]. simpl.
    case_eq (beq_nat Pn Qm); intros H; simpl;
      apply IHalpha.
Qed.

Lemma max_FOv_instant_cons_empty'_pre: forall l beta,
max_FOv
  (replace_pred_l beta l (nlist_list (length l) (nlist_Var1 _))
          (nlist_list (length l) (nlist_empty _))) =
max_FOv beta.
Proof.
  induction l; intros beta.
    simpl. reflexivity.

    simpl. rewrite max_FOv_rep_pred.
    apply IHl.
Qed.

Lemma max_FOv_instant_cons_empty': forall beta alpha,
  (max_FOv (instant_cons_empty' alpha beta)) =
  max_FOv beta.
Proof.
  unfold instant_cons_empty'. intros.
  apply max_FOv_instant_cons_empty'_pre.
Qed.

Lemma aa24 : forall l alpha beta ym n,
  is_in_FOvar (Var ym) (FOvars_in alpha) = true ->
  is_in_FOvar (Var ym) (FOvars_in beta) = false ->
  is_in_FOvar (Var ym) l = false ->
  Nat.leb ym n = true ->
attached_allFO_x
    (newnew_pre (instant_cons_empty' alpha beta) l
       (rev_seq (S n) (length l))) (Var ym) = false.
Proof.
  induction l; intros alpha beta ym n H1 H2 H3 Hleb.
    simpl. apply att_allFO_instant_cons_empty'.
    apply is_in_FOvar_att_allFO_x. assumption.

    simpl.
    case_eq (beq_nat (S (n + length l)) ym); intros Hbeq2.
      rewrite <- (beq_nat_true _ _ Hbeq2) in Hleb.
      rewrite <- plus_Sn_m in Hleb.
      rewrite leb_suc_f2 in Hleb. discriminate.

      apply rename_FOv_att_allFO.
      apply IHl; try assumption.
      simpl in H3. destruct a as [xn].
      case_eq (beq_nat ym xn); intros Hbeq; 
        rewrite Hbeq in *. discriminate.
      assumption.

      apply beq_nat_false_FOv. assumption.
Qed.

Lemma want3 : forall l alpha beta xn,
  SOQFree beta = true ->
  is_in_FOvar_l l (FOvars_in alpha) = true ->
  attached_allFO_x alpha (Var xn) = false ->
  closed_except beta (Var xn) ->
  attached_allFO_x beta (Var xn) = false ->
ex_attached_allFO_lv
  (newnew_pre (instant_cons_empty' alpha beta)
     (rem_FOv (FOvars_in (instant_cons_empty' alpha beta)) (Var xn))
     (rev_seq (S (Nat.max (max_FOv (implSO alpha beta)) xn))
        (length
           (rem_FOv (FOvars_in (instant_cons_empty' alpha beta))
              (Var xn))))) l = false.
Proof.
  induction l; intros alpha beta xn Hno Hin Hat Hcl Hat2.
    simpl. reflexivity.

    simpl in Hin. case_eq (is_in_FOvar a (FOvars_in alpha)); intros Hin2;
        rewrite Hin2 in *. 2 : discriminate.
    simpl.
    destruct a as [ym]. case_eq (beq_nat xn ym); intros Hbeq.
      rewrite <- (beq_nat_true _ _ Hbeq).
    case_eq (rem_FOv (FOvars_in (instant_cons_empty' alpha beta)) (Var xn)).
      intros H. simpl.
      rewrite att_allFO_instant_cons_empty'. 2 : assumption.
      specialize (IHl alpha beta xn).
      rewrite H in IHl. simpl in *. apply IHl.
      all : try assumption.
    intros y l' Heq. rewrite <- Heq.
      rewrite aa23.
     apply IHl. all : try assumption.
      rewrite Heq. intros. discriminate.
      apply x_occ_in_alpha_instant_cons_empty'.
      apply (contrapos_bool_ff _ _ (x_occ_in_free_FO _ _)).
      apply Hcl. apply is_in_FOvar_rem_FOv_f.

      apply att_allFO_instant_cons_empty'. assumption.

      rewrite max_FOv_instant_cons_empty'.
      apply leb_max_suc3. rewrite max_comm.
      apply leb_max_suc3.
      apply leb_refl.

      case_eq (is_in_FOvar (Var ym) (FOvars_in beta)); intros Hin3.

    rewrite want14 with (l := l); try assumption. 
     apply IHl. all : try assumption.

        unfold closed_except in Hcl.
        apply Hcl. apply beq_nat_false_FOv.
        assumption.

        apply beq_nat_false_FOv. assumption.

      rewrite aa24; try assumption.
     apply IHl. all : try assumption.
        rewrite want13.
        apply kk7. assumption.

        apply beq_nat_false_FOv. assumption.

        apply leb_max_suc3.
        apply leb_max_suc3.

        apply want19. assumption.
Qed.

Lemma is_in_FOvar_l_fun2 : forall alpha P,
is_in_FOvar_l (fun2 alpha P) (FOvars_in alpha) = true.
Proof.
  induction alpha; intros [Pn].
    destruct p as [Qm]; destruct f as [xn].
    simpl. case_eq (beq_nat Pn Qm); intros Hbeq.
      apply is_in_FOvar_l_refl. reflexivity.

    destruct f; destruct f0.
    reflexivity.

    destruct f; destruct f0.
    reflexivity.

    destruct f. simpl. apply is_in_FOvar_l_cons_r2.
    apply IHalpha.

    destruct f. simpl. apply is_in_FOvar_l_cons_r2.
    apply IHalpha.

    simpl. apply IHalpha.

    simpl. apply is_in_FOvar_l_app.
    apply IHalpha1. apply IHalpha2.

    simpl. apply is_in_FOvar_l_app.
    apply IHalpha1. apply IHalpha2.

    simpl. apply is_in_FOvar_l_app.
    apply IHalpha1. apply IHalpha2.

    simpl. apply IHalpha.

    simpl. apply IHalpha.
Qed.