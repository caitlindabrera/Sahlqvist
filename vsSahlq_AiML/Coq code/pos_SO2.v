Require Import SecOrder Modal ST_setup Uniform_Defns.
Require Import Arith.EqNat Bool my_arith__my_leb_nat P_occurs_in_alpha my_bool.
Require Import p_is_pos p_occurs_in is_pos_neg occ_in_phi at_pv Unary_Predless.
Require Import List_machinery_impl P_occurs_in_alpha at_pred my_arith Occ_In_Alpha.


Fixpoint is_pos_SO (alpha : SecOrder) (i : nat) : bool :=
  if occ_in_alpha alpha i then
  match alpha with
    predSO (Pred n) (Var m) => EqNat.beq_nat 1 i
  | relatSO (Var n) (Var m) => false
  | eqFO (Var n) (Var m) => false
  | allFO (Var n) beta => is_pos_SO beta i
  | negSO beta => eqb false (is_pos_SO beta i)
  | exFO (Var n) beta => is_pos_SO beta i
  | conjSO beta1 beta2 => if Nat.leb i (length (preds_in beta1)) then is_pos_SO beta1 i
                          else is_pos_SO beta2 (i-(length (preds_in beta1)))
  | disjSO beta1 beta2 => if Nat.leb i (length (preds_in beta1)) then is_pos_SO beta1 i
                          else is_pos_SO beta2 (i-(length (preds_in beta1)))
(*  | implSO beta1 beta2 => if Nat.leb i (length (preds_in beta1)) then is_pos_SO beta1 i
                          else is_pos_SO beta2 (i-(length (preds_in beta1)))
*)
  | implSO beta1 beta2 => if Nat.leb i (length (preds_in beta1)) then eqb false (is_pos_SO beta1 i)
                          else is_pos_SO beta2 (i-(length (preds_in beta1)))
  | allSO (Pred n) beta => match i with
                                     | 0 => false
                                     | S 0 => true
                                     | S j => is_pos_SO beta j
                                     end
  | exSO (Pred n) beta => match i with
                                     | 0 => false
                                     | S 0 => true
                                     | S j => is_pos_SO beta j
                                     end
  end
  else false.

Definition P_is_pos_SO (alpha : SecOrder) (P : predicate) : Prop :=
  (P_occurs_in_alpha alpha P = true ->
    forall i : nat, occ_in_alpha alpha i = true ->
      match P, at_pred (preds_in alpha) i with
      | Pred pn, Pred qm => pn = qm
      end
        -> is_pos_SO alpha i = true) /\
   (P_occurs_in_alpha alpha P = false -> False).

Definition uniform_pos_SO (alpha : SecOrder) : Prop :=
  forall (P : predicate), P_occurs_in_alpha alpha P = true -> 
    P_is_pos_SO alpha P.


(* -------------------------------------------------------------------- *)

Lemma is_pos_SO_occ_f : forall (alpha : SecOrder) (i : nat),
  occ_in_alpha alpha i = false -> is_pos_SO alpha i = false.
Proof.
  intros alpha i Hocc.
  unfold is_pos_SO.
  induction alpha; rewrite Hocc;
  reflexivity.
Qed.

Lemma is_pos_SO_allFO : forall (alpha : SecOrder) (x : FOvariable) 
                               (i : nat),
  is_pos_SO (allFO x alpha) i = is_pos_SO alpha i.
Proof.
  intros alpha x i.
  simpl.
  destruct x.
  rewrite occ_in_alpha_allFO.
  case_eq (occ_in_alpha alpha i); intros Hocc.
    reflexivity.

    symmetry.
    apply is_pos_SO_occ_f.
    assumption.
Qed.

Lemma is_pos_SO_exFO : forall (alpha : SecOrder) (x : FOvariable) 
                               (i : nat),
  is_pos_SO (exFO x alpha) i = is_pos_SO alpha i.
Proof.
  intros alpha x i.
  simpl.
  destruct x.
  rewrite occ_in_alpha_exFO.
  case_eq (occ_in_alpha alpha i); intros Hocc.
    reflexivity.

    symmetry.
    apply is_pos_SO_occ_f.
    assumption.
Qed.

Lemma is_pos_SO_conjSO : forall (beta1 beta2 : SecOrder) (i : nat),
  is_pos_SO (conjSO beta1 beta2) i =
  if occ_in_alpha (conjSO beta1 beta2) i then
    if Nat.leb i (length (preds_in beta1)) 
       then is_pos_SO beta1 i
       else is_pos_SO beta2 (i-(length (preds_in beta1)))
    else false.
Proof.
  reflexivity.
Qed.

Lemma is_pos_SO_implSO : forall (beta1 beta2 : SecOrder) (i : nat),
  is_pos_SO (implSO beta1 beta2) i =
  if occ_in_alpha (implSO beta1 beta2) i then
    if Nat.leb i (length (preds_in beta1)) 
       then eqb false (is_pos_SO beta1 i)
       else is_pos_SO beta2 (i-(length (preds_in beta1)))
    else false.
Proof.
  reflexivity.
Qed.


Lemma is_pos_SO_ST_FOv : forall (phi : Modal) (x y : FOvariable)
                                (i : nat),
  is_pos_SO (ST phi x) i = is_pos_SO (ST phi y) i.
Proof.
  intros phi;
  pose proof (occ_in_alpha_ST_FOv phi) as H;
  induction phi;
    intros x y i;
    specialize (H x y i);
    try destruct p as [pn]; destruct x as [xn]; destruct y as [ym];
    simpl in *; rewrite H;
    try reflexivity;
    try (rewrite (preds_in_ST_FOv phi1 (Var xn) (Var ym));
    rewrite IHphi1 with (y := (Var ym)); try apply occ_in_alpha_ST_FOv;
    rewrite IHphi2 with (y := (Var ym)); try apply occ_in_alpha_ST_FOv;
      reflexivity).

    rewrite (IHphi (occ_in_alpha_ST_FOv phi) (Var xn) (Var ym) _).
      reflexivity.

    case_eq (beq_nat i 0); intros Hbeq;
      [rewrite (beq_nat_true _ _ Hbeq) in *;
      simpl in *;
      reflexivity |];
    rewrite <- H;
    rewrite arith_minus_zero;
    rewrite IHphi with (y := Var (ym+1));
    try apply occ_in_alpha_ST_FOv;
    rewrite occ_in_alpha_allFO;
    rewrite occ_in_alpha_implSO;
    try rewrite occ_in_alpha_implSO;
    try assumption;
    do 2 rewrite occ_in_alpha_relatSO;
    simpl;
    rewrite (preds_in_ST_FOv _ _ (Var (ym + 1)));
    reflexivity.

    case_eq (beq_nat i 0); intros Hbeq;
      [rewrite (beq_nat_true _ _ Hbeq) in *;
      simpl in *;
      reflexivity |];
    rewrite <- H;
    rewrite arith_minus_zero;
    rewrite IHphi with (y := Var (ym+1));
    try apply occ_in_alpha_ST_FOv;
    rewrite occ_in_alpha_exFO;
    rewrite occ_in_alpha_conjSO;
    try rewrite occ_in_alpha_conjSO;
    try assumption;
    do 2 rewrite occ_in_alpha_relatSO;
    simpl;
    rewrite (preds_in_ST_FOv _ _ (Var (ym + 1)));
    reflexivity.
Qed.


Lemma is_pos_SO_occ : forall (alpha : SecOrder) (i : nat),
  is_pos_SO alpha i = true -> occ_in_alpha alpha i = true.
Proof.
  intros alpha i H.
  unfold is_pos_SO in *.
  case_eq (occ_in_alpha alpha i); intros Hocc;
  induction alpha; rewrite Hocc in *;
  try reflexivity; discriminate.
Qed.

Lemma is_pos_SO_box : forall (phi : Modal) (x : FOvariable)
                             (i : nat),
  is_pos_SO (ST (box phi) x) i = is_pos_SO (ST phi x) i.
Proof.
  intros.
  simpl.
  destruct x as [n].
  case_eq (is_pos_SO (ST phi (Var n)) i); intros H1.
    case_eq (is_pos_SO (allFO (Var (n + 1)) (implSO (relatSO
                (Var n) (Var (n + 1))) (ST phi (Var (n + 1))))) i);
      intros H2.
      reflexivity.

      rewrite is_pos_SO_allFO in H2.
      rewrite is_pos_SO_implSO in H2. 
      rewrite occ_in_alpha_implSO in H2.
      simpl in H2.
      rewrite occ_in_alpha_relatSO in H2.
      rewrite preds_in_ST_FOv with (y := (Var n)) in H2.
      rewrite is_pos_SO_ST_FOv with (y := (Var n)) in H2.
      rewrite arith_minus_zero in H2.
      case_eq (Nat.leb i (length (preds_in (ST phi (Var n)))));
        intros Hleb; rewrite Hleb in *.
        case_eq (Nat.leb i 0); intros Hleb2; rewrite Hleb2 in *.
          discriminate.

          rewrite H2 in H1.
          discriminate.

        apply is_pos_SO_occ in H1.
        unfold occ_in_alpha in H1.
        case_eq (beq_nat i 0); intros Hbeq; rewrite Hbeq in *.
          discriminate.

          rewrite Hleb in H1.
          discriminate.

        case_eq (beq_nat i 0); intros Hbeq.
          apply is_pos_SO_occ in H1.
          unfold occ_in_alpha in H1.
          rewrite Hbeq in H1.
          discriminate.

          reflexivity.

    case_eq (is_pos_SO (allFO (Var (n + 1)) (implSO (relatSO
                (Var n) (Var (n + 1))) (ST phi (Var (n + 1))))) i);
      intros H2.
      pose proof H2 as H3.
      simpl in H2.
      rewrite occ_in_alpha_allFO in H2.
      rewrite occ_in_alpha_implSO in H2.
      simpl in H2.
      rewrite occ_in_alpha_relatSO in H2.
      rewrite is_pos_SO_ST_FOv with (y := Var (n+1)) in H1.
      rewrite arith_minus_zero in H2.
      rewrite H1 in H2.
      case_eq (Nat.leb i 0); intros Hleb;
        rewrite Hleb in *.
        rewrite leb_beq_zero in Hleb.
        rewrite (beq_nat_true _ _ Hleb) in H3.
        simpl in H3.
        discriminate.

        case_eq (Nat.leb i (length (preds_in (ST phi (Var (n+1)))))); intros Hleb2;
          rewrite Hleb2 in *;
          discriminate.

      case_eq (beq_nat i 0); intros Hbeq.
        rewrite (beq_nat_true _ _ Hbeq) in H3.
        simpl in H3.
        discriminate.

        reflexivity.

        reflexivity.
Qed.

Lemma is_pos_SO_diam : forall (phi : Modal) (x : FOvariable)
                             (i : nat),
  is_pos_SO (ST (diam phi) x) i = is_pos_SO (ST phi x) i.
Proof.
  intros.
  simpl.
  destruct x as [n].
  case_eq (is_pos_SO (ST phi (Var n)) i); intros H1.
    case_eq (is_pos_SO (exFO (Var (n + 1)) (conjSO (relatSO
                (Var n) (Var (n + 1))) (ST phi (Var (n + 1))))) i);
      intros H2.
      reflexivity.

      rewrite is_pos_SO_exFO in H2.
      rewrite is_pos_SO_conjSO in H2. 
      rewrite occ_in_alpha_conjSO in H2.
      simpl in H2.
      rewrite occ_in_alpha_relatSO in H2.
      rewrite preds_in_ST_FOv with (y := (Var n)) in H2.
      rewrite is_pos_SO_ST_FOv with (y := (Var n)) in H2.
      rewrite arith_minus_zero in H2.
      rewrite H1 in H2.
      pose proof (is_pos_SO_occ _ _ H1) as H3.
      unfold occ_in_alpha in H3.
      case_eq (Nat.leb i (length (preds_in (ST phi (Var n)))));
        intros Hleb; rewrite Hleb in *.
        case_eq (beq_nat i 0); intros Hleb2; rewrite Hleb2 in *.
          discriminate.

          rewrite <- leb_beq_zero in Hleb2.
          rewrite Hleb2 in H2.
          discriminate.

        apply is_pos_SO_occ in H1.
        unfold occ_in_alpha in H1.
        case_eq (beq_nat i 0); intros Hbeq; rewrite Hbeq in *.
          discriminate.

          rewrite Hleb in H1.
          discriminate.

        case_eq (beq_nat i 0); intros Hbeq.
          apply is_pos_SO_occ in H1.
          unfold occ_in_alpha in H1.
          rewrite Hbeq in H1.
          discriminate.

          reflexivity.

    case_eq (is_pos_SO (exFO (Var (n + 1)) (conjSO (relatSO
                (Var n) (Var (n + 1))) (ST phi (Var (n + 1))))) i);
      intros H2.
      pose proof H2 as H3.
      simpl in H2.
      rewrite occ_in_alpha_exFO in H2.
      rewrite occ_in_alpha_conjSO in H2.
      simpl in H2.
      rewrite occ_in_alpha_relatSO in H2.
      rewrite is_pos_SO_ST_FOv with (y := Var (n+1)) in H1.
      rewrite arith_minus_zero in H2.
      rewrite H1 in H2.
      case_eq (Nat.leb i 0); intros Hleb;
        rewrite Hleb in *.
        rewrite leb_beq_zero in Hleb.
        rewrite (beq_nat_true _ _ Hleb) in H3.
        simpl in H3.
        discriminate.

        case_eq (Nat.leb i (length (preds_in (ST phi (Var (n+1)))))); intros Hleb2;
          rewrite Hleb2 in *;
          discriminate.

      case_eq (beq_nat i 0); intros Hbeq.
        rewrite (beq_nat_true _ _ Hbeq) in H3.
        simpl in H3.
        discriminate.

        reflexivity.

        reflexivity.
Qed.

Lemma is_pos_SO_0 : forall (alpha : SecOrder),
  is_pos_SO alpha 0 = false.
Proof.
  induction alpha; reflexivity.
Qed.

Lemma is_pos__ST : forall (phi : Modal) (x : FOvariable) (i : nat),
  is_pos phi i = is_pos_SO (ST phi x) i.
Proof.
  induction phi; intros x i;
    try destruct p; destruct x;
    try (simpl;
    unfold occ_in_alpha; simpl;
    case (beq_nat i 0);
      try reflexivity;
    simpl; do 2 rewrite List.app_length;
    do 2 rewrite <- pv_in__preds_in;
    rewrite <- IHphi1;
    rewrite <- IHphi2;
    reflexivity).

    simpl.
    rewrite <- IHphi.
    rewrite occ_in_alpha_negSO.
    unfold occ_in_alpha.
    rewrite <- pv_in__preds_in.
    reflexivity.

    rewrite is_pos_SO_box.
    case_eq (beq_nat i 0); intros Hbeq. 
      rewrite (beq_nat_true _ _ Hbeq).
      rewrite is_pos_SO_0.
      reflexivity.

      simpl; rewrite (IHphi (Var n));
      rewrite Hbeq;
      case_eq (Nat.leb i (length (pv_in phi))); intros Hleb;
        [reflexivity |];
        case_eq (is_pos_SO (ST phi (Var n )) i); intros Hpos;
          [apply is_pos_SO_occ in Hpos | reflexivity];
          unfold occ_in_alpha in Hpos;
          rewrite Hbeq in Hpos;
          rewrite <- pv_in__preds_in in Hpos;
          rewrite Hleb in Hpos;
          discriminate.

    rewrite is_pos_SO_diam.
    case_eq (beq_nat i 0); intros Hbeq. 
      rewrite (beq_nat_true _ _ Hbeq).
      rewrite is_pos_SO_0.
      reflexivity.

      simpl; rewrite (IHphi (Var n));
      rewrite Hbeq;
      case_eq (Nat.leb i (length (pv_in phi))); intros Hleb;
        [reflexivity |];
        case_eq (is_pos_SO (ST phi (Var n )) i); intros Hpos;
          [apply is_pos_SO_occ in Hpos | reflexivity];
          unfold occ_in_alpha in Hpos;
          rewrite Hbeq in Hpos;
          rewrite <- pv_in__preds_in in Hpos;
          rewrite Hleb in Hpos;
          discriminate.
Qed.


Lemma is_pos_SO_conjSO_l : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_alpha alpha1 i = true ->
    is_pos_SO (conjSO alpha1 alpha2) i = is_pos_SO alpha1 i.
Proof.
  intros alpha1 alpha2 i Hocc.
  simpl.
  rewrite occ_in_alpha_conjSO2_rev.
  apply occ_in_alpha_leb2 in Hocc.
  destruct Hocc as [H1 H2].
  rewrite H2.
  reflexivity.

  left; assumption.
Qed.

Lemma is_pos_SO_disjSO_l : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_alpha alpha1 i = true ->
    is_pos_SO (disjSO alpha1 alpha2) i = is_pos_SO alpha1 i.
Proof.
  intros alpha1 alpha2 i Hocc.
  simpl.
  rewrite occ_in_alpha_disjSO2_rev.
  apply occ_in_alpha_leb2 in Hocc.
  destruct Hocc as [H1 H2].
  rewrite H2.
  reflexivity.

  left; assumption.
Qed.


Lemma is_pos_SO_implSO_l_t : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_alpha alpha1 i = true ->
    is_pos_SO (implSO alpha1 alpha2) i = true -> is_pos_SO alpha1 i = false.
Proof.
  intros alpha1 alpha2 i Hocc.
  simpl.
  rewrite occ_in_alpha_implSO2_rev.
  apply occ_in_alpha_leb2 in Hocc.
  destruct Hocc as [H1 H2].
  rewrite H2.
  case_eq (is_pos_SO alpha1 i); intros H H3.
    discriminate.
    reflexivity.

  left; assumption.
Qed.


Lemma is_pos_SO_conjSO_r : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_alpha alpha1 i = false ->
    occ_in_alpha alpha2 (i - length (preds_in alpha1)) = true ->
      is_pos_SO (conjSO alpha1 alpha2) i = 
        is_pos_SO alpha2 (i - length( preds_in alpha1)).
Proof.
  intros alpha1 alpha2 i Hocc1 Hocc2.
  simpl.
  assert (occ_in_alpha (conjSO alpha1 alpha2) i = true) as H.
    unfold occ_in_alpha.
    apply occ_in_alpha_leb2 in Hocc2.
    simpl.
    destruct Hocc2 as [Ha Hb].
    rewrite (beq_nat_zero_minus _ _ Ha).
    rewrite List.app_length.
    assert (Nat.leb i (length (preds_in alpha1) + 
                  length (preds_in alpha2)) = true)
          as H2.
    rewrite leb_plus_pre with (m := length (preds_in alpha1)) in Hb.
    rewrite arith_plus_comm in Hb.
    rewrite arith_plus_minus_assoc in Hb.
    rewrite arith_minus_refl in Hb.
    rewrite arith_minus_zero in Hb.
    assumption.

    apply occ_in_alpha_f in Hocc1.
    destruct Hocc1 as [Hocc1 | Hocc1].
      rewrite (beq_nat_true _ _ Hocc1) in *.
      simpl in *.
      discriminate.

      apply leb_switch; assumption.

    apply leb_refl.

    rewrite H2.
    reflexivity.

    rewrite H.
    apply occ_in_alpha_leb2 in H.
    apply occ_in_alpha_f in Hocc1.
    destruct Hocc1 as [Hocc1 | Hocc1].
      rewrite (beq_nat_true _ _ Hocc1) in *.
      simpl in *. 
      discriminate.

      rewrite Hocc1.
      reflexivity.
Qed.


Lemma is_pos_SO_disjSO_r : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_alpha alpha1 i = false ->
    occ_in_alpha alpha2 (i - length (preds_in alpha1)) = true ->
      is_pos_SO (disjSO alpha1 alpha2) i = 
        is_pos_SO alpha2 (i - length( preds_in alpha1)).
Proof.
  intros alpha1 alpha2 i Hocc1 Hocc2.
  simpl.
  assert (occ_in_alpha (disjSO alpha1 alpha2) i = true) as H.
    unfold occ_in_alpha.
    apply occ_in_alpha_leb2 in Hocc2.
    simpl.
    destruct Hocc2 as [Ha Hb].
    rewrite (beq_nat_zero_minus _ _ Ha).
    rewrite List.app_length.
    assert (Nat.leb i (length (preds_in alpha1) + 
                  length (preds_in alpha2)) = true)
          as H2.
    rewrite leb_plus_pre with (m := length (preds_in alpha1)) in Hb.
    rewrite arith_plus_comm in Hb.
    rewrite arith_plus_minus_assoc in Hb.
    rewrite arith_minus_refl in Hb.
    rewrite arith_minus_zero in Hb.
    assumption.

    apply occ_in_alpha_f in Hocc1.
    destruct Hocc1 as [Hocc1 | Hocc1].
      rewrite (beq_nat_true _ _ Hocc1) in *.
      simpl in *.
      discriminate.

      apply leb_switch; assumption.

    apply leb_refl.

    rewrite H2.
    reflexivity.

    rewrite H.
    apply occ_in_alpha_leb2 in H.
    apply occ_in_alpha_f in Hocc1.
    destruct Hocc1 as [Hocc1 | Hocc1].
      rewrite (beq_nat_true _ _ Hocc1) in *.
      simpl in *. 
      discriminate.

      rewrite Hocc1.
      reflexivity.
Qed.


Lemma is_pos_SO_implSO_r : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_alpha alpha1 i = false ->
    occ_in_alpha alpha2 (i - length (preds_in alpha1)) = true ->
      is_pos_SO (implSO alpha1 alpha2) i = 
        is_pos_SO alpha2 (i - length( preds_in alpha1)).
Proof.
  intros alpha1 alpha2 i Hocc1 Hocc2.
  simpl.
  assert (occ_in_alpha (implSO alpha1 alpha2) i = true) as H.
    unfold occ_in_alpha.
    apply occ_in_alpha_leb2 in Hocc2.
    simpl.
    destruct Hocc2 as [Ha Hb].
    rewrite (beq_nat_zero_minus _ _ Ha).
    rewrite List.app_length.
    assert (Nat.leb i (length (preds_in alpha1) + 
                  length (preds_in alpha2)) = true)
          as H2.
    rewrite leb_plus_pre with (m := length (preds_in alpha1)) in Hb.
    rewrite arith_plus_comm in Hb.
    rewrite arith_plus_minus_assoc in Hb.
    rewrite arith_minus_refl in Hb.
    rewrite arith_minus_zero in Hb.
    assumption.

    apply occ_in_alpha_f in Hocc1.
    destruct Hocc1 as [Hocc1 | Hocc1].
      rewrite (beq_nat_true _ _ Hocc1) in *.
      simpl in *.
      discriminate.

      apply leb_switch; assumption.

    apply leb_refl.

    rewrite H2.
    reflexivity.

    rewrite H.
    apply occ_in_alpha_leb2 in H.
    apply occ_in_alpha_f in Hocc1.
    destruct Hocc1 as [Hocc1 | Hocc1].
      rewrite (beq_nat_true _ _ Hocc1) in *.
      simpl in *. 
      discriminate.

      rewrite Hocc1.
      reflexivity.
Qed.


Lemma is_pos_SO_negSO : forall (alpha : SecOrder) (i : nat),
  is_pos_SO (negSO alpha) i = true ->
    is_pos_SO alpha i = false.
Proof.
  intros.
  simpl in *.
  case_eq (occ_in_alpha (negSO alpha) i); intros Hocc; rewrite Hocc in *.
    case_eq (is_pos_SO alpha i); intros Hpos; rewrite Hpos in *.
      discriminate.

      reflexivity.

    discriminate.
Qed.


Lemma is_pos_SO_negSO2 : forall (alpha : SecOrder) (i : nat),
  occ_in_alpha alpha i = true ->
    is_pos_SO alpha i = false ->
      is_pos_SO (negSO alpha) i = true.
Proof.
  intros alpha i Hocc Hpos.
  simpl in *.
  rewrite occ_in_alpha_negSO.
  rewrite Hocc.
  rewrite Hpos.
  reflexivity.
Qed.

Lemma is_pos_SO_implSO_r2 : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_alpha alpha1 i = false ->
  is_pos_SO (implSO alpha1 alpha2) i = true ->
  is_pos_SO alpha2 (i - (length (preds_in alpha1))) = true.
Proof.
  intros alpha1 alpha2 i Hocc Hpos.
  simpl in Hpos.
  case_eq (occ_in_alpha (implSO alpha1 alpha2) i); intros Hocc2;
    rewrite Hocc2 in *.
    apply occ_in_alpha_implSO2_fwd in Hocc2.
    destruct Hocc2 as [Hocc2 | Hocc2].
      rewrite Hocc2 in *; discriminate. 

      apply occ_in_alpha_f in Hocc.
      destruct Hocc as [H1 | H2].
        rewrite (beq_nat_true _ _ H1) in *.
        simpl in *.
        rewrite occ_in_alpha_0 in Hocc2.
        discriminate.

        rewrite H2 in *.
        assumption.

      discriminate.
Qed.

Lemma is_pos_SO_implSO_l2 : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_alpha alpha1 i = true ->
  is_pos_SO (implSO alpha1 alpha2) i = true ->
  is_pos_SO alpha1 i = false.
Proof.
  intros alpha1 alpha2 i Hocc Hpos.
  simpl in Hpos.
  apply occ_in_alpha_leb2 in Hocc.
  destruct Hocc as [H1 H2].
  rewrite H2 in Hpos.
  assert (occ_in_alpha (implSO alpha1 alpha2) i = true).
    unfold occ_in_alpha.
    rewrite H1.
    simpl.
    rewrite List.app_length.
    apply leb_plus_r with (m := length (preds_in alpha2)) in H2.
    rewrite H2.
    reflexivity.

    rewrite H in Hpos.
    case_eq (is_pos_SO alpha1 i); intros Hpos2.
      rewrite Hpos2 in *.
      discriminate.

      reflexivity.
Qed.


Lemma is_pos_SO_implSO_f : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_alpha (implSO alpha1 alpha2) i = true ->
  is_pos_SO (implSO alpha1 alpha2) i = false ->
  (occ_in_alpha alpha1 i = true -> is_pos_SO alpha1 i = true) /\
  (occ_in_alpha alpha2 (i - (length (preds_in alpha1))) = true ->
    is_pos_SO alpha2 (i - (length (preds_in alpha1))) = false).
Proof.
  intros alpha1 alpha2 i Hocc Hpos.
  apply conj; intros H.
    simpl in Hpos.
    rewrite Hocc in Hpos.
    destruct (occ_in_alpha_leb2 _ _ H) as [H1 H2].
    rewrite H2 in Hpos.
    case_eq (is_pos_SO alpha1 i); intros Hpos2.
      reflexivity.

      rewrite Hpos2 in *.
      discriminate.

    simpl in Hpos.
    rewrite Hocc in Hpos.
    destruct (occ_in_alpha_leb2 _ _ H) as [H1 H2].
    apply beq_nat_leb_f in H1.
    destruct (leb_switch_t _ _ H1) as [Ha | Hb].
      rewrite (beq_nat_true _ _ Ha).
      rewrite arith_minus_refl. 
      apply is_pos_SO_0.

      rewrite Hb in *.
      assumption.
Qed.

Lemma is_pos_SO_implSO_f2 : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_alpha (implSO alpha1 alpha2) i = true ->
  is_pos_SO (implSO alpha1 alpha2) i = false ->
  (occ_in_alpha alpha1 i = true -> is_pos_SO alpha1 i = true) /\
  (occ_in_alpha alpha1 i = false ->
    is_pos_SO alpha2 (i - (length (preds_in alpha1))) = false).
Proof.
  intros alpha1 alpha2 i Hocc Hpos.
  destruct (is_pos_SO_implSO_f _ _ _ Hocc Hpos) as [H1 H2].
  apply conj; intros H.
    apply H1; assumption.

    apply H2.
    destruct (occ_in_alpha_implSO2_fwd _ _ _ Hocc) as [Ha | Hb].
      rewrite Ha in *; discriminate.

      assumption.
Qed.


Lemma is_pos_SO_allSO : forall (alpha : SecOrder) (Q : predicate) (i : nat),
  occ_in_alpha alpha i = true ->
  is_pos_SO (allSO Q alpha) (S i) = is_pos_SO alpha i.
Proof.
  intros alpha Q i H.
  simpl.
  rewrite occ_in_alpha_allSO.
  simpl.
  rewrite arith_minus_zero.
  rewrite H.
  rewrite if_then_else_true.
  destruct Q.
  case_eq i.
    intros Hi; rewrite Hi in *; discriminate.

    intros j Hi; rewrite Hi in *.
    reflexivity.
Qed.


Lemma is_pos_SO_exSO : forall (alpha : SecOrder) (Q : predicate) (i : nat),
  occ_in_alpha alpha i = true ->
  is_pos_SO (exSO Q alpha) (S i) = is_pos_SO alpha i.
Proof.
  intros alpha Q i H.
  simpl.
  rewrite occ_in_alpha_exSO.
  simpl.
  rewrite arith_minus_zero.
  rewrite H.
  rewrite if_then_else_true.
  destruct Q.
  case_eq i.
    intros Hi; rewrite Hi in *; discriminate.

    intros j Hi; rewrite Hi in *.
    reflexivity.
Qed.




(* ------------------------------------------------------------ *)

Lemma P_is_pos_SO_allFO  : forall (alpha : SecOrder) (x : FOvariable) (P : predicate),
  P_is_pos_SO (allFO x alpha) P <-> P_is_pos_SO alpha P.
Proof.
  intros.
  unfold P_is_pos_SO.
  destruct P as [Pn].
  split; intros H;
    apply conj.
      intros Hpocc i Hocc Heq.
      rewrite <- is_pos_SO_allFO with (x := x).
      apply H; assumption.

      intros Hpocc.
      apply H; assumption.

      intros Hpocc i Hocc Heq.
      rewrite is_pos_SO_allFO.
      rewrite occ_in_alpha_allFO in Hocc.
      rewrite <- P_occurs_in_alpha_allFO in Hpocc.
      apply H; assumption.

      rewrite <- P_occurs_in_alpha_allFO.
      intros H2; apply H; assumption.
Qed.

Lemma P_is_pos_SO_exFO  : forall (alpha : SecOrder) (x : FOvariable) (P : predicate),
  P_is_pos_SO (exFO x alpha) P <-> P_is_pos_SO alpha P.
Proof.
  intros.
  unfold P_is_pos_SO.
  destruct P as [Pn].
  rewrite <- P_occurs_in_alpha_exFO.
  split; intros H;
    apply conj.
      intros Hpocc i Hocc Heq.
      rewrite <- is_pos_SO_exFO with (x := x).
      destruct H as [H _].
      specialize (H Hpocc i).
      rewrite occ_in_alpha_exFO in H.
      simpl in *; destruct x.
      apply H; try assumption.

      apply H.

      intros Hpocc i Hocc Heq.
      rewrite is_pos_SO_exFO.
      rewrite occ_in_alpha_exFO in Hocc.
      destruct x. simpl in *.
      apply H; assumption.

      apply H.
Qed.


(*
Lemma is_pos_box : forall (phi : Modal) (i : nat),
  is_pos (box phi) i = if occ_in_phi (box phi) i then is_pos phi i
                                                 else false.
Proof.
  reflexivity.
Qed.
*)

(* ------------------------------------------------------ *)


Lemma p_occ__ST_conjSO : forall (phi1 phi2 : Modal) (x : FOvariable) (p : propvar),
  (P_occurs_in_l (preds_in (ST phi1 x)) (ST_pv p) = p_occurs_in_l (pv_in phi1) p) ->
  (P_occurs_in_l (preds_in (ST phi2 x)) (ST_pv p) = p_occurs_in_l (pv_in phi2) p) ->
  (P_occurs_in_l (preds_in (ST (mconj phi1 phi2) x)) (ST_pv p) = p_occurs_in_l (pv_in (mconj phi1 phi2)) p).
Proof.
  intros phi1 phi2 x p IHphi1 IHphi2; simpl.
  case_eq (P_occurs_in_l (app (preds_in (ST phi1 x)) (preds_in (ST phi2 x))) (ST_pv p));
    intros HPocc.
    apply P_occurs_in_l_app in HPocc.
    destruct HPocc as [H1 | H2].
      case_eq ( p_occurs_in_l (pv_in phi1 ++ pv_in phi2) p); intros Hpocc.
        apply p_occurs_in_l_app in Hpocc.
        destruct Hpocc as [Ha | Hb];
          reflexivity.

        apply (contrapos_bool_or _ _ _ (p_occurs_in_l_app _ _ _)) in Hpocc.
        destruct Hpocc as [Ha Hb].
        rewrite <- IHphi1 in Ha.
        rewrite Ha in *; discriminate.

      case_eq (p_occurs_in_l (pv_in phi1 ++ pv_in phi2) p); intros Hpocc.
        apply p_occurs_in_l_app in Hpocc.
        destruct Hpocc as [Ha | Hb];
          reflexivity.

        apply (contrapos_bool_or _ _ _ (p_occurs_in_l_app _ _ _)) in Hpocc.
        destruct Hpocc as [Ha Hb].
        rewrite <- IHphi2 in Hb.
        rewrite Hb in *; discriminate.

    apply (contrapos_bool_or _ _ _ (P_occurs_in_l_app _ _ _)) in HPocc.
    destruct HPocc as [H1 H2].
    case_eq (p_occurs_in_l (pv_in phi1 ++ pv_in phi2) p); intros Hpocc.
      apply p_occurs_in_l_app in Hpocc.
      rewrite <- IHphi1 in Hpocc; rewrite <- IHphi2 in Hpocc.
      rewrite H1 in Hpocc; rewrite H2 in Hpocc.
      destruct Hpocc as [Ha | Hb]; discriminate.

      reflexivity.
Qed.


Lemma p_occ__ST : forall (phi : Modal) (x : FOvariable) (p : propvar),
  P_occurs_in_alpha (ST phi x) (ST_pv p) = p_occurs_in_phi phi p.
Proof.
  unfold P_occurs_in_alpha.
  unfold p_occurs_in_phi.
  induction phi;
  intros x q.
    destruct p as [pn]; destruct x as [xn]; destruct q as [qm].
    reflexivity.

    simpl; apply IHphi.

    apply p_occ__ST_conjSO; [apply IHphi1 | apply IHphi2].
    apply p_occ__ST_conjSO; [apply IHphi1 | apply IHphi2].
    apply p_occ__ST_conjSO; [apply IHphi1 | apply IHphi2].

    destruct x as [xn]; simpl.
    rewrite IHphi; reflexivity.

    destruct x as [xn]; simpl.
    rewrite IHphi; reflexivity.
Qed.


Lemma p_is_pos__SO : forall (phi : Modal) (x : FOvariable)
                            (p : propvar),
  p_is_pos phi p <-> P_is_pos_SO (ST phi x) (ST_pv p).
Proof.
  intros phi x p.
  unfold p_is_pos.
  unfold P_is_pos_SO.
  split; intros H;
    (apply conj; [intros Hpocc i Hocc Heq|]).
      rewrite <- is_pos__ST; apply H.
        rewrite <- p_occ__ST with (x := x); assumption.

        rewrite <- occ_in_ST in Hocc; assumption.
  
        destruct p as [n]. simpl in *.
        pose proof (at_pv_ST phi x i) as Hat.
        case_eq (at_pred (preds_in (ST phi x)) i); intros Pn H2;
          rewrite H2 in *;
        case_eq (at_pv (pv_in phi) i); intros pn H3;
          rewrite H3 in *. 
          rewrite Hat; assumption.

      intros HPocc.
      apply H.
      rewrite p_occ__ST in HPocc.
      assumption.

      rewrite is_pos__ST with (x := x); apply H.
        rewrite p_occ__ST; assumption.

        rewrite <- occ_in_ST; assumption.
  
        destruct p as [n]. simpl in *.
        pose proof (at_pv_ST phi x i) as Hat.
        case_eq (at_pred (preds_in (ST phi x)) i); intros Pn H2;
          rewrite H2 in *;
        case_eq (at_pv (pv_in phi) i); intros pn H3;
          rewrite H3 in *. 
          rewrite Heq; assumption.

      intros HPocc.
      apply H.
      rewrite p_occ__ST.
      assumption.
Qed.

Lemma P_occurs_in_alpha__SO : forall (phi : Modal) (x : FOvariable)
                                     (P : predicate),
  P_occurs_in_alpha (ST phi x) P = true <->
    p_occurs_in_phi phi (ST_pred P) = true.
Proof.
  induction phi; intros x P;
  unfold p_occurs_in_phi in *;
  unfold P_occurs_in_alpha in *;
  try (    simpl in *;
    rewrite p_occurs_in_l_app;
    rewrite P_occurs_in_l_app;
    destruct (IHphi1 x P) as [fwd1  rev1];
    destruct (IHphi2 x P) as [fwd2  rev2];
    split; intros H; destruct H as [H | H];
      [left | right | left | right];
      [apply fwd1 | apply fwd2 | apply rev1 | apply rev2];
      assumption);
    try (    destruct x as [n]; simpl;
      apply IHphi).
    destruct p as [n]; destruct x as [xn].
    destruct P as [m].
    simpl.
    apply iff_refl.
Qed.


(* ----------------------------------------------------------------------------------- *)


Lemma uni_pos__SO : forall (phi : Modal) (x : FOvariable),
  uniform_pos phi <-> uniform_pos_SO (ST phi x).
Proof.
  intros phi x.
  unfold uniform_pos.
  unfold uniform_pos_SO.
  split; intros H p Hpocc; destruct p as [n].
    rewrite ST_pv_P.
    apply p_is_pos__SO.
    apply H.
    rewrite ST_pred_p;
    apply P_occurs_in_alpha__SO with (x := x);
    assumption.

    rewrite ST_pred_p.
    apply (p_is_pos__SO phi x (ST_pred (Pred n))).
    apply H.
    simpl.
    apply P_occurs_in_alpha__SO.
    simpl; assumption.
Qed.

Lemma uni_pos_SO_allFO : forall (alpha : SecOrder) (x : FOvariable),
  uniform_pos_SO (allFO x alpha) <-> uniform_pos_SO alpha.
Proof.
  intros alpha x.
  unfold uniform_pos_SO.
  split;
    intros H P H2;
    specialize (H P);
    rewrite <- P_occurs_in_alpha_allFO in *;
    rewrite P_is_pos_SO_allFO in *;
    apply H; assumption.
Qed.

(* ---------------------------------------------------------------------------------- *)

(* ---------------------------------------------------------------------------------- *)

Lemma P_not_occ_alt : forall (alpha : SecOrder) (P : predicate)
                              (W : Set) (Iv : FOvariable -> W)
                             (Ip : predicate -> W -> Prop)
                             (Ir : W -> W -> Prop)
                              (pa : W -> Prop),
  P_occurs_in_alpha alpha P = false -> 
    SOturnst W Iv Ip Ir alpha <->
      SOturnst W Iv (alt_Ip Ip pa P) Ir alpha.
Proof.
  induction alpha.
    intros P W Iv Ip Ir pa HPocc.
    split; intros SOt.
      destruct P as [Pn]; destruct p as [Qm]; destruct f as [xn].
      unfold P_occurs_in_alpha in HPocc.
      simpl in *.
      case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *.
        discriminate.

        assumption.

      destruct P as [Pn]; destruct p as [Qm]; destruct f as [xn].
      unfold P_occurs_in_alpha in HPocc.
      simpl in *.
      case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *.
        discriminate.

        assumption.

    intros P W Iv Ip Ir pa HPocc.
    destruct f; destruct f0.
    simpl in *.
    apply iff_refl.

    intros P W Iv Ip Ir pa HPocc.
    destruct f; destruct f0.
    simpl in *.
    apply iff_refl.

    intros P W Iv Ip Ir pa HPocc;
    rewrite <- P_occurs_in_alpha_allFO in HPocc.
    destruct f as [xn].
    do 2 rewrite SOturnst_allFO in *.
    split; intros SOt d.
      apply IHalpha.
        assumption.
        apply SOt.

        specialize (IHalpha P W (alt_Iv Iv d (Var xn)) Ip Ir pa HPocc).
        apply IHalpha; apply SOt.

    intros P W Iv Ip Ir pa HPocc;
    rewrite <- P_occurs_in_alpha_exFO in HPocc.
    destruct f as [xn].
    do 2 rewrite SOturnst_exFO in *.
    split; intros SOt; destruct SOt as [d SOt];
      exists d.
      apply IHalpha.
        assumption.
        apply SOt.

        specialize (IHalpha P W (alt_Iv Iv d (Var xn)) Ip Ir pa HPocc).
        apply IHalpha; apply SOt.

    intros P W Iv Ip Ir pa HPocc.
    do 2 rewrite SOturnst_negSO in *.
    rewrite <- P_occurs_in_alpha_negSO in HPocc.
    split; intros SOt; unfold not in *; intros SOt2; apply SOt;
      specialize (IHalpha P W Iv Ip Ir pa);
        apply IHalpha; assumption.

    intros P W Iv Ip Ir pa HPocc.
    simpl.
    case_eq (P_occurs_in_alpha alpha1 P); intros HPocc1.
      assert (P_occurs_in_alpha alpha1 P = true \/
                P_occurs_in_alpha alpha2 P = true) as H.
        left; assumption.
      apply P_occurs_in_alpha_conjSO in H.
      rewrite H in HPocc; discriminate.

    case_eq (P_occurs_in_alpha alpha2 P); intros HPocc2.
      assert (P_occurs_in_alpha alpha1 P = true \/
                P_occurs_in_alpha alpha2 P = true) as H.
        right; assumption.
      apply P_occurs_in_alpha_conjSO in H.
      rewrite H in HPocc; discriminate.

      specialize (IHalpha1 P W Iv Ip Ir pa HPocc1).
      specialize (IHalpha2 P W Iv Ip Ir pa HPocc2).
      split; intros H;
        (apply conj;
          [apply IHalpha1; apply H |
          apply IHalpha2; apply H]).

    intros P W Iv Ip Ir pa HPocc.
    simpl.
    case_eq (P_occurs_in_alpha alpha1 P); intros HPocc1.
      assert (P_occurs_in_alpha alpha1 P = true \/
                P_occurs_in_alpha alpha2 P = true) as H.
        left; assumption.
      apply P_occurs_in_alpha_disjSO in H.
      rewrite H in HPocc; discriminate.

    case_eq (P_occurs_in_alpha alpha2 P); intros HPocc2.
      assert (P_occurs_in_alpha alpha1 P = true \/
                P_occurs_in_alpha alpha2 P = true) as H.
        right; assumption.
      apply P_occurs_in_alpha_disjSO in H.
      rewrite H in HPocc; discriminate.

      specialize (IHalpha1 P W Iv Ip Ir pa HPocc1).
      specialize (IHalpha2 P W Iv Ip Ir pa HPocc2).
      split; intros H; (destruct H;
        [left; apply IHalpha1 | right; apply IHalpha2]; apply H).

    intros P W Iv Ip Ir pa HPocc.
    simpl.
    case_eq (P_occurs_in_alpha alpha1 P); intros HPocc1.
      assert (P_occurs_in_alpha alpha1 P = true \/
                P_occurs_in_alpha alpha2 P = true) as H.
        left; assumption.
      apply P_occurs_in_alpha_implSO in H.
      rewrite H in HPocc; discriminate.

    case_eq (P_occurs_in_alpha alpha2 P); intros HPocc2.
      assert (P_occurs_in_alpha alpha1 P = true \/
                P_occurs_in_alpha alpha2 P = true) as H.
        right; assumption.
      apply P_occurs_in_alpha_implSO in H.
      rewrite H in HPocc; discriminate.

      specialize (IHalpha1 P W Iv Ip Ir pa HPocc1).
      specialize (IHalpha2 P W Iv Ip Ir pa HPocc2).
      split; intros H H2;
        apply IHalpha2; apply H; 
        apply IHalpha1; assumption.

    intros P W Iv Ip Ir pa HPocc.
    simpl in HPocc.
    destruct P as [Pn]; destruct p as [Qm].
    pose proof (contrapos_bool_or
                (P_occurs_in_alpha (allSO (Pred Qm) alpha) (Pred Pn))
                (beq_nat Pn Qm)
                (P_occurs_in_alpha alpha (Pred Pn))
                (P_occurs_in_alpha_allSO alpha (Pred Qm) (Pred Pn))) as H.
    apply H in HPocc.
    do 2 rewrite SOturnst_allSO.
    destruct HPocc as [Hf HPocc].
    split; intros SOt pa2.
      rewrite alt_Ip_switch.
        apply IHalpha.
          assumption.

          apply SOt.

          unfold not; intros Hneq.
          rewrite Hneq in Hf; rewrite <- beq_nat_refl in Hf; discriminate.

      specialize (SOt pa2).
      specialize (IHalpha (Pred Pn) W Iv (alt_Ip Ip pa2 (Pred Qm))
                     Ir pa HPocc).
      apply IHalpha.
        rewrite alt_Ip_switch.
        assumption.

        unfold not; intros Hneq.
        rewrite Hneq in Hf; rewrite <- beq_nat_refl in Hf; discriminate.

    intros P W Iv Ip Ir pa HPocc.
    simpl in HPocc.
    destruct P as [Pn]; destruct p as [Qm].
    pose proof (contrapos_bool_or
                (P_occurs_in_alpha (allSO (Pred Qm) alpha) (Pred Pn))
                (beq_nat Pn Qm)
                (P_occurs_in_alpha alpha (Pred Pn))
                (P_occurs_in_alpha_allSO alpha (Pred Qm) (Pred Pn))) as H.
    apply H in HPocc.
    do 2 rewrite SOturnst_exSO.
    destruct HPocc as [Hf HPocc].
    split; intros SOt; destruct SOt as [pa2 SOt]; exists pa2.
      rewrite alt_Ip_switch.
        apply IHalpha.
          assumption.

          apply SOt.

          unfold not; intros Hneq.
          rewrite Hneq in Hf; rewrite <- beq_nat_refl in Hf; discriminate.

      specialize (IHalpha (Pred Pn) W Iv (alt_Ip Ip pa2 (Pred Qm))
                     Ir pa HPocc).
      apply IHalpha.
        rewrite alt_Ip_switch.
        assumption.

        unfold not; intros Hneq.
        rewrite Hneq in Hf; rewrite <- beq_nat_refl in Hf; discriminate.
Qed.

Lemma P_is_pos_occ : forall (alpha : SecOrder) (P : predicate),
  P_is_pos_SO alpha P -> P_occurs_in_alpha alpha P = true.
Proof.
  intros alpha P H.
  unfold P_is_pos_SO in H.
  destruct H as [Ht Hf].
  case_eq (P_occurs_in_alpha alpha P); intros H.
    reflexivity.

    specialize (Hf H); contradiction.
Qed.

Lemma P_is_pos_SO_conjSO_l : forall (alpha1 alpha2 : SecOrder) 
                                    (P : predicate),
  P_occurs_in_alpha alpha1 P = true ->
  P_is_pos_SO (conjSO alpha1 alpha2) P ->
  P_is_pos_SO alpha1 P.
Proof.
  intros alpha1 alpha2 P Hpocc Hpos.
  unfold P_is_pos_SO in Hpos.
  destruct Hpos as [Ha _]. 
  unfold P_is_pos_SO.
  apply conj.
    intros Hpocc2 i Hocc Hw .
    rewrite P_occurs_in_alpha_conjSO in Ha.
    assert (P_occurs_in_alpha alpha1 P = true \/ 
              P_occurs_in_alpha alpha2 P = true) as H.
      left; assumption.
    specialize (Ha H i).
    rewrite occ_in_alpha_conjSO2 in Ha.
    assert (occ_in_alpha alpha1 i = true \/
     occ_in_alpha alpha2 (i - length (preds_in alpha1)) = true)
      as H2.
      left; assumption.
    simpl in *.
    rewrite at_pred_app_l in Ha.
    specialize (Ha H2 Hw).
    assert (occ_in_alpha (conjSO alpha1 alpha2) i = true) as H3.
      rewrite occ_in_alpha_conjSO2.
      assumption.
    rewrite H3 in *.
    apply occ_in_alpha_leb2 in Hocc.
    destruct Hocc as [_ Hocc].
    rewrite Hocc in *.
    assumption.
      apply PeanoNat.Nat.leb_le.
      apply occ_in_alpha_leb2.
      assumption.

  intros.
  rewrite H in Hpocc.
  discriminate.
Qed.


Lemma P_is_pos_SO_conjSO_r : forall (alpha1 alpha2 : SecOrder) 
                                    (P : predicate),
  P_occurs_in_alpha alpha2 P = true ->
  P_is_pos_SO (conjSO alpha1 alpha2) P ->
  P_is_pos_SO alpha2 P.
Proof.
  intros alpha1 alpha2 P Hpocc Hpos.
  unfold P_is_pos_SO in Hpos.
  destruct Hpos as [Ha _]. 
  unfold P_is_pos_SO.
  apply conj.
    intros Hpocc2 i Hocc Hw .
    rewrite P_occurs_in_alpha_conjSO in Ha.
    assert (P_occurs_in_alpha alpha1 P = true \/ 
              P_occurs_in_alpha alpha2 P = true) as H.
      right; assumption.
    specialize (Ha H ((length (preds_in alpha1)) + i)).
    rewrite occ_in_alpha_conjSO2 in Ha.
    assert (occ_in_alpha alpha1 (length(preds_in alpha1) + i) = true \/
     occ_in_alpha alpha2 i = true)
      as H2.
      right; assumption.
    simpl in *.
    rewrite at_pred_app_r in Ha.
    rewrite arith_plus_3 in Ha.
    specialize (Ha H2 Hw).
    assert (occ_in_alpha (conjSO alpha1 alpha2) 
            (length(preds_in alpha1) + i) = true) as H3.
      rewrite occ_in_alpha_conjSO2.
      rewrite arith_plus_3.
      assumption.
    rewrite H3 in *.
    rewrite leb_plus_l in Ha.
    rewrite leb_beq_zero in Ha.
    case_eq (beq_nat i 0); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq) in *.
      simpl in *.
      discriminate.

      rewrite Hbeq in *.
      assumption.

    case_eq (beq_nat i 0); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq) in *.
      simpl in *.
      discriminate.

      reflexivity.

    intros H; rewrite H in *; discriminate.
Qed.

Lemma P_occurs_in_alpha_allSO2 : forall (alpha : SecOrder)
                                        (Q P: predicate),
  P_occurs_in_alpha alpha P = true ->
  P_occurs_in_alpha (allSO Q alpha) P = true.
Proof.
  intros alpha Q P H.
  apply P_occurs_in_alpha_allSO.
  destruct P as [Pn]; destruct Q as [Qm].
  right; assumption.
Qed.

Lemma P_is_pos_SO_allSO : forall (alpha : SecOrder) (P Q : predicate),
P_occurs_in_alpha alpha P = true ->
P_is_pos_SO (allSO Q alpha) P -> P_is_pos_SO alpha P.
Proof.
  intros alpha P Q Hpocc.
  unfold P_is_pos_SO.
  intros Hpos.
  destruct Hpos as [H1 H2].
  apply conj.
    intros Hpocc2 i Hocc Heq.
    destruct P as [Pn].
    apply P_occurs_in_alpha_allSO2 with (Q := Q)in Hpocc.
    specialize (H1 Hpocc (S i)).
    rewrite occ_in_alpha_allSO in H1.
    simpl beq_nat in *.
    case_eq i.
      intros Hi; rewrite Hi in *; discriminate.

      intros j Hi; rewrite Hi in *.
      simpl beq_nat in *.
      simpl minus in *.
      assert ((if false then true else occ_in_alpha alpha (S j)) = true) as H3. 
        simpl; assumption.
      specialize (H1 H3); clear H3.
      simpl preds_in in H1.
      destruct Q as [Qm].
      rewrite at_pred_cons in H1.
      specialize (H1 Heq).
      rewrite is_pos_SO_allSO in H1.
      assumption.

      assumption.

      intros H; rewrite H in *; discriminate.
Qed.

Lemma P_is_pos_SO_exSO : forall (alpha : SecOrder) (P Q : predicate),
P_occurs_in_alpha alpha P = true ->
P_is_pos_SO (exSO Q alpha) P -> P_is_pos_SO alpha P.
Proof.
  intros alpha P Q Hpocc.
  unfold P_is_pos_SO.
  intros Hpos.
  destruct Hpos as [H1 H2].
  apply conj.
    intros Hpocc2 i Hocc Heq.
    destruct P as [Pn].
    apply P_occurs_in_alpha_allSO2 with (Q := Q)in Hpocc.
    specialize (H1 Hpocc (S i)).
    rewrite occ_in_alpha_exSO in H1.
    simpl beq_nat in *.
    case_eq i.
      intros Hi; rewrite Hi in *; discriminate.

      intros j Hi; rewrite Hi in *.
      simpl beq_nat in *.
      simpl minus in *.
      assert ((if false then true else occ_in_alpha alpha (S j)) = true) as H3. 
        simpl; assumption.
      specialize (H1 H3); clear H3.
      simpl preds_in in H1.
      destruct Q as [Qm].
      rewrite at_pred_cons in H1.
      specialize (H1 Heq).
      rewrite is_pos_SO_exSO in H1.
      assumption.

      assumption.

      intros H; rewrite H in *; discriminate.
Qed.