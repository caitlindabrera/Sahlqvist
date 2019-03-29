Require Import SecOrder EqNat my_arith__my_leb_nat
               my_bool Modal ST_setup occ_in_phi ST_setup
               Unary_Predless at_pred. (* Uniform_Defns.
(* Require Import p_is_pos.
Require Import p_occurs_in.
Require Import P_occurs_in_alpha.
Require Import ST_setup.
Require Import Correctness_ST Correctness_ST_world_model.
Require Import List_machinery_impl.
Require Import Monotonicity.
Require Import Uniform8.
*)
Require Import Arith.EqNat Bool my_arith__my_leb_nat P_occurs_in_alpha my_bool my_length_gen.
Require Import p_is_pos p_occurs_in is_pos_neg occ_in_phi at_pv Unary_Predless.
Require Import List_machinery_impl P_occurs_in_alpha at_pred My_Prop.
*)

Definition occ_in_alpha (alpha : SecOrder) (i : nat) : bool :=
  if beq_nat i 0 
    then false
    else if Nat.leb i (length (preds_in alpha))
           then true
           else false.

(* -------------------------------------------------------------- *)

Lemma occ_in_alpha_defn : forall (alpha : SecOrder) (i : nat),
  occ_in_alpha alpha i =
  if beq_nat i 0 
    then false
    else if Nat.leb i (length (preds_in alpha))
           then true
           else false.
Proof.
  intros.
  unfold occ_in_alpha; induction alpha; simpl; reflexivity.
Qed.

Lemma occ_in_alpha_leb2 : forall (alpha : SecOrder) (n : nat),
  occ_in_alpha alpha n = true ->
    (beq_nat n 0 = false /\
      Nat.leb n (length (preds_in alpha)) = true).
Proof.
  intros alpha n Hocc.
  assert (beq_nat n 0 = false) as Hbeq.
    case_eq (beq_nat n 0); intros H; try reflexivity.
      pose proof (beq_nat_true n 0 H) as Heq; rewrite Heq in *.
      unfold occ_in_alpha in *; induction alpha; simpl; discriminate.
  apply conj.
    exact Hbeq.

    case_eq (Nat.leb n (length (preds_in alpha))); intros H;
    try reflexivity.
    unfold occ_in_alpha in *.
    induction alpha;
      rewrite H in *; rewrite Hbeq in *; discriminate.
Qed.


Lemma occ_in_alpha_leb3 : forall (alpha : SecOrder) (i n : nat),
  occ_in_alpha alpha (i - n) = true  ->
    Nat.leb n i = true.
Proof.
  intros alpha i n Hocc.
  apply occ_in_alpha_leb2 in Hocc.
  destruct Hocc as [H1 H2].
  apply beq_nat_leb_f in H1.
  assumption.
Qed. 

Lemma occ_in_alpha_allFO : forall (alpha : SecOrder) (x : FOvariable)
                                  (i : nat),
  occ_in_alpha (allFO x alpha) i = occ_in_alpha alpha i.
Proof.
  intros.
  unfold occ_in_alpha.
  reflexivity.
Qed.

Lemma occ_in_alpha_exFO : forall (alpha : SecOrder) (x : FOvariable)
                                  (i : nat),
  occ_in_alpha (exFO x alpha) i = occ_in_alpha alpha i.
Proof.
  intros.
  unfold occ_in_alpha.
  destruct x.
  reflexivity.
Qed.

Lemma occ_in_alpha_negSO : forall (alpha : SecOrder) (i : nat),
  occ_in_alpha (negSO alpha) i = occ_in_alpha alpha i.
Proof.
  intros.
  simpl.
  induction alpha;
    simpl;
    reflexivity.
Qed.

Lemma occ_in_alpha_conjSO : forall (alpha1 alpha2 : SecOrder) (i : nat),
  beq_nat i 0 = false ->
    occ_in_alpha (conjSO alpha1 alpha2) i =
      Nat.leb i (length (preds_in alpha1 ++ preds_in alpha2)).
Proof.
  intros.
  unfold occ_in_alpha.
  rewrite H.
  simpl.
  case (Nat.leb i (length (preds_in alpha1 ++ preds_in alpha2)));
    reflexivity.
Qed.

Lemma occ_in_alpha_conjSO2_fwd : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_alpha (conjSO alpha1 alpha2) i = true ->
    occ_in_alpha alpha1 i = true \/ 
      occ_in_alpha alpha2 (i - (length(preds_in alpha1))) = true.
Proof.
  intros.
  unfold occ_in_alpha in *.
  case_eq (beq_nat i 0); intros Hbeq; rewrite Hbeq in *.
    discriminate.

    simpl in *.
    rewrite List.app_length in H.
    case_eq (Nat.leb i (length (preds_in alpha1))); intros Hleb.
      left; reflexivity.

      right.
      case_eq (beq_nat (i - length (preds_in alpha1)) 0); intros H2.
         apply beq_nat_leb in H2.
        rewrite H2 in Hleb; discriminate.

        case_eq (Nat.leb i (length (preds_in alpha1) + 
                              length (preds_in alpha2))); intros Hleb2.
          apply leb_minus with (i := length (preds_in alpha1)) in Hleb2.
          rewrite arith_plus_3 in Hleb2.
          rewrite Hleb2; reflexivity.

          rewrite Hleb2 in H; discriminate.
Qed.

Lemma occ_in_alpha_conjSO2_fwd2 : forall (alpha1 alpha2 : SecOrder) (i : nat),
    occ_in_alpha (conjSO alpha1 alpha2) i = true ->
    occ_in_alpha alpha1 i = true \/
    (occ_in_alpha alpha1 i = false /\
       occ_in_alpha alpha2 (i - length (preds_in alpha1)) = true).
Proof.
  intros alpha1 alpha2 i Hocc.
  pose proof (occ_in_alpha_conjSO2_fwd _ _ _ Hocc) as H.
  destruct H.
    left; assumption.

    case_eq (occ_in_alpha alpha1 i); intros H2.
      left; reflexivity.

      right; apply conj.
        reflexivity.

        assumption.
Qed.


Lemma occ_in_alpha_conjSO2_rev : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_alpha alpha1 i = true \/ 
    occ_in_alpha alpha2 (i - (length(preds_in alpha1))) = true ->
      occ_in_alpha (conjSO alpha1 alpha2) i = true.
Proof.
  intros.
  destruct H as [Hl | Hr].
    unfold occ_in_alpha in *.
    case_eq (beq_nat i 0); intros Hbeq; rewrite Hbeq in *.
      discriminate.

      simpl in *.
      rewrite List.app_length.
      case_eq (Nat.leb i (length (preds_in alpha1))); intros Hleb.
        rewrite leb_plus_r with (m:= length (preds_in alpha2)).
          reflexivity.

          assumption.
        rewrite Hleb in *.
        discriminate.

    unfold occ_in_alpha in *.
    case_eq (beq_nat i 0); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq) in *.
      simpl in *.
      discriminate.

      simpl.
      rewrite List.app_length.
      case_eq (beq_nat (i - length (preds_in alpha1)) 0); intros Hbeq2;
        rewrite Hbeq2 in *.
        discriminate.

        case_eq (Nat.leb i (length (preds_in alpha1) 
                            + length (preds_in alpha2)));
          intros Hleb.
          reflexivity.

          case_eq (Nat.leb (i - length (preds_in alpha1))
                           (length (preds_in alpha2)));
            intros Hleb2.
            rewrite leb_plus with (m:= length (preds_in alpha1)) in Hleb2.
            rewrite <- leb_beq_zero in Hbeq2.
            rewrite <- (arith_minus_refl (length (preds_in alpha1))) in Hbeq2.
            pose proof  (contrapos_bool_tt _ _ (leb_minus _ _ _) Hbeq2).
            rewrite arith_minus_plus in Hleb2.
            rewrite arith_plus_comm in Hleb2;
            rewrite Hleb2 in Hleb; discriminate.

            apply leb_switch.
            assumption.

            rewrite Hleb2 in Hr.
            discriminate.
Qed.

Lemma occ_in_alpha_conjSO2 : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_alpha (conjSO alpha1 alpha2) i = true <->
    occ_in_alpha alpha1 i = true \/ 
      occ_in_alpha alpha2 (i - (length(preds_in alpha1))) = true.
Proof.
  intros.
  split; intros H;
    [apply occ_in_alpha_conjSO2_fwd | apply occ_in_alpha_conjSO2_rev];
    assumption.
Qed.


Lemma occ_in_alpha_disjSO : forall (alpha1 alpha2 : SecOrder) (i : nat),
  beq_nat i 0 = false ->
    occ_in_alpha (disjSO alpha1 alpha2) i =
      Nat.leb i (length (preds_in alpha1 ++ preds_in alpha2)).
Proof.
  intros.
  unfold occ_in_alpha.
  rewrite H.
  simpl.
  case (Nat.leb i (length (preds_in alpha1 ++ preds_in alpha2)));
    reflexivity.
Qed.


Lemma occ_in_alpha_disjSO2_fwd : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_alpha (disjSO alpha1 alpha2) i = true ->
    occ_in_alpha alpha1 i = true \/ 
      occ_in_alpha alpha2 (i - (length(preds_in alpha1))) = true.
Proof.
  intros.
  unfold occ_in_alpha in *.
  case_eq (beq_nat i 0); intros Hbeq; rewrite Hbeq in *.
    discriminate.

    simpl in *.
    rewrite List.app_length in H.
    case_eq (Nat.leb i (length (preds_in alpha1))); intros Hleb.
      left; reflexivity.

      right.
      case_eq (beq_nat (i - length (preds_in alpha1)) 0); intros H2.
         apply beq_nat_leb in H2.
        rewrite H2 in Hleb; discriminate.

        case_eq (Nat.leb i (length (preds_in alpha1) + 
                              length (preds_in alpha2))); intros Hleb2.
          apply leb_minus with (i := length (preds_in alpha1)) in Hleb2.
          rewrite arith_plus_3 in Hleb2.
          rewrite Hleb2; reflexivity.

          rewrite Hleb2 in H; discriminate.
Qed.


Lemma occ_in_alpha_disjSO2_rev : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_alpha alpha1 i = true \/ 
    occ_in_alpha alpha2 (i - (length(preds_in alpha1))) = true ->
      occ_in_alpha (disjSO alpha1 alpha2) i = true.
Proof.
  intros.
  destruct H as [Hl | Hr].
    unfold occ_in_alpha in *.
    case_eq (beq_nat i 0); intros Hbeq; rewrite Hbeq in *.
      discriminate.

      simpl in *.
      rewrite List.app_length.
      case_eq (Nat.leb i (length (preds_in alpha1))); intros Hleb.
        rewrite leb_plus_r with (m:= length (preds_in alpha2)).
          reflexivity.

          assumption.
        rewrite Hleb in *.
        discriminate.

    unfold occ_in_alpha in *.
    case_eq (beq_nat i 0); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq) in *.
      simpl in *.
      discriminate.

      simpl.
      rewrite List.app_length.
      case_eq (beq_nat (i - length (preds_in alpha1)) 0); intros Hbeq2;
        rewrite Hbeq2 in *.
        discriminate.

        case_eq (Nat.leb i (length (preds_in alpha1) 
                            + length (preds_in alpha2)));
          intros Hleb.
          reflexivity.

          case_eq (Nat.leb (i - length (preds_in alpha1))
                           (length (preds_in alpha2)));
            intros Hleb2.
            rewrite leb_plus with (m:= length (preds_in alpha1)) in Hleb2.
            rewrite <- leb_beq_zero in Hbeq2.
            rewrite <- (arith_minus_refl (length (preds_in alpha1))) in Hbeq2.
            pose proof  (contrapos_bool_tt _ _ (leb_minus _ _ _) Hbeq2).
            rewrite arith_minus_plus in Hleb2.
            rewrite arith_plus_comm in Hleb2;
            rewrite Hleb2 in Hleb; discriminate.

            apply leb_switch.
            assumption.

            rewrite Hleb2 in Hr.
            discriminate.
Qed.

Lemma occ_in_alpha_disjSO2 : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_alpha (disjSO alpha1 alpha2) i = true <->
    occ_in_alpha alpha1 i = true \/ 
      occ_in_alpha alpha2 (i - (length(preds_in alpha1))) = true.
Proof.
  intros.
  split; intros H;
    [apply occ_in_alpha_conjSO2_fwd | apply occ_in_alpha_conjSO2_rev];
    assumption.
Qed.


Lemma occ_in_alpha_implSO : forall (alpha1 alpha2 : SecOrder) (i : nat),
  beq_nat i 0 = false ->
    occ_in_alpha (implSO alpha1 alpha2) i =
      Nat.leb i (length (preds_in alpha1 ++ preds_in alpha2)).
Proof.
  intros.
  unfold occ_in_alpha.
  rewrite H.
  simpl.
  case (Nat.leb i (length (preds_in alpha1 ++ preds_in alpha2)));
    reflexivity.
Qed.

Lemma occ_in_alpha_implSO2_fwd : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_alpha (implSO alpha1 alpha2) i = true ->
    occ_in_alpha alpha1 i = true \/ 
      occ_in_alpha alpha2 (i - (length(preds_in alpha1))) = true.
Proof.
  intros.
  unfold occ_in_alpha in *.
  case_eq (beq_nat i 0); intros Hbeq; rewrite Hbeq in *.
    discriminate.

    simpl in *.
    rewrite List.app_length in H.
    case_eq (Nat.leb i (length (preds_in alpha1))); intros Hleb.
      left; reflexivity.

      right.
      case_eq (beq_nat (i - length (preds_in alpha1)) 0); intros H2.
         apply beq_nat_leb in H2.
        rewrite H2 in Hleb; discriminate.

        case_eq (Nat.leb i (length (preds_in alpha1) + 
                              length (preds_in alpha2))); intros Hleb2.
          apply leb_minus with (i := length (preds_in alpha1)) in Hleb2.
          rewrite arith_plus_3 in Hleb2.
          rewrite Hleb2; reflexivity.

          rewrite Hleb2 in H; discriminate.
Qed.


Lemma occ_in_alpha_implSO2_rev : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_alpha alpha1 i = true \/ 
    occ_in_alpha alpha2 (i - (length(preds_in alpha1))) = true ->
      occ_in_alpha (implSO alpha1 alpha2) i = true.
Proof.
  intros.
  destruct H as [Hl | Hr].
    unfold occ_in_alpha in *.
    case_eq (beq_nat i 0); intros Hbeq; rewrite Hbeq in *.
      discriminate.

      simpl in *.
      rewrite List.app_length.
      case_eq (Nat.leb i (length (preds_in alpha1))); intros Hleb.
        rewrite leb_plus_r with (m:= length (preds_in alpha2)).
          reflexivity.

          assumption.
        rewrite Hleb in *.
        discriminate.

    unfold occ_in_alpha in *.
    case_eq (beq_nat i 0); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq) in *.
      simpl in *.
      discriminate.

      simpl.
      rewrite List.app_length.
      case_eq (beq_nat (i - length (preds_in alpha1)) 0); intros Hbeq2;
        rewrite Hbeq2 in *.
        discriminate.

        case_eq (Nat.leb i (length (preds_in alpha1) 
                            + length (preds_in alpha2)));
          intros Hleb.
          reflexivity.

          case_eq (Nat.leb (i - length (preds_in alpha1))
                           (length (preds_in alpha2)));
            intros Hleb2.
            rewrite leb_plus with (m:= length (preds_in alpha1)) in Hleb2.
            rewrite <- leb_beq_zero in Hbeq2.
            rewrite <- (arith_minus_refl (length (preds_in alpha1))) in Hbeq2.
            pose proof  (contrapos_bool_tt _ _ (leb_minus _ _ _) Hbeq2).
            rewrite arith_minus_plus in Hleb2.
            rewrite arith_plus_comm in Hleb2;
            rewrite Hleb2 in Hleb; discriminate.

            apply leb_switch.
            assumption.

            rewrite Hleb2 in Hr.
            discriminate.
Qed.

Lemma occ_in_alpha_implSO2 : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_alpha (implSO alpha1 alpha2) i = true <->
    occ_in_alpha alpha1 i = true \/ 
      occ_in_alpha alpha2 (i - (length(preds_in alpha1))) = true.
Proof.
  intros.
  split; intros H;
    [apply occ_in_alpha_conjSO2_fwd | apply occ_in_alpha_conjSO2_rev];
    assumption.
Qed.


Lemma occ_in_alpha_0 : forall (alpha : SecOrder),
  occ_in_alpha alpha 0 = false.
Proof.
  intros; induction alpha;
    simpl; reflexivity.
Qed.

Lemma occ_in_alpha_relatSO : forall (x y : FOvariable) (i : nat),
  occ_in_alpha (relatSO x y) i = false.
Proof.
  intros x y i.
  unfold occ_in_alpha.
  case_eq i.
    intros Hi.
    rewrite <- (beq_nat_refl 0).
    reflexivity.

    intros n Hi.
    destruct x; destruct y.
    simpl.
    reflexivity.
Qed.

Lemma occ_in_alpha_allSO : forall (alpha : SecOrder) (P : predicate) (i : nat),
  occ_in_alpha (allSO P alpha) i = if beq_nat i 1 
                                      then true 
                                      else occ_in_alpha alpha (i - 1).
Proof.
  intros alpha P i.
  destruct P as [Pn].
  unfold occ_in_alpha.
  case_eq i.
    intros Hi.
    simpl.
    reflexivity.

    intros n Hi.
    simpl.
    rewrite arith_minus_zero.
    case_eq n.
      intros Hn.
      simpl.
      reflexivity.

      intros m Hn.
      simpl.
      reflexivity.
Qed.

Lemma occ_in_alpha_exSO : forall (alpha : SecOrder) (P : predicate) (i : nat),
  occ_in_alpha (exSO P alpha) i = if beq_nat i 1 
                                      then true 
                                      else occ_in_alpha alpha (i - 1).
Proof.
  intros alpha P i.
  destruct P as [Pn].
  unfold occ_in_alpha.
  case_eq i.
    intros Hi.
    simpl.
    reflexivity.

    intros n Hi.
    simpl.
    rewrite arith_minus_zero.
    case_eq n.
      intros Hn.
      simpl.
      reflexivity.

      intros m Hn.
      simpl.
      reflexivity.
Qed.

Lemma occ_in_alpha_eqFO : forall (x y : FOvariable) (i : nat),
  occ_in_alpha (eqFO x y) i = false.
Proof.
  intros x y i.
  unfold occ_in_alpha.
  case_eq i.
    intros Hi.
    rewrite <- (beq_nat_refl 0).
    reflexivity.

    intros n Hi.
    destruct x; destruct y.
    simpl.
    reflexivity.
Qed.


Lemma  occ_in_alpha_predSO : forall (P : predicate) (x : FOvariable) (i : nat),
  occ_in_alpha (predSO P x) i = true -> i = 1.
Proof.
  intros P x i Hocc.
  destruct P as [Pn]; destruct x as [xn].
  apply occ_in_alpha_leb2 in Hocc.
  case_eq i.
    intros Hi; rewrite Hi in *.
    simpl in *; destruct Hocc; discriminate.

    intros n Hi; rewrite Hi in *.
    simpl in *.
    destruct Hocc as [H1 H2].
    rewrite leb_beq_zero in H2.
    rewrite (beq_nat_true _ _ H2).
    reflexivity.
Qed.


Lemma occ_in_alpha_ST_FOv : forall (phi : Modal) (x y : FOvariable)
                                (i : nat),
  occ_in_alpha (ST phi x) i = occ_in_alpha (ST phi y) i.
Proof.
  intros phi x y i.
  unfold occ_in_alpha.
  rewrite (preds_in_ST_FOv _ x y).
  reflexivity.
Qed.

Lemma occ_in_alpha_predSO_FOv : forall (P : predicate) (x y : FOvariable)
                                (i : nat),
  occ_in_alpha (predSO P x) i = occ_in_alpha (predSO P y) i.
Proof.
  intros P x y i.
  unfold occ_in_alpha.
  destruct P; destruct x; destruct y.
  reflexivity.
Qed.

Lemma occ_in_alpha_box : forall (phi : Modal) (x : FOvariable)
                                ( i : nat),
  occ_in_alpha (ST (box phi) x) i = occ_in_alpha (ST phi x) i.
Proof.
  intros phi x i; simpl.
  destruct x as [n].
  unfold occ_in_alpha; simpl.
  rewrite preds_in_ST_FOv with (y := Var n).
  reflexivity.
Qed.

Lemma occ_in_ST : forall (phi : Modal) (x : FOvariable) (i : nat),
  occ_in_phi phi i = occ_in_alpha (ST phi x) i.
Proof.
  intros.
  unfold occ_in_alpha.
  rewrite occ_in_phi_defn.
  rewrite <- pv_in__preds_in.
  reflexivity.
Qed.



Lemma is_un_predless_occ_in_alpha : forall (alpha : SecOrder) ( i : nat),
  is_unary_predless alpha = true ->
    occ_in_alpha alpha i = false.
Proof.
  intros alpha i Hun.
  case_eq (beq_nat i 0); intros Hbeq.
  unfold occ_in_alpha.
  induction alpha; rewrite Hbeq; simpl; reflexivity.
  induction alpha;
    try destruct p; try destruct f; try destruct f0;
    [ | | |
    rewrite occ_in_alpha_allFO |
    rewrite occ_in_alpha_exFO |
    rewrite occ_in_alpha_negSO |
    rewrite occ_in_alpha_conjSO |
    rewrite occ_in_alpha_disjSO |
    rewrite occ_in_alpha_implSO | | ];
    try (simpl in *; discriminate);
    try (simpl in *; case_eq (beq_nat i 0); intros Hbeq2;
      [reflexivity | ]; simpl in *; destruct i; simpl in *; 
       [discriminate | reflexivity]);
    try (apply IHalpha; assumption);
    try (unfold occ_in_alpha; simpl; rewrite Hbeq;
      destruct i; simpl in *; [discriminate | reflexivity]);
    try (rewrite  List.app_length;
    pose proof (is_unary_predless_conjSO_l _ _ Hun) as H1;
    pose proof (is_unary_predless_conjSO_r _ _ Hun) as H2;
    apply un_predless_preds_in in H1;
    apply un_predless_preds_in in H2;
    rewrite H1;
    rewrite H2;
    simpl;
    destruct i; simpl in *; [discriminate | reflexivity]).
Qed.


Lemma occ_in_alpha_f : forall (alpha : SecOrder) (n : nat),
  occ_in_alpha alpha n = false ->
    (beq_nat n 0 = true \/
      Nat.leb n (length (preds_in alpha)) = false).
Proof.
  intros alpha n Hocc.
  unfold occ_in_alpha in Hocc.
  case_eq (beq_nat n 0); intros H.
    left; reflexivity.

    right; rewrite H in *.
    case_eq (Nat.leb n (length (preds_in alpha)));
      intros H2.
      rewrite H2 in *; discriminate.

      reflexivity.
Qed.


Lemma occ_in_alpha_excess : forall (alpha : SecOrder) (n : nat),
  beq_nat n 0 = false ->
    occ_in_alpha alpha (n + length (preds_in alpha)) = false.
Proof.
  intros alpha n Hbeq.
  induction  alpha;
    [ | rewrite occ_in_alpha_relatSO | rewrite occ_in_alpha_eqFO |
      rewrite occ_in_alpha_allFO | rewrite occ_in_alpha_exFO |
      rewrite occ_in_alpha_negSO | rewrite occ_in_alpha_conjSO |
      rewrite occ_in_alpha_disjSO | rewrite occ_in_alpha_implSO |
      destruct p as [Pn]; simpl; rewrite occ_in_alpha_allSO |
      destruct p as [Pn]; simpl; rewrite occ_in_alpha_exSO];
    try reflexivity;
    try (try destruct f; simpl; apply IHalpha);
    try (simpl; rewrite List.app_length;
    apply occ_in_alpha_f in IHalpha1;
    apply occ_in_alpha_f in IHalpha2;
    destruct IHalpha1 as [beq1 | leb1];
      [apply beq_nat_zero_f with (m := length (preds_in alpha1)) in Hbeq;
      rewrite Hbeq in *; discriminate |
      rewrite <- arith_plus_assoc;
      rewrite <- arith_plus_comm;
      rewrite arith_plus_comm with (b := length (preds_in alpha2));
      rewrite <- leb_plus_pre;
      assumption]);
    try (  apply beq_nat_zero_f; assumption);
    try ( rewrite one_suc;
    rewrite <- arith_plus_assoc;
    rewrite <- one_suc;
    simpl; rewrite arith_minus_zero;
    rewrite IHalpha;
    rewrite beq_nat_zero_f;
      [reflexivity | assumption]).

    destruct p; destruct f;
    simpl;
    unfold occ_in_alpha;
    rewrite <- one_suc;
    simpl;
    rewrite leb_beq_zero;
    rewrite Hbeq;
    reflexivity.
Qed.


Lemma occ_in_alpha_preds_in : forall (alpha : SecOrder) (n : nat),
  beq_nat n 0 = false ->
  occ_in_alpha alpha ((length (preds_in alpha)) + n) = false.
Proof.
  intros alpha n Hbeq.
  unfold occ_in_alpha.
  case_eq (length (preds_in alpha)).
    intros H.
    simpl.
    rewrite Hbeq.
    rewrite leb_beq_zero.
    rewrite Hbeq.
    reflexivity.

    intros m H.
    simpl.
    case_eq n.
      intros Hn.
      rewrite Hn in *.
      simpl in *; discriminate.

      intros j Hn.
      rewrite leb_plus_l.
      reflexivity.
Qed.


Lemma at_pred_occ_l : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_alpha alpha1 i = true ->
    at_pred (app (preds_in alpha1) (preds_in alpha2)) i
    = at_pred (preds_in alpha1) i.
Proof.
  intros alpha1 alpha2 i Hocc.
  apply occ_in_alpha_leb2 in Hocc.
  apply at_pred_app_l.
  apply PeanoNat.Nat.leb_le.
  apply Hocc.
Qed.

Lemma at_pred_occ_r : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_alpha alpha2 (i - (length (preds_in (alpha1)))) = true ->
    at_pred (app (preds_in alpha1) (preds_in alpha2)) i
    = at_pred (preds_in alpha2) (i - (length (preds_in alpha1))).
Proof.
  intros alpha1 alpha2 i Hocc.
  apply occ_in_alpha_leb2 in Hocc.
  destruct Hocc as [H1 H2].
  pose proof H1 as H3.
  apply beq_nat_leb_f in H1.
  apply leb_ex in H1.
  destruct H1 as [j H1].
  rewrite <- H1 in *.
  rewrite arith_plus_3.
  case_eq (beq_nat j 0); intros Hbeq.
    rewrite (beq_nat_true _ _ Hbeq) in *.
    rewrite plus_zero in *.
    rewrite arith_minus_refl in *.
    simpl in *; discriminate.

    apply at_pred_app_r.
    assumption.
Qed.




