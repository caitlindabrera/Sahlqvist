Require Import SecOrder Modal ST_setup Uniform_Defns.
(* Require Import p_is_pos.
Require Import p_occurs_in.
Require Import P_occurs_in_alpha.
Require Import ST_setup.
Require Import Correctness_ST Correctness_ST_world_model.
Require Import List_machinery_impl.
Require Import Monotonicity.
Require Import Uniform8.
*)
Require Import Arith.EqNat Bool my_arith__my_leb_nat P_occurs_in_alpha my_bool.
Require Import p_is_pos p_occurs_in is_pos_neg is_pos_neg_lemmas occ_in_phi at_pv Unary_Predless.
Require Import List_machinery_impl P_occurs_in_alpha pos_SO2 at_pred Occ_In_Alpha List.

Fixpoint is_neg_SO (alpha : SecOrder) (i : nat) : bool :=
  if occ_in_alpha alpha i then
  match alpha with
    predSO (Pred n) (Var m) => false
  | relatSO (Var n) (Var m) => false
  | eqFO (Var n) (Var m) => false
  | allFO (Var n) beta => is_neg_SO beta i
  | negSO beta => eqb false (is_neg_SO beta i)
  | exFO (Var n) beta => is_neg_SO beta i
  | conjSO beta1 beta2 => if Nat.leb i (length (preds_in beta1)) then is_neg_SO beta1 i
                          else is_neg_SO beta2 (i-(length (preds_in beta1)))
  | disjSO beta1 beta2 => if Nat.leb i (length (preds_in beta1)) then is_neg_SO beta1 i
                          else is_neg_SO beta2 (i-(length (preds_in beta1)))
(*  | implSO beta1 beta2 => if Nat.leb i (length (preds_in beta1)) then is_pos_SO beta1 i
                          else is_pos_SO beta2 (i-(length (preds_in beta1)))
*)
  | implSO beta1 beta2 => if Nat.leb i (length (preds_in beta1)) then eqb false (is_neg_SO beta1 i)
                          else is_neg_SO beta2 (i-(length (preds_in beta1)))
  | allSO (Pred n) beta => match i with
                                     | 0 => false
                                     | S 0 => false
                                     | S j => is_neg_SO beta j
                                     end
  | exSO (Pred n) beta => match i with
                                     | 0 => false
                                     | S 0 => false
                                     | S j => is_neg_SO beta j
                                     end
  end
  else false.

Lemma is_neg_SO_occ : forall (alpha : SecOrder) (i : nat),
  is_neg_SO alpha i = true -> occ_in_alpha alpha i = true.
Proof.
  intros alpha i H.
  case_eq (occ_in_alpha alpha i); intros Hocc.
    reflexivity.

    induction alpha;
    simpl in *; rewrite Hocc in *;
    discriminate.
Qed.



(* -------------------------------------------------------------------- *)

Lemma is_neg_SO_occ_f : forall (alpha : SecOrder) (i : nat),
  occ_in_alpha alpha i = false -> is_neg_SO alpha i = false.
Proof.
  intros alpha i Hocc.
  unfold is_neg_SO.
  induction alpha; rewrite Hocc;
  reflexivity.
Qed.

Lemma is_neg_SO_allFO : forall (alpha : SecOrder) (x : FOvariable) 
                               (i : nat),
  is_neg_SO (allFO x alpha) i = is_neg_SO alpha i.
Proof.
  intros alpha x i.
  simpl.
  destruct x.
  rewrite occ_in_alpha_allFO.
  case_eq (occ_in_alpha alpha i); intros Hocc.
    reflexivity.

    symmetry.
    apply is_neg_SO_occ_f.
    assumption.
Qed.

Lemma is_neg_SO_exFO : forall (alpha : SecOrder) (x : FOvariable) 
                               (i : nat),
  is_neg_SO (exFO x alpha) i = is_neg_SO alpha i.
Proof.
  intros alpha x i.
  simpl.
  destruct x.
  rewrite occ_in_alpha_exFO.
  case_eq (occ_in_alpha alpha i); intros Hocc.
    reflexivity.

    symmetry.
    apply is_neg_SO_occ_f.
    assumption.
Qed.


Lemma is_neg_SO_negSO : forall (alpha : SecOrder) (i : nat),
  is_neg_SO (negSO alpha) i = true ->
    is_neg_SO alpha i = false.
Proof.
  intros.
  simpl in *.
  case_eq (occ_in_alpha (negSO alpha) i); intros Hocc; rewrite Hocc in *.
    case_eq (is_neg_SO alpha i); intros Hneg; rewrite Hneg in *.
      discriminate.

      reflexivity.

    discriminate.
Qed.

Lemma is_neg_SO_negSO2 : forall (alpha : SecOrder) (i : nat),
  occ_in_alpha alpha i = true ->
    is_neg_SO alpha i = false ->
      is_neg_SO (negSO alpha) i = true.
Proof.
  intros alpha i Hocc Hpos.
  simpl in *.
  rewrite occ_in_alpha_negSO.
  rewrite Hocc.
  rewrite Hpos.
  reflexivity.
Qed.

Lemma is_neg_SO_conjSO_l : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_alpha alpha1 i = true ->
    is_neg_SO (conjSO alpha1 alpha2) i = is_neg_SO alpha1 i.
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


Lemma is_neg_SO_conjSO_r : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_alpha alpha1 i = false ->
    occ_in_alpha alpha2 (i - length (preds_in alpha1)) = true ->
      is_neg_SO (conjSO alpha1 alpha2) i = 
        is_neg_SO alpha2 (i - length( preds_in alpha1)).
Proof.
  intros alpha1 alpha2 i Hocc1 Hocc2.
  simpl.
  assert (occ_in_alpha (conjSO alpha1 alpha2) i = true) as H.
    unfold occ_in_alpha.
    apply occ_in_alpha_leb2 in Hocc2.
    simpl.
    destruct Hocc2 as [Ha Hb].
    rewrite (beq_nat_zero_minus _ _ Ha).
    rewrite app_length.
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


Lemma is_neg_SO_disjSO_l : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_alpha alpha1 i = true ->
    is_neg_SO (disjSO alpha1 alpha2) i = is_neg_SO alpha1 i.
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


Lemma is_neg_SO_implSO_l_t : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_alpha alpha1 i = true ->
    is_neg_SO (implSO alpha1 alpha2) i = true -> is_neg_SO alpha1 i = false.
Proof.
  intros alpha1 alpha2 i Hocc.
  simpl.
  rewrite occ_in_alpha_implSO2_rev.
  apply occ_in_alpha_leb2 in Hocc.
  destruct Hocc as [H1 H2].
  rewrite H2.
  case_eq (is_neg_SO alpha1 i); intros H H3.
    discriminate.
    reflexivity.

  left; assumption.
Qed.

Lemma is_neg_SO_disjSO_r : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_alpha alpha1 i = false ->
    occ_in_alpha alpha2 (i - length (preds_in alpha1)) = true ->
      is_neg_SO (disjSO alpha1 alpha2) i = 
        is_neg_SO alpha2 (i - length( preds_in alpha1)).
Proof.
  intros alpha1 alpha2 i Hocc1 Hocc2.
  simpl.
  assert (occ_in_alpha (disjSO alpha1 alpha2) i = true) as H.
    unfold occ_in_alpha.
    apply occ_in_alpha_leb2 in Hocc2.
    simpl.
    destruct Hocc2 as [Ha Hb].
    rewrite (beq_nat_zero_minus _ _ Ha).
    rewrite app_length.
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


Lemma is_neg_SO_implSO_r : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_alpha alpha1 i = false ->
    occ_in_alpha alpha2 (i - length (preds_in alpha1)) = true ->
      is_neg_SO (implSO alpha1 alpha2) i = 
        is_neg_SO alpha2 (i - length( preds_in alpha1)).
Proof.
  intros alpha1 alpha2 i Hocc1 Hocc2.
  simpl.
  assert (occ_in_alpha (implSO alpha1 alpha2) i = true) as H.
    unfold occ_in_alpha.
    apply occ_in_alpha_leb2 in Hocc2.
    simpl.
    destruct Hocc2 as [Ha Hb].
    rewrite (beq_nat_zero_minus _ _ Ha).
    rewrite app_length.
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


Lemma is_neg_SO_implSO : forall (beta1 beta2 : SecOrder) (i : nat),
  is_neg_SO (implSO beta1 beta2) i =
  if occ_in_alpha (implSO beta1 beta2) i then
    if Nat.leb i (length (preds_in beta1)) 
       then eqb false (is_neg_SO beta1 i)
       else is_neg_SO beta2 (i-(length (preds_in beta1)))
    else false.
Proof.
  reflexivity.
Qed.

Lemma is_neg_SO_conjSO : forall (beta1 beta2 : SecOrder) (i : nat),
  is_neg_SO (conjSO beta1 beta2) i =
  if occ_in_alpha (conjSO beta1 beta2) i then
    if Nat.leb i (length (preds_in beta1)) 
       then (is_neg_SO beta1 i)
       else is_neg_SO beta2 (i-(length (preds_in beta1)))
    else false.
Proof.
  reflexivity.
Qed.


Lemma is_neg_SO_implSO_l2 : forall (alpha1 alpha2 : SecOrder) (i : nat),
  occ_in_alpha alpha1 i = true ->
  is_neg_SO (implSO alpha1 alpha2) i = true ->
  is_neg_SO alpha1 i = false.
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
    rewrite app_length.
    apply leb_plus_r with (m := length (preds_in alpha2)) in H2.
    rewrite H2.
    reflexivity.

    rewrite H in Hpos.
    case_eq (is_neg_SO alpha1 i); intros Hneg2.
      rewrite Hneg2 in *.
      discriminate.

      reflexivity.
Qed.



Lemma not_pos_neg_SO : forall (alpha : SecOrder) (i : nat),
  occ_in_alpha alpha i = true ->
  ~(is_pos_SO alpha i = is_neg_SO alpha i).
Proof.
  unfold not; intros alpha.
  induction alpha; intros  i Hocc Hpos.
    simpl in *.
    try destruct p; try destruct f; try destruct f0.
    rewrite Hocc in *.
    rewrite (occ_in_alpha_predSO _ _ _ Hocc) in *.
    discriminate.

    rewrite occ_in_alpha_relatSO in Hocc; discriminate.
    rewrite occ_in_alpha_eqFO in Hocc; discriminate.

    rewrite occ_in_alpha_allFO in Hocc.
    rewrite is_pos_SO_allFO in *.
    rewrite is_neg_SO_allFO in *.
    apply IHalpha with (i := i); assumption.

    rewrite occ_in_alpha_exFO in Hocc.
    rewrite is_pos_SO_exFO in *.
    rewrite is_neg_SO_exFO in *.
    apply IHalpha with (i := i); assumption.

    simpl in Hpos.
    rewrite Hocc in *.
    apply IHalpha with (i := i).
      rewrite <- occ_in_alpha_negSO; assumption.

      case_eq (is_pos_SO alpha i); intros Hpos2;
        rewrite Hpos2 in *;
        case_eq (is_neg_SO alpha i); intros Hneg;
          rewrite Hneg in *.
          reflexivity.
          discriminate.
          discriminate.
          reflexivity.

    simpl in Hpos; rewrite Hocc in Hpos.
    destruct (occ_in_alpha_conjSO2_fwd2 _ _ _ Hocc) as [H | H].
      apply IHalpha1 with (i := i).
      assumption.
      destruct (occ_in_alpha_leb2 _ _ H) as [Hbeq Hleb].
      rewrite Hleb in *.
      assumption.

      apply IHalpha2 with (i := i - length (preds_in alpha1)).
      apply H.
      destruct H as [H1 H2].
      destruct (occ_in_alpha_leb2 _ _ H2) as [Ha Hb].
      apply occ_in_alpha_f in H1.
      destruct H1 as [Hbeq | Hleb].
        rewrite (beq_nat_true _ _ Hbeq) in *.
        simpl in *.
        discriminate.

        rewrite Hleb in *.
        assumption.

    simpl in Hpos; rewrite Hocc in Hpos.
    destruct (occ_in_alpha_conjSO2_fwd2 _ _ _ Hocc) as [H | H].
      apply IHalpha1 with (i := i).
      assumption.
      destruct (occ_in_alpha_leb2 _ _ H) as [Hbeq Hleb].
      rewrite Hleb in *.
      assumption.

      apply IHalpha2 with (i := i - length (preds_in alpha1)).
      apply H.
      destruct H as [H1 H2].
      destruct (occ_in_alpha_leb2 _ _ H2) as [Ha Hb].
      apply occ_in_alpha_f in H1.
      destruct H1 as [Hbeq | Hleb].
        rewrite (beq_nat_true _ _ Hbeq) in *.
        simpl in *.
        discriminate.

        rewrite Hleb in *.
        assumption.

    simpl in Hpos; rewrite Hocc in Hpos.
    destruct (occ_in_alpha_conjSO2_fwd2 _ _ _ Hocc) as [H | H].
      apply IHalpha1 with (i := i).
      assumption.
      destruct (occ_in_alpha_leb2 _ _ H) as [Hbeq Hleb].
      rewrite Hleb in *.
      case_eq (is_pos_SO alpha1 i); intros Hpos2;
        case_eq (is_neg_SO alpha1 i); intros Hneg;
          rewrite Hpos2 in *; rewrite Hneg in *;
          try reflexivity; try discriminate.

      apply IHalpha2 with (i := i - length (preds_in alpha1)).
      apply H.
      destruct H as [H1 H2].
      destruct (occ_in_alpha_leb2 _ _ H2) as [Ha Hb].
      apply occ_in_alpha_f in H1.
      destruct H1 as [Hbeq | Hleb].
        rewrite (beq_nat_true _ _ Hbeq) in *.
        simpl in *.
        discriminate.

        rewrite Hleb in *.
        assumption.

    case_eq i.
      intros Hi; rewrite Hi in *.
      simpl in *; discriminate.

      intros j Hi; rewrite Hi in *.
      case_eq j.
        intros Hj; rewrite Hj in *.
        simpl in *.
(*         rewrite Hocc in Hpos. *)
        destruct p.
        discriminate.

        intros k Hj; rewrite Hj in *.
        simpl in *.
        rewrite Hocc in *.
        destruct p.
        apply IHalpha with ( i := S k).
          unfold occ_in_alpha in Hocc.
          simpl beq_nat in Hocc.
          rewrite occ_in_alpha_defn.
          simpl in *.
          rewrite Hocc.
          reflexivity.

          assumption.


    case_eq i.
      intros Hi; rewrite Hi in *.
      simpl in *; discriminate.

      intros j Hi; rewrite Hi in *.
      case_eq j.
        intros Hj; rewrite Hj in *.
        simpl in *.
(*         rewrite Hocc in Hpos. *)
        destruct p.
        discriminate.

        intros k Hj; rewrite Hj in *.
        simpl in *.
        rewrite Hocc in *.
        destruct p.
        apply IHalpha with ( i := S k).
          unfold occ_in_alpha in Hocc.
          simpl beq_nat in Hocc.
          rewrite occ_in_alpha_defn.
          simpl in *.
          rewrite Hocc.
          reflexivity.

          assumption.
Qed.

Lemma pos_or_neg_SO : forall (alpha : SecOrder) (i : nat),
  occ_in_alpha alpha i = true ->
    is_pos_SO alpha i = true \/ is_neg_SO alpha i = true.
Proof.
  intros alpha.
  induction alpha; intros i Hocc.
    try destruct p; try destruct f; try destruct f0;
    simpl in *; rewrite Hocc.
    apply occ_in_alpha_predSO in Hocc.
    rewrite Hocc.
    left; reflexivity.

    rewrite occ_in_alpha_relatSO in *.
    discriminate.

    rewrite occ_in_alpha_eqFO in *.
    discriminate.

    rewrite occ_in_alpha_allFO in Hocc.
    rewrite is_pos_SO_allFO.
    rewrite is_neg_SO_allFO.
    apply IHalpha; assumption.

    rewrite occ_in_alpha_exFO in Hocc.
    rewrite is_pos_SO_exFO.
    rewrite is_neg_SO_exFO.
    apply IHalpha; assumption.

    rewrite occ_in_alpha_negSO in Hocc.
    specialize (IHalpha i Hocc).
    destruct IHalpha as [H | H].
      case_eq (is_neg_SO alpha i); intros Hneg.
        apply not_pos_neg_SO in Hocc.
        unfold not in Hocc.
        rewrite Hneg in Hocc; rewrite H in Hocc.
        specialize (Hocc (eq_refl _)).
        contradiction.

        simpl. rewrite occ_in_alpha_negSO.
        rewrite Hocc.
        rewrite Hneg.
        right; reflexivity.

      case_eq (is_pos_SO alpha i); intros Hpos.
        apply not_pos_neg_SO in Hocc.
        unfold not in Hocc.
        rewrite Hpos in Hocc; rewrite H in Hocc.
        specialize (Hocc (eq_refl _)).
        contradiction.

        simpl.
        rewrite occ_in_alpha_negSO.
        rewrite Hocc.
        rewrite Hpos.
        left; reflexivity.

    pose proof Hocc as Hocc2.
    apply occ_in_alpha_conjSO2_fwd2 in Hocc.
    destruct Hocc as [Hocc | Hocc].
      specialize (IHalpha1 i Hocc).
      apply occ_in_alpha_leb2 in Hocc.
      destruct Hocc as [Hbeq Hleb].
      simpl.
      rewrite Hleb.
      destruct IHalpha1 as [H | H].
        rewrite Hocc2.
        left; assumption.

        rewrite Hocc2.
        right; assumption.

      destruct Hocc as [Ha Hb].
      apply occ_in_alpha_f in Ha.
      destruct Ha as [Ha | Ha].
        rewrite (beq_nat_true _ _ Ha) in *.
        simpl in *; discriminate.

        simpl.
        rewrite Hocc2.
        rewrite Ha.
        apply IHalpha2; assumption.

    pose proof Hocc as Hocc2.
    apply occ_in_alpha_conjSO2_fwd2 in Hocc.
    destruct Hocc as [Hocc | Hocc].
      specialize (IHalpha1 i Hocc).
      apply occ_in_alpha_leb2 in Hocc.
      destruct Hocc as [Hbeq Hleb].
      simpl.
      rewrite Hleb.
      destruct IHalpha1 as [H | H].
        rewrite Hocc2.
        left; assumption.

        rewrite Hocc2.
        right; assumption.

      destruct Hocc as [Ha Hb].
      apply occ_in_alpha_f in Ha.
      destruct Ha as [Ha | Ha].
        rewrite (beq_nat_true _ _ Ha) in *.
        simpl in *; discriminate.

        simpl.
        rewrite Hocc2.
        rewrite Ha.
        apply IHalpha2; assumption.

    simpl.
    rewrite Hocc.
    pose proof Hocc as Hocc2.
    apply occ_in_alpha_conjSO2_fwd2 in Hocc.
    destruct Hocc as [Hocc | Hocc].
      specialize (IHalpha1 i Hocc).
      pose proof Hocc as Hocc3.
      apply occ_in_alpha_leb2 in Hocc.
      destruct Hocc as [Hbeq Hleb].
      simpl.
      rewrite Hleb.
      destruct IHalpha1 as [H | H].
        rewrite H.
        case_eq (is_neg_SO alpha1 i); intros Hneg.
          rewrite <- Hneg in H.
          pose proof (not_pos_neg_SO _ _ Hocc3 H).
          contradiction.

          right; reflexivity.

        rewrite H.
        case_eq (is_pos_SO alpha1 i); intros Hpos.
          rewrite <- H in Hpos.
          pose proof (not_pos_neg_SO _ _ Hocc3 Hpos).
          contradiction.

          left; reflexivity.

      destruct Hocc as [Hocc1 Hocc3].
      apply occ_in_alpha_f in Hocc1.
      destruct Hocc1 as [Ha | Hb].
        rewrite (beq_nat_true _ _ Ha) in *.
        simpl in *; discriminate.

        rewrite Hb.
        specialize (IHalpha2 (i - length (preds_in alpha1)) Hocc3).
        assumption.

    destruct p as [Pn].
    simpl.  
    rewrite Hocc.
    case_eq i.
      intros Hi; rewrite Hi in *.
      simpl in *; discriminate.

      intros j Hi; rewrite Hi in *.
      rewrite occ_in_alpha_allSO in Hocc.
      simpl in Hocc.
      rewrite arith_minus_zero in *.
      case_eq j.
        intros Hj; rewrite Hj in *.
        left; reflexivity.

        intros k Hj; rewrite Hj in *.
        simpl in *.
        apply IHalpha.
        assumption.

    destruct p as [Pn].
    simpl.  
    rewrite Hocc.
    case_eq i.
      intros Hi; rewrite Hi in *.
      simpl in *; discriminate.

      intros j Hi; rewrite Hi in *.
      rewrite occ_in_alpha_exSO in Hocc.
      simpl in Hocc.
      rewrite arith_minus_zero in *.
      case_eq j.
        intros Hj; rewrite Hj in *.
        left; reflexivity.

        intros k Hj; rewrite Hj in *.
        simpl in *.
        apply IHalpha.
        assumption.
Qed.

Lemma is_pos_neg_SO_t : forall (alpha : SecOrder) (i : nat),
  (is_pos_SO alpha i = true -> is_neg_SO alpha i = false) /\
  (is_neg_SO alpha i = true -> is_pos_SO alpha i = false).
Proof.
  intros alpha.
  induction alpha; intros i;
    try destruct p; try destruct f; try destruct f0;
    (apply conj; intros H1; 
    [pose proof (is_pos_SO_occ _ i H1) as H2|
     pose proof (is_neg_SO_occ _ i H1) as H2 ]);
    try (apply occ_in_alpha_predSO in H2; rewrite H2 in *;
      try reflexivity; try discriminate);
    try (    rewrite occ_in_alpha_relatSO in H2; discriminate);
    try (rewrite occ_in_alpha_eqFO in H2; discriminate);
    try (apply occ_in_alpha_predSO in H2; rewrite H2 in *;
      try reflexivity; try discriminate);
    try (rewrite is_pos_SO_allFO in *;
    rewrite occ_in_alpha_allFO in *;
    rewrite is_neg_SO_allFO in *;
    apply IHalpha; assumption);
    try (rewrite is_pos_SO_exFO in *;
    rewrite occ_in_alpha_exFO in *;
    rewrite is_neg_SO_exFO in *;
    apply IHalpha; assumption).

    apply is_pos_SO_negSO in H1.
    simpl.
    rewrite H2.
    case_eq (is_neg_SO alpha i); intros Hneg.
      reflexivity.

      rewrite <- Hneg in H1.
      rewrite occ_in_alpha_negSO in H2.
      pose proof (not_pos_neg_SO _ _ H2 H1).
      contradiction.

    apply is_neg_SO_negSO in H1.
    simpl; rewrite H2.
    case_eq (is_pos_SO alpha i); intro Hpos.
      reflexivity.

      rewrite <- H1 in Hpos.
      rewrite occ_in_alpha_negSO in H2.
      pose proof (not_pos_neg_SO _ _ H2 Hpos).
      contradiction.

    simpl.
    rewrite H2.
    apply occ_in_alpha_conjSO2_fwd2  in H2.
    destruct H2 as [Hocc | Hocc].
      pose proof (is_pos_SO_conjSO_l _ alpha2 _ Hocc) as H2.
      rewrite H2 in H1.
      apply occ_in_alpha_leb2 in Hocc.
      destruct Hocc as [_ Hleb].
      rewrite Hleb.
      apply IHalpha1; assumption.

      destruct Hocc as [Hocc1 Hocc2].
      pose proof Hocc1 as Hocc3.
      apply occ_in_alpha_f in Hocc1.
      destruct Hocc1 as [Ha | Hb].
        rewrite (beq_nat_true _ _ Ha) in *.
        simpl in *; discriminate.

        rewrite Hb.
        apply IHalpha2.
        pose proof (is_pos_SO_conjSO_r _ alpha2 _ Hocc3 Hocc2) as H2.
        rewrite H2 in H1.
        assumption.

    simpl.
    rewrite H2.
    apply occ_in_alpha_conjSO2_fwd2  in H2.
    destruct H2 as [Hocc | Hocc].
      pose proof (is_neg_SO_conjSO_l _ alpha2 _ Hocc) as H2.
      rewrite H2 in H1.
      apply occ_in_alpha_leb2 in Hocc.
      destruct Hocc as [_ Hleb].
      rewrite Hleb.
      apply IHalpha1; assumption.

      destruct Hocc as [Hocc1 Hocc2].
      pose proof Hocc1 as Hocc3.
      apply occ_in_alpha_f in Hocc1.
      destruct Hocc1 as [Ha | Hb].
        rewrite (beq_nat_true _ _ Ha) in *.
        simpl in *; discriminate.

        rewrite Hb.
        apply IHalpha2.
        pose proof (is_neg_SO_conjSO_r _ alpha2 _ Hocc3 Hocc2) as H2.
        rewrite H2 in H1.
        assumption.

    simpl.
    rewrite H2.
    apply occ_in_alpha_conjSO2_fwd2  in H2.
    destruct H2 as [Hocc | Hocc].
      pose proof (is_pos_SO_disjSO_l _ alpha2 _ Hocc) as H2.
      rewrite H2 in H1.
      apply occ_in_alpha_leb2 in Hocc.
      destruct Hocc as [_ Hleb].
      rewrite Hleb.
      apply IHalpha1; assumption.

      destruct Hocc as [Hocc1 Hocc2].
      pose proof Hocc1 as Hocc3.
      apply occ_in_alpha_f in Hocc1.
      destruct Hocc1 as [Ha | Hb].
        rewrite (beq_nat_true _ _ Ha) in *.
        simpl in *; discriminate.

        rewrite Hb.
        apply IHalpha2.
        pose proof (is_pos_SO_disjSO_r _ alpha2 _ Hocc3 Hocc2) as H2.
        rewrite H2 in H1.
        assumption.

    simpl.
    rewrite H2.
    apply occ_in_alpha_conjSO2_fwd2  in H2.
    destruct H2 as [Hocc | Hocc].
      pose proof (is_neg_SO_disjSO_l _ alpha2 _ Hocc) as H2.
      rewrite H2 in H1.
      apply occ_in_alpha_leb2 in Hocc.
      destruct Hocc as [_ Hleb].
      rewrite Hleb.
      apply IHalpha1; assumption.

      destruct Hocc as [Hocc1 Hocc2].
      pose proof Hocc1 as Hocc3.
      apply occ_in_alpha_f in Hocc1.
      destruct Hocc1 as [Ha | Hb].
        rewrite (beq_nat_true _ _ Ha) in *.
        simpl in *; discriminate.

        rewrite Hb.
        apply IHalpha2.
        pose proof (is_neg_SO_disjSO_r _ alpha2 _ Hocc3 Hocc2) as H2.
        rewrite H2 in H1.
        assumption.

    simpl.
    rewrite H2.
    pose proof H2 as H3.
    apply occ_in_alpha_conjSO2_fwd2  in H2.
    destruct H2 as [Hocc | Hocc].
      pose proof Hocc as Hocc2.
      pose proof (is_pos_SO_implSO_l_t _ alpha2 _ Hocc H1) as H2.
      apply occ_in_alpha_leb2 in Hocc.
      destruct Hocc as [_ Hocc].
      rewrite Hocc.
      case_eq (is_neg_SO alpha1 i); intros Hneg.
        reflexivity.

        destruct (pos_or_neg_SO alpha1 i Hocc2) as [H | H];
          rewrite H in *; discriminate.

      destruct Hocc as [Hocc1 Hocc2].
      apply occ_in_alpha_f in Hocc1.
      destruct Hocc1 as [Hbeq | Hleb].
        rewrite (beq_nat_true _ _ Hbeq) in *.
        simpl in *.
        discriminate.

        rewrite Hleb.
        apply IHalpha2.
        rewrite is_pos_SO_implSO in H1.
        rewrite H3 in H1.
        rewrite Hleb in H1.
        assumption.

    simpl.
    rewrite H2.
    pose proof H2 as H3.
    apply occ_in_alpha_conjSO2_fwd2  in H2.
    destruct H2 as [Hocc | Hocc].
      pose proof Hocc as Hocc2.
      pose proof (is_neg_SO_implSO_l_t _ alpha2 _ Hocc H1) as H2.
      apply occ_in_alpha_leb2 in Hocc.
      destruct Hocc as [_ Hocc].
      rewrite Hocc.
      case_eq (is_neg_SO alpha1 i); intros Hneg.
        rewrite H2 in *; discriminate.

        case_eq (is_pos_SO alpha1 i); intros Hpos.
          reflexivity.

        destruct (pos_or_neg_SO alpha1 i Hocc2) as [H | H];
          rewrite H in *; discriminate.

      destruct Hocc as [Hocc1 Hocc2].
      apply occ_in_alpha_f in Hocc1.
      destruct Hocc1 as [Hbeq | Hleb].
        rewrite (beq_nat_true _ _ Hbeq) in *.
        simpl in *.
        discriminate.

        rewrite Hleb.
        apply IHalpha2.
        rewrite is_neg_SO_implSO in H1.
        rewrite H3 in H1.
        rewrite Hleb in H1.
        assumption.

    simpl.
    rewrite H2.
    case_eq i.
      reflexivity.

      intros j Hi; rewrite Hi in *.
      simpl in *.
      rewrite H2 in *.
      case_eq j.
        reflexivity.

        intros k Hj; rewrite Hj in *.
        apply IHalpha.
        assumption.

    simpl.
    rewrite H2.
    case_eq i.
      reflexivity.

      intros j Hi; rewrite Hi in *.
      simpl in *.
      rewrite H2 in *.
      case_eq j.
        intros Hj; rewrite Hj in *.
        discriminate.

        intros k Hj; rewrite Hj in *.
        apply IHalpha.
        assumption.

    simpl.
    rewrite H2.
    case_eq i.
      reflexivity.

      intros j Hi; rewrite Hi in *.
      simpl in *.
      rewrite H2 in *.
      case_eq j.
        reflexivity.

        intros k Hj; rewrite Hj in *.
        apply IHalpha.
        assumption.

    simpl.
    rewrite H2.
    case_eq i.
      reflexivity.

      intros j Hi; rewrite Hi in *.
      simpl in *.
      rewrite H2 in *.
      case_eq j.
        intros Hj; rewrite Hj in *.
        discriminate.

        intros k Hj; rewrite Hj in *.
        apply IHalpha.
        assumption.
Qed.


Lemma is_neg_SO_0 : forall (alpha : SecOrder),
  is_neg_SO alpha 0 = false.
Proof.
  induction alpha; reflexivity.
Qed.

Lemma is_pos_negSO : forall (alpha : SecOrder) (i : nat),
  is_pos_SO (negSO alpha) i = true ->
    is_neg_SO alpha i = true.
Proof.
  intros alpha i Hpos.
  simpl in *.
  case_eq (occ_in_alpha (negSO alpha) i); intros Hocc;
    rewrite Hocc in *.
    rewrite occ_in_alpha_negSO in Hocc.
    apply pos_or_neg_SO in Hocc.
    destruct Hocc as [Ha | Hb].
      rewrite Ha in *.
      discriminate.

      assumption.

    discriminate.
Qed.

Lemma is_neg_negSO : forall (alpha : SecOrder) (i : nat),
  is_neg_SO (negSO alpha) i = true ->
    is_pos_SO alpha i = true.
Proof.
  intros alpha i Hpos.
  simpl in *.
  case_eq (occ_in_alpha (negSO alpha) i); intros Hocc;
    rewrite Hocc in *.
    rewrite occ_in_alpha_negSO in Hocc.
    apply pos_or_neg_SO in Hocc.
    destruct Hocc as [Ha | Hb].
      rewrite Ha in *.
      reflexivity.

      rewrite Hb in *.
      discriminate.

    discriminate.
Qed.


(* -------------------------------------------------------------------- *)


Definition P_is_neg_SO (alpha : SecOrder) (P : predicate) : Prop :=
  (P_occurs_in_alpha alpha P = true ->
    forall i : nat, occ_in_alpha alpha i = true ->
      match P, at_pred (preds_in alpha) i with
      | Pred pn, Pred qm => pn = qm
      end
        -> is_neg_SO alpha i = true) /\
   (P_occurs_in_alpha alpha P = false -> False).


Lemma P_is_neg_occ : forall (alpha : SecOrder) (P : predicate),
  P_is_neg_SO alpha P -> P_occurs_in_alpha alpha P = true.
Proof.
  intros alpha P H.
  unfold P_is_neg_SO in H.
  destruct H as [Ht Hf].
  case_eq (P_occurs_in_alpha alpha P); intros H.
    reflexivity.

    specialize (Hf H); contradiction.
Qed.


Lemma P_is_neg_SO_allFO  : forall (alpha : SecOrder) (x : FOvariable) (P : predicate),
  P_is_neg_SO (allFO x alpha) P <-> P_is_neg_SO alpha P.
Proof.
  intros.
  unfold P_is_neg_SO.
  destruct P as [Pn].
  split; intros H;
    apply conj.
      intros Hpocc i Hocc Heq.
      rewrite <- is_neg_SO_allFO with (x := x).
      apply H; assumption.

      intros Hpocc.
      apply H; assumption.

      intros Hpocc i Hocc Heq.
      rewrite is_neg_SO_allFO.
      rewrite occ_in_alpha_allFO in Hocc.
      rewrite <- P_occurs_in_alpha_allFO in Hpocc.
      apply H; assumption.

      rewrite <- P_occurs_in_alpha_allFO.
      intros H2; apply H; assumption.
Qed.

Lemma P_is_neg_SO_exFO  : forall (alpha : SecOrder) (x : FOvariable) (P : predicate),
  P_is_neg_SO (exFO x alpha) P <-> P_is_neg_SO alpha P.
Proof.
  intros.
  unfold P_is_neg_SO.
  destruct P as [Pn].
  rewrite <- P_occurs_in_alpha_exFO.
  split; intros H;
    apply conj.
      intros Hpocc i Hocc Heq.
      rewrite <- is_neg_SO_exFO with (x := x).
      destruct H as [H _].
      specialize (H Hpocc i).
      rewrite occ_in_alpha_exFO in H.
      simpl in *; destruct x.
      apply H; try assumption.

      apply H.

      intros Hpocc i Hocc Heq.
      rewrite is_neg_SO_exFO.
      rewrite occ_in_alpha_exFO in Hocc.
      destruct x. simpl in *.
      apply H; assumption.

      apply H.
Qed.

Lemma P_pos_negSO : forall (alpha : SecOrder) (P : predicate),
  P_is_pos_SO (negSO alpha) P -> P_is_neg_SO alpha P.
Proof.
  intros alpha P Hpos.
  unfold P_is_pos_SO in *.
  rewrite <- P_occurs_in_alpha_negSO in Hpos.
  unfold P_is_neg_SO.
  destruct Hpos as [Ha Hb].
  apply conj.
    intros Hpocc i Hocc Heq.
    specialize (Ha Hpocc i).
    rewrite occ_in_alpha_negSO in Ha.
    destruct P as [Pn].
    simpl preds_in in *.
    apply is_pos_negSO.
    apply Ha; assumption.

    assumption.
Qed.


Lemma P_neg_negSO : forall (alpha : SecOrder) (P : predicate),
  P_is_neg_SO (negSO alpha) P -> P_is_pos_SO alpha P.
Proof.
  intros alpha P Hneg.
  unfold P_is_neg_SO in *.
  rewrite <- P_occurs_in_alpha_negSO in Hneg.
  unfold P_is_neg_SO.
  destruct Hneg as [Ha Hb].
  apply conj.
    intros Hpocc i Hocc Heq.
    specialize (Ha Hpocc i).
    rewrite occ_in_alpha_negSO in Ha.
    destruct P as [Pn].
    simpl preds_in in *.
    apply is_neg_negSO.
    apply Ha; assumption.

    assumption.
Qed.

Lemma P_is_neg_SO_conjSO_l : forall (alpha1 alpha2 : SecOrder) 
                                    (P : predicate),
  P_occurs_in_alpha alpha1 P = true ->
  P_is_neg_SO (conjSO alpha1 alpha2) P ->
  P_is_neg_SO alpha1 P.
Proof.
  intros alpha1 alpha2 P Hpocc Hpos.
  unfold P_is_neg_SO in Hpos.
  destruct Hpos as [Ha _]. 
  unfold P_is_neg_SO.
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

Lemma P_is_neg_SO_conjSO_r : forall (alpha1 alpha2 : SecOrder) 
                                    (P : predicate),
  P_occurs_in_alpha alpha2 P = true ->
  P_is_neg_SO (conjSO alpha1 alpha2) P ->
  P_is_neg_SO alpha2 P.
Proof.
  intros alpha1 alpha2 P Hpocc Hpos.
  unfold P_is_neg_SO in Hpos.
  destruct Hpos as [Ha _]. 
  unfold P_is_neg_SO.
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

Lemma P_is_pos_SO_implSO_l : forall (alpha1 alpha2 : SecOrder) 
                                    (P : predicate),
  P_occurs_in_alpha alpha1 P = true ->
  P_is_pos_SO (implSO alpha1 alpha2) P ->
  P_is_neg_SO alpha1 P.
Proof.
  intros alpha1 alpha2 P Hpocc Hpos.
  unfold P_is_pos_SO in Hpos.
  destruct Hpos as [Ha _]. 
  unfold P_is_pos_SO.
  apply conj.
    intros Hpocc2 i Hocc Hw .
    rewrite P_occurs_in_alpha_implSO in Ha.
    assert (P_occurs_in_alpha alpha1 P = true \/ 
              P_occurs_in_alpha alpha2 P = true) as H.
      left; assumption.
    specialize (Ha H i).
    rewrite occ_in_alpha_implSO2 in Ha.
    assert (occ_in_alpha alpha1 i = true \/
     occ_in_alpha alpha2 (i - length (preds_in alpha1)) = true)
      as H2.
      left; assumption.
    simpl in *.
    rewrite at_pred_app_l in Ha.
    specialize (Ha H2 Hw).
    assert (occ_in_alpha (implSO alpha1 alpha2) i = true) as H3.
      rewrite occ_in_alpha_implSO2.
      assumption.
    rewrite H3 in *.
    pose proof Hocc as Hocc2.
    apply occ_in_alpha_leb2 in Hocc.
    destruct Hocc as [_ Hocc].
    rewrite Hocc in *.
      case_eq (is_pos_SO alpha1 i); intros Hpos.
        rewrite Hpos in *.
        discriminate.

        destruct (pos_or_neg_SO alpha1 i Hocc2) as [H4 | H5].
          rewrite H4 in *; discriminate.

          assumption.

        apply PeanoNat.Nat.leb_le.
        apply occ_in_alpha_leb2; assumption.

    intros H; rewrite H in *; discriminate.
Qed.

Lemma P_is_neg_SO_implSO_l : forall (alpha1 alpha2 : SecOrder) 
                                    (P : predicate),
  P_occurs_in_alpha alpha1 P = true ->
  P_is_neg_SO (implSO alpha1 alpha2) P ->
  P_is_pos_SO alpha1 P.
Proof.
  intros alpha1 alpha2 P Hpocc Hpos.
  unfold P_is_pos_SO in Hpos.
  destruct Hpos as [Ha _]. 
  unfold P_is_pos_SO.
  apply conj.
    intros Hpocc2 i Hocc Hw .
    rewrite P_occurs_in_alpha_implSO in Ha.
    assert (P_occurs_in_alpha alpha1 P = true \/ 
              P_occurs_in_alpha alpha2 P = true) as H.
      left; assumption.
    specialize (Ha H i).
    rewrite occ_in_alpha_implSO2 in Ha.
    assert (occ_in_alpha alpha1 i = true \/
     occ_in_alpha alpha2 (i - length (preds_in alpha1)) = true)
      as H2.
      left; assumption.
    simpl in *.
    rewrite at_pred_app_l in Ha.
    specialize (Ha H2 Hw).
    assert (occ_in_alpha (implSO alpha1 alpha2) i = true) as H3.
      rewrite occ_in_alpha_implSO2.
      assumption.
    rewrite H3 in *.
    pose proof Hocc as Hocc2.
    apply occ_in_alpha_leb2 in Hocc.
    destruct Hocc as [_ Hocc].
    rewrite Hocc in *.
      case_eq (is_pos_SO alpha1 i); intros Hpos.
        reflexivity.

        case_eq (is_neg_SO alpha1 i); intros H6;
          rewrite H6 in *.
          discriminate.

        destruct (pos_or_neg_SO alpha1 i Hocc2) as [H4 | H4];
          rewrite H4 in *; discriminate.

        apply PeanoNat.Nat.leb_le.
        apply occ_in_alpha_leb2; assumption.

    intros H; rewrite H in *; discriminate.
Qed.

Lemma P_is_pos_SO_implSO_r : forall (alpha1 alpha2 : SecOrder) 
                                    (P : predicate),
  P_occurs_in_alpha alpha2 P = true ->
  P_is_pos_SO (implSO alpha1 alpha2) P ->
  P_is_pos_SO alpha2 P.
Proof.
  intros alpha1 alpha2 P Hpocc Hpos.
  unfold P_is_pos_SO in Hpos.
  destruct Hpos as [Ha _]. 
  unfold P_is_pos_SO.
  apply conj.
    intros Hpocc2 i Hocc Hw .
    rewrite P_occurs_in_alpha_implSO in Ha.
    assert (P_occurs_in_alpha alpha1 P = true \/ 
              P_occurs_in_alpha alpha2 P = true) as H.
      right; assumption.
    specialize (Ha H ((length (preds_in alpha1)) + i)).
    rewrite occ_in_alpha_implSO2 in Ha.
    assert (occ_in_alpha alpha1 (length(preds_in alpha1) + i) = true \/
     occ_in_alpha alpha2 i = true)
      as H2.
      right; assumption.
    simpl in *.
    rewrite at_pred_app_r in Ha.
    rewrite arith_plus_3 in Ha.
    specialize (Ha H2 Hw).
    assert (occ_in_alpha (implSO alpha1 alpha2) 
            (length(preds_in alpha1) + i) = true) as H3.
      rewrite occ_in_alpha_implSO2.
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


Lemma P_is_neg_SO_implSO_r : forall (alpha1 alpha2 : SecOrder) 
                                    (P : predicate),
  P_occurs_in_alpha alpha2 P = true ->
  P_is_neg_SO (implSO alpha1 alpha2) P ->
  P_is_neg_SO alpha2 P.
Proof.
  intros alpha1 alpha2 P Hpocc Hpos.
  unfold P_is_neg_SO in Hpos.
  destruct Hpos as [Ha _]. 
  unfold P_is_neg_SO.
  apply conj.
    intros Hpocc2 i Hocc Hw .
    rewrite P_occurs_in_alpha_implSO in Ha.
    assert (P_occurs_in_alpha alpha1 P = true \/ 
              P_occurs_in_alpha alpha2 P = true) as H.
      right; assumption.
    specialize (Ha H ((length (preds_in alpha1)) + i)).
    rewrite occ_in_alpha_implSO2 in Ha.
    assert (occ_in_alpha alpha1 (length(preds_in alpha1) + i) = true \/
     occ_in_alpha alpha2 i = true)
      as H2.
      right; assumption.
    simpl in *.
    rewrite at_pred_app_r in Ha.
    rewrite arith_plus_3 in Ha.
    specialize (Ha H2 Hw).
    assert (occ_in_alpha (implSO alpha1 alpha2) 
            (length(preds_in alpha1) + i) = true) as H3.
      rewrite occ_in_alpha_implSO2.
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

Lemma is_neg_SO_allSO : forall (alpha : SecOrder) (P : predicate) (i : nat),
  occ_in_alpha alpha i = true ->
  is_neg_SO (allSO P alpha) (S i) = is_neg_SO alpha i.
Proof.
  intros alpha P i Hocc.
  simpl.
  rewrite occ_in_alpha_allSO.
  simpl.
  rewrite arith_minus_zero.
  rewrite Hocc.
  rewrite if_then_else_true.
  destruct P as [Pn].
  case_eq i.
    intros Hi.
    rewrite Hi in *; simpl in *; discriminate.

    intros j Hi; rewrite Hi in *.
    reflexivity.
Qed.

Lemma is_neg_SO_exSO : forall (alpha : SecOrder) (P : predicate) (i : nat),
  occ_in_alpha alpha i = true ->
  is_neg_SO (exSO P alpha) (S i) = is_neg_SO alpha i.
Proof.
  intros alpha P i Hocc.
  simpl.
  rewrite occ_in_alpha_exSO.
  simpl.
  rewrite arith_minus_zero.
  rewrite Hocc.
  rewrite if_then_else_true.
  destruct P as [Pn].
  case_eq i.
    intros Hi.
    rewrite Hi in *; simpl in *; discriminate.

    intros j Hi; rewrite Hi in *.
    reflexivity.
Qed.


Lemma P_is_neg_SO_allSO : forall (alpha : SecOrder) (P Q : predicate),
P_occurs_in_alpha alpha P = true ->
P_is_neg_SO (allSO Q alpha) P -> P_is_neg_SO alpha P.
Proof.
  intros alpha P Q Hpocc Hpos.
  unfold P_is_neg_SO in *.
  destruct Hpos as [Hpos _].
  apply conj.
    intros Hpocc2 i Hocc Heq.
    destruct P as [Pn]; destruct Q as [Qm].
    rewrite P_occurs_in_alpha_allSO in Hpos.
      assert (PeanoNat.Nat.eqb Pn Qm = true \/
            P_occurs_in_alpha alpha (Pred Pn) = true ) as H.
        right; assumption.
    specialize (Hpos H (S i)).
    rewrite occ_in_alpha_allSO in Hpos.
    rewrite is_neg_SO_allSO in Hpos; try assumption.
    apply Hpos.
      simpl.
      case_eq i.
        intros Hi; rewrite Hi in *.
        simpl in *; discriminate.

        intros j Hi; rewrite Hi in *.
        simpl.
        assumption.

      simpl.
      rewrite arith_minus_zero.
      case_eq i.
        intros Hi; rewrite Hi in *; simpl in *;
        discriminate.

        intros j Hi; rewrite Hi in *.
        assumption.

    intros H; rewrite H in *; discriminate.
Qed.

Lemma P_is_neg_SO_exSO : forall (alpha : SecOrder) (P Q : predicate),
P_occurs_in_alpha alpha P = true ->
P_is_neg_SO (exSO Q alpha) P -> P_is_neg_SO alpha P.
Proof.
  intros alpha P Q Hpocc Hpos.
  unfold P_is_pos_SO in *.
  destruct Hpos as [Hpos _].
  apply conj.
    intros Hpocc2 i Hocc Heq.
    destruct P as [Pn]; destruct Q as [Qm].
    rewrite P_occurs_in_alpha_exSO in Hpos.
      assert (PeanoNat.Nat.eqb Pn Qm = true \/
            P_occurs_in_alpha alpha (Pred Pn) = true ) as H.
        right; assumption.
    specialize (Hpos H (S i)).
    rewrite occ_in_alpha_exSO in Hpos.
    rewrite is_neg_SO_exSO in Hpos; try assumption.
    apply Hpos.
      simpl.
      case_eq i.
        intros Hi; rewrite Hi in *.
        simpl in *; discriminate.

        intros j Hi; rewrite Hi in *.
        simpl.
        assumption.

      simpl.
      rewrite arith_minus_zero.
      case_eq i.
        intros Hi; rewrite Hi in *; simpl in *;
        discriminate.

        intros j Hi; rewrite Hi in *.
        assumption.

    intros H; rewrite H in *; discriminate.
Qed.

Lemma is_neg_SO_ST_FOv : forall (phi : Modal) (x y : FOvariable)
                                (i : nat),
  is_neg_SO (ST phi x) i = is_neg_SO (ST phi y) i.
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


Lemma is_neg_SO_box : forall (phi : Modal) (x : FOvariable)
                             (i : nat),
  is_neg_SO (ST (box phi) x) i = is_neg_SO (ST phi x) i.
Proof.
  intros.
  simpl.
  destruct x as [n].
  case_eq (is_neg_SO (ST phi (Var n)) i); intros H1.
    case_eq (is_neg_SO (allFO (Var (n + 1)) (implSO (relatSO
                (Var n) (Var (n + 1))) (ST phi (Var (n + 1))))) i);
      intros H2.
      reflexivity.

      rewrite is_neg_SO_allFO in H2.
      rewrite is_neg_SO_implSO in H2. 
      rewrite occ_in_alpha_implSO in H2.
      simpl in H2.
      rewrite occ_in_alpha_relatSO in H2.
      rewrite preds_in_ST_FOv with (y := (Var n)) in H2.
      rewrite is_neg_SO_ST_FOv with (y := (Var n)) in H2.
      rewrite arith_minus_zero in H2.
      case_eq (Nat.leb i (length (preds_in (ST phi (Var n)))));
        intros Hleb; rewrite Hleb in *.
        case_eq (Nat.leb i 0); intros Hleb2; rewrite Hleb2 in *.
          discriminate.

          rewrite H2 in H1.
          discriminate.

        apply is_neg_SO_occ in H1.
        unfold occ_in_alpha in H1.
        case_eq (beq_nat i 0); intros Hbeq; rewrite Hbeq in *.
          discriminate.

          rewrite Hleb in H1.
          discriminate.

        case_eq (beq_nat i 0); intros Hbeq.
          apply is_neg_SO_occ in H1.
          unfold occ_in_alpha in H1.
          rewrite Hbeq in H1.
          discriminate.

          reflexivity.

    case_eq (is_neg_SO (allFO (Var (n + 1)) (implSO (relatSO
                (Var n) (Var (n + 1))) (ST phi (Var (n + 1))))) i);
      intros H2.
      pose proof H2 as H3.
      simpl in H2.
      rewrite occ_in_alpha_allFO in H2.
      rewrite occ_in_alpha_implSO in H2.
      simpl in H2.
      rewrite occ_in_alpha_relatSO in H2.
      rewrite is_neg_SO_ST_FOv with (y := Var (n+1)) in H1.
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


Lemma is_neg_SO_diam : forall (phi : Modal) (x : FOvariable)
                             (i : nat),
  is_neg_SO (ST (diam phi) x) i = is_neg_SO (ST phi x) i.
Proof.
  intros.
  simpl.
  destruct x as [n].
  case_eq (is_neg_SO (ST phi (Var n)) i); intros H1.
    case_eq (is_neg_SO (exFO (Var (n + 1)) (conjSO (relatSO
                (Var n) (Var (n + 1))) (ST phi (Var (n + 1))))) i);
      intros H2.
      reflexivity.

      rewrite is_neg_SO_exFO in H2.
      rewrite is_neg_SO_conjSO in H2. 
      rewrite occ_in_alpha_conjSO in H2.
      simpl in H2.
      rewrite occ_in_alpha_relatSO in H2.
      rewrite preds_in_ST_FOv with (y := (Var n)) in H2.
      rewrite is_neg_SO_ST_FOv with (y := (Var n)) in H2.
      rewrite arith_minus_zero in H2.
      case_eq (Nat.leb i (length (preds_in (ST phi (Var n)))));
        intros Hleb; rewrite Hleb in *.
        case_eq (Nat.leb i 0); intros Hleb2; rewrite Hleb2 in *.
                  rewrite leb_beq_zero in Hleb2.
          rewrite (beq_nat_true _ _ Hleb2) in *.
          rewrite is_neg_SO_0 in H1.
          discriminate.

          rewrite H2 in H1.
          discriminate.

        apply is_neg_SO_occ in H1.
        unfold occ_in_alpha in H1.
        case_eq (beq_nat i 0); intros Hbeq; rewrite Hbeq in *.
          discriminate.

          rewrite Hleb in H1.
          discriminate.

        case_eq (beq_nat i 0); intros Hbeq.
          apply is_neg_SO_occ in H1.
          unfold occ_in_alpha in H1.
          rewrite Hbeq in H1.
          discriminate.

          reflexivity.

    case_eq (is_neg_SO (exFO (Var (n + 1)) (conjSO (relatSO
                (Var n) (Var (n + 1))) (ST phi (Var (n + 1))))) i);
      intros H2.
      pose proof H2 as H3.
      simpl in H2.
      rewrite occ_in_alpha_exFO in H2.
      rewrite occ_in_alpha_conjSO in H2.
      simpl in H2.
      rewrite occ_in_alpha_relatSO in H2.
      rewrite is_neg_SO_ST_FOv with (y := Var (n+1)) in H1.
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

(* -------------------------------------------------------------- *)

Lemma is_neg__ST : forall (phi : Modal) (x : FOvariable) (i : nat),
  is_neg phi i = is_neg_SO (ST phi x) i.
Proof.
  induction phi; intros x i;
  try destruct p; destruct x;
    try (simpl;
    unfold occ_in_alpha; simpl;
    case (beq_nat i 0);
      try reflexivity;
    simpl; do 2 rewrite app_length;
    do 2 rewrite <- pv_in__preds_in;
    rewrite <- IHphi1;
    rewrite <- IHphi2;
    reflexivity);
    try rewrite is_neg_SO_box;
    try rewrite is_neg_SO_diam;
    try (case_eq (beq_nat i 0); intros Hbeq;
      [rewrite (beq_nat_true _ _ Hbeq);
      rewrite is_neg_SO_0;
      reflexivity |
      simpl; rewrite (IHphi (Var n));
      rewrite Hbeq;
      case_eq (Nat.leb i (length (pv_in phi))); intros Hleb;
        [reflexivity |];
        case_eq (is_neg_SO (ST phi (Var n )) i); intros Hpos;
          [apply is_neg_SO_occ in Hpos | reflexivity];
          unfold occ_in_alpha in Hpos;
          rewrite Hbeq in Hpos;
          rewrite <- pv_in__preds_in in Hpos;
          rewrite Hleb in Hpos;
          discriminate]).
    try (simpl; case_eq (beq_nat i 0); intros H).
      rewrite (beq_nat_true _ _ H).
      reflexivity.

        rewrite occ_in_alpha_defn.
        rewrite H.
        simpl. rewrite <- pv_in__preds_in.
        case_eq (Nat.leb i (length (pv_in phi))); intros Hleb.
          rewrite <- IHphi.
          reflexivity.

          reflexivity.
Qed.

Lemma p_is_neg__SO : forall (phi : Modal) (x : FOvariable)
                            (p : propvar),
  p_is_neg phi p <-> P_is_neg_SO (ST phi x) (ST_pv p).
Proof.
  intros phi x p.
  unfold p_is_neg.
  unfold P_is_neg_SO.
  split; intros H;
    (apply conj; [intros Hpocc i Hocc Heq|]).
      rewrite <- is_neg__ST; apply H.
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

      rewrite is_neg__ST with (x := x); apply H.
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


Definition uniform_neg_SO (alpha : SecOrder) : Prop :=
  forall (P : predicate), P_occurs_in_alpha alpha P = true -> 
    P_is_neg_SO alpha P.


Lemma uni_neg__SO : forall (phi : Modal) (x : FOvariable),
  uniform_neg phi <-> uniform_neg_SO (ST phi x).
Proof.
  intros phi x.
  unfold uniform_neg.
  unfold uniform_neg_SO.
  split; intros H p Hpocc; destruct p as [n].
    rewrite ST_pv_P.
    apply p_is_neg__SO.
    apply H.
    rewrite ST_pred_p;
    apply P_occurs_in_alpha__SO with (x := x);
    assumption.

    rewrite ST_pred_p.
    apply (p_is_neg__SO phi x (ST_pred (Pred n))).
    apply H.
    simpl.
    apply P_occurs_in_alpha__SO.
    simpl; assumption.
Qed.

Lemma uni_neg_SO_allFO : forall (alpha : SecOrder) (x : FOvariable),
  uniform_neg_SO (allFO x alpha) <-> uniform_neg_SO alpha.
Proof.
  intros alpha x.
  unfold uniform_pos_SO.
  split;
    intros H P H2;
    specialize (H P);
    rewrite <- P_occurs_in_alpha_allFO in *;
    rewrite P_is_neg_SO_allFO in *;
    apply H; assumption.
Qed.

