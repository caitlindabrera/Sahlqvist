Require Import SecOrder.
Require Import Modal.
Require Import my_arith__my_leb_nat.
Require Import is_pos_neg.
Require Import occ_in_phi.
Require Import Arith.EqNat.
Require Import occ_in_phi.
Require Import my_bool.


(* is_pos lemmas *)


Lemma is_pos_occ : forall (phi : Modal) (i : nat),
  is_pos phi i = true -> occ_in_phi phi i = true.
Proof.
  intros phi i Hpos.
  unfold is_pos in *.
  case_eq (occ_in_phi phi i);
  intros Hocc; induction phi; 
  rewrite Hocc in *; try discriminate; try reflexivity.
Qed.

Lemma is_pos_notin : forall (phi : Modal) (i : nat),
  is_pos phi i = true -> Nat.leb i (length (pv_in phi)) = true.
Proof.
  intros phi i H.
  induction phi.
    unfold is_pos in H.
    case_eq (Nat.leb i (length (pv_in (atom p))));
    try reflexivity; intros H_eq; try discriminate.
      unfold occ_in_phi in *; rewrite H_eq in *.
      case_eq (beq_nat i 0); intros H_beq;
        rewrite H_beq in *; try discriminate.

    simpl in *.
    case_eq (Nat.leb i (length (pv_in phi)));
    try reflexivity; intros H_eq; rewrite H_eq in *;
    try discriminate.
      case_eq (beq_nat i 0); intros H_beq; rewrite H_beq in *;
      discriminate.

    simpl in *.
    rewrite List.app_length.
    case_eq (Nat.leb i (length (pv_in phi1)));
    intros H_eq; rewrite H_eq in *.
      pose proof (leb_plus_r i (length (pv_in phi1)) 
                 (length (pv_in phi2)) H_eq) as H_leb.
      exact H_leb.

      rewrite List.app_length in H.
      case_eq (Nat.leb i (length (pv_in phi1) + length (pv_in phi2)));
      intros H_leb; try reflexivity; rewrite H_leb in *;
      try discriminate.
      case_eq (beq_nat i 0); intros H_beq; rewrite H_beq in *;
      discriminate.

    simpl in *.
    rewrite List.app_length.
    case_eq (Nat.leb i (length (pv_in phi1)));
    intros H_eq; rewrite H_eq in *.
      pose proof (leb_plus_r i (length (pv_in phi1)) 
                 (length (pv_in phi2)) H_eq) as H_leb.
      exact H_leb.

      rewrite List.app_length in H.
      case_eq (Nat.leb i (length (pv_in phi1) + length (pv_in phi2)));
      intros H_leb; try reflexivity; rewrite H_leb in *;
      try discriminate.
      case_eq (beq_nat i 0); intros H_beq; rewrite H_beq in *;
      discriminate.

    simpl in *.
    rewrite List.app_length.
    case_eq (Nat.leb i (length (pv_in phi1)));
    intros H_eq; rewrite H_eq in *.
      pose proof (leb_plus_r i (length (pv_in phi1)) 
                 (length (pv_in phi2)) H_eq) as H_leb.
      exact H_leb.

      rewrite List.app_length in H.
      case_eq (Nat.leb i (length (pv_in phi1) + length (pv_in phi2)));
      intros H_leb; try reflexivity; rewrite H_leb in *;
      try discriminate.
      case_eq (beq_nat i 0); intros H_beq; rewrite H_beq in *;
      discriminate.

    simpl in *.
    case_eq (Nat.leb i (length (pv_in phi)));
    intros H_eq; rewrite H_eq in *; try reflexivity; 
    try discriminate.
      case_eq (beq_nat i 0); intros H_beq; rewrite H_beq in *;
      discriminate.

    simpl in *.
    case_eq (Nat.leb i (length (pv_in phi)));
    intros H_eq; rewrite H_eq in *; try reflexivity; 
    try discriminate.
      case_eq (beq_nat i 0); intros H_beq; rewrite H_beq in *;
      discriminate.
Qed.

Lemma is_pos_atom : forall (q : propvar) (i : nat),
  is_pos (atom q) i = true -> (EqNat.beq_nat 1 i = true).
Proof.
  intros q i H.
  simpl in *.
  case_eq i.
    intros H_eq; try rewrite H_eq in *.
    assert (Nat.leb 0 1 = true) as H_leb.
      unfold Nat.leb; reflexivity.
    rewrite H_leb in *; discriminate.

    intros n H_eq.
    case_eq n.
      reflexivity.

      intros m H_eq2; rewrite H_eq2 in *.
      rewrite H_eq in *.
      assert (Nat.leb (S (S m)) 1 = false) as H_f.
        simpl; reflexivity.
      rewrite H_f in *; discriminate.
Qed.

Lemma is_pos_mneg : forall (psi : Modal) (i : nat),
  is_pos (mneg psi) i = true -> (is_pos psi i) = false.
Proof.
  intros psi i H.
  simpl is_pos in H.
  case_eq (Nat.leb i (length (pv_in psi)));
  intros H_eq; rewrite H_eq in *.
    case_eq (is_pos psi i); intros H_pos;
    rewrite H_pos in *; try discriminate;
    try reflexivity.
      case_eq (beq_nat i 0); intros H_beq; rewrite H_beq in *;
      discriminate.

      case_eq (beq_nat i 0); intros H_beq; rewrite H_beq in *;
      discriminate.
Qed.

Lemma is_pos_mneg2 : forall (psi : Modal) (i : nat),
  is_pos psi i = false ->
    occ_in_phi psi i = true ->
      is_pos (mneg psi) i = true.
Proof.
  intros phi i Hpos Hocc.
  simpl.
  destruct (occ_in_phi_leb2 phi i Hocc) as [l r].
  rewrite l.
  rewrite r.
  rewrite Hpos.
  reflexivity.
Qed.

Lemma is_pos_mconj_l : forall (phi1 phi2 : Modal) (i : nat),
  is_pos (mconj phi1 phi2) i = true ->
    ( occ_in_phi phi1 i = true ->  (is_pos phi1 i = true)).
Proof.
  intros phi1 phi2 i Hpos Hocc.
  assert (beq_nat i 0 = false) as Hbeq.
    apply occ_in_phi_0 with (phi := phi1) ; exact Hocc.
  assert (Nat.leb i (length (pv_in phi1)) = true) as Hleb.
    apply occ_in_phi_leb; exact Hocc.
  simpl in Hpos.
  rewrite Hbeq in *.
  rewrite List.app_length in Hpos.
  rewrite leb_plus_r in Hpos.
  rewrite Hleb in Hpos.
    exact Hpos.

    exact Hleb.
Qed.

Lemma is_pos_mconj_r : forall (phi1 phi2 : Modal) (i : nat),
  is_pos (mconj phi1 phi2) i = true ->
    (Nat.leb (length (pv_in phi1) + 1) i = true) ->
      is_pos phi2 (i - (length (pv_in phi1))) = true.
Proof.
  intros phi1 phi2 i Hpos12 Hleb.
  rewrite is_pos_defn_mconj in *.
  case_eq (occ_in_phi (mconj phi1 phi2) i); intros Hocc;
  rewrite Hocc in *.
    case_eq (Nat.leb i (length (pv_in phi1))); intros Hleb2;
    rewrite Hleb2 in *.
      apply leb_notswitch in Hleb2.
      rewrite Hleb in *.
      discriminate.

      exact Hpos12.

      discriminate.
Qed.

Lemma is_pos_mdisj_l : forall (phi1 phi2 : Modal) (i : nat),
  is_pos (mdisj phi1 phi2) i = true ->
    ( occ_in_phi phi1 i = true ->  (is_pos phi1 i = true)).
Proof.
  intros phi1 phi2 i Hpos Hocc.
  assert (beq_nat i 0 = false) as Hbeq.
    apply occ_in_phi_0 with (phi := phi1) ; exact Hocc.
  assert (Nat.leb i (length (pv_in phi1)) = true) as Hleb.
    apply occ_in_phi_leb; exact Hocc.
  simpl in Hpos.
  rewrite Hbeq in *.
  rewrite List.app_length in Hpos.
  rewrite leb_plus_r in Hpos.
  rewrite Hleb in Hpos.
    exact Hpos.

    exact Hleb.
Qed.

Lemma is_pos_mdisj_r : forall (phi1 phi2 : Modal) (i : nat),
  is_pos (mdisj phi1 phi2) i = true ->
    (Nat.leb (length (pv_in phi1) + 1) i = true) ->
      is_pos phi2 (i - (length (pv_in phi1))) = true.
Proof.
  intros phi1 phi2 i Hpos12 Hleb.
  rewrite is_pos_defn_mdisj in *.
  case_eq (occ_in_phi (mdisj phi1 phi2) i); intros Hocc;
  rewrite Hocc in *.
    case_eq (Nat.leb i (length (pv_in phi1))); intros Hleb2;
    rewrite Hleb2 in *.
      apply leb_notswitch in Hleb2.
      rewrite Hleb in *.
      discriminate.

      exact Hpos12.

      discriminate.
Qed.

Lemma is_pos_mconj : forall (phi1 phi2 : Modal) (i : nat),
  is_pos (mconj phi1 phi2) i = true ->
    ( occ_in_phi phi1 i = true ->  (is_pos phi1 i = true)) /\
    ((Nat.leb (length (pv_in phi1) + 1) i = true) ->
       is_pos phi2 (i - (length (pv_in phi1))) = true).
Proof.
  intros phi1 phi2 i Hpos.
  apply conj.
    apply is_pos_mconj_l with (phi2 := phi2); exact Hpos.

    apply is_pos_mconj_r with (phi1 := phi1); exact Hpos.
Qed.


Lemma is_pos_mdisj : forall (phi1 phi2 : Modal) (i : nat),
  is_pos (mdisj phi1 phi2) i = true ->
    ( occ_in_phi phi1 i = true ->  (is_pos phi1 i = true)) /\
    ((Nat.leb (length (pv_in phi1) + 1) i = true) ->
       is_pos phi2 (i - (length (pv_in phi1))) = true).
Proof.
  intros phi1 phi2 i Hpos.
  apply conj.
    apply is_pos_mdisj_l with (phi2 := phi2); exact Hpos.

    apply is_pos_mdisj_r with (phi1 := phi1); exact Hpos.
Qed.

Lemma is_pos_box : forall (phi : Modal) (i : nat),
  is_pos (box phi) i = true <-> is_pos phi i = true.
Proof.
  split; intros H.
  simpl in H.
  case_eq (Nat.leb i (length (pv_in phi)));
  intros H_eq; rewrite H_eq in *; try exact H;
  try discriminate.
      case_eq (beq_nat i 0); intros H_beq; rewrite H_beq in *;
      try discriminate; try exact H.

      case_eq (beq_nat i 0); intros H_beq; rewrite H_beq in *;
      try discriminate; try exact H.

  pose proof (is_pos_occ phi i H) as H1.
  simpl.
  rewrite H.
  rewrite occ_in_phi_defn in H1.
  case_eq (beq_nat i 0); intros Hbeq; rewrite Hbeq in *;
  try discriminate.
  case_eq (Nat.leb i (length (pv_in phi))); intros Hleb;
  rewrite Hleb in *; try discriminate; try reflexivity.
Qed.

Lemma is_pos_box2 : forall (phi : Modal) (i : nat),
  is_pos (box phi) i = is_pos phi i.
Proof.
  intros phi i.
  case_eq (is_pos (box phi) i); intros Hpos.
    pose proof (is_pos_occ _ _ Hpos) as Hocc.
    pose proof Hocc as Hocc2.
    apply occ_in_phi_box with (phi := phi) in Hocc2.
    induction phi; simpl in *; rewrite Hocc2 in *;
    symmetry; assumption.

    case_eq (is_pos phi i); intros Hpos2.
      simpl in Hpos.
      rewrite Hpos2 in Hpos.
      apply if_then_else_true_false in Hpos.
      case_eq (beq_nat i 0); intros Hbeq; rewrite Hbeq in *.
        rewrite (beq_nat_true _ _ Hbeq) in Hpos2.
        apply is_pos_occ in Hpos2.
        apply occ_in_phi_0 in Hpos2.
        simpl in *; discriminate.

        case_eq (Nat.leb i (length (pv_in phi))); intros Hleb.
          rewrite Hleb in *.
          discriminate.

          induction phi; simpl in *; 
          rewrite Hleb in *; rewrite Hbeq in *;
          discriminate.

        reflexivity.
Qed.

Lemma is_pos_diam : forall (phi : Modal) (i : nat),
  is_pos (diam phi) i = true <-> is_pos phi i = true.
Proof.
  split; intros H.
  simpl in H.
  case_eq (Nat.leb i (length (pv_in phi)));
  intros H_eq; rewrite H_eq in *; try exact H;
  try discriminate.
      case_eq (beq_nat i 0); intros H_beq; rewrite H_beq in *;
      try discriminate; try exact H.

      case_eq (beq_nat i 0); intros H_beq; rewrite H_beq in *;
      try discriminate; try exact H.

  pose proof (is_pos_occ phi i H) as H1.
  simpl.
  rewrite H.
  rewrite occ_in_phi_defn in H1.
  case_eq (beq_nat i 0); intros Hbeq; rewrite Hbeq in *;
  try discriminate.
  case_eq (Nat.leb i (length (pv_in phi))); intros Hleb;
  rewrite Hleb in *; try discriminate; try reflexivity.
Qed.

Lemma is_pos_diam2 : forall (phi : Modal) (i : nat),
  is_pos (diam phi) i = is_pos phi i.
Proof.
  intros phi i.
  case_eq (is_pos (diam phi) i); intros Hpos.
    pose proof (is_pos_occ _ _ Hpos) as Hocc.
    pose proof Hocc as Hocc2.
    apply occ_in_phi_box with (phi := phi) in Hocc2.
    induction phi; simpl in *; rewrite Hocc2 in *;
    symmetry; assumption.

    case_eq (is_pos phi i); intros Hpos2.
      simpl in Hpos.
      rewrite Hpos2 in Hpos.
      apply if_then_else_true_false in Hpos.
      case_eq (beq_nat i 0); intros Hbeq; rewrite Hbeq in *.
        rewrite (beq_nat_true _ _ Hbeq) in Hpos2.
        apply is_pos_occ in Hpos2.
        apply occ_in_phi_0 in Hpos2.
        simpl in *; discriminate.

        case_eq (Nat.leb i (length (pv_in phi))); intros Hleb.
          rewrite Hleb in *.
          discriminate.

          induction phi; simpl in *; 
          rewrite Hleb in *; rewrite Hbeq in *;
          discriminate.

        reflexivity.
Qed.

(* ------------------------------------------------------------ *)

(* is_neg lemmas *)


Lemma is_neg_occ : forall (phi : Modal) (i : nat),
  is_neg phi i = true -> occ_in_phi phi i = true.
Proof.
  intros phi i H.
  case_eq (occ_in_phi phi i); intros Hocc;
  try reflexivity;
  induction phi; unfold is_neg in H; rewrite Hocc in *;
  discriminate.
Qed.

Lemma is_neg_mneg : forall (psi : Modal) (i : nat),
  is_neg (mneg psi) i = true -> (is_neg psi i) = false.
Proof.
  intros phi i Hneg.
  pose proof Hneg as Hocc.
  apply is_neg_occ in Hocc.
  simpl in *.
  rewrite Hocc in Hneg.
  case_eq (is_neg phi i); intros H.
    rewrite H in *; discriminate.

    reflexivity.
Qed.

Lemma is_neg_box : forall (phi : Modal) (i : nat),
  is_neg (box phi) i = true -> is_neg phi i = true.
Proof.
  intros phi i Hneg.
  pose proof (is_neg_occ (box phi) i Hneg) as Hocc.
  simpl in *.
  rewrite Hocc in Hneg.
  assumption.
Qed.

Lemma is_neg_diam : forall (phi : Modal) (i : nat),
  is_neg (diam phi) i = true -> is_neg phi i = true.
Proof.
  intros phi i Hneg.
  pose proof (is_neg_occ (box phi) i Hneg) as Hocc.
  simpl in *.
  rewrite Hocc in Hneg.
  assumption.
Qed.

Lemma is_neg_0 : forall (phi : Modal),
  is_neg phi 0 = false.
Proof.
  induction phi; simpl; reflexivity.
Qed.


Lemma is_neg_box2 : forall (phi : Modal) (i : nat),
  is_neg (box phi) i = is_neg phi i.
Proof.
  intros phi i.
  case_eq (beq_nat i 0); intros Hbeq.
    rewrite (beq_nat_true _ _ Hbeq).
    simpl.
    rewrite is_neg_0.
    reflexivity.

    case_eq (Nat.leb i (length (pv_in phi))); intros Hleb;
      simpl;
      rewrite Hbeq;
      rewrite Hleb.
      reflexivity.

      induction phi; simpl in *; rewrite Hbeq; rewrite Hleb;
      reflexivity.
Qed.

Lemma is_neg_diam2 : forall (phi : Modal) (i : nat),
  is_neg (diam phi) i = is_neg phi i.
Proof.
  intros phi i.
  case_eq (beq_nat i 0); intros Hbeq.
    rewrite (beq_nat_true _ _ Hbeq).
    simpl.
    rewrite is_neg_0.
    reflexivity.

    case_eq (Nat.leb i (length (pv_in phi))); intros Hleb;
      simpl;
      rewrite Hbeq;
      rewrite Hleb.
      reflexivity.

      induction phi; simpl in *; rewrite Hbeq; rewrite Hleb;
      reflexivity.
Qed.

(* --------------------------------------------------------------- *)
Lemma is_pos_neg_f_t_mconj : forall (phi1 phi2 : Modal) (i : nat),
    (forall i : nat,
         occ_in_phi phi1 i = true ->
         (is_pos phi1 i = false -> is_neg phi1 i = true) /\
         (is_pos phi1 i = true -> is_neg phi1 i = false)) ->
    (forall i : nat,
         occ_in_phi phi2 i = true ->
         (is_pos phi2 i = false -> is_neg phi2 i = true) /\
         (is_pos phi2 i = true -> is_neg phi2 i = false)) ->
     occ_in_phi (mconj phi1 phi2) i = true ->
 (is_pos (mconj phi1 phi2) i = false -> is_neg (mconj phi1 phi2) i = true) /\
 (is_pos (mconj phi1 phi2) i = true -> is_neg (mconj phi1 phi2) i = false).
Proof.
  intros phi1 phi2 i IHphi1 IHphi2 Hocc.
  apply conj; intros H.
    case_eq (occ_in_phi phi1 i); intros Hocc1.
      simpl.
      simpl in Hocc.
      rewrite Hocc.
      destruct (occ_in_phi_leb2 _ _ Hocc1) as [Ha Hb].
      rewrite Hb.
      destruct (IHphi1 i Hocc1) as [H1 H2].
      simpl in H.
      rewrite Hocc in H.
      rewrite Hb in H.
      apply H1; assumption.

      pose proof (occ_in_phi_mconj _ _ _ Hocc Hocc1) as Hocc2.
      simpl. simpl in Hocc.
      rewrite Hocc.
      destruct (occ_in_phi_f _ _ Hocc1) as [Hbeq | Hleb].
        rewrite (beq_nat_true _ _ Hbeq) in Hocc2.
        simpl in *.
        apply occ_in_phi_0 in Hocc2.
        simpl in *; discriminate.

        rewrite Hleb.
        destruct (IHphi2 (i - length (pv_in phi1)) Hocc2) as [Ha Hb].
        apply Ha.
        simpl in H.
        rewrite Hocc in H.
        rewrite Hleb in H.
        assumption.

    case_eq (occ_in_phi phi1 i); intros Hocc1.
      simpl.
      simpl in Hocc.
      rewrite Hocc.
      destruct (occ_in_phi_leb2 _ _ Hocc1) as [Ha Hb].
      rewrite Hb.
      destruct (IHphi1 i Hocc1) as [H1 H2].
      simpl in H.
      rewrite Hocc in H.
      rewrite Hb in H.
      apply H2; assumption.

      pose proof (occ_in_phi_mconj _ _ _ Hocc Hocc1) as Hocc2.
      simpl. simpl in Hocc.
      rewrite Hocc.
      destruct (occ_in_phi_f _ _ Hocc1) as [Hbeq | Hleb].
        rewrite (beq_nat_true _ _ Hbeq) in Hocc2.
        simpl in *.
        apply occ_in_phi_0 in Hocc2.
        simpl in *; discriminate.

        rewrite Hleb.
        destruct (IHphi2 (i - length (pv_in phi1)) Hocc2) as [Ha Hb].
        apply Hb.
        simpl in H.
        rewrite Hocc in H.
        rewrite Hleb in H.
        assumption.
Qed.

Lemma is_pos_neg_f_t_mimpl : forall (phi1 phi2 : Modal) (i : nat),
    (forall i : nat,
         occ_in_phi phi1 i = true ->
         (is_pos phi1 i = false -> is_neg phi1 i = true) /\
         (is_pos phi1 i = true -> is_neg phi1 i = false)) ->
    (forall i : nat,
         occ_in_phi phi2 i = true ->
         (is_pos phi2 i = false -> is_neg phi2 i = true) /\
         (is_pos phi2 i = true -> is_neg phi2 i = false)) ->
     occ_in_phi (mconj phi1 phi2) i = true ->
 (is_pos (mimpl phi1 phi2) i = false -> is_neg (mimpl phi1 phi2) i = true) /\
 (is_pos (mimpl phi1 phi2) i = true -> is_neg (mimpl phi1 phi2) i = false).
Proof.
  intros phi1 phi2 i IHphi1 IHphi2 Hocc.
  apply conj; intros H.
    case_eq (occ_in_phi phi1 i); intros Hocc1.
      simpl.
      simpl in Hocc.
      rewrite Hocc.
      destruct (occ_in_phi_leb2 _ _ Hocc1) as [Ha Hb].
      rewrite Hb.
      destruct (IHphi1 i Hocc1) as [H1 H2].
      simpl in H.
      rewrite Hocc in H.
      rewrite Hb in H.
      case_eq (is_pos phi1 i); intros Hpos;
        rewrite Hpos in *.
        rewrite H2;
        reflexivity.

        discriminate.

      pose proof (occ_in_phi_mconj _ _ _ Hocc Hocc1) as Hocc2.
      simpl. simpl in Hocc.
      rewrite Hocc.
      destruct (occ_in_phi_f _ _ Hocc1) as [Hbeq | Hleb].
        rewrite (beq_nat_true _ _ Hbeq) in Hocc2.
        simpl in *.
        apply occ_in_phi_0 in Hocc2.
        simpl in *; discriminate.

        rewrite Hleb.
        destruct (IHphi2 (i - length (pv_in phi1)) Hocc2) as [Ha Hb].
        apply Ha.
        simpl in H.
        rewrite Hocc in H.
        rewrite Hleb in H.
        assumption.

    case_eq (occ_in_phi phi1 i); intros Hocc1.
      simpl.
      simpl in Hocc.
      rewrite Hocc.
      destruct (occ_in_phi_leb2 _ _ Hocc1) as [Ha Hb].
      rewrite Hb.
      destruct (IHphi1 i Hocc1) as [H1 H2].
      simpl in H.
      rewrite Hocc in H.
      rewrite Hb in H.
      case_eq (is_pos phi1 i); intros Hpos;
        rewrite Hpos in *.
        discriminate.

        rewrite H1; reflexivity.

      pose proof (occ_in_phi_mconj _ _ _ Hocc Hocc1) as Hocc2.
      simpl. simpl in Hocc.
      rewrite Hocc.
      destruct (occ_in_phi_f _ _ Hocc1) as [Hbeq | Hleb].
        rewrite (beq_nat_true _ _ Hbeq) in Hocc2.
        simpl in *.
        apply occ_in_phi_0 in Hocc2.
        simpl in *; discriminate.

        rewrite Hleb.
        destruct (IHphi2 (i - length (pv_in phi1)) Hocc2) as [Ha Hb].
        apply Hb.
        simpl in H.
        rewrite Hocc in H.
        rewrite Hleb in H.
        assumption.
Qed.

Lemma is_pos_neg_f_t_box : forall (phi : Modal) (i : nat),
    (forall i : nat,
        occ_in_phi phi i = true ->
        (is_pos phi i = false -> is_neg phi i = true) /\
        (is_pos phi i = true -> is_neg phi i = false)) ->
     occ_in_phi (box phi) i = true ->
  (is_pos (box phi) i = false -> is_neg (box phi) i = true) /\
  (is_pos (box phi) i = true -> is_neg (box phi) i = false).
Proof.
  intros phi i IHphi Hocc.
  rewrite is_pos_box2.
  rewrite is_neg_box2.
  apply IHphi.
  rewrite occ_in_phi_box in Hocc.
  assumption.
Qed.

Lemma is_pos_neg_f_t : forall (phi : Modal) (i : nat),
  occ_in_phi phi i = true ->
  (is_pos phi i = false -> is_neg phi i = true) /\
  (is_pos phi i = true -> is_neg phi i = false).
Proof.
  induction phi; intros i Hocc.
    apply occ_in_phi_atom in Hocc.
    rewrite Hocc.
    simpl.
    apply conj.
      intros; discriminate.

      reflexivity.

    pose proof Hocc as Hocc2.
    apply occ_in_phi_mneg with (phi := phi) in Hocc2.
    destruct (IHphi i Hocc2) as [Ha Hb].
    apply conj; intros H; simpl;
      simpl in Hocc; rewrite Hocc.
      case_eq (is_pos phi i); intros Hpos.
        specialize (Hb Hpos).
        rewrite Hb.
        reflexivity.

        specialize (Ha Hpos).
        simpl in H.
        rewrite Hocc in H.
        rewrite Hpos in *.
        discriminate.

      case_eq (is_pos phi i); intros Hpos.
        specialize (Hb Hpos).
        simpl in H.
        rewrite Hocc in H.
        rewrite Hpos in *.
        discriminate.

        specialize (Ha Hpos).
        rewrite Ha.
        reflexivity.

    apply is_pos_neg_f_t_mconj; assumption.
    apply is_pos_neg_f_t_mconj; assumption.
    apply is_pos_neg_f_t_mimpl; assumption.
    apply is_pos_neg_f_t_box; assumption.
    apply is_pos_neg_f_t_box; assumption.
Qed.

Lemma is_pos_neg_f : forall (phi : Modal) (i : nat),
  occ_in_phi phi i = true ->
  (is_pos phi i = false -> is_neg phi i = true).
Proof.
  intros phi i Hocc Hpos.
  apply is_pos_neg_f_t; assumption.
Qed.

Lemma is_pos_neg_t : forall (phi : Modal) (i : nat),
  (is_pos phi i = true -> is_neg phi i = false).
Proof.
  intros phi i Hpos.
  pose proof (is_pos_occ _ _ Hpos) as Hocc.
  apply is_pos_neg_f_t; assumption.
Qed.

Lemma is_neg_pos_f : forall (phi : Modal) (i : nat),
  occ_in_phi phi i = true ->
  (is_neg phi i = false -> is_pos phi i = true).
Proof.
  intros phi i Hocc Hpos.
  pose proof (is_pos_neg_f _ _ Hocc) as H.
  apply contrapos_bool_ft in H; assumption.
Qed.

Lemma is_neg_pos_t : forall (phi : Modal) (i : nat),
  (is_neg phi i = true -> is_pos phi i = false).
Proof.
  intros phi i Hpos.
  pose proof (is_neg_occ _ _ Hpos) as Hocc.
  pose proof (is_pos_neg_t phi i) as H.
  apply contrapos_bool_tf in H; assumption.
Qed.

Lemma is_pos_neg_not_and : forall (phi : Modal) (i : nat),
  ~(is_pos phi i = true /\ is_neg phi i = true).
Proof.
  unfold not; intros phi i H.
  destruct H as [Hpos Hneg].
  apply is_pos_neg_t in Hpos.
  rewrite Hpos in Hneg.
  discriminate.
Qed.

(* ------------------------------------------------------- *)

Lemma is_pos_neg_or_mconj : forall (phi1 phi2 : Modal) (i : nat),
  (forall i : nat,
      occ_in_phi phi1 i = true -> 
      is_pos phi1 i = true \/ is_neg phi1 i = true) ->
  (forall i : nat,
      occ_in_phi phi2 i = true -> 
      is_pos phi2 i = true \/ is_neg phi2 i = true) ->
   occ_in_phi (mconj phi1 phi2) i = true ->
   is_pos (mconj phi1 phi2) i = true \/ is_neg (mconj phi1 phi2) i = true.
Proof.
  intros phi1 phi2 i IHphi1 IHphi2 Hocc.
  case_eq (occ_in_phi phi1 i); intros Hocc2.
    destruct (IHphi1 i Hocc2) as [Hpos1 | Hneg1].
      simpl is_pos at 1.
      simpl in Hocc.
      rewrite Hocc.
      destruct (occ_in_phi_leb2 _ _ Hocc2) as [Ha Hb].
      rewrite Hb.
      left; assumption.

      simpl is_neg at 1.
      simpl in Hocc.
      rewrite Hocc.
      destruct (occ_in_phi_leb2 _ _ Hocc2) as [Ha Hb].
      rewrite Hb.
      right; assumption.

    pose proof (occ_in_phi_mconj _ _ _ Hocc Hocc2) as Hocc3.
    destruct (occ_in_phi_f _ _ Hocc2) as [Hbeq | Hleb].
      simpl in *; rewrite Hbeq in *; discriminate.
      simpl in Hocc.
      destruct (IHphi2 (i - length (pv_in phi1)) Hocc3) as [Hpos2 | Hneg2].
        simpl is_pos.
        rewrite Hocc.
        rewrite Hleb.
        left; assumption.

        simpl is_neg.
        rewrite Hocc.
        rewrite Hleb.
        right; assumption.
Qed.


Lemma is_pos_neg_or_mneg : forall (phi : Modal) (i : nat),
 (forall i : nat,
    occ_in_phi phi i = true -> is_pos phi i = true \/ is_neg phi i = true) ->
  occ_in_phi (mneg phi) i = true ->
  is_pos (mneg phi) i = true \/ is_neg (mneg phi) i = true.
Proof.
  intros phi i IHphi Hocc.
  pose proof Hocc as Hocc2.
  rewrite occ_in_phi_mneg in Hocc.
  destruct (IHphi i Hocc) as [Hpos | Hneg].
    simpl in *.
    rewrite Hocc2.
    apply is_pos_neg_t in Hpos.
    rewrite Hpos.
    right; reflexivity.

    simpl in *.
    rewrite Hocc2.
    apply is_neg_pos_t in Hneg.
    rewrite Hneg.
    left; reflexivity.
Qed.

Lemma is_pos_neg_or_mimpl : forall (phi1 phi2 : Modal) (i : nat),
   (forall i : nat, occ_in_phi phi1 i = true -> 
        is_pos phi1 i = true \/ is_neg phi1 i = true) ->
   (forall i : nat, occ_in_phi phi2 i = true -> 
        is_pos phi2 i = true \/ is_neg phi2 i = true) ->
    occ_in_phi (mimpl phi1 phi2) i = true ->
    is_pos (mimpl phi1 phi2) i = true \/ is_neg (mimpl phi1 phi2) i = true.
Proof.
  intros phi1 phi2 i IHphi1 IHphi2 Hocc.
  case_eq (occ_in_phi phi1 i); intros Hocc2.
    destruct (IHphi1 i Hocc2) as [Hpos1 | Hneg1].
      simpl is_neg.
      simpl in Hocc.
      rewrite Hocc.
      destruct (occ_in_phi_leb2 _ _ Hocc2) as [Ha Hb].
      rewrite Hb.
      apply is_pos_neg_t in Hpos1.
      rewrite Hpos1.
      right; reflexivity.

      simpl is_pos.
      simpl in Hocc.
      rewrite Hocc.
      destruct (occ_in_phi_leb2 _ _ Hocc2) as [Ha Hb].
      rewrite Hb.
      apply is_neg_pos_t in Hneg1.
      rewrite Hneg1.
      left; reflexivity.

    pose proof (occ_in_phi_mconj _ _ _ Hocc Hocc2) as Hocc3.
    destruct (occ_in_phi_f _ _ Hocc2) as [Hbeq | Hleb].
      simpl in *; rewrite Hbeq in *; discriminate.
      simpl in Hocc.
      destruct (IHphi2 (i - length (pv_in phi1)) Hocc3) as [Hpos2 | Hneg2].
        simpl is_pos.
        rewrite Hocc.
        rewrite Hleb.
        left; assumption.

        simpl is_neg.
        rewrite Hocc.
        rewrite Hleb.
        right; assumption.
Qed.

Lemma is_pos_neg_or : forall (phi : Modal) (i : nat),
  occ_in_phi phi i = true ->
  is_pos phi i = true \/ is_neg phi i = true.
Proof.
  intros phi.
  induction phi; intros  i Hocc;
    try (apply is_pos_neg_or_mconj; assumption).

    apply occ_in_phi_atom in Hocc.
    rewrite Hocc.
    left; reflexivity.

    apply is_pos_neg_or_mneg; assumption.
    apply is_pos_neg_or_mimpl; assumption.

    rewrite is_pos_box2.
    rewrite is_neg_box2.
    apply IHphi.
    apply occ_in_phi_box.
    assumption.

    rewrite is_pos_diam2.
    rewrite is_neg_diam2.
    apply IHphi.
    apply occ_in_phi_box.
    assumption.
Qed.

Lemma is_pos_neg_mimpl_l : forall (phi1 phi2 : Modal) (i : nat),
  is_pos (mimpl phi1 phi2) i = true ->
    ( occ_in_phi phi1 i = true ->  (is_neg phi1 i = true)).
Proof.
  intros phi1 phi2 i Hpos Hocc.
  assert (beq_nat i 0 = false) as Hbeq.
    apply occ_in_phi_0 with (phi := phi1) ; exact Hocc.
  assert (Nat.leb i (length (pv_in phi1)) = true) as Hleb.
    apply occ_in_phi_leb; exact Hocc.
  simpl in Hpos.
  rewrite Hbeq in *.
  rewrite List.app_length in Hpos.
  rewrite leb_plus_r in Hpos.
  rewrite Hleb in Hpos.
  case_eq (is_pos phi1 i); intros Hpos'; rewrite Hpos' in *.
    discriminate.

    apply is_pos_neg_f in Hpos'; assumption.

    apply occ_in_phi_leb2; assumption.
Qed.

Lemma is_pos_neg_mimpl_r : forall (phi1 phi2 : Modal) (i : nat),
  is_pos (mimpl phi1 phi2) i = true ->
    (Nat.leb (length (pv_in phi1) + 1) i = true) ->
      is_pos phi2 (i - (length (pv_in phi1))) = true.
Proof.
  intros phi1 phi2 i Hpos12 Hleb.
  rewrite is_pos_defn_mimpl in *.
  case_eq (occ_in_phi (mimpl phi1 phi2) i); intros Hocc;
  rewrite Hocc in *.
    case_eq (Nat.leb i (length (pv_in phi1))); intros Hleb2;
    rewrite Hleb2 in *.
      apply leb_notswitch in Hleb2.
      rewrite Hleb in *.
      discriminate.

      exact Hpos12.

      discriminate.
Qed.

Lemma is_pos_neg_mimpl : forall (phi1 phi2 : Modal) (i : nat),
  is_pos (mimpl phi1 phi2) i = true ->
    ( occ_in_phi phi1 i = true ->  (is_neg phi1 i = true)) /\
    ((Nat.leb (length (pv_in phi1) + 1) i = true) ->
       is_pos phi2 (i - (length (pv_in phi1))) = true).
Proof.
  intros phi1 phi2 i Hpos.
  apply conj.
    apply is_pos_neg_mimpl_l with (phi2 := phi2); exact Hpos.

    apply is_pos_neg_mimpl_r with (phi1 := phi1); exact Hpos.
Qed.  



(* ---------------------------------------------------------------------------- *)
(* is_neg lemmas *)


Lemma is_neg_mconj_l : forall (phi1 phi2 : Modal) (i : nat),
  is_neg (mconj phi1 phi2) i = true ->
    ( occ_in_phi phi1 i = true ->  (is_neg phi1 i = true)).
Proof.
  intros phi1 phi2 i Hneg Hocc.
  assert (beq_nat i 0 = false) as Hbeq.
    apply occ_in_phi_0 with (phi := phi1); assumption.
  assert (Nat.leb i (length (pv_in phi1)) = true) as Hleb.
    apply occ_in_phi_leb; assumption.
  pose proof (is_neg_occ _ _ Hneg) as Hocc2.
  simpl in *.
  rewrite Hocc2 in *.
  rewrite Hleb in Hneg.
  assumption.
Qed.

Lemma is_neg_mconj_r : forall (phi1 phi2 : Modal) (i : nat),
  is_neg (mconj phi1 phi2) i = true ->
    occ_in_phi phi1 i = false ->
       is_neg phi2 (i - (length (pv_in phi1))) = true.
Proof.
  intros phi1 phi2 i Hneg Hocc.
  pose proof (is_neg_occ _ _ Hneg) as Hocc2.
  simpl in *.
  rewrite Hocc2 in Hneg.
  apply occ_in_phi_f in Hocc.
  destruct Hocc as [Hbeq | Hleb].
    rewrite (beq_nat_true _ _ Hbeq) in *.
    simpl in *.
    discriminate.

    rewrite Hleb in *.
    assumption.
Qed.

Lemma is_neg_mconj : forall (phi1 phi2 : Modal) (i : nat),
  is_neg (mconj phi1 phi2) i = true ->
    ( occ_in_phi phi1 i = true ->  (is_neg phi1 i = true)) /\
    (occ_in_phi phi1 i = false ->
       is_neg phi2 (i - (length (pv_in phi1))) = true).
Proof.
  intros phi1 phi2 i Hneg.
  apply conj.
    apply is_neg_mconj_l with (phi2 := phi2); exact Hneg.
    apply is_neg_mconj_r with (phi1 := phi1); exact Hneg.
Qed.

Lemma is_neg_mdisj_l : forall (phi1 phi2 : Modal) (i : nat),
  is_neg (mdisj phi1 phi2) i = true ->
    ( occ_in_phi phi1 i = true ->  (is_neg phi1 i = true)).
Proof.
  intros phi1 phi2 i Hneg Hocc.
  assert (beq_nat i 0 = false) as Hbeq.
    apply occ_in_phi_0 with (phi := phi1); assumption.
  assert (Nat.leb i (length (pv_in phi1)) = true) as Hleb.
    apply occ_in_phi_leb; assumption.
  pose proof (is_neg_occ _ _ Hneg) as Hocc2.
  simpl in *.
  rewrite Hocc2 in *.
  rewrite Hleb in Hneg.
  assumption.
Qed.

Lemma is_neg_mdisj_r : forall (phi1 phi2 : Modal) (i : nat),
  is_neg (mdisj phi1 phi2) i = true ->
    occ_in_phi phi1 i = false ->
       is_neg phi2 (i - (length (pv_in phi1))) = true.
Proof.
  intros phi1 phi2 i Hneg Hocc.
  pose proof (is_neg_occ _ _ Hneg) as Hocc2.
  simpl in *.
  rewrite Hocc2 in Hneg.
  apply occ_in_phi_f in Hocc.
  destruct Hocc as [Hbeq | Hleb].
    rewrite (beq_nat_true _ _ Hbeq) in *.
    simpl in *.
    discriminate.

    rewrite Hleb in *.
    assumption.
Qed.

Lemma is_neg_mdisj : forall (phi1 phi2 : Modal) (i : nat),
  is_neg (mdisj phi1 phi2) i = true ->
    ( occ_in_phi phi1 i = true ->  (is_neg phi1 i = true)) /\
    (occ_in_phi phi1 i = false ->
       is_neg phi2 (i - (length (pv_in phi1))) = true).
Proof.
  intros phi1 phi2 i Hneg.
  apply conj.
    apply is_neg_mdisj_l with (phi2 := phi2); exact Hneg.
    apply is_neg_mdisj_r with (phi1 := phi1); exact Hneg.
Qed.

Lemma is_neg_mimpl_l : forall (phi1 phi2 : Modal) (i : nat),
  is_neg (mimpl phi1 phi2) i = true ->
    ( occ_in_phi phi1 i = true ->  (is_neg phi1 i = false)).
Proof.
  intros phi1 phi2 i Hneg Hocc.
  assert (beq_nat i 0 = false) as Hbeq.
    apply occ_in_phi_0 with (phi := phi1); assumption.
  assert (Nat.leb i (length (pv_in phi1)) = true) as Hleb.
    apply occ_in_phi_leb; assumption.
  pose proof (is_neg_occ _ _ Hneg) as Hocc2.
  simpl in *.
  rewrite Hocc2 in *.
  rewrite Hleb in Hneg.
  case_eq (is_neg phi1 i); intros H; rewrite H in *.
    discriminate. reflexivity.
Qed.

Lemma is_neg_mimpl_r : forall (phi1 phi2 : Modal) (i : nat),
  is_neg (mimpl phi1 phi2) i = true ->
    occ_in_phi phi1 i = false ->
       is_neg phi2 (i - (length (pv_in phi1))) = true.
Proof.
  intros phi1 phi2 i Hneg Hocc.
  pose proof (is_neg_occ _ _ Hneg) as Hocc2.
  simpl in *.
  rewrite Hocc2 in Hneg.
  apply occ_in_phi_f in Hocc.
  destruct Hocc as [Hbeq | Hleb].
    rewrite (beq_nat_true _ _ Hbeq) in *.
    simpl in *.
    discriminate.

    rewrite Hleb in *.
    assumption.
Qed.

Lemma is_neg_mimpl : forall (phi1 phi2 : Modal) (i : nat),
  is_neg (mimpl phi1 phi2) i = true ->
    ( occ_in_phi phi1 i = true ->  (is_neg phi1 i = false)) /\
    (occ_in_phi phi1 i = false ->
       is_neg phi2 (i - (length (pv_in phi1))) = true).
Proof.
  intros phi1 phi2 i Hneg.
  apply conj.
    apply is_neg_mimpl_l with (phi2 := phi2); exact Hneg.
    apply is_neg_mimpl_r with (phi1 := phi1); exact Hneg.
Qed.

