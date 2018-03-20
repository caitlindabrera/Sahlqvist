Require Import Modal.
Require Import Arith.EqNat.
Require Import ST_setup my_arith Coq.Arith.PeanoNat.
Require Import my_arith__my_leb_nat my_bool.



Fixpoint occ_in_phi (phi : Modal) (i : nat) : bool :=
  if beq_nat i 0 
    then false
    else if Nat.leb i (length (pv_in phi)) 
           then true
           else false.

Lemma occ_in_phi_defn : forall (phi : Modal) (i : nat),
  occ_in_phi phi i = if beq_nat i 0 then false
                                    else if Nat.leb i (length (pv_in phi))
                                            then true
                                            else false.
Proof.
  intros; induction phi; simpl; reflexivity.
Qed.


Lemma occ_in_phi_leb : forall (phi : Modal) (i : nat),
  occ_in_phi phi i = true ->
    Nat.leb i (length (pv_in phi)) = true.
Proof.
  intros phi i Hocc.
  case_eq (Nat.leb i (length (pv_in phi))); intros Hleb;
  [reflexivity | unfold occ_in_phi in Hocc; induction phi;
  rewrite Hleb in *; case_eq (beq_nat i 0); intros Hbeq;
  rewrite Hbeq in *; discriminate].
Qed.

Lemma occ_in_phi_0 : forall (phi : Modal) (i : nat),
  occ_in_phi phi i = true -> beq_nat i 0 = false.
Proof.
  intros phi i Hocc.
  destruct i.
    unfold occ_in_phi in *.
    induction phi; simpl in *; discriminate.

    simpl; reflexivity.
Qed.

Lemma occ_in_phi_leb3 : forall (phi : Modal) (n : nat),
  beq_nat n 0 = false ->
    Nat.leb n (length (pv_in phi)) = true -> 
      occ_in_phi phi n = true.
Proof.
  intros phi n H_beq H_leb.
  unfold occ_in_phi.
  induction phi; simpl in *;
    rewrite H_beq in *; rewrite H_leb in *; reflexivity.
Qed.

Lemma occ_in_phi_leb2 : forall (phi : Modal) (n : nat),
  occ_in_phi phi n = true ->
    (beq_nat n 0 = false /\
      Nat.leb n (length (pv_in phi)) = true).
Proof.
  intros phi n Hocc.
  assert (beq_nat n 0 = false) as Hbeq.
    case_eq (beq_nat n 0); intros H; try reflexivity.
      pose proof (beq_nat_true n 0 H) as Heq; rewrite Heq in *.
      unfold occ_in_phi in *; induction phi; simpl; discriminate.
  apply conj.
    exact Hbeq.

    case_eq (Nat.leb n (length (pv_in phi))); intros H;
    try reflexivity.
    unfold occ_in_phi in *.
    induction phi;
      rewrite H in *; rewrite Hbeq in *; discriminate.
Qed.

Lemma occ_in_phi_beq_t : forall (phi : Modal) (i : nat),
  occ_in_phi phi i = true -> beq_nat i 0 = true ->
    False.
Proof.
  intros phi i H H1.
  unfold occ_in_phi in *.
  induction phi; rewrite H1 in *; simpl; discriminate.
Qed.

Lemma occ_in_phi_beq_f : forall (phi : Modal) (i : nat),
  occ_in_phi phi i = true -> beq_nat i 0 = false ->
    (if Nat.leb i (length (pv_in phi)) then true else false) = true.
Proof.
  intros phi i H H1.
  unfold occ_in_phi in*.
  induction phi; rewrite H1 in *; exact H.
Qed.

Lemma occ_in_phi_mconj_l : forall (phi1 phi2 : Modal) (i : nat),
  occ_in_phi phi1 i = true -> 
    occ_in_phi (mconj phi1 phi2) i = true.
Proof.
  intros phi1 phi2 i Hocc1.
  simpl.
  rewrite List.app_length.
(* Search length app.
  rewrite length_app_pv. *)
  case_eq (beq_nat i 0); intros Hbeq.
    unfold occ_in_phi in Hocc1;
    induction phi1; rewrite Hbeq in *; simpl; discriminate.

    case_eq (Nat.leb i (length (pv_in phi1))); intros Hleb.
      rewrite leb_plus_r;
        [reflexivity | exact Hleb].

      unfold occ_in_phi in Hocc1; 
      induction phi1; rewrite Hbeq in *; rewrite Hleb in *;
      discriminate.
Qed.

Lemma occ_in_phi_mdisj_l : forall (phi1 phi2 : Modal) (i : nat),
  occ_in_phi phi1 i = true -> 
    occ_in_phi (mdisj phi1 phi2) i = true.
Proof.
  intros phi1 phi2 i Hocc1.
  simpl.
  rewrite List.app_length.
  case_eq (beq_nat i 0); intros Hbeq.
    unfold occ_in_phi in Hocc1;
    induction phi1; rewrite Hbeq in *; simpl; discriminate.

    case_eq (Nat.leb i (length (pv_in phi1))); intros Hleb.
      rewrite leb_plus_r;
        [reflexivity | exact Hleb].

      unfold occ_in_phi in Hocc1; 
      induction phi1; rewrite Hbeq in *; rewrite Hleb in *;
      discriminate.
Qed.

Lemma occ_in_phi_mimpl_l : forall (phi1 phi2 : Modal) (i : nat),
  occ_in_phi phi1 i = true -> 
    occ_in_phi (mimpl phi1 phi2) i = true.
Proof.
  intros phi1 phi2 i Hocc1.
  simpl.
  rewrite List.app_length.
  case_eq (beq_nat i 0); intros Hbeq.
    unfold occ_in_phi in Hocc1;
    induction phi1; rewrite Hbeq in *; simpl; discriminate.

    case_eq (Nat.leb i (length (pv_in phi1))); intros Hleb.
      rewrite leb_plus_r;
        [reflexivity | exact Hleb].

      unfold occ_in_phi in Hocc1; 
      induction phi1; rewrite Hbeq in *; rewrite Hleb in *;
      discriminate.
Qed.

Lemma occ_in_phi_mconj_r : forall (phi1 phi2 : Modal) (i : nat),
  occ_in_phi phi2 i = true -> 
    occ_in_phi (mconj phi1 phi2) (length (pv_in phi1) + i) = true.
Proof.
  intros phi1 phi2 i Hocc.
  simpl.
  case_eq (beq_nat (length (pv_in phi1) + i) 0); intros Hbeq.
    apply beq_nat_true in Hbeq.
    apply beq_nat_0 in Hbeq.
    destruct Hbeq as [Hl Hi].
    rewrite Hi in *.
    unfold occ_in_phi in Hocc.
    destruct phi2; simpl in *; discriminate.

    rewrite List.app_length.
    rewrite <- leb_plus_pre with (m := (length (pv_in phi1))).
    apply occ_in_phi_leb2 in Hocc.
    destruct Hocc as [l r].
    rewrite r.
    reflexivity.
Qed.

Lemma occ_in_phi_mdisj_r : forall (phi1 phi2 : Modal) (i : nat),
  occ_in_phi phi2 i = true -> 
    occ_in_phi (mdisj phi1 phi2) (length (pv_in phi1) + i) = true.
Proof.
  intros phi1 phi2 i Hocc.
  simpl.
  case_eq (beq_nat (length (pv_in phi1) + i) 0); intros Hbeq.
    apply beq_nat_true in Hbeq.
    apply beq_nat_0 in Hbeq.
    destruct Hbeq as [Hl Hi].
    rewrite Hi in *.
    unfold occ_in_phi in Hocc.
    destruct phi2; simpl in *; discriminate.

    rewrite List.app_length.
    rewrite <- leb_plus_pre with (m := (length (pv_in phi1))).
    apply occ_in_phi_leb2 in Hocc.
    destruct Hocc as [l r].
    rewrite r.
    reflexivity.
Qed.

Lemma occ_in_phi_mimpl_r : forall (phi1 phi2 : Modal) (i : nat),
  occ_in_phi phi2 i = true -> 
    occ_in_phi (mimpl phi1 phi2) (length (pv_in phi1) + i) = true.
Proof.
  intros phi1 phi2 i Hocc.
  simpl.
  case_eq (beq_nat (length (pv_in phi1) + i) 0); intros Hbeq.
    apply beq_nat_true in Hbeq.
    apply beq_nat_0 in Hbeq.
    destruct Hbeq as [Hl Hi].
    rewrite Hi in *.
    unfold occ_in_phi in Hocc.
    destruct phi2; simpl in *; discriminate.

    rewrite List.app_length.
    rewrite <- leb_plus_pre with (m := (length (pv_in phi1))).
    apply occ_in_phi_leb2 in Hocc.
    destruct Hocc as [l r].
    rewrite r.
    reflexivity.
Qed.

Lemma occ_in_phi_mconj : forall (phi1 phi2 : Modal) (i : nat),
  occ_in_phi (mconj phi1 phi2) i = true ->
    occ_in_phi phi1 i = false ->
      occ_in_phi phi2 (i - length (pv_in phi1)) = true.

Proof.
  intros phi1 phi2 i Hocc12 Hocc1.
  rewrite occ_in_phi_defn.
  pose proof (occ_in_phi_leb2 (mconj phi1 phi2) i Hocc12) as H.
  destruct H as [H1 H2].
  case_eq (beq_nat (i - length (pv_in phi1)) 0); intros Hbeq.
    rewrite occ_in_phi_defn in Hocc1.
    apply beq_nat_leb in Hbeq.
    rewrite Hbeq in *.
    rewrite H1 in *.
    discriminate.

    simpl in H2.
    rewrite List.app_length in H2.
    apply leb_minus with (i := (length (pv_in phi1))) in H2.
    rewrite arith_plus_3 in H2.
    rewrite H2 in *.
    reflexivity.
Qed.

Lemma occ_in_phi_mimpl : forall (phi1 phi2 : Modal) (i : nat),
  occ_in_phi (mimpl phi1 phi2) i = true ->
    occ_in_phi phi1 i = false ->
      occ_in_phi phi2 (i - length (pv_in phi1)) = true.
Proof.
  intros phi1 phi2 i Hocc12 Hocc1.
  rewrite occ_in_phi_defn.
  pose proof (occ_in_phi_leb2 (mimpl phi1 phi2) i Hocc12) as H.
  destruct H as [H1 H2].
  case_eq (beq_nat (i - length (pv_in phi1)) 0); intros Hbeq.
    rewrite occ_in_phi_defn in Hocc1.
    apply beq_nat_leb in Hbeq.
    rewrite Hbeq in *.
    rewrite H1 in *.
    discriminate.

    simpl in H2.
    rewrite List.app_length in H2.
    apply leb_minus with (i := (length (pv_in phi1))) in H2.
    rewrite arith_plus_3 in H2.
    rewrite H2 in *.
    reflexivity.
Qed.

Lemma occ_in_phi_mneg : forall (phi : Modal) (i : nat),
  occ_in_phi (mneg phi) i = true <->
    occ_in_phi phi i = true.
Proof.
  intros phi i.
  simpl.
  rewrite occ_in_phi_defn.
  apply iff_refl.
Qed.

Lemma occ_in_phi_mneg2 : forall (phi : Modal) (i : nat),
  occ_in_phi (mneg phi) i = occ_in_phi phi i.
Proof.
  intros phi i.
  case_eq (occ_in_phi phi i); intros Hocc.
    apply occ_in_phi_mneg; assumption.

    destruct (occ_in_phi_mneg phi i) as [fwd rev].
    apply (contrapos_bool_tt _ _ fwd); assumption.
Qed.

Lemma occ_in_phi_box : forall (phi : Modal) (i : nat),
  occ_in_phi (box phi) i = true <->
    occ_in_phi phi i = true.
Proof.
  intros.
  unfold occ_in_phi.
  induction phi; case (beq_nat i 0); simpl; apply iff_refl.
Qed.

Lemma occ_in_phi_box2 : forall (phi : Modal) (i : nat),
  occ_in_phi (box phi) i = occ_in_phi phi i.
Proof.
  intros.
  case_eq (occ_in_phi phi i); intros Hocc.
    apply occ_in_phi_box; assumption.

    destruct (occ_in_phi_box phi i) as [fwd rev].
    apply (contrapos_bool_tt _ _ fwd); assumption.
Qed.


Lemma occ_in_phi_diam : forall (phi : Modal) (i : nat),
  occ_in_phi (diam phi) i = true <->
    occ_in_phi phi i = true.
Proof.
  intros.
  unfold occ_in_phi.
  induction phi; case (beq_nat i 0); simpl; apply iff_refl.
Qed.

Lemma occ_in_phi_diam2 : forall (phi : Modal) (i : nat),
  occ_in_phi (diam phi) i = occ_in_phi phi i.
Proof.
  intros.
  case_eq (occ_in_phi phi i); intros Hocc.
    apply occ_in_phi_diam; assumption.

    destruct (occ_in_phi_diam phi i) as [fwd rev].
    apply (contrapos_bool_tt _ _ fwd); assumption.
Qed.

Lemma occ_in_phi_atom : forall (p : propvar) (i : nat),
  occ_in_phi (atom p) i = true -> i = 1.
Proof.
  intros p i Hocc.
  simpl in  *.
  case_eq i.
    intros Hi; rewrite Hi in *.
    simpl in *; discriminate.

    intros j Hi; rewrite Hi in *.
    simpl in *.
    case_eq j.
      intros Hj; rewrite Hj in *.
      reflexivity.

      intros k Hj; rewrite Hj in *.
      simpl in *; discriminate.
Qed.

Lemma occ_in_phi_f : forall (phi : Modal) (i : nat),
  occ_in_phi phi i = false ->
  beq_nat i 0 = true \/ Nat.leb i (length (pv_in phi)) = false.
Proof.
  intros phi i Hocc.
  case_eq (beq_nat i 0); intros Hbeq.
    left; reflexivity.

    case_eq (Nat.leb i (length (pv_in phi))); intros Hleb.
      induction phi; simpl in *; rewrite Hbeq in *;
      rewrite Hleb in *; discriminate.

      right; reflexivity.
Qed.

