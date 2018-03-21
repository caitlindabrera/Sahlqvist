Require Import Modal.
Require Import is_pos_neg.
Require Import at_pv.
Require Import occ_in_phi.
Require Import p_occurs_in.
Require Import Arith.EqNat.
Require Import my_bool.
Require Import my_arith__my_leb_nat.
Require Import is_pos_neg_lemmas.


(* ---------------------------------------------------------------------------- *)
(* All occurrences of p in phi are positive. *)

Definition p_is_pos (phi : Modal) (p : propvar) : Prop :=
  (p_occurs_in_phi phi p = true ->
    forall i : nat, occ_in_phi phi i = true ->
      match p, at_pv (pv_in phi) i with
      | pv pn, pv qm => pn = qm
      end
        -> is_pos phi i = true) /\
   (p_occurs_in_phi phi p = false -> False).

Definition p_is_neg (phi : Modal) (p : propvar) : Prop :=
  (p_occurs_in_phi phi p = true ->
    forall i : nat, occ_in_phi phi i = true ->
      match p, at_pv (pv_in phi) i with
      | pv pn, pv qm => pn = qm
      end
        -> is_neg phi i = true) /\
   (p_occurs_in_phi phi p = false -> False).

(* ---------------------------------------------------------------------------- *)
(* p_is_pos lemmas *)

Lemma p_is_pos_notin : forall (phi : Modal) (p : propvar),
  p_is_pos phi p -> p_occurs_in_phi phi p = true.
Proof.
  intros phi p H_pos.
  unfold p_is_pos in H_pos.
  case_eq (p_occurs_in_phi phi p); intros H_occ;
  rewrite H_occ in *.
    reflexivity.

    destruct H_pos as [t f].
    assert (false = false) as Hf by reflexivity.
    specialize (f Hf); contradiction.
Qed.

Lemma p_is_pos_atom : forall (p q : propvar),
  p_is_pos (atom q) p -> p = q.
Proof.
  intros p q H_pos.
  destruct p as [pn]; destruct q as [qm]. 
  unfold p_is_pos in H_pos.
  destruct H_pos as [t f].
  simpl in *.  
  case_eq (p_occurs_in_phi (atom (pv qm)) (pv pn));
  intros H_eq; rewrite H_eq in *.
    unfold p_occurs_in_phi in H_eq.
    simpl in H_eq.
    case_eq (beq_nat pn qm); intros H_beq;
    rewrite H_beq in *.
      pose proof (beq_nat_true pn qm H_beq) as H.
      rewrite H; reflexivity.

      discriminate.

    assert (false = false) as Hf by reflexivity.
    pose proof (f Hf); contradiction.
Qed.

Lemma p_is_pos_mneg : forall (phi : Modal) (p : propvar),
  p_is_pos (mneg phi) p -> ~ p_is_pos phi p .
Proof.
  unfold not; intros phi p H_neg H_pos.
  unfold p_is_pos in *. unfold p_occurs_in_phi in *.
  simpl in *.
  destruct H_neg as [t1 l1]; destruct H_pos as [t2 l2].
  case_eq (p_occurs_in_l (pv_in phi) p); intros H_eq.
    pose proof (p_occurs_in_l_ex (pv_in phi) p H_eq) as H.
    destruct H as [L1 [L2 H]].
    rewrite <- H in *.
    rewrite H_eq in *.
    specialize (t1 true_true (length L1 + 1));
    specialize (t2 true_true (length L1 + 1)).

pose proof (@List.app_length propvar) as tryin.
(*    rewrite length_app_pv in *. *)
    simpl length in *.
    rewrite not_zero in *.
    pose proof (leb_refl (length L1 )) as HL1.
    pose proof (leb_plus_gen (length L1) (length L1) 1 (S (length L2))) as H2.
    assert (Nat.leb 1 (S (length L2))=true) as H3 by reflexivity.
    specialize (H2 HL1 H3).
rewrite List.app_length in t1.
simpl length in t1.
rewrite H2 in t1.

(*    rewrite H2 in *. *)
    rewrite occ_in_phi_leb3 in t2.
    specialize (t1 true_true); specialize (t2 true_true).
    destruct p as [pn].
    rewrite (at_pv_app_cons) in *.
    assert (pn = pn) as Hpn by reflexivity.
    specialize (t1 Hpn); specialize (t2 Hpn).
    rewrite t2 in t1.
    discriminate.

      rewrite not_zero; reflexivity.
    rewrite <- H.
    rewrite List.app_length.
    simpl.
    rewrite arith_plus_comm.
    rewrite (arith_plus_comm (length L1) (S (length L2))).
    pose proof ( leb_plus 1 (S (length L2)) (length L1)) as H4.
    rewrite H3 in H4. 
    symmetry; exact H4.

    apply l1; exact H_eq.
Qed.

Lemma p_is_pos_mconj2l: forall (phi1 phi2 : Modal) (p : propvar),
  p_is_pos (mconj phi1 phi2) p -> 
    p_occurs_in_phi phi1 p = true ->
      p_is_pos phi1 p.
Proof.
  intros phi1 phi2 p Hpos Hocc.
  unfold p_is_pos in *.
  destruct Hpos as [l r].
  apply conj.
    intros H i Hocc2 Heq.
    destruct p as [pn].
    assert (p_occurs_in_phi phi1 (pv pn) = true \/
         p_occurs_in_phi phi2 (pv pn) = true) as H2.
      left; exact Hocc.
    destruct (p_occurs_in_phi_mconj phi1 phi2 (pv pn)) as [Hf Hr].
    specialize (Hr H2).
    clear H2 Hf.
    specialize (l Hr i (occ_in_phi_mconj_l phi1 phi2 i Hocc2)).
    pose proof (is_pos_mconj phi1 phi2 i) as H4.
    destruct H4 as [H4l H4r].
      apply l.
      simpl.
      rewrite at_pv_app_l.
        exact Heq.

        apply PeanoNat.Nat.leb_le.
        apply occ_in_phi_leb; exact Hocc2.

      apply H4l.
      exact Hocc2.

    rewrite Hocc; intros; discriminate.
Qed.

Lemma p_is_pos_mconj2r: forall (phi1 phi2 : Modal) (p : propvar),
  p_is_pos (mconj phi1 phi2) p -> 
    p_occurs_in_phi phi2 p = true ->
      p_is_pos phi2 p.
Proof.
  intros phi1 phi2 p Hpos Hpocc.
  unfold p_is_pos.
  destruct Hpos as [Hpocct Hpoccf].
  apply conj; intros H.
    intros i Hocc Heq.
    pose proof (occ_in_phi_mconj_r phi1 phi2 i Hocc) as H0.
    destruct p as [pn].
    case_eq (p_occurs_in_phi (mconj phi1 phi2) (pv pn));
    intros Hpocc2.
      specialize (Hpocct Hpocc2 (length (pv_in phi1) + i) H0).
      simpl pv_in in Hpocct.
      rewrite at_pv_app_r in Hpocct.
        remember (at_pv (pv_in phi2) i) as t;
        destruct t as [qm].
        specialize (Hpocct Heq).
        pose proof (is_pos_mconj_r phi1 phi2 (length (pv_in phi1) + i)
             Hpocct).
        assert (Nat.leb (length (pv_in phi1) + 1) (length (pv_in phi1) + i)
                    = true) as H2.
          rewrite <- leb_plus_pre with (m := (length (pv_in phi1))).
          unfold Nat.leb.
          destruct i.
            apply occ_in_phi_0 in Hocc.
            simpl in Hocc; discriminate.

            reflexivity.
        specialize (H1 H2).
        rewrite arith_plus_3 in H1.
        assumption.

        apply occ_in_phi_leb2 in Hocc.
        apply Hocc.

      specialize (Hpoccf Hpocc2); contradiction.

    rewrite H in *; discriminate.
Qed.

Lemma p_is_pos_mdisj2l: forall (phi1 phi2 : Modal) (p : propvar),
  p_is_pos (mdisj phi1 phi2) p -> 
    p_occurs_in_phi phi1 p = true ->
      p_is_pos phi1 p.
Proof.
  intros phi1 phi2 p Hpos Hocc.
  unfold p_is_pos in *.
  destruct Hpos as [l r].
  apply conj.
    intros H i Hocc2 Heq.
    destruct p as [pn].
    assert (p_occurs_in_phi phi1 (pv pn) = true \/
         p_occurs_in_phi phi2 (pv pn) = true) as H2.
      left; exact Hocc.
    destruct (p_occurs_in_phi_mdisj phi1 phi2 (pv pn)) as [Hf Hr].
    specialize (Hr H2).
    clear H2 Hf.
    specialize (l Hr i (occ_in_phi_mdisj_l phi1 phi2 i Hocc2)).
    pose proof (is_pos_mdisj phi1 phi2 i) as H4.
    destruct H4 as [H4l H4r].
      apply l.
      simpl.
      rewrite at_pv_app_l.
        exact Heq.

        apply PeanoNat.Nat.leb_le.
        apply occ_in_phi_leb; exact Hocc2.

      apply H4l.
      exact Hocc2.

    rewrite Hocc; intros; discriminate.
Qed.

Lemma p_is_pos_mdisj2r: forall (phi1 phi2 : Modal) (p : propvar),
  p_is_pos (mdisj phi1 phi2) p -> 
    p_occurs_in_phi phi2 p = true ->
      p_is_pos phi2 p.
Proof.
  intros phi1 phi2 p Hpos Hpocc.
  unfold p_is_pos.
  destruct Hpos as [Hpocct Hpoccf].
  apply conj; intros H.
    intros i Hocc Heq.
    pose proof (occ_in_phi_mdisj_r phi1 phi2 i Hocc) as H0.
    destruct p as [pn].
    case_eq (p_occurs_in_phi (mconj phi1 phi2) (pv pn));
    intros Hpocc2.
      specialize (Hpocct Hpocc2 (length (pv_in phi1) + i) H0).
      simpl pv_in in Hpocct.
      rewrite at_pv_app_r in Hpocct.
        remember (at_pv (pv_in phi2) i) as t;
        destruct t as [qm].
        specialize (Hpocct Heq).
        pose proof (is_pos_mdisj_r phi1 phi2 (length (pv_in phi1) + i)
             Hpocct).
        assert (Nat.leb (length (pv_in phi1) + 1) (length (pv_in phi1) + i)
                    = true) as H2.
          rewrite <- leb_plus_pre with (m := (length (pv_in phi1))).
          unfold Nat.leb.
          destruct i.
            apply occ_in_phi_0 in Hocc.
            simpl in Hocc; discriminate.

            reflexivity.
        specialize (H1 H2).
        rewrite arith_plus_3 in H1.
        assumption.

        apply occ_in_phi_leb2 in Hocc.
        apply Hocc.

      specialize (Hpoccf Hpocc2); contradiction.

    rewrite H in *; discriminate.
Qed.

Lemma p_is_pos_mimpl2l: forall (phi1 phi2 : Modal) (p : propvar),
  p_is_pos (mimpl phi1 phi2) p -> 
    p_occurs_in_phi phi1 p = true ->
      p_is_neg phi1 p.
Proof.
  intros phi1 phi2 p Hpos Hocc.
  unfold p_is_pos in *.
  unfold p_is_neg.
  destruct Hpos as [l r].
  apply conj.
    intros H i Hocc2 Heq.
    destruct p as [pn].
    assert (p_occurs_in_phi phi1 (pv pn) = true \/
         p_occurs_in_phi phi2 (pv pn) = true) as H2.
      left; exact Hocc.
    destruct (p_occurs_in_phi_mimpl phi1 phi2 (pv pn)) as [Hf Hr].
    specialize (Hr H2).
    clear H2 Hf.
    specialize (l Hr i (occ_in_phi_mimpl_l phi1 phi2 i Hocc2)).
    pose proof (is_pos_neg_mimpl phi1 phi2 i) as H4.
    destruct H4 as [H4l H4r].
      apply l.
      simpl.
      rewrite at_pv_app_l.
        exact Heq.

        apply PeanoNat.Nat.leb_le.
        apply occ_in_phi_leb; exact Hocc2.

      apply H4l.
      exact Hocc2.

    rewrite Hocc; intros; discriminate.
Qed.

Lemma p_is_pos_mimpl2r: forall (phi1 phi2 : Modal) (p : propvar),
  p_is_pos (mimpl phi1 phi2) p -> 
    p_occurs_in_phi phi2 p = true ->
      p_is_pos phi2 p.
Proof.
  intros phi1 phi2 p Hpos Hpocc.
  unfold p_is_pos.
  destruct Hpos as [Hpocct Hpoccf].
  apply conj; intros H.
    intros i Hocc Heq.
    pose proof (occ_in_phi_mimpl_r phi1 phi2 i Hocc) as H0.
    destruct p as [pn].
    case_eq (p_occurs_in_phi (mimpl phi1 phi2) (pv pn));
    intros Hpocc2.
      specialize (Hpocct Hpocc2 (length (pv_in phi1) + i) H0).
      simpl pv_in in Hpocct.
      rewrite at_pv_app_r in Hpocct.
        remember (at_pv (pv_in phi2) i) as t;
        destruct t as [qm].
        specialize (Hpocct Heq).
        pose proof (is_pos_neg_mimpl_r phi1 phi2 (length (pv_in phi1) + i)
             Hpocct).
        assert (Nat.leb (length (pv_in phi1) + 1) (length (pv_in phi1) + i)
                    = true) as H2.
          rewrite <- leb_plus_pre with (m := (length (pv_in phi1))).
          unfold Nat.leb.
          destruct i.
            apply occ_in_phi_0 in Hocc.
            simpl in Hocc; discriminate.

            reflexivity.
        specialize (H1 H2).
        rewrite arith_plus_3 in H1.
        assumption.

        apply occ_in_phi_leb2 in Hocc.
        apply Hocc.

      specialize (Hpoccf Hpocc2); contradiction.

    rewrite H in *; discriminate.
Qed.

Lemma p_is_pos_box : forall (phi : Modal) (p : propvar),
  p_is_pos (box phi) p -> p_is_pos phi p.
Proof.
  intros phi p H.
  unfold p_is_pos in *.
  destruct H as [t f].
  apply conj.
    intros Hoccp i Hocc Hat.
    destruct p as [pn].
    case_eq (at_pv (pv_in phi) i).
      intros qm Hat2.
      rewrite Hat2 in *.
      destruct (p_occurs_in_phi_box phi (pv pn)) as [forw rev].
      specialize (rev Hoccp).
      rewrite rev in t.
      clear forw rev.
      specialize (t true_true i).
      destruct (occ_in_phi_box phi i) as [forw rev]; 
      specialize (rev Hocc); rewrite rev in t; clear forw rev.
      simpl pv_in in t.
      rewrite Hat2 in t.
      specialize (t true_true Hat).
      apply is_pos_box; exact t.

    intros Hf.
    apply f.
    pose proof (contrapos_bool_tt (p_occurs_in_phi (box phi) p) 
                               (p_occurs_in_phi phi p)) as H.
    destruct (p_occurs_in_phi_box phi p) as [forw rev].
    specialize (H forw). 
    apply H; exact Hf. 
Qed.

Lemma p_is_pos_diam : forall (phi : Modal) (p : propvar),
  p_is_pos (diam phi) p -> p_is_pos phi p.
Proof.
  intros phi p H.
  unfold p_is_pos in *.
  destruct H as [t f].
  apply conj.
    intros Hoccp i Hocc Hat.
    destruct p as [pn].
    case_eq (at_pv (pv_in phi) i).
      intros qm Hat2.
      rewrite Hat2 in *.
      destruct (p_occurs_in_phi_diam phi (pv pn)) as [forw rev].
      specialize (rev Hoccp).
      rewrite rev in t.
      clear forw rev.
      specialize (t true_true i).
      destruct (occ_in_phi_diam phi i) as [forw rev]; 
      specialize (rev Hocc); rewrite rev in t; clear forw rev.
      simpl pv_in in t.
      rewrite Hat2 in t.
      specialize (t true_true Hat).
      apply is_pos_diam; exact t.

    intros Hf.
    apply f.
    pose proof (contrapos_bool_tt (p_occurs_in_phi (diam phi) p) 
                               (p_occurs_in_phi phi p)) as H.
    destruct (p_occurs_in_phi_diam phi p) as [forw rev].
    specialize (H forw). 
    apply H; exact Hf. 
Qed.


(* ---------------------------------------------------------------------------- *)
(* p_is_neg lemmas *)

Lemma p_is_neg_notin : forall (phi : Modal) (p : propvar),
  p_is_neg phi p -> p_occurs_in_phi phi p = true.
Proof.
  intros phi p Hneg.
  case_eq (p_occurs_in_phi phi p); intros Hpocc.
    reflexivity.

    unfold p_is_neg in Hneg.
    destruct Hneg as [t f].
    specialize (f Hpocc); contradiction.
Qed.

Lemma p_is_neg_atom : forall (p q : propvar),
  p_is_neg (atom q) p -> p = q.
Proof.
  intros p q H.
  pose proof (p_is_neg_notin (atom q) p H) as H2.
  unfold p_occurs_in_phi in H2.
  simpl in *.
  destruct p as [pn]; destruct q as [qm].
  case_eq (beq_nat pn qm); intros Hbeq; rewrite Hbeq in *.
    rewrite (beq_nat_true pn qm Hbeq); reflexivity.

    discriminate.
Qed.

Lemma p_is_neg_mconj2l: forall (phi1 phi2 : Modal) (p : propvar),
  p_is_neg (mconj phi1 phi2) p -> 
    p_occurs_in_phi phi1 p = true ->
      p_is_neg phi1 p.
Proof.
  intros phi1 phi2 p Hneg Hpocc.
  unfold p_is_neg in *.
  destruct Hneg as [l r].
  assert (p_occurs_in_phi (mconj phi1 phi2) p = true) as Hpocc3.
    apply p_occurs_in_phi_mconj.
    left; exact Hpocc.
  apply conj; intros Hpocc2.
    intros i Hocc Heq.
    assert (Nat.leb i (length (pv_in phi1)) = true) as Hleb.
      apply occ_in_phi_leb.
      exact Hocc.
    assert (beq_nat i 0 = false) as Hbeq.
      apply occ_in_phi_0 with (phi:=phi1).
      exact Hocc.
    pose proof (occ_in_phi_mconj_l phi1 phi2 i Hocc) as Hocc2.
    specialize (l Hpocc3 i Hocc2).
    simpl pv_in in l.    
    rewrite at_pv_app_l in l.
      specialize (l Heq).
      destruct (is_neg_mconj phi1 phi2 i l) as [Hl Hr].
      apply Hl.
      exact Hocc.

      apply PeanoNat.Nat.leb_le.
      exact Hleb.

    rewrite Hpocc2 in *; discriminate.
Qed.

Lemma p_is_neg_mconj2r: forall (phi1 phi2 : Modal) (p : propvar),
  p_is_neg (mconj phi1 phi2) p -> 
    p_occurs_in_phi phi2 p = true ->
      p_is_neg phi2 p.
Proof.
  intros phi1 phi2 p Hneg Hpocc.
  unfold p_is_neg.
  destruct Hneg as [Hpocct Hpoccf].
  apply conj; intros H.
    intros i Hocc Heq.
    pose proof (occ_in_phi_mconj_r phi1 phi2 i Hocc) as H0.
    destruct p as [pn].
    case_eq (p_occurs_in_phi (mconj phi1 phi2) (pv pn));
    intros Hpocc2.
      specialize (Hpocct Hpocc2 (length (pv_in phi1) + i) H0).
      simpl pv_in in Hpocct.
      rewrite at_pv_app_r in Hpocct.
        remember (at_pv (pv_in phi2) i) as t;
        destruct t as [qm].
        specialize (Hpocct Heq).
        pose proof (is_neg_mconj_r phi1 phi2 (length (pv_in phi1) + i)
             Hpocct).
        assert (Nat.leb (length (pv_in phi1) + 1) (length (pv_in phi1) + i)
                    = true) as H2.
          rewrite <- leb_plus_pre with (m := (length (pv_in phi1))).
          unfold Nat.leb.
          destruct i.
            apply occ_in_phi_0 in Hocc.
            simpl in Hocc; discriminate.

            reflexivity.

        case_eq (occ_in_phi phi1 (length (pv_in phi1) + i)); intros Hocc2.
          destruct (occ_in_phi_leb2 _ _ Hocc2) as [Ha Hb].
          apply leb_minus with (i := length (pv_in phi1)) in Hb.
          rewrite arith_plus_3 in Hb.
          rewrite arith_minus_refl in Hb.
          rewrite leb_beq_zero in Hb.
          rewrite (beq_nat_true _ _ Hb) in *.
          apply occ_in_phi_0 in Hocc; discriminate.

        specialize (H1 Hocc2).
        rewrite arith_plus_3 in H1.
        assumption.

        apply occ_in_phi_leb2 in Hocc.
        apply Hocc.

      specialize (Hpoccf Hpocc2); contradiction.

    rewrite H in *; discriminate.
Qed.

Lemma p_is_neg_mdisj2l: forall (phi1 phi2 : Modal) (p : propvar),
  p_is_neg (mdisj phi1 phi2) p -> 
    p_occurs_in_phi phi1 p = true ->
      p_is_neg phi1 p.
Proof.
  intros phi1 phi2 p Hneg Hpocc.
  unfold p_is_neg in *.
  destruct Hneg as [l r].
  assert (p_occurs_in_phi (mdisj phi1 phi2) p = true) as Hpocc3.
    apply p_occurs_in_phi_mdisj.
    left; exact Hpocc.
  apply conj; intros Hpocc2.
    intros i Hocc Heq.
    assert (Nat.leb i (length (pv_in phi1)) = true) as Hleb.
      apply occ_in_phi_leb.
      exact Hocc.
    assert (beq_nat i 0 = false) as Hbeq.
      apply occ_in_phi_0 with (phi:=phi1).
      exact Hocc.
    pose proof (occ_in_phi_mdisj_l phi1 phi2 i Hocc) as Hocc2.
    specialize (l Hpocc3 i Hocc2).
    simpl pv_in in l.    
    rewrite at_pv_app_l in l.
      specialize (l Heq).
      destruct (is_neg_mdisj phi1 phi2 i l) as [Hl Hr].
      apply Hl.
      exact Hocc.

      apply PeanoNat.Nat.leb_le.
      exact Hleb.

    rewrite Hpocc2 in *; discriminate.
Qed.

Lemma p_is_neg_mdisj2r: forall (phi1 phi2 : Modal) (p : propvar),
  p_is_neg (mdisj phi1 phi2) p -> 
    p_occurs_in_phi phi2 p = true ->
      p_is_neg phi2 p.
Proof.
  intros phi1 phi2 p Hneg Hpocc.
  unfold p_is_neg.
  destruct Hneg as [Hpocct Hpoccf].
  apply conj; intros H.
    intros i Hocc Heq.
    pose proof (occ_in_phi_mdisj_r phi1 phi2 i Hocc) as H0.
    destruct p as [pn].
    case_eq (p_occurs_in_phi (mdisj phi1 phi2) (pv pn));
    intros Hpocc2.
      specialize (Hpocct Hpocc2 (length (pv_in phi1) + i) H0).
      simpl pv_in in Hpocct.
      rewrite at_pv_app_r in Hpocct.
        remember (at_pv (pv_in phi2) i) as t;
        destruct t as [qm].
        specialize (Hpocct Heq).
        pose proof (is_neg_mdisj_r phi1 phi2 (length (pv_in phi1) + i)
             Hpocct).
        assert (Nat.leb (length (pv_in phi1) + 1) (length (pv_in phi1) + i)
                    = true) as H2.
          rewrite <- leb_plus_pre with (m := (length (pv_in phi1))).
          unfold Nat.leb.
          destruct i.
            apply occ_in_phi_0 in Hocc.
            simpl in Hocc; discriminate.

            reflexivity.

        case_eq (occ_in_phi phi1 (length (pv_in phi1) + i)); intros Hocc2.
          destruct (occ_in_phi_leb2 _ _ Hocc2) as [Ha Hb].
          apply leb_minus with (i := length (pv_in phi1)) in Hb.
          rewrite arith_plus_3 in Hb.
          rewrite arith_minus_refl in Hb.
          rewrite leb_beq_zero in Hb.
          rewrite (beq_nat_true _ _ Hb) in *.
          apply occ_in_phi_0 in Hocc; discriminate.

        specialize (H1 Hocc2).
        rewrite arith_plus_3 in H1.
        assumption.

        apply occ_in_phi_leb2 in Hocc.
        apply Hocc.

      specialize (Hpoccf Hpocc2); contradiction.

    rewrite H in *; discriminate.
Qed.

Lemma p_is_neg_mimpl2l: forall (phi1 phi2 : Modal) (p : propvar),
  p_is_neg (mimpl phi1 phi2) p -> 
    p_occurs_in_phi phi1 p = true ->
      p_is_pos phi1 p.
Proof.
  intros phi1 phi2 p Hneg Hpocc.
  unfold p_is_neg in *.
  destruct Hneg as [l r].
  assert (p_occurs_in_phi (mimpl phi1 phi2) p = true) as Hpocc3.
    apply p_occurs_in_phi_mimpl.
    left; exact Hpocc.
  apply conj; intros Hpocc2.
    intros i Hocc Heq.
    assert (Nat.leb i (length (pv_in phi1)) = true) as Hleb.
      apply occ_in_phi_leb.
      exact Hocc.
    assert (beq_nat i 0 = false) as Hbeq.
      apply occ_in_phi_0 with (phi:=phi1).
      exact Hocc.
    pose proof (occ_in_phi_mimpl_l phi1 phi2 i Hocc) as Hocc2.
    specialize (l Hpocc3 i Hocc2).
    simpl pv_in in l.    
    rewrite at_pv_app_l in l.
      specialize (l Heq).
      destruct (is_neg_mimpl phi1 phi2 i l) as [Hl Hr].
      apply is_neg_pos_f.
        assumption.

        apply Hl; assumption.
      apply PeanoNat.Nat.leb_le.
      assumption.
    rewrite Hpocc2 in *; discriminate.
Qed.

Lemma p_is_neg_mimpl2r: forall (phi1 phi2 : Modal) (p : propvar),
  p_is_neg (mimpl phi1 phi2) p -> 
    p_occurs_in_phi phi2 p = true ->
      p_is_neg phi2 p.
Proof.
  intros phi1 phi2 p Hneg Hpocc.
  unfold p_is_neg.
  destruct Hneg as [Hpocct Hpoccf].
  apply conj; intros H.
    intros i Hocc Heq.
    pose proof (occ_in_phi_mimpl_r phi1 phi2 i Hocc) as H0.
    destruct p as [pn].
    case_eq (p_occurs_in_phi (mimpl phi1 phi2) (pv pn));
    intros Hpocc2.
      specialize (Hpocct Hpocc2 (length (pv_in phi1) + i) H0).
      simpl pv_in in Hpocct.
      rewrite at_pv_app_r in Hpocct.
        remember (at_pv (pv_in phi2) i) as t;
        destruct t as [qm].
        specialize (Hpocct Heq).
        pose proof (is_neg_mimpl_r phi1 phi2 (length (pv_in phi1) + i)
             Hpocct).
        assert (Nat.leb (length (pv_in phi1) + 1) (length (pv_in phi1) + i)
                    = true) as H2.
          rewrite <- leb_plus_pre with (m := (length (pv_in phi1))).
          unfold Nat.leb.
          destruct i.
            apply occ_in_phi_0 in Hocc.
            simpl in Hocc; discriminate.

            reflexivity.

        case_eq (occ_in_phi phi1 (length (pv_in phi1) + i)); intros Hocc2.
          destruct (occ_in_phi_leb2 _ _ Hocc2) as [Ha Hb].
          apply leb_minus with (i := length (pv_in phi1)) in Hb.
          rewrite arith_plus_3 in Hb.
          rewrite arith_minus_refl in Hb.
          rewrite leb_beq_zero in Hb.
          rewrite (beq_nat_true _ _ Hb) in *.
          apply occ_in_phi_0 in Hocc; discriminate.

        specialize (H1 Hocc2).
        rewrite arith_plus_3 in H1.
        assumption.

        apply occ_in_phi_leb2 in Hocc.
        apply Hocc.

      specialize (Hpoccf Hpocc2); contradiction.

    rewrite H in *; discriminate.
Qed.

Lemma p_is_neg_box : forall (phi : Modal) (p : propvar),
  p_is_neg (box phi) p -> p_is_neg phi p.
Proof.
  intros phi p Hneg.
  unfold p_is_neg in *.
  destruct Hneg as [l r].
  apply conj; intros Hpocc.
    intros i Hocc Heq.
    apply is_neg_box.
    apply l.
      apply p_occurs_in_phi_box; exact Hpocc.

      apply occ_in_phi_box; exact Hocc.

      simpl; exact Heq.

    apply r. 
    destruct (p_occurs_in_phi_box phi p) as [forw rev].
    apply (contrapos_bool_tt _ _ forw).
    exact Hpocc.
Qed.

Lemma p_is_neg_diam : forall (phi : Modal) (p : propvar),
  p_is_neg (diam phi) p -> p_is_neg phi p.
Proof.
  intros phi p Hneg.
  unfold p_is_neg in *.
  destruct Hneg as [l r].
  apply conj; intros Hpocc.
    intros i Hocc Heq.
    apply is_neg_diam.
    apply l.
      apply p_occurs_in_phi_diam; exact Hpocc.

      apply occ_in_phi_diam; exact Hocc.

      simpl; exact Heq.

    apply r. 
    destruct (p_occurs_in_phi_diam phi p) as [forw rev].
    apply (contrapos_bool_tt _ _ forw).
    exact Hpocc.
Qed.


(* ---------------------------------------------------------------------------- *)
(* p_is_pos and p_is_neg relationship *)

Lemma p_is_pos_neg : forall (phi : Modal) (p : propvar),
  p_is_pos (mneg phi) p -> p_is_neg phi p.
Proof.
  intros phi p Hpos.
  unfold p_is_neg.
  unfold p_is_pos in *.
  destruct Hpos as [l r].
  apply conj.
    intros Hpocc i Hocc Heq.
    apply is_pos_neg_f; try assumption.

    apply is_pos_mneg.
    apply l; try assumption.
      apply occ_in_phi_mneg; assumption.

      assumption.
Qed.

Lemma p_is_neg_pos : forall (phi : Modal) (p : propvar),
  p_is_neg (mneg phi) p -> p_is_pos phi p.
Proof.
  intros phi p Hneg.
  unfold p_is_pos.
  unfold p_is_neg in *.
  destruct Hneg as [l r].
  apply conj.
    intros Hpocc i Hocc Heq.
    apply contrapos_bool_ft with (b := is_neg phi i).
      intro H.
      exact (is_pos_neg_f phi i Hocc H).

      apply is_neg_mneg.
      apply l;
        try apply p_occurs_in_phi_mneg;
        try exact Hpocc.

        apply occ_in_phi_mneg.
        exact Hocc.

        simpl.
        exact Heq.

    intros; apply r.
      apply contrapos_bool_tt with (b := p_occurs_in_phi phi p).
        apply p_occurs_in_phi_mneg.

        assumption.
Qed.
