Require Import Modal.
Require Import Arith.EqNat.

(* Whether p occurs in phi or not. *)

Fixpoint p_occurs_in_l (l : list propvar) (p : propvar) : bool :=
  match l with
  | nil => false
  | cons q l' => if match p, q with
                    | pv pn, pv qm => EqNat.beq_nat pn qm
                    end
                    then true
                    else p_occurs_in_l l' p
  end.

Lemma p_occurs_in_l_app : forall (l1 l2 : list propvar) (p : propvar),
  p_occurs_in_l (app l1 l2) p = true <->
    p_occurs_in_l l1 p = true \/ p_occurs_in_l l2 p = true.
Proof.
  intros.
  induction l1; simpl in *.
    induction l2; simpl in *.
      split; intros H; try left; try destruct H; 
        try discriminate; try reflexivity.

      destruct p as [pn]; destruct a as [qm].
      case_eq (EqNat.beq_nat pn qm) ; intros H_eq.
        split; intros H.
          right; reflexivity.

          reflexivity.

        split; intros H.
          apply IHl2.
          exact H.

          apply IHl2; exact H.

      destruct p as [pn]; destruct a as [qm].
      case_eq (EqNat.beq_nat pn qm) ; intros H_eq.
        split; intros H.
          left; reflexivity.

          reflexivity.

        split; intros H.
          apply IHl1.
          exact H.

          apply IHl1; exact H.
Qed.

Lemma p_occurs_in_l_ex : forall (l : list propvar) (p : propvar),
  p_occurs_in_l l p = true -> 
    exists (l1 l2 : list propvar), app l1 (cons p l2) = l.
Proof.
  intros.
  induction l.
    simpl in *; discriminate.

    destruct p as [pn]; destruct a as [qm].
    case_eq (beq_nat pn qm); intros H_beq. 
      exists nil; exists l; simpl;
      rewrite (beq_nat_true pn qm H_beq); reflexivity.

      case_eq (p_occurs_in_l l (pv pn)); intros H_occ;
      rewrite H_occ in *.
        assert (true = true) as Ht by reflexivity.
        specialize (IHl Ht).
        destruct IHl as [l1 [l2 IHl]].
        exists (cons (pv qm) l1).
        exists l2.
        rewrite <- IHl.
        simpl; reflexivity.

        simpl in H; rewrite H_beq in *.
        rewrite H in H_occ; discriminate.
Qed.

Lemma p_occurs_in_l_true : forall (l1 l2 : list propvar) (p : propvar),
  p_occurs_in_l (l1 ++ p :: l2) p = true.
Proof.
  intros.
  destruct p as [pn].
  induction l1.
    simpl.
    rewrite <- (beq_nat_refl pn); reflexivity.

    simpl.
    destruct a as [qm].
    rewrite IHl1.
    case (beq_nat pn qm); reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)

Definition p_occurs_in_phi (phi : Modal) (p : propvar) : bool :=
  p_occurs_in_l (pv_in phi) p.

Lemma p_occurs_in_phi_mneg : forall (phi : Modal) (p : propvar),
  p_occurs_in_phi (mneg phi) p = true <->
    p_occurs_in_phi phi p = true.
Proof.
  split; intros H; unfold p_occurs_in_phi in *;
    simpl in *; exact H.
Qed.

Lemma p_occurs_in_phi_mconj : forall (phi1 phi2 : Modal) (p : propvar),
  p_occurs_in_phi (mconj phi1 phi2) p = true <->
    p_occurs_in_phi phi1 p = true \/ p_occurs_in_phi phi2 p = true.
Proof.
  split; intros H; unfold p_occurs_in_phi in *; simpl in *;
  apply p_occurs_in_l_app; exact H.
Qed.

Lemma p_occurs_in_phi_mdisj : forall (phi1 phi2 : Modal) (p : propvar),
  p_occurs_in_phi (mdisj phi1 phi2) p = true <->
    p_occurs_in_phi phi1 p = true \/ p_occurs_in_phi phi2 p = true.
Proof.
  split; intros H; unfold p_occurs_in_phi in *; simpl in *;
  apply p_occurs_in_l_app; exact H.
Qed.

Lemma p_occurs_in_phi_mimpl : forall (phi1 phi2 : Modal) (p : propvar),
  p_occurs_in_phi (mimpl phi1 phi2) p = true <->
    p_occurs_in_phi phi1 p = true \/ p_occurs_in_phi phi2 p = true.
Proof.
  split; intros H; unfold p_occurs_in_phi in *; simpl in *;
  apply p_occurs_in_l_app; exact H.
Qed.

Lemma p_occurs_in_phi_box : forall (phi : Modal) (p : propvar),
  p_occurs_in_phi (box phi) p = true <->
    p_occurs_in_phi phi p = true.
Proof.
  split; intros H; unfold p_occurs_in_phi in *;
    simpl in *; exact H.
Qed.

Lemma p_occurs_in_phi_diam : forall (phi : Modal) (p : propvar),
  p_occurs_in_phi (diam phi) p = true <->
    p_occurs_in_phi phi p = true.
Proof.
  split; intros H; unfold p_occurs_in_phi in *;
    simpl in *; exact H.
Qed.

