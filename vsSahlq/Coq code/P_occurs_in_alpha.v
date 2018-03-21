Require Export SecOrder.
Require Import Coq.Arith.EqNat.

(* Whether p occurs in phi or not. *)

Fixpoint P_occurs_in_l (l : list predicate) (P : predicate) : bool :=
  match l with
  | nil => false
  | cons Q l' => if match P, Q with
                    | Pred pn, Pred qm => EqNat.beq_nat pn qm
                    end
                    then true
                    else P_occurs_in_l l' P
  end.

Lemma P_occurs_in_l_app_comp : forall (l1 l2 : list predicate) (P : predicate),
  (P_occurs_in_l (app l1 l2) P = true ->
    ((P_occurs_in_l l1 P = true) + (P_occurs_in_l l2 P = true))) *
  (((P_occurs_in_l l1 P = true) + (P_occurs_in_l l2 P = true)) ->
  P_occurs_in_l (app l1 l2) P = true).
Proof.
  intros.
  induction l1; simpl in *.
    induction l2; simpl in *.
      split; intros H; try left; try destruct H; 
        try discriminate; try reflexivity.

      destruct P as [Pn]; destruct a as [Qm].
      case_eq (EqNat.beq_nat Pn Qm) ; intros H_eq.
        split; intros H.
          right; reflexivity.

          reflexivity.

        split; intros H.
          apply IHl2.
          exact H.

          apply IHl2; exact H.

      destruct P as [Pn]; destruct a as [Qm].
      case_eq (EqNat.beq_nat Pn Qm) ; intros H_eq.
        split; intros H.
          left; reflexivity.

          reflexivity.

        split; intros H.
          apply IHl1.
          exact H.

          apply IHl1; exact H.
Defined.

Lemma P_occurs_in_l_app : forall (l1 l2 : list predicate) (P : predicate),
  (P_occurs_in_l (app l1 l2) P = true <->
    ((P_occurs_in_l l1 P = true) \/ (P_occurs_in_l l2 P = true))).
Proof.
  intros.
  induction l1; simpl in *.
    induction l2; simpl in *.
      split; intros H; try left; try destruct H; 
        try discriminate; try reflexivity.

      destruct P as [Pn]; destruct a as [Qm].
      case_eq (EqNat.beq_nat Pn Qm) ; intros H_eq.
        split; intros H.
          right; reflexivity.

          reflexivity.

        split; intros H.
          apply IHl2.
          exact H.

          apply IHl2; exact H.

      destruct P as [Pn]; destruct a as [Qm].
      case_eq (EqNat.beq_nat Pn Qm) ; intros H_eq.
        split; intros H.
          left; reflexivity.

          reflexivity.

        split; intros H.
          apply IHl1.
          exact H.

          apply IHl1; exact H.
Qed.

Lemma P_occurs_in_l_app_f : forall (l1 l2 : list predicate) (P : predicate),
  P_occurs_in_l (app l1 l2) P = false <->
    P_occurs_in_l l1 P = false /\ P_occurs_in_l l2 P = false.
Proof.
  intros.
  induction l1; simpl in *.
    induction l2; simpl in *.
      split; intros H; try apply conj; reflexivity.

      destruct P as [Pn]; destruct a as [Qm].
      case_eq (EqNat.beq_nat Pn Qm) ; intros H_eq.
        split; intros H; try discriminate.
        apply H.

        split; intros H; try apply conj; try apply H.
          reflexivity.

      destruct P as [Pn]; destruct a as [Qm].
      case_eq (EqNat.beq_nat Pn Qm) ; intros H_eq.
        split; intros H; try discriminate.
        apply H.

        split; intros H.
          apply IHl1.
          exact H.

          apply IHl1; exact H.
Qed.


Lemma P_occ_in_l_cons : forall l P Q,
  ~ P = Q ->
  P_occurs_in_l (cons P l) Q = 
  P_occurs_in_l l Q.
Proof.
  intros l P Q Hneq.
  simpl.
  destruct Q as [Qm]; destruct P as [Pn].
  case_eq (beq_nat Qm Pn); intros Hbeq.
    rewrite (beq_nat_true _ _ Hbeq) in Hneq.
    contradiction (Hneq eq_refl).

    reflexivity.
Qed.

Lemma P_occurs_in_l_ex : forall (l : list predicate) (P : predicate),
  P_occurs_in_l l P = true -> 
    exists (l1 l2 : list predicate), app l1 (cons P l2) = l.
Proof.
  intros.
  induction l.
    simpl in *; discriminate.

    destruct P as [Pn]; destruct a as [Qm].
    case_eq (beq_nat Pn Qm); intros H_beq. 
      exists nil; exists l; simpl;
      rewrite (beq_nat_true Pn Qm H_beq); reflexivity.

      case_eq (P_occurs_in_l l (Pred Pn)); intros H_occ;
      rewrite H_occ in *.
        assert (true = true) as Ht by reflexivity.
        specialize (IHl Ht).
        destruct IHl as [l1 [l2 IHl]].
        exists (cons (Pred Qm) l1).
        exists l2.
        rewrite <- IHl.
        simpl; reflexivity.

        simpl in H; rewrite H_beq in *.
        rewrite H in H_occ; discriminate.
Qed.

Lemma P_occurs_in_l_true : forall (l1 l2 : list predicate) (P : predicate),
  P_occurs_in_l (l1 ++ P :: l2) P = true.
Proof.
  intros.
  destruct P as [Pn].
  induction l1.
    simpl.
    rewrite <- (beq_nat_refl Pn); reflexivity.

    simpl.
    destruct a as [Qm].
    rewrite IHl1.
    case (beq_nat Pn Qm); reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)

Definition P_occurs_in_alpha (alpha : SecOrder) (P : predicate) : bool :=
  P_occurs_in_l (preds_in alpha) P.

Lemma P_occurs_in_alpha_allFO : forall (alpha : SecOrder) (x : FOvariable)
                                        (P : predicate),
  P_occurs_in_alpha alpha P = P_occurs_in_alpha (allFO x alpha) P.
Proof.
  intros alpha x P.
  unfold P_occurs_in_alpha.
  reflexivity.
Qed.

(*
Lemma P_occurs_in_alpha_allFO : forall (alpha : SecOrder) (x : FOvariable)
                                        (P : predicate),
  P_occurs_in_alpha alpha P = true <->
    P_occurs_in_alpha (allFO x alpha) P = true.
Proof.
  split; intros H; unfold P_occurs_in_alpha in *; simpl in *; exact H.
Qed.
*)

Lemma P_occurs_in_alpha_exFO : forall (alpha : SecOrder) (x : FOvariable)
                                        (P : predicate),
  P_occurs_in_alpha alpha P = P_occurs_in_alpha (exFO x alpha) P.
Proof.
  intros alpha x P; destruct x;
  unfold P_occurs_in_alpha in *; reflexivity.
Qed.

Lemma P_occurs_in_alpha_negSO : forall (alpha : SecOrder)
                                        (P : predicate),
  P_occurs_in_alpha alpha P = P_occurs_in_alpha (negSO alpha) P.
Proof.
  intros; unfold P_occurs_in_alpha; reflexivity.
Qed.

Lemma P_occurs_in_alpha_conjSO_comp : forall (alpha1 alpha2 : SecOrder)
                                        (P : predicate),
  (P_occurs_in_alpha (conjSO alpha1 alpha2) P = true ->
    (P_occurs_in_alpha alpha1 P = true) + (P_occurs_in_alpha alpha2 P = true)) *
  ((P_occurs_in_alpha alpha1 P = true) + (P_occurs_in_alpha alpha2 P = true) ->
    P_occurs_in_alpha (conjSO alpha1 alpha2) P = true ).
Proof.
  intros until 0. apply pair; intros H;
  unfold P_occurs_in_alpha in *; simpl in *;
  apply P_occurs_in_l_app_comp; assumption.
Defined.

Lemma P_occurs_in_alpha_conjSO : forall (alpha1 alpha2 : SecOrder)
                                        (P : predicate),
  (P_occurs_in_alpha (conjSO alpha1 alpha2) P = true <->
    (P_occurs_in_alpha alpha1 P = true) \/ (P_occurs_in_alpha alpha2 P = true)).
Proof.
  intros until 0. split; intros H;
  unfold P_occurs_in_alpha in *; simpl in *;
  apply P_occurs_in_l_app; assumption.
Qed.

Lemma P_occurs_in_alpha_disjSO_comp : forall (alpha1 alpha2 : SecOrder)
                                        (P : predicate),
  (P_occurs_in_alpha (disjSO alpha1 alpha2) P = true ->
    (P_occurs_in_alpha alpha1 P = true) + (P_occurs_in_alpha alpha2 P = true)) *
  ((P_occurs_in_alpha alpha1 P = true) + (P_occurs_in_alpha alpha2 P = true) ->
    P_occurs_in_alpha (conjSO alpha1 alpha2) P = true ).
Proof.
  intros until 0. apply pair; intros H;
  unfold P_occurs_in_alpha in *; simpl in *;
  apply P_occurs_in_l_app_comp; assumption.
Defined.

Lemma P_occurs_in_alpha_disjSO : forall (alpha1 alpha2 : SecOrder)
                                        (P : predicate),
  (P_occurs_in_alpha (disjSO alpha1 alpha2) P = true <->
    (P_occurs_in_alpha alpha1 P = true) \/ (P_occurs_in_alpha alpha2 P = true)).
Proof.
  intros until 0. split; intros H;
  unfold P_occurs_in_alpha in *; simpl in *;
  apply P_occurs_in_l_app; assumption.
Qed.

Lemma P_occurs_in_alpha_implSO_comp : forall (alpha1 alpha2 : SecOrder)
                                        (P : predicate),
  (P_occurs_in_alpha (implSO alpha1 alpha2) P = true ->
    (P_occurs_in_alpha alpha1 P = true) + (P_occurs_in_alpha alpha2 P = true)) *
  ((P_occurs_in_alpha alpha1 P = true) + (P_occurs_in_alpha alpha2 P = true) ->
    P_occurs_in_alpha (conjSO alpha1 alpha2) P = true ).
Proof.
  intros until 0. apply pair; intros H;
  unfold P_occurs_in_alpha in *; simpl in *;
  apply P_occurs_in_l_app_comp; assumption.
Defined.

Lemma P_occurs_in_alpha_implSO : forall (alpha1 alpha2 : SecOrder)
                                        (P : predicate),
  (P_occurs_in_alpha (implSO alpha1 alpha2) P = true <->
    (P_occurs_in_alpha alpha1 P = true) \/ (P_occurs_in_alpha alpha2 P = true)).
Proof.
  intros until 0. split; intros H;
  unfold P_occurs_in_alpha in *; simpl in *;
  apply P_occurs_in_l_app; assumption.
Qed.

Lemma P_occurs_in_alpha_allSO : forall (alpha : SecOrder)
                                        (Q P: predicate),
  P_occurs_in_alpha (allSO Q alpha) P = true <->
    (match P, Q with
     | Pred Pn, Pred Qm => 
     (beq_nat Pn Qm) = true
     end)   \/ P_occurs_in_alpha alpha P = true.
Proof.
  split; intros H; unfold P_occurs_in_alpha in *;
  destruct P as [Pn]; destruct Q as [Qm]; simpl in *;
  case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *.
    left; reflexivity.

    right; assumption.

    reflexivity.

    destruct H; [discriminate | assumption].
Qed.


Lemma P_occurs_in_alpha_exSO : forall (alpha : SecOrder)
                                        (Q P: predicate),
  P_occurs_in_alpha (exSO Q alpha) P = true <->
    (match P, Q with
     | Pred Pn, Pred Qm => 
     (beq_nat Pn Qm) = true
     end)   \/ P_occurs_in_alpha alpha P = true.
Proof.
  split; intros H; unfold P_occurs_in_alpha in *;
  destruct P as [Pn]; destruct Q as [Qm]; simpl in *;
  case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *.
    left; reflexivity.

    right; assumption.

    reflexivity.

    destruct H; [discriminate | assumption].
Qed.


Lemma  P_occurs_in_alpha_allSO3 : forall alpha P Q,
  ~ Q = P ->
  P_occurs_in_alpha alpha P = P_occurs_in_alpha (allSO Q alpha) P.
Proof.
  intros alpha P Q Hneq.
  unfold P_occurs_in_alpha.
  simpl preds_in.
  rewrite P_occ_in_l_cons.  
    reflexivity.
    assumption.
Qed.

Lemma  P_occurs_in_alpha_exSO2 : forall alpha P Q,
  ~ Q = P ->
  P_occurs_in_alpha alpha P = P_occurs_in_alpha (exSO Q alpha) P.
Proof.
  intros alpha P Q Hneq.
  unfold P_occurs_in_alpha.
  simpl preds_in.
  rewrite P_occ_in_l_cons.  
    reflexivity.
    assumption.
Qed.

Lemma P_occurs_in_alpha_conjSO_f : forall (alpha1 alpha2 : SecOrder)
                                        (P : predicate),
  P_occurs_in_alpha (conjSO alpha1 alpha2) P = false <->
    P_occurs_in_alpha alpha1 P = false /\ P_occurs_in_alpha alpha2 P = false.
Proof.
  split; intros H;
    unfold P_occurs_in_alpha in *;
    simpl in *;
    rewrite P_occurs_in_l_app_f in *;
    apply conj; apply H.
Qed.


(* ---------------------------------------------------------------- *)

Fixpoint l_occurs_in_alpha (alpha : SecOrder) (l : list predicate): bool :=
  match l with
  | nil => true
  | cons P l' => if P_occurs_in_alpha alpha P then l_occurs_in_alpha alpha l'
                                              else false
  end.


(*

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
*)
