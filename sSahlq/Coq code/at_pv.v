Require Export Modal.
Require Import Coq.Arith.EqNat.

Fixpoint at_pv (l : list propvar) (i : nat) : propvar :=
  match l with
  | nil => (pv 1)
  | cons q l' => match i with
                 | S 0 => q
                 | 0 => (pv 1)
                 | _ => at_pv l' (i-1)
                 end
  end.

Lemma at_pv_app_cons : forall (l1 l2 : list propvar) (p : propvar),
  at_pv (app l1 (cons p l2)) (length l1 + 1) = p.
Proof.
  intros; induction l1.
  simpl; reflexivity.
  simpl in *.

  rewrite <- plus_n_Sm. simpl.
  rewrite plus_n_Sm. assumption.
Qed.
(*   pose proof (beq_nat_false ((length l1) +1) 0 (not_zero (length l1))).
  case_eq (length l1 + 1).
    intros; specialize (H H0); contradiction.

    intros n H2.
    rewrite H2 in IHl1.    
    simpl in *.
    exact IHl1.
Qed. *)

Lemma at_pv_app_l : forall (l1 l2 : list propvar) (i : nat),
  i <= (length l1) -> at_pv (app l1 l2) i = at_pv l1 i.

(*   leb_nat i (length l1) = true -> at_pv (app l1 l2) i = at_pv l1 i. *)
Proof.
  induction l1. 
    simpl in *.
    induction l2; simpl in *; try reflexivity.
      intros i H.
      destruct i; try reflexivity.
      contradiction (PeanoNat.Nat.nle_succ_0 _ H).

      simpl app.
      intros l2 i H.
      case_eq i.
        intros Hi.
        simpl.
        reflexivity.

      simpl.
      intros n Hi.
      rewrite IHl1.
        reflexivity.

        simpl in H. rewrite PeanoNat.Nat.sub_0_r.
        rewrite Hi in H. apply le_S_n. assumption.
Qed.
(* SearchAbout S le. simpl in H.
SearchAbout minus 0.
        pose proof (leb_nat_plus (i-1) (length l1) 1) as H0.
        rewrite arith_plus_minus_assoc in H0.
        simpl in H0; rewrite arith_minus_zero in *.
        rewrite <- one_suc in H0.
        rewrite H in H0.
        rewrite Hi in *.
        simpl in H0.
        rewrite arith_minus_zero in H0.
        exact H0.

        rewrite Hi .
        simpl; reflexivity.

        simpl; reflexivity.
Qed.
 *)
Lemma at_pv_app_r : forall (l1 l2 : list propvar) (i : nat),
  beq_nat i 0 = false ->
    at_pv (app l1 l2) (length l1 + i) = at_pv l2 i.
Proof.
  intros l1 l2 i H.
  induction l1.
    simpl; reflexivity.

    simpl.
    case_eq (length l1 + i).
      intros H_eq. rewrite H_eq in IHl1. destruct l1.
        simpl in H_eq.
        rewrite H_eq in H. rewrite <- beq_nat_refl in H.
        discriminate.

        discriminate.
(*       pose proof (arith_plus_zero (length l1) i H_eq) as H1.
      pose proof (arith_plus_zero i (length l1)) as H2.
      rewrite arith_plus_comm in H2.
      specialize (H2 H_eq).
      pose proof (length_nil l1 H1) as H3.
      rewrite H1 in *; rewrite H2 in *.
      rewrite H_eq in *.
      simpl in *.
      discriminate.
 *)
      intros n H2.
      simpl in *.
      rewrite <- H2; exact IHl1.
Qed.