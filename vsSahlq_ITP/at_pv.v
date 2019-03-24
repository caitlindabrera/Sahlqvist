Require Export Modal_syntax.
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

Lemma at_pv_app_l : forall (l1 l2 : list propvar) (i : nat),
  i <= (length l1) -> at_pv (app l1 l2) i = at_pv l1 i.
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

Lemma at_pv_app_r : forall (l1 l2 : list propvar) (i : nat),
  i <> 0 ->  at_pv (app l1 l2) (length l1 + i) = at_pv l2 i.
Proof.
  intros l1 l2 i H.
  induction l1.
    simpl; reflexivity.

    simpl.
    case_eq (length l1 + i).
      intros H_eq. rewrite H_eq in IHl1. destruct l1.
        simpl in H_eq. subst. contradiction.
        discriminate.
      intros n H2.  simpl in *. rewrite <- H2; exact IHl1.
Qed.