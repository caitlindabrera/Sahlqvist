Require Export low_mods.
Require Import Rep_Pred_FOv same_struc.

Definition replace_FOv_max_conj alpha gamma x : SecOrder :=
  replace_FOv alpha x (Var (S (max_FOv (conjSO gamma (exFO x alpha))))).

Definition replace_FOv_max_conj_var alpha gamma x : FOvariable :=
  Var (S (max_FOv (conjSO gamma (exFO x alpha)))).

Lemma same_struc_replace_FOv_max_conj : forall alpha gamma x,
  same_struc alpha (replace_FOv_max_conj alpha gamma x) = true.
Proof.  intros. apply same_struc_replace_FOv. Qed.


Lemma same_struc_replace_FOv_max_conj_list_closed_exFO : forall lv alpha beta x,
  same_struc (replace_FOv_max_conj (list_closed_exFO alpha lv) beta x)
             (list_closed_exFO (replace_FOv_max_conj alpha beta x) lv) = true.
Proof.
  induction lv; intros alpha beta x.
    simpl in *.
    apply same_struc_refl.

    simpl.
    assert (same_struc (replace_FOv_max_conj (exFO a (list_closed_exFO alpha lv)) beta x)
              (exFO x ((replace_FOv_max_conj (list_closed_exFO alpha lv) beta x)))=true) as H3.
      pose proof (same_struc_replace_FOv_max_conj (exFO a (list_closed_exFO alpha lv))
          beta x) as H3.
      apply same_struc_trans with (beta := exFO a (list_closed_exFO alpha lv)).
        apply same_struc_comm. assumption.
        apply same_struc_replace_FOv_max_conj.

    apply same_struc_trans with 
      (beta := (exFO x (replace_FOv_max_conj (list_closed_exFO alpha lv) beta x))).  
      assumption.
    simpl.
    apply IHlv.
Qed.