Require Export low_mods.
Require Import Rep_Pred_FOv replace_FOv_max_conj same_struc.

Fixpoint replace_FOv_A_pre alpha gamma lv n: SecOrder :=
  match n with
  | 0 => alpha
  | S m =>
  match lv with
  | nil => alpha
  | cons x lv' => replace_FOv_A_pre (strip_exFO (replace_FOv_max_conj (list_closed_exFO alpha 
           lv') gamma x) (length lv'))  gamma 
           (strip_exFO_list (replace_FOv_max_conj (list_closed_exFO alpha lv') gamma x)
           (length lv')) m 
  end
  end.

Definition replace_FOv_A alpha gamma lv : SecOrder :=
  replace_FOv_A_pre alpha gamma lv (length lv).

Fixpoint replace_FOv_A_list_pre alpha gamma lv n: list FOvariable :=
  match n with
  | 0 => nil
  | S m =>
  match lv with
  | nil => nil
  | cons x lv' => cons (replace_FOv_max_conj_var (list_closed_exFO alpha lv') gamma x) 
       (replace_FOv_A_list_pre (strip_exFO (replace_FOv_max_conj (list_closed_exFO alpha lv') gamma x)
       (length lv')) gamma (strip_exFO_list (replace_FOv_max_conj (list_closed_exFO alpha lv')
        gamma x) (length lv')) m)
  end
  end.

Definition replace_FOv_A_list alpha gamma lv :=
  replace_FOv_A_list_pre alpha gamma lv (length lv).


Lemma same_struc_replace_FOv_A_pre : forall n lv alpha beta,
  same_struc alpha (replace_FOv_A_pre alpha beta lv n) = true.
Proof.
  induction n; intros lv alpha beta.
    simpl. apply same_struc_refl.

    induction lv.
      simpl. apply same_struc_refl.

      simpl.
      specialize (IHn (strip_exFO_list (replace_FOv_max_conj (list_closed_exFO alpha lv) beta a)
        (length lv)) (strip_exFO (replace_FOv_max_conj (list_closed_exFO alpha lv) beta a)
        (length lv)) beta)  .
      assert (same_struc alpha (strip_exFO (replace_FOv_max_conj (list_closed_exFO alpha lv) beta a)
           (length lv)) =  true) as H.
        pose proof (same_struc_replace_FOv_max_conj_list_closed_exFO
          lv alpha beta a) as H2.
        apply same_struc_strip_exFO with (n := length lv) in H2.
        pose proof (same_struc_strip_exFO_list_closed lv (replace_FOv_max_conj alpha beta a)) as H3.
        pose proof (same_struc_trans _ _ _ (same_struc_replace_FOv_max_conj _ _ _)
               H3 ) as H4.
        apply same_struc_comm in H2.
        apply (same_struc_trans _ _ _ H4 H2).

      apply (same_struc_trans _ _ _ H IHn).
Qed.

Lemma same_struc_replace_FOv_A : forall alpha beta lv,
  same_struc (replace_FOv_A alpha beta lv) alpha = true.
Proof.
  intros alpha beta lv. unfold replace_FOv_A.
  apply same_struc_comm.
  apply same_struc_replace_FOv_A_pre.
Qed.


