Require Import SecOrder.
Require Import P_occurs_in_alpha.
Require Import ST_setup.
Require Import Correctness_ST.
Require Import Arith.EqNat my_bool.
Require Import List_machinery_impl My_List_Map.
Require Import Unary_Predless nList_egs Rep_Pred_FOv Indicies Identify.
Require Import pos_SO2 neg_SO2 Num_Occ Bool my_bool Is_Pos_Rep_Pred P_occ_rep_pred.
Require Import Uniform_Defns Monotonicity_SO Pre_Sahlqvist_Uniform_Pos P_occ_rep_pred.
Require Import Unary_Predless_l Num_Occ_l2 Occ_In_Alpha My_Prop Sahlqvist_Uniform_Pos.
Require Import vsSahlq_preprocessing1 vsSahlq_preprocessing2 vsSahlq_preprocessing3.
Require Import vsSahlq_instant3 vsSahlq_instant9 vsSahlq_instant_pre_to_be_sorted.
Require Import vsSahlq_instant10 vsSahlq_instant13 vsSahlq_instant15 vsSahlq_instant16 vsSahlq_instant17.
Require Import vsSahlq_instant19.
Require Import p_occurs_in occ_in_phi my_arith__my_leb_nat.
Require Import sSahlq_preprocessing1_added sSahlq3_5_plus_3.

Lemma rename_FOv_A_rel_batm : forall lv rel atm beta,
  REL rel = true ->
  BAT atm = true ->
  is_in_FOvar (Var 0) lv = false ->
  existsT2 rel' atm',
    rename_FOv_A (conjSO rel atm) beta lv =  conjSO rel' atm' /\
    REL rel' = true /\
    BAT atm' = true.
Proof.
  induction lv; intros rel atm beta HREL HAT Hin0.
    unfold rename_FOv_A. simpl.
    exists rel. exists atm.
    apply conj. reflexivity.
    apply conj; assumption.

    destruct (IHlv _ _ beta HREL HAT) as [rel' [atm' [Heq [HREL' HAT']]]].
    unfold rename_FOv_A in *.
    simpl. apply is_in_FOvar_cons_f in Hin0. apply Hin0.
    apply is_in_FOvar_cons_f in Hin0. destruct Hin0 as [Hin01 Hin02].
    apply not_eq_sym in Hin02.
    pose proof (same_struc_BAT2_rename_FOv_max_conj (list_closed_exFO (conjSO rel atm) lv) beta a Hin02) as H.
    pose proof (same_struc_BAT2_trans _ _ _ H (same_struc_BAT2_rename_FOv_max_conj_list_closed_exFO
              _ _ _ _ Hin02)) as H1.
    pose proof (same_struc_BAT2_rename_FOv_max_conj (list_closed_exFO (conjSO rel atm) lv)
      beta a Hin02) as H2.
    apply same_struc_BAT2_comm in H1.
    pose proof (same_struc_BAT2_trans _ _ _ H1 H2) as H3.
    apply same_struc_BAT2_strip_exFO with (n := (length lv)) in H3.
    pose proof (same_struc_BAT2_trans _ _ _ (same_struc_BAT2_strip_exFO_list_closed
      _ _) H3) as H4.
    pose proof (same_struc_BAT2_trans _ _ _ (same_struc_BAT2_rename_FOv_max_conj _ _ _ Hin02)
      H4) as H5.
assert (is_in_FOvar (Var 0)
   (strip_exFO_list (rename_FOv_max_conj (list_closed_exFO (conjSO rel atm) lv) beta a) (length lv)) = false) as Hass.
unfold rename_FOv_max_conj. rewrite strip_exFO_list_rename_FOv.
rewrite is_in_FOvar_rename_FOv_list2; try assumption. apply not_eq_sym. assumption.
discriminate.

    pose proof (same_struc_BAT2_trans _ _ _ H5 (same_struc_BAT2_rename_FOv_A_pre
         (length lv)
(strip_exFO_list
       (rename_FOv_max_conj (list_closed_exFO (conjSO rel atm) lv) beta a)
       (length lv)) _ beta Hass)) as H6.
    pose proof H6 as H6'.
    apply same_struc_BAT2_comm in H6.
    destruct (same_struc_conjSO_ex_BAT2 _ _ _ H6) as [rel'' [atm'' [H' Hiff]]].
    rewrite H' in H6.
    apply same_struc__BAT2 in H6.
    pose proof (same_struc_conjSO_l _ _ _ _ H6) as H7.
    apply same_struc_conjSO_r in H6.
    apply same_struc_comm in H6.
    apply same_struc_comm in H7.
    exists rel''. exists atm''.
    apply conj.
      assumption.
      apply conj.
        apply same_struc_REL with (alpha := rel); assumption.
        rewrite H' in H6'. apply same_struc_BAT2_conjSO_BAT_r in H6'; try assumption.
        apply same_struc_REL with (alpha := rel); assumption.
Defined.
