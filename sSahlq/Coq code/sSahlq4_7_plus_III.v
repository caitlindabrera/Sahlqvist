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
Require Import p_occurs_in occ_in_phi my_arith__my_leb_nat List.  
Require Import sSahlq3_5_plus_3 sSahlq_preprocessing1_added sSahlq4_7_plus_I sSahlq4_7_plus_II.

Lemma consistent_lP_lcond_calc_lP_pre_pre : forall (lP : list predicate) (alpha : SecOrder) (P : predicate),
exists (n : nat),
  ind_cond (indicies_l2_pre lP P 0) (calc_lP alpha lP) =
constant_l (fun4_l2' (calc_lx1_P alpha P) (Var (new_FOv_pp_pre2 alpha)) 
(calc_llv_P alpha P)) n.
Proof.
  induction lP; intros alpha [Pn].
    simpl. exists 0. reflexivity.

    simpl in *. destruct a as [Qm].
    destruct (IHlP alpha (Pred Pn)) as [n IH].
    case_eq (beq_nat Pn Qm); intros Hbeq;
      simpl; rewrite ind_cond_ind_l2_pre_cons;
      rewrite IH; simpl.
      exists (S n).
      rewrite (beq_nat_true _ _ Hbeq). reflexivity.

      exists n. reflexivity.
Qed.

Lemma consistent_lP_lcond_calc_lP_pre : forall (lP : list predicate) (alpha : SecOrder) (P : predicate),
consistent_lP_lcond_P lP (calc_lP alpha lP) P.
Proof.
  unfold consistent_lP_lcond_P.
  unfold is_constant.
  unfold indicies_l2.
  intros. exists (fun4_l2' (calc_lx1_P alpha P) (Var (new_FOv_pp_pre2 alpha)) 
(calc_llv_P alpha P)). apply consistent_lP_lcond_calc_lP_pre_pre.
Qed.

Lemma consistent_lP_lcond_calc_lP : forall lP alpha,
consistent_lP_lcond lP
  (calc_lP alpha lP). 
Proof.
  unfold consistent_lP_lcond.
  intros. apply consistent_lP_lcond_calc_lP_pre.
Qed.

(* NEED TO CHANGE THIS. *)
Lemma sS_lem_e5 : forall lP atm alpha x W Iv Ip Ir,
  is_BOXATM_flag_strong_CONJ atm = true ->
SOQFree alpha = true ->
is_in_FOvar (Var 0) (FOvars_in atm) = false ->
  SOturnst W Iv Ip Ir (replace_pred_l alpha lP (list_Var (length lP) x)
    (calc_lP (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm)) lP)) <->
  SOturnst W Iv Ip Ir (replace_pred_l alpha lP (list_Var (length lP) x)
    (calc_lP atm lP)).
Proof.
  intros lP atm alpha x W Iv Ip Ir Hat Hno Hin.
  apply lem_try_l.
    all : try rewrite length_calc_lP.

    rewrite length_calc_lP. all : try reflexivity.
    rewrite is_equiv_conj_assoc_l_comm.
    apply is_equiv_conj_assoc_l_calc_lP_fun5_l''.

    all : try assumption.

    apply is_un_predless_l_calc_lP.
    apply is_un_predless_l_calc_lP.
    apply consistent_lP_lcond_calc_lP.
    apply consistent_lP_lcond_calc_lP.
Qed.

Lemma sS_lem_e5_BAT : forall lP atm alpha x W Iv Ip Ir,
  BAT atm = true ->
SOQFree alpha = true ->
is_in_FOvar (Var 0) (FOvars_in atm) = false ->
  SOturnst W Iv Ip Ir (replace_pred_l alpha lP (list_Var (length lP) x)
    (calc_lP (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm)) lP)) <->
  SOturnst W Iv Ip Ir (replace_pred_l alpha lP (list_Var (length lP) x)
    (calc_lP atm lP)).
Proof.
  intros lP atm alpha x W Iv Ip Ir Hat Hno Hin.
  apply lem_try_l.
    all : try rewrite length_calc_lP.

    rewrite length_calc_lP. all : try reflexivity.
    rewrite is_equiv_conj_assoc_l_comm.
    apply is_equiv_conj_assoc_l_calc_lP_fun5_l''_BAT.

    all : try assumption.

    apply is_un_predless_l_calc_lP.
    apply is_un_predless_l_calc_lP.
    apply consistent_lP_lcond_calc_lP.
    apply consistent_lP_lcond_calc_lP.
Qed.

(* Lemma sS_lem_e19 : forall lP atm1 atm2 P y x W Iv Ip Ir,
 is_BOXATM_flag_strong_CONJ atm1 = true ->
 is_BOXATM_flag_strong_CONJ atm2 = true ->
 SOturnst W Iv Ip Ir (replace_pred_l (predSO P y) lP
      (list_Var (length lP) x) (calc_lP atm1 lP)) <->
  SOturnst W Iv Ip Ir (replace_pred_l (predSO P y) lP
      (list_Var (length lP) x) (calc_lP atm2 lP)).
Proof.
Admitted.  *)

Lemma sS_lem118'_is_in_pred_pre : forall m n atm P x,
  n = num_conn atm ->
  Nat.leb n m = true ->
BOXATM_flag_strong atm x = true -> 
  is_in_pred P (preds_in 
(fun5'' (batm_comp_P atm) (batm_comp_x1 atm) (batm_comp_lx atm))) = 
  is_in_pred P (preds_in atm).
Proof.
  induction m; intros n atm P x Hnum Hleb Hat.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
    destruct p. destruct f. reflexivity.

    destruct n.
    destruct atm; try discriminate.
    destruct p. destruct f. reflexivity.

    simpl in Hleb. destruct atm; try discriminate. 
      destruct f as [x0].  (*  destruct xn. discriminate. *)
      destruct atm; try discriminate. destruct atm1; try discriminate.
      destruct f as [y1]. destruct f0 as [y2].
      destruct x as [xn]. 
      simpl in *. case_eq (beq_nat xn y1); intros Hbeq; rewrite Hbeq in *.
        2 : discriminate.
      case_eq (beq_nat x0 y2); intros Hbeq2; rewrite Hbeq2 in *.
        2 : discriminate.
      case_eq (beq_nat y2 (S y1)); intros Hbeq3; rewrite Hbeq3 in *.
        2 : discriminate.
      pose proof (try3 _ _ Hat) as Hat'.
rewrite <- Hat'.
(*  rewrite <- (beq_nat_true _ _ Hbeq3).
      rewrite <- (beq_nat_true _ _ Hbeq2). rewrite <- Hat'.
 *)      destruct n. discriminate.
      apply (IHm n _ _ (Var x0)). inversion Hnum. reflexivity.
      destruct m. discriminate. apply leb_suc_r. assumption.
      assumption.
Qed.

Lemma sS_lem118'_is_in_pred_pre_BAT : forall m n atm P x,
  n = num_conn atm ->
  Nat.leb n m = true ->
BOXATM_flag_weak atm x = true -> 
  is_in_pred P (preds_in 
(fun5'' (batm_comp_P atm) (batm_comp_x1 atm) (batm_comp_lx atm))) = 
  is_in_pred P (preds_in atm).
Proof.
  induction m; intros n atm P x Hnum Hleb Hat.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
    destruct p. destruct f. reflexivity.

    destruct n.
    destruct atm; try discriminate.
    destruct p. destruct f. reflexivity.

    simpl in Hleb. destruct atm; try discriminate. 
      destruct f as [x0].  (*  destruct xn. discriminate. *)
      destruct atm; try discriminate. destruct atm1; try discriminate.
      destruct f as [y1]. destruct f0 as [y2].
      destruct x as [xn]. 
      simpl in *. case_eq (beq_nat xn y1); intros Hbeq; rewrite Hbeq in *.
        2 : discriminate.
      case_eq (beq_nat x0 y2); intros Hbeq2; rewrite Hbeq2 in *.
        2 : discriminate.
(*       case_eq (beq_nat y2 (S y1)); intros Hbeq3; rewrite Hbeq3 in *.
        2 : discriminate. *)
      pose proof (try3_BAT _ _ Hat) as Hat'.
rewrite <- Hat'.
(*  rewrite <- (beq_nat_true _ _ Hbeq3).
      rewrite <- (beq_nat_true _ _ Hbeq2). rewrite <- Hat'.
 *)      destruct n. discriminate.
      apply (IHm n _ _ (Var x0)). inversion Hnum. reflexivity.
      destruct m. discriminate. apply leb_suc_r. assumption.
      assumption.
Qed.

Lemma sS_lem118'_is_in_pred_pre' : forall atm P x,
BOXATM_flag_strong atm x = true -> 
  is_in_pred P (preds_in 
(fun5'' (batm_comp_P atm) (batm_comp_x1 atm) (batm_comp_lx atm))) = 
  is_in_pred P (preds_in atm).
Proof.
  intros until 0. apply (sS_lem118'_is_in_pred_pre (num_conn atm) (num_conn atm)).
  reflexivity. apply leb_refl.
Qed.

Lemma sS_lem118'_is_in_pred_pre'_BAT : forall atm P x,
BOXATM_flag_weak atm x = true -> 
  is_in_pred P (preds_in 
(fun5'' (batm_comp_P atm) (batm_comp_x1 atm) (batm_comp_lx atm))) = 
  is_in_pred P (preds_in atm).
Proof.
  intros until 0. apply (sS_lem118'_is_in_pred_pre_BAT (num_conn atm) (num_conn atm)).
  reflexivity. apply leb_refl.
Qed.

Lemma preds_in_fun5_l''_app : forall la1 la2 lb1 lb2 lc1 lc2,
  length la1 = length lb1 ->
  length la1 = length lc1 ->
  preds_in (fun5_l'' (app la1 la2) (app lb1 lb2) (app lc1 lc2)) =
  app (preds_in (fun5_l'' la1 lb1 lc1)) (preds_in (fun5_l'' la2 lb2 lc2)).
Proof.
  induction la1; intros la2 lb1 lb2 lc1 lc2 Hl1 Hl2.
    simpl. destruct lb1. destruct lc1. simpl. reflexivity.
    all : try discriminate.

    case_eq la1. intros Hla1. rewrite Hla1 in *.
      case_eq lb1. intros Hlb1. rewrite Hlb1 in *. discriminate.
      intros b1 lb1' Hlb1. rewrite <- Hlb1.
        destruct lb1'. 2 : (rewrite Hlb1 in *; discriminate).
      case_eq lc1. intros Hlc1. rewrite Hlc1 in *. discriminate.
      intros c1 lc1' Hlc1. rewrite <- Hlc1.
        destruct lc1'. 2 : (rewrite Hlc1 in *; discriminate).
      simpl. rewrite Hlb1. rewrite Hlc1. rewrite <- Hlb1.
      rewrite <- Hlc1.

      destruct la2. rewrite Hlb1. simpl.
      destruct lb2.  rewrite Hlc1. simpl.
      rewrite List.app_nil_r. reflexivity.
      rewrite Hlc1. simpl. 
      rewrite List.app_nil_r. reflexivity.
      rewrite Hlb1.
      case_eq ((app (cons b1 nil) lb2)).
        intros H. discriminate.
      intros bb1 lbb1 Hlbb1.  
      simpl in Hlbb1. inversion Hlbb1 as [[H Hlbb1']].
      rewrite <- H. case_eq lbb1. intros Hlbb2.
      case_eq (app lc1 lc2). intros Hlc.
        rewrite Hlc1 in *. discriminate. 
      intros cc1 lcc1 Hlcc1. rewrite Hlc1 in Hlcc1.
      simpl in Hlcc1. inversion Hlcc1 as [[H2 Hlcc1']].
      simpl. destruct la2. simpl. 
      rewrite List.app_nil_r. reflexivity.
      rewrite List.app_nil_r. reflexivity.

      intros bbb1 lbbb1 Hlbbb1.
      rewrite <- Hlbbb1.
      case_eq (app lc1 lc2). intros Hlc.
        rewrite Hlc1 in *. discriminate. 
      intros cc1 lcc1 Hlcc1. rewrite Hlc1 in Hlcc1.
      simpl in Hlcc1. inversion Hlcc1 as [[H2 Hlcc1']].
      rewrite <- Hlcc1'.
      destruct lc2.
      simpl. destruct la2. destruct lbb1. simpl. 
      rewrite List.app_nil_r. reflexivity.
      destruct lbb1.
      rewrite List.app_nil_r. reflexivity.
      rewrite List.app_nil_r. reflexivity.
      destruct lbb1. 
      rewrite List.app_nil_r. reflexivity.
      destruct lbb1;
      rewrite List.app_nil_r; reflexivity.

      simpl. reflexivity.

    intros P lP Hla1. rewrite <- Hla1.
    case_eq lb1. intros Hlb1. rewrite Hlb1 in *. discriminate.
    intros b1 lb1' Hlb1. 
    case_eq lc1. intros Hlc1. rewrite Hlc1 in *. discriminate.
    intros c1 lc1' Hlc1.
    simpl. rewrite Hla1. rewrite <- Hla1.
    case_eq (app la1 la2). rewrite Hla1. discriminate.
    intros aa la Hla. rewrite <- Hla. 
    case_eq lb1'. intros H. rewrite H in *. rewrite Hlb1 in *.
      rewrite Hla1 in *. discriminate.
    intros b lbb Hlbb. rewrite <- Hlbb.
    case_eq lc1'. intros H. rewrite H in *. rewrite Hlc1 in *.
      rewrite Hla1 in *. discriminate.
    intros c lcc Hlcc. rewrite <- Hlcc.
    case_eq (app lb1' lb2). rewrite Hlbb. discriminate. 
    intros bbb lbbb Hlbbb. rewrite <- Hlbbb.
    case_eq (app lc1' lc2). rewrite Hlcc. discriminate. 
    intros ccc lccc Hlccc. rewrite <- Hlccc.
    simpl. rewrite IHla1.  rewrite List.app_assoc.
    reflexivity.

    rewrite Hla1 in*. rewrite Hlb1 in *. rewrite Hlbb in *. 
    simpl. inversion Hl1. reflexivity.

    rewrite Hlc1 in*. rewrite Hla1 in *. rewrite Hlcc in *. 
    simpl. inversion Hl2. reflexivity.
Qed.

Lemma sS_lem118'_is_in_pred : forall m n atm P,
  n = num_conn atm ->
  Nat.leb n m = true ->
is_BOXATM_flag_strong_CONJ atm = true -> 
  is_in_pred P (preds_in 
(fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm))) = 
  is_in_pred P (preds_in atm).
Proof.
  induction m; intros n atm [Pn] Hnum Hleb Hat; try discriminate.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
    destruct p as [Qm]; destruct f. simpl in *.
    reflexivity.

    destruct n. destruct atm; try discriminate.
    destruct p as [Qm]; destruct f. simpl in *.
    reflexivity.

    simpl in Hleb. destruct atm; try discriminate.

    destruct f as [xn]. destruct xn. discriminate.
    destruct atm; try discriminate. destruct atm1; try discriminate.
    destruct f as [y1]. destruct f0 as [y2].
    pose proof (is_BOXATM_flag_strong_CONJ_allFO_eq _ _ _ _ Hat) as Hat2.
    rewrite Hat2 in *. simpl in *. destruct y2. discriminate.
    rewrite <- beq_nat_refl in *.
    simpl in *. case_eq (PeanoNat.Nat.eqb y2 y1);
      intros Hbeq; rewrite Hbeq in *. 2 : discriminate.

(*     rewrite <- (beq_nat_true _ _ Hbeq). *)
    pose proof Hat as Hat'.
    apply try3 in Hat. rewrite <- Hat.
    apply sS_lem118'_is_in_pred_pre' with (x := (Var (S y2))).
    assumption.

    simpl in Hat.
    case_eq (is_BOXATM_flag_strong_CONJ atm1); intros Hbox;
      rewrite Hbox in *. 2 : discriminate.
    simpl. rewrite preds_in_fun5_l''_app.
    do 2 rewrite is_in_pred_app_if.
    simpl in Hnum. inversion Hnum as [Hnum'].
    rewrite Hnum' in Hleb.
    simpl in Hat.
    rewrite (IHm (num_conn atm1) atm1). rewrite (IHm (num_conn atm2) atm2).
    all : try reflexivity. all : try assumption.
      apply leb_plus_take2 in Hleb. assumption.
      apply leb_plus_take1 in Hleb. assumption.
      apply length_batm_conj_comp_P_x1. assumption.
      apply length_batm_conj_comp_P_lx. assumption.
Qed.

Lemma sS_lem118'_is_in_pred_BAT : forall m n atm P,
  n = num_conn atm ->
  Nat.leb n m = true ->
BAT atm = true -> 
  is_in_pred P (preds_in 
(fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm))) = 
  is_in_pred P (preds_in atm).
Proof.
  induction m; intros n atm [Pn] Hnum Hleb Hat; try discriminate.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
    destruct p as [Qm]; destruct f. simpl in *.
    reflexivity.

    destruct n. destruct atm; try discriminate.
    destruct p as [Qm]; destruct f. simpl in *.
    reflexivity.

    simpl in Hleb. destruct atm; try discriminate.

    destruct f as [xn]. (*  destruct xn. discriminate. *)
    destruct atm; try discriminate. destruct atm1; try discriminate.
    destruct f as [y1]. destruct f0 as [y2].
    pose proof (is_BOXATM_flag_strong_CONJ_allFO_eq_BAT _ _ _ _ Hat) as Hat2.
    rewrite Hat2 in *. simpl in *.
(*  destruct y2. discriminate.
    rewrite <- beq_nat_refl in *.
    simpl in *. case_eq (PeanoNat.Nat.eqb y2 y1);
      intros Hbeq; rewrite Hbeq in *. 2 : discriminate. *)

(*     rewrite <- (beq_nat_true _ _ Hbeq). *)
    pose proof Hat as Hat'.
    do 2 rewrite <- beq_nat_refl in *.
    apply try3_BAT in Hat. rewrite <- Hat.
    apply sS_lem118'_is_in_pred_pre'_BAT with (x := (Var (y2))).
    assumption.

    simpl in Hat.
    case_eq (BAT atm1); intros Hbox;
      rewrite Hbox in *. 2 : discriminate.
    simpl. rewrite preds_in_fun5_l''_app.
    do 2 rewrite is_in_pred_app_if.
    simpl in Hnum. inversion Hnum as [Hnum'].
    rewrite Hnum' in Hleb.
    simpl in Hat.
    rewrite (IHm (num_conn atm1) atm1). rewrite (IHm (num_conn atm2) atm2).
    all : try reflexivity. all : try assumption.
      apply leb_plus_take2 in Hleb. assumption.
      apply leb_plus_take1 in Hleb. assumption.
      apply length_batm_conj_comp_P_x1_BAT. assumption.
      apply length_batm_conj_comp_P_lx_BAT. assumption.
Qed.

Lemma sS_lem118'_is_in_pred' : forall atm P,
is_BOXATM_flag_strong_CONJ atm = true -> 
  is_in_pred P (preds_in 
(fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm))) = 
  is_in_pred P (preds_in atm).
Proof.
  intros until 0. apply (sS_lem118'_is_in_pred (num_conn atm) (num_conn atm)).
  reflexivity. apply leb_refl.
Qed.

Lemma sS_lem118'_is_in_pred'_BAT : forall atm P,
BAT atm = true -> 
  is_in_pred P (preds_in 
(fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm))) = 
  is_in_pred P (preds_in atm).
Proof.
  intros until 0. apply (sS_lem118'_is_in_pred_BAT (num_conn atm) (num_conn atm)).
  reflexivity. apply leb_refl.
Qed.


Lemma sS_lem_e4 : forall l atm,
is_BOXATM_flag_strong_CONJ atm = true -> 
list_pred_not_in  (preds_in
(fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm))) l =
list_pred_not_in (preds_in atm) l.
Proof.
  induction l; intros atm Hat. reflexivity.
  simpl. rewrite sS_lem118'_is_in_pred'.
  case_eq (is_in_pred a (preds_in atm)); intros Hin.
    apply IHl. assumption.

    rewrite IHl. reflexivity. all : assumption.
Qed.

Lemma sS_lem_e4_BAT : forall l atm,
BAT atm = true -> 
list_pred_not_in  (preds_in
(fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm))) l =
list_pred_not_in (preds_in atm) l.
Proof.
  induction l; intros atm Hat. reflexivity.
  simpl. rewrite sS_lem118'_is_in_pred'_BAT.
  case_eq (is_in_pred a (preds_in atm)); intros Hin.
    apply IHl. assumption.

    rewrite IHl. reflexivity. all : assumption.
Qed.



Lemma sS_lem_e3 : forall atm rel beta,
is_BOXATM_flag_strong_CONJ atm = true ->  REL rel = true ->
  instant_cons_empty' (conjSO rel 
(fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm))) beta =
  instant_cons_empty' (conjSO rel atm) beta.
Proof.
  intros atm rel beta Hat Hrel.
  unfold instant_cons_empty'. simpl.
  rewrite (preds_in_rel rel Hrel). simpl.
  rewrite sS_lem_e4. reflexivity.
  assumption.
Qed.

Lemma sS_lem_e3_BAT : forall atm rel beta,
BAT atm = true ->  REL rel = true ->
  instant_cons_empty' (conjSO rel 
(fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm))) beta =
  instant_cons_empty' (conjSO rel atm) beta.
Proof.
  intros atm rel beta Hat Hrel.
  unfold instant_cons_empty'. simpl.
  rewrite (preds_in_rel rel Hrel). simpl.
  rewrite sS_lem_e4_BAT. reflexivity.
  assumption.
Qed.

Lemma max_FOv_fun5_l'' : forall atm rel beta,
  is_BOXATM_flag_strong_CONJ atm = true ->
is_in_FOvar (Var 0) (batm_conj_comp_x1 atm)  = false ->
(max_FOv  (implSO  (conjSO rel
   (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm)
               (batm_conj_comp_lx atm))) beta)) =
(max_FOv  (implSO  (conjSO rel atm) beta)).
Proof.
  intros atm rel beta H H2.
  simpl. rewrite max_FOv_fun5_l''_pre. reflexivity.
  assumption. assumption.
Qed.

Lemma max_FOv_fun5_l''_BAT : forall atm rel beta,
  BAT atm = true ->
is_in_FOvar (Var 0) (FOvars_in atm)  = false ->
(max_FOv  (implSO  (conjSO rel
   (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm)
               (batm_conj_comp_lx atm))) beta)) =
(max_FOv  (implSO  (conjSO rel atm) beta)).
Proof.
  intros atm rel beta H H2.
  simpl. rewrite max_FOv_fun5_l''_pre_BAT. reflexivity.
  assumption. assumption.
Qed.

Lemma rep_pred_l_is_unary_predless_gen : forall lP alpha lx lcond,
  is_unary_predless alpha = true ->
    replace_pred_l alpha lP lx lcond = alpha.
Proof.
  induction lP; intros alpha lx lcond H.
    reflexivity.

    destruct lx. reflexivity. destruct lcond. reflexivity.
    simpl. rewrite rep_pred_is_unary_predless.
    apply IHlP.
    assumption.   
    apply rep_pred_l_is_unary_predless. assumption.
Qed.

Lemma calc_lx1_P_fun5_l'' : forall atm P,
  is_BOXATM_flag_strong_CONJ atm = true ->
  calc_lx1_P (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm)) P
= calc_lx1_P atm P.
Proof.
  induction atm; intros P H; try discriminate. reflexivity.

    destruct f as [xn]. destruct xn. discriminate.
    simpl. destruct atm; try discriminate; try reflexivity.
    destruct atm1; try discriminate.
    simpl. rewrite  <- lem_try3 with (y := (Var (S xn))).
    reflexivity.
    apply is_BOXATM_flag_strong__CONJ in H.
    assumption.

    pose proof (is_BOXATM_flag_strong_CONJ_conjSO_l _ _ H).
    simpl. rewrite calc_lx1_P_fun5_l''_app.
    rewrite (IHatm1). rewrite IHatm2.
    reflexivity.
    apply is_BOXATM_flag_strong_CONJ_conjSO_r in H. assumption.
    assumption.
    apply length_batm_conj_comp_P_x1. assumption.
    apply length_batm_conj_comp_P_lx. assumption.
Qed.

Lemma calc_lx1_P_fun5_l''_BAT : forall atm P,
  BAT atm = true ->
  calc_lx1_P (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm)) P
= calc_lx1_P atm P.
Proof.
  induction atm; intros P H; try discriminate. reflexivity.

    destruct f as [xn]. (* destruct xn. discriminate. *)
    simpl. destruct atm; try discriminate; try reflexivity.
    destruct atm1; try discriminate.
    simpl. rewrite  <- lem_try3_BAT with (y := (Var ( xn))).
    reflexivity.
    apply is_BOXATM_flag_strong__CONJ_BAT in H.
    assumption.

    pose proof (BAT_conjSO_l _ _ H).
    simpl. rewrite calc_lx1_P_fun5_l''_app.
    rewrite (IHatm1). rewrite IHatm2.
    reflexivity.
    apply BAT_conjSO_r in H. assumption.
    assumption.
    apply length_batm_conj_comp_P_x1_BAT. assumption.
    apply length_batm_conj_comp_P_lx_BAT. assumption.
Qed.


Lemma sS_lem_e22_pre_predSO : forall lP atm atm2 p f y W Iv Ip Ir,
is_in_FOvar (Var 0) (FOvars_in atm) = false ->
 is_BOXATM_flag_strong_CONJ atm = true ->
 atm2 = (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm)) ->
SOturnst W Iv Ip Ir (replace_pred_l (predSO p f) lP (list_Var (length lP) y) (calc_lP atm2 lP)) <->
SOturnst W Iv Ip Ir (replace_pred_l (predSO p f) lP (list_Var (length lP) y) (calc_lP atm lP)).
Proof.
  induction lP; intros atm atm2 [Pn] [xn] [ym] W Iv Ip Ir Hin0 Hat1 Hat2.
    simpl in *. apply iff_refl.

    assert (length lP = length (list_Var (length lP) (Var ym))) as Hass1.
        symmetry. apply length_list_Var.
    assert (length lP = length (vsS_syn_l (FOv_att_P_l atm2 lP) (Var ym))) as Hass2.
        rewrite <- length_vsS_syn_l.
        apply length_FOv_att_P_l.
    assert (length lP = length (vsS_syn_l (FOv_att_P_l atm lP) (Var ym))) as Hass3.
        rewrite <- length_vsS_syn_l.
        apply length_FOv_att_P_l.
    simpl. case_eq (is_in_pred a lP); intros Hin. 
      rewrite rep_pred__l_is_in2.
      rewrite rep_pred__l_is_in2.
      apply IHlP; assumption.
        all : try assumption.
rewrite length_calc_lP. reflexivity.
apply is_un_predless_l_calc_lP.
apply is_un_predless_fun4_l2'.
rewrite length_calc_lP. reflexivity.
apply is_un_predless_l_calc_lP.
apply is_un_predless_fun4_l2'.
(*         apply un_predless_l_vsS_syn_l.
        apply un_predless_fun1.
        apply un_predless_l_vsS_syn_l.
        apply un_predless_fun1. *)

      rewrite rep_pred__l_switch; try assumption.
      rewrite rep_pred__l_switch; try assumption.
      destruct a as [Qm]. simpl.
      case_eq (beq_nat Qm Pn); intros Hbeq.
        split; intros H.
rewrite rep_pred_l_is_unary_predless_gen.
rewrite rep_pred_l_is_unary_predless_gen in H.
rewrite Hat2 in *. rewrite calc_lx1_P_fun5_l'' in H.
rewrite calc_llv_P_fun5_l'' in H.
rewrite new_FOv_pp_pre2_fun5_l''2 in H.
all : try assumption.

rewrite is_BOXATM_CONJ_is_in_batm_conj_equiv;
assumption.


apply rep_FOv_is_unary_predless.
apply is_un_predless_fun4_l2'.
apply rep_FOv_is_unary_predless.
apply is_un_predless_fun4_l2'.

rewrite rep_pred_l_is_unary_predless_gen.
rewrite rep_pred_l_is_unary_predless_gen in H.
rewrite Hat2 in *. rewrite calc_lx1_P_fun5_l'' in *.
rewrite calc_llv_P_fun5_l'' in *.
rewrite new_FOv_pp_pre2_fun5_l''2 in *.
all : try assumption.

rewrite is_BOXATM_CONJ_is_in_batm_conj_equiv;
assumption.

apply rep_FOv_is_unary_predless.
apply is_un_predless_fun4_l2'.
apply rep_FOv_is_unary_predless.
apply is_un_predless_fun4_l2'.

rewrite Hat2. apply sS_lem_e5.
assumption.
reflexivity.
assumption.

apply is_un_predless_fun4_l2'.
apply is_un_predless_l_calc_lP.
apply is_un_predless_fun4_l2'.
apply is_un_predless_l_calc_lP.
Qed.

Lemma sS_lem_e22_pre_predSO_BAT : forall lP atm atm2 p f y W Iv Ip Ir,
is_in_FOvar (Var 0) (FOvars_in atm) = false ->
 BAT atm = true ->
 atm2 = (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm)) ->
SOturnst W Iv Ip Ir (replace_pred_l (predSO p f) lP (list_Var (length lP) y) (calc_lP atm2 lP)) <->
SOturnst W Iv Ip Ir (replace_pred_l (predSO p f) lP (list_Var (length lP) y) (calc_lP atm lP)).
Proof.
  induction lP; intros atm atm2 [Pn] [xn] [ym] W Iv Ip Ir Hin0 Hat1 Hat2.
    simpl in *. apply iff_refl.

    assert (length lP = length (list_Var (length lP) (Var ym))) as Hass1.
        symmetry. apply length_list_Var.
    assert (length lP = length (vsS_syn_l (FOv_att_P_l atm2 lP) (Var ym))) as Hass2.
        rewrite <- length_vsS_syn_l.
        apply length_FOv_att_P_l.
    assert (length lP = length (vsS_syn_l (FOv_att_P_l atm lP) (Var ym))) as Hass3.
        rewrite <- length_vsS_syn_l.
        apply length_FOv_att_P_l.
    simpl. case_eq (is_in_pred a lP); intros Hin. 
      rewrite rep_pred__l_is_in2.
      rewrite rep_pred__l_is_in2.
      apply IHlP; assumption.
        all : try assumption.
rewrite length_calc_lP. reflexivity.
apply is_un_predless_l_calc_lP.
apply is_un_predless_fun4_l2'.
rewrite length_calc_lP. reflexivity.
apply is_un_predless_l_calc_lP.
apply is_un_predless_fun4_l2'.
(*         apply un_predless_l_vsS_syn_l.
        apply un_predless_fun1.
        apply un_predless_l_vsS_syn_l.
        apply un_predless_fun1. *)

      rewrite rep_pred__l_switch; try assumption.
      rewrite rep_pred__l_switch; try assumption.
      destruct a as [Qm]. simpl.
      case_eq (beq_nat Qm Pn); intros Hbeq.
        split; intros H.
rewrite rep_pred_l_is_unary_predless_gen.
rewrite rep_pred_l_is_unary_predless_gen in H.
rewrite Hat2 in *. rewrite calc_lx1_P_fun5_l''_BAT in H.
rewrite calc_llv_P_fun5_l''_BAT in H.
rewrite new_FOv_pp_pre2_fun5_l''2_BAT in H.
all : try assumption.

(* rewrite is_BOXATM_CONJ_is_in_batm_conj_equiv.

Search "is_in_batm_conj_equiv".
rewrite is_BOXATM_flag_strong_CONJ_is_in_batm_conj_equiv;
assumption. *)


apply rep_FOv_is_unary_predless.
apply is_un_predless_fun4_l2'.
apply rep_FOv_is_unary_predless.
apply is_un_predless_fun4_l2'.

rewrite rep_pred_l_is_unary_predless_gen.
rewrite rep_pred_l_is_unary_predless_gen in H.
rewrite Hat2 in *. rewrite calc_lx1_P_fun5_l''_BAT in *.
rewrite calc_llv_P_fun5_l''_BAT in *.
rewrite new_FOv_pp_pre2_fun5_l''2_BAT in *.
all : try assumption.

(* rewrite is_BOXATM_CONJ_is_in_batm_conj_equiv;
assumption. *)

apply rep_FOv_is_unary_predless.
apply is_un_predless_fun4_l2'.
apply rep_FOv_is_unary_predless.
apply is_un_predless_fun4_l2'.

rewrite Hat2. apply sS_lem_e5_BAT.
assumption.
reflexivity.
assumption.

apply is_un_predless_fun4_l2'.
apply is_un_predless_l_calc_lP.
apply is_un_predless_fun4_l2'.
apply is_un_predless_l_calc_lP.
Qed.

Lemma sS_lem_e22_pre_num_conn : forall m n atm0 lP atm atm2 y W Iv Ip Ir,
  n = num_conn atm0 ->
  Nat.leb n m = true ->

is_in_FOvar (Var 0) (FOvars_in atm) = false ->
  is_BOXATM_flag_strong_CONJ atm = true ->
  is_BOXATM_flag_strong_CONJ atm0 = true ->
  atm2 = (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm)) ->
  SOturnst W Iv Ip Ir (replace_pred_l atm0 lP (list_Var (length lP) y)
    (calc_lP atm2 lP)) <->
  SOturnst W Iv Ip Ir (replace_pred_l atm0 lP (list_Var (length lP) y)
    (calc_lP atm lP)).
Proof.
  induction m; intros n atm0 lP atm atm2 y W Iv Ip Ir Hconn Hleb Hin0 Hat1 Hat2 Hat3; try discriminate.

    destruct n. 2 : discriminate.
    destruct atm0; try discriminate.
    apply sS_lem_e22_pre_predSO; assumption.

    destruct n.
    destruct atm0; try discriminate.
    apply sS_lem_e22_pre_predSO; assumption.

    destruct atm0; try discriminate.
    destruct f as [xn]. destruct xn. discriminate.
    destruct atm0; try discriminate.
    destruct atm0_1; try discriminate.
    do 2 rewrite rep_pred_l_allFO.
    do 2 rewrite SOturnst_allFO.
    split; intros SOt d;
      rewrite rep_pred_l_implSO in *;
      rewrite SOturnst_implSO in *;
      intros SOt2;
      rewrite rep_pred_l_relatSO in *;
      specialize (SOt _ SOt2);
      apply (IHm (num_conn atm0_2) atm0_2 lP atm atm2); try assumption.
        reflexivity.
    simpl in Hconn. inversion Hconn. rewrite Hconn in Hleb.
    simpl in Hleb. destruct m. discriminate.
    apply leb_suc_r. assumption.


    apply is_BOXATM_flag_strong_CONJ_allFO_atm in Hat2.
    apply is_BOXATM_flag_strong__CONJ2 in Hat2. assumption.

        reflexivity.

    simpl in Hconn. inversion Hconn. rewrite Hconn in Hleb.
    simpl in Hleb. destruct m. discriminate.
    apply leb_suc_r. assumption.

    apply is_BOXATM_flag_strong_CONJ_allFO_atm in Hat2.
    apply is_BOXATM_flag_strong__CONJ2 in Hat2. assumption.


    do 2 rewrite rep_pred_l_conjSO.
    pose proof (is_BOXATM_flag_strong_CONJ_conjSO_l _ _ Hat2).
    pose proof (is_BOXATM_flag_strong_CONJ_conjSO_r _ _ Hat2).
    assert (Nat.leb (num_conn atm0_1) m = true) as Hleb1. 
      simpl in Hconn. inversion Hconn as [Hnum'].
      simpl in Hleb. rewrite Hnum' in Hleb.
      apply leb_plus_take1 in Hleb. assumption.
    assert (Nat.leb (num_conn atm0_2) m = true) as Hleb2.
      simpl in Hconn. inversion Hconn as [Hnum'].
      simpl in Hleb. rewrite Hnum' in Hleb.
      apply leb_plus_take2 in Hleb. assumption.
    simpl. split; intros [H1 H2]; (apply conj;
      [apply (IHm (num_conn atm0_1) atm0_1 lP atm atm2) | 
       apply (IHm (num_conn atm0_2) atm0_2 lP atm atm2) ]);
      try assumption; try reflexivity.
Qed.

Lemma sS_lem_e22_pre_num_conn_BAT : forall m n atm0 lP atm atm2 y W Iv Ip Ir,
  n = num_conn atm0 ->
  Nat.leb n m = true ->

is_in_FOvar (Var 0) (FOvars_in atm) = false ->
  BAT atm = true ->
  BAT atm0 = true ->
  atm2 = (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm)) ->
  SOturnst W Iv Ip Ir (replace_pred_l atm0 lP (list_Var (length lP) y)
    (calc_lP atm2 lP)) <->
  SOturnst W Iv Ip Ir (replace_pred_l atm0 lP (list_Var (length lP) y)
    (calc_lP atm lP)).
Proof.
  induction m; intros n atm0 lP atm atm2 y W Iv Ip Ir Hconn Hleb Hin0 Hat1 Hat2 Hat3; try discriminate.

    destruct n. 2 : discriminate.
    destruct atm0; try discriminate.
    apply sS_lem_e22_pre_predSO_BAT; assumption.

    destruct n.
    destruct atm0; try discriminate.
    apply sS_lem_e22_pre_predSO_BAT; assumption.

    destruct atm0; try discriminate.
    destruct f as [xn]. (*  destruct xn. discriminate. *)
    destruct atm0; try discriminate.
    destruct atm0_1; try discriminate.
    do 2 rewrite rep_pred_l_allFO.
    do 2 rewrite SOturnst_allFO.
    split; intros SOt d;
      rewrite rep_pred_l_implSO in *;
      rewrite SOturnst_implSO in *;
      intros SOt2;
      rewrite rep_pred_l_relatSO in *;
      specialize (SOt _ SOt2);
      apply (IHm (num_conn atm0_2) atm0_2 lP atm atm2); try assumption.
        reflexivity.
    simpl in Hconn. inversion Hconn. rewrite Hconn in Hleb.
    simpl in Hleb. destruct m. discriminate.
    apply leb_suc_r. assumption.


    apply is_BOXATM_flag_strong_CONJ_allFO_atm_BAT in Hat2.
    apply is_BOXATM_flag_strong__CONJ2_BAT in Hat2. assumption.

        reflexivity.

    simpl in Hconn. inversion Hconn. rewrite Hconn in Hleb.
    simpl in Hleb. destruct m. discriminate.
    apply leb_suc_r. assumption.

    apply is_BOXATM_flag_strong_CONJ_allFO_atm_BAT in Hat2.
    apply is_BOXATM_flag_strong__CONJ2_BAT in Hat2. assumption.


    do 2 rewrite rep_pred_l_conjSO.
    pose proof (BAT_conjSO_l _ _ Hat2).
    pose proof (BAT_conjSO_r _ _ Hat2).
    assert (Nat.leb (num_conn atm0_1) m = true) as Hleb1. 
      simpl in Hconn. inversion Hconn as [Hnum'].
      simpl in Hleb. rewrite Hnum' in Hleb.
      apply leb_plus_take1 in Hleb. assumption.
    assert (Nat.leb (num_conn atm0_2) m = true) as Hleb2.
      simpl in Hconn. inversion Hconn as [Hnum'].
      simpl in Hleb. rewrite Hnum' in Hleb.
      apply leb_plus_take2 in Hleb. assumption.
    simpl. split; intros [H1 H2]; (apply conj;
      [apply (IHm (num_conn atm0_1) atm0_1 lP atm atm2) | 
       apply (IHm (num_conn atm0_2) atm0_2 lP atm atm2) ]);
      try assumption; try reflexivity.
Qed.

Lemma sS_lem_e22_pre : forall atm0 lP atm atm2 y W Iv Ip Ir,
is_in_FOvar (Var 0) (FOvars_in atm) = false ->
  is_BOXATM_flag_strong_CONJ atm = true ->
  is_BOXATM_flag_strong_CONJ atm0 = true ->
  atm2 = (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm)) ->
  SOturnst W Iv Ip Ir (replace_pred_l atm0 lP (list_Var (length lP) y)
    (calc_lP atm2 lP)) <->
  SOturnst W Iv Ip Ir (replace_pred_l atm0 lP (list_Var (length lP) y)
    (calc_lP atm lP)).
Proof.
  intros until 0.
  apply (sS_lem_e22_pre_num_conn (num_conn atm0) (num_conn atm0)).
  reflexivity.
  apply leb_refl.
Qed.

Lemma sS_lem_e22_pre_BAT : forall atm0 lP atm atm2 y W Iv Ip Ir,
is_in_FOvar (Var 0) (FOvars_in atm) = false ->
  BAT atm = true ->
  BAT atm0 = true ->
  atm2 = (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm)) ->
  SOturnst W Iv Ip Ir (replace_pred_l atm0 lP (list_Var (length lP) y)
    (calc_lP atm2 lP)) <->
  SOturnst W Iv Ip Ir (replace_pred_l atm0 lP (list_Var (length lP) y)
    (calc_lP atm lP)).
Proof.
  intros until 0.
  apply (sS_lem_e22_pre_num_conn_BAT (num_conn atm0) (num_conn atm0)).
  reflexivity.
  apply leb_refl.
Qed.

Lemma sS_lem_e22_pre2_num_conn_pre_num_conn : forall m n atm atm2 lP lcond y x W Iv Ip Ir,
    n = num_conn atm ->
  Nat.leb n m = true ->
  atm2 = (fun5'' (batm_comp_P atm) (batm_comp_x1 atm) (batm_comp_lx atm)) ->
  BOXATM_flag_strong atm  x= true ->
  SOturnst W Iv Ip Ir (replace_pred_l atm2 lP (list_Var (length lP) y) lcond) <->
  SOturnst W Iv Ip Ir (replace_pred_l atm lP (list_Var (length lP) y) lcond).
Proof.
  induction m; intros n atm atm2 lP lcond y x W Iv Ip Ir Hnum Hleb Hat (* Hbox1 *) Hbox2.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
    simpl in *. rewrite Hat. apply iff_refl.

    destruct n.
    destruct atm; try discriminate.
    simpl in *. rewrite Hat. apply iff_refl.

    destruct atm; try discriminate.
(*     destruct f as [xn]. destruct xn. discriminate. *)
    destruct atm; try discriminate.
    destruct atm1; try discriminate.
    simpl in Hat.
    destruct atm2; try discriminate.
    destruct atm2; try discriminate.
    destruct atm2_1; try discriminate.
    inversion Hat as [[H1 H2 H3 H4]].
    do 2 rewrite rep_pred_l_allFO.
    do 2 rewrite SOturnst_allFO.
    pose proof (BOXATM_flag_strong_allFO_eq _ _ _ _ _ Hbox2) as H.
    rewrite H in *.

    split; intros SOt d;
      specialize (SOt d);
      rewrite rep_pred_l_implSO in *;
      intros SOt2; specialize (SOt SOt2).

      rewrite <- H4 in SOt.
      apply (IHm (num_conn atm3) atm3 atm2_2 _ lcond _ f1 _); try assumption.
reflexivity.

simpl in Hnum.
inversion Hnum as [Hnum']. rewrite Hnum in *.
    apply leb_suc_l. assumption.


    simpl in Hnum. inversion Hnum as [Hnum'].
    simpl in Hleb. rewrite Hnum' in Hleb. destruct m. discriminate.

      apply BOXATM_flag_strong_cons in Hbox2.
      apply try3 in Hbox2.
      rewrite Hbox2. assumption.

      apply BOXATM_flag_strong_cons in Hbox2. assumption.

      rewrite <- H4.
      apply (IHm (num_conn atm3) atm3 atm2_2 _ lcond _ f1); try assumption.
reflexivity.

simpl in Hnum.
inversion Hnum as [Hnum']. rewrite Hnum in *.
    apply leb_suc_l. assumption.

      apply BOXATM_flag_strong_cons in Hbox2.
      apply try3 in Hbox2.
      rewrite Hbox2. assumption.

      apply BOXATM_flag_strong_cons in Hbox2. assumption.
Qed.

Lemma sS_lem_e22_pre2_num_conn_pre_num_conn_BAT : forall m n atm atm2 lP lcond y x W Iv Ip Ir,
    n = num_conn atm ->
  Nat.leb n m = true ->
  atm2 = (fun5'' (batm_comp_P atm) (batm_comp_x1 atm) (batm_comp_lx atm)) ->
  BOXATM_flag_weak atm  x= true ->
  SOturnst W Iv Ip Ir (replace_pred_l atm2 lP (list_Var (length lP) y) lcond) <->
  SOturnst W Iv Ip Ir (replace_pred_l atm lP (list_Var (length lP) y) lcond).
Proof.
  induction m; intros n atm atm2 lP lcond y x W Iv Ip Ir Hnum Hleb Hat (* Hbox1 *) Hbox2.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
    simpl in *. rewrite Hat. apply iff_refl.

    destruct n.
    destruct atm; try discriminate.
    simpl in *. rewrite Hat. apply iff_refl.

    destruct atm; try discriminate.
(*     destruct f as [xn]. destruct xn. discriminate. *)
    destruct atm; try discriminate.
    destruct atm1; try discriminate.
    simpl in Hat.
    destruct atm2; try discriminate.
    destruct atm2; try discriminate.
    destruct atm2_1; try discriminate.
    inversion Hat as [[H1 H2 H3 H4]].
    do 2 rewrite rep_pred_l_allFO.
    do 2 rewrite SOturnst_allFO.
    pose proof (BOXATM_flag_weak_allFO_eq _ _ _ _ _ Hbox2) as H.
    rewrite H in *.

    split; intros SOt d;
      specialize (SOt d);
      rewrite rep_pred_l_implSO in *;
      intros SOt2; specialize (SOt SOt2).

      rewrite <- H4 in SOt.
      apply (IHm (num_conn atm3) atm3 atm2_2 _ lcond _ f1 _); try assumption.
reflexivity.

simpl in Hnum.
inversion Hnum as [Hnum']. rewrite Hnum in *.
    apply leb_suc_l. assumption.


    simpl in Hnum. inversion Hnum as [Hnum'].
    simpl in Hleb. rewrite Hnum' in Hleb. destruct m. discriminate.

      apply BOXATM_flag_weak_cons in Hbox2.
      apply try3_BAT in Hbox2.
      rewrite Hbox2. assumption.

      apply BOXATM_flag_weak_cons in Hbox2. assumption.

      rewrite <- H4.
      apply (IHm (num_conn atm3) atm3 atm2_2 _ lcond _ f1); try assumption.
reflexivity.

simpl in Hnum.
inversion Hnum as [Hnum']. rewrite Hnum in *.
    apply leb_suc_l. assumption.

      apply BOXATM_flag_weak_cons in Hbox2.
      apply try3_BAT in Hbox2.
      rewrite Hbox2. assumption.

      apply BOXATM_flag_weak_cons in Hbox2. assumption.
Qed.


Lemma sS_lem_e22_pre2_num_conn_pre : forall atm atm2 lP lcond y x W Iv Ip Ir,
  atm2 = (fun5'' (batm_comp_P atm) (batm_comp_x1 atm) (batm_comp_lx atm)) ->
  BOXATM_flag_strong atm  x= true ->
  SOturnst W Iv Ip Ir (replace_pred_l atm2 lP (list_Var (length lP) y) lcond) <->
  SOturnst W Iv Ip Ir (replace_pred_l atm lP (list_Var (length lP) y) lcond).
Proof.
  intros atm; intros until 0.
  apply (sS_lem_e22_pre2_num_conn_pre_num_conn (num_conn atm) (num_conn atm) atm).
  reflexivity.
  apply leb_refl.
Qed.

Lemma sS_lem_e22_pre2_num_conn_pre_BAT : forall atm atm2 lP lcond y x W Iv Ip Ir,
  atm2 = (fun5'' (batm_comp_P atm) (batm_comp_x1 atm) (batm_comp_lx atm)) ->
  BOXATM_flag_weak atm  x= true ->
  SOturnst W Iv Ip Ir (replace_pred_l atm2 lP (list_Var (length lP) y) lcond) <->
  SOturnst W Iv Ip Ir (replace_pred_l atm lP (list_Var (length lP) y) lcond).
Proof.
  intros atm; intros until 0.
  apply (sS_lem_e22_pre2_num_conn_pre_num_conn_BAT (num_conn atm) (num_conn atm) atm).
  reflexivity.
  apply leb_refl.
Qed.

(* Left it here 24/11/17 *)
(* Just keep going down and copying from sSahlq4_4 or vsSahlq_instant19
any needed lemmas and alter them. *)

Lemma sS_lem_e22_pre2_num_conn : forall m n atm atm2 lP lcond y W Iv Ip Ir,
    n = num_conn atm ->
  Nat.leb n m = true ->
  atm2 = (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm)) ->
  is_BOXATM_flag_strong_CONJ atm = true ->
  SOturnst W Iv Ip Ir (replace_pred_l atm2 lP (list_Var (length lP) y) lcond) <->
  SOturnst W Iv Ip Ir (replace_pred_l atm lP (list_Var (length lP) y) lcond).
Proof.
  induction m ; intros n atm atm3 lP lcond y W Iv Ip Ir Hnum Hleb Hat1 (* Hat2 *) Hat3; try discriminate.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
    rewrite Hat1. simpl. apply iff_refl.

    destruct n.
    destruct atm; try discriminate.
    rewrite Hat1. simpl. apply iff_refl.

    destruct atm; try discriminate.
      destruct f as [xn]. destruct xn. discriminate.
      destruct atm; try discriminate.
      destruct atm1; try discriminate.

    simpl in Hat1. destruct atm3; try discriminate.
    inversion Hat1 as [[Hat1a Hat1b]].
    destruct atm3; try discriminate.
    inversion Hat1b as [[Hat1c Hat1d]].
    do 2 rewrite rep_pred_l_allFO.
    do 2 rewrite SOturnst_allFO.
    split; intros SOt d; 
      rewrite rep_pred_l_implSO in *;
      rewrite SOturnst_implSO in *;
      intros SOt2;
      rewrite rep_pred_l_relatSO in *;
      pose proof (is_BOXATM_flag_strong_CONJ_allFO_eq _ _ _ _ Hat3) as Heq;
      rewrite Heq in *; 
      specialize (SOt d SOt2).
      apply (sS_lem_e22_pre2_num_conn_pre atm2 atm3_2 _ lcond _ f0).

      apply is_BOXATM_flag_strong__CONJ in Hat3.
      apply try3 in Hat3. rewrite Hat3. assumption.
 
      apply is_BOXATM_flag_strong__CONJ in Hat3. assumption.

      rewrite Hat1d.
      assumption.

      rewrite <- Hat1d.
      apply (sS_lem_e22_pre2_num_conn_pre atm2 atm3_2 _ lcond _ f0).

      apply is_BOXATM_flag_strong__CONJ in Hat3.
      apply try3 in Hat3. rewrite Hat3. assumption.
 
      apply is_BOXATM_flag_strong__CONJ in Hat3. assumption.

      assumption.


    simpl in Hat1.
    rewrite Hat1.
    split; intros SOt.
      apply fun5_l''_rep_pred_l_app in SOt.
      rewrite rep_pred_l_conjSO in *.
      rewrite SOturnst_conjSO in *.
      apply conj.
        apply (IHm (num_conn atm1) atm1 
          (fun5_l'' (batm_conj_comp_P atm1) (batm_conj_comp_x1 atm1) 
              (batm_conj_comp_lx atm1))).
        reflexivity.

      simpl in Hnum. inversion Hnum as [Hnum'].
      rewrite Hnum' in *.
      apply leb_plus_take1 in Hleb. assumption.


        reflexivity.
        apply is_BOXATM_flag_strong_CONJ_conjSO_l in Hat3. assumption.
        apply SOt.

        apply (IHm (num_conn atm2) atm2 
          (fun5_l'' (batm_conj_comp_P atm2) (batm_conj_comp_x1 atm2) 
              (batm_conj_comp_lx atm2))).
        reflexivity.

      simpl in Hnum. inversion Hnum as [Hnum'].
      rewrite Hnum' in *.
      apply leb_plus_take2 in Hleb. assumption.

        reflexivity.
        apply is_BOXATM_flag_strong_CONJ_conjSO_r in Hat3. assumption.
        apply SOt.

        apply length_batm_conj_comp_P_x1. 
        apply is_BOXATM_flag_strong_CONJ_conjSO_l in Hat3. assumption.

        apply length_batm_conj_comp_P_lx. 
        apply is_BOXATM_flag_strong_CONJ_conjSO_l in Hat3. assumption.


      apply fun5_l''_rep_pred_l_app.
      rewrite rep_pred_l_conjSO in *.
      rewrite SOturnst_conjSO in *.
        apply length_batm_conj_comp_P_x1. 
        apply is_BOXATM_flag_strong_CONJ_conjSO_l in Hat3. assumption.

        apply length_batm_conj_comp_P_lx. 
        apply is_BOXATM_flag_strong_CONJ_conjSO_l in Hat3. assumption.

      rewrite rep_pred_l_conjSO in *.
      rewrite SOturnst_conjSO in *.
      apply conj.
        apply (IHm (num_conn atm1) atm1 
          (fun5_l'' (batm_conj_comp_P atm1) (batm_conj_comp_x1 atm1) 
              (batm_conj_comp_lx atm1))).
        reflexivity.

      simpl in Hnum. inversion Hnum as [Hnum'].
      rewrite Hnum' in *.
      apply leb_plus_take1 in Hleb. assumption.

        reflexivity.
        apply is_BOXATM_flag_strong_CONJ_conjSO_l in Hat3. assumption.
        apply SOt.

        apply (IHm (num_conn atm2) atm2 
          (fun5_l'' (batm_conj_comp_P atm2) (batm_conj_comp_x1 atm2) 
              (batm_conj_comp_lx atm2))).
        reflexivity.

      simpl in Hnum. inversion Hnum as [Hnum'].
      rewrite Hnum' in *.
      apply leb_plus_take2 in Hleb. assumption.

        reflexivity.
        apply is_BOXATM_flag_strong_CONJ_conjSO_r in Hat3. assumption.
        apply SOt.
Qed.

Lemma sS_lem_e22_pre2_num_conn_BAT : forall m n atm atm2 lP lcond y W Iv Ip Ir,
    n = num_conn atm ->
  Nat.leb n m = true ->
  atm2 = (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm)) ->
  BAT atm = true ->
  SOturnst W Iv Ip Ir (replace_pred_l atm2 lP (list_Var (length lP) y) lcond) <->
  SOturnst W Iv Ip Ir (replace_pred_l atm lP (list_Var (length lP) y) lcond).
Proof.
  induction m ; intros n atm atm3 lP lcond y W Iv Ip Ir Hnum Hleb Hat1 (* Hat2 *) Hat3; try discriminate.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
    rewrite Hat1. simpl. apply iff_refl.

    destruct n.
    destruct atm; try discriminate.
    rewrite Hat1. simpl. apply iff_refl.

    destruct atm; try discriminate.
      destruct f as [xn]. (*  destruct xn. discriminate. *)
      destruct atm; try discriminate.
      destruct atm1; try discriminate.

    simpl in Hat1. destruct atm3; try discriminate.
    inversion Hat1 as [[Hat1a Hat1b]].
    destruct atm3; try discriminate.
    inversion Hat1b as [[Hat1c Hat1d]].
    do 2 rewrite rep_pred_l_allFO.
    do 2 rewrite SOturnst_allFO.
    split; intros SOt d; 
      rewrite rep_pred_l_implSO in *;
      rewrite SOturnst_implSO in *;
      intros SOt2;
      rewrite rep_pred_l_relatSO in *;
      pose proof (is_BOXATM_flag_strong_CONJ_allFO_eq_BAT _ _ _ _ Hat3) as Heq;
      rewrite Heq in *; 
      specialize (SOt d SOt2).
      apply (sS_lem_e22_pre2_num_conn_pre_BAT atm2 atm3_2 _ lcond _ f0).

      apply is_BOXATM_flag_strong__CONJ_BAT in Hat3.
      apply try3_BAT in Hat3. rewrite Hat3. assumption.
 
      apply is_BOXATM_flag_strong__CONJ_BAT in Hat3. assumption.

      rewrite Hat1d.
      assumption.

      rewrite <- Hat1d.
      apply (sS_lem_e22_pre2_num_conn_pre_BAT atm2 atm3_2 _ lcond _ f0).

      apply is_BOXATM_flag_strong__CONJ_BAT in Hat3.
      apply try3_BAT in Hat3. rewrite Hat3. assumption.
 
      apply is_BOXATM_flag_strong__CONJ_BAT in Hat3. assumption.

      assumption.


    simpl in Hat1.
    rewrite Hat1.
    split; intros SOt.
      apply fun5_l''_rep_pred_l_app in SOt.
      rewrite rep_pred_l_conjSO in *.
      rewrite SOturnst_conjSO in *.
      apply conj.
        apply (IHm (num_conn atm1) atm1 
          (fun5_l'' (batm_conj_comp_P atm1) (batm_conj_comp_x1 atm1) 
              (batm_conj_comp_lx atm1))).
        reflexivity.

      simpl in Hnum. inversion Hnum as [Hnum'].
      rewrite Hnum' in *.
      apply leb_plus_take1 in Hleb. assumption.


        reflexivity.
        apply BAT_conjSO_l in Hat3. assumption.
        apply SOt.

        apply (IHm (num_conn atm2) atm2 
          (fun5_l'' (batm_conj_comp_P atm2) (batm_conj_comp_x1 atm2) 
              (batm_conj_comp_lx atm2))).
        reflexivity.

      simpl in Hnum. inversion Hnum as [Hnum'].
      rewrite Hnum' in *.
      apply leb_plus_take2 in Hleb. assumption.

        reflexivity.
        apply BAT_conjSO_r in Hat3. assumption.
        apply SOt.

        apply length_batm_conj_comp_P_x1_BAT. 
        apply BAT_conjSO_l in Hat3. assumption.

        apply length_batm_conj_comp_P_lx_BAT. 
        apply BAT_conjSO_l in Hat3. assumption.


      apply fun5_l''_rep_pred_l_app.
      rewrite rep_pred_l_conjSO in *.
      rewrite SOturnst_conjSO in *.
        apply length_batm_conj_comp_P_x1_BAT. 
        apply BAT_conjSO_l in Hat3. assumption.

        apply length_batm_conj_comp_P_lx_BAT .
        apply BAT_conjSO_l in Hat3. assumption.

      rewrite rep_pred_l_conjSO in *.
      rewrite SOturnst_conjSO in *.
      apply conj.
        apply (IHm (num_conn atm1) atm1 
          (fun5_l'' (batm_conj_comp_P atm1) (batm_conj_comp_x1 atm1) 
              (batm_conj_comp_lx atm1))).
        reflexivity.

      simpl in Hnum. inversion Hnum as [Hnum'].
      rewrite Hnum' in *.
      apply leb_plus_take1 in Hleb. assumption.

        reflexivity.
        apply BAT_conjSO_l in Hat3. assumption.
        apply SOt.

        apply (IHm (num_conn atm2) atm2 
          (fun5_l'' (batm_conj_comp_P atm2) (batm_conj_comp_x1 atm2) 
              (batm_conj_comp_lx atm2))).
        reflexivity.

      simpl in Hnum. inversion Hnum as [Hnum'].
      rewrite Hnum' in *.
      apply leb_plus_take2 in Hleb. assumption.

        reflexivity.
        apply BAT_conjSO_r in Hat3. assumption.
        apply SOt.
Qed.

Lemma sS_lem_e22_pre2 : forall atm atm2 lP lcond y W Iv Ip Ir,
  atm2 = (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm)) ->
  is_BOXATM_flag_strong_CONJ atm = true ->
  SOturnst W Iv Ip Ir (replace_pred_l atm2 lP (list_Var (length lP) y) lcond) <->
  SOturnst W Iv Ip Ir (replace_pred_l atm lP (list_Var (length lP) y) lcond).
Proof.
  intros until 0.
  apply (sS_lem_e22_pre2_num_conn (num_conn atm) (num_conn atm)).
  reflexivity. apply leb_refl.
Qed.

Lemma sS_lem_e22_pre2_BAT : forall atm atm2 lP lcond y W Iv Ip Ir,
  atm2 = (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm)) ->
  BAT atm = true ->
  SOturnst W Iv Ip Ir (replace_pred_l atm2 lP (list_Var (length lP) y) lcond) <->
  SOturnst W Iv Ip Ir (replace_pred_l atm lP (list_Var (length lP) y) lcond).
Proof.
  intros until 0.
  apply (sS_lem_e22_pre2_num_conn_BAT (num_conn atm) (num_conn atm)).
  reflexivity. apply leb_refl.
Qed.

Lemma BOXATM_flag_strong_fun5''_num_conn : forall m n atm x,
    n = num_conn atm ->
  Nat.leb n m = true ->
BOXATM_flag_strong atm x = true ->
BOXATM_flag_strong (fun5'' (batm_comp_P atm) (batm_comp_x1 atm) (batm_comp_lx atm))
  (batm_comp_x1 atm) = true.
Proof.
  induction m; intros n atm x Hnum Hleb Hbox.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
    simpl in *. destruct f. symmetry. apply beq_nat_refl.

    destruct n.
    destruct atm; try discriminate.
    simpl in *. destruct f. symmetry. apply beq_nat_refl.

    destruct atm; try discriminate.
    destruct atm; try discriminate.
    destruct atm1; try discriminate.
    simpl batm_comp_P. simpl batm_comp_x1.
    simpl batm_comp_lx.
    destruct f as [z1]; destruct f0 as [z2]; destruct f1 as [z3].
    simpl. do 2 rewrite <- beq_nat_refl.
    pose proof (BOXATM_flag_strong_cons _ _ _ _ _ Hbox) as H2.
    pose proof (try3 _ _ H2) as H1.
    pose proof (BOXATM_flag_strong_allFO_eq _ _ _ _ _ Hbox) as H3.
    rewrite H3 in *. rewrite <- H1. 
    rewrite (IHm (num_conn atm2) atm2 (Var z3)).
    apply is_BOXATM_flag_strong__CONJ2 in Hbox.
    apply try6 in Hbox. unfold next_FOvar in Hbox.
    simpl in Hbox. rewrite H1 in Hbox. inversion Hbox as [Hbox'].
    rewrite Hbox'.  inversion H3 as [H3']. rewrite <- beq_nat_refl.
    reflexivity.

    reflexivity.

simpl in Hnum.
inversion Hnum as [Hnum']. rewrite Hnum' in *.
    apply leb_suc_l. assumption. assumption.
Qed.

Lemma BOXATM_flag_strong_fun5'' : forall atm x,
BOXATM_flag_strong atm x = true ->
BOXATM_flag_strong (fun5'' (batm_comp_P atm) (batm_comp_x1 atm) (batm_comp_lx atm))
  (batm_comp_x1 atm) = true.
Proof.
  intros atm x. apply (BOXATM_flag_strong_fun5''_num_conn (num_conn atm) (num_conn atm)).
  reflexivity. apply leb_refl.
Qed.

Lemma BOXATM_flag_strong_fun5''_num_conn_BAT : forall m n atm x,
    n = num_conn atm ->
  Nat.leb n m = true ->
BOXATM_flag_weak atm x = true ->
BOXATM_flag_weak (fun5'' (batm_comp_P atm) (batm_comp_x1 atm) (batm_comp_lx atm))
  (batm_comp_x1 atm) = true.
Proof.
  induction m; intros n atm x Hnum Hleb Hbox.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
    simpl in *. destruct f. symmetry. apply beq_nat_refl.

    destruct n.
    destruct atm; try discriminate.
    simpl in *. destruct f. symmetry. apply beq_nat_refl.

    destruct atm; try discriminate.
    destruct atm; try discriminate.
    destruct atm1; try discriminate.
    simpl batm_comp_P. simpl batm_comp_x1.
    simpl batm_comp_lx.
    destruct f as [z1]; destruct f0 as [z2]; destruct f1 as [z3].
    simpl. do 2 rewrite <- beq_nat_refl.
    pose proof (BOXATM_flag_weak_cons _ _ _ _ _ Hbox) as H2.
    pose proof (try3_BAT _ _ H2) as H1.
    pose proof (BOXATM_flag_weak_allFO_eq _ _ _ _ _ Hbox) as H3.
    rewrite H3 in *. rewrite <- H1. 
    rewrite (IHm (num_conn atm2) atm2 (Var z3)).
    apply is_BOXATM_flag_strong__CONJ2_BAT in Hbox. all : try  reflexivity.

simpl in Hnum.
inversion Hnum as [Hnum']. rewrite Hnum' in *.
    apply leb_suc_l. assumption. assumption.
Qed.

Lemma BOXATM_flag_strong_fun5''_BAT : forall atm x,
BOXATM_flag_weak atm x = true ->
BOXATM_flag_weak (fun5'' (batm_comp_P atm) (batm_comp_x1 atm) (batm_comp_lx atm))
  (batm_comp_x1 atm) = true.
Proof.
  intros atm x. apply (BOXATM_flag_strong_fun5''_num_conn_BAT (num_conn atm) (num_conn atm)).
  reflexivity. apply leb_refl.
Qed.

Lemma is_BOXATM_flag_strong_CONJ_fun5_l''_app : forall la1 lb1 lc1 la2 lb2 lc2,
  length la1 = length lb1 ->
  length la1 = length lc1 ->
  is_BOXATM_flag_strong_CONJ
      (fun5_l'' la1 lb1 lc1) = true ->
  is_BOXATM_flag_strong_CONJ
      (fun5_l'' la2 lb2 lc2) = true ->
  is_BOXATM_flag_strong_CONJ
      (fun5_l'' (app la1 la2) (app lb1 lb2) (app lc1 lc2)) = true.
Proof.
  induction la1; intros lb1 lc1 la2 lb2 lc2 Hl1 Hl2 Hb1 Hb2.
    simpl in *. destruct lb1. destruct lc1. assumption.
    all : try discriminate.

    destruct lb1. discriminate. destruct lc1. discriminate.
    simpl in *.
    case_eq la1.
      intros Hnil; rewrite Hnil in *.
      destruct lb1. 2 : discriminate.
      destruct lc1. 2 : discriminate.
      simpl in *.
      destruct la2. destruct lb2. assumption.
      assumption. destruct lb2. assumption.
      destruct lc2. assumption.

      simpl in *. rewrite Hb1. assumption.

      intros P lP Hla1. rewrite <- Hla1.
      case_eq lb1.
        intros Hnil. rewrite Hnil in *.
        rewrite Hla1 in *. discriminate.
      intros x lx Hlb1. rewrite <- Hlb1.
      case_eq lc1.
        intros Hnil. rewrite Hnil in *.
        rewrite Hla1 in *. discriminate. 
      intros lc ll Hlc1. rewrite <- Hlc1.
      case_eq (app la1 la2).
        rewrite Hla1. discriminate.
      intros PP lPP HlPP. rewrite <- HlPP.
      case_eq (app lb1 lb2).
        rewrite Hlb1. discriminate.
      intros xx lxx Hlxx. rewrite <- Hlxx.
      case_eq (app lc1 lc2).
        rewrite Hlc1. discriminate.
      intros llv lllv Hlllv. rewrite <- Hlllv.
      simpl in *. rewrite Hla1 in *. rewrite Hlb1 in *.
      rewrite Hlc1 in *. rewrite <- Hla1 in * .
      rewrite <- Hlb1 in *. rewrite <- Hlc1 in *.
      rewrite (is_BOXATM_flag_strong_CONJ_conjSO_l _ _ Hb1).
      apply IHla1.
        inversion Hl1. reflexivity.
        inversion Hl2. reflexivity.

      apply (is_BOXATM_flag_strong_CONJ_conjSO_r _ _ Hb1).
      assumption.
Qed.

Lemma is_BOXATM_flag_strong_CONJ_fun5_l''_app_BAT : forall la1 lb1 lc1 la2 lb2 lc2,
  length la1 = length lb1 ->
  length la1 = length lc1 ->
  BAT
      (fun5_l'' la1 lb1 lc1) = true ->
  BAT
      (fun5_l'' la2 lb2 lc2) = true ->
  BAT
      (fun5_l'' (app la1 la2) (app lb1 lb2) (app lc1 lc2)) = true.
Proof.
  induction la1; intros lb1 lc1 la2 lb2 lc2 Hl1 Hl2 Hb1 Hb2.
    simpl in *. destruct lb1. destruct lc1. assumption.
    all : try discriminate.

    destruct lb1. discriminate. destruct lc1. discriminate.
    simpl in *.
    case_eq la1.
      intros Hnil; rewrite Hnil in *.
      destruct lb1. 2 : discriminate.
      destruct lc1. 2 : discriminate.
      simpl in *.
      destruct la2. destruct lb2. assumption.
      assumption. destruct lb2. assumption.
      destruct lc2. assumption.

      simpl in *. rewrite Hb1. assumption.

      intros P lP Hla1. rewrite <- Hla1.
      case_eq lb1.
        intros Hnil. rewrite Hnil in *.
        rewrite Hla1 in *. discriminate.
      intros x lx Hlb1. rewrite <- Hlb1.
      case_eq lc1.
        intros Hnil. rewrite Hnil in *.
        rewrite Hla1 in *. discriminate. 
      intros lc ll Hlc1. rewrite <- Hlc1.
      case_eq (app la1 la2).
        rewrite Hla1. discriminate.
      intros PP lPP HlPP. rewrite <- HlPP.
      case_eq (app lb1 lb2).
        rewrite Hlb1. discriminate.
      intros xx lxx Hlxx. rewrite <- Hlxx.
      case_eq (app lc1 lc2).
        rewrite Hlc1. discriminate.
      intros llv lllv Hlllv. rewrite <- Hlllv.
      simpl in *. rewrite Hla1 in *. rewrite Hlb1 in *.
      rewrite Hlc1 in *. rewrite <- Hla1 in * .
      rewrite <- Hlb1 in *. rewrite <- Hlc1 in *.
      rewrite (BAT_conjSO_l _ _ Hb1).
      apply IHla1.
        inversion Hl1. reflexivity.
        inversion Hl2. reflexivity.

      apply (BAT_conjSO_r _ _ Hb1).
      assumption.
Qed.


Lemma is_BOXATM_flag_strong_CONJ_fun5_l'' : forall atm atm2,
is_BOXATM_flag_strong_CONJ atm = true ->
atm2 = fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm) ->
is_BOXATM_flag_strong_CONJ atm2 = true.
Proof.
  induction atm; intros atm0 Hbox Hat; try discriminate.
    rewrite Hat. reflexivity.

    destruct f as [xn]. destruct xn. discriminate.
    destruct atm; try discriminate.
    destruct atm1; try discriminate.
    apply is__BOXATM_flag_strong_CONJ in Hbox.
    apply is_BOXATM_flag_strong__CONJ2 with (x := f).
    rewrite Hat. simpl fun5_l''.
    apply BOXATM_flag_strong_fun5'' in Hbox.
    simpl in Hbox. assumption.

    pose proof Hbox as Hbox'.
      apply is_BOXATM_flag_strong_CONJ_conjSO_l in Hbox.
    simpl in Hat. rewrite Hat.
    apply is_BOXATM_flag_strong_CONJ_fun5_l''_app.
    apply length_batm_conj_comp_P_x1. assumption.
    apply length_batm_conj_comp_P_lx. assumption.
    apply IHatm1. assumption. reflexivity.
    apply IHatm2. apply is_BOXATM_flag_strong_CONJ_conjSO_r in Hbox'.
      assumption.
    reflexivity.
Qed.

Lemma is_BOXATM_flag_strong_CONJ_fun5_l''_BAT : forall atm atm2,
BAT atm = true ->
atm2 = fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm) ->
BAT atm2 = true.
Proof.
  induction atm; intros atm0 Hbox Hat; try discriminate.
    rewrite Hat. reflexivity.

    destruct f as [xn].  (*  destruct xn. discriminate. *)
    destruct atm; try discriminate.
    destruct atm1; try discriminate.
    apply is__BAT in Hbox.
    apply is_BOXATM_flag_strong__CONJ2_BAT with (x := f).
    rewrite Hat. simpl fun5_l''.
    apply BOXATM_flag_strong_fun5''_BAT in Hbox.
    simpl in Hbox. assumption.

    pose proof Hbox as Hbox'.
      apply BAT_conjSO_l in Hbox.
    simpl in Hat. rewrite Hat.
    apply is_BOXATM_flag_strong_CONJ_fun5_l''_app_BAT.
    apply length_batm_conj_comp_P_x1_BAT. assumption.
    apply length_batm_conj_comp_P_lx_BAT. assumption.
    apply IHatm1. assumption. reflexivity.
    apply IHatm2. apply BAT_conjSO_r in Hbox'.
      assumption.
    reflexivity.
Qed.

Lemma sS_lem_e22 : forall lP atm atm2  y W Iv Ip Ir,
is_in_FOvar (Var 0) (FOvars_in atm) = false ->
  is_BOXATM_flag_strong_CONJ atm = true ->
  atm2 = (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm)) ->
  SOturnst W Iv Ip Ir (replace_pred_l atm2 lP (list_Var (length lP) y)
    (calc_lP atm2 lP)) <->
  SOturnst W Iv Ip Ir (replace_pred_l atm lP (list_Var (length lP) y)
    (calc_lP atm lP)).
Proof.
  intros until 0. intros Hin Hat1 Hat2.
  split ;intros H. apply (sS_lem_e22_pre _ _ atm atm2);
    try assumption.

    apply (sS_lem_e22_pre2 atm atm2 _ _ _ _ _ _ ); try assumption.

    apply (sS_lem_e22_pre _ _ atm atm2); try assumption.

    apply is_BOXATM_flag_strong_CONJ_fun5_l'' with (atm := atm);
    assumption.

    apply (sS_lem_e22_pre2 atm atm2); assumption.
Qed.

Lemma sS_lem_e22_BAT : forall lP atm atm2  y W Iv Ip Ir,
is_in_FOvar (Var 0) (FOvars_in atm) = false ->
  BAT atm = true ->
  atm2 = (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm)) ->
  SOturnst W Iv Ip Ir (replace_pred_l atm2 lP (list_Var (length lP) y)
    (calc_lP atm2 lP)) <->
  SOturnst W Iv Ip Ir (replace_pred_l atm lP (list_Var (length lP) y)
    (calc_lP atm lP)).
Proof.
  intros until 0. intros Hin Hat1 Hat2.
  split ;intros H. apply (sS_lem_e22_pre_BAT _ _ atm atm2);
    try assumption.

    apply (sS_lem_e22_pre2_BAT atm atm2 _ _ _ _ _ _ ); try assumption.

    apply (sS_lem_e22_pre_BAT _ _ atm atm2); try assumption.

    apply is_BOXATM_flag_strong_CONJ_fun5_l''_BAT with (atm := atm);
    assumption.

    apply (sS_lem_e22_pre2_BAT atm atm2); assumption.
Qed.

Lemma sS_lem_e2 : forall lP beta rel atm y xn W1 Iv1 Ip1 Ir1,
  REL rel = true ->
is_BOXATM_flag_strong_CONJ atm = true ->
ex_FOvar_x_ll y (FOv_att_P_l atm lP) = false ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  attached_allFO_x beta (Var xn) = false ->
  attached_exFO_x beta (Var xn) = false ->
  closed_except beta (Var xn) ->
is_in_FOvar (Var 0) (FOvars_in atm) = false ->
(*   length lP = length llx1 ->
length llx1 = length lllv -> *)

  x_occ_in_alpha (instant_cons_empty' (conjSO rel atm) beta) (Var xn) = true ->
  is_in_pred_l (preds_in (implSO (conjSO rel atm) beta)) lP = true ->
SOturnst W1 Iv1 Ip1 Ir1
  (replace_pred_l
     (implSO (conjSO rel atm)
        (newnew_pre (instant_cons_empty' (conjSO rel atm) beta) (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
           (rev_seq (S (Nat.max (max_FOv (implSO (conjSO rel atm) beta)) xn))
              (length (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn)))))) lP (list_Var (length lP) y)
     (calc_lP atm lP)) <->
SOturnst W1 Iv1 Ip1 Ir1
  (replace_pred_l
     (implSO (conjSO rel (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm)))
        (newnew_pre (instant_cons_empty' (conjSO rel (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm))) beta)
           (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm))) beta))
              (Var xn))
           (rev_seq (S (Nat.max (max_FOv (implSO (conjSO rel (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm))) beta)) xn))
              (length
                 (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm))) beta))
                    (Var xn)))))) lP (list_Var (length lP) y)
     (calc_lP (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm)) lP)).
Proof.
  intros lP  beta rel atm y xn W Iv Ip Ir Hrel Hat Hex2 Hun Hno Hat1 Hat2 Hc Hin3 (* Hl1 Hl2 *) Hocc Hin.
  rewrite sS_lem_e3.
  do 2 rewrite rep_pred_l_implSO.
  do 2 rewrite rep_pred_l_conjSO.
  all : try assumption.
assert (is_in_FOvar (Var 0) (batm_conj_comp_x1 atm) = false) as Hass.
  rewrite is_BOXATM_CONJ_is_in_batm_conj_equiv; assumption.

  split ;intros SOt [H1 H2].

(*     rewrite (new_FOv_pp_pre2_fun5_l'2 _ Hat Hass) in *. *)
    rewrite max_FOv_fun5_l''.
apply sS_lem_e5; try assumption.

apply SOQFree_newnew_pre.
 apply SOQFree_instant_cons_empty'.
  assumption.

    apply SOt.
    rewrite SOturnst_conjSO. apply conj.

      rewrite rep_pred_l_REL; try assumption.
      rewrite rep_pred_l_REL in H1; try assumption.
      apply (sS_lem_e22 _ atm (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm))).

      all : try assumption.
      reflexivity.


    rewrite max_FOv_fun5_l'' in SOt.
apply sS_lem_e5; try assumption.

apply SOQFree_newnew_pre.
 apply SOQFree_instant_cons_empty'.
  assumption.

    apply SOt.
    rewrite SOturnst_conjSO. apply conj.

      rewrite rep_pred_l_REL; try assumption.
      rewrite rep_pred_l_REL in H1; try assumption.
      apply (sS_lem_e22 _ atm (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm))).

      all : try assumption.
      reflexivity.
Qed.

Lemma sS_lem_e2_BAT : forall lP beta rel atm y xn W1 Iv1 Ip1 Ir1,
  REL rel = true ->
BAT atm = true ->
ex_FOvar_x_ll y (FOv_att_P_l atm lP) = false ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  attached_allFO_x beta (Var xn) = false ->
  attached_exFO_x beta (Var xn) = false ->
  closed_except beta (Var xn) ->
is_in_FOvar (Var 0) (FOvars_in atm) = false ->
(*   length lP = length llx1 ->
length llx1 = length lllv -> *)

  x_occ_in_alpha (instant_cons_empty' (conjSO rel atm) beta) (Var xn) = true ->
  is_in_pred_l (preds_in (implSO (conjSO rel atm) beta)) lP = true ->
SOturnst W1 Iv1 Ip1 Ir1
  (replace_pred_l
     (implSO (conjSO rel atm)
        (newnew_pre (instant_cons_empty' (conjSO rel atm) beta) (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
           (rev_seq (S (Nat.max (max_FOv (implSO (conjSO rel atm) beta)) xn))
              (length (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn)))))) lP (list_Var (length lP) y)
     (calc_lP atm lP)) <->
SOturnst W1 Iv1 Ip1 Ir1
  (replace_pred_l
     (implSO (conjSO rel (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm)))
        (newnew_pre (instant_cons_empty' (conjSO rel (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm))) beta)
           (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm))) beta))
              (Var xn))
           (rev_seq (S (Nat.max (max_FOv (implSO (conjSO rel (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm))) beta)) xn))
              (length
                 (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm))) beta))
                    (Var xn)))))) lP (list_Var (length lP) y)
     (calc_lP (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm)) lP)).
Proof.
  intros lP  beta rel atm y xn W Iv Ip Ir Hrel Hat Hex2 Hun Hno Hat1 Hat2 Hc Hin3 (* Hl1 Hl2 *) Hocc Hin.
  rewrite sS_lem_e3_BAT.
  do 2 rewrite rep_pred_l_implSO.
  do 2 rewrite rep_pred_l_conjSO.
  all : try assumption.
(* assert (is_in_FOvar (Var 0) (batm_conj_comp_x1 atm) = false) as Hass.
admit. *)
(*   rewrite is_BOXATM_CONJ_is_in_batm_conj_equiv; assumption. *)

  split ;intros SOt [H1 H2].

(*     rewrite (new_FOv_pp_pre2_fun5_l'2 _ Hat Hass) in *. *)
    rewrite max_FOv_fun5_l''_BAT.
apply sS_lem_e5_BAT; try assumption.

apply SOQFree_newnew_pre.
 apply SOQFree_instant_cons_empty'.
  assumption.

    apply SOt.
    rewrite SOturnst_conjSO. apply conj.

      rewrite rep_pred_l_REL; try assumption.
      rewrite rep_pred_l_REL in H1; try assumption.
      apply (sS_lem_e22_BAT _ atm (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm))).

      all : try assumption.
      reflexivity.


    rewrite max_FOv_fun5_l''_BAT in SOt.
apply sS_lem_e5_BAT; try assumption.

apply SOQFree_newnew_pre.
 apply SOQFree_instant_cons_empty'.
  assumption.

    apply SOt.
    rewrite SOturnst_conjSO. apply conj.

      rewrite rep_pred_l_REL; try assumption.
      rewrite rep_pred_l_REL in H1; try assumption.
      apply (sS_lem_e22_BAT _ atm (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm))).

      all : try assumption.
      reflexivity.
Qed.

Lemma SOQFree_is_BOXATM_flag_strong_CONJ_pre : 
forall (m n : nat) (batm : SecOrder),
  n = num_conn batm ->
  Nat.leb n m = true ->
  is_BOXATM_flag_strong_CONJ batm = true ->
  SOQFree batm = true.
Proof.
  induction m; intros n batm Hnum Hleb Hbox.
    destruct n. 2 : discriminate.
    destruct batm; try discriminate.
    destruct p. destruct f. reflexivity.

    destruct n.
    destruct batm; try discriminate.
    destruct p. destruct f. reflexivity.

    destruct batm; try discriminate.
    destruct f as [xn]. destruct xn. discriminate.
    destruct batm; try discriminate. destruct batm1; try discriminate.
    simpl in *. destruct f as [z1]; destruct f0 as [z2].
    destruct z2. rewrite if_then_else_false in Hbox. discriminate.
    case_eq (beq_nat xn z1); intros Hbeq; rewrite Hbeq in *.
      2 : discriminate.
     case_eq (beq_nat xn z2); intros Hbeq2; rewrite Hbeq2 in *.
      2 : discriminate.
    case_eq (beq_nat (S z2) (S z1)); intros Hbeq3; rewrite Hbeq3 in *.
      2 : discriminate.
    apply is_BOXATM_flag_strong__CONJ2 in Hbox.
    destruct n. discriminate.
    apply (IHm n batm2). inversion Hnum. reflexivity.
    apply leb_suc_l. assumption. assumption.

    simpl. pose proof (is_BOXATM_flag_strong_CONJ_conjSO_l _ _ Hbox) as Hbox1.
    simpl. pose proof (is_BOXATM_flag_strong_CONJ_conjSO_r _ _ Hbox) as Hbox2.
    rewrite (IHm (num_conn batm1) batm1).
    rewrite (IHm (num_conn batm2) batm2).
    all : try reflexivity. all : try assumption.

    simpl in Hnum. inversion Hnum as [Hnum'].
    simpl in Hleb. rewrite Hnum' in Hleb.
    apply leb_plus_take2 in Hleb. assumption.

    simpl in Hnum. inversion Hnum as [Hnum'].
    simpl in Hleb. rewrite Hnum' in Hleb.
    apply leb_plus_take1 in Hleb. assumption.
Qed.

Lemma SOQFree_is_BOXATM_flag_strong_CONJ : 
forall (batm : SecOrder),
  is_BOXATM_flag_strong_CONJ batm = true ->
  SOQFree batm = true.
Proof.
  intros batm. apply (SOQFree_is_BOXATM_flag_strong_CONJ_pre (num_conn batm) (num_conn batm)).
  reflexivity. apply leb_refl.
Qed.

Lemma batm_comp_P_conj : forall atm x,
  BOXATM_flag_strong atm x = true ->
  batm_conj_comp_P atm = cons (batm_comp_P atm) nil.
Proof.
  destruct atm; intros x H; try discriminate;
    reflexivity.
Qed.

Lemma batm_comp_x1_conj : forall atm x,
  BOXATM_flag_strong atm x = true ->
  batm_conj_comp_x1 atm = cons (batm_comp_x1 atm) nil.
Proof.
  destruct atm; intros x H; try discriminate;
    reflexivity.
Qed.

Lemma batm_comp_P_conj_BAT : forall atm x,
  BOXATM_flag_weak atm x = true ->
  batm_conj_comp_P atm = cons (batm_comp_P atm) nil.
Proof.
  destruct atm; intros x H; try discriminate;
    reflexivity.
Qed.

Lemma batm_comp_x1_conj_BAT : forall atm x,
  BOXATM_flag_weak atm x = true ->
  batm_conj_comp_x1 atm = cons (batm_comp_x1 atm) nil.
Proof.
  destruct atm; intros x H; try discriminate;
    reflexivity.
Qed.

Lemma batm_comp_ln_conj : forall atm x,
  BOXATM_flag_strong atm x = true ->
  batm_conj_comp_ln atm = cons (batm_comp_ln atm) nil.
Proof.
  destruct atm; intros x H; try discriminate;
    reflexivity.
Qed.

Lemma batm_conj__comp_P_pre : forall m n atm x,
  n = num_conn atm ->
  Nat.leb n m = true ->
  BOXATM_flag_strong atm x = true ->
  batm_conj_comp_P atm = cons (batm_comp_P atm) nil.
Proof.
  induction m; intros n atm x Hnum Hleb Hbox.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
    simpl in *. reflexivity.

    destruct n. 
    destruct atm; try discriminate.
    simpl in *. reflexivity.

    simpl in *. destruct atm; try discriminate.
    destruct atm; try discriminate.
    destruct atm1; try discriminate.
    simpl. reflexivity.
Qed.

Lemma batm_conj__comp_P : forall atm x,
  BOXATM_flag_strong atm x = true ->
  batm_conj_comp_P atm = cons (batm_comp_P atm) nil.
Proof.
  intros atm x. apply (batm_conj__comp_P_pre (num_conn atm) (num_conn atm)).
  reflexivity. apply leb_refl.
Qed.

Lemma batm_conj__comp_P_pre_BAT : forall m n atm x,
  n = num_conn atm ->
  Nat.leb n m = true ->
  BOXATM_flag_weak atm x = true ->
  batm_conj_comp_P atm = cons (batm_comp_P atm) nil.
Proof.
  induction m; intros n atm x Hnum Hleb Hbox.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
    simpl in *. reflexivity.

    destruct n. 
    destruct atm; try discriminate.
    simpl in *. reflexivity.

    simpl in *. destruct atm; try discriminate.
    destruct atm; try discriminate.
    destruct atm1; try discriminate.
    simpl. reflexivity.
Qed.

Lemma batm_conj__comp_P_BAT : forall atm x,
  BOXATM_flag_weak atm x = true ->
  batm_conj_comp_P atm = cons (batm_comp_P atm) nil.
Proof.
  intros atm x. apply (batm_conj__comp_P_pre_BAT (num_conn atm) (num_conn atm)).
  reflexivity. apply leb_refl.
Qed.

Lemma batm_conj_comp_P_preds_in_pre : forall m n atm,
  n = num_conn atm ->
  Nat.leb n m = true ->
  is_BOXATM_flag_strong_CONJ atm = true ->
  batm_conj_comp_P atm = preds_in atm.
Proof.
  induction m; intros n atm Hnum Hleb Hbox.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
    simpl in *. destruct p. destruct f. reflexivity.
  
    destruct n.
    destruct atm; try discriminate.
    simpl in *. destruct p. destruct f. reflexivity.

    destruct atm; try discriminate.
    destruct f as [xn]. destruct xn. discriminate.
    destruct atm; try discriminate.
    destruct atm1; try discriminate.
    simpl. destruct f. destruct f0. simpl.
    apply is_BOXATM_flag_strong__CONJ in Hbox.
    pose proof (is_BOXATM_flag_strong__CONJ2 _ _ Hbox).
    rewrite <- (IHm (num_conn atm2) atm2). 
    rewrite batm_conj__comp_P with (x := (Var (S xn))).
    all : try reflexivity. all : try assumption.
    simpl in Hnum. inversion Hnum. rewrite Hnum in Hleb.
    simpl in Hleb. destruct m. discriminate.
    apply leb_suc_r. assumption.

    pose proof (is_BOXATM_flag_strong_CONJ_conjSO_l _ _ Hbox).
    pose proof (is_BOXATM_flag_strong_CONJ_conjSO_r _ _ Hbox).
    simpl in Hnum. inversion Hnum as [Hnum'].
    rewrite Hnum' in Hleb.
    simpl. rewrite (IHm (num_conn atm1) atm1).
    simpl. rewrite (IHm (num_conn atm2) atm2).    
    all : try reflexivity.
    all : try assumption.

      apply leb_plus_take2 in Hleb. assumption.
      apply leb_plus_take1 in Hleb. assumption.
Qed.

Lemma batm_conj_comp_P_preds_in : forall atm,
  is_BOXATM_flag_strong_CONJ atm = true ->
  batm_conj_comp_P atm = preds_in atm.
Proof.
  intros atm H.
  apply (batm_conj_comp_P_preds_in_pre (num_conn atm) (num_conn atm)).
  reflexivity. apply leb_refl. assumption.
Qed.

Lemma batm_conj_comp_P_preds_in_pre_BAT : forall m n atm,
  n = num_conn atm ->
  Nat.leb n m = true ->
  BAT atm = true ->
  batm_conj_comp_P atm = preds_in atm.
Proof.
  induction m; intros n atm Hnum Hleb Hbox.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
    simpl in *. destruct p. destruct f. reflexivity.
  
    destruct n.
    destruct atm; try discriminate.
    simpl in *. destruct p. destruct f. reflexivity.

    destruct atm; try discriminate.
    destruct f as [xn]. (*  destruct xn. discriminate. *)
    destruct atm; try discriminate.
    destruct atm1; try discriminate.
    simpl. destruct f. destruct f0. simpl.
    apply is_BOXATM_flag_strong__CONJ_BAT in Hbox.
    pose proof (is_BOXATM_flag_strong__CONJ2_BAT _ _ Hbox).
    rewrite <- (IHm (num_conn atm2) atm2). 
    rewrite batm_conj__comp_P_BAT with (x := (Var (xn))).
    all : try reflexivity. all : try assumption.
    simpl in Hnum. inversion Hnum. rewrite Hnum in Hleb.
    simpl in Hleb. destruct m. discriminate.
    apply leb_suc_r. assumption.

    pose proof (BAT_conjSO_l _ _ Hbox).
    pose proof (BAT_conjSO_r _ _ Hbox).
    simpl in Hnum. inversion Hnum as [Hnum'].
    rewrite Hnum' in Hleb.
    simpl. rewrite (IHm (num_conn atm1) atm1).
    simpl. rewrite (IHm (num_conn atm2) atm2).    
    all : try reflexivity.
    all : try assumption.

      apply leb_plus_take2 in Hleb. assumption.
      apply leb_plus_take1 in Hleb. assumption.
Qed.

Lemma batm_conj_comp_P_preds_in_BAT : forall atm,
  BAT atm = true ->
  batm_conj_comp_P atm = preds_in atm.
Proof.
  intros atm H.
  apply (batm_conj_comp_P_preds_in_pre_BAT (num_conn atm) (num_conn atm)).
  reflexivity. apply leb_refl. assumption.
Qed.

Lemma batm_comp_lx_conj : forall atm x,
  BOXATM_flag_strong atm x = true ->
  batm_conj_comp_lx atm = cons (batm_comp_lx atm) nil.
Proof.
  destruct atm; intros x H; try discriminate;
    reflexivity.
Qed.

Lemma batm_comp_lx_conj_BAT : forall atm x,
  BOXATM_flag_weak atm x = true ->
  batm_conj_comp_lx atm = cons (batm_comp_lx atm) nil.
Proof.
  destruct atm; intros x H; try discriminate;
    reflexivity.
Qed.

Lemma fun2_fun5_l''_app : forall l1a l1b l2a l2b l3a l3b P,
  length l1a = length l2a ->
  length l1a = length l3a ->
  fun2 (fun5_l'' (app l1a l1b) (app l2a l2b) (app l3a l3b)) P =
  app (fun2 (fun5_l'' l1a l2a l3a) P) (fun2 (fun5_l'' l1b l2b l3b) P).
Proof.
  induction l1a; intros l1b l2a l2b l3a l3b P Hl1 Hl2.
    destruct l2a. destruct l3a. all : try discriminate. reflexivity.

    destruct l2a. discriminate. destruct l3a. discriminate.
    do 3 rewrite <- app_comm_cons.
    case_eq l1a. intros Hl1a. rewrite Hl1a in *. destruct l2a.
      destruct l3a. all : try discriminate.
      simpl. destruct l1b. destruct l2b. simpl. rewrite app_nil_r.
        reflexivity.

        simpl. rewrite app_nil_r. reflexivity.

        destruct l2b. simpl. destruct l1b; rewrite app_nil_r; reflexivity.
        destruct l3b. simpl. destruct l1b; destruct l2b; rewrite app_nil_r;
        reflexivity.

        reflexivity.

      intros Q l1a' Hl1a. rewrite <- Hl1a.
      rewrite fun5_l''_cons. rewrite fun5_l''_cons.
      simpl. rewrite IHl1a. rewrite app_assoc. reflexivity.
      inversion Hl1. reflexivity.
      inversion Hl2. reflexivity.   
      rewrite Hl1a. discriminate.
      rewrite Hl1a in *. destruct l2a; discriminate.
      rewrite Hl1a in *. destruct l3a; discriminate.
      rewrite Hl1a in *. discriminate.
      rewrite Hl1a in *. destruct l2a; discriminate.
      rewrite Hl1a in *. destruct l3a; discriminate.
Qed.


Lemma fun2_fun5_l''_pre  : forall m n atm P,
  n = num_conn atm ->
  Nat.leb n m = true ->
is_BOXATM_flag_strong_CONJ atm = true ->
fun2
  (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm)) P =
fun2 atm P.
Proof.
  induction m; intros n atm [Pn] Hnum Hleb Hbox.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
    destruct p as [Qm]. destruct f as [xn].
    simpl. reflexivity.

    destruct n. 
    destruct atm; try discriminate.
    destruct p as [Qm]. destruct f as [xn].
    simpl. reflexivity.

    destruct atm; try discriminate.
    destruct f as [xn]. destruct xn. discriminate.
    destruct atm; try discriminate.
    destruct atm1; try discriminate.
    pose proof (is_BOXATM_flag_strong_CONJ_allFO_x1 _ _ _ _ Hbox) as Hbox1.
    pose proof (is_BOXATM_flag_strong_CONJ_allFO_relatSO _ _ _ _ Hbox) as Hbox2.
    pose proof (is_BOXATM_flag_strong_CONJ_allFO_atm _ _ _ _ Hbox) as Hbox3.
    apply next_FOvar_match in Hbox2.
    simpl.
    pose proof (is_BOXATM_flag_strong_CONJ_allFO_eq _ _ _ _ Hbox) as Hbox4.
    rewrite Hbox4. rewrite <- Hbox1.
assert (Nat.leb (num_conn atm2) m = true) as Hnum3.

    inversion Hnum as [Hnum'].
    rewrite Hnum' in Hleb.
    destruct m. discriminate. apply leb_suc_r. assumption.

    apply is_BOXATM_flag_strong__CONJ in Hbox.
    apply is_BOXATM_flag_strong__CONJ2 in Hbox3.
    specialize (IHm (num_conn atm2) atm2 (Pred Pn) eq_refl Hnum3 Hbox3).
    rewrite batm_comp_P_conj with (x := (Var (S xn)))in IHm.
    rewrite batm_comp_x1_conj with (x := (Var (S xn)))in IHm.
    rewrite batm_comp_lx_conj with (x := (Var (S xn)))in IHm.
    simpl in IHm. assumption. all : try assumption.

    pose proof (is_BOXATM_flag_strong_CONJ_conjSO_l _ _ Hbox) as Hbox1.
    pose proof (is_BOXATM_flag_strong_CONJ_conjSO_r _ _ Hbox) as Hbox2.
    simpl. rewrite fun2_fun5_l''_app. rewrite (IHm (num_conn atm1) atm1).
    rewrite (IHm (num_conn atm2) atm2). reflexivity.
    all : try reflexivity. all : try assumption.
      simpl in Hnum. inversion Hnum as [Hnum'].
      rewrite Hnum' in *.
      apply leb_plus_take2 in Hleb. assumption.
      simpl in Hnum. inversion Hnum as [Hnum'].
      rewrite Hnum' in *.
      apply leb_plus_take1 in Hleb. assumption.

      apply length_batm_conj_comp_P_x1. assumption.
      apply length_batm_conj_comp_P_lx. assumption.
Qed.

Lemma fun2_fun5_l''_pre_BAT  : forall m n atm P,
  n = num_conn atm ->
  Nat.leb n m = true ->
BAT atm = true ->
fun2
  (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm)) P =
fun2 atm P.
Proof.
  induction m; intros n atm [Pn] Hnum Hleb Hbox.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
    destruct p as [Qm]. destruct f as [xn].
    simpl. reflexivity.

    destruct n. 
    destruct atm; try discriminate.
    destruct p as [Qm]. destruct f as [xn].
    simpl. reflexivity.

    destruct atm; try discriminate.
    destruct f as [xn]. (*  destruct xn. discriminate. *)
    destruct atm; try discriminate.
    destruct atm1; try discriminate.
(* Search BAT allFO. *)
    pose proof (is_BOXATM_flag_strong_CONJ_allFO_x1_BAT _ _ _ _ Hbox) as Hbox1.
(*     pose proof (is_BOXATM_flag_strong_CONJ_allFO_relatSO_BAT _ _ _ _ Hbox) as Hbox2. *)
    pose proof (is_BOXATM_flag_strong_CONJ_allFO_atm_BAT _ _ _ _ Hbox) as Hbox3.
(*     apply next_FOvar_match in Hbox2.
    simpl. *)
    pose proof (is_BOXATM_flag_strong_CONJ_allFO_eq_BAT _ _ _ _ Hbox) as Hbox4.
    rewrite Hbox4. rewrite <- Hbox1.
assert (Nat.leb (num_conn atm2) m = true) as Hnum3.

    inversion Hnum as [Hnum'].
    rewrite Hnum' in Hleb.
    destruct m. discriminate. apply leb_suc_r. assumption.

    apply is_BOXATM_flag_strong__CONJ_BAT in Hbox.
    apply is_BOXATM_flag_strong__CONJ2_BAT in Hbox3.
    specialize (IHm (num_conn atm2) atm2 (Pred Pn) eq_refl Hnum3 Hbox3).
    rewrite batm_comp_P_conj_BAT with (x := (Var (xn)))in IHm.
    rewrite batm_comp_x1_conj_BAT with (x := (Var (xn)))in IHm.
    rewrite batm_comp_lx_conj_BAT with (x := (Var xn))in IHm.
    simpl in IHm. assumption. all : try assumption.


    pose proof (BAT_conjSO_l _ _ Hbox) as Hbox1.
    pose proof (BAT_conjSO_r _ _ Hbox) as Hbox2.
    simpl. rewrite fun2_fun5_l''_app. rewrite (IHm (num_conn atm1) atm1).
    rewrite (IHm (num_conn atm2) atm2). reflexivity.
    all : try reflexivity. all : try assumption.
      simpl in Hnum. inversion Hnum as [Hnum'].
      rewrite Hnum' in *.
      apply leb_plus_take2 in Hleb. assumption.
      simpl in Hnum. inversion Hnum as [Hnum'].
      rewrite Hnum' in *.
      apply leb_plus_take1 in Hleb. assumption.

      apply length_batm_conj_comp_P_x1_BAT. assumption.
      apply length_batm_conj_comp_P_lx_BAT. assumption.
Qed.

Lemma fun2_fun5_l''  : forall atm P,
is_BOXATM_flag_strong_CONJ atm = true ->
fun2
  (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm)) P =
fun2 atm P.
Proof.
  intros atm P.
  apply (fun2_fun5_l''_pre (num_conn atm) (num_conn atm)).
  reflexivity.
  apply leb_refl.
Qed.

Lemma fun2_fun5_l''_BAT  : forall atm P,
BAT atm = true ->
fun2
  (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm)) P =
fun2 atm P.
Proof.
  intros atm P.
  apply (fun2_fun5_l''_pre_BAT (num_conn atm) (num_conn atm)).
  reflexivity.
  apply leb_refl.
Qed.


Lemma FOv_att_P_l_fun5_l'' : forall lP atm,
is_BOXATM_flag_strong_CONJ atm = true ->
(FOv_att_P_l
     (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm)
        (batm_conj_comp_lx atm)) lP) =
(FOv_att_P_l atm lP).
Proof.
  induction lP; intros atm H. reflexivity.
  simpl. rewrite IHlP.
    simpl. rewrite fun2_fun5_l''.
    reflexivity.
    all : assumption.
Qed.

Lemma FOv_att_P_l_fun5_l''_BAT : forall lP atm,
BAT atm = true ->
(FOv_att_P_l
     (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm)
        (batm_conj_comp_lx atm)) lP) =
(FOv_att_P_l atm lP).
Proof.
  induction lP; intros atm H. reflexivity.
  simpl. rewrite IHlP.
    simpl. rewrite fun2_fun5_l''_BAT.
    reflexivity.
    all : assumption.
Qed.

Lemma lem1 : forall atm rel xn beta,
REL rel = true ->
is_BOXATM_flag_strong_CONJ atm = true ->
attached_allFO_x beta (Var xn) = false ->
attached_exFO_x beta (Var xn) = false ->
closed_except beta (Var xn) ->
x_occ_in_alpha (instant_cons_empty' (conjSO rel atm) beta) (Var xn) = true ->

x_occ_in_alpha
  (instant_cons_empty'
     (conjSO rel
        (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm)
           (batm_conj_comp_lx atm))) beta) (Var xn) = true.
Proof.
  intros until 0. intros Hrel Hbox Hat1 Hat2 Hcl Hocc.
  unfold instant_cons_empty' in *. simpl in *.
  rewrite (preds_in_rel rel Hrel) in *. simpl in *.
  rewrite sS_lem_e4. assumption.
  assumption.
Qed.

Lemma lem1_BAT : forall atm rel xn beta,
REL rel = true ->
BAT atm = true ->
attached_allFO_x beta (Var xn) = false ->
attached_exFO_x beta (Var xn) = false ->
closed_except beta (Var xn) ->
x_occ_in_alpha (instant_cons_empty' (conjSO rel atm) beta) (Var xn) = true ->

x_occ_in_alpha
  (instant_cons_empty'
     (conjSO rel
        (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm)
           (batm_conj_comp_lx atm))) beta) (Var xn) = true.
Proof.
  intros until 0. intros Hrel Hbox Hat1 Hat2 Hcl Hocc.
  unfold instant_cons_empty' in *. simpl in *.
  rewrite (preds_in_rel rel Hrel) in *. simpl in *.
  rewrite sS_lem_e4_BAT. assumption.
  assumption.
Qed.

Lemma preds_in_fun5'' : forall ln P x,
  preds_in (fun5'' P x ln) =
  cons P nil.
Proof.
  induction ln; intros [Pn] [xn]. reflexivity.
  simpl. rewrite IHln. destruct a. reflexivity.
Qed.

Lemma is_BOXATM_flag_strong_CONJ_preds_in_pre : forall m n atm,
  n = num_conn atm ->
  Nat.leb n m = true ->
  is_BOXATM_flag_strong_CONJ atm = true ->
  preds_in (fun5_l'' (batm_conj_comp_P atm)
    (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm)) =
  batm_conj_comp_P atm.
Proof.
  induction m; intros n atm Hnum Hleb Hbox.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
      simpl in *. destruct p. destruct f. reflexivity.

    destruct n.
    destruct atm; try discriminate.
      simpl in *. destruct p. destruct f. reflexivity.

    destruct atm; try discriminate.
      destruct f as [xn]. destruct xn. discriminate.
      destruct atm; try discriminate.
      destruct atm1; try discriminate.
      simpl. destruct f as [y1].
      simpl. rewrite preds_in_fun5''. reflexivity.

    simpl in Hnum. inversion Hnum as [Hnum'].
    rewrite Hnum' in Hleb. simpl in Hleb. simpl.
    pose proof (is_BOXATM_flag_strong_CONJ_conjSO_l _ _ Hbox) as Hbox1.
    pose proof (is_BOXATM_flag_strong_CONJ_conjSO_r _ _ Hbox) as Hbox2.
      simpl. rewrite preds_in_fun5_l''_app.
      rewrite (IHm (num_conn atm1) atm1).
      rewrite (IHm (num_conn atm2) atm2).     
      all: try reflexivity. all : try assumption.
      apply leb_plus_take2 in Hleb; assumption.
      apply leb_plus_take1 in Hleb. assumption.
      apply length_batm_conj_comp_P_x1. assumption.
      apply length_batm_conj_comp_P_lx. assumption.
Qed.

Lemma is_BOXATM_flag_strong_CONJ_preds_in : forall atm,
  is_BOXATM_flag_strong_CONJ atm = true ->
  preds_in (fun5_l'' (batm_conj_comp_P atm)
    (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm)) =
  batm_conj_comp_P atm.
Proof.
  intros atm. apply (is_BOXATM_flag_strong_CONJ_preds_in_pre (num_conn atm) (num_conn atm)).
  reflexivity. apply leb_refl.
Qed.

Lemma is_BOXATM_flag_strong_CONJ_preds_in_pre_BAT : forall m n atm,
  n = num_conn atm ->
  Nat.leb n m = true ->
  BAT atm = true ->
  preds_in (fun5_l'' (batm_conj_comp_P atm)
    (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm)) =
  batm_conj_comp_P atm.
Proof.
  induction m; intros n atm Hnum Hleb Hbox.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
      simpl in *. destruct p. destruct f. reflexivity.

    destruct n.
    destruct atm; try discriminate.
      simpl in *. destruct p. destruct f. reflexivity.

    destruct atm; try discriminate.
      destruct f as [xn]. (*  destruct xn. discriminate. *)
      destruct atm; try discriminate.
      destruct atm1; try discriminate.
      simpl. destruct f as [y1].
      simpl. rewrite preds_in_fun5''. reflexivity.

    simpl in Hnum. inversion Hnum as [Hnum'].
    rewrite Hnum' in Hleb. simpl in Hleb. simpl.
    pose proof (BAT_conjSO_l _ _ Hbox) as Hbox1.
    pose proof (BAT_conjSO_r _ _ Hbox) as Hbox2.
      simpl. rewrite preds_in_fun5_l''_app.
      rewrite (IHm (num_conn atm1) atm1).
      rewrite (IHm (num_conn atm2) atm2).     
      all: try reflexivity. all : try assumption.
      apply leb_plus_take2 in Hleb; assumption.
      apply leb_plus_take1 in Hleb. assumption.
      apply length_batm_conj_comp_P_x1_BAT. assumption.
      apply length_batm_conj_comp_P_lx_BAT. assumption.
Qed.

Lemma is_BOXATM_flag_strong_CONJ_preds_in_BAT : forall atm,
  BAT atm = true ->
  preds_in (fun5_l'' (batm_conj_comp_P atm)
    (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm)) =
  batm_conj_comp_P atm.
Proof.
  intros atm. apply (is_BOXATM_flag_strong_CONJ_preds_in_pre_BAT (num_conn atm) (num_conn atm)).
  reflexivity. apply leb_refl.
Qed.


Lemma sS_lem118'_is_in_pred_l:  forall lP (atm : SecOrder),
  is_BOXATM_flag_strong_CONJ atm = true ->
  is_in_pred_l  (preds_in (fun5_l''
    (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm))) lP =
  is_in_pred_l (preds_in atm) lP.
Proof.
  intros lP atm H.
  rewrite is_BOXATM_flag_strong_CONJ_preds_in.
  rewrite batm_conj_comp_P_preds_in. reflexivity.
  all : assumption.
Qed. 

Lemma sS_lem118'_is_in_pred_l_BAT:  forall lP (atm : SecOrder),
  BAT atm = true ->
  is_in_pred_l  (preds_in (fun5_l''
    (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm))) lP =
  is_in_pred_l (preds_in atm) lP.
Proof.
  intros lP atm H.
  rewrite is_BOXATM_flag_strong_CONJ_preds_in_BAT.
  rewrite batm_conj_comp_P_preds_in_BAT. reflexivity.
  all : assumption.
Qed. 

Lemma lem2 : forall atm rel lP beta,
REL rel = true ->
is_BOXATM_flag_strong_CONJ atm = true ->
SOQFree beta = true ->
is_in_pred_l (preds_in (implSO (conjSO rel atm) beta)) lP = true ->
is_in_pred_l
  (preds_in
     (implSO
        (conjSO rel
           (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm)
              (batm_conj_comp_lx atm))) beta)) lP = true.
Proof.
  intros atm rel lP beta Hrel Hbox Hno Hin.
  simpl in *. do 2 rewrite is_in_pred_l_app_if in Hin.
  do 2 rewrite is_in_pred_l_app_if.
  rewrite (preds_in_rel rel Hrel) in *. simpl in *. 
  case_eq (is_in_pred_l (preds_in beta) lP ); intros Hin2;
    rewrite Hin2 in *. 2 : rewrite if_then_else_false in Hin.
    2 : discriminate.
  case_eq (is_in_pred_l (preds_in atm) lP); intros Hin3;
    rewrite Hin3 in *. 2 : discriminate.
  rewrite sS_lem118'_is_in_pred_l. rewrite Hin3. reflexivity.
  assumption.
Qed.

Lemma lem2_BAT : forall atm rel lP beta,
REL rel = true ->
BAT atm = true ->
SOQFree beta = true ->
is_in_pred_l (preds_in (implSO (conjSO rel atm) beta)) lP = true ->
is_in_pred_l
  (preds_in
     (implSO
        (conjSO rel
           (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm)
              (batm_conj_comp_lx atm))) beta)) lP = true.
Proof.
  intros atm rel lP beta Hrel Hbox Hno Hin.
  simpl in *. do 2 rewrite is_in_pred_l_app_if in Hin.
  do 2 rewrite is_in_pred_l_app_if.
  rewrite (preds_in_rel rel Hrel) in *. simpl in *. 
  case_eq (is_in_pred_l (preds_in beta) lP ); intros Hin2;
    rewrite Hin2 in *. 2 : rewrite if_then_else_false in Hin.
    2 : discriminate.
  case_eq (is_in_pred_l (preds_in atm) lP); intros Hin3;
    rewrite Hin3 in *. 2 : discriminate.
  rewrite sS_lem118'_is_in_pred_l_BAT. rewrite Hin3. reflexivity.
  assumption.
Qed.
