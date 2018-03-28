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
Require Import sSahlq3_5_plus_3 sSahlq_preprocessing1_added sSahlq4_7_plus_I.



Lemma is_in_FOvar_0_batm_pre'' : forall m n atm x,
n = num_conn atm ->
Nat.leb n m = true ->
  BOXATM_flag_strong atm x = true ->
  ~ (batm_comp_x1 atm) = (Var 0) ->
  is_in_FOvar (Var 0) (FOvars_in (fun5'' (batm_comp_P atm)
    (batm_comp_x1 atm) (batm_comp_lx atm))) = false.
Proof.
  induction m; intros n atm x Hnum Hleb Hbox Hnot.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
    simpl in *. destruct x as [xn]. destruct f as [ym].
    destruct ym. contradiction (Hnot eq_refl).
    reflexivity.

    destruct n. 
    destruct atm; try discriminate.
    simpl in *. destruct x as [xn]. destruct f as [ym].
    destruct ym. contradiction (Hnot eq_refl).
    reflexivity.

    simpl in Hleb. destruct atm; try discriminate.
    simpl in Hnum. inversion Hnum as [Hnum'].
    destruct atm; try discriminate.
    destruct atm1; try discriminate.
    pose proof Hbox as Hbox'.
    simpl. destruct f0 as [y1]. destruct f1 as [y2].
    simpl. destruct y1. simpl in *. contradiction (Hnot eq_refl).
    simpl in Hbox. destruct x as [xn].
    destruct f as [y3]. case_eq (beq_nat y2 (S (S y1)));
      intros Hbeq; rewrite Hbeq in *.

destruct y3. simpl in *. destruct y2. discriminate.
rewrite if_then_else_false in Hbox. discriminate.

(*     rewrite <-(beq_nat_true _ _ Hbeq). *)
(* pose proof is_BOXATM_flag_strong_CONJ_allFO_x1. *)
    case_eq (beq_nat (S y3) y2); intros Hbeq2; rewrite Hbeq2 in *.
      2 : rewrite if_then_else_false in Hbox. 2: discriminate.
    rewrite (beq_nat_true _ _ Hbeq2).
    rewrite <- (is_BOXATM_flag_strong_CONJ_allFO_x1 atm2 (Var (S y3)) (Var (S y1)) (Var y2)).
    apply (IHm (num_conn atm2) _ (Var y2)). reflexivity.

    simpl in Hnum'.
    rewrite Hnum' in Hleb. apply leb_suc_l. assumption.

    rewrite (beq_nat_true _ _ Hbeq2) in Hbox.
    case_eq (BOXATM_flag_strong atm2 (Var y2)); intros Hbox2.
      reflexivity. rewrite Hbox2 in *. rewrite if_then_else_false in *. discriminate.

    rewrite (is_BOXATM_flag_strong_CONJ_allFO_x1 atm2 (Var (S y3)) (Var (S y1)) (Var y2)).
    rewrite (beq_nat_true _ _ Hbeq). discriminate.
    simpl. destruct y3. simpl in *. destruct y2. discriminate.
    destruct y2. discriminate. discriminate.
    case_eq (PeanoNat.Nat.eqb xn (S y1)); intros H1; rewrite H1 in *.
      2 : discriminate.
    rewrite <- (beq_nat_true _ _ Hbeq2). simpl.
    rewrite <- beq_nat_refl.
    rewrite (beq_nat_true _ _ Hbeq) in Hbeq2. simpl in Hbeq2.
    rewrite Hbeq2. rewrite (beq_nat_true _ _ Hbeq2) in *.
    assumption.

    apply is_BOXATM_flag_strong__CONJ2 in Hbox'. assumption.

simpl. destruct y3. destruct y2. simpl in *. rewrite if_then_else_false in *.
   discriminate. simpl in *.
  rewrite if_then_else_false in Hbox. discriminate.
  case_eq (beq_nat xn (S y1)); intros Hbeq2; rewrite Hbeq2 in *.
    2 : discriminate.
  case_eq (beq_nat (S y3) y2); intros Hbeq3; rewrite Hbeq3 in *.
    2 : discriminate.

  discriminate.
Qed.

Lemma is_in_FOvar_0_batm'' : forall atm x,
  BOXATM_flag_strong atm x = true ->
  ~ (batm_comp_x1 atm) = (Var 0) ->
  is_in_FOvar (Var 0) (FOvars_in (fun5'' (batm_comp_P atm)
    (batm_comp_x1 atm) (batm_comp_lx atm))) = false.
Proof.
  intros atm x.
  apply (is_in_FOvar_0_batm_pre'' (num_conn atm) (num_conn atm)).
  reflexivity.
  apply leb_refl.
Qed.

Lemma FOvars_in_fun5_l''_app : forall la1 la2 lb1 lb2 lc1 lc2,
length la1 = length lb1 ->
length la1 = length lc1 ->
~ la1 = nil ->
~ la2 = nil ->
~ lb2 = nil ->
~ lc2 = nil ->
FOvars_in
     (fun5_l'' (app la1 la2) (app lb1 lb2) (app lc1 lc2)) =
app (FOvars_in (fun5_l'' la1 lb1 lc1)) (FOvars_in (fun5_l'' la2 lb2 lc2)).
Proof.
  induction la1; intros la2 lb1 lb2 lc1 lc2 Hl1 Hl2 Hnil1 Hnil2 Hnil3 Hnil4.
    contradiction (Hnil1 eq_refl).

    destruct lb1. discriminate. destruct lc1. discriminate.
    case_eq la1. simpl. intros Hla1.
      rewrite Hla1 in *. destruct lb1. 2 : discriminate.
      destruct lc1. 2 : discriminate.
      simpl. destruct la2. contradiction (Hnil2 eq_refl).
      destruct lb2. contradiction (Hnil3 eq_refl).  simpl.
      destruct lc2. contradiction (Hnil4 eq_refl).
      simpl. reflexivity.

      intros P lP Hla1. rewrite <- Hla1.
      rewrite fun5_l''_cons. do 3 rewrite <- app_comm_cons.
      rewrite fun5_l''_cons. simpl. rewrite IHla1. rewrite app_assoc.
      reflexivity.

      simpl in *. inversion Hl1. reflexivity.
      simpl in *. inversion Hl2. reflexivity.
      rewrite Hla1. discriminate.
      all : try assumption.
      rewrite Hla1. discriminate.
      rewrite Hla1 in *. destruct lb1; discriminate.
      rewrite Hla1 in *. destruct lc1; discriminate.
      rewrite Hla1. discriminate.
      rewrite Hla1 in *. destruct lb1; discriminate.
      rewrite Hla1 in *. destruct lc1; discriminate.
Qed.


Lemma batm_conj_comp_P_ln_nil : forall atm,
is_BOXATM_flag_strong_CONJ atm = true ->
(batm_conj_comp_P atm = nil <->
batm_conj_comp_ln atm = nil).
Proof.
  induction atm; intros H; try discriminate.
    simpl. split; discriminate.

    simpl. split; discriminate.

    simpl. split; intros H2; pose proof H2 as H2'.
      apply app_rnil_l in H2. apply IHatm1 in H2.
      apply app_rnil_r in H2'. apply IHatm2 in H2'.
      rewrite H2. rewrite H2'. reflexivity.

      apply is_BOXATM_flag_strong_CONJ_conjSO_r in H. assumption.
      apply is_BOXATM_flag_strong_CONJ_conjSO_l in H. assumption.

      apply app_rnil_l in H2. apply IHatm1 in H2.
      apply app_rnil_r in H2'. apply IHatm2 in H2'.
      rewrite H2. rewrite H2'. reflexivity.

      apply is_BOXATM_flag_strong_CONJ_conjSO_r in H. assumption.
      apply is_BOXATM_flag_strong_CONJ_conjSO_l in H. assumption.
Qed.

Lemma batm_conj_comp_P_lx_nil : forall atm,
is_BOXATM_flag_strong_CONJ atm = true ->
(batm_conj_comp_P atm = nil <->
batm_conj_comp_lx atm = nil).
Proof.
  induction atm; intros H; try discriminate.
    simpl. split; discriminate.

    simpl. split; discriminate.

    simpl. split; intros H2; pose proof H2 as H2'.
      apply app_rnil_l in H2. apply IHatm1 in H2.
      apply app_rnil_r in H2'. apply IHatm2 in H2'.
      rewrite H2. rewrite H2'. reflexivity.

      apply is_BOXATM_flag_strong_CONJ_conjSO_r in H. assumption.
      apply is_BOXATM_flag_strong_CONJ_conjSO_l in H. assumption.

      apply app_rnil_l in H2. apply IHatm1 in H2.
      apply app_rnil_r in H2'. apply IHatm2 in H2'.
      rewrite H2. rewrite H2'. reflexivity.

      apply is_BOXATM_flag_strong_CONJ_conjSO_r in H. assumption.
      apply is_BOXATM_flag_strong_CONJ_conjSO_l in H. assumption.
Qed.

Lemma batm_conj_comp_P_x1_nil : forall atm,
is_BOXATM_flag_strong_CONJ atm = true ->
(batm_conj_comp_P atm = nil <->
batm_conj_comp_x1 atm = nil).
Proof.
  induction atm; intros H; try discriminate.
    simpl. split; discriminate.

    simpl. split; discriminate.

    simpl. split; intros H2; pose proof H2 as H2'.
      apply app_rnil_l in H2. apply IHatm1 in H2.
      apply app_rnil_r in H2'. apply IHatm2 in H2'.
      rewrite H2. rewrite H2'. reflexivity.

      apply is_BOXATM_flag_strong_CONJ_conjSO_r in H. assumption.
      apply is_BOXATM_flag_strong_CONJ_conjSO_l in H. assumption.

      apply app_rnil_l in H2. apply IHatm1 in H2.
      apply app_rnil_r in H2'. apply IHatm2 in H2'.
      rewrite H2. rewrite H2'. reflexivity.

      apply is_BOXATM_flag_strong_CONJ_conjSO_r in H. assumption.
      apply is_BOXATM_flag_strong_CONJ_conjSO_l in H. assumption.
Qed.

Lemma batm_conj_comp_P_not_nil : forall atm,
is_BOXATM_flag_strong_CONJ atm = true ->
batm_conj_comp_P atm <> nil.
Proof.
  induction atm; intros H; try discriminate.
    simpl in *. intros HH.
    pose proof (app_rnil_l _ _ HH) as H1.
    pose proof (app_rnil_r _ _ HH) as H2.
    rewrite H1 in *. rewrite H2 in *.
    contradiction (IHatm1 (is_BOXATM_flag_strong_CONJ_conjSO_l _ _ H) eq_refl).
Qed.

Lemma batm_conj_comp_P_not_nil_BAT : forall atm,
BAT atm = true ->
batm_conj_comp_P atm <> nil.
Proof.
  induction atm; intros H; try discriminate.
    simpl in *. intros HH.
    pose proof (app_rnil_l _ _ HH) as H1.
    pose proof (app_rnil_r _ _ HH) as H2.
    rewrite H1 in *. rewrite H2 in *.
    contradiction (IHatm1 (BAT_conjSO_l _ _ H) eq_refl).
Qed.

Lemma batm_conj_comp_x1_not_nil_BAT : forall atm,
BAT atm = true ->
batm_conj_comp_x1 atm <> nil.
Proof.
  induction atm; intros H; try discriminate.
    simpl in *. intros HH.
    pose proof (app_rnil_l _ _ HH) as H1.
    pose proof (app_rnil_r _ _ HH) as H2.
    rewrite H1 in *. rewrite H2 in *.
    contradiction (IHatm1 (BAT_conjSO_l _ _ H) eq_refl).
Qed.

Lemma batm_conj_comp_lx_not_nil_BAT : forall atm,
BAT atm = true ->
batm_conj_comp_lx atm <> nil.
Proof.
  induction atm; intros H; try discriminate.
    simpl in *. intros HH.
    pose proof (app_rnil_l _ _ HH) as H1.
    pose proof (app_rnil_r _ _ HH) as H2.
    rewrite H1 in *. rewrite H2 in *.
    contradiction (IHatm1 (BAT_conjSO_l _ _ H) eq_refl).
Qed.


Lemma is_in_FOvar_0_batm_conj_pre''_BAT : forall m n atm,
n = num_conn atm ->
Nat.leb n m = true ->

  BAT atm = true ->
  is_in_FOvar (Var 0) (batm_conj_comp_x1 atm) = false ->
  is_in_FOvar (Var 0) (FOvars_in (fun5_l'' (batm_conj_comp_P atm)
    (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm))) = false.
Proof.
Admitted.
(*
  induction m; intros n atm Hnum Hleb Hbox Hin.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate. assumption.

    destruct n.     destruct atm; try discriminate.
    assumption.

    destruct atm; try discriminate.
    destruct f as [xn].

    destruct atm; try discriminate. destruct atm1; try discriminate.
    simpl. destruct f as [y1]. destruct f0 as [y2].
    destruct y1. simpl in *. discriminate.
    destruct xn. simpl batm_conj_comp_x1 in Hin.
simpl in Hbox. destruct y2.  
pose proof (is_BOXATM_flag_strong_CONJ_allFO_x1 _ _ _ _ Hbox) as Heq.
    pose proof (is_BOXATM_flag_strong_CONJ_allFO_eq _ _ _ _ Hbox) as Heq2.
    pose proof (is_BOXATM_flag_strong_CONJ_allFO_relatSO _ _ _ _ Hbox) as Heq3.
    simpl in Heq3.

    simpl in *. destruct y2. rewrite if_then_else_false in Hbox.
    discriminate.
    inversion Heq2 as [Heq2'].
    rewrite Heq2' in *. rewrite <- beq_nat_refl in Hbox.
    rewrite Heq3 in Hbox. rewrite <- beq_nat_refl in Hbox.
    rewrite Heq3. inversion Heq3 as [Heq3']. rewrite Heq3' in *.
    rewrite <- beq_nat_refl in Hbox. rewrite <- Heq.

    rewrite Heq. rewrite <- Heq.
 apply is_in_FOvar_0_batm'' with (x := (Var (S (S y1)))).
    assumption. intros HH. rewrite HH in *. discriminate.

(* simpl. case_eq ((batm_conj_comp_P atm2)).
  intros H.  simpl. *)
  simpl in *. case_eq (batm_conj_comp_P atm2).
    intros H. pose proof H as H'. 
    apply batm_conj_comp_P_x1_nil in H. rewrite H.
    apply batm_conj_comp_P_lx_nil in H'. rewrite H'.
    simpl. do 3 rewrite app_nil_r. apply (IHm (num_conn atm1) atm1).
    reflexivity.
    simpl in Hnum. inversion Hnum as [Hnum'].
    rewrite Hnum' in Hleb. simpl in Hleb.
    apply leb_plus_take1 in Hleb. assumption.
    apply is_BOXATM_flag_strong_CONJ_conjSO_l in Hbox. assumption.

    simpl in Hin.     rewrite is_in_FOvar_app in *.
    case_eq (is_in_FOvar (Var 0) (batm_conj_comp_x1 atm1));
      intros Hin2; rewrite Hin2 in *. discriminate.
    reflexivity.

    apply is_BOXATM_flag_strong_CONJ_conjSO_r in Hbox. assumption.
    apply is_BOXATM_flag_strong_CONJ_conjSO_r in Hbox. assumption.

    intros P lP HlP. rewrite <- HlP.

    simpl. simpl in Hin. rewrite FOvars_in_fun5_l''_app.
    rewrite is_in_FOvar_app in *.
    rewrite (IHm (num_conn atm1) atm1). apply (IHm (num_conn atm2) atm2).
      all : try reflexivity.

    simpl in Hnum. inversion Hnum as [Hnum'].
    rewrite Hnum' in Hleb. simpl in Hleb.
    apply leb_plus_take2 in Hleb. assumption.

    apply is_BOXATM_flag_strong_CONJ_conjSO_r in Hbox. assumption.

    case_eq (is_in_FOvar (Var 0) (batm_conj_comp_x1 atm1));
      intros Hin2; rewrite Hin2 in *. discriminate.
    assumption.

    simpl in Hnum. inversion Hnum as [Hnum'].
    rewrite Hnum' in Hleb. simpl in Hleb.
    apply leb_plus_take1 in Hleb. assumption.

    apply is_BOXATM_flag_strong_CONJ_conjSO_l in Hbox. assumption.

    case_eq (is_in_FOvar (Var 0) (batm_conj_comp_x1 atm1));
      intros Hin2; rewrite Hin2 in *. discriminate.
    reflexivity.

    apply length_batm_conj_comp_P_x1.
    apply is_BOXATM_flag_strong_CONJ_conjSO_l in Hbox. assumption.

    apply length_batm_conj_comp_P_lx_BAT.
    apply is_BOXATM_flag_strong_CONJ_conjSO_l in Hbox. assumption.

    apply batm_conj_comp_P_not_nil.
    apply is_BOXATM_flag_strong_CONJ_conjSO_l in Hbox. assumption.

    apply batm_conj_comp_P_not_nil.
    apply is_BOXATM_flag_strong_CONJ_conjSO_r in Hbox. assumption.

    case_eq (batm_conj_comp_x1 atm2). intros HH.
      apply batm_conj_comp_P_x1_nil in HH. rewrite HH in *. discriminate.
    apply is_BOXATM_flag_strong_CONJ_conjSO_r in Hbox. assumption.
      discriminate.

    case_eq (batm_conj_comp_lx atm2). intros HH.
      apply batm_conj_comp_P_lx_nil in HH. rewrite HH in *. discriminate.
    apply is_BOXATM_flag_strong_CONJ_conjSO_r in Hbox. assumption.
      discriminate.
Qed.
*)


Lemma is_in_FOvar_0_batm_conj_pre'' : forall m n atm,
n = num_conn atm ->
Nat.leb n m = true ->

  is_BOXATM_flag_strong_CONJ atm = true ->
  is_in_FOvar (Var 0) (batm_conj_comp_x1 atm) = false ->
  is_in_FOvar (Var 0) (FOvars_in (fun5_l'' (batm_conj_comp_P atm)
    (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm))) = false.
Proof.
  induction m; intros n atm Hnum Hleb Hbox Hin.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate. assumption.

    destruct n.     destruct atm; try discriminate.
    assumption.

    destruct atm; try discriminate.
    destruct f as [xn]. destruct xn. discriminate.
    destruct atm; try discriminate. destruct atm1; try discriminate.
    simpl. destruct f as [y1]. destruct f0 as [y2].
    destruct y1. simpl in *. discriminate.
pose proof (is_BOXATM_flag_strong_CONJ_allFO_x1 _ _ _ _ Hbox) as Heq.
    pose proof (is_BOXATM_flag_strong_CONJ_allFO_eq _ _ _ _ Hbox) as Heq2.
    pose proof (is_BOXATM_flag_strong_CONJ_allFO_relatSO _ _ _ _ Hbox) as Heq3.
    simpl in Heq3.

    simpl in *. destruct y2. rewrite if_then_else_false in Hbox.
    discriminate.
    inversion Heq2 as [Heq2'].
    rewrite Heq2' in *. rewrite <- beq_nat_refl in Hbox.
    rewrite Heq3 in Hbox. rewrite <- beq_nat_refl in Hbox.
    rewrite Heq3. inversion Heq3 as [Heq3']. rewrite Heq3' in *.
    rewrite <- beq_nat_refl in Hbox. rewrite <- Heq.

    rewrite Heq. rewrite <- Heq.
 apply is_in_FOvar_0_batm'' with (x := (Var (S (S y1)))).
    assumption. intros HH. rewrite HH in *. discriminate.

(* simpl. case_eq ((batm_conj_comp_P atm2)).
  intros H.  simpl. *)
  simpl in *. case_eq (batm_conj_comp_P atm2).
    intros H. pose proof H as H'. 
    apply batm_conj_comp_P_x1_nil in H. rewrite H.
    apply batm_conj_comp_P_lx_nil in H'. rewrite H'.
    simpl. do 3 rewrite app_nil_r. apply (IHm (num_conn atm1) atm1).
    reflexivity.
    simpl in Hnum. inversion Hnum as [Hnum'].
    rewrite Hnum' in Hleb. simpl in Hleb.
    apply leb_plus_take1 in Hleb. assumption.
    apply is_BOXATM_flag_strong_CONJ_conjSO_l in Hbox. assumption.

    simpl in Hin.     rewrite is_in_FOvar_app in *.
    case_eq (is_in_FOvar (Var 0) (batm_conj_comp_x1 atm1));
      intros Hin2; rewrite Hin2 in *. discriminate.
    reflexivity.

    apply is_BOXATM_flag_strong_CONJ_conjSO_r in Hbox. assumption.
    apply is_BOXATM_flag_strong_CONJ_conjSO_r in Hbox. assumption.

    intros P lP HlP. rewrite <- HlP.

    simpl. simpl in Hin. rewrite FOvars_in_fun5_l''_app.
    rewrite is_in_FOvar_app in *.
    rewrite (IHm (num_conn atm1) atm1). apply (IHm (num_conn atm2) atm2).
      all : try reflexivity.

    simpl in Hnum. inversion Hnum as [Hnum'].
    rewrite Hnum' in Hleb. simpl in Hleb.
    apply leb_plus_take2 in Hleb. assumption.

    apply is_BOXATM_flag_strong_CONJ_conjSO_r in Hbox. assumption.

    case_eq (is_in_FOvar (Var 0) (batm_conj_comp_x1 atm1));
      intros Hin2; rewrite Hin2 in *. discriminate.
    assumption.

    simpl in Hnum. inversion Hnum as [Hnum'].
    rewrite Hnum' in Hleb. simpl in Hleb.
    apply leb_plus_take1 in Hleb. assumption.

    apply is_BOXATM_flag_strong_CONJ_conjSO_l in Hbox. assumption.

    case_eq (is_in_FOvar (Var 0) (batm_conj_comp_x1 atm1));
      intros Hin2; rewrite Hin2 in *. discriminate.
    reflexivity.

    apply length_batm_conj_comp_P_x1.
    apply is_BOXATM_flag_strong_CONJ_conjSO_l in Hbox. assumption.

    apply length_batm_conj_comp_P_lx.
    apply is_BOXATM_flag_strong_CONJ_conjSO_l in Hbox. assumption.

    apply batm_conj_comp_P_not_nil.
    apply is_BOXATM_flag_strong_CONJ_conjSO_l in Hbox. assumption.

    apply batm_conj_comp_P_not_nil.
    apply is_BOXATM_flag_strong_CONJ_conjSO_r in Hbox. assumption.

    case_eq (batm_conj_comp_x1 atm2). intros HH.
      apply batm_conj_comp_P_x1_nil in HH. rewrite HH in *. discriminate.
    apply is_BOXATM_flag_strong_CONJ_conjSO_r in Hbox. assumption.
      discriminate.

    case_eq (batm_conj_comp_lx atm2). intros HH.
      apply batm_conj_comp_P_lx_nil in HH. rewrite HH in *. discriminate.
    apply is_BOXATM_flag_strong_CONJ_conjSO_r in Hbox. assumption.
      discriminate.
Qed.

Lemma if_then_else_ft : forall (a b : bool),
  (if a then b else false) = true ->
  a = true /\ b = true.
Proof.
  intros a b H. case_eq a; intros Ha; rewrite Ha in *.
  apply conj. reflexivity. assumption. discriminate.
Qed.

Lemma BOXATM_flag_strong_cons :
forall (atm : SecOrder) (x y1 y2 z : FOvariable),
    BOXATM_flag_strong (allFO x (implSO (relatSO y1 y2) atm)) z = true ->
    BOXATM_flag_strong atm y2 = true.
Proof.
  intros atm [xn] [y1] [y2] [zn] H.
  simpl in *. destruct xn. destruct y2;
    rewrite if_then_else_false in H; discriminate.
  case_eq (beq_nat zn y1); intros Hbeq; rewrite Hbeq in *.
    2 : discriminate.
  case_eq (beq_nat (S xn) y2); intros Hbeq2; rewrite Hbeq2 in *.
    2 : discriminate.
  case_eq (beq_nat y2 (S y1)); intros Hbeq3; rewrite Hbeq3 in *.
    2 : discriminate.
  rewrite (beq_nat_true _ _ Hbeq2) in *. assumption.
Qed.

Lemma BOXATM_flag_weak_cons :
forall (atm : SecOrder) (x y1 y2 z : FOvariable),
    BOXATM_flag_weak (allFO x (implSO (relatSO y1 y2) atm)) z = true ->
    BOXATM_flag_weak atm y2 = true.
Proof.
  intros atm [xn] [y1] [y2] [zn] H.
  simpl in *. destruct xn.
    destruct y2. simpl in H.
    case_eq (PeanoNat.Nat.eqb zn y1); intros Hbeq;
      rewrite Hbeq in *. 2 : discriminate.
    assumption.

    simpl in H. rewrite if_then_else_false in H. discriminate.

  case_eq (beq_nat zn y1); intros Hbeq; rewrite Hbeq in *.
    2 : discriminate.
  case_eq (beq_nat (S xn) y2); intros Hbeq2; rewrite Hbeq2 in *.
    2 : discriminate.
  rewrite (beq_nat_true _ _ Hbeq2) in *. assumption.
Qed.

Lemma lem_h1_pre: forall m n atm x,
n = num_conn atm ->
Nat.leb n m = true ->
 BOXATM_flag_strong atm x = true ->
 (~ batm_comp_x1 atm = (Var 0)) ->
  is_in_FOvar (Var 0) (FOvars_in atm) = false.
Proof.
  induction m; intros n atm x Hnum Hleb Hbox Hnot.
    destruct n. 2 : discriminate. destruct atm; try discriminate.
     destruct f as [xn]. simpl in *. destruct x as [ym].
      destruct xn. contradiction (Hnot eq_refl). reflexivity.

    destruct n. destruct atm; try discriminate.
     destruct f as [xn]. simpl in *. destruct x as [ym].
      destruct xn. contradiction (Hnot eq_refl). reflexivity.

    pose proof Hbox as Hbox'.
    destruct atm; try discriminate. destruct atm; try discriminate.
    destruct atm1; try discriminate.
    destruct f as [ym]. destruct f0 as [y1]. destruct f1 as [y2].
    simpl. destruct x as [xn]. apply if_then_else_ft in Hbox.
    destruct Hbox as [H1 H2].
    apply if_then_else_ft in H2. destruct H2 as [H2 H3].
    apply if_then_else_ft in H3. destruct H3 as [H3 H4].
    destruct ym. destruct y2; discriminate.
    destruct y1. contradiction (Hnot eq_refl).
    destruct y2. discriminate. apply (IHm (num_conn atm2) atm2 (Var (S ym))).
    reflexivity.

    simpl in Hnum. inversion Hnum as [Hnum'].
    rewrite Hnum' in Hleb.
    simpl in Hleb. destruct m. discriminate.
    apply leb_suc_r. assumption.
 assumption.

    destruct xn.

    discriminate.

pose proof Hbox' as Hbox''.
    apply try7 in Hbox'.
    rewrite <- try6 with (x := (Var (S ym))) (y1 := (Var (S y1))) (y2 := (Var (S y2))).
    rewrite Hbox'. unfold next_FOvar. discriminate.

    simpl. simpl in H1. simpl in H2. simpl in H3. rewrite (beq_nat_true _ _ H2).
    rewrite (beq_nat_true _ _ H3). simpl. rewrite <- beq_nat_refl.
    apply BOXATM_flag_strong_cons in Hbox''. rewrite (beq_nat_true _ _ H3) in *. assumption.
Qed.


Lemma lem_h1: forall atm x,
 BOXATM_flag_strong atm x = true ->
 (~ batm_comp_x1 atm = (Var 0)) ->
  is_in_FOvar (Var 0) (FOvars_in atm) = false.
Proof. 
  intros atm x. apply (lem_h1_pre (num_conn atm) (num_conn atm)).
  reflexivity. apply leb_refl.
Qed.

Lemma is_BOXATM_CONJ_is_in_batm_conj_equiv_pre : forall m n atm,
n = num_conn atm ->
Nat.leb n m = true ->
is_BOXATM_flag_strong_CONJ atm = true ->
is_in_FOvar (Var 0) (batm_conj_comp_x1 atm)  = 
is_in_FOvar (Var 0) (FOvars_in atm).
Proof.
  induction m; intros n atm Hnum Hleb Hbox.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
    destruct f as [zn]. simpl in *. reflexivity.

    destruct n. 
    destruct atm; try discriminate.
    destruct f as [zn]. simpl in *. reflexivity.

    destruct atm; try discriminate. destruct f as [xn].
    destruct xn. discriminate.
    destruct atm; try discriminate. destruct atm1; try discriminate.
    destruct f as [y1]. destruct f0 as [y2]. simpl in *.
    destruct y1. reflexivity.
    destruct y2. rewrite if_then_else_false in Hbox. discriminate.
    rewrite (lem_h1 _ (Var (S xn))). reflexivity.
(*     rewrite (is_in_FOvar_BOXATM_flag_strong (xn)). reflexivity. *)


    apply if_then_else_ft in Hbox. destruct Hbox as [H1 H2].
    apply if_then_else_ft in H2. destruct H2 as [H3 H2].
    apply if_then_else_ft in H2. apply H2.

    rewrite (try3 _ (Var (S xn))). discriminate.
    apply if_then_else_ft in Hbox. destruct Hbox as [H1 H2].
    apply if_then_else_ft in H2. destruct H2 as [H3 H2].
    apply if_then_else_ft in H2. apply H2.
    

    simpl. do 2 rewrite is_in_FOvar_app.
    rewrite (IHm (num_conn atm1) atm1).
    rewrite (IHm (num_conn atm2) atm2).   
    all : try reflexivity.

    simpl in Hnum. inversion Hnum as [Hnum'].
    rewrite Hnum' in Hleb.
    simpl in Hleb. apply leb_plus_take2 in Hleb.
    assumption.

    apply is_BOXATM_flag_strong_CONJ_conjSO_r in Hbox. assumption.

    simpl in Hnum. inversion Hnum as [Hnum'].
    rewrite Hnum' in Hleb.
    simpl in Hleb. apply leb_plus_take1 in Hleb.
    assumption.

      apply is_BOXATM_flag_strong_CONJ_conjSO_l in Hbox. assumption.
Qed.

Lemma is_BOXATM_CONJ_is_in_batm_conj_equiv : forall atm,
is_BOXATM_flag_strong_CONJ atm = true ->
is_in_FOvar (Var 0) (batm_conj_comp_x1 atm)  = 
is_in_FOvar (Var 0) (FOvars_in atm).
Proof.
  intros atm. apply (is_BOXATM_CONJ_is_in_batm_conj_equiv_pre (num_conn atm) (num_conn atm)).
  reflexivity. apply leb_refl.
Qed.

Lemma next_FOvar_match : forall f f0,
match f with
      | Var y1 => match f0 with
                  | Var y2 => y2 = S y1
                  end
      end ->
  next_FOvar f = f0.
Proof.
  unfold next_FOvar.
  destruct f. destruct f0. intros H. rewrite H. reflexivity.
Qed.

Lemma length_fun4_l2_lP' : forall llx1 lx2 lllv,
  length llx1 = length lx2 ->
  length llx1 = length lllv ->
  length (fun4_l2_lP' llx1 lx2 lllv) = length llx1.
Proof.
  induction llx1; intros lx2 lllv H1 H2.
    reflexivity.

    destruct lx2. discriminate. destruct lllv. discriminate.
    simpl in *. rewrite IHllx1. reflexivity.
    inversion H1. reflexivity.
    inversion H2. reflexivity.
Qed.



Lemma is_un_predless_l_calc_lP : forall lP atm,
is_unary_predless_l (calc_lP atm lP) = true.
Proof.
  induction lP; intros atm. reflexivity.
  simpl. rewrite IHlP.
  rewrite is_un_predless_fun4_l2'. reflexivity.
Qed.



Fixpoint eq_SO (alpha1 alpha2 : SecOrder) : bool :=
  match alpha1, alpha2 with
  | predSO P x, predSO Q y => 
    if (match P, Q with Pred n, Pred m => beq_nat n m end) then 
    (match x, y with Var xn, Var ym => beq_nat xn ym end) else false
  | relatSO x1 y1, relatSO x2 y2 =>
      match x1, y1, x2, y2 with Var x1, Var y1, Var x2, Var y2 =>
    if beq_nat x1 x2 then beq_nat y1 y2 else false end
  | eqFO x1 y1, eqFO x2 y2 =>
      match x1, y1, x2, y2 with Var x1, Var y1, Var x2, Var y2 =>
    if beq_nat x1 x2 then beq_nat y1 y2 else false end
  | allFO x alpha', allFO y beta' => 
      match x, y with Var xn, Var ym =>
      if beq_nat xn ym then eq_SO alpha' beta' else false
      end
  | exFO x alpha', exFO y beta' => 
      match x, y with Var xn, Var ym =>
      if beq_nat xn ym then eq_SO alpha' beta' else false
      end
  | negSO alpha', negSO beta' => eq_SO alpha' beta'
  | conjSO alpha1 alpha2, conjSO beta1 beta2 => 
    if eq_SO alpha1 beta1 then eq_SO alpha2 beta2 else false
  | disjSO alpha1 alpha2, disjSO beta1 beta2 => 
    if eq_SO alpha1 beta1 then eq_SO alpha2 beta2 else false
  | implSO alpha1 alpha2, implSO beta1 beta2 => 
    if eq_SO alpha1 beta1 then eq_SO alpha2 beta2 else false
  | allSO P alpha', allSO Q beta' => 
    match P, Q with Pred n, Pred m =>
    if beq_nat n m then eq_SO alpha' beta' else false end
  | exSO P alpha', exSO Q beta' => 
    match P, Q with Pred n, Pred m =>
    if beq_nat n m then eq_SO alpha' beta' else false end
  | _ , _=> false
  end.

Fixpoint eq_SO_l (l1 l2 : list SecOrder) : bool :=
  match l1, l2 with
  | nil, nil => true
  | nil, _ => false
  | _, nil => false
  | cons a1 l1', cons a2 l2' => if eq_SO a1 a2 then eq_SO_l l1' l2' else false
  end.

Fixpoint calc_conj alpha : list SecOrder :=
  match alpha with
  | conjSO beta1 beta2 => app (calc_conj beta1) (calc_conj beta2)
  | _ => cons alpha nil
  end.

Definition is_equiv_conj_assoc alpha beta : bool :=
  eq_SO_l (calc_conj alpha) (calc_conj beta).

Lemma calc_conj_not_nil : forall cond,
~(calc_conj cond = nil).
Proof.
  induction cond; try discriminate.
  simpl. intros H. 
  apply app_rnil_l in H. rewrite H in IHcond1.
  contradiction (IHcond1 eq_refl).
Qed.

Lemma is_equiv_conj_assoc_relatSO : forall cond x y,
  is_equiv_conj_assoc (relatSO x y) cond = true ->
  cond = relatSO x y.
Proof.
  induction cond; intros [xn] [ym] H;
    try (unfold is_equiv_conj_assoc; discriminate).

    unfold is_equiv_conj_assoc in H. simpl in *.
    destruct f as [z1]; destruct f0 as [z2].
    case_eq (beq_nat xn z1); intros Hbeq; rewrite Hbeq in *.
      2 : discriminate.
    case_eq (beq_nat ym z2); intros Hbeq2; rewrite Hbeq2 in *.
      2 : discriminate.
    rewrite (beq_nat_true _ _ Hbeq). rewrite (beq_nat_true _ _ Hbeq2).
    reflexivity.

    unfold is_equiv_conj_assoc in H. simpl calc_conj in H.
    case_eq (calc_conj cond1). intros Hnil.
      contradiction (calc_conj_not_nil _ Hnil).
    intros beta lbeta Hlbeta.
    case_eq (calc_conj cond2). intros Hnil.
      contradiction (calc_conj_not_nil _ Hnil).
    intros gamma lgamma Hlgamma.
    rewrite Hlgamma in *. rewrite Hlbeta in *.
    simpl in H. case_eq (lbeta ++ gamma :: lgamma ).
      intros Hnil. rewrite Hnil in *.
      symmetry in Hnil. contradiction (app_cons_not_nil _ _ _ Hnil).
    intros delta ldelta Hldelta. rewrite Hldelta in *.
    rewrite if_then_else_false in H. discriminate.
Qed.

Lemma is_equiv_conj_assoc_eqFO : forall cond x y,
  is_equiv_conj_assoc (eqFO x y) cond = true ->
  cond = eqFO x y.
Proof.
  induction cond; intros [xn] [ym] H;
    try (unfold is_equiv_conj_assoc; discriminate).

    unfold is_equiv_conj_assoc in H. simpl in *.
    destruct f as [z1]; destruct f0 as [z2].
    case_eq (beq_nat xn z1); intros Hbeq; rewrite Hbeq in *.
      2 : discriminate.
    case_eq (beq_nat ym z2); intros Hbeq2; rewrite Hbeq2 in *.
      2 : discriminate.
    rewrite (beq_nat_true _ _ Hbeq). rewrite (beq_nat_true _ _ Hbeq2).
    reflexivity.

    unfold is_equiv_conj_assoc in H. simpl calc_conj in H.
    case_eq (calc_conj cond1). intros Hnil.
      contradiction (calc_conj_not_nil _ Hnil).
    intros beta lbeta Hlbeta.
    case_eq (calc_conj cond2). intros Hnil.
      contradiction (calc_conj_not_nil _ Hnil).
    intros gamma lgamma Hlgamma.
    rewrite Hlgamma in *. rewrite Hlbeta in *.
    simpl in H. case_eq (lbeta ++ gamma :: lgamma ).
      intros Hnil. rewrite Hnil in *.
      symmetry in Hnil. contradiction (app_cons_not_nil _ _ _ Hnil).
    intros delta ldelta Hldelta. rewrite Hldelta in *.
    rewrite if_then_else_false in H. discriminate.
Qed.


Lemma calc_conj_not_conjSO : forall alpha,
match alpha with
| conjSO _ _  => true
| _ => false
end = false ->
calc_conj alpha = cons alpha nil.
Proof.
  induction alpha; intros H; try reflexivity.
    discriminate.
Qed.

Lemma eq__SO_rev : forall alpha beta,
  eq_SO alpha beta = true ->
  alpha = beta.
Proof.
  induction alpha; intros beta H;
    try (destruct beta; discriminate).
    destruct beta; try discriminate.
    destruct p as [P1]. destruct p0 as [P2].
    destruct f as [xn]. destruct f0 as [ym].
    simpl in *. case_eq (beq_nat P1 P2); intros Hbeq;
      rewrite Hbeq in *. 2 : discriminate.
    rewrite (beq_nat_true _ _ H). 
    rewrite (beq_nat_true _ _ Hbeq).
    reflexivity.

    destruct f as [x1]. destruct f0 as [x2].
    destruct beta; try discriminate.
    destruct f as [y1]. destruct f0 as [y2].
    simpl in *. case_eq (beq_nat x1 y1); intros Hbeq;
      rewrite Hbeq in *. 2 : discriminate.
    rewrite (beq_nat_true _ _ Hbeq) in *.
    rewrite (beq_nat_true _ _ H) in *.
    reflexivity.

    destruct f as [x1]. destruct f0 as [x2].
    destruct beta; try discriminate.
    destruct f as [y1]. destruct f0 as [y2].
    simpl in *. case_eq (beq_nat x1 y1); intros Hbeq;
      rewrite Hbeq in *. 2 : discriminate.
    rewrite (beq_nat_true _ _ Hbeq) in *.
    rewrite (beq_nat_true _ _ H) in *.
    reflexivity.

    destruct f as [xn]. destruct beta; try discriminate.
    destruct f as [ym]. simpl in *.
    case_eq (beq_nat xn ym); intros Hbeq; rewrite Hbeq in *.
      2 : discriminate.
    rewrite (beq_nat_true _ _ Hbeq). 
    rewrite (IHalpha beta H). reflexivity.

    destruct f as [xn]. destruct beta; try discriminate.
    destruct f as [ym]. simpl in *.
    case_eq (beq_nat xn ym); intros Hbeq; rewrite Hbeq in *.
      2 : discriminate.
    rewrite (beq_nat_true _ _ Hbeq). 
    rewrite (IHalpha beta H). reflexivity.

    destruct beta; try discriminate.
    simpl in H. rewrite (IHalpha _ H).
    reflexivity.

    destruct beta; try discriminate.
    simpl in H.
    apply if_then_else_ft in H.
    destruct H as [H1 H2].
    rewrite (IHalpha1 _ H1).
    rewrite (IHalpha2 _ H2).
    reflexivity.

    destruct beta; try discriminate.
    simpl in H.
    apply if_then_else_ft in H.
    destruct H as [H1 H2].
    rewrite (IHalpha1 _ H1).
    rewrite (IHalpha2 _ H2).
    reflexivity.

    destruct beta; try discriminate.
    simpl in H.
    apply if_then_else_ft in H.
    destruct H as [H1 H2].
    rewrite (IHalpha1 _ H1).
    rewrite (IHalpha2 _ H2).
    reflexivity.

    destruct p as [Pn]. destruct beta; try discriminate.
    destruct p as [Qm]. simpl in H.
    apply if_then_else_ft in H.
    destruct H as [H1 H2].
    rewrite (beq_nat_true _ _ H1).
    rewrite (IHalpha _ H2). reflexivity.

    destruct p as [Pn]. destruct beta; try discriminate.
    destruct p as [Qm]. simpl in H.
    apply if_then_else_ft in H.
    destruct H as [H1 H2].
    rewrite (beq_nat_true _ _ H1).
    rewrite (IHalpha _ H2). reflexivity.

Qed.

Lemma is_equiv_conj_assoc_not_conjSO : forall alpha cond2,
match alpha with
| conjSO _ _  => true
| _ => false
end = false ->
is_equiv_conj_assoc alpha cond2 = true ->
cond2 = alpha.
Proof.
  intros alpha cond2 H1 H2.
  unfold is_equiv_conj_assoc in H2.
  rewrite (calc_conj_not_conjSO alpha H1) in H2.
  case_eq (calc_conj cond2). intros Hnil.
    rewrite Hnil in H2. simpl in H2. discriminate.
  intros beta lbeta Hlbeta. simpl in H2.
  rewrite Hlbeta in *. destruct lbeta.
  apply if_then_else_ft in H2. destruct H2 as [H2 H2'].
  apply eq__SO_rev in H2. rewrite H2 in *.
  rewrite (calc_conj_not_conjSO) in Hlbeta.
    inversion Hlbeta. reflexivity.

    destruct cond2; try discriminate; try reflexivity.

    simpl in Hlbeta.
    case_eq (calc_conj cond2_1). intros Hnil. 
      contradiction (calc_conj_not_nil _ Hnil).
    intros beta2 lbeta2 Hlbeta2.
    rewrite Hlbeta2 in Hlbeta.
    inversion Hlbeta as [[H3 H4]].
    destruct lbeta2. 2 : discriminate.
    simpl in H4. contradiction (calc_conj_not_nil _ H4).

    rewrite if_then_else_false in H2. discriminate.
Qed.

Lemma eq__SO_l_rev : forall l1 l2,
  eq_SO_l l1 l2 = true ->
  l1 = l2.
Proof.
  induction l1; intros l2 H.
    destruct l2. reflexivity. discriminate.

    simpl in *. destruct l2. discriminate.
    apply if_then_else_ft in H.
    destruct H as [H1 H2].
    apply eq__SO_rev in H1.
    apply IHl1 in H2. rewrite H1. rewrite H2.
    reflexivity.
Qed.

Lemma eq_SO_l_calc_conj_app_cons : forall alpha1 alpha2 beta,
eq_SO_l (calc_conj alpha1 ++ calc_conj alpha2) (beta:: nil) = false.
Proof.
  intros alpha1 alpha2 beta.
  case_eq (calc_conj alpha1). intros Hnil.
    contradiction (calc_conj_not_nil _ Hnil).
  case_eq (calc_conj alpha2). intros Hnil.
    contradiction (calc_conj_not_nil _ Hnil).
  intros. simpl.
  case_eq (eq_SO_l (l0 ++ s :: l) nil ).
    intros Hnil.
    apply eq__SO_l_rev in Hnil. symmetry in Hnil. 
    contradiction ( app_cons_not_nil _ _ _ Hnil).

    intros H2. rewrite if_then_else_false.
    reflexivity.
Qed.

Lemma is_equiv_conj_assoc_conjSO_not : forall beta alpha1 alpha2,
  (match beta with 
  | conjSO _ _ => true
  | _ => false end )  = false ->
  is_equiv_conj_assoc (conjSO alpha1 alpha2) beta = false.
Proof.
  induction beta; intros alpha1 alpha2 H; try discriminate;
    try (unfold is_equiv_conj_assoc; simpl; apply eq_SO_l_calc_conj_app_cons).
Qed.


Lemma eq_SO_refl : forall alpha,
  eq_SO alpha alpha = true.
Proof.
  induction alpha. 
    destruct p. destruct f. simpl.
    do 2 rewrite <- beq_nat_refl. reflexivity.

    destruct f. destruct f0. simpl.
    do 2 rewrite <- beq_nat_refl. reflexivity.

    destruct f. destruct f0. simpl.
    do 2 rewrite <- beq_nat_refl. reflexivity.

    destruct f. simpl. rewrite <- beq_nat_refl.
    assumption.

    destruct f. simpl. rewrite <- beq_nat_refl.
    assumption.

    simpl. assumption.

    simpl. rewrite IHalpha1. rewrite IHalpha2.
    reflexivity.

    simpl. rewrite IHalpha1. rewrite IHalpha2.
    reflexivity.

    simpl. rewrite IHalpha1. rewrite IHalpha2.
    reflexivity.

    destruct p. simpl. rewrite <- beq_nat_refl.
    assumption.

    destruct p. simpl. rewrite <- beq_nat_refl.
    assumption.
Qed.

Lemma eq__SO_rev_f : forall alpha beta,
  eq_SO alpha beta = false ->
  ~ alpha = beta.
Proof.
  intros alpha beta H1 H2.
  rewrite H2 in *. rewrite eq_SO_refl in H1.
  discriminate.
Qed.


Lemma eq_SO_comm : forall a b,
  eq_SO a b = eq_SO b a.
Proof.
  intros a b.
  case_eq (eq_SO a b); intros H.
    apply eq__SO_rev in H. rewrite H.
    rewrite eq_SO_refl. reflexivity.

    apply eq__SO_rev_f in H.
    case_eq (eq_SO b a); intros H2.
      2 : reflexivity. 
    apply eq__SO_rev in H2.
    rewrite H2 in H. contradiction (H eq_refl).
Qed.

Lemma eq_SO_l_comm : forall l1 l2,
  eq_SO_l l1 l2 = eq_SO_l l2 l1.
Proof.
  induction l1; intros l2.
    destruct l2; reflexivity.

    simpl. destruct l2. reflexivity.
    simpl. rewrite eq_SO_comm.
    rewrite IHl1. reflexivity.
Qed.

Lemma is_equiv_conj_assoc_conjSO : forall beta alpha1 alpha2,
  is_equiv_conj_assoc (conjSO alpha1 alpha2) beta = true ->
  exists beta1 beta2,
      beta = conjSO beta1 beta2.
Proof.
  intros beta alpha1 alpha2 H.
  destruct beta; try (rewrite is_equiv_conj_assoc_conjSO_not in H; [
    discriminate | reflexivity]).
  exists beta1. exists beta2. reflexivity.
Qed.

Fixpoint is_subfml_SO (alpha beta : SecOrder) : bool :=
  if eq_SO alpha beta then true else
  match beta with
  | conjSO beta1 beta2 => if is_subfml_SO alpha beta1 then true
    else is_subfml_SO alpha beta2
  | disjSO beta1 beta2 => if is_subfml_SO alpha beta1 then true
    else is_subfml_SO alpha beta2
  | implSO beta1 beta2 => if is_subfml_SO alpha beta1 then true
    else is_subfml_SO alpha beta2
  | allFO _ beta' => is_subfml_SO alpha beta'
  | exFO _ beta' => is_subfml_SO alpha beta'
  | allSO _ beta' => is_subfml_SO alpha beta'
  | exSO _ beta' => is_subfml_SO  alpha beta'
  | _ => false
  end.

Lemma eq_SO_l_refl : forall l,
  eq_SO_l l l = true.
Proof.
  induction l. reflexivity.
  simpl. rewrite eq_SO_refl.
  assumption.
Qed.

Lemma is_equiv_conj_assoc_refl : forall alpha,
  is_equiv_conj_assoc alpha alpha = true.
Proof.
  unfold is_equiv_conj_assoc. intros alpha.
  apply eq_SO_l_refl.
Qed.

Lemma   is_equiv_conj_assoc_comm : forall alpha beta,
  is_equiv_conj_assoc alpha beta = is_equiv_conj_assoc beta alpha.
Proof.
  intros alpha beta.
  unfold is_equiv_conj_assoc.
  rewrite eq_SO_l_comm. reflexivity.
Qed.

Fixpoint is_equiv_conj_assoc_l (l1 l2 : list SecOrder) : bool :=
  match l1, l2 with
  | nil, _ => true
  | _, nil => true
  | cons a l1', cons b l2' =>
    if is_equiv_conj_assoc a b then is_equiv_conj_assoc_l l1' l2'
      else false
  end.

Lemma   is_equiv_conj_assoc_l_comm : forall l1 l2 ,
  is_equiv_conj_assoc_l l1 l2 = is_equiv_conj_assoc_l l2 l1.
Proof.
  induction l1; intros l2.
    destruct l2; reflexivity.

    simpl. destruct l2. reflexivity.
    rewrite IHl1. simpl.
    rewrite is_equiv_conj_assoc_comm. reflexivity.
Qed.

Lemma eq_SO_l_app_ex : forall l1 l2 l3 l4,
  eq_SO_l (app l1 l2) (app l3 l4) = true ->
  exists l3' l4',
    eq_SO_l l1 l3' = true /\
    eq_SO_l l2 l4' = true /\
    eq_SO_l (app l3 l4) (app l3' l4') = true.
Proof.
  induction l1; intros l2 l3 l4 H.
    simpl in *. exists nil. 
    exists (app l3 l4).
    apply conj. reflexivity.
    apply conj. assumption.
    apply eq_SO_l_refl.

    exists (cons a l1).
    exists l2.
    apply conj. apply eq_SO_l_refl.
    apply conj. apply eq_SO_l_refl.
    rewrite eq_SO_l_comm. assumption.
Qed.

Lemma eq__SO_l_rev_f : forall l1 l2,
  eq_SO_l l1 l2 = false ->
  ~ l1 = l2.
Admitted.

Lemma eq_SO_l_calc_conj_nil : forall cond,
 eq_SO_l (calc_conj cond) nil = false.
Proof.
  induction cond; try reflexivity.
  simpl.
  case_eq (calc_conj cond1).
    intros H. rewrite H in *. discriminate.
    intros a la Hla. simpl. reflexivity.
Qed.

Lemma is_equiv_conj_assoc_conjSO2: forall cond1 cond2 beta1 beta2,
  is_equiv_conj_assoc (conjSO cond1 cond2) (conjSO beta1 beta2) = true ->
  exists beta1' beta2',
    is_equiv_conj_assoc cond1 beta1' =true /\
    is_equiv_conj_assoc cond2 beta2' = true /\
    is_equiv_conj_assoc (conjSO beta1 beta2) (conjSO beta1' beta2') = true.
Proof.
  intros until 0. intros H.
pose proof H as H'.
  unfold is_equiv_conj_assoc in *.
  simpl in H.
  apply eq_SO_l_app_ex in H.  
  destruct H as [l3' [l4' [H1 [H2 H3]]]].
  apply eq__SO_l_rev in H1.
  apply eq__SO_l_rev in H2.
  apply eq__SO_l_rev in H3.
  exists cond1. exists cond2.
  apply conj. apply eq_SO_l_refl.
  apply conj. apply eq_SO_l_refl.
  rewrite eq_SO_l_comm. assumption.
Qed.

Lemma eq_SO_l_trans : forall l1 l2 l3,
  eq_SO_l l1 l2 = true ->
  eq_SO_l l2 l3 = true ->
  eq_SO_l l1 l3 = true.
Proof.
  induction l1; intros l2 l3 H1 H2.
    destruct l2. destruct l3. reflexivity.
    all : try discriminate.

    destruct l2. discriminate.
    destruct l3. discriminate.
    simpl in *. case_eq (eq_SO a s);
      intros H1'; rewrite H1' in *.
      2 : discriminate.
    case_eq (eq_SO s s0); intros H2';
      rewrite H2' in *. 2 : discriminate.
    apply eq__SO_rev in H1'.
    apply eq__SO_rev in H2'.
    rewrite H1' in *. rewrite H2' in *.
    rewrite eq_SO_refl.
    apply (IHl1 l2 l3); assumption.
Qed.

Lemma is_equiv_conj_assoc_trans : forall alpha beta gamma,
  is_equiv_conj_assoc alpha beta = true ->
  is_equiv_conj_assoc beta gamma = true ->
  is_equiv_conj_assoc alpha gamma = true.
Proof.
  unfold is_equiv_conj_assoc. 
  intros until 0. intros H1 H2.
  apply (eq_SO_l_trans _ _ _ H1 H2).
Qed.

Lemma is_equiv_conj_assoc_allFO : forall cond1 cond2 x1 x2,
  is_equiv_conj_assoc (allFO x1 cond1) (allFO x2 cond2) = true ->
    x1 = x2 /\ is_equiv_conj_assoc cond1 cond2 = true.
Admitted.

Lemma is_equiv_conj_assoc_exFO : forall cond1 cond2 x1 x2,
  is_equiv_conj_assoc (exFO x1 cond1) (exFO x2 cond2) = true ->
    x1 = x2 /\ is_equiv_conj_assoc cond1 cond2 = true.
Admitted.

Lemma is_equiv_conj_assoc_negSO : forall cond1 cond2,
  is_equiv_conj_assoc (negSO cond1) (negSO cond2) = true ->
   is_equiv_conj_assoc cond1 cond2 = true.
Admitted.


Lemma calc_conj_conjSO_not : forall alpha beta1 beta2,
  (match alpha with
  | conjSO _ _ => true 
  | _ => false end) = false ->
  ~ calc_conj alpha = calc_conj (conjSO beta1 beta2).
Admitted.

Fixpoint list_add (l : list nat) : nat :=
  match l with
  | nil => 0
  | cons n l' => n + (list_add l')
  end.

Lemma list_add_app : forall l1 l2,
  list_add (app l1 l2) = plus (list_add l1) (list_add l2).
Proof.
  induction l1; intros l2. reflexivity.
  simpl. rewrite IHl1. rewrite arith_plus_assoc.
  reflexivity.
Qed.

Lemma num_conn_calc_conj_S : forall alpha,
  S (num_conn alpha) = plus (list_add (map (num_conn)  (calc_conj alpha)))  (length (calc_conj alpha)).
Proof.
  induction alpha; try reflexivity;
    try ( simpl;  rewrite <- plus_n_O;
    rewrite <- one_suc; reflexivity).

    simpl. rewrite map_app.
    rewrite app_length.
    rewrite plus_n_Sm.
    rewrite IHalpha2.
    rewrite <- plus_Sn_m.
    rewrite IHalpha1.
    rewrite list_add_app.
    remember (list_add (map num_conn (calc_conj alpha1))) as A.
    remember (length (calc_conj alpha1)) as B.
    remember ((list_add (map num_conn (calc_conj alpha2)))) as C.
    remember (length (calc_conj alpha2)) as D.
    rewrite (arith_plus_assoc A B (C + D)). 
    rewrite (arith_plus_comm B (C+D)).
    rewrite (arith_plus_assoc C D B).
    rewrite <- (arith_plus_assoc A C (D + B)).
    rewrite (arith_plus_comm D B). reflexivity.
Qed.

Lemma num_conn_calc_conj : forall alpha,
  num_conn alpha = (plus (list_add (map (num_conn)  (calc_conj alpha)))  (length (calc_conj alpha))) - 1.
Proof.
  intros alpha.
  case_eq (num_conn alpha).
    intros Hnil. rewrite <- num_conn_calc_conj_S.
    simpl. rewrite Hnil. reflexivity.

    intros n Hn. rewrite <- num_conn_calc_conj_S. 
    simpl. rewrite Hn. rewrite <- Minus.minus_n_O.
    reflexivity.
Qed.

Lemma is_equiv_conj_assoc_num_conn_pre : forall alpha beta,
  (calc_conj alpha) = (calc_conj beta) ->
  num_conn alpha = num_conn beta.
Proof.
  intros alpha beta H.
  do 2 rewrite num_conn_calc_conj.
  rewrite H. reflexivity.
Qed.

Lemma is_equiv_conj_assoc_num_conn : forall alpha beta,
  is_equiv_conj_assoc alpha beta = true ->
  num_conn alpha = num_conn beta.
Proof.
  intros alpha beta H.
  unfold is_equiv_conj_assoc in H.
  apply eq__SO_l_rev in H.
  apply is_equiv_conj_assoc_num_conn_pre. assumption.
Qed.

Lemma passing_conj_calc_conj : forall cond W Iv Ip Ir,
    SOturnst W Iv Ip Ir cond  <->
    SOturnst W Iv Ip Ir (passing_conj (calc_conj cond)).
Proof.
  induction cond; intros W Iv Ip Ir; try (simpl; apply iff_refl).
  split; intros SOt. apply passing_conj_app.
    apply calc_conj_not_nil.
    apply calc_conj_not_nil. 
    simpl. apply conj. apply IHcond1. apply SOt.
      apply IHcond2. apply SOt.

    apply passing_conj_app in SOt.
    apply conj. apply IHcond1. apply SOt.
      apply IHcond2. apply SOt.
    apply calc_conj_not_nil.
    apply calc_conj_not_nil. 
Qed.

Lemma passing_conj_rep_FOv : forall l x y W Iv Ip Ir,
  SOturnst W Iv Ip Ir (replace_FOv (passing_conj l) x y) <->
  SOturnst W Iv Ip Ir (passing_conj (map (fun a => replace_FOv a x y) l)).
Proof.
  induction l; intros x y W Iv Ip Ir.
    simpl. destruct x as [xn].
    case_eq (beq_nat xn 1); intros Hbeq;
      simpl; destruct y; split; reflexivity.

    simpl. case_eq l.
      intros Hnil. simpl. apply iff_refl.

      intros b lb Hlb. rewrite <- Hlb.
      destruct x as [xn].
      case_eq (map (fun a0 : SecOrder => replace_FOv a0 (Var xn) y) l).
        intros H. rewrite Hlb in *. discriminate.
      intros c lc Hlc. rewrite <- Hlc.
      simpl.
      split; intros [SOt1 SOt2];
        (apply conj;[ |
        apply IHl]; assumption).
Qed.
    
Lemma passing_conj_calc_conj_rep_FOv : forall cond x y W Iv Ip Ir,
    SOturnst W Iv Ip Ir (replace_FOv cond x y)  <->
    SOturnst W Iv Ip Ir (replace_FOv (passing_conj (calc_conj cond)) x y).
Proof.
  induction cond; intros x y W Iv Ip Ir; try (simpl; apply iff_refl).
  destruct x as [xn].
  split; intros SOt.
    apply passing_conj_rep_FOv.
    rewrite map_app.
    apply passing_conj_app.
      pose proof (calc_conj_not_nil cond1) as H.
      destruct (calc_conj cond1); try discriminate.
      contradiction (H eq_refl).
      pose proof (calc_conj_not_nil cond2) as H.
      destruct (calc_conj cond2); try discriminate.
      contradiction (H eq_refl).

    simpl.
    apply conj.
      apply passing_conj_rep_FOv.
      apply IHcond1. apply SOt.

      apply passing_conj_rep_FOv.
      apply IHcond2. apply SOt.

    apply passing_conj_rep_FOv in SOt.
    rewrite map_app in SOt.
    apply passing_conj_app in SOt.
    simpl.
    apply conj.
      apply IHcond1. apply passing_conj_rep_FOv.
      apply SOt.

      apply IHcond2.
      apply passing_conj_rep_FOv. apply SOt.

      pose proof (calc_conj_not_nil cond1) as HH.
      destruct (calc_conj cond1); try discriminate.
      contradiction (HH eq_refl).
      pose proof (calc_conj_not_nil cond2) as HH.
      destruct (calc_conj cond2); try discriminate.
      contradiction (HH eq_refl).
Qed.

Lemma lem_try_predSO_pre_fwd : forall cond1 cond2 un ym W Iv Ip Ir,
is_equiv_conj_assoc cond1 cond2 = true ->
SOturnst W Iv Ip Ir (replace_FOv cond1 (Var un) (Var ym)) ->
 SOturnst W Iv Ip Ir (replace_FOv cond2 (Var un) (Var ym)).
Proof.
  intros until 0. intros H1 SOt.
  apply passing_conj_calc_conj_rep_FOv.
  apply passing_conj_calc_conj_rep_FOv in SOt.
  unfold is_equiv_conj_assoc in H1.
  apply eq__SO_l_rev in H1. rewrite H1 in *.
  assumption.
Qed.

Lemma lem_try_predSO_pre : forall cond1 cond2 un ym W Iv Ip Ir,
is_equiv_conj_assoc cond1 cond2 = true ->
SOturnst W Iv Ip Ir (replace_FOv cond1 (Var un) (Var ym)) <-> SOturnst W Iv Ip Ir (replace_FOv cond2 (Var un) (Var ym)).
Proof.
  intros until 0. intros H.
  split; intros SOt.
    apply (lem_try_predSO_pre_fwd cond1 cond2); assumption.
    apply (lem_try_predSO_pre_fwd cond2 cond1).
    rewrite is_equiv_conj_assoc_comm. assumption.
    assumption.
Qed.

Lemma lem_try_predSO : forall cond1 cond2 p f P u W Iv Ip Ir,
is_equiv_conj_assoc cond1 cond2 = true ->
SOturnst W Iv Ip Ir (replace_pred (predSO p f) P u cond1) <-> SOturnst W Iv Ip Ir (replace_pred (predSO p f) P u cond2).
Proof.
  intros cond1 cond2 [Qm] [ym] [Pn] [un] W Iv Ip Ir H.
  simpl. case_eq (beq_nat Pn Qm); intros Hbeq.
  apply lem_try_predSO_pre. assumption.

    simpl. apply iff_refl.
Qed.


Lemma lem_try : forall alpha cond1 cond2 P W Iv Ip Ir u,
  is_equiv_conj_assoc cond1 cond2 = true ->
  SOturnst W Iv Ip Ir (replace_pred alpha P u cond1) <->
  SOturnst W Iv Ip Ir (replace_pred alpha P u cond2).
Proof.
  induction alpha; intros cond1 cond2 P W Iv Ip Ir u H.
    apply lem_try_predSO. assumption.

    do 2 rewrite rep_pred_relatSO. apply iff_refl.

    do 2 rewrite rep_pred_eqFO. apply iff_refl.

    do 2 rewrite rep_pred_allFO.
    do 2 rewrite SOturnst_allFO.
    split; intros SOt d; specialize (SOt d);
      apply (IHalpha cond1 cond2); assumption.

    do 2 rewrite rep_pred_exFO.
    do 2 rewrite SOturnst_exFO.
    split; intros [d SOt]; exists d;
      apply (IHalpha cond1 cond2); assumption.

    do 2 rewrite rep_pred_negSO.
    do 2 rewrite SOturnst_negSO.
    split; intros SOt1 SOt2;
      apply SOt1; apply (IHalpha cond1 cond2);
      assumption.

    do 2 rewrite rep_pred_conjSO.
    simpl. split; intros [SOt1 SOt2];
      (apply conj; [ apply (IHalpha1 cond1 cond2);
        assumption |
      apply (IHalpha2 cond1 cond2);
        assumption]).

    do 2 rewrite rep_pred_disjSO.
    simpl. split; (intros [SOt1 | SOt2];
    [ left; apply (IHalpha1 cond1 cond2); try assumption;
      try reflexivity
    | right; apply (IHalpha2 cond1 cond2); try assumption;
      try reflexivity]).

    do 2 rewrite rep_pred_implSO.
    simpl. split; (intros SOt1 SOt2;
      apply (IHalpha2 cond1 cond2); try reflexivity;
      try assumption; apply SOt1; apply (IHalpha1 cond1 cond2);
      try reflexivity; try assumption).


    destruct P as [Pn]. destruct p as [Qm].
    simpl. case_eq (beq_nat Pn Qm); intros Hbeq.
      apply IHalpha. assumption.

    split; intros SOt pa;
      apply (IHalpha cond1 cond2); try assumption;
      apply SOt.

    destruct P as [Pn]. destruct p as [Qm].
    simpl. case_eq (beq_nat Pn Qm); intros Hbeq.
      apply IHalpha. assumption.

    split; intros [pa SOt]; exists pa;
      apply (IHalpha cond1 cond2); try assumption;
      apply SOt.
Qed.

(* I think try and go from here (12:55pm on 23/11/17) *) 

Lemma consistent_lP_lcond_cons_rem_gen : forall lP lcond P x,
  consistent_lP_lcond (cons P lP) (cons x lcond) ->
  consistent_lP_lcond (lP) (lcond).
Proof.
  intros until 0. intros H.
  destruct lP. intros Q.
    unfold consistent_lP_lcond_P.
    simpl. apply is_constant_nil. apply x.

    destruct lcond. unfold consistent_lP_lcond in *.
    intros Q. unfold consistent_lP_lcond_P in *.
    unfold indicies_l2 in *. rewrite ind_cond_nil_gen.
    apply is__constant_l.

  apply consistent_lP_lcond_cons_switch in H.
  apply consistent_lP_lcond_cons_rem in H. assumption.
Qed.

Lemma lem_try_l : forall lP lcond1 lcond2 alpha W Iv Ip Ir u,
  length lcond1 = length lcond2 ->
  length lP = length lcond1 ->
  length lP = length lcond2 ->
  is_equiv_conj_assoc_l lcond1 lcond2 = true ->
is_unary_predless_l lcond1 = true ->
is_unary_predless_l lcond2 = true ->
consistent_lP_lcond lP lcond1 ->
consistent_lP_lcond lP lcond2 ->
  SOturnst W Iv Ip Ir (replace_pred_l alpha lP (list_Var (length lP) u) lcond1) <->
  SOturnst W Iv Ip Ir (replace_pred_l alpha lP (list_Var (length lP) u) lcond2).
Proof.
  induction lP; intros lcond1 lcond2 alpha W Iv Ip Ir u Hl Hl1 Hl2 Hequiv Hun1 Hun2 Hcon1 Hcon2.
    simpl. apply iff_refl.

    simpl. destruct lcond1. destruct lcond2.
      apply iff_refl. discriminate.
    destruct lcond2. discriminate.
    simpl in Hun1. case_eq (is_unary_predless s); intros Hun1';
      rewrite Hun1' in *. 2 : discriminate.
    simpl in Hun2. case_eq (is_unary_predless s0); intros Hun2';
      rewrite Hun2' in *. 2 : discriminate.
    simpl in Hequiv.
    case_eq (is_equiv_conj_assoc s s0); intros H;
      rewrite H in *. 2 : discriminate.
    inversion Hl as [Hl'].
    pose proof (consistent_lP_lcond_cons_rem_gen _ _ _ _ Hcon1) as Hcon1'.
    pose proof (consistent_lP_lcond_cons_rem_gen _ _ _ _ Hcon2) as Hcon2'.
    simpl in Hl1. inversion Hl1 as [Hl1'].
    simpl in Hl2. inversion Hl2 as [Hl2'].
    split; intros SOt.
      case_eq (is_in_pred a lP); intros Hin2.
        rewrite rep_pred__l_is_in2.
        rewrite rep_pred__l_is_in2 in SOt.
        apply (IHlP lcond1).
        all : try assumption.

        rewrite length_list_Var. reflexivity.

        rewrite length_list_Var. reflexivity.

        rewrite rep_pred__l_switch.
        apply (IHlP lcond1). all : try assumption.
        rewrite <- rep_pred__l_switch.
        apply (lem_try _ s).
        all : try assumption.

      case_eq (is_in_pred a lP); intros Hin2.
        rewrite rep_pred__l_is_in2.
        rewrite rep_pred__l_is_in2 in SOt.
        apply (IHlP lcond1 lcond2).
        all : try assumption.

        rewrite length_list_Var. reflexivity.

        rewrite length_list_Var. reflexivity.

        rewrite rep_pred__l_switch.
        apply (IHlP lcond1 lcond2). all : try assumption.
        rewrite <- rep_pred__l_switch.
        apply (lem_try _ s0).
        all : try assumption.

        rewrite is_equiv_conj_assoc_comm. assumption.
Qed.

Lemma try'' : forall m n batm x,
  n = num_conn batm ->
  Nat.leb n m = true ->
  BOXATM_flag_strong batm x = true ->
    batm = (fun5'' (batm_comp_P batm) (batm_comp_x1 batm) (batm_comp_lx batm)).
Proof.
  induction m; intros n batm x Hnum Hleb Hbox; try discriminate.
    destruct batm; try discriminate.
    destruct p. destruct f. simpl. reflexivity.
    destruct n; discriminate.

    destruct n. destruct batm; try discriminate.
      simpl. reflexivity.
    destruct batm; try discriminate.
    destruct batm; try discriminate.
    destruct batm1; try discriminate.
    simpl. destruct f as [x1]. destruct f0 as [x2]. destruct f1 as [x3].
    simpl in *. destruct x as [xn]. case_eq (beq_nat xn x2);
      intros Hbeq; rewrite Hbeq in *. 2 :discriminate.
    case_eq (beq_nat x1 x3); intros Hbeq2; rewrite Hbeq2 in *.
      2 : discriminate.
    case_eq (beq_nat x3 (S x2)); intros Hbeq3; rewrite Hbeq3 in *.
      2 : discriminate.
    rewrite (beq_nat_true _ _ Hbeq2) in *.
    destruct n. discriminate.
    rewrite (IHm n batm2 (Var x3)) at 1; try assumption.
    rewrite try3 with (x := (Var x3)).
    reflexivity. assumption. inversion Hnum. reflexivity.
    apply leb_suc_l in Hleb. assumption.
Qed.

Lemma try''' : forall batm x,
  BOXATM_flag_strong batm x = true ->
    batm = (fun5'' (batm_comp_P batm) (batm_comp_x1 batm) (batm_comp_lx batm)).
Proof.
  intros batm x. apply (try'' (num_conn batm) (num_conn batm)).
  reflexivity. apply leb_refl.
Qed.

Lemma is_equiv_conj_assoc_fun5'' : forall atm x,
  BOXATM_flag_strong atm x = true ->
  is_equiv_conj_assoc (fun5'' (batm_comp_P atm) (batm_comp_x1 atm) (batm_comp_lx atm)) atm = true.
Proof.
  intros atm x H.
  unfold is_equiv_conj_assoc.
  rewrite <- try''' with ( x:=x).
  apply eq_SO_l_refl.
  assumption.
Qed.

Lemma calc_conj_fun5_l''_app : forall la1 la2 la3 lb1 lb2 lb3 ,
~la1 = nil ->
~lb1 = nil ->
  length la1 = length la2 ->
  length la1 = length la3 ->
  length lb1 = length lb2 ->
  length lb1 = length lb3 ->
  calc_conj (fun5_l'' (app la1 lb1) (app la2 lb2) (app la3 lb3)) =
  app (calc_conj (fun5_l'' la1 la2 la3)) (calc_conj (fun5_l'' lb1 lb2 lb3)).
Proof.
  induction la1; intros la2 la3 lb1 lb2 lb3 Hnila Hnilb Hl1 Hl2 Hl3 Hl4.
    contradiction (Hnila eq_refl).

    case_eq la1. intros Hla1. rewrite Hla1 in *. destruct la2. discriminate.
    destruct la2. 2 : discriminate. destruct la3. discriminate.
    destruct la3. 2 : discriminate.
    simpl. destruct lb1. contradiction (Hnilb eq_refl).
    destruct lb2. discriminate. simpl. destruct lb3.
    discriminate. reflexivity.

    intros pa1 lpa1 Hla1. rewrite <- Hla1.
    simpl.
    destruct la2. rewrite Hla1 in *. discriminate.
    destruct la3. rewrite Hla1 in *. discriminate.
    case_eq lb1. intros Hlb1. rewrite Hlb1 in *. contradiction (Hnilb eq_refl).
    intros pb1 lpb1 Hlb1. rewrite <- Hlb1.
    rewrite Hla1. rewrite <- Hla1.
    case_eq (app la1 lb1).
      rewrite Hla1. discriminate.
    intros PP lPP HlPP.
    rewrite <- HlPP.
    simpl.
    destruct la2. rewrite Hla1 in *. discriminate.
    case_eq ((f0 :: la2) ++ lb2 ).
      discriminate.
    intros PPP lPPP HlPPP. rewrite <- HlPPP.  
    destruct la3. rewrite Hla1 in *. discriminate.
    case_eq ((l0 :: la3) ++ lb3 ).
      discriminate.
    intros aa laa Hlaa. rewrite <- Hlaa.
    simpl. rewrite app_comm_cons.
    rewrite app_comm_cons. rewrite IHla1.
    rewrite app_assoc. reflexivity.

    rewrite Hla1. discriminate.
    rewrite Hlb1. discriminate.
    rewrite Hla1 in *. simpl in *. inversion Hl1. reflexivity. 
    rewrite Hla1 in *. simpl in *. inversion Hl2. reflexivity.
    rewrite Hlb1 in *. simpl in *. inversion Hl3. reflexivity. 
    rewrite Hlb1 in *. simpl in *. inversion Hl4. reflexivity.
Qed.

Lemma calc_conj_fun5_l'' : forall atm,
  is_BOXATM_flag_strong_CONJ atm = true ->
  (calc_conj (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm))) =
  (calc_conj atm).
Proof.
  induction atm; intros H; try discriminate.
    simpl in *. reflexivity.

    destruct f as [xn]. destruct xn. discriminate.
    simpl in *. destruct atm; try discriminate.
    destruct atm1; try discriminate.
    destruct f as [z1]; destruct f0 as [z2].
    destruct z2. rewrite if_then_else_false in H.
    discriminate.
    case_eq (BOXATM_flag_strong atm2 (Var (S xn)));
      intros H2; rewrite H2 in *.
      2 : (do 3 rewrite if_then_else_false in *; discriminate).
    pose proof H2 as H2'.
    apply try3 in H2.
    case_eq (beq_nat xn z1); intros Hbeq2;
      rewrite Hbeq2 in *. 2 : discriminate.
    rewrite <- (beq_nat_true _ _ Hbeq2). simpl.
    rewrite <- H2. rewrite <- try''' with (x := (Var (S xn))).
    case_eq (beq_nat xn z2); intros Hbeq3; rewrite Hbeq3 in *.
      2 : discriminate.
    rewrite (beq_nat_true _ _ Hbeq3) in H2.
    rewrite H2. reflexivity.
    assumption.

    pose proof (is_BOXATM_flag_strong_CONJ_conjSO_l _ _ H) as H1.
    pose proof (is_BOXATM_flag_strong_CONJ_conjSO_r _ _ H) as H2.
    simpl. rewrite calc_conj_fun5_l''_app.
    rewrite IHatm1. rewrite IHatm2. reflexivity.
      all : try assumption.

      apply batm_conj_comp_P_not_nil. assumption.
      apply batm_conj_comp_P_not_nil. assumption.

      apply length_batm_conj_comp_P_x1. assumption.
      apply length_batm_conj_comp_P_lx. assumption.

      apply length_batm_conj_comp_P_x1. assumption.
      apply length_batm_conj_comp_P_lx. assumption.
Qed.

Lemma is_equiv_conj_assoc_fun5_l'' : forall atm,
  is_BOXATM_flag_strong_CONJ atm = true ->
  is_equiv_conj_assoc (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm)) atm = true.
Proof.
  intros atm H.
  unfold is_equiv_conj_assoc.
  rewrite calc_conj_fun5_l''. rewrite eq_SO_l_refl.
  reflexivity. assumption.
Qed.

Lemma lem_try_fun5'' : forall alpha atm x P W Iv Ip Ir u,
  BOXATM_flag_strong atm x = true ->
  SOturnst W Iv Ip Ir (replace_pred alpha P u (fun5'' (batm_comp_P atm) (batm_comp_x1 atm) (batm_comp_lx atm))) <->
  SOturnst W Iv Ip Ir (replace_pred alpha P u atm).
Proof.
  intros until 0. intros H.
  apply lem_try.
  apply is_equiv_conj_assoc_fun5'' with (x := x).
  assumption.
Qed.

Lemma lem_try_fun5_l'' : forall alpha atm P W Iv Ip Ir u,
  is_BOXATM_flag_strong_CONJ atm = true ->
  SOturnst W Iv Ip Ir (replace_pred alpha P u (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm))) <->
  SOturnst W Iv Ip Ir (replace_pred alpha P u atm).
Proof.
  intros until 0. intros H.
  apply lem_try.
  apply is_equiv_conj_assoc_fun5_l''.
  assumption.
Qed.

(* Left it here 23/11/17 *)
(* This is good up to here (minus heaps of stuff!!!) *)
(* Try again to find the bigger picture and whether I need to
define fun5_l''_l for rep_pred_l. *)

   
(* Lemma lem_try_l_fun5_l'' : forall lP lcond1 lcond2 alpha W Iv Ip Ir u,
  length lcond1 = length lcond2 ->
  length lP = length lcond1 ->
  length lP = length lcond2 ->
  is_equiv_conj_assoc_l lcond1 lcond2 = true ->
is_unary_predless_l lcond1 = true ->
is_unary_predless_l lcond2 = true ->
consistent_lP_lcond lP lcond1 ->
consistent_lP_lcond lP lcond2 ->
  SOturnst W Iv Ip Ir (replace_pred_l alpha lP (list_Var (length lP) u) lcond1) <->
  SOturnst W Iv Ip Ir (replace_pred_l alpha lP (list_Var (length lP) u) lcond2).
Proof.
Admitted. *)

Lemma lem_try3_pre : forall m n atm P x y,
  n = num_conn atm ->
  Nat.leb n m = true ->
  BOXATM_flag_strong atm y = true ->
  P_branch_allFO atm P = P_branch_allFO (fun5'' (batm_comp_P atm) x (batm_comp_lx atm)) P.
Proof.
  induction m; intros n atm P x y Hnum Hleb Hbox.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate. reflexivity.

    destruct n.
    destruct atm; try discriminate. reflexivity.

    destruct atm; try discriminate.
    destruct atm; try discriminate.
    destruct atm1; try discriminate.
    simpl. apply (IHm (num_conn atm2) atm2 _ f f1).
      reflexivity.

      simpl in Hnum. inversion Hnum as [Hnum'].
      destruct n. discriminate.
      inversion Hnum' as [Hnum''].
      rewrite <- Hnum''. simpl in Hleb.
      destruct m. discriminate.
      apply leb_suc_r. assumption.

      apply BOXATM_flag_strong_cons in Hbox.
      assumption.
Qed.

Lemma lem_try3 : forall atm P x y,
  BOXATM_flag_strong atm y = true ->
  P_branch_allFO atm P = P_branch_allFO (fun5'' (batm_comp_P atm) x (batm_comp_lx atm)) P.
Proof.
  intros atm P x y.
  apply (lem_try3_pre (num_conn atm) (num_conn atm)).
  reflexivity. apply leb_refl.
Qed.

Lemma lem_try3_BAT_pre : forall m n atm P x y,
  n = num_conn atm ->
  Nat.leb n m = true ->
  BOXATM_flag_weak atm y = true ->
  P_branch_allFO atm P = P_branch_allFO (fun5'' (batm_comp_P atm) x (batm_comp_lx atm)) P.
Proof.
  induction m; intros n atm P x y Hnum Hleb Hbox.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate. reflexivity.

    destruct n.
    destruct atm; try discriminate. reflexivity.

    destruct atm; try discriminate.
    destruct atm; try discriminate.
    destruct atm1; try discriminate.
    simpl. apply (IHm (num_conn atm2) atm2 _ f f1).
      reflexivity.

      simpl in Hnum. inversion Hnum as [Hnum'].
      destruct n. discriminate.
      inversion Hnum' as [Hnum''].
      rewrite <- Hnum''. simpl in Hleb.
      destruct m. discriminate.
      apply leb_suc_r. assumption.

      apply BOXATM_flag_weak_cons in Hbox.
      assumption.
Qed.

Lemma lem_try3_BAT : forall atm P x y,
  BOXATM_flag_weak atm y = true ->
  P_branch_allFO atm P = P_branch_allFO (fun5'' (batm_comp_P atm) x (batm_comp_lx atm)) P.
Proof.
  intros atm P x y.
  apply (lem_try3_BAT_pre (num_conn atm) (num_conn atm)).
  reflexivity. apply leb_refl.
Qed.

Lemma calc_llv_P_allFO : forall alpha beta x P,
  calc_llv_P (allFO x (implSO beta alpha)) P =
  if P_branch_allFO (allFO x (implSO beta alpha)) P then
     cons (comp_cond_lx2 (allFO x (implSO beta alpha))) nil
      else nil.
Proof.
  reflexivity.
Qed.

Lemma comp_cond_lx2_allFO_predSO : forall alpha beta x,
  match beta with
  | predSO _ _ => true
  | _ => false
  end = true ->
  comp_cond_lx2 (allFO x (implSO alpha beta)) = nil.
Proof.  
  intros until 0. intros H.
  destruct beta; try reflexivity; try discriminate.
Qed.


Lemma comp_cond_lx2_allFO : forall alpha beta x,
  match beta with
  | predSO _ _ => true
  | _ => false
  end = false ->
  comp_cond_lx2 (allFO x (implSO alpha beta)) = cons x (comp_cond_lx2 beta).
Proof.  
  intros until 0. intros H.
  destruct beta; try reflexivity; try discriminate.
Qed.

Lemma BOXATM_flag_strong_allFO_eq : forall batm x1 x2 x3 x4,
  BOXATM_flag_strong (allFO x1 (implSO (relatSO x2 x3) batm)) x4 = true ->
  x1 = x3.
Proof.
  intros batm [x1] [x2] [x3] [x4] H.
  simpl in *. case_eq (beq_nat x4 x2); intros Hbeq; rewrite Hbeq in *.
    2 : discriminate.
  case_eq (beq_nat x1 x3); intros Hbeq2; rewrite Hbeq2 in *.
    2 : discriminate.
  rewrite (beq_nat_true _ _ Hbeq2).
    reflexivity.
Qed.



Lemma comp_cond_lx2_fun5''_pre : forall m n batm y,
  n = num_conn batm ->
  Nat.leb n m = true ->
  BOXATM_flag_strong batm y = true ->
  comp_cond_lx2 (fun5'' (batm_comp_P batm) y (batm_comp_lx batm)) =
  comp_cond_lx2 batm.
Proof.
  induction m; intros n batm y Hnum Hleb Hbox.
    destruct n. 2 : discriminate.
    destruct batm; try discriminate. reflexivity.

    destruct n.
    destruct  batm; try discriminate. reflexivity.

    destruct batm; try discriminate.
    destruct batm; try discriminate.
    destruct batm1; try discriminate.
    pose proof (BOXATM_flag_strong_cons _ _ _  _ _ Hbox) as Hbox2.
    simpl fun5''.

    destruct batm2; try discriminate.
      rewrite comp_cond_lx2_allFO_predSO; reflexivity.

      rewrite comp_cond_lx2_allFO.
      rewrite comp_cond_lx2_allFO. 
      rewrite (IHm (num_conn (allFO f2 batm2)) (allFO f2 batm2)).
      all : try reflexivity.

      simpl in Hnum. inversion Hnum as [Hnum'].   
      destruct n. discriminate. destruct n. discriminate.
      simpl. destruct m. destruct n; discriminate.
      inversion Hnum' as [Hnum''']. rewrite <- Hnum'''.
      apply leb_suc_l. assumption.

      apply BOXATM_flag_strong_allFO_eq in Hbox. rewrite Hbox in *.
      assumption.

      destruct f.
      simpl. destruct batm2; try reflexivity;
      try discriminate.
Qed.

Lemma comp_cond_lx2_fun5'' : forall batm y,
  BOXATM_flag_strong batm y = true ->
  comp_cond_lx2 (fun5'' (batm_comp_P batm) y (batm_comp_lx batm)) =
  comp_cond_lx2 batm.
Proof.
  intros batm y.
  apply (comp_cond_lx2_fun5''_pre (num_conn batm) (num_conn batm)).
    reflexivity.

    apply leb_refl.
Qed.

Lemma comp_cond_lx2_fun5''_pre_BAT : forall m n batm y,
  n = num_conn batm ->
  Nat.leb n m = true ->
  BOXATM_flag_weak batm y = true ->
  comp_cond_lx2 (fun5'' (batm_comp_P batm) y (batm_comp_lx batm)) =
  comp_cond_lx2 batm.
Proof.
  induction m; intros n batm y Hnum Hleb Hbox.
    destruct n. 2 : discriminate.
    destruct batm; try discriminate. reflexivity.

    destruct n.
    destruct  batm; try discriminate. reflexivity.

    destruct batm; try discriminate.
    destruct batm; try discriminate.
    destruct batm1; try discriminate.
    pose proof (BOXATM_flag_weak_cons _ _ _  _ _ Hbox) as Hbox2.
    simpl fun5''.

    destruct batm2; try discriminate.
      rewrite comp_cond_lx2_allFO_predSO; reflexivity.

      rewrite comp_cond_lx2_allFO.
      rewrite comp_cond_lx2_allFO. 
      rewrite (IHm (num_conn (allFO f2 batm2)) (allFO f2 batm2)).
      all : try reflexivity.

      simpl in Hnum. inversion Hnum as [Hnum'].   
      destruct n. discriminate. destruct n. discriminate.
      simpl. destruct m. destruct n; discriminate.
      inversion Hnum' as [Hnum''']. rewrite <- Hnum'''.
      apply leb_suc_l. assumption.

      apply BOXATM_flag_weak_allFO_eq in Hbox. rewrite Hbox in *.
      assumption.

      destruct f.
      simpl. destruct batm2; try reflexivity;
      try discriminate.
Qed.

Lemma comp_cond_lx2_fun5''_BAT : forall batm y,
  BOXATM_flag_weak batm y = true ->
  comp_cond_lx2 (fun5'' (batm_comp_P batm) y (batm_comp_lx batm)) =
  comp_cond_lx2 batm.
Proof.
  intros batm y.
  apply (comp_cond_lx2_fun5''_pre_BAT (num_conn batm) (num_conn batm)).
    reflexivity.

    apply leb_refl.
Qed.


Lemma calc_llv_P_fun5_l''_app : forall la1 la2 la3 lb1 lb2 lb3 P,
  length la1 = length la2 ->
  length la1 = length la3 ->
  calc_llv_P (fun5_l'' (app la1 lb1) (app la2 lb2) (app la3 lb3)) P =
  app (calc_llv_P (fun5_l'' la1 la2 la3) P) (calc_llv_P (fun5_l'' lb1 lb2 lb3) P).
Proof.
  induction la1; intros la2 la3 lb1 lb2 lb3 P Hl1 Hl2 .
    simpl in *. destruct la2. 2 : discriminate.
    destruct la3. 2 : discriminate. reflexivity.

    destruct la2. discriminate. destruct la3. discriminate.
    simpl. case_eq la1. intros Hla1.
      rewrite Hla1 in *. destruct la2. 2 : discriminate.
      destruct la3. 2 : discriminate.
      simpl. destruct lb1. destruct lb2. 
        simpl. rewrite app_nil_r. reflexivity.
        simpl. rewrite app_nil_r. reflexivity.

        destruct lb2. simpl. destruct lb1.
          simpl. rewrite app_nil_r. reflexivity.
          simpl. rewrite app_nil_r. reflexivity.

        destruct lb3. simpl. destruct lb1. destruct lb2.
          simpl. rewrite app_nil_r. reflexivity.
          simpl. rewrite app_nil_r. reflexivity.
          destruct lb2.
            simpl. rewrite app_nil_r. reflexivity.
            simpl. rewrite app_nil_r. reflexivity.

        simpl. reflexivity.
      intros P1 lP1 Hla1. rewrite <- Hla1.
      case_eq (app la1 lb1). intros Hnil.
        rewrite Hla1 in *. discriminate.
      intros PP1 lPP1 HlPP1. rewrite <- HlPP1.
      case_eq la2. intros Hnil. rewrite Hnil in *. rewrite Hla1 in *. discriminate.
      intros x2 lx2 Hla2. rewrite <- Hla2.
      case_eq (app la2 lb2). intros Hnil. rewrite Hla2 in *. discriminate.
      intros xx2 lxx2 Hlxx2. rewrite <- Hlxx2.
      case_eq la3. intros Hnil. rewrite Hnil in *. rewrite Hla1 in *. discriminate.
      intros x3 lx3 Hla3. rewrite <- Hla3.
      case_eq (app la3 lb3). intros Hnil. rewrite Hla3 in *. discriminate.
      intros xx3 lxx3 Hlxx3. rewrite <- Hlxx3.
      simpl. rewrite IHla1. rewrite app_assoc. reflexivity.
      simpl in Hl1. inversion Hl1. reflexivity.
      simpl in Hl2. inversion Hl2. reflexivity.
Qed.

Lemma calc_lx1_P_fun5_l''_app : forall la1 la2 la3 lb1 lb2 lb3 P,
  length la1 = length la2 ->
  length la1 = length la3 ->
  calc_lx1_P (fun5_l'' (app la1 lb1) (app la2 lb2) (app la3 lb3)) P =
  app (calc_lx1_P (fun5_l'' la1 la2 la3) P) (calc_lx1_P (fun5_l'' lb1 lb2 lb3) P).
Proof.
  induction la1; intros la2 la3 lb1 lb2 lb3 P Hl1 Hl2 .
    simpl in *. destruct la2. 2 : discriminate.
    destruct la3. 2 : discriminate. reflexivity.

    destruct la2. discriminate. destruct la3. discriminate.
    simpl. case_eq la1. intros Hla1.
      rewrite Hla1 in *. destruct la2. 2 : discriminate.
      destruct la3. 2 : discriminate.
      simpl. destruct lb1. destruct lb2. 
        simpl. rewrite app_nil_r. reflexivity.
        simpl. rewrite app_nil_r. reflexivity.

        destruct lb2. simpl. destruct lb1.
          simpl. rewrite app_nil_r. reflexivity.
          simpl. rewrite app_nil_r. reflexivity.

        destruct lb3. simpl. destruct lb1. destruct lb2.
          simpl. rewrite app_nil_r. reflexivity.
          simpl. rewrite app_nil_r. reflexivity.
          destruct lb2.
            simpl. rewrite app_nil_r. reflexivity.
            simpl. rewrite app_nil_r. reflexivity.

        simpl. reflexivity.
      intros P1 lP1 Hla1. rewrite <- Hla1.
      case_eq (app la1 lb1). intros Hnil.
        rewrite Hla1 in *. discriminate.
      intros PP1 lPP1 HlPP1. rewrite <- HlPP1.
      case_eq la2. intros Hnil. rewrite Hnil in *. rewrite Hla1 in *. discriminate.
      intros x2 lx2 Hla2. rewrite <- Hla2.
      case_eq (app la2 lb2). intros Hnil. rewrite Hla2 in *. discriminate.
      intros xx2 lxx2 Hlxx2. rewrite <- Hlxx2.
      case_eq la3. intros Hnil. rewrite Hnil in *. rewrite Hla1 in *. discriminate.
      intros x3 lx3 Hla3. rewrite <- Hla3.
      case_eq (app la3 lb3). intros Hnil. rewrite Hla3 in *. discriminate.
      intros xx3 lxx3 Hlxx3. rewrite <- Hlxx3.
      simpl. rewrite IHla1. rewrite app_assoc. reflexivity.
      simpl in Hl1. inversion Hl1. reflexivity.
      simpl in Hl2. inversion Hl2. reflexivity.
Qed.

Lemma calc_llv_P_fun5_l''_pre : forall m n batm P,
  n = num_conn batm ->
  Nat.leb n m = true ->
  is_BOXATM_flag_strong_CONJ batm = true ->
  calc_llv_P (fun5_l'' (batm_conj_comp_P batm) (batm_conj_comp_x1 batm) (batm_conj_comp_lx batm)) P =
  calc_llv_P batm P.
Proof.
  induction m; intros n batm P Hnum Hleb Hbox.
    destruct n. 2 : discriminate.
    destruct batm; try discriminate. reflexivity.

    destruct n.
    destruct batm; try discriminate. reflexivity.

    destruct batm; try discriminate.
    destruct f as [xn]. destruct xn. discriminate.
    destruct batm; try discriminate.
    pose proof (is_BOXATM_flag_strong__CONJ _ _ _  Hbox) as H1.
    destruct batm1; try discriminate.
    pose proof (is_BOXATM_flag_strong_CONJ_allFO_eq _ _  _ _ Hbox) as H2.
    simpl batm_conj_comp_P.
    simpl batm_conj_comp_x1. simpl batm_conj_comp_lx.
    simpl fun5_l''.
    do 2 rewrite calc_llv_P_allFO.
    case_eq (P_branch_allFO (allFO (Var (S xn)) (implSO (relatSO f f0) batm2)) P); intros HP.
      simpl in HP. 
      rewrite lem_try3 with (x := (Var (S xn))) (y := (Var (S xn))) in HP.
        2 : assumption.
      simpl P_branch_allFO.
      rewrite HP.
  
      pose proof (comp_cond_lx2_fun5'' (allFO (Var (S xn)) (implSO (relatSO f f0) batm2)) f) as HH.
      simpl fun5'' in HH. rewrite HH. reflexivity.
      apply is__BOXATM_flag_strong_CONJ. assumption.

      simpl in HP. 
      rewrite lem_try3 with (x := (Var (S xn))) (y := (Var (S xn))) in HP.
        2 : assumption.
      simpl P_branch_allFO.
      rewrite HP. reflexivity.

      simpl.
      rewrite calc_llv_P_fun5_l''_app.
      rewrite (IHm (num_conn batm1) batm1).
      rewrite (IHm (num_conn batm2) batm2).
      all : try reflexivity.
      all : try (apply length_batm_conj_comp_P_x1).
      all : try (apply length_batm_conj_comp_P_lx).
      all : try (apply is_BOXATM_flag_strong_CONJ_conjSO_l in Hbox; assumption).
      all : try (apply is_BOXATM_flag_strong_CONJ_conjSO_r in Hbox; assumption).

      simpl in Hnum. inversion Hnum as [Hnum'].
      rewrite Hnum' in *.
      apply leb_plus_take2 in Hleb. assumption.
      simpl in Hnum. inversion Hnum as [Hnum'].
      rewrite Hnum' in *.
      apply leb_plus_take1 in Hleb. assumption.
Qed.

Lemma calc_llv_P_fun5_l'' : forall batm P,
  is_BOXATM_flag_strong_CONJ batm = true ->
  calc_llv_P (fun5_l'' (batm_conj_comp_P batm) (batm_conj_comp_x1 batm) (batm_conj_comp_lx batm)) P =
  calc_llv_P batm P.
Proof.
  intros batm P. apply (calc_llv_P_fun5_l''_pre (num_conn batm) (num_conn batm)).
  reflexivity. apply leb_refl.
Qed.

Lemma calc_llv_P_fun5_l''_pre_BAT : forall m n batm P,
  n = num_conn batm ->
  Nat.leb n m = true ->
  BAT batm = true ->
  calc_llv_P (fun5_l'' (batm_conj_comp_P batm) (batm_conj_comp_x1 batm) (batm_conj_comp_lx batm)) P =
  calc_llv_P batm P.
Proof.
  induction m; intros n batm P Hnum Hleb Hbox.
    destruct n. 2 : discriminate.
    destruct batm; try discriminate. reflexivity.

    destruct n.
    destruct batm; try discriminate. reflexivity.

    destruct batm; try discriminate.
    destruct f as [xn]. (*  destruct xn. discriminate. *)
    destruct batm; try discriminate.
    pose proof (is_BOXATM_flag_strong__CONJ_BAT _ _ _  Hbox) as H1.
    destruct batm1; try discriminate.
    pose proof (is_BOXATM_flag_strong_CONJ_allFO_eq_BAT _ _  _ _ Hbox) as H2.
    simpl batm_conj_comp_P.
    simpl batm_conj_comp_x1. simpl batm_conj_comp_lx.
    simpl fun5_l''.
    do 2 rewrite calc_llv_P_allFO.
    case_eq (P_branch_allFO (allFO (Var (xn)) (implSO (relatSO f f0) batm2)) P); intros HP.
      simpl in HP. 
      rewrite lem_try3_BAT with (x := (Var ( xn))) (y := (Var ( xn))) in HP.
        2 : assumption.
      simpl P_branch_allFO.
      rewrite HP.
  
      pose proof (comp_cond_lx2_fun5''_BAT (allFO (Var (xn)) (implSO (relatSO f f0) batm2)) f) as HH.
      simpl fun5'' in HH. rewrite HH. reflexivity.
      apply is__BAT. assumption.

      simpl in HP. 
      rewrite lem_try3_BAT with (x := (Var (xn))) (y := (Var (xn))) in HP.
        2 : assumption.
      simpl P_branch_allFO.
      rewrite HP. reflexivity.

      simpl.
      rewrite calc_llv_P_fun5_l''_app.
      rewrite (IHm (num_conn batm1) batm1).
      rewrite (IHm (num_conn batm2) batm2).
      all : try reflexivity.
      all : try (apply length_batm_conj_comp_P_x1_BAT).
      all : try (apply length_batm_conj_comp_P_lx_BAT).
      all : try (apply BAT_conjSO_l in Hbox; assumption).
      all : try (apply BAT_conjSO_r in Hbox; assumption).

      simpl in Hnum. inversion Hnum as [Hnum'].
      rewrite Hnum' in *.
      apply leb_plus_take2 in Hleb. assumption.
      simpl in Hnum. inversion Hnum as [Hnum'].
      rewrite Hnum' in *.
      apply leb_plus_take1 in Hleb. assumption.
Qed.

Lemma calc_llv_P_fun5_l''_BAT : forall batm P,
  BAT batm = true ->
  calc_llv_P (fun5_l'' (batm_conj_comp_P batm) (batm_conj_comp_x1 batm) (batm_conj_comp_lx batm)) P =
  calc_llv_P batm P.
Proof.
  intros batm P. apply (calc_llv_P_fun5_l''_pre_BAT (num_conn batm) (num_conn batm)).
  reflexivity. apply leb_refl.
Qed.
(* 
Fixpoint  max_FOv_l (l : list FOvariable) : nat :=
  match l with
  | nil => 0
  | cons (Var xn) l' => max xn (max_FOv_l l')
  end. *)
          
Lemma max_FOv_fun5'' : forall lx xn P,
  max_FOv (fun5'' P (Var xn) lx) = max xn (max_FOv_l lx).
Proof.
  induction lx; intros xn P.
    simpl. rewrite max_comm. reflexivity.

    simpl. destruct a as [ym]. rewrite IHlx.
    rewrite (max_comm ym (max_FOv_l lx)). rewrite <- max_max.
    rewrite (max_comm _ ym). 
    rewrite PeanoNat.Nat.max_assoc.
    rewrite max_refl. 
    rewrite PeanoNat.Nat.max_assoc.
    rewrite (max_comm ym xn).
    rewrite <- PeanoNat.Nat.max_assoc.
    rewrite (max_comm ym). reflexivity.
Qed.

Lemma max_FOv_l_batm_comp_lx_pre : forall m n atm xn,
S n = num_conn atm ->
Nat.leb n m = true ->
  BOXATM_flag_strong atm (Var xn) = true ->
   max xn  (max_FOv_l (batm_comp_lx atm)) = max_FOv atm.
Proof.
  induction m; intros n atm xn Hnum Hleb Hbox.
    destruct n.  destruct atm; try discriminate.
    simpl in *.
    destruct atm; try discriminate. discriminate.

    destruct atm; try discriminate. 
    destruct atm; try discriminate.
    simpl. destruct f as [zn].
    destruct atm1; try discriminate.
    destruct f as [y1]. destruct f0 as [y2].
    rewrite (PeanoNat.Nat.max_assoc zn).
    simpl.
    rewrite (max_comm y1 y2).
    rewrite (PeanoNat.Nat.max_assoc zn).
    pose proof (BOXATM_flag_strong_allFO_eq _ _ _ _ _ Hbox) as H2.
      inversion H2 as [H2'].
    rewrite max_refl.
    simpl in Hbox.
    case_eq (beq_nat xn y1); intros Hbeq; rewrite Hbeq in *.
      2 : discriminate.
    rewrite (beq_nat_true _ _ Hbeq) in *.
    rewrite (max_comm y2 y1).
    rewrite <- PeanoNat.Nat.max_assoc.

    case_eq (num_conn atm2).
         intros H. destruct atm2; try discriminate.
            simpl. destruct f as [un]. simpl in *.

          destruct n. discriminate. destruct n. 2 : discriminate.
          rewrite H2' in *. rewrite <- beq_nat_refl in *.
          case_eq (beq_nat y2 (S y1)); intros Hbeq2;
            rewrite Hbeq2 in *. 2 : discriminate.
          rewrite (beq_nat_true _ _ Hbox). rewrite max_refl.
          rewrite (max_comm un 0). reflexivity.

        do 2 rewrite if_then_else_false in Hbox. discriminate.

        do 2 rewrite if_then_else_false in Hbox. discriminate.


      intros n' Hnum'.
    specialize (IHm n' atm2 y2).
    rewrite Hnum' in IHm. specialize (IHm eq_refl).
    assert (Nat.leb n' m = true) as Hass1.
      simpl in Hnum. rewrite Hnum' in Hnum.
      inversion Hnum as [Hnum''].
      rewrite Hnum'' in Hleb. simpl in Hleb.
      apply leb_suc_l. assumption.

    assert (BOXATM_flag_strong atm2 (Var y2) = true) as Hass2.
      rewrite H2' in Hbox. rewrite <- beq_nat_refl in Hbox.
      case_eq (beq_nat y2 (S y1)); intros Hbeq2; rewrite Hbeq2 in *.
        2 : discriminate. assumption.

    specialize (IHm Hass1 Hass2).
    destruct (max_or y2 (max_FOv_l (batm_comp_lx atm2))) as [H3 | H4].
      rewrite H3 in *. rewrite IHm. rewrite max_refl.
      reflexivity.

      rewrite H4 in *. rewrite IHm in *. rewrite H4. reflexivity.
Qed.

Lemma max_FOv_l_batm_comp_lx : forall atm xn,
  BOXATM_flag_strong atm (Var xn) = true ->
  max xn (max_FOv_l (batm_comp_lx atm)) = max_FOv atm.
Proof.
  intros atm xn.
  case_eq (num_conn atm).
    intros Hnil. destruct atm; try discriminate.
    simpl. destruct f as [ym]. destruct xn.
      intros H. rewrite <- (beq_nat_true _ _ H). reflexivity.

      intros H. simpl in *. destruct ym. discriminate. rewrite (beq_nat_true _ _ H).
      reflexivity.

    intros n' Hnum.
    apply (max_FOv_l_batm_comp_lx_pre n' n').
      symmetry. assumption.

      apply leb_refl.
Qed.

Lemma is_in_FOvar_0_batm''_pre : forall m n atm x,
n = num_conn atm ->
Nat.leb n m = true ->
  BOXATM_flag_strong atm x = true ->
  ~ (batm_comp_x1 atm) = (Var 0) ->
  is_in_FOvar (Var 0) (FOvars_in (fun5'' (batm_comp_P atm)
    (batm_comp_x1 atm) (batm_comp_lx atm))) = false.
Proof.
  induction m; intros n atm x Hnum Hleb Hbox Hnot.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
    simpl in *. destruct x as [xn]. destruct f as [ym].
    destruct ym. contradiction (Hnot eq_refl).
    reflexivity.

    destruct n. 
    destruct atm; try discriminate.
    simpl in *. destruct x as [xn]. destruct f as [ym].
    destruct ym. contradiction (Hnot eq_refl).
    reflexivity.

    simpl in Hleb. destruct atm; try discriminate.
    simpl in Hnum. inversion Hnum as [Hnum'].
    destruct atm; try discriminate.
    destruct atm1; try discriminate.
    pose proof Hbox as Hbox'.
    simpl. destruct f0 as [y1]. destruct f1 as [y2].
    simpl. destruct y1. simpl in *. contradiction (Hnot eq_refl).
    simpl in Hbox. destruct x as [xn].
    destruct f as [y3]. case_eq (beq_nat y2 (S (S y1)));
      intros Hbeq; rewrite Hbeq in *.

     destruct y3. 
      destruct y2; simpl in *; rewrite if_then_else_false in Hbox';
        discriminate.
     destruct y2.    
        discriminate. 

pose proof (is_BOXATM_flag_strong_CONJ_allFO_x1 atm2 (Var (S y3)) 
  (Var (S y1)) (Var (S y2)) (is_BOXATM_flag_strong__CONJ2 _ _  Hbox')) as H.
    case_eq (beq_nat (S y3) (S y2)); intros Hbeq0; rewrite Hbeq0 in *.
      simpl in Hbeq0. rewrite (beq_nat_true _ _ Hbeq0).

     rewrite <- (is_BOXATM_flag_strong_CONJ_allFO_x1 atm2 (Var (S y3)) (Var (S y1)) (Var (S y2))).
    apply (IHm (num_conn atm2) _ (Var (S y2))). reflexivity.

    simpl in Hnum'.
    rewrite Hnum' in Hleb. apply leb_suc_l. assumption.

    case_eq (PeanoNat.Nat.eqb y3 y2); intros Hbeq2; 
      rewrite Hbeq2 in *. rewrite (beq_nat_true _ _ Hbeq2) in Hbox.
    case_eq (BOXATM_flag_strong atm2 (Var (S y2))); intros Hbox2.
      reflexivity. rewrite Hbox2 in *. rewrite if_then_else_false in *. discriminate.
    discriminate.

    rewrite (is_BOXATM_flag_strong_CONJ_allFO_x1 atm2 (Var (S y3)) (Var (S y1)) (Var (S y2))).
    rewrite (beq_nat_true _ _ Hbeq). discriminate.
    simpl. destruct y3. simpl in *. destruct y2. discriminate.
    rewrite if_then_else_false in *. discriminate.
    case_eq (PeanoNat.Nat.eqb xn (S y1)); intros H1; rewrite H1 in *.
      2 : discriminate.
    case_eq (PeanoNat.Nat.eqb (S y3) y2); intros H2; rewrite H2 in *.
      2 : discriminate.
    rewrite Hbox. simpl in Hbeq. rewrite Hbeq. rewrite (beq_nat_true _ _ Hbeq) in H2.
    rewrite H2. reflexivity.

    simpl. rewrite Hbeq0. 
    simpl in Hbeq. rewrite Hbeq.
    rewrite (beq_nat_true _ _ Hbeq) in Hbeq0. rewrite Hbeq0.
    case_eq (beq_nat xn (S y1)); intros Hbeq2; rewrite Hbeq2 in *. 
      2 : discriminate.
    assumption. rewrite if_then_else_false in Hbox. discriminate.

simpl. destruct y3. destruct y2. simpl in *. rewrite if_then_else_false in *.
   discriminate. simpl in *.
  rewrite if_then_else_false in Hbox. discriminate.
  case_eq (beq_nat xn (S y1)); intros Hbeq2; rewrite Hbeq2 in *.
    2 : discriminate.
  case_eq (beq_nat (S y3) y2); intros Hbeq3; rewrite Hbeq3 in *.
    2 : discriminate.

  discriminate.
Qed.

Lemma is_in_FOvar_0_batm_conj''_pre : forall m n atm,
n = num_conn atm ->
Nat.leb n m = true ->

  is_BOXATM_flag_strong_CONJ atm = true ->
  is_in_FOvar (Var 0) (batm_conj_comp_x1 atm) = false ->
  is_in_FOvar (Var 0) (FOvars_in (fun5_l'' (batm_conj_comp_P atm)
    (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm))) = false.
Proof.
  induction m; intros n atm Hnum Hleb Hbox Hin.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate. assumption.

    destruct n.     destruct atm; try discriminate.
    assumption.

    destruct atm; try discriminate.
    destruct f as [xn]. destruct xn. discriminate.
    destruct atm; try discriminate. destruct atm1; try discriminate.
    simpl. destruct f as [y1]. destruct f0 as [y2].
    destruct y1. simpl in *. discriminate.
pose proof (is_BOXATM_flag_strong_CONJ_allFO_x1 _ _ _ _ Hbox) as Heq.
    pose proof (is_BOXATM_flag_strong_CONJ_allFO_eq _ _ _ _ Hbox) as Heq2.
    pose proof (is_BOXATM_flag_strong_CONJ_allFO_relatSO _ _ _ _ Hbox) as Heq3.
    simpl in Heq3.

    simpl in *. destruct y2. rewrite if_then_else_false in Hbox.
    discriminate. rewrite Heq2.
    rewrite Heq3 in *. rewrite <- Heq.
    rewrite <- Heq3 in *. rewrite <- Heq2 in *. rewrite <- beq_nat_refl in *. 
    rewrite Heq2 in *. rewrite Heq3 in *. 
    inversion Heq2 as [Heq2']. rewrite Heq2' in Hbox.  inversion Heq3 as [Heq3'].
    rewrite Heq3' in Hbox. rewrite <- beq_nat_refl in Hbox.

    rewrite Heq. rewrite <- Heq.
 apply is_in_FOvar_0_batm'' with (x := (Var (S (S y1)))).
    assumption. intros HH. rewrite HH in *. discriminate.

  simpl in *. case_eq (batm_conj_comp_P atm2).
    intros H. pose proof H as H'. 
    apply batm_conj_comp_P_x1_nil in H. rewrite H.
    apply batm_conj_comp_P_lx_nil in H'. rewrite H'.
    simpl. do 3 rewrite app_nil_r. apply (IHm (num_conn atm1) atm1).
    reflexivity.
    simpl in Hnum. inversion Hnum as [Hnum'].
    rewrite Hnum' in Hleb. simpl in Hleb.
    apply leb_plus_take1 in Hleb. assumption.
    apply is_BOXATM_flag_strong_CONJ_conjSO_l in Hbox. assumption.

    simpl in Hin.     rewrite is_in_FOvar_app in *.
    case_eq (is_in_FOvar (Var 0) (batm_conj_comp_x1 atm1));
      intros Hin2; rewrite Hin2 in *. discriminate.
    reflexivity.

    apply is_BOXATM_flag_strong_CONJ_conjSO_r in Hbox. assumption.
    apply is_BOXATM_flag_strong_CONJ_conjSO_r in Hbox. assumption.

    intros P lP HlP. rewrite <- HlP.

    simpl. simpl in Hin. rewrite FOvars_in_fun5_l''_app.
    rewrite is_in_FOvar_app in *.
    rewrite (IHm (num_conn atm1) atm1). apply (IHm (num_conn atm2) atm2).
      all : try reflexivity.

    simpl in Hnum. inversion Hnum as [Hnum'].
    rewrite Hnum' in Hleb. simpl in Hleb.
    apply leb_plus_take2 in Hleb. assumption.

    apply is_BOXATM_flag_strong_CONJ_conjSO_r in Hbox. assumption.

    case_eq (is_in_FOvar (Var 0) (batm_conj_comp_x1 atm1));
      intros Hin2; rewrite Hin2 in *. discriminate.
    assumption.

    simpl in Hnum. inversion Hnum as [Hnum'].
    rewrite Hnum' in Hleb. simpl in Hleb.
    apply leb_plus_take1 in Hleb. assumption.

    apply is_BOXATM_flag_strong_CONJ_conjSO_l in Hbox. assumption.

    case_eq (is_in_FOvar (Var 0) (batm_conj_comp_x1 atm1));
      intros Hin2; rewrite Hin2 in *. discriminate.
    reflexivity.

    apply length_batm_conj_comp_P_x1.
    apply is_BOXATM_flag_strong_CONJ_conjSO_l in Hbox. assumption.

    apply length_batm_conj_comp_P_lx.
    apply is_BOXATM_flag_strong_CONJ_conjSO_l in Hbox. assumption.

    apply batm_conj_comp_P_not_nil.
    apply is_BOXATM_flag_strong_CONJ_conjSO_l in Hbox. assumption.

    apply batm_conj_comp_P_not_nil.
    apply is_BOXATM_flag_strong_CONJ_conjSO_r in Hbox. assumption.

    case_eq (batm_conj_comp_x1 atm2). intros HH.
      apply batm_conj_comp_P_x1_nil in HH. rewrite HH in *. discriminate.
    apply is_BOXATM_flag_strong_CONJ_conjSO_r in Hbox. assumption.
      discriminate.

    case_eq (batm_conj_comp_lx atm2). intros HH.
      apply batm_conj_comp_P_lx_nil in HH. rewrite HH in *. discriminate.
    apply is_BOXATM_flag_strong_CONJ_conjSO_r in Hbox. assumption.
      discriminate.
Qed.


Lemma is_in_FOvar_0_batm_conj'' : forall atm,
  is_BOXATM_flag_strong_CONJ atm = true ->
  is_in_FOvar (Var 0) (batm_conj_comp_x1 atm) = false ->
  is_in_FOvar (Var 0) (FOvars_in (fun5_l'' (batm_conj_comp_P atm)
    (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm))) = false.
Proof.
  intros atm. apply (is_in_FOvar_0_batm_conj_pre'' (num_conn atm) (num_conn atm)).
  reflexivity. apply leb_refl.
Qed.

Lemma max_FOv_fun5_l''_pre_pre : forall m n atm,
n = num_conn atm ->
Nat.leb n m = true ->
is_BOXATM_flag_strong_CONJ atm = true ->
is_in_FOvar (Var 0) (batm_conj_comp_x1 atm)  = false ->
(max_FOv  (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm)
     (batm_conj_comp_lx atm))) =
 max_FOv atm.
Proof.
  induction m; intros n atm Hnum Hleb Hat Hnot.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate. reflexivity.

    destruct n.
    destruct atm; try discriminate. reflexivity.
    simpl in Hleb. destruct atm; try discriminate.
      destruct f as [xn]. destruct xn. discriminate.
      destruct atm; try discriminate.
      destruct atm1; try discriminate.
      destruct f as [y1]. destruct f0 as [y2].
      simpl.


      pose proof (is_BOXATM_flag_strong_CONJ_allFO_eq _ _ _ _ Hat) as Hat1.
      pose proof (is_BOXATM_flag_strong_CONJ_allFO_atm _ _ _ _ Hat) as Hat2.
      pose proof (is_BOXATM_flag_strong_CONJ_allFO_x1 _ _ _ _ Hat) as Hat3.
      pose proof (is_BOXATM_flag_strong_CONJ_allFO_relatSO _ _ _ _ Hat) as Hat4.
      simpl in Hat4.
      rewrite (max_r y1). simpl. 
      rewrite max_FOv_fun5''. simpl.
      rewrite <- max_FOv_l_batm_comp_lx with (xn := y2).
      rewrite <- (PeanoNat.Nat.max_assoc y1 y2).
      rewrite (PeanoNat.Nat.max_assoc y2 y2).
      rewrite max_refl.
      rewrite (PeanoNat.Nat.max_assoc y1 y2).
      remember (max_FOv_l (batm_comp_lx atm2)) as t.
      case_eq t.
        intros Ht. rewrite max_refl. rewrite max_refl.
        rewrite max_comm. simpl.
        rewrite Hat4. rewrite max_S.
        inversion Hat1 as [Hat1'].
        rewrite <- Hat1' in Hat4.
        inversion Hat4 as [Hat4']. 
        rewrite max_refl. reflexivity.

        intros t2 Ht2. rewrite (PeanoNat.Nat.max_assoc xn xn).
        rewrite max_refl.
        rewrite (PeanoNat.Nat.max_assoc xn xn).
        rewrite max_refl. rewrite Hat4.
        rewrite max_S. simpl.
        do 3 rewrite PeanoNat.Nat.succ_max_distr.
        rewrite <- Ht2. rewrite Heqt.
        rewrite Hat4 in Hat1.
        inversion Hat1 as [Hat1'].
        rewrite PeanoNat.Nat.max_assoc.
        rewrite max_refl. reflexivity. assumption.
  
        inversion Hat1 as [Hat1']. rewrite Hat1'. 
        rewrite Hat4. apply le_S. apply le_n.

        simpl in Hat. 
        case_eq (is_BOXATM_flag_strong_CONJ atm1); intros Hat1;
          rewrite Hat1 in *. 2 : discriminate.
        simpl.
        rewrite max_FOv_fun5_l''_app'.
          rewrite (IHm (num_conn atm1) atm1).
          rewrite (IHm (num_conn atm2) atm2).
          all : try  reflexivity.

          simpl in Hnum. inversion Hnum as [Hnum'].
          rewrite Hnum' in Hleb.
          apply leb_plus_take2 in Hleb. assumption.

          simpl in Hnum. inversion Hnum as [Hnum'].
          rewrite Hnum' in Hleb.
          apply leb_plus_take1 in Hleb. assumption.


(*         apply try2. assumption. simpl in Hnot.  *)

        apply is_in_FOvar_app_r in Hnot. assumption.

          simpl in Hnum. inversion Hnum as [Hnum'].
          rewrite Hnum' in Hleb.
          apply leb_plus_take1 in Hleb. assumption.

          assumption.

(*         apply try2. assumption. simpl in Hnot.  *)

        apply is_in_FOvar_app_l in Hnot. assumption.

        apply length_batm_conj_comp_P_x1. assumption.
        apply length_batm_conj_comp_P_lx. assumption.

simpl in Hnot. apply is_in_FOvar_app_l in Hnot.

          apply is_in_FOvar_0_batm_conj''; assumption.
simpl in Hnot. apply is_in_FOvar_app_r in Hnot.
          apply is_in_FOvar_0_batm_conj''; assumption.
Qed.

Lemma is_in_FOvar_max_FOv_l: forall alpha x,
  BAT alpha = true ->
  is_in_FOvar x (FOvars_in alpha) = false ->
 ~ (x = Var (max_FOv_l (batm_comp_lx alpha))).
Admitted.

Lemma max_random1 : forall a b c,
  max a (max (max b a) (max a c)) =
  max b (max a c).
Proof.
  intros a b c.
  rewrite (max_comm b a).
  rewrite (PeanoNat.Nat.max_assoc).
  rewrite (PeanoNat.Nat.max_assoc a a b).
  rewrite max_refl.
  rewrite (max_comm a b).
  rewrite (max_comm a c).
  rewrite  <- max_max.
  rewrite PeanoNat.Nat.max_assoc.
  reflexivity.
Qed.

Lemma max_FOv_batm_comp_num_conn : forall m n atm x,
  n = num_conn atm ->
  Nat.leb n m = true ->
  BOXATM_flag_weak atm x = true ->
  (max_FOv atm) = max (match (batm_comp_x1 atm) with Var n => n end)
      (max_FOv_l (batm_comp_lx atm)).
Proof.
  induction m; intros n atm x Hnum Hleb H; try discriminate.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
    simpl. destruct f as [xn]. rewrite PeanoNat.Nat.max_0_r.
    reflexivity.

    destruct n.
    destruct atm; try discriminate.
    simpl. destruct f as [xn]. rewrite PeanoNat.Nat.max_0_r.
    reflexivity.

    destruct atm; try discriminate.
    destruct atm; try discriminate.
    destruct atm1; try discriminate.
    simpl batm_comp_x1.
    simpl batm_comp_lx.
    destruct f as [xn].
    destruct f0 as [ym].
    destruct f1 as [zn]. simpl.
    pose proof (BOXATM_flag_weak_allFO_eq _ _ _ _ _ H) as H2.
    pose proof (BOXATM_flag_weak_allFO _ _ _ _ _ H) as H3.
    pose proof (try3_BAT _ _  H3) as H4.
    rewrite (IHm (num_conn atm2) atm2 (Var xn)).
    rewrite H4. 
    inversion H2 as [H2'].
    rewrite H2' in *.
    apply max_random1.
    reflexivity.
          simpl in Hnum. inversion Hnum as [Hnum'].
          rewrite Hnum' in Hleb. simpl in Hleb.
          destruct m. discriminate. apply leb_suc_r. assumption.
          assumption.
Qed.

Lemma max_FOv_batm_comp : forall atm x,
  BOXATM_flag_weak atm x = true ->
  (max_FOv atm) = max (match (batm_comp_x1 atm) with Var n => n end)
      (max_FOv_l (batm_comp_lx atm)).
Proof.
  intros atm x. apply (max_FOv_batm_comp_num_conn (num_conn atm)
    (num_conn atm) _ _ eq_refl (leb_refl _)).
Qed.


Lemma is_in_FOvar_fun5''_num_conn  : forall m n atm x z,
  n = num_conn atm ->
  Nat.leb n m = true ->
  BOXATM_flag_weak atm z = true ->
  is_in_FOvar x (FOvars_in (fun5''
    (batm_comp_P atm) (batm_comp_x1 atm)
    (batm_comp_lx atm))) =
  is_in_FOvar x (FOvars_in atm).
Proof.
  induction m; intros n atm x z Hnum Hleb H.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
    simpl. reflexivity.

    destruct n. 
    destruct atm; try discriminate.
    simpl. reflexivity.

    destruct atm; try discriminate.
    destruct atm; try discriminate.
    destruct atm1; try discriminate.
    simpl.

    destruct x as [xn]. destruct f as [zn].
    destruct f0 as [y1]; destruct f1 as [y2].
    destruct z as [un].

    pose proof (try3_BAT _ _ H) as H2.
    rewrite <- H2 in H.
    rewrite <- BAT_BOXATM_flag_weak_allFO in H.
    apply BAT_allFO in H.
    destruct H as [H3 H4].
    inversion H3 as [H3'].
    rewrite H3' in *.
    pose proof (try3_BAT _ _ H4) as H5. 
    rewrite <- H5. 
    rewrite (IHm (num_conn atm2) atm2 _ (Var y2)).
    all : try reflexivity.
          simpl in Hnum. inversion Hnum as [Hnum'].
          rewrite Hnum' in Hleb. simpl in Hleb.
          destruct m. discriminate. apply leb_suc_r. assumption.
          assumption.
Qed.

Lemma is_in_FOvar_fun5''  : forall atm x z,
  BOXATM_flag_weak atm z = true ->
  is_in_FOvar x (FOvars_in (fun5''
    (batm_comp_P atm) (batm_comp_x1 atm)
    (batm_comp_lx atm))) =
  is_in_FOvar x (FOvars_in atm).
Proof.
  intros atm x z.
  apply (is_in_FOvar_fun5''_num_conn (num_conn atm) (num_conn atm)
     _ _ _ eq_refl (leb_refl _)).
Qed.


Lemma is_in_FOvar_fun5_l''_num_conn  : forall m n atm x,
  n = num_conn atm ->
  Nat.leb n m = true ->
  BAT atm = true ->
  is_in_FOvar x (FOvars_in (fun5_l''
    (batm_conj_comp_P atm) (batm_conj_comp_x1 atm)
    (batm_conj_comp_lx atm))) =
  is_in_FOvar x (FOvars_in atm).
Proof.
  induction m; intros n atm [xn] Hnum Hleb H; try discriminate.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
    simpl in *. destruct f as [ym]. reflexivity.

    destruct n. 
    destruct atm; try discriminate.
    simpl in *. destruct f as [ym]. reflexivity.

    destruct atm; try discriminate.
    destruct atm; try discriminate.
    destruct atm1; try discriminate.
    simpl. destruct f as [z1]; destruct f0 as [z2].
    destruct f1 as [z3].
    rewrite BAT_BOXATM_flag_weak_allFO in H.
    simpl in H. rewrite <- beq_nat_refl in H.
    case_eq (beq_nat z1 z3); intros Hbeq; rewrite Hbeq in *.
      2 : discriminate.
    pose proof (try3_BAT _ _ H) as H2.
    rewrite (beq_nat_true _ _ Hbeq) in *.
    rewrite <- H2.

    rewrite (is_in_FOvar_fun5'' _ _ _ H).
    reflexivity.

    simpl.
 rewrite FOvars_in_fun5_l''_app.
    do 2 rewrite is_in_FOvar_app.
    rewrite (IHm (num_conn atm1) atm1 (Var xn)).
    rewrite (IHm (num_conn atm2) atm2 (Var xn)).  
    all : try reflexivity.

          simpl in Hnum. inversion Hnum as [Hnum'].
          rewrite Hnum' in Hleb.
          apply leb_plus_take2 in Hleb. assumption.

          apply (BAT_conjSO_r _ _ H).

          simpl in Hnum. inversion Hnum as [Hnum'].
          rewrite Hnum' in Hleb.
          apply leb_plus_take1 in Hleb. assumption.

          apply (BAT_conjSO_l _ _ H).

    apply length_batm_conj_comp_P_x1_BAT. 
      apply (BAT_conjSO_l _ _ H).

    apply length_batm_conj_comp_P_lx_BAT. 
      apply (BAT_conjSO_l _ _ H).

    apply batm_conj_comp_P_not_nil_BAT.
      apply (BAT_conjSO_l _ _ H).

    apply batm_conj_comp_P_not_nil_BAT.
      apply (BAT_conjSO_r _ _ H).

    apply batm_conj_comp_x1_not_nil_BAT.
      apply (BAT_conjSO_r _ _ H).

    apply batm_conj_comp_lx_not_nil_BAT.
      apply (BAT_conjSO_r _ _ H).
Qed.

Lemma fun5__l'' : forall P x l,
  fun5_l'' (cons P nil) (cons x nil) (cons l nil) =
  fun5'' P x l.
Proof. reflexivity.
Qed.

Lemma is_in_FOvar_fun5_l''  : forall atm x,
  BAT atm = true ->
  is_in_FOvar x (FOvars_in (fun5_l''
    (batm_conj_comp_P atm) (batm_conj_comp_x1 atm)
    (batm_conj_comp_lx atm))) =
  is_in_FOvar x (FOvars_in atm).
Proof.
  intros atm x. apply (is_in_FOvar_fun5_l''_num_conn (num_conn atm)
    (num_conn atm)_  _ eq_refl (leb_refl _)).
Qed.


Lemma max_FOv_fun5_l''_pre_pre_BAT : forall m n atm,
n = num_conn atm ->
Nat.leb n m = true ->
BAT atm = true ->
is_in_FOvar (Var 0) (FOvars_in atm)  = false ->
(max_FOv  (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm)
     (batm_conj_comp_lx atm))) =
 max_FOv atm.
Proof.
  induction m; intros n atm Hnum Hleb Hat Hnot.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate. reflexivity.

    destruct n.
    destruct atm; try discriminate. reflexivity.
    simpl in Hleb. destruct atm; try discriminate.
      destruct f as [xn]. (* destruct xn. discriminate. *)
      destruct atm; try discriminate.
      destruct atm1; try discriminate.
      destruct f as [y1]. destruct f0 as [y2].
      simpl.

(* pose proof max_r. *)
      pose proof (is_BOXATM_flag_strong_CONJ_allFO_eq_BAT _ _ _ _ Hat) as Hat1.
      pose proof (is_BOXATM_flag_strong_CONJ_allFO_atm_BAT _ _ _ _ Hat) as Hat2.
      pose proof (is_BOXATM_flag_strong_CONJ_allFO_x1_BAT _ _ _ _ Hat) as Hat3.
(*       pose proof (is_BOXATM_flag_strong_CONJ_allFO_relatSO_BAT _ _ _ _ Hat) as Hat4. *)
(*       simpl in Hat4. *)
(*       rewrite (max_r y1). simpl.  *)
      rewrite max_FOv_fun5''.
inversion Hat1 as [Hat1'].
 simpl.
      rewrite (max_FOv_batm_comp _ (Var y2) Hat2).
      rewrite Hat3. reflexivity.



        simpl in Hat. 
        case_eq (BAT atm1); intros Hat1;
          rewrite Hat1 in *. 2 : discriminate.
        simpl.
        rewrite max_FOv_fun5_l''_app'.
          rewrite (IHm (num_conn atm1) atm1).
          rewrite (IHm (num_conn atm2) atm2).
          all : try  reflexivity.

          simpl in Hnum. inversion Hnum as [Hnum'].
          rewrite Hnum' in Hleb.
          apply leb_plus_take2 in Hleb. assumption.

          simpl in Hnum. inversion Hnum as [Hnum'].
          rewrite Hnum' in Hleb.
          apply leb_plus_take1 in Hleb. assumption.

        apply is_in_FOvar_app_r in Hnot. assumption.

          simpl in Hnum. inversion Hnum as [Hnum'].
          rewrite Hnum' in Hleb.
          apply leb_plus_take1 in Hleb. assumption.

          assumption.

(*         apply try2. assumption. simpl in Hnot.  *)

        apply is_in_FOvar_app_l in Hnot. assumption.

        apply length_batm_conj_comp_P_x1_BAT. assumption.
        apply length_batm_conj_comp_P_lx_BAT. assumption.

simpl in Hnot. apply is_in_FOvar_app_l in Hnot.
rewrite is_in_FOvar_fun5_l''; assumption.
simpl in Hnot. apply is_in_FOvar_app_r in Hnot.
rewrite is_in_FOvar_fun5_l''; assumption.
Qed.
(*
      rewrite <- max_FOv_l_batm_comp_lx with (xn := y2). reflexivity.
assumption.
      rewrite <- (PeanoNat.Nat.max_assoc y1 y2).
      rewrite (PeanoNat.Nat.max_assoc y2 y2).
      rewrite max_refl.
      rewrite (PeanoNat.Nat.max_assoc y1 y2).
      remember (max_FOv_l (batm_comp_lx atm2)) as t.
      case_eq t.
        intros Ht. rewrite PeanoNat.Nat.max_0_r.
 rewrite max_refl. rewrite max_refl.
        rewrite max_comm. simpl.
simpl in Hnot. destruct xn. discriminate.
destruct y1. discriminate. destruct y2. discriminate.
apply BOXATM_flag_weak_BAT in Hat2.
pose proof (is_in_FOvar_max_FOv_l atm2 (Var 0) Hat2 Hnot) as HH.
rewrite Ht in Heqt. rewrite Heqt in HH. contradiction (HH eq_refl).
*)
(* 
rewrite PeanoNat.Nat.max_0_r.
        rewrite Hat4. rewrite max_S.
        inversion Hat1 as [Hat1'].
        rewrite <- Hat1' in Hat4.
        inversion Hat4 as [Hat4']. 
        rewrite max_refl. reflexivity.
 *)
(*
        intros t2 Ht2. rewrite (PeanoNat.Nat.max_assoc xn xn).
        rewrite max_refl.
        rewrite (PeanoNat.Nat.max_assoc xn xn).
        rewrite max_refl.
(*  rewrite Hat4. *)
(*         rewrite max_S. *) simpl.
(* 
        do 3 rewrite PeanoNat.Nat.succ_max_distr. *)
        rewrite <- Ht2. rewrite Heqt.

        rewrite Hat4 in Hat1.
        inversion Hat1 as [Hat1'].
        rewrite PeanoNat.Nat.max_assoc.
        rewrite max_refl. reflexivity. assumption.
  
        inversion Hat1 as [Hat1']. rewrite Hat1'. 
        rewrite Hat4. apply le_S. apply le_n.

        simpl in Hat. 
        case_eq (is_BOXATM_flag_strong_CONJ atm1); intros Hat1;
          rewrite Hat1 in *. 2 : discriminate.
        simpl.
        rewrite max_FOv_fun5_l''_app'.
          rewrite (IHm (num_conn atm1) atm1).
          rewrite (IHm (num_conn atm2) atm2).
          all : try  reflexivity.

          simpl in Hnum. inversion Hnum as [Hnum'].
          rewrite Hnum' in Hleb.
          apply leb_plus_take2 in Hleb. assumption.

          simpl in Hnum. inversion Hnum as [Hnum'].
          rewrite Hnum' in Hleb.
          apply leb_plus_take1 in Hleb. assumption.


(*         apply try2. assumption. simpl in Hnot.  *)

        apply is_in_FOvar_app_r in Hnot. assumption.

          simpl in Hnum. inversion Hnum as [Hnum'].
          rewrite Hnum' in Hleb.
          apply leb_plus_take1 in Hleb. assumption.

          assumption.

(*         apply try2. assumption. simpl in Hnot.  *)

        apply is_in_FOvar_app_l in Hnot. assumption.

        apply length_batm_conj_comp_P_x1. assumption.
        apply length_batm_conj_comp_P_lx. assumption.

simpl in Hnot. apply is_in_FOvar_app_l in Hnot.
Search is_in_FOvar fun5_l''.
          apply is_in_FOvar_0_batm_conj''; assumption.
simpl in Hnot. apply is_in_FOvar_app_r in Hnot.
          apply is_in_FOvar_0_batm_conj''; assumption.
Qed.
*)
Lemma max_FOv_fun5_l''_pre : forall  atm,
is_BOXATM_flag_strong_CONJ atm = true ->
is_in_FOvar (Var 0) (batm_conj_comp_x1 atm)  = false ->
(max_FOv  (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm)
     (batm_conj_comp_lx atm))) =
 max_FOv atm.
Proof.
  intros atm. apply (max_FOv_fun5_l''_pre_pre (num_conn atm) (num_conn atm)).
  reflexivity. apply leb_refl.
Qed. 

Lemma max_FOv_fun5_l''_pre_BAT : forall  atm,
BAT atm = true ->
is_in_FOvar (Var 0) (FOvars_in atm)  = false ->
(max_FOv  (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm)
     (batm_conj_comp_lx atm))) =
 max_FOv atm.
Proof.
  intros atm. apply (max_FOv_fun5_l''_pre_pre_BAT (num_conn atm) (num_conn atm)).
  reflexivity. apply leb_refl.
Qed. 

Lemma new_FOv_pp_pre2_fun5_l''2 : forall atm,
is_BOXATM_flag_strong_CONJ atm = true ->
is_in_FOvar (Var 0) (batm_conj_comp_x1 atm) = false ->
(new_FOv_pp_pre2  (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm)
     (batm_conj_comp_lx atm))) =
 new_FOv_pp_pre2 atm.
Proof.
  unfold new_FOv_pp_pre2. intros atm H1 H2.
  rewrite max_FOv_fun5_l''_pre. reflexivity.
  assumption. assumption.
Qed.

Lemma new_FOv_pp_pre2_fun5_l''2_BAT : forall atm,
BAT atm = true ->
is_in_FOvar (Var 0) (FOvars_in atm) = false ->
(new_FOv_pp_pre2  (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm)
     (batm_conj_comp_lx atm))) =
 new_FOv_pp_pre2 atm.
Proof.
  unfold new_FOv_pp_pre2. intros atm H1 H2.
  rewrite max_FOv_fun5_l''_pre_BAT. reflexivity.
  assumption. assumption.
Qed.

Definition is_conj alpha :=
  match alpha with
  | conjSO _ _ => true
  | _ => false
  end.

Lemma is_conj_calc_conj : forall alpha,
  is_conj alpha = false ->
  calc_conj alpha = cons alpha nil.
Proof.
  induction alpha; intros H; try reflexivity.
  discriminate.
Qed.

Lemma is_equiv_conj_assoc_disjSO : forall alpha beta gamma delta,
  is_conj alpha = false ->
  is_conj beta = false ->
  is_conj gamma = false ->
  is_conj delta = false ->
  is_equiv_conj_assoc (disjSO alpha beta) (disjSO gamma delta) =
  if is_equiv_conj_assoc alpha gamma then is_equiv_conj_assoc beta delta
      else false.
Proof.
  intros alpha beta gamma delta H1 H2 H3 H4.
  unfold is_equiv_conj_assoc.
  simpl.
  rewrite (is_conj_calc_conj alpha H1).
  rewrite (is_conj_calc_conj beta H2).
  rewrite (is_conj_calc_conj gamma H3).
  rewrite (is_conj_calc_conj delta H4).
  simpl. 
  case_eq (eq_SO alpha gamma);
  case_eq (eq_SO beta delta); reflexivity.
Qed.

Lemma is_conj_fun4' : forall l a b,
  is_conj (fun4' a b l) = false.
Proof.
  destruct l; intros aa bb; reflexivity.
Qed.

Lemma is_conj_fun4_l2' : forall aa bb l,
  is_conj (fun4_l2' aa bb l) = false.
Proof.
  induction aa; intros bb l.
    simpl. reflexivity.

    simpl. destruct aa. destruct l. reflexivity. apply is_conj_fun4'.
    destruct l. reflexivity.
    destruct l0. apply is_conj_fun4'.
    simpl in *. reflexivity.
Qed.

Lemma is_equiv_conj_assoc_fun4_l2'_app : forall l1 l2 l1' l2' llx1 llx2 x,
  length l1 = length l1' ->
  length l2 = length l2' ->
  length l1 = length llx1 ->
  length l2 = length llx2 ->
  is_equiv_conj_assoc (fun4_l2' (app l1 l2) x (app llx1 llx2))
    (fun4_l2' (app l1' l2') x (app llx1 llx2)) =
  if is_equiv_conj_assoc (fun4_l2' l1 x llx1) (fun4_l2' l1' x llx1) then    
     is_equiv_conj_assoc (fun4_l2' l2 x llx2) (fun4_l2' l2' x llx2) else
     false.
Proof.
  induction l1; intros l2 l1' l2' llx1 llx2 x Hl1 Hl2 Hl3 Hl4.
    destruct l1'. destruct llx1.
    simpl. reflexivity.
    all : try discriminate.

    destruct l1'. discriminate.
    destruct llx1. discriminate.
    simpl. case_eq l1. intros Hnil.
      rewrite Hnil in *. simpl.
      destruct l1'. 2 : ( discriminate).
      destruct llx1. simpl.
      destruct l2. destruct l2'.
      destruct llx2. simpl. rewrite is_equiv_conj_assoc_refl.
      case_eq (is_equiv_conj_assoc (fun4' a x l) (fun4' f x l) );
        reflexivity.
      all : try discriminate.

      destruct llx2. discriminate.
      destruct l2'. discriminate.
      simpl.
      case_eq l2.
        intros Hnil2. rewrite Hnil2 in *. destruct l2'.
        2 : discriminate. destruct llx2. 2 : discriminate.

        apply is_equiv_conj_assoc_disjSO.

apply is_conj_fun4'.
apply is_conj_fun4'.
apply is_conj_fun4'.
apply is_conj_fun4'.

        intros x2 lx2 Hlx2.
        rewrite <- Hlx2.
        destruct llx2. rewrite Hlx2 in *. discriminate.
        destruct l2'.  rewrite Hlx2 in *. discriminate.
        simpl in IHl1.
        rewrite is_equiv_conj_assoc_disjSO.
        rewrite is_equiv_conj_assoc_disjSO. reflexivity.

apply is_conj_fun4'.
apply is_conj_fun4_l2'.
apply is_conj_fun4'.
apply is_conj_fun4_l2'.

apply is_conj_fun4'. reflexivity.
apply is_conj_fun4'. reflexivity.

      intros x1 lx1 Hlx1. rewrite <- Hlx1.
      destruct llx1. rewrite Hlx1 in *. discriminate.
      destruct l1'. rewrite Hlx1 in *. discriminate.
      case_eq (app l1 l2).
        intros Hnil. rewrite Hlx1 in Hnil. discriminate.
      intros xx lxx Hlxx. rewrite <- Hlxx.
      case_eq ((l0 :: llx1) ++ llx2).
        discriminate.
      intros yy lyy Hlyy. rewrite <- Hlyy.
      case_eq ((f0 :: l1') ++ l2').
        discriminate.
      intros zz lzz Hlzz. rewrite <- Hlzz.
      rewrite is_equiv_conj_assoc_disjSO.
      rewrite is_equiv_conj_assoc_disjSO.
      rewrite (IHl1).   
      case_eq (is_equiv_conj_assoc (fun4' a x l) (fun4' f x l)); intros HHH;
        reflexivity.

      rewrite Hlx1 in *. simpl in *.
      inversion Hl1. reflexivity.

      all : try assumption.

      rewrite Hlx1 in *. simpl in *. inversion Hl3. reflexivity.

apply is_conj_fun4'.
apply is_conj_fun4_l2'.
apply is_conj_fun4'.
apply is_conj_fun4_l2'.

apply is_conj_fun4'.
apply is_conj_fun4_l2'.
apply is_conj_fun4'.
apply is_conj_fun4_l2'.
Qed. 

Lemma length_calc_lx1_P_fun5_l'' : forall atm P,
is_BOXATM_flag_strong_CONJ atm = true ->
length (calc_lx1_P atm P) =
length (calc_lx1_P (fun5_l'' (batm_conj_comp_P atm) 
    (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm)) P).
Proof.
  induction atm; intros P H; try discriminate; try reflexivity.

    simpl. destruct atm; try discriminate; try reflexivity.
    destruct f as [xn]. destruct xn. discriminate.
    destruct atm1; try discriminate.
    pose proof (is_BOXATM_flag_strong__CONJ _ _ _ H) as H0. 
    simpl. case_eq (P_branch_allFO atm2 P ); intros H2;
      rewrite <- lem_try3 with ( y:= Var (S xn)).
      rewrite H2. reflexivity.
      assumption.
      rewrite H2. reflexivity.
      assumption.

    simpl. rewrite calc_lx1_P_fun5_l''_app.
    do 2 rewrite app_length.
    rewrite IHatm1. rewrite IHatm2. reflexivity.
      apply is_BOXATM_flag_strong_CONJ_conjSO_r in H. assumption.
      apply is_BOXATM_flag_strong_CONJ_conjSO_l in H. assumption.

      apply length_batm_conj_comp_P_x1.  
      apply is_BOXATM_flag_strong_CONJ_conjSO_l in H. assumption.
      apply length_batm_conj_comp_P_lx. 
      apply is_BOXATM_flag_strong_CONJ_conjSO_l in H. assumption.
Qed. 

Lemma length_calc_lx1_P_llv : forall atm P,
  is_BOXATM_flag_strong_CONJ atm = true ->
  length (calc_lx1_P atm P) = length (calc_llv_P atm P).
Proof.
  induction atm; intros P H; try discriminate. reflexivity.
    simpl. destruct atm; try discriminate; try reflexivity.
    destruct f as [xn]. destruct xn. discriminate.
    destruct atm1; try discriminate.
    case_eq (P_branch_allFO atm2 P); intros H2.
      destruct atm2; try discriminate; reflexivity.
    reflexivity.

    simpl. do 2 rewrite app_length.
    rewrite IHatm1. rewrite IHatm2. reflexivity.

    apply is_BOXATM_flag_strong_CONJ_conjSO_r in H. assumption.
    apply is_BOXATM_flag_strong_CONJ_conjSO_l in H. assumption.
Qed.

Lemma length_calc_lx1_P_llv_BAT : forall atm P,
  BAT atm = true ->
  length (calc_lx1_P atm P) = length (calc_llv_P atm P).
Proof.
  induction atm; intros P H; try discriminate. reflexivity.
    simpl. destruct atm; try discriminate; try reflexivity.
    destruct f as [xn]. (*  destruct xn. discriminate. *)
    destruct atm1; try discriminate.
    case_eq (P_branch_allFO atm2 P); intros H2.
      destruct atm2; try discriminate; reflexivity.
    reflexivity.

    simpl. do 2 rewrite app_length.
    rewrite IHatm1. rewrite IHatm2. reflexivity.

    apply BAT_conjSO_r in H. assumption.
    apply BAT_conjSO_l in H. assumption.
Qed.

Lemma length_calc_lx1_P_fun5_l''_BAT : forall atm P,
BAT atm = true ->
length (calc_lx1_P atm P) =
length (calc_lx1_P (fun5_l'' (batm_conj_comp_P atm) 
    (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm)) P).
Proof.
  induction atm; intros P H; try discriminate; try reflexivity.

    simpl. destruct atm; try discriminate; try reflexivity.
    destruct f as [xn]. (*  destruct xn. discriminate. *)
    destruct atm1; try discriminate.
    pose proof (is_BOXATM_flag_strong__CONJ_BAT _ _ _ H) as H0. 
    simpl. case_eq (P_branch_allFO atm2 P ); intros H2;
      rewrite <- lem_try3_BAT with ( y:= Var (xn)).
      rewrite H2. reflexivity.
      assumption.
      rewrite H2. reflexivity.
      assumption.

    simpl. rewrite calc_lx1_P_fun5_l''_app.
    do 2 rewrite app_length.
    rewrite IHatm1. rewrite IHatm2. reflexivity.
      apply BAT_conjSO_r in H. assumption.
      apply BAT_conjSO_l in H. assumption.

      apply length_batm_conj_comp_P_x1_BAT.
      apply BAT_conjSO_l in H. assumption.
      apply length_batm_conj_comp_P_lx_BAT. 
      apply BAT_conjSO_l in H. assumption.
Qed. 


Lemma lem_try2_pre : forall atm  P x,
is_BOXATM_flag_strong_CONJ atm = true ->
is_equiv_conj_assoc
  (fun4_l2' (calc_lx1_P atm P) x (calc_llv_P atm P))
  (fun4_l2' (calc_lx1_P (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm)
           (batm_conj_comp_lx atm)) P) x (calc_llv_P atm P)) = true.
Proof.
  induction atm; intros P x H; try discriminate.
    simpl. apply is_equiv_conj_assoc_refl.

    destruct f as [xn]. destruct xn. discriminate.
    destruct atm; try discriminate.
    destruct atm1; try discriminate.
    simpl calc_lx1_P. 
    case_eq (P_branch_allFO atm2 P); intros Hb2;
      pose proof (is_BOXATM_flag_strong__CONJ _ _ _ H) as H0.
      rewrite <- lem_try3 with (y := (Var (S xn))).
      rewrite Hb2.
      simpl.
      apply is_equiv_conj_assoc_refl.
      all : try assumption.

      rewrite <- lem_try3 with ( y:= (Var (S xn))).
      rewrite Hb2. apply is_equiv_conj_assoc_refl.
      assumption.

    pose proof (is_BOXATM_flag_strong_CONJ_conjSO_l _ _ H) as Hl.
    pose proof (is_BOXATM_flag_strong_CONJ_conjSO_r _ _ H) as Hr.
    simpl.
    rewrite calc_lx1_P_fun5_l''_app.
    rewrite is_equiv_conj_assoc_fun4_l2'_app.
    rewrite IHatm1. rewrite IHatm2. reflexivity.

    all : try assumption.

    apply length_calc_lx1_P_fun5_l''. assumption. 

    apply length_calc_lx1_P_fun5_l''. assumption. 

    apply length_calc_lx1_P_llv. assumption.

    apply length_calc_lx1_P_llv. assumption.

      apply length_batm_conj_comp_P_x1. assumption. 

      apply length_batm_conj_comp_P_lx. assumption.
Qed.

Lemma lem_try2 : forall atm a,
is_BOXATM_flag_strong_CONJ atm = true ->
is_in_FOvar (Var 0) (FOvars_in atm) = false ->
  is_equiv_conj_assoc (fun4_l2' (calc_lx1_P atm a) (Var (new_FOv_pp_pre2 atm)) (calc_llv_P atm a))
    (fun4_l2' (calc_lx1_P (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm)) a)
       (Var (new_FOv_pp_pre2 (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm))))
       (calc_llv_P (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm)) a)) = true.
Proof.
  intros atm P H H2.
  rewrite calc_llv_P_fun5_l''. 2: assumption.
  rewrite new_FOv_pp_pre2_fun5_l''2; try assumption.
  2:  rewrite is_BOXATM_CONJ_is_in_batm_conj_equiv.
  all : try assumption.
  apply lem_try2_pre.
  assumption.
Qed.

Lemma lem_try2_pre_BAT : forall atm  P x,
BAT atm = true ->
is_equiv_conj_assoc
  (fun4_l2' (calc_lx1_P atm P) x (calc_llv_P atm P))
  (fun4_l2' (calc_lx1_P (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm)
           (batm_conj_comp_lx atm)) P) x (calc_llv_P atm P)) = true.
Proof.
  induction atm; intros P x H; try discriminate.
    simpl. apply is_equiv_conj_assoc_refl.

    destruct f as [xn]. (*  destruct xn. discriminate. *)
    destruct atm; try discriminate.
    destruct atm1; try discriminate.
    simpl calc_lx1_P.
    case_eq (P_branch_allFO atm2 P); intros Hb2;
      pose proof (is_BOXATM_flag_strong__CONJ_BAT _ _ _ H) as H0.
      rewrite <- lem_try3_BAT with (y := (Var (xn))).
      rewrite Hb2.
      simpl.
      apply is_equiv_conj_assoc_refl.
      all : try assumption.

      rewrite <- lem_try3_BAT with ( y:= (Var (xn))).
      rewrite Hb2. apply is_equiv_conj_assoc_refl.
      assumption.

    pose proof (BAT_conjSO_l _ _ H) as Hl.
    pose proof (BAT_conjSO_r _ _ H) as Hr.
    simpl.
    rewrite calc_lx1_P_fun5_l''_app.
    rewrite is_equiv_conj_assoc_fun4_l2'_app.
    rewrite IHatm1. rewrite IHatm2. reflexivity.

    all : try assumption.

    apply length_calc_lx1_P_fun5_l''_BAT. assumption. 

    apply length_calc_lx1_P_fun5_l''_BAT. assumption. 

    apply length_calc_lx1_P_llv_BAT. assumption.

    apply length_calc_lx1_P_llv_BAT. assumption.

      apply length_batm_conj_comp_P_x1_BAT. assumption. 

      apply length_batm_conj_comp_P_lx_BAT. assumption.
Qed.

Lemma lem_try2_BAT : forall atm a,
BAT atm = true ->
is_in_FOvar (Var 0) (FOvars_in atm) = false ->
  is_equiv_conj_assoc (fun4_l2' (calc_lx1_P atm a) (Var (new_FOv_pp_pre2 atm)) (calc_llv_P atm a))
    (fun4_l2' (calc_lx1_P (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm)) a)
       (Var (new_FOv_pp_pre2 (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm))))
       (calc_llv_P (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_lx atm)) a)) = true.
Proof.
  intros atm P H H2.
  rewrite calc_llv_P_fun5_l''_BAT. 2: assumption.
  rewrite new_FOv_pp_pre2_fun5_l''2_BAT; try assumption.
  apply lem_try2_pre_BAT.
  assumption.
Qed.

Lemma is_equiv_conj_assoc_l_calc_lP_fun5_l'' : forall lP atm,
is_BOXATM_flag_strong_CONJ atm = true ->
is_in_FOvar (Var 0) (FOvars_in atm) = false ->
  is_equiv_conj_assoc_l (calc_lP atm lP) 
    (calc_lP (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) 
      (batm_conj_comp_lx atm)) lP) = true.
Proof.
  induction lP; intros atm H H2. reflexivity.
  simpl. rewrite IHlP.
  rewrite lem_try2. reflexivity.
  all :  assumption.
Qed.

Lemma is_equiv_conj_assoc_l_calc_lP_fun5_l''_BAT : forall lP atm,
BAT atm = true ->
is_in_FOvar (Var 0) (FOvars_in atm) = false ->
  is_equiv_conj_assoc_l (calc_lP atm lP) 
    (calc_lP (fun5_l'' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) 
      (batm_conj_comp_lx atm)) lP) = true.
Proof.
  induction lP; intros atm H H2. reflexivity.
  simpl. rewrite IHlP.
  rewrite lem_try2_BAT. reflexivity.
  all :  assumption.
Qed.