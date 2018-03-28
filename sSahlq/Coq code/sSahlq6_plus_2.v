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
Require Import p_occurs_in occ_in_phi my_arith__my_leb_nat sSahlq_preprocessing1_added.  
Require Import sSahlq3_5_plus_3 sSahlq4_7_plus_I sSahlq4_7_plus_II sSahlq4_7_plus_III.

(* a more recent sSahlq5 version. *)




(* The end *)

(* CHANGE THIS *)
(* THIS IS THE NEXT THING TO WORK ON. FIGURE OUT WHAT llx1, etc. SHOULD BE *)

Lemma sSahlq_instant_aim1_fwd4_closer2_REV : forall lx lP lP2 lx1 ln beta rel atm y xn W Iv Ip Ir,
  REL rel = true ->
    atm = fun5_l'' lP2 lx1 ln ->
(* length lP2 = length llx2 -> *)
lP2 <> nil ->
(* ex_nil_in_llv llx2 = false -> *)
ex_FOvar_x_ll y (FOv_att_P_l atm lP) = false ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  attached_allFO_x beta (Var xn) = false ->
  attached_exFO_x beta (Var xn) = false ->
  closed_except beta (Var xn) ->

  x_occ_in_alpha (instant_cons_empty' (conjSO rel atm) beta) (Var xn) = true ->
  is_in_pred_l (preds_in (implSO (conjSO rel atm) beta)) lP = true ->
  SOturnst W Iv Ip Ir (replace_pred_l (list_closed_allFO (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)  
      (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) beta)) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn)))))) lx)
    lP (list_Var (length lP) y)
    (calc_lP atm lP)) ->
(* (fun1_l (FOv_att_P_l (conjSO rel atm) lP) y)) -> *)
  SOturnst W Iv Ip Ir (list_closed_SO (list_closed_allFO
      (implSO (conjSO rel atm) beta) lx) lP).
Proof.
  intros lx lP lP2 lx1 ln beta rel atm y xn W Iv Ip Ir Hrel Hat Hnil  Hex2 Hun Hno Hat1 Hat2 Hc Hocc Hin SOt. 
  rewrite rep_pred_l_list_closed_allFO in SOt.
  pose proof equiv_list_closed_allFO.
  apply (impl_list_closed_allFO _ _ (list_closed_SO (implSO (conjSO rel atm) beta) lP)) in SOt.
    apply equiv_list_closed_SO_list_closed_allFO.
    assumption.
    intros.
Admitted.
(*
    apply vsSahlq_instant_aim1_fwd4_closer_REV with (lP2 := lP2) (llx2 := llx2) in H0.
    all : try assumption.
Qed.
 *)

(* MAKE THIS WORK. *)
Lemma sSahlq_instant_aim1_fwd4_closer2_REV_gen : forall lx lP beta rel atm y xn W Iv Ip Ir,
  REL rel = true ->
  BAT atm = true -> 
ex_FOvar_x_ll y (FOv_att_P_l atm lP) = false ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  attached_allFO_x beta (Var xn) = false ->
  attached_exFO_x beta (Var xn) = false ->
  closed_except beta (Var xn) ->
is_in_FOvar (Var 0) (FOvars_in atm) = false ->
(* length lP = length llx1 -> *)
(* length llx1 = length lllv -> *)

  x_occ_in_alpha (instant_cons_empty' (conjSO rel atm) beta) (Var xn) = true ->
  is_in_pred_l (preds_in (implSO (conjSO rel atm) beta)) lP = true ->

  SOturnst W Iv Ip Ir (replace_pred_l (list_closed_allFO (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)  
      (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) beta)) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn)))))) lx)
    lP (list_Var (length lP) y)
    (calc_lP atm lP)) ->
  SOturnst W Iv Ip Ir (list_closed_SO (list_closed_allFO
      (implSO (conjSO rel atm) beta) lx) lP).
Proof.
  intros lx lP beta rel atm y xn W Iv Ip Ir Hrel Hat Hex2 Hun Hno Hat1 Hat2 Hc Hin3 (* Hl1 Hl2 *) Hocc Hin SOt.
  apply sS_lem_e1_BAT; try assumption.
  apply sSahlq_instant_aim1_fwd4_closer2_REV with (lP2 := (batm_conj_comp_P atm))
    (y := y) (xn := xn)
    (lx1 := (batm_conj_comp_x1 atm)) (ln := (batm_conj_comp_lx atm)); try assumption.

(*  (llx1 := llx1) (lllv := lllv); try assumption. *)

reflexivity.

apply batm_conj_comp_P_not_nil_BAT. assumption.

rewrite FOv_att_P_l_fun5_l''_BAT; assumption.
apply lem1_BAT; assumption.
apply lem2_BAT; assumption.

    rewrite rep_pred_l_list_closed_allFO in *.
    apply (equiv_list_closed_allFO ((replace_pred_l
              (implSO (conjSO rel atm)
                 (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)
                    (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
                    (rev_seq (S (Nat.max (max_FOv (implSO (conjSO rel atm) beta)) xn))
                       (length
                          (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta))
                             (Var xn)))))) lP (list_Var (length lP) y)
              (calc_lP atm (* (fun5_l' (batm_conj_comp_P atm) (batm_conj_comp_x1 atm) (batm_conj_comp_ln atm)) *) lP)))).
    intros W1 Iv1 Ip1 Ir1.
(* pose proof sS_lem_e2_2 as H. apply H.
Print sS_lem_e2.
 *)
     apply sS_lem_e2_BAT; try assumption.
     assumption.
Qed.

Fixpoint rem_dups_FOv (l : list FOvariable) : list FOvariable :=
  match l with
  | nil => nil
  | cons P l' => if is_in_FOvar P l' then rem_dups_FOv l' else cons P (rem_dups_FOv l')
  end.

Lemma lem1 : forall l x,
  is_in_FOvar x l = false ->
  is_in_FOvar x (rem_dups_FOv l) = false.
Proof.
  induction l; intros x H.
    reflexivity.

    simpl in *. destruct x as [xn]. destruct a as [ym].
    case_eq (beq_nat xn ym); intros Hbeq; rewrite Hbeq in *.
      discriminate.
    case_eq (is_in_FOvar (Var ym) l); intros H2.
      apply IHl. assumption.

      simpl. rewrite Hbeq. apply IHl. assumption.
Qed.

Lemma lem2 : forall l l2 x,
  is_in_FOvar x l = false ->
  ~ (l = cons x l2).
Proof.
  induction l; intros l2 x H1 H2. discriminate.
  simpl in H1. destruct x as [xn]. destruct a as [ym].
  case_eq (beq_nat xn ym); intros Hbeq; rewrite Hbeq in *.
    discriminate.
  inversion H2 as [[H' H'']]. rewrite H' in *.
  rewrite <- beq_nat_refl in *. discriminate.
Qed.


Lemma rem_dups_FOv_no : forall l l2 x,
  ~ rem_dups_FOv l = (cons x (cons x l2)).
Proof.
  induction l; intros l2 x H. discriminate.
  simpl in *. case_eq (is_in_FOvar a l); intros Hin;
    rewrite Hin in *. apply (IHl _ _ H).
    inversion H as [[H1 H2]].
    rewrite H1 in Hin. apply lem1 in Hin.
    apply (lem2 _ l2) in Hin. contradiction (Hin H2).
Qed.

Lemma lem4 : forall l x,
  is_in_FOvar x l = true ->
  rem_dups_FOv (cons x l) = rem_dups_FOv l.
Proof.
  induction l; intros x H. discriminate.
  simpl in *. destruct x as [xn]. destruct a as [ym].
  case_eq (beq_nat xn ym); intros Hbeq; rewrite Hbeq in *.
    reflexivity.
  rewrite H. reflexivity.
Qed.

Lemma lem6 : forall l,
  PeanoNat.Nat.leb (length (rem_dups_FOv l)) (length l) = true.
Proof.
  induction l. reflexivity.
  simpl in *. case_eq (is_in_FOvar a l); intros H.
    apply leb_suc_r. assumption.

    simpl. assumption.
Qed.

Lemma lem3 : forall l x,
  ~ (rem_dups_FOv l = cons x l).
Proof.
  intros l x H.
  assert (length (rem_dups_FOv l) = length (cons x l)) as Hass.
    rewrite H. reflexivity.
  simpl in Hass. 
  pose proof (lem6 l) as Hass2.
  rewrite Hass in Hass2.
  rewrite leb_suc_f in Hass2. discriminate.
Qed.

Lemma rem_dups_FOv_cons : forall l y,
    rem_dups_FOv (cons y l) = (cons y l) ->
  is_in_FOvar y l = false.
Proof.
  intros l y H. simpl in H. case_eq (is_in_FOvar y l);
    intros Hin; rewrite Hin in *.
    contradiction (lem3 _ _ H).

    reflexivity.
Qed.

Lemma lem8 : forall l x1 xn x,
  ~ x = x1 ->
  ~ x = xn ->
  is_in_FOvar x l = false ->
  is_in_FOvar x (FOvars_in (fun4' x1 xn l)) = false.
Proof.
  induction l; intros [x1] [xn] [ym] H1 H2 Hin.
    simpl in *. rewrite FOvar_neq. rewrite FOvar_neq.
    reflexivity. all : try assumption.

    simpl FOvars_in. destruct a as [zn].
    simpl in *.
    case_eq (beq_nat ym zn); intros Hbeq; rewrite Hbeq in *.
      discriminate.
    rewrite FOvar_neq. apply IHl.
    all : try assumption.
    apply beq_nat_false_FOv. assumption.
Qed.

Lemma if_then_else_bool : forall (b  : bool),
  (if b then true else false) = b.
Proof.
  intros b. case b; reflexivity.
Qed.


Lemma x_occ_in_alpha_is_in_FOvar : forall alpha x,
  x_occ_in_alpha alpha x = is_in_FOvar x (FOvars_in alpha).
Proof.
  induction alpha; intros [xn]; try reflexivity.
    destruct p. destruct f.  simpl.
    rewrite if_then_else_bool. reflexivity.

    destruct f. destruct f0. simpl. rewrite if_then_else_bool.
    reflexivity.

    destruct f. destruct f0. simpl. rewrite if_then_else_bool.
    reflexivity.

    destruct f. simpl. rewrite IHalpha. reflexivity.

    destruct f. simpl. rewrite IHalpha. reflexivity.

    simpl. rewrite IHalpha. reflexivity.

    simpl. rewrite IHalpha1. rewrite IHalpha2.
    rewrite is_in_FOvar_app. reflexivity.

    simpl. rewrite IHalpha1. rewrite IHalpha2.
    rewrite is_in_FOvar_app. reflexivity.

    simpl. rewrite IHalpha1. rewrite IHalpha2.
    rewrite is_in_FOvar_app. reflexivity.

    simpl. apply IHalpha.

    simpl. apply IHalpha.
Qed.

Lemma lem7 : forall l xn x1 x2 W Iv Ip Ir d,
  is_in_FOvar x1 l = false ->
  is_in_FOvar x2 l = false ->
  ~ x1 = xn ->
  ~ x2 = xn ->
  SOturnst W (alt_Iv Iv d x1) Ip Ir (fun4' x1 xn l) ->
  SOturnst W (alt_Iv Iv d x2) Ip Ir (fun4' x2 xn l).
Proof.
  induction l; intros [xn] [x1] [x2] W Iv Ip Ir d H1 H2 Hneq1 Hneq2 SOt.
    simpl in *. rewrite <- beq_nat_refl in *.
    rewrite FOvar_neq in SOt. rewrite FOvar_neq.
    all : try assumption.

    destruct a as [ym]. simpl fun4' in *.
    rewrite SOturnst_exFO in *. destruct SOt as [d2 SOt].
    exists d2. rewrite SOturnst_conjSO in *.
      simpl in H1. simpl in H2.
      rewrite beq_nat_comm in H1.
      rewrite beq_nat_comm in H2.
      case_eq (beq_nat ym x1); intros Hbeq;
        rewrite Hbeq in *. discriminate.
      case_eq (beq_nat ym x2); intros Hbeq2;
        rewrite Hbeq2 in *. discriminate.
    destruct SOt as [SOt1 SOt2]. apply conj.
      simpl in *.
      do 2 rewrite <- beq_nat_refl in *. rewrite Hbeq2.
      rewrite Hbeq in *.
      assumption.
      rewrite alt_Iv_switch.
      rewrite <- alt_Iv_equiv.
      rewrite alt_Iv_switch in SOt2.
      rewrite <- alt_Iv_equiv in SOt2.
      assumption.
  
      apply x_occ_in_free_FO.
      rewrite x_occ_in_alpha_is_in_FOvar.
      apply lem8; try assumption.
      apply beq_nat_false_FOv. rewrite beq_nat_comm.
      assumption.
  
      apply beq_nat_false_FOv. rewrite beq_nat_comm.
      assumption.

      apply x_occ_in_free_FO.
      rewrite x_occ_in_alpha_is_in_FOvar.
      apply lem8; try assumption.
      apply beq_nat_false_FOv. rewrite beq_nat_comm.
      assumption.

      apply beq_nat_false_FOv. rewrite beq_nat_comm.
      assumption.
Qed.

Lemma lem10 : forall l n m,
  is_in_FOvar (Var n) l = false ->
  is_in_FOvar (Var m) l = false ->
  is_in_FOvar (Var ((max n m))) l = false.
Proof.
  induction l; intros n m H1 H2. reflexivity.
  simpl in *. destruct a as [xn]. 
  case_eq (beq_nat n xn); intros Hbeq;
    rewrite Hbeq in *. discriminate.
  case_eq (beq_nat m xn); intros Hbeq2;
    rewrite Hbeq2 in *. discriminate.
  specialize (IHl n m H1 H2).
  destruct (max_or n m) as [H | H];
    rewrite H in *. rewrite Hbeq. assumption.
    rewrite Hbeq2. assumption.
Qed. 



Lemma lem9_r : forall l1 l2 xn y2 y1,
is_in_FOvar
  (Var (S(Nat.max (new_FOv_pp_pre2 (fun4' (Var y2) (Var xn) l1)) (new_FOv_pp_pre2 (fun4' (Var y1) (Var xn) l2))))) l2 =
false.
Proof.
  intros until 0. apply lem12. simpl.
  apply leb_suc_r. rewrite max_comm.
  rewrite leb_max_suc3. reflexivity.
  apply lem13.
Qed.

Lemma lem9_l : forall l1 l2 xn y2 y1,
is_in_FOvar
  (Var (S(Nat.max (new_FOv_pp_pre2 (fun4' (Var y2) (Var xn) l1)) (new_FOv_pp_pre2 (fun4' (Var y1) (Var xn) l2))))) l1 =
false.
Proof.
  intros until 0. apply lem12. simpl.
  apply leb_suc_r. (* rewrite max_comm. *)
  rewrite leb_max_suc3. reflexivity.
  apply lem13.
Qed.

Lemma lem14 : forall l u x1 xn,
  ~u = x1 ->
  ~ u = xn ->
  is_in_FOvar u l = false ->
  x_occ_in_alpha (fun4' x1 xn l) u = false.
Proof.
  induction l; intros [un] [x1] [xn] H1 H2 H3.
    simpl in *. rewrite FOvar_neq. apply FOvar_neq.
    all : try assumption.

    simpl. destruct a as [ym]. simpl in H3.
    case_eq (beq_nat un ym); intros Hbeq; rewrite Hbeq in *. discriminate.
    rewrite FOvar_neq. apply IHl. all : try assumption.
    apply beq_nat_false_FOv. assumption.
Qed.

Lemma lem11 : forall l u z xn W Iv Ip Ir d,
  is_in_FOvar u l = false ->
  is_in_FOvar z l = false ->
  ~ u = xn ->
  ~ z = xn ->
  SOturnst W (alt_Iv Iv d z) Ip Ir (fun4' z xn l) <->
  SOturnst W (alt_Iv Iv d u) Ip Ir (fun4' u xn l).
Proof.
  induction l; intros [un] [zn] [xn] W Iv Ip Ir d H1 H2 H3 H4.
    simpl in *. simpl. do 2  rewrite <- beq_nat_refl.
    rewrite FOvar_neq. rewrite FOvar_neq. apply iff_refl.
    all : try assumption.

    destruct a as [ym].
    simpl fun4'. do 2 rewrite SOturnst_exFO.
    simpl in H1; simpl in H2.
    rewrite beq_nat_comm in H1. rewrite beq_nat_comm in H2.
    case_eq (beq_nat ym un); intros Hbeq; rewrite Hbeq in *. discriminate.
    case_eq (beq_nat ym zn); intros Hbeq2; rewrite Hbeq2 in *. discriminate.
    split; intros [d2 SOt]; exists d2;
      rewrite SOturnst_conjSO in *; destruct SOt as [SOt1 SOt2];
      apply conj. simpl in *; do 2 rewrite <- beq_nat_refl in *.
        rewrite Hbeq in *. rewrite Hbeq2 in *.
        assumption.

        rewrite alt_Iv_switch. apply alt_Iv_equiv.
        apply x_occ_in_free_FO. apply lem14; try assumption.
        apply beq_nat_false_FOv. rewrite beq_nat_comm. assumption.

        rewrite alt_Iv_switch in SOt2. apply alt_Iv_equiv in SOt2.
        assumption.
        apply x_occ_in_free_FO. apply lem14; try assumption.
        apply beq_nat_false_FOv. rewrite beq_nat_comm. assumption.
        apply beq_nat_false_FOv. rewrite beq_nat_comm. assumption.
        apply beq_nat_false_FOv. rewrite beq_nat_comm. assumption.

simpl in *; do 2 rewrite <- beq_nat_refl in *.
        rewrite Hbeq in *. rewrite Hbeq2 in *.
        assumption.

        rewrite alt_Iv_switch. apply alt_Iv_equiv.
        apply x_occ_in_free_FO. apply lem14; try assumption.
        apply beq_nat_false_FOv. rewrite beq_nat_comm. assumption.

        rewrite alt_Iv_switch in SOt2. apply alt_Iv_equiv in SOt2.
        assumption.
        apply x_occ_in_free_FO. apply lem14; try assumption.
        apply beq_nat_false_FOv. rewrite beq_nat_comm. assumption.
        apply beq_nat_false_FOv. rewrite beq_nat_comm. assumption.
        apply beq_nat_false_FOv. rewrite beq_nat_comm. assumption.
Qed.

Lemma lem15 : forall l x,
rem_dups_FOv (cons x l) = cons x l ->
rem_dups_FOv l = l.
Proof.
  induction l; intros [xn] H. reflexivity.
  pose proof (rem_dups_FOv_cons _ _ H) as H2.
  simpl in *. destruct a as [ym].
  
  case_eq (beq_nat xn ym); intros Hbeq; rewrite Hbeq in *.
    case_eq (is_in_FOvar (Var ym) l); intros Hbeq2; rewrite Hbeq2 in *.
      rewrite (beq_nat_true _ _ Hbeq) in H.
      contradiction (rem_dups_FOv_no _ _ _ H).

      discriminate.

    rewrite H2 in *. inversion H as [H3].
    reflexivity.
Qed.

Lemma lem19 : forall l xn y,
  Nat.leb xn (max_FOv (fun4' y (Var xn) l)) = true.
Admitted.

Lemma lem20 : forall l xn y,
  max_FOv (fun4' y (Var xn) l) = xn \/
  Nat.leb xn (max_FOv (fun4' y (Var xn) l)) = true.
Proof.
  induction l; intros xn [ym].
    simpl. destruct (max_or ym xn) as [H | H].
      rewrite H. apply max_leb_r in H. right. assumption.

      left. assumption.

    simpl. destruct a as [zn]. 
    destruct (IHl xn (Var zn)) as [IH | IH].
      rewrite IH.
      destruct (max_or zn (max (max ym zn) xn)) as [H | H];
        rewrite H. pose proof (max_leb_r _ _ _ H) as H2.
        apply leb_max in H2. right. apply H2.
        destruct (max_or (max ym zn) xn) as [H1 | H1];
          rewrite H1. apply max_leb_r in H1. right. assumption.
          left. reflexivity.

      right. rewrite max_comm. apply leb_max_suc3.
      rewrite max_comm.
      apply leb_max_suc3. assumption.
Qed.

Lemma lem18 : forall l xn y,
  ~S (S (max_FOv (fun4' y (Var xn) l))) = xn.
Proof.
  intros l xn y H.
  pose proof (leb_refl xn) as H2.
  rewrite <- H in H2 at 1.
  destruct (lem20 l xn y) as [H3 | H3].
    rewrite H3 in H2.
    apply leb_suc_l in H2. rewrite leb_suc_f in H2.
    discriminate.

    do 2 rewrite <- leb_defn_suc in H3.
    pose proof (leb_trans _ _ _ H3 H2) as H4.
    apply leb_suc_l in H4. rewrite leb_suc_f in H4.
    discriminate.
Qed.

Lemma lem17  : forall l1 l2 xn y1 y2,
~ S (S (Nat.max (max_FOv (fun4' (Var y2) (Var xn) l1)) (max_FOv (fun4' (Var y1) (Var xn) l2)))) = xn.
Proof.
  intros until 0. intros H.
  destruct (max_or  (max_FOv (fun4' (Var y2) (Var xn) l1)) (max_FOv (fun4' (Var y1) (Var xn) l2)))
    as [H1 | H1];
    rewrite H1 in *;
    apply lem18 in H; assumption.
Qed.

Lemma lem16 : forall l1 l2 xn y1 y2,
Var (S (Nat.max (new_FOv_pp_pre2 (fun4' (Var y2) (Var xn) l1)) (new_FOv_pp_pre2 (fun4' (Var y1) (Var xn) l2)))) <>
Var xn.
Proof.
  intros until 0.
  intros H. inversion H as [H2].
  apply lem17 in H2. assumption.
Qed.

Lemma lem_try : forall l1 l2 x1 xn,
  is_in_FOvar x1 l1 = false ->
  is_in_FOvar xn l1 = false ->
  is_in_FOvar x1 l2 = false ->
  is_in_FOvar xn l2 = false ->
  length l1 = length l2 ->
  rem_dups_FOv l1 = l1 ->
  rem_dups_FOv l2 = l2 ->
  forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (fun4' x1 xn l1) ->
  SOturnst W Iv Ip Ir (fun4' x1 xn l2).
Proof.
  induction l1; intros l2 [x1] [xn] H1 H2 H3 H4 Hl Hr1 Hr2 W Iv Ip Ir SOt.
    destruct l2. 2 : discriminate. assumption.
  destruct l2. discriminate.
  simpl fun4' in *. rewrite SOturnst_exFO in *.
  destruct SOt as [d SOt]; exists d.
    rewrite SOturnst_conjSO in *. destruct f as [y1].
    destruct a as [y2].
    destruct SOt as [SOt1 SOt2].
    apply conj.
    simpl in *. rewrite <- beq_nat_refl in *. 
    rewrite beq_nat_comm in H1. 
    rewrite beq_nat_comm in H2.
    rewrite beq_nat_comm in H3. 
    rewrite beq_nat_comm in H4.
    case_eq (beq_nat y2 x1); intros Hbeq; rewrite Hbeq in *.
      discriminate.
    case_eq (beq_nat y1 x1); intros Hbeq2; rewrite Hbeq2 in *.
      discriminate.
    assumption.

    apply is_in_FOvar_cons_f in H1.
    apply is_in_FOvar_cons_f in H2.
    apply is_in_FOvar_cons_f in H3.
    apply is_in_FOvar_cons_f in H4.
    destruct H1 as [H1a H1b].
    destruct H2 as [H2a H2b].
    destruct H3 as [H3a H3b].
    destruct H4 as [H4a H4b].
    apply FOv_neq_switch in H1b.
    apply FOv_neq_switch in H2b.
    apply FOv_neq_switch in H3b.
    apply FOv_neq_switch in H4b.
    pose proof (rem_dups_FOv_cons _ _  Hr1).
    pose proof (rem_dups_FOv_cons _ _  Hr2).
    apply (lem11 _ (Var (S (Nat.max (new_FOv_pp_pre2 (fun4' (Var y2) (Var xn) l1)) (new_FOv_pp_pre2 (fun4' (Var y1) (Var xn) l2))))));
      try assumption.
    apply lem9_r. 
    apply lem16.

    apply (lem11 _ (Var (S (Nat.max (new_FOv_pp_pre2 (fun4' (Var y2) (Var xn) l1)) (new_FOv_pp_pre2 (fun4' (Var y1) (Var xn) l2)))))) in SOt2;
      try assumption.
    apply IHl1; try assumption.
    apply lem9_l.
    apply lem9_r.
    simpl in Hl. inversion Hl. reflexivity.
    apply lem15 in Hr1. assumption.
    apply lem15 in Hr2. assumption.

    apply lem9_l.
    apply lem16.
Qed.

Lemma lem_try_2 : forall l1 l2 x1 xn,
  is_in_FOvar x1 l1 = false ->
  is_in_FOvar xn l1 = false ->
  is_in_FOvar x1 l2 = false ->
  is_in_FOvar xn l2 = false ->
  length l1 = length l2 ->
  rem_dups_FOv l1 = l1 ->
  rem_dups_FOv l2 = l2 ->
  forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (fun4' x1 xn l1) <->
  SOturnst W Iv Ip Ir (fun4' x1 xn l2).
Proof.
  intros until 0. intros H1 H2 H3 H4 H5 H6 H7 W Iv Ip Ir.
  split; intros SOt; [apply (lem_try l1 l2)| apply (lem_try l2 l1)];
    try assumption. symmetry. assumption.
Qed.



(* 

Fixpoint funfun (alpha : SecOrder) : list (list FOvariable) :=
  match alpha with
  | predSO P x => cons (cons x nil) nil
  | allFO x (implSO (relatSO y1 y2) beta) => cons y1 nil
  | conjSO beta1 beta2 => app (funfun beta1) (funfun beta2)
  | _ => nil
  end. *)

Lemma sSahlq_hopeful3_REV : forall lx lP beta alpha rel atm y xn W Iv Ip Ir,
  REL rel = true ->
  BAT atm = true ->
ex_FOvar_x_ll y (FOv_att_P_l atm lP) = false ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  attached_allFO_x beta (Var xn) = false ->
  attached_exFO_x beta (Var xn) = false ->
  closed_except beta (Var xn) ->
is_in_FOvar (Var 0) (FOvars_in atm) = false ->
  x_occ_in_alpha (instant_cons_empty' (conjSO rel atm) beta) (Var xn) = true ->
  is_in_pred_l (preds_in (implSO (conjSO rel atm) beta)) lP = true ->
  (exists P, P_occurs_in_alpha alpha P = true) ->
 (forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir alpha <-> SOturnst W Iv Ip Ir (list_closed_allFO (implSO (conjSO rel atm) beta) lx)) ->
  SOturnst W Iv Ip Ir (replace_pred_l (list_closed_allFO (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)  
      (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) beta)) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn)))))) lx)
    lP (list_Var (length lP) y)
    (calc_lP atm lP)) ->
  SOturnst W Iv Ip Ir (list_closed_SO alpha lP).
Proof.
  intros lx lP beta alpha rel atm Hex y xn W Iv Ip Ir HREL HAT Hun Hno Hat1 Hat2
    Hc Hin8 Hocc Hin Hpocc Hequiv SOt.
  apply sSahlq_instant_aim1_fwd4_closer2_REV_gen in SOt; try assumption.
  pose proof (equiv_list_closed_SO lP  _ _ Hequiv) as H.
  apply H.
  assumption.
Qed.
(* admit.
admit.
Qed.
 *)
Lemma SOQFree_bxatm : forall atm,
  BAT atm = true ->
  SOQFree atm = true.
Proof.
Admitted.


Lemma sSahlq_hopeful3_REV_atm : forall lx lP  beta alpha atm y xn W Iv Ip Ir,
  BAT atm = true ->
ex_FOvar_x_ll y (FOv_att_P_l atm lP) = false ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  attached_allFO_x beta (Var xn) = false ->
  attached_exFO_x beta (Var xn) = false ->
  closed_except beta (Var xn) ->
  x_occ_in_alpha (instant_cons_empty' atm beta) (Var xn) = true ->
  is_in_pred_l (preds_in (implSO atm beta)) lP = true ->
  (exists P, P_occurs_in_alpha alpha P = true) ->
 (forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir alpha <-> SOturnst W Iv Ip Ir (list_closed_allFO (implSO atm beta) lx)) ->
  SOturnst W Iv Ip Ir (replace_pred_l (list_closed_allFO (implSO
    atm
    (newnew_pre (instant_cons_empty' atm beta)  
      (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn))
      (rev_seq (S (max (max_FOv (implSO atm beta)) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn)))))) lx)
    lP (list_Var (length lP) y)
    (calc_lP atm lP)) ->
  SOturnst W Iv Ip Ir (list_closed_SO alpha lP).
Proof.
Admitted.

Lemma sSahlq_lem3 : forall beta rel atm xn P,
  REL rel = true ->
  is_BOXATM_flag_strong_CONJ atm = true ->
  SOQFree beta = true ->
  closed_except beta (Var xn) ->
  attached_allFO_x beta (Var xn) = false ->
ex_attached_allFO_lv
     (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)
        (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
        (rev_seq (S (Nat.max (max_FOv (implSO (conjSO rel atm) beta)) xn))
           (length
              (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta))
                 (Var xn))))) (fun2 (conjSO rel atm) P) = false.
Proof.
  intros beta rel atm xn P HREL HAT Hno Hcl Hatt.
  apply want3; try assumption.
  apply is_in_FOvar_l_fun2.
  simpl.
  rewrite att_allFO_x_REL.
admit. (* apply att_allFO_x_AT. *)
  all : try assumption.
Admitted.

Lemma sSahlq_lem2 : forall lP beta rel atm xn,
  REL rel = true ->
  is_BOXATM_flag_strong_CONJ atm = true ->
  SOQFree beta = true ->
  attached_allFO_x beta (Var xn) = false ->
  closed_except beta (Var xn) ->
ex_attached_allFO_llv
  (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)
     (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
     (rev_seq
        (S (Nat.max (Nat.max (Nat.max (max_FOv rel) (max_FOv atm)) (max_FOv beta)) xn))
        (length (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn)))))
  (FOv_att_P_l (conjSO rel atm) lP) = false.
Proof.
  induction lP; intros beta rel atm xn HREL HAT Hno Hat1 Hcl.
    simpl. reflexivity.

    simpl FOv_att_P_l. simpl.
    pose proof sSahlq_lem3 as H3. simpl in H3. rewrite H3; try assumption.
    clear H3. apply IHlP; assumption.
Qed.

Lemma sSahlq_lem5 : forall beta rel atm xn P,
  REL rel = true ->
  is_BOXATM_flag_strong_CONJ atm = true ->
  SOQFree beta = true ->
  closed_except beta (Var xn) ->
  attached_exFO_x beta (Var xn) = false ->
ex_attached_exFO_lv
     (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)
        (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
        (rev_seq (S (Nat.max (max_FOv (implSO (conjSO rel atm) beta)) xn))
           (length
              (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta))
                 (Var xn))))) (fun2 (conjSO rel atm) P) = false.
Proof.
  intros beta rel atm xn P HREL HAT Hno Hcl Hatt.
  apply want3_EX; try assumption.
  apply is_in_FOvar_l_fun2.
  simpl.
  rewrite att_exFO_x_REL.
admit. (*  apply att_exFO_x_AT. *)
  all : try assumption.
Admitted.


Lemma sSahlq_lem4a : forall lP beta rel atm xn,
  REL rel = true ->
  is_BOXATM_flag_strong_CONJ atm = true ->
  SOQFree beta = true ->
  attached_exFO_x beta (Var xn) = false ->
  closed_except beta (Var xn) ->
ex_attached_exFO_llv
  (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)
     (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
     (rev_seq
        (S (Nat.max (Nat.max (Nat.max (max_FOv rel) (max_FOv atm)) (max_FOv beta)) xn))
        (length (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn)))))
  (FOv_att_P_l (conjSO rel atm) lP) = false.
Proof.
  induction lP; intros beta rel atm xn HREL HAT Hno Hat1 Hcl.
    simpl. reflexivity.

    simpl FOv_att_P_l. simpl.
    pose proof sSahlq_lem5 as H3. simpl in H3. rewrite H3; try assumption.
    clear H3. apply IHlP; assumption.
Qed.

Lemma sSahlq_lem_h1 : forall rel atm beta xn,
REL rel = true ->
BAT atm = true ->
SOQFree beta = true ->
SOQFree
  (implSO (conjSO rel atm)
     (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)
        (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
        (rev_seq (S (Nat.max (max_FOv (implSO (conjSO rel atm) beta)) xn))
           (length
              (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn)))))) =
true.
Proof.
  intros rel atm beta xn Hrel Hatm Hno.
  simpl. rewrite (SOQFree_rel _ Hrel).
  rewrite (SOQFree_bxatm _ Hatm).
  apply SOQFree_newnew_pre. unfold instant_cons_empty'.
  apply SOQFree_rep_pred_l. 2 : assumption.
  apply SOQFree_l_empty.
Qed.

Require Import List.


Lemma ex_FOvar_x_ll_calc_llv_lP : forall lP atm y,
  x_occ_in_alpha atm y = false ->
  ex_FOvar_x_ll y (flat_map (fun l => l) (calc_llv_lP atm lP)) = false.
Admitted.

Lemma ex_FOvar_x_ll_calc_lx1_lP : forall lP atm y,
  x_occ_in_alpha atm y = false ->
  ex_FOvar_x_ll y (calc_lx1_lP atm lP) = false.
Admitted.

Lemma x_occ_in_alpha_implSO_l : forall alpha beta y,
  x_occ_in_alpha (implSO alpha beta) y = false -> 
  x_occ_in_alpha alpha y = false.
Admitted.

Lemma max_FOv_l_instant_cons_empty' : forall alpha beta,
  max_FOv_l (FOvars_in alpha) = max_FOv_l (FOvars_in (instant_cons_empty' beta alpha)).
Admitted.

Lemma rem_FOv_nil : forall l x,
  rem_FOv l x = nil ->
  exists n,
  l = constant_l x n.
Admitted.

Lemma length_sSahlq_pa_l5' : forall lllv  (W : Set) llu (Ir : W -> W -> Prop),
  length lllv = length llu ->
  length (sSahlq_pa_l5' Ir lllv llu) = length lllv.
Proof.
  induction lllv; intros W llu Ir Hl. reflexivity.
  simpl in *. destruct llu. discriminate.
  simpl in *. rewrite IHlllv. reflexivity.
  inversion Hl. reflexivity.
Qed.


Lemma length_calc_llv_lP : forall lP atm,
  length (calc_llv_lP atm lP) = length lP.
Proof.
  induction lP; intros atm. reflexivity.
  simpl. rewrite IHlP. reflexivity.
Qed.


Lemma length_map2 : forall { A B : Type} (l : list (list A)) (f : A -> B),
  length (map2 f l) = length l.
Proof.
  induction l; intros f. reflexivity.
  simpl. rewrite IHl.
  reflexivity.
Qed.

Lemma length_calc_lx1_lP_llv : forall lP atm,
  length (calc_lx1_lP atm lP) = length (calc_llv_lP atm lP).
Proof.
  induction lP; intros atm. reflexivity.
  simpl. rewrite IHlP. reflexivity.
Qed.

Lemma  length_calc_lx1_lP : forall lP atm,
  length (calc_lx1_lP atm lP) = length lP.
Proof.
  induction lP; intros atm. reflexivity.
  simpl. rewrite IHlP. reflexivity.
Qed.

Lemma closed_except_free_FO : forall alpha x,
  closed_except alpha x ->
  free_FO alpha x = true.
Proof.
  intros alpha x H. unfold closed_except in H.
  apply H.
Qed.

Lemma rem_FOv_x_occ_in_alpha : forall alpha x,
  rem_FOv (FOvars_in alpha) x = nil ->
  x_occ_in_alpha alpha x = false.
Admitted.

Lemma sSahlq_instant_aim1_fwd4_nil : forall beta rel atm xn,
closed_except beta (Var xn) ->
rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn) = nil ->
x_occ_in_alpha (instant_cons_empty' (conjSO rel atm) beta) (Var xn) = false.
Proof.
  intros beta rel atm x Hc Hnil.
  apply closed_except_free_FO in Hc.
  apply free_FO_x_occ in Hc.
  apply rem_FOv_x_occ_in_alpha in Hnil.
  assumption.
Qed.

Lemma bound_FO_overP_implSO : forall x alpha beta,
  bound_FO_overP (implSO alpha beta) x = false <->
  bound_FO_overP alpha x = false /\ bound_FO_overP beta x = false.
Proof.
  intros [xn] alpha beta.
  unfold bound_FO_overP.
  simpl. rewrite is_in_FOvar_app.
  case_eq (is_in_FOvar (Var xn) (list_quant_FOv_overP alpha));
    intros Hin. split; intros H. discriminate. apply H.

    split; intros H. apply conj. reflexivity. assumption.
    apply H.
Qed.

Lemma bound_FO_overP_implSO_t : forall x alpha beta,
  bound_FO_overP (implSO alpha beta) x = true <->
  bound_FO_overP alpha x = true \/ bound_FO_overP beta x = true.
Proof.
  intros [xn] alpha beta.
  unfold bound_FO_overP.
  simpl. rewrite is_in_FOvar_app.
  case_eq (is_in_FOvar (Var xn) (list_quant_FOv_overP alpha));
    intros Hin. split; intros H. left. reflexivity. reflexivity.

    split; intros H. right. assumption.
    destruct H. discriminate.
    apply H.
Qed.


Lemma ex_bound_FO_overP_l_implSO : forall l alpha beta,
  ex_bound_FO_overP_l (implSO alpha beta) l = false <->
  ex_bound_FO_overP_l alpha l = false /\ ex_bound_FO_overP_l beta l = false.
Proof.
  induction l; intros alpha beta.
    simpl. split. intros. apply conj; reflexivity. reflexivity.

    simpl.
    case_eq (bound_FO_overP (implSO alpha beta) a);
      intros H. apply bound_FO_overP_implSO_t in H.
      destruct H as [H | H]; rewrite H.
        split; intros H2. discriminate. apply H2.

        split; intros H2. discriminate. apply H2.

      apply bound_FO_overP_implSO in H. destruct H as [H1 H2].
      rewrite H1. rewrite H2. apply IHl.
Qed.

Lemma ex_bound_FO_overP_l_implSO_t : forall l alpha beta,
  ex_bound_FO_overP_l (implSO alpha beta) l = true <->
  ex_bound_FO_overP_l alpha l = true \/ ex_bound_FO_overP_l beta l = true.
Proof.
  induction l; intros alpha beta.
    simpl. split. intros. discriminate.
    intros H. destruct H; discriminate.

    simpl.
    case_eq (bound_FO_overP (implSO alpha beta) a);
      intros H. apply bound_FO_overP_implSO_t in H.
      destruct H as [H | H]; rewrite H.
        split; intros H2. left. reflexivity. reflexivity.

        split; intros H2. right. reflexivity.  reflexivity. 

      apply bound_FO_overP_implSO in H. destruct H as [H1 H2].
      rewrite H1. rewrite H2. apply IHl.
Qed.

Lemma ex_bound_FO_overP_ll_implSO : forall l alpha beta,
  ex_bound_FO_overP_ll (implSO alpha beta) l = false <->
  ex_bound_FO_overP_ll alpha l = false /\ ex_bound_FO_overP_ll beta l = false.
Proof.
  induction l; intros alpha beta.
    simpl. split. intros. apply conj; reflexivity. reflexivity.

    simpl. case_eq (ex_bound_FO_overP_l (implSO alpha beta) a);
      intros H. apply ex_bound_FO_overP_l_implSO_t in H.
      destruct H as [H | H]; rewrite H.
        split; intros H2. discriminate. destruct H2. discriminate.

        split; intros H2. discriminate. destruct H2. discriminate.

      apply ex_bound_FO_overP_l_implSO in H. destruct H as [H1 H2].
      rewrite H1. rewrite H2. apply IHl.
Qed.

Fixpoint list_occ_FOv_pre (x : FOvariable) (l : list FOvariable) (n : nat) : list nat :=
  match l with
  | nil => nil
  | cons y l' => if match x, y with Var xn, Var ym => beq_nat xn ym end 
    then cons n (list_occ_FOv_pre x l' (S n))
    else (list_occ_FOv_pre x l' (S n))
  end.

Definition list_occ_FOv x l := list_occ_FOv_pre x l 1.

Fixpoint eq_nat_list (l1 l2 : list nat) : bool :=
  match l1, l2 with
  | nil, _ => false
  | _, nil => false
  | cons n1 l1', cons n2 l2' => if beq_nat n1 n2 then eq_nat_list l1' l2'
    else false
  end.


Fixpoint same_pattern_FOv_l (l1 l2 : list FOvariable) : bool :=
  match l1, l2 with 
  | nil, _  => true
  | _, nil => true
  | cons x l1', cons y l2' => 
    if eq_nat_list (list_occ_FOv x (cons x l1')) (list_occ_FOv y (cons y l2')) 
      then same_pattern_FOv_l l1' l2'
      else false
  end.

Fixpoint same_pattern_FOv_ll (ll1 ll2 : list (list FOvariable)) : bool :=
  match ll1, ll2 with 
  | nil, _  => true
  | _, nil => true
  | cons lx ll1', cons ly ll2' => if same_pattern_FOv_l lx ly then
    same_pattern_FOv_ll ll1' ll2' else false
  end.

Lemma list_occ_FOv_pre_nil : forall l x n m,
  list_occ_FOv_pre x l (S n) = nil ->
  list_occ_FOv_pre x l m = nil.
Proof.
  induction l; intros [xn] n m H. reflexivity.
  simpl. destruct a as [ym]. simpl in *. 
  case_eq (beq_nat xn ym); intros Hbeq; rewrite Hbeq in *. 
    discriminate.
  apply (IHl _ (S n) _ H).
Qed.

Lemma list_occ_FOv_pre_not_nil : forall l x n m,
  ~ (list_occ_FOv_pre x l (S n) = nil) ->
  ~ (list_occ_FOv_pre x l m = nil).
Proof.
  induction l; intros [xn] n m H H2. contradiction (H eq_refl).
  simpl in *. destruct a as [ym].
  case_eq (beq_nat xn ym); intros Hbeq; rewrite Hbeq in *. 
    discriminate.
  apply (IHl _ (S n) _ H H2).
Qed.

Lemma list_occ_FOv_pre_not_cons_0 : forall l l2 x n,
  ~ (list_occ_FOv_pre x l (S n) = cons 0 l2).
Proof.
  induction l; intros l2 [xn] n H. discriminate.
  simpl in *. destruct a as [ym].
  case_eq (beq_nat xn ym); intros Hbeq; rewrite Hbeq in *.
    discriminate. apply (IHl _ _ _ H).
Qed.

Lemma list_occ_FOv_pre_eq_S_cons : forall l ln ln2 x n m m2,
  list_occ_FOv_pre x l (S n) = cons (S m) ln ->
  list_occ_FOv_pre x l n = cons m2 ln2 ->
  m2 = m.
Proof.
  induction l; intros ln ln2 [xn] n m m2 H1 H2. discriminate.
  destruct a as [ym]. simpl in *.
  case_eq (beq_nat xn ym); intros Hbeq; rewrite Hbeq in *.
    inversion H1 as [[H1a H1b]].
    inversion H2 as [[H2a H2b]].
    rewrite <- H1a. rewrite H2a. reflexivity.

    apply (IHl _ _ _ _ _ _ H1 H2).
Qed.

Fixpoint list_nat_incr (l : list nat) (n : nat) : list nat :=
  match l with
  | nil => nil
  | cons m l' => cons (plus m n) (list_nat_incr l' n)
  end.

    
Lemma beq_nat_S_f : forall n m,
  beq_nat n (n + (S m)) = false.
Proof.
  induction n; intros m. reflexivity.
  simpl in *. apply IHn.
Qed.

Lemma beq_nat_add : forall a b n,
  beq_nat (a + n) (b + n) = beq_nat a b.
Proof.
  induction a; intros b n.
    simpl. destruct b.
      simpl. rewrite <- beq_nat_refl. reflexivity.
      rewrite PeanoNat.Nat.add_comm.
      apply beq_nat_S_f.

    simpl in *. destruct b. simpl. destruct n. reflexivity.
      rewrite beq_nat_comm. rewrite PeanoNat.Nat.add_comm.
      rewrite plus_Sn_m. rewrite plus_n_Sm. apply beq_nat_S_f.

      simpl. apply IHa.
Qed.

Lemma eq_nat_list__add : forall l1 l2 n,
  eq_nat_list (list_nat_incr l1 n) (list_nat_incr l2 n) =
  eq_nat_list l1 l2.
Proof.
  induction l1; intros l2 n. reflexivity.
  simpl. destruct l2. reflexivity.
  simpl. rewrite IHl1.
  rewrite beq_nat_add. reflexivity.
Qed.

Lemma list_occ_FOv_pre_list_nat_incr : forall l n x,
  list_occ_FOv_pre x l (S n) = list_nat_incr (list_occ_FOv_pre x l n) 1.
Proof.
  induction l; intros n [xn]. reflexivity.
  simpl in *. destruct a as [ym].
  case_eq (beq_nat xn ym); intros Hbeq.
    simpl. rewrite one_suc. rewrite IHl. reflexivity.

    apply IHl.
Qed.


Lemma eq_nat_list_list_occ_FOv_pre_S : forall l1 l2 x1 x2 n,
  eq_nat_list (list_occ_FOv_pre  x1 l1 (S n)) (list_occ_FOv_pre x2 l2 (S n)) =
  eq_nat_list (list_occ_FOv_pre x1 l1 n) (list_occ_FOv_pre x2 l2 n).
Proof.
  intros l1 l2 x1 x2 n.
  do 2 rewrite list_occ_FOv_pre_list_nat_incr.
  rewrite eq_nat_list__add. reflexivity.
Qed.

Lemma equiv_fun4_l2'_fwd : forall alpha llv1 llv2 lx P u W Iv Ip Ir,
  length llv1 = length llv2 ->
  length_id_2 llv1 llv2 = true ->
  same_pattern_FOv_ll llv1 llv2 = true ->
  SOturnst W Iv Ip Ir (replace_pred alpha P u (fun4_l2' lx u llv1)) ->
  SOturnst W Iv Ip Ir (replace_pred alpha P u (fun4_l2' lx u llv2)).
Proof.
  induction alpha; intros llv1 llv2 lx P u W Iv Ip Ir Hl1 Hl2 Hs SOt.
Admitted.

Lemma consistent_lP_lllv_new_FOvars_lll : forall lP lllv llx x,
  @consistent_lP_lllv llx lP lllv ->
  @consistent_lP_lllv llx lP (new_FOvars_lll lllv x).
Admitted.

Lemma length_id_1_gen_new_FOvars_ll : forall {A : Type} (l1 :  (list A)) l2 x,
  length_id_1_gen l1 (new_FOvars_ll l2 x) =
  length_id_1_gen l1 l2.
Proof.
  induction l1; intros l2 x. simpl. destruct l2; reflexivity.
  simpl. destruct l2. reflexivity.
  simpl. apply IHl1.
Qed. 

Lemma length_id_2_gen_new_FOvars_lll : forall {A : Type} (l1 : list (list A)) l2 x,
  length_id_2_gen l1 (new_FOvars_lll l2 x) =
  length_id_2_gen l1 l2.
Proof. 
  induction l1; intros l2 x. simpl. destruct l2; reflexivity.
  simpl. destruct l2. reflexivity.
  simpl. rewrite IHl1.
 rewrite length_id_1_gen_new_FOvars_ll.
  reflexivity.
Qed.

Lemma length_id_1_gen_new_FOvars_lll : forall {A : Type} (l1 : list (list A)) l2 x,
  length_id_1_gen l1 (new_FOvars_lll l2 x) =
  length_id_1_gen l1 l2.
Proof.
  induction l1; intros l2 x. simpl. destruct l2; reflexivity.
  simpl in *. destruct l2. reflexivity.
  simpl. apply IHl1.
Qed.

Lemma ex_att_predSO_ll_app_f : forall l1 l2 alpha,
  ex_att_predSO_ll alpha (app l1 l2) = false <->
  ex_att_predSO_ll alpha l1 = false /\ ex_att_predSO_ll alpha l2 = false.
Admitted.

Lemma ex_att_predSO_f : forall alpha m,
  Nat.leb (S(max_FOv alpha)) m = true ->
   ex_att_predSO alpha (Var m) = false.
Proof.
  induction alpha; intros m H; try reflexivity.
    simpl in *. destruct f as [xn]. destruct m. discriminate.
    case_eq (beq_nat (S m) xn); intros Hbeq.
      rewrite <- (beq_nat_true _ _ Hbeq) in *.
      rewrite leb_suc_f in H. discriminate.

      reflexivity.

    simpl in *. destruct m. discriminate.
    destruct f as [ym]. apply leb_max in H.
    destruct H as [H1 H2].
    apply (IHalpha (S m) H2).

    simpl in *. destruct m. discriminate.
    destruct f as [ym]. apply leb_max in H.
    destruct H as [H1 H2].
    apply (IHalpha (S m) H2).

    simpl in *. apply (IHalpha _ H).

    simpl in *. destruct m. discriminate.
    apply leb_max in H. destruct H as [H1 H2].
    rewrite (IHalpha1 (S m) H1).
    apply (IHalpha2 (S m) H2).

    simpl in *. destruct m. discriminate.
    apply leb_max in H. destruct H as [H1 H2].
    rewrite (IHalpha1 (S m) H1).
    apply (IHalpha2 (S m) H2).

    simpl in *. destruct m. discriminate.
    apply leb_max in H. destruct H as [H1 H2].
    rewrite (IHalpha1 (S m) H1).
    apply (IHalpha2 (S m) H2).

    simpl in *. apply (IHalpha _ H).

    simpl in *. apply (IHalpha _ H).
Qed.

Lemma ex_att_predSO_l_new_FOvars_l : forall l alpha,
ex_att_predSO_l alpha (new_FOvars_l l (Var (S (max_FOv alpha)))) = false.
Proof.
  induction l; intros alpha. reflexivity.
  simpl. destruct a as [ym]. rewrite ex_att_predSO_f.
  apply IHl.
    rewrite <- plus_Sn_m.
    apply leb_plus_r.
    apply leb_refl.
Qed.

Lemma ex_att_predSO_ll_new_FOvars_ll : forall l alpha,
ex_att_predSO_ll alpha (new_FOvars_ll l (Var (S (max_FOv alpha)))) = false.
Proof.
  induction l; intros alpha. reflexivity.
  simpl in *.
  rewrite ex_att_predSO_l_new_FOvars_l.
  apply IHl. 
Qed.

Lemma ex_att_predSO_ll_new_FOvars_lll : forall lllv alpha,
  ex_att_predSO_ll alpha (flat_map (fun l => l) (new_FOvars_lll lllv 
    (Var (S (max_FOv alpha))))) = false.
Proof.
  induction lllv; intros alpha. reflexivity.
  simpl. apply ex_att_predSO_ll_app_f.
  apply conj. apply ex_att_predSO_ll_new_FOvars_ll.
  apply IHlllv.
Qed.



Require Import List.

Lemma max_FOv_l_new_FOvars_l : forall l1 xn,
  ~ l1 = nil ->
  max_FOv_l (new_FOvars_l l1 (Var xn)) = plus (max_FOv_l l1) xn.
Proof.
  induction l1; intros xn Hnil.
    contradiction (Hnil eq_refl).

    destruct l1. simpl. destruct a as [ym].
      do 2 rewrite PeanoNat.Nat.max_0_r.
      apply PeanoNat.Nat.add_comm.

      remember (cons f l1) as t.
      simpl. destruct a as [ym].
      rewrite IHl1.
      rewrite (PeanoNat.Nat.add_comm xn).
      apply PeanoNat.Nat.add_max_distr_r.

      rewrite Heqt. discriminate.
Qed.
Definition fun_id_list {A : Type} (l : list A) : list A := l.

Lemma is_in_FOvar_new_FOvars_l : forall l1 xn ym,
  is_in_FOvar (Var (xn + ym)) (new_FOvars_l l1 (Var xn)) =
  is_in_FOvar (Var ym) l1.
Proof.
  induction l1; intros xn ym. reflexivity.
  destruct a as [zn]. simpl.
  rewrite PeanoNat.Nat.add_comm at 1.
  rewrite (PeanoNat.Nat.add_comm xn zn).
  rewrite beq_nat_add.
  rewrite IHl1. reflexivity.
Qed.

Lemma is_in_FOvar_new_FOvars_ll : forall l1 xn ym,
  is_in_FOvar (Var (xn + ym)) (flat_map fun_id_list (new_FOvars_ll l1 (Var xn))) =
  is_in_FOvar (Var ym) (flat_map fun_id_list l1).
Proof.
  induction l1; intros xn ym. reflexivity.
  simpl. do 2 rewrite is_in_FOvar_app.
  rewrite IHl1. unfold fun_id_list.
  rewrite is_in_FOvar_new_FOvars_l. reflexivity.
Qed.

Lemma is_in_FOvar_new_FOvars_lll : forall l1 xn ym,
  is_in_FOvar (Var (xn + ym)) (flat_map fun_id_list(flat_map fun_id_list (new_FOvars_lll l1 (Var xn)))) =
  is_in_FOvar (Var ym) (flat_map fun_id_list(flat_map fun_id_list l1)).
Proof.
  induction l1; intros xn ym. reflexivity.
  simpl. do 2 rewrite flat_map_app. do 2 rewrite is_in_FOvar_app.
  rewrite IHl1. unfold fun_id_list.
  rewrite is_in_FOvar_new_FOvars_ll. reflexivity.
Qed.

Lemma is_all_diff_FOv_new_FOvars_l_app : forall l1 l2 xn,
  Nat.leb (S (max_FOv_l l2)) xn = true ->
  is_all_diff_FOv (app l1 l2) = true ->
  is_all_diff_FOv (app (new_FOvars_l l1 (Var xn)) l2) = true.
Proof.
  induction l1; intros l2 xn Hleb H. assumption.
  simpl in *. destruct a as [ym]. 
  case_eq (is_in_FOvar (Var ym) (app l1 l2)); intros Hin;
    rewrite Hin in *. discriminate.
  rewrite is_in_FOvar_app.
  rewrite is_in_FOvar_new_FOvars_l.
  pose proof Hin as Hin'.
  apply is_in_FOvar_app_l in Hin. rewrite Hin.
  destruct xn. discriminate.
  rewrite lem12.
    apply IHl1; try assumption.

  simpl. apply leb_plus_r. assumption.
Qed.

Lemma is_all_diff_FOv_app : forall l1 l2,
  is_all_diff_FOv (app l1 l2) = true <->
  cap_FOv l1 l2 = nil /\
  is_all_diff_FOv l1 = true /\
  is_all_diff_FOv l2 = true.
Proof.
  induction l1; intros l2. simpl.
    split; intros H. apply conj. reflexivity.
    apply conj. reflexivity. assumption.
    apply H.

    simpl. rewrite is_in_FOvar_app.
    case_eq (is_in_FOvar a l1); intros Hin1.
      split; intros H. discriminate.
      destruct H as [H1 [H2 H3]]. discriminate.

      case_eq (is_in_FOvar a l2); intros Hin2.
        split; intros H. discriminate.
        destruct H as [H1 [H2 H3]]. discriminate.

        apply IHl1.
Qed.

Lemma cap_FOv_app_nil_rev : forall l1 l2 l3,
(cap_FOv l1 l3 = nil /\ cap_FOv l2 l3 = nil) ->
cap_FOv (app l1 l2) l3 = nil.
Proof.
  induction l1; intros l2 l3 H.
    simpl in *. apply H.

    simpl in *. case_eq (is_in_FOvar a l3);
      intros H2; rewrite H2 in *.
      destruct H. discriminate.
    apply (IHl1 l2 l3); assumption.
Qed.

Lemma cap_FOv_new_FOvars_lll_l : forall a l2 x,
cap_FOv (fun_id_list a) (flat_map fun_id_list (flat_map fun_id_list l2)) = nil ->
cap_FOv (fun_id_list (new_FOvars_l a x)) (flat_map fun_id_list (flat_map fun_id_list (new_FOvars_lll l2 x))) = nil.
Proof.
  induction a; intros l2 [xn] H. reflexivity.
  simpl in *. destruct a as [ym].
  rewrite is_in_FOvar_new_FOvars_lll.
  case_eq ( is_in_FOvar (Var ym) (flat_map fun_id_list (flat_map fun_id_list l2)));
    intros Hin; rewrite Hin in *. discriminate.
  apply IHa. assumption.
Qed.

Lemma cap_FOv_new_FOvars_lll_ll : forall l1 l2 x,
  cap_FOv (flat_map fun_id_list l1)  (flat_map fun_id_list (flat_map fun_id_list l2)) = nil ->
  cap_FOv (flat_map fun_id_list (new_FOvars_ll l1 x)) (flat_map fun_id_list (flat_map fun_id_list (new_FOvars_lll l2 x))) = nil.
Proof.
  induction l1; intros l2 x H. reflexivity.
  simpl in *. apply cap_FOv_app_nil in H.
  destruct H as [H1 H2].
  apply cap_FOv_app_nil_rev. 
  apply conj.
    apply cap_FOv_new_FOvars_lll_l. assumption.

    apply IHl1. assumption.
Qed.

Lemma cap_FOv_new_FOvars_ll_l : forall a l2 x,
cap_FOv (fun_id_list a) (flat_map fun_id_list l2) = nil ->
cap_FOv (fun_id_list (new_FOvars_l a x)) (flat_map fun_id_list (new_FOvars_ll l2 x)) = nil.
Proof.
  induction a; intros l2 [xn] H. reflexivity.
  simpl in *. destruct a as [ym].
  rewrite is_in_FOvar_new_FOvars_ll.
  case_eq ( is_in_FOvar (Var ym)  (flat_map fun_id_list l2));
    intros Hin; rewrite Hin in *. discriminate.
  apply IHa. assumption.
Qed.

Lemma is_all_diff_FOv_new_FOvars_l : forall l x,
  is_all_diff_FOv (new_FOvars_l l x) =   is_all_diff_FOv l.
Proof.
  induction l; intros [xn]. reflexivity.
  destruct a as [ym]. simpl.
  rewrite is_in_FOvar_new_FOvars_l. rewrite IHl.
  reflexivity.
Qed.

Lemma is_all_diff_FOv_new_FOvars_ll : forall l2 x,
   is_all_diff_FOv (flat_map (fun l => l) l2) = true ->
  is_all_diff_FOv  (flat_map (fun l => l) (new_FOvars_ll l2 x))  = true.
Proof.
  induction l2; intros x H. reflexivity.
  simpl in *. apply is_all_diff_FOv_app.
  apply is_all_diff_FOv_app in H.
  destruct H as [H1 [H2 H3]].
  apply conj.
    apply cap_FOv_new_FOvars_ll_l. assumption.

    apply conj.
      rewrite is_all_diff_FOv_new_FOvars_l.
      assumption.

      apply IHl2. assumption.
Qed.

Lemma is_all_diff_FOv_new_FOvars_lll : forall l2 x,
   is_all_diff_FOv (flat_map (fun l => l) (flat_map (fun l => l) l2)) = true ->
  is_all_diff_FOv (flat_map (fun l => l) (flat_map (fun l => l) (new_FOvars_lll l2 x))) = true.
Proof.
  induction l2; intros x H. assumption.
  simpl in *. rewrite flat_map_app in *.
  rewrite flat_map_app in H.

  apply is_all_diff_FOv_app.
  apply is_all_diff_FOv_app in H.
  destruct H as [H1 [H2 H3]].
  apply conj.
    apply cap_FOv_new_FOvars_lll_ll. assumption.

    apply conj.
      apply is_all_diff_FOv_new_FOvars_ll. assumption.

      apply IHl2. assumption.
Qed.

Lemma  is_all_diff_FOv2_3 : forall l1 l2,
  length l1 = length l2 ->
  is_all_diff_FOv3 l1 l2 = true ->
  is_all_diff_FOv2 l2 = true.
Proof.
  induction l1; intros l2 Hl H.
    destruct l2. reflexivity. discriminate.

    destruct l2. discriminate.
    simpl in *.
    case_eq (is_in_FOvar a l); intros H2; rewrite H2 in *.
      discriminate.
    case_eq (is_all_diff_FOv l); intros H3; rewrite H3 in *.
      2 : discriminate.
    apply IHl1. inversion Hl. reflexivity.
    assumption.
Qed.

Lemma is_all_diff_FOv3_app : forall l1 l2 l3 l4,
  length l1 = length l3 ->
  length l2 = length l4 ->
  is_all_diff_FOv3 (app l1 l2) (app l3 l4) = true <->
  is_all_diff_FOv2 (app l3 l4) = true /\
  is_all_diff_FOv3 l1 l3 = true /\
  is_all_diff_FOv3 l2 l4 = true.
Proof.
  induction l1; intros l2 l3 l4 Hl1 Hl2.
    simpl. destruct l3. 2 : discriminate.
    simpl. split; intros H.
      apply conj. apply is_all_diff_FOv2_3 in H.
        assumption. assumption.
      apply conj. reflexivity. assumption.

      apply H.

    simpl. destruct l3. discriminate.
    simpl.
    case_eq (is_in_FOvar a l); intros Hin.
      split; intros H.
        discriminate.

        apply H.

      simpl in Hl1. inversion Hl1 as [Hl1'].
      case_eq (is_all_diff_FOv l); intros Hall.
      apply IHl1; assumption.
      split; intros H. discriminate. apply H.
Qed.
 

Lemma length_new_FOvars_ll : forall llv x,
  length (new_FOvars_ll llv x) = length llv.
Proof.
  induction llv; intros [xn]. reflexivity.
  simpl. rewrite IHllv. reflexivity.
Qed.

Lemma length_new_FOvars_l : forall llv x,
  length (new_FOvars_l llv x) = length llv.
Proof.
  induction llv; intros [xn]. reflexivity.
  simpl. rewrite IHllv. reflexivity.
Qed.

Lemma is_all_diff_FOv2_app : forall l1 l2,
  is_all_diff_FOv2 (app l1 l2) = 
  if is_all_diff_FOv2 l1 then is_all_diff_FOv2 l2 else false.
Proof.
  induction l1; intros l2.      
    simpl. reflexivity.

    simpl. case_eq (is_all_diff_FOv a); intros H.
      apply IHl1.

      reflexivity.
Qed.

Lemma is_all_diff_FOv2_new_FOvars_ll : forall l x,
  is_all_diff_FOv2 (new_FOvars_ll l x) = is_all_diff_FOv2 l.
Proof.
  induction l; intros x. reflexivity.
  simpl. rewrite IHl.
  rewrite is_all_diff_FOv_new_FOvars_l. reflexivity.
Qed.

Lemma is_all_diff_FOv2_new_FOvars_lll : forall l x,
  is_all_diff_FOv2 (flat_map fun_id_list (new_FOvars_lll l x)) = is_all_diff_FOv2 (flat_map fun_id_list l).
Proof.
  induction l; intros x. reflexivity.
  simpl. do 2 rewrite is_all_diff_FOv2_app. rewrite IHl.
  unfold fun_id_list at 1.  unfold fun_id_list at 2.
  rewrite is_all_diff_FOv2_new_FOvars_ll. reflexivity.
Qed.

Lemma is_all_diff_FOv__2 : forall l,
  is_all_diff_FOv (flat_map fun_id_list l) = true ->
  is_all_diff_FOv2 l = true.
Proof.
  induction l; intros H. reflexivity.
  simpl in *. apply is_all_diff_FOv_app_t in H.
  destruct H as [H1 H2].
  unfold fun_id_list in H1. rewrite H1. apply IHl. assumption.
Qed.

Lemma is_in_FOvar_new_FOvars_l_2_S: forall l xn ym,
  Nat.leb (S ym) xn = true ->
is_in_FOvar (Var ym) (new_FOvars_l l (Var (xn))) = false.
Proof.
  induction l; intros xn ym H . reflexivity.
  simpl in *. destruct a as [zn]. (*  destruct xn. discriminate. *)
  rewrite IHl. 
  case_eq (beq_nat ym ( ( xn + zn))); intros Hbeq.
    2 : reflexivity.
  destruct xn. discriminate.
  rewrite (beq_nat_true _ _ Hbeq) in H.
  apply leb_plus_take1 in H. 
  rewrite leb_suc_f in H. discriminate.
  assumption.
Qed.

Lemma is_all_diff_FOv__3_new_FOvars_ll : forall l l2 n,
  is_all_diff_FOv (flat_map fun_id_list l) = true ->
 length l2 = length l ->
 Nat.leb (max_FOv_l l2) n = true ->
  is_all_diff_FOv3 l2 (new_FOvars_ll l (Var (S n))) = true.
Proof.
  induction l; intros l2 n H1 Hl2 Hleb. destruct l2; reflexivity.
  simpl in *.
  assert ((new_FOvars_l a (Var (S n)) :: new_FOvars_ll l (Var (S n))) =
      (app (cons (new_FOvars_l a (Var (S n))) nil) (new_FOvars_ll l (Var (S n))))) as Hass.
    reflexivity.
  destruct l2. simpl in *. reflexivity.
  simpl in Hl2. inversion Hl2 as [Hl2'].
  assert ((cons f l2) = (app (cons f nil) l2)) as Hass2.
    reflexivity.
  rewrite Hass. rewrite Hass2. apply is_all_diff_FOv3_app.
    reflexivity.
    rewrite length_new_FOvars_ll. assumption. 

    apply conj.
      simpl.
      apply is_all_diff_FOv_app_t in H1. destruct H1 as [H1 H2].
      unfold fun_id_list in H1. rewrite is_all_diff_FOv_new_FOvars_l.
      rewrite H1. rewrite is_all_diff_FOv2_new_FOvars_ll.
      apply is_all_diff_FOv__2. assumption.

      apply conj.
        simpl. destruct f as [zn].
          rewrite is_in_FOvar_new_FOvars_l_2_S.
          rewrite is_all_diff_FOv_new_FOvars_l.
          apply is_all_diff_FOv_app_t in H1.
          destruct H1 as [H1 H2]. unfold fun_id_list in H1.
          rewrite H1. reflexivity.

          simpl in Hleb. apply leb_max in Hleb. apply Hleb.

        apply IHl; try assumption.
          apply is_all_diff_FOv_app_t in H1. destruct H1 as [H1 H2].
          assumption.

          simpl in Hleb. destruct f.
          apply leb_max in Hleb. apply Hleb.
Qed.


Lemma is_all_diff_FOv__3_new_FOvars_ll2 : forall l l2 n,
  is_all_diff_FOv2 l = true ->
 length l2 = length l ->
 Nat.leb (max_FOv_l l2) n = true ->
  is_all_diff_FOv3 l2 (new_FOvars_ll l (Var (S n))) = true.
Proof.
  induction l; intros l2 n H1 Hl2 Hleb. destruct l2; reflexivity.
  simpl in *.
  assert ((new_FOvars_l a (Var (S n)) :: new_FOvars_ll l (Var (S n))) =
      (app (cons (new_FOvars_l a (Var (S n))) nil) (new_FOvars_ll l (Var (S n))))) as Hass.
    reflexivity.
  destruct l2. simpl in *. reflexivity.
  simpl in Hl2. inversion Hl2 as [Hl2'].
  assert ((cons f l2) = (app (cons f nil) l2)) as Hass2.
    reflexivity.
  rewrite Hass. rewrite Hass2. apply is_all_diff_FOv3_app.
    reflexivity.
    rewrite length_new_FOvars_ll. assumption. 

    apply if_then_else_ft in H1. destruct H1 as [H1 H2].
    apply conj. simpl.
      unfold fun_id_list in H1. rewrite is_all_diff_FOv_new_FOvars_l.
      rewrite H1. rewrite is_all_diff_FOv2_new_FOvars_ll. assumption.

      apply conj.
        simpl. destruct f as [zn].
          rewrite is_in_FOvar_new_FOvars_l_2_S.
          rewrite is_all_diff_FOv_new_FOvars_l. rewrite H1. reflexivity.

          simpl in Hleb. apply leb_max in Hleb. apply Hleb.

        apply IHl; try assumption.
          simpl in Hleb. destruct f.
          apply leb_max in Hleb. apply Hleb.
Qed.


(* Left it here 02/01/18  
Not sure. Think through thoroughly. *)
Lemma is_all_diff_FOv3_new_FOvars_lll : forall l1 l2 n,
  length l1 = length l2 ->
  length_id_2_gen l1 l2 = true ->
  is_all_diff_FOv (flat_map (fun l => l) (flat_map (fun l => l) l2)) = true ->
  Nat.leb (S (max_FOv_l (flat_map (fun l=>l) l1))) n = true ->
  is_all_diff_FOv3 (flat_map (fun l => l) l1)
    (flat_map (fun l => l) (new_FOvars_lll l2 (Var n))) = true.
Proof.
  induction l1; intros l2 n Hl1 Hl2 H Hleb. reflexivity.
  simpl in *. destruct n. discriminate.
  destruct l2. discriminate.
  apply if_then_else_ft in Hl2.
  simpl in *. apply is_all_diff_FOv3_app.
    rewrite length_new_FOvars_ll.
    apply length__id_1_gen. apply Hl2. 

    apply length__id_1_gen.
    apply length_id_gen_2_1. rewrite length_id_2_gen_new_FOvars_lll.
    apply Hl2. rewrite length_id_1_gen_new_FOvars_lll.
    apply length__id_1_gen. inversion Hl1. reflexivity.

    rewrite flat_map_app in H.
    apply is_all_diff_FOv_app in H.
    destruct H as [H1 [H2 H3]].
    apply conj.
      rewrite is_all_diff_FOv2_app.
        rewrite is_all_diff_FOv2_new_FOvars_ll.
        apply is_all_diff_FOv__2 in H2. rewrite H2.

        rewrite is_all_diff_FOv2_new_FOvars_lll.
        apply is_all_diff_FOv__2. assumption.

      apply conj.
        apply is_all_diff_FOv__3_new_FOvars_ll.
          assumption.

          apply length__id_1_gen. apply Hl2.

          rewrite max_FOv_l_app in Hleb.
          apply leb_max in Hleb. apply Hleb.

          apply IHl1; try assumption.
            inversion Hl1. reflexivity.

            apply Hl2.

          rewrite max_FOv_l_app in Hleb.
          apply leb_max in Hleb. apply Hleb.
Qed.

Lemma is_all_diff_FOv3_new_FOvars_lll2 : forall l1 l2 n,
  length l1 = length l2 ->
  length_id_2_gen l1 l2 = true ->
  is_all_diff_FOv2 (flat_map (fun l => l) l2) = true ->
  Nat.leb (S (max_FOv_l (flat_map (fun l=>l) l1))) n = true ->
  is_all_diff_FOv3 (flat_map (fun l => l) l1)
    (flat_map (fun l => l) (new_FOvars_lll l2 (Var n))) = true.
Proof.
  induction l1; intros l2 n Hl1 Hl2 H Hleb. reflexivity.
  simpl in *. destruct n. discriminate.
  destruct l2. discriminate.
  apply if_then_else_ft in Hl2.
  simpl in *. apply is_all_diff_FOv3_app.
    rewrite length_new_FOvars_ll.
    apply length__id_1_gen. apply Hl2. 

    apply length__id_1_gen.
    apply length_id_gen_2_1. rewrite length_id_2_gen_new_FOvars_lll.
    apply Hl2. rewrite length_id_1_gen_new_FOvars_lll.
    apply length__id_1_gen. inversion Hl1. reflexivity.

    rewrite is_all_diff_FOv2_app in H.
    apply if_then_else_ft in H.
    destruct H as [H1 H2].
    apply conj.
      rewrite is_all_diff_FOv2_app.
        rewrite is_all_diff_FOv2_new_FOvars_ll. rewrite H1.
        rewrite is_all_diff_FOv2_new_FOvars_lll. assumption.

      apply conj.
        apply is_all_diff_FOv__3_new_FOvars_ll2. assumption.
          apply length__id_1_gen. apply Hl2.

          rewrite max_FOv_l_app in Hleb.
          apply leb_max in Hleb. apply Hleb.

          apply IHl1; try assumption.
            inversion Hl1. reflexivity.

            apply Hl2.

          rewrite max_FOv_l_app in Hleb.
          apply leb_max in Hleb. apply Hleb.
Qed.

Lemma leb_max_FOv_l_calc_lx1_P : forall atm P,
  Nat.leb (max_FOv_l (calc_lx1_P atm P)) (max_FOv atm) = true.
Proof.
  induction atm; intros P; try reflexivity.
    simpl. destruct atm; try reflexivity.
    case_eq (P_branch_allFO atm2 P); intros H.
      destruct atm1; try reflexivity. simpl.
        destruct f0. destruct f. destruct f1.
        rewrite PeanoNat.Nat.max_0_r.
        rewrite max_comm.
        do 3 apply leb_max_suc3.
        apply leb_refl.

        reflexivity.

    simpl. rewrite max_FOv_l_app.
    apply leb_max_max_gen.
    apply IHatm1. apply IHatm2.
Qed.

Lemma leb_max_FOv_l_calc_llv_P : forall atm P,
  Nat.leb (max_FOv_l (flat_map (fun l => l) (calc_llv_P atm P))) (max_FOv atm) = true.
Proof.
Admitted.

Lemma max_FOv_l_calc_lx1_lP : forall lP atm,
  Nat.leb (max_FOv_l (flat_map (fun l => l) (calc_lx1_lP atm lP)))
          (max_FOv atm) = true.
Proof.
  induction lP; intros atm. reflexivity.
  simpl in *. rewrite max_FOv_l_app.
  pose proof (leb_max_max_gen (max_FOv_l (calc_lx1_P atm a)) (max_FOv atm)
    (max_FOv_l (flat_map (fun l => l) (calc_lx1_lP atm lP)))
     (max_FOv atm)) as Hass.
  rewrite max_refl in Hass. apply Hass.
    apply leb_max_FOv_l_calc_lx1_P.

    apply IHlP.
Qed.


Lemma max_FOv_l_calc_llv_lP : forall lP atm,
  Nat.leb (max_FOv_l (flat_map (fun l => l) (flat_map (fun l => l) (calc_llv_lP atm lP))))
          (max_FOv atm) = true.
Proof.
  induction lP; intros atm. reflexivity.
  simpl in *. rewrite flat_map_app. rewrite max_FOv_l_app.
  pose proof (leb_max_max_gen  (max_FOv_l (flat_map (fun l : list FOvariable => l) (calc_llv_P atm a))) (max_FOv atm)
    (max_FOv_l
        (flat_map (fun l : list FOvariable => l)
           (flat_map (fun l : list (list FOvariable) => l) (calc_llv_lP atm lP))))
     (max_FOv atm)) as Hass.
  rewrite max_refl in Hass. apply Hass.
    apply leb_max_FOv_l_calc_llv_P.

    apply IHlP.
Qed.

Lemma bound_FO_overP_is_in_FOvar : forall l alpha a,
  is_in_FOvar a l = true ->
  ex_bound_FO_overP_l alpha l = false ->
  bound_FO_overP alpha a =  false.
Proof. 
  induction l; intros alpha P H1 H2. discriminate.
  simpl in *. destruct P as [Pn]. destruct a as [Qm].
  apply if_then_else_tf in H2. destruct H2 as [H2 H3].
  case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *.
    rewrite (beq_nat_true _ _ Hbeq) in *. assumption.

    apply IHl; assumption.
Qed.

Lemma ex_bound_FO_overP_l_is_in : forall l2 l1 alpha,
  ex_bound_FO_overP_l alpha l1 = false ->
  is_in_FOvar_l l2 l1 = true ->
  ex_bound_FO_overP_l alpha l2 = false.
Proof.
  induction l2; intros l1 alpha H1 H2. reflexivity.
  simpl in *. apply if_then_else_ft in H2.
  destruct H2 as [H2 H3].
  rewrite (bound_FO_overP_is_in_FOvar l1 _ _  H2 H1).
  apply (IHl2 _ _ H1 H3).
Qed.

Lemma lemma6 : forall atm rel beta xn,
REL rel = true ->
BAT atm = true ->
attached_allFO_x beta (Var xn) = false ->
attached_exFO_x beta (Var xn) = false ->
  ex_bound_FO_overP_l
    (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)
       (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
       (rev_seq (S (Nat.max (Nat.max (Nat.max (max_FOv rel) (max_FOv atm)) (max_FOv beta)) xn))
          (length (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn)))))
    (FOvars_in atm) = false.
Admitted.

Lemma is_in_FOvar_l_calc_lx1_P_num_conn : forall m n atm P,
  n = num_conn atm ->
  Nat.leb n m = true ->
  BAT atm = true ->
  is_in_FOvar_l (calc_lx1_P atm P) (FOvars_in atm) = true.
Proof. 
  induction m; intros n atm P Hnum Hleb Hbat.
    destruct n. destruct atm; try discriminate.
      reflexivity. discriminate.

    destruct n. destruct atm; try discriminate.
      reflexivity.
    destruct atm; try discriminate.
      simpl in *. destruct atm; try discriminate.
      destruct atm1; try discriminate. destruct f0 as [z1].
      destruct f as [z2]. destruct f1 as [z3].
      rewrite <- beq_nat_refl in *. case_eq (beq_nat z2 z3);
        intros Hbeq; rewrite Hbeq in *. 2 : discriminate.
      simpl. case_eq (P_branch_allFO atm2 P); intros Hp.
        simpl. rewrite <- beq_nat_refl.
        case_eq (beq_nat z1 z2); intros Hbeq2; reflexivity.
        reflexivity.

      simpl. rewrite is_in_FOvar_l_app. reflexivity.
      apply (IHm (num_conn atm1) atm1 P). reflexivity.
        rewrite Hnum in Hleb. simpl in Hleb.
        apply leb_plus_take1 in Hleb. assumption.
        apply BAT_conjSO_l in Hbat. assumption.

      apply (IHm (num_conn atm2) atm2 P). reflexivity.
        rewrite Hnum in Hleb. simpl in Hleb.
        apply leb_plus_take2 in Hleb. assumption.
        apply BAT_conjSO_r in Hbat. assumption.
Qed.

Lemma is_in_FOvar_l_calc_lx1_P : forall atm P,
  BAT atm = true ->
  is_in_FOvar_l (calc_lx1_P atm P) (FOvars_in atm) = true.
Proof.
  intros atm P . apply (is_in_FOvar_l_calc_lx1_P_num_conn (num_conn atm) (num_conn atm)).
  reflexivity. apply leb_refl.
Qed.

Lemma lemma5 : forall lP atm rel beta xn,
REL rel = true ->
BAT atm = true ->
attached_allFO_x beta (Var xn) = false ->
attached_exFO_x beta (Var xn) = false ->
ex_bound_FO_overP_ll
  (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)
     (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
     (rev_seq (S (Nat.max (max_FOv (implSO (conjSO rel atm) beta)) xn))
        (length (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn)))))
  (calc_lx1_lP atm lP) = false.
Proof.
  induction lP; intros atm rel beta xn Hrel Hbat Hat1 Hat2. reflexivity.
  simpl. rewrite (ex_bound_FO_overP_l_is_in _ _ _ (lemma6 _ _ _ _ Hrel Hbat Hat1 Hat2)).
  apply IHlP; try assumption.
  apply is_in_FOvar_l_calc_lx1_P. assumption.
Qed.

Lemma new_FOvars_l_0 : forall l,
  new_FOvars_l l (Var 0) = l.
Proof.
  induction l. reflexivity.
  simpl. destruct a . rewrite IHl. 
  reflexivity.
Qed.

Lemma lemma12_pre : forall l a y xn zn W Iv Ip Ir,
Nat.leb (S (max_FOv_l l)) zn = true ->
is_in_FOvar y (a :: nil) = false ->
(* is_in_FOvar a l = false -> *)
ex_FOvar_x_ll y (l :: nil) = false ->
~ y = Var xn ->
~ a = Var xn ->
SOturnst W Iv Ip Ir (replace_FOv (fun4' a y l) y (Var xn)) <->
SOturnst W Iv Ip Ir (replace_FOv (fun4' a y (new_FOvars_l l (Var zn))) y (Var xn)).
Proof.
  induction l; intros [un] [ym] xn zn W Iv Ip Ir Hleb (* Hin *) Hin Hex Hneq1 Hneq2.
    simpl. rewrite <- beq_nat_refl. apply iff_refl.

    simpl. destruct a as [vn].
    simpl in Hex. apply if_then_else_tf in Hex.
    destruct Hex as [Hex1 Hex2].
    apply if_then_else_tf in Hex1. clear Hex2.
    destruct Hex1 as [Hex1 Hex2]. 
    rewrite Hex1.
    simpl in Hin. apply if_then_else_tf in Hin. destruct Hin as [Hin1 Hin3].
    rewrite Hin1.
    case_eq (beq_nat ym (zn + vn)); intros Hbeq.
      
      do 2 rewrite SOturnst_exFO. split; intros [d SOt]; exists d.
        rewrite SOturnst_conjSO in *.
      destruct SOt as [SOt1 SOt2].  
      apply conj.
        simpl. rewrite <- beq_nat_refl.     
        simpl in SOt1. rewrite <- beq_nat_refl in SOt1.
Admitted.

Lemma lemma12 : forall lx1 llv zn xn y W Iv Ip Ir,
length lx1 = length llv ->
 is_in_FOvar y lx1 = false ->
ex_FOvar_x_ll y llv = false ->
~ y = (Var xn) ->
Nat.leb (S (max_FOv_l (flat_map fun_id_list llv))) zn = true ->
SOturnst W Iv Ip Ir (replace_FOv (fun4_l2' lx1 y llv) y (Var xn)) <->
SOturnst W Iv Ip Ir (replace_FOv (fun4_l2' lx1 y (new_FOvars_ll llv (Var zn))) y (Var xn)).
Proof.
  induction lx1; intros llv zn xn y W Iv Ip Ir Hl Hin Hex Hneq  Hleb.
    destruct llv.  simpl. apply iff_refl.
    discriminate.

    simpl. destruct llv. discriminate.
    destruct lx1. destruct llv. 
    simpl max_FOv_l in Hleb. rewrite app_nil_r in Hleb.
    unfold fun_id_list in Hleb. simpl. apply lemma12_pre; try assumption.

Admitted.

Lemma lemma8_predSO : forall p f P y xn lx1 llv W Iv Ip Ir,
length lx1 = length llv ->
  is_in_FOvar y lx1 = false ->
  ex_FOvar_x_ll y llv = false ->
  x_occ_in_alpha (predSO p f) y = false ->
Nat.leb (S (max_FOv_l (flat_map fun_id_list llv))) xn = true ->
SOturnst W Iv Ip Ir (replace_pred (predSO p f) P y (fun4_l2' lx1 y llv)) <->
SOturnst W Iv Ip Ir (replace_pred (predSO p f) P y (fun4_l2' lx1 y (new_FOvars_ll llv (Var xn)))).
Proof.
  intros [Qm] [zn] [Pn] [ym] xn lx1 llv W Iv Ip Ir Hl Hin Hex Hocc Hleb.
  simpl. case_eq (beq_nat Pn Qm); intros Hbeq.
    apply lemma12; try assumption.

    apply iff_refl.
    
Admitted.

Lemma lemma8 : forall alpha llv lx1 y xn P W Iv Ip Ir,
  length lx1 = length llv ->
  is_in_FOvar y lx1 = false ->
  ex_FOvar_x_ll y llv = false ->
  x_occ_in_alpha alpha y = false ->
 Nat.leb (S (max_FOv_l  (flat_map fun_id_list ( llv)))) xn = true ->
  SOturnst W Iv Ip Ir (replace_pred alpha P y
     (fun4_l2' lx1 y llv)) <->
  SOturnst W Iv Ip Ir (replace_pred alpha P y
     (fun4_l2' lx1 y (new_FOvars_ll llv (Var xn)))).
Proof.
  induction alpha; intros llv lx1 y x P W Iv Ip Ir Hl Hin Hex Hocc Hleb.
 apply lemma8_predSO; try assumption.
Admitted.

(* Left it here 3/1/18 *)

Lemma lemma11 : forall lP lllv llx1 l l0 n1 n2 P y xn,
Nat.leb (S (max_FOv_l (flat_map fun_id_list (flat_map fun_id_list (l0 :: lllv))))) xn =
       true ->
  ind_llv (indicies_l2 lP P) llx1 = constant_l l n1 ->
  @ind_gen _ nil (indicies_l2 lP P) lllv = constant_l l0 n2 ->
  exists n3,
     (ind_cond (indicies_l2 lP P)
        (fun4_l2_lP' llx1 (list_Var (length lP) y) 
        (new_FOvars_lll lllv (Var xn)))) = 
      constant_l (fun4_l2' l y  (new_FOvars_ll l0 (Var xn))) n3.
Proof.
  induction lP; intros lllv llx1 l l0 n1 n2 P y xn Hleb Hin1 Hin2.
    simpl in *. exists 0. reflexivity.

    simpl. unfold indicies_l2 in *. simpl in *.
    destruct P as [Pn]. destruct a as [Qm].
    case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *.
      simpl in *. destruct llx1. destruct n1. discriminate.
      destruct l. 2 : discriminate. simpl.
      rewrite ind_cond_nil_gen. exists (S (length (indicies_l2_pre lP (Pred Pn) 1))).
      reflexivity.

      destruct lllv. destruct n2. discriminate.
      destruct l0. 2 : discriminate.
      simpl in *. rewrite ind_cond_nil_gen.
      exists (S (length (indicies_l2_pre lP (Pred Pn) 1))).
      destruct l. reflexivity. simpl. destruct l; reflexivity.

      simpl. destruct n1. discriminate.
      destruct n2. discriminate.
      simpl in *. inversion Hin1 as [[Hin1a Hin1b]].
      inversion Hin2 as [[Hin2a Hin2b]].
      rewrite ind_llv_pre_cons in Hin1b.
      rewrite ind_gen_pre_cons in Hin2b.
      destruct xn. discriminate.
      assert (Nat.leb
         (max_FOv_l
            (flat_map fun_id_list
               (fun_id_list l0 ++  flat_map fun_id_list lllv))) xn =
       true) as Hass.
        rewrite flat_map_app.
        rewrite max_FOv_l_app.
        do 2 rewrite flat_map_app in Hleb.
        do 2 rewrite max_FOv_l_app in Hleb.
        unfold fun_id_list at 2.
        pose proof (leb_max_max_gen (max_FOv_l (flat_map fun_id_list l0)) xn
          (max_FOv_l (flat_map fun_id_list (flat_map fun_id_list lllv))) xn) as H2.
        rewrite max_refl in H2. apply H2.
          apply leb_max in Hleb. apply Hleb.

          apply leb_max in Hleb. destruct Hleb as [Hl1 Hl2].
          apply leb_max in Hl2. apply Hl2.

      destruct (IHlP _ _ _ _ _ _ _ y (S xn) Hass Hin1b Hin2b) as [nn Hnn].
      rewrite ind_cond_ind_l2_pre_cons.
      rewrite Hnn.
      exists (S nn). reflexivity.

(* --- *)

      destruct llx1. rewrite ind_llv_nil_gen in Hin1.
      destruct l. simpl. rewrite ind_cond_nil_gen.
      exists (length (indicies_l2_pre lP (Pred Pn) 1)).
      reflexivity.

      destruct n1. simpl in *. destruct l. destruct l0. simpl.
          rewrite ind_cond_nil_gen. exists (length (indicies_l2_pre lP (Pred Pn) 1)).
          reflexivity.

          simpl. rewrite ind_cond_nil_gen.
          case_eq (length (indicies_l2_pre lP (Pred Pn) 1)).
            intros Hnil. exists 0. reflexivity.
            intros mm Hmm. rewrite Hmm in Hin1. discriminate.

        destruct l0.
          simpl. rewrite ind_cond_nil_gen. exists (length (indicies_l2_pre lP (Pred Pn) 1)).
          reflexivity.

          rewrite ind_cond_nil_gen. simpl.
          case_eq (length (indicies_l2_pre lP (Pred Pn) 1)).
            intros Hnil. exists 0. reflexivity.
            intros mm Hmm. rewrite Hmm in Hin1. discriminate.

          case_eq (length (indicies_l2_pre lP (Pred Pn) 1)).
            intros Hnil. rewrite Hnil in *. discriminate.
            intros mm Hmm. rewrite Hmm in Hin1. discriminate.

      rewrite ind_llv_ind_l2_pre_cons in Hin1.
      destruct lllv. rewrite ind_gen_nil_gen in Hin2.
      destruct l0. simpl. rewrite ind_cond_nil_gen.
      exists (length (indicies_l2_pre lP (Pred Pn) 1)). destruct l.
      reflexivity. simpl. destruct l; reflexivity.

      destruct n2. simpl in *. rewrite ind_cond_nil_gen.
        case_eq (length (indicies_l2_pre lP (Pred Pn) 1)).
          intros Hnil. exists 0. reflexivity.

          intros mm Hmm. rewrite Hmm in *. discriminate.

        case_eq (length (indicies_l2_pre lP (Pred Pn) 1)).
          intros Hnil. rewrite Hnil in Hin2. discriminate.

          intros mm Hmm. rewrite Hmm in *. discriminate.

      rewrite ind_gen_pre_cons in Hin2.
      assert (match xn with
 | 0 => false
 | S m' =>
     Nat.leb
       (max_FOv_l (flat_map fun_id_list (fun_id_list l0 ++ flat_map fun_id_list lllv)))
       m'
 end = true) as Hass.
        destruct xn. discriminate.
        rewrite flat_map_app.
        simpl in Hleb. 
        do 2 rewrite flat_map_app in Hleb.
        do 2 rewrite max_FOv_l_app in Hleb.
        rewrite max_FOv_l_app.
        apply leb_max in Hleb. destruct Hleb as [Hleb1 Hleb2].
        apply leb_max in Hleb2. destruct Hleb2.
        pose proof (leb_max_max_gen (max_FOv_l (flat_map fun_id_list (fun_id_list l0)))
          xn (max_FOv_l (flat_map fun_id_list (flat_map fun_id_list lllv))) xn) as H2.
        rewrite max_refl in H2. apply H2; assumption.

      destruct (IHlP _ _ _ _ _ _ _ y xn Hass Hin1 Hin2) as [nn Hnn].
      exists ( nn). simpl. rewrite ind_cond_ind_l2_pre_cons. rewrite Hnn.
      reflexivity.
Qed.

Lemma lemma10 : forall lP a P lllv l0 llx1 l y xn,
consistent_lP_llv_P (a :: lP) (l :: llx1) P ->
@consistent_lP_lllv_P nil (a :: lP) (l0 :: lllv) P ->
Nat.leb (S (max_FOv_l (flat_map fun_id_list (flat_map fun_id_list (l0 :: lllv))))) xn =
       true ->
length lP = length llx1 ->
length lP = length lllv ->
consistent_lP_lcond_P (a :: lP)
  (fun4_l2' l y l0
   :: fun4_l2_lP' llx1 (list_Var (length lP) y) (new_FOvars_lll lllv (Var xn))) P.
Proof.
  intros until 0. intros Hcon1 Hcon2 Hleb Hl1 Hl2.
  unfold consistent_lP_lcond_P.
  unfold consistent_lP_llv_P in *.
  unfold consistent_lP_lllv_P in *.
  unfold indicies_l2 in *.
  destruct a as [Qm]. destruct P as [Pn].
  simpl in *. case_eq (beq_nat Pn Qm); intros Hbeq;
    rewrite Hbeq in *. simpl in *.
    rewrite ind_llv_ind_l2_pre_cons in Hcon1.
    rewrite ind_gen_pre_cons in Hcon2.
    rewrite ind_cond_ind_l2_pre_cons.

    destruct Hcon1 as [l1 [n1 Hcon1]].
    destruct Hcon2 as [l2 [n2 Hcon2]].
    unfold is_constant.
Admitted.


Lemma lemma9 : forall lP a lllv l0 llx1 l y xn,
consistent_lP_llv (a :: lP) (l :: llx1) ->
@consistent_lP_lllv nil (a :: lP) (l0 :: lllv) ->
Nat.leb (S (max_FOv_l (flat_map fun_id_list (flat_map fun_id_list (l0 :: lllv))))) xn =
       true ->
length lP = length llx1 ->
length lP = length lllv ->
consistent_lP_lcond (a :: lP)
  (fun4_l2' l y l0
   :: fun4_l2_lP' llx1 (list_Var (length lP) y) (new_FOvars_lll lllv (Var xn))).
Proof.
  intros until 0. intros Hcon1 Hcon2 Hleb Hl1 Hl2 P.
Admitted.

Lemma x_occ_in_alpha_rep_FOv_f : forall alpha x y,
  ~ x = y ->
  x_occ_in_alpha (replace_FOv alpha x y) x = false.
Proof.
  induction alpha; intros [xn] [ym] H.
    simpl. destruct p. destruct f as [zn].
    case_eq (beq_nat xn zn); intros Hbeq.
      simpl. apply FOvar_neq. assumption.
      simpl. assumption.

    destruct f as [z1]. destruct f0 as [z2].
    simpl. case_eq (beq_nat xn z1); intros Hbeq;
      case_eq (beq_nat xn z2); intros Hbeq2;
        simpl; try rewrite (FOvar_neq _ _ H). reflexivity.

        assumption.

        rewrite Hbeq. reflexivity. rewrite Hbeq. rewrite Hbeq2.
        reflexivity.

    destruct f as [z1]. destruct f0 as [z2].
    simpl. case_eq (beq_nat xn z1); intros Hbeq;
      case_eq (beq_nat xn z2); intros Hbeq2;
        simpl; try rewrite (FOvar_neq _ _ H). reflexivity.

        assumption.

        rewrite Hbeq. reflexivity. rewrite Hbeq. rewrite Hbeq2.
        reflexivity.

    destruct f as [z1].
    simpl. case_eq (beq_nat xn z1); intros Hbeq.
      simpl. rewrite (FOvar_neq _ _ H). apply IHalpha. assumption.

      simpl. rewrite Hbeq.

      apply IHalpha. assumption.

    destruct f as [z1].
    simpl. case_eq (beq_nat xn z1); intros Hbeq.
      simpl. rewrite (FOvar_neq _ _ H). apply IHalpha. assumption.

      simpl. rewrite Hbeq.

      apply IHalpha. assumption.

    simpl in *. apply IHalpha. assumption.

    simpl. rewrite IHalpha1. apply IHalpha2. all : try assumption.

    simpl. rewrite IHalpha1. apply IHalpha2. all : try assumption.

    simpl. rewrite IHalpha1. apply IHalpha2. all : try assumption.

    destruct p. simpl. apply IHalpha. assumption.

    destruct p. simpl. apply IHalpha. assumption.
Qed.

Lemma x_occ_in_alpha_rep_pred : forall alpha P cond y,
  x_occ_in_alpha alpha y = false ->
  x_occ_in_alpha (replace_pred alpha P y cond) y = false.
Proof.
  induction alpha; intros P cond y H.
    destruct p as [Qm]. destruct P as [Pn].
    simpl in *. destruct f as [xn]. destruct y as [ym].
    case_eq (beq_nat Pn Qm); intros Hbeq.
      apply x_occ_in_alpha_rep_FOv_f.
      apply beq_nat_false_FOv. assumption.

      simpl. assumption.

    simpl in *. destruct P as [Pn]. destruct f as [z1].
    destruct f0 as [z2]. simpl. destruct y as [ym].
    assumption.

    simpl in *. destruct P as [Pn]. destruct f as [z1].
    destruct f0 as [z2]. simpl. destruct y as [ym].
    assumption.

    destruct f as [zn]. simpl in *. destruct y as [ym].
    destruct P. simpl. apply if_then_else_tf in H.
    destruct H as [H1 H2]. rewrite H1. apply IHalpha. assumption.

    destruct f as [zn]. simpl in *. destruct y as [ym].
    destruct P. simpl. apply if_then_else_tf in H.
    destruct H as [H1 H2]. rewrite H1. apply IHalpha. assumption.

    destruct P. simpl in *. apply IHalpha. assumption.

    destruct P. simpl in *. apply if_then_else_tf in H.
    destruct H as [H1 H2].
    rewrite (IHalpha1 _ _ _  H1).
    apply (IHalpha2 _ _ _  H2).

    destruct P. simpl in *. apply if_then_else_tf in H.
    destruct H as [H1 H2].
    rewrite (IHalpha1 _ _ _  H1).
    apply (IHalpha2 _ _ _  H2).

    destruct P. simpl in *. apply if_then_else_tf in H.
    destruct H as [H1 H2].
    rewrite (IHalpha1 _ _ _  H1).
    apply (IHalpha2 _ _ _  H2).

    destruct p as [Qm]. destruct P as [Pn]. simpl.
    case_eq (beq_nat Pn Qm); intros Hbeq; simpl;
      apply IHalpha; assumption.

    destruct p as [Qm]. destruct P as [Pn]. simpl.
    case_eq (beq_nat Pn Qm); intros Hbeq; simpl;
      apply IHalpha; assumption.
Qed.

Lemma x_occ_in_alpha_rep_pred_l : forall lP alpha cond y,
  x_occ_in_alpha alpha y = false ->
  x_occ_in_alpha (replace_pred_l alpha lP (list_Var (length lP) y) cond) y = false.
Proof.
  induction lP; intros alpha cond y H. assumption.
  simpl in *. destruct cond. assumption.
  apply x_occ_in_alpha_rep_pred.
  apply IHlP. assumption.
Qed.

Lemma lemma7 : forall lP lllv alpha llx1 y xn W Iv Ip Ir,
  length lP = length llx1 ->
  length lP = length lllv ->
  length_id_2_gen llx1 lllv = true ->
  ex_FOvar_x_ll y llx1 = false ->
  ex_FOvar_x_ll y (flat_map fun_id_list lllv) = false ->
x_occ_in_alpha alpha y = false ->
(*   ~ (Var xn) = y -> *)
  Nat.leb (S (max_FOv_l (flat_map fun_id_list (flat_map fun_id_list lllv)))) xn = true ->
  SOturnst W Iv Ip Ir (replace_pred_l alpha lP (list_Var (length lP) y)
     (fun4_l2_lP' llx1 (list_Var (length lP) y) lllv)) <->
  SOturnst W Iv Ip Ir (replace_pred_l alpha lP (list_Var (length lP) y)
     (fun4_l2_lP' llx1 (list_Var (length lP) y) (new_FOvars_lll lllv (Var xn)))).
Proof.
  induction lP; intros lllv alpha llx1 y xn W Iv Ip Ir Hl1 Hl2 Hl3 Hex1 Hex2 (* Hneq *) Hocc Hleb.
    simpl. apply iff_refl.

    destruct llx1. discriminate.
    destruct lllv. discriminate.
    simpl in Hl1. inversion Hl1 as [Hl1'].
    simpl in Hl2. inversion Hl2 as [Hl2'].
    simpl.
(*     pose proof (consistent_lP_llv_cons_rem_gen _ _ _ _ Hcon1) as Hcon1'.
    pose proof (consistent_lP_lllv_cons _ _ _ _ nil Hcon2) as Hcon2'. *)
    pose proof (length_list_Var (length lP) y) as H1.
      symmetry in H1.
    assert (length lP =
length (fun4_l2_lP' llx1 (list_Var (length lP) y) (new_FOvars_lll lllv (Var xn)))) as H2.
      rewrite length_fun4_l2_lP'. assumption. rewrite length_list_Var.
      symmetry. assumption.
      rewrite length_new_FOvars_lll. rewrite <- Hl1'. assumption.
    assert (is_unary_predless_l
  (fun4_l2_lP' llx1 (list_Var (length lP) y) (new_FOvars_lll lllv (Var xn))) = true) as H3.
      apply is_un_predless_l_fun4_l2_lP'.
    assert (is_unary_predless (fun4_l2' l y (new_FOvars_ll l0 (Var xn))) = true) as H4.
      apply is_un_predless_fun4_l2'.
    assert (length lP = length (fun4_l2_lP' llx1 (list_Var (length lP) y) lllv)) as H5.
      rewrite length_fun4_l2_lP'. assumption.
    assert (is_unary_predless_l (fun4_l2_lP' llx1 (list_Var (length lP) y) lllv) = true) as H6.
      apply is_un_predless_l_fun4_l2_lP'. rewrite length_list_Var. symmetry. assumption.
      rewrite <- Hl1'. assumption.
    assert (is_unary_predless (fun4_l2' l y l0) = true) as H7.
      apply is_un_predless_fun4_l2'.
    assert (is_unary_predless_l (fun4_l2_lP' llx1 (list_Var (length lP) y) lllv) = true) as H8.
      apply is_un_predless_l_fun4_l2_lP'.
    assert (Nat.leb (S (max_FOv_l (flat_map fun_id_list (flat_map fun_id_list lllv)))) xn = true) as H9.
      simpl in Hleb. destruct xn. discriminate.
      rewrite flat_map_app in Hleb. rewrite max_FOv_l_app in Hleb.
      apply leb_max in Hleb. apply Hleb.
    assert (Nat.leb (S (max_FOv_l (flat_map fun_id_list l0))) xn = true) as H10.
      simpl in Hleb. destruct xn. discriminate.
      rewrite flat_map_app in Hleb. rewrite max_FOv_l_app in Hleb.
      apply leb_max in Hleb. apply Hleb.
    simpl in Hl3. apply if_then_else_ft in Hl3. destruct Hl3 as [Hl3a Hl3b].
    apply length__id_1_gen in Hl3a.
    apply ex_FOvar_x_ll_cons in Hex1. destruct Hex1 as [Hex1a Hex1b]. 
    simpl in Hex2.  
    rewrite ex_FOvar_x_ll_app in Hex2.
      apply if_then_else_tf in Hex2. destruct Hex2 as [Hex2a Hex2b].
    case_eq (is_in_pred a lP); intros Hin.
      rewrite rep_pred__l_is_in2.
      rewrite rep_pred__l_is_in2.
      apply IHlP. all: try assumption.


split; intros SOt.

  apply (lemma8 _ _ _ _ xn) in SOt; try assumption.
  rewrite rep_pred__l_switch in SOt; try assumption.
  apply (IHlP _ _ _ y xn) in SOt; try assumption.
  rewrite <- rep_pred__l_switch in SOt; try assumption.
  apply x_occ_in_alpha_rep_pred. assumption.  
  apply x_occ_in_alpha_rep_pred_l. assumption. 


  apply (lemma8 _ _ _ _ xn); try assumption.

  apply x_occ_in_alpha_rep_pred_l. assumption.
 
  rewrite rep_pred__l_switch; try assumption.
  apply (IHlP _ _ _ y xn); try assumption.
  apply x_occ_in_alpha_rep_pred. assumption.  

  rewrite <- rep_pred__l_switch; try assumption.
Qed.

Lemma lemma8'_predSO_pre_pre : forall l xn ym a W Iv Ip Ir,
 is_in_FOvar (Var ym) (a :: nil) = false ->
 ex_FOvar_x_ll (Var ym) (l :: nil) = false ->
SOturnst W Iv Ip Ir (replace_FOv (fun4' a (Var ym) l) (Var ym) (Var xn)) <->
SOturnst W Iv Ip Ir (replace_FOv (fun4' a (Var ym) (new_FOvars_l l (Var (S xn)))) (Var ym) (Var xn)).
Proof.
  induction l; intros xn ym [zn] W Iv Ip Ir Hin Hex.
    simpl in Hin. apply if_then_else_tf in Hin. destruct Hin as [Hin1 Hin2].
    simpl. rewrite Hin1. rewrite <- beq_nat_refl.
    apply iff_refl.

    simpl. destruct a as [vn].
    simpl in Hex. apply if_then_else_tf in Hex.
    destruct Hex as [Hex1 Hex2]. clear Hex2.
    apply if_then_else_tf in Hex1. destruct Hex1 as [Hex1 Hex2].
    rewrite Hex1.
    simpl in Hin. apply if_then_else_tf in Hin. destruct Hin as [Hin1 Hin2].
    rewrite Hin1.
Admitted.

Lemma lemma8'_predSO_pre : forall lx1 llv xn ym W Iv Ip Ir,
length lx1 = length llv ->
is_in_FOvar (Var ym) lx1 = false ->
ex_FOvar_x_ll (Var ym) llv = false ->
SOturnst W Iv Ip Ir (replace_FOv (fun4_l2' lx1 (Var ym) llv) (Var ym) (Var xn)) <->
SOturnst W Iv Ip Ir (replace_FOv (fun4_l2' lx1 (Var ym) (new_FOvars_ll llv (Var (S xn)))) (Var ym) (Var xn)).
Proof.
  induction lx1; intros llv xn ym W Iv Ip Ir Hl Hin Hex.
    destruct llv. 2 : discriminate.
    simpl. apply iff_refl.

    destruct llv. discriminate.
    simpl. destruct lx1. destruct llv. 2 : discriminate.
Admitted.
      

Lemma lemma8'_predSO : forall lx1 llv p f P y W Iv Ip Ir,
  length lx1 = length llv ->
  is_in_FOvar y lx1 = false ->
  ex_FOvar_x_ll y llv = false ->
SOturnst W Iv Ip Ir (replace_pred (predSO p f) P y (fun4_l2' lx1 y llv)) <->
SOturnst W Iv Ip Ir
  (replace_pred (predSO p f) P y (fun4_l2' lx1 y (new_FOvars_ll llv (Var (S (max_FOv (predSO p f))))))).
Proof.
  intros until 0. intros H1 H2 H3.
  destruct p as [Qm]; destruct P as [Pn];
  destruct f as [xn]; destruct y as [ym].
  simpl. case_eq (beq_nat Pn Qm); intros Hbeq.
Admitted.

Lemma lemma8' : forall alpha  llv lx1 y  P W Iv Ip Ir,
  length lx1 = length llv ->
  is_in_FOvar y lx1 = false ->
  ex_FOvar_x_ll y llv = false ->
  SOturnst W Iv Ip Ir (replace_pred alpha P y
     (fun4_l2' lx1 y llv)) <->
  SOturnst W Iv Ip Ir (replace_pred alpha P y
     (fun4_l2' lx1 y (new_FOvars_ll llv (Var (S (max_FOv (alpha))))))).
Proof.
  induction alpha; intros llv lx1 y P W Iv Ip Ir Hl Hin Hex.
    apply lemma8'_predSO; try assumption.
Admitted.

Lemma lemma8''_predSO_pre : forall llv lx1 ym y xn W Iv Ip Ir,
length lx1 = length llv ->
is_in_FOvar y lx1 = false ->
is_in_FOvar (Var ym) lx1 = false ->
ex_FOvar_x_ll y llv = false ->
ex_FOvar_x_ll (Var ym) llv = false ->
is_all_diff_FOv3 lx1 llv = true ->
is_all_diff_FOv3 lx1 (new_FOvars_ll llv (Var (S xn))) = true ->
ex_FOvar_x_ll y (new_FOvars_ll llv (Var (S xn))) = false ->
ex_FOvar_x_ll (Var ym) (new_FOvars_ll llv (Var (S xn))) = false ->
SOturnst W Iv Ip Ir (replace_FOv (fun4_l2' lx1 y llv) y (Var ym)) <->
SOturnst W Iv Ip Ir
  (replace_FOv (fun4_l2' lx1 y (new_FOvars_ll llv (Var (S xn)))) y (Var ym)).
Proof.
  induction llv; intros lx1 ym [zn] xn W Iv Ip Ir Hl Hin Hin0 Hex1 Hex3 Hall Hall2 Hex2 Hex4.
    simpl in *. apply iff_refl.

    simpl in *. destruct lx1. discriminate.
    simpl. case_eq lx1.
      intros Hnil. rewrite Hnil in *.
      destruct llv. 2 : discriminate.
      simpl in *.
destruct f as [vn]. apply if_then_else_tf in Hin.
      apply if_then_else_tf in Hin0.
      apply if_then_else_tf in Hex1.
      apply if_then_else_tf in Hex2.
      apply if_then_else_tf in Hex3.
      apply if_then_else_ft in Hall.
      apply if_then_else_ft in Hall2.
      apply if_then_else_tf in Hex4.
      destruct Hin as [Hin Hc]; clear Hc.
      destruct Hin0 as [Hin0 Hc]; clear Hc.
      destruct Hex1 as [Hex1 Hc]; clear Hc.
      destruct Hex2 as [Hex2 Hc]; clear Hc.
      destruct Hex3 as [Hex3 Hc]; clear Hc.
      destruct Hex4 as [Hex4 Hc]; clear Hc.
      destruct Hall as [Hall Hc]; clear Hc.
      destruct Hall2 as [Hall2 Hc]; clear Hc.
      case_eq (is_in_FOvar (Var vn) a); intros Hin3; rewrite Hin3 in *.
        discriminate.
      case_eq (is_in_FOvar (Var vn) (new_FOvars_l a (Var (S xn)))); intros Hin4; 
        rewrite Hin4 in *. discriminate.
      split; intros SOt.
        apply sSahlq_equiv_new_simpl_try3_base_pre in SOt.
        apply sSahlq_equiv_new_simpl_try3_base_pre.

          simpl. rewrite Hin. assumption.
          simpl. rewrite Hin0. assumption.
          
          assumption. assumption.

rewrite length_new_FOvars_l. assumption.

          simpl. rewrite Hin. assumption.
          simpl. rewrite Hin0. assumption.
  
          all : try assumption.


        apply sSahlq_equiv_new_simpl_try3_base_pre in SOt.
        apply sSahlq_equiv_new_simpl_try3_base_pre.

          simpl. rewrite Hin. assumption.
          simpl. rewrite Hin0. assumption.
          
          assumption. assumption.

rewrite length_new_FOvars_l in SOt. assumption.

          simpl. rewrite Hin. assumption.
          simpl. rewrite Hin0. assumption.
  
          all : try assumption.

    intros x1 lx1' Hlx1. rewrite <- Hlx1.
    case_eq llv. intros Hnil. rewrite Hnil in *.
      rewrite Hlx1 in *. discriminate.
    intros lv llv' Hllv. rewrite <- Hllv.
    case_eq (new_FOvars_ll llv (Var (S xn))).
      intros Hnil. rewrite Hllv in Hnil. discriminate.
    intros ll lll Hlll. rewrite <- Hlll.
    do 2 rewrite replace_FOv_disjSO.
    do 2 rewrite SOturnst_disjSO.
    simpl in *. destruct f as [vn]. 
apply if_then_else_tf in Hin.
      apply if_then_else_tf in Hin0.
      apply if_then_else_tf in Hex1.
      apply if_then_else_tf in Hex2.
      apply if_then_else_tf in Hex3.
      apply if_then_else_ft in Hall.
      apply if_then_else_ft in Hall2.
      apply if_then_else_tf in Hex4.
      destruct Hin as [Hina Hinb].
      destruct Hin0 as [Hin0a Hin0b].
      destruct Hex1 as [Hex1a Hex1b].
      destruct Hex2 as [Hex2a Hex2b]. 
      destruct Hex3 as [Hex3a Hex3b].
      destruct Hex4 as [Hex4a Hex4b].
      destruct Hall as [Halla Hallb].
      destruct Hall2 as [Hall2a Hall2b].
      case_eq (is_in_FOvar (Var vn) a); intros Hin3; rewrite Hin3 in *.
        discriminate.
      case_eq (is_in_FOvar (Var vn) (new_FOvars_l a (Var (S xn)))); intros Hin4; 
        rewrite Hin4 in *. discriminate.
    split; (intros [SOt | SOt]; [left | right]).
        apply sSahlq_equiv_new_simpl_try3_base_pre in SOt.
        apply sSahlq_equiv_new_simpl_try3_base_pre.

          simpl. rewrite Hina. assumption.
          simpl. rewrite Hin0a. assumption.
          
          assumption. assumption.

rewrite length_new_FOvars_l. assumption.

          simpl. rewrite Hina. assumption.
          simpl. rewrite Hin0a. assumption.
  
          all : try assumption.
(* -- *)

apply IHllv; try assumption. simpl in Hl. inversion Hl. reflexivity.

(* -- *)

        apply sSahlq_equiv_new_simpl_try3_base_pre in SOt.
        apply sSahlq_equiv_new_simpl_try3_base_pre.

          simpl. rewrite Hina. assumption.
          simpl. rewrite Hin0a. assumption.
          
          assumption. assumption.

rewrite length_new_FOvars_l in SOt. assumption.

          simpl. rewrite Hina. assumption.
          simpl. rewrite Hin0a. assumption.
  
          all : try assumption.

apply IHllv in SOt; try assumption. simpl in Hl. inversion Hl. reflexivity.
Qed.

Lemma lemma8''_predSO : forall llv lx1 p f y xn P W Iv Ip Ir,
length lx1 = length llv ->
is_in_FOvar y lx1 = false ->
ex_FOvar_x_ll y llv = false ->
ex_FOvar_x_ll y (new_FOvars_ll llv (Var (S xn))) = false ->
(* -- *)
is_in_FOvar f lx1 = false ->
ex_FOvar_x_ll f llv = false ->
is_all_diff_FOv3 lx1 llv = true ->
is_all_diff_FOv3 lx1 (new_FOvars_ll llv (Var (S xn))) = true ->
ex_FOvar_x_ll f (new_FOvars_ll llv (Var (S xn))) = false ->
SOturnst W Iv Ip Ir (replace_pred (predSO p f) P y (fun4_l2' lx1 y llv)) <->
SOturnst W Iv Ip Ir
  (replace_pred (predSO p f) P y (fun4_l2' lx1 y (new_FOvars_ll llv (Var (S xn))))).
Proof.
  intros until 0; intros Hl Hin Hex1 Hex2 Hadd1 Hadd2 Hadd3 Hadd4 Hadd5. simpl.
  destruct P as [Pn]. destruct p as [Qm].
  destruct f as [ym]. case_eq (beq_nat Pn Qm); intros Hbeq.
    apply lemma8''_predSO_pre; try assumption.

    apply iff_refl.
Qed.

Lemma lemma8'' : forall alpha  llv lx1 y xn P W Iv Ip Ir,
  length lx1 = length llv ->
  is_in_FOvar y lx1 = false ->
  ex_FOvar_x_ll y llv = false ->
  ex_FOvar_x_ll y (new_FOvars_ll llv (Var (S xn))) = false ->
  SOturnst W Iv Ip Ir (replace_pred alpha P y
     (fun4_l2' lx1 y llv)) <->
  SOturnst W Iv Ip Ir (replace_pred alpha P y
     (fun4_l2' lx1 y (new_FOvars_ll llv (Var (S xn))))).
Proof.
  induction alpha; intros until 0; intros Hl Hin Hex1 Hex2.
    apply lemma8''_predSO; try assumption.
admit.
Admitted.



Lemma is_in_FOvar_app_lr : forall l1 l2 l,
  is_in_FOvar_l (app l1 l2) l = true ->
  is_in_FOvar_l l2 l = true.
Admitted.

Lemma cap_FOv_app_r_nil : forall l1 l2 l3,
  cap_FOv l1 l2 = nil /\
  cap_FOv l1 l3 = nil <->
  cap_FOv l1 (app l2 l3) = nil.
Proof.
  induction l1; intros l2 l3. 
    simpl. split; intros. reflexivity. apply conj; reflexivity.
  simpl in *.
  rewrite is_in_FOvar_app.
  split; [intros [H1 H2] | intros H].
    case_eq (is_in_FOvar a l2); intros Hin2; rewrite Hin2 in *.   
      discriminate.
    case_eq (is_in_FOvar a l3); intros Hin3; rewrite Hin3 in *.   
      discriminate.
    apply IHl1; try assumption. apply conj; assumption.

  case_eq (is_in_FOvar a l2); intros Hin2; rewrite Hin2 in *.   
      discriminate.
    case_eq (is_in_FOvar a l3); intros Hin3; rewrite Hin3 in *.   
      discriminate.
    apply IHl1; try assumption.
Qed.


Lemma lemma7'' : forall lP lllv alpha llx1 y xn W Iv Ip Ir,
  length lP = length llx1 ->
  length lP = length lllv ->
  length_id_2_gen llx1 lllv = true ->
  ex_FOvar_x_ll y llx1 = false ->
  ex_FOvar_x_ll y (flat_map fun_id_list lllv) = false ->
  ex_FOvar_x_ll y (flat_map fun_id_list (new_FOvars_lll lllv (Var (S xn)))) = false ->
  cap_FOv (flat_map fun_id_list llx1) (flat_map fun_id_list (flat_map fun_id_list lllv)) = nil ->
  SOturnst W Iv Ip Ir (replace_pred_l alpha lP (list_Var (length lP) y)
     (fun4_l2_lP' llx1 (list_Var (length lP) y) lllv)) <->
  SOturnst W Iv Ip Ir (replace_pred_l alpha lP (list_Var (length lP) y)
     (fun4_l2_lP' llx1 (list_Var (length lP) y) (new_FOvars_lll lllv (Var (S xn))))).
Proof.
  induction lP; intros lllv alpha llx1 y xn W Iv Ip Ir Hl1 Hl2 Hl3 Hex1 Hex2 Hex3 Hcap.
    simpl. apply iff_refl.

    destruct llx1. discriminate.
    destruct lllv. discriminate.
    simpl in Hl1. inversion Hl1 as [Hl1'].
    simpl in Hl2. inversion Hl2 as [Hl2'].
    simpl.
(*     pose proof (consistent_lP_llv_cons_rem_gen _ _ _ _ Hcon1) as Hcon1'.
    pose proof (consistent_lP_lllv_cons _ _ _ _ nil Hcon2) as Hcon2'. *)
    pose proof (length_list_Var (length lP) y) as H1.
      symmetry in H1.
    simpl in Hl3. apply if_then_else_ft in Hl3. destruct Hl3 as [Hl3a Hl3b].
    apply length__id_1_gen in Hl3a.
    apply ex_FOvar_x_ll_cons in Hex1. destruct Hex1 as [Hex1a Hex1b]. 
    simpl in Hex2.  
    rewrite ex_FOvar_x_ll_app in Hex2.
      apply if_then_else_tf in Hex2. destruct Hex2 as [Hex2a Hex2b].
    assert (length lP =
length
  (fun4_l2_lP' llx1 (list_Var (length lP) y)
     (new_FOvars_lll lllv (Var (S ( (max_FOv alpha))))))) as H11.
      rewrite length_fun4_l2_lP'. assumption.
      rewrite length_list_Var. symmetry. assumption.
      rewrite length_new_FOvars_lll. rewrite <- Hl1'. assumption.

    assert (is_unary_predless_l
  (fun4_l2_lP' llx1 (list_Var (length lP) y) (new_FOvars_lll lllv (Var (S ( (max_FOv alpha)))))) = true) as H3.
      apply is_un_predless_l_fun4_l2_lP'.
    assert (is_unary_predless (fun4_l2' l y (new_FOvars_ll l0 (Var (S (max_FOv alpha) )))) = true) as H4.
      apply is_un_predless_fun4_l2'.
    assert (length lP = length (fun4_l2_lP' llx1 (list_Var (length lP) y) lllv)) as H5.
      rewrite length_fun4_l2_lP'. assumption. rewrite <- Hl1'. assumption. rewrite <- Hl1'. assumption.

    assert (is_unary_predless_l (fun4_l2_lP' llx1 (list_Var (length lP) y) lllv) = true) as H6.
      apply is_un_predless_l_fun4_l2_lP'.
    assert (is_unary_predless (fun4_l2' l y l0) = true) as H7.
      apply is_un_predless_fun4_l2'.
    simpl in Hex3. pose proof (ex_FOvar_x_ll_app_r _ _ _ Hex3) as Hex3r.
    assert (cap_FOv (flat_map fun_id_list llx1) (flat_map fun_id_list (flat_map fun_id_list lllv)) = nil) as Hcap2.
      simpl in Hcap. apply cap_FOv_app_nil in Hcap.
      destruct Hcap as [Hcap1 Hcap2]. rewrite flat_map_app in Hcap2. 
      apply cap_FOv_app_r_nil in Hcap2. destruct Hcap2 as [Hcap2 Hcap3]. assumption.
pose proof (ex_FOvar_x_ll_app_l _ _ _ Hex3) as Hex3l.

    case_eq (is_in_pred a lP); intros Hin.
      rewrite rep_pred__l_is_in2.
      rewrite rep_pred__l_is_in2.
      apply IHlP. all: try assumption.

rewrite length_fun4_l2_lP'. assumption. 
rewrite length_list_Var. symmetry. assumption.
rewrite length_new_FOvars_lll. rewrite <- Hl1'. assumption.

apply is_un_predless_l_fun4_l2_lP'.
apply is_un_predless_fun4_l2'.


split; intros SOt.
  rewrite rep_pred__l_switch. 
  apply (IHlP lllv); try assumption.
  rewrite <- rep_pred__l_switch.
  apply lemma8''; try assumption.
  all : try assumption.
  
apply is_un_predless_fun4_l2'.
apply is_un_predless_fun4_l2'.

apply is_un_predless_l_fun4_l2_lP'.

  rewrite rep_pred__l_switch in SOt.
  apply (IHlP lllv) in SOt; try assumption.
  rewrite <- rep_pred__l_switch in SOt.
  apply lemma8'' in SOt; try assumption.
  all : try assumption.

apply is_un_predless_fun4_l2'.
apply is_un_predless_fun4_l2'.

apply is_un_predless_l_fun4_l2_lP'.
Qed.

(* Left it here 4/1/18 *)
(* Do on paper; it's getting confusing. *)
Lemma lemma7' : forall lP lllv alpha llx1 y xn W Iv Ip Ir,
  length lP = length llx1 ->
  length lP = length lllv ->
  length_id_2_gen llx1 lllv = true ->
  ex_FOvar_x_ll y llx1 = false ->
  ex_FOvar_x_ll y (flat_map fun_id_list lllv) = false ->
  ex_FOvar_x_ll y (flat_map fun_id_list (new_FOvars_lll lllv (Var (S (max_FOv alpha))))) = false ->
  ex_bound_FO_overP_ll alpha llx1  = false ->
  is_in_FOvar_l (flat_map fun_id_list llx1) (FOvars_in alpha) = true ->
  is_in_FOvar_l (flat_map fun_id_list (flat_map fun_id_list lllv)) (FOvars_in alpha) = true ->
  is_all_diff_FOv3 (flat_map fun_id_list llx1) (flat_map fun_id_list lllv) = true ->
  Nat.leb (max_FOv alpha) xn = true ->
  SOturnst W Iv Ip Ir (replace_pred_l alpha lP (list_Var (length lP) y)
     (fun4_l2_lP' llx1 (list_Var (length lP) y) lllv)) <->
  SOturnst W Iv Ip Ir (replace_pred_l alpha lP (list_Var (length lP) y)
     (fun4_l2_lP' llx1 (list_Var (length lP) y) (new_FOvars_lll lllv (Var (S xn))))).
Proof.
Admitted.
(*
  induction lP; intros lllv alpha llx1 y xn W Iv Ip Ir Hl1 Hl2 Hl3 Hex1 Hex2 Hex3 Hexb Hin1 Hin2 Hall Hleb.
    simpl. apply iff_refl.

    destruct llx1. discriminate.
    destruct lllv. discriminate.
    simpl in Hl1. inversion Hl1 as [Hl1'].
    simpl in Hl2. inversion Hl2 as [Hl2'].
    simpl.
(*     pose proof (consistent_lP_llv_cons_rem_gen _ _ _ _ Hcon1) as Hcon1'.
    pose proof (consistent_lP_lllv_cons _ _ _ _ nil Hcon2) as Hcon2'. *)
    pose proof (length_list_Var (length lP) y) as H1.
      symmetry in H1.
    simpl in Hl3. apply if_then_else_ft in Hl3. destruct Hl3 as [Hl3a Hl3b].
    apply length__id_1_gen in Hl3a.
    apply ex_FOvar_x_ll_cons in Hex1. destruct Hex1 as [Hex1a Hex1b]. 
    simpl in Hex2.  
    rewrite ex_FOvar_x_ll_app in Hex2.
      apply if_then_else_tf in Hex2. destruct Hex2 as [Hex2a Hex2b].
    apply ex_bound_FO_overP_ll_cons in Hexb. destruct Hexb as [Hexb1 Hexb2].
    assert (length lP =
length
  (fun4_l2_lP' llx1 (list_Var (length lP) y)
     (new_FOvars_lll lllv (Var (S ( (max_FOv alpha))))))) as H11.
      rewrite length_fun4_l2_lP'. assumption.
      rewrite length_list_Var. symmetry. assumption.
      rewrite length_new_FOvars_lll. rewrite <- Hl1'. assumption.

    assert (is_unary_predless_l
  (fun4_l2_lP' llx1 (list_Var (length lP) y) (new_FOvars_lll lllv (Var (S ( (max_FOv alpha)))))) = true) as H3.
      apply is_un_predless_l_fun4_l2_lP'.
    assert (is_unary_predless (fun4_l2' l y (new_FOvars_ll l0 (Var (S (max_FOv alpha) )))) = true) as H4.
      apply is_un_predless_fun4_l2'.
    assert (length lP = length (fun4_l2_lP' llx1 (list_Var (length lP) y) lllv)) as H5.
      rewrite length_fun4_l2_lP'. assumption. rewrite <- Hl1'. assumption. rewrite <- Hl1'. assumption.

    assert (is_unary_predless_l (fun4_l2_lP' llx1 (list_Var (length lP) y) lllv) = true) as H6.
      apply is_un_predless_l_fun4_l2_lP'.
    assert (is_unary_predless (fun4_l2' l y l0) = true) as H7.
      apply is_un_predless_fun4_l2'.
    simpl in Hex3. pose proof (ex_FOvar_x_ll_app_r _ _ _ Hex3) as Hex3r.
pose proof (ex_FOvar_x_ll_app_l _ _ _ Hex3) as Hex3l.
(*
    assert (is_unary_predless_l (fun4_l2_lP' llx1 (list_Var (length lP) y) lllv) = true) as H8.
      apply is_un_predless_l_fun4_l2_lP'.
    assert (Nat.leb (S (max_FOv_l (flat_map fun_id_list (flat_map fun_id_list lllv)))) xn = true) as H9.
      simpl in Hleb. destruct xn. discriminate.
      rewrite flat_map_app in Hleb. rewrite max_FOv_l_app in Hleb.
      apply leb_max in Hleb. apply Hleb.
    assert (Nat.leb (S (max_FOv_l (flat_map fun_id_list l0))) xn = true) as H10.
      simpl in Hleb. destruct xn. discriminate.
      rewrite flat_map_app in Hleb. rewrite max_FOv_l_app in Hleb.
      apply leb_max in Hleb. apply Hleb.
*)
    case_eq (is_in_pred a lP); intros Hin.
      rewrite rep_pred__l_is_in2.
      rewrite rep_pred__l_is_in2.
      apply IHlP. all: try assumption.

        simpl in Hin1. apply is_in_FOvar_app_lr in Hin1. assumption.

        simpl in Hin2. rewrite flat_map_app in Hin2.
        apply is_in_FOvar_app_lr in Hin2. assumption.

simpl in Hall. apply is_all_diff_FOv3_app_r in Hall. assumption.
  unfold fun_id_list. assumption.
admit. admit. admit.

split; intros SOt.
 apply lemma8'; try assumption.
admit.
admit.
    rewrite rep_pred__l_switch; try assumption.
    apply (IHlP lllv); try assumption.
admit.
admit.
admit.
admit.
admit.
admit.
admit.

  rewrite rep_pred__l_switch in SOt; try assumption.
  apply IHlP in SOt; try assumption.

  apply lemma8' in SOt; try assumption.

  rewrite rep_pred__l_switch in SOt; try assumption.
  apply IHlP in SOt; try assumption.  
  rewrite <- rep_pred__l_switch in SOt; try assumption.
  


  apply lemma8'; try assumption.
admit.

  rewrite rep_pred__l_switch; try assumption.
  apply IHlP; try assumption.

admit.
admit.
admit.

x_occ_in_alpha 



  apply (lemma8') in SOt; try assumption.

(*   apply (lemma8 _ _ _ _ xn) in SOt; try assumption. *)
  rewrite rep_pred__l_switch in SOt; try assumption.
  apply (IHlP _ _ _ y) in SOt; try assumption.
  rewrite <- rep_pred__l_switch in SOt; try assumption.



  apply (lemma8 _ _ _ _ xn); try assumption.

  apply x_occ_in_alpha_rep_pred_l. assumption.
 
  rewrite rep_pred__l_switch; try assumption.
  apply (IHlP _ _ _ y xn); try assumption.
  apply x_occ_in_alpha_rep_pred. assumption.  

  rewrite <- rep_pred__l_switch; try assumption.
Qed.
*)

(* Lemma lemma7' : forall lP lllv alpha llx1 y W Iv Ip Ir,
  length lP = length llx1 ->
  length lP = length lllv ->
  length_id_2_gen llx1 lllv = true ->
  ex_FOvar_x_ll y llx1 = false ->
  ex_FOvar_x_ll y (flat_map fun_id_list lllv) = false ->
  ex_bound_FO_overP_ll alpha llx1  = false ->
  is_in_FOvar_l (flat_map fun_id_list llx1) (FOvars_in alpha) = true ->
  is_in_FOvar_l (flat_map fun_id_list (flat_map fun_id_list lllv)) (FOvars_in alpha) = true ->
  SOturnst W Iv Ip Ir (replace_pred_l alpha lP (list_Var (length lP) y)
     (fun4_l2_lP' llx1 (list_Var (length lP) y) lllv)) <->
  SOturnst W Iv Ip Ir (replace_pred_l alpha lP (list_Var (length lP) y)
     (fun4_l2_lP' llx1 (list_Var (length lP) y) (new_FOvars_lll lllv (Var (S (max_FOv alpha)))))).
Proof.
  induction lP; intros lllv alpha llx1 y W Iv Ip Ir Hl1 Hl2 Hl3 Hex1 Hex2 Hexb Hin1 Hin2.
    simpl. apply iff_refl.

    destruct llx1. discriminate.
    destruct lllv. discriminate.
    simpl in Hl1. inversion Hl1 as [Hl1'].
    simpl in Hl2. inversion Hl2 as [Hl2'].
    simpl.
(*     pose proof (consistent_lP_llv_cons_rem_gen _ _ _ _ Hcon1) as Hcon1'.
    pose proof (consistent_lP_lllv_cons _ _ _ _ nil Hcon2) as Hcon2'. *)
    pose proof (length_list_Var (length lP) y) as H1.
      symmetry in H1.
    simpl in Hl3. apply if_then_else_ft in Hl3. destruct Hl3 as [Hl3a Hl3b].
    apply length__id_1_gen in Hl3a.
    apply ex_FOvar_x_ll_cons in Hex1. destruct Hex1 as [Hex1a Hex1b]. 
    simpl in Hex2.  
    rewrite ex_FOvar_x_ll_app in Hex2.
      apply if_then_else_tf in Hex2. destruct Hex2 as [Hex2a Hex2b].
    apply ex_bound_FO_overP_ll_cons in Hexb. destruct Hexb as [Hexb1 Hexb2].
    assert (length lP =
length
  (fun4_l2_lP' llx1 (list_Var (length lP) y)
     (new_FOvars_lll lllv (Var (S ( (max_FOv alpha))))))) as H11.
      rewrite length_fun4_l2_lP'. assumption.
      rewrite length_list_Var. symmetry. assumption.
      rewrite length_new_FOvars_lll. rewrite <- Hl1'. assumption.

    assert (is_unary_predless_l
  (fun4_l2_lP' llx1 (list_Var (length lP) y) (new_FOvars_lll lllv (Var (S ( (max_FOv alpha)))))) = true) as H3.
      apply is_un_predless_l_fun4_l2_lP'.
    assert (is_unary_predless (fun4_l2' l y (new_FOvars_ll l0 (Var (S (max_FOv alpha) )))) = true) as H4.
      apply is_un_predless_fun4_l2'.
    assert (length lP = length (fun4_l2_lP' llx1 (list_Var (length lP) y) lllv)) as H5.
      rewrite length_fun4_l2_lP'. assumption. rewrite <- Hl1'. assumption. rewrite <- Hl1'. assumption.

    assert (is_unary_predless_l (fun4_l2_lP' llx1 (list_Var (length lP) y) lllv) = true) as H6.
      apply is_un_predless_l_fun4_l2_lP'.
    assert (is_unary_predless (fun4_l2' l y l0) = true) as H7.
      apply is_un_predless_fun4_l2'.
(*
    assert (is_unary_predless_l (fun4_l2_lP' llx1 (list_Var (length lP) y) lllv) = true) as H8.
      apply is_un_predless_l_fun4_l2_lP'.
    assert (Nat.leb (S (max_FOv_l (flat_map fun_id_list (flat_map fun_id_list lllv)))) xn = true) as H9.
      simpl in Hleb. destruct xn. discriminate.
      rewrite flat_map_app in Hleb. rewrite max_FOv_l_app in Hleb.
      apply leb_max in Hleb. apply Hleb.
    assert (Nat.leb (S (max_FOv_l (flat_map fun_id_list l0))) xn = true) as H10.
      simpl in Hleb. destruct xn. discriminate.
      rewrite flat_map_app in Hleb. rewrite max_FOv_l_app in Hleb.
      apply leb_max in Hleb. apply Hleb.
*)
    case_eq (is_in_pred a lP); intros Hin.
      rewrite rep_pred__l_is_in2.
      rewrite rep_pred__l_is_in2.
      apply IHlP. all: try assumption.
        simpl in Hin1. apply is_in_FOvar_app_lr in Hin1. assumption.

        simpl in Hin2. rewrite flat_map_app in Hin2.
        apply is_in_FOvar_app_lr in Hin2. assumption.

split; intros SOt.

  apply lemma8'; try assumption.
admit.
admit.
  rewrite rep_pred__l_switch; try assumption.
  apply IHlP; try assumption.
admit.
admit.
admit.

x_occ_in_alpha 



  apply (lemma8') in SOt; try assumption.

(*   apply (lemma8 _ _ _ _ xn) in SOt; try assumption. *)
  rewrite rep_pred__l_switch in SOt; try assumption.
  apply (IHlP _ _ _ y) in SOt; try assumption.
  rewrite <- rep_pred__l_switch in SOt; try assumption.



  apply (lemma8 _ _ _ _ xn); try assumption.

  apply x_occ_in_alpha_rep_pred_l. assumption.
 
  rewrite rep_pred__l_switch; try assumption.
  apply (IHlP _ _ _ y xn); try assumption.
  apply x_occ_in_alpha_rep_pred. assumption.  

  rewrite <- rep_pred__l_switch; try assumption.
Qed.

Admitted. *)



(*     rewrite rep_pred__l_switch; try assumption.
    split; intros SOt.
      apply lemma8; try assumption.

      rewrite rep_pred__l_switch; try assumption.
      apply (IHlP _ _ _ y xn) in SOt; try assumption.

      apply lemma8 in SOt; try assumption. 
      rewrite rep_pred__l_switch in SOt; try assumption.
      apply (IHlP _ _ _ y xn); try assumption.
Qed. *)

(* Lemma lemma7 : forall lP lllv alpha llx1 y xn W Iv Ip Ir,
  length lP = length llx1 ->
  length lP = length lllv ->
  consistent_lP_llv lP llx1 ->
  @consistent_lP_lllv nil lP lllv ->
  Nat.leb (S (max_FOv_l (flat_map fun_id_list (flat_map fun_id_list lllv)))) xn = true ->
  SOturnst W Iv Ip Ir (replace_pred_l alpha lP (list_Var (length lP) y)
     (fun4_l2_lP' llx1 (list_Var (length lP) y) lllv)) <->
  SOturnst W Iv Ip Ir (replace_pred_l alpha lP (list_Var (length lP) y)
     (fun4_l2_lP' llx1 (list_Var (length lP) y) (new_FOvars_lll lllv (Var xn)))).
Proof.
  induction lP; intros lllv alpha llx1 y xn W Iv Ip Ir Hl1 Hl2 Hcon1 Hcon2 Hleb.
    simpl. apply iff_refl.

    destruct llx1. discriminate.
    destruct lllv. discriminate.
      simpl in Hl1. inversion Hl1 as [Hl1'].
    simpl in Hl2. inversion Hl2 as [Hl2'].
    simpl.
    pose proof (consistent_lP_llv_cons_rem_gen _ _ _ _ Hcon1) as Hcon1'.
    pose proof (consistent_lP_lllv_cons _ _ _ _ nil Hcon2) as Hcon2'.
    pose proof (length_list_Var (length lP) y) as H1.
      symmetry in H1.
    assert (length lP =
length (fun4_l2_lP' llx1 (list_Var (length lP) y) (new_FOvars_lll lllv (Var xn)))) as H2.
      rewrite length_fun4_l2_lP'. assumption. rewrite length_list_Var.
      symmetry. assumption.
      rewrite length_new_FOvars_lll. rewrite <- Hl1'. assumption.
    assert (is_unary_predless_l
  (fun4_l2_lP' llx1 (list_Var (length lP) y) (new_FOvars_lll lllv (Var xn))) = true) as H3.
      apply is_un_predless_l_fun4_l2_lP'.
    assert (is_unary_predless (fun4_l2' l y (new_FOvars_ll l0 (Var xn))) = true) as H4.
      apply is_un_predless_fun4_l2'.
    assert (length lP = length (fun4_l2_lP' llx1 (list_Var (length lP) y) lllv)) as H5.
      rewrite length_fun4_l2_lP'. assumption.
    assert (is_unary_predless_l (fun4_l2_lP' llx1 (list_Var (length lP) y) lllv) = true) as H6.
      apply is_un_predless_l_fun4_l2_lP'. rewrite length_list_Var. symmetry. assumption.
      rewrite <- Hl1'. assumption.
    assert (is_unary_predless (fun4_l2' l y l0) = true) as H7.
      apply is_un_predless_fun4_l2'.
    assert (is_unary_predless_l (fun4_l2_lP' llx1 (list_Var (length lP) y) lllv) = true) as H8.
      apply is_un_predless_l_fun4_l2_lP'.
    case_eq (is_in_pred a lP); intros Hin.
      rewrite rep_pred__l_is_in2.
      rewrite rep_pred__l_is_in2.
      apply IHlP. all: try assumption.
admit.
    simpl. split; intros SOt.
      apply lemma8.
      rewrite rep_pred__l_switch; try assumption.
      apply (IHlP _ _ _ y xn); try assumption.
      rewrite <- rep_pred__l_consistent in SOt; try assumption.

      apply is_un_predless_l_fun4_l2_lP'.
      apply is_un_predless_fun4_l2'.

admit.

      apply (consistent_lP_lx_list_Var (cons a lP)).

      apply  consistent_lP_llv_cons_rem_gen in Hcon1. assumption.

      apply consistent_lP_lllv_cons in Hcon2. assumption.

      simpl in Hleb.
      destruct xn. discriminate.
      simpl. rewrite flat_map_app in Hleb.
      rewrite max_FOv_l_app in Hleb.
      apply leb_max in Hleb. apply Hleb.

      apply is_un_predless_l_fun4_l2_lP'.
      apply is_un_predless_fun4_l2'.

      apply (consistent_lP_lcond_fun4_l2_lP' (cons a lP) (cons l llx1) (cons l0 lllv) _ nil).
        simpl in *. rewrite <- Hl1. assumption. assumption. 
        assumption.

      apply (consistent_lP_lx_list_Var (cons a lP)).

(* --- *)

      apply lemma8 in SOt.
      rewrite rep_pred__l_consistent; try assumption.
      apply (IHlP _ _ _ y xn); try assumption.

      apply  consistent_lP_llv_cons_rem_gen in Hcon1. assumption.

      apply consistent_lP_lllv_cons in Hcon2. assumption.

      simpl in Hleb.
      destruct xn. discriminate.
      simpl. rewrite flat_map_app in Hleb.
      rewrite max_FOv_l_app in Hleb.
      apply leb_max in Hleb. apply Hleb.

      rewrite <- rep_pred__l_consistent; try assumption.

      apply is_un_predless_l_fun4_l2_lP'.
      apply is_un_predless_fun4_l2'.

admit.

      apply (consistent_lP_lx_list_Var (cons a lP)).


      apply is_un_predless_l_fun4_l2_lP'.
      apply is_un_predless_fun4_l2'.

      apply (consistent_lP_lcond_fun4_l2_lP' (cons a lP) (cons l llx1) (cons l0 lllv) _ nil).
        simpl in *. rewrite <- Hl1. assumption. assumption. 
        assumption.

      apply (consistent_lP_lx_list_Var (cons a lP)).
Qed.





admit.
admit.
      rewrite <- rep_pred__l_consistent.
      assumption.
      
      apply is_un_predless_l_fun4_l2_lP'.
      apply is_un_predless_fun4_l2'.



      apply  consistent_lP_llv_cons_rem_gen in Hcon1. assumption.

      apply consistent_lP_lllv_cons in Hcon2. assumption.

      rewrite <- rep_pred__l_consistent.
      assumption.

      apply is_un_predless_l_fun4_l2_lP'.
      apply is_un_predless_fun4_l2'.

      apply (consistent_lP_lcond_fun4_l2_lP' (cons a lP) (cons l llx1) (cons l0 lllv) _ nil).
        simpl in *. rewrite <- Hl1. assumption. assumption. 
        assumption.

      apply (consistent_lP_lx_list_Var (cons a lP)).

      apply is_un_predless_l_fun4_l2_lP'.
      apply is_un_predless_fun4_l2'.
      
      apply (consistent_lP_lcond_fun4_l2_lP' (cons a lP) (cons l llx1) (cons l0 lllv) _ nil).
        simpl in *. rewrite <- Hl1. assumption. assumption. 
        assumption.
      apply is_un_predless_l_fun4_l2_lP'.
      apply is_un_predless_fun4_l2'.


      apply (consistent_lP_lx_list_Var (cons a lP)).

*) 

Lemma is_un_predless_P_branch_allFO : forall (alpha : SecOrder) (P : predicate),
    is_unary_predless alpha = true ->P_branch_allFO alpha P = false.
Admitted.

Lemma bound_FO_overP_P_branch_allFO : forall beta alpha x P,
  bound_FO_overP (allFO x (implSO alpha beta)) x = false ->
  P_branch_allFO beta P = false.
Proof.
  intros beta alpha [xn] P H. unfold bound_FO_overP in H.
  simpl in H.
  case_eq (is_unary_predless beta); intros Hun; rewrite Hun in *. 
    apply is_un_predless_P_branch_allFO. assumption.

    simpl in H. rewrite if_then_else_false in H.
    simpl in H. rewrite <- beq_nat_refl in H. discriminate.
Qed.

Lemma is_in_FOvar_comp_cond_lx2 : forall atm x P,
  is_in_FOvar x (list_quant_FOv_overP atm) = false ->
  P_branch_allFO atm P = true ->
  is_in_FOvar x (comp_cond_lx2 atm) = false.
Admitted.

Lemma ex_bound_FO_overP_l_app_l : forall alpha l1 l2,
  ex_bound_FO_overP_l alpha (app l1 l2) = false ->
  ex_bound_FO_overP_l alpha l1 = false.
Admitted.

Lemma ex_bound_FO_overP_l_app_r : forall alpha l1 l2,
  ex_bound_FO_overP_l alpha (app l1 l2) = false ->
  ex_bound_FO_overP_l alpha l2 = false.
Admitted.

Lemma is_un_predless_BOXATM_flag_weak_num_conn : forall m n atm y,
  n = num_conn atm ->
  Nat.leb n m = true ->
  BOXATM_flag_weak atm y = true ->
  is_unary_predless atm = false.
Proof.
  induction m; intros n atm y Hnum Hleb Hat.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
    simpl in *. destruct p. destruct f. reflexivity.

    destruct n.
    destruct atm; try discriminate.
    simpl in *. destruct p. destruct f. reflexivity.

    destruct atm; try discriminate.
    destruct atm ;try discriminate.
    destruct f as [zn].
    simpl. rewrite (IHm (num_conn atm2) atm2 (Var zn)).
    apply if_then_else_false.
      reflexivity.

      simpl in Hnum. inversion Hnum as [Hnum'].
      rewrite Hnum' in *. simpl in Hleb. destruct m.
        discriminate. apply leb_plus_take2 in Hleb.
        apply leb_suc_r. assumption.

      destruct atm1; try discriminate.
      apply BOXATM_flag_weak_allFO in Hat.
      assumption.
Qed.

Lemma is_un_predless_BOXATM_flag_weak : forall atm y,
  BOXATM_flag_weak atm y = true ->
  is_unary_predless atm = false.
Proof.
  intros until 0. apply (is_un_predless_BOXATM_flag_weak_num_conn (num_conn atm)
    (num_conn atm)). reflexivity. apply leb_refl.
Qed.

Lemma is_in_FOvar_comp_cond_lx2_2_num_conn : forall m n atm x y,
  n = num_conn atm ->
  Nat.leb n m = true ->
BOXATM_flag_weak atm y = true ->
is_in_FOvar x (list_quant_FOv_overP atm) = false ->
is_in_FOvar x (comp_cond_lx2 atm) = false.
Proof.
  induction m; intros n atm x y Hnum Hleb Hb Hin.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate. reflexivity.

    destruct n.
    destruct atm; try discriminate. reflexivity.
    destruct atm; try discriminate.
    destruct atm; try discriminate.
    destruct atm1; try discriminate; try reflexivity.
    pose proof (BOXATM_flag_weak_allFO _ _ _ _ _ Hb) as Hb2.
    pose proof (BOXATM_flag_weak_allFO _ _ _ _ _ Hb) as Hb3.
    simpl in Hin.
    destruct y as [ym]. destruct f as [z1]. destruct f0 as [z2].
    destruct f1 as [z3]. destruct x as [xn].
    apply is_un_predless_BOXATM_flag_weak in Hb2. rewrite Hb2 in *.
    simpl in Hin.
    destruct atm2; try reflexivity; try (case_eq (beq_nat xn z1); intros Hbeq;
      try reflexivity; rewrite Hbeq in *; try discriminate).
    remember (allFO f atm2) as beta.
    apply (IHm (num_conn beta) beta _ (Var z1)) in Hin.
      simpl. rewrite Heqbeta. rewrite <- Heqbeta.
      simpl. rewrite Hbeq. assumption.
      reflexivity.
simpl in Hnum. inversion Hnum. rewrite Hnum in *. simpl in Hleb.
      destruct m. discriminate. apply leb_suc_r. assumption.
      assumption.
Qed.

Lemma is_in_FOvar_comp_cond_lx2_2 : forall atm x y,
BOXATM_flag_weak atm y = true ->
is_in_FOvar x (list_quant_FOv_overP atm) = false ->
is_in_FOvar x (comp_cond_lx2 atm) = false.
Proof.
  intros atm x y. apply (is_in_FOvar_comp_cond_lx2_2_num_conn 
    (num_conn atm) (num_conn atm) atm _ _ eq_refl (leb_refl _ )).
Qed.

Lemma is_in_FOvar_bound_FO_overP_num_conn : forall m n atm P x,
  n = num_conn atm ->
  Nat.leb n m = true ->
  BAT atm = true ->
  bound_FO_overP atm x = false ->
  is_in_FOvar x (flat_map fun_id_list (calc_llv_P atm P)) = false.
Proof.
  induction m; intros n atm P x Hnum Hleb Hbat Hb.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate. reflexivity.

    destruct n. 
    destruct atm; try discriminate. reflexivity.

    destruct atm; try discriminate.
      simpl. destruct atm; try discriminate.
      pose proof (is_BOXATM_flag_strong__CONJ_BAT _ _ _ Hbat) as Hbat2.
(*       apply BOXATM_flag_weak_BAT in Hbat2. *)
      case_eq (P_branch_allFO atm2 P); intros Hbranch.
        destruct atm2; try discriminate. reflexivity.
        remember (allFO f0 atm2) as beta. simpl.
        destruct x as [xn]. destruct f as [y1].       
        case_eq (beq_nat xn y1); intros Hbeq.
          rewrite (beq_nat_true _ _ Hbeq) in Hb.
          apply bound_FO_overP_P_branch_allFO with (P := P) in Hb.
          rewrite Hb in *. discriminate.

          rewrite app_nil_r.
          destruct atm1; try discriminate.

        specialize (IHm (num_conn atm2) atm2 P (Var xn)).
        unfold bound_FO_overP in Hb. simpl in Hb.
        destruct f as [y3]. destruct f1 as [y2].
        case_eq (is_unary_predless beta); intros Hun;
          rewrite Hun in *. 
          rewrite is_un_predless_P_branch_allFO in Hbranch. discriminate. assumption.
          apply is_in_FOvar_comp_cond_lx2_2 with (y := (Var y1)); try assumption.
          simpl in Hb. rewrite Hbeq in *. assumption.


          reflexivity.

    simpl in *. rewrite flat_map_app.
    rewrite is_in_FOvar_app.
    apply bound_FO_overP_conjSO in Hb.
    destruct Hb.
    apply BAT_conjSO_t in Hbat.
    destruct Hbat.
    rewrite (IHm (num_conn atm1) atm1).
    apply (IHm (num_conn atm2) atm2).
    all : try reflexivity.
    all : try assumption.
    
    simpl in Hnum. inversion Hnum as [Hnum'].
    rewrite Hnum' in Hleb.
      apply leb_plus_take2 in Hleb. assumption.

    simpl in Hnum. inversion Hnum as [Hnum'].
    rewrite Hnum' in Hleb.
      apply leb_plus_take1 in Hleb. assumption.
Qed.

Lemma is_in_FOvar_bound_FO_overP : forall atm P x,
  BAT atm = true ->
  bound_FO_overP atm x = false ->
  is_in_FOvar x (flat_map fun_id_list (calc_llv_P atm P)) = false.
Proof.
  intros atm P x. apply (is_in_FOvar_bound_FO_overP_num_conn (num_conn atm)
    (num_conn atm) atm P x eq_refl (leb_refl _)).
Qed.

Lemma ex_bound_FO_overP_l_calc_lx1__llv : forall llx1 atm a,
BAT atm = true ->
ex_bound_FO_overP_l atm llx1 = false ->
cap_FOv llx1 (flat_map fun_id_list (calc_llv_P atm a)) = nil.
Proof.
  induction llx1; intros atm P Hb Hex. reflexivity.
  simpl in *.
  apply if_then_else_tf in Hex. destruct Hex as [Hex1 Hex2].
  apply (IHllx1 _ P Hb) in Hex2.
  rewrite Hex2. rewrite is_in_FOvar_bound_FO_overP. reflexivity.
  all : assumption.
Qed.

Lemma ex_bound_FO_overP_l_calc_llv : forall lP llx atm,
BAT atm = true ->
ex_bound_FO_overP_l atm llx = false ->
cap_FOv llx 
        (flat_map fun_id_list (flat_map fun_id_list (calc_llv_lP atm lP))) = nil.
Proof.
Admitted.

Lemma cap_FOv_nil : forall l,
  cap_FOv l nil = nil.
Proof.
  induction l.  reflexivity.
  simpl. assumption.
Qed.

Lemma ex_bound_FO_overP_l_app : forall l1 l2 atm,
  ex_bound_FO_overP_l atm (app l1 l2) =
  if ex_bound_FO_overP_l atm l1 then true else ex_bound_FO_overP_l atm l2.
Proof.
  induction l1; intros l2 atm. reflexivity.
  simpl. rewrite IHl1. case_eq (bound_FO_overP atm a); intros;
   reflexivity.
Qed.

Lemma ex_bound_FO_overP_l__l : forall llx atm,
  ex_bound_FO_overP_ll atm llx = ex_bound_FO_overP_l atm (flat_map fun_id_list llx).
Proof.
  induction llx; intros atm. reflexivity.
  simpl. rewrite IHllx. rewrite ex_bound_FO_overP_l_app.
  reflexivity.
Qed.

Lemma ex_bound_FO_overP_ll_calc_lx1__llv : forall lP llx1 atm,
BAT atm = true ->
ex_bound_FO_overP_ll atm llx1 = false ->
cap_FOv (flat_map fun_id_list llx1) 
        (flat_map fun_id_list (flat_map fun_id_list (calc_llv_lP atm lP))) = nil.
Proof.
  induction lP; intros llx1 atm Hat H.
    simpl. apply cap_FOv_nil.

    simpl. rewrite flat_map_app.
    apply cap_FOv_app_r_nil. apply conj.
      apply ex_bound_FO_overP_l_calc_lx1__llv; try assumption.
      rewrite ex_bound_FO_overP_l__l in H. assumption.

    apply IHlP; assumption.
Qed.


(* Left it here 22/12/17. *)
(* Try and make the below work. Work on the admitted "ex_att_predSO_ll" goal.
Not sure it works, but might need to add in hypotheses about atm, etc. *)

(* A new year; keep going!! *)

(* Left it here 21/12/17 *)

Lemma sSahlq_instant_aim1_fwd4 : forall lP beta rel atm y xn W Iv Ip Ir,
  REL rel = true ->
  BAT atm = true ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  attached_allFO_x beta (Var xn) = false ->
  attached_exFO_x beta (Var xn) = false ->
  closed_except beta (Var xn) ->
  x_occ_in_alpha (implSO (conjSO rel atm) (instant_cons_empty' (conjSO rel atm) beta)) y = false ->
  x_occ_in_alpha (instant_cons_empty' (conjSO rel atm) beta) (Var xn) = true ->

is_all_diff_FOv2 (flat_map (fun l : list (list FOvariable) => l) (calc_llv_lP atm lP)) = true ->
ex_bound_FO_overP_ll (conjSO rel atm) (calc_lx1_lP atm lP) = false ->
ex_FOvar_x_ll y (flat_map (fun l => l)  (new_FOvars_lll (calc_llv_lP atm lP)
  (Var (S (max_FOv (implSO (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)
      (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
        (rev_seq (S (Nat.max (max_FOv (implSO (conjSO rel atm) beta)) xn))
           (length (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) 
                  (Var xn))))))))))) = false ->


  SOturnst W Iv Ip Ir (list_closed_SO (implSO (conjSO rel atm)
              (instant_cons_empty' (conjSO rel atm) beta)) lP) ->
  SOturnst W Iv Ip Ir (replace_pred_l (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)  
      (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) beta)) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))))))
    lP (list_Var (length lP) y)      (fun4_l2_lP' (calc_lx1_lP atm lP) (list_Var (length lP) y) (new_FOvars_lll (calc_llv_lP atm lP) (Var (S(max_FOv (implSO (conjSO rel atm)
     (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)
        (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
        (rev_seq (S (Nat.max (max_FOv (implSO (conjSO rel atm) beta)) xn))
           (length
              (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta))
 (Var xn)))))) )))))).
(*   SOturnst W Iv Ip Ir (replace_pred_l (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)  
      (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) beta)) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))))))
    lP (list_Var (length lP) y)
    (fun1_l (FOv_att_P_l (conjSO rel atm) lP) y)).
 *)
Proof.
  intros lP beta rel atm y xn W Iv Ip Ir Hrel Hat Hun Hno Hat1 Hat2 Hc Hocc2 Hocc 
  Hadd1 Hadd2 Hadd3 SOt.
case_eq (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn)).
  intros Hnil. simpl.
   rewrite sSahlq_instant_aim1_fwd4_nil in Hocc; try assumption.
   discriminate. 

intros zz lzz Hlzz. rewrite <- Hlzz.

apply (sSahlq_equiv_new_simpl_try3_LP'_withextrahyp3 lP
    _ (calc_lx1_lP atm lP) y W).

simpl.
rewrite SOQFree_newnew_pre.
rewrite (SOQFree_rel rel Hrel).
rewrite (SOQFree_bxatm _ Hat). reflexivity.
apply SOQFree_instant_cons_empty'. assumption.

apply consistent_lP_llv_calc_lx1_lP.
apply consistent_lP_lllv_new_FOvars_lll.
apply consistent_lP_lllv_calc_llv_lP.

rewrite length_id_2_gen_new_FOvars_lll.
apply length_id_2_gen_calc_lx1_llv_lP.

rewrite length_id_1_gen_new_FOvars_lll.
apply length_id_1_gen_calc_lx1_llv_lP.

apply ex_bound_FO_overP_ll_implSO.
apply conj.

assumption.

apply lemma5; assumption.

assumption. 

apply ex_att_predSO_ll_new_FOvars_lll.

apply ex_FOvar_x_ll_calc_lx1_lP.
apply x_occ_in_alpha_implSO_l in Hocc2. apply x_occ_in_alpha_conjSO in Hocc2.
apply Hocc2.

apply is_all_diff_FOv3_new_FOvars_lll2.
  apply length_calc_lx1_lP_llv.
  apply length_id_2_gen_calc_lx1_llv_lP.

assumption.

simpl.
apply (leb_trans _ _ _ (max_FOv_l_calc_lx1_lP _ _)).
apply leb_max_suc3. rewrite max_comm.
apply leb_max_suc3. apply leb_refl.


      destruct (nlist_list_ex (length lP) (sSahlq_pa_l5' Ir (new_FOvars_lll (calc_llv_lP atm lP) (Var (S(max_FOv (implSO (conjSO rel atm)
     (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)
        (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
        (rev_seq (S (Nat.max (max_FOv (implSO (conjSO rel atm) beta)) xn))
           (length
              (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta))
 (Var xn)))))) )))) (map2 (Iv_ify Iv) (calc_lx1_lP atm lP)))
        ) as [l Heq].

        rewrite length_sSahlq_pa_l5'.
        rewrite length_new_FOvars_lll.
        apply length_calc_llv_lP.

        rewrite length_new_FOvars_lll.
        rewrite length_map2.
        rewrite length_calc_lx1_lP_llv. reflexivity.

    destruct (nlist_list_closed_SO' W Iv Ir 
        (implSO (conjSO rel atm) (instant_cons_empty' (conjSO rel atm) beta)) lP Ip) as [fwd rev].

    intros SOt2.
pose proof kk10.

    apply (kk10  (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
(rev_seq (S (Nat.max (max_FOv (implSO (conjSO rel atm) beta)) xn))
        (length (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))))
      (instant_cons_empty' (conjSO rel atm) beta) (Var xn)).

        apply closed_except_inst_cons_empty'. assumption.

        apply is_in_FOvar_rem_FOv_same.

rewrite max_FOv__l.
remember (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) as l'.
rewrite Hlzz. simpl length.
rewrite min_l_rev_seq.
rewrite max_FOv__l.
rewrite Heql'.
rewrite <- max_FOv_l_instant_cons_empty'.
simpl. rewrite max_FOv_l_app.
remember (max_FOv_l (FOvars_in beta)) as l2.
rewrite max_FOv_l_app.

apply leb_max_suc3.
rewrite max_comm. apply leb_max_suc3.
apply leb_refl.

apply decr_strict_rev_seq.

(* assumption.
        rewrite Heq. simpl length.
        rewrite min_l_rev_seq.
        simpl. rewrite max_FOv_instant_cons_empty'.
        apply leb_max_suc3. rewrite max_comm.
        apply leb_max_suc3. apply leb_refl.

        apply decr_strict_rev_seq.
 *)
      destruct (nlist_list_ex (length lP) (sSahlq_pa_l5' Ir (new_FOvars_lll (calc_llv_lP atm lP) (Var (S(max_FOv (implSO (conjSO rel atm)
     (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)
        (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
        (rev_seq (S (Nat.max (max_FOv (implSO (conjSO rel atm) beta)) xn))
           (length
              (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta))
 (Var xn)))))) )))) (map2 (Iv_ify Iv) (calc_lx1_lP atm lP))))
         as [l2 Heq'].

        rewrite length_sSahlq_pa_l5'.
        rewrite length_new_FOvars_lll.
        apply length_calc_llv_lP.

        rewrite length_new_FOvars_lll.
        rewrite length_map2.
        rewrite length_calc_lx1_lP_llv. reflexivity.
 
        rewrite <- Heq' in *. apply fwd;
        assumption.
Qed.

Lemma sSahlq_instant_aim1_fwd4_closer : forall lP beta rel atm y xn  W Iv Ip Ir,
  REL rel = true ->
  BAT atm = true ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  attached_allFO_x beta (Var xn) = false ->
  attached_exFO_x beta (Var xn) = false ->
  closed_except beta (Var xn) ->
  x_occ_in_alpha (instant_cons_empty' (conjSO rel atm) beta) (Var xn) = true ->
x_occ_in_alpha (implSO (conjSO rel atm) (instant_cons_empty' (conjSO rel atm) beta)) y =
false ->
is_all_diff_FOv2 (flat_map (fun l : list (list FOvariable) => l) (calc_llv_lP atm lP)) =
true ->
ex_FOvar_x_ll y (flat_map (fun l : list (list FOvariable) => l)
     (new_FOvars_lll (calc_llv_lP atm lP) (Var (S  (max_FOv
        (implSO (conjSO rel atm)
           (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)
              (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta))
                   (Var xn))
              (rev_seq (S (Nat.max (max_FOv (implSO (conjSO rel atm) beta)) xn))
                (length
              (rem_FOv
                (FOvars_in (instant_cons_empty' (conjSO rel atm) beta))
                (Var xn))))))))))) = false ->
ex_bound_FO_overP_ll (conjSO rel atm) (calc_lx1_lP atm lP) = false ->
  is_in_pred_l (preds_in (implSO (conjSO rel atm) beta)) lP = true ->
  SOturnst W Iv Ip Ir (list_closed_SO (implSO (conjSO rel atm) beta) lP) ->
  SOturnst W Iv Ip Ir (replace_pred_l (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)  
      (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) beta)) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) 
        (Var xn))))))
    lP (list_Var (length lP) y)
    (fun4_l2_lP' (calc_lx1_lP atm lP) (list_Var (length lP) y) (new_FOvars_lll (calc_llv_lP atm lP) (Var (S(max_FOv (implSO (conjSO rel atm)
     (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)
        (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
        (rev_seq (S (Nat.max (max_FOv (implSO (conjSO rel atm) beta)) xn))
           (length
              (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta))
 (Var xn)))))) )))))).
Proof.
  intros lP beta rel atm y xn  W Iv Ip Ir Hrel Hat Hun Hno Hat1 Hat2 Hc 
    Hocc Hocc2 Hall Hex1 Hex2 Hin SOt.
  apply sSahlq_instant_aim1_fwd4; try assumption.
  apply list_closed_SO_instant_cons_empty2; try assumption.
  simpl. rewrite Hno.
  rewrite SOQFree_rel.
  rewrite SOQFree_bxatm.
  reflexivity. all: assumption.
Qed.

Lemma sSahlq_instant_aim1_fwd4_closer2 : forall lx lP beta rel atm y xn W Iv Ip Ir,
  REL rel = true ->
  BAT atm = true ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  attached_allFO_x beta (Var xn) = false ->
  attached_exFO_x beta (Var xn) = false ->
  closed_except beta (Var xn) ->
  x_occ_in_alpha (instant_cons_empty' (conjSO rel atm) beta) (Var xn) = true ->
x_occ_in_alpha (implSO (conjSO rel atm) (instant_cons_empty' (conjSO rel atm) beta)) y =
false ->
is_all_diff_FOv2 (flat_map (fun l : list (list FOvariable) => l) (calc_llv_lP atm lP)) =
true ->
ex_FOvar_x_ll y (flat_map (fun l : list (list FOvariable) => l)
     (new_FOvars_lll (calc_llv_lP atm lP) (Var (S  (max_FOv
        (implSO (conjSO rel atm)
           (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)
              (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta))
                   (Var xn))
              (rev_seq (S (Nat.max (max_FOv (implSO (conjSO rel atm) beta)) xn))
                (length
              (rem_FOv
                (FOvars_in (instant_cons_empty' (conjSO rel atm) beta))
                (Var xn))))))))))) = false ->
ex_bound_FO_overP_ll (conjSO rel atm) (calc_lx1_lP atm lP) = false ->

  is_in_pred_l (preds_in (implSO (conjSO rel atm) beta)) lP = true ->
  SOturnst W Iv Ip Ir (list_closed_SO (list_closed_allFO
      (implSO (conjSO rel atm) beta) lx) lP) ->
  SOturnst W Iv Ip Ir (replace_pred_l (list_closed_allFO (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)  
      (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) beta)) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn)))))) lx)
    lP (list_Var (length lP) y)
    (fun4_l2_lP' (calc_lx1_lP atm lP) (list_Var (length lP) y) (new_FOvars_lll (calc_llv_lP atm lP) (Var (S(max_FOv (implSO (conjSO rel atm)
     (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)
        (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
        (rev_seq (S (Nat.max (max_FOv (implSO (conjSO rel atm) beta)) xn))
           (length
              (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta))
 (Var xn)))))) )))))).
Proof.
   intros lx lP beta rel atm y xn W Iv Ip Ir Hrel Hat Hun Hno Hat1 
      Hat2 Hc Hocc Hocc2 Hall Hex1 Hex2 Hin SOt. 
  rewrite rep_pred_l_list_closed_allFO.
  pose proof equiv_list_closed_allFO.
  apply (impl_list_closed_allFO _ (list_closed_SO (implSO (conjSO rel atm) beta) lP)).
    intros.
    apply sSahlq_instant_aim1_fwd4_closer.
    all : try assumption.
    apply equiv_list_closed_SO_list_closed_allFO.
    assumption.
Qed.

Lemma sSahlq_hopeful3 : forall lx lP beta alpha rel atm y xn W Iv Ip Ir,
  REL rel = true ->
  BAT atm = true ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  attached_allFO_x beta (Var xn) = false ->
  attached_exFO_x beta (Var xn) = false ->
  closed_except beta (Var xn) ->
  x_occ_in_alpha (instant_cons_empty' (conjSO rel atm) beta) (Var xn) = true ->
x_occ_in_alpha (implSO (conjSO rel atm) (instant_cons_empty' (conjSO rel atm) beta)) y =
false ->
is_all_diff_FOv2 (flat_map (fun l : list (list FOvariable) => l) (calc_llv_lP atm lP)) =
true ->
ex_FOvar_x_ll y (flat_map (fun l : list (list FOvariable) => l)
     (new_FOvars_lll (calc_llv_lP atm lP) (Var (S  (max_FOv
        (implSO (conjSO rel atm)
           (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)
              (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta))
                   (Var xn))
              (rev_seq (S (Nat.max (max_FOv (implSO (conjSO rel atm) beta)) xn))
                (length
              (rem_FOv
                (FOvars_in (instant_cons_empty' (conjSO rel atm) beta))
                (Var xn))))))))))) = false ->
ex_bound_FO_overP_ll (conjSO rel atm) (calc_lx1_lP atm lP) = false ->

  is_in_pred_l (preds_in (implSO (conjSO rel atm) beta)) lP = true ->
  (exists P, P_occurs_in_alpha alpha P = true) ->
 (forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir alpha <-> SOturnst W Iv Ip Ir (list_closed_allFO (implSO (conjSO rel atm) beta) lx)) ->
  SOturnst W Iv Ip Ir (list_closed_SO alpha lP) ->
  SOturnst W Iv Ip Ir (replace_pred_l (list_closed_allFO (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)  
      (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) beta)) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn)))))) lx)
    lP (list_Var (length lP) y)
    (fun4_l2_lP' (calc_lx1_lP atm lP) (list_Var (length lP) y) (new_FOvars_lll (calc_llv_lP atm lP) (Var (S(max_FOv (implSO (conjSO rel atm)
     (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)
        (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
        (rev_seq (S (Nat.max (max_FOv (implSO (conjSO rel atm) beta)) xn))
           (length
              (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta))
 (Var xn)))))) )))))).
Proof.
   intros lx lP beta alpha rel atm y xn W Iv Ip Ir HREL HAT Hun Hno Hat1 Hat2
    Hc Hocc Hocc2 Hall Hex1 Hex2 Hin Hpocc Hequiv SOt.
  apply sSahlq_instant_aim1_fwd4_closer2; try assumption.
  pose proof (equiv_list_closed_SO lP  _ _ Hequiv) as H.
  apply H.
  assumption.
Qed.

Lemma sSahlq_hopeful3_atm : forall lx lP beta alpha atm y xn W Iv Ip Ir,
  BAT atm = true ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  attached_allFO_x beta (Var xn) = false ->
  attached_exFO_x beta (Var xn) = false ->
  closed_except beta (Var xn) ->
  x_occ_in_alpha (instant_cons_empty' atm beta) (Var xn) = true ->
  is_in_pred_l (preds_in (implSO atm beta)) lP = true ->
  (exists P, P_occurs_in_alpha alpha P = true) ->
 (forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir alpha <-> SOturnst W Iv Ip Ir (list_closed_allFO (implSO atm beta) lx)) ->
  SOturnst W Iv Ip Ir (list_closed_SO alpha lP) ->
  SOturnst W Iv Ip Ir (replace_pred_l (list_closed_allFO (implSO
    atm
    (newnew_pre (instant_cons_empty' atm beta)  
      (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn))
      (rev_seq (S (max (max_FOv (implSO atm beta)) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn)))))) lx)
    lP (list_Var (length lP) y)
    (calc_lP atm lP)).
Proof.
Admitted.
(*   intros lx lP beta alpha atm y xn W Iv Ip Ir HAT Hun Hno Hat1 Hat2
    Hc Hocc Hin Hpocc Hequiv SOt.
  apply vsSahlq_instant_aim1_fwd4_closer2_atm; try assumption.
  pose proof (equiv_list_closed_SO lP  _ _ Hequiv) as H.
  apply H.
  assumption.
Qed.
 *)

Lemma FAKE : forall atm,
is_in_FOvar (Var 0) (FOvars_in atm) = false.
Admitted.

Lemma max_lem_cant_find : forall n m,
  S (max n m) = max (S n) (S m).
Proof.
  induction n; intros m. reflexivity.
  simpl. destruct m; reflexivity.
Qed.

Lemma is_in_FOvar_S_max_FOv_l : forall l,
is_in_FOvar (Var (S (max_FOv_l l))) l = false.
Proof.
  induction l. reflexivity.
  simpl. destruct a as [ym]. destruct ym.
    simpl. assumption.

    simpl. case_eq (max_FOv_l l).
      intros H. rewrite one_suc. rewrite beq_nat_suc_false.
      induction l. reflexivity.
      destruct a as [zn]. destruct zn. 
      simpl. apply IHl0. simpl in IHl. assumption.
      simpl in H. assumption.

      simpl in H. destruct (max_FOv_l l); discriminate.

      intros m Hm.       rewrite max_lem_cant_find.
      rewrite beq_nat_max_S. rewrite Hm in IHl.
      rewrite max_lem_cant_find.
      destruct (max_or (S (S ym)) (S (S m))) as [H | H];
        rewrite H. 2 : assumption.
      case_eq (beq_nat (S (S ym)) (S (S m))); intros Hbeq.
        rewrite (beq_nat_true _ _ Hbeq) in *.
        assumption.

        apply lem12. simpl.
        rewrite Hm. simpl.  
        apply max_leb_r in H. assumption.
Qed.

Lemma x_occ_in_alpha_new_FOv_pp_pre2 : forall alpha,
  x_occ_in_alpha alpha (Var (new_FOv_pp_pre2 alpha)) = false.
Proof.
  intros alpha.
  rewrite x_occ_in_alpha_is_in_FOvar.
  unfold new_FOv_pp_pre2.
  rewrite max_FOv__l.
  apply is_in_FOvar_S_max_FOv_l.
Qed.

Lemma length_rename_FOv_list : forall lv x y,
  length (rename_FOv_list lv x y) = length lv.
Proof.
  induction lv; intros [xn] [ym]. reflexivity.
  simpl. destruct a as [zn].
  case_eq (beq_nat xn zn);
    simpl; rewrite IHlv; reflexivity.
Qed.

Fixpoint replace_FOv_l (alpha : SecOrder) (l1 l2 : list FOvariable)
                        : SecOrder :=
  match l1, l2 with
  | cons x1 l1', cons x2 l2' => replace_FOv (replace_FOv_l alpha l1' l2') x1 x2
  | _, _ => alpha
  end.

Lemma rep__ren_FOv : forall alpha x y,
  replace_FOv alpha x y = rename_FOv alpha x y.
Proof.
  induction alpha; intros [xn] [ym]; try reflexivity.
    simpl. destruct p. destruct f. reflexivity.

    simpl. destruct f. rewrite IHalpha. 
    rewrite beq_nat_comm. reflexivity.

    simpl. destruct f. rewrite IHalpha. 
    rewrite beq_nat_comm. reflexivity.

    simpl. rewrite IHalpha. reflexivity.

    simpl. rewrite IHalpha1. rewrite IHalpha2. reflexivity.
    simpl. rewrite IHalpha1. rewrite IHalpha2. reflexivity.
    simpl. rewrite IHalpha1. rewrite IHalpha2. reflexivity.

    simpl in *. destruct p. rewrite IHalpha. reflexivity.

    simpl in *. destruct p. rewrite IHalpha. reflexivity.
Qed.

Lemma rep_FOv__l_ex  : forall l1 l2 atm x y,
  exists l1' l2',
  replace_FOv_l (replace_FOv atm x y) l1 l2 =
  replace_FOv_l atm l1' l2'.
Proof.
  induction l1; intros l2 atm [xn] [ym].      
    simpl. exists (cons (Var xn) nil). exists (cons (Var ym) nil).
    reflexivity.

    simpl. destruct l2.
    simpl. exists (cons (Var xn) nil). exists (cons (Var ym) nil).
    reflexivity.

    destruct (IHl1 l2 atm (Var xn) (Var ym)) as [l1' [l2' H]].
    rewrite H. 
    exists (cons a l1'). exists (cons f l2').
    reflexivity.
Qed.

Lemma rename_FOv_A_pre__list : forall n lv rel atm beta rel' atm',
  rename_FOv_A_pre (conjSO rel atm) beta lv n = conjSO rel' atm' ->
  exists l1 l2,
  atm' = replace_FOv_l atm l1 l2.
Proof.
  induction n; intros until 0; intros H.
    simpl in *. exists nil. exists nil.  simpl. inversion H. reflexivity.

    simpl in *. destruct lv.
    simpl in *. exists nil. exists nil.  simpl. inversion H. reflexivity.

   unfold rename_FOv_max_conj in H. destruct f as [zn].
   simpl in H.
  pose proof (strip_exFO_rename_FOv lv
       ((conjSO rel atm))  (Var zn)
    (Var (            (S
               (Nat.max (max_FOv beta)
                  (Nat.max zn (max_FOv (list_closed_exFO (conjSO rel atm) lv)))))))) as H2.
   unfold rename_FOv in H2. rewrite H2 in H. clear H2.
    simpl in H.
    apply IHn in H.
    destruct H as [l1 [l2 H]].
    destruct (rep_FOv__l_ex l1 l2 atm (Var zn)
      (Var (S
            (Nat.max (max_FOv beta)
               (Nat.max zn (max_FOv (list_closed_exFO (conjSO rel atm) lv)))))))
      as [l1' [l2' H2]]. rewrite rep__ren_FOv in H2. simpl in H2.
    rewrite H2 in H.
    exists l1'. exists l2'. assumption.
Qed.

(* Parameter x f : FOvariable.
Parameter alpha : SecOrder.
Parameter P p : predicate.
Eval compute in (calc_llv_P (allFO x alpha) P).
Eval compute in (calc_llv_P (allFO x (predSO p f)) P). *)

Lemma calc_llv_P_allFO_gen : forall alpha x P,
  calc_llv_P (allFO x alpha) P =
  if P_branch_allFO (allFO x alpha) P then cons (comp_cond_lx2 (allFO x alpha)) nil
      else nil.
Proof.
  intros. simpl.
  destruct alpha; try reflexivity.
Qed.

Lemma P_branch_allFO_exchange : forall alpha x y P,
  P_branch_allFO (allFO x alpha) P =
  P_branch_allFO (allFO y alpha) P.
Proof.
  intros alpha x y P.
  simpl. destruct alpha; reflexivity.
Qed.

Lemma rename_FOv_predSO_or : forall P x y z,
  rename_FOv (predSO P x) y z = predSO P x \/
  rename_FOv (predSO P x) y z = predSO P z.
Proof.
  intros [Pn] [xn] [ym] [zn].
  simpl. case_eq (beq_nat ym xn); intros Hbeq;
    [right | left]; reflexivity.
Qed.

Lemma rename_FOv_relatSO : forall x1 x2 y z,
  exists y1 y2,
  rename_FOv (relatSO x1 x2) y z = relatSO y1 y2.
Proof.
  intros [x1] [x2] [ym] [zn].
  simpl. case_eq (beq_nat ym x1); intros Hbeq;
    [exists (Var zn) | exists (Var x1)];
  
    (case_eq (beq_nat ym x2);
      intros Hbeq2; [exists (Var zn) | exists (Var x2)]);
      reflexivity.
Qed.

Lemma rename_FOv_eqFO : forall x1 x2 y z,
  exists y1 y2,
  rename_FOv (eqFO x1 x2) y z = eqFO y1 y2.
Proof.
  intros [x1] [x2] [ym] [zn].
  simpl. case_eq (beq_nat ym x1); intros Hbeq;
    [exists (Var zn) | exists (Var x1)];
  
    (case_eq (beq_nat ym x2);
      intros Hbeq2; [exists (Var zn) | exists (Var x2)]);
      reflexivity.
Qed.


Lemma rename_FOv_allFO_or : forall alpha x y z,
  rename_FOv (allFO x alpha) y z = allFO x (rename_FOv alpha y z) \/
  rename_FOv (allFO x alpha) y z = allFO z (rename_FOv alpha y z).
Proof.
  intros alpha [xn] [ym] [zn].
  simpl. case_eq (beq_nat xn ym); intros Hbeq;
    [right | left]; reflexivity.
Qed.


Lemma rename_FOv_exFO_or : forall alpha x y z,
  rename_FOv (exFO x alpha) y z = exFO x (rename_FOv alpha y z) \/
  rename_FOv (exFO x alpha) y z = exFO z (rename_FOv alpha y z).
Proof.
  intros alpha [xn] [ym] [zn].
  simpl. case_eq (beq_nat xn ym); intros Hbeq;
    [right | left]; reflexivity.
Qed.

Lemma P_branch_allFO_rename_FOv_num_conn : forall m n alpha P y z,
  n = num_conn alpha ->
  Nat.leb n m = true ->
  P_branch_allFO  (rename_FOv alpha y z) P =
  P_branch_allFO alpha P.
Proof.
  induction m; intros n alpha [Pn] [xn] [ym] Hnum Hleb.
    destruct n. 2 : discriminate. 
    destruct alpha; try reflexivity; try discriminate.
    simpl. destruct f as [zn]. destruct p as [Qm].
    case_eq (beq_nat xn zn); intros Hbeq; reflexivity.

    destruct f as [z1]; destruct f0 as [z2].
    simpl. case_eq (beq_nat xn z1); intros Hbeq; 
      case_eq (beq_nat xn z2); intros Hbeq2;
      reflexivity.

    destruct f as [z1]; destruct f0 as [z2].
    simpl. case_eq (beq_nat xn z1); intros Hbeq; 
      case_eq (beq_nat xn z2); intros Hbeq2;
      reflexivity.

    destruct n.
      destruct alpha; try reflexivity.
    simpl. destruct f as [zn]. destruct p as [Qm].
    case_eq (beq_nat xn zn); intros Hbeq; reflexivity.

    destruct f as [z1]; destruct f0 as [z2].
    simpl. case_eq (beq_nat xn z1); intros Hbeq; 
      case_eq (beq_nat xn z2); intros Hbeq2;
      reflexivity.

    destruct f as [z1]; destruct f0 as [z2].
    simpl. case_eq (beq_nat xn z1); intros Hbeq; 
      case_eq (beq_nat xn z2); intros Hbeq2;
      reflexivity.

    simpl. destruct f as [zn]. case_eq (beq_nat zn xn);
      intros Hbeq. simpl.
      destruct alpha; try reflexivity.
        destruct (rename_FOv_predSO_or p f (Var xn) (Var ym)) as [H | H];
          unfold rename_FOv in H; rewrite H; reflexivity.

        destruct (rename_FOv_relatSO f f0 (Var xn) (Var ym)) as [y1 [y2 H]];
          unfold rename_FOv in H; rewrite H; reflexivity.

        destruct (rename_FOv_eqFO f f0 (Var xn) (Var ym)) as [y1 [y2 H]];
          unfold rename_FOv in H; rewrite H; reflexivity.

        destruct (rename_FOv_allFO_or alpha f (Var xn) (Var ym)) as [H | H];
          unfold rename_FOv in H; rewrite H; reflexivity.

        destruct (rename_FOv_exFO_or alpha f (Var xn) (Var ym)) as [H | H];
          unfold rename_FOv in H; rewrite H; reflexivity.

simpl. apply (IHm (num_conn alpha2) alpha2 (Pred Pn) (Var xn) (Var ym)).
   reflexivity. 

    simpl in Hnum.
        rewrite Hnum in Hleb. simpl in Hleb. destruct m. discriminate.
        apply leb_plus_take2 in Hleb. apply leb_suc_r. assumption.

      simpl.
      destruct alpha; try reflexivity.
        destruct (rename_FOv_predSO_or p f (Var xn) (Var ym)) as [H | H];
          unfold rename_FOv in H; rewrite H; reflexivity.

        destruct (rename_FOv_relatSO f f0 (Var xn) (Var ym)) as [y1 [y2 H]];
          unfold rename_FOv in H; rewrite H; reflexivity.

        destruct (rename_FOv_eqFO f f0 (Var xn) (Var ym)) as [y1 [y2 H]];
          unfold rename_FOv in H; rewrite H; reflexivity.

        destruct (rename_FOv_allFO_or alpha f (Var xn) (Var ym)) as [H | H];
          unfold rename_FOv in H; rewrite H; reflexivity.

        destruct (rename_FOv_exFO_or alpha f (Var xn) (Var ym)) as [H | H];
          unfold rename_FOv in H; rewrite H; reflexivity.

simpl. apply (IHm (num_conn alpha2) alpha2 (Pred Pn) (Var xn) (Var ym)).
   reflexivity. 

    simpl in Hnum.
        rewrite Hnum in Hleb. simpl in Hleb. destruct m. discriminate.
        apply leb_plus_take2 in Hleb. apply leb_suc_r. assumption.

      simpl. destruct f as [zn].
      case_eq (beq_nat zn xn); intros Hbeq; reflexivity.


      destruct alpha; try discriminate; try reflexivity.

        simpl.
        destruct f as [zn]. case_eq (beq_nat zn xn); intros Hbeq.

      destruct alpha; try reflexivity.
        destruct (rename_FOv_predSO_or p f (Var xn) (Var ym)) as [H | H];
          unfold rename_FOv in H; rewrite H; reflexivity.

        destruct (rename_FOv_relatSO f f0 (Var xn) (Var ym)) as [y1 [y2 H]];
          unfold rename_FOv in H; rewrite H; reflexivity.

        destruct (rename_FOv_eqFO f f0 (Var xn) (Var ym)) as [y1 [y2 H]];
          unfold rename_FOv in H; rewrite H; reflexivity.

        destruct (rename_FOv_allFO_or alpha f (Var xn) (Var ym)) as [H | H];
          unfold rename_FOv in H; rewrite H; reflexivity.

        destruct (rename_FOv_exFO_or alpha f (Var xn) (Var ym)) as [H | H];
          unfold rename_FOv in H; rewrite H; reflexivity.

simpl. apply (IHm (num_conn alpha2) alpha2 (Pred Pn) (Var xn) (Var ym)).
   reflexivity. 

    simpl in Hnum.
        rewrite Hnum in Hleb. simpl in Hleb. destruct m. discriminate.
        apply leb_plus_take2 in Hleb. apply leb_suc_r. assumption.

      destruct alpha; try reflexivity.
        destruct (rename_FOv_predSO_or p f (Var xn) (Var ym)) as [H | H];
          unfold rename_FOv in H; rewrite H; reflexivity.

        destruct (rename_FOv_relatSO f f0 (Var xn) (Var ym)) as [y1 [y2 H]];
          unfold rename_FOv in H; rewrite H; reflexivity.

        destruct (rename_FOv_eqFO f f0 (Var xn) (Var ym)) as [y1 [y2 H]];
          unfold rename_FOv in H; rewrite H; reflexivity.

        destruct (rename_FOv_allFO_or alpha f (Var xn) (Var ym)) as [H | H];
          unfold rename_FOv in H; rewrite H; reflexivity.

        destruct (rename_FOv_exFO_or alpha f (Var xn) (Var ym)) as [H | H];
          unfold rename_FOv in H; rewrite H; reflexivity.

simpl. apply (IHm (num_conn alpha2) alpha2 (Pred Pn) (Var xn) (Var ym)).
   reflexivity. 

    simpl in Hnum.
        rewrite Hnum in Hleb. simpl in Hleb. destruct m. discriminate.
        apply leb_plus_take2 in Hleb. apply leb_suc_r. assumption.

        destruct f as [zn]. simpl. case_eq (beq_nat zn xn); intros Hbeq;
          reflexivity.
Qed.

Lemma P_branch_allFO_rename_FOv : forall alpha P y z,
  P_branch_allFO  (rename_FOv alpha y z) P =
  P_branch_allFO alpha P.
Proof.
  intros until 0. apply (P_branch_allFO_rename_FOv_num_conn (num_conn alpha) (num_conn alpha)).
  reflexivity. apply leb_refl.
Qed.

Lemma P_branch_allFO_rename_FOv_allFO : forall alpha P x y z,
  P_branch_allFO (allFO x (rename_FOv alpha y z)) P =
  P_branch_allFO (allFO x alpha) P.
Proof.
  induction alpha; intros [Pn] [xn] [ym] [zn]; try reflexivity.
    simpl. destruct f as [un].
    case_eq (beq_nat ym un); intros Hbeq; reflexivity.

    simpl. destruct f as [u1]; destruct f0 as [u2].
    case_eq (beq_nat ym u1); intros Hbeq;
      case_eq (beq_nat ym u2); intros Hbeq2; reflexivity.

    simpl. destruct f as [u1]; destruct f0 as [u2].
    case_eq (beq_nat ym u1); intros Hbeq;
      case_eq (beq_nat ym u2); intros Hbeq2; reflexivity.

    simpl. destruct f as [u1].
    case_eq (beq_nat u1 ym); intros Hbeq; reflexivity.

    simpl. destruct f as [u1].
    case_eq (beq_nat u1 ym); intros Hbeq; reflexivity.

    simpl. pose proof P_branch_allFO_rename_FOv as H.
    unfold rename_FOv in H. apply (H _ _ (Var ym) (Var zn)).
Qed.

(* Left it here 8/1/18 *)

Lemma is_all_diff_FOv2_calc_llv_P_rename_FOv : forall atm x y P,
  is_all_diff_FOv2 (calc_llv_P atm P) = true ->
  is_all_diff_FOv2 (calc_llv_P (rename_FOv atm x y) P) = true.
Proof.
  induction atm; intros [xn] [ym] P H.
    destruct p. destruct f as [zn].
    simpl in *. case_eq (beq_nat xn zn); intros Hbeq; reflexivity.

    destruct f as [z1]; destruct f0 as [z2]. simpl.
    case_eq (beq_nat xn z1); intros Hbeq; 
      case_eq (beq_nat xn z2); intros Hbeq2; reflexivity.

    destruct f as [z1]; destruct f0 as [z2]. simpl.
    case_eq (beq_nat xn z1); intros Hbeq; 
      case_eq (beq_nat xn z2); intros Hbeq2; reflexivity.

    destruct f as [z1].
    simpl rename_FOv. case_eq (beq_nat z1 xn);
      intros Hbeq. rewrite calc_llv_P_allFO_gen in *.
      rewrite (P_branch_allFO_exchange _ _ (Var z1)).
      pose proof P_branch_allFO_rename_FOv_allFO as H2.
        unfold rename_FOv in H2.
        rewrite (H2 _ _ (Var z1) (Var xn) (Var ym)).
      case_eq (P_branch_allFO (allFO (Var z1) atm) P);
        intros Hp; rewrite Hp in *. 2 : reflexivity.
Admitted.

Lemma is_all_diff_FOv2_calc_llv_P_replace_FOv_l : forall lx ly atm P,
  is_all_diff_FOv2 (calc_llv_P atm P) = true ->
  is_all_diff_FOv2 (calc_llv_P (replace_FOv_l atm lx ly) P) = true.
Admitted.

Lemma rename_FOv_A_is_all_diff_FOv2 : forall n lv P beta rel atm rel' atm',
  REL rel = true ->
  BAT atm = true ->
  REL rel' = true ->
  BAT atm' = true ->
  rename_FOv_A_pre (conjSO rel atm) beta lv n = conjSO rel' atm' ->
is_all_diff_FOv2 (calc_llv_P atm P) = true ->
is_all_diff_FOv2 (calc_llv_P atm' P) = true.
Proof.
  induction n; intros lv P beta rel atm rel' atm' Hrel1 Hbat1 Hrel2 Hbat2 Hren Hall.
    simpl in *.
admit.

    simpl in *. destruct lv. 
admit.
    unfold rename_FOv_max_conj in Hren.
    simpl in *. destruct f as [zn].
    rewrite strip_exFO_rename_FOv in Hren.

destruct (rename_FOv_A_pre__list _ _ _ _ _ _ _ Hren) as [l1 [l2 H]].
  rewrite H. apply is_all_diff_FOv2_calc_llv_P_replace_FOv_l.
pose proof is_all_diff_FOv2_calc_llv_P_rename_FOv as H2.
  unfold rename_FOv in H2. apply (H2 _ (Var zn)
    (Var ((S
           (Nat.max (max_FOv beta)
              (Nat.max zn (max_FOv (list_closed_exFO (conjSO rel atm) lv)))))))).
    assumption.
Admitted.

(* 
  is_all_diff_FOv2 (flat_map fun_id_list (calc_llv_P
    (replace_FOv_l (rename_FOv atm x y) lx ly))).
    
Search replace_FOv_l.



  unfold rename_FOv_A.


  induction m; intros n lv P beta rel atm rel' atm' Hlength Hleb
    Hrel1 Hbat1 Hrel2 Hbat2 Hren Hall.
    destruct n. 2 : discriminate. destruct lv. 2 : discriminate.
    unfold rename_FOv_A in *. 
    simpl in *. inversion Hren as [[H1 H2]]. rewrite H2 in *. assumption.

    destruct n. destruct lv. 2 : discriminate.
    unfold rename_FOv_A in *. 
    simpl in *. inversion Hren as [[H1 H2]]. rewrite H2 in *. assumption.

    destruct lv. discriminate.
    unfold rename_FOv_A in *. simpl in *.
    unfold rename_FOv_max_conj in Hren.
    rewrite strip_exFO_rename_FOv in Hren.
    rewrite strip_exFO_list_rename_FOv in Hren.
    rewrite rename_FOv_conjSO in Hren.

assert (length lv = length (rename_FOv_list lv f
            (Var (S (max_FOv (conjSO beta
         (exFO f (list_closed_exFO (conjSO rel atm) lv)))))))) as Hass.
  rewrite length_rename_FOv_list. reflexivity.

  rewrite Hass in Hren.

    pose proof (IHm (length lv) _ P beta _ _ _ _ _ _ _ _ _ _ Hren).



  induction lv; intros until 0; intros Hrel1 Hbat1 Hrel2 Hbat2 Hren Hall.
    unfold rename_FOv_A in *. 
    simpl in *. inversion Hren as [[H1 H2]]. rewrite H2 in *. assumption.

    unfold rename_FOv_A in *. simpl in *.
    unfold rename_FOv_max_conj in Hren.
    rewrite strip_exFO_rename_FOv in Hren.
    rewrite strip_exFO_list_rename_FOv in Hren.
    rewrite rename_FOv_conjSO in Hren.

assert (length lv = length (rename_FOv_list lv a
            (Var (S (max_FOv (conjSO beta
         (exFO a (list_closed_exFO (conjSO rel atm) lv)))))))) as Hass.
  rewrite length_rename_FOv_list. reflexivity.

  rewrite Hass in Hren.

    pose proof (IHlv P beta _ _ _ _ _ _ _ _ Hren).

 *)

Lemma is_all_diff_FOv2_calc_llv_lP__P : forall atm,
  (forall lP, 
    is_all_diff_FOv2 (flat_map fun_id_list (calc_llv_lP atm lP)) = true) ->
  forall P,
    is_all_diff_FOv2 (calc_llv_P atm P) = true.
Proof.
  intros atm H P.
  specialize (H (cons P nil)). simpl in *. rewrite app_nil_r in H.
  unfold fun_id_list in *. assumption.
Qed.

Lemma rename_FOv_A_conjSO_predSO : forall lv alpha rel p f,
  REL rel = true ->
  exists rel' f',
  rename_FOv_A (conjSO rel (predSO p f)) alpha lv = conjSO rel' (predSO p f') /\
    REL rel' = true.
Admitted.

Lemma rep_FOv_l_strip_exFO : forall l1 l2 lv f alpha beta,
exists l0 l3 : list FOvariable,
  replace_FOv_l (strip_exFO (rename_FOv_max_conj (list_closed_exFO alpha lv) beta f) (length lv)) l1 l2 =
  replace_FOv_l alpha l0 l3.
Proof.
  induction l1; intros l2 lv f alpha beta. simpl.
    unfold rename_FOv_max_conj.
    rewrite strip_exFO_rename_FOv.
    exists (cons f nil). exists (cons (Var (S (max_FOv (conjSO beta (exFO f (list_closed_exFO alpha lv)))))) nil).
    simpl. rewrite rep__ren_FOv. reflexivity.

    simpl. destruct l2.
    unfold rename_FOv_max_conj.
    rewrite strip_exFO_rename_FOv.
    exists (cons f nil). exists (cons (Var (S (max_FOv (conjSO beta (exFO f (list_closed_exFO alpha lv)))))) nil).
    simpl. rewrite rep__ren_FOv. reflexivity.

    destruct (IHl1 l2 lv f alpha beta) as [l3 [l4 H]].
    rewrite H.
    exists (cons a l3). exists (cons f0 l4). reflexivity.
Qed.

Fixpoint seq_FOv (x0 : FOvariable) (n : nat) : list FOvariable :=
  match n with  
  | 0 => nil
  | S m => cons x0 (seq_FOv (next_FOvar x0) m)
  end.


Fixpoint rev_seq_FOv (x0 : FOvariable) (n : nat) : list FOvariable :=
  match n with  
  | 0 => nil
  | S m => cons (Var (plus (match x0 with Var xn => xn end) m)) (rev_seq_FOv x0 m)
  end.

Lemma rep_FOv__l_switch : forall l1 l2 x y alpha,
  is_in_FOvar x l1 = false ->
  is_in_FOvar x l2 = false ->
  replace_FOv_l (replace_FOv alpha x y) l1 l2 = replace_FOv (replace_FOv_l alpha l1 l2) x y.
Admitted.

Fixpoint decr_strict_FOv lx : bool :=
  match lx with
  | nil => true 
  | cons x nil => true
  | cons x lx' => if Nat.leb (S(max_FOv_l lx')) (match x with Var xn => xn end) 
      then decr_strict_FOv lx' else false
  end.

Lemma decr_strict_FOv_defn : forall lx xn,
 ~ lx = nil ->
  decr_strict_FOv (cons (Var xn) lx) = if Nat.leb (S (max_FOv_l lx)) xn
    then decr_strict_FOv lx else false.
Proof.
  intros lx xn Hnil. destruct lx. contradiction (Hnil eq_refl).
  reflexivity.
Qed.

Fixpoint min_FOv_l (l : list FOvariable) : nat :=
  match l with
  | nil => 0
  | cons (Var ym) nil => ym
  | cons (Var ym) l' => min ym (min_FOv_l l')
  end.

Lemma rep_FOv__l_end : forall l1 l2 alpha x y,
  length l1 = length l2 ->
  replace_FOv_l (replace_FOv alpha x y) l1 l2 =
  replace_FOv_l alpha (app l1 (cons x nil)) (app l2 (cons y nil)).
Proof.
  induction l1; intros l2 alpha x y Hl. destruct l2. reflexivity. discriminate.
  destruct l2. discriminate.
  simpl in *. rewrite IHl1. reflexivity. inversion Hl. reflexivity.
Qed. 

Lemma min_FOv_l_app : forall l1 l2,
  ~ l1 = nil ->
  ~ l2 = nil ->
  min_FOv_l (app l1 l2) = min (min_FOv_l l1) (min_FOv_l l2).
Proof.
  induction l1; intros l2 Hl1 Hl2.
    contradiction (Hl1 eq_refl).
  
    simpl in *. destruct a as [ym].
    destruct l2. contradiction (Hl2 eq_refl).
    destruct l1. simpl. reflexivity.
    simpl in *. rewrite IHl1. destruct f0. destruct f. destruct l2. simpl.
      rewrite PeanoNat.Nat.min_assoc.
      reflexivity.

      simpl. rewrite PeanoNat.Nat.min_assoc. reflexivity.

      discriminate.

      discriminate.
Qed.

Lemma lemma_max_rand : forall m t alpha zn,
PeanoNat.Nat.leb (Nat.max (max_FOv alpha) m )
  (Nat.max
     (max_FOv
        (rename_FOv_n alpha zn (S (Nat.max m (Nat.max zn (Nat.max (max_FOv alpha) (max_FOv_l t)))))))
     m) = true.
Proof.
  intros m t alpha zn.
  apply leb_max_max.
  pose proof (aa18 alpha (Var zn) (S (Nat.max m (Nat.max zn (Nat.max (max_FOv alpha) (max_FOv_l t)))))) as HH.
  simpl in HH.
  assert (Nat.leb (max_FOv alpha) (Nat.max m (Nat.max zn (Nat.max (max_FOv alpha) (max_FOv_l t)))) = true) as Hass.
    rewrite max_comm. apply leb_max_suc3.
    rewrite max_comm. apply leb_max_suc3.
    apply leb_max_suc3. apply leb_refl.
  specialize (HH Hass).
  destruct HH as [H1 H2].
  case_eq (x_occ_in_alpha alpha (Var zn)); intros Hocc.
    rewrite H1. apply leb_suc_r.
    rewrite max_comm. apply leb_max_suc3.
    rewrite max_comm. apply leb_max_suc3.
    apply leb_max_suc3. apply leb_refl.
    assumption.
  
    rewrite H2. apply leb_refl. assumption.
Qed.

Lemma lemma_max_rand2 : forall alpha beta t zn,
Nat.leb (Nat.max (max_FOv alpha) (max_FOv beta))
  (Nat.max (max_FOv beta) (Nat.max zn (max_FOv (list_closed_exFO alpha t)))) = true.
Proof.
  intros alpha beta t zn.
  rewrite max_FOv_list_closed_exFO.
  rewrite (max_comm (max_FOv beta)).
  apply leb_max_max. rewrite max_comm.
  do 2 apply leb_max_suc3. apply leb_refl.
Qed.

Lemma rename_FOv_A_rep_FOv_l_num_conn : forall n lv alpha beta,
  length lv = n ->
  is_in_FOvar (Var 0) lv = false ->
  ~ lv = nil ->
  exists l1 l2,
  rename_FOv_A alpha beta lv = replace_FOv_l alpha l1 l2 /\
  length l1 = length l2 /\
  Nat.leb  (S(max_FOv (conjSO alpha beta))) (min_FOv_l l2) = true.
Proof.
  unfold rename_FOv_A.
  induction n; intros lv alpha beta Hl Hin Hnot.
    destruct lv. contradiction (Hnot eq_refl). discriminate.
    destruct lv. discriminate.
    destruct lv. simpl in *.
    destruct f as [xn]. destruct xn. discriminate.
    rewrite strip_exFO_0.
    unfold rename_FOv_max_conj.
    exists (cons (Var (S xn)) nil).
    exists (cons (Var (S (max_FOv (conjSO beta (exFO (Var (S xn)) alpha)))) )nil).
    apply conj. simpl. rewrite rep__ren_FOv. reflexivity.
    apply conj. reflexivity.
      simpl.
      case_eq (max_FOv alpha). intros Hnil. simpl.
        apply leb_max_suc3. apply leb_refl.

        intros m Hm. rewrite (max_comm (max_FOv beta)).
        apply leb_max_max. simpl. rewrite max_comm. apply leb_max_suc3.
        apply leb_refl. 

    remember (cons f0 lv) as t.
    simpl. unfold rename_FOv_max_conj.
    rewrite strip_exFO_rename_FOv.
    destruct (IHn (strip_exFO_list
       (rename_FOv (list_closed_exFO alpha t) f
          (Var (S (max_FOv (conjSO beta (exFO f (list_closed_exFO alpha t))))))) (length t))
      (rename_FOv alpha f (Var (S (max_FOv (conjSO beta (exFO f (list_closed_exFO alpha t)))))))
      beta) as [l1 [l2 [H1 H2]]].
      rewrite strip_exFO_list_rename_FOv.
      rewrite length_rename_FOv_list. simpl in Hl. inversion Hl.
      reflexivity.
 simpl.
pose proof is_in_FOvar_strip_exFO_list as HH.
  unfold rename_FOv_max_conj in HH. simpl in HH. apply HH.
    simpl in Hin. destruct f as [ym]. destruct ym. discriminate.
    assumption.
    simpl in Hin. destruct f as [ym]. destruct ym; discriminate.

    rewrite strip_exFO_list_rename_FOv.
    rewrite Heqt. simpl. destruct f as [x1]. destruct f0 as [x2].
    case_eq (beq_nat x1 x2); discriminate.

    rewrite strip_exFO_list_rename_FOv in H1.
    rewrite length_rename_FOv_list in H1.
    rewrite strip_exFO_list_rename_FOv. rewrite H1.
    rewrite <- rep__ren_FOv.
    exists (app l1 (cons f nil)).
    exists (app l2 (cons (Var (S (max_FOv (conjSO beta (exFO f (list_closed_exFO alpha t)))))) nil)).
    destruct H2 as [H2 H3].
    rewrite rep_FOv__l_end. apply conj. reflexivity.
    apply conj.
      simpl. do 2 rewrite app_length.
      rewrite H2. simpl. reflexivity.

      rewrite min_FOv_l_app.
      simpl min_FOv_l. destruct f as [zn].
      destruct (min_or (min_FOv_l l2)
          (S (Nat.max (max_FOv beta) (Nat.max zn (max_FOv (list_closed_exFO alpha t)))))) as [Hmin | Hmin];
        rewrite Hmin. case_eq (min_FOv_l l2).
          intros HH. rewrite HH in *. simpl in *.
          discriminate.

          intros mm HH. rewrite HH in H3.
          simpl in H3.
          apply (leb_trans (max (max_FOv alpha) (max_FOv beta))
            (Nat.max
          (max_FOv
             (rename_FOv_n alpha zn (S (Nat.max (max_FOv beta) (Nat.max zn (max_FOv (list_closed_exFO alpha t)))))))
          (max_FOv beta)) mm).
rewrite max_FOv_list_closed_exFO.
apply lemma_max_rand.

          assumption.
apply lemma_max_rand2.

destruct l2; discriminate.
discriminate.
assumption.
Qed.

Lemma cap_FOv_cons_nil : forall l1 x,
  cap_FOv l1 (cons x nil) = nil ->
  is_in_FOvar x l1 = false.
Proof.
  induction l1; intros [xn] H. reflexivity.
  simpl in *. destruct a as [ym].
  rewrite beq_nat_comm.
  case_eq (beq_nat ym xn); intros Hbeq; rewrite Hbeq in *.
    discriminate.
  apply IHl1. assumption.
Qed.

Lemma cap_FOv_cons_nil_rev : forall l1 x,
  is_in_FOvar x l1 = false ->
  cap_FOv l1 (cons x nil) = nil.
Proof.
  induction l1; intros [xn] H. reflexivity.
  simpl in *. destruct a as [ym].
  rewrite beq_nat_comm in H.
  case_eq (beq_nat ym xn); intros Hbeq; rewrite Hbeq in *.
    discriminate.
  apply IHl1. assumption.
Qed.

Lemma is_in_FOvar_min_FOv_l : forall l2 m n,
  Nat.leb (S n) (min_FOv_l l2) = true ->
  Nat.leb m n = true ->
  is_in_FOvar (Var m) l2 = false.
Proof.
  induction l2; intros m n H1 H2. reflexivity.
  simpl min_FOv_l in H1. destruct a as [ym].
  destruct l2. simpl.
    case_eq (beq_nat m ym); intros Hbeq. 2 : reflexivity.
    rewrite (beq_nat_true _ _ Hbeq) in *.
    pose proof (leb_trans _ _ _ H1 H2) as H3.
    rewrite leb_suc_f in H3. discriminate.

    simpl. case_eq (beq_nat m ym); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq) in *.
      apply leb_min_r in H1. destruct H1 as [H11 H12].
      pose proof (leb_trans _ _ _ H11 H2) as H3.
      rewrite leb_suc_f in H3. discriminate.

      apply IHl2 with (n := n).
      apply leb_min_r in H1. apply H1.
      assumption.
Qed.

Lemma rename_FOv_list_closed_exFO : forall l x y alpha,
  rename_FOv (list_closed_exFO alpha l) x y =
  list_closed_exFO (rename_FOv alpha x y) (rename_FOv_list l x y).
Proof.
  induction l; intros [xn] [ym] alpha. reflexivity.
  simpl. destruct a as [zn].
  rewrite (beq_nat_comm zn).
  case_eq (beq_nat xn zn); intros Hbeq;
    simpl; unfold rename_FOv in *; rewrite (IHl (Var xn) (Var ym));
    reflexivity.
Qed.

Lemma strip_exFO_list_list_closed_exFO : forall lv alpha,
  strip_exFO_list (list_closed_exFO alpha lv) (length lv) = lv.
Proof.
  induction lv; intros alpha. simpl. apply strip_exFO_list_0.
  simpl. rewrite IHlv. reflexivity.
Qed.

Lemma rename_FOv_A_rep_FOv_l_num_conn2 : forall n lv alpha beta,
  length lv = n ->
  is_in_FOvar (Var 0) lv = false ->
  ~ lv = nil ->
  exists l1 l2,
  rename_FOv_A alpha beta lv = replace_FOv_l alpha l1 l2 /\
  length l1 = length l2 /\
  Nat.leb  (S(max_FOv (conjSO alpha beta))) (min_FOv_l l2) = true /\
  is_all_diff_FOv l2 = true.
Proof.
  unfold rename_FOv_A.
  induction n; intros lv alpha beta Hl Hin Hnot.
    destruct lv. contradiction (Hnot eq_refl). discriminate.
    destruct lv. discriminate.
    destruct lv. simpl in *.
    destruct f as [xn]. destruct xn. discriminate.
    rewrite strip_exFO_0.
    unfold rename_FOv_max_conj.
    exists (cons (Var (S xn)) nil).
    exists (cons (Var (S (max_FOv (conjSO beta (exFO (Var (S xn)) alpha)))) )nil).
    apply conj. simpl. rewrite rep__ren_FOv. reflexivity.
    apply conj. reflexivity.
    apply conj.
      simpl.
      case_eq (max_FOv alpha). intros Hnil. simpl.
        apply leb_max_suc3. apply leb_refl.

        intros m Hm. rewrite (max_comm (max_FOv beta)).
        apply leb_max_max. simpl. rewrite max_comm. apply leb_max_suc3.
        apply leb_refl.

      reflexivity. 

    remember (cons f0 lv) as t.
    simpl. unfold rename_FOv_max_conj.
    rewrite strip_exFO_rename_FOv.

case_eq (x_occ_in_alpha alpha f); intros Hocc.
    destruct (IHn (strip_exFO_list
       (rename_FOv (list_closed_exFO alpha t) f
          (Var (S (max_FOv (conjSO beta (exFO f (list_closed_exFO alpha t))))))) (length t))
      (rename_FOv alpha f (Var (S (max_FOv (conjSO beta (exFO f (list_closed_exFO alpha t)))))))
      beta) as [l1 [l2 [H1 H2]]].
      rewrite strip_exFO_list_rename_FOv.
      rewrite length_rename_FOv_list. simpl in Hl. inversion Hl.
      reflexivity.
 simpl.
pose proof is_in_FOvar_strip_exFO_list as HH.
  unfold rename_FOv_max_conj in HH. simpl in HH. apply HH.
    simpl in Hin. destruct f as [ym]. destruct ym. discriminate.
    assumption.
    simpl in Hin. destruct f as [ym]. destruct ym; discriminate.

    rewrite strip_exFO_list_rename_FOv.
    rewrite Heqt. simpl. destruct f as [x1]. destruct f0 as [x2].
    case_eq (beq_nat x1 x2); discriminate.

    rewrite strip_exFO_list_rename_FOv in H1.
    rewrite length_rename_FOv_list in H1.
    rewrite strip_exFO_list_rename_FOv. rewrite H1.
    rewrite <- rep__ren_FOv.


    exists (app l1 (cons f nil)).
    exists (app l2 (cons (Var (S (max_FOv (conjSO beta (exFO f (list_closed_exFO alpha t)))))) nil)).
    destruct H2 as [H2 H3].
    rewrite rep_FOv__l_end. apply conj. reflexivity.
    apply conj.
      simpl. do 2 rewrite app_length.
      rewrite H2. simpl. reflexivity.

apply conj.
      rewrite min_FOv_l_app.
      simpl min_FOv_l. destruct f as [zn].
      destruct (min_or (min_FOv_l l2)
          (S (Nat.max (max_FOv beta) (Nat.max zn (max_FOv (list_closed_exFO alpha t)))))) as [Hmin | Hmin];
        rewrite Hmin. case_eq (min_FOv_l l2).
          intros HH. rewrite HH in *. simpl in *. destruct H3. discriminate.

          intros mm HH. rewrite HH in H3.
          simpl in H3.
          apply (leb_trans (max (max_FOv alpha) (max_FOv beta))
            (Nat.max
          (max_FOv
             (rename_FOv_n alpha zn (S (Nat.max (max_FOv beta) (Nat.max zn (max_FOv (list_closed_exFO alpha t)))))))
          (max_FOv beta)) mm).
rewrite max_FOv_list_closed_exFO.
apply lemma_max_rand.

          apply H3.
rewrite (max_comm (max_FOv beta)).
apply leb_max_max.
rewrite max_FOv_list_closed_exFO.
rewrite (max_comm zn).
apply leb_max_suc3.
apply leb_max_suc3.
apply leb_refl.

destruct l2. destruct H3. discriminate. discriminate.
discriminate.

(* -- *)

apply is_all_diff_FOv_app.
destruct H3 as [H3 H4].
apply conj.
  apply cap_FOv_cons_nil_rev.
    simpl max_FOv in H3.
    rewrite aa18_t in H3.
    destruct f as [zn].
    apply  is_in_FOvar_min_FOv_l with (n := 
          (Nat.max
             (S (Nat.max (max_FOv beta) (Nat.max zn (max_FOv (list_closed_exFO alpha t)))))
             (max_FOv beta))). assumption.
    apply leb_max_suc3. apply leb_refl.
    destruct f as [zn]. simpl. 
    rewrite max_comm.
    apply leb_max_suc3. rewrite max_comm.
    apply leb_max_suc3.
    rewrite max_FOv_list_closed_exFO.
    apply leb_max_suc3. apply leb_refl.
    assumption.

    apply conj. assumption.

    reflexivity.
    assumption.

(* --- *)


    rewrite rename_FOv_not_occ in *.
    rewrite rename_FOv_list_closed_exFO.
    rewrite rename_FOv_not_occ.
    assert (length (strip_exFO_list
       (list_closed_exFO alpha
          (rename_FOv_list t f
             (Var (S (max_FOv (conjSO beta (exFO f (list_closed_exFO alpha t))))))))
       (length t)) = length t) as Hass.
      
      pose proof (length_strip_exFO_list_rename_FOv t alpha beta f) as HH.
      unfold rename_FOv_max_conj in HH. rewrite rename_FOv_list_closed_exFO in HH.
      rewrite rename_FOv_not_occ in HH. assumption.

      assumption.

    pose proof (IHn (strip_exFO_list
       (list_closed_exFO alpha
          (rename_FOv_list t f
             (Var (S (max_FOv (conjSO beta (exFO f (list_closed_exFO alpha t))))))))
       (length t)) alpha beta) as HH.
    rewrite Hass in HH. apply HH.
      simpl in Hl.
      inversion Hl. reflexivity.

    rewrite <- (length_rename_FOv_list t f (Var (S (max_FOv (conjSO beta (exFO f
      (list_closed_exFO alpha t))))))).
    rewrite strip_exFO_list_list_closed_exFO.
    simpl in Hin. destruct f as [zn]. apply if_then_else_tf in Hin.
    destruct Hin as [Hin1 Hin2].
    rewrite is_in_FOvar_rename_FOv_list2. assumption. destruct zn; discriminate.
    discriminate. 
    intros HHH. rewrite HHH in *. destruct t; discriminate.
    assumption.
assumption.
Qed.

Fixpoint incr_strict_FOv ln : bool :=
  match ln with
  | nil => true 
  | cons _ nil => true
  | cons x ln' => if match x with Var n => Nat.leb (S(max_FOv_l ln')) n end then incr_strict_FOv ln' else false
  end.

Lemma decr_strict_FOv_max_FOv_l : forall l xn,
  decr_strict_FOv (cons (Var xn) l) = true ->
  max_FOv_l (cons (Var xn) l) = xn.
Proof.
  induction l; intros xn H. simpl in *.
    apply PeanoNat.Nat.max_0_r.
  destruct a as [ym]. remember (cons (Var ym) l) as t.
  simpl in *. rewrite Heqt in *. rewrite <- Heqt in *.
  destruct xn. discriminate.
  apply if_then_else_ft in H. destruct H as [H1 H2].
  specialize (IHl ym). destruct l. rewrite Heqt in *.
    simpl in *. rewrite PeanoNat.Nat.max_0_r in *.
    destruct ym. reflexivity.

    apply leb_suc_l in H1.
    apply leb_max_l in H1.
    rewrite H1. reflexivity.

  apply leb_suc_r in H1. apply leb_max_l in H1. assumption.
Qed.

Lemma leb_min_FOv_l_max_FOv_l  : forall l,
  Nat.leb (min_FOv_l l) (max_FOv_l l) = true.
Proof.
  induction l. reflexivity.
  simpl. destruct a as [ym]. destruct l. simpl.
    rewrite PeanoNat.Nat.max_0_r.
    apply leb_refl.
  remember (cons f l) as t.
  apply leb_min_max.
  assumption.
Qed.

Lemma decr_strict_FOv_min_FOv_l : forall l xn,
  ~ l = nil ->
  decr_strict_FOv (cons (Var xn) l) = true ->
  min_FOv_l (cons (Var xn) l) = min_FOv_l l.
Proof.
  intros l xn Hnil Hd. simpl. destruct l. contradiction (Hnil eq_refl).
  remember (cons f l) as t.
  simpl in Hd. rewrite Heqt in *. rewrite <- Heqt in *.
  destruct xn. discriminate.
  apply if_then_else_ft in Hd. destruct Hd as [Hd1 Hd2].
  destruct (min_or (S xn) (min_FOv_l t)) as [H | H].
    2 : assumption.
  rewrite H.
  apply leb_min in H. 
  apply leb_notswitch in Hd1.
  rewrite <- one_suc in Hd1.
  rewrite (leb_trans (S xn) (min_FOv_l t) (max_FOv_l t)) in Hd1.
    discriminate.
    assumption.
    apply leb_min_FOv_l_max_FOv_l.
Qed.

Lemma leb_decr_strict_FOv_app_pre : forall l2 n ,
Nat.leb (S n) (min_FOv_l l2) = true ->
decr_strict_FOv l2 = true ->
decr_strict_FOv (app l2 (cons (Var n) nil)) = true.
Proof.
  induction l2; intros n Hleb Hd. simpl in *. discriminate.
  destruct a as [ym]. simpl app.
  case_eq l2. intros Hnil. rewrite Hnil in *.
    simpl in *. destruct ym. discriminate. rewrite PeanoNat.Nat.max_0_r.
    rewrite Hleb. reflexivity.
  intros x lx Hlx. rewrite <- Hlx.
  simpl in Hd. rewrite Hlx in *. rewrite <- Hlx in *.
  destruct ym. discriminate. 
  apply if_then_else_ft in Hd. destruct Hd as [Hd1 Hd2].
  rewrite decr_strict_FOv_defn.
assert (Nat.leb (S (max_FOv_l (l2 ++ Var n :: nil))) (S ym) = true) as Hass.
  rewrite leb_defn_suc.
  rewrite max_FOv_l_app.
  rewrite <- (max_refl ym).
  apply leb_max_max_gen.
    assumption.
    simpl. rewrite PeanoNat.Nat.max_0_r.
    simpl in Hleb. rewrite Hlx in *. rewrite <- Hlx in *.
    case_eq (min_FOv_l l2). intros Hl2.
      rewrite Hl2 in *. discriminate.
  
      intros mm Hmm. rewrite Hmm in *.  apply leb_min_r in Hleb.
      apply Hleb.
  rewrite Hass. apply IHl2.
    simpl in Hleb. rewrite Hlx in *. rewrite <- Hlx in *.
    case_eq (min_FOv_l l2). intros Hl2.
      rewrite Hl2 in *. discriminate.
  
      intros mm Hmm. rewrite Hmm in *.  apply leb_min_r in Hleb.
      apply Hleb. assumption.
  
      destruct l2; discriminate.
Qed.

Lemma leb_decr_strict_FOv_app : forall l2 n m,
Nat.leb (S n) m = true ->
Nat.leb m (min_FOv_l l2) = true ->
decr_strict_FOv l2 = true ->
decr_strict_FOv (app l2 (cons (Var n) nil)) = true.
Proof.
  intros l2 n m H1 H2 H3.
  apply leb_decr_strict_FOv_app_pre.
  apply (leb_trans _ _ _ H1 H2).
  assumption.
Qed.

Lemma rem_FOv_app : forall l1 l2 x,
  rem_FOv (app l1 l2) x = app (rem_FOv l1 x) (rem_FOv l2 x).
Proof.
  induction l1; intros l2 [xn]. reflexivity.
  simpl. destruct a as [zn]. case_eq (beq_nat xn zn); intros Hbeq.
    apply IHl1.

    rewrite IHl1. reflexivity.
Qed.


Lemma is_in_FOvar_rem_FOv : forall l x,
  is_in_FOvar x l = false ->
  rem_FOv l x = l.
Proof.
  induction l; intros [xn] Hin. reflexivity.
  simpl in *. destruct a as [ym].
  case_eq (beq_nat xn ym); intros Hbeq; rewrite Hbeq in *.
    discriminate.
  rewrite IHl. reflexivity. assumption.
Qed.


Lemma rep_FOv_not_occ : forall alpha x y,
  x_occ_in_alpha alpha x = false ->
  replace_FOv alpha x y = alpha.
Proof.
  induction alpha; intros [xn] [ym] Hocc.
    simpl in *. destruct p. destruct f as [zn].
    rewrite Hocc. reflexivity.

    destruct f as [z1]; destruct f0 as [z2].
    simpl in *. case_eq (beq_nat xn z1); intros Hbeq;
      rewrite Hbeq in Hocc. discriminate.
      rewrite Hocc. reflexivity.

    destruct f as [z1]; destruct f0 as [z2].
    simpl in *. case_eq (beq_nat xn z1); intros Hbeq;
      rewrite Hbeq in Hocc. discriminate.
      rewrite Hocc. reflexivity.

    destruct f as [zn].  simpl in *.
    case_eq (beq_nat xn zn); intros Hbeq; rewrite Hbeq in *.
      discriminate. rewrite IHalpha. reflexivity. assumption.

    destruct f as [zn].  simpl in *.
    case_eq (beq_nat xn zn); intros Hbeq; rewrite Hbeq in *.
      discriminate. rewrite IHalpha. reflexivity. assumption.

    simpl in *. rewrite IHalpha. reflexivity. assumption.

    simpl in *. apply x_occ_in_alpha_conjSO in Hocc.
    rewrite IHalpha1. rewrite IHalpha2. reflexivity.
    apply Hocc. apply Hocc.

    simpl in *. apply x_occ_in_alpha_conjSO in Hocc.
    rewrite IHalpha1. rewrite IHalpha2. reflexivity.
    apply Hocc. apply Hocc.

    simpl in *. apply x_occ_in_alpha_conjSO in Hocc.
    rewrite IHalpha1. rewrite IHalpha2. reflexivity.
    apply Hocc. apply Hocc.

    destruct p. simpl in *. rewrite IHalpha. reflexivity. assumption.

    destruct p. simpl in *. rewrite IHalpha. reflexivity. assumption.
Qed.

Lemma max_FOv_rep_FOv : forall atm x ym,
  (x_occ_in_alpha atm x = true ->
  max_FOv (replace_FOv atm x (Var ym)) = max (max_FOv_l (rem_FOv (FOvars_in atm) x)) ym).
Proof.
  induction atm; intros [xn] ym Hocc.
    destruct p. destruct f as [zn]. simpl in *.
    rewrite Hocc. reflexivity.

    destruct f as [z1]. destruct f0 as [z2].
    simpl in *. case_eq (beq_nat xn z1); intros Hbeq;
      rewrite Hbeq in *; try discriminate;
      case_eq (beq_nat xn z2); intros Hbeq2;
        simpl. apply max_refl.
        rewrite PeanoNat.Nat.max_0_r. rewrite max_comm. reflexivity.
        rewrite PeanoNat.Nat.max_0_r. rewrite max_comm. reflexivity.
        rewrite Hbeq2 in *. discriminate.

    destruct f as [z1]. destruct f0 as [z2].
    simpl in *. case_eq (beq_nat xn z1); intros Hbeq;
      rewrite Hbeq in *; try discriminate;
      case_eq (beq_nat xn z2); intros Hbeq2;
        simpl. apply max_refl.
        rewrite PeanoNat.Nat.max_0_r. rewrite max_comm. reflexivity.
        rewrite PeanoNat.Nat.max_0_r. rewrite max_comm. reflexivity.
        rewrite Hbeq2 in *. discriminate.

    destruct f as [zn]. simpl in *.
    case_eq (beq_nat xn zn); intros Hbeq; rewrite Hbeq in *.
      simpl. case_eq (x_occ_in_alpha atm (Var xn)); intros Hocc2.
        simpl. rewrite IHatm. rewrite max_comm.
        rewrite <- PeanoNat.Nat.max_assoc.
        rewrite max_refl. reflexivity. assumption.

        rewrite rep_FOv_not_occ. rewrite is_in_FOvar_rem_FOv.
        rewrite max_comm. rewrite max_FOv__l. reflexivity.
        rewrite x_occ_in_alpha_is_in_FOvar in Hocc2. assumption.
        assumption.

      simpl. rewrite IHatm. rewrite PeanoNat.Nat.max_assoc.
      reflexivity. assumption.

    destruct f as [zn]. simpl in *.
    case_eq (beq_nat xn zn); intros Hbeq; rewrite Hbeq in *.
      simpl. case_eq (x_occ_in_alpha atm (Var xn)); intros Hocc2.
        simpl. rewrite IHatm. rewrite max_comm.
        rewrite <- PeanoNat.Nat.max_assoc.
        rewrite max_refl. reflexivity. assumption.

        rewrite rep_FOv_not_occ. rewrite is_in_FOvar_rem_FOv.
        rewrite max_comm. rewrite max_FOv__l. reflexivity.
        rewrite x_occ_in_alpha_is_in_FOvar in Hocc2. assumption.
        assumption.

      simpl. rewrite IHatm. rewrite PeanoNat.Nat.max_assoc.
      reflexivity. assumption.

    simpl in *. apply IHatm. assumption.

    simpl in Hocc. simpl.
      rewrite rem_FOv_app. rewrite max_FOv_l_app.
      case_eq (x_occ_in_alpha atm1 (Var xn)); 
      intros Hocc2; rewrite Hocc2 in *. rewrite IHatm1. 2 : assumption.
      case_eq (x_occ_in_alpha atm2 (Var xn)); intros Hocc3.
        rewrite IHatm2. 2 : assumption. 
        rewrite <- (PeanoNat.Nat.max_assoc _ ym).
        rewrite (max_comm ym).
        rewrite <- (PeanoNat.Nat.max_assoc _ _ ym).
        rewrite max_refl. 
        rewrite (PeanoNat.Nat.max_assoc _ _ ym).  reflexivity.

        rewrite (is_in_FOvar_rem_FOv (FOvars_in atm2)).
        rewrite (rep_FOv_not_occ atm2).
        rewrite (max_FOv__l atm2).
        rewrite <- (PeanoNat.Nat.max_assoc _ ym).
        rewrite (max_comm ym).
        rewrite (PeanoNat.Nat.max_assoc _ _ ym).  reflexivity.
        assumption. rewrite x_occ_in_alpha_is_in_FOvar in Hocc3.
        assumption.

        rewrite IHatm2.
        rewrite (is_in_FOvar_rem_FOv (FOvars_in atm1)).
        rewrite (rep_FOv_not_occ atm1).
        rewrite (max_FOv__l atm1).
        rewrite <- (PeanoNat.Nat.max_assoc _ _ ym). reflexivity.
        all : try assumption. rewrite x_occ_in_alpha_is_in_FOvar in Hocc2.
        assumption.

    simpl in Hocc. simpl.
      rewrite rem_FOv_app. rewrite max_FOv_l_app.
      case_eq (x_occ_in_alpha atm1 (Var xn)); 
      intros Hocc2; rewrite Hocc2 in *. rewrite IHatm1. 2 : assumption.
      case_eq (x_occ_in_alpha atm2 (Var xn)); intros Hocc3.
        rewrite IHatm2. 2 : assumption. 
        rewrite <- (PeanoNat.Nat.max_assoc _ ym).
        rewrite (max_comm ym).
        rewrite <- (PeanoNat.Nat.max_assoc _ _ ym).
        rewrite max_refl. 
        rewrite (PeanoNat.Nat.max_assoc _ _ ym).  reflexivity.

        rewrite (is_in_FOvar_rem_FOv (FOvars_in atm2)).
        rewrite (rep_FOv_not_occ atm2).
        rewrite (max_FOv__l atm2).
        rewrite <- (PeanoNat.Nat.max_assoc _ ym).
        rewrite (max_comm ym).
        rewrite (PeanoNat.Nat.max_assoc _ _ ym).  reflexivity.
        assumption. rewrite x_occ_in_alpha_is_in_FOvar in Hocc3.
        assumption.

        rewrite IHatm2.
        rewrite (is_in_FOvar_rem_FOv (FOvars_in atm1)).
        rewrite (rep_FOv_not_occ atm1).
        rewrite (max_FOv__l atm1).
        rewrite <- (PeanoNat.Nat.max_assoc _ _ ym). reflexivity.
        all : try assumption. rewrite x_occ_in_alpha_is_in_FOvar in Hocc2.
        assumption.

    simpl in Hocc. simpl.
      rewrite rem_FOv_app. rewrite max_FOv_l_app.
      case_eq (x_occ_in_alpha atm1 (Var xn)); 
      intros Hocc2; rewrite Hocc2 in *. rewrite IHatm1. 2 : assumption.
      case_eq (x_occ_in_alpha atm2 (Var xn)); intros Hocc3.
        rewrite IHatm2. 2 : assumption. 
        rewrite <- (PeanoNat.Nat.max_assoc _ ym).
        rewrite (max_comm ym).
        rewrite <- (PeanoNat.Nat.max_assoc _ _ ym).
        rewrite max_refl. 
        rewrite (PeanoNat.Nat.max_assoc _ _ ym).  reflexivity.

        rewrite (is_in_FOvar_rem_FOv (FOvars_in atm2)).
        rewrite (rep_FOv_not_occ atm2).
        rewrite (max_FOv__l atm2).
        rewrite <- (PeanoNat.Nat.max_assoc _ ym).
        rewrite (max_comm ym).
        rewrite (PeanoNat.Nat.max_assoc _ _ ym).  reflexivity.
        assumption. rewrite x_occ_in_alpha_is_in_FOvar in Hocc3.
        assumption.

        rewrite IHatm2.
        rewrite (is_in_FOvar_rem_FOv (FOvars_in atm1)).
        rewrite (rep_FOv_not_occ atm1).
        rewrite (max_FOv__l atm1).
        rewrite <- (PeanoNat.Nat.max_assoc _ _ ym). reflexivity.
        all : try assumption. rewrite x_occ_in_alpha_is_in_FOvar in Hocc2.
        assumption.

     destruct p. simpl in *. apply IHatm. assumption.

     destruct p. simpl in *. apply IHatm. assumption.
Qed.

Lemma leb_max_rand6 : forall l p n zn,
is_in_FOvar (Var zn) l = true ->
Nat.leb (Nat.max zn (Nat.max (max_FOv_l l) p))
  (Nat.max (max_FOv_l (rem_FOv l (Var zn)))
     (S (Nat.max (Nat.max zn (Nat.max (max_FOv_l l) p)) n))) = true.
Proof.
  intros l p n zn Hin.
  rewrite (max_comm _ (S (max (max zn (max (max_FOv_l l) p)) n))).
  apply leb_max_suc3. apply leb_suc_r.
  rewrite (max_comm zn). apply leb_max_suc3.
  apply leb_refl.
Qed.

Lemma leb_max_rand5 : forall alpha n t zn,
x_occ_in_alpha alpha (Var zn) = true ->
Nat.leb (Nat.max n (Nat.max zn (max_FOv (list_closed_exFO alpha t))))
  (Nat.max
     (max_FOv
        (rename_FOv alpha (Var zn)
           (Var (S (Nat.max n (Nat.max zn (max_FOv (list_closed_exFO alpha t))))))))
     n) = true.
Proof.
  intros alpha n t zn H. rewrite (max_comm n).
  apply leb_max_max. rewrite <- rep__ren_FOv.
  rewrite max_FOv_rep_FOv. rewrite max_FOv_list_closed_exFO.
  rewrite max_FOv__l.
  apply leb_max_rand6.
  rewrite x_occ_in_alpha_is_in_FOvar in H.
  all : assumption.
Qed.

Lemma leb_max_rand4 : forall alpha beta t zn,
x_occ_in_alpha alpha (Var zn) = true ->
Nat.leb (Nat.max (max_FOv beta) (Nat.max zn (max_FOv (list_closed_exFO alpha t))))
  (Nat.max
     (max_FOv
        (rename_FOv alpha (Var zn)
           (Var (S (Nat.max (max_FOv beta) (Nat.max zn (max_FOv (list_closed_exFO alpha t))))))))
     (max_FOv beta)) = true.
Proof.
  intros alpha beta t zn H.
  apply leb_max_rand5. assumption.
Qed.

Lemma is_in_FOvar_rand1 : forall beta alpha x,
  is_in_FOvar x (cons (Var (S (max_FOv (conjSO beta (exFO x alpha))))) nil) = false.
Admitted.

Lemma cap_FOv_nil_rand1 : forall alpha beta x,
cap_FOv (Var x :: nil) (Var (S (max_FOv (conjSO beta (exFO (Var x) alpha)))) :: nil) =
nil.
Admitted.

Lemma leb_max_FOv_l_rand1 : forall beta alpha x,
  Nat.leb (max_FOv_l (cons x nil)) 
    (max_FOv_l (cons (Var (S (max_FOv (conjSO beta (exFO x alpha))))) nil))
      = true.
Admitted.

Lemma is_in_FOvar_l_ren_FOv_list : forall l1 l2 x y,
  is_in_FOvar_l l1 l2 = true ->
  is_in_FOvar_l (rename_FOv_list l1 x y) (rename_FOv_list l2 x y) = true.
Admitted.

Lemma leb_max_FOv_l_rand2 : forall alpha beta f t l1 l2,
is_in_FOvar_l l1
       (FOvars_in (rename_FOv alpha f (Var (S (max_FOv (conjSO beta (exFO f (list_closed_exFO alpha t)))))))) = true ->
Nat.leb (max_FOv_l (l1 ++ f :: nil))
  (max_FOv_l (l2 ++ Var (S (max_FOv (conjSO beta (exFO f (list_closed_exFO alpha t))))) :: nil)) = true.
Admitted.

Lemma leb_max_FOv_l_rand3 : forall alpha x beta,
  Nat.leb (S (max_FOv_l (cons x nil)))
    (max_FOv_l (cons (Var (S (max_FOv (conjSO beta (exFO x alpha))))) nil)) = true.
Proof.
  intros alpha [xn] beta.
  simpl. rewrite PeanoNat.Nat.max_0_r.
  rewrite max_comm. do 2 apply leb_max_suc3.
  apply leb_refl.
Qed.

Lemma is_in_FOvar_l_ren_FOv_list_rand1 : forall l1 t f alpha beta,
is_in_FOvar_l l1 (rename_FOv_list t f (Var (S (max_FOv (conjSO beta (exFO f (list_closed_exFO alpha t))))))) =
     true ->
is_in_FOvar_l l1 (f :: t) = true.
Proof.
  induction l1; intros t f alpha beta H. reflexivity.
  simpl. destruct a as [ym]. destruct f as [xn].
  simpl in H. 
  case_eq ( is_in_FOvar (Var ym)
        (rename_FOv_list t (Var xn) (Var (S (Nat.max (max_FOv beta) (Nat.max xn (max_FOv (list_closed_exFO alpha t))))))));
    intros Hin; rewrite Hin in *. 2 : discriminate.
  case_eq (beq_nat ym xn); intros Hbeq.
    apply (IHl1 _ _ alpha beta). assumption.

    case_eq (is_in_FOvar (Var ym) t); intros Hin2.
      apply (IHl1 _ _ alpha beta). assumption.

      
(* Search is_in_FOvar rename_FOv_list. *)
Admitted.

Lemma leb_max_FOv_l_rand4_pre : forall alpha beta f l1 l2 t,
Nat.leb (S (max_FOv_l l1)) (min_FOv_l l2) = true ->
is_in_FOvar_l l1   (strip_exFO_list
          (rename_FOv (list_closed_exFO alpha t) f (Var (S (max_FOv (conjSO beta (exFO f (list_closed_exFO alpha t)))))))
          (length t)) = true ->
Nat.leb (S(max_FOv_l (l1 ++ f :: nil))) (min_FOv_l (l2 ++ Var (S (max_FOv (conjSO beta (exFO f (list_closed_exFO alpha t))))) :: nil)) = true.
Proof.
Admitted.
(*   intros until 0. intros Hleb Hin. (*   Hl Hleb1 Hleb2 Hall Hdec Hin. *)
  rewrite max_FOv_l_app.
  rewrite min_FOv_l_app. rewrite PeanoNat.Nat.succ_max_distr.
Search Nat.leb max.
  apply leb_max_max_gen. apply (leb_trans _ _ _ Hleb (leb_min_FOv_l_max_FOv_l _)).
  simpl. destruct f as [un].
  rewrite PeanoNat.Nat.max_0_r.
  rewrite (max_comm (max_FOv beta)).
  do 2 apply leb_max_suc3.
  apply leb_refl.
Qed.
 *)
Lemma leb_max_FOv_l_rand4 : forall alpha beta f l1 l2 t,
Nat.leb (S (max_FOv_l l1)) (min_FOv_l l2) = true ->
is_in_FOvar_l l1
       (strip_exFO_list
          (rename_FOv (list_closed_exFO alpha t) f (Var (S (max_FOv (conjSO beta (exFO f (list_closed_exFO alpha t)))))))
          (length t)) = true ->
match min_FOv_l (l2 ++ Var (S (max_FOv (conjSO beta (exFO f (list_closed_exFO alpha t))))) :: nil) with
| 0 => false
| S m' => Nat.leb (max_FOv_l (l1 ++ f :: nil)) m'
end = true.
Proof.
  apply leb_max_FOv_l_rand4_pre.
Qed.

Lemma is_in_FOvar_0_ren_FOv_list : forall alpha beta f t,
is_in_FOvar (Var 0) (f :: t) = false ->
is_in_FOvar (Var 0) (rename_FOv_list t f (Var (S (max_FOv (conjSO beta (exFO f (list_closed_exFO alpha t))))))) = false.
Admitted.

Lemma is_in_FOvar_l_ren_FOv_list_rand2 : forall t f alpha beta l1,
is_in_FOvar_l l1 (rename_FOv_list t f (Var (S (max_FOv (conjSO beta (exFO f (list_closed_exFO alpha t))))))) = true ->
is_in_FOvar_l (l1 ++ f :: nil) (f :: t) = true.
Admitted.

Open Scope nat.

Fixpoint indicies_l2_FOv_pre lx x count :=
  match lx with
  | nil => nil
  | cons y lx' => match x, y with Var xn, Var ym =>
      if beq_nat xn ym then cons (1 + count) (indicies_l2_FOv_pre lx' x (S count))
        else indicies_l2_FOv_pre lx' x (S count)
  end end.

Definition indicies_l2_FOv lx x :=
  indicies_l2_FOv_pre lx x 0.

Definition consistent_lx_lx_x l1 l2 x : Prop :=
  is_constant (@ind_gen FOvariable (Var 0) (indicies_l2_FOv l1 x) l2).

Definition consistent_lx_lx l1 l2 : Prop :=
  forall x, consistent_lx_lx_x l1 l2 x.

Lemma consistent_lx_lx_cons_nil : forall x y,
  consistent_lx_lx (cons x nil) (cons y nil).
Proof.
  unfold consistent_lx_lx.
  unfold consistent_lx_lx_x.
  unfold is_constant.
  unfold indicies_l2_FOv.
  intros [xn] [ym] [zn]. simpl.
  case_eq (beq_nat zn xn); intros Hbeq.
    simpl. exists (Var ym). exists 1. reflexivity.
    simpl. exists (Var 0). exists 0. reflexivity.
Qed.

Lemma is_in_FOvar_ren_FOv_list : forall l x u z,
x <> z ->
u <> x ->
 is_in_FOvar x l = false ->
is_in_FOvar x (rename_FOv_list l z u) = false.
Proof.
  induction l; intros [xn] [zn] [ym] H1 H2 Hin. reflexivity.
  simpl. destruct a as [un]. simpl in Hin.
  apply if_then_else_tf in Hin. destruct Hin as [Hin1 Hin2].
  case_eq (beq_nat ym un); intros Hbeq;
    simpl. rewrite beq_nat_comm. rewrite (FOvar_neq _ _ H2).
    apply  IHl; assumption.

    rewrite Hin1. apply IHl; assumption.
Qed.

Lemma is_in_FOvar_rep_FOv : forall alpha x u z,
x <> z ->
u <> x ->
 is_in_FOvar x (FOvars_in alpha) = false ->
is_in_FOvar x (FOvars_in (replace_FOv alpha z u)) = false.
Proof.
  intros until 0.
  rewrite rep__ren_FOv.
  rewrite FOvars_in_rename_FOv.
  apply is_in_FOvar_ren_FOv_list.
Qed.

Lemma x_occ_in_alpha_rep_FOv2 : forall alpha z u x,
  ~ x = z ->
  ~ u = x ->
  x_occ_in_alpha alpha x = false ->
  x_occ_in_alpha (replace_FOv alpha z u) x = false.
Proof.
  intros until 0.
  do 2 rewrite x_occ_in_alpha_is_in_FOvar.
  apply (is_in_FOvar_rep_FOv).
Qed.

Lemma x_occ_in_alpha_rep_FOv_l : forall l1 l2 atm x,
  length l1 = length l2 ->
  is_in_FOvar x l1 = true ->
  is_in_FOvar x l2 = false ->
  x_occ_in_alpha (replace_FOv_l atm l1 l2) x = false.
Proof.
  induction l1; intros l2 atm [xn] Hl Hin1 Hin2. discriminate.
  destruct a as [ym]. simpl in *.
  destruct l2. discriminate.
  destruct f as [zn]. simpl in *.
  apply if_then_else_tf in Hin2. 
  case_eq (beq_nat xn ym); intros Hbeq; rewrite Hbeq in *.
    rewrite (beq_nat_true _ _ Hbeq).
    apply x_occ_in_alpha_rep_FOv_f.
    apply beq_nat_false_FOv.
    rewrite <- (beq_nat_true _ _ Hbeq).
    apply Hin2.

    apply x_occ_in_alpha_rep_FOv2.
      apply beq_nat_false_FOv. assumption.
      apply beq_nat_false_FOv. rewrite beq_nat_comm.
        apply Hin2.
      apply IHl1.
        inversion Hl. reflexivity.
        assumption.
        apply Hin2.
Qed.

(* Left it here 19/01/18 *)
(* Keep going on admitted lemmas until lem_try1 (now, rename_FOv_A_rep_FOv_l_num_conn9) is closed. 
Then try applying it upwards and downwards. *)
Lemma rep_FOv__l_not_in : forall l1 l2 atm x y,
  length l1 = length l2 ->
  is_in_FOvar x l1 = true ->
  is_in_FOvar x l2 = false ->
  replace_FOv (replace_FOv_l atm l1 l2) x y = replace_FOv_l atm l1 l2.
Proof.
  induction l1; intros l2 atm [xn] [ym] Hl H1 H2. discriminate.
  simpl. destruct l2. discriminate.
  destruct a as [zn]. destruct f as [un].
  simpl in *.
  apply if_then_else_tf in H2.
  case_eq (beq_nat xn zn); intros Hbeq; rewrite Hbeq in *.
    rewrite (beq_nat_true _ _ Hbeq) in *.
    rewrite (rep_FOv_not_occ). reflexivity.
    apply x_occ_in_alpha_rep_FOv_f.
    apply beq_nat_false_FOv. apply H2.

    case_eq (is_in_FOvar (Var zn) l1); intros Hin.
      rewrite (rep_FOv_not_occ). reflexivity.
      apply x_occ_in_alpha_rep_FOv2.
      apply beq_nat_false_FOv. assumption.
      apply beq_nat_false_FOv. rewrite beq_nat_comm. apply H2.
      apply x_occ_in_alpha_rep_FOv_l.
        inversion Hl. reflexivity.
        assumption. apply H2.

      rewrite (rep_FOv_not_occ _ (Var xn)).
      reflexivity.
      apply x_occ_in_alpha_rep_FOv2.
      apply beq_nat_false_FOv. assumption.
      apply beq_nat_false_FOv. rewrite beq_nat_comm.
        apply H2.
      apply x_occ_in_alpha_rep_FOv_l.
        inversion Hl. reflexivity.
      assumption. apply H2.
Qed.

Lemma leb_max_FOv_l_rand5 : forall l1 l2 un y,
  ~ l2 = nil ->
  Nat.leb (S (max_FOv_l (cons (Var un) l1))) 
          (min_FOv_l (cons y l2)) = true ->
  Nat.leb (S un) (min_FOv_l l2) = true.
Proof.
  intros l1 l2 un [ym] Hnil2 H.
  simpl max_FOv_l in H.
  simpl min_FOv_l in H.
  destruct l2. contradiction (Hnil2 eq_refl).
  remember (cons f l2) as ll.
  apply leb_min_r in H.
  destruct H as [H1 H2].
  simpl in *.
  case_eq (min_FOv_l ll). intros Hnil; rewrite Hnil in *.   
    discriminate.
  intros mm Hmm. rewrite Hmm in H2.
  apply leb_max in H2. apply H2.
Qed.

Lemma is_in_FOvar_l_constant_l : forall l x,
  is_in_FOvar_l l (cons x nil) = true ->
  exists n, l = constant_l x n.
Proof.
  induction l; intros [xn] Hin.
    exists 0. reflexivity.

    simpl in Hin. destruct a as [ym].
    apply if_then_else_ft in Hin. destruct Hin as [Hin1 Hin2].
    apply if_then_else_ft in Hin1. destruct Hin1 as [Hin1 Hin3].
    rewrite (beq_nat_true _ _ Hin1) in *.
    destruct (IHl _ Hin2) as [n IH].
    rewrite IH. exists (S n). reflexivity.
Qed.

Lemma min_FOv_l_constant_l  : forall n xn,
  min_FOv_l (constant_l (Var xn) (S n)) = xn.
Proof.
  induction n; intros xn. reflexivity.
  remember (S n) as m. simpl in *.
  case_eq (constant_l (Var xn) m). reflexivity.
  intros mm lmm Hlmm. rewrite <- Hlmm.
  rewrite Heqm in *.
  destruct (min_or xn (min_FOv_l (constant_l (Var xn) (S n)))) as [H | H];
    rewrite H. reflexivity.
    apply IHn.
Qed.

Lemma leb_min_FOv_l_is_in_FOvar_l_gen_pre : forall l n ym,
  is_in_FOvar (Var ym) l = true ->
  Nat.leb n (min_FOv_l l) = true ->
  Nat.leb n ym = true.
Proof.
  induction l; intros n ym Hin Hleb. discriminate.
  destruct a as [zn]. simpl in *.
  case_eq (beq_nat ym zn); intros Hbeq; rewrite Hbeq in *.
    destruct l. rewrite (beq_nat_true _ _ Hbeq). assumption.
    remember (cons f l) as ll.
    rewrite (beq_nat_true _ _ Hbeq) in *.
    apply leb_min_r in Hleb. apply Hleb.

    destruct l. discriminate.
    remember (cons f l) as ll.  
    apply leb_min_r in Hleb. destruct Hleb.
    apply IHl; assumption.
Qed.


Lemma leb_min_r2 : forall n m1 m2,
  Nat.leb n m1 = true ->
  Nat.leb n m2 = true ->
  Nat.leb n (min m1 m2) = true.
Proof.
  induction n; intros m1 m2 H1 H2. reflexivity.
  simpl in *. destruct m1. discriminate.
  destruct m2. discriminate. simpl.
  apply IHn; assumption.
Qed.

Lemma leb_min_FOv_l_is_in_FOvar_l_gen : forall l' l n,
  ~ l' = nil ->
  is_in_FOvar_l l' l = true ->
  Nat.leb n (min_FOv_l  l) = true ->
  Nat.leb n (min_FOv_l l') = true.
Proof.
  induction l'; intros l n Hnot Hin Hleb.
    contradiction (Hnot eq_refl).

    destruct a as [ym].
    destruct l'. simpl in *.
    apply if_then_else_ft in Hin. 
    destruct Hin as [Hin1 Hin2].
    apply (leb_min_FOv_l_is_in_FOvar_l_gen_pre _ _ _ Hin1 Hleb).

    remember (cons f l') as ll'.
    simpl in *. rewrite Heqll'.
    rewrite <- Heqll'.
    apply if_then_else_ft in Hin. destruct Hin as [Hin1 Hin2].
    apply leb_min_r2.
      apply (leb_min_FOv_l_is_in_FOvar_l_gen_pre _ _ _ Hin1 Hleb).  
      apply IHl' with (l := l); try assumption.
        rewrite Heqll'. discriminate.
Qed.

Lemma leb_min_FOv_l_is_in_FOvar_l : forall l l' x n,
  is_in_FOvar_l l' l = true ->
  Nat.leb n (min_FOv_l (cons x l)) = true ->
  Nat.leb n (min_FOv_l (cons x l')) = true.
Proof.
  intros until 0. intros Hin. 
  apply leb_min_FOv_l_is_in_FOvar_l_gen. discriminate.
  destruct x as [xn]. simpl. rewrite <- beq_nat_refl. 
  apply is_in_FOvar_l_cons_r2.
  assumption.
Qed.

Lemma is_in_FOvar_max_FOv_l_leb : forall l1 l2,
is_in_FOvar_l l1 l2 = true ->
Nat.leb (max_FOv_l l1) (max_FOv_l l2) = true.
Proof.
  induction l1; intros l2 Hin. reflexivity.
  simpl in *. destruct a as [ym]. apply if_then_else_ft in Hin.
  destruct Hin as [Hin1 Hin2].
  rewrite <- (max_refl (max_FOv_l l2)).
  apply leb_max_max_gen.
    apply is_in_FOvar_leb_max_FOv_l. assumption.

    apply IHl1; assumption.
Qed.

Lemma leb_max_FOv_l_rand6 : forall l1 l2 l1' l2' f f0,
  Nat.leb (S (max_FOv_l (cons f l1))) (min_FOv_l (cons f0 l2)) = true ->
  Nat.leb (S (max_FOv_l l1')) (min_FOv_l l2') = true ->
  is_in_FOvar_l l2' l2 = true ->
  is_in_FOvar_l l1' l1 = true ->
  Nat.leb (S (max_FOv_l (cons f l1'))) (min_FOv_l (cons f0 l2')) = true.
Proof.
  intros until 0; intros Hleb1 Hleb2 Hin1 Hin2.
  destruct f as [xn]. destruct f0 as [ym].
  simpl min_FOv_l in *.
    destruct l2. destruct l2'; discriminate.
    destruct l2'. discriminate.
    remember (cons f l2) as ll2. remember (cons f0 l2') as ll2'.
    apply leb_min_r in Hleb1. destruct Hleb1 as [Hleb1 Hleb3].
    simpl max_FOv_l. case_eq (min_FOv_l ll2').
      intros Hnil. rewrite Hnil in *. discriminate.
    intros mm Hmm. rewrite Hmm in *. simpl in Hleb2.
    destruct ym. discriminate. simpl.
    assert (~ ll2' = nil) as Hnotnil. rewrite Heqll2'. discriminate.
pose proof (leb_min_FOv_l_is_in_FOvar_l_gen _ _ (min_FOv_l ll2) Hnotnil Hin1 (leb_refl _)) as Hp.
pose proof (leb_trans _ _ _ Hleb3 Hp) as Hp2.
rewrite Hmm in Hp2. simpl in Hp2. 
simpl in Hleb1.
apply leb_min_r2.
  rewrite <- (max_refl ym).
  apply leb_max_max_gen.
    apply leb_max in Hleb1. apply Hleb1.
    apply (leb_trans _ _ _ (is_in_FOvar_max_FOv_l_leb _ _ Hin2)).
    apply leb_max in Hleb1. apply Hleb1.

  rewrite <- (max_refl mm).
  apply leb_max_max_gen.
    apply leb_max in Hp2. apply Hp2.
    apply (leb_trans _ _ _ (is_in_FOvar_max_FOv_l_leb _ _ Hin2)).
    apply leb_max in Hp2. apply Hp2.
Qed.

Lemma decr_strict_FOv_cons : forall l x,
  decr_strict_FOv (cons x l) = true ->
  decr_strict_FOv l = true.
Proof.
  intros l [xn] H.
  simpl in H. destruct l. reflexivity.
  destruct xn. discriminate. 
  apply if_then_else_ft in H. apply H.
Qed.

Lemma is_all_diff_FOv_is_in_FOvar_l : forall l' l,
  is_in_FOvar_l l' l = true ->
  decr_strict_FOv l' = true ->
  is_all_diff_FOv l = true ->
  is_all_diff_FOv l' = true.
Proof.
  induction l'; intros l Hin Hdec Hall. reflexivity.
  destruct a as [ym].
  simpl in Hin. apply if_then_else_ft in Hin.
  destruct Hin as [Hin1 Hin2].
  simpl. simpl in Hdec. destruct l'. reflexivity.
    destruct ym. discriminate.
  rewrite sS_lem_f7_gen_pre.
  apply if_then_else_ft in Hdec.
  apply (IHl' _ Hin2). apply Hdec. assumption.
  apply if_then_else_ft in Hdec. apply Hdec.
Qed.

Lemma ind_gen_FOv_pre_cons : forall {A : Type} lP P n (pa pa2 : A) lpa,
  @ind_gen A pa2 (indicies_l2_FOv_pre lP P (S n)) (cons pa lpa) =
  @ind_gen A pa2 (indicies_l2_FOv_pre lP P n) lpa.
Proof.
  induction lP; intros P n pa lpa.
    simpl. reflexivity.

    destruct a as [Qm]. destruct P as [Pn]. simpl.
    destruct n; intros lpa2;
    case_eq (beq_nat Pn Qm); intros Hbeq; simpl; try (rewrite IHlP;
      reflexivity).
Qed.

Lemma ind_l2_FOv_pre_nil : forall l x n,
  is_in_FOvar x l = false ->
  indicies_l2_FOv_pre l x n = nil.
Proof.
  induction l; intros [xn] n Hin. reflexivity.
  simpl in *. destruct a as [ym].
  case_eq (beq_nat xn ym); intros Hbeq; rewrite Hbeq in *.
      discriminate.
  apply IHl. assumption.
Qed.

Lemma consistent_lx_lx_x_pre_cons_not_in : forall l1 l2 x u y z n,
  is_in_FOvar x l1 = false ->
  @ind_gen _ (Var 0)(indicies_l2_FOv l1 u) l2 = constant_l z (S n) ->
  exists m, @ind_gen _ (Var 0) (indicies_l2_FOv (cons x l1) u) (cons y l2) = constant_l z m.
Proof.
  intros l1 l2 [xn] [un] [ym] [zn] n (* H1 *) (* H2 *) H3 (* H4 *) H5.
  unfold indicies_l2_FOv in *.
  simpl in *. case_eq (beq_nat un xn); intros Hbeq.
    simpl.
    rewrite ind_gen_FOv_pre_cons. rewrite H5. 
    rewrite ( beq_nat_true _ _ Hbeq) in H5.
    rewrite ind_l2_FOv_pre_nil in H5. discriminate.
    assumption.

    rewrite ind_gen_FOv_pre_cons. exists (S n).
    assumption.
Qed.

Lemma ind_gen_ind_l2_FOv_is_not_in_pre : forall l1 l2 n y x0,
  @ind_gen FOvariable x0 (indicies_l2_FOv_pre l1 y n) l2 = nil ->
  is_in_FOvar y l1 = false.
Proof.
  induction l1; intros l2 n [ym] [x0] H. reflexivity.
  simpl in *. destruct a as [zn].
  case_eq (beq_nat ym zn);
    intros Hbeq; simpl in H; rewrite Hbeq in H.
    simpl in H.
    destruct l2; discriminate.

    apply IHl1 in H. assumption.
Qed.

Lemma ind_gen_ind_l2_FOv_is_not_in : forall l1 l2 y x0,
  @ind_gen FOvariable x0 (indicies_l2_FOv l1 y) l2 = nil ->
  is_in_FOvar y l1 = false.
Proof.
  unfold indicies_l2_FOv. intros until 0.
  apply ind_gen_ind_l2_FOv_is_not_in_pre.
Qed.

Lemma consistent_lx_lx_x_cons_not_in : forall l1' l2' x y y',
  is_in_FOvar x l1' = false ->
(*   is_in_FOvar y l2' = false -> *)
  consistent_lx_lx_x l1' l2' y' ->
  consistent_lx_lx_x (cons x l1') (cons y l2') y'.
Proof.
  unfold consistent_lx_lx_x .
  unfold is_constant.
  intros until 0. intros H1 H3.
  destruct H3 as [a [n H]].
  destruct n. simpl in *.
    pose proof H as H'.
    apply ind_gen_ind_l2_FOv_is_not_in in H.
    unfold indicies_l2_FOv in *.
    destruct x as [xn]. destruct y' as [ym].
    simpl. case_eq (beq_nat ym xn); intros Hbeq;
      simpl; rewrite ind_gen_FOv_pre_cons.
      rewrite H'. exists y. exists 1. reflexivity.

      rewrite H'. exists (Var 0). exists 0. reflexivity.

    exists a. apply (consistent_lx_lx_x_pre_cons_not_in _ _ _ _ _ _ _ H1 H).
Qed.

Lemma consistent_lx_lx_cons_not_in : forall l1' l2' x y,
  is_in_FOvar x l1' = false ->
(*   is_in_FOvar y l2' = false -> *)
  consistent_lx_lx l1' l2' ->
  consistent_lx_lx (cons x l1') (cons y l2').
Proof.
  intros l1 l2 x y H1 (* H2 *) Hcon.
  unfold consistent_lx_lx in *.
  intros y'.
  apply (consistent_lx_lx_x_cons_not_in _ _ _ _ _ H1 (Hcon y')).
Qed.

Lemma leb_min_FOv_l_cons_rem : forall l x n,
  ~ l = nil ->
  Nat.leb n (min_FOv_l (cons x l)) = true ->
  Nat.leb n (min_FOv_l l) = true.
Proof.
  intros l [xn] n Hnil Hleb.
  simpl in Hleb. destruct l. contradiction (Hnil eq_refl).
  apply leb_min_r in Hleb. apply Hleb.
Qed.


Lemma is_in_FOvar__l_tff : forall l1 l2 x,
  is_in_FOvar_l l1 l2 = true ->
  is_in_FOvar x l2 = false ->
  is_in_FOvar x l1 = false.
Proof.
  induction l1; intros l2 [xn] H1 H2. reflexivity.
  simpl in *. destruct a as [ym].
  apply if_then_else_ft in H1. destruct H1 as [H1 H3].
  case_eq (beq_nat xn ym); intros Hbeq. rewrite (beq_nat_true _ _ Hbeq) in *.
    rewrite H2 in *. discriminate.
  apply (IHl1 _ _ H3 H2).
Qed.


Lemma decr_strict_FOv_cons2 : forall l xn,
  Nat.leb (S(max_FOv_l l)) xn = true ->
  decr_strict_FOv l = true ->
  decr_strict_FOv (cons (Var xn) l) = true.
Proof.
  induction l; intros xn H1 H2. reflexivity.
  simpl in *. destruct a as [ym].
  destruct xn. discriminate.
  rewrite H1. destruct l. reflexivity.
  assumption.
Qed.

Lemma decr_strict_FOv_cons_leb : forall l xn,
 ~ l = nil ->
  decr_strict_FOv (cons (Var xn) l) = true ->
  Nat.leb (S (max_FOv_l l)) xn = true.
Proof.
  intros l xn Hnot H.
  rewrite decr_strict_FOv_defn in H.
  apply if_then_else_ft in H. apply H.
  assumption.
Qed. 

Lemma leb_max_FOv_l_is_in_FOvar_l : forall l1 l2,
  is_in_FOvar_l l1 l2 = true ->
  Nat.leb (max_FOv_l l1) (max_FOv_l l2) = true.
Proof.
  induction l1; intros l2 H. reflexivity.
  destruct a as [ym]. simpl in *.
  rewrite <- (max_refl (max_FOv_l l2)).
  apply if_then_else_ft in H. destruct H as [H1 H2].
  apply leb_max_max_gen.
    apply is_in_FOvar_leb_max_FOv_l.
    assumption.

    apply IHl1. assumption.
Qed.

Lemma leb_max_FOv_l_rand7 : forall l l2 xn,
  ~ l2 = nil ->
  decr_strict_FOv (cons (Var xn) l2) = true ->
  is_in_FOvar_l l l2 = true ->
  Nat.leb (S (max_FOv_l l)) xn = true.
Proof.
  intros l l2 xn Hnot Hdec Hin.
  apply decr_strict_FOv_cons_leb in Hdec.
  destruct xn. discriminate.
  simpl in *.
  apply (leb_trans _ _ _ (leb_max_FOv_l_is_in_FOvar_l _ _ Hin) Hdec).
  assumption.
Qed.

(* Gold, I think *)
Lemma rename_FOv_A_rep_FOv_l_num_conn9 : forall n l1 l2 alpha beta ,
  n = length l1 ->
  length l1 = length l2 ->
  Nat.leb  (S(max_FOv (conjSO alpha beta))) (min_FOv_l l2) = true ->
    Nat.leb (S (max_FOv_l l1)) (min_FOv_l l2) = true ->
  is_all_diff_FOv l2 = true ->
  decr_strict_FOv l2 = true ->
  exists l1' l2',
    replace_FOv_l alpha l1 l2 = replace_FOv_l alpha l1' l2' /\
    length l1' = length l2' /\
    Nat.leb  (S(max_FOv (conjSO alpha beta))) (min_FOv_l l2') = true /\
    Nat.leb (S (max_FOv_l l1')) (min_FOv_l l2') = true /\
    is_all_diff_FOv l2' = true /\
    decr_strict_FOv l2' = true /\
    consistent_lx_lx l1' l2' /\
    is_in_FOvar_l l2' l2 = true /\
    is_in_FOvar_l l1' l1 = true.
Proof.
  induction n; intros l1 l2 alpha beta Hn Hl Hleb Hleb2 Hall Hdec.
    destruct l1. 2 : discriminate.
    destruct l2; discriminate.

    destruct l1. discriminate.
    destruct l2. discriminate.

    simpl replace_FOv_l.
case_eq l2.
  intros Hnil. rewrite Hnil in *. destruct l1. 2 : discriminate.
  simpl in *. exists (cons f nil). exists (cons f0 nil).
  simpl. apply conj.
    reflexivity.
    apply conj. reflexivity.
    apply conj. destruct f0. destruct n0. discriminate. assumption.
    apply conj. destruct f0. assumption.
    apply conj. reflexivity.
    apply conj. reflexivity.
    apply conj. apply consistent_lx_lx_cons_nil.
    apply conj. destruct f0. rewrite <- beq_nat_refl. reflexivity.
    destruct f. rewrite <-beq_nat_refl. reflexivity.
intros xx lxx Hlxx. rewrite <- Hlxx.  
assert (~ l2 = nil) as Hass0.
  rewrite Hlxx. discriminate.
    destruct (IHn l1 l2 alpha beta) as [l1' [l2' [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 H9]]]]]]]]]].
simpl in Hn. inversion Hn. reflexivity.

simpl in Hl. inversion Hl. reflexivity.

apply leb_min_FOv_l_cons_rem in Hleb; assumption.

apply leb_min_FOv_l_cons_rem in Hleb2; try assumption.
case_eq (min_FOv_l l2). intros Hnil. rewrite Hnil in *. discriminate.
intros mm Hmm. rewrite Hmm in Hleb2. simpl in Hleb2.
destruct f. apply leb_max in Hleb2. apply Hleb2.

simpl in Hall. case_eq (is_in_FOvar f0 l2); intros Hin; rewrite Hin in *.
discriminate. assumption.

apply decr_strict_FOv_cons in Hdec. assumption.

assert (is_in_FOvar f l2 = false) as Hass.
    destruct f as [un].
    apply is_in_FOvar_min_FOv_l with (n := un).
    apply leb_max_FOv_l_rand5 in Hleb2.
    assumption. assumption.
    apply leb_refl.
case_eq (is_in_FOvar f l1); intros Hin.
  rewrite rep_FOv__l_not_in.
  exists l1'. exists l2'.
  apply conj. assumption.
  apply conj. assumption.
  apply conj. assumption.
  apply conj. assumption.
  apply conj. assumption.
  apply conj. assumption.
  apply conj. assumption.
  apply conj;
    apply is_in_FOvar_l_cons_r2.
    all : try assumption.
      simpl in Hl. inversion Hl. reflexivity.
  exists (cons f l1'). exists (cons f0 l2').
  apply conj. simpl. rewrite H1. reflexivity.
  apply conj. simpl. rewrite H2. reflexivity.
  apply conj.  apply leb_min_FOv_l_is_in_FOvar_l
    with (l := l2); assumption.
  assert (is_in_FOvar_l (f0 :: l2') (f0 :: l2) = true) as Hass4.
    destruct f0. simpl. rewrite <- beq_nat_refl.
    apply is_in_FOvar_l_cons_r2. assumption.
  apply conj.
    apply leb_max_FOv_l_rand6 with (l1 := l1) (l2 := l2);
    assumption.
  apply conj.
    apply (is_all_diff_FOv_is_in_FOvar_l _ (cons f0 l2));
    try assumption.
    apply decr_strict_FOv_cons2. destruct f0 as [un].
    apply leb_max_FOv_l_rand7 with (l2 := l2); try assumption.
    assumption.

  apply conj.
    apply decr_strict_FOv_cons2. destruct f0 as [un].
    apply leb_max_FOv_l_rand7 with (l2 := l2); try assumption.
    assumption.
(* 
    apply (decr_strict_FOv_is_in_FOvar_l _ (cons f0 l2)); 
    assumption.
 *)  apply conj.
    assert (is_in_FOvar f l1' = false) as Hass2.
      apply (is_in_FOvar__l_tff _ _ _ H9 Hin).
    assert (is_in_FOvar f0 l2 = false) as Hass5.
      simpl in Hall. case_eq (is_in_FOvar f0 l2); intros Hinn;
      rewrite Hinn in *. discriminate. reflexivity.
    assert (is_in_FOvar f0 l2' = false) as Hass3.
      apply (is_in_FOvar__l_tff _ _ _ H8 Hass5).

    apply consistent_lx_lx_cons_not_in; assumption.
  apply conj. assumption.
  destruct f. simpl. rewrite <- beq_nat_refl.
  apply is_in_FOvar_l_cons_r2. assumption.
Qed.

(* Gold, I think *)
Lemma rename_FOv_A_rep_FOv_l9 : forall l1 l2 alpha beta ,
  length l1 = length l2 ->
  Nat.leb  (S(max_FOv (conjSO alpha beta))) (min_FOv_l l2) = true ->
    Nat.leb (S (max_FOv_l l1)) (min_FOv_l l2) = true ->
  is_all_diff_FOv l2 = true ->
  decr_strict_FOv l2 = true ->
  exists l1' l2',
    replace_FOv_l alpha l1 l2 = replace_FOv_l alpha l1' l2' /\
    length l1' = length l2' /\
    Nat.leb  (S(max_FOv (conjSO alpha beta))) (min_FOv_l l2') = true /\
    Nat.leb (S (max_FOv_l l1')) (min_FOv_l l2') = true /\
    is_all_diff_FOv l2' = true /\
    decr_strict_FOv l2' = true /\
    consistent_lx_lx l1' l2' /\
    is_in_FOvar_l l2' l2 = true /\
    is_in_FOvar_l l1' l1 = true.
Proof.
  intros until 0.
  apply (rename_FOv_A_rep_FOv_l_num_conn9 (length l1) _ _ _ _ (eq_refl)).
Qed.

