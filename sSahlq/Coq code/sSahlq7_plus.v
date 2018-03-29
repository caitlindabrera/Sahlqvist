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
Require Import sSahlq6_plus_2.


(* Second half of sSahlq6_plus. (First half is sSahlq6_plus_2.) *)
(* Search "consistent_lP_lpa". *)

Lemma ind_pa_nil  : forall (W : Set) l,
  @ind_pa W l nil = constant_l pa_f (length l).
Proof.
  induction l. reflexivity.
  simpl. rewrite IHl. destruct a. reflexivity.
  simpl. destruct a; reflexivity.
Qed.

Lemma tryA : forall (W:Set) lP lpa P pa n,
  ind_pa (indicies_l2 lP P) 
      lpa = constant_l pa n <->
  (@ind_gen (W -> Prop) pa_f (indicies_l2 lP P) 
      lpa = constant_l pa n).
Proof.
  intros W. induction lP; intros lpa [Pn] pa n. simpl. apply iff_refl.
  unfold indicies_l2 in *. simpl in *. destruct a as [Qm].
  case_eq (beq_nat Pn Qm); intros Hbeq.
    simpl. destruct lpa. rewrite ind_pa_nil. rewrite ind_gen_nil.
      apply iff_refl.
    simpl. rewrite ind_gen_pre_cons. rewrite ind_pa_pre_cons.
    destruct n. split; discriminate. simpl.
      split; intros H; inversion H as [[H1 H2]]. rewrite H2.
        rewrite IHlP in H2. rewrite H2. reflexivity.

        destruct (IHlP lpa (Pred Pn) pa n) as [fwd rev].
        rewrite rev in *. rewrite H2 in *. reflexivity.
        all : try assumption.

    simpl. destruct lpa. rewrite ind_pa_nil. rewrite ind_gen_nil.
      apply iff_refl.
    simpl. rewrite ind_gen_pre_cons. rewrite ind_pa_pre_cons.
    apply IHlP.
Qed.

Lemma try3 : forall (W:Set) lP lpa P,
  (exists n pa, ind_pa (indicies_l2 lP P) 
      lpa = constant_l pa n) <->
  ( exists n pa, @ind_gen (W -> Prop) pa_f (indicies_l2 lP P) 
      lpa = constant_l pa n).
Proof.
  intros. split; intros [n [pa HH]]; apply tryA in HH; exists n; exists pa;
  assumption.
Qed.

Lemma try2 : forall (W:Set) lP lpa,
  (forall P, exists n pa, ind_pa (indicies_l2 lP P) 
      lpa = constant_l pa n) <->
  (forall P, exists n pa, @ind_gen (W -> Prop) pa_f (indicies_l2 lP P) 
      lpa = constant_l pa n).
Proof.
  intros W lP lpa. split; intros H P; apply try3; apply H.
Qed.

Lemma try4 : forall W lP lpa pa0,
  @consistent_lP_lpa W pa0 lP lpa <->
(forall P, exists n pa, @ind_gen _ pa0 (indicies_l2 lP P) lpa = constant_l pa n) .
Proof.
  unfold consistent_lP_lpa. unfold consistent_lP_lpa_P.
  unfold is_constant. intros. split; intros H P; specialize (H P).
    destruct H as [pa [n H]]. exists n. exists pa. assumption.

    destruct H as [pa [n H]]. exists n. exists pa. assumption.
Qed.

Lemma try5 : forall W lP lpa,
  @consistent_lP_lpa W pa_f lP lpa <->
(forall P, exists n pa, ind_pa (indicies_l2 lP P) 
      lpa = constant_l pa n).
Proof.
  intros. split; intros HH.
    apply try2. apply try4. assumption.

    apply try4. apply try2. assumption.
Qed.

Lemma try : forall W lP lpa pa0,
  @consistent_lP_lpa W pa0 lP lpa <->
(forall P, exists n pa, @ind_gen _ pa0 (indicies_l2 lP P) lpa = constant_l pa n) .
Proof.
Admitted.
(* commented 28/03
 intros W. induction lP; intros lpa pa0; unfold consistent_lP_lpa;
    unfold consistent_lP_lpa_P.
    split; intros H P. exists 0. exists pa_t. reflexivity.
      simpl. apply is_constant_nil. apply pa_t.

    destruct a as [Qm]. unfold indicies_l2 in *.  simpl.
    split; intros H [Pn]; specialize (H (Pred Pn)).
      simpl in *. case_eq (beq_nat Pn Qm); intros Hbeq;
        rewrite Hbeq in *. simpl in *. destruct lpa.
          unfold is_constant in *. destruct H as [pa1 [n1 H1]].
          rewrite H1. exists n1. exists pa1. reflexivity.

          unfold is_constant in *. destruct H as [pa2 [n2 H2]].
          rewrite ind_gen_pre_cons in *.
          simpl in *.
          destruct n1. discriminate. rewrite ind_gen_nil in *.
          rewrite H1. exists pa1. (S 
          simpl in H1. inversion H1 as [[H3 H2]].
          

 destruct n1. rewr 2 : discriminate.
        exists 1. exists pa_f. simpl in *.

Search ind_gen nil.
 destruct lP. reflexivity.
        simpl.
        simpl.


 ; unfold constant_l; unfold is_constant.
    simpl.
*)

Lemma is_in_FOvar_l_app_cons_nil : forall l2 l x,
  is_in_FOvar_l (app l (cons x nil)) l2 = 
  is_in_FOvar_l (cons x l) l2.
Admitted.

Lemma rename_FOv_A_rep_FOv_l : forall lv alpha beta,
  is_in_FOvar (Var 0) lv = false ->
  ~ lv = nil ->
  exists l1 l2,
  rename_FOv_A alpha beta lv = replace_FOv_l alpha l1 l2 /\
  length l1 = length l2 /\
  Nat.leb  (S(max_FOv (conjSO alpha beta))) (min_FOv_l l2) = true.
Proof.
  intros lv alpha beta. apply (rename_FOv_A_rep_FOv_l_num_conn (length lv) _ _ _ eq_refl).
Qed.

Lemma rename_FOv_A_rep_FOv_l2 : forall lv alpha beta,
  is_in_FOvar (Var 0) lv = false ->
  ~ lv = nil ->
  exists l1 l2,
  rename_FOv_A alpha beta lv = replace_FOv_l alpha l1 l2 /\
  length l1 = length l2 /\
  Nat.leb  (S(max_FOv (conjSO alpha beta))) (min_FOv_l l2) = true /\
 is_all_diff_FOv l2 = true.
Proof.
  intros lv alpha beta. apply (rename_FOv_A_rep_FOv_l_num_conn2 (length lv) _ _ _ eq_refl).
Qed.

Lemma min_FOv_l_cons : forall l n,
~ l = nil ->
  min_FOv_l (cons (Var n) l) = min n (min_FOv_l l).
Proof.
  intros l n H. destruct l. contradiction (H eq_refl).
  reflexivity.
Qed. 

Lemma leb_min_rev : forall n m1 m2,
  Nat.leb n m1 = true ->
  Nat.leb n m2 = true ->
  Nat.leb n (min m1 m2) = true.
Proof.
  induction n; intros m1 m2 H1 H2. reflexivity.
  simpl. case_eq (min m1 m2). intros H. destruct m1. discriminate.
  destruct m2; discriminate.

  intros mm Hmm. destruct m1. discriminate.
  destruct m2. discriminate.
  simpl in Hmm. inversion Hmm as [Hmm'].
  apply IHn; assumption.
Qed.

Lemma max_FOv_l_app_cons_nil : forall l1 xn,
max_FOv_l (app l1 (cons (Var xn) nil)) = max (max_FOv_l l1) xn.
Admitted.

Lemma rep_FOv_l_conjSO : forall l1 l2 alpha beta,
  replace_FOv_l (conjSO alpha beta) l1 l2 = 
  conjSO (replace_FOv_l alpha l1 l2) (replace_FOv_l beta l1 l2).
Proof.
  induction l1; intros l2 alpha beta. reflexivity.
  simpl in *. destruct l2. reflexivity.
  rewrite IHl1. simpl. destruct a. reflexivity.
Qed.

Lemma rep_FOv_l_disjSO : forall l1 l2 alpha beta,
  replace_FOv_l (disjSO alpha beta) l1 l2 = 
  disjSO (replace_FOv_l alpha l1 l2) (replace_FOv_l beta l1 l2).
Proof.
  induction l1; intros l2 alpha beta. reflexivity.
  simpl in *. destruct l2. reflexivity.
  rewrite IHl1. simpl. destruct a. reflexivity.
Qed.

Lemma rep_FOv_l_implSO : forall l1 l2 alpha beta,
  replace_FOv_l (implSO alpha beta) l1 l2 = 
  implSO (replace_FOv_l alpha l1 l2) (replace_FOv_l beta l1 l2).
Proof.
  induction l1; intros l2 alpha beta. reflexivity.
  simpl in *. destruct l2. reflexivity.
  rewrite IHl1. simpl. destruct a. reflexivity.
Qed.



Lemma leb_min_FOv_l_cons_l : forall l x,
  Nat.leb (min_FOv_l (cons x l)) (min_FOv_l l) = true.
Admitted.

Lemma rep_FOv_l_predSO_ex  : forall l1 l2 P x,
  exists y,
  replace_FOv_l (predSO P x) l1 l2 = predSO P y.
Proof.
  induction l1; intros l2 P x. simpl. exists x. reflexivity.
  simpl. destruct l2. exists x. reflexivity.
  destruct (IHl1 l2 P x) as [y H].
  rewrite H. destruct y as [ym]. destruct a as [xn].
  simpl. destruct P as [Pn]. case_eq (beq_nat xn ym);
    intros Hbeq. exists f. reflexivity.
    exists (Var ym). reflexivity.
Qed.

Lemma rep_FOv_l_relatSO_ex  : forall l1 l2 x y,
  exists x' y',
  replace_FOv_l (relatSO x y) l1 l2 = relatSO x' y'.
Proof.
  induction l1; intros l2 [xn] [ym]. simpl.
    exists (Var xn). exists (Var ym). reflexivity.
  simpl. destruct l2.
    exists (Var xn). exists (Var ym). reflexivity.
  destruct (IHl1 l2 (Var xn) (Var ym)) as [[xn'] [[ym'] H]].
  rewrite H. destruct a as [zn].
  simpl. case_eq (beq_nat zn xn');
    intros Hbeq; [exists f | exists (Var xn')];
    (case_eq (beq_nat zn ym'); intros Hbeq2;
      [exists f | exists (Var ym')]); try reflexivity.
Qed.

Lemma rep_FOv_l_eqFO_ex  : forall l1 l2 x y,
  exists x' y',
  replace_FOv_l (eqFO x y) l1 l2 = eqFO x' y'.
Proof.
  induction l1; intros l2 [xn] [ym]. simpl.
    exists (Var xn). exists (Var ym). reflexivity.
  simpl. destruct l2.
    exists (Var xn). exists (Var ym). reflexivity.
  destruct (IHl1 l2 (Var xn) (Var ym)) as [[xn'] [[ym'] H]].
  rewrite H. destruct a as [zn].
  simpl. case_eq (beq_nat zn xn');
    intros Hbeq; [exists f | exists (Var xn')];
    (case_eq (beq_nat zn ym'); intros Hbeq2;
      [exists f | exists (Var ym')]); try reflexivity.
Qed.

Lemma is_all_diff_FOv2_calc_llv_P_rename_FOv_A_pre_allFO : forall l1 l2 atm f  P,
(forall l1 l2 : list FOvariable,
        length l1 = length l2 ->
        is_all_diff_FOv l2 = true ->
        Nat.leb (S (max_FOv atm)) (min_FOv_l l2) = true ->
        (forall P : predicate, is_all_diff_FOv2 (calc_llv_P atm P) = true) ->
        forall P : predicate, is_all_diff_FOv2 (calc_llv_P (replace_FOv_l atm l1 l2) P) = true) ->
  length l1 = length l2 ->
  is_all_diff_FOv l2 = true ->
  Nat.leb (S (max_FOv (allFO f atm))) (min_FOv_l l2) = true ->
  (forall P : predicate, is_all_diff_FOv2 (calc_llv_P (allFO f atm) P) = true) ->
is_all_diff_FOv2 (calc_llv_P (replace_FOv_l (allFO f atm) l1 l2) P) = true.
Proof.
  intros until 0. intros IH Hl Hall Hleb Hall2.
  assert (Nat.leb (S (max_FOv atm)) (min_FOv_l l2) = true) as Hleb2.
    simpl in *.
    case_eq (min_FOv_l l2). intros Hnil. rewrite Hnil in *.
      discriminate.
    intros m Hm. rewrite Hm in *. destruct f as [zn].
      apply leb_max in Hleb.
      apply Hleb.
  specialize (IH _ _ Hl Hall Hleb2).



  simpl calc_llv_P in Hall2.
  destruct atm; try discriminate.
Admitted.







(*   induction l1; intros l2 atm f P IH Hl Hall Hleb Hall2. simpl.
    destruct l2; discriminate.
  destruct l2. discriminate.
  destruct atm; try discriminate.
 *)  

Lemma rep_FOv_l_negSO : forall l1 l2 atm,
  replace_FOv_l (negSO atm) l1 l2 = negSO (replace_FOv_l atm l1 l2).
Proof.
  induction l1; intros l2 atm. reflexivity.
  simpl. destruct l2. reflexivity.
  rewrite IHl1. simpl. destruct a. reflexivity.
Qed.

Lemma calc_llv_P_rep_FOv_l_allFO_branch_t : forall l1 l2 atm x P,
  P_branch_allFO (replace_FOv_l (allFO x atm) l1 l2) P = true ->
  calc_llv_P (replace_FOv_l (allFO x atm) l1 l2) P =
  cons (comp_cond_lx2 (replace_FOv_l (allFO x atm) l1 l2)) nil.
Admitted.

Lemma calc_llv_P_rep_FOv_l_allFO_branch_f : forall l1 l2 atm x P,
  P_branch_allFO (replace_FOv_l (allFO x atm) l1 l2) P = false ->
  calc_llv_P (replace_FOv_l (allFO x atm) l1 l2) P = nil.
Admitted.

Lemma calc_llv_P_allFO_branch_t : forall atm x P,
  P_branch_allFO (allFO x atm) P = true ->
  calc_llv_P (allFO x atm) P =
  cons (comp_cond_lx2 (allFO x atm)) nil.
Admitted.

Lemma calc_llv_P_allFO_branch_f : forall atm x P,
  P_branch_allFO (allFO x atm) P = false ->
  calc_llv_P (allFO x atm) P = nil.
Admitted.

Fixpoint of_form_predSO alpha : bool :=
  match alpha with
  | predSO  _ _ => true
  | _ => false
  end.

Fixpoint of_form_allFO alpha : bool :=
  match alpha with
  | allFO  _ _ => true
  | _ => false
  end.

Fixpoint of_form_implSO alpha : bool :=
  match alpha with
  | implSO  _ _ => true
  | _ => false
  end.

 Lemma of_form_implSO_match : forall {B : Type} alpha (b1 : SecOrder -> B) (b2 : B),
  of_form_implSO alpha = false ->
  match alpha with
  | implSO beta1 beta2 => b1 beta2
  | _ => b2
  end = b2.
Proof.
  intros until 0. intros H.
  destruct alpha; try reflexivity.
  discriminate.
Qed. 

Lemma of_form_implSO_rep_FOv : forall alpha x y,
  of_form_implSO (replace_FOv alpha x y) =
  of_form_implSO alpha.
Proof.
  induction alpha; intros [xn] [ym]; try reflexivity.
    simpl. destruct p. destruct f as [zn].
    case_eq (beq_nat xn zn); intros Hbeq; reflexivity.

    destruct f as [z1]; destruct f0 as [z2].
    simpl. case_eq (beq_nat xn z1); intros Hbeq;
      case_eq (beq_nat xn z2); intros Hbeq2; reflexivity.

    destruct f as [z1]; destruct f0 as [z2].
    simpl. case_eq (beq_nat xn z1); intros Hbeq;
      case_eq (beq_nat xn z2); intros Hbeq2; reflexivity.

    destruct f as [zn]. simpl.
    case_eq (beq_nat xn zn); intros Hbeq; reflexivity.

    destruct f as [zn]. simpl.
    case_eq (beq_nat xn zn); intros Hbeq; reflexivity.

    destruct p. reflexivity.

    destruct p. reflexivity.
Qed.

Lemma P_branch_allFO_rep_FOv_num_conn : forall m n alpha x y P,
      n = num_conn alpha ->
      Nat.leb n m = true ->
  P_branch_allFO (replace_FOv alpha x y) P =
  P_branch_allFO alpha P.
Proof.
  induction m; intros n alpha [xn] [ym] [Pn] Hnum Hleb.
    destruct n. 2 : discriminate.
    destruct alpha; try discriminate.

      simpl. destruct p as [Qm]. destruct f as [zn].
      case_eq (beq_nat xn zn); intros Hbeq;
        reflexivity.

      destruct f as [z1]. destruct f0 as [z2].
      simpl. case_eq (beq_nat xn z1); case_eq (beq_nat xn z2);
        reflexivity.

      destruct f as [z1]. destruct f0 as [z2].
      simpl. case_eq (beq_nat xn z1); case_eq (beq_nat xn z2);
        reflexivity.

    destruct n. 
    destruct alpha; try discriminate.

      simpl. destruct p as [Qm]. destruct f as [zn].
      case_eq (beq_nat xn zn); intros Hbeq;
        reflexivity.

      destruct f as [z1]. destruct f0 as [z2].
      simpl. case_eq (beq_nat xn z1); case_eq (beq_nat xn z2);
        reflexivity.

      destruct f as [z1]. destruct f0 as [z2].
      simpl. case_eq (beq_nat xn z1); case_eq (beq_nat xn z2);
        reflexivity.

    destruct alpha; try discriminate; try reflexivity.
    simpl. destruct f as [zn].
    simpl in Hnum. inversion Hnum as [Hnum'].
    rewrite Hnum' in *. simpl in Hleb.
    case_eq (beq_nat xn zn); intros Hbeq.
      simpl. case_eq (of_form_implSO alpha); intros Hof.
        destruct alpha; try discriminate.
        simpl. apply (IHm (num_conn alpha2) alpha2).
        reflexivity.

                destruct m.
        discriminate. apply leb_plus_take2 in Hleb.
        apply leb_suc_r. assumption.


        rewrite (of_form_implSO_match alpha).
        rewrite of_form_implSO_match. reflexivity.
        rewrite of_form_implSO_rep_FOv.
        all : try assumption.

      simpl. case_eq (of_form_implSO alpha); intros Hof.
        destruct alpha; try discriminate.
        simpl. apply (IHm (num_conn alpha2) alpha2).
        reflexivity.

        destruct m.
        discriminate. apply leb_plus_take2 in Hleb.
        apply leb_suc_r. assumption.

        rewrite (of_form_implSO_match alpha).
        rewrite of_form_implSO_match. reflexivity.
        rewrite of_form_implSO_rep_FOv.
        all : try assumption.

      destruct f as [zn]. simpl. case_eq (beq_nat xn zn); reflexivity.

      destruct p. reflexivity.

      destruct p. reflexivity.
Qed.

Lemma P_branch_allFO_rep_FOv : forall alpha x y P,
  P_branch_allFO (replace_FOv alpha x y) P =
  P_branch_allFO alpha P.
Proof.
  intros alpha x y P.
  apply (P_branch_allFO_rep_FOv_num_conn (num_conn alpha) (num_conn alpha)).
  reflexivity. apply leb_refl.
Qed.

Lemma P_branch_allFO_rep_FOv_l : forall l1 l2 alpha P,
  P_branch_allFO (replace_FOv_l alpha l1 l2) P =
  P_branch_allFO alpha P.
Admitted.

Lemma is_all_diff_FOv_cons : forall l' y,
  is_all_diff_FOv (cons y l') =
 if is_in_FOvar y l' then false else is_all_diff_FOv l'.
Proof.
  reflexivity.
Qed.

Lemma comp_cond_lx2_rep_FOv_num_conn_allFO1 : forall m n alpha1 alpha2 zn ym vn,
(forall (n : nat) (alpha : SecOrder) (z y : FOvariable),
      n = num_conn alpha ->
      Nat.leb n m = true ->
      is_in_FOvar z (comp_cond_lx2 alpha) = false ->
      comp_cond_lx2 (replace_FOv alpha z y) = comp_cond_lx2 alpha) ->
S n = num_conn (allFO (Var vn) (implSO alpha1 alpha2)) ->
Nat.leb (S n) (S m) = true ->
is_in_FOvar (Var zn) (comp_cond_lx2 (allFO (Var vn) (implSO alpha1 alpha2))) = false ->
PeanoNat.Nat.eqb zn vn = true ->
comp_cond_lx2 (allFO (Var ym) (replace_FOv (implSO alpha1 alpha2) (Var zn) (Var ym))) =
comp_cond_lx2 (allFO (Var vn) (implSO alpha1 alpha2)).
Proof.
  intros m n alpha1 alpha2 zn ym vn IH Hnum Hleb Hin Hbeq.
  remember alpha2 as t. rewrite Heqt in *.
  destruct alpha2;
    try (simpl in *; rewrite Hbeq in Hin; discriminate).

    simpl. destruct p. destruct f as [xn].
    case_eq (beq_nat zn xn); reflexivity.
Qed.

Lemma comp_cond_lx2_rep_FOv_num_conn_allFO2 : forall m n alpha1 alpha2 zn ym vn,
(forall (n : nat) (alpha : SecOrder) (z y : FOvariable),
      n = num_conn alpha ->
      Nat.leb n m = true ->
      is_in_FOvar z (comp_cond_lx2 alpha) = false ->
      comp_cond_lx2 (replace_FOv alpha z y) = comp_cond_lx2 alpha) ->
S n = num_conn (allFO (Var vn) (implSO alpha1 alpha2)) ->
Nat.leb (S n) (S m) = true ->
is_in_FOvar (Var zn) (comp_cond_lx2 (allFO (Var vn) (implSO alpha1 alpha2))) = false ->
PeanoNat.Nat.eqb zn vn = false ->
comp_cond_lx2 (allFO (Var vn) (replace_FOv (implSO alpha1 alpha2) (Var zn) (Var ym))) =
comp_cond_lx2 (allFO (Var vn) (implSO alpha1 alpha2)).
Proof.
  intros m n alpha1 alpha2 zn ym vn IH Hnum Hleb Hin Hbeq.
  remember alpha2 as t. rewrite Heqt in *.
  destruct alpha2.
    simpl. destruct p. destruct f as [xn].
    case_eq (beq_nat zn xn); reflexivity.

    destruct f as [u1]. destruct f0 as [u2].
    simpl. case_eq (beq_nat zn u1); intros Hbeq3;
      case_eq (beq_nat zn u2); intros Hbeq2; reflexivity.

    destruct f as [u1]. destruct f0 as [u2].
    simpl. case_eq (beq_nat zn u1); intros Hbeq3;
      case_eq (beq_nat zn u2); intros Hbeq2; reflexivity.

    destruct f as [u1]. rewrite <- Heqt. simpl.
    rewrite Heqt. simpl replace_FOv.
    case_eq (beq_nat zn u1); intros Hbeq2.
      rewrite <- (IH (num_conn (allFO (Var u1) alpha2))
         (allFO (Var u1) alpha2) (Var zn) (Var ym)).
      simpl. rewrite Hbeq2. all : try reflexivity.

      rewrite <- Heqt in *.
      simpl in Hnum. inversion Hnum as [Hnum'].
      rewrite Hnum' in *. simpl in Hleb. destruct m.
        discriminate. simpl in *.
      apply leb_plus_take2 in Hleb.
      apply leb_suc_r. assumption.

      simpl in *. rewrite Hbeq in *. assumption.

      rewrite <- (IH (num_conn (allFO (Var u1) alpha2))
         (allFO (Var u1) alpha2) (Var zn) (Var ym)).
      simpl. rewrite Hbeq2. all : try reflexivity.

      rewrite <- Heqt in *.
      simpl in Hnum. inversion Hnum as [Hnum'].
      rewrite Hnum' in *. simpl in Hleb. destruct m.
        discriminate. simpl in *.
      apply leb_plus_take2 in Hleb.
      apply leb_suc_r. assumption.
      simpl in *. rewrite Hbeq in *. assumption.

    destruct f as [un]. simpl. case_eq (beq_nat zn un);
      intros Hbeq4; reflexivity.

    destruct p. reflexivity.

    destruct p. reflexivity.
Qed.

Lemma comp_cond_lx2_rep_FOv_num_conn : forall m n alpha z y,
      n = num_conn alpha ->
      Nat.leb n m = true ->
  is_in_FOvar z (comp_cond_lx2 alpha) = false ->
  comp_cond_lx2 (replace_FOv alpha z y) = comp_cond_lx2 alpha.
Proof.
  induction m; intros n alpha [zn] [ym] Hnum Hleb Hin.
    destruct n. 2 : discriminate.
    destruct alpha; try discriminate.
      simpl. destruct p. destruct f as [xn].
      case_eq (beq_nat zn xn); reflexivity.

      destruct f as [u1]. destruct f0 as [u2].
      simpl. case_eq (beq_nat zn u1); intros Hbeq;
        case_eq (beq_nat zn u2); intros Hbeq2; reflexivity.

      destruct f as [u1]. destruct f0 as [u2].
      simpl. case_eq (beq_nat zn u1); intros Hbeq;
        case_eq (beq_nat zn u2); intros Hbeq2; reflexivity.

    destruct n.
    destruct alpha; try discriminate.
      simpl. destruct p. destruct f as [xn].
      case_eq (beq_nat zn xn); reflexivity.

      destruct f as [u1]. destruct f0 as [u2].
      simpl. case_eq (beq_nat zn u1); intros Hbeq;
        case_eq (beq_nat zn u2); intros Hbeq2; reflexivity.

      destruct f as [u1]. destruct f0 as [u2].
      simpl. case_eq (beq_nat zn u1); intros Hbeq;
        case_eq (beq_nat zn u2); intros Hbeq2; reflexivity.

    destruct alpha; try discriminate; try reflexivity.
(* -- *)
      destruct f as [vn]. simpl replace_FOv.
      case_eq (beq_nat zn vn); intros Hbeq.
        simpl. destruct alpha; try discriminate; try reflexivity.

        simpl. destruct p. destruct f as [xn].
        case_eq (beq_nat zn xn); reflexivity.

        destruct f as [u1]. destruct f0 as [u2].
        simpl. case_eq (beq_nat zn u1); intros Hbeq2;
          case_eq (beq_nat zn u2); intros Hbeq3; reflexivity.

        destruct f as [u1]. destruct f0 as [u2].
        simpl. case_eq (beq_nat zn u1); intros Hbeq2;
          case_eq (beq_nat zn u2); intros Hbeq3; reflexivity.

        simpl. destruct f as [xn].
        case_eq (beq_nat zn xn); reflexivity.

        simpl. destruct f as [xn].
        case_eq (beq_nat zn xn); reflexivity.

        apply comp_cond_lx2_rep_FOv_num_conn_allFO1 with (m := m) (n := n) (alpha1 := alpha1);
          try assumption.

        destruct p. reflexivity.
        destruct p. reflexivity.

        simpl. destruct alpha; try discriminate; try reflexivity.

        simpl. destruct p. destruct f as [xn].
        case_eq (beq_nat zn xn); reflexivity.

        destruct f as [u1]. destruct f0 as [u2].
        simpl. case_eq (beq_nat zn u1); intros Hbeq2;
          case_eq (beq_nat zn u2); intros Hbeq3; reflexivity.

        destruct f as [u1]. destruct f0 as [u2].
        simpl. case_eq (beq_nat zn u1); intros Hbeq2;
          case_eq (beq_nat zn u2); intros Hbeq3; reflexivity.

        simpl. destruct f as [xn].
        case_eq (beq_nat zn xn); reflexivity.

        simpl. destruct f as [xn].
        case_eq (beq_nat zn xn); reflexivity.

        apply comp_cond_lx2_rep_FOv_num_conn_allFO2 with (m := m) (n := n) (alpha1 := alpha1);
          assumption.

        destruct p. reflexivity.
        destruct p. reflexivity.

(* -- *)
      destruct f as [xn]. simpl in *.
      case_eq (beq_nat zn xn); reflexivity.

      destruct p; reflexivity. 
      destruct p; reflexivity.
Qed.

Lemma comp_cond_lx2_rep_FOv : forall alpha z y,
  is_in_FOvar z (comp_cond_lx2 alpha) = false ->
  comp_cond_lx2 (replace_FOv alpha z y) = comp_cond_lx2 alpha.
Proof.
  intros until 0.
  apply (comp_cond_lx2_rep_FOv_num_conn (num_conn alpha) (num_conn alpha)
    alpha _ _ eq_refl (leb_refl _)).
Qed.


Lemma is_in_FOvar_l_comp_cond_lx2_num_conn : forall m n  alpha,
      n = num_conn alpha ->
      Nat.leb n m = true ->
  is_in_FOvar_l (comp_cond_lx2 alpha) (FOvars_in alpha) = true.
Proof.
  induction m; intros n alpha Hnum Hleb.
    destruct n. 2 : discriminate.
    destruct alpha; try discriminate; try reflexivity.

    destruct n.
    destruct alpha; try discriminate; try reflexivity.

    destruct alpha; try discriminate; try reflexivity.
      destruct alpha; try reflexivity.
      destruct alpha2; try reflexivity;
        try (simpl; destruct f; rewrite <- beq_nat_refl; reflexivity).

        remember (allFO f0 alpha2) as t.
        simpl. rewrite Heqt. rewrite <- Heqt.
        simpl. destruct f as [zn]. rewrite <- beq_nat_refl.
        apply is_in_FOvar_l_cons_r2.
        apply is_in_FOvar_l_app_r1. apply (IHm (num_conn t) t).
          reflexivity. 

        
    simpl in Hnum.
    inversion Hnum as [Hnum'].
    rewrite Hnum' in Hleb.
    destruct m. discriminate. apply leb_suc_r.
    simpl in *. apply leb_plus_take2 in Hleb. assumption.
Qed.

Lemma is_in_FOvar_l_comp_cond_lx2 : forall alpha,
  is_in_FOvar_l (comp_cond_lx2 alpha) (FOvars_in alpha) = true.
Proof.
  intros alpha.
  apply (is_in_FOvar_l_comp_cond_lx2_num_conn
     (num_conn alpha) (num_conn alpha) alpha eq_refl (leb_refl _ )).
Qed.

Lemma is_in_FOvar_comp_cond_lx2_rep_FOv_num_conn  : forall m n alpha x y z,
      n = num_conn alpha ->
      Nat.leb n m = true ->
  ~ x = z ->
  is_in_FOvar x (comp_cond_lx2 alpha) = false ->
  is_in_FOvar x (comp_cond_lx2 (replace_FOv alpha y z)) = false.
Proof.
  induction m; intros n alpha [xn] [ym] [zn] Hnum Hleb Hneq H.
    destruct n. 2 : discriminate.
    destruct alpha; try discriminate.
      simpl. destruct p. destruct f as [un].
      case_eq (beq_nat ym un); reflexivity.

      destruct f as [u1]. destruct f0 as [u2].
      simpl. case_eq (beq_nat ym u1); intros Hbeq;
        case_eq (beq_nat ym u2); intros Hbeq2; reflexivity.

      destruct f as [u1]. destruct f0 as [u2].
      simpl. case_eq (beq_nat ym u1); intros Hbeq;
        case_eq (beq_nat ym u2); intros Hbeq2; reflexivity.

    destruct n. 
    destruct alpha; try discriminate.
      simpl. destruct p. destruct f as [un].
      case_eq (beq_nat ym un); reflexivity.

      destruct f as [u1]. destruct f0 as [u2].
      simpl. case_eq (beq_nat ym u1); intros Hbeq;
        case_eq (beq_nat ym u2); intros Hbeq2; reflexivity.

      destruct f as [u1]. destruct f0 as [u2].
      simpl. case_eq (beq_nat ym u1); intros Hbeq;
        case_eq (beq_nat ym u2); intros Hbeq2; reflexivity.

    destruct alpha; try discriminate; try reflexivity.
(* -- *)
      destruct f as [un]. simpl replace_FOv.
      case_eq (beq_nat ym un); intros Hbeq.
        destruct alpha; try reflexivity. 
          destruct p. destruct f as [v1].
          simpl. case_eq (beq_nat ym v1); 
          reflexivity.

          destruct f as [v1]; destruct f0 as [v2];
          simpl. case_eq (beq_nat ym v1);
            case_eq (beq_nat ym v2); reflexivity.

          destruct f as [v1]; destruct f0 as [v2];
          simpl. case_eq (beq_nat ym v1);
            case_eq (beq_nat ym v2); reflexivity.

        destruct f as [v1]; 
        simpl. case_eq (beq_nat ym v1); reflexivity.

        destruct f as [v1]; 
        simpl. case_eq (beq_nat ym v1); reflexivity.

          remember alpha2 as t2. rewrite Heqt2.
          simpl replace_FOv.
          destruct alpha2; try reflexivity; try discriminate.
            simpl. destruct p as [Pn]. destruct f as [u1].
            case_eq (beq_nat ym u1); reflexivity.

    destruct f as [u1]. destruct f0 as [u2].
    simpl. case_eq (beq_nat ym u1); intros Hbeq2;
      case_eq (beq_nat ym u2); intros Hbeq3;
        simpl in *; rewrite Heqt2 in H;
        (rewrite FOvar_neq; [reflexivity | assumption]).

    destruct f as [u1]. destruct f0 as [u2].
    simpl. case_eq (beq_nat ym u1); intros Hbeq2;
      case_eq (beq_nat ym u2); intros Hbeq3;
        simpl in *; rewrite Heqt2 in H;
        (rewrite FOvar_neq; [reflexivity | assumption]).

    simpl in H. rewrite Heqt2 in H. rewrite <- Heqt2 in *.
    simpl in H. case_eq (beq_nat xn un); intros Hbeq2;
      rewrite Hbeq2 in *. discriminate.
    destruct f as [vn]. case_eq (beq_nat ym vn); intros Hbeq3.
      assert (replace_FOv t2 (Var ym) (Var zn) =
        allFO (Var zn) (replace_FOv alpha2 (Var ym) (Var zn))) as Hass.
        rewrite Heqt2. simpl. rewrite Hbeq3. reflexivity.
      simpl. rewrite Hass. rewrite <- Hass.
      simpl. rewrite FOvar_neq.
      apply (IHm (num_conn t2) t2 _ _ _); try assumption.
        reflexivity.

simpl in Hnum. inversion Hnum as [Hnum'].
rewrite Hnum' in *. simpl in Hleb. destruct m. discriminate.
apply leb_plus_take2 in Hleb. apply leb_suc_r. assumption.

      assumption.

      assert (replace_FOv t2 (Var ym) (Var zn) =
        allFO (Var vn) (replace_FOv alpha2 (Var ym) (Var zn))) as Hass.
        rewrite Heqt2. simpl. rewrite Hbeq3. reflexivity.
      simpl. rewrite Hass. rewrite <- Hass.
      simpl. rewrite FOvar_neq.
      apply (IHm (num_conn t2) t2 _ _ _); try assumption.
        reflexivity.
simpl in Hnum. inversion Hnum as [Hnum'].
rewrite Hnum' in *. simpl in Hleb. destruct m. discriminate.
apply leb_plus_take2 in Hleb. apply leb_suc_r. assumption.
      assumption.

    destruct f as [vn]. simpl. case_eq (beq_nat ym vn);
      intros; simpl; rewrite (FOvar_neq _ _ Hneq); reflexivity.

    simpl. rewrite (FOvar_neq _ _ Hneq); reflexivity.

    simpl. rewrite (FOvar_neq _ _ Hneq); reflexivity.

    simpl. rewrite (FOvar_neq _ _ Hneq); reflexivity.

    simpl. rewrite (FOvar_neq _ _ Hneq); reflexivity.

    destruct p. simpl. rewrite (FOvar_neq _ _ Hneq); reflexivity.

    destruct p. simpl. rewrite (FOvar_neq _ _ Hneq); reflexivity.

(* -- *)

    destruct p. simpl. reflexivity.
    destruct p. simpl. reflexivity.

(* ------- *)
        destruct alpha; try reflexivity. 
          destruct p. destruct f as [v1].
          simpl. case_eq (beq_nat ym v1); 
          reflexivity.

          destruct f as [v1]; destruct f0 as [v2];
          simpl. case_eq (beq_nat ym v1);
            case_eq (beq_nat ym v2); reflexivity.

          destruct f as [v1]; destruct f0 as [v2];
          simpl. case_eq (beq_nat ym v1);
            case_eq (beq_nat ym v2); reflexivity.

        destruct f as [v1]; 
        simpl. case_eq (beq_nat ym v1); reflexivity.

        destruct f as [v1]; 
        simpl. case_eq (beq_nat ym v1); reflexivity.

          remember alpha2 as t2. rewrite Heqt2.
          simpl replace_FOv.
          destruct alpha2; try reflexivity; try discriminate.
            simpl. destruct p as [Pn]. destruct f as [u1].
            case_eq (beq_nat ym u1); reflexivity.

    destruct f as [u1]. destruct f0 as [u2].
    simpl. case_eq (beq_nat ym u1); intros Hbeq2;
      case_eq (beq_nat ym u2); intros Hbeq3;
        simpl in *; rewrite Heqt2 in H; assumption.

    destruct f as [u1]. destruct f0 as [u2].
    simpl. case_eq (beq_nat ym u1); intros Hbeq2;
      case_eq (beq_nat ym u2); intros Hbeq3;
        simpl in *; rewrite Heqt2 in H; assumption.

    simpl in H. rewrite Heqt2 in H. rewrite <- Heqt2 in *.
    simpl in H. case_eq (beq_nat xn un); intros Hbeq2;
      rewrite Hbeq2 in *. discriminate.
    destruct f as [vn]. case_eq (beq_nat ym vn); intros Hbeq3.
      assert (replace_FOv t2 (Var ym) (Var zn) =
        allFO (Var zn) (replace_FOv alpha2 (Var ym) (Var zn))) as Hass.
        rewrite Heqt2. simpl. rewrite Hbeq3. reflexivity.
      simpl. rewrite Hass. rewrite <- Hass.
      simpl. rewrite FOvar_neq.
      apply (IHm (num_conn t2) t2 _ _ _); try assumption.
        reflexivity.

simpl in Hnum. inversion Hnum as [Hnum'].
rewrite Hnum' in *. simpl in Hleb. destruct m. discriminate.
apply leb_plus_take2 in Hleb. apply leb_suc_r. assumption.

        apply beq_nat_false_FOv. assumption.

      assert (replace_FOv t2 (Var ym) (Var zn) =
        allFO (Var vn) (replace_FOv alpha2 (Var ym) (Var zn))) as Hass.
        rewrite Heqt2. simpl. rewrite Hbeq3. reflexivity.
      simpl. rewrite Hass. rewrite <- Hass.
      simpl. rewrite FOvar_neq.
      apply (IHm (num_conn t2) t2 _ _ _); try assumption.
        reflexivity.
simpl in Hnum. inversion Hnum as [Hnum'].
rewrite Hnum' in *. simpl in Hleb. destruct m. discriminate.
apply leb_plus_take2 in Hleb. apply leb_suc_r. assumption.

        apply beq_nat_false_FOv. assumption.

    rewrite Heqt2 in H. simpl in H.
    destruct f as [vn]. simpl. case_eq (beq_nat ym vn);
      intros; simpl; assumption.

    rewrite Heqt2 in H. simpl in H.
    simpl. assumption.

    rewrite Heqt2 in H. simpl in H.
    simpl. assumption.

    rewrite Heqt2 in H. simpl in H.
    simpl. assumption.

    rewrite Heqt2 in H. simpl in H.
    simpl. assumption.

    destruct p. simpl.
    rewrite Heqt2 in H. simpl in H.
    simpl. assumption.

    destruct p. simpl.
    rewrite Heqt2 in H. simpl in H.
    simpl. assumption.

(* -- *)

    destruct p. simpl. reflexivity.
    destruct p. simpl. reflexivity.

    destruct f as [vn].
    simpl.
    case_eq (beq_nat ym vn); intros Hbeq; reflexivity.

    destruct p. simpl. reflexivity.
    destruct p. simpl. reflexivity.
Qed.

Lemma is_in_FOvar_comp_cond_lx2_rep_FOv  : forall alpha x y z,
  ~ x = z ->
  is_in_FOvar x (comp_cond_lx2 alpha) = false ->
  is_in_FOvar x (comp_cond_lx2 (replace_FOv alpha y z)) = false.
Proof.
  intros alpha x y z.
  apply (is_in_FOvar_comp_cond_lx2_rep_FOv_num_conn (num_conn alpha)  
    (num_conn alpha) alpha x y z eq_refl (leb_refl _)).
Qed.

Lemma leb_Var_not: forall zn ym,
  Nat.leb zn ym = true ->
  ~ Var zn = Var (S ym).
Proof.
  intros zn ym H H2. inversion H2 as [H3].
  rewrite H3 in *. rewrite leb_suc_f in H. 
  discriminate.
Qed. 

Lemma is_all_diff_FOv_comp_cond_lx2_rep_FOv_num_conn : forall m n atm x ym,
      n = num_conn atm ->
      Nat.leb n m = true ->
Nat.leb (S (max_FOv atm)) ym = true ->
  is_all_diff_FOv (comp_cond_lx2 atm) = true ->
  is_all_diff_FOv (comp_cond_lx2 (replace_FOv atm x (Var ym))) = true.
Proof.
  induction m; intros n atm [xn] ym Hnum Hleb Hleb2 Hall. 
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
      simpl in *. destruct p. destruct f as [zn].
      case_eq (beq_nat xn zn); reflexivity.

      simpl. destruct f as [z1]. destruct f0 as [z2].
      case_eq (beq_nat xn z1); intros Hbeq; 
        case_eq (beq_nat xn z2); intros Hbeq2; reflexivity.

      simpl. destruct f as [z1]. destruct f0 as [z2].
      case_eq (beq_nat xn z1); intros Hbeq; 
        case_eq (beq_nat xn z2); intros Hbeq2; reflexivity.

    destruct n.
    destruct atm; try discriminate.
      simpl in *. destruct p. destruct f as [zn].
      case_eq (beq_nat xn zn); reflexivity.

      simpl. destruct f as [z1]. destruct f0 as [z2].
      case_eq (beq_nat xn z1); intros Hbeq; 
        case_eq (beq_nat xn z2); intros Hbeq2; reflexivity.

      simpl. destruct f as [z1]. destruct f0 as [z2].
      case_eq (beq_nat xn z1); intros Hbeq; 
        case_eq (beq_nat xn z2); intros Hbeq2; reflexivity.

    destruct atm; try discriminate; try reflexivity;
      try (destruct p; reflexivity).


(* -- *)

simpl replace_FOv. destruct f as [zn].
case_eq (beq_nat xn zn); intros Hbeq.
  destruct atm; try discriminate; try reflexivity.
    destruct p. destruct f as [un].
    simpl. case_eq (beq_nat xn un); reflexivity.

      simpl. destruct f as [z1]. destruct f0 as [z2].
      case_eq (beq_nat xn z1); intros Hbeq2; 
        case_eq (beq_nat xn z2); intros Hbeq3; reflexivity.

      simpl. destruct f as [z1]. destruct f0 as [z2].
      case_eq (beq_nat xn z1); intros Hbeq3; 
        case_eq (beq_nat xn z2); intros Hbeq2; reflexivity.

      simpl. destruct f as [un]. case_eq (beq_nat xn un); reflexivity.

      simpl in *. destruct f as [un]. case_eq (beq_nat xn un);
        intros Hbeq2; reflexivity.
  (* --  *)
remember atm2 as t. rewrite Heqt.
    simpl in Hall. destruct atm2; try reflexivity.
      destruct p. destruct f as [un]. simpl.
      case_eq (beq_nat xn un); intros Hbeq2; reflexivity.

      simpl. destruct f as [z1]. destruct f0 as [z2].
      case_eq (beq_nat xn z1); intros Hbeq2; 
        case_eq (beq_nat xn z2); intros Hbeq3; reflexivity.

      simpl. destruct f as [z1]. destruct f0 as [z2].
      case_eq (beq_nat xn z1); intros Hbeq3; 
        case_eq (beq_nat xn z2); intros Hbeq2; reflexivity.

remember (allFO f atm2) as t2.
      destruct f as [un]. simpl. rewrite Heqt2.
      case_eq (beq_nat xn un); intros Hbeq2.
        assert (replace_FOv (allFO (Var un) atm2) (Var xn) (Var ym) =
          allFO (Var ym) (replace_FOv atm2 (Var xn) (Var ym))) as Hass.
          simpl. rewrite Hbeq2. reflexivity.
        rewrite Hass. rewrite <- Hass.
        rewrite <- Heqt2.
        rewrite is_all_diff_FOv_cons.
        rewrite (IHm (num_conn t2) t2); try reflexivity; try assumption.

rewrite Heqt in *. rewrite Heqt2 in Hall.
rewrite is_all_diff_FOv_cons in Hall.
case_eq (is_in_FOvar (Var zn) (comp_cond_lx2 (allFO (Var un) atm2)));
    intros Hin2; rewrite Hin2 in *. discriminate.
rewrite (beq_nat_true _ _ Hbeq) in *.
rewrite <- Heqt2 in Hin2.
rewrite comp_cond_lx2_rep_FOv.
case_eq (is_in_FOvar (Var ym) (comp_cond_lx2 t2)); intros Hin3.
  2 : reflexivity.

apply is_in__FOvar with (l2 := FOvars_in t2) in Hin3.
apply want19 in Hin3.
apply (leb_trans _ _ _ Hleb2) in Hin3.
simpl in Hin3.
 case_eq (max_FOv t2). intros Hnil. rewrite Hnil in *.
    discriminate.
    intros mm Hmm. rewrite Hmm in Hin3.
    apply leb_max in Hin3.
    destruct Hin3 as [Hin3a Hin3b].
    apply leb_max in Hin3b. destruct Hin3b as [Hin4 Hin5].
    rewrite leb_suc_f in Hin5. discriminate.

apply is_in_FOvar_l_comp_cond_lx2. assumption.

rewrite Heqt in *. simpl in Hnum.
    inversion Hnum as [Hnum'].
    rewrite Hnum' in Hleb.
    destruct m. discriminate.
    simpl in Hleb. apply leb_suc_r.
    apply leb_plus_take2 in Hleb. assumption.

rewrite Heqt in *. simpl in Hleb2. destruct ym. discriminate.
  apply leb_max in Hleb2. destruct Hleb2 as [Hleb3 Hleb4].
  apply leb_max in Hleb4. apply Hleb4.


        rewrite Heqt in Hall. rewrite Heqt2 in Hall.
        rewrite <- Heqt2 in Hall. simpl in Hall.
        case_eq (is_in_FOvar (Var zn) (comp_cond_lx2 t2));
          intros Hinn; rewrite Hinn in *. discriminate.
        assumption.

        assert (replace_FOv (allFO (Var un) atm2) (Var xn) (Var ym) =
          allFO (Var un) (replace_FOv atm2 (Var xn) (Var ym))) as Hass.
          simpl. rewrite Hbeq2. reflexivity.
        rewrite Hass. rewrite <- Hass.
        rewrite <- Heqt2.
        rewrite is_all_diff_FOv_cons.
        rewrite (IHm (num_conn t2) t2); try reflexivity; try assumption.

rewrite Heqt in *. rewrite Heqt2 in Hall.
rewrite is_all_diff_FOv_cons in Hall.
case_eq (is_in_FOvar (Var zn) (comp_cond_lx2 (allFO (Var un) atm2)));
    intros Hin2; rewrite Hin2 in *. discriminate.
rewrite (beq_nat_true _ _ Hbeq) in *.
rewrite <- Heqt2 in Hin2.
rewrite comp_cond_lx2_rep_FOv.
case_eq (is_in_FOvar (Var ym) (comp_cond_lx2 t2)); intros Hin3.
  2 : reflexivity.

apply is_in__FOvar with (l2 := FOvars_in t2) in Hin3.
apply want19 in Hin3.
apply (leb_trans _ _ _ Hleb2) in Hin3.
simpl in Hin3.
 case_eq (max_FOv t2). intros Hnil. rewrite Hnil in *.
    discriminate.
    intros mm Hmm. rewrite Hmm in Hin3.
    apply leb_max in Hin3.
    destruct Hin3 as [Hin3a Hin3b].
    apply leb_max in Hin3b. destruct Hin3b as [Hin4 Hin5].
    rewrite leb_suc_f in Hin5. discriminate.

apply is_in_FOvar_l_comp_cond_lx2. assumption.

rewrite Heqt in *. simpl in Hnum.
    inversion Hnum as [Hnum'].
    rewrite Hnum' in Hleb.
    destruct m. discriminate.
    simpl in Hleb. apply leb_suc_r.
    apply leb_plus_take2 in Hleb. assumption.

rewrite Heqt in *. simpl in Hleb2. destruct ym. discriminate.
  apply leb_max in Hleb2. destruct Hleb2 as [Hleb3 Hleb4].
  apply leb_max in Hleb4. apply Hleb4.

        rewrite Heqt in Hall. rewrite Heqt2 in Hall.
        rewrite <- Heqt2 in Hall. simpl in Hall.
        case_eq (is_in_FOvar (Var zn) (comp_cond_lx2 t2));
          intros Hinn; rewrite Hinn in *. discriminate.
        assumption.

      simpl. destruct f as [un]. case_eq (beq_nat xn un); reflexivity.

      simpl. destruct p. reflexivity.
      simpl. destruct p. reflexivity.


  (* -- *)

      simpl. destruct p. reflexivity.
      simpl. destruct p. reflexivity.

  destruct atm; try discriminate; try reflexivity.
    destruct p. destruct f as [un].
    simpl. case_eq (beq_nat xn un); reflexivity.

      simpl. destruct f as [z1]. destruct f0 as [z2].
      case_eq (beq_nat xn z1); intros Hbeq2; 
        case_eq (beq_nat xn z2); intros Hbeq3; reflexivity.

      simpl. destruct f as [z1]. destruct f0 as [z2].
      case_eq (beq_nat xn z1); intros Hbeq3; 
        case_eq (beq_nat xn z2); intros Hbeq2; reflexivity.

      simpl. destruct f as [un]. case_eq (beq_nat xn un); reflexivity.

      simpl in *. destruct f as [un]. case_eq (beq_nat xn un);
        intros Hbeq2; reflexivity.

  (* --  *)
remember atm2 as t. rewrite Heqt.
    simpl in Hall. destruct atm2; try reflexivity.
      destruct p. destruct f as [un]. simpl.
      case_eq (beq_nat xn un); intros Hbeq2; reflexivity.

      simpl. destruct f as [z1]. destruct f0 as [z2].
      case_eq (beq_nat xn z1); intros Hbeq2; 
        case_eq (beq_nat xn z2); intros Hbeq3; reflexivity.

      simpl. destruct f as [z1]. destruct f0 as [z2].
      case_eq (beq_nat xn z1); intros Hbeq3; 
        case_eq (beq_nat xn z2); intros Hbeq2; reflexivity.

remember (allFO f atm2) as t2.
      destruct f as [un]. simpl. rewrite Heqt2.
      case_eq (beq_nat xn un); intros Hbeq2.
        assert (replace_FOv (allFO (Var un) atm2) (Var xn) (Var ym) =
          allFO (Var ym) (replace_FOv atm2 (Var xn) (Var ym))) as Hass.
          simpl. rewrite Hbeq2. reflexivity.
        rewrite Hass. rewrite <- Hass.
        rewrite <- Heqt2.
        rewrite is_all_diff_FOv_cons.
        rewrite (IHm (num_conn t2) t2); try reflexivity; try assumption.


rewrite Heqt in *. rewrite Heqt2 in Hall.
rewrite is_all_diff_FOv_cons in Hall.
case_eq (is_in_FOvar (Var zn) (comp_cond_lx2 (allFO (Var un) atm2)));
    intros Hin2; rewrite Hin2 in *. discriminate.
rewrite is_in_FOvar_comp_cond_lx2_rep_FOv. reflexivity.
simpl in Hleb2. destruct ym. discriminate.
apply leb_max in Hleb2.
apply leb_Var_not. apply Hleb2.

 rewrite Heqt2 in *.
rewrite Hin2. reflexivity.

(* intros HH. inversion HH as [HH']. rewrite HH' in *.
 rewrite <- beq_nat_refl in *. discriminate. *)

rewrite Heqt in *. simpl in Hnum.
    inversion Hnum as [Hnum'].
    rewrite Hnum' in Hleb.
    destruct m. discriminate.
    simpl in Hleb. apply leb_suc_r.
    apply leb_plus_take2 in Hleb. assumption.

rewrite Heqt in *. simpl in Hleb2. destruct ym. discriminate.
  apply leb_max in Hleb2. destruct Hleb2 as [Hleb3 Hleb4].
  apply leb_max in Hleb4. apply Hleb4.
        rewrite Heqt in Hall. rewrite Heqt2 in Hall.
        rewrite <- Heqt2 in Hall. simpl in Hall.
        case_eq (is_in_FOvar (Var zn) (comp_cond_lx2 t2));
          intros Hinn; rewrite Hinn in *. discriminate.
        assumption.

        assert (replace_FOv (allFO (Var un) atm2) (Var xn) (Var ym) =
          allFO (Var un) (replace_FOv atm2 (Var xn) (Var ym))) as Hass.
          simpl. rewrite Hbeq2. reflexivity.
        rewrite Hass. rewrite <- Hass.
        rewrite <- Heqt2.
        rewrite is_all_diff_FOv_cons.
        rewrite (IHm (num_conn t2) t2); try reflexivity; try assumption.


rewrite Heqt in *. rewrite Heqt2 in Hall.
rewrite is_all_diff_FOv_cons in Hall.
case_eq (is_in_FOvar (Var zn) (comp_cond_lx2 (allFO (Var un) atm2)));
    intros Hin2; rewrite Hin2 in *. discriminate.
rewrite is_in_FOvar_comp_cond_lx2_rep_FOv. reflexivity.

simpl in Hleb2. destruct ym. discriminate.
apply leb_max in Hleb2.
apply leb_Var_not. apply Hleb2.

 rewrite Heqt2 in *.
rewrite Hin2. reflexivity.
(* intros HH. inversion HH as [HH']. rewrite HH' in *.
 rewrite <- beq_nat_refl in *. discriminate. *)

rewrite Heqt in *. simpl in Hnum.
    inversion Hnum as [Hnum'].
    rewrite Hnum' in Hleb.
    destruct m. discriminate.
    simpl in Hleb. apply leb_suc_r.
    apply leb_plus_take2 in Hleb. assumption.

rewrite Heqt in *. simpl in Hleb2. destruct ym. discriminate.
  apply leb_max in Hleb2. destruct Hleb2 as [Hleb3 Hleb4].
  apply leb_max in Hleb4. apply Hleb4.
        rewrite Heqt in Hall. rewrite Heqt2 in Hall.
        rewrite <- Heqt2 in Hall. simpl in Hall.
        case_eq (is_in_FOvar (Var zn) (comp_cond_lx2 t2));
          intros Hinn; rewrite Hinn in *. discriminate.
        assumption.

      simpl. destruct f as [un]. case_eq (beq_nat xn un); reflexivity.

      simpl. destruct p. reflexivity.
      simpl. destruct p. reflexivity.


  (* -- *)

      simpl. destruct p. reflexivity.
      simpl. destruct p. reflexivity.

(* -- *)


    simpl in *. destruct f as [zn]. case_eq (beq_nat xn zn);
      intros Hbeq; reflexivity.
Qed.


Lemma is_all_diff_FOv_comp_cond_lx2_rep_FOv : forall atm x ym,
Nat.leb (S (max_FOv atm)) ym = true ->
  is_all_diff_FOv (comp_cond_lx2 atm) = true ->
  is_all_diff_FOv (comp_cond_lx2 (replace_FOv atm x (Var ym))) = true.
Proof.
  intros atm x ym.
  apply (is_all_diff_FOv_comp_cond_lx2_rep_FOv_num_conn 
    (num_conn atm) (num_conn atm) atm _ _ eq_refl (leb_refl _)).
Qed.

Lemma leb_max_rand2 : forall n zn m l2,
Nat.leb n m = true ->
min_FOv_l (Var (S zn) :: l2) = S m ->
Nat.leb n zn = true.
Admitted.






  

Lemma leb_max_FOv_l_rem_FOv : forall l n x,
 Nat.leb (max_FOv_l l) n = true ->
 Nat.leb (max_FOv_l (rem_FOv l x)) n = true.
Admitted.

Lemma leb_max_rand3 : forall l zn nn ym,
is_in_FOvar (Var ym) l = true ->
  Nat.leb (max_FOv_l l) (Nat.min zn nn) = true ->
Nat.leb (Nat.max (max_FOv_l (rem_FOv l (Var ym))) (S zn)) nn = true.
Proof.
  intros l zn nn ym Hin Hleb.
  apply leb_min_r in Hleb. destruct Hleb as [Hleb1 Hleb2].
  apply leb_max_FOv_l_rem_FOv with (x := (Var ym)) in Hleb1.
  
Admitted.
(* Search max_FOv_l rem_FOv.

Search Nat.leb min.
  induction l ;intros zn nn ym Hin Hleb.
    simpl in *. discriminate.

    simpl in *. destruct a as [un].
    case_eq (beq_nat ym un); intros Hbeq; rewrite Hbeq in *.
       destruct nn.
Admitted.
 *)

Lemma leb_max_FOv_min_FOv_l_rep_FOv : forall l2 y z atm,
  ~ l2 = nil ->
  Nat.leb (S(max_FOv atm)) (min_FOv_l (cons z l2)) = true ->
  Nat.leb (S (max_FOv (replace_FOv atm y z))) (min_FOv_l l2) = true.
Proof.
  intros l2 y [zn] atm Hnil Hleb.
  rewrite max_FOv__l in Hleb.
  case_eq (x_occ_in_alpha atm y); intros Hocc.
  rewrite max_FOv_rep_FOv.
    simpl min_FOv_l in Hleb. case_eq l2. intros Hnil2.
      rewrite Hnil2 in *. contradiction (Hnil eq_refl).
    intros x lx Hl2. rewrite Hl2 in *. rewrite <- Hl2 in *.
    pose proof  Hleb as Hleb'.
    apply leb_min_r in Hleb. destruct Hleb as [Hleb1 Hleb2].
    case_eq (min_FOv_l l2). intros Hnil3. rewrite Hnil3 in *.
      discriminate.
    intros m Hm. rewrite Hm in *. simpl. simpl in Hleb2.
    
    
    
Admitted.

Fixpoint rename_FOv_list_l  (l l1 l2 : list FOvariable) :=
  match l1, l2 with
  | nil, _ => l
  | _, nil => l
  | cons x l1', cons y l2' => rename_FOv_list (rename_FOv_list_l l l1' l2') x y
  end.

Fixpoint rename_FOv_llist (llv : list (list FOvariable)) x y : list (list FOvariable) :=
  match llv with
  | nil => nil
  | cons l llv' => cons (rename_FOv_list l x y) (rename_FOv_llist llv' x y)
  end.

Fixpoint rename_FOv_llist_l  (l : list (list FOvariable)) (l1 l2 : list FOvariable) :=
  match l1, l2 with
  | nil, _ => l
  | _, nil => l
  | cons x l1', cons y l2' => rename_FOv_llist (rename_FOv_llist_l l l1' l2') x y
  end.

(* Left it here 15/01/18 *)


Lemma comp_cond_lx2_rep_FOv2_num_conn : forall m n  atm x y z,
      n = num_conn atm ->
      Nat.leb n m = true ->
  BOXATM_flag_weak atm z = true ->
  comp_cond_lx2 (replace_FOv atm x y) =
  rename_FOv_list (comp_cond_lx2 atm) x y.
Proof.
  induction m; intros n atm [xn] [ym] [zn] Hnum Hleb Hb.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
    destruct f as [un].
    simpl in *. destruct p. case_eq (beq_nat xn un); intros Hbeq;
      reflexivity.

    destruct n.
    destruct atm; try discriminate.
    destruct f as [un].
    simpl in *. destruct p. case_eq (beq_nat xn un); intros Hbeq;
      reflexivity.

    destruct atm; try discriminate.
    destruct f as [un]. simpl replace_FOv.
    case_eq (beq_nat xn un); intros Hbeq.
      destruct atm; try discriminate.
      simpl in Hb. destruct atm1; try discriminate.
      destruct f as [v1]. destruct f0 as [v2].
      case_eq (beq_nat zn v1); intros Hbeq1; rewrite Hbeq1 in *.
        case_eq (beq_nat un v2); intros Hbeq2; rewrite Hbeq2 in *.
          all : try discriminate.
      destruct atm2; try discriminate.
        simpl. destruct p. destruct f as [wn].
        case_eq (beq_nat xn wn); intros Hbeq3; try reflexivity.
        remember (allFO f atm2) as t. simpl. 
        rewrite Heqt. rewrite <- Heqt.
        destruct f as [vn].
        case_eq (beq_nat xn vn); intros Hbeq3.
          assert (replace_FOv t (Var xn) (Var ym) = allFO (Var ym) (replace_FOv atm2 (Var xn) (Var ym)))
            as Hass. rewrite Heqt. simpl. rewrite Hbeq3. reflexivity.
          rewrite Hass. rewrite <- Hass. simpl rename_FOv_list. rewrite Hbeq.
          rewrite (IHm (num_conn t) t (Var xn) (Var ym) (Var un)); try reflexivity; try assumption.
simpl in Hnum. inversion Hnum as [Hnum'].
rewrite Hnum' in *. simpl in Hleb. destruct m. discriminate.
apply leb_suc_r. assumption.

          assert (replace_FOv t (Var xn) (Var ym) = allFO (Var vn) (replace_FOv atm2 (Var xn) (Var ym)))
            as Hass. rewrite Heqt. simpl. rewrite Hbeq3. reflexivity.
          rewrite Hass. rewrite <- Hass. simpl rename_FOv_list. rewrite Hbeq.
          rewrite (IHm (num_conn t) t (Var xn) (Var ym) (Var un)); try reflexivity; try assumption.
simpl in Hnum. inversion Hnum as [Hnum'].
rewrite Hnum' in *. simpl in Hleb. destruct m. discriminate.
apply leb_suc_r. assumption.

      destruct atm; try discriminate.
      simpl in Hb. destruct atm1; try discriminate.
      destruct f as [v1]. destruct f0 as [v2].
      case_eq (beq_nat zn v1); intros Hbeq1; rewrite Hbeq1 in *.
        case_eq (beq_nat un v2); intros Hbeq2; rewrite Hbeq2 in *.
          all : try discriminate.
      destruct atm2; try discriminate.
        simpl. destruct p. destruct f as [wn].
        case_eq (beq_nat xn wn); intros Hbeq3; try reflexivity.
        remember (allFO f atm2) as t. simpl. 
        rewrite Heqt. rewrite <- Heqt.
        destruct f as [vn].
        case_eq (beq_nat xn vn); intros Hbeq3.
          assert (replace_FOv t (Var xn) (Var ym) = allFO (Var ym) (replace_FOv atm2 (Var xn) (Var ym)))
            as Hass. rewrite Heqt. simpl. rewrite Hbeq3. reflexivity.
          rewrite Hass. rewrite <- Hass. simpl rename_FOv_list. rewrite Hbeq.
          rewrite (IHm (num_conn t) t (Var xn) (Var ym) (Var un)); try reflexivity; try assumption.
simpl in Hnum. inversion Hnum as [Hnum'].
rewrite Hnum' in *. simpl in Hleb. destruct m. discriminate.
apply leb_suc_r. assumption.

          assert (replace_FOv t (Var xn) (Var ym) = allFO (Var vn) (replace_FOv atm2 (Var xn) (Var ym)))
            as Hass. rewrite Heqt. simpl. rewrite Hbeq3. reflexivity.
          rewrite Hass. rewrite <- Hass. simpl rename_FOv_list. rewrite Hbeq.
          rewrite (IHm (num_conn t) t (Var xn) (Var ym) (Var un)); try reflexivity; try assumption.
simpl in Hnum. inversion Hnum as [Hnum'].
rewrite Hnum' in *. simpl in Hleb. destruct m. discriminate.
apply leb_suc_r. assumption.
Qed.

Lemma comp_cond_lx2_rep_FOv2 : forall atm x y z,
  BOXATM_flag_weak atm z = true ->
  comp_cond_lx2 (replace_FOv atm x y) =
  rename_FOv_list (comp_cond_lx2 atm) x y.
Proof.
  intros atm x y z. apply (comp_cond_lx2_rep_FOv2_num_conn 
    (num_conn atm) (num_conn atm) atm _ _ _ eq_refl (leb_refl _)).
Qed.

Fixpoint head_list_FOv (l : list FOvariable) : FOvariable :=
  match l with
  | nil => Var 0
  | cons x _ => x
  end.

Lemma BOXATM_flag_weak_rep_FOv_gen_num_conn : forall m n atm x y z,
      n = num_conn atm ->
      Nat.leb n m = true ->
(BOXATM_flag_weak atm x = true ->
BOXATM_flag_weak (replace_FOv atm x y) y = true) /\
(~ x = z ->
BOXATM_flag_weak atm z = true ->
BOXATM_flag_weak (replace_FOv atm x y) z = true).
Proof.
  induction m; intros n atm [xn] [ym] [zn] Hnum Hleb.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate;
    try (apply conj; intros; discriminate).
    destruct p. destruct f as [un]. simpl in *.
    apply conj. intros Hb.
      rewrite Hb. simpl. rewrite <- beq_nat_refl. reflexivity.

      intros Hnot Hb.
      rewrite <- (beq_nat_true _ _ Hb). rewrite FOvar_neq.
      simpl. rewrite <- beq_nat_refl. reflexivity.
      assumption.

    destruct n.
    destruct atm; try discriminate;
    try (apply conj; intros; discriminate).
    destruct p. destruct f as [un]. simpl in *.
    apply conj. intros Hb.
      rewrite Hb. simpl. rewrite <- beq_nat_refl. reflexivity.

      intros Hnot Hb.
      rewrite <- (beq_nat_true _ _ Hb). rewrite FOvar_neq.
      simpl. rewrite <- beq_nat_refl. reflexivity.
      assumption.

    destruct atm; try discriminate;
    try (apply conj; intros; discriminate).
    apply conj. intros Hb.
      destruct atm; try discriminate.
      destruct atm1; try discriminate.
      destruct f as [u1]; destruct f0 as [u2]; destruct f1 as [u3].
      simpl in Hb.
simpl in Hnum. inversion Hnum as [Hnum'].
rewrite Hnum' in *. simpl in Hleb. destruct m. discriminate.
      case_eq (beq_nat xn u2); intros Hbeq; rewrite Hbeq in *.
        2 : discriminate.
      case_eq (beq_nat u1 u3); intros Hbeq2; rewrite Hbeq2 in *.
        2 : discriminate.
      simpl. rewrite Hbeq.
      case_eq (beq_nat xn u1); intros Hbeq3.
        rewrite (beq_nat_true _ _ Hbeq3). rewrite Hbeq2.
        simpl; rewrite <- beq_nat_refl. 
          apply (IHm (num_conn atm2) atm2 (Var u1) (Var ym) (Var zn)).
            reflexivity. 2 : assumption.
apply leb_suc_r. assumption.

        rewrite <- (beq_nat_true _ _ Hbeq2). rewrite Hbeq3.
        simpl. do 2 rewrite <- beq_nat_refl.
          apply (IHm (num_conn atm2) atm2 (Var xn) (Var ym)).
            reflexivity.

apply leb_suc_r. assumption.

            apply beq_nat_false_FOv. assumption.
            assumption.

      intros Hnot Hb.
      destruct atm; try discriminate.
      destruct atm1; try discriminate.
      destruct f as [u1]; destruct f0 as [u2]; destruct f1 as [u3].
      simpl in Hb.
simpl in Hnum. inversion Hnum as [Hnum'].
rewrite Hnum' in *. simpl in Hleb. destruct m. discriminate.
      case_eq (beq_nat zn u2); intros Hbeq; rewrite Hbeq in *.
        2 : discriminate.
      case_eq (beq_nat u1 u3); intros Hbeq2; rewrite Hbeq2 in *.
        2 : discriminate.
      simpl. case_eq (beq_nat xn u1); intros Hbeq3;
        rewrite <- (beq_nat_true _ _ Hbeq) in *; rewrite (FOvar_neq _ _ Hnot);
        rewrite <- (beq_nat_true _ _ Hbeq2) in *; rewrite Hbeq3;
        simpl; do 2 rewrite <- beq_nat_refl.
        apply (IHm (num_conn atm2) atm2 _ _ (Var zn)). reflexivity.

apply leb_suc_r. assumption.
          rewrite (beq_nat_true _ _ Hbeq3). assumption.

        apply (IHm (num_conn atm2) atm2 (Var xn) (Var ym) (Var u1)).
          reflexivity.
apply leb_suc_r. assumption.
          apply (beq_nat_false_FOv _ _ Hbeq3). assumption.
Qed.


Lemma BOXATM_flag_weak_rep_FOv_gen : forall atm x y z,
(BOXATM_flag_weak atm x = true ->
BOXATM_flag_weak (replace_FOv atm x y) y = true) /\
(~ x = z ->
BOXATM_flag_weak atm z = true ->
BOXATM_flag_weak (replace_FOv atm x y) z = true).
Proof.
  intros atm x y z. apply (BOXATM_flag_weak_rep_FOv_gen_num_conn
    (num_conn atm) (num_conn atm) atm _ _ _ eq_refl (leb_refl _ )).
Qed.

Lemma BOXATM_flag_weak_rep_FOv_1 : forall atm x y,
(BOXATM_flag_weak atm x = true ->
BOXATM_flag_weak (replace_FOv atm x y) y = true).
Proof.
  intros atm x y z. apply (BOXATM_flag_weak_rep_FOv_gen atm x y (Var 0)).
  assumption.
Qed.

Lemma BOXATM_flag_weak_rep_FOv_2 : forall atm x y z,
~ x = z ->
BOXATM_flag_weak atm z = true ->
BOXATM_flag_weak (replace_FOv atm x y) z = true.
Proof.
  intros atm x y z. apply BOXATM_flag_weak_rep_FOv_gen.
Qed.

Lemma BOXATM_flag_weak_rep_FOv_num_conn : forall m n atm x y z,
      n = num_conn atm ->
      Nat.leb n m = true ->
  BOXATM_flag_weak atm z = true ->
  BOXATM_flag_weak (replace_FOv atm x y) (head_list_FOv (rename_FOv_list (cons z nil) x y) )= true.
Proof.
  induction m; intros n atm [xn] [ym] [zn] Hnum Hleb H.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
    destruct p. destruct f as [un]. simpl in *.
    case_eq (beq_nat xn un); intros Hbeq;  simpl;
      rewrite (beq_nat_true _ _ H); rewrite Hbeq; simpl;
      rewrite <- beq_nat_refl; reflexivity.

    destruct n.
    destruct atm; try discriminate.
    destruct p. destruct f as [un]. simpl in *.
    case_eq (beq_nat xn un); intros Hbeq;  simpl;
      rewrite (beq_nat_true _ _ H); rewrite Hbeq; simpl;
      rewrite <- beq_nat_refl; reflexivity.

    simpl rename_FOv_list. case_eq (beq_nat xn zn); intros Hbeq;
      simpl head_list_FOv.
      apply BOXATM_flag_weak_rep_FOv_1. rewrite (beq_nat_true _ _ Hbeq) in *.
      assumption.

      apply BOXATM_flag_weak_rep_FOv_2. apply beq_nat_false_FOv.
      assumption. assumption.
Qed.


Lemma BOXATM_flag_weak_rep_FOv : forall atm x y z,
  BOXATM_flag_weak atm z = true ->
  BOXATM_flag_weak (replace_FOv atm x y) (head_list_FOv (rename_FOv_list (cons z nil) x y) )= true.
Proof.
  intros atm x y z. apply (BOXATM_flag_weak_rep_FOv_num_conn (num_conn atm) (num_conn atm) atm _ _ _ 
    eq_refl (leb_refl _)).
Qed.

Lemma rename_FOv_list__l_head_list_FOv : forall l1 l2 z x y,
rename_FOv_list (cons (head_list_FOv (rename_FOv_list_l (cons z nil) l1 l2)) nil) x y =
rename_FOv_list (rename_FOv_list_l (cons z nil) l1 l2) x y.
Proof.
  induction l1; intros l2 [zn] [xn] [ym]. reflexivity.
  simpl. destruct l2. reflexivity.
  rewrite <- IHl1. simpl. destruct a as [vn].
  destruct ( head_list_FOv (rename_FOv_list_l (Var zn :: nil) l1 l2)) as [un].
  case_eq (beq_nat vn un); intros Hbeq.
    simpl. destruct f as [wn]. reflexivity.
    simpl. reflexivity.
Qed.

Lemma BOXATM_flag_weak_rep_FOv_l : forall l1 l2 atm z,
  BOXATM_flag_weak atm z = true ->
  BOXATM_flag_weak (replace_FOv_l atm l1 l2) (head_list_FOv (rename_FOv_list_l (cons z nil) l1 l2) )= true.
Proof.
  induction l1; intros l2 atm z H.
    simpl. assumption.
  simpl. destruct l2. assumption.
  apply (IHl1 l2) in H.
  apply (BOXATM_flag_weak_rep_FOv _ a f ) in H.
  rewrite rename_FOv_list__l_head_list_FOv in H.
  assumption.
Qed.


Lemma comp_cond_lx2_rep_FOv_l : forall l1 l2 atm z,
  BOXATM_flag_weak atm z = true ->
  comp_cond_lx2 (replace_FOv_l atm l1 l2) =
  rename_FOv_list_l (comp_cond_lx2 atm) l1 l2.
Proof.
  induction l1; intros l2 atm z H. reflexivity.
  simpl. destruct l2. reflexivity.
  rewrite <- IHl1 with (z := z). 2 : assumption.
  rewrite comp_cond_lx2_rep_FOv2 with (z := (head_list_FOv (rename_FOv_list_l (cons z nil) l1 l2) )).
  reflexivity.
  apply BOXATM_flag_weak_rep_FOv_l. assumption.
Qed.

Lemma ren_FOv_list_not_in : forall l x y,
  is_in_FOvar x l = false ->
  rename_FOv_list l x y = l.
Proof.
  induction l; intros [xn] [ym] Hin. reflexivity.
  simpl in *. destruct a as [zn].   
  apply if_then_else_tf in Hin. destruct Hin as [H1 H2].
  rewrite H1. rewrite IHl. reflexivity.
  assumption.
Qed. 

Lemma is_all_diff_FOv_comp_cond_lx2_rep_FOv_l_pre_pre : forall l x ym,
Nat.leb (S (max_FOv_l l)) ym = true ->
is_all_diff_FOv l = true ->
is_all_diff_FOv (rename_FOv_list l x (Var ym)) = true.
Proof.
  induction l; intros [xn] ym Hleb Hall. reflexivity.
  destruct a as [zn]. simpl in *. destruct ym. discriminate.
  case_eq (is_in_FOvar (Var zn) l); intros Hin; rewrite Hin in *.
    discriminate.
  case_eq (beq_nat xn zn); intros Hbeq.
    simpl.  rewrite (beq_nat_true _ _  Hbeq) in *.
    rewrite ren_FOv_list_not_in. 2 : assumption.
    apply leb_max in Hleb. destruct Hleb as [Hleb1 Hleb2].
    rewrite lem12; assumption.

    apply leb_max in Hleb. destruct Hleb as [Hleb1 Hleb2].
    simpl. rewrite is_in_FOvar_rename_FOv_list2. rewrite Hin.
    apply IHl; assumption.
    intros H. inversion H as [HH]. rewrite HH in *.
      rewrite <- beq_nat_refl in Hbeq. discriminate.

      intros H. inversion H as [HH]. rewrite HH in *.
      rewrite leb_suc_f in Hleb1. discriminate.
Qed.

(* Lemma FAKE2 : forall l l1 l2 x y,
  rename_FOv_list (rename_FOv_list_l l l1 l2) x y =
  rename_FOv_list_l (rename_FOv_list l x y) l1 l2.
Admitted. *)

Lemma leb_max_rand7 : forall l n m x,
  ~ (min n m = 0) ->
  Nat.leb (S (max_FOv_l l)) (min n m) = true ->
  Nat.leb (S (max_FOv_l (rename_FOv_list l x (Var n)))) (min n m) = true.
Proof.
Admitted.
(*
  induction l; intros n m [xn] Hnot Hleb.
    simpl in *. assumption.
  simpl in *. case_eq (min n m).
    intros Hmin. rewrite Hmin in *. discriminate.
  intros nn Hnn. rewrite Hnn in *. destruct a as [ym].
  destruct n. simpl in *. discriminate.
  destruct m. simpl in *. discriminate.
  simpl in Hnn. inversion Hnn as [Hnn'].
  destruct nn. rewrite Hnn'.
  destruct ym. destruct xn. simpl.
  destruct l. simpl in *. simpl.
  case_eq (beq_nat xn ym); intros Hbeq.
    specialize (IHl n m (Var xn)).
    rewrite Hnn' in IHl. destruct nn. rewrite Hnn'.
    simpl. destruct l. simpl in *. 
    simpl. rewrite <- (max_refl nn). apply leb_max_max_gen.
admit.
      apply IHl. 
    
Admitted.
*)



Lemma rename_FOv_list__l_is_in : forall l1 l2 l x y,
  is_in_FOvar x l1 = true ->
(*   is_in_FOvar y l2 = false -> *)
  is_all_diff_FOv l = true ->
  decr_strict_FOv l2 = true ->
  Nat.leb (S (max_FOv_l l)) (min_FOv_l l2) = true ->
(*   is_all_diff_FOv l2 = true -> *)
  rename_FOv_list (rename_FOv_list_l l l1 l2) x y =
  rename_FOv_list_l l l1 l2.
Proof.
  induction l1; intros l2 l [xn] [ym] Hin Hall Hdec Hleb. discriminate.
  destruct a as [zn]. simpl. destruct l2. discriminate.
  simpl in Hin. case_eq (beq_nat xn zn); intros Hbeq; rewrite Hbeq in *.
  case_eq (is_in_FOvar (Var xn) l1); intros Hin2.
    rewrite IHl1.
admit.
    rewrite (beq_nat_true _ _ Hbeq) in *.
    assumption. assumption.
    apply decr_strict_FOv_cons in Hdec. assumption.
    destruct f as [un].
    rewrite min_FOv_l_cons in Hleb. apply leb_min_r in Hleb.
    destruct Hleb. assumption.
admit.

    rewrite (beq_nat_true _ _ Hbeq) in *.
    
    
  
(*

    apply decr_strict_FOv_cons in Hdec.
    
    
 apply IHl1.
  all : try assumption.
    
    
  rewrite IHl1.
    simpl.

Hall : is_all_diff_FOv l2 = true
xx : FOvariable
lxx : list FOvariable
Hdec1 : Nat.leb (max_FOv_l l2) ym = true
Hdec2 : decr_strict_FOv l2 = true
H : Nat.leb (S (max_FOv_l l)) (S ym) = true
H0 : Nat.leb (S (max_FOv_l l)) (min_FOv_l l2) = true
Hall2 : is_all_diff_FOv l = true
Hin : is_in_FOvar (Var (S ym)) l2 = false
Hlxx : l2 = xx :: lxx
Hin2 : is_in_FOvar a l1 = true
 *)Admitted.

Lemma leb_max_FOv_l_ren_FOv_l_list_l : forall l l1 l2,
  Nat.leb (max_FOv_l (rename_FOv_list_l l l1 l2))
    (max (max_FOv_l l) (max_FOv_l l2)) = true.
Admitted.

Lemma leb_min_max_FOv_l : forall l n m,
  Nat.leb n (min (min_FOv_l l) m) = true ->
  Nat.leb (max n (max_FOv_l l)) m = true.
Admitted.

Lemma leb_max_rand9 : forall n ym m,
Nat.leb (S n) (Nat.min (S ym) m) = true ->
Nat.leb n (Nat.min m ym) = true.
Proof.
  induction n; intros ym m H. reflexivity.
  simpl in H. destruct m. discriminate.
  destruct ym. discriminate.
  simpl. case_eq (min (S ym) m).
    intros Hnil; rewrite Hnil in *. discriminate.
  intros mm Hmm. rewrite Hmm in *. apply IHn.
  rewrite Hmm. assumption.
Qed.

Lemma leb_max_rand8 : forall l l2 ym,
Nat.leb (S (max_FOv_l l)) (Nat.min (S ym) (min_FOv_l l2)) = true ->
Nat.leb (max_FOv_l l) (Nat.min (min_FOv_l l2) ym) = true.
Proof.
  intros. apply leb_max_rand9. assumption.
Qed.

Lemma is_all_diff_FOv_comp_cond_lx2_rep_FOv_l_pre : forall l1 l2 l,
is_all_diff_FOv l2 = true ->
decr_strict_FOv l2 = true ->
Nat.leb (S (max_FOv_l l)) (min_FOv_l l2) = true ->
is_all_diff_FOv l = true ->
is_all_diff_FOv (rename_FOv_list_l l l1 l2) = true.
Proof.
  induction l1; intros l2 l Hall Hdec Hleb Hall2. assumption.
  destruct l2. assumption.
  simpl. destruct f as [ym].
  rewrite is_all_diff_FOv_cons in Hall.
  case_eq (is_in_FOvar (Var ym) l2); intros Hin; rewrite Hin in *.
    discriminate. 
  case_eq l2. intros Hnil. rewrite Hnil in *.
    simpl in *. destruct l1; simpl;
    apply is_all_diff_FOv_comp_cond_lx2_rep_FOv_l_pre_pre;
      try assumption.

    intros xx lxx Hlxx. rewrite <- Hlxx.
    simpl in Hdec. rewrite Hlxx in Hdec. rewrite <- Hlxx in Hdec.
    destruct ym. discriminate.
    apply if_then_else_ft in Hdec. destruct Hdec as [Hdec1 Hdec2].
    case_eq (is_in_FOvar a l1); intros Hin2.
      rewrite min_FOv_l_cons in Hleb. apply leb_min_r in Hleb.
      destruct Hleb.
      rewrite rename_FOv_list__l_is_in; try assumption.
      apply IHl1; try assumption. rewrite Hlxx. discriminate.

apply is_all_diff_FOv_comp_cond_lx2_rep_FOv_l_pre_pre.
  rewrite min_FOv_l_cons in Hleb.
  pose proof Hleb as Hleb'. apply leb_min_r in Hleb.
  destruct Hleb as [Hleba Hlebb].
  assert (Nat.leb (Nat.max (max_FOv_l l) (max_FOv_l l2)) ( ym) = true) as Hass.
    apply leb_min_max_FOv_l.
    apply leb_max_rand8. assumption.
  apply (leb_trans _ _ _ (leb_max_FOv_l_ren_FOv_l_list_l _ _ _ ) Hass).
    rewrite Hlxx. discriminate.
  apply IHl1; try assumption.
  rewrite min_FOv_l_cons in Hleb. apply leb_min_r in Hleb. apply Hleb.
  rewrite Hlxx. discriminate.
Qed.


(*

Lemma
  Nat.leb (S (max_FOv_l)) (min_FOvar_l (cons y l2)) = true ->
  decr_strict_FOv (cons y l2) = true ->
  is_in_FOvar x l1 = false ->
  rename_FOv_list (rename_FOv_list_l l l1 l2) x y = 
  rename_FOv_list_l (rename_FOv_list x y) l1 l2.

    rewrite FAKE2.
    apply IHl1; try assumption.
      rewrite min_FOv_l_cons in Hleb.
      apply leb_max_rand7  with (x := a) in Hleb.
      apply leb_min_r in Hleb. apply Hleb.
      intros H. rewrite H in *. discriminate.
      rewrite Hlxx. discriminate.

      apply is_all_diff_FOv_comp_cond_lx2_rep_FOv_l_pre_pre.
      rewrite min_FOv_l_cons in Hleb. apply leb_min_r in Hleb.
      apply Hleb.

      rewrite Hlxx. discriminate.
      assumption.
Qed.
Search rename_FOv_list max_FOv_l.

    apply (is_all_diff_FOv_comp_cond_lx2_rep_FOv_l_pre_pre).


      destruct ym. discriminate. assumption.
      assumption. destruct ym/
Search is_all_diff_FOv rename_FOv_list.
Search decr_strict_FOv cons.
Search is_all_diff_FOv cons.

rewrite FAKE2. apply IHl1; try assumption.
admit.
admit.
rewrite min_FOv_l_cons in Hleb.
apply leb_max_rand7 with (x := a) in Hleb.
apply leb_min_r in Hleb. apply Hleb.




  rewrite max_FOv_l_
Lemma
  Nat.leb (S (max_FOv_
admit.
apply is_all_diff_FOv_comp_cond_lx2_rep_FOv_l_pre_pre.


 assumption.



  apply is_all_diff_FOv_comp_cond_lx2_rep_FOv_l_pre_pre.

admit.
    apply IHl1. rewrite is_all_diff_FOv_cons in Hall.
    case_eq (is_all_diff_FOv l2); intros Hall0; rewrite Hall0 in *.
       reflexivity. rewrite if_then_else_false in Hall. discriminate.
admit.
      assumption.

Qed.
Search is_all_diff_FOv rename_FOv_list.


 reflexivity.
  induction l; intros l1 l2 Hall Hleb Hall2.
    simpl.
*)

Lemma max_FOv_l_is_in_FOvar : forall l xn,
  is_in_FOvar (Var xn) l = true ->
  Nat.leb xn (max_FOv_l l) = true.
Proof.
  induction l; intros xn Hin. discriminate.
  simpl in *. destruct a as [ym].
  case_eq (beq_nat xn ym); intros Hbeq; rewrite Hbeq in *.
    rewrite (beq_nat_true _ _ Hbeq).    
    apply leb_max_suc3. apply leb_refl.

    rewrite max_comm. apply leb_max_suc3.
    apply IHl. assumption.
Qed.

Lemma max_FOv_l_is_in_FOvar_l : forall l1 l2,
  is_in_FOvar_l l1 l2 = true -> 
  Nat.leb (max_FOv_l l1) (max_FOv_l l2) = true.
Proof.
  induction l1; intros l2 Hin. reflexivity.
  simpl in *. destruct a as [ym].
  apply if_then_else_ft in Hin. destruct Hin as [Hin1 Hin2].
  rewrite <- (max_refl (max_FOv_l l2)).
  apply leb_max_max_gen.
    apply max_FOv_l_is_in_FOvar. assumption.

    apply IHl1. assumption.
Qed.

Lemma is_all_diff_FOv_comp_cond_lx2_rep_FOv_l : forall l1 l2 atm z,
BOXATM_flag_weak atm z = true ->
is_all_diff_FOv l2 = true ->
decr_strict_FOv l2 = true ->
Nat.leb (S (max_FOv (atm))) (min_FOv_l l2) = true ->
  is_all_diff_FOv (comp_cond_lx2 ( atm)) = true ->
  is_all_diff_FOv (comp_cond_lx2 (replace_FOv_l ( atm) l1 l2)) = true.
Proof.
  intros l1 l2 atm z Hbat Hall Hdec Hleb Hall2.
  rewrite comp_cond_lx2_rep_FOv_l with (z := z).
  apply is_all_diff_FOv_comp_cond_lx2_rep_FOv_l_pre; try assumption.
  simpl in*. case_eq (min_FOv_l l2). intros Hnil; rewrite Hnil in *.
    discriminate.
  intros mm Hmm. rewrite Hmm in *. 
  rewrite max_FOv__l in Hleb.
  apply (leb_trans _ _ _ (max_FOv_l_is_in_FOvar_l _ _ 
      (is_in_FOvar_l_comp_cond_lx2 _)) Hleb).
  assumption.
Qed.

(*
Lemma
  is_all

  induction l1; intros l2 atm Hall Hleb Hall2. assumption.
  simpl in *. destruct l2. assumption.
  simpl in Hall. case_eq (is_in_FOvar f l2);
      intros Hin2; rewrite Hin2 in *. discriminate.
  case_eq l2. intros Hnil. rewrite Hnil in *. destruct l1. simpl.
    destruct f as [zn].
    apply is_all_diff_FOv_comp_cond_lx2_rep_FOv; try assumption.

    destruct f as [zn].
    apply is_all_diff_FOv_comp_cond_lx2_rep_FOv; try assumption.
  intros ff lff Hl2. rewrite <- Hl2.
  case_eq (is_in_FOvar a l1); intros Hin.
    rewrite rep_FOv__l_not_in; try assumption.
    case_eq l2. intros Hnil. rewrite Hnil in *.
      simpl in *. destruct l1; simpl; assumption.
    intros xx lxx Hlxx. rewrite <- Hlxx.
    apply IHl1; try assumption.
      simpl in Hleb. destruct f as [zn].
      rewrite Hlxx in Hleb. rewrite <- Hlxx in Hleb.
      case_eq (min_FOv_l l2). intros Hnil.
        rewrite Hnil in *.
        destruct zn; discriminate.
      intros nn Hnn.
      rewrite Hnn in Hleb.
      destruct zn. simpl in Hleb. discriminate. 
      simpl in Hleb. apply leb_min_r in Hleb. apply Hleb. 

(*       destruct f as [zn].
      apply is_all_diff_FOv_comp_cond_lx2_rep_FOv.
        simpl in Hleb. rewrite Hl2 in *.
        rewrite <- Hl2 in *.
        destruct zn. discriminate.
        case_eq (min_FOv_l l2).
          intros Hnil. rewrite Hnil in *. 
          discriminate.
        intros nn Hnn. rewrite Hnn in Hleb. simpl in Hleb.
        simpl.  rewrite max_FOv_rep_FOv_l2.
        apply leb_min_r in Hleb. apply Hleb.

admit.

      apply IHl1; try assumption.
        simpl in Hleb. rewrite Hl2 in *.
        rewrite <- Hl2 in *.
        destruct zn. discriminate.
        case_eq (min_FOv_l l2).
          intros Hnil. rewrite Hnil in *. 
          discriminate.
        intros nn Hnn. rewrite Hnn in Hleb. simpl in Hleb.
        apply leb_min_r in Hleb. apply Hleb.
Qed. *)

    rewrite <- rep_FOv__l_switch. 2 : assumption.
    destruct a as [ym]. destruct f as [zn].

assert (Nat.leb (S (max_FOv (replace_FOv atm (Var ym) (Var zn)))) 
      (min_FOv_l l2) = true ) as Hass.
 apply leb_max_FOv_min_FOv_l_rep_FOv. rewrite Hl2. discriminate. assumption.
(* -- *)

case_eq (min_FOv_l l2). intros Hnil.
  simpl in Hleb. rewrite Hl2 in Hleb. rewrite <- Hl2 in Hleb.
  rewrite Hnil in Hleb. rewrite PeanoNat.Nat.min_0_r in Hleb.
  discriminate.

intros nn Hnn. 
simpl in Hleb. rewrite Hl2 in Hleb. rewrite <- Hl2 in Hleb.
rewrite Hnn in Hleb.
destruct zn. discriminate. simpl in Hleb.
case_eq (x_occ_in_alpha atm (Var ym)); intros Hocc.
rewrite max_FOv_rep_FOv.
apply leb_max_rand3. rewrite max_FOv__l in Hleb. assumption.
assumption.
  rewrite rep_FOv_not_occ. apply leb_min_r in Hleb. apply Hleb.
  assumption.


admit.
    apply IHl1; try assumption.

case_eq (min_FOv_l l2). intros Hnil.
  simpl in Hleb. rewrite Hl2 in Hleb. rewrite <- Hl2 in Hleb.
  rewrite Hnil in Hleb. rewrite PeanoNat.Nat.min_0_r in Hleb.
  discriminate.

intros nn Hnn. 
simpl in Hleb. rewrite Hl2 in Hleb. rewrite <- Hl2 in Hleb.
rewrite Hnn in Hleb.
destruct zn. discriminate. simpl in Hleb.
case_eq (x_occ_in_alpha atm (Var ym)); intros Hocc.
rewrite max_FOv_rep_FOv.
apply leb_max_rand3. rewrite max_FOv__l in Hleb. assumption.
assumption.
  rewrite rep_FOv_not_occ. apply leb_min_r in Hleb. apply Hleb.
  assumption.

apply is_all_diff_FOv_comp_cond_lx2_rep_FOv.
destruct zn. simpl in Hleb. destruct l2; discriminate.
case_eq (min_FOv_l (cons (Var (S zn)) l2)). 
  intros Hnil. rewrite Hnil in *. discriminate.
intros mm Hmm. rewrite Hmm in Hleb. simpl.
apply leb_max_rand2 with (m := mm) (l2 := l2); try assumption.
assumption.
Qed.
*)

(* Left it here 12/01/18 *)
(* Keep going down! *)
(*
Lemma is_all_diff_FOv_comp_cond_lx2_rep_FOv_l : forall l1 l2 atm x,
is_all_diff_FOv l2 = true ->
Nat.leb (S (max_FOv (allFO x atm))) (min_FOv_l l2) = true ->
  is_all_diff_FOv (comp_cond_lx2 (allFO x atm)) = true ->
  is_all_diff_FOv (comp_cond_lx2 (replace_FOv_l (allFO x atm) l1 l2)) = true.
Proof.
  induction l1; intros l2 atm x Hall Hleb Hall2. assumption.
  simpl in *. destruct l2. assumption.
  simpl in Hall. case_eq (is_in_FOvar f l2);
      intros Hin2; rewrite Hin2 in *. discriminate.
  case_eq (is_in_FOvar a l1); intros Hin.
    rewrite rep_FOv__l_not_in; try assumption.
    case_eq l2. intros Hnil. rewrite Hnil in *.
      simpl in *. destruct l1; simpl; assumption.
    intros xx lxx Hlxx. rewrite <- Hlxx.
    apply IHl1; try assumption.
      simpl in Hleb. destruct f as [zn].
      rewrite Hlxx in Hleb. rewrite <- Hlxx in Hleb.
      case_eq (min_FOv_l l2). intros Hnil.
        rewrite Hnil in *.
        destruct zn; discriminate.
      intros nn Hnn. destruct x as [xn].
      rewrite Hnn in Hleb.
      destruct zn. simpl in Hleb. discriminate. 
      simpl in Hleb. apply leb_min_r in Hleb. apply Hleb.

    rewrite <- rep_FOv__l_switch. 2 : assumption.
    destruct x as [xn]. destruct a as [ym]. destruct f as [zn].
    case_eq (beq_nat ym xn); intros Hbeq.
      simpl. rewrite Hbeq.
    apply IHl1; try assumption.
admit.
pose proof (is_all_diff_FOv_comp_cond_lx2_rep_FOv (allFO (Var xn) atm) (Var ym) zn).
simpl in H. rewrite Hbeq in H. apply H.
destruct zn. simpl in Hleb. destruct l2; discriminate.
case_eq (min_FOv_l (cons (Var (S zn)) l2)). 
  intros Hnil. rewrite Hnil in *. discriminate.
intros mm Hmm. rewrite Hmm in Hleb.
apply leb_max_rand2 with (m := mm) (l2 := l2); assumption.
assumption.



(*  simpl in Hleb.
        destruct l2. discriminate.
        destruct l2. destruct f as [ym].
        destruct ym. 2 : discriminate.
        destruct zn; discriminate.
        simpl in Hleb. discriminate.
        simpl in Hleb. destruct f as [zn].
        rewrite Hnil in *. *)
  destruct atm; try discriminate; try reflexivity.
  destruct atm2; try discriminate; try reflexivity.


    simpl in *. destruct atm; try reflexivity.
    destruct atm2; try discriminate.

  intros l1 l2 atm x Hall Hleb Hall2.
  simpl in *. destruct atm; try reflexivity; try discriminate. 
Admitted.

 *)

(* (* Similar one in sSahlq4_7_plus_II *)
Lemma calc_llv_P_allFO_ : forall alpha beta x P,
  calc_llv_P (alpha) P =
  if P_branch_allFO alpha P then
     cons (comp_cond_lx2 alpha) nil
      else nil.
Proof.
  reflexivity.
Qed. *)


Lemma rep_FOv_l_allFO_ex : forall l1 l2 atm f,
  exists x,
  replace_FOv_l (allFO f atm) l1 l2 = allFO x (replace_FOv_l atm l1 l2).
Admitted.

(* Lemma is_all_diff_FOv2_calc_llv_P_rename_FOv_A_pre_num_conn_allFO : forall m n atm f l1 l2,
(forall (n : nat) (atm : SecOrder) (l1 l2 : list FOvariable),
      n = num_conn atm ->
      Nat.leb n m = true ->
      BAT atm = true ->
      length l1 = length l2 ->
      is_all_diff_FOv l2 = true ->
      Nat.leb (S (max_FOv atm)) (min_FOv_l l2) = true ->
      (forall P : predicate, is_all_diff_FOv2 (calc_llv_P atm P) = true) ->
      forall P : predicate, is_all_diff_FOv2 (calc_llv_P (replace_FOv_l atm l1 l2) P) = true) ->
 S n = num_conn (allFO f atm) ->
 Nat.leb (S n) (S m) = true ->
 BAT (allFO f atm) = true ->
 length l1 = length l2 ->
 is_all_diff_FOv l2 = true ->
 Nat.leb (S (max_FOv (allFO f atm))) (min_FOv_l l2) = true ->
 (forall P : predicate, is_all_diff_FOv2 (calc_llv_P (allFO f atm) P) = true ) ->
forall P0 : predicate,
is_all_diff_FOv2 (calc_llv_P (replace_FOv_l (allFO f atm) l1 l2) P0) = true.
Proof.
Admitted.
 *)
Lemma is_all_diff_FOv2_calc_llv_P_rename_FOv_A_pre_num_conn_allFO : forall m n atm f l1 l2,
(forall (n : nat) (atm : SecOrder) (l1 l2 : list FOvariable),
      n = num_conn atm ->
      Nat.leb n m = true ->
      BAT atm = true ->
      length l1 = length l2 ->
      is_all_diff_FOv l2 = true ->
      decr_strict_FOv l2 = true ->
      Nat.leb (S (max_FOv atm)) (min_FOv_l l2) = true ->
      (forall P : predicate, is_all_diff_FOv2 (calc_llv_P atm P) = true) ->
      forall P : predicate, is_all_diff_FOv2 (calc_llv_P (replace_FOv_l atm l1 l2) P) = true) ->
 S n = num_conn (allFO f atm) ->
 Nat.leb (S n) (S m) = true ->
 BAT (allFO f atm) = true ->
 length l1 = length l2 ->
 is_all_diff_FOv l2 = true ->
  decr_strict_FOv l2 = true ->
 Nat.leb (S (max_FOv (allFO f atm))) (min_FOv_l l2) = true ->
 (forall P : predicate, is_all_diff_FOv2 (calc_llv_P (allFO f atm) P) = true ) ->
forall P0 : predicate,
is_all_diff_FOv2 (calc_llv_P (replace_FOv_l (allFO f atm) l1 l2) P0) = true.
Proof.
  intros until 0. intros IH Hnum Hleb Hbat Hl Hall Hdec Hleb2 Hall2 P.
  case_eq (P_branch_allFO (replace_FOv_l (allFO f atm) l1 l2) P);
    intros Hb.
    rewrite calc_llv_P_rep_FOv_l_allFO_branch_t.
    simpl.
    rewrite P_branch_allFO_rep_FOv_l in Hb.
    specialize (Hall2 P).
    rewrite calc_llv_P_allFO_branch_t in Hall2; try assumption.
    rewrite BAT_BOXATM_flag_weak_allFO in Hbat.
    rewrite is_all_diff_FOv_comp_cond_lx2_rep_FOv_l with 
      (z := batm_comp_x1 (allFO f atm)); try assumption. reflexivity.
    unfold is_all_diff_FOv2 in Hall2. apply if_then_else_ft in Hall2.
    apply Hall2.
    assumption.

destruct (rep_FOv_l_allFO_ex l1 l2 (atm) f) as [x H].
rewrite H. rewrite calc_llv_P_allFO_gen. rewrite <- H.
rewrite Hb. reflexivity.
Qed.

(*
    rewrite is_all_diff_FOv_comp_cond_lx2_rep_FOv_l. reflexivity.
    simpl in *. destruct atm; try assumption; try reflexivity.
    destruct atm2; try reflexivity.
    apply if_then_else_ft in Hall2. apply Hall2.
    assumption.

    rewrite calc_llv_P_rep_FOv_l_allFO_branch_f. reflexivity.
    assumption.
Qed.
*)




(* 
    simpl in Hall2.


admit. assumption.

    rewrite calc_llv_P_rep_FOv_l_allFO_branch_f. reflexivity.
    assumption.
Qed.






  assert (Nat.leb (S (max_FOv atm)) (min_FOv_l l2) = true) as Hleb3.
    simpl in *.
    case_eq (min_FOv_l l2). intros Hnil. rewrite Hnil in *.
      discriminate.
    intros mm Hmm. rewrite Hmm in *. destruct f as [zn].
      apply leb_max in Hleb2.
      apply Hleb2.
  
  specialize (IH (num_conn atm) atm _ _ Hl Hall Hleb3).



  simpl calc_llv_P in Hall2.
  destruct atm; try discriminate.
Admitted. *)


(* Lemma is_all_diff_FOv2_calc_llv_P_rename_FOv_A_pre_num_conn : forall m n atm l1 l2,
  n = num_conn atm ->
  Nat.leb n m = true ->
  BAT atm = true ->
  length l1 = length l2 ->
  is_all_diff_FOv l2 = true ->
  Nat.leb (S (max_FOv atm)) (min_FOv_l l2) = true ->
  (forall P, is_all_diff_FOv2 (calc_llv_P atm P) = true) ->
  (forall P, is_all_diff_FOv2 (calc_llv_P (replace_FOv_l atm l1 l2) P) = true).
 *)

Lemma is_all_diff_FOv2_calc_llv_P_rename_FOv_A_pre_num_conn : forall m n atm l1 l2,
  n = num_conn atm ->
  Nat.leb n m = true ->
  BAT atm = true ->
  length l1 = length l2 ->
  is_all_diff_FOv l2 = true ->
decr_strict_FOv l2 = true ->
  Nat.leb (S (max_FOv atm)) (min_FOv_l l2) = true ->
  (forall P, is_all_diff_FOv2 (calc_llv_P atm P) = true) ->
  (forall P, is_all_diff_FOv2 (calc_llv_P (replace_FOv_l atm l1 l2) P) = true).
Proof.
  induction m; intros n atm l1 l2 Hnum Hleb0 Hbat Hl Hall Hdec Hleb Hall2 P.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
    destruct (rep_FOv_l_predSO_ex l1 l2 p f) as [y HH].
    rewrite HH in *. reflexivity.

    destruct n.
    destruct atm; try discriminate.
    destruct (rep_FOv_l_predSO_ex l1 l2 p f) as [y HH].
    rewrite HH in *. reflexivity.

    destruct atm; try discriminate.
       apply (is_all_diff_FOv2_calc_llv_P_rename_FOv_A_pre_num_conn_allFO m n _ _ _ _);
       assumption.

    rewrite rep_FOv_l_conjSO. simpl.
    simpl in Hall2.
    rewrite is_all_diff_FOv2_app.
    pose proof (BAT_conjSO_l _ _ Hbat).
    pose proof (BAT_conjSO_r _ _ Hbat).
    rewrite (IHm (num_conn atm1) atm1).
    apply (IHm (num_conn atm2) atm2).
    all : try assumption.
    all : try reflexivity.
      inversion Hnum as [Hnum'].
      rewrite Hnum' in Hleb0. simpl in Hleb0.
        apply leb_plus_take2 in Hleb0. assumption.

      simpl in *. case_eq (min_FOv_l l2). intros Hnil. rewrite Hnil in *.
        discriminate.
      intros mm Hmm. rewrite Hmm in *.
      apply leb_max in Hleb. apply Hleb.

      intros P2. specialize (Hall2 P2).
      rewrite is_all_diff_FOv2_app in Hall2.
      apply if_then_else_ft in Hall2.
      apply Hall2.

      inversion Hnum as [Hnum'].
      rewrite Hnum' in Hleb0. simpl in Hleb0.
        apply leb_plus_take1 in Hleb0. assumption.


      simpl in *. case_eq (min_FOv_l l2). intros Hnil. rewrite Hnil in *.
        discriminate.
      intros mm Hmm. rewrite Hmm in *.
      apply leb_max in Hleb. apply Hleb.

      intros P2. specialize (Hall2 P2).
      rewrite is_all_diff_FOv2_app in Hall2.
      apply if_then_else_ft in Hall2.
      apply Hall2.
Qed.      

(* 

    destruct (rep_FOv_l_relatSO_ex l1 l2 f f0) as [x [ y HH]].
    rewrite HH. reflexivity.

    destruct (rep_FOv_l_eqFO_ex l1 l2 f f0) as [x [ y HH]].
    rewrite HH. reflexivity.

    apply is_all_diff_FOv2_calc_llv_P_rename_FOv_A_pre_allFO; assumption.
admit.

    rewrite rep_FOv_l_negSO. reflexivity.

    rewrite rep_FOv_l_conjSO. simpl.
    simpl in Hall2.
    rewrite is_all_diff_FOv2_app.
    rewrite (IHatm1). apply IHatm2.
    all : try assumption.
admit.
      intros P2. specialize (Hall2 P2).
      rewrite is_all_diff_FOv2_app in Hall2.
      apply if_then_else_ft in Hall2.
      apply Hall2.
admit.
      intros P2. specialize (Hall2 P2).
      rewrite is_all_diff_FOv2_app in Hall2.
      apply if_then_else_ft in Hall2.
      apply Hall2.

    rewrite rep_FOv_l_disjSO. reflexivity.

    rewrite rep_FOv_l_implSO. reflexivity.
Admitted.
Admitted.
 *)


(* Left it here 16/01/18. Go up *)
Lemma is_all_diff_FOv2_calc_llv_P_rename_FOv_A_pre : forall atm l1 l2,
  BAT atm = true ->
  length l1 = length l2 ->
  is_all_diff_FOv l2 = true ->
decr_strict_FOv l2 = true ->
  Nat.leb (S (max_FOv atm)) (min_FOv_l l2) = true ->
  (forall P, is_all_diff_FOv2 (calc_llv_P atm P) = true) ->
  (forall P, is_all_diff_FOv2 (calc_llv_P (replace_FOv_l atm l1 l2) P) = true).
Proof.
Admitted.
(*
  intros atm l1 l2. apply (is_all_diff_FOv2_calc_llv_P_rename_FOv_A_pre_num_conn
 (num_conn atm) (num_conn atm) atm _ _ eq_refl (leb_refl _ )).
Qed.

(*
  induction atm; intros l1 l2 Hl Hall Hleb Hall2 P.
    destruct (rep_FOv_l_predSO_ex l1 l2 p f) as [y HH].
    rewrite HH in *. reflexivity.

    destruct (rep_FOv_l_relatSO_ex l1 l2 f f0) as [x [ y HH]].
    rewrite HH. reflexivity.

    destruct (rep_FOv_l_eqFO_ex l1 l2 f f0) as [x [ y HH]].
    rewrite HH. reflexivity.

    apply is_all_diff_FOv2_calc_llv_P_rename_FOv_A_pre_allFO; assumption.
admit.

    rewrite rep_FOv_l_negSO. reflexivity.

    rewrite rep_FOv_l_conjSO. simpl.
    simpl in Hall2.
    rewrite is_all_diff_FOv2_app.
    rewrite (IHatm1). apply IHatm2.
    all : try assumption.
admit.
      intros P2. specialize (Hall2 P2).
      rewrite is_all_diff_FOv2_app in Hall2.
      apply if_then_else_ft in Hall2.
      apply Hall2.
admit.
      intros P2. specialize (Hall2 P2).
      rewrite is_all_diff_FOv2_app in Hall2.
      apply if_then_else_ft in Hall2.
      apply Hall2.

    rewrite rep_FOv_l_disjSO. reflexivity.

    rewrite rep_FOv_l_implSO. reflexivity.
Admitted.
*)


(* 
  induction l1; intros l2 atm Hl Hal Hleb Hall2. assumption.
  simpl. destruct l2. discriminate.
  intros P. simpl in Hl.
  inversion Hl as [Hl'].
  simpl in Hal. case_eq (is_in_FOvar f l2); intros Hin2; rewrite Hin2 in *.
    discriminate.
  pose proof (leb_trans _ _ _ Hleb (leb_min_FOv_l_cons_l _ _)) as H2.
  case_eq (is_in_FOvar a l1); intros Hin.
    rewrite rep_FOv__l_not_in. apply IHl1; try assumption.
    assumption.

    rewrite <- rep_FOv__l_switch. 2 : assumption.
    apply (IHl1); try assumption.

      case_eq (x_occ_in_alpha atm a); intros Hocc.
        destruct f as [zn].
        pose proof (max_FOv_rename_FOv2 atm a zn Hocc) as H3.
        rewrite <- rep__ren_FOv in H3.
        assert (Nat.leb (S (max (max_FOv atm) zn)) (min_FOv_l l2) = true) as Hass.
          simpl min_FOv_l in Hleb. case_eq l2. intros Hl2. rewrite Hl2 in *. 
          destruct zn; discriminate.
          intros xx lxx Hlxx. rewrite <- Hlxx. rewrite Hlxx in Hleb.
          rewrite <- Hlxx in Hleb.
          pose proof (leb_min_r _ _ _ Hleb) as Hleb2.
          rewrite PeanoNat.Nat.succ_max_distr.
          destruct Hleb2 as [Hleb2 Hleb3].
          apply leb_suc_r in Hleb2.
          apply leb_max_l in Hleb2. rewrite max_comm in Hleb2. rewrite Hleb2.
Search max Nat.leb.
Search max S "dist".
Search max
          destruct (min_or zn (min_FOv_l l2)) as [H|H].
            rewrite H in *.

Search min Nat.leb.
Search min or.
Search max min Nat.leb.
          case_eq (min zn (min_FOv_l l2)). intros Hnil; rewrite Hnil in *.
            discriminate.
          intros mm Hmm. rewrite Hmm in *.
          simpl. rewrite Hlxx. simpl. destruct xx. destruct lxx.
          destruct n.  discriminate.
admit.
        rewrite <- leb_defn_suc in H3.
        apply (leb_trans _ _ _ H3 Hass).


Search replace_FOv replace_FOv_l.

Search rename_FOv_list.
    rewrite <- rep_FOv__l_switch. 2 : assumption.
  apply is_all_diff_FOv2_calc_llv_P_rename_FOv.
Search calc_llv_P rename_FOv.
Search min_FOv_l.
  simpl in Hleb. destruct f as [zn]. 
    simpl in *.
Admitted. *)
*)

Lemma rename_FOv_A_rep_FOv_l_num_conn3 : forall n lv alpha beta,
  length lv = n ->
  is_in_FOvar (Var 0) lv = false ->
  ~ lv = nil ->
  exists l1 l2,
  rename_FOv_A alpha beta lv = replace_FOv_l alpha l1 l2 /\
  length l1 = length l2 /\
  Nat.leb  (S(max_FOv (conjSO alpha beta))) (min_FOv_l l2) = true /\
  is_all_diff_FOv l2 = true.
Proof.
Admitted.
(*
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
*)

Definition rev_seq_FOv2 (x0 : FOvariable) (n : nat) : list FOvariable :=
  List.rev (seq_FOv x0 n).

    
Lemma rev__seq_FOv :forall m n,
  app (List.rev (seq_FOv (Var (S n)) m)) (cons (Var n) nil) =
  List.rev (seq_FOv (Var n) (S m)).
Proof.
  reflexivity.
Qed.

Lemma app_cons_nil2 : forall {A : Type} l1 l2 (a1 a2 : A),
  (app l1 (cons a1 nil)) = (app l2 (cons a2 nil)) ->
  l1 = l2 /\ a1 = a2.
Proof.
  induction l1; intros l2 a1 a2 H.
    simpl in *. destruct l2. apply conj. reflexivity.
    inversion H. reflexivity.

    destruct l2; discriminate.

    simpl in *. destruct l2. destruct l1; discriminate.
    simpl in H. inversion H as [[H1 H2]].
    apply IHl1 in H2. destruct H2 as [H2 H3].
    rewrite H2. rewrite H3. apply conj; reflexivity.
Qed.

Lemma rev_eq : forall {A : Type} (l1 l2 : list A),
  l1 = l2 <->
  List.rev l1 = List.rev l2.
Proof.
  induction l1; intros l2. simpl.
    destruct l2. apply iff_refl.

    simpl. split; intros H. discriminate.
    destruct (List.rev l2); discriminate.

    simpl. destruct l2. split; intros H.
      discriminate. destruct (List.rev l1); discriminate.

      split; intros H.
        simpl in *. inversion H as [[H1 H2]].
        apply IHl1 in H2. reflexivity.

        simpl in H.
        apply app_cons_nil2 in H. destruct H as [H1 H2].
        rewrite H2. apply IHl1 in H1. rewrite H1. 
        reflexivity.
Qed.

Lemma rev_refl : forall {A : Type} (l : list A),
  List.rev (List.rev l) = l.
Proof.
  induction l. reflexivity.
  simpl. rewrite List.rev_app_distr.
  simpl. rewrite IHl. reflexivity.
Qed.

(* Lemma rev__seq_FOv2 : forall n xn,
(Var (xn + n) :: List.rev (seq_FOv (Var xn) n))%list = 
List.rev (seq_FOv (Var xn) (S n)).
Proof.
  intros n xn. apply rev_eq.
  simpl. rewrite rev_refl.
  rewrite List.rev_app_distr.
  rewrite rev_refl. simpl.
  apply rev_eq. simpl.
  rewrite List.rev_app_distr.
  simpl.
   rewrite List.rev_app_distr.



 rewrite List.rev_append. rewrite IHl.
 rewrite List.rev_refl.

  induction n; intros xn. simpl. rewrite <- plus_n_O.
    reflexivity.

    simpl. 

 do 3 rewrite rev__seq_FOv. rewrite <- IHn.
    simpl. rewrite IHn. *)

Lemma seq_FOv_rand1 : forall n xn,
(seq_FOv (Var xn) n ++ Var (xn + n) :: nil)%list = (Var xn :: seq_FOv (Var (S xn)) n)%list.
Proof.
  induction n; intros xn. simpl.
    rewrite <- plus_n_O. reflexivity.

  simpl. rewrite <- IHn. simpl. rewrite
  plus_n_Sm. reflexivity.
Qed.

Lemma rev_seq_FOv__2 : forall n x,
  rev_seq_FOv x n = rev_seq_FOv2 x n.
Proof. 
  unfold rev_seq_FOv2.
  induction n; intros x. reflexivity.
    simpl. destruct x as [xn]. simpl. rewrite IHn.
    apply rev_eq. simpl.
    rewrite rev_refl. rewrite List.rev_app_distr.
    simpl. rewrite rev_refl.
    rewrite seq_FOv_rand1. reflexivity.
Qed.

Lemma rev_seq_FOv_cons : forall m n,
  rev_seq_FOv (Var n) (S m) = cons (Var (n + ( m))) (rev_seq_FOv (Var n) m).
Proof.
  reflexivity.
Qed.

Lemma rev_seq_FOv2_cons : forall m n,
  rev_seq_FOv2 (Var n) (S m) = cons (Var (n + ( m))) (rev_seq_FOv2 (Var n) m).
Proof.
  intros m n.
  rewrite <- rev_seq_FOv__2. rewrite rev_seq_FOv_cons.
  rewrite rev_seq_FOv__2. reflexivity.
Qed.

Lemma max_FOv_list_closed_exFO_max : forall lv alpha zn,
  is_in_FOvar (Var zn) (FOvars_in alpha) = true ->
  max zn (max_FOv (list_closed_exFO alpha lv)) = 
  max_FOv (list_closed_exFO alpha lv).
Admitted.

(* 
Let alpha := (conjSO (eqFO (Var 1) (Var 2)) 
              (conjSO (eqFO (Var 3) (Var 2))
                      (eqFO (Var 8) (Var 8)))).
Let beta := conjSO (eqFO (Var 3) (Var 2)) 
                   (eqFO (Var 9) (Var 4)).
Let lv := cons (Var 1) (cons (Var 1) (cons (Var 3) nil)).
Eval compute in (rename_FOv_A alpha beta lv).
Eval compute in (replace_FOv_l alpha lv (seq_FOv 
    (Var (S (max_FOv (conjSO beta (list_closed_exFO alpha lv)))))  (length lv))).
Eval compute in ((rename_FOv_A alpha beta lv) =(replace_FOv_l alpha lv (seq_FOv 
    (Var (S (max_FOv (conjSO beta (list_closed_exFO alpha lv)))))  (length lv)))).
Let l1 := (cons (Var 1) (cons (Var 3) (cons (Var 2) nil))).
Let l2 := (cons (Var 2) (cons (Var 1) (cons (Var 4) nil))).
Eval compute in (replace_FOv_l alpha l1 l2).
 *)

Fixpoint pio_FOv (x : FOvariable) (l : list FOvariable) : list FOvariable :=
  match l with
  | nil => cons x nil
  | cons y l' => 
      if match x, y with Var xn, Var ym => Nat.leb xn ym end
       then cons x l else cons y (pio_FOv x l')
  end.

Fixpoint sort_FOv_flag (l1 l2 : list FOvariable) :=
  match l1 with 
  | nil => l2
  | cons x l1' => sort_FOv_flag l1' (pio_FOv x l2)
  end.

(* Require Import List.

Fixpoint merge l1 l2 :=
  let fix merge_aux l2 :=
  match l1, l2 with
  | nil, _ => l2
  | _, nil => l1
  | a1::l1', a2::l2' =>
      if Nat.leb a1 a2 then a1 :: merge l1' l2 else a2 :: merge_aux l2'
  end
  in merge_aux l2.
*)



Fixpoint pio_FOv2 (x : FOvariable) (l2 l3 : list FOvariable) : list FOvariable :=
  match l2, l3 with
  | nil, _ => cons x l3
  | _, nil => cons x l3
  | cons x1 l2', cons x2 l3' =>
      if match x, x1 with Var xn, Var ym => Nat.leb xn ym end
        then cons x l3 else cons x2 (pio_FOv2 x l2' l3')
  end. 

Fixpoint sort_FOv_flag2 (l1 l2 l3 : list FOvariable) :=
  match l1 with 
  | nil => l3
  | cons x l1' => sort_FOv_flag2 l1' (pio_FOv x l2) (pio_FOv2 x l2 l3)
  end.
(* 
Fixpoint sort_FOv_flag3 (l1 l2 l3 l4 : list FOvariable) :=
  match l1 with 
  | nil => l3
  | cons x l1' => sort_FOv_flag2 l1' (pio_FOv x l2) (pio_FOv2 x l2 l3 l4)
  end.

Let l := (cons (3) (cons ( 5) (cons ( 4) (cons ( 8) (cons ( 4) nil))))).
Let l1 := (cons (Var 1) (cons (Var 2) (cons (Var 3) (cons (Var 2) nil)))).
Let l2 := (cons (Var 2) (cons (Var 4) (cons (Var 2) (cons (Var 4) nil )))).

Eval compute in (sort_FOv_flag2 l1 nil l2).
Eval compute in (sort_FOv_flag l1 nil).


Definition sort_FOv (l : list FOvariable) : list FOvariable :=
  sort_FOv_flag l nil.
 *)

Lemma rep_FOv_double : forall alpha x y,
  replace_FOv (replace_FOv alpha x y) x y = replace_FOv alpha x y.
Proof.
  intros alpha [xn] [ym].
  case_eq (beq_nat xn ym); intros Hbeq.
    rewrite (beq_nat_true _ _ Hbeq) in *.
    rewrite rep_FOv_refl. reflexivity.

    rewrite rep_FOv_not_occ. reflexivity.
    apply x_occ_in_alpha_rep_FOv_f.
    apply beq_nat_false_FOv. assumption.
Qed.

Lemma ren_FOv_list_refl : forall l x,
  rename_FOv_list l x x = l.
Admitted.

Lemma rep_FOv_double2 : forall alpha x y,
  replace_FOv (replace_FOv alpha x y) y x =
  replace_FOv alpha y x.
Admitted.

Lemma rep_FOv_double3 : forall alpha x y z,
  replace_FOv (replace_FOv alpha x y) z y = replace_FOv (replace_FOv alpha z y) x y.
Proof.
Admitted.

Lemma rep_FOv_double4 : forall alpha x y z,
  replace_FOv (replace_FOv alpha x y) y z =
  replace_FOv (replace_FOv alpha x z) y z.
Proof.
Admitted.

Lemma rem_dups_FOv_double : forall l x,
  ~ rem_dups_FOv l = (cons x (cons x l)).
Admitted.

Lemma rem_dups_FOv_cons2 : forall l x,
  rem_dups_FOv (cons x l) = cons x l ->
  rem_dups_FOv l = l.
Proof.
  induction l; intros [xn] H. reflexivity.
  pose proof (rem_dups_FOv_cons _ _ H) as H5.
  simpl in *. destruct a as [ym].
  case_eq (beq_nat xn ym); intros Hbeq; rewrite Hbeq in *.
    discriminate.
  rewrite H5 in *.
  case_eq (is_in_FOvar (Var ym) l); intros Hin; rewrite Hin in *.
    inversion H as [H1]. reflexivity.

    rewrite (IHl (Var ym)). reflexivity.
    rewrite Hin. inversion H as [H1]. do 2 rewrite H1. reflexivity.
Qed.

Lemma rep_FOv__l2 : forall l1 l2 x y alpha,
length l1 = length l2 ->
(* is_in_FOvar x l1 = true -> *)
is_in_FOvar x l2 = true ->
rem_dups_FOv l2 = l2 ->
replace_FOv (replace_FOv_l alpha l1 l2) x y = 
replace_FOv (replace_FOv_l alpha l1 (rename_FOv_list l2 x y)) x y.
Proof.
  induction l1; intros l2 [xn] [ym]  alpha Hl Hin2 Hrem.
    simpl. reflexivity.
  simpl. destruct l2. discriminate.
  pose proof (rem_dups_FOv_cons _ _ Hrem) as Hrem2.
  apply rem_dups_FOv_cons2 in Hrem.
  simpl. destruct f as [zn].
  simpl in *. destruct a as [un].
  inversion Hl as [Hl'].

  case_eq (beq_nat xn zn); intros Hbeq; rewrite Hbeq in *.
    rewrite (beq_nat_true _ _ Hbeq).
    case_eq (is_in_FOvar (Var zn) l2); intros Hin3.
       2 : (rewrite ren_FOv_list_not_in; [
       rewrite rep_FOv_double4;  reflexivity |  assumption]).

    rewrite rep_FOv_double4.
    case_eq (beq_nat un zn); intros Hbeq2.
      rewrite (beq_nat_true _ _ Hbeq2).
      do 2 rewrite rep_FOv_double. apply IHl1; assumption.

      case_eq (beq_nat un ym); intros Hbeq3.
        rewrite (beq_nat_true _ _ Hbeq3) in *.
        do 2 rewrite rep_FOv_refl. apply IHl1; assumption.

        case_eq (beq_nat zn ym); intros Hbeq4.
          rewrite (beq_nat_true _ _ Hbeq4) in *.
          do 2 rewrite rep_FOv_refl. rewrite ren_FOv_list_refl.
          reflexivity.

          rewrite rep_FOv_double3. rewrite IHl1.
          rewrite rep_FOv_double3. reflexivity.
          all : try assumption.

    case_eq (beq_nat un zn); intros Hbeq2.
      rewrite (beq_nat_true _ _ Hbeq2).
      do 2 rewrite rep_FOv_refl. apply IHl1; assumption.

      case_eq (beq_nat xn ym); intros Hbeq3.
        rewrite (beq_nat_true _ _ Hbeq3) in *. 
        rewrite ren_FOv_list_refl. reflexivity.

        case_eq (beq_nat xn un); intros Hbeq4.
          rewrite <- (beq_nat_true _ _ Hbeq4).
          rewrite (rep_FOv_not_occ _ (Var xn) (Var ym)).
          rewrite (rep_FOv_not_occ _ (Var xn) (Var ym)).
          case_eq (is_in_FOvar (Var xn) l1); intros Hin3.
            rewrite (rep_FOv_not_occ 
              (replace_FOv_l alpha l1 (rename_FOv_list l2 (Var xn) (Var ym))) (Var xn) (Var zn)).
            specialize (IHl1 l2 (Var xn) (Var ym) alpha).
            rewrite (rep_FOv_not_occ (replace_FOv_l alpha l1 (rename_FOv_list _ _ _ )) (Var xn) (Var ym)) in IHl1.
            rewrite <- IHl1. 
            rewrite IHl1.
            simpl in IHl1.
Admitted.







(* Left it here 25/01/18. Doesn't work, I think. See counterexample 
in notes. Try to make work though. *)

(* Lemma rep_FOv__l2 : forall l1 l2 x y alpha,
length l1 = length l2 ->
(* is_in_FOvar x l1 = true -> *)
is_in_FOvar x l2 = true ->
replace_FOv (replace_FOv_l alpha l1 l2) x y = 
replace_FOv (replace_FOv_l alpha l1 (rename_FOv_list l2 x y)) x y.
Proof.
  induction l1; intros l2 [xn] [ym]  alpha Hl Hin2.
    simpl. reflexivity.
  simpl. destruct l2. discriminate.
  simpl. destruct f as [zn].
  simpl in *. destruct a as [un].
  inversion Hl as [Hl'].

  case_eq (beq_nat xn zn); intros Hbeq; rewrite Hbeq in *.
    rewrite (beq_nat_true _ _ Hbeq).
    case_eq (is_in_FOvar (Var zn) l2); intros Hin3.
       2 : (rewrite ren_FOv_list_not_in; [
       rewrite rep_FOv_double4;  reflexivity |  assumption]).

    rewrite rep_FOv_double4.
    case_eq (beq_nat un zn); intros Hbeq2.
      rewrite (beq_nat_true _ _ Hbeq2).
      do 2 rewrite rep_FOv_double. apply IHl1; assumption.

      case_eq (beq_nat un ym); intros Hbeq3.
        rewrite (beq_nat_true _ _ Hbeq3) in *.
        do 2 rewrite rep_FOv_refl. apply IHl1; assumption.

        case_eq (beq_nat zn ym); intros Hbeq4.
          rewrite (beq_nat_true _ _ Hbeq4) in *.
          do 2 rewrite rep_FOv_refl. rewrite ren_FOv_list_refl.
          reflexivity.

          rewrite rep_FOv_double3. rewrite IHl1.
          rewrite rep_FOv_double3. reflexivity.
          all : try assumption.

    case_eq (beq_nat un zn); intros Hbeq2.
      rewrite (beq_nat_true _ _ Hbeq2).
      do 2 rewrite rep_FOv_refl. apply IHl1; assumption.

      case_eq (beq_nat xn ym); intros Hbeq3.
        rewrite (beq_nat_true _ _ Hbeq3) in *. 
        rewrite ren_FOv_list_refl. reflexivity.

        case_eq (beq_nat xn un); intros Hbeq4.
          rewrite <- (beq_nat_true _ _ Hbeq4).
          rewrite (rep_FOv_not_occ _ (Var xn) (Var ym)).
          rewrite (rep_FOv_not_occ _ (Var xn) (Var ym)).
          case_eq (is_in_FOvar (Var xn) l1); intros Hin3.
            rewrite (rep_FOv_not_occ 
              (replace_FOv_l alpha l1 (rename_FOv_list l2 (Var xn) (Var ym))) (Var xn) (Var zn)).
            
Admitted. *)
(*
            reflexivity.
            

          apply IHl1.
          
Lemma
  replace_FOv (replace_FOv alpha x y) (
          rewrite rep_FOv_double4.

      case_eq (beq_nat un ym); intros Hbeq3.
        rewrite (beq_nat_true _ _ Hbeq3) in *.






        rewrite <- rep_FOv_double2. apply IHl1; assumption.

        case_eq (beq_nat zn ym); intros Hbeq4.
          rewrite (beq_nat_true _ _ Hbeq4) in *.
          do 2 rewrite rep_FOv_refl. rewrite ren_FOv_list_refl.
          reflexivity.

          rewrite rep_FOv_double3. rewrite IHl1.
          rewrite rep_FOv_double3. reflexivity.
          all : try assumption.



Lemma rep_FOv_double_switch : forall alpha x y u v,
  ~ x = u ->
  ~
  replace_FOv (replace_FOv alpha x y) u v =
  replace_FOv (replace_FOv alpha u v) x y.

      

admit.
    

    case_eq (beq_nat 
    rewrite IHl1.

  case_eq (is_in_FOvar (Var zn) l2); intros Hin3.

    rewrite (beq_nat_true _ _ Hbeq) in *.
    case_eq (beq_nat un zn); intros Hbeq2.
      rewrite (beq_nat_true _ _ Hbeq2) in *.
      rewrite rep_FOv_refl.
        case_eq (is_in_FOvar (Var zn) l2); intros Hin4.
          rewrite IHl1.
          rewrite rep_FOv_double. reflexivity.
          all : try assumption.

          rewrite ren_FOv_list_not_in.
          rewrite rep_FOv_double. reflexivity.
          assumption.
      
        case_eq (beq_nat zn ym); intros Hbeq3.
          rewrite (beq_nat_true _ _ Hbeq3).
          rewrite ren_FOv_list_refl. reflexivity.

            case_eq (beq_nat un ym); intros Hbeq5.
              rewrite (beq_nat_true _ _ Hbeq5) in *.
              rewrite rep_FOv_refl.
              rewrite rep_FOv_double2.
              rewrite <- IHl1. reflexivity. all : try assumption.

              rewrite rep_FOv_double3.
              rewrite <- IHl1. rewrite rep_FOv_double3.
              rewrite rep_FOv_double4. reflexivity. assumption.
              assumption.

    rewrite (beq_nat_true _ _ Hbeq).
    case_eq (beq_nat un zn); intros Hbeq2.
      rewrite (beq_nat_true _ _ Hbeq2) in *.
      rewrite rep_FOv_refl.
      rewrite <- (beq_nat_true _ _ Hbeq2) in *.
      rewrite ren_FOv_list_not_in.
      rewrite rep_FOv_double.
      reflexivity. assumption.

      rewrite rep_FOv_double4. rewrite rep_FOv_double3.
      rewrite ren_FOv_list_not_in.
      rewrite rep_FOv_double3. reflexivity. assumption.

(* -- *)

    case_eq (is_in_FOvar (Var xn) l2); intros Hin3.
      2 : rewrite ren_FOv_list_not_in;[ reflexivity | assumption].

    case_eq (beq_nat un xn); intros Hbeq2.
      rewrite (beq_nat_true _ _ Hbeq2) in *.
      case_eq (beq_nat xn ym); intros Hbeq3.
        rewrite (beq_nat_true _ _ Hbeq3).
        do 2 rewrite rep_FOv_refl. rewrite ren_FOv_list_refl.
        reflexivity.

        rewrite (rep_FOv_not_occ _ (Var xn)).
2 : (apply x_occ_in_alpha_rep_FOv_f; apply beq_nat_false_FOv;
  assumption).
        rewrite (rep_FOv_not_occ _ (Var xn) (Var ym)).
        rewrite IHl1. reflexivity.
        case_eq (is_in_FOvar (Var xn) l1); intros Hin4.
          
      rewrite rep_FOv_double3.



      all : try assumption.

    

      
      
      

 rewrite IHl1.

  apply IHl1; assumption.


      
        case_eq (beq_nat zn ym); intros Hbeq3.
          rewrite (beq_nat_true _ _ Hbeq3).
          rewrite rep_FOv_double3. rewrite IHl1.
          rewrite rep_FOv_double3. reflexivity.
          all : try assumption.

          case_eq (beq_nat un ym); intros Hbeq5.
            rewrite (beq_nat_true _ _ Hbeq5) in *.
            rewrite <- IHl1.
            rewrite IHl1. reflexivity.
            rewrite rep_FOv_double4.
            rewrite <- IHl1. reflexivity. all : try assumption.

            rewrite rep_FOv_double3.
            rewrite <- IHl1. rewrite rep_FOv_double3.
            rewrite rep_FOv_double4. reflexivity. assumption.
            assumption.
              

              rewrite ren_FOv_list_not_in. reflexivity.
               assumption. rewrite rep_FOv_double4.
              reflexivity. assumption.

    

                    case_eq (is_in_FOvar (Var zn) l2); intros Hin4.
          rewrite IHl1.
          rewrite rep_FOv_double. reflexivity.
          all : try assumption.

          rewrite ren_FOv_list_not_in.
          rewrite rep_FOv_double. reflexivity.
          assumption.

            


            reflexivity.

            rewrite rep_FOv_double2.
           rewrite IHl1.
Search rename_FOv_list is_in_FOvar.


Lemma rep_FOv_double2 : forall alpha x y,
  replace_FOv (replace_FOv alpha x y) y x =
  replace_FOv alpha y x.

(*         case_eq (beq_nat zn ym); intros Hbeq4.
          rewrite (beq_nat_true _ _ Hbeq4) in *.
          do 2 rewrite rep_FOv_refl. rewrite ren_FOv_list_refl.
          reflexivity.
 *)

Search replace_FOv.

Lemma
  ~ 
  replace_FOv (replace_FOv alpha x y) z y =
  replace_FOv (replace_FOv alpha z y) x y.

rep_FOv__l_switch
          rewrite <- IHl1.
          rewrite IHl1. reflexivity.

 rewrite ren_FOv_list_refl.
Search rename_FOv_list is_in_FOvar.

*)

(* Lemma rep_FOv__l2 : forall l1 l2 x y alpha,
length l1 = length l2 ->
is_in_FOvar x l1 = true ->
is_in_FOvar x l2 = true ->
replace_FOv (replace_FOv_l alpha l1 l2) x y = 
replace_FOv_l alpha l1 (rename_FOv_list l2 x y).
Proof.
  induction l1; intros l2 [xn] [ym]  alpha Hl Hin1 Hin2. discriminate.
  simpl. destruct l2. discriminate.
  simpl. destruct f as [zn].
  simpl in *. destruct a as [un].
  case_eq (beq_nat xn zn); intros Hbeq; rewrite Hbeq in *.
    case_eq (beq_nat xn un); intros Hbeq2; rewrite Hbeq2 in *.
      rewrite (beq_nat_true _ _ Hbeq) in *. rewrite (beq_nat_true _ _ Hbeq2).
      rewrite rep_FOv_refl.
      case_eq (is_in_FOvar (Var un) l1); intros Hin3.
        case_eq (is_in_FOvar (Var un) l2); intros Hin4.
          rewrite IHl1.

 rewrite IHl1.
Search replace_FOv.
    
    rewrite IHl1. 
    simpl.
Search replace_FOv replace_FOv_l is_in_FOvar.
    simpl. 
Admitted.
 *)

Lemma rem_dups_FOv_decr_strict_FOv: forall l,
  decr_strict_FOv l = true ->
  rem_dups_FOv l = l.
Proof.
  induction l; intros H. reflexivity.
  simpl in *. destruct l. reflexivity.
  remember (cons f l) as t.
  destruct a as [xn]. destruct xn. discriminate.
  apply if_then_else_ft in H. destruct H as [H1 H2].
  rewrite sS_lem_f7_gen_pre. rewrite IHl. reflexivity. assumption.
  assumption.
Qed.

Fixpoint pio x l : list FOvariable := 
  match l with
  | nil => cons x nil
  | cons y l' => if match x,y with Var xn, Var ym =>
    Nat.leb ym xn end then cons x l else cons y (pio x l')
  end.

Fixpoint pio2 x1 l1 x2 l2 : list FOvariable := 
  match l1, l2 with
  | nil, _ => cons x2 l2
  | _, nil => cons x2 l2
  | cons y1 l1', cons y2 l2' => if match x1, y1 with Var xn, Var ym =>
      Nat.leb ym xn end then cons x2 l2 else cons y2 (pio2 x1 l1' x2 l2')
  end.

Fixpoint pio_l l1 l2 : list FOvariable :=
  match l1 with
  | nil => l2
  | cons x l1' => pio_l l1' (pio x l2)
  end.

Fixpoint pio2_l l1 l2 l1' l2' : list FOvariable :=
  match l1, l1' with
  | nil, _ => l2'
  | _, nil => l2'
  | cons x1 ll1, cons x1' ll1' => pio2_l ll1 (pio_l ll1 (pio x1 l2)) ll1' (pio2 x1 l2 x1' l2')
  end.

Definition order1 l : list FOvariable :=
  pio_l l nil.

Definition order2 l1 l2 : list FOvariable :=
  pio2_l l1 nil l2 nil.

Fixpoint diff_l l1 l2 :=
  match l1, l2 with
  | cons x1 l1', cons x2 l2' =>
    if match x1, x2 with Var xn, Var ym =>
      beq_nat xn ym end then diff_l l1' l2'    
      else cons x1 (diff_l l1' l2') 
  | _ , _=> nil
  end.

Fixpoint diff_r l1 l2 :=
  match l1, l2 with
  | cons x1 l1', cons x2 l2' =>
    if match x1, x2 with Var xn, Var ym =>
      beq_nat xn ym end then diff_r l1' l2'    
      else cons x2 (diff_r l1' l2') 
  | _ , _=> nil
  end.


(* Let l1 := cons (Var 1) (cons (Var 2) (cons (Var 3) (cons (Var 2) nil))).
Let l2 := cons (Var 2) (cons (Var 4) (cons (Var 2) (cons (Var 4) nil))).
Eval compute in (order1 l2).
Eval compute in (order2 l2 l1). *)


(* emma consistent_lx_lx_order1_2_x : forall (l1 l2 : list FOvariable) (x y: FOvariable),
length l1 = length l2 ->
exists (a : FOvariable) (n : nat),
  @ind_gen _ y (indicies_l2_FOv (order2 l2 l1) x) (order1 l2) = constant_l a n.
Proof.
  induction l1; intros l2 [xn] [ym] Hl.
    destruct l2. 2 : discriminate.
    simpl. exists (Var 0). exists 0.
    reflexivity.

    destruct l2. discriminate.
    unfold order2. simpl. unfold order1. simpl.
    unfold order2 in IHl1.
    unfold order1 in*. simpl in *.




    simpl.

    destruct
    simpl.

Lemma consistent_lx_lx_order1_2_x : forall l1 l2 x,
  length l1 = length l2 ->
  consistent_lx_lx_x (order2 l2 l1) (order1 l2) x.
Proof.
  unfold consistent_lx_lx_x. unfold is_constant.
  

Lemma consistent_lx_lx_order1_2 : forall l1 l2,
  length l1 = length l2 ->
  consistent_lx_lx (order2 l2 l1) (order1 l2).
Proof.
  unfold consistent_lx_lx.
 *)

Lemma order2_nil : forall l,
  order2 l nil = nil.
Proof.
  unfold order2.
  destruct l; reflexivity.
Qed.

Lemma diff_r_refl : forall l,
  diff_r l l = nil.
Proof.
  induction l. reflexivity.
  simpl. destruct a . rewrite <- beq_nat_refl.
  assumption.
Qed.

Fixpoint rem_FOv_l l l2 :=
  match l2 with
  | nil => l
  | cons y l2' => rem_FOv (rem_FOv_l l l2') y  
  end.

Lemma is_in_FOvar_l_ren_FOv_list_gen : forall l x y,
is_in_FOvar_l (rename_FOv_list l x y)
  (rem_FOv l x ++ y :: nil) = true.
Proof.
  induction l; intros [xn] [ym]. reflexivity.
  simpl. destruct a as [zn]. case_eq (beq_nat xn zn);
    intros Hbeq. simpl.
    rewrite is_in_FOvar_app. simpl.
    rewrite <- beq_nat_refl. rewrite if_then_else_true.
    apply IHl.

    simpl. rewrite <- beq_nat_refl.
    apply is_in_FOvar_l_cons_r2.
    apply IHl.
Qed.

Lemma is_in_FOvar_rep_FOv : forall alpha x y,
is_in_FOvar_l (FOvars_in (replace_FOv alpha x y))
(app (rem_FOv (FOvars_in alpha) x) (cons y nil)) = true.
Proof.
  intros alpha x y.
  rewrite rep__ren_FOv.
  rewrite FOvars_in_rename_FOv.
  apply is_in_FOvar_l_ren_FOv_list_gen.
Qed.


Lemma is_in_FOvar_l_app_cons: forall l l1 l2 x,
  is_in_FOvar_l l (app l1 (cons x l2)) =
  is_in_FOvar_l l (cons x (app l1 l2)).
Proof.
  induction l; intros l1 l2 [xn]. reflexivity.
  simpl. destruct a as [ym].
  rewrite is_in_FOvar_app_comm. simpl.
  case_eq (beq_nat ym xn); intros Hbeq.
    apply IHl.
  rewrite is_in_FOvar_app_comm.
  case_eq (is_in_FOvar (Var ym) (app l1 l2));
    intros Hin. apply IHl.
    reflexivity.
Qed.

Lemma is_in_FOvar_l_cons_cons : forall l1 l2 x,
  is_in_FOvar_l l1 l2 = true ->
  is_in_FOvar_l (cons x l1) (cons x l2) = true.
Proof.
  intros l1 l2 [xn] H.
  simpl. rewrite <- beq_nat_refl.
  apply is_in_FOvar_l_cons_r2. assumption.
Qed.

Lemma is_in_FOvar_l_rem_FOv_app : forall l1 l2 l3 x,
  is_in_FOvar_l (rem_FOv l1 x) (app (rem_FOv l2 x) l3) =
  is_in_FOvar_l (rem_FOv l1 x) (rem_FOv (app l2 l3) x).
Proof.
  induction l1; intros l2 l3 [xn]. reflexivity.
  simpl. destruct a as [ym]. case_eq (beq_nat xn ym);
    intros Hbeq. apply IHl1.

    simpl. rewrite rem_FOv_app at 1.
    rewrite is_in_FOvar_app.
    rewrite is_in_FOvar_app.
    case_eq (is_in_FOvar (Var ym) (rem_FOv l2 (Var xn)));
      intros Hin. apply IHl1.
    rewrite want13. 
    case_eq (is_in_FOvar (Var ym) l3); intros Hin2.
      apply IHl1. reflexivity.
      apply beq_nat_false_FOv. assumption.
Qed.

Lemma is_in_FOvar_l_rem_FOv  : forall l1 l2 x,
  is_in_FOvar_l l1 l2 = true ->
  is_in_FOvar_l (rem_FOv l1 x) (rem_FOv l2 x) = true.
Proof.
  induction l1; intros l2 [xn] H. reflexivity.
  destruct a as [ym]. simpl in *.
  apply if_then_else_ft in H. destruct H as [H1 H2].
  case_eq (beq_nat xn ym); intros Hbeq.
    apply IHl1. assumption.

    simpl. rewrite want13. rewrite H1.
    apply IHl1. assumption.
      apply beq_nat_false_FOv. assumption.
Qed.

Lemma is_in_FOvar_rep_FOv_l : forall l1 l2 alpha,
length l1 = length l2 ->
is_in_FOvar_l (FOvars_in (replace_FOv_l alpha l1 l2))
(app (rem_FOv_l (FOvars_in alpha) l1) l2) = true.
Proof.
  induction l1; intros l2 alpha H. simpl.
    apply is_in_FOvar_l_app_l1. apply is_in_FOvar_l_refl.

    simpl. destruct l2. discriminate.
    apply (is_in_FOvar_l_trans _ _ _ (is_in_FOvar_rep_FOv _ _ _)).
    rewrite is_in_FOvar_l_app_cons_nil.
    rewrite is_in_FOvar_l_app_cons.
    apply is_in_FOvar_l_cons_cons.
    rewrite is_in_FOvar_l_rem_FOv_app.
    apply is_in_FOvar_l_rem_FOv.
    apply IHl1.
    simpl in H. inversion H. reflexivity.
Qed.

Lemma FOvars_in_rep_FOv : forall alpha x y,
  FOvars_in (replace_FOv alpha x y) =
  rename_FOv_list (FOvars_in alpha) x y.
Proof.
  induction alpha; intros [xn] [ym].
    simpl. destruct p. destruct f as [zn].
    case_eq (beq_nat xn zn); intros Hbeq; reflexivity.

    destruct f as [z1]. destruct f0 as [z2].
    simpl. 
    case_eq (beq_nat xn z1); case_eq (beq_nat xn z2);
      reflexivity.

    destruct f as [z1]. destruct f0 as [z2].
    simpl. 
    case_eq (beq_nat xn z1); case_eq (beq_nat xn z2);
      reflexivity.

    destruct f as [zn]. simpl.
    case_eq (beq_nat xn zn); intros Hbeq;
      simpl; rewrite IHalpha; reflexivity.

    destruct f as [zn]. simpl.
    case_eq (beq_nat xn zn); intros Hbeq;
      simpl; rewrite IHalpha; reflexivity.

    simpl. apply IHalpha.

    simpl. rewrite IHalpha1. rewrite IHalpha2.
    rewrite rename_FOv_list_app. reflexivity.

    simpl. rewrite IHalpha1. rewrite IHalpha2.
    rewrite rename_FOv_list_app. reflexivity.

    simpl. rewrite IHalpha1. rewrite IHalpha2.
    rewrite rename_FOv_list_app. reflexivity.

    destruct p. simpl. rewrite IHalpha. reflexivity.

    destruct p. simpl. rewrite IHalpha. reflexivity.
Qed.

Lemma FOvars_in_rep_FOv_l : forall l1 l2 alpha,
  FOvars_in (replace_FOv_l alpha l1 l2) =
  rename_FOv_list_l (FOvars_in alpha) l1 l2.
Proof.
  induction l1; intros l2 alpha. reflexivity.
  simpl. destruct l2. reflexivity.  
  rewrite FOvars_in_rep_FOv. rewrite IHl1.
  reflexivity.
Qed.

Lemma same_struc_length_FOvars_in : forall alpha beta,
  same_struc alpha beta = true ->
  length (FOvars_in alpha) = length (FOvars_in beta).
Admitted.

Lemma app_app_length_conj : forall {A : Type} (l1 l2 l3 l4 : list A),
  app l1 l2 = app l3 l4 ->
  length l1 = length l3 ->
  l1 = l3 /\ l2 = l4.
Admitted.

Lemma same_struc_FOvars_in_eq : forall alpha beta,
  same_struc alpha beta = true ->
  FOvars_in alpha = FOvars_in beta ->
  alpha = beta.
Proof.
  induction alpha; intros beta Hs Hf;
    destruct beta; try discriminate.
    simpl in *. destruct p as [Pn].
    destruct p0 as [Qm]. rewrite (beq_nat_true _ _ Hs).
    inversion Hf as [H1]. reflexivity.

    destruct f as [z1]; destruct f0 as [z2];
    destruct f1 as [z3]; destruct f2 as [z4].
    simpl in *. inversion Hf. reflexivity.

    destruct f as [z1]; destruct f0 as [z2];
    destruct f1 as [z3]; destruct f2 as [z4].
    simpl in *. inversion Hf. reflexivity.

    destruct f as [z1]. destruct f0 as [z2].
    simpl in *. inversion Hf.
    rewrite (IHalpha beta); try assumption. reflexivity.

    destruct f as [z1]. destruct f0 as [z2].
    simpl in *. inversion Hf.
    rewrite (IHalpha beta); try assumption. reflexivity.

    simpl in *. rewrite (IHalpha beta); try assumption.
    reflexivity.

    simpl in *. apply if_then_else_ft in Hs.
    destruct Hs as [Hs1 Hs2].
    pose proof (same_struc_length_FOvars_in _ _ Hs1).
    apply app_app_length_conj in Hf.
    destruct Hf as [H1 H2]. rewrite (IHalpha1 beta1).
      rewrite (IHalpha2 beta2). reflexivity.
    all : try assumption.

    simpl in *. apply if_then_else_ft in Hs.
    destruct Hs as [Hs1 Hs2].
    pose proof (same_struc_length_FOvars_in _ _ Hs1).
    apply app_app_length_conj in Hf.
    destruct Hf as [H1 H2]. rewrite (IHalpha1 beta1).
      rewrite (IHalpha2 beta2). reflexivity.
    all : try assumption.

    simpl in *. apply if_then_else_ft in Hs.
    destruct Hs as [Hs1 Hs2].
    pose proof (same_struc_length_FOvars_in _ _ Hs1).
    apply app_app_length_conj in Hf.
    destruct Hf as [H1 H2]. rewrite (IHalpha1 beta1).
      rewrite (IHalpha2 beta2). reflexivity.
    all : try assumption.

    simpl in *. destruct p as [Pn]. destruct p0 as [Qm].
    apply if_then_else_ft in Hs. destruct Hs as [H1 H2].
    rewrite (beq_nat_true _ _ H1). rewrite (IHalpha beta);
    try assumption. reflexivity.

    simpl in *. destruct p as [Pn]. destruct p0 as [Qm].
    apply if_then_else_ft in Hs. destruct Hs as [H1 H2].
    rewrite (beq_nat_true _ _ H1). rewrite (IHalpha beta);
    try assumption. reflexivity.
Qed. 

Lemma same_struc_rep_FOv_l : forall l1 l2 alpha,
  same_struc alpha (replace_FOv_l alpha l1 l2) = true.
Admitted.

Lemma is_in_FOvar_ren_FOv_list_l : forall l1 l2 l x,
  is_in_FOvar x l1 = true ->
  is_in_FOvar x l2 = false ->
  is_in_FOvar x (rename_FOv_list_l l l1 l2) = false.
Admitted.

Lemma ren_FOv_list_trans : forall l x y z,
  ~ x = y ->
  rename_FOv_list (rename_FOv_list l x y) y z =
  rename_FOv_list (rename_FOv_list l x z) y z.
Proof.
  induction l; intros [xn] [ym] [zn] H. reflexivity.
  simpl. destruct a as [un]. case_eq (beq_nat xn un); intros Hbeq.
    simpl. rewrite <- beq_nat_refl.
    case_eq (beq_nat ym zn); intros Hbeq2;
    rewrite (IHl); try reflexivity; try assumption.

    simpl. case_eq (beq_nat ym un); intros Hbeq2.
      rewrite IHl. reflexivity. assumption.

      rewrite IHl. reflexivity. assumption.
Qed.

Lemma ren_FOv_list_switch : forall l x y z,
  rename_FOv_list (rename_FOv_list l x y) z y =
  rename_FOv_list (rename_FOv_list l z y) x y.
Admitted.

Lemma ren_FOv_list__l_is_in : forall l1 l2 l x y,
  ~ l1 = nil ->
  ~ l2 = nil ->
  is_in_FOvar x l1 = false ->
  is_in_FOvar x l2 = true ->
  rename_FOv_list (rename_FOv_list_l l l1 l2) x y = 
  rename_FOv_list_l l l1 (rename_FOv_list l2 x y).
Proof.
Admitted.
(*
  induction l1; intros l2 l [xn] [ym] H1 H2 Hin1 Hin2.
    contradiction (H1 eq_refl).

    destruct l2. contradiction (H2 eq_refl).

    destruct l1. simpl. destruct f as [zn].
destruct l2.
      simpl in *. case_eq (beq_nat xn zn); intros Hbeq;
        rewrite Hbeq in *. destruct a as [un].
        rewrite (beq_nat_true _ _ Hbeq).
        rewrite ren_FOv_list_trans.
        rewrite ren_FOv_list_switch.
case_eq (beq_nat xn un); intros Hbeq2; rewrite Hbeq2 in *.
discriminate.
        

        rewrite ren_FOv_list_not_in.
Search rename_FOv_list.




Search rename_FOv_list is_in_FOvar.
        rewrite IHl1.

 apply if_then_else_ft in Hin2. 
admit.
*)

Lemma ind_gen_ind_l2_FOv_constant_l : forall l x x0,
  exists n, @ind_gen _ x0 (indicies_l2_FOv l x) l = constant_l x n.
Proof.
  induction l; intros [xn] x0.
    simpl. exists 0. reflexivity.

    unfold indicies_l2_FOv in *.
    simpl in *. destruct a as [ym].
    case_eq (beq_nat xn ym); intros Hbeq;
      simpl; rewrite ind_gen_FOv_pre_cons.
      destruct (IHl (Var ym) x0) as [n IH];
      rewrite (beq_nat_true _ _ Hbeq).
      rewrite IH. exists (S n). reflexivity.

      destruct (IHl (Var xn) x0) as [n IH].
      exists n. assumption.
Qed.

Lemma ind_gen_ind_l2_FOv_ren_FOv_list_same : forall l x y x0,
  ~ x = y ->
  exists n,
  @ind_gen _ x0 (indicies_l2_FOv l x) (rename_FOv_list l x y) = constant_l y n.
Proof.
  induction l; intros [xn] [ym] x0 H. exists 0. reflexivity.
  simpl. destruct a as [zn]. case_eq (beq_nat xn zn); intros Hbeq;
    unfold indicies_l2_FOv; simpl;
    rewrite Hbeq; simpl;
    destruct (IHl _ _ x0 H) as [n IH];
    rewrite ind_gen_FOv_pre_cons; unfold indicies_l2_FOv in IH;
    rewrite IH. 
      exists (S n); reflexivity.

      exists (n); reflexivity.
Qed.

Lemma ind_gen_ind_l2_FOv_ren_FOv_list_same3 : forall l x y x0,
  ~ x = y ->
  exists n,
  @ind_gen _ x0 (indicies_l2_FOv l y) (rename_FOv_list l x y) = constant_l y n.
Proof.
  induction l; intros [xn] [ym] x0 H. exists 0. reflexivity.
  simpl. destruct a as [zn]. case_eq (beq_nat xn zn); intros Hbeq;
    unfold indicies_l2_FOv in *; simpl.
    rewrite <- (beq_nat_true _ _ Hbeq). rewrite beq_nat_comm.
    rewrite (FOvar_neq _ _ H). rewrite ind_gen_FOv_pre_cons.
    apply IHl. assumption.

    case_eq (beq_nat ym zn); intros Hbeq2;
      simpl; rewrite ind_gen_FOv_pre_cons;
      destruct (IHl (Var xn) (Var ym) x0 H) as [n IH].
      rewrite (beq_nat_true _ _ Hbeq2) in *.
      exists (S n). rewrite IH. reflexivity.

      rewrite IH. exists n. reflexivity.
Qed.

Lemma rename_FOv_list_l_cons : forall  l1 l2 l x y t,
  cons x t = rename_FOv_list_l (cons y l) l1 l2 ->
  t = rename_FOv_list_l l l1 l2.
Admitted.

(* Lemma ind_gen_ind_l2_FOv_ren_FOv_list_same2 : forall l l1 l2 x y x0,
  ~ x = y ->
  exists n,
  @ind_gen _ x0 (indicies_l2_FOv l x) (rename_FOv_list (rename_FOv_list_l l l1 l2) x y) = constant_l y n.
Proof.
  induction l; intros l1 l2 [xn] [ym] x0 H. exists 0. reflexivity.
  simpl. destruct a as [zn]. case_eq (beq_nat xn zn); intros Hbeq;
    unfold indicies_l2_FOv; simpl;
    rewrite Hbeq; simpl;
    destruct (IHl l1 l2 _ _ x0 H) as [n IH].

remember (rename_FOv_list_l (Var zn :: l) l1 l2)  as t.
destruct t.
admit.
destruct f as [un]. simpl. case_eq (beq_nat xn un); intros Hbeq2.
  apply rename_FOv_list_l_cons in Heqt.
  rewrite Heqt in *.
    rewrite ind_gen_FOv_pre_cons; unfold indicies_l2_FOv in IH;
    rewrite IH. 
      exists (S n); reflexivity.

  pose proof Heqt as Heqt'.
  apply rename_FOv_list_l_cons in Heqt.
  rewrite Heqt in *.
    rewrite ind_gen_FOv_pre_cons; unfold indicies_l2_FOv in IH;
    rewrite IH. 
      exists (S n); reflexivity.


      exists (n); reflexivity.
Qed. *)

Lemma ind_gen_ind_l2_FOv_trans : forall l1 l2 l3 x x0,
  length l1 = length l2 ->
  length l1 = length l3 ->
  (exists n,
  @ind_gen _ x0 (indicies_l2_FOv l1 x) l2 = constant_l x n) ->
  (exists n,
  @ind_gen _ x0 (indicies_l2_FOv l2 x) l3 = constant_l x n) ->
  (exists n,
  @ind_gen _ x0 (indicies_l2_FOv l1 x) l3 = constant_l x n).
Proof.
  induction l1; intros l2 l3 [xn] x0 Hl1 Hl2 H1 H2.
    simpl in *. exists 0. reflexivity.

    unfold indicies_l2_FOv in *.
    simpl in *. destruct a as [ym].
    destruct l2. discriminate. destruct l3. discriminate.
        inversion Hl1 as [Hl1'].
        inversion Hl2 as [Hl2'].
    case_eq (beq_nat xn ym); intros Hbeq; rewrite Hbeq in *;
      simpl in *. destruct f as [vn].
      destruct H2 as [n2 H2].
      case_eq (beq_nat xn vn); intros Hbeq2; rewrite Hbeq2 in *.
        simpl in H2. destruct n2. discriminate. inversion H2.
        rewrite ind_gen_FOv_pre_cons.
        assert (exists n : nat,
   @ind_gen _ x0 (indicies_l2_FOv_pre l1 (Var xn) 0) l2 = constant_l (Var xn) n) as Hass1.
          destruct H1 as [n1 H1]. destruct n1. discriminate.
          simpl in H1. inversion H1 as [[H1a H1b]].
          rewrite ind_gen_FOv_pre_cons in H1b. rewrite H1b. exists (n1).
          reflexivity.
        assert (exists n : nat,
   @ind_gen _ x0 (indicies_l2_FOv_pre l2 (Var xn) 0) l3 = constant_l (Var xn) n) as Hass2.
          simpl in H2. inversion H2 as [[H1a H1b]].
          rewrite ind_gen_FOv_pre_cons in H1b. rewrite H1b. exists (n2).
          reflexivity.
        destruct  (IHl1 l2 l3 (Var xn) x0 Hl1' Hl2' Hass1 Hass2) as [n IH].
        rewrite IH. exists (S n). reflexivity.

        rewrite ind_gen_FOv_pre_cons in H1. destruct H1 as [n1 H1].
        destruct n1. discriminate. simpl in H1.
        inversion H1 as [[H3 H4]]. rewrite H3 in *. rewrite <- beq_nat_refl in *.
        discriminate.

      rewrite ind_gen_FOv_pre_cons. apply IHl1 with (l2 := l2); try assumption.
        destruct H1 as [n1 H1]. rewrite ind_gen_FOv_pre_cons in H1.
        exists n1. assumption.

        destruct f as [un]. destruct H2 as [n2 H2].
        case_eq (beq_nat xn un); intros Hbeq2; rewrite Hbeq2 in *;
          simpl in H2; rewrite ind_gen_FOv_pre_cons in H2;
          simpl in H2. destruct n2. discriminate.
          simpl in H2.
          inversion H2 as [[H3 H4]]. rewrite H4. exists n2. reflexivity.

          exists n2. assumption.
Qed.

Lemma ind_gen_ind_l2_FOv_trans_gen : forall l1 l2 l3 x y z x0,
  length l1 = length l2 ->
  length l1 = length l3 ->
  (exists n,
  @ind_gen _ x0 (indicies_l2_FOv l1 x) l2 = constant_l y n) ->
  (exists n,
  @ind_gen _ x0 (indicies_l2_FOv l2 y) l3 = constant_l z n) ->
  (exists n,
  @ind_gen _ x0 (indicies_l2_FOv l1 x) l3 = constant_l z n).
Proof.
  induction l1; intros l2 l3 [xn] [ym] [zn] x0 Hl1 Hl2 H1 H2.
    simpl in *. exists 0. reflexivity.

    unfold indicies_l2_FOv in *.
    simpl in *. destruct a as [un].
    destruct l2. discriminate. destruct l3. discriminate.
        inversion Hl1 as [Hl1'].
        inversion Hl2 as [Hl2'].
    destruct f as [v1]. destruct f0 as [v2].
    case_eq (beq_nat xn un); intros Hbeq; rewrite Hbeq in *;
      simpl in *.
      destruct H2 as [n2 H2]. rewrite ind_gen_FOv_pre_cons.
      destruct H1 as [n1 H1]. destruct n1. discriminate.
      simpl in H1. inversion H1 as [[H5 H6]].
      rewrite ind_gen_FOv_pre_cons in H6.
      rewrite H5 in *. rewrite <- beq_nat_refl in *.
      simpl in H2. destruct n2. discriminate. inversion H2.
      rewrite ind_gen_FOv_pre_cons in H3.
(*         assert (exists n : nat,
   @ind_gen _ x0 (indicies_l2_FOv_pre l1 (Var xn) 0) l2 = constant_l (Var xn) n) as Hass1.
          destruct H1 as [n1 H1]. destruct n1. discriminate.
          simpl in H1. inversion H1 as [[H1a H1b]].
          rewrite ind_gen_FOv_pre_cons in H1b. rewrite H1b. exists (n1).
          rewrite (beq_nat_true _ _ Hbeq) in *. rewrite (beq_nat_true _ _ Hbeq2) in *.
          rewrite H1a.
          reflexivity. *)
(*         assert (exists n : nat,
   @ind_gen _ x0 (indicies_l2_FOv_pre l2 (Var xn) 0) l3 = constant_l (Var xn) n) as Hass2.
          simpl in H2. inversion H2 as [[H1a H1b]].
          rewrite ind_gen_FOv_pre_cons in H1b. rewrite H1b. exists (n2).
          simpl in H3.
          reflexivity.
 *)        destruct  (IHl1 l2 l3 (Var xn) (Var ym) (Var zn) x0 Hl1' Hl2') as [n IH].
            exists n1. assumption.

            exists n2. assumption.
            
        rewrite IH. exists (S n). reflexivity.

      rewrite ind_gen_FOv_pre_cons in H1. rewrite ind_gen_FOv_pre_cons.
      destruct H1 as [n1 H1]. destruct H2 as [n2 H2].
      case_eq (beq_nat ym v1); intros Hbeq2; rewrite Hbeq2 in *.
        simpl in *. destruct n2. discriminate.
        simpl in H2.  inversion H2 as [[H2a H2b]].
        apply IHl1 with (l2 := l2) (y := (Var ym)); try assumption.
          exists n1. assumption.

          rewrite ind_gen_FOv_pre_cons in H2b. exists n2. assumption.

          apply IHl1 with (l2 := l2) (y := (Var ym)); try assumption.
            exists n1. assumption.

            exists n2. rewrite ind_gen_FOv_pre_cons in H2. assumption.
Qed.


(*
Lemma ind_gen_ind_l2_FOv_trans_gen : forall l1 l2 l3 x y1 y2 x0,
  length l1 = length l2 ->
  length l1 = length l3 ->
  (exists n,
  @ind_gen _ x0 (indicies_l2_FOv l1 x) l2 = constant_l y1 n) ->
  (exists n,
  @ind_gen _ x0 (indicies_l2_FOv l2 x) l3 = constant_l y2 n) ->
  (exists n,
  @ind_gen _ x0 (indicies_l2_FOv l1 x) l3 = constant_l y2 n).
Proof.
  induction l1; intros l2 l3 [xn] [y1] [y2] x0 Hl1 Hl2 H1 H2.
    simpl in *. exists 0. reflexivity.

    unfold indicies_l2_FOv in *.
    simpl in *. destruct a as [ym].
    destruct l2. discriminate. destruct l3. discriminate.
        inversion Hl1 as [Hl1'].
        inversion Hl2 as [Hl2'].
    case_eq (beq_nat xn ym); intros Hbeq; rewrite Hbeq in *;
      simpl in *. destruct f as [vn].
      destruct H2 as [n2 H2].
      case_eq (beq_nat xn vn); intros Hbeq2; rewrite Hbeq2 in *.
        simpl in H2. destruct n2. discriminate. inversion H2.
        rewrite ind_gen_FOv_pre_cons.
        assert (exists n : nat,
   @ind_gen _ x0 (indicies_l2_FOv_pre l1 (Var xn) 0) l2 = constant_l (Var xn) n) as Hass1.
          destruct H1 as [n1 H1]. destruct n1. discriminate.
          simpl in H1. inversion H1 as [[H1a H1b]].
          rewrite ind_gen_FOv_pre_cons in H1b. rewrite H1b. exists (n1).
          rewrite (beq_nat_true _ _ Hbeq) in *. rewrite (beq_nat_true _ _ Hbeq2) in *.
          rewrite H1a.
          reflexivity.
(*         assert (exists n : nat,
   @ind_gen _ x0 (indicies_l2_FOv_pre l2 (Var xn) 0) l3 = constant_l (Var xn) n) as Hass2.
          simpl in H2. inversion H2 as [[H1a H1b]].
          rewrite ind_gen_FOv_pre_cons in H1b. rewrite H1b. exists (n2).
          simpl in H3.
          reflexivity.
 *)        destruct  (IHl1 l2 l3 (Var xn) (Var y1) (Var y2) x0 Hl1' Hl2') as [n IH].
            destruct H1 as [n1 H1]. destruct n1. discriminate.
            simpl in H1. inversion H1 as [[H1a H1b]].
            rewrite ind_gen_FOv_pre_cons in H1b. rewrite H1b. exists (n1).
            rewrite (beq_nat_true _ _ Hbeq) in *. rewrite (beq_nat_true _ _ Hbeq2) in *.
            reflexivity.

            simpl in H2. inversion H2 as [[H1a H1b]].
            rewrite ind_gen_FOv_pre_cons in H1b. rewrite H1b. exists (n2).
            rewrite (beq_nat_true _ _ Hbeq) in *. rewrite (beq_nat_true _ _ Hbeq2) in *.
            reflexivity.
            
        rewrite IH. exists (S n). reflexivity.

        rewrite ind_gen_FOv_pre_cons in H1. destruct H1 as [n1 H1].
        destruct n1. discriminate. simpl in H1.
        inversion H1 as [[H3 H4]].
        rewrite ind_gen_FOv_pre_cons.
        rewrite ind_gen_FOv_pre_cons in H2.
    
 rewrite H3 in *. rewrite <- beq_nat_refl in *.
        discriminate.

      rewrite ind_gen_FOv_pre_cons. apply IHl1 with (l2 := l2); try assumption.
        destruct H1 as [n1 H1]. rewrite ind_gen_FOv_pre_cons in H1.
        exists n1. assumption.

        destruct f as [un]. destruct H2 as [n2 H2].
        case_eq (beq_nat xn un); intros Hbeq2; rewrite Hbeq2 in *;
          simpl in H2; rewrite ind_gen_FOv_pre_cons in H2;
          simpl in H2. destruct n2. discriminate.
          simpl in H2.
          inversion H2 as [[H3 H4]]. rewrite H4. exists n2. reflexivity.

          exists n2. assumption.
Qed.
 *)

Lemma ind_gen_FOv_ren_FOv_list : forall l x y z x0,
  ~ x = y ->
  ~ x = z ->
  @ind_gen _ x0 (indicies_l2_FOv l x) (rename_FOv_list l y z) =
  @ind_gen _ x0 (indicies_l2_FOv l x) l.
Proof.
  induction l; intros [xn] [ym] [zn] x0 H1 H2. reflexivity.
  unfold indicies_l2_FOv in *.
  simpl in *. destruct a as [un]. case_eq (beq_nat ym un);
    intros Hbeq. rewrite <- (beq_nat_true _ _ Hbeq).
    rewrite (FOvar_neq _ _ H1).
    simpl. do 2  rewrite ind_gen_FOv_pre_cons. apply (IHl); assumption.

    case_eq (beq_nat xn un); intros Hbeq2; simpl;
      do 2 rewrite ind_gen_FOv_pre_cons;
      rewrite IHl; try assumption;
      reflexivity.
Qed.

Lemma ind_gen_ind_l2_FOv_refl: forall l x x0,
  exists n,
  @ind_gen _ x0 (indicies_l2_FOv l x) l = constant_l x n.
Proof.
  induction l; intros [xn] x0. simpl. exists 0. reflexivity.
  unfold indicies_l2_FOv in *.
  simpl in *. destruct a as [ym].
  case_eq (beq_nat xn ym); intros Hbeq.
    simpl. rewrite ind_gen_FOv_pre_cons.
    destruct (IHl (Var xn) x0) as [n IH].
    rewrite IH. rewrite (beq_nat_true _ _ Hbeq).
    exists (S n). reflexivity.

    rewrite ind_gen_FOv_pre_cons.
    apply IHl.
Qed.

Lemma constant_l_eq : forall {A : Type} (x y : A) m n,
  constant_l x (S m) = constant_l y (S n) ->
  (x = y /\ m = n).
Admitted.

(* Lemma ind_gen_ind_l2_FOv_ren_FOv_diff : forall l l2 x y z x0,
~ x = y ->
@ind_gen _ x0 (indicies_l2_FOv l x) (rename_FOv_list l2 y z) =
@ind_gen _ x0 (indicies_l2_FOv l x) l2.
Proof.
  induction l; intros l2 [xn] [ym] [zn] x0 Hneq. reflexivity.
  unfold indicies_l2_FOv in *. simpl. destruct a as [un].
  case_eq (beq_nat xn un); intros Hbeq.
    simpl. case_eq l2. intros Hnil.
      simpl. reflexivity.
    intros [vn] lxx Hlxx. rewrite <- Hlxx.
    case_eq (rename_FOv_list l2 (Var ym) (Var zn)).
      rewrite Hlxx. simpl. case_eq (beq_nat ym vn); discriminate.
    intros [wn] lxx2 Hlxx2.
    rewrite Hlxx in Hlxx2. simpl in Hlxx2.
    case_eq (beq_nat ym vn); intros Hbeq2; rewrite Hbeq2 in *.
      inversion Hlxx2 as [[H1 H2]]. rewrite (beq_nat_true _ _ Hbeq2) in *.
       
    simpl. destruct l2. simpl. rewrite ind_gen_nil_gen.
      reflexivity.
    destruct f as [vn]. simpl.
    case_eq (beq_nat ym vn); intros Hbeq2.
      do 2 rewrite ind_gen_FOv_pre_cons.
      rewrite IHl.
      rewrite (beq_nat_true _ _ Hbeq2). reflexivity. assumption.
      simpl.

    
  simpl in *.  *)

Lemma ind_gen_ind_l2_FOv_ren_FOv_const : forall l l2 x y z1 z2 x0 n,
  ~ y = z1 ->
  @ind_gen _ x0 (indicies_l2_FOv l x) l2 = constant_l y n ->
  @ind_gen _ x0 (indicies_l2_FOv l x)
    (rename_FOv_list l2 z1 z2) = constant_l y n.
Proof.
  induction l; intros l2 [xn] [ym] [z1] [z2] x0 n Hnot H.
    simpl in *. destruct n. reflexivity. discriminate.

    unfold indicies_l2_FOv in *.
    simpl in *. destruct a as [z3].
    case_eq (beq_nat xn z3); intros Hbeq; rewrite Hbeq in *.
      simpl in *. destruct l2. simpl.
      rewrite ind_gen_nil_gen in *.  rewrite H.
      reflexivity.

      destruct f as [vn]. simpl. 
      rewrite ind_gen_FOv_pre_cons in H.
      destruct n. discriminate.
      inversion H as [[H1 H2]]. rewrite H1 in *.
      case_eq (beq_nat z1 ym); intros Hbeq2.
        rewrite (beq_nat_true _ _ Hbeq2) in Hnot.
        contradiction (Hnot eq_refl).

        rewrite ind_gen_FOv_pre_cons.
        rewrite (IHl _ _ _ _ _ _ _ Hnot H2). reflexivity.

      destruct l2. simpl in *. rewrite H. reflexivity.
      simpl in *. destruct f as [wn]. 
      rewrite ind_gen_FOv_pre_cons in H.
      case_eq (beq_nat z1 wn); intros Hbeq2;
        rewrite ind_gen_FOv_pre_cons; 
        apply IHl; assumption.
Qed.


Lemma ind_gen_ind_l2_FOv_ren_FOv_const_eq : forall l2 l x y z x0 n,
  ~ l2 = nil ->
(*   is_in_FOvar x l = true ->
   *)
  length l  = length l2 ->
  @ind_gen _ x0 (indicies_l2_FOv l x) l2 = constant_l y n ->
  @ind_gen _ x0 (indicies_l2_FOv l x)
    (rename_FOv_list l2 y z) = constant_l z n.
Proof.
  induction l2; intros l [xn] [ym] [zn] x0 n Hnot Hl H.
    contradiction (Hnot eq_refl).

    destruct l2. simpl in *. destruct a as [un].
    destruct l. simpl in *. destruct n. reflexivity. discriminate.
    destruct l. 2 : discriminate.
    unfold indicies_l2_FOv in *. simpl in *.
    destruct f as [vn]. case_eq (beq_nat xn vn);
      intros Hbeq; rewrite Hbeq in *.
      simpl in *. destruct n. discriminate. destruct n. 2 : discriminate.
      simpl in H. inversion H. rewrite <- beq_nat_refl. reflexivity.

      simpl. simpl in *. destruct n. reflexivity. discriminate. 

    unfold indicies_l2_FOv in *.
    remember (cons f l2) as l2'. destruct l. discriminate.
    simpl in *.
    destruct a as [un]. destruct f0 as [vn].
    case_eq (beq_nat xn vn); intros Hbeq; rewrite Hbeq in *.
      simpl in H. rewrite ind_gen_FOv_pre_cons in H.
      destruct n. discriminate.
      simpl in H. inversion H as [[H1 H2]].
      simpl. rewrite <- beq_nat_refl.
      rewrite ind_gen_FOv_pre_cons.
      rewrite IHl2 with (n := n). reflexivity.
      rewrite Heql2'. discriminate.
      inversion Hl. reflexivity.
      assumption.

      rewrite ind_gen_FOv_pre_cons in H.
      case_eq (beq_nat ym un); intros Hbeq2;
        rewrite ind_gen_FOv_pre_cons;
        apply IHl2. rewrite Heql2'. discriminate.
        inversion Hl. reflexivity.
        assumption.

        simpl. rewrite Heql2'. discriminate.
        inversion Hl. reflexivity.
        assumption.
Qed.

Lemma ind_l2_FOv_ren_FOv_list_l_const : forall l1 l2 l x y x0 n,
  is_in_FOvar x l1 = false ->
  ~ n = 0 ->
  @ind_gen _ x0 (indicies_l2_FOv l x) (rename_FOv_list_l l l1 l2) =
  constant_l y n ->
  y = x.
Proof.
  induction l1; intros l2 l [xn] [ym] [x0] n Hin Hnot H.
    simpl in *. destruct (ind_gen_ind_l2_FOv_refl l (Var xn) (Var x0)) as   
      [m H2]. rewrite H2 in *.
    destruct n. contradiction (Hnot eq_refl).
    destruct m. discriminate.
    apply constant_l_eq in H. symmetry. apply H.

    destruct l2. simpl in *. destruct a as [zn].
    simpl in *. destruct (ind_gen_ind_l2_FOv_refl l (Var xn) (Var x0)) as   
      [m H2]. rewrite H2 in *.
    destruct n. contradiction (Hnot eq_refl).
    destruct m. discriminate.
    apply constant_l_eq in H. symmetry. apply H.

    simpl in *. destruct a as [zn].
    apply if_then_else_tf in Hin.
    destruct Hin as [Hin1 Hin2].
    

(* 
    apply IHl1 in H
    destruct m. destruct n. 
 rewrite ind_gen_ind_l2_FOv_refl in H.
 *)Admitted.

Lemma ren_FOv_list_l_nil : forall l1 l2,
  rename_FOv_list_l nil l1 l2 = nil.
Admitted.

Lemma ren_FOv_list_l_not_nil : forall l2 l3 l1,
  ~ l1 = nil ->
  ~rename_FOv_list_l l1 l2 l3 = nil.
Proof.
  induction l2; intros l3 l1 H1 H2.
    destruct l1. contradiction (H1 eq_refl).
    discriminate.

    simpl in *. destruct l3.
    destruct l1. contradiction (H1 eq_refl).
    discriminate.

    case_eq (rename_FOv_list_l l1 l2 l3).
      intros H3. contradiction (IHl2 _ _ H1 H3).
    intros x l H. rewrite H in H2.
    destruct x as [xn]; destruct a as [ym].
    simpl in *. case_eq (beq_nat ym xn); intros Hbeq;
      rewrite Hbeq in *; discriminate.
Qed.

Lemma length_ren_FOv_list_l : forall l2 l3 l1,
  length (rename_FOv_list_l l1 l2 l3) = length l1.
Proof.
  induction l2; intros l3 l1. reflexivity.
  simpl. destruct l3. reflexivity.
  rewrite length_rename_FOv_list.
  apply IHl2.
Qed.

Lemma consistent_lx_lx_ren_FOv_list_l_pre_gen : forall l3 l4 l2 l x y n x0,
  ~ l2 = nil ->
(*   is_in_FOvar x l = true ->
   *)
  length l  = length l2 ->
  @ind_gen _ x0 (indicies_l2_FOv l x) l2 = constant_l y n ->
exists z,
  @ind_gen _ x0 (indicies_l2_FOv l x)
    (rename_FOv_list_l l2 l3 l4) = constant_l z n.
Proof.
  induction l3; intros l4 l2 l [xn] [ym] n x0 Hnot Hl H.
    simpl in *. exists (Var ym). assumption.

    simpl in *. destruct l4. exists (Var ym).
    assumption.

    apply IHl3 with (l4 := l4) in H; try assumption.
    destruct H as [[zn] H]. destruct a as [vn]. destruct f as [un].
    case_eq (beq_nat vn zn); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq) in *.
      apply (ind_gen_ind_l2_FOv_ren_FOv_const_eq) with (z := (Var un)) in H.
      exists (Var un). assumption.
        apply ren_FOv_list_l_not_nil. assumption.

        rewrite length_ren_FOv_list_l. assumption.

      apply (ind_gen_ind_l2_FOv_ren_FOv_const) with (z1 := (Var vn))
        (z2 := (Var un)) in H.
      exists (Var zn). assumption.
      apply beq_nat_false_FOv. rewrite beq_nat_comm. assumption.
Qed.
  
(* Left it here 2/02/18. *)
(* Trying the computational method. Keep ttrying this then go down. *)

Lemma consistent_lx_lx_ren_FOv_list_l_pre : forall (l1 l2 l : list FOvariable) x x0,
exists (a : FOvariable) (n : nat),
  @ind_gen _ x0 (indicies_l2_FOv l x) (rename_FOv_list_l l l1 l2) = constant_l a n.
Proof.
  intros l1 l2 l x x0.
  destruct (ind_gen_ind_l2_FOv_refl l x x0) as [n H2].
  destruct l. simpl in *. destruct n. 2 : discriminate.
  exists (Var 0). exists 0. reflexivity.
  pose proof (consistent_lx_lx_ren_FOv_list_l_pre_gen l1 l2 (cons f l) (cons f l) x x n x0) as H.
  destruct H as [z H].
    discriminate.
    reflexivity.
    assumption.

    exists z. exists n. assumption.
Qed.

Lemma consistent_lx_lx_ren_FOv_list_l : forall l1 l2 l,
consistent_lx_lx l (rename_FOv_list_l l l1 l2).
Proof.
  unfold consistent_lx_lx.
  unfold consistent_lx_lx_x.
  unfold is_constant.
  intros l1 l2 l x.
  apply (consistent_lx_lx_ren_FOv_list_l_pre _ _ _ _ (Var 0)).
Qed.

Lemma consistent_lx_lx_rep_FOv_l : forall l1 l2 alpha,
  consistent_lx_lx (FOvars_in alpha) (FOvars_in (replace_FOv_l alpha l1 l2)).
Proof.
  intros l1 l2 alpha.
  rewrite FOvars_in_rep_FOv_l.
  apply consistent_lx_lx_ren_FOv_list_l.
Qed.

Lemma rep_FOv_l_order_pre_pre : forall l x y,
rename_FOv_list l x y =
rename_FOv_list_l l
  (order2 (diff_r l (rename_FOv_list l x y))
     (diff_l l (rename_FOv_list l x y)))
  (order1 (diff_r l (rename_FOv_list l x y))).
Proof.
Admitted.

(* Lemma ren_FOv_list__l_switch : forall l1 l2 l x y,
  is_in_FOvar x l1 = false ->
  is_in_FOvar x l2 = false ->
  rename_FOv_list (rename_FOv_list_l l l1 l2) x y =
  rename_FOv_list_l (rename_FOv_list l x y) l1 l2.
Proof.
  induction l1; intros l2 l [xn] [ym] Hin1 Hin2. reflexivity.
  simpl. destruct l2. reflexivity.
  destruct a as [zn]. simpl in *.
  apply if_then_else_tf in Hin1. destruct Hin1 as [H1 H2].
  destruct f as [un]. apply if_then_else_tf in Hin2.
  destruct Hin2 as [H3 H4].
  
  simpl. *)

(* Not true. Not sure what conditions are needed to make it true. *)
(* Lemma ren_FOv_list__l_switch : forall l1 l2 l x y,
  consistent_lx_lx (cons x l1) (cons y l2) ->
  rename_FOv_list (rename_FOv_list_l l l1 l2) x y =
  rename_FOv_list_l (rename_FOv_list l x y) l1 l2.
Proof. *)
  
(* Let l :=   (cons (Var 1) (cons (Var 5) (cons (Var 2) (cons (Var 8) nil)))).
Let l2 := cons (Var 5) (cons (Var 8) nil).
Let l1 := cons (Var 8) (cons (Var 2) nil).
Eval compute in (rename_FOv_list_l l l1 l2 =
rename_FOv_list_l l
  (order2 (diff_r l (rename_FOv_list_l l l1 l2))
     (diff_l l (rename_FOv_list_l l l1 l2)))
  (order1 (diff_r l (rename_FOv_list_l l l1 l2)))).
 *)

Lemma ind_gen_ind_l2_FOv_diff_l_r : forall (l1 l2 : list FOvariable) n (x y x0 : FOvariable),
  @ind_gen _ x0 (indicies_l2_FOv l1 x) l2 = constant_l y n ->
exists (m : nat),
  @ind_gen _ x0 (indicies_l2_FOv (diff_l l1 l2) x) (diff_r l1 l2) = constant_l y m.
Proof.
  induction l1; intros l2 n [xn] [ym] x0 H.
    simpl in *. exists 0. reflexivity.

    simpl. destruct a as [un].
    destruct l2. simpl. exists 0. reflexivity.

    destruct f as [zn]. unfold indicies_l2_FOv in *. simpl in *.
    case_eq (beq_nat un zn); intros Hbeq;
      case_eq (beq_nat xn un); intros Hbeq2; rewrite Hbeq2 in *;
        simpl in *; rewrite ind_gen_FOv_pre_cons in H.
        destruct n. discriminate. simpl in H. inversion H as [[H1 H2]].
        apply IHl1 with (n := n). assumption.

        apply IHl1 with (n := n). assumption.

        rewrite Hbeq2. simpl. rewrite ind_gen_FOv_pre_cons.
        destruct n. discriminate. simpl in H.
        inversion H as [[H1 H2]].
        destruct (IHl1 l2 n (Var xn) (Var ym) x0 H2) as [m H3].
        rewrite H3. exists (S m). reflexivity.

        rewrite Hbeq2. rewrite ind_gen_FOv_pre_cons.
        apply IHl1 with (n := n). assumption.
Qed.

Lemma consistent_lx_lx_diff_r_l : forall l1 l2,
  consistent_lx_lx l1 l2 ->
  consistent_lx_lx (diff_l l1 l2) (diff_r l1 l2).
Proof.
  unfold consistent_lx_lx.
  unfold consistent_lx_lx_x.
  unfold is_constant.
  intros l1 l2 H x.
  specialize (H x). destruct H as [y [n H2]].
  exists y.
  apply ind_gen_ind_l2_FOv_diff_l_r with (n := n).
  assumption.
Qed.

(* Left it here 5/02/18.
Not sure what I was trying to do with the above lemma.
Figure out whether this computation method will actually work.
Try pen and paper for this. *)
Lemma rep_FOv_l_order_pre : forall l1 l2 l,
rename_FOv_list_l l l1 l2 =
rename_FOv_list_l l
  (order2 (diff_r l (rename_FOv_list_l l l1 l2))
     (diff_l l (rename_FOv_list_l l l1 l2)))
  (order1 (diff_r l (rename_FOv_list_l l l1 l2))).
Proof.
Admitted.
(* commented 28/03
  induction l1; intros l2 l.
    rewrite diff_r_refl. reflexivity. 

    simpl. destruct l2.
    rewrite diff_r_refl. reflexivity. 

    case_eq (is_in_FOvar a l1); intros Hin1;
      case_eq (is_in_FOvar a l2); intros Hin2.
admit.

        rewrite ren_FOv_list_not_in. apply IHl1.
        apply is_in_FOvar_ren_FOv_list_l; try assumption.

        destruct l1. simpl in *.
          apply rep_FOv_l_order_pre_pre. 
        rewrite ren_FOv_list__l_is_in. apply IHl1.
          discriminate. destruct l2; discriminate.
          all : try assumption.





Search rename_FOv_list rename_FOv_list_l.


        


        
Lemma 
  is_in_Fovar 
Search is_in_FOvar rename_FOv_list_l.
Search rename_FOv_list  is_in_FOvar.
      
Lemma
  rename_FOv_list (rename_FOv_list_l l l1 l2) x y =
  rename
Admitted.
*)

Lemma rep_FOv_l_order : forall l1 l2 alpha,
  length l1 = length l2 ->
  replace_FOv_l alpha l1 l2 = replace_FOv_l alpha 
    (order2 (diff_r (FOvars_in alpha) (FOvars_in (replace_FOv_l alpha l1 l2))) 
            (diff_l (FOvars_in alpha) (FOvars_in (replace_FOv_l alpha l1 l2))))
    (order1 (diff_r (FOvars_in alpha) (FOvars_in (replace_FOv_l alpha l1 l2)))).
Proof.
  intros l1 l2 alpha Hl.
  rewrite FOvars_in_rep_FOv_l.
  apply same_struc_FOvars_in_eq.
    pose proof (same_struc_rep_FOv_l l1 l2 alpha) as H2.
    apply same_struc_comm in H2.
    apply (same_struc_trans _ _ _ H2 (same_struc_rep_FOv_l _ _ _)).

    do 2 rewrite FOvars_in_rep_FOv_l.
    apply rep_FOv_l_order_pre.
Qed.


    
(* 
  
  induction l1; intros l2 alpha Hl.
    destruct l2. 2:discriminate.
    simpl. rewrite diff_r_refl.
    simpl. reflexivity.



Search FOvars_in_rep_FOv_l.

    simpl.

    rewrite order2_nil. reflexivity.  
  destruct l2. discriminate.
  simpl. unfold order2. unfold order1.
  simpl. rewrite IHl1.


 simpl. *)


Lemma replace_FOv_l_num_conn : forall m n l1 l2 alpha,
  n = length l1 ->
  Nat.leb n m = true->
  length l1 = length l2 ->
  exists l1' l2',
  replace_FOv_l alpha l1 l2 = replace_FOv_l alpha l1' l2' /\
  decr_strict_FOv l2' = true /\
  length l1' = length l2' /\
  Nat.leb (length l1') (length l1) = true.
Proof.
Admitted.
(* commented 28/03
  induction m; intros n l1 l2 alpha Hn Hleb Hl.
    destruct n. 2 : discriminate.
    destruct l1. destruct l2.
    exists nil. exists nil. apply conj. reflexivity.
    apply conj. reflexivity.
    apply conj; reflexivity.
    all : try discriminate.

    destruct n.
    destruct l1. destruct l2.
    exists nil. exists nil. apply conj. reflexivity.
    apply conj. reflexivity.
    apply conj; reflexivity.
    all : try discriminate.

    destruct l1. discriminate.
    simpl in *. destruct l2.
    exists nil. exists nil. apply conj. reflexivity.
    apply conj. reflexivity.
    apply conj; reflexivity.

    simpl in Hl. inversion Hl as [Hl'].
    simpl in Hn. inversion Hn as [Hn']. 
    destruct (IHm n l1 l2 alpha Hn'  Hleb Hl') as [l1' [l2' [IH1 [IH2 [IH3 IH4]]]]].
    rewrite IH1.
    case_eq (is_in_FOvar f l1'); intros Hin.
      case_eq (is_in_FOvar f l2'); intros Hin2.

admit.
        rewrite (rep_FOv_not_occ _ f f0).
        exists l1'. exists l2'. apply conj. reflexivity.
        apply conj. assumption. apply conj. assumption.
      apply leb_suc_r. assumption.

        apply x_occ_in_alpha_rep_FOv_l; assumption.


        rewrite rep_FOv__l2.
        destruct (IHm (length l1') l1' (rename_FOv_list l2' f f0) alpha eq_refl)
          as [l1'' [l2'' [IH1' [IH2' [IH3' IH4']]]]].
          rewrite Hn' in Hleb.
          apply (leb_trans _ _ _ IH4 Hleb).

          rewrite length_rename_FOv_list. assumption.

        exists l1''. exists l2''. apply conj. assumption.
        apply conj. assumption. apply conj. assumption.
        apply leb_suc_r. apply (leb_trans _ _ _ IH4' IH4).
        all : try assumption.

      
rep_FOv__l_not_in
*)

Lemma replace_FOv_l_lem : forall l1 l2 alpha,
  length l1 = length l2 ->
  exists l1' l2',
  replace_FOv_l alpha l1 l2 = replace_FOv_l alpha l1' l2' /\
  decr_strict_FOv l2' = true /\
  length l1' = length l2'.
Proof.
Admitted.
(*
  induction l1; intros l2 alpha Hl. destruct l2.
    exists nil. exists nil. apply conj. reflexivity.
    apply conj; reflexivity.
    discriminate.

    simpl in *. destruct l2.
    exists nil. exists nil. apply conj. reflexivity.
    apply conj; reflexivity.

    simpl in Hl. inversion Hl as [Hl'].
    destruct (IHl1 l2 alpha Hl') as [l1' [l2' [IH1 [IH2 IH3]]]].
    rewrite IH1.
    case_eq (is_in_FOvar a l1'); intros Hin.
      case_eq (is_in_FOvar a l2'); intros Hin2.
        rewrite rep_FOv__l2.
        destruct (IHl1 (rename


        exists l1'. exists (rename_FOv_list l2' a f).
        apply conj. reflexivity.
        apply conj.
 l1'0 l2'0 
  
      rewrite rep_FOv__l_not_in.
      
    discriminate.
*)

Lemma rename_FOv_A_replace_FOv_l_num_conn : forall n lv alpha beta,
  length lv = n ->
  is_in_FOvar_l lv (FOvars_in alpha) = true ->
  rename_FOv_A_pre alpha beta lv n = replace_FOv_l alpha lv (seq_FOv 
    (Var (S (max_FOv (conjSO beta (list_closed_exFO alpha lv)))))  (length lv)).
Proof.
  induction n; intros lv alpha beta Hl Hin. destruct lv. unfold rename_FOv_A.
     reflexivity. discriminate.
  destruct lv. discriminate.
  simpl.
  simpl. unfold rename_FOv_max_conj.
  rewrite strip_exFO_rename_FOv. rewrite strip_exFO_list_rename_FOv.
    simpl. destruct f as [zn]. simpl in Hin.
    apply if_then_else_ft in Hin. destruct Hin as [Hin1 Hin2].
    rewrite max_FOv_list_closed_exFO_max.
 case_eq (is_in_FOvar (Var zn) lv); intros Hin3.
  rewrite rep_FOv__l_not_in.
Admitted.
(*   rwerite 
    rewrite IHn.


Search replace_FOv_l replace_FOv.
rep_FOv__l_not_in
rep_FOv__l_switch
      
    unfold rename_FOv_A in IHlv.
 *)

Lemma rename_FOv_A_replace_FOv_l : forall lv alpha beta,
  rename_FOv_A alpha beta lv = replace_FOv_l alpha lv (rev_seq_FOv2 
    (Var (S (max_FOv (conjSO beta (list_closed_exFO alpha lv)))))  (length lv)).
Proof.
Admitted.
(*
  induction lv; intros alpha beta. unfold rename_FOv_A. reflexivity.
  simpl. rewrite <- rev_seq_FOv__2. simpl.
  rewrite rev_seq_FOv__2. unfold rename_FOv_A.
  simpl. unfold rename_FOv_max_conj.
  rewrite strip_exFO_rename_FOv. rewrite strip_exFO_list_rename_FOv.
    simpl. destruct a as [zn].
    unfold rename_FOv_A in IHlv.
    rewrite IHlv. rewrite IHlv. rewrite IHlv.

 case_eq (rev_seq_FOv2 
    (Var (S (max (max_FOv alpha) (max_FOv beta)))) (S (length lv))).
    intros Hnil.
admit.  
  intros xx lxx Hlxx.

 rewrite <- Hlxx.
 unfold rev_seq_FOv2. simpl. unfold rename_FOv_A.
  simpl. unfold rename_FOv_max_conj. rewrite strip_exFO_rename_FOv.
  rewrite strip_exFO_list_rename_FOv.
*)

Lemma rename_FOv_A_rep_FOv_l3_num_conn : forall n lv alpha beta,
  length lv = n ->
  is_in_FOvar (Var 0) lv = false ->
  ~ lv = nil ->
  is_in_FOvar_l lv (FOvars_in alpha) = true ->
  exists l1 l2,
  rename_FOv_A alpha beta lv = replace_FOv_l alpha l1 l2 /\
  length l1 = length l2 /\
  Nat.leb  (S(max_FOv (conjSO alpha beta))) (min_FOv_l l2) = true /\
  is_all_diff_FOv l2 = true /\
Nat.leb (S (max_FOv_l l1)) (min_FOv_l l2) = true /\
decr_strict_FOv l2 = true.
Proof.
  induction n; intros lv alpha beta Hl Hin Hnil Hin2.
    destruct lv. 2 : discriminate.
    contradiction (Hnil eq_refl).

    destruct lv. discriminate.
    destruct lv. unfold rename_FOv_A.
    simpl. rewrite strip_exFO_0.
    unfold rename_FOv_max_conj.
    exists (cons f nil). exists (cons (Var (S (max_FOv (conjSO beta (exFO f alpha))))) nil).
    apply conj.
      simpl. rewrite rep__ren_FOv. reflexivity.

      apply conj. reflexivity.

      apply conj. simpl. destruct f as [zn].
admit.

      apply conj. reflexivity.

      apply conj. simpl. destruct f as [zn].
      rewrite PeanoNat.Nat.max_0_r.
admit.

      reflexivity.

    remember (cons f0 lv) as lv'.
    destruct (IHn lv' alpha beta) as [l1 [l2 [H1 [H2 [H3 [H4 [H5 H6]]]]]]].
      simpl in Hl. inversion Hl. reflexivity.

      simpl in Hin. destruct f as [zn]. destruct zn. discriminate.
      assumption.
      rewrite Heqlv'. discriminate. simpl in Hin2.
      case_eq (is_in_FOvar_l lv' (FOvars_in alpha)); intros Hin3;
        rewrite Hin3 in *. reflexivity. rewrite if_then_else_false in Hin2.
        discriminate.

    exists (cons f l1). exists (cons (Var 1) l2).
      apply conj. simpl. unfold rename_FOv_A. simpl.
      unfold rename_FOv_max_conj. rewrite strip_exFO_rename_FOv.
      rewrite strip_exFO_list_rename_FOv.




 unfold rename_FOv_A_pre.
  
 unfold rename_FOv_A.

    unfold rename_FOv_A_pre. simpl.

      simpl in Hl. inversion Hl as [Hl'].
      simpl in Hin. destruct f as [zn].
        destruct zn. discriminate.

(*       destruct (IHn lv' alpha beta) as [l1 [l2 [H1 [H2 [H3 [H4 [H5 H6]]]]]]]. *)

      
Admitted.


Lemma rename_FOv_A_rep_FOv_l3 : forall lv alpha beta,
  is_in_FOvar (Var 0) lv = false ->
  ~ lv = nil ->
  exists l1 l2,
  rename_FOv_A alpha beta lv = replace_FOv_l alpha l1 l2 /\
  length l1 = length l2 /\
  Nat.leb  (S(max_FOv (conjSO alpha beta))) (min_FOv_l l2) = true /\
  is_all_diff_FOv l2 = true /\
Nat.leb (S (max_FOv_l l1)) (min_FOv_l l2) = true /\
decr_strict_FOv l2 = true.
Proof.
  intros lv alpha beta H.
Admitted.
(*   apply (rename_FOv_A_rep_FOv_l3_num_conn (length lv) _ _ _ eq_refl).
Qed. *)

Lemma  rename_FOv_llist_app : forall l1 l2 x y,
  rename_FOv_llist (app l1 l2) x y = app (rename_FOv_llist l1 x y) (rename_FOv_llist l2 x y).
Proof.
  induction l1; intros l2 [xn] [ym]. reflexivity.
  simpl. rewrite IHl1. reflexivity.
Qed.



Lemma rep_FOv_implSO : forall alpha1 alpha2 x y,
  replace_FOv (implSO alpha1 alpha2) x y =
  implSO (replace_FOv alpha1 x y) (replace_FOv alpha2 x y).
Proof.
  intros alpha1 alpha2 [xn] [ym]; reflexivity.
Qed.

Lemma of_form_predSO_match : forall {A : Type} alpha (a b : A),
  of_form_predSO alpha = false ->
 ( match alpha with
  | predSO _ _ => a
  | _ => b
  end) = b.
Proof.
  destruct alpha; intros a b H; try reflexivity.
  discriminate.
Qed.

Lemma of_form_predSO_rep_FOv : forall alpha x y,
  of_form_predSO (replace_FOv alpha x y) = of_form_predSO alpha.
Proof.
  induction alpha; intros [xn] [ym]; try reflexivity.
    destruct p. destruct f as [zn]. simpl.
    case_eq (beq_nat xn zn); reflexivity.

    destruct f as [z1]; destruct f0 as [z2]. simpl.
    case_eq (beq_nat xn z1); case_eq (beq_nat xn z2); reflexivity.

    destruct f as [z1]; destruct f0 as [z2]. simpl.
    case_eq (beq_nat xn z1); case_eq (beq_nat xn z2); reflexivity.

    destruct f as [zn]. simpl. case_eq (beq_nat xn zn); reflexivity.

    destruct f as [zn]. simpl. case_eq (beq_nat xn zn); reflexivity.

    destruct p. simpl. reflexivity.

    destruct p. simpl. reflexivity.
Qed.

Lemma comp_cond_lx2_rep_FOv_gen_num_conn : forall m n alpha x y,
  n = num_conn alpha ->
  Nat.leb n m = true ->
  comp_cond_lx2 (replace_FOv alpha x y) = rename_FOv_list (comp_cond_lx2 alpha) x y.
Proof.
  induction m; intros n alpha [xn] [ym] Hnum Hleb.
    destruct n. 2 : discriminate.
    destruct alpha; try discriminate.
      destruct p. destruct f as [zn]. simpl.
      case_eq (beq_nat xn zn); reflexivity.

      destruct f as [z1]; destruct f0 as [z2].
      simpl. case_eq (beq_nat xn z1); case_eq (beq_nat xn z2);
        reflexivity.

      destruct f as [z1]; destruct f0 as [z2].
      simpl. case_eq (beq_nat xn z1); case_eq (beq_nat xn z2);
        reflexivity.

    destruct n. 
    destruct alpha; try discriminate.
      destruct p. destruct f as [zn]. simpl.
      case_eq (beq_nat xn zn); reflexivity.

      destruct f as [z1]; destruct f0 as [z2].
      simpl. case_eq (beq_nat xn z1); case_eq (beq_nat xn z2);
        reflexivity.

      destruct f as [z1]; destruct f0 as [z2].
      simpl. case_eq (beq_nat xn z1); case_eq (beq_nat xn z2);
        reflexivity.

      destruct alpha; try discriminate; try reflexivity.

(* -- *)
    destruct f as [zn]. simpl.
          simpl in Hnum. inversion Hnum as [Hnum'].
          rewrite Hnum' in *. simpl in Hleb.
  case_eq (beq_nat xn zn);
      intros Hbeq.
      destruct alpha; try discriminate; try reflexivity.
        simpl. destruct p. destruct f as [un].
        case_eq (beq_nat xn un); reflexivity.

        simpl. destruct f as [v1]; destruct f0 as [v2].
        case_eq (beq_nat xn v1); case_eq (beq_nat xn v2);
          reflexivity.

        simpl. destruct f as [v1]; destruct f0 as [v2].
        case_eq (beq_nat xn v1); case_eq (beq_nat xn v2);
          reflexivity.

        simpl. destruct f as [v1].
        case_eq (beq_nat xn v1); reflexivity.

        simpl. destruct f as [v1].
        case_eq (beq_nat xn v1); reflexivity.

        case_eq (of_form_predSO alpha2); intros Hof.
          destruct alpha2; try discriminate. simpl.
          destruct p. destruct f as [vn]. case_eq (beq_nat xn vn);
          reflexivity.

          rewrite of_form_predSO_match.
          simpl. rewrite Hbeq. rewrite of_form_predSO_match.
          rewrite (IHm (num_conn alpha2) alpha2); try reflexivity.
            destruct m. discriminate.
            apply leb_plus_take2 in Hleb. 
            apply leb_suc_r. assumption.

          rewrite of_form_predSO_rep_FOv.
          all : try assumption.

        destruct p. reflexivity.
        destruct p. reflexivity.

      destruct alpha; try discriminate; try reflexivity.
        simpl. destruct p. destruct f as [un].
        case_eq (beq_nat xn un); reflexivity.

        simpl. destruct f as [v1]; destruct f0 as [v2].
        case_eq (beq_nat xn v1); case_eq (beq_nat xn v2);
          reflexivity.

        simpl. destruct f as [v1]; destruct f0 as [v2].
        case_eq (beq_nat xn v1); case_eq (beq_nat xn v2);
          reflexivity.

        simpl. destruct f as [v1].
        case_eq (beq_nat xn v1); reflexivity.

        simpl. destruct f as [v1].
        case_eq (beq_nat xn v1); reflexivity.

        case_eq (of_form_predSO alpha2); intros Hof.
          destruct alpha2; try discriminate. simpl.
          destruct p. destruct f as [vn]. case_eq (beq_nat xn vn);
          reflexivity.

          rewrite of_form_predSO_match.
          simpl. rewrite Hbeq. rewrite of_form_predSO_match.
          rewrite (IHm (num_conn alpha2) alpha2); try reflexivity.
            destruct m. discriminate.
            apply leb_plus_take2 in Hleb. 
            apply leb_suc_r. assumption.
          rewrite of_form_predSO_rep_FOv.
          all : try assumption.

        destruct p. reflexivity.
        destruct p. reflexivity.
(* -- *)

        destruct f as [zn]. simpl. case_eq (beq_nat xn zn);
          reflexivity.

        destruct p. reflexivity.
        destruct p. reflexivity.
Qed.


Lemma comp_cond_lx2_rep_FOv_gen : forall alpha x y,
  comp_cond_lx2 (replace_FOv alpha x y) = rename_FOv_list (comp_cond_lx2 alpha) x y.
Proof.
  intros alpha x y.
  apply (comp_cond_lx2_rep_FOv_gen_num_conn (num_conn alpha) (num_conn alpha)).
  reflexivity. apply leb_refl.
Qed.

Lemma calc_llv_P_rep_FOv_num_conn : forall m n alpha x y P,
  n = num_conn alpha ->
  Nat.leb n m = true ->
  calc_llv_P (replace_FOv alpha x y) P = 
  rename_FOv_llist (calc_llv_P alpha P) x y. 
Proof.
  induction m; intros n alpha [xn] [ym] [Pn] Hnum Hleb.
    destruct n. 2 : discriminate.
    destruct alpha; try discriminate.
      destruct p; destruct f as [un]. simpl. 
      case_eq (beq_nat xn un); intros Hbeq; reflexivity.

      destruct f as [z1]; destruct f0 as [z2].
      simpl. case_eq (beq_nat xn z1); intros Hbeq;
        case_eq (beq_nat xn z2); intros Hbeq2;
          reflexivity.

      destruct f as [z1]; destruct f0 as [z2].
      simpl. case_eq (beq_nat xn z1); intros Hbeq;
        case_eq (beq_nat xn z2); intros Hbeq2;
          reflexivity.

    destruct n.
      destruct alpha; try discriminate.
        destruct p; destruct f as [un]. simpl. 
        case_eq (beq_nat xn un); intros Hbeq; reflexivity.

        destruct f as [z1]; destruct f0 as [z2].
        simpl. case_eq (beq_nat xn z1); intros Hbeq;
          case_eq (beq_nat xn z2); intros Hbeq2;
            reflexivity.

        destruct f as [z1]; destruct f0 as [z2].
        simpl. case_eq (beq_nat xn z1); intros Hbeq;
          case_eq (beq_nat xn z2); intros Hbeq2;
            reflexivity.


      destruct alpha; try discriminate; try reflexivity;
        try (destruct p; reflexivity).

      destruct f as [zn]. simpl. case_eq (beq_nat xn zn);
        intros Hbeq. destruct alpha; try discriminate; try reflexivity.
          simpl. destruct p. destruct f as [un].
          case_eq (beq_nat xn un); reflexivity.

          destruct f as [u1]; destruct f0 as [u2].
          simpl.  case_eq (beq_nat xn u1);
            case_eq (beq_nat xn u2); reflexivity.

          destruct f as [u1]; destruct f0 as [u2].
          simpl.  case_eq (beq_nat xn u1);
            case_eq (beq_nat xn u2); reflexivity.

          destruct f as [u1].
          simpl.  case_eq (beq_nat xn u1);
            reflexivity.

          destruct f as [u1].
          simpl.  case_eq (beq_nat xn u1);
            reflexivity.
(* -- *)
        case_eq (P_branch_allFO alpha2 (Pred Pn)); intros Hb.
          case_eq (of_form_predSO alpha2); intros Hf.
            destruct alpha2; try discriminate.
            rewrite rep_FOv_implSO. destruct f as [vn].
            destruct p as [Qm]. simpl in *.
            case_eq (beq_nat xn vn); intros Hbeq2;
              simpl; rewrite Hb; reflexivity.

          rewrite of_form_predSO_match. simpl.
          rewrite of_form_predSO_match. rewrite P_branch_allFO_rep_FOv.
          rewrite Hb. simpl. rewrite Hbeq.
          rewrite comp_cond_lx2_rep_FOv_gen. reflexivity.
          rewrite of_form_predSO_rep_FOv. assumption. assumption.

          simpl. rewrite P_branch_allFO_rep_FOv. rewrite Hb. reflexivity.
(* -- *)

          destruct p. reflexivity.
          destruct p. reflexivity.

        destruct alpha; try discriminate; try reflexivity.
          simpl. destruct p. destruct f as [un].
          case_eq (beq_nat xn un); reflexivity.

          destruct f as [u1]; destruct f0 as [u2].
          simpl.  case_eq (beq_nat xn u1);
            case_eq (beq_nat xn u2); reflexivity.

          destruct f as [u1]; destruct f0 as [u2].
          simpl.  case_eq (beq_nat xn u1);
            case_eq (beq_nat xn u2); reflexivity.

          destruct f as [u1].
          simpl.  case_eq (beq_nat xn u1);
            reflexivity.

          destruct f as [u1].
          simpl.  case_eq (beq_nat xn u1);
            reflexivity.
(* -- *)
        case_eq (P_branch_allFO alpha2 (Pred Pn)); intros Hb.
          case_eq (of_form_predSO alpha2); intros Hf.
            destruct alpha2; try discriminate.
            rewrite rep_FOv_implSO. destruct f as [vn].
            destruct p as [Qm]. simpl in *.
            case_eq (beq_nat xn vn); intros Hbeq2;
              simpl; rewrite Hb; reflexivity.

          rewrite of_form_predSO_match. simpl.
          rewrite of_form_predSO_match. rewrite P_branch_allFO_rep_FOv.
          rewrite Hb. simpl. rewrite Hbeq.
          rewrite comp_cond_lx2_rep_FOv_gen. reflexivity.
          rewrite of_form_predSO_rep_FOv. assumption. assumption.

          simpl. rewrite P_branch_allFO_rep_FOv. rewrite Hb. reflexivity.
(* -- *)

          destruct p. reflexivity.
          destruct p. reflexivity.


    destruct f as [zn]. simpl. case_eq (beq_nat xn zn); reflexivity.

    simpl in Hnum. inversion Hnum as [Hnum'].
    rewrite Hnum' in *. simpl in Hleb.
    simpl. rewrite (IHm (num_conn alpha1) alpha1).
    rewrite (IHm (num_conn alpha2) alpha2).
    rewrite rename_FOv_llist_app. all : try reflexivity.
    apply leb_plus_take2 in Hleb. assumption.
    apply leb_plus_take1 in Hleb. assumption.
Qed.

Lemma calc_llv_P_rep_FOv : forall alpha x y P,
  calc_llv_P (replace_FOv alpha x y) P = 
  rename_FOv_llist (calc_llv_P alpha P) x y. 
Proof.
  intros alpha x y P.
  apply (calc_llv_P_rep_FOv_num_conn (num_conn alpha) (num_conn alpha)).
  reflexivity. apply leb_refl.
Qed.

(* Lemma ren_FOv_llist_l_nil : forall llv l,
  rename_FOv_llist_l llv nil l = llv.
Proof.
  induction llv; intros l. reflexivity.
  simpl. rewrite IHllv. reflexivity.
Qed.

Lemma ren_FOv_llist_l_nil2 : forall llv l,
  rename_FOv_llist_l llv l nil = llv.
Proof.
  induction llv; intros l. reflexivity.
  simpl. rewrite IHllv. destruct l; reflexivity.
Qed. 
 *)
Lemma calc_llv_P_rep_FOv_l : forall l1 l2 alpha P,
  calc_llv_P (replace_FOv_l alpha l1 l2) P = 
  rename_FOv_llist_l (calc_llv_P alpha P) l1 l2.
Proof.
  induction l1; intros l2 alpha P. reflexivity.
  simpl. destruct l2. reflexivity.
  rewrite calc_llv_P_rep_FOv.
  rewrite IHl1. reflexivity.
Qed.

Lemma is_in_FOvar_l_list_quant_FOv_overP : forall alpha,
  is_in_FOvar_l (list_quant_FOv_overP alpha) (FOvars_in alpha) = true.
Proof.
  induction alpha; try reflexivity; try (simpl; assumption).
    destruct f as [zn]. simpl. 
    case_eq (is_unary_predless alpha); intros Hun; simpl;
      [| rewrite <- beq_nat_refl];
      apply is_in_FOvar_l_cons_r2; assumption.

    destruct f as [zn]. simpl. 
    case_eq (is_unary_predless alpha); intros Hun; simpl;
      [| rewrite <- beq_nat_refl];
      apply is_in_FOvar_l_cons_r2; assumption.

    simpl. rewrite is_in_FOvar_l_app. reflexivity.
    all : try assumption.

    simpl. rewrite is_in_FOvar_l_app. reflexivity.
    all : try assumption.

    simpl. rewrite is_in_FOvar_l_app. reflexivity.
    all : try assumption.
Qed.

Lemma BOXATM_flag_weak_allFO_gen : forall alpha beta x z,
  BOXATM_flag_weak (allFO x (implSO beta alpha)) z = true ->
  BOXATM_flag_weak alpha x = true.
Proof.
  intros alpha beta [xn] [zn] H.
  simpl in H. destruct beta; try discriminate.
  destruct f as [y1]. destruct f0 as [y2].
  apply if_then_else_ft in H. destruct H as [H1 H2].
  apply if_then_else_ft in H2. apply H2.
Qed.

Lemma is_all_diff_FOv2_calc_llv_P_rename_FOv_A_pre2_pre_pre_num_conn_pre_num_conn : forall m n alpha xn ym z rel atm,
  n = num_conn atm ->
  Nat.leb n m = true ->
  REL rel = true ->
  BOXATM_flag_weak atm z = true ->
  Nat.leb (S (max_FOv (conjSO (conjSO rel atm) alpha))) ym = true ->
  Nat.leb (S xn) ym = true ->
  is_all_diff_FOv (comp_cond_lx2 atm) = true ->
  is_all_diff_FOv (rename_FOv_list (comp_cond_lx2 atm) (Var xn) (Var ym)) = true.
Proof.
  induction m; intros n alpha xn ym z rel atm Hnum Hleb Hrel Hat Hleb1 Hleb2 Hall.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate. reflexivity.

    destruct n.
    destruct atm; try discriminate. reflexivity.

    destruct atm; try discriminate.
    destruct atm; try discriminate.
    case_eq (of_form_predSO atm2); intros Hof;
      simpl. destruct atm2; try discriminate. reflexivity.
    rewrite of_form_predSO_match.
    simpl in Hall. rewrite of_form_predSO_match in Hall.
    simpl. destruct f as [un]. simpl in Hall.
    case_eq (is_in_FOvar (Var un) (comp_cond_lx2 atm2)); intros Hin;
      rewrite Hin in *. discriminate.
        destruct ym. discriminate. simpl in Hleb1.
    apply leb_max in Hleb1.
    destruct Hleb1 as [Hleb1 Hleb4].
    apply leb_max in Hleb1. destruct Hleb1 as [Hleb1 Hleb5].
    apply leb_max in Hleb5. destruct Hleb5 as [Hleb5 Hleb6].
    apply leb_max in Hleb6. destruct Hleb6 as [Hleb6 Hleb7].

    case_eq (beq_nat xn un); intros Hbeq.
      simpl. rewrite (beq_nat_true _ _ Hbeq) in *.
      rewrite ren_FOv_list_not_in. 2 : assumption.
      rewrite is_in_FOvar_comp_cond_lx2_2 with (y := Var un).
      all : try assumption. apply BOXATM_flag_weak_allFO_gen in Hat. 
      assumption.

      apply (is_in_FOvar__l_tff _ _ _ (is_in_FOvar_l_list_quant_FOv_overP _)).
      rewrite (max_FOv__l atm2) in Hleb7.
      apply sS_lem_f7_gen_pre. assumption.

          simpl. rewrite is_in_FOvar_ren_FOv_list.
          apply (IHm (num_conn atm2) alpha _ _ (Var un) rel); try reflexivity;
            try assumption.
            
            simpl in Hnum. inversion Hnum as [Hnum'].
            rewrite Hnum' in *. simpl in Hleb.
            destruct m. discriminate. apply leb_plus_take2 in Hleb.
            apply leb_suc_r. assumption.

apply BOXATM_flag_weak_allFO_gen in Hat. assumption.
            simpl. rewrite <- (max_refl ym).
            apply leb_max_max_gen.
            simpl. rewrite <- (max_refl ym).
            apply leb_max_max_gen. all : try  assumption.
            apply beq_nat_false_FOv. rewrite beq_nat_comm.
            assumption.

            intros H. inversion H as [HH]. rewrite <- HH in *.
            rewrite leb_suc_f in Hleb5. discriminate.
Qed.

Lemma is_all_diff_FOv2_calc_llv_P_rename_FOv_A_pre2_pre_pre_num_conn_pre : forall alpha xn ym z rel atm,
  REL rel = true ->
  BOXATM_flag_weak atm z = true ->
  Nat.leb (S (max_FOv (conjSO (conjSO rel atm) alpha))) ym = true ->
  Nat.leb (S xn) ym = true ->
  is_all_diff_FOv (comp_cond_lx2 atm) = true ->
  is_all_diff_FOv (rename_FOv_list (comp_cond_lx2 atm) (Var xn) (Var ym)) = true.
Proof.
  intros until 0. apply (is_all_diff_FOv2_calc_llv_P_rename_FOv_A_pre2_pre_pre_num_conn_pre_num_conn
    (num_conn atm) (num_conn atm)).
    reflexivity. apply leb_refl.
Qed.

Lemma leb_max_FOv_rand1_l : forall rel atm1 atm2 alpha ym,
  Nat.leb (S (max_FOv (conjSO (conjSO rel (conjSO atm1 atm2)) alpha))) ym = true ->
  Nat.leb (S (max_FOv (conjSO (conjSO rel  atm1) alpha))) ym = true.
Proof.
  intros until 0. intros Hleb. simpl in *.
  destruct ym. discriminate.
  apply leb_max in Hleb. destruct Hleb as [Hleb1 Hleb2]. 
  apply leb_max in Hleb1. destruct Hleb1 as [Hleb1 Hleb3].
  apply leb_max in Hleb3. destruct Hleb3.
  rewrite <- (max_refl ym).
  apply leb_max_max_gen.
    rewrite <- (max_refl ym).
    apply leb_max_max_gen.
    all : assumption.
Qed.

Lemma leb_max_FOv_rand1_r : forall rel atm1 atm2 alpha ym,
  Nat.leb (S (max_FOv (conjSO (conjSO rel (conjSO atm1 atm2)) alpha))) ym = true ->
  Nat.leb (S (max_FOv (conjSO (conjSO rel  atm2) alpha))) ym = true.
Proof.
  intros until 0. intros Hleb. simpl in *.
  destruct ym. discriminate.
  apply leb_max in Hleb. destruct Hleb as [Hleb1 Hleb2]. 
  apply leb_max in Hleb1. destruct Hleb1 as [Hleb1 Hleb3].
  apply leb_max in Hleb3. destruct Hleb3.
  rewrite <- (max_refl ym).
  apply leb_max_max_gen.
    rewrite <- (max_refl ym).
    apply leb_max_max_gen.
    all : assumption.
Qed.

Lemma is_all_diff_FOv2_calc_llv_P_rename_FOv_A_pre2_pre_pre_num_conn : forall m n alpha xn ym rel atm,
  n = num_conn atm ->
  Nat.leb n m = true ->
  REL rel = true ->
  BAT atm = true ->
  Nat.leb (S (max_FOv (conjSO (conjSO rel atm) alpha))) ym = true ->
  Nat.leb (S xn) ym = true ->
  (forall P, is_all_diff_FOv2 (calc_llv_P atm P) = true) ->
  forall P, is_all_diff_FOv2 (rename_FOv_llist (calc_llv_P atm P) (Var xn) (Var ym)) = true.
Proof.
  induction m; intros n alpha xn ym rel atm Hnum Hleb Hrel Hat Hleb2 Hleb3 Hall P.
    destruct n. 2 :discriminate.
    destruct atm; try discriminate.
      destruct p. destruct f as [zn]. reflexivity.

    destruct n.
    destruct atm; try discriminate.
      destruct p. destruct f. reflexivity.

    destruct atm; try discriminate.
      specialize (Hall P).
      simpl. simpl in Hall. destruct atm; try discriminate.
      case_eq (P_branch_allFO atm2 P); intros Hp;
        rewrite Hp in *.
        case_eq (of_form_predSO atm2); intros Hof.
          destruct atm2; try discriminate. reflexivity.
        rewrite of_form_predSO_match in *.    
        pose proof (is_BOXATM_flag_strong__CONJ_BAT _ _ _ Hat) as Hat2.
        rewrite of_form_predSO_match in Hall.
        simpl in *. destruct f as [un].
        apply if_then_else_ft in Hall. destruct Hall as [Hall1 Hall2].
        clear Hall2.
        case_eq (is_in_FOvar (Var un) (comp_cond_lx2 atm2)); intros Hin;
          rewrite Hin in *. discriminate.
        destruct ym. discriminate.
apply leb_max in Hleb2.
          destruct Hleb2 as [Hleb2 Hleb4].
          apply leb_max in Hleb2. destruct Hleb2 as [Hleb2 Hleb5].
          apply leb_max in Hleb5. destruct Hleb5 as [Hleb5 Hleb6].
          apply leb_max in Hleb6. destruct Hleb6 as [Hleb6 Hleb7].
        case_eq (beq_nat xn un);
          intros Hbeq. simpl. rewrite (beq_nat_true _ _ Hbeq) in *.
          rewrite ren_FOv_list_not_in. 2 : assumption.
          rewrite is_in_FOvar_comp_cond_lx2_2 with (y := Var un).
          rewrite Hall1. reflexivity. assumption.
          apply (is_in_FOvar__l_tff _ _ _ (is_in_FOvar_l_list_quant_FOv_overP _)).
          rewrite (max_FOv__l atm2) in Hleb7.
          apply sS_lem_f7_gen_pre. assumption. 

          simpl. rewrite is_in_FOvar_ren_FOv_list.
          rewrite is_all_diff_FOv2_calc_llv_P_rename_FOv_A_pre2_pre_pre_num_conn_pre
              with (alpha := alpha) (rel := rel) (z := Var un); try assumption. reflexivity.

            simpl. rewrite <- (max_refl ym).
            apply leb_max_max_gen.
            simpl. rewrite <- (max_refl ym).
            apply leb_max_max_gen. all : try  assumption.
            apply beq_nat_false_FOv. rewrite beq_nat_comm.
            assumption.

            intros H. inversion H as [HH]. rewrite <- HH in *.
            rewrite leb_suc_f in Hleb5. discriminate.

(* -- *)

      simpl. rewrite rename_FOv_llist_app.
      rewrite is_all_diff_FOv2_app.
      simpl in Hnum. inversion Hnum as [Hnum'].
      rewrite Hnum' in *. simpl in Hleb.
      pose proof (BAT_conjSO_l _ _ Hat).
      pose proof (BAT_conjSO_r _ _ Hat).
      rewrite (IHm (num_conn atm1) alpha) with (rel := rel).
      apply (IHm (num_conn atm2) alpha) with (rel := rel).
        all : try reflexivity. all : try assumption.
          apply leb_plus_take2 in Hleb. assumption.

          apply leb_max_FOv_rand1_r in Hleb2. assumption.

        intros PP. specialize (Hall PP).
        simpl in Hall. rewrite is_all_diff_FOv2_app in Hall.
        apply if_then_else_ft in Hall. destruct Hall as [Halla Hallb].
        assumption.
          apply leb_plus_take1 in Hleb. assumption.

          apply leb_max_FOv_rand1_l in Hleb2. assumption.

        intros PP. specialize (Hall PP).
        simpl in Hall. rewrite is_all_diff_FOv2_app in Hall.
        apply if_then_else_ft in Hall. destruct Hall as [Halla Hallb].
        assumption.
Qed.

Lemma is_all_diff_FOv2_calc_llv_P_rename_FOv_A_pre2_pre_pre : forall alpha xn ym rel atm,
  REL rel = true ->
  BAT atm = true ->
  Nat.leb (S (max_FOv (conjSO (conjSO rel atm) alpha))) ym = true ->
  Nat.leb (S xn) ym = true ->
  (forall P, is_all_diff_FOv2 (calc_llv_P atm P) = true) ->
  forall P, is_all_diff_FOv2 (rename_FOv_llist (calc_llv_P atm P) (Var xn) (Var ym)) = true.
Proof.
  intros until 0. apply (is_all_diff_FOv2_calc_llv_P_rename_FOv_A_pre2_pre_pre_num_conn
    (num_conn atm) (num_conn atm)).
    reflexivity. apply leb_refl.
Qed.


Lemma BAT_rep_FOv_num_conn_pre : forall m n atm x y z,
  n = num_conn atm ->
  Nat.leb n m = true ->
  ~ x = z ->
  BOXATM_flag_weak atm z = true ->
  BOXATM_flag_weak (replace_FOv atm x y) z = true.
Proof.
  induction m; intros n atm [xn] [ym] [zn] Hnum Hleb Hnot Hat.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
    destruct f as [un]. destruct p. simpl in *.
    rewrite <- (beq_nat_true _ _ Hat).
    rewrite (FOvar_neq _ _ Hnot). simpl. rewrite <- beq_nat_refl.
    reflexivity.

    destruct n.
    destruct atm; try discriminate.
    destruct f as [un]. destruct p. simpl in *.
    rewrite <- (beq_nat_true _ _ Hat).
    rewrite (FOvar_neq _ _ Hnot). simpl. rewrite <- beq_nat_refl.
    reflexivity.

    destruct atm; try discriminate.
    destruct f as [u1]. destruct atm; try discriminate.
    destruct atm1; try discriminate.
    destruct f as [u2]. destruct f0 as [u3].
    simpl in Hat. apply if_then_else_ft in Hat.
    destruct Hat as [Hat1 Hat2].
    apply if_then_else_ft in Hat2. destruct Hat2 as [Hat2 Hat3].
    simpl. case_eq (beq_nat xn u1); intros Hbeq.
      case_eq (beq_nat xn u2); intros Hbeq2.
        rewrite <- (beq_nat_true _ _ Hbeq2) in *.
        rewrite beq_nat_comm in Hat1. rewrite (FOvar_neq _ _ Hnot) in Hat1.
        discriminate.

        rewrite <- (beq_nat_true _ _ Hat2). rewrite Hbeq.
        simpl. rewrite Hat1. rewrite <- beq_nat_refl.
        case_eq (beq_nat xn ym); intros Hbeq3.
          rewrite (beq_nat_true _ _ Hbeq3).
          rewrite rep_FOv_refl. rewrite (beq_nat_true _ _ Hbeq) in Hbeq3.
          rewrite <- (beq_nat_true _ _ Hbeq3). assumption.
        apply (IHm (num_conn atm2)); try assumption. reflexivity.
admit.
Admitted.
(*
          apply beq_nat_false_FOv. assumption.
          
Search BOXATM_flag_weak replace_FOv.
        simpl.
        rewrite (beq_nat_true _ _ Hbeq). rewrite Hat2.
        simpl. rewrite <- beq_nat_refl.
         
      rewrite (beq_nat_true _ _ Hbeq). rewrite H
      case_eq (beq_nat xn u2); intros Hbeq2.
*)

Lemma BOXATM_flag_weak_rep_FOv_3 : forall m n atm x y y1 y2 y3,
(forall (n : nat) (atm : SecOrder) (x y : FOvariable),
      n = num_conn atm -> Nat.leb n m = true -> BAT atm = true -> BAT (replace_FOv atm x y) = true) ->
 S n = num_conn (allFO y1 (implSO (relatSO y2 y3) atm))->
 Nat.leb (S n) (S m) = true ->
BOXATM_flag_weak (allFO y1 (implSO (relatSO y2 y3) atm)) (batm_comp_x1 (allFO y1 (implSO (relatSO y2 y3) atm))) = true ->
BOXATM_flag_weak (replace_FOv (allFO y1 (implSO (relatSO y2 y3) atm)) x y) (batm_comp_x1 (replace_FOv (allFO y1 (implSO (relatSO y2 y3) atm)) x y)) = true.
Proof.
  intros m n atm [xn] [ym] [z1] [z2] [z3] IH Hnum Hleb Hb.
  simpl in *. rewrite <- beq_nat_refl in Hb.
  apply if_then_else_ft in Hb. destruct Hb as [Hb1 Hb2].
  rewrite <- (beq_nat_true _ _ Hb1).
  case_eq (beq_nat xn z1); intros Hbeq.
    case_eq (beq_nat xn z2); intros Hbeq2.
      simpl. rewrite <- beq_nat_refl.
      pose proof (is_BOXATM_flag_strong__CONJ2_BAT _ _ Hb2) as Hb3.
      assert (Nat.leb (num_conn atm) m = true) as Hass2.
        inversion Hnum as [Hnum']. rewrite Hnum' in *.
        apply leb_suc_l in Hleb. assumption.
      specialize (IH (num_conn atm) atm (Var xn) (Var ym) eq_refl Hass2 Hb3).
      
Search BOXATM_flag_weak BAT.
Admitted.

Lemma BAT__BOXATM_flat_weak_of_form_allFO_predSO : forall alpha,
  (of_form_allFO alpha = true \/ of_form_predSO alpha = true) ->
  BAT alpha = true -> BOXATM_flag_weak alpha (batm_comp_x1 alpha) = true.
Proof.
  induction alpha; intros H Hb; try discriminate.
    simpl. destruct f.  rewrite <- beq_nat_refl. reflexivity.

    rewrite BAT_BOXATM_flag_weak_allFO in Hb. assumption.

    simpl in H. destruct H; discriminate.
Qed.

Lemma batm_comp_x1_rep_FOv_num_conn : forall m n atm x y,
 n = num_conn atm -> 
  Nat.leb n m = true ->
  BOXATM_flag_weak atm x = true ->
  batm_comp_x1 (replace_FOv atm x y) = y.
Proof.
  induction m; intros n atm [xn] [ym] Hnum Hleb Hb.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
    simpl in *. destruct f as [zn]. destruct p.
    rewrite Hb. reflexivity.

    destruct n.
    destruct atm; try discriminate.
    simpl in *. destruct f as [zn]. destruct p.
    rewrite Hb. reflexivity.

    destruct atm; try discriminate.
    destruct atm; try discriminate.
    destruct atm1; try discriminate.
    pose proof (BOXATM_flag_weak_allFO_eq _ _ _ _ _ Hb) as Heq.
    rewrite <- Heq.
    destruct f as [z1]; destruct f0 as [z2]; destruct f1 as [z3].
    simpl in *. inversion Heq as [Heq'].
    rewrite Heq' in *. rewrite <- beq_nat_refl in Hb.
    case_eq (beq_nat xn z2); intros Hbeq; rewrite Hbeq in *;
      case_eq (beq_nat xn z3); intros Hbeq2; try reflexivity; try discriminate.
Qed.

Lemma batm_comp_x1_rep_FOv : forall atm x y,
  BOXATM_flag_weak atm x = true ->
  batm_comp_x1 (replace_FOv atm x y) = y.
Proof.
  intros atm x y. apply (batm_comp_x1_rep_FOv_num_conn (num_conn atm) (num_conn atm)
    _ _ _ eq_refl (leb_refl _)).
Qed.

Lemma batm_comp_x1_rep_FOv2_num_conn : forall m n atm x y z,
n = num_conn atm -> 
  Nat.leb n m = true ->
  ~ x = z ->
  BOXATM_flag_weak atm z = true ->
  batm_comp_x1 (replace_FOv atm x y) = z.
Proof.
  induction m; intros n atm x y z Hnum Hleb Hnot Hb.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
    simpl in *. destruct x as [xn].
    destruct p. destruct f as [zn].
    destruct z as [ym]. rewrite <- (beq_nat_true _ _ Hb).
    rewrite FOvar_neq. reflexivity. assumption.

    destruct n.
    destruct atm; try discriminate.
    simpl in *. destruct x as [xn].
    destruct p. destruct f as [zn].
    destruct z as [ym]. rewrite <- (beq_nat_true _ _ Hb).
    rewrite FOvar_neq. reflexivity. assumption.

    simpl in Hleb. destruct atm; try discriminate.
    destruct atm; try discriminate.
    destruct atm1; try discriminate.
    pose proof (BOXATM_flag_weak_allFO_eq _ _ _ _ _ Hb) as Heq.
    rewrite <- Heq.
    destruct f as [z1]; destruct f0 as [z2]; destruct f1 as [z3].
    simpl in *. inversion Heq as [Heq'].
    rewrite Heq' in *. rewrite <- beq_nat_refl in Hb.
    destruct x as [xn]. destruct z as [zn].
    apply if_then_else_ft in Hb. destruct Hb as [Hb1 Hb2].
    rewrite (beq_nat_true _ _ Hb1) in *. destruct y as [ym].
    rewrite (FOvar_neq _ _ Hnot).
    case_eq (beq_nat xn z3); intros Hbeq; try reflexivity; try discriminate.
Qed.

Lemma batm_comp_x1_rep_FOv2 : forall atm x y z,
  ~ x = z ->
  BOXATM_flag_weak atm z = true ->
  batm_comp_x1 (replace_FOv atm x y) = z.
Proof.
  intros atm x y z. apply (batm_comp_x1_rep_FOv2_num_conn (num_conn atm) (num_conn atm)).
  reflexivity. apply leb_refl.
Qed.

Lemma BOXATM_flag_weak_rep_FOv_3' : forall m n atm x y y1 y2 y3,
(forall (n : nat) (atm : SecOrder) (x y : FOvariable),
      n = num_conn atm -> Nat.leb n m = true -> BAT atm = true -> BAT (replace_FOv atm x y) = true) ->
 S n = num_conn (allFO y1 (implSO (relatSO y2 y3) atm))->
 Nat.leb (S n) (S m) = true ->
BAT (allFO y1 (implSO (relatSO y2 y3) atm)) = true ->
BAT (replace_FOv (allFO y1 (implSO (relatSO y2 y3) atm)) x y)  = true.
Proof.
  intros m n atm [xn] [ym] [z1] [z2] [z3] IH Hnum Hleb Hb.
  simpl in *. rewrite <- beq_nat_refl in Hb.
  apply if_then_else_ft in Hb. destruct Hb as [Hb1 Hb2].
  rewrite <- (beq_nat_true _ _ Hb1).
  case_eq (beq_nat xn z1); intros Hbeq;
    case_eq (beq_nat xn z2); intros Hbeq2.
      simpl. rewrite <- beq_nat_refl.
      pose proof (is_BOXATM_flag_strong__CONJ2_BAT _ _ Hb2) as Hb3.
      assert (Nat.leb (num_conn atm) m = true) as Hass2.
        inversion Hnum as [Hnum']. rewrite Hnum' in *.
        apply leb_suc_l in Hleb. assumption.
      specialize (IH (num_conn atm) atm (Var xn) (Var ym) eq_refl Hass2 Hb3).
      apply BAT__BOXATM_flat_weak_of_form_allFO_predSO in IH.
      rewrite batm_comp_x1_rep_FOv in IH. assumption.
      rewrite (beq_nat_true _ _  Hbeq) in *. assumption.
      destruct atm; try discriminate.
        right. destruct p. destruct f as [zn]. simpl.
          case_eq (beq_nat xn zn); intros Hbeq3;  reflexivity.

        destruct f as [zn]. left. simpl.
        case_eq (beq_nat xn zn); reflexivity.

      simpl. rewrite <- beq_nat_refl.
      pose proof (is_BOXATM_flag_strong__CONJ2_BAT _ _ Hb2) as Hb3.
      assert (Nat.leb (num_conn atm) m = true) as Hass2.
        inversion Hnum as [Hnum']. rewrite Hnum' in *.
        apply leb_suc_l in Hleb. assumption.
      rewrite <- beq_nat_refl.
      specialize (IH (num_conn atm) atm (Var xn) (Var ym) eq_refl Hass2 Hb3).
      apply BAT__BOXATM_flat_weak_of_form_allFO_predSO in IH.
      rewrite batm_comp_x1_rep_FOv in IH. assumption.
      rewrite (beq_nat_true _ _  Hbeq) in *. assumption.
      destruct atm; try discriminate.
        right. destruct p. destruct f as [zn]. simpl.
          case_eq (beq_nat xn zn); intros Hbeq3;  reflexivity.

        destruct f as [zn]. left. simpl.
        case_eq (beq_nat xn zn); reflexivity.

      simpl. rewrite <- beq_nat_refl.
      pose proof (is_BOXATM_flag_strong__CONJ2_BAT _ _ Hb2) as Hb3.
      assert (Nat.leb (num_conn atm) m = true) as Hass2.
        inversion Hnum as [Hnum']. rewrite Hnum' in *.
        apply leb_suc_l in Hleb. assumption.
      rewrite <- beq_nat_refl.
      specialize (IH (num_conn atm) atm (Var xn) (Var ym) eq_refl Hass2 Hb3).
      apply BAT__BOXATM_flat_weak_of_form_allFO_predSO in IH.
      rewrite batm_comp_x1_rep_FOv2 with (z := (Var z1)) in IH. assumption.
        apply beq_nat_false_FOv. assumption. assumption.
      destruct atm; try discriminate.
        right. destruct p. destruct f as [zn]. simpl.
          case_eq (beq_nat xn zn); intros Hbeq3;  reflexivity.

        destruct f as [zn]. left. simpl.
        case_eq (beq_nat xn zn); reflexivity.

      simpl. do 2 rewrite <- beq_nat_refl.
      pose proof (is_BOXATM_flag_strong__CONJ2_BAT _ _ Hb2) as Hb3.
      assert (Nat.leb (num_conn atm) m = true) as Hass2.
        inversion Hnum as [Hnum']. rewrite Hnum' in *.
        apply leb_suc_l in Hleb. assumption.
      specialize (IH (num_conn atm) atm (Var xn) (Var ym) eq_refl Hass2 Hb3).
      apply BAT__BOXATM_flat_weak_of_form_allFO_predSO in IH.
      rewrite batm_comp_x1_rep_FOv2 with (z := (Var z1)) in IH. assumption.
        apply beq_nat_false_FOv. assumption. assumption.
      destruct atm; try discriminate.
        right. destruct p. destruct f as [zn]. simpl.
          case_eq (beq_nat xn zn); intros Hbeq3;  reflexivity.

        destruct f as [zn]. left. simpl.
        case_eq (beq_nat xn zn); reflexivity.
Qed.


Lemma BAT_rep_FOv_num_conn : forall m n atm x y,
  n = num_conn atm ->
  Nat.leb n m = true ->
  BAT atm = true ->
  BAT (replace_FOv atm x y) = true.
Proof.
  induction m; intros n atm [xn] [ym] Hnum Hleb Hat.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
    destruct p. destruct f as [zn]. simpl.
    case_eq (beq_nat xn zn); reflexivity.

    destruct n.
    destruct atm; try discriminate.
    destruct p. destruct f as [zn]. simpl.
    case_eq (beq_nat xn zn); reflexivity.

    destruct atm; try discriminate.
    destruct atm; try discriminate.
    destruct atm1; try discriminate.
    destruct f as [u1]; destruct f0 as [u2];
    destruct f1 as [u3]. pose proof Hat as Hat'.
    simpl in Hat. rewrite <- beq_nat_refl in Hat.
    apply if_then_else_ft in Hat. destruct Hat as [Hat Hat2].
    apply BOXATM_flag_weak_rep_FOv_3' with (m := m) (n := n); assumption.

    simpl.
    pose proof (BAT_conjSO_l _ _ Hat).
    pose proof (BAT_conjSO_r _ _ Hat).
    simpl in Hnum. inversion Hnum as [Hnum'].
    rewrite Hnum' in *. simpl in Hleb.
    pose proof (leb_plus_take1 _ _ _ Hleb).
    pose proof (leb_plus_take2 _ _ _ Hleb).
    rewrite (IHm (num_conn atm1) atm1).
    apply (IHm (num_conn atm2) atm2). all : try reflexivity.
    all : try assumption.
Qed.

Lemma BAT_rep_FOv : forall atm x y,
  BAT atm = true ->
  BAT (replace_FOv atm x y) = true.
Proof.
  intros atm x y. apply (BAT_rep_FOv_num_conn (num_conn atm) (num_conn atm)).
  reflexivity. apply leb_refl.
Qed.

Lemma BAT_rep_FOv_l : forall l1 l2 atm,
  BAT atm = true ->
  BAT (replace_FOv_l atm l1 l2) = true.
Proof.
  induction l1; intros l2 atm Hat. assumption.
  simpl. destruct l2. assumption.
  apply BAT_rep_FOv. apply IHl1. assumption.
Qed.

Lemma consistent_lx_lx_x_cons : forall l1 l2 x y z,
  consistent_lx_lx_x (cons x l1) (cons y l2) z ->
  consistent_lx_lx_x l1 l2 z.
Proof.
  intros l1 l2 x y z Hcon.
  unfold consistent_lx_lx_x in *.
  unfold is_constant in *.
  destruct Hcon as [a [n H]].
    unfold indicies_l2_FOv in *.
    destruct x as [xn]. destruct z as [zn].
    simpl indicies_l2_FOv_pre in H.
    case_eq (beq_nat zn xn); intros Hbeq; rewrite Hbeq in *.
      simpl in H. rewrite ind_gen_FOv_pre_cons in H.
      destruct n. discriminate. simpl in H. inversion H as [H2].
      exists a. exists n. assumption.

      rewrite ind_gen_FOv_pre_cons in H. exists a. exists n.
      assumption.
Qed.

Lemma consistent_lx_lx_cons : forall l1 l2 x y,
  consistent_lx_lx (cons x l1) (cons y l2) ->
  consistent_lx_lx l1 l2.
Proof.
  intros l1 l2 x y Hcon.
  unfold consistent_lx_lx in *.
  intros xx. specialize (Hcon xx). apply consistent_lx_lx_x_cons in Hcon.
  assumption.
Qed.

Lemma leb_max_FOv_rep_FOv : forall atm x ym,
  Nat.leb (max_FOv (replace_FOv atm x (Var ym))) 
    (max (max_FOv atm) ym) = true.
Proof.
  induction atm; intros [xn] ym.
    simpl. destruct p. destruct f as [zn].
    case_eq (beq_nat xn zn); intros Hbeq;
      simpl; [rewrite max_comm|]; apply leb_max_suc3;
      apply leb_refl.

    destruct f as [z1]; destruct f0 as [z2].
    simpl. case_eq (beq_nat xn z1); intros Hbeq;
      case_eq (beq_nat xn z2); intros Hbeq2;
        simpl.
        rewrite max_refl. rewrite (max_comm _ ym).
        apply leb_max_suc3. apply leb_refl.

        rewrite (max_comm _ ym).
        apply leb_max_max_gen.
          apply leb_refl.

          rewrite max_comm.
          apply leb_max_suc3. apply leb_refl.

        apply leb_max_max_gen.
          apply leb_max_suc3. apply leb_refl.

          apply leb_refl.


        apply leb_max_suc3. apply leb_refl.

    destruct f as [z1]; destruct f0 as [z2].
    simpl. case_eq (beq_nat xn z1); intros Hbeq;
      case_eq (beq_nat xn z2); intros Hbeq2;
        simpl.
        rewrite max_refl. rewrite (max_comm _ ym).
        apply leb_max_suc3. apply leb_refl.

        rewrite (max_comm _ ym).
        apply leb_max_max_gen.
          apply leb_refl.

          rewrite max_comm.
          apply leb_max_suc3. apply leb_refl.

        apply leb_max_max_gen.
          apply leb_max_suc3. apply leb_refl.

          apply leb_refl.


        apply leb_max_suc3. apply leb_refl.

    destruct f as [zn]. simpl.
    case_eq (beq_nat xn zn); intros Hbeq.
      simpl. rewrite <- (max_refl   (Nat.max (Nat.max zn (max_FOv atm)) ym)).
      apply leb_max_max_gen.
        rewrite (max_comm _ ym).
        apply leb_max_suc3. apply leb_refl.

        rewrite <- PeanoNat.Nat.max_assoc.
        rewrite (max_comm zn).
        apply leb_max_suc3. apply IHatm.

      simpl. rewrite <- PeanoNat.Nat.max_assoc.
      apply leb_max_max_gen. apply leb_refl.
      apply IHatm.

    destruct f as [zn]. simpl.
    case_eq (beq_nat xn zn); intros Hbeq.
      simpl. rewrite <- (max_refl   (Nat.max (Nat.max zn (max_FOv atm)) ym)).
      apply leb_max_max_gen.
        rewrite (max_comm _ ym).
        apply leb_max_suc3. apply leb_refl.

        rewrite <- PeanoNat.Nat.max_assoc.
        rewrite (max_comm zn).
        apply leb_max_suc3. apply IHatm.

      simpl. rewrite <- PeanoNat.Nat.max_assoc.
      apply leb_max_max_gen. apply leb_refl.
      apply IHatm.

    simpl in *. apply IHatm.

    simpl in *. rewrite <- (max_refl (Nat.max (Nat.max (max_FOv atm1) (max_FOv atm2)) ym)).
    apply leb_max_max_gen.
(*       rewrite (max_comm (max_FOv atm1)). *)
      rewrite <- PeanoNat.Nat.max_assoc. rewrite (max_comm _ ym).
      rewrite PeanoNat.Nat.max_assoc. apply leb_max_suc3.
      apply IHatm1.

      rewrite (max_comm (max_FOv atm1)). 
      rewrite <- PeanoNat.Nat.max_assoc. rewrite (max_comm _ ym).
      rewrite PeanoNat.Nat.max_assoc. apply leb_max_suc3.
      apply IHatm2.

    simpl in *. rewrite <- (max_refl (Nat.max (Nat.max (max_FOv atm1) (max_FOv atm2)) ym)).
    apply leb_max_max_gen.
(*       rewrite (max_comm (max_FOv atm1)). *)
      rewrite <- PeanoNat.Nat.max_assoc. rewrite (max_comm _ ym).
      rewrite PeanoNat.Nat.max_assoc. apply leb_max_suc3.
      apply IHatm1.

      rewrite (max_comm (max_FOv atm1)). 
      rewrite <- PeanoNat.Nat.max_assoc. rewrite (max_comm _ ym).
      rewrite PeanoNat.Nat.max_assoc. apply leb_max_suc3.
      apply IHatm2.

    simpl in *. rewrite <- (max_refl (Nat.max (Nat.max (max_FOv atm1) (max_FOv atm2)) ym)).
    apply leb_max_max_gen.
(*       rewrite (max_comm (max_FOv atm1)). *)
      rewrite <- PeanoNat.Nat.max_assoc. rewrite (max_comm _ ym).
      rewrite PeanoNat.Nat.max_assoc. apply leb_max_suc3.
      apply IHatm1.

      rewrite (max_comm (max_FOv atm1)). 
      rewrite <- PeanoNat.Nat.max_assoc. rewrite (max_comm _ ym).
      rewrite PeanoNat.Nat.max_assoc. apply leb_max_suc3.
      apply IHatm2.

    simpl in *. destruct p. simpl. apply IHatm.

    simpl in *. destruct p. simpl. apply IHatm.
Qed. 

Lemma leb_max_FOv_rep_FOv_l : forall l1 l2 atm,
  Nat.leb (max_FOv (replace_FOv_l atm l1 l2)) 
    (max (max_FOv atm)  (max_FOv_l l2)) = true.
Proof.
  induction l1; intros l2 atm. simpl.
    apply max_leb_l with (b := (max_FOv_l l2)). reflexivity.

    destruct l2. simpl. rewrite PeanoNat.Nat.max_0_r.
    apply leb_refl.

    simpl. destruct f as [zn].
    rewrite PeanoNat.Nat.max_assoc.
    rewrite (max_comm _ zn).
    rewrite <- PeanoNat.Nat.max_assoc.
    apply (leb_trans _ _ _ (leb_max_FOv_rep_FOv _ _ _)).
    rewrite (max_comm _ zn).
    apply leb_max_max_gen.
      apply leb_refl.

      apply IHl1.
Qed.

Lemma leb_max_FOv_rand2 : forall zn l1 l2' rel atm alpha,
Nat.leb (S (max_FOv (conjSO (conjSO rel atm) alpha))) (min_FOv_l (Var zn :: l2')) = true ->
decr_strict_FOv (Var zn :: l2') = true ->
Nat.leb (S (max_FOv (conjSO (conjSO rel (replace_FOv_l atm l1 l2')) alpha))) zn = true.
Proof.
  intros until 0. intros Hleb Hdec.
  simpl in *. destruct l2'. destruct zn. discriminate. destruct l1; simpl; assumption.
  destruct zn.  discriminate.
  remember (cons f l2') as l2.
  simpl in *. apply if_then_else_ft in Hdec.
  destruct Hdec as [Hdec1 Hdec2].
  case_eq (min_FOv_l l2). intros Hnil. rewrite Hnil in *.
     discriminate.
  intros mm Hmm. rewrite Hmm in Hleb. 
  apply leb_min_r in Hleb.
  destruct Hleb as [Hleb2 Hleb3]. 
  apply leb_max in Hleb2. destruct Hleb2 as [Hleb2 Hleb4].
  apply leb_max in Hleb2. destruct Hleb2 as [Hleb2 Hleb5].
  rewrite <- (max_refl zn).
  apply leb_max_max_gen.
    rewrite <- (max_refl zn).
    apply leb_max_max_gen. all : try assumption.
    apply (leb_trans _ _ _ (leb_max_FOv_rep_FOv_l _ _ _)).
    rewrite <- (max_refl zn). apply leb_max_max_gen;
    assumption.
Qed.

Lemma leb_max_FOv_l_rand8 : forall l1 ym zn l2',
Nat.leb (S (max_FOv_l (Var ym :: l1))) (min_FOv_l (Var zn :: l2')) = true ->
Nat.leb (S ym) zn = true.
Proof.
  intros l1 ym zn l2' H. simpl in *.
  destruct l2'. destruct zn. discriminate.
    apply leb_max in H. apply H.
  remember (cons f l2') as l2.
  destruct zn. discriminate.
  simpl in *. case_eq (min_FOv_l l2). 
    intros Hnil. rewrite Hnil in *. discriminate.
  intros m Hm. rewrite Hm in *.
  apply leb_max in H.
  destruct H as [H1 H2].
  apply leb_min_r in H1. apply H1.
Qed.

Lemma ren_FOv_llist_not_occ : forall l x y,
  ex_FOvar_x_ll x l = false ->
  rename_FOv_llist l x y = l.
Proof.
  induction l; intros [xn] [ym] H. reflexivity.
  simpl in *. case_eq (is_in_FOvar (Var xn) a);
    intros Hin; rewrite Hin in *. discriminate.
  rewrite IHl.
  rewrite ren_FOv_list_not_in. reflexivity.
  assumption. assumption.
Qed.

(* Left it here 23/01/18. Need to add hypothesis. *)
Lemma ex_FOvar_x_ll_ren_FOv_llist : forall ll x y,
~ x = y ->
ex_FOvar_x_ll x (rename_FOv_llist ll x y) = false.
Proof.
  induction ll; intros [xn] [ym] Hnot. reflexivity.
  simpl in *. rewrite IHll.
  rewrite is_in_FOvar_rename. reflexivity.
  all : assumption.
Qed.

Lemma ex_FOvar_x_ll_ren_FOv_llist2 : forall alpha x y z,
~ x = y ->
~ x = z ->
ex_FOvar_x_ll x (rename_FOv_llist alpha y z) = 
ex_FOvar_x_ll x alpha.
Proof.
  induction alpha; intros [xn] [ym] [zn] H1 H2.
    reflexivity.
  simpl. rewrite is_in_FOvar_rename_FOv_list2.
  rewrite IHalpha. reflexivity.
  all : assumption.
Qed.

Lemma ex_FOv_x_ll_ren_FOv_llist_l : forall l1 l2 llv x,
  length l1 = length l2 ->
  is_in_FOvar x l1 = true ->
  is_in_FOvar x l2 = false ->
  ex_FOvar_x_ll x (rename_FOv_llist_l llv l1 l2) = false.
Proof.
  induction l1; intros l2 llv x Hl Hin1 Hin2. discriminate.
  simpl in *. destruct x as [xn]. destruct a as [ym].
  destruct l2. discriminate.
  case_eq (beq_nat xn ym); intros Hbeq; rewrite Hbeq in *.
    rewrite (beq_nat_true _ _ Hbeq).
    apply ex_FOvar_x_ll_ren_FOv_llist.
    destruct f as [zn]. apply beq_nat_false_FOv.
    simpl in Hin2. rewrite (beq_nat_true _ _ Hbeq) in *.
    case_eq (beq_nat ym zn); intros Hbeq2; rewrite Hbeq2 in *.
      discriminate. reflexivity.

      destruct f as [zn]. rewrite ex_FOvar_x_ll_ren_FOv_llist2.
      apply IHl1; try assumption.
      simpl in Hl. inversion Hl. reflexivity.
      simpl in Hin2. case_eq (beq_nat xn zn); intros Hbeq2;
        rewrite Hbeq2 in *. discriminate.
      assumption.

      apply beq_nat_false_FOv. assumption.

      simpl in Hin2. case_eq (beq_nat xn zn); intros Hbeq3;
        rewrite Hbeq3 in *. discriminate.
      apply beq_nat_false_FOv. assumption.
Qed.

Lemma  ren_FOv_list__l_rem: forall l1 l2 llv x y,
  length l1 = length l2 ->
  is_in_FOvar x l1 = true ->
  is_in_FOvar x l2 = false ->
  rename_FOv_llist (rename_FOv_llist_l llv l1 l2) x y =
  rename_FOv_llist_l llv l1 l2.
Proof.
  intros l1 l2 llv x y Hl Hin1 Hin2.
  rewrite ren_FOv_llist_not_occ. reflexivity.
  apply ex_FOv_x_ll_ren_FOv_llist_l; try assumption.
Qed.

Lemma is_all_diff_FOv2_calc_llv_P_rename_FOv_A_pre2_pre : forall l1 l2 alpha rel atm,
  REL rel = true ->
  BAT atm = true ->
  length l1 = length l2 ->
  Nat.leb (S (max_FOv (conjSO (conjSO rel atm) alpha))) (min_FOv_l l2) = true ->
  is_all_diff_FOv l2 = true ->
  decr_strict_FOv l2 = true ->
  Nat.leb (S (max_FOv_l l1)) (min_FOv_l l2) = true ->
  consistent_lx_lx l1 l2 ->
  (forall P, is_all_diff_FOv2 (calc_llv_P atm P) = true) ->
  forall P, is_all_diff_FOv2 (rename_FOv_llist_l (calc_llv_P atm P) l1 l2) = true.
Proof.
  induction l1; intros l2 alpha rel atm Hrel Hbat Hl Hleb Hall Hdec Hleb2 Hcon Hall2.
    assumption.
  destruct l2. assumption.
  simpl.
  destruct f as [zn]. destruct l2. destruct l1. 2 : discriminate.
    simpl in *. destruct a as [ym].
    rewrite PeanoNat.Nat.max_0_r in Hleb2.
    apply is_all_diff_FOv2_calc_llv_P_rename_FOv_A_pre2_pre_pre
      with (alpha := alpha) (rel := rel); try assumption.

  remember (cons f l2) as l2'. destruct a as [ym]. intros P.
  case_eq (is_in_FOvar (Var ym) l1); intros Hin.
    rewrite ren_FOv_list__l_rem. apply IHl1 with (alpha := alpha)
      (rel := rel); try assumption.
      simpl in Hl. inversion Hl. reflexivity.

      simpl min_FOv_l in Hleb. rewrite Heql2' in Hleb.
      rewrite <- Heql2' in Hleb. apply leb_min_r in Hleb.
      apply Hleb.

      simpl in Hall. case_eq (is_in_FOvar (Var zn) l2');
        intros HHin; rewrite HHin in *. discriminate.
      assumption.

      apply decr_strict_FOv_cons in Hdec. assumption.

    assert (Nat.leb (S (max_FOv_l (Var ym :: l1))) (min_FOv_l (l2')) = true) as Hass.
      simpl. case_eq (min_FOv_l l2'). simpl in *. intros Hnil; rewrite Hnil in *. 
      rewrite Heql2' in *. destruct zn; discriminate.

      intros mm Hmm. simpl in Hleb2. rewrite Heql2' in Hleb2. rewrite <- Heql2' in Hleb2.
      destruct zn. discriminate. simpl in Hleb2. rewrite Hmm in Hleb2.
      apply leb_min_r in Hleb2. apply Hleb2.

    case_eq (min_FOv_l l2'). intros H. rewrite H in *. discriminate.
    intros mm Hmm. rewrite Hmm in Hass. simpl in *.
    apply leb_max in Hass. apply Hass.

    apply consistent_lx_lx_cons in Hcon. assumption.

    simpl in Hl. inversion Hl. reflexivity.

    assumption.

    simpl in Hleb2. rewrite Heql2' in Hleb2.
    rewrite <- Heql2' in Hleb2.
    destruct zn. discriminate.
    simpl in Hleb2. case_eq (min_FOv_l l2').
      intros Hnil. rewrite Hnil in *. discriminate.
    intros m Hm. rewrite Hm in Hleb2.
    apply is_in_FOvar_min_FOv_l with (n := ym).
      simpl. rewrite Hm. 
      apply leb_max in Hleb2. destruct Hleb2 as [Hleb2 Hleb3].
      apply leb_min_r in Hleb2. apply Hleb2.

      apply leb_refl.

  rewrite <- calc_llv_P_rep_FOv_l.
  apply is_all_diff_FOv2_calc_llv_P_rename_FOv_A_pre2_pre_pre
    with (alpha := alpha) (rel := rel); try assumption.

    apply BAT_rep_FOv_l. assumption.

    apply leb_max_FOv_rand2; assumption.

    apply leb_max_FOv_l_rand8 in Hleb2; assumption.

  intros P2. rewrite calc_llv_P_rep_FOv_l.
  apply IHl1 with (alpha := alpha) (rel := rel); try assumption.
    simpl in Hl. inversion Hl. reflexivity.

    apply (leb_trans _ _ _ Hleb). simpl. rewrite Heql2'.
    rewrite <- Heql2'.  rewrite min_comm. apply leb_min_l.

    rewrite is_all_diff_FOv_cons in Hall.
    case_eq (is_in_FOvar (Var zn) l2'); intros Hin2; rewrite Hin2 in *.
      discriminate. assumption.

    apply decr_strict_FOv_cons in Hdec. assumption.

    assert (Nat.leb (S (max_FOv_l (Var ym :: l1))) (min_FOv_l (l2')) = true) as Hass.
      simpl. case_eq (min_FOv_l l2'). simpl in *. intros Hnil; rewrite Hnil in *. 
      rewrite Heql2' in *. destruct zn; discriminate.

      intros mm Hmm. simpl in Hleb2. rewrite Heql2' in Hleb2. rewrite <- Heql2' in Hleb2.
      destruct zn. discriminate. simpl in Hleb2. rewrite Hmm in Hleb2.
      apply leb_min_r in Hleb2. apply Hleb2.

    case_eq (min_FOv_l l2'). intros H. rewrite H in *. discriminate.
    intros mm Hmm. rewrite Hmm in Hass. simpl in *.
    apply leb_max in Hass. apply Hass.

    apply consistent_lx_lx_cons in Hcon. assumption.
Qed.

(* Lemma is_all_diff_FOv2_calc_llv_P_rename_FOv_A_pre2 : forall l1 l2 alpha rel atm,
  REL rel = true ->
  BAT atm = true ->
  length l1 = length l2 ->
  Nat.leb (S (max_FOv (conjSO (conjSO rel atm) alpha))) (min_FOv_l l2) = true ->
  is_all_diff_FOv l2 = true ->
  decr_strict_FOv l2 = true ->
  Nat.leb (S (max_FOv_l l1)) (min_FOv_l l2) = true ->
  consistent_lx_lx l1 l2 ->
  (forall P, is_all_diff_FOv2 (calc_llv_P atm P) = true) ->
  forall P, is_all_diff_FOv2 (calc_llv_P (replace_FOv_l atm l1 l2) P) = true.
Proof.
  intros until 0. intros Hrel Hbat Hl Hleb Hall Hdec Hleb2 Hcon Hall2 P.
  rewrite calc_llv_P_rep_FOv_l.
  

(rename_FOv_llist_l (calc_llv_P atm P) l1 l2)

  induction l1; intros l2 alpha rel atm Hrel Hbat Hl Hleb Hall Hdec Hleb2 Hcon Hall2 P.
    simpl in *. destruct l2. 2 : discriminate. apply Hall2.

    destruct l2. discriminate. simpl in *.
    



replace_FOv_l
rename_FOv_list_l
Search calc_llv_P replace_FOv.


Admitted. *)

Lemma is_all_diff_FOv2_calc_llv_P_rename_FOv_A : forall atm rel atm' rel' lv alpha,
BAT atm = true ->
REL rel = true ->
is_in_FOvar (Var 0) lv = false ->
rename_FOv_A (conjSO rel atm) alpha lv = conjSO rel' atm' ->
  (forall P, 
    is_all_diff_FOv2  (calc_llv_P atm P) = true) ->
  forall P,
    is_all_diff_FOv2 (calc_llv_P atm' P) = true.
Proof.
  intros until 0; intros Hat Hrel Hren Hin H.
  case_eq lv. 
    intros Hlv. rewrite Hlv in *. unfold rename_FOv_A in Hin. simpl in *.
    inversion Hin as [[H1 H2 ]]. rewrite H2 in *. assumption.

    intros y ly Hly.

(*   destruct (rename_FOv_A_rep_FOv_l3 lv (conjSO rel atm) alpha) as [l1 [l2 [Heq [Hl Hleb]]]];
    try assumption. rewrite Hly. discriminate.
 *)
(*  [Hall [Hleb2 Hdec]]]]]]];
    try assumption. rewrite Hly. discriminate.
*)
  destruct (rename_FOv_A_rep_FOv_l3 lv (conjSO rel atm) alpha) as [l1 [l2 [Heq [Hl [Hleb [Hall [Hleb2 Hdec]]]]]]];
    try assumption. rewrite Hly. discriminate.
  destruct (rename_FOv_A_rep_FOv_l9 l1 l2 (conjSO rel atm) alpha) as 
    [l1' [l2' [Heq' [H1' [H2' [H3' [H4' [H5' [H6' [H7' H8']]]]]]]]]];
    try assumption.
  rewrite <- Heq in Heq'.
  rewrite Hin in *.
  rewrite rep_FOv_l_conjSO in Heq'.
  inversion Heq' as [[Heq1 Heq2]].
  intros P.
  rewrite calc_llv_P_rep_FOv_l.
  apply is_all_diff_FOv2_calc_llv_P_rename_FOv_A_pre2_pre with (rel := rel) (alpha := alpha);
     try assumption.
Qed.



(*     rewrite Hly. discriminate. 
  rewrite Heq in *.
  rewrite rep_FOv_l_conjSO in Hin.
  inversion Hin as [[ Ha Hb]].    
  apply is_all_diff_FOv2_calc_llv_P_rename_FOv_A_pre; try assumption. 
  simpl in *.
  destruct (min_FOv_l l2). discriminate.  
  apply leb_max in H2. destruct H2 as [H2 H5].
  apply leb_max in H2. apply H2.
Qed. *)

(* Lemma is_all_diff_FOv2_calc_llv_P_rename_FOv_A : forall atm rel atm' rel' lv alpha,
BAT atm = true ->
REL rel = true ->
is_in_FOvar (Var 0) lv = false ->
rename_FOv_A (conjSO rel atm) alpha lv = conjSO rel' atm' ->
  (forall P, 
    is_all_diff_FOv2  (calc_llv_P atm P) = true) ->
  forall P,
    is_all_diff_FOv2 (calc_llv_P atm' P) = true.
Proof.
  intros until 0; intros Hat Hrel Hren Hin H.
  case_eq lv. 
    intros Hlv. rewrite Hlv in *. unfold rename_FOv_A in Hin. simpl in *.
    inversion Hin as [[H1 H2 ]]. rewrite H2 in *. assumption.

    intros y ly Hly.
  destruct (rename_FOv_A_rep_FOv_l2 lv (conjSO rel atm) alpha) as [l1 [l2 [Heq [H1 [H2 [H3 H4]]]]]];
    try assumption.
    rewrite Hly. discriminate. 
  rewrite Heq in *.
  rewrite rep_FOv_l_conjSO in Hin.
  inversion Hin as [[ Ha Hb]].    
  apply is_all_diff_FOv2_calc_llv_P_rename_FOv_A_pre; try assumption. 
  simpl in *.
  destruct (min_FOv_l l2). discriminate.  
  apply leb_max in H2. destruct H2 as [H2 H5].
  apply leb_max in H2. apply H2.
Qed. *)

(* Lemma is_all_diff_FOv2_calc_llv_P_rename_FOv_A : forall atm rel atm' rel' lv alpha,
BAT atm = true ->
REL rel = true ->
is_in_FOvar (Var 0) lv = false ->
rename_FOv_A (conjSO rel atm) alpha lv = conjSO rel' atm' ->
  (forall P, 
    is_all_diff_FOv2  (calc_llv_P atm P) = true) ->
  forall P,
    is_all_diff_FOv2 (calc_llv_P atm' P) = true.
Proof.
  intros until 0; intros Hat Hrel Hren Hin H.
  case_eq lv. 
    intros Hlv. rewrite Hlv in *. unfold rename_FOv_A in Hin. simpl in *.
    inversion Hin as [[H1 H2 ]]. rewrite H2 in *. assumption.

    intros y ly Hly.
  destruct (rename_FOv_A_rep_FOv_l2_2 lv (conjSO rel atm) alpha) as [l1 [l2 [Heq [H1 [H2 [H3 H4]]]]]];
    try assumption.
    rewrite Hly. discriminate. 
  rewrite Heq in *.
  rewrite rep_FOv_l_conjSO in Hin.
  inversion Hin as [[ Ha Hb]].    
  apply is_all_diff_FOv2_calc_llv_P_rename_FOv_A_pre; try assumption. 
  simpl in *.
  destruct (min_FOv_l l2). discriminate.  
  apply leb_max in H2. destruct H2 as [H2 H5].
  apply leb_max in H2. apply H2.
Qed. *)
(*

(* Lemma is_all_diff_FOv2_calc_llv_P_rename_FOv_A_num_conn : forall m n atm rel atm' rel' lv alpha,
  n = num_conn atm ->
  Nat.leb n m = true ->
BAT atm = true ->
REL rel = true ->
  is_in_FOvar (Var 0) lv = false ->
rename_FOv_A (conjSO rel atm) alpha lv = conjSO rel' atm' ->
  (forall P, 
    is_all_diff_FOv2  (calc_llv_P atm P) = true) ->
  forall P,
    is_all_diff_FOv2 (calc_llv_P atm' P) = true.
Proof.
   

  induction m; intros until 0; intros Hnum Hleb Hat Hrel Hin Hren H.
    destruct n. destruct atm; try discriminate.
    destruct (rename_FOv_A_conjSO_predSO lv alpha rel p f Hrel) as [rel'' [f' [H1 H2]]].
    rewrite Hren in H1. inversion H1 as [[H3 H4]].
    simpl. reflexivity. discriminate.

    destruct n. destruct atm; try discriminate.
    destruct (rename_FOv_A_conjSO_predSO lv alpha rel p f Hrel) as [rel'' [f' [H1 H2]]].
    rewrite Hren in H1. inversion H1 as [[H3 H4]].
    simpl. reflexivity.

    destruct atm; try discriminate.
      apply 

Search rename_FOv_A.


    


    destruct (sSahlq_preprocessing3_added.rename_FOv_A_rel_batm lv rel (predSO p f) alpha) as
      [rel'' [atm'' [H1'' [H2'' H3'']]]];
      try assumption.
    rewrite Hren in H1''.
    inversion H1'' as [H1'''].
    unfold rename_FOv_A in Hren. simpl in Hren.
    simpl in *.
Admitted.

 *)
*)
Require Import List.

Lemma is_all_diff_FOv2_rename_FOv_A_num_conn : forall n lP atm rel atm' rel' lv alpha,
length lP = n ->
BAT atm = true ->
REL rel = true ->
rename_FOv_A (conjSO rel atm) alpha lv = conjSO rel' atm' ->
is_in_FOvar (Var 0) lv = false ->
(forall lP : list predicate,
       is_all_diff_FOv2
         (flat_map (fun l : list (list FOvariable) => l) 
          (calc_llv_lP atm lP)) = true) ->
       is_all_diff_FOv2
         (flat_map (fun l : list (list FOvariable) => l) 
          (calc_llv_lP atm' lP)) = true.
Proof.
  induction n; intros lP atm rel atm' rel' lv alpha Hl Hat Hrel Hren Hin H.
    destruct lP. reflexivity. discriminate.

  destruct lP. discriminate.
  simpl. rewrite is_all_diff_FOv2_app.
  simpl in Hl. inversion Hl as [Hl'].
  rewrite (IHn lP _ _ _ _ _ _ Hl' Hat Hrel Hren Hin H).
  rewrite (is_all_diff_FOv2_calc_llv_P_rename_FOv_A _ _ _ _ _ _ Hat Hrel Hin Hren).
    reflexivity.
  apply is_all_diff_FOv2_calc_llv_lP__P. assumption.
Qed.


Lemma is_all_diff_FOv2_rename_FOv_A : forall lP atm rel atm' rel' lv alpha,
BAT atm = true ->
REL rel = true ->
rename_FOv_A (conjSO rel atm) alpha lv = conjSO rel' atm' ->
is_in_FOvar (Var 0) lv = false ->
(forall lP : list predicate,
       is_all_diff_FOv2
         (flat_map (fun l : list (list FOvariable) => l) 
          (calc_llv_lP atm lP)) = true) ->
       is_all_diff_FOv2
         (flat_map (fun l : list (list FOvariable) => l) 
          (calc_llv_lP atm' lP)) = true.
Proof.
  intros until 0. apply (is_all_diff_FOv2_rename_FOv_A_num_conn
    (length lP)). reflexivity.
Qed.
(*
  intros until 0. apply (is_all_diff_FOv2_rename_FOv_A_num_conn (length lP)
    lP _ _ _ _ _ _ eq_refl).
Qed.
  induction lP; intros atm rel atm' rel' lv alpha Hat Hrel Hren H. reflexivity.
  simpl. rewrite is_all_diff_FOv2_app.
  rewrite (IHlP _ _ _ _ _ _ Hat Hrel Hren H).
  rewrite is_all_diff_FOv2_calc_llv_lP__P. reflexivity.
  intros lP'. unfold fun_id_list.
  apply (IHlP _ _ _ _ _ _ Hat Hrel Hren H).
  assumption.


Admitted. *)

Open Scope type.

(* sSahlq4_7_plus_I *)

Lemma sS_preprocessing_Step1_1_againTRY'_withex''' : forall phi1 phi2 rel atm x lv,
  sSahlq_ante phi1 = true ->
  uniform_pos phi2 ->
  is_in_FOvar (Var 0) lv = false ->
  REL rel = true ->
  BAT atm = true ->
          is_in_pred_l (preds_in (conjSO rel atm)) (preds_in (ST phi1 x)) = true ->
is_in_FOvar_l lv (FOvars_in (conjSO rel atm)) = true ->
( forall lP,  (is_all_diff_FOv2 (flat_map (fun l : list (list FOvariable) => l) 
(calc_llv_lP atm lP)) = true)) ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
      (Ir : W -> W -> Prop),
    SOturnst W Iv Ip Ir (ST phi1 x) <->
    SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv)) ->
existsT2 lv0 : list FOvariable,
     ((existsT2 atm0 : SecOrder,
        (is_in_FOvar (Var 0) lv0 = false) *
         (BAT atm0 = true) *
((is_in_FOvar (Var (new_FOv_pp_pre2 atm0)) (FOvars_in atm0) = false) * 
( forall lP,  (is_all_diff_FOv2 (flat_map (fun l : list (list FOvariable) => l)
       (calc_llv_lP atm0 lP)) = true)) * 
  ((existsT rel0 : SecOrder,
     REL rel0 = true /\
          is_in_pred_l (preds_in (conjSO rel0 atm0)) (preds_in (ST phi1 x)) = true /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (ST (mimpl phi1 phi2) x) <->
          SOturnst W Iv Ip Ir
            (list_closed_allFO (implSO (conjSO rel0 atm0) (ST phi2 x)) lv0))) +
       (is_in_pred_l (preds_in atm0) (preds_in (ST phi1 x)) = true /\
      forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir (ST (mimpl phi1 phi2) x) <->
      SOturnst W Iv Ip Ir (list_closed_allFO (implSO atm0 (ST phi2 x)) lv0)))))).
Proof.
  intros phi1 phi2 rel atm x lv Hvsa Hun Hin0 HREL HAT Hin Hinl Hall H.
  pose proof (equiv_implSO2 _ _ (ST phi2 x) H) as H1.
  pose proof (equiv3_3_struc2_2' lv (conjSO rel atm) (ST phi2 x)) as H2.
  pose proof (SOturnst_trans _ _ _ H1 H2) as H3.
  pose proof rename_FOv_A_rel_atm.
  destruct (sSahlq_preprocessing3_added.rename_FOv_A_rel_batm lv rel atm (ST phi2 x) HREL HAT)
     as [rel' [atm' [H' [HREL' HAT']]]] . assumption.
  rewrite H' in *.
  exists (rename_FOv_A_list (conjSO rel atm) (ST phi2 x) lv).
  exists atm'.
  apply pair.
apply pair.
apply is_in_FOvar_rename_FOv_A_list_0. assumption. apply pair.
unfold new_FOv_pp_pre2.
 apply pair.
rewrite max_FOv__l.
apply is_in_FOvar_S_max_FOv_l.
intros lP.
 apply (is_all_diff_FOv2_rename_FOv_A _ _ _ _ _ _ _ HAT HREL H' Hin0 Hall).

(*  apply (is_all_diff_FOv2_rename_FOv_A _ _ _ _ _ _ _ HAT HREL H' Hall).
 *)
  left.
  exists rel'.
  apply conj. assumption.
  apply conj. 2: assumption.
    rewrite <- H'.
    rewrite preds_in_rename_FOv_A.
    assumption.
Defined.

(* Lemma sS_preprocessing_Step1_1_againTRY'_withex'' : forall phi1 phi2 rel atm x lv,
  sSahlq_ante phi1 = true ->
  uniform_pos phi2 ->
  is_in_FOvar (Var 0) lv = false ->
  REL rel = true ->
  BAT atm = true ->
          is_in_pred_l (preds_in (conjSO rel atm)) (preds_in (ST phi1 x)) = true ->
( forall lP,  (is_all_diff_FOv2 (flat_map (fun l : list (list FOvariable) => l) 
(calc_llv_lP atm lP)) = true)) ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
      (Ir : W -> W -> Prop),
    SOturnst W Iv Ip Ir (ST phi1 x) <->
    SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv)) ->
existsT2 lv0 : list FOvariable,
     ((existsT2 atm0 : SecOrder,
        (is_in_FOvar (Var 0) lv0 = false) *
         (BAT atm0 = true) *
((is_in_FOvar (Var (new_FOv_pp_pre2 atm0)) (FOvars_in atm0) = false) * 
( forall lP,  (is_all_diff_FOv2 (flat_map (fun l : list (list FOvariable) => l)
       (calc_llv_lP atm0 lP)) = true)) * 
  ((existsT rel0 : SecOrder,
     REL rel0 = true /\
          is_in_pred_l (preds_in (conjSO rel0 atm0)) (preds_in (ST phi1 x)) = true /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (ST (mimpl phi1 phi2) x) <->
          SOturnst W Iv Ip Ir
            (list_closed_allFO (implSO (conjSO rel0 atm0) (ST phi2 x)) lv0))) +
       (is_in_pred_l (preds_in atm0) (preds_in (ST phi1 x)) = true /\
      forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir (ST (mimpl phi1 phi2) x) <->
      SOturnst W Iv Ip Ir (list_closed_allFO (implSO atm0 (ST phi2 x)) lv0)))))).
Proof.
  intros phi1 phi2 rel atm x lv Hvsa Hun Hin0 HREL HAT Hin Hall H.
  pose proof (equiv_implSO2 _ _ (ST phi2 x) H) as H1.
  pose proof (equiv3_3_struc2_2' lv (conjSO rel atm) (ST phi2 x)) as H2.
  pose proof (SOturnst_trans _ _ _ H1 H2) as H3.
  pose proof rename_FOv_A_rel_atm.
  destruct (sSahlq_preprocessing3_added.rename_FOv_A_rel_batm lv rel atm (ST phi2 x) HREL HAT)
     as [rel' [atm' [H' [HREL' HAT']]]] . assumption.
  rewrite H' in *.
  exists (rename_FOv_A_list (conjSO rel atm) (ST phi2 x) lv).
  exists atm'.
  apply pair.
apply pair.
apply is_in_FOvar_rename_FOv_A_list_0. assumption. apply pair.
unfold new_FOv_pp_pre2.
 apply pair.
rewrite max_FOv__l.
apply is_in_FOvar_S_max_FOv_l.
intros lP.
 apply (is_all_diff_FOv2_rename_FOv_A _ _ _ _ _ _ _ HAT HREL H' Hin0 Hall).

(*  apply (is_all_diff_FOv2_rename_FOv_A _ _ _ _ _ _ _ HAT HREL H' Hall).
 *)
  left.
  exists rel'.
  apply conj. assumption.
  apply conj. 2: assumption.
    rewrite <- H'.
    rewrite preds_in_rename_FOv_A.
    assumption.
Defined. *)

Lemma is_all_diff_FOv2_calc_llv_lP_predSO : forall lP P x,
  is_all_diff_FOv2 (flat_map fun_id_list (calc_llv_lP (predSO P x) lP)) = 
  is_all_diff_FOv2 (calc_llv_P (predSO P x) P).
Proof.
  induction lP; intros P x. reflexivity.
  simpl. apply IHlP.
Qed.

(* sSahlq4_7_plus_I *)
Lemma preprocess_sSahlq_ante_predSO_againTRY_BAT : forall p f,
  conjSO_exFO_relatSO (predSO p f) = true ->
existsT2 (lv : list FOvariable) (atm : SecOrder),
  (is_in_FOvar (Var 0) lv = false) *
( forall lP,  (is_all_diff_FOv2 (flat_map (fun l : list (list FOvariable) => l)
       (calc_llv_lP atm lP)) = true)) *
  (BAT atm = true) *
  ((existsT rel : SecOrder,
      REL rel = true /\
      is_in_pred_l (preds_in (conjSO rel atm)) (preds_in (predSO p f)) =
      true /\
      (forall (W : Set) (Iv : FOvariable -> W)
         (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop),
       SOturnst W Iv Ip Ir (predSO p f) <->
       SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv))) +
   (is_in_pred_l (preds_in atm) (preds_in (predSO p f)) = true /\
   (forall (W : Set) (Iv : FOvariable -> W)
      (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop),
    SOturnst W Iv Ip Ir (predSO p f) <->
    SOturnst W Iv Ip Ir (list_closed_exFO atm lv)))).
Proof.
  intros p f H.
    exists nil.
    exists (predSO p f).
    destruct p as [Pn].
    destruct f as [xn].
    simpl.
    apply pair. apply pair. apply pair. reflexivity.

      intros lP. rewrite is_all_diff_FOv2_calc_llv_lP_predSO.
      simpl. reflexivity. reflexivity.

      right. rewrite <- beq_nat_refl.
      apply conj. reflexivity.
      intros.
      apply iff_refl.
Defined.


(* sSahlq4_7_plus_I *)
Lemma preprocess_sSahlq_ante_exFO_againTRY_BAT : forall alpha f,
  conjSO_exFO_relatSO_BAT (exFO f alpha) = true ->
   (forall lP, is_all_diff_FOv2 (flat_map (fun l : list (list FOvariable) => l) (calc_llv_lP (exFO f alpha) lP)) =
   true)  ->
  is_in_FOvar (Var 0) (FOvars_in (exFO f alpha)) = false ->
  (existsT P : predicate, P_occurs_in_alpha (exFO f alpha) P = true) ->
(conjSO_exFO_relatSO_BAT alpha = true ->
          (forall lP : list predicate,
           is_all_diff_FOv2
             (flat_map (fun l : list (list FOvariable) => l) (calc_llv_lP alpha lP)) = true) ->
          is_in_FOvar (Var 0) (FOvars_in alpha) = false ->
          (existsT P : predicate, P_occurs_in_alpha alpha P = true) ->
          existsT2 (lv : list FOvariable) (atm : SecOrder),
            (is_in_FOvar (Var 0) lv = false) *
            (forall lP : list predicate,
             is_all_diff_FOv2
               (flat_map (fun l : list (list FOvariable) => l) (calc_llv_lP atm lP)) = true) *
            (BAT atm = true) *
            ((existsT rel : SecOrder,
                REL rel = true /\
                is_in_pred_l (preds_in (conjSO rel atm)) (preds_in alpha) = true /\
                (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
                   (Ir : W -> W -> Prop),
                 SOturnst W Iv Ip Ir alpha <->
                 SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv))) +
             (is_in_pred_l (preds_in atm) (preds_in alpha) = true /\
              (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
                 (Ir : W -> W -> Prop),
               SOturnst W Iv Ip Ir alpha <-> SOturnst W Iv Ip Ir (list_closed_exFO atm lv))))) ->
existsT2 (lv : list FOvariable) (atm : SecOrder),
            (is_in_FOvar (Var 0) lv = false) *
   (forall lP, is_all_diff_FOv2 (flat_map (fun l : list (list FOvariable) => l) (calc_llv_lP atm lP)) =
   true) *
  (BAT atm = true) *
  ((existsT rel : SecOrder,
      REL rel = true /\
      is_in_pred_l (preds_in (conjSO rel atm))
        (preds_in (exFO f alpha)) = true /\
      (forall (W : Set) (Iv : FOvariable -> W)
         (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop),
       SOturnst W Iv Ip Ir (exFO f alpha) <->
       SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv))) +
   (is_in_pred_l (preds_in atm) (preds_in (exFO f alpha)) = true /\
   (forall (W : Set) (Iv : FOvariable -> W)
      (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop),
    SOturnst W Iv Ip Ir (exFO f alpha) <->
    SOturnst W Iv Ip Ir (list_closed_exFO atm lv)))).
Proof.
Admitted.
(*
  intros alpha f H Hin0 Hocc IHalpha.
    simpl in H.
    destruct Hocc as [P Hocc]. rewrite <- P_occurs_in_alpha_exFO in Hocc.
    assert (existsT P, P_occurs_in_alpha alpha P = true) as Hocc2.
      exists P. assumption.
    simpl FOvars_in in Hin0. apply is_in_FOvar_cons_f in Hin0.
    destruct Hin0 as [HH01 HH02].
    specialize (IHalpha H HH01 Hocc2).
    destruct IHalpha as [lv [atm [[Hin00 HAT] [  [rel [HREL [Hin SOt]]] | [Hin SOt] ]]]];
      exists (cons f lv);
      exists atm;
      apply pair. apply pair. simpl. rewrite Hin00.
      destruct f as [nn]. destruct nn. contradiction (HH02 eq_refl).
reflexivity.
assumption.
      left.
      exists rel.
      apply conj. assumption.
      apply conj. rewrite preds_in_exFO. assumption.

      intros W Iv Ip Ir.
      simpl list_closed_exFO.
      do 2 rewrite SOturnst_exFO.
      split; intros SOt2;
        destruct SOt2 as [d SOt2];
        exists d;
        apply SOt;
        assumption.
apply pair.
simpl. rewrite Hin00.
      destruct f as [nn]. destruct nn. contradiction (HH02 eq_refl).
reflexivity.
assumption.

      right.
      apply conj. rewrite preds_in_exFO. assumption.
      intros W Iv Ip Ir.
      simpl list_closed_exFO.
      do 2 rewrite SOturnst_exFO.
      split; intros SOt2;
        destruct SOt2 as [d SOt2];
        exists d;
        apply SOt;
        assumption.
Defined.
*)

Lemma is_all_diff_FOv2_calc_llv_lP_conjSO_r : forall lP alpha1 alpha2,
  is_all_diff_FOv2 (flat_map fun_id_list (calc_llv_lP (conjSO alpha1 alpha2) lP)) = true ->
  is_all_diff_FOv2 (flat_map fun_id_list (calc_llv_lP alpha2 lP)) = true.
Proof.
  induction lP; intros alpha1 alpha2 H. reflexivity.
  simpl in *. rewrite is_all_diff_FOv2_app in *. 
  apply if_then_else_ft in H. destruct H as [H1 H2].
  unfold fun_id_list in H1. rewrite is_all_diff_FOv2_app in H1.
  apply if_then_else_ft in H1. destruct H1 as [H1 H3].
  unfold fun_id_list at 1. rewrite H3.
  apply (IHlP alpha1). assumption.
Qed.

Lemma is_all_diff_FOv2_calc_llv_lP_conjSO_l : forall lP alpha1 alpha2,
  is_all_diff_FOv2 (flat_map fun_id_list (calc_llv_lP (conjSO alpha1 alpha2) lP)) = true ->
  is_all_diff_FOv2 (flat_map fun_id_list (calc_llv_lP alpha1 lP)) = true.
Proof.
  induction lP; intros alpha1 alpha2 H. reflexivity.
  simpl in *. rewrite is_all_diff_FOv2_app in *. 
  apply if_then_else_ft in H. destruct H as [H1 H2].
  unfold fun_id_list in H1. rewrite is_all_diff_FOv2_app in H1.
  apply if_then_else_ft in H1. destruct H1 as [H1 H3].
  unfold fun_id_list at 1. rewrite H1.
  apply (IHlP alpha1 alpha2). assumption.
Qed.


(* Left it here 9/01/18 *)
(* Not sure if this will work. *)
(* sSahlq4_7_plus_I *)
Lemma preprocess_sSahlq_ante_4_againTRY_BAT : forall alpha1 alpha2 lv1 rel1 lv2 rel2 atm2,
( forall lP,  (is_all_diff_FOv2 (flat_map (fun l : list (list FOvariable) => l)
       (calc_llv_lP atm2 lP)) = true)) ->

  conjSO_exFO_relatSO_BAT alpha2 = true ->
  REL rel1 = true -> 
is_in_FOvar (Var 0) lv1 = false ->
is_in_FOvar (Var 0) lv2 = false ->
is_in_FOvar_l lv1 (FOvars_in rel1) = true ->
is_in_FOvar_l lv2 (FOvars_in (conjSO rel2 atm2)) = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha1 <->
      SOturnst W Iv Ip Ir (list_closed_exFO rel1 lv1)) ->
  REL rel2 = true ->
  BAT atm2 = true ->
  is_in_pred_l (preds_in (conjSO rel2 atm2)) (preds_in alpha2) = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha2 <->
      SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel2 atm2) lv2) ) ->
  conjSO_exFO_relatSO_BAT alpha1 = true ->
existsT2 lv : list FOvariable,
  (existsT2 atm : SecOrder,
    (is_in_FOvar (Var 0) lv = false) *
( forall lP,  (is_all_diff_FOv2 (flat_map (fun l : list (list FOvariable) => l)
       (calc_llv_lP atm lP)) = true)) *
         (BAT atm = true) *
    (existsT rel : SecOrder,
       REL rel = true /\
          is_in_pred_l (preds_in (conjSO rel atm))
                       (preds_in (conjSO alpha1 alpha2)) = true /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
          SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv)))).
Proof.
  intros alpha1 alpha2 lv1 rel1 lv2 rel2 atm2
        Hall  H HREL1 Hin01 Hin02 Hin03 Hin04 H_1 HREL2 HAT2 Hin H_2 H1.
     destruct (same_struc_conjSO_ex_BAT2 _ _ _ (same_struc_BAT2_rename_FOv_A (conjSO rel2 atm2) 
                                            (list_closed_exFO rel1 lv1)
                                             lv2 Hin02)) as [rel2' [atm2' Heq2]].
     exists (app 
                (rename_FOv_A_list (conjSO rel2 atm2) 
                     (list_closed_exFO rel1 lv1) lv2)
(rename_FOv_A_list rel1 
                  (rename_FOv_A (conjSO rel2 atm2)
                     (list_closed_exFO rel1 lv1) lv2) lv1 )).
    exists  atm2'.
    apply pair.
      pose proof (same_struc_BAT2_rename_FOv_A (conjSO rel2 atm2) (list_closed_exFO rel1 lv1)
         lv2) as Hsame2.
      pose proof (same_struc_BAT2_rename_FOv_A rel1
         (rename_FOv_A (conjSO rel2 atm2)
            (list_closed_exFO rel1 lv1) lv2) lv1) as Hsame1.

destruct Heq2 as [Heq2 Heq22].
      rewrite Heq2 in Hsame2.

rewrite  Heq2 in *. apply pair.
apply pair.
apply is_in_FOvar_rename_FOv_A_list_0_app.

intros lP.

apply (is_all_diff_FOv2_rename_FOv_A _ _ _ _ _ _ _ HAT2 HREL2 Heq2);
assumption.

(* destruct (sSahlq_preprocessing3_added.rename_FOv_A_rel_batm
  _ _ _ (list_closed_exFO rel1 lv1) HREL2 HAT2 Hin02) as [rel'' [atm'' [H1'' [H2'' H3'']]]].
rewrite Heq2 in H1''. inversion H1''. assumption.
 *)
apply (same_struc_BAT2_conjSO_BAT_r atm2 atm2' rel2 rel2');
try assumption.
apply rename_FOv_A_REL in Heq2; assumption.
apply same_struc_BAT2_comm.
apply Hsame2. assumption.

(*       apply same_struc_BAT2_conjSO_r in Hsame2.
      apply same_struc_comm in Hsame2.
rewrite Heq2 in Heq22.
      apply same_struc_BAT in Hsame2; try assumption. *)
    exists (conjSO (rename_FOv_A rel1 (rename_FOv_A (conjSO rel2 atm2) 
                      (list_closed_exFO rel1 lv1) lv2) lv1) rel2').
    apply conj.
      pose proof (same_struc_BAT2_rename_FOv_A (conjSO rel2 atm2) (list_closed_exFO rel1 lv1)
         lv2) as Hsame2.
      pose proof (same_struc_BAT2_rename_FOv_A rel1
         (rename_FOv_A (conjSO rel2 atm2)
            (list_closed_exFO rel1 lv1) lv2) lv1) as Hsame1.
      destruct Heq2 as [Heq2 Heq2'].
      rewrite Heq2 in Hsame2.
apply REL_conjSO_rename_FOv_A; try assumption.
apply rename_FOv_A_REL in Heq2; assumption.

(*      apply same_struc_conjSO_l in Hsame2.
      apply same_struc_comm in Hsame2.
      apply same_struc_REL in Hsame2; try assumption.
      apply same_struc_comm in Hsame1.
      apply same_struc_REL in Hsame1; try assumption.
      simpl; rewrite Hsame1; assumption.
*)
    apply conj.
      assert (preds_in (rename_FOv_A (conjSO rel2 atm2)   
                      (list_closed_exFO rel1 lv1) lv2) =
                       preds_in (conjSO rel2' atm2')) as Hpreds.
      destruct Heq2 as [Heq2 Heq2'].
        rewrite Heq2. reflexivity.
      simpl. rewrite preds_in_rename_FOv_A in *.
      rewrite <- app_assoc.
      assert (preds_in (conjSO rel2' atm2') = 
              app (preds_in rel2') (preds_in atm2')) as Hpreds2.
        reflexivity.
      rewrite <- Hpreds2.
      rewrite <- Hpreds.
      apply is_in_pred_l_2app.
      rewrite preds_in_rel. reflexivity. assumption.
      assumption.

    intros W Iv Ip Ir.
    split; intros SOt.
      apply (equiv_list_closed_exFO (conjSO (conjSO (rename_FOv_A rel1 (rename_FOv_A (conjSO rel2 atm2) 
                      (list_closed_exFO rel1 lv1) lv2) lv1) rel2')  atm2')
                                    (conjSO (rename_FOv_A rel1 (rename_FOv_A (conjSO rel2 atm2) 
                      (list_closed_exFO rel1 lv1) lv2) lv1) (conjSO rel2' atm2'))).
        intros; split; intros; apply equiv_conjSO5; assumption.
      destruct Heq2 as [Heq2 Heq2'].
      rewrite <- Heq2.
      rewrite list_closed_exFO_app.
      apply equiv3_3_struc2_both with (alpha := rel1).
      rewrite SOturnst_conjSO; apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.

      apply (equiv_list_closed_exFO (conjSO (conjSO (rename_FOv_A rel1 (rename_FOv_A (conjSO rel2 atm2) 
                      (list_closed_exFO rel1 lv1) lv2) lv1) rel2')  atm2')
                                    (conjSO (rename_FOv_A rel1 (rename_FOv_A (conjSO rel2 atm2) 
                      (list_closed_exFO rel1 lv1) lv2) lv1) (conjSO rel2' atm2'))) in SOt;
        try (intros; split; intros; apply equiv_conjSO5; assumption).
      destruct Heq2 as [Heq2 Heq2'].
      rewrite <- Heq2 in SOt.
      rewrite list_closed_exFO_app in SOt.
      apply equiv3_3_struc2_both with (alpha := rel1) in SOt.
      rewrite SOturnst_conjSO; apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.
Defined.

(* commented 28/03
Lemma preprocess_sSahlq_ante_4_againTRY_BAT : forall alpha1 alpha2 lv1 rel1 lv2 rel2 atm2,
( forall lP,  (is_all_diff_FOv2 (flat_map (fun l : list (list FOvariable) => l)
       (calc_llv_lP atm2 lP)) = true)) ->

  conjSO_exFO_relatSO_BAT alpha2 = true ->
  REL rel1 = true -> 
is_in_FOvar (Var 0) lv1 = false ->
is_in_FOvar (Var 0) lv2 = false ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha1 <->
      SOturnst W Iv Ip Ir (list_closed_exFO rel1 lv1)) ->
  REL rel2 = true ->
  BAT atm2 = true ->
  is_in_pred_l (preds_in (conjSO rel2 atm2)) (preds_in alpha2) = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha2 <->
      SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel2 atm2) lv2) ) ->
  conjSO_exFO_relatSO_BAT alpha1 = true ->
existsT2 lv : list FOvariable,
  (existsT2 atm : SecOrder,
    (is_in_FOvar (Var 0) lv = false) *
( forall lP,  (is_all_diff_FOv2 (flat_map (fun l : list (list FOvariable) => l)
       (calc_llv_lP atm lP)) = true)) *
         (BAT atm = true) *
    (existsT rel : SecOrder,
       REL rel = true /\
          is_in_pred_l (preds_in (conjSO rel atm))
                       (preds_in (conjSO alpha1 alpha2)) = true /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
          SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv)))).
Proof.
  intros alpha1 alpha2 lv1 rel1 lv2 rel2 atm2
        Hall  H HREL1 Hin01 Hin02 H_1 HREL2 HAT2 Hin H_2 H1.
     destruct (same_struc_conjSO_ex_BAT2 _ _ _ (same_struc_BAT2_rename_FOv_A (conjSO rel2 atm2) 
                                            (list_closed_exFO rel1 lv1)
                                             lv2 Hin02)) as [rel2' [atm2' Heq2]].
     exists (app 
                (rename_FOv_A_list (conjSO rel2 atm2) 
                     (list_closed_exFO rel1 lv1) lv2)
(rename_FOv_A_list rel1 
                  (rename_FOv_A (conjSO rel2 atm2)
                     (list_closed_exFO rel1 lv1) lv2) lv1 )).
    exists  atm2'.
    apply pair.
      pose proof (same_struc_BAT2_rename_FOv_A (conjSO rel2 atm2) (list_closed_exFO rel1 lv1)
         lv2) as Hsame2.
      pose proof (same_struc_BAT2_rename_FOv_A rel1
         (rename_FOv_A (conjSO rel2 atm2)
            (list_closed_exFO rel1 lv1) lv2) lv1) as Hsame1.

destruct Heq2 as [Heq2 Heq22].
      rewrite Heq2 in Hsame2.

rewrite  Heq2 in *. apply pair.
apply pair.
apply is_in_FOvar_rename_FOv_A_list_0_app.

intros lP.

apply (is_all_diff_FOv2_rename_FOv_A _ _ _ _ _ _ _ HAT2 HREL2 Heq2);
assumption.

(* destruct (sSahlq_preprocessing3_added.rename_FOv_A_rel_batm
  _ _ _ (list_closed_exFO rel1 lv1) HREL2 HAT2 Hin02) as [rel'' [atm'' [H1'' [H2'' H3'']]]].
rewrite Heq2 in H1''. inversion H1''. assumption.
 *)
apply (same_struc_BAT2_conjSO_BAT_r atm2 atm2' rel2 rel2');
try assumption.
apply rename_FOv_A_REL in Heq2; assumption.
apply same_struc_BAT2_comm.
apply Hsame2. assumption.

(*       apply same_struc_BAT2_conjSO_r in Hsame2.
      apply same_struc_comm in Hsame2.
rewrite Heq2 in Heq22.
      apply same_struc_BAT in Hsame2; try assumption. *)
    exists (conjSO (rename_FOv_A rel1 (rename_FOv_A (conjSO rel2 atm2) 
                      (list_closed_exFO rel1 lv1) lv2) lv1) rel2').
    apply conj.
      pose proof (same_struc_BAT2_rename_FOv_A (conjSO rel2 atm2) (list_closed_exFO rel1 lv1)
         lv2) as Hsame2.
      pose proof (same_struc_BAT2_rename_FOv_A rel1
         (rename_FOv_A (conjSO rel2 atm2)
            (list_closed_exFO rel1 lv1) lv2) lv1) as Hsame1.
      destruct Heq2 as [Heq2 Heq2'].
      rewrite Heq2 in Hsame2.
apply REL_conjSO_rename_FOv_A; try assumption.
apply rename_FOv_A_REL in Heq2; assumption.

(*      apply same_struc_conjSO_l in Hsame2.
      apply same_struc_comm in Hsame2.
      apply same_struc_REL in Hsame2; try assumption.
      apply same_struc_comm in Hsame1.
      apply same_struc_REL in Hsame1; try assumption.
      simpl; rewrite Hsame1; assumption.
*)
    apply conj.
      assert (preds_in (rename_FOv_A (conjSO rel2 atm2)   
                      (list_closed_exFO rel1 lv1) lv2) =
                       preds_in (conjSO rel2' atm2')) as Hpreds.
      destruct Heq2 as [Heq2 Heq2'].
        rewrite Heq2. reflexivity.
      simpl. rewrite preds_in_rename_FOv_A in *.
      rewrite <- app_assoc.
      assert (preds_in (conjSO rel2' atm2') = 
              app (preds_in rel2') (preds_in atm2')) as Hpreds2.
        reflexivity.
      rewrite <- Hpreds2.
      rewrite <- Hpreds.
      apply is_in_pred_l_2app.
      rewrite preds_in_rel. reflexivity. assumption.
      assumption.

    intros W Iv Ip Ir.
    split; intros SOt.
      apply (equiv_list_closed_exFO (conjSO (conjSO (rename_FOv_A rel1 (rename_FOv_A (conjSO rel2 atm2) 
                      (list_closed_exFO rel1 lv1) lv2) lv1) rel2')  atm2')
                                    (conjSO (rename_FOv_A rel1 (rename_FOv_A (conjSO rel2 atm2) 
                      (list_closed_exFO rel1 lv1) lv2) lv1) (conjSO rel2' atm2'))).
        intros; split; intros; apply equiv_conjSO5; assumption.
      destruct Heq2 as [Heq2 Heq2'].
      rewrite <- Heq2.
      rewrite list_closed_exFO_app.
      apply equiv3_3_struc2_both with (alpha := rel1).
      rewrite SOturnst_conjSO; apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.

      apply (equiv_list_closed_exFO (conjSO (conjSO (rename_FOv_A rel1 (rename_FOv_A (conjSO rel2 atm2) 
                      (list_closed_exFO rel1 lv1) lv2) lv1) rel2')  atm2')
                                    (conjSO (rename_FOv_A rel1 (rename_FOv_A (conjSO rel2 atm2) 
                      (list_closed_exFO rel1 lv1) lv2) lv1) (conjSO rel2' atm2'))) in SOt;
        try (intros; split; intros; apply equiv_conjSO5; assumption).
      destruct Heq2 as [Heq2 Heq2'].
      rewrite <- Heq2 in SOt.
      rewrite list_closed_exFO_app in SOt.
      apply equiv3_3_struc2_both with (alpha := rel1) in SOt.
      rewrite SOturnst_conjSO; apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.
Defined. *)


Lemma is_all_diff_FOv2_calc_llv_lP_conjSO1_pre : forall lP alpha1 alpha2,
       is_all_diff_FOv2
         (flat_map (fun l : list (list FOvariable) => l)
            (calc_llv_lP (conjSO alpha1 alpha2) lP)) = true ->
       is_all_diff_FOv2
         (flat_map (fun l : list (list FOvariable) => l)
            (calc_llv_lP alpha1 lP)) = true.
Proof.
  induction lP; intros alpha1 alpha2 H. reflexivity.
  simpl in *. do 2 rewrite is_all_diff_FOv2_app in *.
  apply if_then_else_ft in H. destruct H as [H1 H2].
  apply if_then_else_ft in H1. destruct H1 as [H1 H3].
  rewrite H1. apply IHlP in H2. assumption.
Qed.

Lemma is_all_diff_FOv2_calc_llv_lP_conjSO1 : forall alpha1 alpha2,
(forall lP : list predicate,
       is_all_diff_FOv2
         (flat_map (fun l : list (list FOvariable) => l)
            (calc_llv_lP (conjSO alpha1 alpha2) lP)) = true) ->
(forall lP : list predicate,
       is_all_diff_FOv2
         (flat_map (fun l : list (list FOvariable) => l)
            (calc_llv_lP alpha1 lP)) = true).
Proof.
  intros alpha1 alpha2 H lP.
  apply is_all_diff_FOv2_calc_llv_lP_conjSO1_pre with (alpha2 := alpha2).
  apply H.
Qed.

Lemma is_all_diff_FOv2_calc_llv_lP_conjSO2_pre : forall lP alpha1 alpha2,
       is_all_diff_FOv2
         (flat_map (fun l : list (list FOvariable) => l)
            (calc_llv_lP (conjSO alpha1 alpha2) lP)) = true ->
       is_all_diff_FOv2
         (flat_map (fun l : list (list FOvariable) => l)
            (calc_llv_lP alpha2 lP)) = true.
Proof.
  induction lP; intros alpha1 alpha2 H. reflexivity.
  simpl in *. do 2 rewrite is_all_diff_FOv2_app in *.
  apply if_then_else_ft in H. destruct H as [H1 H2].
  apply if_then_else_ft in H1. destruct H1 as [H1 H3].
  rewrite H3. apply IHlP in H2. assumption.
Qed.

Lemma is_all_diff_FOv2_calc_llv_lP_conjSO2 : forall alpha1 alpha2,
(forall lP : list predicate,
       is_all_diff_FOv2
         (flat_map (fun l : list (list FOvariable) => l)
            (calc_llv_lP (conjSO alpha1 alpha2) lP)) = true) ->
(forall lP : list predicate,
       is_all_diff_FOv2
         (flat_map (fun l : list (list FOvariable) => l)
            (calc_llv_lP alpha2 lP)) = true).
Proof.
  intros alpha1 alpha2 H lP.
  apply is_all_diff_FOv2_calc_llv_lP_conjSO2_pre with (alpha1 := alpha1).
  apply H.
Qed.


(* sSahlq4_7_plus_I *)
Lemma preprocess_sSahlq_ante_againTRY : forall alpha,
  conjSO_exFO_relatSO_BAT alpha = true ->
( forall lP,  (is_all_diff_FOv2 (flat_map (fun l : list (list FOvariable) => l)
       (calc_llv_lP alpha lP)) = true)) ->
  is_in_FOvar (Var 0) (FOvars_in alpha) = false ->
  (existsT P, P_occurs_in_alpha alpha P = true) ->
  existsT2 lv atm,
    (is_in_FOvar (Var 0) lv = false) *
( forall lP,  (is_all_diff_FOv2 (flat_map (fun l : list (list FOvariable) => l)
       (calc_llv_lP atm lP)) = true)) *
    (BAT atm = true) *
    ((existsT rel,
      REL rel = true /\
      is_in_pred_l (preds_in (conjSO rel atm)) (preds_in alpha) = true /\
        forall W Iv Ip Ir,
          SOturnst W Iv Ip Ir alpha <->
          SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv)) +
     (is_in_pred_l (preds_in atm) (preds_in alpha) = true /\
        forall W Iv Ip Ir,
          SOturnst W Iv Ip Ir alpha <->
          SOturnst W Iv Ip Ir (list_closed_exFO atm lv))).
Proof.
Admitted.
(* commented 28/03
  intros alpha H Hall Hin0 Hocc.
  induction alpha; try (simpl in *; discriminate).
    apply preprocess_sSahlq_ante_predSO_againTRY_BAT; assumption.

    destruct Hocc as [[Pn] Hocc].
    unfold P_occurs_in_alpha in Hocc. destruct f. destruct f0.
    simpl in Hocc. discriminate.

    apply conjSO_exFO_relatSO_BAT_allFO in H. 
exists nil. exists (allFO f alpha). apply pair.
    apply pair. apply pair. reflexivity.
assumption.

 assumption.
right. simpl. apply conj.
apply is_in_pred_l_refl.
intros. apply iff_refl.


    apply preprocess_sSahlq_ante_exFO_againTRY_BAT; try assumption.

    simpl in H.
    case_eq (conjSO_exFO_relatSO_BAT alpha1); intros H1;
      rewrite H1 in H; try discriminate.
    specialize (IHalpha1 H1).
case_eq (conjSO_exFO_relatSO_BAT alpha2 ); intros H1'.

    specialize (IHalpha2 H1').
    destruct (trying1 alpha1) as [Hocc1 | Hocc2].
    destruct (preprocess_vsSahlq_ante_notocc_againTRY_BAT _ H1 
      (is_in_FOvar_app_l _ _ _ Hin0) Hocc1)
      as [lv1 [rel1 [Hin01 [Hrel1 [Hin1 SOt]]]]].
    destruct IHalpha2 as [lv2 [atm2 [Hat2 [[rel2 [Hrel2 [Hin H2]]] | [Hin H2]]]]].

intros lP. apply (is_all_diff_FOv2_calc_llv_lP_conjSO_r _ alpha1).
apply Hall.

      apply is_in_FOvar_app_r in Hin0.
 assumption.

      destruct Hocc as [P Hocc].
      apply P_occurs_in_alpha_conjSO_comp in Hocc.
      rewrite (Hocc1 P) in Hocc.
      destruct Hocc. discriminate.
      exists P. assumption.

      destruct (preprocess_sSahlq_ante_4_againTRY_BAT alpha1 alpha2 lv1 rel1 lv2 rel2 atm2)
        as [lv' [atm' [Hat' [rel' [Hrel' [Hin' H']]]]]]; try assumption.
apply Hat2. apply Hat2. apply Hat2.



      exists lv'. exists atm'. apply pair.
        apply pair. apply pair. apply Hat'.
admit. apply Hat'.
      left. exists rel'. apply conj. assumption.
      apply conj. all: try assumption.

      destruct (preprocess_sSahlq_ante_6_againTRY_BAT alpha1 alpha2 lv1 rel1 lv2 atm2)
        as [lv' [atm' [Hat' [rel' [Hrel' [Hin' H']]]]]]; try assumption.
apply Hat2. apply Hat2.
      exists lv'. exists atm'. apply pair.
apply pair. apply pair. apply Hat'. admit. apply Hat'.
      left. exists rel'. apply conj. assumption.
      apply conj. all: try assumption.

    destruct (trying1 alpha2) as [Hocc1b | Hocc2b].
    destruct (preprocess_vsSahlq_ante_notocc_againTRY_BAT _ H1' 
      (is_in_FOvar_app_r _ _ _ Hin0) Hocc1b)
      as [lv2 [rel2 [Hrel2 [Hin2 SOt]]]].
    destruct IHalpha1 as [lv1 [atm1 [Hat1 [[rel1 [Hrel1 [Hin H2]]] | [Hin H2]]]]].

intros lP. apply (is_all_diff_FOv2_calc_llv_lP_conjSO_l _ alpha1 alpha2).
apply Hall.

    apply (is_in_FOvar_app_l _ _ _ Hin0).
      assumption.

      destruct (preprocess_sSahlq_ante_2_againTRY_BAT alpha1 alpha2 lv1 rel1 atm1 lv2 rel2)
        as [lv' [atm' [Hat' [rel' [Hrel' [Hin' H']]]]]]; try assumption.
 apply Hat1. apply Hat1. apply SOt.
      exists lv'. exists atm'. apply pair.
apply pair. apply pair. apply Hat'. admit. apply Hat'.
(*  apply Hat1. assumption. *)
      left. exists rel'. apply conj. assumption.
      apply conj. all: try assumption.

      destruct (preprocess_sSahlq_ante_8_againTRY alpha1 alpha2 lv1 atm1 lv2 rel2)
        as [lv' [atm' [Hat' [rel' [Hrel' [Hin' H']]]]]]; try assumption.
apply Hat1.
apply Hat1.
apply SOt.
      exists lv'. exists atm'. apply pair.
apply pair. apply pair. apply Hat'.
admit. apply Hat'.

      left. exists rel'. apply conj. assumption.
      apply conj. all: try assumption.

      pose proof (is_all_diff_FOv2_calc_llv_lP_conjSO1 alpha1 alpha2 Hall) as Hass1.
      pose proof (is_all_diff_FOv2_calc_llv_lP_conjSO2 alpha1 alpha2 Hall) as Hass2.
      destruct (IHalpha1 Hass1 (is_in_FOvar_app_l _ _ _ Hin0) Hocc2) as [lv1 [atm1 [Hatm1 [[rel1 [Hrel1 [Hin SOt]] ] | [Hin SOt ] ]]] ].
      destruct (IHalpha2 Hass2 (is_in_FOvar_app_r _ _ _ Hin0) Hocc2b) as [lv2 [atm2 [Hatm2 [[rel2 [Hrel2 [Hin2 SOt2]] ] | [Hin2 SOt2 ] ]]] ].

      destruct (preprocess_sSahlq_ante_1_againTRY alpha1 alpha2 lv1 rel1 atm1 lv2 rel2 atm2)
        as [lv' [atm' [Hat' [rel' [Hrel' [Hin' H']]]]]]; try assumption.
apply Hatm1.
apply Hatm2.
apply Hatm1.
apply Hatm2.
      exists lv'. exists atm'. apply pair.
apply pair. apply pair. apply Hat'.
admit. apply Hat'.

      left. exists rel'. apply conj. assumption.
      apply conj. all: try assumption.

      destruct (preprocess_sSahlq_ante_3_againTRY alpha1 alpha2 lv1 rel1 atm1 lv2 atm2)
        as [lv' [atm' [Hat' [rel' [Hrel' [Hin' H']]]]]]; try assumption.
apply Hatm1.
apply Hatm2.
apply Hatm1.
apply Hatm2.
      exists lv'. exists atm'. apply pair. apply pair.
      apply pair. apply Hat'.
admit. apply Hat'.
      left. exists rel'. apply conj. assumption.
      apply conj. all: try assumption.

      destruct (IHalpha2 Hass2 (is_in_FOvar_app_r _ _ _ Hin0) Hocc2b) as [lv2 [atm2 [Hatm2 [[rel2 [Hrel2 [Hin2 SOt2]] ] | [Hin2 SOt2 ] ]]] ].

      destruct (preprocess_sSahlq_ante_7_againTRY alpha1 alpha2 lv1 atm1 lv2 rel2 atm2)
        as [lv' [atm' [Hat' [rel' [Hrel' [Hin' H']]]]]]; try assumption.
apply Hatm1.
apply Hatm2.
apply Hatm1.
apply Hatm2.
 
      exists lv'. exists atm'. apply pair.
      apply pair. apply pair. apply Hat'.
admit. apply Hat'.
      left. exists rel'. apply conj. assumption.
      apply conj. all: try assumption.

      destruct (preprocess_sSahlq_ante_9_againTRY alpha1 alpha2 lv1 atm1 lv2 atm2)
        as [lv' [atm' [Hat' [Hin' H']]]]; try assumption.
apply Hatm1.
apply Hatm2.
apply Hatm1.
apply Hatm2.

      exists lv'. exists atm'. apply pair.  
      apply pair. apply pair. apply Hat'.
admit. apply Hat'.
      right. apply conj. assumption.
      assumption.

(* rewrite H1' in *.
case_eq (BAT alpha1); intros Hbat1; rewrite Hbat1 in *.
case_eq (BAT alpha2); intros Hbat2; rewrite Hbat2 in *.
all : try discriminate. *)

exists nil. exists (conjSO alpha1 alpha2). apply pair.
apply pair. apply pair. reflexivity.
admit.
simpl. 
case_eq (if BAT alpha1 then BAT alpha2 else false);
  intros HBAT; rewrite HBAT in *.  reflexivity.
  rewrite H1' in *. discriminate.
(* rewrite Hbat1. assumption. *)
right. simpl. apply conj.
apply is_in_pred_l_refl.
intros. apply iff_refl.

case_eq (BAT alpha1); intros Hbat1; rewrite Hbat1 in *.
case_eq (BAT alpha2); intros Hbat2; rewrite Hbat2 in *.
all : try discriminate.

exists nil. exists (conjSO alpha1 alpha2). apply pair.
apply pair. apply pair. reflexivity.
admit.
simpl. rewrite Hbat1. assumption.
right. simpl. apply conj.
apply is_in_pred_l_refl.
intros. apply iff_refl.
Qed.
*)

(* sSahlq4_7_plus_I *)
Lemma sS_preprocessing_Step1_pre_againTRY'_withex' : forall phi1 phi2 x,
  ~ x = Var 0 ->
  sSahlq_ante phi1 = true ->
  uniform_pos phi2  ->
  existsT2 lv : list FOvariable,
   (existsT2 atm : SecOrder,
       (is_in_FOvar (Var 0) lv = false) *
       (BAT atm = true) *
((is_in_FOvar (Var (new_FOv_pp_pre2 atm)) (FOvars_in atm) = false) * 
 ( forall lP,  (is_all_diff_FOv2 (flat_map (fun l : list (list FOvariable) => l)
       (calc_llv_lP atm lP)) = true)) * 
    ((existsT rel : SecOrder,
     REL rel = true /\
          is_in_pred_l (preds_in (conjSO rel atm)) (preds_in (ST phi1 x)) = true /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (ST (mimpl phi1 phi2) x) <->
          SOturnst W Iv Ip Ir (list_closed_allFO (implSO (conjSO rel atm) (ST phi2 x)) lv))) +

    (is_in_pred_l (preds_in atm) (preds_in (ST phi1 x)) = true /\
      forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir (ST (mimpl phi1 phi2) x) <->
      SOturnst W Iv Ip Ir (list_closed_allFO (implSO atm (ST phi2 x)) lv))))).
Proof.
Admitted.
(* commented 28/03
  intros phi1 phi2 x Hnot Hvsa Hun.
  pose proof (preprocess_sSahlq_ante_againTRY (ST phi1 x)
      (sSahlq_ante_conjSO_exFO_relatSO_BAT _ _ Hvsa) 
      (is_in_FOvar_ST_0_not phi1 x Hnot) (ex_P_ST phi1 x)) as H1.
  destruct H1 as [lv [atm [[Hin1 HAT] [ [rel [HREL [Hin H]]] | [Hin H] ]]]].
  
    apply sS_preprocessing_Step1_1_againTRY'_withex'' with (phi2 := phi2) in H; try assumption.
    apply sS_preprocessing_Step1_3_againTRY'_withex' with (phi2 := phi2) in H; try assumption.
Defined.
*)

Lemma sSahlq_hopeful4_REV'_withex'_FULL : forall lP xn phi1 phi2,
  sSahlq_ante phi1 = true ->
  uniform_pos phi2  ->
  ~ Var xn = Var 0 ->
  is_in_pred_l (preds_in (ST (mimpl phi1 phi2) (Var xn))) lP = true ->
  existsT2 (lx : list FOvariable) (atm : SecOrder),
    (is_in_FOvar (Var 0) lx = false) *
    (BAT atm = true) *
    ((existsT rel,
      REL rel = true /\
      is_in_pred_l (preds_in (conjSO rel atm)) (preds_in (ST phi1 (Var xn))) = true /\
      (is_all_diff_FOv2 (flat_map (fun l : list (list FOvariable) => l) (calc_llv_lP atm lP)) = true) /\
forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (replace_pred_l (list_closed_allFO (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))) (Var xn)))))) lx)
    lP (list_Var (length lP) (Var (new_FOv_pp_pre2 (implSO (conjSO rel atm) (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))))))
    (fun4_l2_lP' (calc_lx1_lP atm lP) (list_Var (length lP) (Var (new_FOv_pp_pre2 (implSO (conjSO rel atm) (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn))))))) (new_FOvars_lll (calc_llv_lP atm lP) (Var (S(max_FOv (implSO (conjSO rel atm)
     (newnew_pre (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))
        (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))) (Var xn))
        (rev_seq (S (Nat.max (max_FOv (implSO (conjSO rel atm) (ST phi2 (Var xn)))) xn))
           (length
              (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn))))
 (Var xn)))))) )))))) <->
  SOturnst W Iv Ip Ir (list_closed_SO (ST (mimpl phi1 phi2) (Var xn)) lP)) +

     (is_in_pred_l (preds_in atm) (preds_in (ST phi1 (Var xn))) = true /\
(is_all_diff_FOv2 (flat_map (fun l : list (list FOvariable) => l) (calc_llv_lP atm lP)) = true) /\
forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (replace_pred_l (list_closed_allFO (implSO atm
    (newnew_pre (instant_cons_empty' atm (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO atm (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn)))))) lx)
    lP (list_Var (length lP) (Var (new_FOv_pp_pre2 (implSO atm (instant_cons_empty' atm (ST phi2 (Var xn)))))))
    (fun4_l2_lP' (calc_lx1_lP atm lP) (list_Var (length lP) (Var (new_FOv_pp_pre2 atm))) (new_FOvars_lll (calc_llv_lP atm lP) (Var (S(max_FOv (implSO atm
     (newnew_pre (instant_cons_empty' atm (ST phi2 (Var xn)))
        (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn))
        (rev_seq (S (Nat.max (max_FOv (implSO atm (ST phi2 (Var xn)))) xn))
           (length
              (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn))))
 (Var xn)))))) )))))) <->
  SOturnst W Iv Ip Ir (list_closed_SO (ST (mimpl phi1 phi2) (Var xn)) lP))).
Proof.
Admitted.
(* commented 28/03
  intros lP xn phi1 phi2 Hvs Hun Hnot Hin0.
  destruct (sS_preprocessing_Step1_pre_againTRY'_withex' _ _ (Var xn) Hnot Hvs Hun)
    as [lv [atm [[Hin00 HAT] [Hex [ [rel [HREL [Hin SOt]]]  | [Hin SOt]  ]]]]].
    exists lv. exists atm.
    apply pair. apply pair; assumption.
    left. exists rel. apply conj. assumption.
    apply conj. assumption.
apply conj.

pose proof sSahlq4_7_plus_I.sS_preprocessing_Step1_pre_againTRY'_withex'.
pose proof sS_preprocessing_Step1_pre_againTRY'_withex'.

    intros W Iv Ip Ir.  
split; intros H.
admit.
(*     apply sSahlq_hopeful3_REV with (alpha := (ST (mimpl phi1 phi2) (Var xn))) in H ;
      try assumption.
        apply sSahlq_lem_f3_BAT; assumption.
      apply uni_pos__SO. assumption.
      apply no_SOquant_ST.

      apply att_allFO_x_ST.
      apply att_exFO_x_ST.
      apply closed_except_ST.

apply FAKE.

      apply x_occ_in_alpha_instant_cons_empty'.
        apply x_occ_in_alpha_ST.

      assert (is_in_pred_l 
          (preds_in (implSO (conjSO rel atm) (ST phi2 (Var xn)))) 
          (preds_in (implSO (ST phi1 (Var xn)) (ST phi2 (Var xn)))) = true) as HH1.
        simpl. apply is_in_pred_l_2app.
        apply Hin. apply is_in_pred_l_refl.
      apply (is_in_pred_l_trans _ _ _ HH1 Hin0).

      apply ex_P_occ_in_alpha_ST.
 *)

        apply sSahlq_hopeful3 with (alpha := (ST (mimpl phi1 phi2) (Var xn)));
      try assumption.
      apply uni_pos__SO. assumption.
      apply no_SOquant_ST.

      apply att_allFO_x_ST.
      apply att_exFO_x_ST.
      apply closed_except_ST.
      apply x_occ_in_alpha_instant_cons_empty'.
        apply x_occ_in_alpha_ST.

      assert (is_in_pred_l 
          (preds_in (implSO (conjSO rel atm) (ST phi2 (Var xn)))) 
          (preds_in (implSO (ST phi1 (Var xn)) (ST phi2 (Var xn)))) = true) as HH1.
        simpl. apply is_in_pred_l_2app.
        apply Hin. apply is_in_pred_l_refl.

apply x_occ_in_alpha_new_FOv_pp_pre2.
admit.
admit.
admit.

      assert (is_in_pred_l 
          (preds_in (implSO (conjSO rel atm) (ST phi2 (Var xn)))) 
          (preds_in (implSO (ST phi1 (Var xn)) (ST phi2 (Var xn)))) = true) as HH1.
        simpl. apply is_in_pred_l_2app.
        apply Hin. apply is_in_pred_l_refl.
      apply (is_in_pred_l_trans _ _ _ HH1 Hin0).

      apply ex_P_occ_in_alpha_ST.

    exists lv. exists atm.
    apply pair. apply pair; assumption.
    right.
    apply conj. assumption.
    intros W Iv Ip Ir.
split; intros H.
    apply sSahlq_hopeful3_REV_atm with (alpha := (ST (mimpl phi1 phi2) (Var xn))) in H;
      try assumption.
      apply sSahlq_lem_f3_BAT; assumption.

      apply uni_pos__SO. assumption.
      apply no_SOquant_ST.

      apply att_allFO_x_ST.
      apply att_exFO_x_ST.
      apply closed_except_ST.
      apply x_occ_in_alpha_instant_cons_empty'.
        apply x_occ_in_alpha_ST.

      assert (is_in_pred_l 
          (preds_in (implSO atm (ST phi2 (Var xn)))) 
          (preds_in (implSO (ST phi1 (Var xn)) (ST phi2 (Var xn)))) = true) as HH1.
        simpl. apply is_in_pred_l_2app.
        apply Hin. apply is_in_pred_l_refl.
      apply (is_in_pred_l_trans _ _ _ HH1 Hin0).

      apply ex_P_occ_in_alpha_ST.

    apply sSahlq_hopeful3_atm with (alpha := (ST (mimpl phi1 phi2) (Var xn)));
      try assumption.
      apply uni_pos__SO. assumption.
      apply no_SOquant_ST.

      apply att_allFO_x_ST.
      apply att_exFO_x_ST.
      apply closed_except_ST.
      apply x_occ_in_alpha_instant_cons_empty'.
        apply x_occ_in_alpha_ST.

      assert (is_in_pred_l 
          (preds_in (implSO atm (ST phi2 (Var xn)))) 
          (preds_in (implSO (ST phi1 (Var xn)) (ST phi2 (Var xn)))) = true) as HH1.
        simpl. apply is_in_pred_l_2app.
        apply Hin. apply is_in_pred_l_refl.
      apply (is_in_pred_l_trans _ _ _ HH1 Hin0).

      apply ex_P_occ_in_alpha_ST.
Defined. *)
(* Defined. *)

(* Lemma sSahlq_hopeful4_REV'_withex'_FULL : forall lP  xn phi1 phi2,
  sSahlq_ante phi1 = true ->
  uniform_pos phi2  ->
  ~ Var xn = Var 0 ->
  is_in_pred_l (preds_in (ST (mimpl phi1 phi2) (Var xn))) lP = true ->
  existsT2 (lx : list FOvariable) (atm : SecOrder),
    (is_in_FOvar (Var 0) lx = false) *
    (BAT atm = true) *
    ((existsT rel,
      REL rel = true /\
      is_in_pred_l (preds_in (conjSO rel atm)) (preds_in (ST phi1 (Var xn))) = true /\
forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (replace_pred_l (list_closed_allFO (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))) (Var xn)))))) lx)
    lP (list_Var (length lP) (Var (new_FOv_pp_pre2 atm)))
    (calc_lP atm lP) ) <->
  SOturnst W Iv Ip Ir (list_closed_SO (ST (mimpl phi1 phi2) (Var xn)) lP)) +

     (is_in_pred_l (preds_in atm) (preds_in (ST phi1 (Var xn))) = true /\
forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (replace_pred_l (list_closed_allFO (implSO atm
    (newnew_pre (instant_cons_empty' atm (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO atm (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn)))))) lx)
    lP (list_Var (length lP) (Var (new_FOv_pp_pre2 atm)))
    (calc_lP atm lP)) <->
  SOturnst W Iv Ip Ir (list_closed_SO (ST (mimpl phi1 phi2) (Var xn)) lP))).
Proof.
  intros lP  xn phi1 phi2 Hvs Hun Hnot Hin0.
  destruct (sS_preprocessing_Step1_pre_againTRY'_withex' _ _ (Var xn) Hnot Hvs Hun)
    as [lv [atm [[Hin00 HAT] [Hex [ [rel [HREL [Hin SOt]]]  | [Hin SOt]  ]]]]].
    exists lv. exists atm.
    apply pair. apply pair; assumption.
    left. exists rel. apply conj. assumption.
    apply conj. assumption.
    intros W Iv Ip Ir.  
split; intros H.
    apply sSahlq_hopeful3_REV with (alpha := (ST (mimpl phi1 phi2) (Var xn))) in H ;
      try assumption.
        apply sSahlq_lem_f3_BAT; assumption.
      apply uni_pos__SO. assumption.
      apply no_SOquant_ST.

      apply att_allFO_x_ST.
      apply att_exFO_x_ST.
      apply closed_except_ST.

apply FAKE.

      apply x_occ_in_alpha_instant_cons_empty'.
        apply x_occ_in_alpha_ST.

      assert (is_in_pred_l 
          (preds_in (implSO (conjSO rel atm) (ST phi2 (Var xn)))) 
          (preds_in (implSO (ST phi1 (Var xn)) (ST phi2 (Var xn)))) = true) as HH1.
        simpl. apply is_in_pred_l_2app.
        apply Hin. apply is_in_pred_l_refl.
      apply (is_in_pred_l_trans _ _ _ HH1 Hin0).

      apply ex_P_occ_in_alpha_ST.

        apply sSahlq_hopeful3 with (alpha := (ST (mimpl phi1 phi2) (Var xn)));
      try assumption.
      apply uni_pos__SO. assumption.
      apply no_SOquant_ST.

      apply att_allFO_x_ST.
      apply att_exFO_x_ST.
      apply closed_except_ST.
      apply x_occ_in_alpha_instant_cons_empty'.
        apply x_occ_in_alpha_ST.

      assert (is_in_pred_l 
          (preds_in (implSO (conjSO rel atm) (ST phi2 (Var xn)))) 
          (preds_in (implSO (ST phi1 (Var xn)) (ST phi2 (Var xn)))) = true) as HH1.
        simpl. apply is_in_pred_l_2app.
        apply Hin. apply is_in_pred_l_refl.
      apply (is_in_pred_l_trans _ _ _ HH1 Hin0).

      apply ex_P_occ_in_alpha_ST.

    exists lv. exists atm.
    apply pair. apply pair; assumption.
    right.
    apply conj. assumption.
    intros W Iv Ip Ir.
split; intros H.
    apply sSahlq_hopeful3_REV_atm with (alpha := (ST (mimpl phi1 phi2) (Var xn))) in H;
      try assumption.
      apply sSahlq_lem_f3_BAT; assumption.

      apply uni_pos__SO. assumption.
      apply no_SOquant_ST.

      apply att_allFO_x_ST.
      apply att_exFO_x_ST.
      apply closed_except_ST.
      apply x_occ_in_alpha_instant_cons_empty'.
        apply x_occ_in_alpha_ST.

      assert (is_in_pred_l 
          (preds_in (implSO atm (ST phi2 (Var xn)))) 
          (preds_in (implSO (ST phi1 (Var xn)) (ST phi2 (Var xn)))) = true) as HH1.
        simpl. apply is_in_pred_l_2app.
        apply Hin. apply is_in_pred_l_refl.
      apply (is_in_pred_l_trans _ _ _ HH1 Hin0).

      apply ex_P_occ_in_alpha_ST.

    apply sSahlq_hopeful3_atm with (alpha := (ST (mimpl phi1 phi2) (Var xn)));
      try assumption.
      apply uni_pos__SO. assumption.
      apply no_SOquant_ST.

      apply att_allFO_x_ST.
      apply att_exFO_x_ST.
      apply closed_except_ST.
      apply x_occ_in_alpha_instant_cons_empty'.
        apply x_occ_in_alpha_ST.

      assert (is_in_pred_l 
          (preds_in (implSO atm (ST phi2 (Var xn)))) 
          (preds_in (implSO (ST phi1 (Var xn)) (ST phi2 (Var xn)))) = true) as HH1.
        simpl. apply is_in_pred_l_2app.
        apply Hin. apply is_in_pred_l_refl.
      apply (is_in_pred_l_trans _ _ _ HH1 Hin0).

      apply ex_P_occ_in_alpha_ST.
Defined.
(* Defined. *) *)

Lemma sSahlq_hopeful4_REV'_withex'_FULL_allFO : forall lP  xn phi1 phi2,
  sSahlq_ante phi1 = true ->
  uniform_pos phi2  ->
  ~ Var xn = Var 0 ->
  is_in_pred_l (preds_in (ST (mimpl phi1 phi2) (Var xn))) lP = true ->
  existsT2 lx atm,
    (BAT atm = true) *
    ((existsT rel,
      REL rel = true /\
      is_in_pred_l (preds_in (conjSO rel atm)) (preds_in (ST phi1 (Var xn))) = true /\
forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (allFO (Var xn) (replace_pred_l (list_closed_allFO (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))) (Var xn)))))) lx)
    lP (list_Var (length lP) (Var (new_FOv_pp_pre2 atm)))
    (calc_lP atm lP))) <->
  SOturnst W Iv Ip Ir (allFO (Var xn) (list_closed_SO (ST (mimpl phi1 phi2) (Var xn)) lP))) +

     (is_in_pred_l (preds_in atm) (preds_in (ST phi1 (Var xn))) = true /\
forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (allFO (Var xn) (replace_pred_l (list_closed_allFO (implSO atm
    (newnew_pre (instant_cons_empty' atm (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO atm (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn)))))) lx)
    lP (list_Var (length lP) (Var (new_FOv_pp_pre2 atm)))
    (calc_lP atm lP))) <->
  SOturnst W Iv Ip Ir (allFO (Var xn) (list_closed_SO (ST (mimpl phi1 phi2) (Var xn)) lP)))).
Proof.
Admitted.
(* commented 28/03
  intros lP xn phi1 phi2 H1 H2 Hnot H3.
  destruct (sSahlq_hopeful4_REV'_withex'_FULL lP xn phi1 phi2 H1 H2 Hnot H3) as [lx [atm [[Hin00 Hat] [ [rel [Hrel [Hin SOt]]]| [Hin SOt] ]]]];
  exists lx; exists atm; apply pair; try assumption ; [left | right].
    exists rel. apply conj. assumption. apply conj. assumption.
    intros.
    apply equiv_allFO with (W := W) (Iv := Iv) (Ip := Ip) (Ir := Ir) (x := (Var xn)) in SOt.
    assumption.


    apply conj. assumption. intros.
    apply equiv_allFO with (W := W) (Iv := Iv) (Ip := Ip) (Ir := Ir) (x := (Var xn)) in SOt.
    assumption.
Defined.
*)

Lemma sSahlq_hopeful4_REV'_withex'_FULL_allFO_in : forall lP xn phi1 phi2 ,
  sSahlq_ante phi1 = true ->
  uniform_pos phi2  ->
  ~ Var xn = Var 0 ->
  is_in_pred_l (preds_in (ST (mimpl phi1 phi2) (Var xn))) lP = true ->
  existsT2 lx atm  ,
    (BAT atm = true) *
    ((existsT rel,
      REL rel = true /\
      is_in_pred_l (preds_in (conjSO rel atm)) (preds_in (ST phi1 (Var xn))) = true /\
forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (allFO (Var xn) (replace_pred_l (list_closed_allFO (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))) (Var xn)))))) lx)
    lP (list_Var (length lP) (Var (new_FOv_pp_pre2 atm)))
    (calc_lP atm lP))) <->
  SOturnst W Iv Ip Ir (list_closed_SO (allFO (Var xn) (ST (mimpl phi1 phi2) (Var xn))) lP)) +

     (is_in_pred_l (preds_in atm) (preds_in (ST phi1 (Var xn))) = true /\
forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (allFO (Var xn) (replace_pred_l (list_closed_allFO (implSO atm
    (newnew_pre (instant_cons_empty' atm (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO atm (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn)))))) lx)
    lP (list_Var (length lP) (Var (new_FOv_pp_pre2 atm)))
    (calc_lP atm lP))) <->
  SOturnst W Iv Ip Ir (list_closed_SO (allFO (Var xn) (ST (mimpl phi1 phi2) (Var xn))) lP))).
Proof.
  intros lP xn phi1 phi2 H1 H2 Hnot H3.
  destruct (sSahlq_hopeful4_REV'_withex'_FULL_allFO lP  xn phi1 phi2 H1 H2 Hnot H3) as [lx [atm [Hat [ [rel [Hrel [Hin SOt]]]| [Hin SOt] ]]]];
  exists lx; exists atm; apply pair; try assumption; [left | right].
    exists rel. apply conj. assumption. apply conj. assumption.
    intros. split; intros HH. apply equiv_list_closed_SO_allFO.
      apply SOt. assumption.

      apply equiv_list_closed_SO_allFO in HH. apply SOt. assumption.

    apply conj. assumption. intros.
    split; intros HH. apply equiv_list_closed_SO_allFO.
      apply SOt. assumption.

      apply equiv_list_closed_SO_allFO in HH. apply SOt. assumption.
Defined.

Lemma preds_in_allFO : forall alpha x,
  preds_in (allFO x alpha) = preds_in alpha.
Proof.
  reflexivity.
Qed.

Lemma sSahlq_full_SO_pre : forall xn phi1 phi2,
  sSahlq_ante phi1 = true ->
  uniform_pos phi2  ->
  ~ Var xn = Var 0 ->
  existsT2 lx batm ,
    (BAT batm = true) *
    ((existsT rel,
      REL rel = true /\
      is_in_pred_l (preds_in (conjSO rel batm)) (preds_in (ST phi1 (Var xn))) = true /\
forall W Iv Ip Ir,

  SOturnst W Iv Ip Ir (allFO (Var xn) (replace_pred_l (list_closed_allFO (implSO
    (conjSO rel batm)
    (newnew_pre (instant_cons_empty' (conjSO rel batm) (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel batm) (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel batm) (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel batm) (ST phi2 (Var xn)))) (Var xn)))))) lx)
    (preds_in (ST (mimpl phi1 phi2) (Var xn))) (list_Var (length (preds_in (ST (mimpl phi1 phi2) (Var xn)))) (Var (new_FOv_pp_pre2 batm)))
    (calc_lP batm    (preds_in (allFO (Var xn) (ST (mimpl phi1 phi2) (Var xn))))))) <->
  SOturnst W Iv Ip Ir (uni_closed_SO (allFO (Var xn) (ST (mimpl phi1 phi2) (Var xn))))) +

     (is_in_pred_l (preds_in batm) (preds_in (ST phi1 (Var xn))) = true /\
forall W Iv Ip Ir,

  SOturnst W Iv Ip Ir (allFO (Var xn) (replace_pred_l (list_closed_allFO (implSO batm
    (newnew_pre (instant_cons_empty' batm (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' batm (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO batm (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' batm (ST phi2 (Var xn)))) (Var xn)))))) lx)
    (preds_in (ST (mimpl phi1 phi2) (Var xn))) (list_Var (length (preds_in (ST (mimpl phi1 phi2) (Var xn)))) (Var (new_FOv_pp_pre2 batm)))
    (calc_lP batm (preds_in (allFO (Var xn) (ST (mimpl phi1 phi2) (Var xn))))))) <->
  SOturnst W Iv Ip Ir (uni_closed_SO (allFO (Var xn) (ST (mimpl phi1 phi2) (Var xn)))))).
Proof.
  intros xn phi1 phi2 H1 H2 Hnot. unfold uni_closed_SO in *. unfold uni_closed_SO.
  rewrite preds_in_allFO.

(* pose proof (sSahlq_hopeful4_REV'_withex'_FULL_allFO_in  *)
  apply sSahlq_hopeful4_REV'_withex'_FULL_allFO_in; try assumption.
  simpl. apply is_in_pred_l_refl.
Defined.

Lemma is_un_predless_is_in_pred : forall alpha,
  (forall P, is_in_pred P (preds_in alpha) = false) ->
  is_unary_predless alpha = true.
Admitted.

Lemma is_un_predless_is_in_pred2 : forall alpha P,
  is_unary_predless alpha = true ->
  is_in_pred P (preds_in alpha) = false.
Admitted.

Lemma is_in_pred_l_nil : forall l,
  is_in_pred_l l nil = true ->
  l = nil.
Proof.
  induction l; intros H. reflexivity.
  simpl in H. destruct a. discriminate.
Qed.

Lemma is_un_predless_rep_pred_l_is_in : forall lP lcond alpha x,
  is_in_pred_l (preds_in alpha) lP = true ->
  is_unary_predless_l lcond = true ->
  length lP = length lcond ->
  is_unary_predless (replace_pred_l alpha lP (list_Var (length lP) x) lcond) = true.
Proof.
Admitted.
(*
  induction lP; intros lcond alpha x Hin Hun Hl. 
    simpl. apply is_in_pred_l_nil in Hin.
    apply un_predless_preds_in_rev. assumption.

    case_eq (is_in_pred a (preds_in alpha)); intros Hin2.
      simpl. destruct lcond. discriminate.
      
Search is_unary_predless replace_pred replace_pred_l.
Search is_in_pred_l cons is_in_pred.
admit. 
      simpl. destruct lcond. discriminate.

        simpl in Hl. inversion Hl as [Hl'].
        simpl in Hun. case_eq (is_unary_predless_l lcond);
          intros Hcond; rewrite Hcond in *.
          2 : (rewrite if_then_else_false in Hun; discriminate).
          rewrite rep_pred_not_in. 
          apply is_in_pred_l_cons in Hin; try assumption.
          apply IHlP; assumption.

          apply is_in_pred_l_cons in Hin; try assumption.
          apply is_un_predless_is_in_pred2. apply IHlP;
          assumption.
Qed.

Search is_unary_predless is_in_pred false.
          apply IHlP; assumption.

             apply is_in_pred_l_cons in Hin; try assumption.

            apply IHlP; assumption.
Search is_in_pred replace_pred_l.
Search is_in_pred_l is_in_pred cons.

Search is_in_pred is_in_pred_l cons.
Search is_in_pred replace_pred false.
  intros lP lcond alpha x Hin Hun.
  apply is_un_predless_is_in_pred.
  intros P.
Admitted.
*)

Lemma is_un_predless_l_calc_lP : forall lP batm,
(*   is_in_pred_l (preds_in batm) lP = true -> *)
  is_unary_predless_l (calc_lP batm lP) = true.
Proof.
  induction lP; intros batm. reflexivity.
  simpl in *. rewrite is_un_predless_fun4_l2'.
  apply IHlP.
Qed.

Lemma is_un_predless_corresp_sSahlq : forall xn phi1 phi2 y lx batm rel,
    BAT batm = true ->
    REL rel = true ->
    is_in_pred_l (preds_in (conjSO rel batm)) (preds_in (ST phi1 (Var xn))) = true ->
  is_unary_predless ((replace_pred_l (list_closed_allFO (implSO
    (conjSO rel batm)
    (newnew_pre (instant_cons_empty' (conjSO rel batm) (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel batm) (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel batm) (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel batm) (ST phi2 (Var xn)))) (Var xn)))))) lx)
    (preds_in (ST (mimpl phi1 phi2) (Var xn))) (list_Var (length (preds_in (ST (mimpl phi1 phi2) (Var xn)))) y)
    (calc_lP batm (preds_in (ST (mimpl phi1 phi2) (Var xn)))))) (* (Var (new_FOv_pp_pre2 batm))) lllv))) *) = true.
Proof.
  intros until 0. intros Hbat Hrel Hin.
  apply is_un_predless_rep_pred_l_is_in.
    rewrite preds_in_list_closed_allFO.
    simpl in *.
    rewrite is_in_pred_l_app_if.
    rewrite (is_in_pred_l_app_2l _ _ _ Hin).
    rewrite preds_in_newnew_pre.
    apply (is_in_pred_l_trans _  (preds_in (ST phi2 (Var xn)))).
      apply something3.
  
      apply is_in_pred_l_app_2r. apply is_in_pred_l_refl. 

  apply is_un_predless_l_calc_lP.
  rewrite length_calc_lP. reflexivity.
Qed.

Lemma is_un_predless_corresp_atm_sSahlq : forall xn phi1 phi2 y lx batm,
    BAT batm = true ->
    is_in_pred_l (preds_in batm) (preds_in (ST phi1 (Var xn))) = true ->
  is_unary_predless ((replace_pred_l (list_closed_allFO (implSO batm
    (newnew_pre (instant_cons_empty' batm (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' batm (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO batm (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' batm (ST phi2 (Var xn)))) (Var xn)))))) lx)
    (preds_in (ST (mimpl phi1 phi2) (Var xn))) (list_Var (length (preds_in (ST (mimpl phi1 phi2) (Var xn)))) y)
    (calc_lP batm (preds_in (ST (mimpl phi1 phi2) (Var xn)))))) = true.
Proof.
Admitted.

Lemma sSahlq_full_SO : forall xn phi1 phi2 (lllv : (list (list (list FOvariable))))
  ( llx1 : list (list FOvariable)),
  sSahlq_ante phi1 = true ->
  uniform_pos phi2  ->
  ~ Var xn = Var 0 ->
  existsT (alpha : SecOrder),
is_unary_predless alpha = true /\
forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir alpha <->
  SOturnst W Iv Ip Ir (uni_closed_SO (allFO (Var xn) (ST (mimpl phi1 phi2) (Var xn)))).
Proof.
  intros xn phi1 phi2 lllv llx1 H1 H2 Hnot.
  destruct (sSahlq_full_SO_pre xn phi1 phi2  H1 H2 Hnot) as  [lx [batm [Hat [[rel [Hrel [Hin SOt]]]| [Hin SOt] ]]]].  
  exists ((allFO (Var xn) (replace_pred_l (list_closed_allFO (implSO
    (conjSO rel batm)
    (newnew_pre (instant_cons_empty' (conjSO rel batm) (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel batm) (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel batm) (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel batm) (ST phi2 (Var xn)))) (Var xn)))))) lx)
    (preds_in (ST (mimpl phi1 phi2) (Var xn))) (list_Var (length (preds_in (ST (mimpl phi1 phi2) (Var xn)))) (Var (new_FOv_pp_pre2 batm)))
    (calc_lP batm (preds_in (allFO (Var xn) (ST (mimpl phi1 phi2) (Var xn)))))))).
    apply conj. apply is_un_predless_corresp_sSahlq. all : try assumption.

  exists ((allFO (Var xn) (replace_pred_l (list_closed_allFO (implSO batm
    (newnew_pre (instant_cons_empty' batm (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' batm (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO batm (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' batm (ST phi2 (Var xn)))) (Var xn)))))) lx)
    (preds_in (ST (mimpl phi1 phi2) (Var xn))) (list_Var (length (preds_in (ST (mimpl phi1 phi2) (Var xn)))) (Var (new_FOv_pp_pre2 batm)))
    (calc_lP batm (preds_in (allFO (Var xn) (ST (mimpl phi1 phi2) (Var xn)))))))).
    apply conj. apply is_un_predless_corresp_atm_sSahlq. all : try assumption.
Defined.

Lemma sSahlq_full_Modal : forall phi1 phi2 (lllv : (list (list (list FOvariable))))
  ( llx1 : list (list FOvariable)),
  sSahlq_ante phi1 = true ->
  uniform_pos phi2  ->
  existsT (alpha : SecOrder),
is_unary_predless alpha = true /\
forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir alpha <->
  mturnst_frame W Ir (mimpl phi1 phi2).
Proof.
  intros phi1 phi2 lllv llx1 H1 H2.
  destruct (sSahlq_full_SO 1 phi1 phi2 lllv llx1 H1 H2) as [alpha [Hun SOt]].
  discriminate.
  exists alpha. apply conj. assumption.
  intros. split; intros HH.
    apply (correctness_ST _ _ (Var 1) Iv Ip).
    apply SOt. assumption.

    apply SOt.
    apply (correctness_ST _ _ (Var 1) Iv Ip).
    assumption.
Defined.

(*
 Locate correctness_ST_world       .
Locate same_struc_rename_FOv_A_pre .
Locate no_SOquant_rep_pred_l .  
 *)
(*Print All Dependencies vsSahlq_full_Modal. *)