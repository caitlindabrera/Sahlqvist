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
Require Import sSahlq3_5_plus_3.


Lemma same_struc_conjSO_ex_AA : forall gamma alpha beta,
  same_struc gamma (conjSO alpha beta) = true ->
  existsT2 alpha' beta',
    gamma = conjSO alpha' beta' /\
    (is_BOXATM_flag_strong_CONJ gamma = true <->
    is_BOXATM_flag_strong_CONJ (conjSO alpha' beta') = true).
Proof.
  induction gamma; intros alpha beta H;
    try (simpl in *; discriminate).
    exists gamma1. exists gamma2. apply conj. reflexivity.
    apply iff_refl.
Defined.

Lemma same_struc_conjSO_ex_BAT2 : forall gamma alpha beta,
  same_struc_BAT2 gamma (conjSO alpha beta) = true ->
  existsT2 alpha' beta',
    gamma = conjSO alpha' beta' /\
    (BAT gamma = true <->
    BAT (conjSO alpha' beta') = true).
Proof.
  induction gamma; intros alpha beta H;
    pose proof (same_struc__BAT2 _ _ H);
    try (simpl in *; discriminate).
    exists gamma1. exists gamma2. apply conj. reflexivity.
    apply iff_refl.
Defined.

Lemma same_struc_BAT2_refl : forall alpha,
  same_struc_BAT2 alpha alpha = true.
Proof.
  intros alpha. apply same_struc_BAT2_defn.
  apply conj. apply same_struc_refl.
  apply iff_refl.
Qed.

Lemma same_struc_BAT2_trans : forall alpha beta gamma,
  same_struc_BAT2 alpha beta = true ->
  same_struc_BAT2 beta gamma = true ->
  same_struc_BAT2 alpha gamma = true.
Proof.
  intros alpha beta gamma H1 H2.
  unfold same_struc_BAT2 in *.
  apply andb_true_iff in H1.
  apply andb_true_iff in H2.
  apply andb_true_iff.
  destruct H1 as [H1a H1b].
  destruct H2 as [H2a H2b].
  apply conj.
    apply (same_struc_trans _ _ _ H1a H2a).

    apply andb_true_iff.
    apply andb_true_iff in H1b.
    apply andb_true_iff in H2b.
    destruct H1b as [H1b1 H1b2].
    destruct H2b as [H2b1 H2b2].
    case_eq (batm_paired alpha); intros H1; rewrite H1 in *.
      case_eq (batm_paired gamma); intros H2; rewrite H2 in *.
        apply conj; reflexivity.

        case_eq (batm_paired beta); intros H3; rewrite H3 in *; discriminate.

      apply conj. reflexivity.
      case_eq (batm_paired gamma); intros H2; rewrite H2 in*.
        rewrite H2b2 in *. discriminate. reflexivity.
Qed.



(* Lemma same_struc_BAT2_rename_FOv_allFO : forall alpha z xn ym,
same_struc_BAT2 alpha (rename_FOv alpha (Var xn) (Var ym)) = true ->
same_struc_BAT2 (allFO z alpha) (rename_FOv (allFO z alpha) (Var xn) (Var ym)) = true.
Proof.
  intros alpha [zn] xn ym H.
  apply andb_true_iff in H.
  apply andb_true_iff.
  destruct H as [H1 H2].
  apply conj.
    simpl in H1.
    simpl. case_eq (beq_nat zn xn); intros Hbeq2;
      assumption.

    apply andb_true_iff.
    apply andb_true_iff in H2.
    destruct H2 as [H3 H4].
    apply conj.
      case_eq (batm_paired (allFO (Var zn) alpha)); intros H.
        2 : reflexivity.

Lemma batm_paired_rename_FOv : forall alpha z x y,
  batm_paired (allFO z alpha) = true ->
  batm_paired (rename_FOv (allFO z alpha) x y) = true.
      destruct alpha; try reflexivity.
      destruct alpha; try discriminate.
      simpl.

      simpl. case_eq (beq_nat zn xn); intros Hbeq.
      simpl batm_paired. destruct alpha.

  unfold same_struc_BAT2.
  apply
  simpl rename_FOv.
  case_eq (beq_nat zn xn); intros Hbeq.
    
 *)

(* Left it here. Try these then keep going. !! 
Want to get the defn of  batm_paired correct *)
(* Lemma batm_comp_x1_rename_FOv_t_no : forall alpha x y,
  ~ x = (Var 1) ->
  batm_comp_x1 alpha = x ->
(batm_comp_x1 (rename_FOv alpha x y) = y).
Proof.
  induction alpha; intros [xn] [ym] Hnot H; try discriminate;
    try (    simpl in H; symmetry in H; contradiction (Hnot H)).

    simpl in *. destruct f as [zn]. inversion H as [H']. 
    rewrite <- beq_nat_refl. simpl. reflexivity.

    simpl in H. destruct alpha; try discriminate;
    try (simpl in H; symmetry in H; contradiction (Hnot H)).
    destruct alpha1; 
    try (simpl in H; symmetry in H; contradiction (Hnot H)).
    simpl. destruct f as [z1]. case_eq (beq_nat z1 xn);
      intros Hbeq. destruct f0 as [z2]. destruct f1 as [z3].
      inversion H as [H']. rewrite <- beq_nat_refl.
      case_eq (beq_nat xn z3); intros Hbeq2; reflexivity.

      destruct f0 as [z2]. destruct f1 as [z3].
      inversion H as [H']. rewrite <- beq_nat_refl.
      case_eq (beq_nat xn z3); intros Hbeq2;
         reflexivity.
Qed. *)

Lemma batm_comp_x1_rename_FOv_t : forall alpha x y,
  ~ x = (Var 0) ->
  batm_comp_x1 alpha = x ->
(batm_comp_x1 (rename_FOv alpha x y) = y).
Proof.
  induction alpha; intros [xn] [ym] Hnot H; try discriminate;
    try (    simpl in H; symmetry in H; contradiction (Hnot H)).

    simpl in *. destruct f as [zn]. inversion H as [H']. 
    rewrite <- beq_nat_refl. simpl. reflexivity.

    simpl in H. destruct alpha; try discriminate;
    try (simpl in H; symmetry in H; contradiction (Hnot H)).
    destruct alpha1; 
    try (simpl in H; symmetry in H; contradiction (Hnot H)).
    simpl. destruct f as [z1]. case_eq (beq_nat z1 xn);
      intros Hbeq. destruct f0 as [z2]. destruct f1 as [z3].
      inversion H as [H']. rewrite <- beq_nat_refl.
      case_eq (beq_nat xn z3); intros Hbeq2; reflexivity.

      destruct f0 as [z2]. destruct f1 as [z3].
      inversion H as [H']. rewrite <- beq_nat_refl.
      case_eq (beq_nat xn z3); intros Hbeq2;
         reflexivity.
Qed.

Lemma batm_comp_x1_rename_FOv_f : forall alpha x y z,
~ x = z ->
  batm_comp_x1 alpha = z ->
(batm_comp_x1 (rename_FOv alpha x y) = z).
Proof.
  induction alpha; intros [xn] [ym] [zn] Hnot H; try assumption.
    simpl in *. rewrite H. 
    rewrite FOvar_neq. simpl. reflexivity. assumption.

    simpl in *. destruct f as [z1]. destruct f0 as [z2].
    case_eq (beq_nat xn z1); intros Hbeq; case_eq (beq_nat xn z2);
      intros HBeq2; assumption.

    simpl in *. destruct f as [z1]. destruct f0 as [z2].
    case_eq (beq_nat xn z1); intros Hbeq; case_eq (beq_nat xn z2);
      intros HBeq2; assumption.

    destruct f as [z1].
    destruct alpha;
      try (simpl in *; case_eq (beq_nat z1 xn); intros Hbeq; assumption).

      simpl in *. case_eq (beq_nat z1 xn); intros Hbeq;
        destruct f as [z2]; case_eq (beq_nat xn z2); intros Hbeq2;
          assumption.

      simpl in *. case_eq (beq_nat z1 xn); intros Hbeq;
        destruct f as [z2]; case_eq (beq_nat xn z2); intros Hbeq2;
          destruct f0 as [z3]; case_eq (beq_nat xn z3); intros Hbeq3;
          assumption.

      simpl in *. case_eq (beq_nat z1 xn); intros Hbeq;
        destruct f as [z2]; case_eq (beq_nat xn z2); intros Hbeq2;
          destruct f0 as [z3]; case_eq (beq_nat xn z3); intros Hbeq3;
          assumption.

      simpl in *. case_eq (beq_nat z1 xn); intros Hbeq;
        destruct f as [z2]; case_eq (beq_nat z2 xn); intros Hbeq2;
          assumption.

      simpl in *. case_eq (beq_nat z1 xn); intros Hbeq;
        destruct f as [z2]; case_eq (beq_nat z2 xn); intros Hbeq2;
          assumption.

      simpl. case_eq (beq_nat z1 xn); intros Hbeq.
        destruct alpha1; try assumption.
          simpl in *. destruct f as [z2]. case_eq (beq_nat xn z2);
            intros Hbeq2; assumption.

          simpl in *. destruct f as [u1]; destruct f0 as [u2].
          case_eq (beq_nat xn u1); intros Hbeq2.
            rewrite (beq_nat_true _ _ Hbeq2) in *. contradiction (Hnot H).
          case_eq (beq_nat xn u2); intros Hbeq3; assumption.

          simpl in *. destruct f as [u1]; destruct f0 as [u2].
          case_eq (beq_nat xn u1); intros Hbeq2;
          case_eq (beq_nat xn u2); intros; assumption.

          simpl in *. destruct f as [z2]. case_eq (beq_nat z2 xn);
            intros Hbeq2; assumption.

          simpl in *. destruct f as [z2]. case_eq (beq_nat z2 xn);
            intros Hbeq2; assumption.

          destruct alpha1; try assumption. simpl in *. destruct f as [z2].
            case_eq (beq_nat xn z2); intros Hbeq2; assumption.

            destruct f as [u1]; destruct f0 as [u2].
            simpl in *. case_eq (beq_nat xn u1);
              intros Hbeq2. rewrite (beq_nat_true _ _ Hbeq2) in *.
              contradiction (Hnot H).
              case_eq (beq_nat xn u2); intros Hbeq3; assumption.

              simpl in *. destruct f as [u1]; destruct f0 as [z2].  
              case_eq (beq_nat xn u1); intros Hbeq2;
              case_eq (beq_nat xn z2); intros Hbeq3; assumption.

              simpl in *. destruct f as [u1];
              case_eq (beq_nat u1 xn); intros Hbeq2;  assumption.

              simpl in *. destruct f as [u1];
              case_eq (beq_nat u1 xn); intros Hbeq2;  assumption.

    simpl in *. destruct f as [z1].
    case_eq (beq_nat z1 xn); intros Hbeq; assumption.
Qed.

(* Fixpoint batm_paired_deg (alpha : SecOrder) : bool :=
  match alpha with
  | allFO y (implSO (relatSO z1 z2) beta) => false
  | conjSO beta1 beta2 => false
  | exFO _ beta => batm_paired_deg beta
  | negSO beta => batm_paired_deg beta
  | disjSO beta1 beta2 =>
    if batm_paired_deg beta1 then batm_paired beta2_deg
    else true
  | implSO beta1 beta2 =>
    if batm_paired_deg beta1 then batm_paired_deg beta2
    else true
  | allSO P beta => batm_paired beta
  | exSO P beta => batm_paired beta
  | _ => true
  end.
 *)
Fixpoint batm_paired_deg alpha : bool :=
  match alpha with
  | allFO _ (implSO (relatSO _ _ ) _) => false 
  | allFO _ _ => true 
  | conjSO _ _ => false
  | _ => true
  end.

(* Lemma same_struc_old_deg : forall alpha beta,
  same_struc alpha beta = true ->
  batm_paired_old_deg alpha = true -> 
  batm_paired_old_deg beta = true.
Proof.
  induction alpha; intros beta Hs Hb; try discriminate;
    destruct beta; try discriminate; try reflexivity.
    simpl in *. destruct beta; try discriminate; try reflexivity.
    destruct beta1; try discriminate; try reflexivity.
    destruct alpha; try discriminate.
    destruct alpha1; try discriminate.
Qed. *)

(* Lemma batm_paired_rename_FOv_fwd_allFO : forall alpha f x y,
 (forall x y,  batm_paired_old alpha = true -> batm_paired_old (rename_FOv alpha x y) = true) ->
  batm_paired_old (allFO f alpha) = true ->
batm_paired_old (rename_FOv (allFO f alpha) x y ) = true.
Proof.
  intros alpha [zn] [xn] [ym] IH H.
  case_eq (batm_paired_old_deg (allFO (Var zn) alpha)); intros Hd.
(*     simpl rename_FOv. case_eq (beq_nat zn xn); intros Hbeq. *)
    apply (same_struc_old_deg _ (rename_FOv (allFO (Var zn) alpha) (Var xn) (Var ym))) in Hd.
    apply batm_paired_old__deg in Hd. assumption.
    apply same_struc_rename_FOv.

    destruct alpha; try discriminate.
    destruct alpha1; try discriminate.
(*     destruct f as [z1]; destruct f0 as [z2]. *)
      simpl.
      case_eq (beq_nat zn xn); intros Hbeq. simpl in *.
 destruct f as [u1]; destruct f0 as [u2].
      case_eq (beq_nat xn u1); intros Hbeq2.
        case_eq (beq_nat xn u2); intros Hbeq3. 
          rewrite <- beq_nat_refl.
          simpl in H. rewrite (beq_nat_true _ _ Hbeq) in *.
          rewrite Hbeq3 in *.
          case_eq (batm_comp_x1 alpha2 ); intros rn Hrn.
          rewrite Hrn in H.
          specialize (IH (Var xn) (Var ym)).
          simpl in IH.
(*           rewrite Hbeq2 in *. rewrite Hbeq3 in *. simpl in IH. *)
          case_eq (PeanoNat.Nat.eqb u2 rn); intros Hbeq4; rewrite Hbeq4 in *.
            2 : discriminate.
          case_eq (batm_comp_x1 (rename_FOv_n alpha2 xn ym)); intros r2 Hr2.  
          case_eq (beq_nat ym r2); intros Hbeq5. apply IH. assumption. assumption.
          case_eq (beq_nat xn rn); intros Hbeq6.
            rewrite <- (beq_nat_true _ _ Hbeq6) in Hrn.
            pose proof (batm_comp_x1_rename_FOv_t alpha2 _ (Var ym) Hnot Hrn) as H0.
            unfold rename_FOv in H0. rewrite H0 in Hr2. inversion Hr2 as [HHH].
            rewrite HHH in *. rewrite <- beq_nat_refl in *. discriminate.

            pose proof (batm_comp_x1_rename_FOv_f alpha2 (Var xn) (Var ym) (Var rn)) as H0.
            unfold rename_FOv in H0. rewrite H0 in Hr2. inversion Hr2 as [HHH].
            rewrite HHH in *.
            rewrite (beq_nat_true _ _ Hbeq3) in *. rewrite <- (beq_nat_true _ _ Hbeq3) in *.
            rewrite Hbeq4 in *. discriminate.
              intros HH. inversion HH as [HHH]. rewrite HHH in *.
              rewrite <- beq_nat_refl in Hbeq6. discriminate.


              assumption.

    simpl in *. case_eq (beq_nat zn xn); intros Hbeq.
      case_eq (beq_nat xn z1); intros Hbeq2.
        case_eq (beq_nat xn z2); intros Hbeq3.
          simpl in *. rewrite <- beq_nat_refl.
          rewrite (beq_nat_true _ _ Hbeq3) in *. rewrite Hbeq in *.
          case_eq (batm_comp_x1 alpha2); intros r1 Hr1; rewrite Hr1 in *.
          case_eq (batm_comp_x1 (rename_FOv_n alpha2 z2 ym)); intros r2 Hr2.
pose proof batm_comp_x1_rename_FOv_t as H0.
          case_eq (beq_nat z2 r1); intros Hbeq4; rewrite Hbeq4 in *. 2 : discriminate.
          rewrite (beq_nat_true _ _ Hbeq4) in *.
          unfold rename_FOv in H0. specialize (H0 alpha2 (Var r1) (Var ym)).
          simpl in H0. rewrite H0 in Hr2. inversion Hr2. rewrite <- beq_nat_refl.
          rewrite (beq_nat_true _ _ Hbeq2) in *.
          specialize (IH (Var xn) (Var ym)). simpl in IH.
          apply IH.
          simpl in IH.
          
Search batm_paired batm_comp_x1.

admit.
 *)    

Lemma batm_paired_rename_FOv_fwd_allFO : forall alpha f x y,
  ~ x = (Var 0) ->
 (forall x y,  ~ x = (Var 0) -> batm_paired alpha = true -> batm_paired (rename_FOv alpha x y) = true) ->
  batm_paired (allFO f alpha) = true ->
batm_paired (rename_FOv (allFO f alpha) x y ) = true.
Proof.
  induction alpha; intros [zn] [xn] [ym] Hnot IH H; try reflexivity.
    simpl in *. destruct f as [un].
    case_eq (beq_nat zn xn); intros Hbeq;
      case_eq (beq_nat xn un); intros Hbeq2; reflexivity.

    destruct f as [u1] ;destruct f0 as [u2].
    simpl in *. case_eq (beq_nat zn xn); intros Hbeq;
      case_eq (beq_nat xn u1); intros Hbeq1;
        case_eq (beq_nat xn u2); intros Hbeq2;
          reflexivity.

    destruct f as [u1] ;destruct f0 as [u2].
    simpl in *. case_eq (beq_nat zn xn); intros Hbeq;
      case_eq (beq_nat xn u1); intros Hbeq1;
        case_eq (beq_nat xn u2); intros Hbeq2;
          reflexivity.

    destruct f as [un]. simpl. case_eq (beq_nat zn xn);
      intros Hbeq;
      case_eq (beq_nat un xn); intros Hbeq2; reflexivity.

    destruct f as [un]. simpl. case_eq (beq_nat zn xn);
      intros Hbeq;
      case_eq (beq_nat un xn); intros Hbeq2; reflexivity.

    simpl. case_eq (beq_nat zn xn) ;intros Hbeq;
      reflexivity.

    simpl. case_eq (beq_nat zn xn); intros Hbeq;
      reflexivity.

    simpl. case_eq (beq_nat zn xn); intros Hbeq;
      reflexivity.

(* ----*)

    simpl rename_FOv. case_eq (beq_nat zn xn); intros Hbeq.
    destruct alpha1; try reflexivity.
      simpl. destruct f as [un]. case_eq (beq_nat xn un);
        intros Hbeq2; reflexivity.

      simpl. destruct f as [u1]; destruct f0 as [u2].
      case_eq (beq_nat xn u1); intros Hbeq2.
        case_eq (beq_nat xn u2); intros Hbeq3.
          rewrite <- beq_nat_refl.
          simpl in H. rewrite (beq_nat_true _ _ Hbeq) in *.
          rewrite Hbeq3 in *.
          case_eq (batm_comp_x1 alpha2 ); intros rn Hrn.
          rewrite Hrn in H.
          specialize (IH (Var xn) (Var ym)).
          simpl in IH.
          rewrite Hbeq2 in *. rewrite Hbeq3 in *. simpl in IH.
          case_eq (PeanoNat.Nat.eqb u2 rn); intros Hbeq4; rewrite Hbeq4 in *.
            2 : discriminate.
          case_eq (batm_comp_x1 (rename_FOv_n alpha2 xn ym)); intros r2 Hr2.  
          case_eq (beq_nat ym r2); intros Hbeq5. apply IH. assumption. assumption.
          case_eq (beq_nat xn rn); intros Hbeq6.
            rewrite <- (beq_nat_true _ _ Hbeq6) in Hrn.
            pose proof (batm_comp_x1_rename_FOv_t alpha2 _ (Var ym) Hnot Hrn) as H0.
            unfold rename_FOv in H0. rewrite H0 in Hr2. inversion Hr2 as [HHH].
            rewrite HHH in *. rewrite <- beq_nat_refl in *. discriminate.

            pose proof (batm_comp_x1_rename_FOv_f alpha2 (Var xn) (Var ym) (Var rn)) as H0.
            unfold rename_FOv in H0. rewrite H0 in Hr2. inversion Hr2 as [HHH].
            rewrite HHH in *.
            rewrite (beq_nat_true _ _ Hbeq3) in *. rewrite <- (beq_nat_true _ _ Hbeq3) in *.
            rewrite Hbeq4 in *. discriminate.
              intros HH. inversion HH as [HHH]. rewrite HHH in *.
              rewrite <- beq_nat_refl in Hbeq6. discriminate.


              assumption.

 simpl in IH.
              unfold rename_FOv in IH. specialize (IH (Var xn) (Var ym)).
              simpl in IH. rewrite Hbeq2 in *. rewrite Hbeq3 in *. simpl in IH.

          case_eq (beq_nat ym u2); intros Hbeq4.
            case_eq (batm_comp_x1 (rename_FOv_n alpha2 xn ym)); intros un Hun.
            case_eq (beq_nat u2 un); intros Hbeq5.
              apply IH. assumption.
              simpl in H. rewrite (beq_nat_true _ _ Hbeq) in H.
              rewrite Hbeq3 in H. discriminate.

              simpl in H. rewrite (beq_nat_true _ _ Hbeq) in H.
              rewrite Hbeq3 in H. discriminate.

              simpl in H. rewrite (beq_nat_true _ _ Hbeq) in H.
              rewrite Hbeq3 in H. discriminate.

 simpl in IH.
              unfold rename_FOv in IH. specialize (IH (Var xn) (Var ym)).
              simpl in IH. rewrite Hbeq2 in *.

          case_eq (beq_nat xn u2); intros Hbeq3.
            rewrite <- beq_nat_refl.
            simpl in *. rewrite Hbeq3 in *.
            rewrite (beq_nat_true _ _ Hbeq) in *.
            rewrite Hbeq3 in *.
            case_eq (batm_comp_x1 alpha2); intros rn Hrn.
            case_eq (batm_comp_x1 (rename_FOv_n alpha2 xn ym)); intros r2 Hr2.
            rewrite Hrn in *.
            case_eq (PeanoNat.Nat.eqb u2 rn); intros Hbeq4; rewrite Hbeq4 in *.
              2 : discriminate.
          case_eq (beq_nat ym r2); intros Hbeq5. apply IH. assumption. assumption.
          case_eq (beq_nat xn rn); intros Hbeq6.
            rewrite <- (beq_nat_true _ _ Hbeq6) in Hrn.
            pose proof (batm_comp_x1_rename_FOv_t alpha2 _ (Var ym) Hnot  Hrn) as H0.
            unfold rename_FOv in H0. rewrite H0 in Hr2. inversion Hr2 as [HHH].
            rewrite HHH in *. rewrite <- beq_nat_refl in *. discriminate.

            pose proof (batm_comp_x1_rename_FOv_f alpha2 (Var xn) (Var ym) (Var rn)) as H0.
            unfold rename_FOv in H0. rewrite H0 in Hr2. inversion Hr2 as [HHH].
            rewrite HHH in *.
            rewrite (beq_nat_true _ _ Hbeq3) in *. rewrite <- (beq_nat_true _ _ Hbeq3) in *.
            rewrite Hbeq4 in *. discriminate.
              intros HH. inversion HH as [HHH]. rewrite HHH in *.
              rewrite <- beq_nat_refl in Hbeq6. discriminate.

              assumption.

            rewrite Hbeq3 in *. simpl in *.
            rewrite (beq_nat_true _ _ Hbeq) in *.
            rewrite Hbeq3 in *. discriminate.


        destruct f as [u1]; destruct f0 as [u2].
        simpl. case_eq (beq_nat xn u1); intros Hbeq2;
          case_eq (beq_nat xn u2); intros Hbeq3;
            reflexivity.

        simpl. destruct f as [un]. simpl.
        case_eq (beq_nat un xn); intros Hbeq2; reflexivity.

        simpl. destruct f as [un]. simpl.
        case_eq (beq_nat un xn); intros Hbeq2; reflexivity.
(* ---- *)

   destruct alpha1; try reflexivity.
      simpl. destruct f as [un]. case_eq (beq_nat xn un);
        intros Hbeq2; reflexivity.

      simpl. destruct f as [u1]; destruct f0 as [u2].
      case_eq (beq_nat xn u1); intros Hbeq2.
        case_eq (beq_nat xn u2); intros Hbeq3.
          case_eq (beq_nat zn ym); intros Hbeq0.
          simpl in H. rewrite (beq_nat_true _ _ Hbeq3) in *.
          rewrite Hbeq in *. discriminate.

          simpl in H. case_eq (beq_nat zn u2); intros Hbeq4;
            rewrite Hbeq4 in *. 2 : discriminate.
          rewrite (beq_nat_true _ _ Hbeq4) in *. rewrite beq_nat_comm in Hbeq.      
          rewrite Hbeq in *. discriminate.

          simpl in H.
          case_eq (beq_nat zn u2); intros Hbeq4; rewrite Hbeq4 in *.
            2 : discriminate.
          case_eq (batm_comp_x1 alpha2 ); intros rn Hrn.
          rewrite Hrn in H.
          case_eq (PeanoNat.Nat.eqb u2 rn); intros Hbeq5; rewrite Hbeq5 in *.
            2 :discriminate.
          case_eq (batm_comp_x1 (rename_FOv alpha2 (Var xn) (Var ym)));
            intros r2 Hr2. unfold rename_FOv in Hr2. rewrite Hr2.
unfold rename_FOv in IH.
            specialize (IH (Var xn) (Var ym)). simpl in IH. 
            rewrite Hbeq3 in *. rewrite Hbeq2 in *. simpl in IH.
          case_eq (beq_nat u2 r2); intros Hbeq7. 
            apply IH. assumption. assumption.
          case_eq (beq_nat xn rn); intros Hbeq6.
            rewrite <- (beq_nat_true _ _ Hbeq6) in Hrn.
            pose proof (batm_comp_x1_rename_FOv_t alpha2 _ (Var ym) Hnot Hrn) as H0.
            unfold rename_FOv in H0. rewrite H0 in Hr2. inversion Hr2 as [HHH].
            rewrite HHH in *.
            rewrite (beq_nat_true _ _ Hbeq6) in *.
            rewrite (beq_nat_true _ _ Hbeq4) in *.
            rewrite beq_nat_comm in Hbeq5. rewrite Hbeq5 in *. discriminate.

            pose proof (batm_comp_x1_rename_FOv_f alpha2 (Var xn) (Var ym) (Var rn)) as H0.
            unfold rename_FOv in H0.
            rewrite H0 in Hr2. inversion Hr2 as [Hr2']. rewrite Hr2' in *. 
            rewrite Hbeq7 in *. discriminate.

            intros HH. inversion HH as [HHH]. rewrite HHH in *.
            rewrite <- beq_nat_refl in Hbeq6. discriminate.

            assumption.

          case_eq (beq_nat xn u2); intros Hbeq3.
(*             case_eq (beq_nat zn ym); intros Hbeq4; *)
              simpl in H. rewrite <- (beq_nat_true _ _ Hbeq3) in H.
              rewrite Hbeq in H. discriminate.

          simpl in H.
          case_eq (beq_nat zn u2); intros Hbeq4; rewrite Hbeq4 in *.
            2 : discriminate.

          case_eq (batm_comp_x1 alpha2 ); intros rn Hrn.
          rewrite Hrn in H.
          case_eq (PeanoNat.Nat.eqb u2 rn); intros Hbeq5; rewrite Hbeq5 in *.
            2 :discriminate.
          case_eq (batm_comp_x1 (rename_FOv alpha2 (Var xn) (Var ym)));
            intros r2 Hr2. unfold rename_FOv in Hr2. rewrite Hr2.
unfold rename_FOv in IH.
            specialize (IH (Var xn) (Var ym)). simpl in IH. 
            rewrite Hbeq3 in *. rewrite Hbeq2 in *. simpl in IH.
          case_eq (beq_nat u2 r2); intros Hbeq7. 
            apply IH. assumption. assumption.
          case_eq (beq_nat xn rn); intros Hbeq6.
            rewrite <- (beq_nat_true _ _ Hbeq6) in Hrn.
            pose proof (batm_comp_x1_rename_FOv_t alpha2 _ (Var ym) Hnot Hrn) as H0.
            unfold rename_FOv in H0. rewrite H0 in Hr2. inversion Hr2 as [HHH].
            rewrite HHH in *.
            rewrite (beq_nat_true _ _ Hbeq6) in *.
            rewrite (beq_nat_true _ _ Hbeq4) in *.
            rewrite beq_nat_comm in Hbeq5. rewrite Hbeq5 in *. discriminate.

            pose proof (batm_comp_x1_rename_FOv_f alpha2 (Var xn) (Var ym) (Var rn)) as H0.
            unfold rename_FOv in H0.
            rewrite H0 in Hr2. inversion Hr2 as [Hr2']. rewrite Hr2' in *. 
            rewrite Hbeq7 in *. discriminate.

            intros HH. inversion HH as [HHH]. rewrite HHH in *.
            rewrite <- beq_nat_refl in Hbeq6. discriminate.

            assumption.
(* 
  rewrite <- beq_nat_refl in *. discriminate.
            

          specialize (IH (Var xn) (Var ym)).
          simpl in IH.
          rewrite Hbeq2 in *. rewrite Hbeq3 in *. simpl in IH.
          case_eq (PeanoNat.Nat.eqb u2 rn); intros Hbeq4; rewrite Hbeq4 in *.
            2 : discriminate.
          case_eq (batm_comp_x1 (rename_FOv_n alpha2 xn ym)); intros r2 Hr2.  
          case_eq (beq_nat ym r2); intros Hbeq5. apply IH. assumption.
          case_eq (beq_nat xn rn); intros Hbeq6.
            rewrite <- (beq_nat_true _ _ Hbeq6) in Hrn.
            pose proof (batm_comp_x1_rename_FOv_t alpha2 _ (Var ym) Hrn) as H0.
            unfold rename_FOv in H0. rewrite H0 in Hr2. inversion Hr2 as [HHH].
            rewrite HHH in *. rewrite <- beq_nat_refl in *. discriminate.

            pose proof (batm_comp_x1_rename_FOv_f alpha2 (Var xn) (Var ym) (Var rn)) as H0.
            unfold rename_FOv in H0. rewrite H0 in Hr2. inversion Hr2 as [HHH].
            rewrite HHH in *.
            rewrite (beq_nat_true _ _ Hbeq3) in *. rewrite <- (beq_nat_true _ _ Hbeq3) in *.
            rewrite Hbeq4 in *. discriminate.
              intros HH. inversion HH as [HHH]. rewrite HHH in *.
              rewrite <- beq_nat_refl in Hbeq6. discriminate.


              assumption.

 simpl in IH.
              unfold rename_FOv in IH. specialize (IH (Var xn) (Var ym)).
              simpl in IH. rewrite Hbeq2 in *. rewrite Hbeq3 in *. simpl in IH.
 *)
(*           case_eq (beq_nat ym u2); intros Hbeq4.
            case_eq (batm_comp_x1 (rename_FOv_n alpha2 xn ym)); intros un Hun.
            case_eq (beq_nat u2 un); intros Hbeq5.
              apply IH.
              simpl in H. rewrite (beq_nat_true _ _ Hbeq) in H.
              rewrite Hbeq3 in H. discriminate.

              simpl in H. rewrite (beq_nat_true _ _ Hbeq) in H.
              rewrite Hbeq3 in H. discriminate.

              simpl in H. rewrite (beq_nat_true _ _ Hbeq) in H.
              rewrite Hbeq3 in H. discriminate.

 simpl in IH.
              unfold rename_FOv in IH. specialize (IH (Var xn) (Var ym)).
              simpl in IH. rewrite Hbeq2 in *.

          case_eq (beq_nat xn u2); intros Hbeq3.
            rewrite <- beq_nat_refl.
            simpl in *. rewrite Hbeq3 in *.
            rewrite (beq_nat_true _ _ Hbeq) in *.
            rewrite Hbeq3 in *.
            case_eq (batm_comp_x1 alpha2); intros rn Hrn.
            case_eq (batm_comp_x1 (rename_FOv_n alpha2 xn ym)); intros r2 Hr2.
            rewrite Hrn in *.
            case_eq (PeanoNat.Nat.eqb u2 rn); intros Hbeq4; rewrite Hbeq4 in *.
              2 : discriminate.
          case_eq (beq_nat ym r2); intros Hbeq5. apply IH. assumption.
          case_eq (beq_nat xn rn); intros Hbeq6.
            rewrite <- (beq_nat_true _ _ Hbeq6) in Hrn.
            pose proof (batm_comp_x1_rename_FOv_t alpha2 _ (Var ym) Hrn) as H0.
            unfold rename_FOv in H0. rewrite H0 in Hr2. inversion Hr2 as [HHH].
            rewrite HHH in *. rewrite <- beq_nat_refl in *. discriminate.

            pose proof (batm_comp_x1_rename_FOv_f alpha2 (Var xn) (Var ym) (Var rn)) as H0.
            unfold rename_FOv in H0. rewrite H0 in Hr2. inversion Hr2 as [HHH].
            rewrite HHH in *.
            rewrite (beq_nat_true _ _ Hbeq3) in *. rewrite <- (beq_nat_true _ _ Hbeq3) in *.
            rewrite Hbeq4 in *. discriminate.
              intros HH. inversion HH as [HHH]. rewrite HHH in *.
              rewrite <- beq_nat_refl in Hbeq6. discriminate.

              assumption.

            rewrite Hbeq3 in *. simpl in *.
            rewrite (beq_nat_true _ _ Hbeq) in *.
            rewrite Hbeq3 in *. discriminate.

 *)
        destruct f as [u1]; destruct f0 as [u2].
        simpl. case_eq (beq_nat xn u1); intros Hbeq2;
          case_eq (beq_nat xn u2); intros Hbeq3;
            reflexivity.

        simpl. destruct f as [un]. simpl.
        case_eq (beq_nat un xn); intros Hbeq2; reflexivity.

        simpl. destruct f as [un]. simpl.
        case_eq (beq_nat un xn); intros Hbeq2; reflexivity.



            
          

(*  simpl in IH.
              unfold rename_FOv in IH. specialize (IH (Var xn) (Var ym)).
              simpl in IH. rewrite Hbeq2 in *. rewrite Hbeq3 in *. simpl in IH.
              apply IH.
              simpl in H. rewrite (beq_nat_true _ _ Hbeq) in H.
              rewrite Hbeq3 in H. discriminate.

              simpl in *. rewrite
 assumption.
          

 _ _ _ _ Hrn) in Hr2.
  
            rewrite (beq_nat_true _ _ Hbeq) in Hrn.

            pose proof (batm_comp_x1_rename_FOv_or alpha2 (Var xn) (Var ym) (Var rn) Hrn) 
              as [HH | HH].
              simpl in HH. pose proof Hr2 as Hr3.
              rewrite HH in Hr2. inversion Hr2 as [Hr2'].
              rewrite Hr2' in *. 

 in Hr2.



    simpl. case_eq (beq_nat zn xn); intros Hbeq.
      simpl. destruct alpha1.

 *)

    simpl. case_eq (beq_nat zn xn) ;intros Hbeq;
      reflexivity.

    simpl. case_eq (beq_nat zn xn) ;intros Hbeq;
      reflexivity.
Qed.


(* Lemma batm_paired_rename_FOv_fwd_allFO : forall alpha f x y,
  ~ x = (Var 1) ->
 (forall x y,  ~ x = (Var 1) -> batm_paired alpha = true -> batm_paired (rename_FOv alpha x y) = true) ->
  batm_paired (allFO f alpha) = true ->
batm_paired (rename_FOv (allFO f alpha) x y ) = true.
Proof.
Admitted. *)
(*
  induction alpha; intros [zn] [xn] [ym] IH H; try reflexivity.
    simpl in *. destruct f as [un].
    case_eq (beq_nat zn xn); intros Hbeq;
      case_eq (beq_nat xn un); intros Hbeq2; reflexivity.

    destruct f as [u1] ;destruct f0 as [u2].
    simpl in *. case_eq (beq_nat zn xn); intros Hbeq;
      case_eq (beq_nat xn u1); intros Hbeq1;
        case_eq (beq_nat xn u2); intros Hbeq2;
          reflexivity.

    destruct f as [u1] ;destruct f0 as [u2].
    simpl in *. case_eq (beq_nat zn xn); intros Hbeq;
      case_eq (beq_nat xn u1); intros Hbeq1;
        case_eq (beq_nat xn u2); intros Hbeq2;
          reflexivity.

    destruct f as [un]. simpl. case_eq (beq_nat zn xn);
      intros Hbeq;
      case_eq (beq_nat un xn); intros Hbeq2; reflexivity.

    destruct f as [un]. simpl. case_eq (beq_nat zn xn);
      intros Hbeq;
      case_eq (beq_nat un xn); intros Hbeq2; reflexivity.

    simpl. case_eq (beq_nat zn xn) ;intros Hbeq;
      reflexivity.

    simpl. case_eq (beq_nat zn xn); intros Hbeq;
      reflexivity.

    simpl. case_eq (beq_nat zn xn); intros Hbeq;
      reflexivity.

(* ----*)

    simpl rename_FOv. case_eq (beq_nat zn xn); intros Hbeq.
    destruct alpha1; try reflexivity.
      simpl. destruct f as [un]. case_eq (beq_nat xn un);
        intros Hbeq2; reflexivity.

      simpl. destruct f as [u1]; destruct f0 as [u2].
      case_eq (beq_nat xn u1); intros Hbeq2.
        case_eq (beq_nat xn u2); intros Hbeq3.
          rewrite <- beq_nat_refl.
          simpl in H. rewrite (beq_nat_true _ _ Hbeq) in *.
          rewrite Hbeq3 in *.
          case_eq (batm_comp_x1 alpha2 ); intros rn Hrn.
          rewrite Hrn in H.
          specialize (IH (Var xn) (Var ym)).
          simpl in IH.
          rewrite Hbeq2 in *. rewrite Hbeq3 in *. simpl in IH.
          case_eq (PeanoNat.Nat.eqb u2 rn); intros Hbeq4; rewrite Hbeq4 in *.
            2 : discriminate.
          case_eq (batm_comp_x1 (rename_FOv_n alpha2 xn ym)); intros r2 Hr2.  
          case_eq (beq_nat ym r2); intros Hbeq5. apply IH. assumption.
          case_eq (beq_nat xn rn); intros Hbeq6.
            rewrite <- (beq_nat_true _ _ Hbeq6) in Hrn.
            pose proof (batm_comp_x1_rename_FOv_t alpha2 _ (Var ym) _ Hrn) as H0.
            unfold rename_FOv in H0. rewrite H0 in Hr2. inversion Hr2 as [HHH].
            rewrite HHH in *. rewrite <- beq_nat_refl in *. discriminate.

            pose proof (batm_comp_x1_rename_FOv_f alpha2 (Var xn) (Var ym) (Var rn)) as H0.
            unfold rename_FOv in H0. rewrite H0 in Hr2. inversion Hr2 as [HHH].
            rewrite HHH in *.
            rewrite (beq_nat_true _ _ Hbeq3) in *. rewrite <- (beq_nat_true _ _ Hbeq3) in *.
            rewrite Hbeq4 in *. discriminate.
              intros HH. inversion HH as [HHH]. rewrite HHH in *.
              rewrite <- beq_nat_refl in Hbeq6. discriminate.


              assumption.

 simpl in IH.
              unfold rename_FOv in IH. specialize (IH (Var xn) (Var ym)).
              simpl in IH. rewrite Hbeq2 in *. rewrite Hbeq3 in *. simpl in IH.

          case_eq (beq_nat ym u2); intros Hbeq4.
            case_eq (batm_comp_x1 (rename_FOv_n alpha2 xn ym)); intros un Hun.
            case_eq (beq_nat u2 un); intros Hbeq5.
              apply IH.
              simpl in H. rewrite (beq_nat_true _ _ Hbeq) in H.
              rewrite Hbeq3 in H. discriminate.

              simpl in H. rewrite (beq_nat_true _ _ Hbeq) in H.
              rewrite Hbeq3 in H. discriminate.

              simpl in H. rewrite (beq_nat_true _ _ Hbeq) in H.
              rewrite Hbeq3 in H. discriminate.

 simpl in IH.
              unfold rename_FOv in IH. specialize (IH (Var xn) (Var ym)).
              simpl in IH. rewrite Hbeq2 in *.

          case_eq (beq_nat xn u2); intros Hbeq3.
            rewrite <- beq_nat_refl.
            simpl in *. rewrite Hbeq3 in *.
            rewrite (beq_nat_true _ _ Hbeq) in *.
            rewrite Hbeq3 in *.
            case_eq (batm_comp_x1 alpha2); intros rn Hrn.
            case_eq (batm_comp_x1 (rename_FOv_n alpha2 xn ym)); intros r2 Hr2.
            rewrite Hrn in *.
            case_eq (PeanoNat.Nat.eqb u2 rn); intros Hbeq4; rewrite Hbeq4 in *.
              2 : discriminate.
          case_eq (beq_nat ym r2); intros Hbeq5. apply IH. assumption.
          case_eq (beq_nat xn rn); intros Hbeq6.
            rewrite <- (beq_nat_true _ _ Hbeq6) in Hrn.
            pose proof (batm_comp_x1_rename_FOv_t alpha2 _ (Var ym) Hrn) as H0.
            unfold rename_FOv in H0. rewrite H0 in Hr2. inversion Hr2 as [HHH].
            rewrite HHH in *. rewrite <- beq_nat_refl in *. discriminate.

            pose proof (batm_comp_x1_rename_FOv_f alpha2 (Var xn) (Var ym) (Var rn)) as H0.
            unfold rename_FOv in H0. rewrite H0 in Hr2. inversion Hr2 as [HHH].
            rewrite HHH in *.
            rewrite (beq_nat_true _ _ Hbeq3) in *. rewrite <- (beq_nat_true _ _ Hbeq3) in *.
            rewrite Hbeq4 in *. discriminate.
              intros HH. inversion HH as [HHH]. rewrite HHH in *.
              rewrite <- beq_nat_refl in Hbeq6. discriminate.

              assumption.

            rewrite Hbeq3 in *. simpl in *.
            rewrite (beq_nat_true _ _ Hbeq) in *.
            rewrite Hbeq3 in *. discriminate.


        destruct f as [u1]; destruct f0 as [u2].
        simpl. case_eq (beq_nat xn u1); intros Hbeq2;
          case_eq (beq_nat xn u2); intros Hbeq3;
            reflexivity.

        simpl. destruct f as [un]. simpl.
        case_eq (beq_nat un xn); intros Hbeq2; reflexivity.

        simpl. destruct f as [un]. simpl.
        case_eq (beq_nat un xn); intros Hbeq2; reflexivity.
(* ---- *)

   destruct alpha1; try reflexivity.
      simpl. destruct f as [un]. case_eq (beq_nat xn un);
        intros Hbeq2; reflexivity.

      simpl. destruct f as [u1]; destruct f0 as [u2].
      case_eq (beq_nat xn u1); intros Hbeq2.
        case_eq (beq_nat xn u2); intros Hbeq3.
          case_eq (beq_nat zn ym); intros Hbeq0.
          simpl in H. rewrite (beq_nat_true _ _ Hbeq3) in *.
          rewrite Hbeq in *. discriminate.

          simpl in H. case_eq (beq_nat zn u2); intros Hbeq4;
            rewrite Hbeq4 in *. 2 : discriminate.
          rewrite (beq_nat_true _ _ Hbeq4) in *. rewrite beq_nat_comm in Hbeq.      
          rewrite Hbeq in *. discriminate.

          simpl in H.
          case_eq (beq_nat zn u2); intros Hbeq4; rewrite Hbeq4 in *.
            2 : discriminate.
          case_eq (batm_comp_x1 alpha2 ); intros rn Hrn.
          rewrite Hrn in H.
          case_eq (PeanoNat.Nat.eqb u2 rn); intros Hbeq5; rewrite Hbeq5 in *.
            2 :discriminate.
          case_eq (batm_comp_x1 (rename_FOv alpha2 (Var xn) (Var ym)));
            intros r2 Hr2. unfold rename_FOv in Hr2. rewrite Hr2.
unfold rename_FOv in IH.
            specialize (IH (Var xn) (Var ym)). simpl in IH. 
            rewrite Hbeq3 in *. rewrite Hbeq2 in *. simpl in IH.
          case_eq (beq_nat u2 r2); intros Hbeq7. 
            apply IH. assumption.
          case_eq (beq_nat xn rn); intros Hbeq6.
            rewrite <- (beq_nat_true _ _ Hbeq6) in Hrn.
            pose proof (batm_comp_x1_rename_FOv_t alpha2 _ (Var ym) Hrn) as H0.
            unfold rename_FOv in H0. rewrite H0 in Hr2. inversion Hr2 as [HHH].
            rewrite HHH in *.
            rewrite (beq_nat_true _ _ Hbeq6) in *.
            rewrite (beq_nat_true _ _ Hbeq4) in *.
            rewrite beq_nat_comm in Hbeq5. rewrite Hbeq5 in *. discriminate.

            pose proof (batm_comp_x1_rename_FOv_f alpha2 (Var xn) (Var ym) (Var rn)) as H0.
            unfold rename_FOv in H0.
            rewrite H0 in Hr2. inversion Hr2 as [Hr2']. rewrite Hr2' in *. 
            rewrite Hbeq7 in *. discriminate.

            intros HH. inversion HH as [HHH]. rewrite HHH in *.
            rewrite <- beq_nat_refl in Hbeq6. discriminate.

            assumption.

          case_eq (beq_nat xn u2); intros Hbeq3.
(*             case_eq (beq_nat zn ym); intros Hbeq4; *)
              simpl in H. rewrite <- (beq_nat_true _ _ Hbeq3) in H.
              rewrite Hbeq in H. discriminate.

          simpl in H.
          case_eq (beq_nat zn u2); intros Hbeq4; rewrite Hbeq4 in *.
            2 : discriminate.

          case_eq (batm_comp_x1 alpha2 ); intros rn Hrn.
          rewrite Hrn in H.
          case_eq (PeanoNat.Nat.eqb u2 rn); intros Hbeq5; rewrite Hbeq5 in *.
            2 :discriminate.
          case_eq (batm_comp_x1 (rename_FOv alpha2 (Var xn) (Var ym)));
            intros r2 Hr2. unfold rename_FOv in Hr2. rewrite Hr2.
unfold rename_FOv in IH.
            specialize (IH (Var xn) (Var ym)). simpl in IH. 
            rewrite Hbeq3 in *. rewrite Hbeq2 in *. simpl in IH.
          case_eq (beq_nat u2 r2); intros Hbeq7. 
            apply IH. assumption.
          case_eq (beq_nat xn rn); intros Hbeq6.
            rewrite <- (beq_nat_true _ _ Hbeq6) in Hrn.
            pose proof (batm_comp_x1_rename_FOv_t alpha2 _ (Var ym) Hrn) as H0.
            unfold rename_FOv in H0. rewrite H0 in Hr2. inversion Hr2 as [HHH].
            rewrite HHH in *.
            rewrite (beq_nat_true _ _ Hbeq6) in *.
            rewrite (beq_nat_true _ _ Hbeq4) in *.
            rewrite beq_nat_comm in Hbeq5. rewrite Hbeq5 in *. discriminate.

            pose proof (batm_comp_x1_rename_FOv_f alpha2 (Var xn) (Var ym) (Var rn)) as H0.
            unfold rename_FOv in H0.
            rewrite H0 in Hr2. inversion Hr2 as [Hr2']. rewrite Hr2' in *. 
            rewrite Hbeq7 in *. discriminate.

            intros HH. inversion HH as [HHH]. rewrite HHH in *.
            rewrite <- beq_nat_refl in Hbeq6. discriminate.

            assumption.
(* 
  rewrite <- beq_nat_refl in *. discriminate.
            

          specialize (IH (Var xn) (Var ym)).
          simpl in IH.
          rewrite Hbeq2 in *. rewrite Hbeq3 in *. simpl in IH.
          case_eq (PeanoNat.Nat.eqb u2 rn); intros Hbeq4; rewrite Hbeq4 in *.
            2 : discriminate.
          case_eq (batm_comp_x1 (rename_FOv_n alpha2 xn ym)); intros r2 Hr2.  
          case_eq (beq_nat ym r2); intros Hbeq5. apply IH. assumption.
          case_eq (beq_nat xn rn); intros Hbeq6.
            rewrite <- (beq_nat_true _ _ Hbeq6) in Hrn.
            pose proof (batm_comp_x1_rename_FOv_t alpha2 _ (Var ym) Hrn) as H0.
            unfold rename_FOv in H0. rewrite H0 in Hr2. inversion Hr2 as [HHH].
            rewrite HHH in *. rewrite <- beq_nat_refl in *. discriminate.

            pose proof (batm_comp_x1_rename_FOv_f alpha2 (Var xn) (Var ym) (Var rn)) as H0.
            unfold rename_FOv in H0. rewrite H0 in Hr2. inversion Hr2 as [HHH].
            rewrite HHH in *.
            rewrite (beq_nat_true _ _ Hbeq3) in *. rewrite <- (beq_nat_true _ _ Hbeq3) in *.
            rewrite Hbeq4 in *. discriminate.
              intros HH. inversion HH as [HHH]. rewrite HHH in *.
              rewrite <- beq_nat_refl in Hbeq6. discriminate.


              assumption.

 simpl in IH.
              unfold rename_FOv in IH. specialize (IH (Var xn) (Var ym)).
              simpl in IH. rewrite Hbeq2 in *. rewrite Hbeq3 in *. simpl in IH.
 *)
(*           case_eq (beq_nat ym u2); intros Hbeq4.
            case_eq (batm_comp_x1 (rename_FOv_n alpha2 xn ym)); intros un Hun.
            case_eq (beq_nat u2 un); intros Hbeq5.
              apply IH.
              simpl in H. rewrite (beq_nat_true _ _ Hbeq) in H.
              rewrite Hbeq3 in H. discriminate.

              simpl in H. rewrite (beq_nat_true _ _ Hbeq) in H.
              rewrite Hbeq3 in H. discriminate.

              simpl in H. rewrite (beq_nat_true _ _ Hbeq) in H.
              rewrite Hbeq3 in H. discriminate.

 simpl in IH.
              unfold rename_FOv in IH. specialize (IH (Var xn) (Var ym)).
              simpl in IH. rewrite Hbeq2 in *.

          case_eq (beq_nat xn u2); intros Hbeq3.
            rewrite <- beq_nat_refl.
            simpl in *. rewrite Hbeq3 in *.
            rewrite (beq_nat_true _ _ Hbeq) in *.
            rewrite Hbeq3 in *.
            case_eq (batm_comp_x1 alpha2); intros rn Hrn.
            case_eq (batm_comp_x1 (rename_FOv_n alpha2 xn ym)); intros r2 Hr2.
            rewrite Hrn in *.
            case_eq (PeanoNat.Nat.eqb u2 rn); intros Hbeq4; rewrite Hbeq4 in *.
              2 : discriminate.
          case_eq (beq_nat ym r2); intros Hbeq5. apply IH. assumption.
          case_eq (beq_nat xn rn); intros Hbeq6.
            rewrite <- (beq_nat_true _ _ Hbeq6) in Hrn.
            pose proof (batm_comp_x1_rename_FOv_t alpha2 _ (Var ym) Hrn) as H0.
            unfold rename_FOv in H0. rewrite H0 in Hr2. inversion Hr2 as [HHH].
            rewrite HHH in *. rewrite <- beq_nat_refl in *. discriminate.

            pose proof (batm_comp_x1_rename_FOv_f alpha2 (Var xn) (Var ym) (Var rn)) as H0.
            unfold rename_FOv in H0. rewrite H0 in Hr2. inversion Hr2 as [HHH].
            rewrite HHH in *.
            rewrite (beq_nat_true _ _ Hbeq3) in *. rewrite <- (beq_nat_true _ _ Hbeq3) in *.
            rewrite Hbeq4 in *. discriminate.
              intros HH. inversion HH as [HHH]. rewrite HHH in *.
              rewrite <- beq_nat_refl in Hbeq6. discriminate.

              assumption.

            rewrite Hbeq3 in *. simpl in *.
            rewrite (beq_nat_true _ _ Hbeq) in *.
            rewrite Hbeq3 in *. discriminate.

 *)
        destruct f as [u1]; destruct f0 as [u2].
        simpl. case_eq (beq_nat xn u1); intros Hbeq2;
          case_eq (beq_nat xn u2); intros Hbeq3;
            reflexivity.

        simpl. destruct f as [un]. simpl.
        case_eq (beq_nat un xn); intros Hbeq2; reflexivity.

        simpl. destruct f as [un]. simpl.
        case_eq (beq_nat un xn); intros Hbeq2; reflexivity.



            
          

(*  simpl in IH.
              unfold rename_FOv in IH. specialize (IH (Var xn) (Var ym)).
              simpl in IH. rewrite Hbeq2 in *. rewrite Hbeq3 in *. simpl in IH.
              apply IH.
              simpl in H. rewrite (beq_nat_true _ _ Hbeq) in H.
              rewrite Hbeq3 in H. discriminate.

              simpl in *. rewrite
 assumption.
          

 _ _ _ _ Hrn) in Hr2.
  
            rewrite (beq_nat_true _ _ Hbeq) in Hrn.

            pose proof (batm_comp_x1_rename_FOv_or alpha2 (Var xn) (Var ym) (Var rn) Hrn) 
              as [HH | HH].
              simpl in HH. pose proof Hr2 as Hr3.
              rewrite HH in Hr2. inversion Hr2 as [Hr2'].
              rewrite Hr2' in *. 

 in Hr2.



    simpl. case_eq (beq_nat zn xn); intros Hbeq.
      simpl. destruct alpha1.

 *)

    simpl. case_eq (beq_nat zn xn) ;intros Hbeq;
      reflexivity.

    simpl. case_eq (beq_nat zn xn) ;intros Hbeq;
      reflexivity.
Qed.
*)

Lemma batm_paired_conjSO_r : forall alpha1 alpha2,
batm_paired (conjSO alpha1 alpha2) = true ->
batm_paired alpha2 = true.
Proof.
  intros alpha1 alpha2 H.
  simpl in *. case_eq (batm_paired alpha2); intros H2.
    reflexivity.
  
    rewrite H2 in *. rewrite if_then_else_false in H. discriminate.
Qed.

Lemma batm_paired_conjSO_l : forall alpha1 alpha2,
batm_paired (conjSO alpha1 alpha2) = true ->
batm_paired alpha1 = true.
Proof.
  intros alpha1 alpha2 H.
  simpl in *. case_eq (batm_paired alpha1); intros H2.
    reflexivity.
  
    rewrite H2 in *. discriminate.
Qed.

Lemma batm_paired_rename_FOv_fwd : forall alpha x y,
  ~ x = (Var 0) ->
  batm_paired alpha = true -> batm_paired (rename_FOv alpha x y) = true.
Proof.
  induction alpha; intros  [xn] [ym] Hnot H.
    simpl. destruct f as [zn]. 
    case_eq (beq_nat xn zn); reflexivity.

    destruct f as [z1]; destruct f0 as [z2].
    simpl. case_eq (beq_nat xn z1); intros Hbeq;
      case_eq (beq_nat xn z2); intros Hbeq2; reflexivity.

    destruct f as [z1]; destruct f0 as [z2].
    simpl. case_eq (beq_nat xn z1); intros Hbeq;
      case_eq (beq_nat xn z2); intros Hbeq2; reflexivity.

    apply batm_paired_rename_FOv_fwd_allFO; try assumption.

    destruct f as [zn]. simpl.
    simpl in *.  case_eq (beq_nat zn xn); intros Hbeq;  
      simpl; apply (IHalpha (Var xn) (Var ym)); assumption.

    simpl in *. apply (IHalpha (Var xn) (Var ym)); assumption.

    unfold rename_FOv in *. simpl.
    rewrite (IHalpha1 (Var xn) (Var ym)).
    apply (IHalpha2 (Var xn) (Var ym)).
all : try assumption.
    apply batm_paired_conjSO_r in H. assumption.
    apply batm_paired_conjSO_l in H. assumption.


    unfold rename_FOv in *. simpl.
    rewrite (IHalpha1 (Var xn) (Var ym)).
    apply (IHalpha2 (Var xn) (Var ym)).
all : try assumption.
    apply batm_paired_conjSO_r in H. assumption.
    apply batm_paired_conjSO_l in H. assumption.

    unfold rename_FOv in *. simpl.
    rewrite (IHalpha1 (Var xn) (Var ym)).
    apply (IHalpha2 (Var xn) (Var ym)).
all : try assumption.
    apply batm_paired_conjSO_r in H. assumption.
    apply batm_paired_conjSO_l in H. assumption.

    simpl in *. apply (IHalpha (Var xn) (Var ym)); assumption.

    simpl in *. apply (IHalpha (Var xn) (Var ym)); assumption.
Qed.

(*
Lemma batm_paired_rename_FOv_fwd : forall alpha x y,
  batm_paired alpha = true -> batm_paired (rename_FOv alpha x y) = true.
Proof.
  induction alpha; intros  [xn] [ym] H.
    simpl. destruct f as [zn]. 
    case_eq (beq_nat xn zn); reflexivity.

    destruct f as [z1]; destruct f0 as [z2].
    simpl. case_eq (beq_nat xn z1); intros Hbeq;
      case_eq (beq_nat xn z2); intros Hbeq2; reflexivity.

    destruct f as [z1]; destruct f0 as [z2].
    simpl. case_eq (beq_nat xn z1); intros Hbeq;
      case_eq (beq_nat xn z2); intros Hbeq2; reflexivity.

    apply batm_paired_rename_FOv_fwd_allFO.
    apply IHalpha. assumption.

    destruct f as [zn]. simpl.
    simpl in *.  case_eq (beq_nat zn xn); intros Hbeq;  
      simpl; apply (IHalpha (Var xn) (Var ym)); assumption.

    simpl in *. apply (IHalpha (Var xn) (Var ym)); assumption.

    unfold rename_FOv in *. simpl.
    rewrite (IHalpha1 (Var xn) (Var ym)).
    apply (IHalpha2 (Var xn) (Var ym)).
    apply batm_paired_conjSO_r in H. assumption.
    apply batm_paired_conjSO_l in H. assumption.


    unfold rename_FOv in *. simpl.
    rewrite (IHalpha1 (Var xn) (Var ym)).
    apply (IHalpha2 (Var xn) (Var ym)).
    apply batm_paired_conjSO_r in H. assumption.
    apply batm_paired_conjSO_l in H. assumption.

    unfold rename_FOv in *. simpl.
    rewrite (IHalpha1 (Var xn) (Var ym)).
    apply (IHalpha2 (Var xn) (Var ym)).
    apply batm_paired_conjSO_r in H. assumption.
    apply batm_paired_conjSO_l in H. assumption.

    simpl in *. apply (IHalpha (Var xn) (Var ym)); assumption.

    simpl in *. apply (IHalpha (Var xn) (Var ym)); assumption.
Qed.
*)

Lemma batm_paired_implSO_rename_FOv_relatSO : forall beta z1 z2 x y,
  batm_paired (implSO (rename_FOv (relatSO z1 z2) x y) beta) = true ->
  batm_paired beta = true.
Admitted.

Lemma batm_paired_defn : forall alpha z u1 u2,
  batm_paired (allFO z (implSO (relatSO u1 u2) alpha)) = true <->
  z = u2 /\ (batm_comp_x1 alpha) = u2 /\ batm_paired alpha = true.
Proof.
  intros alpha [zn] [u1] [u2].
  simpl. case_eq (beq_nat zn u2); intros Hbeq.
    case_eq (batm_comp_x1 alpha); intros xn Hxn;
    case_eq (beq_nat u2 xn); intros Hbeq2.
      rewrite (beq_nat_true _ _ Hbeq) in *.
      rewrite (beq_nat_true _ _ Hbeq2) in *.
      split; intros SOt.
        apply conj. reflexivity. apply conj. reflexivity. assumption.
        apply SOt.

      rewrite (beq_nat_true _ _ Hbeq) in *.
      split; intros SOt. discriminate.
        destruct SOt as [SOt1 [SOt2 SOt3]].
        inversion SOt2 as [SOt2']. rewrite SOt2' in *.
        rewrite <- beq_nat_refl in Hbeq2. discriminate.

      split; intros SOt. discriminate.
      destruct SOt as [SOt1 [SOt2 SOt3]].
      inversion SOt1 as [SOt1']. rewrite SOt1' in *.
      rewrite <- beq_nat_refl in Hbeq. discriminate.
Qed.

Lemma batm_paired_implSO_relatSO : forall beta x y,
  batm_paired (implSO (relatSO x y) beta) = 
  batm_paired beta.
Proof.
  reflexivity.
Qed.

Lemma rename_FOv_allFO_eq : forall alpha x y,
  rename_FOv (allFO x alpha) x y = 
  allFO y (rename_FOv alpha x y).
Proof.
  intros alpha [xn] [ym]. simpl.
  rewrite <- beq_nat_refl. reflexivity.
Qed.

Lemma rename_FOv_allFO_noteq : forall alpha x y z,
  ~ z = x ->
  rename_FOv (allFO z alpha) x y = 
  allFO z (rename_FOv alpha x y).
Proof.
  intros alpha [xn] [ym] [zn] H. simpl.
  rewrite FOvar_neq. reflexivity. assumption.
Qed.

Lemma rename_FOv_relatSO_tt: forall x y,
  rename_FOv (relatSO x x) x y =
  relatSO y y.
Proof.
  intros [xn] [ym]. simpl.
  rewrite <- beq_nat_refl. reflexivity.
Qed.

Lemma rename_FOv_relatSO_ft: forall x y z,
  ~ x = z ->
  rename_FOv (relatSO z x) x y =
  relatSO z y.
Proof.
  intros [xn] [ym] [zn] H. simpl.
  rewrite FOvar_neq. rewrite <- beq_nat_refl.
  reflexivity. assumption.
Qed.

Lemma batm_comp_P_rename_FOv_noteq_allFO : forall alpha f v1 v2 xn ym,
(forall v1 v2 x y : FOvariable,
          v1 <> v2 ->
          batm_comp_x1 alpha = v1 ->
          batm_comp_x1 (rename_FOv alpha x y) = v2 -> v1 = x /\ v2 = y)->
Var v1 <> Var v2 ->
batm_comp_x1 (allFO f alpha) = Var v1 ->
batm_comp_x1 (rename_FOv (allFO f alpha) (Var xn) (Var ym)) = Var v2 ->
Var v1 = Var xn /\ Var v2 = Var ym.
Proof.
  intros alpha [zn] v1 v2 xn ym IH Hnot Hb1 Hb2.
    destruct alpha. simpl in *. destruct f as [vn].
    case_eq (beq_nat zn xn);intros Hbeq; rewrite Hbeq in *;
      case_eq (beq_nat xn vn); intros Hbeq2; rewrite Hbeq2 in *;
        simpl in Hb2; simpl in *; 
      rewrite <- Hb1 in *; rewrite <- Hb2 in *;
      contradiction (Hnot eq_refl).

    destruct f as [u1]; destruct f0 as [u2].
    simpl in *. case_eq (beq_nat zn xn); intros Hbeq; 
      rewrite Hbeq in *;
      case_eq (beq_nat xn u1); intros Hbeq2; rewrite Hbeq2 in *;
        case_eq (beq_nat xn u2); intros Hbeq3; rewrite Hbeq3 in *;
          simpl in *; 
          rewrite <- Hb1 in *; rewrite <- Hb2 in *;
          contradiction (Hnot eq_refl).

    destruct f as [u1]; destruct f0 as [u2].
    simpl in *. case_eq (beq_nat zn xn); intros Hbeq; 
      rewrite Hbeq in *;
      case_eq (beq_nat xn u1); intros Hbeq2; rewrite Hbeq2 in *;
        case_eq (beq_nat xn u2); intros Hbeq3; rewrite Hbeq3 in *;
          simpl in *; 
          rewrite <- Hb1 in *; rewrite <- Hb2 in *;
          contradiction (Hnot eq_refl).

    destruct f as [vn]. simpl in *.
    case_eq (beq_nat zn xn); intros Hbeq; rewrite Hbeq in *;
      case_eq (beq_nat vn xn); intros Hbeq2; rewrite Hbeq2 in *;
          simpl in *; 
          rewrite <- Hb1 in *; rewrite <- Hb2 in *;
          contradiction (Hnot eq_refl).

    destruct f as [vn]. simpl in *.
    case_eq (beq_nat zn xn); intros Hbeq; rewrite Hbeq in *;
      case_eq (beq_nat vn xn); intros Hbeq2; rewrite Hbeq2 in *;
          simpl in *; 
          rewrite <- Hb1 in *; rewrite <- Hb2 in *;
          contradiction (Hnot eq_refl).

    simpl in *.
    case_eq (beq_nat zn xn); intros Hbeq; rewrite Hbeq in *;
      simpl in *; 
      rewrite <- Hb1 in *; rewrite <- Hb2 in *;
      contradiction (Hnot eq_refl).

    simpl in *.
    case_eq (beq_nat zn xn); intros Hbeq; rewrite Hbeq in *;
      simpl in *; 
      rewrite <- Hb1 in *; rewrite <- Hb2 in *;
      contradiction (Hnot eq_refl).

    simpl in *.
    case_eq (beq_nat zn xn); intros Hbeq; rewrite Hbeq in *;
      simpl in *; 
      rewrite <- Hb1 in *; rewrite <- Hb2 in *;
      contradiction (Hnot eq_refl).


    destruct alpha1; try
    (simpl in *;
    case_eq (beq_nat zn xn); intros Hbeq; rewrite Hbeq in *;
      simpl in *; 
      rewrite <- Hb1 in *; rewrite <- Hb2 in *;
      contradiction (Hnot eq_refl)).


      simpl in *. destruct f as [un].
      case_eq (beq_nat zn xn); intros Hbeq; rewrite Hbeq in *;
        case_eq (beq_nat xn un); intros Hbeq2; rewrite Hbeq2 in *;
          simpl in Hb2;
          try (rewrite <- Hb1 in *; rewrite <- Hb2 in *;
          contradiction (Hnot eq_refl)).

      destruct f as [u1]; destruct f0 as [u2].
      simpl in Hb1. simpl in Hb2.
      case_eq (beq_nat zn xn); intros Hbeq; rewrite Hbeq in *;
          try (rewrite <- Hb1 in *; rewrite <- Hb2 in *;
          contradiction (Hnot eq_refl));

        case_eq (beq_nat xn u1); intros Hbeq2; rewrite Hbeq2 in *;
          case_eq (beq_nat xn u2); intros Hbeq3; rewrite Hbeq3 in *;
            simpl in Hb2. rewrite (beq_nat_true _ _ Hbeq2).
            apply conj; symmetry; assumption.

            simpl in Hb2. rewrite (beq_nat_true _ _ Hbeq2).
            apply conj; symmetry; assumption.


          rewrite <- Hb1 in *. rewrite <- Hb2 in *.
          contradiction (Hnot eq_refl).

          rewrite <- Hb1 in *; rewrite <- Hb2 in *;
          contradiction (Hnot eq_refl).

            simpl in Hb2. rewrite (beq_nat_true _ _ Hbeq2).
            apply conj; symmetry; assumption.

          rewrite (beq_nat_true _ _ Hbeq2). 
          apply conj; symmetry; assumption.

          rewrite <- Hb1 in *; rewrite <- Hb2 in *;
          contradiction (Hnot eq_refl).

          rewrite <- Hb1 in *; rewrite <- Hb2 in *;
          contradiction (Hnot eq_refl).


        simpl in *. destruct f as [u1]; destruct f0 as [u2].
      case_eq (beq_nat zn xn); intros Hbeq; rewrite Hbeq in *;
          try (rewrite <- Hb1 in *; rewrite <- Hb2 in *;
          contradiction (Hnot eq_refl));

        case_eq (beq_nat xn u1); intros Hbeq2; rewrite Hbeq2 in *;
          case_eq (beq_nat xn u2); intros Hbeq3; rewrite Hbeq3 in *;
            simpl in Hb2;
      rewrite <- Hb1 in *; rewrite <- Hb2 in *;
      contradiction (Hnot eq_refl).

        simpl in *. destruct f as [u1]; 
      case_eq (beq_nat zn xn); intros Hbeq; rewrite Hbeq in *;
          try (rewrite <- Hb1 in *; rewrite <- Hb2 in *;
          contradiction (Hnot eq_refl));
          case_eq (beq_nat u1 xn); intros Hbeq2; rewrite Hbeq2 in *;
            simpl in Hb2;
      rewrite <- Hb1 in *; rewrite <- Hb2 in *;
      contradiction (Hnot eq_refl).

        simpl in *. destruct f as [u1]; 
      case_eq (beq_nat zn xn); intros Hbeq; rewrite Hbeq in *;
          try (rewrite <- Hb1 in *; rewrite <- Hb2 in *;
          contradiction (Hnot eq_refl));
          case_eq (beq_nat u1 xn); intros Hbeq2; rewrite Hbeq2 in *;
            simpl in Hb2;
      rewrite <- Hb1 in *; rewrite <- Hb2 in *;
      contradiction (Hnot eq_refl).

    simpl in *.
    case_eq (beq_nat zn xn); intros Hbeq; rewrite Hbeq in *;
      simpl in *; 
      rewrite <- Hb1 in *; rewrite <- Hb2 in *;
      contradiction (Hnot eq_refl).

    simpl in *.
    case_eq (beq_nat zn xn); intros Hbeq; rewrite Hbeq in *;
      simpl in *; 
      rewrite <- Hb1 in *; rewrite <- Hb2 in *;
      contradiction (Hnot eq_refl).
Qed.

Lemma batm_comp_P_rename_FOv_noteq : forall alpha v1 v2 x y,
  ~ v1 = v2 ->
  batm_comp_x1 alpha = v1 ->
  batm_comp_x1 (rename_FOv alpha x y) = v2 ->
  v1 = x /\ v2 = y.
Proof.
  induction alpha; intros [v1] [v2] [xn] [ym] Hnot Hb1 Hb2;
    try (      simpl in *; rewrite <- Hb1 in *; rewrite <- Hb2 in *;
      contradiction (Hnot eq_refl)).
    destruct f as [zn]. simpl in *. rewrite Hb1 in *.
    case_eq (beq_nat xn zn); intros Hbeq; rewrite Hbeq in *.
      simpl in *. rewrite (beq_nat_true _ _ Hbeq) in *.
      apply conj. symmetry. assumption.
      symmetry. assumption.

      simpl in *. contradiction (Hnot Hb2).

    destruct f as [z1]; destruct f0 as [z2].
    simpl in *; case_eq (beq_nat xn z1); intros Hbeq;
      rewrite Hbeq in *; case_eq (beq_nat xn z2);
        intros Hbeq2; rewrite Hbeq2 in *;
        simpl in *; rewrite <- Hb1 in *;  
        rewrite <- Hb2 in *; contradiction (Hnot eq_refl).

    destruct f as [z1]; destruct f0 as [z2].
    simpl in *; case_eq (beq_nat xn z1); intros Hbeq;
      rewrite Hbeq in *; case_eq (beq_nat xn z2);
        intros Hbeq2; rewrite Hbeq2 in *;
        simpl in *; rewrite <- Hb1 in *;  
        rewrite <- Hb2 in *; contradiction (Hnot eq_refl).

apply (batm_comp_P_rename_FOv_noteq_allFO _ _ _ _ _ _ IHalpha Hnot Hb1 Hb2).

    simpl in *. destruct f as [zn].
    case_eq (beq_nat zn xn); intros Hbeq; rewrite Hbeq in *;
      simpl in *; rewrite <- Hb1 in *; rewrite <- Hb2 in *;
      contradiction (Hnot eq_refl).
Qed.

Lemma batm_comp_P_rename_FOv_eq : forall alpha v x y,
  ~ x = y ->
  batm_comp_x1 alpha = v ->
  batm_comp_x1 (rename_FOv alpha x y) = v ->
  ~ v = x.
Admitted.

Lemma batm_comp_x1_is_in_FOvar_num_conn : forall m n alpha x,
    n = num_conn alpha ->
  Nat.leb n m = true ->
  batm_paired alpha = true ->
  batm_comp_x1 alpha = x ->
  ~ x = Var 0 ->
  is_in_FOvar x (FOvars_in alpha) = true.
Proof.
  induction m; intros n alpha [xn] Hnum Hleb H1 H Hnot; try discriminate.
    destruct n. 2 : discriminate.
    destruct alpha; try discriminate.
    simpl in *. rewrite H. rewrite <-beq_nat_refl. reflexivity.

    simpl in *. symmetry in H.
    contradiction ( Hnot H).

    simpl in *. symmetry in H.
    contradiction ( Hnot H).

    destruct n.
    destruct alpha; try discriminate.
    simpl in *. rewrite H. rewrite <-beq_nat_refl. reflexivity.

    simpl in *. symmetry in H.
    contradiction ( Hnot H).

    simpl in *. symmetry in H.
    contradiction ( Hnot H).

    destruct alpha; try
      (simpl in H; symmetry in H;
      contradiction (Hnot H)); try discriminate.

      simpl in *. destruct f as [zn].
      case_eq (beq_nat xn zn); intros Hbeq.
        reflexivity.
(*     apply IHalpha; try assumption. *)
      destruct alpha; try discriminate;
        try (simpl in *; symmetry in H;
        contradiction ( Hnot H)).
      destruct alpha1; try discriminate;
        try (simpl in *; symmetry in H;
        contradiction ( Hnot H)).
      rewrite H in *. destruct f0 as [v1].
      simpl. case_eq (beq_nat zn v1); intros HH; 
        rewrite HH in *. 2: discriminate.
      case_eq (batm_comp_x1 alpha2); intros v2 Hv2; rewrite Hv2 in *.
      case_eq (beq_nat v1 v2); intros Hbeq2; rewrite Hbeq2 in *.
        2 : discriminate.
      rewrite <- beq_nat_refl. reflexivity.
Qed.

Lemma batm_comp_x1_is_in_FOvar : forall alpha x,
  batm_paired alpha = true ->
  batm_comp_x1 alpha = x ->
  ~ x = Var 0 ->
  is_in_FOvar x (FOvars_in alpha) = true.
Proof.
  intros alpha x. apply (batm_comp_x1_is_in_FOvar_num_conn 
    (num_conn alpha) (num_conn alpha)).
    reflexivity.

    apply leb_refl.
Qed.

Lemma batm_comp_x1_rename_FOv_ft_allFO : forall alpha f xn ym,
(forall x y : FOvariable,
          x <> y ->
          y <> Var 0 ->
          is_in_FOvar y (FOvars_in alpha) = false ->
          batm_comp_x1 (rename_FOv alpha x y) = y -> batm_comp_x1 alpha = x) ->
Var xn <> Var ym ->
Var ym <> Var 0 ->
is_in_FOvar (Var ym) (FOvars_in (allFO f alpha)) = false ->
batm_comp_x1 (rename_FOv (allFO f alpha) (Var xn) (Var ym)) = Var ym ->
batm_comp_x1 (allFO f alpha) = Var xn.
Proof.
  intros alpha [zn] xn ym IH Hnot Hnot2 Hin Hb;
  destruct alpha;
    try (    simpl in *;
    case_eq (beq_nat  zn xn); intros Hbeq; rewrite Hbeq in *;
          simpl in *; symmetry in Hb; contradiction (Hnot2 Hb)).


    simpl in *. destruct f as [un].
    case_eq (beq_nat zn xn); intros Hbeq; rewrite Hbeq in *;
      case_eq (beq_nat xn un); intros Hbeq2; rewrite Hbeq2 in *;
        simpl in *; symmetry in Hb; contradiction (Hnot2 Hb).

    destruct f as [u1]; destruct f0 as [u2].
    simpl in *. case_eq (beq_nat zn xn); intros Hbeq; rewrite Hbeq in *;
      case_eq (beq_nat xn u1); intros Hbeq2; rewrite Hbeq2 in *;
        case_eq (beq_nat xn u2); intros Hbeq3; rewrite Hbeq3 in *;
          simpl in *; symmetry in Hb; contradiction (Hnot2 Hb).

    destruct f as [u1]; destruct f0 as [u2].
    simpl in *. case_eq (beq_nat zn xn); intros Hbeq; rewrite Hbeq in *;
      case_eq (beq_nat xn u1); intros Hbeq2; rewrite Hbeq2 in *;
        case_eq (beq_nat xn u2); intros Hbeq3; rewrite Hbeq3 in *;
          simpl in *; symmetry in Hb; contradiction (Hnot2 Hb).

    destruct f as [u1].
    simpl in *. case_eq (beq_nat zn xn); intros Hbeq; rewrite Hbeq in *;
      case_eq (beq_nat u1 xn); intros Hbeq2; rewrite Hbeq2 in *;
          simpl in *; symmetry in Hb; contradiction (Hnot2 Hb).

    destruct f as [u1].
    simpl in *. case_eq (beq_nat zn xn); intros Hbeq; rewrite Hbeq in *;
      case_eq (beq_nat u1 xn); intros Hbeq2; rewrite Hbeq2 in *;
          simpl in *; symmetry in Hb; contradiction (Hnot2 Hb).

    simpl in *. case_eq (beq_nat zn xn); intros Hbeq; rewrite Hbeq in *.
      destruct alpha1; try (symmetry in Hb; contradiction (Hnot2 Hb)).
        simpl in *; destruct f as [vn];
        case_eq (beq_nat xn vn); intros Hbeq2; rewrite Hbeq2 in *;
          symmetry in Hb; contradiction (Hnot2 Hb).


        destruct f as [u1]; destruct f0 as [u2].
        simpl in *. case_eq (beq_nat xn u1); intros Hbeq2;
          rewrite Hbeq2 in *.
          rewrite (beq_nat_true _ _ Hbeq2). reflexivity.

          case_eq (beq_nat xn u2); intros Hbeq3; rewrite Hbeq3 in *;
            inversion Hb as [Hb'];
            rewrite Hb' in Hin; rewrite <- beq_nat_refl in Hin;
            rewrite if_then_else_same in Hin; discriminate.

        destruct f as [v1]; destruct f0 as [v2].
        simpl in *. case_eq (beq_nat xn v1); intros Hbeq2; 
          rewrite Hbeq2 in *;
          case_eq (beq_nat xn v2); intros Hbeq3; rewrite Hbeq3 in *;
          symmetry in Hb; contradiction (Hnot2 Hb).

        destruct f as [v1]. 
        simpl in *. case_eq (beq_nat v1 xn); intros Hbeq2; 
          rewrite Hbeq2 in *;
          symmetry in Hb; contradiction (Hnot2 Hb).

        destruct f as [v1]. 
        simpl in *. case_eq (beq_nat v1 xn); intros Hbeq2; 
          rewrite Hbeq2 in *;
          symmetry in Hb; contradiction (Hnot2 Hb).


      destruct alpha1; try (symmetry in Hb; contradiction (Hnot2 Hb)).
        simpl in *; destruct f as [vn];
        case_eq (beq_nat xn vn); intros Hbeq2; rewrite Hbeq2 in *;
          symmetry in Hb; contradiction (Hnot2 Hb).

        destruct f as [u1]; destruct f0 as [u2].
        simpl in *. case_eq (beq_nat xn u1); intros Hbeq2;
          rewrite Hbeq2 in *.
          rewrite (beq_nat_true _ _ Hbeq2). reflexivity.

          case_eq (beq_nat xn u2); intros Hbeq3; rewrite Hbeq3 in *;
            inversion Hb as [Hb'];
            rewrite Hb' in Hin; rewrite <- beq_nat_refl in Hin;
            rewrite if_then_else_same in Hin; discriminate.


        destruct f as [v1]; destruct f0 as [v2].
        simpl in *. case_eq (beq_nat xn v1); intros Hbeq2; 
          rewrite Hbeq2 in *;
          case_eq (beq_nat xn v2); intros Hbeq3; rewrite Hbeq3 in *;
          symmetry in Hb; contradiction (Hnot2 Hb).

        destruct f as [v1]. 
        simpl in *. case_eq (beq_nat v1 xn); intros Hbeq2; 
          rewrite Hbeq2 in *;
          symmetry in Hb; contradiction (Hnot2 Hb).

        destruct f as [v1]. 
        simpl in *. case_eq (beq_nat v1 xn); intros Hbeq2; 
          rewrite Hbeq2 in *;
          symmetry in Hb; contradiction (Hnot2 Hb).
Qed.

Lemma batm_comp_x1_rename_FOv_ft : forall alpha x y,
  ~ x = y ->
  ~ y = Var 0 ->
  is_in_FOvar y (FOvars_in alpha) = false ->
  batm_comp_x1 (rename_FOv alpha x y) = y ->
  batm_comp_x1 alpha = x.
Proof.
  induction alpha; intros [xn] [ym] Hnot Hnot2 Hin Hb;
    try (    simpl in *; apply not_eq_sym in Hnot2;
    contradiction (Hnot2 Hb)).

    destruct f as [zn].
    simpl in *. apply if_then_else_true_false in Hin.
    case_eq (beq_nat xn zn); intros Hbeq; rewrite Hbeq in *.
      rewrite (beq_nat_true _ _ Hbeq). reflexivity.

      simpl in *. apply beq_nat_false_FOv in Hin.
      symmetry in Hb. contradiction (Hin Hb).

    destruct f as [u1]; destruct f0 as [u2].
    simpl in *.
    case_eq (beq_nat xn u1); intros Hbeq; rewrite Hbeq in *;
      case_eq (beq_nat xn u2); intros Hbeq2; rewrite Hbeq2 in *;
        simpl in *; apply not_eq_sym in Hnot2;
        contradiction (Hnot2 Hb).

    destruct f as [u1]; destruct f0 as [u2].
    simpl in *.
    case_eq (beq_nat xn u1); intros Hbeq; rewrite Hbeq in *;
      case_eq (beq_nat xn u2); intros Hbeq2; rewrite Hbeq2 in *;
        simpl in *; apply not_eq_sym in Hnot2;
        contradiction (Hnot2 Hb).

    
apply (batm_comp_x1_rename_FOv_ft_allFO _ _ _ _ IHalpha Hnot Hnot2 Hin Hb).

    destruct f as [u1].  simpl in *.
    case_eq (beq_nat u1 xn); intros Hbeq; rewrite Hbeq in *;
        simpl in *; apply not_eq_sym in Hnot2;
        contradiction (Hnot2 Hb).
Qed.

Lemma batm_comp_x1_rename_FOv_relatSO : forall u1 u2 x y,
  batm_comp_x1 (rename_FOv (relatSO u1 u2) x y) = Var 0.
Proof.
  intros [u1] [u2] [xn] [ym].
  simpl.
  case_eq (beq_nat xn u1); intros Hbeq;
    case_eq (beq_nat xn u2); intros Hbeq2;
      reflexivity.
Qed.

Lemma batm_comp_x1_rename_FOv_eqFO : forall u1 u2 x y,
  batm_comp_x1 (rename_FOv (eqFO u1 u2) x y) = Var 0.
Proof.
  intros [u1] [u2] [xn] [ym].
  simpl.
  case_eq (beq_nat xn u1); intros Hbeq;
    case_eq (beq_nat xn u2); intros Hbeq2;
      reflexivity.
Qed.

Lemma batm_comp_x1_rename_FOv_exFO : forall alpha u x y,
  batm_comp_x1 (rename_FOv (exFO u alpha) x y) = Var 0.
Proof.
  intros alpha [un] [xn] [ym].
  simpl.
  case_eq (beq_nat un xn); intros Hbeq;
      reflexivity.
Qed.

Lemma batm_comp_x1_rename_FOv_0_or_allFO : forall alpha f ym,
( forall y : FOvariable,
          batm_comp_x1 alpha = Var 0 ->
          batm_comp_x1 (rename_FOv alpha (Var 0) y) = Var 0 \/
          batm_comp_x1 (rename_FOv alpha (Var 0) y) = y) ->
batm_comp_x1 (allFO f alpha) = Var 0 ->
batm_comp_x1 (rename_FOv (allFO f alpha) (Var 0) (Var ym)) = Var 0 \/
batm_comp_x1 (rename_FOv (allFO f alpha) (Var 0) (Var ym)) = Var ym.
Proof.
  intros alpha [zn] ym IH H.
  simpl in *. case_eq (beq_nat zn 0); intros Hbeq;
    destruct alpha;
try (      simpl in *; destruct f as [vn];
      destruct vn; left; reflexivity);
try (      simpl in *; destruct f as [v1]; destruct f0 as [v2];
      destruct v1; destruct v2; left; reflexivity);
try (simpl in *; left; reflexivity);

destruct alpha1; 
try (      simpl in *; destruct f as [vn];
      destruct vn; left; reflexivity);
try (      simpl in *; destruct f as [v1]; destruct f0 as [v2];
      destruct v1; destruct v2; left; reflexivity);
try (simpl in *; left; reflexivity).

rewrite H. simpl. destruct f0 as [vn]. destruct vn;
right; reflexivity.

rewrite H. simpl. destruct f0 as [vn]. destruct vn;
right; reflexivity.
Qed.


Lemma batm_comp_x1_rename_FOv_0_or : forall alpha y,
  batm_comp_x1 alpha = Var 0 ->
  batm_comp_x1 (rename_FOv alpha (Var 0) y) = Var 0 \/
  batm_comp_x1 (rename_FOv alpha (Var 0) y) = y.
Proof.
  induction alpha; intros [ym] H;
    try (    simpl in *; left; reflexivity).

    simpl in *. rewrite H. simpl. right. reflexivity.

    rewrite batm_comp_x1_rename_FOv_relatSO. left. reflexivity.

    rewrite batm_comp_x1_rename_FOv_eqFO. left. reflexivity.

    apply batm_comp_x1_rename_FOv_0_or_allFO; assumption.

    rewrite batm_comp_x1_rename_FOv_exFO. left. reflexivity.
Qed.

(* I think it should work *)
(* Left it here. Try and figure out what's wrong.
4/12/17 *)
Lemma batm_paired_rename_FOv_rev_allFO : forall alpha f xn ym,
(forall x y : FOvariable,
~ y = Var 0 ->
is_in_FOvar y (FOvars_in alpha) = false ->
      batm_paired (rename_FOv alpha x y) = true -> batm_paired alpha = true) ->
~ Var ym = Var 0 ->
is_in_FOvar (Var ym) (FOvars_in (allFO f alpha)) = false ->
batm_paired (rename_FOv (allFO f alpha) (Var xn) (Var ym)) = true ->
batm_paired (allFO f alpha) = true.
Proof.
  intros alpha [zn] xn ym IH Hnot Hin Hb.
  destruct alpha; try discriminate; try reflexivity.
  destruct alpha1; try discriminate; try reflexivity.
  specialize (IH (Var xn) (Var ym)).
  rewrite rename_FOv_implSO in IH.
  destruct f as [u1]; destruct f0 as [u2].  
  simpl FOvars_in in *.
  apply is_in_FOvar_cons_f in Hin. destruct Hin as [Hin1 Hin2].
  specialize (IH Hnot Hin1).
  apply is_in_FOvar_cons_f in Hin1. destruct Hin1 as [Hin1 Hin3].
  apply is_in_FOvar_cons_f in Hin1. destruct Hin1 as [Hin1 Hin4].
  apply batm_paired_defn.
  case_eq (beq_nat zn u2); intros Hbeq.
    rewrite (beq_nat_true _ _ Hbeq) in *. apply conj. reflexivity.
    case_eq (batm_comp_x1 alpha2); intros vn Hvn.
    case_eq (beq_nat vn u2); intros Hbeq2.
      rewrite (beq_nat_true _ _ Hbeq2). apply conj. reflexivity.
      rewrite batm_paired_implSO_relatSO in IH.
      apply IH. simpl.
      simpl in Hb. rewrite (beq_nat_comm u2 xn) in Hb.
      case_eq (beq_nat xn u1); intros Hbeq3; rewrite Hbeq3 in *;
        case_eq (beq_nat xn u2); intros Hbeq4; rewrite Hbeq4 in *;
          simpl in Hb; simpl;
          case_eq (batm_comp_x1 (rename_FOv_n alpha2 xn ym)); 
            intros jn Hjn; rewrite Hjn in *;
          rewrite <- beq_nat_refl in *.
          case_eq (beq_nat ym jn); intros Hbeq5; rewrite Hbeq5 in *.
            all : try discriminate. assumption.

          case_eq (beq_nat u2 jn); intros Hbeq5; rewrite Hbeq5 in *.
            all : try discriminate. assumption.

          case_eq (beq_nat ym jn); intros Hbeq5; rewrite Hbeq5 in *.
            all : try discriminate. assumption.

          case_eq (beq_nat u2 jn); intros Hbeq5; rewrite Hbeq5 in *.
            all : try discriminate. assumption.

case_eq (beq_nat xn u2); intros Hbeq3.
  rewrite (beq_nat_true _ _ Hbeq3) in *.
  rewrite rename_FOv_allFO_eq in Hb.
  case_eq (beq_nat xn u1); intros Hbeq4.
    rewrite (beq_nat_true _ _ Hbeq4) in *.
    rewrite (beq_nat_true _ _ Hbeq3) in *.
    rewrite rename_FOv_implSO in Hb.
    rewrite rename_FOv_relatSO_tt in Hb.
    apply batm_paired_defn in Hb.
    destruct Hb as [Hb1 [Hb2 Hb3]].
    pose proof (batm_comp_x1_rename_FOv_t).
    apply not_eq_sym in Hin4. 
    pose proof (batm_comp_x1_rename_FOv_ft alpha2 (Var u2)
       (Var ym) Hin4 Hnot Hin1 Hb2) as H0.   
    rewrite H0 in *. inversion Hvn as [Hvn'].
    rewrite Hvn' in *. rewrite <- beq_nat_refl in *.
    discriminate.

    rewrite rename_FOv_implSO in Hb.
    rewrite rename_FOv_relatSO_ft in Hb.
    apply batm_paired_defn in Hb.
    destruct Hb as [Hb1 [Hb2 Hb3]].
    pose proof (batm_comp_x1_rename_FOv_t).
    apply not_eq_sym in Hin4. 
    pose proof (batm_comp_x1_rename_FOv_ft alpha2 (Var u2)
       (Var ym) Hin4 Hnot Hin1 Hb2) as H0.   
    rewrite H0 in *. inversion Hvn as [Hvn'].
    rewrite Hvn' in *. rewrite <- beq_nat_refl in *.
    discriminate.

    apply beq_nat_false_FOv. rewrite (beq_nat_true _ _ Hbeq3) in *.
    assumption.

    rewrite rename_FOv_allFO_noteq in *.
    rewrite rename_FOv_implSO in Hb.
    simpl rename_FOv at 1 in Hb.
    rewrite Hbeq3 in *.
    case_eq (beq_nat xn u1); intros Hbeq4;
      rewrite Hbeq4 in *.
      apply batm_paired_defn in Hb.
      destruct Hb as [Hb1 [Hb2 Hb3]].
(*       pose proof (batm_comp_x1_rename_FOv_f). *)
      apply not_eq_sym in Hin4.
 
(*       pose proof (batm_comp_x1_rename_FOv_f alpha2 (Var xn)
         (Var ym) (Var vn)). *)
      case_eq (beq_nat xn vn); intros Hbeq6.
        rewrite (beq_nat_true _ _ Hbeq6) in *.
        destruct vn.
          destruct (batm_comp_x1_rename_FOv_0_or alpha2 (Var ym) Hvn)   
            as [H1 | H2].
            rewrite H1 in *. destruct u2; discriminate.

            rewrite H2 in *. contradiction (Hin2 Hb2).

          rewrite batm_comp_x1_rename_FOv_t in Hb2; try assumption.
          contradiction (Hin2 Hb2). discriminate.

        rewrite (batm_comp_x1_rename_FOv_f _ _ _ (Var vn)) in Hb2.
        inversion Hb2 as [Hb2']. rewrite Hb2' in *.
        rewrite <- beq_nat_refl in *. discriminate.
        apply beq_nat_false_FOv. assumption.
        assumption.

        apply batm_paired_defn in Hb.
        destruct Hb as [Hb1 [Hb2 Hb3]].
        apply batm_comp_P_rename_FOv_noteq with (v1 := Var vn) in Hb2.
        destruct Hb2 as [Hb2 Hb2'].
        symmetry in Hb2'. contradiction (Hin2 Hb2').

        apply beq_nat_false_FOv. assumption. assumption.

        apply beq_nat_false_FOv. rewrite beq_nat_comm.
        assumption.

    simpl in Hb.
    case_eq (PeanoNat.Nat.eqb zn xn); intros Hbeq2; rewrite Hbeq2 in *.
      case_eq (beq_nat xn u1); intros Hbeq3; rewrite Hbeq3 in *.
        rewrite <- (beq_nat_true _ _ Hbeq2) in Hb.
        rewrite Hbeq in Hb. simpl in Hb.
        rewrite (FOvar_neq _ _ Hin4) in Hb. discriminate.

        rewrite <- (beq_nat_true _ _ Hbeq2) in Hb.
        rewrite Hbeq in Hb. simpl in Hb.
        rewrite (FOvar_neq _ _ Hin4) in Hb. discriminate.


      case_eq (beq_nat xn u1); intros Hbeq3; rewrite Hbeq3 in *;
        case_eq (beq_nat xn u2); intros Hbeq4; rewrite Hbeq4 in *;
          simpl in *. apply not_eq_sym in Hin2.
          rewrite (FOvar_neq _ _ Hin2) in Hb. discriminate.

          rewrite Hbeq in Hb. discriminate.

          simpl in *. apply not_eq_sym in Hin2.
          rewrite (FOvar_neq _ _ Hin2) in Hb. discriminate.

          rewrite Hbeq in Hb. discriminate.
Qed.
(* 

Lemma : forall alpha v y,
  batm_comp_x1 alpha = v ->
  batm_comp_x1 (rename_FOv alpha v y) = y.

      rewrite H0 in *. inversion Hvn as [Hvn'].
      rewrite Hvn' in *. rewrite <- beq_nat_refl in *.
      discriminate.

    apply beq_nat_false_FOv. rewrite (beq_nat_true _ _ Hbeq3) in *.
    assumption.

      
    rewrite rename_FOv_rel
Search Var beq_nat.

   



    simpl in Hb.
    
    

    

      

    destruct Hb
     rewrite rename_FOv_implSO_relatSO in Hb.
  

          simpl in Hb.

      simpl in Hb. rewrite (beq_nat_comm u2 xn) in Hb.
      case_eq (beq_nat xn u1); intros Hbeq3; rewrite Hbeq3 in *;
        case_eq (beq_nat xn u2); intros Hbeq4; rewrite Hbeq4 in *;
          simpl in Hb; simpl;
          case_eq (batm_comp_x1 (rename_FOv_n alpha2 xn ym)); 
            intros jn Hjn; rewrite Hjn in *;
          rewrite <- beq_nat_refl in *.
          case_eq (beq_nat ym jn); intros Hbeq5; rewrite Hbeq5 in *.
            all : try discriminate.
          case_eq (beq_nat vn jn); intros Hbeq6.
            rewrite (beq_nat_true _ _ Hbeq6) in *.
(*             pose proof (batm_comp_P_rename_FOv_eq alpha2 (Var jn)
              (Var xn) (Var ym)) as HH. *)

simpl in  IH. rewrite Hbeq3 in *. rewrite Hbeq4 in *. simpl in *.
specialize (IH Hb).
            rewrite <- (beq_nat_true _ _ Hbeq5) in *.
            rewrite (batm_comp_x1_is_in_FOvar _ _ IH Hvn Hnot) in *.
            discriminate.


            assert (~Var vn = Var jn) as Hnot2.
              intros HH2. inversion HH2 as [HH3].
              rewrite HH3 in *. rewrite <- beq_nat_refl in *.
              discriminate.
            destruct (batm_comp_P_rename_FOv_noteq alpha2 (Var vn)
              (Var jn) (Var xn) (Var ym) Hnot2 Hvn Hjn) as [HH1 HH2].
            inversion HH1 as [HH1']. rewrite HH1' in *.
            rewrite Hbeq2 in *. discriminate.


          case_eq (beq_nat u2 jn); intros Hbeq5; rewrite Hbeq5 in *.
            all : try discriminate.
            assert (~Var vn = Var jn) as Hnot2.
              intros HH2. inversion HH2 as [HH3].
              rewrite HH3 in *. rewrite beq_nat_comm in Hbeq5.
              rewrite Hbeq5 in *.
              discriminate.
            destruct (batm_comp_P_rename_FOv_noteq alpha2 (Var vn)
              (Var jn) (Var xn) (Var ym) Hnot2 Hvn Hjn) as [HH1 HH2].
            inversion HH2 as [HH2']. rewrite HH2' in *.
            rewrite (beq_nat_true _ _ Hbeq5) in Hin2.   
            contradiction (Hin2 eq_refl).

          case_eq (beq_nat ym jn); intros Hbeq5; rewrite Hbeq5 in *.
            all : try discriminate.
          case_eq (beq_nat vn jn); intros Hbeq6.
            rewrite (beq_nat_true _ _ Hbeq6) in *.
(*             pose proof (batm_comp_P_rename_FOv_eq alpha2 (Var jn)
              (Var xn) (Var ym)) as HH. *)

simpl in  IH. rewrite Hbeq3 in *. rewrite Hbeq4 in *. simpl in *.
specialize (IH Hb).
            rewrite <- (beq_nat_true _ _ Hbeq5) in *.
            rewrite (batm_comp_x1_is_in_FOvar _ _ IH Hvn Hnot) in *.
            discriminate.


            assert (~Var vn = Var jn) as Hnot2.
              intros HH2. inversion HH2 as [HH3].
              rewrite HH3 in *. rewrite <- beq_nat_refl in *.
              discriminate.
            destruct (batm_comp_P_rename_FOv_noteq alpha2 (Var vn)
              (Var jn) (Var xn) (Var ym) Hnot2 Hvn Hjn) as [HH1 HH2].
            inversion HH1 as [HH1']. rewrite HH1' in *.
            rewrite Hbeq2 in *. discriminate.


          case_eq (beq_nat u2 jn); intros Hbeq5; rewrite Hbeq5 in *.
            all : try discriminate.
            assert (~Var vn = Var jn) as Hnot2.
              intros HH2. inversion HH2 as [HH3].
              rewrite HH3 in *. rewrite beq_nat_comm in Hbeq5.
              rewrite Hbeq5 in *.
              discriminate.
            destruct (batm_comp_P_rename_FOv_noteq alpha2 (Var vn)
              (Var jn) (Var xn) (Var ym) Hnot2 Hvn Hjn) as [HH1 HH2].
            inversion HH2 as [HH2']. rewrite HH2' in *.
            rewrite (beq_nat_true _ _ Hbeq5) in Hin2.   
            contradiction (Hin2 eq_refl).

    simpl in Hb.
    case_eq (beq_nat zn xn); intros Hbeq2; rewrite Hbeq2 in *.
      rewrite <- (beq_nat_true _ _ Hbeq2) in Hb.
      rewrite Hbeq in Hb. case_eq (beq_nat zn u1);
        intros Hbeq3; rewrite Hbeq3 in *. simpl in *.
        case_eq (beq_nat ym u2); intros Hbeq4; rewrite Hbeq4 in *.
          2 : discriminate.
        case_eq (batm_comp_x1 (rename_FOv_n alpha2 zn ym));
          intros v2 Hv2; rewrite Hv2 in *.
        case_eq (beq_nat u2 v2); intros Hbeq5; rewrite Hbeq5 in *.
          2 : discriminate.
        rewrite <- (beq_nat_true _ _ Hbeq2) in *.
        rewrite Hbeq3 in *. rewrite Hbeq in *.
        simpl in IH.
admit.
simpl in *.
      case_eq (beq_nat xn u2); intros Hbeq3; rewrite Hbeq3 in *.
        

    rewrite (beq_nat_true _ _ Hbeq) in *. apply conj. reflexivity.
    case_eq (batm_comp_x1 alpha2); intros vn Hvn.
    case_eq (beq_nat vn u2); intros Hbeq2.
      rewrite (beq_nat_true _ _ Hbeq2). apply conj. reflexivity.
      rewrite batm_paired_implSO_relatSO in IH.
      apply IH. simpl.
      simpl in Hb. rewrite (beq_nat_comm u2 xn) in Hb.
      case_eq (beq_nat xn u1); intros Hbeq3; rewrite Hbeq3 in *;
        case_eq (beq_nat xn u2); intros Hbeq4; rewrite Hbeq4 in *;
          simpl in Hb; simpl;
          case_eq (batm_comp_x1 (rename_FOv_n alpha2 xn ym)); 
            intros jn Hjn; rewrite Hjn in *;
          rewrite <- beq_nat_refl in *.
          case_eq (beq_nat ym jn); intros Hbeq5; rewrite Hbeq5 in *.
            all : try discriminate. assumption.

          case_eq (beq_nat u2 jn); intros Hbeq5; rewrite Hbeq5 in *.
            all : try discriminate. assumption.

          case_eq (beq_nat ym jn); intros Hbeq5; rewrite Hbeq5 in *.
            all : try discriminate. assumption.

          case_eq (beq_nat u2 jn); intros Hbeq5; rewrite Hbeq5 in *.
            all : try discriminate. assumption.

          simpl in Hb.

      simpl in Hb. rewrite (beq_nat_comm u2 xn) in Hb.
      case_eq (beq_nat xn u1); intros Hbeq3; rewrite Hbeq3 in *;
        case_eq (beq_nat xn u2); intros Hbeq4; rewrite Hbeq4 in *;
          simpl in Hb; simpl;
          case_eq (batm_comp_x1 (rename_FOv_n alpha2 xn ym)); 
            intros jn Hjn; rewrite Hjn in *;
          rewrite <- beq_nat_refl in *.
          case_eq (beq_nat ym jn); intros Hbeq5; rewrite Hbeq5 in *.
            all : try discriminate.
          case_eq (beq_nat vn jn); intros Hbeq6.
            rewrite (beq_nat_true _ _ Hbeq6) in *.
(*             pose proof (batm_comp_P_rename_FOv_eq alpha2 (Var jn)
              (Var xn) (Var ym)) as HH. *)

simpl in  IH. rewrite Hbeq3 in *. rewrite Hbeq4 in *. simpl in *.
specialize (IH Hb).
            rewrite <- (beq_nat_true _ _ Hbeq5) in *.
            rewrite (batm_comp_x1_is_in_FOvar _ _ IH Hvn Hnot) in *.
            discriminate.


            assert (~Var vn = Var jn) as Hnot2.
              intros HH2. inversion HH2 as [HH3].
              rewrite HH3 in *. rewrite <- beq_nat_refl in *.
              discriminate.
            destruct (batm_comp_P_rename_FOv_noteq alpha2 (Var vn)
              (Var jn) (Var xn) (Var ym) Hnot2 Hvn Hjn) as [HH1 HH2].
            inversion HH1 as [HH1']. rewrite HH1' in *.
            rewrite Hbeq2 in *. discriminate.


          case_eq (beq_nat u2 jn); intros Hbeq5; rewrite Hbeq5 in *.
            all : try discriminate.
            assert (~Var vn = Var jn) as Hnot2.
              intros HH2. inversion HH2 as [HH3].
              rewrite HH3 in *. rewrite beq_nat_comm in Hbeq5.
              rewrite Hbeq5 in *.
              discriminate.
            destruct (batm_comp_P_rename_FOv_noteq alpha2 (Var vn)
              (Var jn) (Var xn) (Var ym) Hnot2 Hvn Hjn) as [HH1 HH2].
            inversion HH2 as [HH2']. rewrite HH2' in *.
            rewrite (beq_nat_true _ _ Hbeq5) in Hin2.   
            contradiction (Hin2 eq_refl).

          case_eq (beq_nat ym jn); intros Hbeq5; rewrite Hbeq5 in *.
            all : try discriminate.
          case_eq (beq_nat vn jn); intros Hbeq6.
            rewrite (beq_nat_true _ _ Hbeq6) in *.
(*             pose proof (batm_comp_P_rename_FOv_eq alpha2 (Var jn)
              (Var xn) (Var ym)) as HH. *)

simpl in  IH. rewrite Hbeq3 in *. rewrite Hbeq4 in *. simpl in *.
specialize (IH Hb).
            rewrite <- (beq_nat_true _ _ Hbeq5) in *.
            rewrite (batm_comp_x1_is_in_FOvar _ _ IH Hvn Hnot) in *.
            discriminate.


            assert (~Var vn = Var jn) as Hnot2.
              intros HH2. inversion HH2 as [HH3].
              rewrite HH3 in *. rewrite <- beq_nat_refl in *.
              discriminate.
            destruct (batm_comp_P_rename_FOv_noteq alpha2 (Var vn)
              (Var jn) (Var xn) (Var ym) Hnot2 Hvn Hjn) as [HH1 HH2].
            inversion HH1 as [HH1']. rewrite HH1' in *.
            rewrite Hbeq2 in *. discriminate.


          case_eq (beq_nat u2 jn); intros Hbeq5; rewrite Hbeq5 in *.
            all : try discriminate.
            assert (~Var vn = Var jn) as Hnot2.
              intros HH2. inversion HH2 as [HH3].
              rewrite HH3 in *. rewrite beq_nat_comm in Hbeq5.
              rewrite Hbeq5 in *.
              discriminate.
            destruct (batm_comp_P_rename_FOv_noteq alpha2 (Var vn)
              (Var jn) (Var xn) (Var ym) Hnot2 Hvn Hjn) as [HH1 HH2].
            inversion HH2 as [HH2']. rewrite HH2' in *.
            rewrite (beq_nat_true _ _ Hbeq5) in Hin2.   
            contradiction (Hin2 eq_refl).



          case_eq (beq_nat ym jn); intros Hbeq5; rewrite Hbeq5 in *.
            all : try discriminate.
          case_eq (beq_nat vn jn); intros Hbeq6.
            rewrite (beq_nat_true _ _ Hbeq6) in *.
(*             pose proof (batm_comp_P_rename_FOv_eq alpha2 (Var jn)
              (Var xn) (Var ym)) as HH. *)

simpl in  IH. rewrite Hbeq3 in *. rewrite Hbeq4 in *. simpl in *.
specialize (IH Hb).
            rewrite <- (beq_nat_true _ _ Hbeq5) in *.
            rewrite (batm_comp_x1_is_in_FOvar _ _ IH Hvn Hnot) in *.
            discriminate.


            assert (~Var vn = Var jn) as Hnot2.
              intros HH2. inversion HH2 as [HH3].
              rewrite HH3 in *. rewrite <- beq_nat_refl in *.
              discriminate.
            destruct (batm_comp_P_rename_FOv_noteq alpha2 (Var vn)
              (Var jn) (Var xn) (Var ym) Hnot2 Hvn Hjn) as [HH1 HH2].
            inversion HH1 as [HH1']. rewrite HH1' in *.
            rewrite Hbeq2 in *. discriminate.


            
            rewrite Hbeq2 in *. discriminate.

          case_eq (beq_nat vn jn); intros Hbeq6.
            rewrite (beq_nat_true _ _ Hbeq6) in *.
(*             pose proof (batm_comp_P_rename_FOv_eq alpha2 (Var jn)
              (Var xn) (Var ym)) as HH. *)

simpl in  IH. rewrite Hbeq3 in *. rewrite Hbeq4 in *. simpl in *.
specialize (IH Hb).
            rewrite <- (beq_nat_true _ _ Hbeq5) in *.
            rewrite (batm_comp_x1_is_in_FOvar _ _ IH Hvn Hnot) in *.
            discriminate.


            assert (~Var vn = Var jn) as Hnot2.
              intros HH2. inversion HH2 as [HH3].
              rewrite HH3 in *. rewrite <- beq_nat_refl in *.
              discriminate.
            destruct (batm_comp_P_rename_FOv_noteq alpha2 (Var vn)
              (Var jn) (Var xn) (Var ym) Hnot2 Hvn Hjn) as [HH1 HH2].
            inversion HH1 as [HH1']. rewrite HH1' in *.
            rewrite Hbeq2 in *. discriminate.


          
            specialize (HH Hnot2 Hvn Hjn).
          


          case_eq (beq_nat u2 jn); intros Hbeq5; rewrite Hbeq5 in *.
            all : try discriminate. assumption.

          case_eq (beq_nat ym jn); intros Hbeq5; rewrite Hbeq5 in *.
            all : try discriminate. assumption.

          case_eq (beq_nat u2 jn); intros Hbeq5; rewrite Hbeq5 in *.
            all : try discriminate. assumption.

          simpl in Hb.


        
admit.

      case_eq (beq_nat xn zn); intros Hbeq3.
        rewrite <- (beq_nat_true _ _ Hbeq) in Hb.
        rewrite <- (beq_nat_true _ _ Hbeq3) in Hb.
        rewrite rename_FOv_allFO_eq in Hb.
        case_eq (beq_nat xn u1); intros Hbeq4.
          rewrite <- (beq_nat_true _ _ Hbeq4) in Hb.
          rewrite rename_FOv_implSO in Hb.
          rewrite rename_FOv_relatSO_tt in Hb.
Search implSO rename_FOv batm_paired.
Search rename_FOv allFO.

 
admit.


Lemma
;
Search batm_paired implSO.
Search rename_FOv allFO.

Lemma
  
Search batm_paired "def".



  | allFO y (implSO (relatSO z1 z2) beta) =>
    match y, z1, z2 with
    | Var ym, Var zn1, Var zn2 =>
    if beq_nat ym zn2 then 
    if match (batm_comp_x1 beta) with Var xn =>
     beq_nat zn2 xn end
      then batm_paired beta
      else false else false
    end
 *)

(* Lemma batm_paired_rename_FOv_rev_allFO : forall alpha f xn ym,
(forall x y : FOvariable,
      batm_paired (rename_FOv alpha x y) = true -> batm_paired alpha = true) ->
batm_paired (rename_FOv (allFO f alpha) (Var xn) (Var ym)) = true ->
batm_paired (allFO f alpha) = true.
Proof.

Admitted. *)
(*   intros alpha [zn] xn ym IH Hin Hb.
  destruct alpha; try discriminate; try reflexivity.
  destruct alpha1; try discriminate; try reflexivity.
  specialize (IH (Var xn) (Var ym)).
  rewrite rename_FOv_implSO in IH.
  destruct f as [u1]; destruct f0 as [u2].  
  simpl FOvars_in in *.
  apply is_in_FOvar_cons_f in Hin. destruct Hin as [Hin1 Hin2].
  specialize (IH Hin1).
  apply is_in_FOvar_cons_f in Hin1. destruct Hin1 as [Hin1 Hin3].
  apply is_in_FOvar_cons_f in Hin1. destruct Hin1 as [Hin1 Hin4].
  simpl in *.
  case_eq (beq_nat zn xn); intros Hbeq; rewrite Hbeq in *.
    case_eq (beq_nat xn u1); intros Hbeq2; rewrite Hbeq2 in *.
      case_eq (beq_nat xn u2); intros Hbeq3; rewrite Hbeq3 in *.
        simpl in Hb. rewrite <- beq_nat_refl in Hb.
        case_eq (batm_comp_x1 (rename_FOv_n alpha2 xn ym)); intros v1 Hv1;
          rewrite Hv1 in *.
        case_eq (beq_nat ym v1); intros Hbeq4; rewrite Hbeq4 in *.
          2 : discriminate.
        rewrite (beq_nat_true _ _ Hbeq). rewrite Hbeq3.
        case_eq (batm_comp_x1 alpha2); intros v2 Hv2.
        case_eq (beq_nat u2 v2); intros Hbeq5.
          apply IH.
admit.
          simpl. assumption. simpl in IH.
admit.
    2 : discriminate.

  simpl rename_FOv at 2 in IH.
  

  simpl rename_FOv in IH.
  simpl rename_FOv in IH.
  destruct f as [u1]; destruct f0 as [u2].
  case_eq (beq_nat zn xn); intros Hbeq; rewrite Hbeq in *.
    simpl in *.
    specialize (IH (Var xn) (Var ym)). rewrite rename_FOv_implSO in IH.
    simpl in IH. case_eq (beq_nat xn u1); intros Hbeq2;
      rewrite Hbeq2 in *.
      case_eq (beq_nat xn u2); intros Hbeq3; rewrite Hbeq3 in *.
        rewrite <- beq_nat_refl in *. simpl in *.
        rewrite (beq_nat_true _ _ Hbeq). rewrite Hbeq3.
        case_eq (batm_comp_x1 alpha2); intros vn Hvn.
        case_eq (batm_comp_x1 (rename_FOv_n alpha2 xn ym)); intros v2 Hv2.
        rewrite Hv2 in *.
        case_eq (beq_nat ym v2); intros Hbeq4; rewrite Hbeq4 in *. 2 : discriminate.
        specialize (IH Hb). rewrite IH.
        case_eq (beq_nat vn xn); intros Hbeq5.
          rewrite (beq_nat_true _ _ Hbeq5) in *.
          rewrite beq_nat_comm. rewrite Hbeq3. reflexivity.
          apply (batm_comp_x1_rename_FOv_f _ (Var xn) (Var ym) (Var vn)) in Hvn.
          simpl in *. rewrite Hvn in *. 


          rewrite <- (beq_nat_true _ _ Hbeq3).
          rewrite beq_nat_comm. rewrite Hbeq5.

          apply (batm_comp_x1_rename_FOv_t _ (Var xn) (Var ym)) in Hvn.
          simpl in *.
          rewrite Hv2 in Hvn. inverei
Search batm_comp_x1 rename_FOv.

batm_comp_x1_rename_FOv_f:
  forall (alpha : SecOrder) (x y z : FOvariable),
  x <> z -> batm_comp_x1 alpha = z -> batm_comp_x1 (rename_FOv alpha x y) = z
batm_comp_x1_rename_FOv_t:
  forall (alpha : SecOrder) (x y : FOvariable),
  x <> Var 0 -> batm_comp_x1 alpha = x -> batm_comp_x1 (rename_FOv alpha x y) = y


  case_eq (beq_nat zn u2); intros Hbeq. *)



Lemma batm_paired_rename_FOv_rev : forall alpha x y,
  ~ y = Var 0 ->
  is_in_FOvar y (FOvars_in alpha) = false ->
  batm_paired (rename_FOv alpha x y) = true -> batm_paired alpha = true.
Proof.
  induction alpha; intros [xn] [ym] H0 Hin H; try reflexivity.
    apply (batm_paired_rename_FOv_rev_allFO _ _ xn ym);
    try assumption.

    destruct f as [zn]. simpl FOvars_in in Hin.
    apply is_in_FOvar_cons_f in Hin. destruct Hin as [Hin1 Hin2].
    simpl in *. 
    case_eq (beq_nat zn xn); intros Hbeq; rewrite Hbeq in *;
      simpl in *; apply (IHalpha (Var xn) (Var ym)) in H;
      assumption.

    simpl in *; apply (IHalpha (Var xn) (Var ym)) in H;
    assumption.

    simpl in *.
    rewrite (IHalpha1 (Var xn) (Var ym)).
    apply (IHalpha2 (Var xn) (Var ym)). assumption.
    apply is_in_FOvar_app_r in Hin. assumption.
    apply batm_paired_conjSO_r in H. assumption. assumption.
    apply is_in_FOvar_app_l in Hin. assumption. 
    apply batm_paired_conjSO_l in H. assumption.

    simpl in *.
    rewrite (IHalpha1 (Var xn) (Var ym)).
    apply (IHalpha2 (Var xn) (Var ym)); try assumption.
    apply is_in_FOvar_app_r in Hin. assumption.
    apply batm_paired_conjSO_r in H. assumption. assumption.
    apply is_in_FOvar_app_l in Hin. assumption. 
    apply batm_paired_conjSO_l in H. assumption.

    simpl in *.
    rewrite (IHalpha1 (Var xn) (Var ym)).
    apply (IHalpha2 (Var xn) (Var ym)). assumption.
    apply is_in_FOvar_app_r in Hin. assumption.
    apply batm_paired_conjSO_r in H. assumption. assumption.
    apply is_in_FOvar_app_l in Hin. assumption. 
    apply batm_paired_conjSO_l in H. assumption.


    simpl in *; apply (IHalpha (Var xn) (Var ym)) in H;
    assumption.

    simpl in *; apply (IHalpha (Var xn) (Var ym)) in H;
    assumption.
Qed.

(* The reason for the condition on x is because of the degenerate case
  of batm_comp_x1. Would recommend changing to Var 0. *)
Lemma same_struc_BAT2_rename_FOv : forall alpha x y,
  ~ x = (Var 0) ->
  ~ y = Var 0 ->
  is_in_FOvar y (FOvars_in alpha) = false ->
  same_struc_BAT2 alpha (rename_FOv alpha x y) = true.
Proof.
  intros alpha x y Hnot Hin Hin2.
  unfold same_struc_BAT2.
  apply andb_true_iff.
  apply conj. apply same_struc_rename_FOv.
    case_eq (batm_paired alpha); intros H.
      rewrite batm_paired_rename_FOv_fwd.
      apply andb_true_r. assumption.

      assumption.

    case_eq (batm_paired (rename_FOv alpha x y) ); intros H2.
      apply batm_paired_rename_FOv_rev in H2. rewrite H in H2.
      discriminate.

      assumption. assumption.

      apply andb_true_r.
Qed.


(*
  intros alpha x y; destruct x as [xn]; destruct y as [ym].
  induction alpha. 
    destruct p as [Pn]; destruct f as [z1]. simpl.
    case (beq_nat xn z1); simpl; 
    unfold same_struc_BAT2; simpl;
    apply andb_true_iff; apply conj; symmetry. 
      apply beq_nat_refl. reflexivity.
      apply beq_nat_refl. reflexivity.

    destruct f as [z1]; destruct f0 as [z2].
    simpl. case (beq_nat xn z1); case (beq_nat xn z2);
    reflexivity.

    destruct f as [z1]; destruct f0 as [z2].
    simpl. case (beq_nat xn z1); case (beq_nat xn z2);
    reflexivity.

    destruct f as [zn]. simpl.
    case (beq_nat zn xn); simpl. 
      unfold same_struc_BAT2.
      apply andb_true_iff.
      apply andb_true_iff in IHalpha.
      destruct IHalpha as [IH1 IH2].
      apply conj. simpl. assumption.
      apply andb_true_iff in IH2.
      apply andb_true_iff.
      destruct IH2 as [IH2 IH3].
      apply conj.
        simpl in IH2. simpl. destruct alpha; try assumption;
        try reflexivity.
        destruct f.
 simpl.
      destruct alpha; try discriminate.
  simpl. ; assumption.

    destruct f as [zn]. simpl.
    case (beq_nat zn xn); simpl; assumption.

    simpl. assumption.

    simpl. unfold rename_FOv in *.
    rewrite IHalpha1. rewrite IHalpha2.
    reflexivity.

    simpl. unfold rename_FOv in *.
    rewrite IHalpha1. rewrite IHalpha2.
    reflexivity.

    simpl. unfold rename_FOv in *.
    rewrite IHalpha1. rewrite IHalpha2.
    reflexivity.

    simpl. destruct p. rewrite <- beq_nat_refl.
    assumption.

    simpl. destruct p. rewrite <- beq_nat_refl.
    assumption.
Qed.
*)

(* Fixpoint max_FOv_l (l : list FOvariable) : nat :=
  match l with
  | nil => 0
  | cons x l' => match x with Var xn => 
    max xn (max_FOv_l l') end
  end. *)

Lemma max_FOv_list_closed_exFO : forall l alpha,
  max_FOv (list_closed_exFO alpha l) =
  max (max_FOv alpha) (max_FOv_l l).
Proof.
  induction l; intros alpha.
    simpl. symmetry. apply PeanoNat.Nat.max_0_r.

    simpl. destruct a as [ym].
    rewrite IHl.
    rewrite (PeanoNat.Nat.max_assoc _ ym).
    rewrite (max_comm _ ym).
    rewrite <- PeanoNat.Nat.max_assoc.
    reflexivity.
Qed.



Lemma max_FOv_l_FOvars_in : forall alpha,
  max_FOv_l (FOvars_in alpha) =   max_FOv alpha.
Proof.
  induction alpha;
    try (    simpl; rewrite max_FOv_l_app; rewrite IHalpha1; rewrite IHalpha2;
    reflexivity);
    try (    simpl; assumption).
    destruct f. simpl. apply PeanoNat.Nat.max_0_r.

    destruct f. destruct f0. simpl. rewrite PeanoNat.Nat.max_0_r.
    reflexivity.

    destruct f. destruct f0. simpl. rewrite PeanoNat.Nat.max_0_r.
    reflexivity.

    destruct f. simpl. rewrite IHalpha. reflexivity.

    destruct f. simpl. rewrite IHalpha. reflexivity.
Qed.


Lemma shouldbeeasy : forall l l2 l3 zn,
is_in_FOvar (Var (S (Nat.max (max_FOv_l l2)
           (Nat.max zn (Nat.max (max_FOv_l l) l3))))) l= false.
Proof.
Admitted.

Lemma shouldbeeasy4 : forall l n xn,
is_in_FOvar (Var (S (Nat.max n (Nat.max xn (max_FOv_l l)))))
  l = false.
Admitted.

Lemma same_struc_BAT2_rename_FOv_max_conj : forall alpha gamma x,
  ~ x = (Var 0) ->
  same_struc_BAT2 alpha (rename_FOv_max_conj alpha gamma x) = true.
Proof.
  intros.
  apply same_struc_BAT2_rename_FOv.
  assumption.

discriminate.

  simpl. destruct x as [xn].
  rewrite <- (max_FOv_l_FOvars_in alpha). 
  apply shouldbeeasy4.
Qed.

Lemma same_struc_BAT2_comm : forall alpha beta,
  same_struc_BAT2 alpha beta = true ->
  same_struc_BAT2 beta alpha = true.
Proof.
  intros alpha beta H.
  unfold same_struc_BAT2 in *.
  apply andb_true_iff.
  apply andb_true_iff in H.
  destruct H as [H1 H2].
  apply conj. apply same_struc_comm. assumption.
  apply andb_true_iff.
  apply andb_true_iff in H2.
  destruct H2 as [H2 H3].
  apply conj; assumption.
Qed.

Lemma same_struc_BAT2_rename_FOv_max_conj_list_closed_exFO : forall lv alpha beta x,
  ~ x = Var 0 ->
  same_struc_BAT2 (rename_FOv_max_conj (list_closed_exFO alpha lv) beta x)
             (list_closed_exFO (rename_FOv_max_conj alpha beta x) lv) = true.
Proof.
  induction lv; intros alpha beta x Hnot.
    simpl in *.
    apply same_struc_BAT2_refl.

    simpl.
    assert (same_struc_BAT2 (rename_FOv_max_conj (exFO a (list_closed_exFO alpha lv)) beta x)
              (exFO x ((rename_FOv_max_conj (list_closed_exFO alpha lv) beta x)))=true) as H3.
      pose proof (same_struc_BAT2_rename_FOv_max_conj (exFO a (list_closed_exFO alpha lv))
          beta x Hnot) as H3.
      apply same_struc_BAT2_trans with (beta := exFO a (list_closed_exFO alpha lv)).
        apply same_struc_BAT2_comm. assumption.
        apply same_struc_BAT2_rename_FOv_max_conj. assumption.

    apply same_struc_BAT2_trans with 
      (beta := (exFO x (rename_FOv_max_conj (list_closed_exFO alpha lv) beta x))).  
      assumption.
    simpl.
    apply IHlv. assumption.
Qed.

Lemma same_struc_BAT2_strip_exFO : forall n alpha beta,
  same_struc_BAT2 alpha beta = true ->
  same_struc_BAT2 (strip_exFO alpha n) (strip_exFO beta n) = true.
Proof.
  induction n; intros alpha beta H.
    do 2 rewrite strip_exFO_0.
    assumption.

    destruct alpha; destruct beta; simpl in *; try discriminate;
      try assumption.
    apply IHn.
    assumption.
Qed.

Lemma same_struc_BAT2_strip_exFO_list_closed : forall l alpha,
  same_struc_BAT2 alpha (strip_exFO (list_closed_exFO alpha l) 
      (length l)) = true.
Proof.
  induction l; intros alpha.
    simpl.
    rewrite strip_exFO_0.
    apply same_struc_BAT2_refl.

    simpl.
    apply IHl.
Qed.

Lemma rename_FOv_strip_exFO_list : forall lv alpha x y,
  strip_exFO_list (rename_FOv (list_closed_exFO alpha lv) x y) (length lv) =
  rename_FOv_list lv x y.
Proof.
  induction lv; intros alpha x y.
    simpl. apply strip_exFO_list_0.

    simpl in *. destruct x as [xn]. destruct a as [ym].
    case_eq (beq_nat xn ym); intros Hbeq;
      simpl; destruct y as [zn]; rewrite beq_nat_comm in Hbeq;
      rewrite Hbeq;
      simpl; rewrite <- (IHlv alpha (Var xn) (Var zn));
      reflexivity.
Qed.

Lemma is_in_FOvar_strip_exFO_list_pre : forall lv alpha xn ym,
is_in_FOvar (Var 0) lv = false ->
is_in_FOvar (Var 0) (strip_exFO_list (rename_FOv_n
   (list_closed_exFO alpha lv) (S xn) (S ym)) (length lv)) = false.
Proof.
  induction lv; intros alpha xn ym H.
    simpl in *. rewrite strip_exFO_list_0. reflexivity.

    simpl. destruct a as [zn].
    apply is_in_FOvar_cons_f in H. destruct H as [H H'].
    case_eq (beq_nat zn (S xn)); intros Hbeq. 
      simpl. apply IHlv. apply H.

      simpl. destruct zn. contradiction (H' eq_refl).
      apply IHlv. assumption.
Qed.

Lemma Var_not_eq : forall zn ym n,
Var (S zn) <> Var (S (Nat.max n (S (Nat.max zn ym)))).
Proof.
  intros zn ym n H.
  inversion H as [H'].
  rewrite PeanoNat.Nat.succ_max_distr in H'.
  rewrite (max_comm (S zn)) in H'.
  rewrite PeanoNat.Nat.max_assoc in H'.
  symmetry in H'. apply max_leb_r in H'.
  rewrite leb_suc_f in H'. discriminate.
Qed.

Lemma is_in_FOvar_strip_exFO_list : forall lv f beta alpha,
is_in_FOvar (Var 0) lv = false ->
  ~ f = Var 0 ->
is_in_FOvar (Var 0) (strip_exFO_list (rename_FOv_max_conj
   (list_closed_exFO alpha lv) beta f) (length lv)) = false.
Proof.
  induction lv; intros f beta alpha Hin Hnot.
    simpl in *. rewrite strip_exFO_list_0. reflexivity.

    simpl in *. destruct a as [ym]. destruct ym. discriminate.
    specialize (IHlv _ beta alpha Hin Hnot).
unfold rename_FOv_max_conj. simpl. destruct f as [zn]. 
    unfold rename_FOv_max_conj in IHlv. simpl in IHlv.
    case_eq (max_FOv (list_closed_exFO alpha lv)).
      intros H0. rewrite H0 in *. simpl in *.
      rewrite PeanoNat.Nat.max_0_r in *.
      destruct zn. contradiction (Hnot eq_refl). 
      case_eq (beq_nat ym zn); intros Hbeq; simpl in *;
        pose proof (rename_FOv_strip_exFO_list lv alpha (Var (S zn))
          (Var (S (Nat.max (max_FOv beta) (S (Nat.max zn ym)))))) as H;
        simpl in H; rewrite H;
        rewrite is_in_FOvar_rename_FOv_list; try assumption; try discriminate.
apply Var_not_eq.
apply Var_not_eq.

    intros n Hn. rewrite Hn in IHlv.
    simpl. destruct zn. contradiction (Hnot eq_refl). simpl.
    case_eq (beq_nat ym zn); intros Hbeq.
      simpl in *. apply is_in_FOvar_strip_exFO_list_pre. assumption.

      simpl. apply is_in_FOvar_strip_exFO_list_pre. assumption.
Qed.

Lemma same_struc_BAT2_rename_FOv_A_pre : forall n lv alpha beta,
  is_in_FOvar (Var 0) lv  = false ->
  same_struc_BAT2 alpha (rename_FOv_A_pre alpha beta lv n) = true.
Proof.
  induction n; intros lv alpha beta Hin.
    simpl. apply same_struc_BAT2_refl.

      simpl. destruct lv. apply same_struc_BAT2_refl.
apply is_in_FOvar_cons_f in Hin. destruct Hin as [Hin1 Hin2]. apply not_eq_sym in Hin2.
      specialize (IHn (strip_exFO_list (rename_FOv_max_conj (list_closed_exFO alpha lv) beta f)
        (length lv)) (strip_exFO (rename_FOv_max_conj (list_closed_exFO alpha lv) beta f)
        (length lv)) beta)  .
      assert (same_struc_BAT2 alpha (strip_exFO (rename_FOv_max_conj (list_closed_exFO alpha lv) beta f)
           (length lv)) =  true) as H.
        pose proof (same_struc_BAT2_rename_FOv_max_conj_list_closed_exFO
          lv alpha beta f) as H2.
        apply same_struc_BAT2_strip_exFO with (n := length lv) in H2.
        pose proof (same_struc_BAT2_strip_exFO_list_closed lv (rename_FOv_max_conj alpha beta f)) as H3.
        pose proof (same_struc_BAT2_trans _ _ _ (same_struc_BAT2_rename_FOv_max_conj _ _ _ Hin2)
               H3 ) as H4.
        apply same_struc_BAT2_comm in H2.
        apply (same_struc_BAT2_trans _ _ _ H4 H2). assumption.

      assert (same_struc_BAT2 alpha (strip_exFO (rename_FOv_max_conj (list_closed_exFO alpha lv) beta f)
           (length lv)) =  true) as H'.
        pose proof (same_struc_BAT2_rename_FOv_max_conj_list_closed_exFO
          lv alpha beta f) as H2.
        apply same_struc_BAT2_strip_exFO with (n := length lv) in H2.
        pose proof (same_struc_BAT2_strip_exFO_list_closed lv (rename_FOv_max_conj alpha beta f)) as H3.
        pose proof (same_struc_BAT2_trans _ _ _ (same_struc_BAT2_rename_FOv_max_conj _ _ _ Hin2)
               H3 ) as H4.
        apply same_struc_BAT2_comm in H2.
        apply (same_struc_BAT2_trans _ _ _ H4 H2). assumption.

assert (is_in_FOvar (Var 0) (strip_exFO_list (rename_FOv_max_conj (list_closed_exFO alpha lv) beta f) (length lv)) = false) as HH.

  apply is_in_FOvar_strip_exFO_list; assumption.
      apply (same_struc_BAT2_trans _ _ _ H (IHn HH)).

Qed.


(* Lemma same_struc_conjSO_ex_BAT : forall gamma alpha beta,
  same_struc_BAT gamma (conjSO alpha beta) = true ->
  existsT2 alpha' beta',
    gamma = conjSO alpha' beta' /\
    (BAT gamma = true <->
    BAT (conjSO alpha' beta') = true).
Proof.
  induction gamma; intros alpha beta H;
    try (simpl in *; discriminate).
admit.
admit.
admit.
admit.
admit.
admit.
    exists gamma1. exists gamma2. apply conj. reflexivity.
    apply iff_refl.
Defined.
 *)

Lemma strip_exFO_rename_FOv : forall l alpha x y,
  strip_exFO (rename_FOv (list_closed_exFO alpha l) x y) (length l) =
  rename_FOv alpha x y.
Proof.
  induction l; intros alpha x y.
    simpl. rewrite strip_exFO_0. reflexivity.

    simpl. unfold rename_FOv. destruct x as [xn].
    destruct y as [ym].  simpl. destruct a as [zn].
    case_eq (beq_nat zn xn); intros H;  
      simpl; unfold rename_FOv in IHl;
      apply (IHl alpha (Var xn) (Var ym)).
Qed.


Lemma strip_exFO_list_rename_FOv : forall l alpha x y ,
  strip_exFO_list (rename_FOv (list_closed_exFO alpha l) x y) (length l) =
  rename_FOv_list l x y.
Proof.
  induction l; intros alpha x y.
    simpl. apply strip_exFO_list_0.

    simpl. destruct x as [xn]. destruct y as [ym].
    destruct a as [zn]. simpl. rewrite beq_nat_comm.
    case_eq (beq_nat xn zn); intros Hbeq; simpl;
      unfold rename_FOv in IHl;   
      rewrite (IHl alpha (Var xn) (Var ym));
      reflexivity.
Qed.

Lemma is_BOXATM_flag_strong_CONJ_next_FOvar : forall alpha x1 x2 x3,
  is_BOXATM_flag_strong_CONJ (allFO x1 (implSO (relatSO x2 x3) alpha)) = true ->
  x3 = next_FOvar x2.
Proof.
  intros alpha [x1] [x2] [x3] H.
  simpl in H. unfold next_FOvar.
  destruct x1. discriminate.
  case_eq (beq_nat x3 (S x2)); intros Hbeq;
    rewrite Hbeq in *.  rewrite (beq_nat_true _ _ Hbeq).
    reflexivity.

    do 2 rewrite if_then_else_false in H.
    discriminate.
Qed.

Lemma rename_FOv_n_0 : forall alpha,
  rename_FOv_n alpha 0 0 = alpha.
Proof.
  induction alpha.
    destruct f as [xn]. destruct xn; reflexivity.

    destruct f as [xn]. destruct f0 as [ym]. simpl.
    destruct xn; destruct ym; reflexivity.

    destruct f as [xn]. destruct f0 as [ym]. simpl.
    destruct xn; destruct ym; reflexivity.

    destruct f as [xn]. destruct xn; simpl in *; rewrite IHalpha; reflexivity.

    destruct f as [xn]. destruct xn; simpl in *; rewrite IHalpha; reflexivity.

    simpl. rewrite IHalpha. reflexivity.

    simpl. rewrite IHalpha1. rewrite IHalpha2. reflexivity.

    simpl. rewrite IHalpha1. rewrite IHalpha2. reflexivity.
    
    simpl. rewrite IHalpha1. rewrite IHalpha2. reflexivity.

    simpl. rewrite IHalpha. reflexivity.

    simpl. rewrite IHalpha. reflexivity.
Qed.

Lemma BOXATM_flag_weak_allFO_eq : forall batm x1 x2 x3 x4,
  BOXATM_flag_weak (allFO x1 (implSO (relatSO x2 x3) batm)) x4 = true ->
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

Lemma BOXATM_flag_weak_BAT_num_conn : forall m n alpha x,
    n = num_conn alpha ->
  Nat.leb n m = true ->
  BOXATM_flag_weak alpha x = true ->
  BAT alpha = true.
Proof.
  induction m; intros n alpha [xn] Hnum Hleb Hb.
    destruct n. 2 : discriminate.
    destruct alpha; try discriminate. reflexivity.

    destruct n. 
    destruct alpha; try discriminate. reflexivity.

    destruct alpha; try discriminate.
    destruct alpha; try discriminate.
    destruct alpha1; try discriminate.
    apply BAT_allFO.
    apply conj.
      apply BOXATM_flag_weak_allFO_eq in Hb. assumption.

      apply BOXATM_flag_weak_allFO in Hb. assumption.
Qed.

Lemma BOXATM_flag_weak_BAT : forall alpha x,
  BOXATM_flag_weak alpha x = true ->
  BAT alpha = true.
Proof.
  intros alpha x. apply (BOXATM_flag_weak_BAT_num_conn (num_conn alpha)
    (num_conn alpha) _ _ eq_refl (leb_refl _ )).
Qed.

(* Left it here. 30/11/17.
Keep going! *)

Lemma lem_try2_BOX_num_conn : forall m n atm x y,
    n = num_conn atm ->
  Nat.leb n m = true ->
   ~ x = Var 0 ->
  is_in_FOvar y (FOvars_in atm) = false ->
  BOXATM_flag_weak atm (batm_comp_x1 atm) = true ->
  BOXATM_flag_weak (rename_FOv atm x y) (batm_comp_x1 (rename_FOv atm x y)) = true.
Proof.
  induction m; intros n atm [xn] [ym] Hnum Hleb Hin0 Hin Hb.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
    simpl in *. destruct f as [un].
    case_eq (beq_nat xn un); intros Hbeq.
      simpl; symmetry; apply beq_nat_refl.

      simpl. assumption.    

    destruct n.
    destruct atm; try discriminate.
    simpl in *. destruct f as [un].
    case_eq (beq_nat xn un); intros Hbeq.
      simpl; symmetry; apply beq_nat_refl.

      simpl. assumption.
    
    destruct atm; try discriminate.
    destruct atm; try discriminate.
    destruct atm1; try discriminate.
    rewrite <- BAT_BOXATM_flag_weak_allFO in Hb.
    pose proof (is_BOXATM_flag_strong_CONJ_allFO_eq_BAT _ _ _ _ Hb) as H1.
    rewrite BAT_BOXATM_flag_weak_allFO in Hb.
    rewrite H1 in *.
    destruct f1 as [z1]. destruct f0 as [z2].
(* simpl. case_eq (beq_nat xn 0); intros Hbeq. rewrite (beq_nat_true _ _ Hbeq) in *.
simpl in *. destruct z1. destruct z2. simpl. rewrite <- beq_nat_refl.
destruct ym. simpl in *. discriminate. simpl in *. *)


    simpl. case_eq (beq_nat z1 xn); intros Hbeq;
      case_eq (beq_nat xn z2); intros Hbeq2;
        rewrite beq_nat_comm; rewrite Hbeq;
        simpl; rewrite <- beq_nat_refl; try rewrite <- beq_nat_refl;
        simpl in Hb; do 2 rewrite <- beq_nat_refl in *;
        try rewrite <- (batm_comp_x1_rename_FOv_t atm2 (Var xn) (Var ym)).
        apply (IHm (num_conn atm2) atm2 (Var xn) (Var ym)).
reflexivity.

 simpl in *.
inversion Hnum as [Hnum']. rewrite Hnum' in *.
    apply leb_suc_l in Hleb. assumption. assumption.

    simpl in Hin. case_eq (is_in_FOvar (Var ym) (FOvars_in atm2)); intros Hin2;
      rewrite Hin2 in *. do 3 rewrite if_then_else_true in Hin. discriminate.
      reflexivity.

        pose proof (try3_BAT _ _ Hb) as Hb'.
        rewrite Hb'. rewrite (beq_nat_true _ _ Hbeq) in *.
        assumption.

assumption.

        pose proof (try3_BAT _ _ Hb) as Hb'.
        rewrite Hb'. rewrite (beq_nat_true _ _ Hbeq) in *.
        reflexivity.

        apply (IHm (num_conn atm2) atm2 (Var xn) (Var ym)).
reflexivity.

 simpl in *.
inversion Hnum as [Hnum']. rewrite Hnum' in *.
    apply leb_suc_l in Hleb. assumption.

assumption.

    simpl in Hin. case_eq (is_in_FOvar (Var ym) (FOvars_in atm2)); intros Hin2;
      rewrite Hin2 in *. do 3 rewrite if_then_else_true in Hin. discriminate.
      reflexivity.

        pose proof (try3_BAT _ _ Hb) as Hb'.
        rewrite Hb'. rewrite (beq_nat_true _ _ Hbeq) in *.
        assumption.
assumption.

        pose proof (try3_BAT _ _ Hb) as Hb'.
        rewrite Hb'. rewrite (beq_nat_true _ _ Hbeq) in *.
        reflexivity.

        rewrite <- (batm_comp_x1_rename_FOv_f atm2  (Var xn) (Var ym) (Var z1)).
        apply (IHm (num_conn atm2) atm2 (Var xn) (Var ym)).
reflexivity.
 simpl in *.
inversion Hnum as [Hnum']. rewrite Hnum' in *.
    apply leb_suc_l in Hleb. assumption.
assumption.

    simpl in Hin. case_eq (is_in_FOvar (Var ym) (FOvars_in atm2)); intros Hin2;
      rewrite Hin2 in *. do 3 rewrite if_then_else_true in Hin. discriminate.
      reflexivity.

        pose proof (try3_BAT _ _ Hb) as Hb'.
        rewrite Hb'. assumption.


apply beq_nat_false_FOv. rewrite beq_nat_comm. assumption.

        pose proof (try3_BAT _ _ Hb) as Hb'.
        rewrite Hb'. reflexivity.

        rewrite <- (batm_comp_x1_rename_FOv_f atm2  (Var xn) (Var ym) (Var z1)).
        apply (IHm (num_conn atm2) atm2 (Var xn) (Var ym)).
reflexivity.

 simpl in *.
inversion Hnum as [Hnum']. rewrite Hnum' in *.
    apply leb_suc_l in Hleb. assumption.

assumption.

    simpl in Hin. case_eq (is_in_FOvar (Var ym) (FOvars_in atm2)); intros Hin2;
      rewrite Hin2 in *. do 3 rewrite if_then_else_true in Hin. discriminate.
      reflexivity.

        pose proof (try3_BAT _ _ Hb) as Hb'.
        rewrite Hb'. assumption.

apply beq_nat_false_FOv. rewrite beq_nat_comm. assumption.

       pose proof (try3_BAT _ _ Hb) as Hb'.
        rewrite Hb'. reflexivity.
Qed.

Lemma lem_try2_BOX : forall atm x y,
   ~ x = Var 0 ->
  is_in_FOvar y (FOvars_in atm) = false ->
  BOXATM_flag_weak atm (batm_comp_x1 atm) = true ->
  BOXATM_flag_weak (rename_FOv atm x y) (batm_comp_x1 (rename_FOv atm x y)) = true.
Proof.
  intros atm x y. apply (lem_try2_BOX_num_conn (num_conn atm) (num_conn atm)).
  reflexivity. apply leb_refl.
Qed.

Lemma lem_try2_num_conn : forall m n atm x y,
    n = num_conn atm ->
  Nat.leb n m = true ->
  ~ x = Var 0 ->
  is_in_FOvar y (FOvars_in atm) = false ->
  BAT atm = true ->
  BAT (rename_FOv atm x y) = true.
Proof.
  induction m; intros n atm [xn] [ym] Hnum Hleb Hin0 Hin Hb; try discriminate.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
    unfold rename_FOv. destruct f as [zn].
    simpl in *.
    case_eq (beq_nat xn zn); intros Hbeq; reflexivity.

    destruct n.
    destruct atm; try discriminate.
    unfold rename_FOv. destruct f as [zn].
    simpl in *.
    case_eq (beq_nat xn zn); intros Hbeq; reflexivity.

    destruct atm; try discriminate.
    simpl.
    destruct f as [zn].
    rewrite BAT_BOXATM_flag_weak_allFO in Hb.
    apply (lem_try2_BOX _ (Var xn) (Var ym)) in Hb.
      simpl in Hb. case_eq (beq_nat zn xn); intros Hbeq;
        rewrite Hbeq in *; rewrite BAT_BOXATM_flag_weak_allFO.
        all : try assumption.


    rewrite rename_FOv_conjSO.
    apply BAT_conjSO_t. apply BAT_conjSO_t in Hb.
    destruct Hb as [Hb1 Hb2].
    apply conj.
      apply (IHm (num_conn atm1) atm1 (Var xn) (Var ym)).
      reflexivity.

        rewrite Hnum in Hleb. simpl in Hleb.
        apply leb_plus_take1 in Hleb. assumption.

assumption.

        apply is_in_FOvar_app_l in Hin. assumption.
assumption.

      apply (IHm (num_conn atm2) atm2 (Var xn) (Var ym)).
      reflexivity.

        rewrite Hnum in Hleb. simpl in Hleb.
        apply leb_plus_take2 in Hleb. assumption.

assumption.

        apply is_in_FOvar_app_r in Hin. assumption.

assumption.
Qed.

Lemma lem_try2 : forall atm x y,
  ~ x = Var 0 ->
  is_in_FOvar y (FOvars_in atm) = false ->
  BAT atm = true ->
  BAT (rename_FOv atm x y) = true.
Proof.
  intros atm x y.
  apply (lem_try2_num_conn (num_conn atm) (num_conn atm)).
  reflexivity. apply leb_refl.
Qed.


(*

pose proof (is_BOXATM_flag_strong_CONJ_next_FOvar _ _ _ _ Hb) as H1.
pose proof (is_BOXATM_flag_strong_CONJ_allFO_eq _ _ _ _ Hb) as H2.
pose proof (is_BOXATM_flag_strong__CONJ _ _ _ Hb) as H3.

simpl.
destruct xn. destruct z2. discriminate. simpl.
  destruct z1.  inversion H2 as [H2'].
  rewrite <- beq_nat_refl. simpl.
  case_eq (beq_nat z2 ym); intros Hbeq2.
    simpl in Hb. simpl in H1. rewrite H2' in *.
    rewrite <- beq_nat_refl in Hb. destruct z2. 2: discriminate.
    simpl in *. destruct ym;      discriminate.

    simpl in *. destruct z2. 2 : discriminate.
    destruct ym. discriminate. simpl in *.
    destruct zn. 2 : discriminate.
    destruct ym. discriminate.
    simpl in *.  
*)
(*
Lemma lem_try2_num_conn : forall m n atm x y,
    n = num_conn atm ->
  Nat.leb n m = true ->
  is_in_FOvar y (FOvars_in atm) = false ->
  is_BOXATM_flag_strong_CONJ atm = true ->
  is_BOXATM_flag_strong_CONJ 
    (rename_FOv atm x y) = true.
Proof.
  induction m; intros n atm [xn] [ym] Hnum Hleb Hin Hb; try discriminate.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
    unfold rename_FOv. destruct f as [zn].
    simpl in *.
    case_eq (beq_nat xn zn); intros Hbeq; reflexivity.

    destruct n.
    destruct atm; try discriminate.
    unfold rename_FOv. destruct f as [zn].
    simpl in *.
    case_eq (beq_nat xn zn); intros Hbeq; reflexivity.

    destruct atm; try discriminate.
    destruct f as [zn]. destruct zn. discriminate.
    destruct atm; try discriminate.
    destruct atm1; try discriminate.
    unfold rename_FOv.
    destruct f as [z1]; destruct f0 as [z2].

pose proof (is_BOXATM_flag_strong_CONJ_next_FOvar _ _ _ _ Hb) as H1.
pose proof (is_BOXATM_flag_strong_CONJ_allFO_eq _ _ _ _ Hb) as H2.
pose proof (is_BOXATM_flag_strong__CONJ _ _ _ Hb) as H3.

simpl.
destruct xn. destruct z2. discriminate. simpl.
  destruct z1.  inversion H2 as [H2'].
  rewrite <- beq_nat_refl. simpl.
  case_eq (beq_nat z2 ym); intros Hbeq2.
    simpl in Hb. simpl in H1. rewrite H2' in *.
    rewrite <- beq_nat_refl in Hb. destruct z2. 2: discriminate.
    simpl in *. destruct ym;      discriminate.

    simpl in *. destruct z2. 2 : discriminate.
    destruct ym. discriminate. simpl in *.
    destruct zn. 2 : discriminate.
    destruct ym. discriminate.
    simpl in *.  


 rewrite H1 in *. rewrite H2 in *. simpl.
case_eq (beq_nat xn z1); intros Hbeq.
  case_eq (beq_nat xn z2); intros Hbeq2.
    rewrite (beq_nat_true _ _ Hbeq2) in *.
    rewrite (beq_nat_true _ _ Hbeq) in *.
    unfold next_FOvar in H1. inversion H1 as [H0].
    contradiction (n_Sn _ H0). destruct xn.
    rewrite <- (beq_nat_true _ _ Hbeq) in *. simpl.
    destruct ym. rewrite rename_FOv_n_0. apply H3.

    simpl in Hb.  simpl in Hin. destruct ym.
    simpl in *. discriminate. simpl in Hin.
    destruct z1. 2 : discriminate.
    destruct z2. discriminate.
    simpl in *. destruct z2. 2 : discriminate.
    destruct zn. 2 : discriminate.
    
    discriminate. 
*)
(*
destruct atm2; simpl. simpl.
Search not S.
    discriminate.
    inversion H1.
    destruct xn.  
    simpl.
Search is_BOXATM_flag_strong_CONJ BOXATM_flag_strong.
pose proof (is_BOXATM_flag_strong_CONJ _ _ _ _ Hb) as H3.

 simpl rename_FOv_n.
    case_eq (beq_nat xn z1); intros Hbeq.
      case_eq (beq_nat xn z2); intros Hbeq2.
        rewrite (beq_nat_true _ _ Hbeq2) in *.
        rewrite (beq_nat_true _ _ Hbeq) in *.
        simpl in Hb. rewrite (beq_nat_comm z1) in Hb.
        rewrite one_suc in Hb. rewrite beq_nat_suc_false in Hb.
        do 2 rewrite if_then_else_false in Hb. discriminate.

        destruct xn. simpl.
        destruct z2. discriminate.
        simpl in Hb.
        case_eq (beq_nat zn z2); intros Hbeq3;
          rewrite Hbeq3 in *.
          simpl in Hin.
         
Search beq_nat S false.
        destruct z1. simpl in *. rewrite if_then_else_false in Hb.
        discriminate.
        
Search is_BOXATM_flag_strong_CONJ allFO.
    destruct xn. simpl.
    
*)

(* Lemma lem_try2 : forall atm x y,
  is_in_FOvar y (FOvars_in atm) = false ->
  is_BOXATM_flag_strong_CONJ atm = true ->
  is_BOXATM_flag_strong_CONJ 
    (rename_FOv atm x y) = true.
Proof.
  induction atm; intros x y Hin Hb; try discriminate.
    unfold rename_FOv. destruct x as [xn]. 
    destruct y as [ym]. destruct f as [zn].
    simpl in *.
    case_eq (beq_nat xn zn); intros Hbeq; reflexivity.

    destruct f as [xn]. destruct xn. discriminate.
    destruct atm; try discriminate. simpl in *.
Admitted.
 *)

Lemma BOXATM_flag_weak_rename_FOv : forall atm x y,
  is_in_FOvar y (FOvars_in atm) = false ->
  BOXATM_flag_weak atm (batm_comp_x1 atm) = true ->
  BOXATM_flag_weak (rename_FOv atm x y) (batm_comp_x1 (rename_FOv atm x y)) = true.
Proof.
Admitted.

Lemma BAT_rename_FOv_num_conn : forall m n atm x y,
    n = num_conn atm ->
  Nat.leb n m = true ->
  is_in_FOvar y (FOvars_in atm) = false ->
  is_in_FOvar (Var 0) (FOvars_in atm) = false ->
  BAT atm = true ->
  BAT (rename_FOv atm x y) = true.
Proof.
  induction m; intros n atm x y Hnum Hleb Hin Hin2 Hb.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
    destruct y as [ym]. destruct f as [zn].
    destruct x as [xn].
    simpl in *. case_eq (beq_nat xn zn); intros Hbeq; reflexivity.

    destruct n.
    destruct atm; try discriminate.
    destruct y as [ym]. destruct f as [zn].
    destruct x as [xn].
    simpl in *. case_eq (beq_nat xn zn); intros Hbeq; reflexivity.

    destruct atm; try discriminate.
    destruct atm; try discriminate.
    destruct atm1; try discriminate.  
    pose proof Hb as Hb'.
    apply BAT_allFO in Hb.
    destruct f as [zn]. destruct x as [xn]. destruct y as [ym].
    destruct f0 as [z1]; destruct f1 as [z2].
    simpl. destruct Hb as [Hb1 Hb2].
    case_eq (beq_nat zn xn); intros Hbeq.
      case_eq (beq_nat xn z1); intros Hbeq2.
        case_eq (beq_nat xn z2); intros Hbeq3.
          apply BAT_allFO. apply conj. reflexivity.
          pose proof Hb2 as Hb2'.
          apply try3_BAT in Hb2. apply batm_comp_x1_rename_FOv_t  with (y := (Var ym)) in Hb2.
(*           pose proof Hb2 as Hb2'. *)
          rewrite <- Hb2. simpl.
          pose proof (BOXATM_flag_weak_rename_FOv atm2 (Var xn) (Var ym)) as H.
          simpl in H. rewrite (beq_nat_true _ _ Hbeq) in *. apply H.

          simpl in *. case_eq (is_in_FOvar (Var ym) (FOvars_in atm2)); intros HH;   
            rewrite HH in *. do 3 rewrite if_then_else_true in Hin. discriminate.
            reflexivity.

          pose proof Hb2' as Hb2''.
          apply try3_BAT in Hb2'. rewrite Hb2'.
          assumption.

          simpl in Hin2. destruct zn; discriminate.

          rewrite (beq_nat_true _ _ Hbeq) in *.
          apply beq_nat_false_FOv in Hbeq3. contradiction (Hbeq3 Hb1).

        case_eq (beq_nat xn z2); intros Hbeq3.
          apply BAT_allFO. apply conj. reflexivity.
          pose proof Hb2 as Hb2'.
          apply try3_BAT in Hb2.  
          rewrite (beq_nat_true _ _ Hbeq) in *.
          rewrite <- (batm_comp_x1_rename_FOv_t atm2 (Var xn) (Var ym)).
          apply (BOXATM_flag_weak_rename_FOv _ (Var xn) (Var ym)).
admit.
          rewrite <- Hb2 in Hb2'. all : try assumption.
admit.

        inversion Hb1 as [Hb1']. rewrite Hb1' in *. 
        rewrite <- (beq_nat_true _ _ Hbeq) in *.
        rewrite <- beq_nat_refl in Hbeq3. discriminate.

      case_eq (beq_nat xn z1); intros Hbeq2.
        case_eq (beq_nat xn z2); intros Hbeq3.
          rewrite (beq_nat_true _ _ Hbeq3) in *.
          inversion Hb1 as [Hb1'].
          rewrite Hb1' in *. rewrite <- beq_nat_refl in *.
          discriminate.

          apply BAT_allFO.
          apply conj. assumption.
          pose proof Hb2 as Hb2'.
          apply try3_BAT in Hb2.  
          rewrite <- (batm_comp_x1_rename_FOv_f atm2 (Var xn) (Var ym) (Var zn)).
          apply (BOXATM_flag_weak_rename_FOv _ (Var xn) (Var ym)).
admit.
          rewrite Hb2. assumption.
          intros HH. inversion HH as [HH']. rewrite HH' in *.
          rewrite <- beq_nat_refl in *. discriminate.
          assumption.

          inversion Hb1 as [Hb1']. rewrite <- Hb1'.
          rewrite beq_nat_comm. rewrite Hbeq. 
          apply BAT_allFO. apply conj. reflexivity.

          pose proof Hb2 as Hb2'.
          apply try3_BAT in Hb2.  
          rewrite <- (batm_comp_x1_rename_FOv_f atm2 (Var xn) (Var ym) (Var zn)).
          apply (BOXATM_flag_weak_rename_FOv _ (Var xn) (Var ym)).
admit.
          rewrite Hb2. assumption.
          intros HH. inversion HH as [HH']. rewrite HH' in *.
          rewrite <- beq_nat_refl in *. discriminate.
          assumption.

      rewrite rename_FOv_conjSO.
      apply BAT_conjSO_fwd in Hb. destruct Hb.
      simpl. rewrite (IHm (num_conn atm1) atm1).
      apply (IHm (num_conn atm2) atm2).
      all : try reflexivity.
      all : try assumption.
      
admit.
admit.
admit.
admit.
admit.
admit.
Admitted. (* Easy *)

Lemma BAT_rename_FOv : forall atm x y,
  is_in_FOvar y (FOvars_in atm) = false ->
  is_in_FOvar (Var 0) (FOvars_in atm) = false ->
  BAT atm = true ->
  BAT (rename_FOv atm x y) = true.
Proof.
  intros atm x y .
  apply (BAT_rename_FOv_num_conn (num_conn atm) (num_conn atm)).
  reflexivity. apply leb_refl.
Qed.


Lemma is_in_FOvar_leb_max_FOv_l : forall l xn,
  is_in_FOvar (Var xn) l = true ->
  Nat.leb xn (max_FOv_l l) = true.
Proof.
  induction l; intros xn H. discriminate.
  simpl in *. destruct a as [ym].
  case_eq (beq_nat xn ym); intros Hbeq; rewrite Hbeq in *.
    rewrite (beq_nat_true _ _ Hbeq).
    apply leb_max_suc3. apply leb_refl.

    rewrite max_comm. apply leb_max_suc3.
    apply IHl. assumption.
Qed.

(* Search max_FOv list_closed_exFO. max_FOv_list_closed_exFO *)
Lemma lem_try_pre_pre : forall l n m a,
  is_in_FOvar (Var (S (max n (max m (max (max_FOv_l l) a))))) l = false.
Proof.
  intros l n m a.
  case_eq (is_in_FOvar (Var (S (Nat.max n (Nat.max m (Nat.max (max_FOv_l l) a))))) l );
    intros H. 2 : reflexivity.
  apply is_in_FOvar_leb_max_FOv_l in H.
  remember (max_FOv_l l) as t.
  simpl in H. destruct t. discriminate.
  apply leb_max in H.
  destruct H as [H1 H2].
  apply leb_max in H2. destruct H2 as [H2 H3].
  rewrite max_comm in H3. rewrite leb_max_suc in H3.
  discriminate.
Qed.

Lemma lem_try_pre : forall atm2 lv2 rel1 zn,
is_in_FOvar (Var (S (Nat.max (max_FOv rel1) (Nat.max zn (max_FOv (list_closed_exFO atm2 lv2)))))) (FOvars_in atm2) =
false.
Proof.
  intros. rewrite max_FOv_list_closed_exFO. rewrite <- (max_FOv_l_FOvars_in atm2).
  apply lem_try_pre_pre.
Qed.

Lemma FOvars_in_rename_FOv : forall alpha x y,
  FOvars_in (rename_FOv alpha x y) =
  rename_FOv_list (FOvars_in alpha) x y.
Proof.
  induction alpha; intros [xn] [ym].
    simpl. destruct f as [zn]. simpl.
    case_eq (beq_nat xn zn); intros Hbeq; reflexivity.

    destruct f as [z1]; destruct f0 as [z2].
    simpl in *. case_eq (beq_nat xn z1); intros Hbeq;
      case_eq (beq_nat xn z2); intros Hbeq2;
        reflexivity.

    destruct f as [z1]; destruct f0 as [z2].
    simpl in *. case_eq (beq_nat xn z1); intros Hbeq;
      case_eq (beq_nat xn z2); intros Hbeq2;
        reflexivity.

    destruct f as [zn]. simpl.
    case_eq (beq_nat zn xn); intros Hbeq;
      rewrite beq_nat_comm; rewrite Hbeq; simpl;
      rewrite <- (IHalpha (Var xn) (Var ym)); reflexivity.

    destruct f as [zn]. simpl.
    case_eq (beq_nat zn xn); intros Hbeq;
      rewrite beq_nat_comm; rewrite Hbeq; simpl;
      rewrite <- (IHalpha (Var xn) (Var ym)); reflexivity.

    simpl. apply (IHalpha (Var xn) (Var ym)).

    rewrite rename_FOv_conjSO.
    simpl. rewrite rename_FOv_list_app.
    rewrite <- (IHalpha1 (Var xn) (Var ym)).
    rewrite <- (IHalpha2 (Var xn) (Var ym)).
    reflexivity.

    rewrite rename_FOv_disjSO.
    simpl. rewrite rename_FOv_list_app.
    rewrite <- (IHalpha1 (Var xn) (Var ym)).
    rewrite <- (IHalpha2 (Var xn) (Var ym)).
    reflexivity.

    rewrite rename_FOv_implSO.
    simpl. rewrite rename_FOv_list_app.
    rewrite <- (IHalpha1 (Var xn) (Var ym)).
    rewrite <- (IHalpha2 (Var xn) (Var ym)).
    reflexivity.

    simpl. apply (IHalpha (Var xn) (Var ym)).

    simpl. apply (IHalpha (Var xn) (Var ym)).
Qed.

Lemma is_in_FOvar_rename_FOv_list2 : forall l x y z,
  ~ x = y ->
  ~ x = z ->
  is_in_FOvar x (rename_FOv_list l y z) =
  is_in_FOvar x l.
Proof.
  intros l [xn] [ym] [zn] Hneq1 Hneq.
  case_eq (beq_nat ym zn); intros Hbeq2.
    rewrite (beq_nat_true _ _ Hbeq2). rewrite rename_FOv_list_refl.
    reflexivity.

    apply is_in_FOvar_rename_FOv_list.
    apply beq_nat_false_FOv.
    apply FOvar_neq. assumption.
    assumption. apply beq_nat_false_FOv.
    assumption.
Qed.

Lemma is_in_FOvar_lem_try : forall atm2 x n ,
is_in_FOvar (Var 0) (FOvars_in atm2) = false ->
is_in_FOvar (Var 0)
  (FOvars_in  (rename_FOv atm2 x
        (Var (S n)))) = false.
Proof.
  intros atm2 x n.
  rewrite  FOvars_in_rename_FOv.
  intros H.
  destruct x as [xn]. destruct xn.
  apply is_in_FOvar_rename. discriminate.

    rewrite is_in_FOvar_rename_FOv_list2. assumption.
    discriminate. discriminate.
Qed.

(* Lemma is_in_FOvar_rename_FOv_list : forall l x n,
is_in_FOvar (Var 0) l = false ->
is_in_FOvar (Var 0) (rename_FOv_list l x (Var (S n))) = false.
Proof.
  Locate is_in_FOvar_rename_FOv_list.
pose proof vsSahlq_instant9.is_in_FOvar_rename_FOv_list.

  induction atm2; intros x n Hin.
    
Admitted.
 *)
Lemma lem_try : forall n lv2 atm2 atm2' rel1,
REL rel1 = true ->
is_in_FOvar (Var 0) (FOvars_in atm2) = false ->
rename_FOv_A_pre atm2 rel1 lv2 n =  atm2' ->
BAT atm2 = true ->
BAT atm2' = true.
Proof.
  induction n; intros lv2 atm2 atm2' rel1 Hrel Hin H Hb.
    simpl in *. rewrite H in *. assumption.

    destruct lv2. simpl in *. rewrite H in *. assumption.
    simpl in H. unfold rename_FOv_max_conj in H.
    rewrite strip_exFO_rename_FOv in H.
    rewrite strip_exFO_list_rename_FOv in H.
    simpl in *. destruct f as [zn].
    rewrite <- H.
    apply (IHn (rename_FOv_list lv2 (Var zn)
        (Var (S (Nat.max (max_FOv rel1) (Nat.max zn (max_FOv (list_closed_exFO atm2 lv2)))))))
     (rename_FOv atm2 (Var zn) (Var (S (Nat.max (max_FOv rel1) 
        (Nat.max zn (max_FOv (list_closed_exFO atm2 lv2))))))) _ rel1); try assumption.
apply is_in_FOvar_lem_try. assumption.

reflexivity.
apply BAT_rename_FOv. apply lem_try_pre. assumption. assumption.
Qed.

(* Lemma lem_try : forall n lv2 atm2 atm2' rel1,
REL rel1 = true ->
rename_FOv_A_pre atm2 rel1 lv2 n =  atm2' ->
is_BOXATM_flag_strong_CONJ atm2 = true ->
is_BOXATM_flag_strong_CONJ atm2' = true.
Proof.
  induction n; intros lv2 atm2 atm2' rel1 Hrel H Hb.
    simpl in *. rewrite H in *. assumption.

    destruct lv2. simpl in *. rewrite H in *. assumption.
    simpl in H. unfold rename_FOv_max_conj in H.
    rewrite strip_exFO_rename_FOv in H.
    rewrite strip_exFO_list_rename_FOv in H.
    simpl in *. destruct f as [zn].
    apply (IHn _ _ _ _ Hrel H).
is_BOXATM_flag_weak_CONJ
    apply lem_try2.
      rewrite max_FOv_list_closed_exFO.
      do 2 rewrite <- max_FOv_l_FOvars_in.
      apply shouldbeeasy.

assumption.
Qed. *)

Lemma rename_FOv_rel : forall rel x y,
REL rel = true ->
REL (rename_FOv rel x y) = true.
Proof.
  induction rel ; intros x y H; try discriminate.
    destruct f as [y1]; destruct f0 as [y2].
    destruct x as [x1]. destruct y as [x2].
    simpl in *.
    case_eq (beq_nat x1 y1); intros Hbeq;
      case_eq (beq_nat x1 y2); intros Hbeq2;
        reflexivity.

    rewrite rename_FOv_conjSO. simpl.
    rewrite IHrel1. apply IHrel2.
      apply REL_conjSO_r in H. assumption.
      apply REL_conjSO_l in H. assumption.
Qed.

Lemma shouldbeeasy3 : forall l a b c d,
is_in_FOvar (Var (S (Nat.max a (Nat.max b (Nat.max (Nat.max c (max_FOv_l l)) d)))))
  l = false.
Proof.
  intros l a b c d.
  case_eq (is_in_FOvar (Var (S (Nat.max a (Nat.max b (Nat.max (Nat.max c (max_FOv_l l)) d))))) l);
    intros H. 2 : reflexivity.
  apply is_in_FOvar_leb_max_FOv_l in H.
  remember (max_FOv_l l) as t.
  simpl in H. destruct t. discriminate.
  apply leb_max in H.
  destruct H as [H1 H2].
  apply leb_max in H2. destruct H2 as [H2 H3].
  rewrite max_comm in H3.
  apply leb_max in H3. destruct H3 as [H3 H4]. rewrite leb_max_suc in H4.
  discriminate.
Qed.

Lemma shouldbeeasy2 : forall rel1 atm2 rel2 lv2 zn,
is_in_FOvar (Var (S (Nat.max (max_FOv rel1)
           (Nat.max zn (max_FOv (list_closed_exFO (conjSO rel2 atm2) lv2))))))
  (FOvars_in atm2) = false.
Proof.
  intros rel1 atm2 rel2 lv2 zn.
  rewrite max_FOv_list_closed_exFO. simpl.
  rewrite <- (max_FOv_l_FOvars_in atm2).
  apply shouldbeeasy3.
Qed.

(* Lemma lem_try3 : forall n lv2 atm2 atm2' rel1 rel2 rel2',
REL rel1 = true ->
REL rel2 = true ->
REL rel2' = true ->
rename_FOv_A_pre (conjSO rel2 atm2) rel1 lv2 n = conjSO rel2' atm2' ->
is_BOXATM_flag_strong_CONJ atm2 = true ->
is_BOXATM_flag_strong_CONJ atm2' = true.
Proof.
  induction n; intros lv2 atm2 atm2' rel1 rel2 rel2' Hrel1 Hrel2 Hrel2' H Hb.
    simpl in *. inversion H as [[H1 H2]]. rewrite H2 in *. assumption.

    destruct lv2.
    simpl in *. inversion H as [[H1 H2]]. rewrite H2 in *. assumption.
    simpl in H. unfold rename_FOv_max_conj in H.
    rewrite strip_exFO_rename_FOv in H.
    rewrite strip_exFO_list_rename_FOv in H.
    simpl in *. destruct f as [zn].
    rewrite rename_FOv_conjSO in H.

    apply (IHn (rename_FOv_list lv2 (Var zn)
         (Var
            (S
               (Nat.max (max_FOv rel1)
                  (Nat.max zn (max_FOv (list_closed_exFO (conjSO rel2 atm2) lv2))))))) (rename_FOv atm2 (Var zn)
            (Var
               (S
                  (Nat.max (max_FOv rel1)
                     (Nat.max zn (max_FOv (list_closed_exFO (conjSO rel2 atm2) lv2))))))) _ _ (rename_FOv rel2 (Var zn) (Var (S
                  (Nat.max (max_FOv rel1) (Nat.max zn 
                  (max_FOv (list_closed_exFO (conjSO rel2 atm2) lv2)))))))
                   _ Hrel1 (rename_FOv_rel _ _ _ Hrel2) Hrel2').

assumption.
apply lem_try2_BOX.
      apply shouldbeeasy2. assumption.
Qed. *)

Lemma lem_try3_BAT : forall n lv2 atm2 atm2' rel1 rel2 rel2',
is_in_FOvar (Var 0) lv2 = false ->
REL rel1 = true ->
REL rel2 = true ->
REL rel2' = true ->
rename_FOv_A_pre (conjSO rel2 atm2) rel1 lv2 n = conjSO rel2' atm2' ->
BAT atm2 = true ->
BAT atm2' = true.
Proof.
  induction n; intros lv2 atm2 atm2'  rel1 rel2 rel2' Hin0 Hrel1 Hrel2 Hrel2' H Hb.
    simpl in *. inversion H as [[H1 H2]]. rewrite H2 in *. assumption.

    destruct lv2.
    simpl in *. inversion H as [[H1 H2]]. rewrite H2 in *. assumption.
    simpl in H. unfold rename_FOv_max_conj in H.
    rewrite strip_exFO_rename_FOv in H.
    rewrite strip_exFO_list_rename_FOv in H.
    simpl in *. destruct f as [zn].
    rewrite rename_FOv_conjSO in H.

    assert (is_in_FOvar (Var 0)
   (rename_FOv_list lv2 (Var zn)
      (Var (S (Nat.max (max_FOv rel1) (Nat.max zn (max_FOv (list_closed_exFO (conjSO rel2 atm2) lv2))))))) =
      false) as Hass.

    destruct zn. discriminate.
    rewrite is_in_FOvar_rename_FOv_list2. assumption. discriminate. discriminate.

    apply (IHn (rename_FOv_list lv2 (Var zn)
         (Var
            (S
               (Nat.max (max_FOv rel1)
                  (Nat.max zn (max_FOv (list_closed_exFO (conjSO rel2 atm2) lv2))))))) (rename_FOv atm2 (Var zn)
            (Var
               (S
                  (Nat.max (max_FOv rel1)
                     (Nat.max zn (max_FOv (list_closed_exFO (conjSO rel2 atm2) lv2))))))) _ _ (rename_FOv rel2 (Var zn) (Var (S
                  (Nat.max (max_FOv rel1) (Nat.max zn 
                  (max_FOv (list_closed_exFO (conjSO rel2 atm2) lv2)))))))
                   _ Hass Hrel1 (rename_FOv_rel _ _ _ Hrel2) Hrel2').

assumption.
apply lem_try2.
destruct zn; discriminate.

      apply shouldbeeasy2. assumption.
Qed.

Lemma same_struc_rename_FOv_A_pre : forall n lv alpha beta,
  is_in_FOvar (Var 0) lv = false ->
  same_struc_BAT2 alpha (rename_FOv_A_pre alpha beta lv n) = true.
Proof.
  induction n; intros lv alpha beta Hin.
    simpl. apply same_struc_BAT2_refl.

    induction lv.
      simpl. apply same_struc_BAT2_refl.

      simpl.
      simpl in Hin. destruct a as [ym]. remember (Var ym) as a.
      destruct ym. discriminate.
      assert (~ a = Var 0) as Hass.
        rewrite Heqa. discriminate.
      specialize (IHn (strip_exFO_list (rename_FOv_max_conj (list_closed_exFO alpha lv) beta a)
        (length lv)) (strip_exFO (rename_FOv_max_conj (list_closed_exFO alpha lv) beta a)
        (length lv)) beta)  .
      assert (same_struc_BAT2 alpha (strip_exFO (rename_FOv_max_conj (list_closed_exFO alpha lv) beta a)
           (length lv)) =  true) as H.
        pose proof (same_struc_BAT2_rename_FOv_max_conj_list_closed_exFO
          lv alpha beta a) as H2.
        apply same_struc_BAT2_strip_exFO with (n := length lv) in H2.
        pose proof (same_struc_BAT2_strip_exFO_list_closed lv (rename_FOv_max_conj alpha beta a)) as H3.
        pose proof (same_struc_BAT2_trans _ _ _ (same_struc_BAT2_rename_FOv_max_conj _ _ _ Hass)
               H3 ) as H4.
        apply same_struc_BAT2_comm in H2.
        apply (same_struc_BAT2_trans _ _ _ H4 H2). assumption.

assert (is_in_FOvar (Var 0) (strip_exFO_list (rename_FOv_max_conj (list_closed_exFO alpha lv) beta a) (length lv)) =
 false) as Hass2.
unfold rename_FOv_max_conj.
  rewrite strip_exFO_list_rename_FOv. rewrite is_in_FOvar_rename_FOv_list2. assumption.
    rewrite Heqa. discriminate. discriminate.

      apply (same_struc_BAT2_trans _ _ _ H (IHn Hass2)).
Qed.

Lemma same_struc_BAT2_rename_FOv_A : forall alpha beta lv,
  is_in_FOvar (Var 0) lv = false ->
  same_struc_BAT2 (rename_FOv_A alpha beta lv) alpha = true.
Proof.
  intros alpha beta lv Hin. unfold rename_FOv_A.
  apply same_struc_BAT2_comm.
(*   destruct (nlist_list_ex (length lv) lv eq_refl) as [ln Heq].
  rewrite <- Heq. *)
  apply same_struc_BAT2_rename_FOv_A_pre. assumption.
Qed.

(* Lemma lemsum : forall x y,
  eqFO (Var 1) (Var 1) = (x y). *)
(* Let x := (Var 2).
Let y1 := Var 3.
Let y2 := Var 2.
Let z := Var 2.
Let P := Pred 1.
Let y2' := Var 4.
Let z' := Var 5.
Let alpha1 := allFO x (implSO (relatSO y1 y2) (predSO P z)).
Let alpha2 := allFO x (implSO (relatSO y1 y2') (predSO P z')).
Let beta1 := alpha2.
Let beta2 := alpha1.
Eval compute in (same_struc_BAT2 (conjSO alpha1 alpha2) (conjSO beta1 beta2)).
Eval compute in (BAT beta2).
Eval compute in (BAT alpha2). *)

Lemma batm_paired_REL : forall rel,
  REL rel = true ->
  batm_paired rel = true.
Proof.
  induction rel; intros Hrel; try discriminate; try reflexivity.
  simpl. rewrite (IHrel1). apply IHrel2.
  apply REL_conjSO_r in Hrel. assumption.
  apply REL_conjSO_l in Hrel. assumption.
Qed.

Lemma same_struc_BAT2_conjSO_BAT_r : forall alpha1 alpha2 rel1 rel2,
  REL rel1 = true ->
  REL rel2 = true ->
  same_struc_BAT2 (conjSO rel1 alpha1) (conjSO rel2 alpha2) = true ->
  BAT alpha1 = true ->
  BAT alpha2 = true.
Proof.
  intros until 0. intros Hrel1 Hrel2 Hss Hb.
  pose proof (same_struc_BAT2_2 _ _ Hss) as Hss2.
  apply same_struc_BAT2_defn in Hss.
  destruct Hss as [Hss1 Hss3].
  simpl in Hss3.
  rewrite (batm_paired_REL rel1) in Hss3.
  rewrite (batm_paired_REL rel2) in Hss3.
  apply (same_struc_BAT2_2 alpha1).
    apply same_struc_BAT2_defn.
    apply conj.
      apply same_struc_conjSO_r in Hss1.
      all : try assumption.
Qed.

(* Lemma same_struc_BAT2_conjSO_l : forall alpha1 alpha2 beta1 beta2,
  same_struc_BAT2 (conjSO alpha1 beta1) (conjSO alpha2 beta2) = true ->
  same_struc_BAT2 alpha1 alpha2 = true /\
  same_struc_BAT2 beta1 beta2 = true.
Proof.
  intros alpha1 alpha2 beta1 beta2 Hss.
  simpl in Hss. apply same_struc_BAT2_defn in Hss.
 destruct Hss as[ Hss1 Hss2].
  apply conj.
  apply same_struc_BAT2_defn. apply conj. 
    simpl in Hss1.
    case_eq (same_struc alpha1 alpha2); intros Hss3;
      rewrite Hss3 in *.
      reflexivity. discriminate.

    simpl in Hss2. split; intros H. rewrite H in *.
      case_eq (batm_paired alpha2 ); intros H2; rewrite H2 in *.
        reflexivity.
Qed. *)


