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
Require Import sSahlq3_5_plus_3 sSahlq_preprocessing1_added sSahlq_preprocessing3_added.


(* ADDED BAT *)

(*  From sSahlq4_6.

Cleaned up a bit. *)


(* Keep going!!! *)

(* The end ish *)


Fixpoint conjSO_exFO_relatSO_BAT alpha : bool :=
  if BAT alpha then true else
  match alpha with
    predSO _ _ => true 
  | relatSO _ _ => true
  | eqFO _ _ => false
  | allFO _ _ => false
  | exFO x beta => conjSO_exFO_relatSO_BAT beta
  | negSO _ => false 
  | conjSO beta1 beta2 => 
    if conjSO_exFO_relatSO_BAT beta1 then conjSO_exFO_relatSO_BAT beta2 else false
  | disjSO _ _ => false
  | implSO _ _ => false
  | allSO _ _ => false
  | exSO _ _ => false
  end.

Lemma bxatm_BOXATM_flag_weak_ST : forall phi x,
  bxatm phi = true ->
  BOXATM_flag_weak (ST phi x) x = true.
Proof.
  induction phi; intros [xn] H; try discriminate.
    simpl in *. destruct p. simpl. symmetry. apply beq_nat_refl.

    simpl in *. do 2 rewrite <- beq_nat_refl.
    apply IHphi. assumption.
Qed.

Lemma sSahlq_ante_mconj : forall phi1 phi2,
  sSahlq_ante (mconj phi1 phi2) = true ->
  (sSahlq_ante phi1 = true /\ sSahlq_ante phi2 = true).
Proof.
  intros phi1 phi2 H.
  simpl in *.
  case_eq (sSahlq_ante phi1); intros H1;
    rewrite H1 in *.
    apply conj.
      reflexivity.

      assumption.

    discriminate.
Qed.

Lemma sSahlq_ante_conjSO_exFO_relatSO_BAT : forall phi x,
  sSahlq_ante phi = true ->
  conjSO_exFO_relatSO_BAT (ST phi x) = true.
Proof.
   induction phi; intros [xn] Hvs;
    try (simpl in *; discriminate).

    destruct p; reflexivity.

    apply sSahlq_ante_mconj in Hvs.
    simpl.
    rewrite IHphi1. rewrite IHphi2.
    rewrite if_then_else_true. reflexivity.
    apply Hvs. apply Hvs.

    simpl in *. do 2 rewrite <- beq_nat_refl.
    rewrite bxatm_BOXATM_flag_weak_ST. reflexivity.
    assumption.

    simpl in Hvs.
    simpl. apply IHphi. assumption.
Qed.


Lemma beq_nat_max_S : forall n m,
  beq_nat (max (S n) m) n = false.
Proof.
  induction n; intros m.
    simpl. destruct m; reflexivity.

    simpl. destruct m. simpl. simpl in IHn. apply (IHn 0).
    simpl in IHn. apply IHn.
Qed.

Lemma preprocess_sSahlq_ante_predSO_againTRY : forall p f,
  conjSO_exFO_relatSO (predSO p f) = true ->
existsT2 (lv : list FOvariable) (atm : SecOrder),
  (is_BOXATM_flag_strong_CONJ atm = true) *
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
    apply pair.
      reflexivity.
      right. rewrite <- beq_nat_refl.
      apply conj. reflexivity.
      intros.
      apply iff_refl.
Defined.

Lemma preprocess_sSahlq_ante_predSO_againTRY_BAT : forall p f,
  conjSO_exFO_relatSO (predSO p f) = true ->
existsT2 (lv : list FOvariable) (atm : SecOrder),
  (is_in_FOvar (Var 0) lv = false) *
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
    apply pair. apply pair;
      reflexivity.
      right. rewrite <- beq_nat_refl.
      apply conj. reflexivity.
      intros.
      apply iff_refl.
Defined.


Lemma preprocess_sSahlq_ante_exFO_againTRY : forall alpha f,
  conjSO_exFO_relatSO (exFO f alpha) = true ->
  (existsT P : predicate, P_occurs_in_alpha (exFO f alpha) P = true) ->
(conjSO_exFO_relatSO alpha = true ->
          (existsT P : predicate, P_occurs_in_alpha alpha P = true) ->
          existsT2 (lv : list FOvariable) (atm : SecOrder),
            (is_BOXATM_flag_strong_CONJ atm = true) *
            ((existsT rel : SecOrder,
                REL rel = true /\
                is_in_pred_l (preds_in (conjSO rel atm))
                  (preds_in alpha) = true /\
                (forall (W : Set) (Iv : FOvariable -> W)
                   (Ip : predicate -> W -> Prop) 
                   (Ir : W -> W -> Prop),
                 SOturnst W Iv Ip Ir alpha <->
                 SOturnst W Iv Ip Ir
                   (list_closed_exFO (conjSO rel atm) lv))) +
             (is_in_pred_l (preds_in atm) (preds_in alpha) = true /\
             (forall (W : Set) (Iv : FOvariable -> W)
                (Ip : predicate -> W -> Prop) 
                (Ir : W -> W -> Prop),
              SOturnst W Iv Ip Ir alpha <->
              SOturnst W Iv Ip Ir (list_closed_exFO atm lv))))) ->
existsT2 (lv : list FOvariable) (atm : SecOrder),
  (is_BOXATM_flag_strong_CONJ atm = true) *
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
  intros alpha f H Hocc IHalpha.
    simpl in H.
    destruct Hocc as [P Hocc]. rewrite <- P_occurs_in_alpha_exFO in Hocc.
    assert (existsT P, P_occurs_in_alpha alpha P = true) as Hocc2.
      exists P. assumption.
    specialize (IHalpha H Hocc2).
    destruct IHalpha as [lv [atm [HAT [  [rel [HREL [Hin SOt]]] | [Hin SOt] ]]]];
      exists (cons f lv);
      exists atm;
      apply pair; try assumption.
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

Lemma preprocess_sSahlq_ante_exFO_againTRY_BAT : forall alpha f,
  conjSO_exFO_relatSO_BAT (exFO f alpha) = true ->
  is_in_FOvar (Var 0) (FOvars_in (exFO f alpha)) = false ->
  (existsT P : predicate, P_occurs_in_alpha (exFO f alpha) P = true) ->
(conjSO_exFO_relatSO_BAT alpha = true ->
  is_in_FOvar (Var 0) (FOvars_in alpha) = false ->
          (existsT P : predicate, P_occurs_in_alpha alpha P = true) ->
          existsT2 (lv : list FOvariable) (atm : SecOrder),
            (is_in_FOvar (Var 0) lv = false) *
            (BAT atm = true) *
            ((existsT rel : SecOrder,
                REL rel = true /\
                is_in_pred_l (preds_in (conjSO rel atm))
                  (preds_in alpha) = true /\
                (forall (W : Set) (Iv : FOvariable -> W)
                   (Ip : predicate -> W -> Prop) 
                   (Ir : W -> W -> Prop),
                 SOturnst W Iv Ip Ir alpha <->
                 SOturnst W Iv Ip Ir
                   (list_closed_exFO (conjSO rel atm) lv))) +
             (is_in_pred_l (preds_in atm) (preds_in alpha) = true /\
             (forall (W : Set) (Iv : FOvariable -> W)
                (Ip : predicate -> W -> Prop) 
                (Ir : W -> W -> Prop),
              SOturnst W Iv Ip Ir alpha <->
              SOturnst W Iv Ip Ir (list_closed_exFO atm lv))))) ->
existsT2 (lv : list FOvariable) (atm : SecOrder),
            (is_in_FOvar (Var 0) lv = false) *
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

(* Not true because there's a restriction on boxed atoms that 
  the FOvariables have to match up, but this isn't captured for 
  same_struc. *)


(* 
Lemma same_struc_BAT : forall alpha beta,
  same_struc alpha beta = true ->
  is_BOXATM_flag_strong_CONJ alpha = true ->
  is_BOXATM_flag_strong_CONJ beta = true.
Proof.
Admitted.
 *)




(*   induction alpha; intros beta Hss HREL;
    simpl in *; try discriminate.

    destruct beta; try discriminate.
    reflexivity.

    destruct beta; try discriminate.
    destruct f as [xn]. destruct xn. discriminate.
    simpl. destruct f0 as [ym]. destruct ym.
      destruct alpha; try discriminate.
      destruct alpha1; try discriminate.
      destruct f. destruct f0.
    case_eq (is_BOXATM_flag_strong_CONJ alpha1); intros HAT1;
      rewrite HAT1 in *; try discriminate.
    destruct beta; try discriminate.
    case_eq (same_struc alpha1 beta1); intros Hss1;
      rewrite Hss1 in *; try discriminate.

    simpl.
    rewrite IHalpha1; try assumption.
    apply IHalpha2; try assumption.
    reflexivity.
Qed.
 *)

(* Fixpoint batm_paired_pre (alpha : SecOrder) x : bool :=
  match alpha with
  | allFO y (implSO (relatSO z1 z2) beta) =>
    match x, y, z1, z2 with
    | Var xn, Var ym, Var zn1, Var zn2 =>
    if beq_nat xn zn1 then if beq_nat ym zn2
      then batm_paired_pre beta (Var zn2) 
      else false else false
    end
  | conjSO beta1 beta2 => 
    if batm_paired_pre beta1 x then batm_paired_pre beta2 x
    else false
  | _ => true
  end. *)





(* Lemma preprocess_sSahlq_ante_4_againTRY : forall alpha1 alpha2 lv1 rel1 lv2 rel2 atm2,
  conjSO_exFO_relatSO alpha2 = true ->
  REL rel1 = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha1 <->
      SOturnst W Iv Ip Ir (list_closed_exFO rel1 lv1)) ->
  REL rel2 = true ->
  is_BOXATM_flag_strong_CONJ atm2 = true ->
  is_in_pred_l (preds_in (conjSO rel2 atm2)) (preds_in alpha2) = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha2 <->
      SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel2 atm2) lv2) ) ->
  conjSO_exFO_relatSO alpha1 = true ->
existsT2 lv : list FOvariable,
  (existsT2 atm : SecOrder,
         (is_BOXATM_flag_strong_CONJ atm = true) *
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
         H HREL1 H_1 HREL2 HAT2 Hin H_2 H1.
     destruct (same_struc_conjSO_ex_AA _ _ _ (same_struc_rename_FOv_A (conjSO rel2 atm2) 
                                            (list_closed_exFO rel1 lv1)
                                             lv2)) as [rel2' [atm2' Heq2]].
     exists (app 
                (rename_FOv_A_list (conjSO rel2 atm2) 
                     (list_closed_exFO rel1 lv1) lv2)
(rename_FOv_A_list rel1 
                  (rename_FOv_A (conjSO rel2 atm2)
                     (list_closed_exFO rel1 lv1) lv2) lv1 )).
    exists  atm2'.
    apply pair.
      pose proof (same_struc_rename_FOv_A (conjSO rel2 atm2) (list_closed_exFO rel1 lv1)
         lv2) as Hsame2.
      pose proof (same_struc_rename_FOv_A rel1
         (rename_FOv_A (conjSO rel2 atm2)
            (list_closed_exFO rel1 lv1) lv2) lv1) as Hsame1.

destruct Heq2 as [Heq2 Heq22].
      rewrite Heq2 in Hsame2.
      apply same_struc_conjSO_r in Hsame2.
      apply same_struc_comm in Hsame2.
rewrite Heq2 in Heq22.
      apply same_struc_BAT in Hsame2; try assumption.
    exists (conjSO (rename_FOv_A rel1 (rename_FOv_A (conjSO rel2 atm2) 
                      (list_closed_exFO rel1 lv1) lv2) lv1) rel2').
    apply conj.
      pose proof (same_struc_rename_FOv_A (conjSO rel2 atm2) (list_closed_exFO rel1 lv1)
         lv2) as Hsame2.
      pose proof (same_struc_rename_FOv_A rel1
         (rename_FOv_A (conjSO rel2 atm2)
            (list_closed_exFO rel1 lv1) lv2) lv1) as Hsame1.
      rewrite Heq2 in Hsame2.
      apply same_struc_conjSO_l in Hsame2.
      apply same_struc_comm in Hsame2.
      apply same_struc_REL in Hsame2; try assumption.
      apply same_struc_comm in Hsame1.
      apply same_struc_REL in Hsame1; try assumption.
      simpl; rewrite Hsame1; assumption.

    apply conj.
      assert (preds_in (rename_FOv_A (conjSO rel2 atm2)   
                      (list_closed_exFO rel1 lv1) lv2) =
                       preds_in (conjSO rel2' atm2')) as Hpreds.
        rewrite Heq2. reflexivity.
      simpl. rewrite preds_in_rename_FOv_A in *.
      rewrite app_assoc.
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
      rewrite <- Heq2 in SOt.
      rewrite list_closed_exFO_app in SOt.
      apply equiv3_3_struc2_both with (alpha := rel1) in SOt.
      rewrite SOturnst_conjSO; apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.
Defined. *)

(*
Lemma rename_FOv_A_REL_pre : forall n l rel alpha beta rel' alpha',
  rename_FOv_A_pre (conjSO rel alpha) beta l n = conjSO rel' alpha' ->
  REL rel = true ->
  REL rel' = true.
Proof.
  intros n l 
  induction n; intros l rel alpha beta rel' alpha' H Hrel.
    simpl in *. inversion H as [[H1 H2]]. rewrite H1 in *.
    assumption.

    simpl in H. destruct l.  inversion H as [[H1 H2]].
    rewrite H1 in *. assumption.

    unfold rename_FOv_max_conj in H.
    rewrite strip_exFO_rename_FOv in H.
    rewrite strip_exFO_list_rename_FOv in H.
    rewrite rename_FOv_conjSO in H.
Search same_struc rename_FOv_A.
    simpl in H.
*)
Lemma rename_FOv_A_REL : forall l rel alpha beta rel' alpha',
  rename_FOv_A (conjSO rel alpha) beta l = conjSO rel' alpha' ->
  REL rel = true ->
  REL rel' = true.
Proof.
  intros until 0. intros H Hrel.
  pose proof (same_struc_rename_FOv_A (conjSO rel alpha) beta l) as H2.
  rewrite H in H2. apply same_struc_conjSO_l in H2.
  apply same_struc_comm in H2.
  apply (same_struc_REL rel rel') in Hrel; assumption.
Qed.

Lemma rename_FOv_A_REL2_pre : forall n l rel beta,
  REL rel = true ->
  REL (rename_FOv_A_pre rel beta l n) = true.
Proof.
  induction n; intros l rel beta Hrel. assumption.
  simpl. destruct l. assumption.
  unfold rename_FOv_max_conj.
  rewrite strip_exFO_rename_FOv.
  rewrite strip_exFO_list_rename_FOv.
  apply IHn. apply rename_FOv_rel. assumption.
Qed.

Lemma rename_FOv_A_REL2 : forall l rel beta,
  REL rel = true ->
  REL (rename_FOv_A rel beta l) = true.
Proof.
  unfold rename_FOv_A. intros l rel beta.
  apply rename_FOv_A_REL2_pre.
Qed.

Lemma REL_conjSO_rename_FOv_A : forall lv1 beta rel1 rel2',
REL rel1 = true ->
REL rel2' = true ->
REL (conjSO (rename_FOv_A rel1 beta lv1)  rel2') = true.
Proof.
  intros lv1 beta rel1 rel2' Hrel1 Hrel2.
  simpl. rewrite rename_FOv_A_REL2.
  all : assumption.
Qed.

Lemma is_in_FOvar_rename_FOv_A_list_pre_0 :
forall n (lv1 : list FOvariable) (alpha1 beta1 : SecOrder),
is_in_FOvar (Var 0) (rename_FOv_A_list_pre alpha1 beta1 lv1 n) = false.
Proof.
  induction n; intros lv1 alpha beta. reflexivity.
  simpl. destruct lv1. reflexivity.
  simpl. apply IHn.
Qed.

Lemma is_in_FOvar_rename_FOv_A_list_0 : forall lv1 alpha1 beta1,
  is_in_FOvar (Var 0) ((rename_FOv_A_list alpha1 beta1 lv1)) = false.
Proof.
  unfold rename_FOv_A_list.
  intros lv1. apply (is_in_FOvar_rename_FOv_A_list_pre_0).
Qed.

Lemma is_in_FOvar_rename_FOv_A_list_0_app_pre : forall n m lv1 lv2 alpha1 alpha2 beta1 beta2,
  is_in_FOvar (Var 0) (app (rename_FOv_A_list_pre alpha1 beta1 lv1 n)
    (rename_FOv_A_list_pre alpha2 beta2 lv2 m)) = false.
Proof.
  induction n; intros m lv1 lv2 alpha1 alpha2 beta1 beta2.
    simpl. apply (is_in_FOvar_rename_FOv_A_list_pre_0).

    simpl. destruct lv1. apply is_in_FOvar_rename_FOv_A_list_pre_0.

    simpl. apply IHn.
Qed.

Lemma is_in_FOvar_rename_FOv_A_list_0_app : forall lv1 lv2 alpha1 alpha2 beta1 beta2,
  is_in_FOvar (Var 0) (app (rename_FOv_A_list alpha1 beta1 lv1)
    (rename_FOv_A_list alpha2 beta2 lv2)) = false.
Proof.
  intros lv1 lv2. unfold rename_FOv_A_list.
  apply (is_in_FOvar_rename_FOv_A_list_0_app_pre).
Qed.

Lemma preprocess_sSahlq_ante_4_againTRY_BAT : forall alpha1 alpha2 lv1 rel1 lv2 rel2 atm2,
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
         H HREL1 Hin01 Hin02 H_1 HREL2 HAT2 Hin H_2 H1.
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
apply is_in_FOvar_rename_FOv_A_list_0_app.

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
      rewrite app_assoc.
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

Lemma preprocess_sSahlq_ante_6_againTRY_BAT : forall alpha1 alpha2 lv1 rel1 
        lv2 atm2,
  conjSO_exFO_relatSO_BAT alpha2 = true ->
  is_in_FOvar (Var 0) lv1 = false ->
  is_in_FOvar (Var 0) lv2 = false ->
  REL rel1 = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha1 <->
      SOturnst W Iv Ip Ir (list_closed_exFO rel1 lv1)) ->
  BAT atm2 = true ->
  is_in_pred_l (preds_in atm2) (preds_in alpha2) = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha2 <->
      SOturnst W Iv Ip Ir (list_closed_exFO atm2 lv2)) ->
  conjSO_exFO_relatSO_BAT alpha1 = true ->
existsT2 lv : list FOvariable,
    (existsT2 atm : SecOrder,
        (is_in_FOvar (Var 0) lv = false) *
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
  intros alpha1 alpha2 lv1 rel1  lv2  atm2
        H Hin01 Hin02 HREL1 H_1  HAT2 Hin2 H_2 H1.
     exists (app 
                (rename_FOv_A_list atm2
                     (list_closed_exFO rel1 lv1) lv2)
(rename_FOv_A_list rel1 
                  (rename_FOv_A  atm2
                     (list_closed_exFO rel1 lv1) lv2) lv1 )).

    exists (rename_FOv_A atm2 (list_closed_exFO rel1 lv1) lv2).
    apply pair.
      pose proof (same_struc_BAT2_rename_FOv_A atm2 (list_closed_exFO rel1 lv1)
         lv2) as Hsame2.
      apply same_struc_BAT2_comm in Hsame2.
      apply same_struc_BAT2_2 in Hsame2; try assumption.
apply pair.
apply is_in_FOvar_rename_FOv_A_list_0_app.

assumption.
assumption.
(*       apply same_struc_BAT2 in Hsame2; try assumption. *)

    exists (rename_FOv_A rel1 (rename_FOv_A atm2 (list_closed_exFO rel1 lv1) lv2) lv1).
    apply conj.
      pose proof (same_struc_rename_FOv_A rel1
         (rename_FOv_A (atm2)
            (list_closed_exFO rel1 lv1) lv2) lv1) as Hsame1.
      apply same_struc_comm in Hsame1.
      apply same_struc_REL in Hsame1; try assumption.

    apply conj.
      simpl. do 2 rewrite preds_in_rename_FOv_A in *.
      apply is_in_pred_l_2app.
      rewrite preds_in_rel. reflexivity. assumption.
      assumption.

    intros W Iv Ip Ir.
    split; intros SOt.
      rewrite list_closed_exFO_app.
      apply equiv3_3_struc2_both with (alpha := rel1).
      simpl.
      apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.

      rewrite list_closed_exFO_app in SOt.
      apply equiv3_3_struc2_both with (alpha := rel1) in SOt.
      simpl.
      apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.
Defined.

Lemma preprocess_sSahlq_ante_2_againTRY_BAT : forall alpha1 alpha2 lv1 rel1 atm1 
                                       lv2 rel2,
  conjSO_exFO_relatSO_BAT alpha2 = true ->
  is_in_FOvar (Var 0) lv1 = false ->
  is_in_FOvar (Var 0) lv2 = false ->
  REL rel1 = true ->
  BAT atm1 = true ->
  is_in_pred_l (preds_in (conjSO rel1 atm1)) (preds_in alpha1) = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha1 <->
      SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel1 atm1) lv1)) ->
  REL rel2 = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha2 <->
      SOturnst W Iv Ip Ir (list_closed_exFO rel2 lv2)) ->
  conjSO_exFO_relatSO_BAT alpha1 = true ->
  existsT2 lv : list FOvariable,
   (existsT2 atm : SecOrder,
        (is_in_FOvar (Var 0) lv = false) *
       (BAT atm = true) *
      (existsT2 rel : SecOrder,
          REL rel = true /\
          is_in_pred_l (preds_in (conjSO rel atm))
                       (preds_in (conjSO alpha1 alpha2)) = true /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
          SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv)))). 
Proof.
  intros alpha1 alpha2 lv1 rel1 atm1 lv2 rel2 H HREL1 Hin01 Hin02 HAT1 Hin H_1
         HREL2 H_2 H1.
    destruct (same_struc_conjSO_ex _ _ _ (same_struc_rename_FOv_A (conjSO rel1 atm1) 
                                            (rename_FOv_A rel2 
                                               (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1))
      as [rel1' [atm1' Heq1]].
     exists (app 
                (rename_FOv_A_list rel2 
                     (list_closed_exFO (conjSO rel1 atm1) lv1) lv2)
(rename_FOv_A_list (conjSO rel1 atm1) 
                  (rename_FOv_A rel2
                     (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1 )).

    exists atm1'.
    apply pair.
apply pair.
apply is_in_FOvar_rename_FOv_A_list_0_app.
      pose proof (same_struc_BAT2_rename_FOv_A rel2 (list_closed_exFO (conjSO rel1 atm1) lv1)
         lv2) as Hsame2.
      pose proof (same_struc_BAT2_rename_FOv_A (conjSO rel1 atm1)
         (rename_FOv_A rel2
            (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1) as Hsame1.
      rewrite Heq1 in Hsame1.
      apply same_struc_BAT2_comm in Hsame1.
      apply same_struc_BAT2_conjSO_BAT_r in Hsame1. all : try assumption.
      apply same_struc_BAT2_comm in Hsame2.
      apply rename_FOv_A_REL in Heq1; assumption. 
assumption.

    exists (conjSO rel1' (rename_FOv_A rel2 (list_closed_exFO (conjSO rel1 atm1) lv1) lv2)) .
    apply conj.
      pose proof (same_struc_BAT2_rename_FOv_A rel2 (list_closed_exFO (conjSO rel1 atm1) lv1)
         lv2) as Hsame2.
      pose proof (same_struc_BAT2_rename_FOv_A (conjSO rel1 atm1)
         (rename_FOv_A rel2
            (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1) as Hsame1.
      rewrite Heq1 in Hsame1.
simpl. rewrite rename_FOv_A_REL2. 
apply rename_FOv_A_REL in Heq1. rewrite Heq1. reflexivity. all : try assumption.

    apply conj.
      assert (preds_in (rename_FOv_A (conjSO rel1 atm1)
                        (rename_FOv_A rel2   
                      (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1) =
                       preds_in (conjSO rel1' atm1')) as Hpreds.
        rewrite Heq1. reflexivity.
      simpl. rewrite preds_in_rename_FOv_A in *.
      rewrite is_in_pred_l_app_rear1. 
      assert (preds_in (conjSO rel1' atm1') = 
              app (preds_in rel1') (preds_in atm1')) as Hpreds1.
        reflexivity.
      rewrite <- Hpreds1.
      rewrite <- Hpreds.
      apply is_in_pred_l_2app.
        assumption.
      rewrite preds_in_rel. reflexivity. assumption.

    intros W Iv Ip Ir.
    split; intros SOt.
      apply (equiv_list_closed_exFO 
                (conjSO (conjSO rel1' (rename_FOv_A rel2 (list_closed_exFO (conjSO rel1 atm1) lv1) lv2)) atm1')
                        (conjSO (conjSO rel1' atm1') (rename_FOv_A rel2 (list_closed_exFO (conjSO rel1 atm1) lv1) lv2))).
      apply equiv_conjSO4.
      rewrite <- Heq1.
      rewrite list_closed_exFO_app.
      apply equiv3_3_struc2_both with (alpha := conjSO rel1 atm1).
      simpl.
      apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.

      apply (equiv_list_closed_exFO (conjSO (conjSO rel1' (rename_FOv_A rel2 (list_closed_exFO (conjSO rel1 atm1) lv1) lv2)) atm1')
                                    (conjSO (conjSO rel1' atm1') (rename_FOv_A rel2 (list_closed_exFO (conjSO rel1 atm1) lv1) lv2)))
              in SOt.
      rewrite <- Heq1 in SOt.
      rewrite list_closed_exFO_app in SOt.
      apply equiv3_3_struc2_both with (alpha := (conjSO rel1 atm1)) in SOt.
      simpl.
      apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.

        apply equiv_conjSO4.
Defined.

Lemma preprocess_sSahlq_ante_8_againTRY : forall alpha1 alpha2 lv1 atm1 
        lv2 rel2,
  conjSO_exFO_relatSO_BAT alpha2 = true ->
  is_in_FOvar (Var 0) lv1 = false ->
  is_in_FOvar (Var 0) lv2 = false ->
  BAT atm1 = true ->
  is_in_pred_l (preds_in atm1) (preds_in alpha1) = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha1 <->
      SOturnst W Iv Ip Ir (list_closed_exFO atm1 lv1)) ->
  REL rel2 = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha2 <->
      SOturnst W Iv Ip Ir (list_closed_exFO rel2 lv2)) ->
  conjSO_exFO_relatSO_BAT alpha1 = true ->
existsT2 lv : list FOvariable,
   (existsT2 atm : SecOrder,
      (is_in_FOvar (Var 0) lv = false) *
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
  intros alpha1 alpha2 lv1 atm1 lv2 rel2
        H Hin01 Hin02 HAT1 Hin H_1 HREL2 H_2 H1.
     exists (app 
                (rename_FOv_A_list rel2 
                     (list_closed_exFO atm1 lv1) lv2)
(rename_FOv_A_list atm1
                  (rename_FOv_A rel2
                     (list_closed_exFO atm1 lv1) lv2) lv1 )).

    exists (rename_FOv_A atm1 (rename_FOv_A rel2 (list_closed_exFO atm1 lv1) lv2) lv1).
    apply pair.
      pose proof (same_struc_BAT2_rename_FOv_A rel2 (list_closed_exFO atm1 lv1)
         lv2) as Hsame2.
      pose proof (same_struc_BAT2_rename_FOv_A atm1
         (rename_FOv_A rel2
            (list_closed_exFO atm1 lv1) lv2) lv1) as Hsame1.
      apply same_struc_BAT2_comm in Hsame1.
      apply same_struc_BAT2_2 in Hsame1; try assumption.
apply pair.
apply is_in_FOvar_rename_FOv_A_list_0_app. assumption.
assumption.

    exists (rename_FOv_A rel2 (list_closed_exFO atm1 lv1) lv2).
    apply conj.
      pose proof (same_struc_rename_FOv_A rel2 (list_closed_exFO atm1 lv1)
         lv2) as Hsame2.
      apply same_struc_comm in Hsame2.
      apply same_struc_REL in Hsame2; try assumption.

    apply conj.
      simpl. do 2 rewrite preds_in_rename_FOv_A.
      rewrite is_in_pred_l_app_comm_l.
      apply is_in_pred_l_2app. assumption.
      rewrite preds_in_rel. reflexivity. assumption.

    intros W Iv Ip Ir.
    split; intros SOt.
      apply (equiv_list_closed_exFO (conjSO (rename_FOv_A rel2 (list_closed_exFO atm1 lv1) lv2) (rename_FOv_A atm1 (rename_FOv_A rel2 (list_closed_exFO atm1 lv1) lv2) lv1))
                                    (conjSO (rename_FOv_A atm1 (rename_FOv_A rel2 (list_closed_exFO atm1 lv1) lv2) lv1) (rename_FOv_A rel2 (list_closed_exFO atm1 lv1) lv2))).
        apply equiv_conjSO.
      rewrite list_closed_exFO_app.
      apply equiv3_3_struc2_both with (alpha := atm1).
      simpl.
      apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.

      apply (equiv_list_closed_exFO (conjSO (rename_FOv_A rel2 (list_closed_exFO atm1 lv1) lv2) (rename_FOv_A atm1 (rename_FOv_A rel2 (list_closed_exFO atm1 lv1) lv2) lv1))
                                    (conjSO (rename_FOv_A atm1 (rename_FOv_A rel2 (list_closed_exFO atm1 lv1) lv2) lv1) (rename_FOv_A rel2 (list_closed_exFO atm1 lv1) lv2))) in SOt.
        apply equiv_conjSO.
      rewrite list_closed_exFO_app in SOt.
      apply equiv3_3_struc2_both with (alpha := atm1) in SOt.
      simpl.
      apply conj.
        apply H_2. apply SOt.
        apply H_1. apply SOt.

        apply equiv_conjSO.
Defined.

Lemma preprocess_sSahlq_ante_1_againTRY : forall alpha1 alpha2 lv1 rel1 atm1 
        lv2 rel2 atm2,
  conjSO_exFO_relatSO_BAT alpha2 = true ->
  is_in_FOvar (Var 0) lv1 = false ->
  is_in_FOvar (Var 0) lv2 = false ->
  REL rel1 = true ->
  BAT atm1 = true ->
  is_in_pred_l (preds_in (conjSO rel1 atm1)) (preds_in alpha1) = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha1 <->
      SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel1 atm1) lv1)) ->
  REL rel2 = true ->
  BAT atm2 = true ->
  is_in_pred_l (preds_in (conjSO rel2 atm2)) (preds_in alpha2) = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha2 <->
      SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel2 atm2) lv2)) ->
  conjSO_exFO_relatSO_BAT alpha1 = true ->
existsT2 lv : list FOvariable,
    (existsT2 atm : SecOrder,
      (is_in_FOvar (Var 0) lv = false) *
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
  intros alpha1 alpha2 lv1 rel1 atm1 lv2 rel2 atm2
        H Hin01 Hin02 HREL1 HAT1 Hin1 H_1 HREL2 HAT2 Hin2 H_2 H1.
    destruct (same_struc_conjSO_ex _ _ _ (same_struc_rename_FOv_A (conjSO rel1 atm1) 
                                            (rename_FOv_A (conjSO rel2 atm2) 
                                               (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1))
      as [rel1' [atm1' Heq1]].
    destruct (same_struc_conjSO_ex _ _ _ (same_struc_rename_FOv_A (conjSO rel2 atm2) 
                                            (list_closed_exFO (conjSO rel1 atm1) lv1)
                                             lv2)) as [rel2' [atm2' Heq2]].
     exists (app 
                (rename_FOv_A_list (conjSO rel2 atm2) 
                     (list_closed_exFO (conjSO rel1 atm1) lv1) lv2)
(rename_FOv_A_list (conjSO rel1 atm1) 
                  (rename_FOv_A (conjSO rel2 atm2)
                     (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1 )).

    exists (conjSO atm1' atm2').
    apply pair.
apply pair.
apply is_in_FOvar_rename_FOv_A_list_0_app. 

      pose proof (same_struc_BAT2_rename_FOv_A (conjSO rel2 atm2) (list_closed_exFO (conjSO rel1 atm1) lv1)
         lv2) as Hsame2.
      pose proof (same_struc_BAT2_rename_FOv_A (conjSO rel1 atm1)
         (rename_FOv_A (conjSO rel2 atm2)
            (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1) as Hsame1.
      rewrite Heq2 in Hsame2.
      rewrite Heq1 in Hsame1.
      apply same_struc_BAT2_comm in Hsame2.
      apply same_struc_BAT2_conjSO_BAT_r in Hsame2.
      apply same_struc_BAT2_comm in Hsame1.
      apply same_struc_BAT2_conjSO_BAT_r in Hsame1.
      simpl. rewrite Hsame1. all : try  assumption.
      apply rename_FOv_A_REL in Heq1; assumption.
      apply rename_FOv_A_REL in Heq2; assumption.


(*       apply same_struc_BAT2_comm in Hsame2.
      apply same_struc_BAT in Hsame2; try assumption.
      apply same_struc_conjSO_r in Hsame1.
      apply same_struc_comm in Hsame1.
      apply same_struc_BAT in Hsame1; try assumption.
      simpl; rewrite Hsame1; assumption.
 *)
    exists (conjSO rel1' rel2').
    apply conj.
      pose proof (same_struc_rename_FOv_A (conjSO rel2 atm2) (list_closed_exFO (conjSO rel1 atm1) lv1)
         lv2) as Hsame2.
      pose proof (same_struc_rename_FOv_A (conjSO rel1 atm1)
         (rename_FOv_A (conjSO rel2 atm2)
            (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1) as Hsame1.
      rewrite Heq2 in Hsame2.
      rewrite Heq1 in Hsame1.
      apply same_struc_conjSO_l in Hsame2.
      apply same_struc_comm in Hsame2.
      apply same_struc_REL in Hsame2; try assumption.
      apply same_struc_conjSO_l in Hsame1.
      apply same_struc_comm in Hsame1.
      apply same_struc_REL in Hsame1; try assumption.
      simpl; rewrite Hsame1; assumption.

    apply conj.
      simpl.
      assert (preds_in (rename_FOv_A (conjSO rel1 atm1)
                        (rename_FOv_A (conjSO rel2 atm2)   
                      (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1) =
                       preds_in (conjSO rel1' atm1')) as Hpreds.
        rewrite Heq1. reflexivity.
      assert (preds_in (rename_FOv_A (conjSO rel2 atm2)
                      (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) =
                       preds_in (conjSO rel2' atm2')) as Hpreds0.
        rewrite Heq2. reflexivity.
      simpl. rewrite preds_in_rename_FOv_A in *.
      rewrite is_in_pred_l_app_rear2. 
      assert (preds_in (conjSO rel1' atm1') = 
              app (preds_in rel1') (preds_in atm1')) as Hpreds1.
        reflexivity.
       assert (preds_in (conjSO rel2' atm2') = 
              app (preds_in rel2') (preds_in atm2')) as Hpreds2.
        reflexivity.
     rewrite <- Hpreds1.
     rewrite <- Hpreds2.
      rewrite <- Hpreds.
      rewrite <- Hpreds0.
      apply is_in_pred_l_2app;
        assumption.

    intros W Iv Ip Ir.
    split; intros SOt.
      apply (equiv_list_closed_exFO (conjSO (conjSO rel1' rel2') (conjSO atm1' atm2'))
                                    (conjSO (conjSO rel1' atm1') (conjSO rel2' atm2'))).
        apply equiv_conjSO3.
      rewrite <- Heq1.
      rewrite <- Heq2.
      rewrite list_closed_exFO_app.
      apply equiv3_3_struc2_both with (alpha := (conjSO rel1 atm1)).
      simpl.
      apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.

      apply (equiv_list_closed_exFO (conjSO (conjSO rel1' rel2') (conjSO atm1' atm2'))
                                    (conjSO (conjSO rel1' atm1') (conjSO rel2' atm2')))
              in SOt.
      rewrite <- Heq1 in SOt.
      rewrite <- Heq2 in SOt.
      rewrite list_closed_exFO_app in SOt.
      apply equiv3_3_struc2_both with (alpha := (conjSO rel1 atm1)) in SOt.
      simpl.
      apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.

        apply equiv_conjSO3.
Defined.

Lemma preprocess_sSahlq_ante_3_againTRY : forall alpha1 alpha2 lv1 rel1 atm1 lv2 atm2,
  conjSO_exFO_relatSO_BAT alpha2 = true ->
  is_in_FOvar (Var 0) lv1 = false ->
  is_in_FOvar (Var 0) lv2 = false ->
  REL rel1 = true ->
  BAT atm1 = true ->
  is_in_pred_l (preds_in (conjSO rel1 atm1)) (preds_in alpha1) = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha1 <->
      SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel1 atm1) lv1)) ->
  BAT atm2 = true ->
  is_in_pred_l (preds_in atm2) (preds_in alpha2) = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha2 <->
      SOturnst W Iv Ip Ir (list_closed_exFO atm2 lv2)) ->
  conjSO_exFO_relatSO_BAT alpha1 = true ->
existsT2 lv : list FOvariable,
  (existsT2 atm : SecOrder,
     (is_in_FOvar (Var 0) lv = false) *
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
  intros alpha1 alpha2 lv1 rel1 atm1 lv2 atm2
         H Hin01 Hin02 HREL1 HAT1 Hin1 H_1 HAT2 Hin2 H_2 H1.
    destruct (same_struc_conjSO_ex _ _ _ (same_struc_rename_FOv_A (conjSO rel1 atm1) 
                                            (rename_FOv_A atm2
                                               (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1))
      as [rel1' [atm1' Heq1]].
     exists (app 
                (rename_FOv_A_list atm2 
                     (list_closed_exFO (conjSO rel1 atm1) lv1) lv2)
(rename_FOv_A_list (conjSO rel1 atm1) 
                  (rename_FOv_A atm2
                     (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1 )).

    exists (conjSO atm1' (rename_FOv_A atm2 (list_closed_exFO (conjSO rel1 atm1) lv1)
         lv2)).
    apply pair.
      pose proof (same_struc_BAT2_rename_FOv_A atm2 (list_closed_exFO (conjSO rel1 atm1) lv1)
         lv2) as Hsame2.
      pose proof (same_struc_BAT2_rename_FOv_A (conjSO rel1 atm1)
         (rename_FOv_A atm2
            (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1) as Hsame1.
      rewrite Heq1 in Hsame1.
      apply same_struc_BAT2_comm in Hsame1.
      apply same_struc_BAT2_conjSO_BAT_r in Hsame1.
      apply same_struc_BAT2_comm in Hsame2.
      apply same_struc_BAT2_2 in Hsame2.
      simpl. rewrite Hsame1. all : try assumption.
apply pair.
apply is_in_FOvar_rename_FOv_A_list_0_app.

      apply rename_FOv_A_REL in Heq1; assumption.
      apply same_struc__BAT2 in Hsame1. apply same_struc_conjSO_l in Hsame1.
      apply same_struc_REL in Hsame1; assumption.


    exists rel1'.
    apply conj.
      pose proof (same_struc_rename_FOv_A atm2 (list_closed_exFO (conjSO rel1 atm1) lv1)
         lv2) as Hsame2.
      pose proof (same_struc_rename_FOv_A (conjSO rel1 atm1)
         (rename_FOv_A atm2
            (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1) as Hsame1.
      rewrite Heq1 in Hsame1.
      apply same_struc_conjSO_l in Hsame1.
      apply same_struc_comm in Hsame1.
      apply same_struc_REL in Hsame1; try assumption.

    apply conj.
      simpl.
      assert (preds_in (rename_FOv_A (conjSO rel1 atm1)
                        (rename_FOv_A (atm2)   
                      (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1) =
                       preds_in (conjSO rel1' atm1')) as Hpreds.
        rewrite Heq1. reflexivity.
      simpl. rewrite preds_in_rename_FOv_A in *.
      rewrite <- app_assoc.
      assert (preds_in (conjSO rel1' atm1') = 
              app (preds_in rel1') (preds_in atm1')) as Hpreds1.
        reflexivity.
     rewrite <- Hpreds1.
      rewrite <- Hpreds.
      apply is_in_pred_l_2app;
        assumption.

    intros W Iv Ip Ir.
    split; intros SOt.
      apply (equiv_list_closed_exFO (conjSO rel1' (conjSO atm1' (rename_FOv_A atm2 
              (list_closed_exFO (conjSO rel1 atm1) lv1) lv2)))
                                    (conjSO (conjSO rel1' atm1')
              (rename_FOv_A atm2 (list_closed_exFO (conjSO rel1 atm1) lv1) lv2))).
        apply equiv_conjSO5.
      rewrite <- Heq1.
      rewrite list_closed_exFO_app.
      apply equiv3_3_struc2_both with (alpha := (conjSO rel1 atm1)).
      simpl.
      apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.

      apply (equiv_list_closed_exFO (conjSO rel1' (conjSO atm1' (rename_FOv_A atm2 
              (list_closed_exFO (conjSO rel1 atm1) lv1) lv2)))
                                    (conjSO (conjSO rel1' atm1') (rename_FOv_A atm2 
              (list_closed_exFO (conjSO rel1 atm1) lv1) lv2)))
              in SOt.
      rewrite <- Heq1 in SOt.
      rewrite list_closed_exFO_app in SOt.
      apply equiv3_3_struc2_both with (alpha := (conjSO rel1 atm1)) in SOt.
      simpl.
      apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.

        apply equiv_conjSO5.
Defined.

Lemma preprocess_sSahlq_ante_7_againTRY : forall alpha1 alpha2 lv1 atm1 
        lv2 rel2 atm2,
  conjSO_exFO_relatSO_BAT alpha2 = true ->
  is_in_FOvar (Var 0) lv1 = false ->
  is_in_FOvar (Var 0) lv2 = false ->
  BAT atm1 = true ->
  is_in_pred_l (preds_in atm1) (preds_in alpha1) = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha1 <->
      SOturnst W Iv Ip Ir (list_closed_exFO atm1 lv1)) ->
  REL rel2 = true ->
  BAT atm2 = true ->
  is_in_pred_l (preds_in (conjSO rel2 atm2)) (preds_in alpha2) = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha2 <->
      SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel2 atm2) lv2)) ->
  conjSO_exFO_relatSO_BAT alpha1 = true ->
existsT2 lv : list FOvariable,
  (existsT2 atm : SecOrder,
       (is_in_FOvar (Var 0) lv = false) *
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
  intros alpha1 alpha2 lv1 atm1 lv2 rel2 atm2
        H Hin01 Hin02 HAT1 Hin1 H_1 HREL2 HAT2 Hin2 H_2 H1.
    destruct (same_struc_conjSO_ex _ _ _ (same_struc_rename_FOv_A (conjSO rel2 atm2) 
                                            (list_closed_exFO atm1 lv1)
                                             lv2)) as [rel2' [atm2' Heq2]].
     exists (app 
                (rename_FOv_A_list (conjSO rel2 atm2) 
                     (list_closed_exFO atm1 lv1) lv2)
(rename_FOv_A_list  atm1
                  (rename_FOv_A (conjSO rel2 atm2)
                     (list_closed_exFO  atm1 lv1) lv2) lv1 )).

    exists (conjSO (rename_FOv_A atm1 (rename_FOv_A (conjSO rel2 atm2) 
                        (list_closed_exFO atm1 lv1) lv2) lv1) atm2').
    apply pair.
      pose proof (same_struc_BAT2_rename_FOv_A (conjSO rel2 atm2) (list_closed_exFO atm1 lv1)
         lv2) as Hsame2.
      pose proof (same_struc_BAT2_rename_FOv_A atm1
         (rename_FOv_A (conjSO rel2 atm2)
            (list_closed_exFO  atm1 lv1) lv2) lv1) as Hsame1.
      rewrite Heq2 in Hsame2.
      apply same_struc_BAT2_comm in Hsame2.
      apply same_struc_BAT2_conjSO_BAT_r in Hsame2.
      apply same_struc_BAT2_comm in Hsame1.
      apply same_struc_BAT2_2 in Hsame1; try assumption.
      simpl. rewrite Hsame1. all : try assumption.
apply pair.
apply is_in_FOvar_rename_FOv_A_list_0_app.

      apply rename_FOv_A_REL in Heq2; assumption.

      apply same_struc__BAT2 in Hsame2.   
      apply same_struc_conjSO_l in Hsame2.
      apply same_struc_REL in Hsame2; assumption.

    exists rel2'.
    apply conj.
      pose proof (same_struc_rename_FOv_A (conjSO rel2 atm2) (list_closed_exFO atm1 lv1)
         lv2) as Hsame2.
      rewrite Heq2 in Hsame2.
      apply same_struc_conjSO_l in Hsame2.
      apply same_struc_comm in Hsame2.
      apply same_struc_REL in Hsame2; try assumption.

    apply conj.
      simpl.
      assert (preds_in (rename_FOv_A (conjSO rel2 atm2)
                      (list_closed_exFO ( atm1) lv1) lv2) =
                       preds_in (conjSO rel2' atm2')) as Hpreds0.
        rewrite Heq2. reflexivity.
      simpl. rewrite preds_in_rename_FOv_A in *.
      rewrite <- app_assoc.
      rewrite <- is_in_pred_l_app_rear1.
      rewrite is_in_pred_l_app_comm_l.
       assert (preds_in (conjSO rel2' atm2') = 
              app (preds_in rel2') (preds_in atm2')) as Hpreds2.
        reflexivity.
     rewrite <- Hpreds2.
      rewrite <- Hpreds0.
      apply is_in_pred_l_2app;
        assumption.

    intros W Iv Ip Ir.
    split; intros SOt.
      apply (equiv_list_closed_exFO (conjSO  rel2' (conjSO (rename_FOv_A atm1 (rename_FOv_A (conjSO rel2 atm2) 
                        (list_closed_exFO atm1 lv1) lv2) lv1) atm2'))
                                    (conjSO (rename_FOv_A atm1 (rename_FOv_A (conjSO rel2 atm2) 
                        (list_closed_exFO atm1 lv1) lv2) lv1) (conjSO rel2' atm2'))).
        apply equiv_conjSO6.
      rewrite <- Heq2.
      rewrite list_closed_exFO_app.
      apply equiv3_3_struc2_both with (alpha := (atm1)).
      simpl.
      apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.

      apply (equiv_list_closed_exFO (conjSO  rel2' (conjSO (rename_FOv_A atm1 (rename_FOv_A (conjSO rel2 atm2) 
                        (list_closed_exFO atm1 lv1) lv2) lv1) atm2'))
                                    (conjSO (rename_FOv_A atm1 (rename_FOv_A (conjSO rel2 atm2) 
                        (list_closed_exFO atm1 lv1) lv2) lv1) (conjSO rel2' atm2'))) in SOt;
        try apply equiv_conjSO6.
      rewrite <- Heq2 in SOt.
      rewrite list_closed_exFO_app in SOt.
      apply equiv3_3_struc2_both with (alpha := (atm1)) in SOt.
      simpl.
      apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.
Defined.

Lemma preprocess_sSahlq_ante_9_againTRY : forall alpha1 alpha2 lv1 atm1 
        lv2 atm2,
  conjSO_exFO_relatSO_BAT alpha2 = true ->
  is_in_FOvar (Var 0) lv1 = false ->
  is_in_FOvar (Var 0) lv2 = false ->
  BAT atm1 = true ->
  is_in_pred_l (preds_in (atm1)) (preds_in alpha1) = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha1 <->
      SOturnst W Iv Ip Ir (list_closed_exFO  atm1 lv1)) ->
  BAT atm2 = true ->
  is_in_pred_l (preds_in (atm2)) (preds_in alpha2) = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha2 <->
      SOturnst W Iv Ip Ir (list_closed_exFO atm2 lv2)) ->
  conjSO_exFO_relatSO_BAT alpha1 = true ->
existsT2 lv : list FOvariable,
   (existsT2 atm : SecOrder,
       (is_in_FOvar (Var 0) lv = false) *
       (BAT atm = true) *
          (is_in_pred_l (preds_in (atm))
                       (preds_in (conjSO alpha1 alpha2)) = true /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
          SOturnst W Iv Ip Ir (list_closed_exFO (atm) lv)))).
Proof.
  intros alpha1 alpha2 lv1 atm1 lv2 atm2
        H Hin01 Hin02 HAT1 Hin1 H_1 HAT2 Hin2 H_2 H1.
     exists (app 
                (rename_FOv_A_list atm2
                     (list_closed_exFO atm1 lv1) lv2)
(rename_FOv_A_list atm1
                  (rename_FOv_A atm2
                     (list_closed_exFO atm1 lv1) lv2) lv1 )).

    exists (conjSO (rename_FOv_A atm1 (rename_FOv_A atm2 (list_closed_exFO atm1 lv1) lv2)
              lv1) (rename_FOv_A atm2 (list_closed_exFO atm1 lv1) lv2)
).
    apply pair.
apply pair.
apply is_in_FOvar_rename_FOv_A_list_0_app.

      pose proof (same_struc_BAT2_rename_FOv_A atm2 (list_closed_exFO atm1 lv1)
         lv2) as Hsame2.
      pose proof (same_struc_BAT2_rename_FOv_A atm1
         (rename_FOv_A atm2
            (list_closed_exFO atm1 lv1) lv2) lv1) as Hsame1.
      apply same_struc_BAT2_comm in Hsame2.
      apply same_struc_BAT2_2 in Hsame2; try assumption.
      apply same_struc_BAT2_comm in Hsame1.
      apply same_struc_BAT2_2 in Hsame1; try assumption.
      simpl; rewrite Hsame1. assumption.
assumption.
assumption.

    apply conj.
      simpl.
      simpl. do 2  rewrite preds_in_rename_FOv_A in *.
      apply is_in_pred_l_2app;
        assumption.

    intros W Iv Ip Ir.
    split; intros SOt.
      rewrite list_closed_exFO_app.
      apply equiv3_3_struc2_both with (alpha :=  atm1).
      simpl.
      apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.

      rewrite list_closed_exFO_app in SOt.
      apply equiv3_3_struc2_both with (alpha := atm1) in SOt.
      simpl.
      apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.
Defined.

Lemma preprocess_vsSahlq_ante_5_againTRY_BAT : forall alpha1 alpha2 lv1 rel1 lv2 rel2,
  conjSO_exFO_relatSO_BAT alpha2 = true ->  
  is_in_FOvar (Var 0) lv1 = false ->
  is_in_FOvar (Var 0) lv2 = false ->
  REL rel1 = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha1 <->
      SOturnst W Iv Ip Ir (list_closed_exFO rel1 lv1)) ->
  REL rel2 = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha2 <->
      SOturnst W Iv Ip Ir (list_closed_exFO rel2 lv2)) ->
  conjSO_exFO_relatSO_BAT alpha1 = true ->
existsT2 lv : list FOvariable,
  (existsT rel : SecOrder,
    (is_in_FOvar (Var 0) lv = false) /\
     REL rel = true /\
      (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
         (Ir : W -> W -> Prop),
       SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
       SOturnst W Iv Ip Ir (list_closed_exFO rel lv))).
Proof.
  intros alpha1 alpha2 lv1 rel1 lv2 rel2
         H Hin1 Hin2 HREL1 H_1 HREL2 H_2 H1.
     exists (app 
                (rename_FOv_A_list rel2 
                     (list_closed_exFO rel1 lv1) lv2)
(rename_FOv_A_list rel1 
                  (rename_FOv_A rel2
                     (list_closed_exFO rel1 lv1) lv2) lv1 )).

pose proof equiv3_3_struc2_both.
    exists (conjSO
                (rename_FOv_A rel1
                   (rename_FOv_A rel2 (list_closed_exFO rel1 lv1) lv2) lv1)
                (rename_FOv_A rel2 (list_closed_exFO rel1 lv1) lv2)).
    apply conj.
apply is_in_FOvar_rename_FOv_A_list_0_app.

apply conj.
      pose proof (same_struc_rename_FOv_A rel2 (list_closed_exFO rel1 lv1)
         lv2) as Hsame2.
      pose proof (same_struc_rename_FOv_A rel1
         (rename_FOv_A rel2
            (list_closed_exFO rel1 lv1) lv2) lv1) as Hsame1.
      apply same_struc_comm in Hsame2.
      apply same_struc_REL in Hsame2; try assumption.
      apply same_struc_comm in Hsame1.
      apply same_struc_REL in Hsame1; try assumption.
      simpl; rewrite Hsame1; try assumption.

    intros W Iv Ip Ir.
    split; intros SOt.
      rewrite list_closed_exFO_app.
      apply equiv3_3_struc2_both with (alpha := rel1).
      simpl.
      apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.

      rewrite list_closed_exFO_app in SOt.
      apply equiv3_3_struc2_both with (alpha := rel1) in SOt.
      simpl.
      apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.
Defined.

Lemma BAT_occ_num_conn : forall m n alpha,
  n = num_conn alpha ->
  Nat.leb n m = true ->
  BAT alpha = true ->
~ (forall P, P_occurs_in_alpha alpha P = false).
Proof.
  induction m; intros n alpha Hnum Hleb H1 H2; try discriminate.
    destruct n. 2 : discriminate.
    destruct alpha; try discriminate.
    specialize (H2 p). destruct p as [Pn].
    unfold P_occurs_in_alpha in H2.
    simpl in *. destruct f. simpl in *.
    rewrite <- beq_nat_refl in *. discriminate.

    destruct n. 
    destruct alpha; try discriminate.
    specialize (H2 p). destruct p as [Pn].
    unfold P_occurs_in_alpha in H2.
    simpl in *. destruct f. simpl in *.
    rewrite <- beq_nat_refl in *. discriminate.

    destruct alpha; try discriminate.
      destruct alpha; try discriminate.
      destruct alpha1; try discriminate.
      unfold P_occurs_in_alpha in *.
      destruct f0. destruct f1.
      simpl in H2.

      apply is_BOXATM_flag_strong__CONJ_BAT in H1.
      apply BOXATM_flag_weak_BAT in H1.   
      apply (IHm (num_conn alpha2) alpha2); try assumption.
        reflexivity.

    inversion Hnum as [Hnum'].
    rewrite Hnum' in Hleb.
    destruct m. discriminate. apply leb_suc_r. assumption.

      pose proof (P_occurs_in_alpha_conjSO_all_f_l _ _ H2) as H3.
      apply (IHm (num_conn alpha1) alpha1); try assumption.
        reflexivity.

        rewrite Hnum in Hleb. simpl in Hleb.
        apply leb_plus_take1 in Hleb. assumption.

        apply BAT_conjSO_l in H1. assumption.
Qed.


Lemma BAT_occ : forall alpha,
  BAT alpha = true ->
~ (forall P, P_occurs_in_alpha alpha P = false).
Proof.
  intros alpha. apply (BAT_occ_num_conn (num_conn alpha)
    (num_conn alpha) _ eq_refl (leb_refl _)).
Qed.

Lemma conjSO_exFO_relatSO_BAT_allFO : forall alpha x,
  conjSO_exFO_relatSO_BAT (allFO x alpha) = true ->
  BAT (allFO x alpha) = true.
Proof.
  intros alpha [xn] H.
  case_eq (BAT (allFO (Var xn) alpha)); intros H2.
    reflexivity.
  simpl in *. rewrite H2 in *. discriminate.
Qed.

Lemma trying2_BAT : forall alpha,
  conjSO_exFO_relatSO_BAT alpha = true ->
  is_in_FOvar (Var 0) (FOvars_in alpha) = false ->
  (forall P, P_occurs_in_alpha alpha P = false) ->
  existsT2 lv rel,
  is_in_FOvar (Var 0) lv = false /\
  REL rel = true /\
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha <->
      SOturnst W Iv Ip Ir (list_closed_exFO rel lv)).
Proof.
  induction alpha; intros H1 Hin0 H2; try (    simpl in *; discriminate).
    simpl in *. specialize (H2 p).
    destruct p. unfold P_occurs_in_alpha in H2.
    destruct f. simpl in *. rewrite <- beq_nat_refl in H2.
    discriminate.

    exists nil. exists (relatSO f f0).
    apply conj. reflexivity.
    apply conj. reflexivity.
    simpl. intros. apply iff_refl.
    apply conjSO_exFO_relatSO_BAT_allFO in H1.
    contradiction (BAT_occ _ H1 H2).

    assert (forall P, P_occurs_in_alpha (alpha) P = false) as H2'.
      intros P. specialize (H2 P).
      rewrite <- P_occurs_in_alpha_exFO in H2.
      assumption.
    simpl FOvars_in in Hin0. apply is_in_FOvar_cons_f in Hin0.
    destruct Hin0 as [Hin0 Heqf].
    simpl in H1. destruct (IHalpha H1 Hin0 H2') as [lv [rel [Hin02 [Hrel H]]]].
    exists (cons f lv). exists rel.
    apply conj. simpl. destruct f as [nn]. destruct nn.
      contradiction (Heqf eq_refl). assumption.
    apply conj. assumption.
    intros. simpl list_closed_exFO.
    do 2 rewrite SOturnst_exFO. split; intros [d SOt];
      exists d; apply H; assumption.

    simpl in H1. case_eq (conjSO_exFO_relatSO_BAT alpha1);
      intros H3; rewrite H3 in H1.
case_eq (conjSO_exFO_relatSO_BAT alpha2);
      intros H3'; rewrite H3' in H1.

    destruct (IHalpha1 H3 (is_in_FOvar_app_l _ _ _ Hin0) (P_occurs_in_alpha_conjSO_all_f_l _ _ H2))
      as [lv [rel [Hin3 [HREL H]]]].
    destruct (IHalpha2 H3' (is_in_FOvar_app_r _ _ _ Hin0)(P_occurs_in_alpha_conjSO_all_f_r _ _ H2))
      as [lv2 [rel2 [Hin4 [HREL2 H4]]]].
    destruct (preprocess_vsSahlq_ante_5_againTRY_BAT alpha1 alpha2 lv rel lv2 rel2)
      as [lv' [rel' [Hrel' H']]];
      try assumption.
    exists lv'. exists rel'.
    apply conj. assumption.
    assumption.

    case_eq (BAT (conjSO alpha1 alpha2)); intros Hbat;
      pose proof Hbat as Hbat';
      simpl in Hbat; rewrite Hbat in *. 2 : discriminate.
    case_eq (BAT alpha1); intros Hbat1; rewrite Hbat1 in *;
    case_eq (BAT alpha2); intros Hbat2; try rewrite Hbat2 in *;
    try discriminate.
    contradiction (BAT_occ _ Hbat' H2).

    case_eq (BAT (conjSO alpha1 alpha2)); intros Hbat;
      pose proof Hbat as Hbat';
      simpl in Hbat; rewrite Hbat in *. 2 : discriminate.
    case_eq (BAT alpha1); intros Hbat1; rewrite Hbat1 in *;
    case_eq (BAT alpha2); intros Hbat2; try rewrite Hbat2 in *;
    try discriminate.
    contradiction (BAT_occ _ Hbat' H2).
Defined.


Lemma preprocess_vsSahlq_ante_notocc_againTRY_BAT : forall alpha,
  conjSO_exFO_relatSO_BAT alpha = true ->
  is_in_FOvar (Var 0) (FOvars_in alpha) = false ->
  (forall P, P_occurs_in_alpha alpha P = false) ->
  existsT2 lv rel,
      (is_in_FOvar (Var 0) lv = false) /\
      (REL rel = true) /\
      (is_in_pred_l (preds_in rel) (preds_in alpha) = true) /\
        forall W Iv Ip Ir,
          SOturnst W Iv Ip Ir alpha <->
          SOturnst W Iv Ip Ir (list_closed_exFO rel lv).
Proof.
  intros alpha H1 Hin0 H2. destruct (trying2_BAT alpha H1 Hin0 H2)
     as [lv [rel [Hin [Hrel H]]]].
  exists lv. exists rel.
  apply conj. assumption.
  apply conj. assumption. 
  apply conj. rewrite preds_in_rel. reflexivity.
  all :  assumption.
Defined.

Lemma preprocess_sSahlq_ante_againTRY : forall alpha,
  conjSO_exFO_relatSO_BAT alpha = true ->
  is_in_FOvar (Var 0) (FOvars_in alpha) = false ->
  (existsT P, P_occurs_in_alpha alpha P = true) ->
  existsT2 lv atm,
    (is_in_FOvar (Var 0) lv = false) *
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
  intros alpha H Hin0 Hocc.
  induction alpha; try (simpl in *; discriminate).
    apply preprocess_sSahlq_ante_predSO_againTRY_BAT; assumption.

    destruct Hocc as [[Pn] Hocc].
    unfold P_occurs_in_alpha in Hocc. destruct f. destruct f0.
    simpl in Hocc. discriminate.

    apply conjSO_exFO_relatSO_BAT_allFO in H. 
exists nil. exists (allFO f alpha). apply pair.
    apply pair. reflexivity. assumption.
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
      apply is_in_FOvar_app_r in Hin0. assumption.

      destruct Hocc as [P Hocc].
      apply P_occurs_in_alpha_conjSO_comp in Hocc.
      rewrite (Hocc1 P) in Hocc.
      destruct Hocc. discriminate.
      exists P. assumption.

      destruct (preprocess_sSahlq_ante_4_againTRY_BAT alpha1 alpha2 lv1 rel1 lv2 rel2 atm2)
        as [lv' [atm' [Hat' [rel' [Hrel' [Hin' H']]]]]]; try assumption.
apply Hat2. apply Hat2.

      exists lv'. exists atm'. apply pair. apply pair; apply Hat'.
      left. exists rel'. apply conj. assumption.
      apply conj. all: try assumption.

      destruct (preprocess_sSahlq_ante_6_againTRY_BAT alpha1 alpha2 lv1 rel1 lv2 atm2)
        as [lv' [atm' [Hat' [rel' [Hrel' [Hin' H']]]]]]; try assumption.
apply Hat2. apply Hat2.
      exists lv'. exists atm'. apply pair.
apply pair. apply Hat'. apply Hat'.
      left. exists rel'. apply conj. assumption.
      apply conj. all: try assumption.

    destruct (trying1 alpha2) as [Hocc1b | Hocc2b].
    destruct (preprocess_vsSahlq_ante_notocc_againTRY_BAT _ H1' 
      (is_in_FOvar_app_r _ _ _ Hin0) Hocc1b)
      as [lv2 [rel2 [Hrel2 [Hin2 SOt]]]].
    destruct IHalpha1 as [lv1 [atm1 [Hat1 [[rel1 [Hrel1 [Hin H2]]] | [Hin H2]]]]].
    apply (is_in_FOvar_app_l _ _ _ Hin0).
      assumption.

      destruct (preprocess_sSahlq_ante_2_againTRY_BAT alpha1 alpha2 lv1 rel1 atm1 lv2 rel2)
        as [lv' [atm' [Hat' [rel' [Hrel' [Hin' H']]]]]]; try assumption.
 apply Hat1. apply Hat1. apply SOt.
      exists lv'. exists atm'. apply pair.
apply pair. apply Hat'. apply Hat'.
(*  apply Hat1. assumption. *)
      left. exists rel'. apply conj. assumption.
      apply conj. all: try assumption.

      destruct (preprocess_sSahlq_ante_8_againTRY alpha1 alpha2 lv1 atm1 lv2 rel2)
        as [lv' [atm' [Hat' [rel' [Hrel' [Hin' H']]]]]]; try assumption.
apply Hat1.
apply Hat1.
apply SOt.
      exists lv'. exists atm'. apply pair. assumption.
      left. exists rel'. apply conj. assumption.
      apply conj. all: try assumption.

      destruct (IHalpha1 (is_in_FOvar_app_l _ _ _ Hin0) Hocc2) as [lv1 [atm1 [Hatm1 [[rel1 [Hrel1 [Hin SOt]] ] | [Hin SOt ] ]]] ].
      destruct (IHalpha2 (is_in_FOvar_app_r _ _ _ Hin0) Hocc2b) as [lv2 [atm2 [Hatm2 [[rel2 [Hrel2 [Hin2 SOt2]] ] | [Hin2 SOt2 ] ]]] ].

      destruct (preprocess_sSahlq_ante_1_againTRY alpha1 alpha2 lv1 rel1 atm1 lv2 rel2 atm2)
        as [lv' [atm' [Hat' [rel' [Hrel' [Hin' H']]]]]]; try assumption.
apply Hatm1.
apply Hatm2.
apply Hatm1.
apply Hatm2.
      exists lv'. exists atm'. apply pair.
apply pair. apply Hat'. apply Hat'.
      left. exists rel'. apply conj. assumption.
      apply conj. all: try assumption.

      destruct (preprocess_sSahlq_ante_3_againTRY alpha1 alpha2 lv1 rel1 atm1 lv2 atm2)
        as [lv' [atm' [Hat' [rel' [Hrel' [Hin' H']]]]]]; try assumption.
apply Hatm1.
apply Hatm2.
apply Hatm1.
apply Hatm2.
      exists lv'. exists atm'. apply pair. assumption.
      left. exists rel'. apply conj. assumption.
      apply conj. all: try assumption.

      destruct (IHalpha2 (is_in_FOvar_app_r _ _ _ Hin0) Hocc2b) as [lv2 [atm2 [Hatm2 [[rel2 [Hrel2 [Hin2 SOt2]] ] | [Hin2 SOt2 ] ]]] ].

      destruct (preprocess_sSahlq_ante_7_againTRY alpha1 alpha2 lv1 atm1 lv2 rel2 atm2)
        as [lv' [atm' [Hat' [rel' [Hrel' [Hin' H']]]]]]; try assumption.
apply Hatm1.
apply Hatm2.
apply Hatm1.
apply Hatm2.
 
      exists lv'. exists atm'. apply pair. assumption.
      left. exists rel'. apply conj. assumption.
      apply conj. all: try assumption.

      destruct (preprocess_sSahlq_ante_9_againTRY alpha1 alpha2 lv1 atm1 lv2 atm2)
        as [lv' [atm' [Hat' [Hin' H']]]]; try assumption.
apply Hatm1.
apply Hatm2.
apply Hatm1.
apply Hatm2.

      exists lv'. exists atm'. apply pair. assumption.
      right. apply conj. assumption.
      assumption.

(* rewrite H1' in *.
case_eq (BAT alpha1); intros Hbat1; rewrite Hbat1 in *.
case_eq (BAT alpha2); intros Hbat2; rewrite Hbat2 in *.
all : try discriminate. *)

exists nil. exists (conjSO alpha1 alpha2). apply pair.
apply pair. reflexivity.
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
apply pair. reflexivity.
simpl. rewrite Hbat1. assumption.
right. simpl. apply conj.
apply is_in_pred_l_refl.
intros. apply iff_refl.
Qed.



(* Not true, since sSahlq_ante can have inermost boxes. *)
Lemma sSahlq_ante_conjSO_exFO_relatSO : forall phi x,
  sSahlq_ante phi = true ->
  conjSO_exFO_relatSO (ST phi x) = true.
Proof.
Admitted.
(*   induction phi; intros [xn] Hvs;
    try (simpl in *; discriminate).

    destruct p; reflexivity.

    apply sSahlq_ante_mconj in Hvs.
    simpl.
    rewrite IHphi1. apply IHphi2.
    apply Hvs. apply Hvs.

    simpl in *.
    apply IHphi; assumption.
Qed.
 *)
Lemma sS_lem_f7_gen_pre : forall l n,
Nat.leb (max_FOv_l l) n = true ->
is_in_FOvar (Var (S n)) l = false.
Proof.
  induction l; intros n H.
    reflexivity.

    simpl in *. destruct a as [xn].
    destruct xn. simpl in *. apply IHl. assumption.
    case_eq (beq_nat n xn); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq) in *.
      pose proof (max_leb_l (Nat.max (S xn) (max_FOv_l l)) (S xn) _ eq_refl) as H2.
      pose proof (leb_trans _ _ _ H2 H) as H3.
      rewrite leb_suc_f in H3. discriminate.

      apply IHl. apply leb_max in H. apply H.
Qed.

Lemma sS_lem_f7_gen : forall alpha n,
  Nat.leb (max_FOv alpha) n = true ->
  is_in_FOvar (Var (S n)) (FOvars_in alpha) = false.
Proof.
  intros alpha n H. rewrite <- max_FOv_l_FOvars_in in H.
  apply sS_lem_f7_gen_pre. assumption.
Qed.



Lemma sS_preprocessing_Step1_1_againTRY'_withex'' : forall phi1 phi2 rel atm x lv,
  sSahlq_ante phi1 = true ->
  uniform_pos phi2 ->
  is_in_FOvar (Var 0) lv = false ->
  REL rel = true ->
  BAT atm = true ->
          is_in_pred_l (preds_in (conjSO rel atm)) (preds_in (ST phi1 x)) = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
      (Ir : W -> W -> Prop),
    SOturnst W Iv Ip Ir (ST phi1 x) <->
    SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv)) ->
existsT2 lv0 : list FOvariable,
     ((existsT2 atm0 : SecOrder,
        (is_in_FOvar (Var 0) lv0 = false) *
         (BAT atm0 = true) *
((is_in_FOvar (Var (new_FOv_pp_pre2 atm0)) (FOvars_in atm0) = false) *
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
  intros phi1 phi2 rel atm x lv Hvsa Hun Hin0 HREL HAT Hin H.
  pose proof (equiv_implSO2 _ _ (ST phi2 x) H) as H1.
  pose proof (equiv3_3_struc2_2' lv (conjSO rel atm) (ST phi2 x)) as H2.
  pose proof (SOturnst_trans _ _ _ H1 H2) as H3.
  pose proof rename_FOv_A_rel_atm.
  destruct (rename_FOv_A_rel_batm lv rel atm (ST phi2 x) HREL HAT)
     as [rel' [atm' [H' [HREL' HAT']]]] . assumption.
  rewrite H' in *.
  exists (rename_FOv_A_list (conjSO rel atm) (ST phi2 x) lv).
  exists atm'.
  apply pair.
apply pair.
apply is_in_FOvar_rename_FOv_A_list_0. assumption. apply pair.
unfold new_FOv_pp_pre2.
apply sS_lem_f7_gen. apply leb_refl.

  left.
  exists rel'.
  apply conj. assumption.
  apply conj. 2: assumption.
    rewrite <- H'.
    rewrite preds_in_rename_FOv_A.
    assumption.
Defined.

Lemma sS_lem_f7 : forall alpha n,
  is_BOXATM_flag_strong_CONJ alpha = true ->
  Nat.leb (max_FOv alpha) n = true ->
  is_in_FOvar (Var (S n)) (FOvars_in alpha) = false.
Proof.
Admitted.



(*   induction alpha; intros n Hat Hleb; try discriminate.
    destruct p. destruct f as [m]. simpl in *.
    destruct m. reflexivity. case_eq (beq_nat n m); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq) in *. 
      rewrite my_arith__my_leb_nat.leb_suc_f in Hleb. discriminate.

      reflexivity.

    simpl. destruct f as [xn]. destruct xn. simpl in *. discriminate.
    case_eq (beq_nat n xn); intros Hbeq.
admit.
    simpl in Hat. destruct alpha; try discriminate.
    destruct alpha1; try discriminate. destruct f as [y1].
    destruct f0 as [y2]. case_eq (beq_nat xn y1);
      intros Hbeq2; rewrite Hbeq2 in *. 2 : discriminate.
    destruct y2. discriminate.
    case_eq (beq_nat xn y2); intros Hbeq3; rewrite Hbeq3 in *.
      2 : discriminate.
    case_eq (beq_nat (S y2) (S y1)); intros Hbeq4; rewrite Hbeq4 in *.
      2 : discriminate.
    simpl FOvars_in. simpl in Hbeq4.
    rewrite (beq_nat_true _ _ Hbeq4) in *.
    rewrite (beq_nat_true _ _ Hbeq2) in *.
    simpl in IHalpha.

 destruct y1. 
    apply IHalpha.

    simpl.
    rewrite is_in_FOvar_app. rewrite IHalpha1. apply IHalpha2.
      apply (AT_conjSO_r _ _ Hat).
      simpl in Hleb. apply leb_max in Hleb.
      apply Hleb.

      apply (AT_conjSO_l _ _ Hat).
      simpl in Hleb. apply leb_max in Hleb.
      apply Hleb.
Qed.
 *)
Lemma sS_lem_f1'' : forall alpha,
is_BOXATM_flag_strong_CONJ alpha = true ->
  is_in_FOvar (Var (S (max_FOv alpha))) (FOvars_in alpha) = false.
Proof.
  intros alpha Hat. apply sS_lem_f7. assumption. apply leb_refl.
Qed.

Lemma sS_lem_f1''_gen : forall alpha,
  is_in_FOvar (Var (S (max_FOv alpha))) (FOvars_in alpha) = false.
Proof.
  intros alpha. apply sS_lem_f7_gen. apply leb_refl.
Qed.

Lemma sS_preprocessing_Step1_3_againTRY'_withex' : forall phi1 phi2 atm x lv,
  sSahlq_ante phi1 = true ->
  uniform_pos phi2 ->
  is_in_FOvar (Var 0) lv = false ->
  BAT atm = true ->
  is_in_pred_l (preds_in (atm)) (preds_in (ST phi1 x)) = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
      (Ir : W -> W -> Prop),
    SOturnst W Iv Ip Ir (ST phi1 x) <->
    SOturnst W Iv Ip Ir (list_closed_exFO atm lv)) ->
existsT2 lv0 : list FOvariable,
   (existsT2 atm0 : SecOrder,
      (is_in_FOvar (Var 0) lv0 = false) *
       (BAT atm0 = true) *
((is_in_FOvar (Var (new_FOv_pp_pre2 atm0)) (FOvars_in atm0) = false) *

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
      SOturnst W Iv Ip Ir (list_closed_allFO (implSO atm0 (ST phi2 x)) lv0))))).
Proof.
  intros phi1 phi2 atm x lv Hvsa Hun Hin0 HAT Hin H.
  pose proof (equiv_implSO2 _ _ (ST phi2 x) H) as H1.
  pose proof (equiv3_3_struc2_2' lv atm (ST phi2 x)) as H2.
  pose proof (SOturnst_trans _ _ _ H1 H2) as H3.
  pose proof (same_struc_BAT2_rename_FOv_A atm (ST phi2 x) lv) as H4.
  apply same_struc_BAT2_comm in H4.
  apply same_struc_BAT2_2 in H4. 2 : assumption.
  exists (rename_FOv_A_list atm (ST phi2 x) lv).
  exists (rename_FOv_A atm (ST phi2 x) lv).
  apply pair.
apply pair.
rewrite is_in_FOvar_rename_FOv_A_list_0. reflexivity.
 assumption.
  apply pair.
   unfold new_FOv_pp_pre2. 
    apply (sS_lem_f1''_gen ).

  right.
  apply conj.
    rewrite preds_in_rename_FOv_A. assumption.
  assumption. assumption.
Defined.

Lemma is_in_FOvar_ST_0_not : forall phi x,
  ~ x = Var 0 ->
  is_in_FOvar (Var 0) (FOvars_in (ST phi x)) = false.
Proof.
  induction phi; intros [xn] H.
    simpl. destruct p. simpl. destruct xn. 
    contradiction (H eq_refl). reflexivity.

    simpl. apply IHphi. assumption.

    simpl. rewrite is_in_FOvar_app.
    rewrite IHphi1. apply IHphi2.
    all : try assumption.

    simpl. rewrite is_in_FOvar_app.
    rewrite IHphi1. apply IHphi2.
    all : try assumption.

    simpl. rewrite is_in_FOvar_app.
    rewrite IHphi1. apply IHphi2.
    all : try assumption.

    simpl in *. rewrite <- one_suc.
    destruct xn. contradiction (H eq_refl).
    apply IHphi. discriminate.

    simpl in *. rewrite <- one_suc.
    destruct xn. contradiction (H eq_refl).
    apply IHphi. discriminate.
Qed. 

Lemma sS_preprocessing_Step1_pre_againTRY'_withex' : forall phi1 phi2 x,
  ~ x = Var 0 ->
  sSahlq_ante phi1 = true ->
  uniform_pos phi2  ->
  existsT2 lv : list FOvariable,
   (existsT2 atm : SecOrder,
       (is_in_FOvar (Var 0) lv = false) *
       (BAT atm = true) *
((is_in_FOvar (Var (new_FOv_pp_pre2 atm)) (FOvars_in atm) = false) *
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
  intros phi1 phi2 x Hnot Hvsa Hun.
  pose proof (preprocess_sSahlq_ante_againTRY (ST phi1 x)
      (sSahlq_ante_conjSO_exFO_relatSO_BAT _ _ Hvsa) 
      (is_in_FOvar_ST_0_not phi1 x Hnot) (ex_P_ST phi1 x)) as H1.
  destruct H1 as [lv [atm [[Hin1 HAT] [ [rel [HREL [Hin H]]] | [Hin H] ]]]].
  
    apply sS_preprocessing_Step1_1_againTRY'_withex'' with (phi2 := phi2) in H; try assumption.
    apply sS_preprocessing_Step1_3_againTRY'_withex' with (phi2 := phi2) in H; try assumption.
Defined.

Lemma sSahlq_lem_f4 : forall atm x P,
is_BOXATM_flag_strong_CONJ atm = true ->
  is_in_FOvar x (FOvars_in atm) = false ->
is_in_FOvar x (fun2 atm P) = false.
Proof.
Admitted.
(*   induction atm; intros [xn] [Pn] Hat Hin; try discriminate.
    destruct p as [Qm]. destruct f as [ym]. simpl in *.
    case_eq (beq_nat Pn Qm); intros Hbeq.
      simpl. case_eq (beq_nat xn ym); intros Hbeq2;
        rewrite Hbeq2 in *. discriminate.

        reflexivity.
      reflexivity.
admit.

    pose proof (AT_conjSO_l _ _ Hat).
    pose proof (AT_conjSO_r _ _ Hat).
    simpl in Hin.
    rewrite is_in_FOvar_app in Hin. 
    case_eq (is_in_FOvar (Var xn) (FOvars_in atm1));
      intros Hin1; rewrite Hin1 in *. discriminate.
    simpl. rewrite is_in_FOvar_app. rewrite IHatm1.
    rewrite IHatm2. reflexivity.
    all : assumption.
Qed.
 *)

Lemma sSahlq_lem_f4_BAT_num_conn : forall m n  batm x P,
  n = num_conn batm ->
  Nat.leb n m = true ->
BAT batm = true ->
  is_in_FOvar x (FOvars_in batm) = false ->
is_in_FOvar x (fun2 batm P) = false.
Proof.
  induction m; intros n batm x P Hnum Hleb Hbat Hin.
    destruct n. 2 : discriminate.
    destruct batm ; try discriminate.
    destruct P as [Pn]. destruct x as [xn].
    destruct p as [Qm]. destruct f as [ym]. simpl in *.
    case_eq (beq_nat Pn Qm); intros Hbeq.
      simpl. case_eq (beq_nat xn ym); intros Hbeq2;
        rewrite Hbeq2 in *. discriminate.

        reflexivity.
      reflexivity.

    destruct n.
    destruct batm ; try discriminate.
    destruct P as [Pn]. destruct x as [xn].
    destruct p as [Qm]. destruct f as [ym]. simpl in *.
    case_eq (beq_nat Pn Qm); intros Hbeq.
      simpl. case_eq (beq_nat xn ym); intros Hbeq2;
        rewrite Hbeq2 in *. discriminate.

        reflexivity.
      reflexivity.

    destruct batm; try discriminate.
    destruct batm; try discriminate.
    destruct batm1; try discriminate.
    simpl fun2. apply (IHm (num_conn batm2) batm2).
      reflexivity.

inversion Hnum as [Hnum']. rewrite Hnum' in *.
simpl in *. destruct m. discriminate.
    apply leb_suc_l. assumption.

      apply is_BOXATM_flag_strong__CONJ_BAT in Hbat.
      apply BOXATM_flag_weak_BAT in Hbat. assumption.

      simpl FOvars_in in Hin.
      apply is_in_FOvar_cons_f in Hin. destruct Hin as [Hin H2].
      apply is_in_FOvar_cons_f in Hin. destruct Hin as [Hin H3].
      apply is_in_FOvar_cons_f in Hin. destruct Hin as [Hin H4].
      assumption.

    simpl fun2. rewrite is_in_FOvar_app.
    simpl in Hin.
    assert (Nat.leb (num_conn batm1) m = true) as Hass.
        rewrite Hnum in Hleb. simpl in Hleb.
        apply leb_plus_take1 in Hleb. assumption.
    assert (Nat.leb (num_conn batm2) m = true) as Hass2.
        rewrite Hnum in Hleb. simpl in Hleb.
        apply leb_plus_take2 in Hleb. assumption.

    rewrite (IHm (num_conn batm1) batm1 _ _ eq_refl Hass (BAT_conjSO_l _ _ Hbat)
      (is_in_FOvar_app_l _ _ _ Hin)).
    apply (IHm (num_conn batm2) batm2 _ _ eq_refl Hass2 (BAT_conjSO_r _ _ Hbat)
      (is_in_FOvar_app_r _ _ _ Hin)).
Qed.

Lemma sSahlq_lem_f4_BAT : forall atm x P,
BAT atm = true ->
  is_in_FOvar x (FOvars_in atm) = false ->
is_in_FOvar x (fun2 atm P) = false.
Proof.
  intros atm x P. apply (sSahlq_lem_f4_BAT_num_conn (num_conn atm)
    (num_conn atm) _ _ _ eq_refl (leb_refl _)).
Qed.

Lemma sSahlq_lem_f3 : forall lP atm x,
is_BOXATM_flag_strong_CONJ atm = true ->
  is_in_FOvar x (FOvars_in atm) = false ->
ex_FOvar_x_ll x (FOv_att_P_l atm lP) = false.
Proof.
  induction lP; intros atm x Hat H.
    simpl in *. reflexivity.

    simpl in *. rewrite sSahlq_lem_f4. apply IHlP.
    all : try assumption.
Qed.

Lemma sSahlq_lem_f3_BAT : forall lP atm x,
BAT atm = true ->
  is_in_FOvar x (FOvars_in atm) = false ->
ex_FOvar_x_ll x (FOv_att_P_l atm lP) = false.
Proof.
  induction lP; intros atm x Hat H.
    simpl in *. reflexivity.

    simpl in *. rewrite sSahlq_lem_f4_BAT. apply IHlP.
    all : try assumption.
Qed.

Lemma ttry : forall m n batm x,
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
    rewrite try3 with (x := (Var x3)). reflexivity.
    assumption. inversion Hnum. reflexivity.
    apply leb_suc_l in Hleb. assumption.
Qed.

Lemma ttry_BAT : forall m n batm x,
  n = num_conn batm ->
  Nat.leb n m = true ->
  BOXATM_flag_weak batm x = true ->
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
(*     case_eq (beq_nat x3 (S x2)); intros Hbeq3; rewrite Hbeq3 in *.
      2 : discriminate. *)
    rewrite (beq_nat_true _ _ Hbeq2) in *.
    destruct n. discriminate.
    rewrite (IHm n batm2 (Var x3)) at 1; try assumption.
    rewrite try3_BAT with (x := (Var x3)). reflexivity.
    assumption. inversion Hnum. reflexivity.
    apply leb_suc_l in Hleb. assumption.
Qed.


Lemma ttry' : forall batm x,
  BOXATM_flag_strong batm x = true ->
    batm = (fun5'' (batm_comp_P batm) (batm_comp_x1 batm) (batm_comp_lx batm)).
Proof.
  intros batm x. apply (ttry (num_conn batm) (num_conn batm)).
  reflexivity. apply leb_refl.
Qed.

Lemma ttry'_BAT : forall batm x,
  BOXATM_flag_weak batm x = true ->
    batm = (fun5'' (batm_comp_P batm) (batm_comp_x1 batm) (batm_comp_lx batm)).
Proof.
  intros batm x. apply (ttry_BAT (num_conn batm) (num_conn batm)).
  reflexivity. apply leb_refl.
Qed.

Lemma fun5_l''_cons : forall lP lx1 lxn P x1 xn ,
  ~ lP = nil ->
  ~ lx1 = nil ->
  ~ lxn = nil ->
  fun5_l'' (cons P lP) (cons x1 lx1) (cons xn lxn) =
  conjSO (fun5'' P x1 xn) (fun5_l'' lP lx1 lxn).
Proof.
  intros until 0. intros H1 H2 H3.
  simpl. destruct lP. contradiction (H1 eq_refl).
  destruct lx1. contradiction (H2 eq_refl).
  destruct lxn. contradiction (H3 eq_refl).
  reflexivity.
Qed.

Lemma fun5_l''_app : forall l1a l1b l2a l2b l3a l3b,
  length l1a = length l2a ->
  length l1a = length l3a ->
  forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (fun5_l'' (app l1a l1b) (app l2a l2b) (app l3a l3b)) <->
  SOturnst W Iv Ip Ir (conjSO (fun5_l'' l1a l2a l3a) (fun5_l'' l1b l2b l3b)).
Proof.
  induction l1a; intros l1b l2a l2b l3a l3b H2 H3 W Iv Ip Ir.
    destruct l2a. destruct l3a. simpl.
    split; intros H. apply conj. reflexivity. assumption.
    apply H.
    all : try discriminate.

    destruct l2a. discriminate. destruct l3a. discriminate.
    case_eq l1a. intros Hl1a. rewrite Hl1a in *.
      destruct l2a. destruct l3a. all : try discriminate.
      simpl app. destruct l1b. destruct l2b. destruct l3b.
      simpl. split; intros H. apply conj. assumption. reflexivity. apply H.

      simpl. split; intros H. apply conj. assumption. reflexivity. apply H.

      destruct l3b.
      simpl. split; intros H. apply conj. assumption. reflexivity. apply H.
      simpl. split; intros H. apply conj. assumption. reflexivity. apply H.

      destruct l2b. destruct l3b.
      simpl. split; intros H. apply conj. assumption. destruct l1b; reflexivity. apply H.

      simpl. split; intros H. apply conj. assumption. destruct l1b; reflexivity. apply H.

      destruct l3b. 
      simpl. split; intros H. apply conj. assumption. destruct l1b;  destruct l2b; reflexivity. apply H.

      rewrite SOturnst_conjSO. 
      split; intros SOt;
        apply conj; apply SOt.

  intros P l1a' Hl1a. rewrite Hl1a in *. rewrite <- Hl1a.
  case_eq l2a. intros Hl2a. rewrite Hl2a in *. discriminate.
  intros x1 lx1 Hl2a. rewrite <- Hl2a.
  case_eq l3a. intros Hl3a. rewrite Hl3a in *. discriminate.
  intros xn lxn Hl3a. rewrite <- Hl3a. simpl app.
  rewrite fun5_l''_cons.
  rewrite fun5_l''_cons.
  do 3 rewrite SOturnst_conjSO.
  split; intros [SOt1 SOt2].  
    rewrite <- Hl1a in *. simpl in SOt2.
    simpl in *. apply IHl1a in SOt2. destruct SOt2.
    apply conj. apply conj. all : try assumption.
    inversion H2. reflexivity.
    inversion H3. reflexivity.

    rewrite <- Hl1a in *.
    simpl in *. destruct SOt1 as [SOt1 SOt3].
    apply conj. assumption. apply IHl1a.
    inversion H2. reflexivity.
    inversion H3. reflexivity.
    apply conj; assumption.

    rewrite Hl1a. discriminate.
    rewrite Hl2a. discriminate.
    rewrite Hl3a. discriminate.

    rewrite Hl1a. discriminate.
    rewrite Hl2a. discriminate.
    rewrite Hl3a. discriminate.
Qed.

Lemma fun5_l''_rep_pred_l_app : forall  l1a l1b l2a l2b l3a l3b lP lx lcond,
  length l1a = length l2a ->
  length l1a = length l3a ->
  forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (replace_pred_l (fun5_l'' (app l1a l1b) (app l2a l2b) (app l3a l3b)) lP lx lcond) <->
  SOturnst W Iv Ip Ir (replace_pred_l (conjSO (fun5_l'' l1a l2a l3a) (fun5_l'' l1b l2b l3b)) lP lx lcond).
Proof.
  induction l1a; intros l1b l2a l2b l3a l3b lP lx lcond H2 H3 W Iv Ip Ir.
    destruct l2a. destruct l3a. simpl. all : try discriminate.
    rewrite rep_pred_l_conjSO. simpl.
    split; intros H.
      apply conj. rewrite rep_pred_l_eqFO. reflexivity.
      assumption.

      apply H.

    destruct l2a. discriminate. destruct l3a. discriminate.
    case_eq l1a. intros Hl1a. rewrite Hl1a in *.
      destruct l2a. destruct l3a. all : try discriminate.
      simpl app. destruct l1b. destruct l2b. destruct l3b.
      simpl.
      rewrite rep_pred_l_conjSO.
      split; intros H. apply conj. assumption.
        rewrite rep_pred_l_eqFO. reflexivity. apply H.

      simpl.  rewrite rep_pred_l_conjSO.
      split; intros H. apply conj. assumption.
        rewrite rep_pred_l_eqFO. reflexivity. apply H.

      destruct l3b.
      simpl. rewrite rep_pred_l_conjSO.
      split; intros H. apply conj. assumption.
         rewrite rep_pred_l_eqFO. reflexivity. apply H.
      simpl. rewrite rep_pred_l_conjSO.
      split; intros H. apply conj. assumption. 
        rewrite rep_pred_l_eqFO. reflexivity. apply H.

      destruct l2b. destruct l3b.
      simpl. rewrite rep_pred_l_conjSO.
      split; intros H. apply conj. assumption. destruct l1b;
        rewrite rep_pred_l_eqFO; reflexivity. apply H.

      simpl. rewrite rep_pred_l_conjSO.
      split; intros H. apply conj. assumption. destruct l1b; 
        rewrite rep_pred_l_eqFO; reflexivity. apply H.

      destruct l3b. 
      simpl. rewrite rep_pred_l_conjSO. 
      split; intros H. apply conj. assumption. destruct l1b;  destruct l2b; 
        rewrite rep_pred_l_eqFO; reflexivity. apply H.

rewrite fun5_l''_cons.
simpl. apply iff_refl.
all : try discriminate.

  intros P l1a' Hl1a. rewrite Hl1a in *. rewrite <- Hl1a.
  case_eq l2a. intros Hl2a. rewrite Hl2a in *. discriminate.
  intros x1 lx1 Hl2a. rewrite <- Hl2a.
  case_eq l3a. intros Hl3a. rewrite Hl3a in *. discriminate.
  intros xn lxn Hl3a. rewrite <- Hl3a. simpl app.
  rewrite fun5_l''_cons.
  rewrite fun5_l''_cons.
  do 3 rewrite rep_pred_l_conjSO.
  do 3 rewrite SOturnst_conjSO.
  split; intros [SOt1 SOt2].  
    rewrite <- Hl1a in *. simpl in SOt2.
    simpl in *. apply IHl1a in SOt2.
    rewrite rep_pred_l_conjSO in SOt2. destruct SOt2.
    apply conj. apply conj. all : try assumption.
    inversion H2. reflexivity.
    inversion H3. reflexivity.

    rewrite <- Hl1a in *.
    simpl in *. destruct SOt1 as [SOt1 SOt3].
    apply conj. assumption. apply IHl1a.
    inversion H2. reflexivity.
    inversion H3. reflexivity.
    rewrite rep_pred_l_conjSO.
    apply conj; assumption.

    rewrite Hl1a. discriminate.
    rewrite Hl2a. discriminate.
    rewrite Hl3a. discriminate.

    rewrite Hl1a. discriminate.
    rewrite Hl2a. discriminate.
    rewrite Hl3a. discriminate.
Qed.

(* Lemma try5' : forall m n batm,
  n = num_conn batm ->
  Nat.leb n m = true ->
  is_BOXATM_flag_strong_CONJ batm = true ->
    forall W Iv Ip Ir,
      SOturnst W Iv Ip Ir batm <->
      SOturnst W Iv Ip Ir (fun5_l'' (batm_conj_comp_P batm) (batm_conj_comp_x1 batm) 
(batm_conj_comp_lx batm)).
Proof.
  induction m; intros n batm Hnum Hleb Hbox W Iv Ip Ir; try discriminate.
    destruct batm; try discriminate.
    destruct p. destruct f. simpl. reflexivity.

    destruct n; discriminate.

    destruct n; discriminate.

    destruct batm; try discriminate.
    destruct p. destruct f. simpl. reflexivity.

    simpl in Hnum. destruct n. discriminate. simpl in Hbox.
    destruct f as [xn]. destruct xn. discriminate.
    destruct batm; try discriminate.
    destruct batm1; try discriminate.
    destruct f as [x2]. destruct f0 as [x1].
    case_eq (beq_nat xn x2); intros Hbeq; rewrite Hbeq in *.
      2 : discriminate.
    case_eq (beq_nat (S xn) x1); intros Hbeq2; rewrite Hbeq2 in *.
      2 : discriminate.
    case_eq (beq_nat x1 (S x2)); intros Hbeq3; rewrite Hbeq3 in *.
      2 : discriminate.
    simpl fun5_l''. do 2 rewrite SOturnst_allFO.
    split; intros SOt d; specialize (SOt d); rewrite SOturnst_implSO in *;
      intros SOt2.  rewrite (beq_nat_true _ _ Hbeq2) in *.
(*       rewrite <- (beq_nat_true _ _ Hbeq3) in *.  *)
specialize (SOt SOt2).
      rewrite ttry' with (x := (Var x1))  in SOt.
      rewrite <- (try6 _ (Var (S xn)) (Var x2) (Var x1)) in SOt.
      simpl batm_comp_x1 in SOt. simpl next_FOvar in SOt.
      rewrite <- (beq_nat_true _ _ Hbeq3) in *. assumption.
      simpl. rewrite Hbeq. rewrite (beq_nat_true _ _ Hbeq3) in *.
      rewrite Hbeq. rewrite <- beq_nat_refl. rewrite (beq_nat_true _ _ Hbeq).
      assumption. assumption.
      
  rewrite (beq_nat_true _ _ Hbeq2) in *.
(*       rewrite <- (beq_nat_true _ _ Hbeq3) in *. *)
 specialize (SOt SOt2).
      rewrite ttry' with (x := (Var x1)) .
      rewrite <- (try6 _ (Var (S xn)) (Var x2) (Var x1)).
      simpl batm_comp_x1. simpl next_FOvar.
      rewrite <- (beq_nat_true _ _ Hbeq3) in *. assumption.
      simpl. rewrite Hbeq. rewrite (beq_nat_true _ _ Hbeq3) in *.
      rewrite Hbeq. rewrite <- beq_nat_refl. rewrite (beq_nat_true _ _ Hbeq).
      assumption. assumption.

    simpl in Hnum. simpl in Hbox.
    case_eq (is_BOXATM_flag_strong_CONJ batm1); intros H1;
      rewrite H1 in *. 2: discriminate.

    simpl. rewrite fun5_l''_app. simpl. split; intros [SOt1 SOt2];
      apply conj. apply (IHm (num_conn batm1) batm1); try assumption.
        reflexivity.
        rewrite Hnum in Hleb. simpl in Hleb.
        apply leb_plus_take1 in Hleb. assumption.

      apply (IHm (num_conn batm2) batm2); try assumption.
        reflexivity.

        rewrite Hnum in Hleb. simpl in Hleb.
        apply leb_plus_take2 in Hleb. assumption.

      apply (IHm (num_conn batm1) batm1) in SOt1; try assumption.
        reflexivity.
        rewrite Hnum in Hleb. simpl in Hleb.
        apply leb_plus_take1 in Hleb. assumption.

      apply (IHm (num_conn batm2) batm2) in SOt2; try assumption.
        reflexivity.

        rewrite Hnum in Hleb. simpl in Hleb.
        apply leb_plus_take2 in Hleb. assumption.
      apply length_batm_conj_comp_P_x1. assumption.
      apply length_batm_conj_comp_P_lx. assumption.
Qed. *)

Lemma try5'_BAT : forall m n batm,
  n = num_conn batm ->
  Nat.leb n m = true ->
  BAT batm = true ->
    forall W Iv Ip Ir,
      SOturnst W Iv Ip Ir batm <->
      SOturnst W Iv Ip Ir (fun5_l'' (batm_conj_comp_P batm) (batm_conj_comp_x1 batm) 
(batm_conj_comp_lx batm)).
Proof.
  induction m; intros n batm Hnum Hleb Hbox W Iv Ip Ir; try discriminate.
    destruct batm; try discriminate.
    destruct p. destruct f. simpl. reflexivity.

    destruct n; discriminate.

    destruct n; discriminate.

    destruct batm; try discriminate.
    destruct p. destruct f. simpl. reflexivity.

    simpl in Hnum. destruct n. discriminate. simpl in Hbox.
    destruct f as [xn]. (*  destruct xn. discriminate. *)
    destruct batm; try discriminate.
    destruct batm1; try discriminate.
    destruct f as [x2]. destruct f0 as [x1].
    rewrite <- beq_nat_refl in Hbox.
    case_eq (beq_nat xn x1); intros Hbeq; rewrite Hbeq in *.
      2 : discriminate.
(*     case_eq (beq_nat (S xn) x1); intros Hbeq2; rewrite Hbeq2 in *.
      2 : discriminate.
    case_eq (beq_nat x1 (S x2)); intros Hbeq3; rewrite Hbeq3 in *.
      2 : discriminate. *)
    simpl fun5_l''. do 2 rewrite SOturnst_allFO.
    split; intros SOt d; specialize (SOt d); rewrite SOturnst_implSO in *;
      intros SOt2.  rewrite (beq_nat_true _ _ Hbeq) in *.
(*       rewrite <- (beq_nat_true _ _ Hbeq3) in *.  *)
specialize (SOt SOt2).
      rewrite ttry'_BAT with (x := (Var x1))  in SOt.
      rewrite <- (try3_BAT _ _ Hbox) at 2; assumption. assumption.

(*       rewrite <- (try6 _ (Var (S xn)) (Var x2) (Var x1)) in SOt.
      simpl batm_comp_x1 in SOt. simpl next_FOvar in SOt.
      rewrite <- (beq_nat_true _ _ Hbeq3) in *. assumption.
      simpl. rewrite Hbeq. rewrite (beq_nat_true _ _ Hbeq3) in *.
      rewrite Hbeq. rewrite <- beq_nat_refl. rewrite (beq_nat_true _ _ Hbeq).
      assumption. assumption.
*)
  rewrite (beq_nat_true _ _ Hbeq) in *. 
(*       rewrite <- (beq_nat_true _ _ Hbeq3) in *. *)
 specialize (SOt SOt2).
      rewrite ttry'_BAT with (x := (Var x1)) .
      rewrite (try3_BAT _ _ Hbox) ; assumption. assumption.
(*       rewrite <- (try6 _ (Var (S xn)) (Var x2) (Var x1)).
      simpl batm_comp_x1. simpl next_FOvar.
      rewrite <- (beq_nat_true _ _ Hbeq3) in *. assumption.
      simpl. rewrite Hbeq. rewrite (beq_nat_true _ _ Hbeq3) in *.
      rewrite Hbeq. rewrite <- beq_nat_refl. rewrite (beq_nat_true _ _ Hbeq).
      assumption. assumption.
 *)
    simpl in Hnum. simpl in Hbox.

    case_eq (BAT batm1); intros H1;
      rewrite H1 in *. 2: discriminate.

    simpl. rewrite fun5_l''_app. simpl. split; intros [SOt1 SOt2];
      apply conj. apply (IHm (num_conn batm1) batm1); try assumption.
        reflexivity.
        rewrite Hnum in Hleb. simpl in Hleb.
        apply leb_plus_take1 in Hleb. assumption.

      apply (IHm (num_conn batm2) batm2); try assumption.
        reflexivity.

        rewrite Hnum in Hleb. simpl in Hleb.
        apply leb_plus_take2 in Hleb. assumption.

      apply (IHm (num_conn batm1) batm1) in SOt1; try assumption.
        reflexivity.
        rewrite Hnum in Hleb. simpl in Hleb.
        apply leb_plus_take1 in Hleb. assumption.

      apply (IHm (num_conn batm2) batm2) in SOt2; try assumption.
        reflexivity.

        rewrite Hnum in Hleb. simpl in Hleb.
        apply leb_plus_take2 in Hleb. assumption.
      apply length_batm_conj_comp_P_x1_BAT. assumption.
      apply length_batm_conj_comp_P_lx_BAT. assumption.
Qed.

Lemma try5'' : forall batm,
  BAT batm = true ->
    forall W Iv Ip Ir,
      SOturnst W Iv Ip Ir batm <->
      SOturnst W Iv Ip Ir (fun5_l'' (batm_conj_comp_P batm) (batm_conj_comp_x1 batm) 
(batm_conj_comp_lx batm)).
Proof.
  intros batm. apply (try5'_BAT (num_conn batm) (num_conn batm)).
  reflexivity. apply leb_refl.
Qed.


(* Lemma sS_lem_e1 : forall batm rel beta lx lP W Iv Ip Ir,
  REL rel = true ->
  is_BOXATM_flag_strong_CONJ batm = true ->
  SOturnst W Iv Ip Ir (list_closed_SO (list_closed_allFO (implSO (conjSO rel batm) beta) lx) lP) <->
  SOturnst W Iv Ip Ir (list_closed_SO (list_closed_allFO (implSO 
    (conjSO rel (fun5_l'' (batm_conj_comp_P batm) (batm_conj_comp_x1 batm) 
(batm_conj_comp_lx batm))) beta) lx) lP).
Proof.
  intros atm rel beta lx lP W Iv Ip Ir Hrel Hat.
  apply equiv_list_closed_SO. intros W1 Iv1 Ip1 Ir1.
  apply equiv_list_closed_allFO. intros W2 Iv2 Ip2 Ir2.
  split; intros SOt [H1 H2];
    apply SOt; simpl in *; apply conj. assumption.
    apply try5''; try assumption.

    assumption. apply (try5'' atm); assumption.
Qed. *)

Lemma sS_lem_e1_BAT : forall batm rel beta lx lP W Iv Ip Ir,
  REL rel = true ->
  BAT batm = true ->
  SOturnst W Iv Ip Ir (list_closed_SO (list_closed_allFO (implSO (conjSO rel batm) beta) lx) lP) <->
  SOturnst W Iv Ip Ir (list_closed_SO (list_closed_allFO (implSO 
    (conjSO rel (fun5_l'' (batm_conj_comp_P batm) (batm_conj_comp_x1 batm) 
(batm_conj_comp_lx batm))) beta) lx) lP).
Proof.
  intros atm rel beta lx lP W Iv Ip Ir Hrel Hat.
  apply equiv_list_closed_SO. intros W1 Iv1 Ip1 Ir1.
  apply equiv_list_closed_allFO. intros W2 Iv2 Ip2 Ir2.
  split; intros SOt [H1 H2];
    apply SOt; simpl in *; apply conj. assumption.
    apply try5''; try assumption.

    assumption. apply (try5'' atm); assumption.
Qed.

Lemma sS_lem118'_is_in_pred_pre_pre : forall alpha x,
  BOXATM_flag_strong alpha x = true ->
  is_BOXATM_flag_strong_CONJ alpha = true.
Admitted.

Lemma batm_comp_ln_max_FOv : forall atm,
is_BOXATM_flag_strong_CONJ atm = true ->
batm_comp_ln atm =
  (max_FOv atm) - match batm_comp_x1 atm with Var n => n end.
Admitted.

Lemma max_S : forall n,
  max n (S n) = S n.
Proof.
  induction n. reflexivity.
  simpl in *. rewrite IHn. reflexivity.
Qed.


Lemma BOXATM_flag_strong_max_FOv_pre : forall m n atm ym,
  n = num_conn atm ->
  Nat.leb n m = true ->
  BOXATM_flag_strong atm (Var ym) = true ->
  max ym (max_FOv atm) = max_FOv atm.
Proof.
  induction m; intros n atm ym Hnum Hleb H.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
    simpl in *. destruct f as [xn]. rewrite (beq_nat_true _ _ H).
    rewrite max_refl. reflexivity.

    destruct n.
    destruct atm; try discriminate.
    simpl in *. destruct f as [xn]. rewrite (beq_nat_true _ _ H).
    rewrite max_refl. reflexivity.

    destruct atm; try discriminate. destruct atm; try discriminate.
    destruct atm1; try discriminate.
    destruct f as [xn]. destruct f0 as [y1]. destruct f1 as [y2].
    simpl in *. case_eq (beq_nat ym y1); intros Hbeq;
      rewrite Hbeq in *. 2 : discriminate.
    simpl in *. case_eq (beq_nat xn y2); intros Hbeq2;
      rewrite Hbeq2 in *. 2 : discriminate.
    simpl in *. case_eq (beq_nat y2 (S y1)); intros Hbeq3;
      rewrite Hbeq3 in *. 2 : discriminate.
    rewrite (beq_nat_true _ _ Hbeq3).
    rewrite (beq_nat_true _ _ Hbeq).
    rewrite (beq_nat_true _ _ Hbeq2).
    rewrite <- (beq_nat_true _ _ Hbeq3).
    rewrite (beq_nat_true _ _ Hbeq3). rewrite max_S.
    rewrite (PeanoNat.Nat.max_assoc y1). rewrite max_S.
    reflexivity.
Qed.

Lemma BOXATM_flag_strong_max_FOv : forall atm2 ym,
  BOXATM_flag_strong atm2 (Var ym) = true ->
  max ym (max_FOv atm2) = max_FOv atm2.
Proof.
  intros atm2 ym. apply (BOXATM_flag_strong_max_FOv_pre (num_conn atm2) (num_conn atm2)).
  reflexivity. apply leb_refl.
Qed.

 Lemma BOXATM_flag_strong_max_nil_not : forall atm n,
  BOXATM_flag_strong atm (Var (S n)) = true ->
  ~max_FOv atm = 0.
Admitted.

Lemma batm_comp_ln_max_FOv_plus_pre : forall m n atm x,
  n = num_conn atm ->
  Nat.leb n m = true ->
BOXATM_flag_strong atm x = true ->
  (max_FOv atm) = plus (batm_comp_ln atm)  (match batm_comp_x1 atm with Var n => n end).
Proof.
  induction m; intros n atm x Hnum Hleb H.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
    simpl in *. reflexivity.

    destruct n.
    destruct atm; try discriminate.
    simpl in *. reflexivity.

    destruct atm; try discriminate. destruct x as [zn].
    destruct f as [xn]. simpl in *.
    destruct atm; try discriminate. destruct atm1; try discriminate.
    destruct f as [y1]. destruct f0 as [y2].
    simpl in *.
    case_eq (beq_nat zn y1); intros Hbeq; rewrite Hbeq in *. 2: discriminate.
    case_eq (beq_nat xn y2); intros Hbeq2; rewrite Hbeq2 in *. 2: discriminate.
    case_eq (beq_nat y2 (S y1)); intros Hbeq3; rewrite Hbeq3 in *. 2: discriminate.
    rewrite (beq_nat_true _ _ Hbeq3).
    rewrite max_S.
    rewrite BOXATM_flag_strong_max_FOv.
    destruct xn. destruct y2; discriminate.
    pose proof H as H'.
    apply try7 in H'. 
    specialize (IHm (num_conn atm2) atm2).
    rewrite H' in IHm.
    rewrite (BOXATM_flag_strong_max_FOv atm2 (S xn) H).
    rewrite plus_n_Sm. rewrite <- (beq_nat_true _  _ Hbeq3).
    rewrite <- (beq_nat_true _ _ Hbeq2). 
    apply (IHm (Var (S xn))). reflexivity.

    inversion Hnum as [Hnum'].
    rewrite Hnum' in Hleb.
    destruct m. discriminate. apply leb_suc_r. assumption.

      assumption.
rewrite <- (beq_nat_true _  _ Hbeq3).
    rewrite <- (beq_nat_true _ _ Hbeq2). 
    assumption.
Qed.

Lemma batm_comp_ln_max_FOv_plus : forall atm x,
BOXATM_flag_strong atm  x = true ->
  (max_FOv atm) = plus (batm_comp_ln atm)  (match batm_comp_x1 atm with Var n => n end).
Proof.
  intros atm x. apply (batm_comp_ln_max_FOv_plus_pre (num_conn atm) (num_conn atm)).
  reflexivity. apply leb_refl.
Qed.

Lemma is_BOXATM_flag_strong_CONJ_allFO_atm : forall atm x y1 y2,
  is_BOXATM_flag_strong_CONJ (allFO x (implSO (relatSO y1 y2) atm)) = true ->
  BOXATM_flag_strong atm y2 = true.
Proof.
  intros atm [xn] [y1] [y2] H.
  simpl in *. destruct xn. discriminate.
  case_eq (beq_nat xn y1); intros Hbeq; rewrite Hbeq in *.
    2 : discriminate.
  case_eq (beq_nat (S xn) y2); intros Hbeq2; rewrite Hbeq2 in *.
    2 : discriminate.
  case_eq (beq_nat y2 (S y1)); intros Hbeq3; rewrite Hbeq3 in *.
    2 : discriminate.
  rewrite (beq_nat_true _ _ Hbeq2) in *. assumption.
Qed.

Lemma is_BOXATM_flag_strong_CONJ_allFO_atm_BAT : forall atm x y1 y2,
  BAT (allFO x (implSO (relatSO y1 y2) atm)) = true ->
  BOXATM_flag_weak atm y2 = true.
Proof.
  intros atm [xn] [y1] [y2] H.
  simpl in *. (*  destruct xn. discriminate. *)
  rewrite <- beq_nat_refl in H.
  case_eq (beq_nat xn y2); intros Hbeq; rewrite Hbeq in *.
    2 : discriminate.
  rewrite (beq_nat_true _ _ Hbeq) in *. assumption.
Qed.

Lemma is_BOXATM_flag_strong_CONJ_allFO_x1 : forall atm x y1 y2,
  is_BOXATM_flag_strong_CONJ (allFO x (implSO (relatSO y1 y2) atm)) = true ->
  batm_comp_x1 atm = y2.
Proof.
  intros atm [xn] [y1] [y2] H.
  simpl in H. destruct xn. discriminate.
  case_eq (PeanoNat.Nat.eqb xn y1); intros Hbeq;
    rewrite Hbeq in *. 2 : discriminate.
  case_eq (PeanoNat.Nat.eqb (S xn) y2); intros Hbeq2;
    rewrite Hbeq2 in *. 2 : discriminate.
  case_eq (PeanoNat.Nat.eqb y2 (S y1)); intros Hbeq3;
    rewrite Hbeq3 in *. 2 : discriminate.
  apply try3 in H. rewrite (beq_nat_true _ _ Hbeq2) in *.
  assumption.
Qed.

Lemma is_BOXATM_flag_strong_CONJ_allFO_x1_BAT : forall atm x y1 y2,
  BAT (allFO x (implSO (relatSO y1 y2) atm)) = true ->
  batm_comp_x1 atm = y2.
Proof.
  intros atm [xn] [y1] [y2] H.
  simpl in H. (*  destruct xn. discriminate. *)
  rewrite <- beq_nat_refl in H.
  case_eq (PeanoNat.Nat.eqb xn y2); intros Hbeq;
    rewrite Hbeq in *. 2 : discriminate.
  apply try3_BAT in H. rewrite (beq_nat_true _ _ Hbeq) in *.
  assumption.
Qed.

Lemma is_BOXATM_flag_strong_CONJ_allFO_relatSO : forall atm x y1 y2,
  is_BOXATM_flag_strong_CONJ (allFO x (implSO (relatSO y1 y2) atm)) = true ->
  match y1, y2 with Var y1, Var y2 => y2 = S y1 end.
Proof.
  intros atm [xn] [y1] [y2] H.
  simpl in H. destruct xn. discriminate.
  case_eq (PeanoNat.Nat.eqb xn y1); intros Hbeq;  
    rewrite Hbeq in *. 2 : discriminate.
  case_eq (PeanoNat.Nat.eqb (S xn) y2); intros Hbeq2;
    rewrite Hbeq2 in *. 2 : discriminate.
  case_eq (PeanoNat.Nat.eqb y2 (S y1)); intros Hbeq3;
    rewrite Hbeq3 in *. 2 : discriminate.
  rewrite (beq_nat_true _ _ Hbeq3). reflexivity.
Qed.

Lemma is_BOXATM_flag_strong__CONJ2_pre : forall m n atm x,
n = num_conn atm ->
Nat.leb n m = true ->
  BOXATM_flag_strong atm x = true ->
  is_BOXATM_flag_strong_CONJ atm = true.
Proof.
  induction m; intros n atm x Hnum Hleb H.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
    reflexivity.

    destruct n.
    destruct atm; try discriminate.
    reflexivity.

    destruct atm; try discriminate. destruct atm; try discriminate.
    destruct atm1; try discriminate.
    destruct f as [ym]. destruct f0 as [y1]. destruct f1 as [y2].
    destruct x as [xn]. simpl in *.
    destruct ym. destruct y2; simpl in *; rewrite if_then_else_false in H; discriminate.
    case_eq (beq_nat xn y1); intros Hbeq; rewrite Hbeq in *. 2 : discriminate.
    case_eq (beq_nat (S ym) y2); intros Hbeq2; rewrite Hbeq2 in *. 2 : discriminate.
    case_eq (beq_nat y2 (S y1)); intros Hbeq3; rewrite Hbeq3 in *. 2 : discriminate.
    rewrite (beq_nat_true _ _ Hbeq3) in Hbeq2. simpl in Hbeq2. rewrite Hbeq2.
    assumption.
Qed.

Lemma is_BOXATM_flag_strong__CONJ2 : forall atm x,
  BOXATM_flag_strong atm x = true ->
  is_BOXATM_flag_strong_CONJ atm = true.
Proof.
  intros atm x. apply (is_BOXATM_flag_strong__CONJ2_pre (num_conn atm) (num_conn atm)).
  reflexivity. apply leb_refl.
Qed.

Lemma is_BOXATM_flag_strong__CONJ2_pre_BAT : forall m n atm x,
n = num_conn atm ->
Nat.leb n m = true ->
  BOXATM_flag_weak atm x = true ->
  BAT atm = true.
Proof.
  induction m; intros n atm x Hnum Hleb H.
    destruct n. 2 : discriminate.
    destruct atm; try discriminate.
    reflexivity.

    destruct n.
    destruct atm; try discriminate.
    reflexivity.

    destruct atm; try discriminate. destruct atm; try discriminate.
    destruct atm1; try discriminate.
    destruct f as [ym]. destruct f0 as [y1]. destruct f1 as [y2].
    destruct x as [xn]. simpl in *.
    rewrite <- beq_nat_refl.
    case_eq (beq_nat xn y1); intros Hbeq; rewrite Hbeq in *.
      2 : discriminate.
    case_eq (beq_nat ym y2); intros Hbeq2; rewrite Hbeq2 in *.
      2 : discriminate.
    assumption.
Qed.

Lemma is_BOXATM_flag_strong__CONJ2_BAT : forall atm x,
  BOXATM_flag_weak atm x = true ->
  BAT atm = true.
Proof.
  intros atm x. apply (is_BOXATM_flag_strong__CONJ2_pre_BAT (num_conn atm) (num_conn atm)).
  reflexivity. apply leb_refl.
Qed.

Lemma max_FOv_conjSO : forall alpha beta,
  max_FOv (conjSO alpha beta) =
  max (max_FOv alpha) (max_FOv beta).
Proof.
  reflexivity.
Qed.

Require Import List.


Lemma max_FOv_is_in_FOvar : forall alpha n,
(*   (exists x, is_in_FOvar x (FOvars_in alpha) = true) -> *)
  max_FOv alpha = n ->
  is_in_FOvar (Var n) (FOvars_in alpha) = true.
Proof.
  induction alpha; intros n Hmax.
    destruct p. destruct f. simpl in *. rewrite Hmax.
    rewrite <- beq_nat_refl. reflexivity.

    destruct f as [y1]. destruct f0 as [y2]. simpl in *.
(*     simpl in *. case_eq (beq_nat n y1); intros Hbeq.
      reflexivity.
    case_eq (beq_nat n y2); intros Hbeq2. reflexivity. *)
    destruct (max_or y1 y2) as [H | H]; rewrite H in Hmax;
    rewrite Hmax; rewrite <- beq_nat_refl. reflexivity.
    rewrite if_then_else_true. reflexivity.

    destruct f as [y1]. destruct f0 as [y2]. simpl in *.
(*     simpl in *. case_eq (beq_nat n y1); intros Hbeq.
      reflexivity.
    case_eq (beq_nat n y2); intros Hbeq2. reflexivity. *)
    destruct (max_or y1 y2) as [H | H]; rewrite H in Hmax;
    rewrite Hmax; rewrite <- beq_nat_refl. reflexivity.
    rewrite if_then_else_true. reflexivity.

    destruct f as [xn]. simpl in *.
    destruct (max_or xn (max_FOv alpha)) as [H | H];
      rewrite H in Hmax. rewrite Hmax. rewrite <- beq_nat_refl.
      reflexivity. 
      rewrite IHalpha. rewrite if_then_else_true.
    reflexivity. assumption.

    destruct f as [xn]. simpl in *.
    destruct (max_or xn (max_FOv alpha)) as [H | H];
      rewrite H in Hmax. rewrite Hmax. rewrite <- beq_nat_refl.
      reflexivity. 
      rewrite IHalpha. rewrite if_then_else_true.
    reflexivity. assumption.

    simpl in *. apply IHalpha. assumption.

    simpl in *. rewrite is_in_FOvar_app.
    destruct (max_or (max_FOv alpha1) (max_FOv alpha2)) as [H | H];
      rewrite H in Hmax. 
      rewrite IHalpha1. reflexivity. assumption.
      rewrite IHalpha2. rewrite if_then_else_true. reflexivity.
      assumption.

    simpl in *. rewrite is_in_FOvar_app.
    destruct (max_or (max_FOv alpha1) (max_FOv alpha2)) as [H | H];
      rewrite H in Hmax. 
      rewrite IHalpha1. reflexivity. assumption.
      rewrite IHalpha2. rewrite if_then_else_true. reflexivity.
      assumption.

    simpl in *. rewrite is_in_FOvar_app.
    destruct (max_or (max_FOv alpha1) (max_FOv alpha2)) as [H | H];
      rewrite H in Hmax. 
      rewrite IHalpha1. reflexivity. assumption.
      rewrite IHalpha2. rewrite if_then_else_true. reflexivity.
      assumption.

    simpl in *. apply IHalpha; assumption.

    simpl in *. apply IHalpha; assumption.
Qed.

Lemma max_max_FOv : forall alpha,
  is_in_FOvar (Var 0) (FOvars_in alpha) = false ->
  max (max_FOv alpha) 1 = max_FOv alpha.
Proof.
  induction alpha; intros H.
    destruct p. destruct f as [xn]. simpl in *.
    destruct xn. discriminate. simpl. destruct xn;
    reflexivity.

    destruct f as [y1]; destruct f0 as [y2].
    simpl in *. destruct y1. discriminate.
    destruct y2. discriminate.
    simpl. rewrite max_comm.  reflexivity.

    destruct f as [y1]; destruct f0 as [y2].
    simpl in *. destruct y1. discriminate.
    destruct y2. discriminate.
    simpl. rewrite max_comm.  reflexivity.

    destruct f as [xn]. destruct xn. discriminate.
    simpl in *. case_eq (max_FOv alpha). 
      intros H2. simpl. destruct xn; reflexivity.
      intros m Hm. simpl. rewrite max_comm. reflexivity.

    destruct f as [xn]. destruct xn. discriminate.
    simpl in *. case_eq (max_FOv alpha). 
      intros H2. simpl. destruct xn; reflexivity.
      intros m Hm. simpl. rewrite max_comm. reflexivity.

    simpl in *. apply IHalpha. assumption.

    simpl in *.  rewrite <- PeanoNat.Nat.max_assoc.
    rewrite IHalpha2. reflexivity.
    apply is_in_FOvar_app_r in H. assumption.

    simpl in *.  rewrite <- PeanoNat.Nat.max_assoc.
    rewrite IHalpha2. reflexivity.
    apply is_in_FOvar_app_r in H. assumption.

    simpl in *.  rewrite <- PeanoNat.Nat.max_assoc.
    rewrite IHalpha2. reflexivity.
    apply is_in_FOvar_app_r in H. assumption.

    simpl in *. apply IHalpha. assumption.

    simpl in *. apply IHalpha. assumption.
Qed.

Lemma max_FOv_fun5_l''_app' : forall la1 la2 lb1 lb2 lc1 lc2,
  length la1 = length lb1 ->
  length la1 = length lc1 ->
  is_in_FOvar (Var 0) (FOvars_in (fun5_l'' la1 lb1 lc1)) = false ->
  is_in_FOvar (Var 0) (FOvars_in (fun5_l'' la2 lb2 lc2)) = false ->
(*   ~ (max_FOv (fun5_l' la2 lb2 lc2)) = 1 -> *)
  max_FOv (fun5_l'' (app la1 la2) (app lb1 lb2) (app lc1 lc2)) =
  max (max_FOv (fun5_l'' la1 lb1 lc1)) (max_FOv (fun5_l'' la2 lb2 lc2)).
Proof.
  induction la1; intros la2 lb1 lb2 lc1 lc2 Hl1 Hl2 Hmax1 Hmax2.
    simpl in *. destruct lb1. destruct lc1. simpl.
    case_eq (max_FOv (fun5_l'' la2 lb2 lc2)). intros H.
      rewrite max_FOv_is_in_FOvar in Hmax2. discriminate.
      assumption. reflexivity. discriminate. discriminate.

    destruct lb1. discriminate. destruct lc1. discriminate.
    do 3 rewrite <- app_comm_cons.
case_eq la1.
  intros Hla1. rewrite Hla1 in *.
  destruct lb1. 2 : discriminate. destruct lc1. 2 : discriminate.
  do 3 rewrite app_nil_l.
  simpl fun5_l'' at 2.
  simpl. destruct la2. destruct lb2. simpl in *.
    rewrite max_max_FOv. reflexivity.
    assumption.

    simpl.
    rewrite max_max_FOv. reflexivity.
    assumption. 
    destruct lb2. simpl. destruct la2.
    rewrite max_max_FOv. reflexivity.
    assumption.
    rewrite max_max_FOv. reflexivity.
    assumption.

    destruct lc2. simpl. destruct la2; destruct lb2.
    rewrite max_max_FOv. reflexivity.
    assumption.
    rewrite max_max_FOv. reflexivity.
    assumption.
    rewrite max_max_FOv. reflexivity.
    assumption.
    rewrite max_max_FOv. reflexivity.
    assumption.

    rewrite max_FOv_conjSO. reflexivity.
intros P lP Hla1. rewrite <- Hla1.


(*   simpl in IHla1.
  simpl in *. *) 
    rewrite fun5_l''_cons.
    rewrite fun5_l''_cons.
    do 2 rewrite max_FOv_conjSO.

    rewrite IHla1.
    rewrite PeanoNat.Nat.max_assoc.
    reflexivity.

    simpl in Hl1. inversion Hl1. reflexivity.
    simpl in Hl2. inversion Hl2. reflexivity.

simpl in Hmax1. destruct la1; simpl in *. reflexivity.
  destruct lb1. discriminate.
  destruct la1. destruct lb1. destruct lc1. discriminate.
  simpl in Hmax1. apply is_in_FOvar_app_r in Hmax1. assumption.
  discriminate. destruct lb1. discriminate.
  destruct lc1. discriminate. destruct lc1. discriminate.
  simpl in Hmax1. apply is_in_FOvar_app_r in Hmax1. assumption.
  assumption. 

  rewrite Hla1. discriminate.
  destruct lb1. rewrite Hla1 in *. discriminate. discriminate.
  destruct lc1. rewrite Hla1 in *. discriminate. discriminate.
  rewrite Hla1. discriminate.
  simpl in Hl1. rewrite Hla1 in *. inversion Hl1.
    destruct lb1; discriminate.
  simpl in Hl2. rewrite Hla1 in *. inversion Hl2.
    destruct lc1; discriminate.
Qed.


Lemma max_FOv_batm_conj_comp_x1_0: forall atm,
  is_BOXATM_flag_strong_CONJ atm = true ->
  max_FOv atm = 0 ->
  exists n,
  batm_conj_comp_x1 atm = constant_l (Var 0) n.
Proof.
Admitted.

Lemma try : forall atm,
  is_BOXATM_flag_strong_CONJ atm = true ->
  ~ (batm_conj_comp_P atm = nil).
Proof.
  induction atm; intros H1 H2; try discriminate.
  simpl in H1. case_eq (is_BOXATM_flag_strong_CONJ atm1); 
    intros Hat1; rewrite Hat1 in *. 2 : discriminate.
  simpl in H2. apply app_rnil_r in H2. apply IHatm2; assumption.
Qed. 

Lemma is__BOXATM_flag_strong_CONJ : forall alpha x y1 y2,
  is_BOXATM_flag_strong_CONJ (allFO x (implSO (relatSO y1 y2) alpha)) = true ->
  BOXATM_flag_strong (allFO x (implSO (relatSO y1 y2) alpha)) y1 = true.
Proof.
  intros alpha [xn] [y1] [y2] H.
  simpl in *. rewrite <- beq_nat_refl.
  destruct xn. discriminate.
  case_eq (beq_nat xn y1); intros Hbeq; rewrite Hbeq in *. 2 : discriminate.
  assumption.
Qed.

Lemma is__BAT : forall alpha x y1 y2,
  BAT (allFO x (implSO (relatSO y1 y2) alpha)) = true ->
  BOXATM_flag_weak (allFO x (implSO (relatSO y1 y2) alpha)) y1 = true.
Proof.
  intros alpha [xn] [y1] [y2] H.
  simpl in *. rewrite <- beq_nat_refl.
  rewrite <- beq_nat_refl in H.
(*   destruct xn. discriminate. *)
  case_eq (beq_nat xn y2); intros Hbeq; rewrite Hbeq in *. 2 : discriminate.
  assumption.
Qed.