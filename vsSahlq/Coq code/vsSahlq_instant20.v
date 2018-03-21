Require Export vsSahlq_instant19.

Open Scope type_scope.

(* --------------------------------- *)
(* Belongs in vsSahlq_instant13 *)

Lemma preprocess_vsSahlq_ante_againTRY_loc : forall alpha x,
  closed_except alpha x ->
  conjSO_exFO_relatSO alpha = true ->
  (existsT P, P_occurs_in_alpha alpha P = true) ->
  existsT2 lv atm,
    (AT atm = true) *
    ((existsT rel,
      REL rel = true /\
      is_in_pred_l (preds_in (conjSO rel atm)) (preds_in alpha) = true /\
      closed_except (list_closed_exFO (conjSO rel atm) lv) x /\
        forall W Iv Ip Ir,
          SOturnst W Iv Ip Ir alpha <->
          SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv)) +
     (is_in_pred_l (preds_in atm) (preds_in alpha) = true /\
      closed_except(list_closed_exFO atm lv) x /\
        forall W Iv Ip Ir,
          SOturnst W Iv Ip Ir alpha <->
          SOturnst W Iv Ip Ir (list_closed_exFO atm lv))).
Proof.
Admitted.
(*  intros alpha H Hocc.
  induction alpha; try (simpl in *; discriminate).
    apply preprocess_vsSahlq_ante_predSO_againTRY; assumption.

    destruct Hocc as [[Pn] Hocc].
    unfold P_occurs_in_alpha in Hocc. destruct f. destruct f0.
    simpl in Hocc. discriminate.

    apply preprocess_vsSahlq_ante_exFO_againTRY; assumption.

    simpl in H.
    case_eq (conjSO_exFO_relatSO alpha1); intros H1;
      rewrite H1 in H; try discriminate.
    specialize (IHalpha1 H1).
    specialize (IHalpha2 H).
    destruct (trying1 alpha1) as [Hocc1 | Hocc2].
    destruct (preprocess_vsSahlq_ante_notocc_againTRY _ H1 Hocc1)
      as [lv1 [rel1 [Hrel1 [Hin1 SOt]]]].
    destruct IHalpha2 as [lv2 [atm2 [Hat2 [[rel2 [Hrel2 [Hin H2]]] | [Hin H2]]]]].
      destruct Hocc as [P Hocc].
      apply P_occurs_in_alpha_conjSO_comp in Hocc.
      rewrite (Hocc1 P) in Hocc.
      destruct Hocc. discriminate.
      exists P. assumption.

      destruct (preprocess_vsSahlq_ante_4_againTRY alpha1 alpha2 lv1 rel1 lv2 rel2 atm2)
        as [lv' [atm' [Hat' [rel' [Hrel' [Hin' H']]]]]]; try assumption.
      exists lv'. exists atm'. apply pair. assumption.
      left. exists rel'. apply conj. assumption.
      apply conj. all: try assumption.

      destruct (preprocess_vsSahlq_ante_6_againTRY alpha1 alpha2 lv1 rel1 lv2 atm2)
        as [lv' [atm' [Hat' [rel' [Hrel' [Hin' H']]]]]]; try assumption.
      exists lv'. exists atm'. apply pair. assumption.
      left. exists rel'. apply conj. assumption.
      apply conj. all: try assumption.

    destruct (trying1 alpha2) as [Hocc1b | Hocc2b].
    destruct (preprocess_vsSahlq_ante_notocc_againTRY _ H Hocc1b)
      as [lv2 [rel2 [Hrel2 [Hin2 SOt]]]].
    destruct IHalpha1 as [lv1 [atm1 [Hat1 [[rel1 [Hrel1 [Hin H2]]] | [Hin H2]]]]].
      assumption.

      destruct (preprocess_vsSahlq_ante_2_againTRY alpha1 alpha2 lv1 rel1 atm1 lv2 rel2)
        as [lv' [atm' [Hat' [rel' [Hrel' [Hin' H']]]]]]; try assumption.
      exists lv'. exists atm'. apply pair. assumption.
      left. exists rel'. apply conj. assumption.
      apply conj. all: try assumption.

      destruct (preprocess_vsSahlq_ante_8_againTRY alpha1 alpha2 lv1 atm1 lv2 rel2)
        as [lv' [atm' [Hat' [rel' [Hrel' [Hin' H']]]]]]; try assumption.
      exists lv'. exists atm'. apply pair. assumption.
      left. exists rel'. apply conj. assumption.
      apply conj. all: try assumption.

      destruct (IHalpha1 Hocc2) as [lv1 [atm1 [Hatm1 [[rel1 [Hrel1 [Hin SOt]] ] | [Hin SOt ] ]]] ].
      destruct (IHalpha2 Hocc2b) as [lv2 [atm2 [Hatm2 [[rel2 [Hrel2 [Hin2 SOt2]] ] | [Hin2 SOt2 ] ]]] ].

      destruct (preprocess_vsSahlq_ante_1_againTRY alpha1 alpha2 lv1 rel1 atm1 lv2 rel2 atm2)
        as [lv' [atm' [Hat' [rel' [Hrel' [Hin' H']]]]]]; try assumption.
      exists lv'. exists atm'. apply pair. assumption.
      left. exists rel'. apply conj. assumption.
      apply conj. all: try assumption.

      destruct (preprocess_vsSahlq_ante_3_againTRY alpha1 alpha2 lv1 rel1 atm1 lv2 atm2)
        as [lv' [atm' [Hat' [rel' [Hrel' [Hin' H']]]]]]; try assumption.
      exists lv'. exists atm'. apply pair. assumption.
      left. exists rel'. apply conj. assumption.
      apply conj. all: try assumption.

      destruct (IHalpha2 Hocc2b) as [lv2 [atm2 [Hatm2 [[rel2 [Hrel2 [Hin2 SOt2]] ] | [Hin2 SOt2 ] ]]] ].

      destruct (preprocess_vsSahlq_ante_7_againTRY alpha1 alpha2 lv1 atm1 lv2 rel2 atm2)
        as [lv' [atm' [Hat' [rel' [Hrel' [Hin' H']]]]]]; try assumption.
      exists lv'. exists atm'. apply pair. assumption.
      left. exists rel'. apply conj. assumption.
      apply conj. all: try assumption.

      destruct (preprocess_vsSahlq_ante_9_againTRY alpha1 alpha2 lv1 atm1 lv2 atm2)
        as [lv' [atm' [Hat' [Hin' H']]]]; try assumption.
      exists lv'. exists atm'. apply pair. assumption.
      right. apply conj. assumption.
      assumption.
Defined.
*)

(* --------------------------------- *)
(* Belongs in vsSahlq_instant19 *)


Lemma free_FO_list_closed_allFO_implSO : forall lv alpha beta x,
  free_FO (list_closed_allFO (implSO alpha beta) lv) x =
  free_FO (implSO (list_closed_allFO alpha lv) (list_closed_allFO beta lv)) x.
Proof.
  induction lv; intros alpha beta x. reflexivity.
  simpl. destruct x as [xn]. destruct a as [ym].
  case_eq (beq_nat xn ym); intros Hbeq. reflexivity.
  rewrite IHlv. reflexivity.
Qed.

Lemma free_FO_list_closed_allFO_exFO : forall lv alpha,
  free_FO (list_closed_allFO alpha lv) = free_FO (list_closed_exFO alpha lv).
Proof.
  induction lv; intros alpha. reflexivity.
  simpl. rewrite IHlv. reflexivity.
Qed.

Lemma free_FO_list_closed_allFO_is_in : forall lv alpha x,
  free_FO (list_closed_allFO alpha lv) x = true ->
  is_in_FOvar x lv = false.
Proof.
  induction lv; intros alpha x H. reflexivity.
  simpl in *. destruct x as [xn]. destruct a as [ym].
  case_eq (beq_nat xn ym); intros Hbeq; rewrite Hbeq in *.
    discriminate.
  apply IHlv in H. assumption.
Qed.

Lemma rename_FOv_list_closed_exFO : forall lv alpha x y,
  rename_FOv (list_closed_exFO alpha lv) x y =
  list_closed_exFO (rename_FOv alpha x y) (rename_FOv_list lv x y).
Proof.
  induction lv; intros alpha [xn] [ym]. reflexivity.
  simpl. destruct a as [zn]. rewrite beq_nat_comm.
  unfold rename_FOv in *.
  case_eq (beq_nat xn zn);
    intros Hbeq. simpl. rewrite (IHlv _ (Var xn) (Var ym)).
    reflexivity.

 simpl. rewrite (IHlv _ (Var xn) (Var ym)).
    reflexivity.
Qed.

Lemma  strip_exFO_list_closed_exFO : forall lx n alpha,
  length lx = n ->
  strip_exFO (list_closed_exFO alpha lx) n =
  alpha.
Proof.
  induction lx; intros n alpha H. destruct n. simpl.
    apply strip_exFO_0. discriminate.
  destruct n. discriminate.
  simpl. apply IHlx. simpl in H. inversion H. reflexivity.
Qed.

Lemma strip_exFO_list_list_closed_exFO : forall lv n alpha,
  length lv = n ->
  strip_exFO_list (list_closed_exFO alpha lv) n = lv.
Proof.
  induction lv; intros n alpha H. destruct n. simpl.
    apply strip_exFO_list_0. discriminate.
  destruct n. discriminate.
  simpl. rewrite IHlv. reflexivity.
  simpl in H. inversion H. reflexivity.
Qed.

Lemma is_in_FOvar_max_FOv_conjSO_l : forall beta alpha x,
  is_in_FOvar x (FOvars_in beta) = true ->
  ~ x = Var (S (max_FOv (conjSO beta alpha))).
Proof.
  intros beta alpha x H1 H2.
  simpl in H2. rewrite H2 in H1.
  apply want19 in H1. simpl Nat.max in H1.
  rewrite PeanoNat.Nat.succ_max_distr in H1.
  rewrite max_comm in H1.
  rewrite leb_max_suc in H1. discriminate.
Qed.

Lemma is_in_FOvar_max_FOv_conjSO_r : forall beta alpha x,
  is_in_FOvar x (FOvars_in alpha) = true ->
  ~ x = Var (S (max_FOv (conjSO beta alpha))).
Proof.
  intros beta alpha x H1 H2.
  simpl in H2. rewrite H2 in H1.
  apply want19 in H1. simpl Nat.max in H1.
  rewrite PeanoNat.Nat.succ_max_distr in H1.
  rewrite leb_max_suc in H1. discriminate.
Qed.

Lemma length_rename_FOv_list : forall lv x y,
  length (rename_FOv_list lv x y) = length lv.
Proof.
  induction lv; intros [xn] [ym]. reflexivity.
  simpl. destruct a as [zn].
  case_eq (beq_nat xn zn); intros Hbeq; simpl;
    rewrite IHlv; reflexivity.
Qed.

Lemma lem2'_pre : forall n lv alpha beta x,
  is_in_FOvar x (FOvars_in beta) = true ->
  is_in_FOvar x lv = false ->
  free_FO alpha x = true ->
  free_FO (rename_FOv_A_pre alpha beta lv n) x = true.
Proof.
  induction n; intros lv alpha beta x H1 H2 H3. assumption.
  simpl in *. destruct lv. assumption.
  unfold rename_FOv_max_conj. rewrite rename_FOv_list_closed_exFO.
  rewrite strip_exFO_list_closed_exFO.
  rewrite strip_exFO_list_list_closed_exFO.
  apply is_in_FOvar_cons_f in H2. destruct H2 as [H2a H2b].
  apply IHn. assumption.
    rewrite is_in_FOvar_rename_FOv_list; try assumption.
    apply is_in_FOvar_max_FOv_conjSO_l. assumption.
    apply is_in_FOvar_max_FOv_conjSO_r. simpl.
    destruct f. rewrite <- beq_nat_refl. reflexivity.

    rewrite <- kk16; try assumption.
    apply is_in_FOvar_max_FOv_conjSO_l. assumption.

    apply length_rename_FOv_list.
    apply length_rename_FOv_list.
Qed.


Lemma lem2' : forall lv alpha beta x,
  is_in_FOvar x (FOvars_in beta) = true ->
  is_in_FOvar x lv = false ->
  free_FO alpha x = true ->
  free_FO (rename_FOv_A alpha beta lv) x = true.
Proof.
  intros lv alpha beta x H1 H2 H3.
  unfold rename_FOv_A. apply lem2'_pre; assumption.
Qed. 

Lemma lem2 :  forall lv rel atm phi x,
  free_FO (conjSO rel atm) x = true ->
  free_FO (rename_FOv_A (conjSO rel atm) (ST phi x) lv) x = true.
Proof.
  induction lv; intros rel atm phi x H. assumption.
Admitted.  

Lemma lem1_pre : forall n lv alpha beta x,
  is_in_FOvar x (FOvars_in beta) = true ->
  is_in_FOvar x lv = false ->
  free_FO alpha x = true ->
  is_in_FOvar x (rename_FOv_A_list_pre alpha beta lv n) = false.
Proof.
  induction n; intros lv alpha beta [xn] H1 H2 H3. 
    destruct lv; reflexivity.
  simpl in *. destruct lv. assumption.
  unfold rename_FOv_max_conj. rewrite rename_FOv_list_closed_exFO.
  rewrite strip_exFO_list_closed_exFO.
  rewrite strip_exFO_list_list_closed_exFO.
  apply is_in_FOvar_cons_f in H2. destruct H2 as [H2a H2b].
  remember (rename_FOv_max_conj_var (list_closed_exFO alpha lv) beta f)
    as t.
  simpl in *.
  destruct f as [un].
  assert (Var xn <> Var (S (Nat.max (max_FOv beta) (Nat.max un (max_FOv (list_closed_exFO alpha lv)))))) as Hass.
    pose proof is_in_FOvar_max_FOv_conjSO_l as H4. simpl in H4.
    simpl in H4. apply (H4 _ (exFO (Var un) _) (Var xn)). assumption.
  rewrite (IHn _ _ _ (Var xn)).
  destruct t as [zn]. unfold rename_FOv_max_conj_var in Heqt.
  case_eq (beq_nat xn zn); intros Hbeq.
    rewrite (beq_nat_true _ _ Hbeq) in *.
    contradiction (is_in_FOvar_max_FOv_conjSO_l _ _ _ H1 Heqt).
    reflexivity. assumption.
  rewrite is_in_FOvar_rename_FOv_list; try assumption.
  intros HH. inversion HH as [HH2]. symmetry in HH2.
  apply PeanoNat.Nat.eqb_eq in HH2.
  apply beq__leb in HH2. simpl in HH2. destruct un. discriminate.
  apply leb_max in HH2. destruct HH2 as [HH2 HH3].
  rewrite max_comm in HH3. rewrite leb_max_suc in HH3. discriminate.

  rewrite <- kk16; try assumption.

  apply length_rename_FOv_list.  
  apply length_rename_FOv_list.
Qed.


Lemma lem1 : forall lv alpha beta x,
  is_in_FOvar x (FOvars_in beta) = true ->
  is_in_FOvar x lv = false ->
  free_FO alpha x = true ->
  is_in_FOvar x (rename_FOv_A_list alpha beta lv) = false.
Proof.
  intros lv rel atm phi x H.
  unfold rename_FOv_A_list.
  apply lem1_pre; try assumption.
Qed. 

Lemma free_FO_list_closed_exFO : forall lx alpha x,
   free_FO (list_closed_exFO alpha lx) x =
  if free_FO alpha x then if is_in_FOvar x lx then false else true else false.
Proof.
  induction lx; intros alpha [xn]. simpl. case_eq (free_FO alpha (Var xn)); reflexivity.
  simpl. destruct a as [ym]. case_eq (beq_nat xn ym); intros Hbeq.
    rewrite if_then_else_same. reflexivity.

    apply IHlx.
Qed.

Lemma free_FO_list_closed_allFO : forall lx alpha x,
   free_FO (list_closed_allFO alpha lx) x =
  if free_FO alpha x then if is_in_FOvar x lx then false else true else false.
Proof.
  induction lx; intros alpha [xn]. simpl. case_eq (free_FO alpha (Var xn)); reflexivity.
  simpl. destruct a as [ym]. case_eq (beq_nat xn ym); intros Hbeq.
    rewrite if_then_else_same. reflexivity.

    apply IHlx.
Qed.

Lemma free_FO_list_closed_allFO_rem  : forall lx alpha x,
  free_FO (list_closed_allFO alpha lx) x = true ->
  free_FO alpha x = true.
Proof.
  induction lx; intros alpha [xn] H. simpl in *. assumption.
  simpl in *. destruct a as [ym]. case_eq (beq_nat xn ym); intros Hbeq;
    rewrite Hbeq in *. discriminate. apply IHlx. assumption.
Qed.

Lemma is_in_FOvar_ST : forall phi x,
  is_in_FOvar x (FOvars_in (ST phi x)) = true.
Proof.
  induction phi; intros [xn].
    destruct p. simpl. rewrite <- beq_nat_refl. reflexivity.

    simpl. apply IHphi.
  
    simpl. rewrite is_in_FOvar_app.
    rewrite IHphi1. reflexivity.

    simpl. rewrite is_in_FOvar_app.
    rewrite IHphi1. reflexivity.

    simpl. rewrite is_in_FOvar_app.
    rewrite IHphi1. reflexivity.

    simpl. rewrite <- beq_nat_refl. rewrite if_then_else_same.
    reflexivity.

    simpl. rewrite <- beq_nat_refl. rewrite if_then_else_same.
    reflexivity.
Qed.

Lemma free_FO_rename_FOv_A__list_t : forall lv rel atm x phi2,
  free_FO (list_closed_exFO (conjSO rel atm) lv) x = true ->
  free_FO (list_closed_allFO (implSO (rename_FOv_A (conjSO rel atm) (ST phi2 x) lv) (ST phi2 x))
     (rename_FOv_A_list (conjSO rel atm) (ST phi2 x) lv)) x = true.
Proof.
  intros lv rel atm x phi2 H.
  rewrite free_FO_list_closed_allFO_implSO.
  simpl. rewrite <- free_FO_list_closed_allFO_exFO in H.
  pose proof (free_FO_list_closed_allFO_is_in _ _ _ H) as H2.
  rewrite free_FO_list_closed_allFO.
  pose proof (free_FO_list_closed_allFO_rem _ _ _ H).
  rewrite lem1.
  rewrite lem2'. reflexivity. all: try assumption.
  all:apply is_in_FOvar_ST. 
Qed.

Lemma free_FO_rename_FOv_A__list_f : forall lv rel atm x phi2,
(forall y : FOvariable, x <> y -> free_FO (list_closed_exFO (conjSO rel atm) lv) y = false) ->
forall y : FOvariable,
x <> y ->
free_FO
  (list_closed_allFO (implSO (rename_FOv_A (conjSO rel atm) (ST phi2 x) lv) (ST phi2 x))
     (rename_FOv_A_list (conjSO rel atm) (ST phi2 x) lv)) y = false.
Proof.
(* 
  intros lv rel atm x phi2 H y H2. specialize (H _ H2).
  rewrite free_FO_list_closed_allFO_implSO.
  simpl. rewrite <- free_FO_list_closed_allFO_exFO in H.
  pose proof (free_FO_list_closed_allFO_is_in _ _ _ H) as H2.
  rewrite free_FO_list_closed_allFO.
  pose proof (free_FO_list_closed_allFO_rem _ _ _ H).
  rewrite lem1.
  rewrite lem2'. reflexivity. all: try assumption.
  all:apply is_in_FOvar_ST. 
Qed. *)
Admitted.

Lemma closed_except_rename_FOv_A__list : forall lv rel atm x phi2,
  closed_except (list_closed_exFO (conjSO rel atm) lv) x ->
  closed_except (list_closed_allFO 
    (implSO (rename_FOv_A (conjSO rel atm) (ST phi2 x) lv) (ST phi2 x))
    (rename_FOv_A_list (conjSO rel atm) (ST phi2 x) lv)) x.
Proof.
  intros lv rel atm x phi2 [H1 H2]. unfold closed_except in *.
  apply conj. apply free_FO_rename_FOv_A__list_t. assumption.
 apply free_FO_rename_FOv_A__list_f. assumption.
Qed.

Lemma vsS_preprocessing_Step1_1_againTRY'_withex''_loc : forall phi1 phi2 rel atm x lv,
  vsSahlq_ante phi1 = true ->
  uniform_pos phi2 ->
  REL rel = true ->
  AT atm = true ->
          is_in_pred_l (preds_in (conjSO rel atm)) (preds_in (ST phi1 x)) = true ->
closed_except (list_closed_exFO (conjSO rel atm) lv) x ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
      (Ir : W -> W -> Prop),
    SOturnst W Iv Ip Ir (ST phi1 x) <->
    SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv)) ->
existsT2 lv0 : list FOvariable,
     ((existsT2 atm0 : SecOrder,
         (AT atm0 = true) *
((is_in_FOvar (Var (new_FOv_pp_pre2 atm0)) (FOvars_in atm0) = false) *
  ((existsT rel0 : SecOrder,
     REL rel0 = true /\
          is_in_pred_l (preds_in (conjSO rel0 atm0)) (preds_in (ST phi1 x)) = true /\
          closed_except (list_closed_allFO (implSO (conjSO rel0 atm0) (ST phi2 x)) lv0) x /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (ST (mimpl phi1 phi2) x) <->
          SOturnst W Iv Ip Ir
            (list_closed_allFO (implSO (conjSO rel0 atm0) (ST phi2 x)) lv0))) +
       (is_in_pred_l (preds_in atm0) (preds_in (ST phi1 x)) = true /\
      closed_except (list_closed_allFO (implSO atm0 (ST phi2 x)) lv0) x /\
      forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir (ST (mimpl phi1 phi2) x) <->
      SOturnst W Iv Ip Ir (list_closed_allFO (implSO atm0 (ST phi2 x)) lv0)))))).
Proof.
  intros phi1 phi2 rel atm x lv Hvsa Hun HREL HAT Hc Hin H.
  pose proof (equiv_implSO2 _ _ (ST phi2 x) H) as H1.
  pose proof (equiv3_3_struc2_2' lv (conjSO rel atm) (ST phi2 x)) as H2.
  pose proof (SOturnst_trans _ _ _ H1 H2) as H3.
  pose proof rename_FOv_A_rel_atm.
  destruct (rename_FOv_A_rel_atm lv rel atm (ST phi2 x) HREL HAT)
     as [rel' [atm' [H' [HREL' HAT']]]] .
  rewrite H' in *.
  exists (rename_FOv_A_list (conjSO rel atm) (ST phi2 x) lv).
  exists atm'.
  apply pair. assumption. apply pair.
unfold new_FOv_pp_pre2.

apply (lem_f1'' atm'); try assumption.
  left.
  exists rel'.
  apply conj. assumption.
  apply conj. 
    rewrite <- H'.
    rewrite preds_in_rename_FOv_A.
    assumption.
    apply conj.
rewrite <- H'.
apply closed_except_rename_FOv_A__list. assumption.
    assumption.
Defined.

Lemma vsS_preprocessing_Step1_3_againTRY'_withex'_loc : forall phi1 phi2 atm x lv,
  vsSahlq_ante phi1 = true ->
  uniform_pos phi2 ->
  AT atm = true ->
  is_in_pred_l (preds_in (atm)) (preds_in (ST phi1 x)) = true ->
  closed_except (list_closed_exFO atm lv) x ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
      (Ir : W -> W -> Prop),
    SOturnst W Iv Ip Ir (ST phi1 x) <->
    SOturnst W Iv Ip Ir (list_closed_exFO atm lv)) ->
existsT2 lv0 : list FOvariable,
   (existsT2 atm0 : SecOrder,
       (AT atm0 = true) *
((is_in_FOvar (Var (new_FOv_pp_pre2 atm0)) (FOvars_in atm0) = false) *

    ((existsT rel0 : SecOrder,
       REL rel0 = true /\
      is_in_pred_l (preds_in (conjSO rel0 atm0)) (preds_in (ST phi1 x)) = true /\
      closed_except  (list_closed_allFO (implSO (conjSO rel0 atm0) (ST phi2 x)) lv0) x /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (ST (mimpl phi1 phi2) x) <->
          SOturnst W Iv Ip Ir
            (list_closed_allFO (implSO (conjSO rel0 atm0) (ST phi2 x)) lv0))) +
     (is_in_pred_l (preds_in atm0) (preds_in (ST phi1 x)) = true /\
      closed_except (list_closed_allFO (implSO atm0 (ST phi2 x)) lv0) x /\
     forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir (ST (mimpl phi1 phi2) x) <->
      SOturnst W Iv Ip Ir (list_closed_allFO (implSO atm0 (ST phi2 x)) lv0))))).
Proof.
Admitted.
(*
  intros phi1 phi2 atm x lv Hvsa Hun HAT Hin H.
  pose proof (equiv_implSO2 _ _ (ST phi2 x) H) as H1.
  pose proof (equiv3_3_struc2_2' lv atm (ST phi2 x)) as H2.
  pose proof (SOturnst_trans _ _ _ H1 H2) as H3.
  pose proof (same_struc_rename_FOv_A atm (ST phi2 x) lv) as H4.
  apply same_struc_comm in H4.
  apply same_struc_AT in H4. 2 : assumption.
  exists (rename_FOv_A_list atm (ST phi2 x) lv).
  exists (rename_FOv_A atm (ST phi2 x) lv).
  apply pair. assumption.
  apply pair.
   unfold new_FOv_pp_pre2. 
    apply (lem_f1'' ). assumption.

  right.
  apply conj.
    rewrite preds_in_rename_FOv_A. assumption.
  assumption.
Defined.
*)
Lemma vsS_preprocessing_Step1_pre_againTRY'_withex'_loc : forall phi1 phi2 x,
  vsSahlq_ante phi1 = true ->
  uniform_pos phi2  ->
  existsT2 lv : list FOvariable,
   (existsT2 atm : SecOrder,
       (AT atm = true) *
((is_in_FOvar (Var (new_FOv_pp_pre2 atm)) (FOvars_in atm) = false) *
    ((existsT rel : SecOrder,
     REL rel = true /\
          is_in_pred_l (preds_in (conjSO rel atm)) (preds_in (ST phi1 x)) = true /\
          closed_except (list_closed_allFO (implSO (conjSO rel atm) (ST phi2 x)) lv) x /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (ST (mimpl phi1 phi2) x) <->
          SOturnst W Iv Ip Ir (list_closed_allFO (implSO (conjSO rel atm) (ST phi2 x)) lv))) +

    (is_in_pred_l (preds_in atm) (preds_in (ST phi1 x)) = true /\
    closed_except (list_closed_allFO (implSO atm (ST phi2 x)) lv) x /\
      forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir (ST (mimpl phi1 phi2) x) <->
      SOturnst W Iv Ip Ir (list_closed_allFO (implSO atm (ST phi2 x)) lv))))).
Proof.
  intros phi1 phi2 x Hvsa Hun.
  pose proof (preprocess_vsSahlq_ante_againTRY_loc (ST phi1 x) x (closed_except_ST _ _ ) 
      (vsSahlq_ante_conjSO_exFO_relatSO _ _ Hvsa)  (ex_P_ST phi1 x)) as H1.
  destruct H1 as [lv [atm [HAT [ [rel [HREL [Hin [Hc H]]]] | [Hin [Hc H]] ]]]].
   
    apply vsS_preprocessing_Step1_1_againTRY'_withex''_loc with (phi2 := phi2) in H; try assumption.
    apply vsS_preprocessing_Step1_3_againTRY'_withex'_loc with (phi2 := phi2) in H; try assumption.
Defined.


(* --------------------------------- *)

Lemma hopeful4_REV'_withex'_FULL : forall lP xn phi1 phi2,
  vsSahlq_ante phi1 = true ->
  uniform_pos phi2  ->
  is_in_pred_l (preds_in (ST (mimpl phi1 phi2) (Var xn))) lP = true ->
  existsT2 (lx : list FOvariable) (atm : SecOrder),
    (AT atm = true) *
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
    (vsS_syn_l (FOv_att_P_l (conjSO rel atm) lP) (Var (new_FOv_pp_pre2 atm)))) <->
  SOturnst W Iv Ip Ir (list_closed_SO (ST (mimpl phi1 phi2) (Var xn)) lP)) +

     (is_in_pred_l (preds_in atm) (preds_in (ST phi1 (Var xn))) = true /\
forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (replace_pred_l (list_closed_allFO (implSO atm
    (newnew_pre (instant_cons_empty' atm (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO atm (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn)))))) lx)
    lP (list_Var (length lP) (Var (new_FOv_pp_pre2 atm)))
    (vsS_syn_l (FOv_att_P_l atm lP) (Var (new_FOv_pp_pre2 atm)))) <->
  SOturnst W Iv Ip Ir (list_closed_SO (ST (mimpl phi1 phi2) (Var xn)) lP))).
Proof.
  intros lP xn phi1 phi2 Hvs Hun Hin0.
  destruct (vsS_preprocessing_Step1_pre_againTRY'_withex' _ _ (Var xn) Hvs Hun)
    as [lv [atm [HAT [Hex [ [rel [HREL [Hin SOt]]]  | [Hin SOt]  ]]]]].
    exists lv. exists atm.
    apply pair. assumption.
    left. exists rel. apply conj. assumption.
    apply conj. assumption.
    intros W Iv Ip Ir.  
split; intros H.
    apply hopeful3_REV with (alpha := (ST (mimpl phi1 phi2) (Var xn))) in H ;
      try assumption.
        apply lem_f3; assumption.
      apply uni_pos__SO. assumption.
      apply SOQFree_ST.

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

        apply hopeful3 with (alpha := (ST (mimpl phi1 phi2) (Var xn)));
      try assumption.
      apply uni_pos__SO. assumption.
      apply SOQFree_ST.

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
    apply pair. assumption.
    right.
    apply conj. assumption.
    intros W Iv Ip Ir.
split; intros H.
    apply hopeful3_REV_atm with (alpha := (ST (mimpl phi1 phi2) (Var xn))) in H;
      try assumption.
      apply lem_f3; assumption.

      apply uni_pos__SO. assumption.
      apply SOQFree_ST.

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

    apply hopeful3_atm with (alpha := (ST (mimpl phi1 phi2) (Var xn)));
      try assumption.
      apply uni_pos__SO. assumption.
      apply SOQFree_ST.

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
 
Lemma closed_except_list_closed_allFO : forall lv alpha beta x,
  (closed_except alpha x -> closed_except beta x) ->
  closed_except (list_closed_allFO alpha lv) x ->
  closed_except (list_closed_allFO beta lv) x.
Proof.
  intros lv alpha beta x H1 [H2 H3].
  unfold closed_except in *. apply conj.
  
Admitted.


Lemma closed_except_eg1_pre : forall rel atm phi2 xn lP,
closed_except (implSO (conjSO rel atm) (ST phi2 (Var xn))) (Var xn) ->
 closed_except
   (implSO
      (replace_pred_l (conjSO rel atm) lP (list_Var (length lP) (Var (new_FOv_pp_pre2 atm)))
         (vsS_syn_l (FOv_att_P_l (conjSO rel atm) lP) (Var (new_FOv_pp_pre2 atm))))
      (replace_pred_l
         (newnew_pre (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))
            (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))) (Var xn))
            (rev_seq (S (Nat.max (max_FOv (implSO (conjSO rel atm) (ST phi2 (Var xn)))) xn))
               (length (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))) (Var xn))))) lP
         (list_Var (length lP) (Var (new_FOv_pp_pre2 atm)))
         (vsS_syn_l (FOv_att_P_l (conjSO rel atm) lP) (Var (new_FOv_pp_pre2 atm))))) (Var xn).
Admitted.

Lemma free_FO_rep_pred_vsS_syn_l : forall llv lP lx y x alpha,
  free_FO alpha x = true ->
  free_FO (replace_pred_l alpha lP lx (vsS_syn_l llv y)) x = true.
Admitted.

Lemma free_FO_newnew_pre : forall lx alpha m n  xn,
  is_in_FOvar (Var xn) lx = false ->
  Nat.leb xn (S m) = true ->
  free_FO alpha (Var xn) = true ->
  free_FO (newnew_pre alpha lx (rev_seq m n)) (Var xn) = true.
Admitted.

Lemma free_FO_instant_cons_empty'_t : forall beta alpha y,
  SOQFree beta = true  ->
  free_FO beta y = true ->
  free_FO (instant_cons_empty' alpha beta) y = true.
Proof.
  induction beta; intros alpha [xn] Hno H.
    destruct p as [Pn]; destruct f as [ym].
    simpl in *.
    unfold instant_cons_empty'.
    simpl. case_eq (is_in_pred (Pred Pn) (preds_in alpha));
      intros H2.
      simpl. assumption.
      simpl. rewrite <- beq_nat_refl.
      simpl. rewrite H. reflexivity.

    destruct f as [ym]; destruct f0 as [zn]. simpl in *.
    assumption.

    destruct f as [ym]; destruct f0 as [zn]. simpl in *.
    assumption.

    destruct f as [ym]. simpl in *.
    rewrite instant_cons_empty'_allFO.
    simpl.
    case_eq (beq_nat xn ym); intros Hbeq;
      rewrite Hbeq in *. discriminate.
      apply IHbeta; assumption.

    destruct f as [ym]. simpl in *.
    rewrite instant_cons_empty'_exFO.
    simpl.
    case_eq (beq_nat xn ym); intros Hbeq;
      rewrite Hbeq in *. discriminate.
      apply IHbeta; assumption.

    rewrite instant_cons_empty'_negSO.
    simpl in *. apply IHbeta; assumption.

    rewrite instant_cons_empty'_conjSO.
    simpl in *. case_eq (SOQFree beta1);
      intros H2; rewrite H2 in *. 2 : discriminate.
    case_eq (free_FO beta1 (Var xn)); intros H3;
      rewrite H3 in H.
    rewrite IHbeta1. reflexivity. reflexivity.
    all : try assumption.

    rewrite IHbeta2. rewrite if_then_else_same. reflexivity.
    all : try assumption. 

    rewrite instant_cons_empty'_disjSO.
    simpl in *. case_eq (SOQFree beta1);
      intros H2; rewrite H2 in *. 2 : discriminate.
    case_eq (free_FO beta1 (Var xn)); intros H3;
      rewrite H3 in H.
    rewrite IHbeta1. reflexivity. reflexivity.
    all : try assumption.

    rewrite IHbeta2. rewrite if_then_else_same. reflexivity.
    all : try assumption. 

    rewrite instant_cons_empty'_implSO.
    simpl in *. case_eq (SOQFree beta1);
      intros H2; rewrite H2 in *. 2 : discriminate.
    case_eq (free_FO beta1 (Var xn)); intros H3;
      rewrite H3 in H.
    rewrite IHbeta1. reflexivity. reflexivity.
    all : try assumption.

    rewrite IHbeta2. rewrite if_then_else_same. reflexivity.
    all : try assumption. 

    simpl in *. destruct p. discriminate.

    simpl in *. destruct p. discriminate.
Qed.



Lemma leb_eg1 : forall n xn,
Nat.leb xn (S (S (Nat.max n xn))) = true.
Proof.
  intros n xn.
  rewrite PeanoNat.Nat.succ_max_distr.
  rewrite PeanoNat.Nat.succ_max_distr.  
  rewrite max_comm.  apply leb_max_suc3.
  do 2 apply leb_suc_r. apply leb_refl.
Qed.

Lemma closed_except_eg1_free_t : forall rel atm phi2 xn lv lP,
REL rel = true ->
free_FO (list_closed_allFO (implSO (conjSO rel atm) (ST phi2 (Var xn))) lv) (Var xn) = true ->
free_FO (list_closed_allFO  (implSO
  (replace_pred_l (conjSO rel atm) lP (list_Var (length lP) (Var (new_FOv_pp_pre2 atm)))
    (vsS_syn_l (FOv_att_P_l (conjSO rel atm) lP) (Var (new_FOv_pp_pre2 atm))))
  (replace_pred_l
    (newnew_pre (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))
      (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (Nat.max (max_FOv (implSO (conjSO rel atm) (ST phi2 (Var xn)))) xn))
        (length (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn))))
          (Var xn))))) lP (list_Var (length lP) (Var (new_FOv_pp_pre2 atm)))
          (vsS_syn_l (FOv_att_P_l (conjSO rel atm) lP) (Var (new_FOv_pp_pre2 atm))))) lv) 
  (Var xn) = true.
Proof.
  intros rel atm phi2 xn lv lP Hrel H.
  rewrite free_FO_list_closed_allFO_implSO in *.
  apply orb_true_iff in H. 
  apply orb_true_iff. fold free_FO in *.
  destruct H; [left|right].
    rewrite free_FO_list_closed_allFO in *.
    apply andb_true_iff in H. destruct H as [H1 H2].
    apply andb_true_iff. apply conj.
      rewrite rep_pred_l_conjSO.
      apply orb_true_iff in H1.
      apply orb_true_iff. fold free_FO in *.
      destruct H1; [left|right].
        rewrite rep_pred_l_REL; assumption.
        apply free_FO_rep_pred_vsS_syn_l; assumption.
        assumption.

    rewrite free_FO_list_closed_allFO in *.
    apply andb_true_iff in H. destruct H as [H1 H2].
    apply andb_true_iff. apply conj.
      apply free_FO_rep_pred_vsS_syn_l.
      apply free_FO_newnew_pre.
        apply is_in_FOvar_rem_FOv_same.
        apply leb_eg1.

        apply free_FO_instant_cons_empty'_t.
        apply SOQFree_ST. assumption.
        assumption.
Qed.

Lemma closed_except_eg1_free_f : forall rel atm phi2 xn lv lP,
(forall y : FOvariable,
Var xn <> y ->free_FO (list_closed_allFO (implSO (conjSO rel atm) (ST phi2 (Var xn))) lv) y = false) ->
forall y : FOvariable,
Var xn <> y -> 
free_FO (list_closed_allFO  (implSO
  (replace_pred_l (conjSO rel atm) lP (list_Var (length lP) (Var (new_FOv_pp_pre2 atm)))
    (vsS_syn_l (FOv_att_P_l (conjSO rel atm) lP) (Var (new_FOv_pp_pre2 atm))))
  (replace_pred_l
    (newnew_pre (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))
      (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (Nat.max (max_FOv (implSO (conjSO rel atm) (ST phi2 (Var xn)))) xn))
        (length (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn))))
          (Var xn))))) lP (list_Var (length lP) (Var (new_FOv_pp_pre2 atm)))
          (vsS_syn_l (FOv_att_P_l (conjSO rel atm) lP) (Var (new_FOv_pp_pre2 atm))))) lv) 
  y = false.
Admitted.

(* Up to here *)
Lemma closed_except_eg1 : forall rel atm phi2 xn lv lP,
   closed_except (list_closed_allFO (implSO (conjSO rel atm) (ST phi2 (Var xn))) lv) (Var xn) ->
closed_except (replace_pred_l   (list_closed_allFO (implSO (conjSO rel atm)
  (newnew_pre (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))
  (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))) (Var xn))
     (rev_seq (S (Nat.max (max_FOv (implSO (conjSO rel atm) (ST phi2 (Var xn)))) xn))
       (length (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))) (Var xn))))))
        lv) lP (list_Var (length lP) (Var (new_FOv_pp_pre2 atm)))
     (vsS_syn_l (FOv_att_P_l (conjSO rel atm) lP) (Var (new_FOv_pp_pre2 atm)))) (Var xn).
Proof.
Admitted.
(*   intros rel atm phi2 xn lv lP [H1 H2].
  rewrite rep_pred_l_list_closed_allFO.
  rewrite rep_pred_l_implSO. unfold closed_except in *.
  apply conj. apply closed_except_eg1_free_t. assumption.
  apply closed_except_eg1_free_f. assumption.
Qed. *)
(* 
  apply (closed_except_list_closed_allFO _ _ _ _ (closed_except_eg1_pre _ _ _ _ _) H).
Qed.
 *)
Lemma hopeful4_REV'_withex'_FULL_loc : forall lP xn phi1 phi2,
  vsSahlq_ante phi1 = true ->
  uniform_pos phi2  ->
  is_in_pred_l (preds_in (ST (mimpl phi1 phi2) (Var xn))) lP = true ->
  existsT2 (lx : list FOvariable) (atm : SecOrder),
    (AT atm = true) *
    ((existsT rel,
      REL rel = true /\
      is_in_pred_l (preds_in (conjSO rel atm)) (preds_in (ST phi1 (Var xn))) = true /\
closed_except (replace_pred_l (list_closed_allFO (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))) (Var xn)))))) lx)
    lP (list_Var (length lP) (Var (new_FOv_pp_pre2 atm)))
    (vsS_syn_l (FOv_att_P_l (conjSO rel atm) lP) (Var (new_FOv_pp_pre2 atm)))) (Var xn) /\
forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (replace_pred_l (list_closed_allFO (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))) (Var xn)))))) lx)
    lP (list_Var (length lP) (Var (new_FOv_pp_pre2 atm)))
    (vsS_syn_l (FOv_att_P_l (conjSO rel atm) lP) (Var (new_FOv_pp_pre2 atm)))) <->
  SOturnst W Iv Ip Ir (list_closed_SO (ST (mimpl phi1 phi2) (Var xn)) lP)) +

     (is_in_pred_l (preds_in atm) (preds_in (ST phi1 (Var xn))) = true /\
closed_except (replace_pred_l (list_closed_allFO (implSO atm
    (newnew_pre (instant_cons_empty' atm (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO atm (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn)))))) lx)
    lP (list_Var (length lP) (Var (new_FOv_pp_pre2 atm)))
    (vsS_syn_l (FOv_att_P_l atm lP) (Var (new_FOv_pp_pre2 atm)))) (Var xn) /\
forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (replace_pred_l (list_closed_allFO (implSO atm
    (newnew_pre (instant_cons_empty' atm (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO atm (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn)))))) lx)
    lP (list_Var (length lP) (Var (new_FOv_pp_pre2 atm)))
    (vsS_syn_l (FOv_att_P_l atm lP) (Var (new_FOv_pp_pre2 atm)))) <->
  SOturnst W Iv Ip Ir (list_closed_SO (ST (mimpl phi1 phi2) (Var xn)) lP))).
Proof.
  intros lP xn phi1 phi2 Hvs Hun Hin0.
  destruct (vsS_preprocessing_Step1_pre_againTRY'_withex'_loc _ _ (Var xn) Hvs Hun)
    as [lv [atm [HAT [Hex [ [rel [HREL [Hin [Hc SOt]]]]  | [Hin [Hc SOt]]  ]]]]].
    exists lv. exists atm.
    apply pair. assumption.
    left. exists rel. apply conj. assumption.
    apply conj. assumption.
    apply conj.

admit.
    intros W Iv Ip Ir.  
split; intros H.
    apply hopeful3_REV with (alpha := (ST (mimpl phi1 phi2) (Var xn))) in H ;
      try assumption.
        apply lem_f3; assumption.
      apply uni_pos__SO. assumption.
      apply SOQFree_ST.

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

        apply hopeful3 with (alpha := (ST (mimpl phi1 phi2) (Var xn)));
      try assumption.
      apply uni_pos__SO. assumption.
      apply SOQFree_ST.

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
    apply pair. assumption.
    right.
    apply conj. assumption.
    apply conj. admit.
    intros W Iv Ip Ir.
split; intros H.
    apply hopeful3_REV_atm with (alpha := (ST (mimpl phi1 phi2) (Var xn))) in H;
      try assumption.
      apply lem_f3; assumption.

      apply uni_pos__SO. assumption.
      apply SOQFree_ST.

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

    apply hopeful3_atm with (alpha := (ST (mimpl phi1 phi2) (Var xn)));
      try assumption.
      apply uni_pos__SO. assumption.
      apply SOQFree_ST.

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
Admitted.
(* Defined. *)

Lemma hopeful4_REV'_withex'_FULL_allFO : forall lP xn phi1 phi2,
  vsSahlq_ante phi1 = true ->
  uniform_pos phi2  ->
  is_in_pred_l (preds_in (ST (mimpl phi1 phi2) (Var xn))) lP = true ->
  existsT2 lx atm,
    (AT atm = true) *
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
    (vsS_syn_l (FOv_att_P_l (conjSO rel atm) lP) (Var (new_FOv_pp_pre2 atm))))) <->
  SOturnst W Iv Ip Ir (allFO (Var xn) (list_closed_SO (ST (mimpl phi1 phi2) (Var xn)) lP))) +

     (is_in_pred_l (preds_in atm) (preds_in (ST phi1 (Var xn))) = true /\
forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (allFO (Var xn) (replace_pred_l (list_closed_allFO (implSO atm
    (newnew_pre (instant_cons_empty' atm (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO atm (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn)))))) lx)
    lP (list_Var (length lP) (Var (new_FOv_pp_pre2 atm)))
    (vsS_syn_l (FOv_att_P_l atm lP) (Var (new_FOv_pp_pre2 atm))))) <->
  SOturnst W Iv Ip Ir (allFO (Var xn) (list_closed_SO (ST (mimpl phi1 phi2) (Var xn)) lP)))).
Proof.
  intros lP xn phi1 phi2 H1 H2 H3.
  destruct (hopeful4_REV'_withex'_FULL lP xn phi1 phi2 H1 H2 H3) as [lx [atm [Hat [ [rel [Hrel [Hin SOt]]]| [Hin SOt] ]]]];
  exists lx; exists atm; apply pair; try assumption; [left | right].
    exists rel. apply conj. assumption. apply conj. assumption.
    intros.
    apply equiv_allFO with (W := W) (Iv := Iv) (Ip := Ip) (Ir := Ir) (x := (Var xn)) in SOt.
    assumption.


    apply conj. assumption. intros.
    apply equiv_allFO with (W := W) (Iv := Iv) (Ip := Ip) (Ir := Ir) (x := (Var xn)) in SOt.
    assumption.
Defined.

Lemma hopeful4_REV'_withex'_FULL_allFO_in : forall lP xn phi1 phi2,
  vsSahlq_ante phi1 = true ->
  uniform_pos phi2  ->
  is_in_pred_l (preds_in (ST (mimpl phi1 phi2) (Var xn))) lP = true ->
  existsT2 lx atm,
    (AT atm = true) *
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
    (vsS_syn_l (FOv_att_P_l (conjSO rel atm) lP) (Var (new_FOv_pp_pre2 atm))))) <->
  SOturnst W Iv Ip Ir (list_closed_SO (allFO (Var xn) (ST (mimpl phi1 phi2) (Var xn))) lP)) +

     (is_in_pred_l (preds_in atm) (preds_in (ST phi1 (Var xn))) = true /\
forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (allFO (Var xn) (replace_pred_l (list_closed_allFO (implSO atm
    (newnew_pre (instant_cons_empty' atm (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO atm (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn)))))) lx)
    lP (list_Var (length lP) (Var (new_FOv_pp_pre2 atm)))
    (vsS_syn_l (FOv_att_P_l atm lP) (Var (new_FOv_pp_pre2 atm))))) <->
  SOturnst W Iv Ip Ir (list_closed_SO (allFO (Var xn) (ST (mimpl phi1 phi2) (Var xn))) lP))).
Proof.
  intros lP xn phi1 phi2 H1 H2 H3.
  destruct (hopeful4_REV'_withex'_FULL_allFO lP xn phi1 phi2 H1 H2 H3) as [lx [atm [Hat [ [rel [Hrel [Hin SOt]]]| [Hin SOt] ]]]];
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

Lemma hopeful4_REV'_withex'_FULL_allFO_in_loc : forall lP xn phi1 phi2,
  vsSahlq_ante phi1 = true ->
  uniform_pos phi2  ->
  is_in_pred_l (preds_in (ST (mimpl phi1 phi2) (Var xn))) lP = true ->
  existsT2 lx atm,
    (AT atm = true) *
    ((existsT rel,
      REL rel = true /\
      is_in_pred_l (preds_in (conjSO rel atm)) (preds_in (ST phi1 (Var xn))) = true /\
      closed_except ((replace_pred_l (list_closed_allFO (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))) (Var xn)))))) lx)
    lP (list_Var (length lP) (Var (new_FOv_pp_pre2 atm)))
    (vsS_syn_l (FOv_att_P_l (conjSO rel atm) lP) (Var (new_FOv_pp_pre2 atm))))) (Var xn) /\
forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir ((replace_pred_l (list_closed_allFO (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))) (Var xn)))))) lx)
    lP (list_Var (length lP) (Var (new_FOv_pp_pre2 atm)))
    (vsS_syn_l (FOv_att_P_l (conjSO rel atm) lP) (Var (new_FOv_pp_pre2 atm))))) <->
  SOturnst W Iv Ip Ir (list_closed_SO ((ST (mimpl phi1 phi2) (Var xn))) lP)) +

     (is_in_pred_l (preds_in atm) (preds_in (ST phi1 (Var xn))) = true /\
closed_except ( (replace_pred_l (list_closed_allFO (implSO atm
    (newnew_pre (instant_cons_empty' atm (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO atm (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn)))))) lx)
    lP (list_Var (length lP) (Var (new_FOv_pp_pre2 atm)))
    (vsS_syn_l (FOv_att_P_l atm lP) (Var (new_FOv_pp_pre2 atm))))) (Var xn) /\
forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir ( (replace_pred_l (list_closed_allFO (implSO atm
    (newnew_pre (instant_cons_empty' atm (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO atm (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn)))))) lx)
    lP (list_Var (length lP) (Var (new_FOv_pp_pre2 atm)))
    (vsS_syn_l (FOv_att_P_l atm lP) (Var (new_FOv_pp_pre2 atm))))) <->
  SOturnst W Iv Ip Ir (list_closed_SO ((ST (mimpl phi1 phi2) (Var xn))) lP))).
Proof.
  intros lP xn phi1 phi2 H1 H2 H3.
  destruct (hopeful4_REV'_withex'_FULL_loc lP xn phi1 phi2 H1 H2 H3) as [lx [atm [Hat [ [rel [Hrel [Hin [Hc SOt]]]]| [Hin [Hc SOt]] ]]]];
  exists lx; exists atm; apply pair; try assumption; [left | right].
    exists rel. apply conj. assumption. apply conj. assumption.
    apply conj. assumption.
    intros. split; intros HH;
      apply SOt; assumption.

    apply conj. assumption. apply conj. assumption. intros.
    split; intros HH;
      apply SOt; assumption.
Defined.

Lemma vsSahlq_full_SO_pre : forall xn phi1 phi2,
  vsSahlq_ante phi1 = true ->
  uniform_pos phi2  ->

  existsT2 lx atm,
    (AT atm = true) *
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
    (preds_in (ST (mimpl phi1 phi2) (Var xn))) (list_Var (length (preds_in (ST (mimpl phi1 phi2) (Var xn)))) (Var (new_FOv_pp_pre2 atm)))
    (vsS_syn_l (FOv_att_P_l (conjSO rel atm) (preds_in (ST (mimpl phi1 phi2) (Var xn)))) (Var (new_FOv_pp_pre2 atm))))) <->
  SOturnst W Iv Ip Ir (uni_closed_SO (allFO (Var xn) (ST (mimpl phi1 phi2) (Var xn))))) +

     (is_in_pred_l (preds_in atm) (preds_in (ST phi1 (Var xn))) = true /\
forall W Iv Ip Ir,

  SOturnst W Iv Ip Ir (allFO (Var xn) (replace_pred_l (list_closed_allFO (implSO atm
    (newnew_pre (instant_cons_empty' atm (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO atm (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn)))))) lx)
    (preds_in (ST (mimpl phi1 phi2) (Var xn))) (list_Var (length (preds_in (ST (mimpl phi1 phi2) (Var xn)))) (Var (new_FOv_pp_pre2 atm)))
    (vsS_syn_l (FOv_att_P_l atm (preds_in (ST (mimpl phi1 phi2) (Var xn)))) (Var (new_FOv_pp_pre2 atm))))) <->
  SOturnst W Iv Ip Ir (uni_closed_SO (allFO (Var xn) (ST (mimpl phi1 phi2) (Var xn)))))).
Proof.
  intros xn phi1 phi2 H1 H2. unfold uni_closed_SO in *. unfold uni_closed_SO.
  apply hopeful4_REV'_withex'_FULL_allFO_in; try assumption.
  simpl. apply is_in_pred_l_refl.
Defined.

(* Lemma predSO_ST_eq_FO : forall alpha p f,
 (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
      (Ir : W -> W -> Prop),
    SOturnst W Iv Ip Ir (predSO p f) <-> SOturnst W Iv Ip Ir alpha) ->
    alpha = predSO p f.
Proof.
  induction alpha; intros [Pn] [ym] H1.
    simpl in *. destruct f as [zn]. destruct p as [Qm].
    case_eq (beq_nat ym zn); intros Hbeq2.  rewrite (beq_nat_true _ _ Hbeq2) in *.
      case_eq (beq_nat Pn Qm); intros Hbeq.
        rewrite (beq_nat_true _ _ Hbeq) in *. reflexivity.
        specialize (H1 nat (fun n => 0) (fun P => match P with Pred Sn =>
          if beq_nat Sn Qm then (fun n => True) else fun n => False end)
        (fun n => fun m => True)).
        simpl in *. rewrite <- beq_nat_refl in *. rewrite Hbeq in *. 
        destruct H1 as [Ha Hb]. contradiction Hb. exact I.

 
      case_eq (beq_nat Pn Qm); intros Hbeq.
        rewrite (beq_nat_true _ _ Hbeq) in *. 
        specialize (H1 nat (fun n => match n with Var un =>
          if beq_nat un zn then 0 else 1 end) (fun P => fun n => match n with 0 =>
          True | _ => False end) (fun n => fun m => True)).
        simpl in *. rewrite <- beq_nat_refl in *. rewrite Hbeq2 in *.
         destruct H1 as [Ha Hb]. contradiction Hb. exact I.

        specialize (H1 nat (fun n => match n with Var un =>
          if beq_nat un zn then 0 else 1 end) (fun P => fun n => match n with 0 =>
          True | _ => False end) (fun n => fun m => True)).
        simpl in *. rewrite <- beq_nat_refl in *. rewrite Hbeq2 in *.
         destruct H1 as [Ha Hb]. contradiction Hb. exact I.

      specialize (H1 nat (fun n => 0) (fun P => (fun w => True)) 
        (fun n => fun m => False)). simpl in *. 
         destruct H1 as [Ha Hb]. contradiction Ha. exact I.

      specialize (H1 nat (fun n => 0) (fun P => (fun w => False)) 
        (fun n => fun m => False)). simpl in *. 
         destruct H1 as [Ha Hb]. contradiction Hb. reflexivity.

      

        specialize (H1 nat (fun n => match n with Var un =>
          if beq_nat un zn then 0 else 1 end) (fun P => fun n => match n with 0 =>
          True | _ => False end) (fun n => fun m => True)).
        simpl in *. rewrite <- beq_nat_refl in *. rewrite Hbeq2 in *.
         destruct H1 as [Ha Hb]. contradiction Hb. exact I.

        simpl in *.

 match P with Pred Sn =>
          if beq_nat Sn Qm then (fun n => True) else fun n => False end)
        (fun n => fun m => True)).
        simpl in *. rewrite <- beq_nat_refl in *. rewrite Hbeq in *. 
        destruct H1 as [Ha Hb]. contradiction Hb. exact I.

      2 : discriminate.
    rewrite <- (beq_nat_true _ _ Hbeq2) in *.
    destruct p as [Qm].
    case_eq (beq_nat Pn Qm); intros Hbeq. rewrite (beq_nat_true _ _ Hbeq) in *.
      specialize (H1 nat (fun z => match z with Var un => 
        if beq_nat xn un then 0 else if beq_nat ym un then 1 else 2 end)
        (fun S => fun n => match n with 0 => Var xn = Var ym | S m => True end)).
      simpl in *. do 2  rewrite <- beq_nat_refl in *.
      case_eq (beq_nat xn ym); intros Hbeq3. rewrite (beq_nat_true _ _ Hbeq3). reflexivity.
      rewrite Hbeq3 in H1. apply H1.  
      apply (fun n => (fun m => True)). exact I.



  is_in_FOvar x (FOvars_in alpha) = true ->
  x = f.
Proof.
  induction alpha; intros [Pn] [ym] [xn] H1 H2.
    simpl in *. destruct f as [zn].
    case_eq (beq_nat xn zn); intros Hbeq2; rewrite Hbeq2 in *.
      2 : discriminate.
    rewrite <- (beq_nat_true _ _ Hbeq2) in *.
    destruct p as [Qm].
    case_eq (beq_nat Pn Qm); intros Hbeq. rewrite (beq_nat_true _ _ Hbeq) in *.
      specialize (H1 nat (fun z => match z with Var un => 
        if beq_nat xn un then 0 else if beq_nat ym un then 1 else 2 end)
        (fun S => fun n => match n with 0 => Var xn = Var ym | S m => True end)).
      simpl in *. do 2  rewrite <- beq_nat_refl in *.
      case_eq (beq_nat xn ym); intros Hbeq3. rewrite (beq_nat_true _ _ Hbeq3). reflexivity.
      rewrite Hbeq3 in H1. apply H1.  
      apply (fun n => (fun m => True)). exact I.


      specialize (H1 nat (fun z => match z with Var un => 
        if beq_nat xn un then 0 else if beq_nat ym un then 1 else 2 end) 
        (fun S => match S with Pred Sn => if beq_nat Pn Sn then (fun n => True) else fun n => Var xn = Var ym end)).
      simpl in *. do 2 rewrite <- beq_nat_refl in *. rewrite Hbeq in H1.
      apply H1. apply (fun n => (fun m => True)). exact I.

      simpl in *. destruct f as [z1]; destruct f0 as [z2].
      specialize (H1 nat (fun u => 0) (fun P => (fun w => False))
        (fun x1 => fun x2 => True)). simpl in *.
      destruct H1 as [Ha Hb]. contradiction Hb. exact I.

      simpl in *. destruct f as [z1]; destruct f0 as [z2].
      specialize (H1 nat (fun u => 0) (fun P => (fun w => False))
        (fun x1 => fun x2 => True)). simpl in *.
      destruct H1 as [Ha Hb]. contradiction Hb. reflexivity.

      destruct f as [zn]. simpl in H2. case_eq (beq_nat xn zn);
        intros Hbeq; rewrite Hbeq in *. rewrite <- (beq_nat_true _ _ Hbeq) in *.
        case_eq (
         specialize (H1 nat).


      

      case_eq (beq_nat xn z1); intros Hbeq1; rewrite Hbeq1 in *.

  induction phi; intros [Pn] [ym] [xn] H.
    simpl in *. destruct p as [Qm]. simpl in *.
    case_eq (beq_nat Pn Qm); intros Hbeq. rewrite (beq_nat_true _ _ Hbeq) in *.
      specialize (H nat (fun z => match z with Var zn => 
        if beq_nat xn zn then 0 else if beq_nat ym zn then 1 else 2 end)
        (fun S => fun n => match n with 0 => Var xn = Var ym | S m => True end)).
      simpl in *. do 2  rewrite <- beq_nat_refl in *.
      case_eq (beq_nat xn ym); intros Hbeq2. rewrite (beq_nat_true _ _ Hbeq2). reflexivity.
      rewrite Hbeq2 in H. apply H.  
      apply (fun n => (fun m => True)). exact I.

    specialize (H nat (fun z => match z with Var zn => 
      if beq_nat xn zn then 0 else if beq_nat ym zn then 1 else 2 end) 
      (fun S => match S with Pred Sn => if beq_nat Pn Sn then (fun n => True) else fun n => Var xn = Var ym end)).
    simpl in *. do 2 rewrite <- beq_nat_refl in *. rewrite Hbeq in H.
    apply H. apply (fun n => (fun m => True)). exact I.

    simpl in *. specialize (IHphi (Pred Pn) (Var ym) (Var xn)).
    apply IHphi. intros W Iv Ip Ir. split; intros H2.
      specialize (H W Iv 
        (fun P => fun w => w = (Iv (Var ym)) -> ~ Ip (Pred Pn) (Iv (Var ym)))).
      simpl in H. 
        
        apply H. apply IHphi.
    

Search "functional_extensionality".

Lemma closed_except_equiv  : forall alpha phi x,
  (forall W Iv Ip Ir, SOturnst W Iv Ip Ir alpha <->
  SOturnst W Iv Ip Ir (ST phi x)) ->
  closed_except alpha x.
Proof.
  induction alpha; intros phi x H.


    simpl in *.

Lemma
 *)


Lemma vsSahlq_full_SO_pre_loc : forall xn phi1 phi2,
  vsSahlq_ante phi1 = true ->
  uniform_pos phi2  ->
  existsT2 lx atm,
    (AT atm = true) *
    ((existsT rel,
      REL rel = true /\
      is_in_pred_l (preds_in (conjSO rel atm)) (preds_in (ST phi1 (Var xn))) = true /\
      (closed_except ((replace_pred_l (list_closed_allFO (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))) (Var xn)))))) lx)
    (preds_in (ST (mimpl phi1 phi2) (Var xn))) (list_Var (length (preds_in (ST (mimpl phi1 phi2) (Var xn)))) (Var (new_FOv_pp_pre2 atm)))
    (vsS_syn_l (FOv_att_P_l (conjSO rel atm) (preds_in (ST (mimpl phi1 phi2) (Var xn)))) (Var (new_FOv_pp_pre2 atm))))) (Var xn)) /\
forall W Iv Ip Ir,

  SOturnst W Iv Ip Ir ((replace_pred_l (list_closed_allFO (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))) (Var xn)))))) lx)
    (preds_in (ST (mimpl phi1 phi2) (Var xn))) (list_Var (length (preds_in (ST (mimpl phi1 phi2) (Var xn)))) (Var (new_FOv_pp_pre2 atm)))
    (vsS_syn_l (FOv_att_P_l (conjSO rel atm) (preds_in (ST (mimpl phi1 phi2) (Var xn)))) (Var (new_FOv_pp_pre2 atm))))) <->
  SOturnst W Iv Ip Ir (uni_closed_SO ((ST (mimpl phi1 phi2) (Var xn))))) +

     (is_in_pred_l (preds_in atm) (preds_in (ST phi1 (Var xn))) = true /\
closed_except ((replace_pred_l (list_closed_allFO (implSO atm
    (newnew_pre (instant_cons_empty' atm (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO atm (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn)))))) lx)
    (preds_in (ST (mimpl phi1 phi2) (Var xn))) (list_Var (length (preds_in (ST (mimpl phi1 phi2) (Var xn)))) (Var (new_FOv_pp_pre2 atm)))
    (vsS_syn_l (FOv_att_P_l atm (preds_in (ST (mimpl phi1 phi2) (Var xn)))) (Var (new_FOv_pp_pre2 atm))))) (Var xn) /\
forall W Iv Ip Ir,

  SOturnst W Iv Ip Ir ((replace_pred_l (list_closed_allFO (implSO atm
    (newnew_pre (instant_cons_empty' atm (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO atm (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn)))))) lx)
    (preds_in (ST (mimpl phi1 phi2) (Var xn))) (list_Var (length (preds_in (ST (mimpl phi1 phi2) (Var xn)))) (Var (new_FOv_pp_pre2 atm)))
    (vsS_syn_l (FOv_att_P_l atm (preds_in (ST (mimpl phi1 phi2) (Var xn)))) (Var (new_FOv_pp_pre2 atm))))) <->
  SOturnst W Iv Ip Ir (uni_closed_SO ( (ST (mimpl phi1 phi2) (Var xn)))))).
Proof.
  intros xn phi1 phi2 H1 H2. unfold uni_closed_SO in *. unfold uni_closed_SO.
  apply hopeful4_REV'_withex'_FULL_allFO_in_loc; try assumption.
  simpl. apply is_in_pred_l_refl.
Defined.


Lemma vsSahlq_full_SO : forall xn phi1 phi2,
  vsSahlq_ante phi1 = true ->
  uniform_pos phi2  ->
  existsT (alpha : SecOrder),
is_unary_predless alpha = true /\
forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir alpha <->
  SOturnst W Iv Ip Ir (uni_closed_SO (allFO (Var xn) (ST (mimpl phi1 phi2) (Var xn)))).
Proof.
  intros xn phi1 phi2 H1 H2.
  destruct (vsSahlq_full_SO_pre xn phi1 phi2 H1 H2) as  [lx [atm [Hat [[rel [Hrel [Hin SOt]]]| [Hin SOt] ]]]].
    exists (allFO (Var xn) (replace_pred_l
           (list_closed_allFO
              (implSO (conjSO rel atm)
                 (newnew_pre (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))
                    (rem_FOv
                       (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn))))
                       (Var xn))
                    (rev_seq
                       (S (Nat.max (max_FOv (implSO (conjSO rel atm) (ST phi2 (Var xn)))) xn))
                       (length
                          (rem_FOv
                             (FOvars_in
                                (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn))))
                             (Var xn)))))) lx) (preds_in (ST (mimpl phi1 phi2) (Var xn)))
           (list_Var (length (preds_in (ST (mimpl phi1 phi2) (Var xn))))
              (Var (new_FOv_pp_pre2 atm)))
           (vsS_syn_l (FOv_att_P_l (conjSO rel atm) (preds_in (ST (mimpl phi1 phi2) (Var xn))))
              (Var (new_FOv_pp_pre2 atm))))).
      apply conj.
apply is_un_predless_corresp; assumption.

      apply SOt.


    exists (allFO (Var xn) (replace_pred_l
           (list_closed_allFO
              (implSO atm
                 (newnew_pre (instant_cons_empty' atm (ST phi2 (Var xn)))
                    (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn))
                    (rev_seq (S (Nat.max (max_FOv (implSO atm (ST phi2 (Var xn)))) xn))
                       (length
                          (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn))))
                             (Var xn)))))) lx) (preds_in (ST (mimpl phi1 phi2) (Var xn)))
           (list_Var (length (preds_in (ST (mimpl phi1 phi2) (Var xn))))
              (Var (new_FOv_pp_pre2 atm)))
           (vsS_syn_l (FOv_att_P_l atm (preds_in (ST (mimpl phi1 phi2) (Var xn))))
              (Var (new_FOv_pp_pre2 atm))))).
      apply conj.
apply is_un_predless_corresp_atm; assumption.
      apply SOt.
Defined.

(* Lemma vsSahlq_full_SO_loc : forall xn phi1 phi2,
  vsSahlq_ante phi1 = true ->
  uniform_pos phi2  ->
  existsT (alpha : SecOrder),
is_unary_predless alpha = true /\
closed_except alpha (Var xn) /\
forall W Iv Ip Ir w,
  SOturnst W (alt_Iv Iv w (Var xn)) Ip Ir alpha <->
  SOturnst W (alt_Iv Iv w (Var xn)) Ip Ir (uni_closed_SO (ST (mimpl phi1 phi2) (Var xn))).
Proof.
  intros xn phi1 phi2 H1 H2.
  destruct (vsSahlq_full_SO_pre_loc xn phi1 phi2 H1 H2) as  [lx [atm [Hat [[rel [Hrel [Hin SOt]]]| [Hin SOt] ]]]].
    exists ( (replace_pred_l
           (list_closed_allFO
              (implSO (conjSO rel atm)
                 (newnew_pre (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))
                    (rem_FOv
                       (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn))))
                       (Var xn))
                    (rev_seq
                       (S (Nat.max (max_FOv (implSO (conjSO rel atm) (ST phi2 (Var xn)))) xn))
                       (length
                          (rem_FOv
                             (FOvars_in
                                (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn))))
                             (Var xn)))))) lx) (preds_in (ST (mimpl phi1 phi2) (Var xn)))
           (list_Var (length (preds_in (ST (mimpl phi1 phi2) (Var xn))))
              (Var (new_FOv_pp_pre2 atm)))
           (vsS_syn_l (FOv_att_P_l (conjSO rel atm) (preds_in (ST (mimpl phi1 phi2) (Var xn))))
              (Var (new_FOv_pp_pre2 atm))))).
      apply conj.
apply is_un_predless_corresp; assumption.
apply conj.
admit.

      apply SOt.


    exists ((replace_pred_l
           (list_closed_allFO
              (implSO atm
                 (newnew_pre (instant_cons_empty' atm (ST phi2 (Var xn)))
                    (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn))
                    (rev_seq (S (Nat.max (max_FOv (implSO atm (ST phi2 (Var xn)))) xn))
                       (length
                          (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn))))
                             (Var xn)))))) lx) (preds_in (ST (mimpl phi1 phi2) (Var xn)))
           (list_Var (length (preds_in (ST (mimpl phi1 phi2) (Var xn))))
              (Var (new_FOv_pp_pre2 atm)))
           (vsS_syn_l (FOv_att_P_l atm (preds_in (ST (mimpl phi1 phi2) (Var xn))))
              (Var (new_FOv_pp_pre2 atm))))).
      apply conj.
apply is_un_predless_corresp_atm; assumption.
apply conj. admit.
      apply SOt.
Admitted. *)

Lemma closed_except_pres_equiv : forall alpha beta x,
  (forall W Iv Ip Ir, SOturnst W Iv Ip Ir alpha <-> SOturnst W Iv Ip Ir beta) ->
  closed_except alpha x ->
  closed_except beta x.
Proof.
Admitted.

Lemma closed_except_pres_equiv_rev : forall alpha beta x,
  (forall W Iv Ip Ir, SOturnst W Iv Ip Ir alpha <-> SOturnst W Iv Ip Ir beta) ->
  closed_except beta x ->
  closed_except alpha x.
Proof.
  intros alpha beta x H.
  apply closed_except_pres_equiv. intros.
  split; intros HH; apply H; assumption.
Qed.

Lemma closed_except_allSO : forall alpha P x,
  closed_except (allSO P alpha) x <->
  closed_except alpha x.
Proof.
  intros alpha P x.
  unfold closed_except. simpl.
  apply iff_refl.
Qed.

Lemma closed_except_list_closed_SO : forall lP alpha x,
  closed_except (list_closed_SO alpha lP) x <->
  closed_except alpha x.
Proof.
  induction lP; intros alpha x. apply iff_refl.
  simpl. split; intros H. apply closed_except_allSO in H.
    apply (IHlP alpha) in H. assumption.

    apply closed_except_allSO. apply IHlP. assumption.
Qed.

Lemma vsSahlq_full_SO_loc : forall xn phi1 phi2,
  vsSahlq_ante phi1 = true ->
  uniform_pos phi2  ->
  existsT (alpha : SecOrder),
is_unary_predless alpha = true /\
closed_except alpha (Var xn) /\
forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir alpha <->
  SOturnst W Iv Ip Ir (uni_closed_SO (ST (mimpl phi1 phi2) (Var xn))).
Proof.
  intros xn phi1 phi2 H1 H2.
  destruct (vsSahlq_full_SO_pre_loc xn phi1 phi2 H1 H2) as  [lx [atm [Hat [[rel [Hrel [Hin [Hc SOt]]]]| [Hin [Hc SOt]] ]]]].
    exists ( (replace_pred_l
           (list_closed_allFO
              (implSO (conjSO rel atm)
                 (newnew_pre (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))
                    (rem_FOv
                       (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn))))
                       (Var xn))
                    (rev_seq
                       (S (Nat.max (max_FOv (implSO (conjSO rel atm) (ST phi2 (Var xn)))) xn))
                       (length
                          (rem_FOv
                             (FOvars_in
                                (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn))))
                             (Var xn)))))) lx) (preds_in (ST (mimpl phi1 phi2) (Var xn)))
           (list_Var (length (preds_in (ST (mimpl phi1 phi2) (Var xn))))
              (Var (new_FOv_pp_pre2 atm)))
           (vsS_syn_l (FOv_att_P_l (conjSO rel atm) (preds_in (ST (mimpl phi1 phi2) (Var xn))))
              (Var (new_FOv_pp_pre2 atm))))).
      apply conj.
apply is_un_predless_corresp; assumption.
apply conj.
  assumption.
(*   apply (closed_except_pres_equiv_rev _ _ _ SOt).
  apply closed_except_list_closed_SO. apply closed_except_ST. *)

      apply SOt.


    exists ((replace_pred_l
           (list_closed_allFO
              (implSO atm
                 (newnew_pre (instant_cons_empty' atm (ST phi2 (Var xn)))
                    (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn))
                    (rev_seq (S (Nat.max (max_FOv (implSO atm (ST phi2 (Var xn)))) xn))
                       (length
                          (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn))))
                             (Var xn)))))) lx) (preds_in (ST (mimpl phi1 phi2) (Var xn)))
           (list_Var (length (preds_in (ST (mimpl phi1 phi2) (Var xn))))
              (Var (new_FOv_pp_pre2 atm)))
           (vsS_syn_l (FOv_att_P_l atm (preds_in (ST (mimpl phi1 phi2) (Var xn))))
              (Var (new_FOv_pp_pre2 atm))))).
      apply conj.
apply is_un_predless_corresp_atm; assumption.
apply conj. assumption.
(*   apply (closed_except_pres_equiv_rev _ _ _ SOt).
  apply closed_except_list_closed_SO. apply closed_except_ST. *)

      apply SOt.
Qed.

Theorem vsSahlq_full_Modal_sep : forall phi1 phi2,
  vsSahlq_ante phi1 = true ->
  uniform_pos phi2  ->
  existsT (alpha : SecOrder),
is_unary_predless alpha = true /\
forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir alpha <->
  mturnst_frame W Ir (mimpl phi1 phi2).
Proof.
  intros phi1 phi2 H1 H2.
  destruct (vsSahlq_full_SO 0 phi1 phi2 H1 H2) as [alpha [Hun SOt]].
  exists alpha. apply conj. assumption.
  intros. split; intros HH.
    apply (correctness_ST _ _ (Var 0) Iv Ip).
    apply SOt. assumption.

    apply SOt.
    apply (correctness_ST _ _ (Var 0) Iv Ip).
    assumption.
Defined.

Theorem vsSahlq_full_Modal_sep_loc : forall phi1 phi2,
  vsSahlq_ante phi1 = true ->
  uniform_pos phi2  ->
  existsT2 (alpha : SecOrder), exists (x : FOvariable),
is_unary_predless alpha = true /\
closed_except alpha x /\
forall W Iv Ip Ir w,
SOturnst W (alt_Iv Iv w x) Ip Ir alpha <->
  mturnst_frame_loc W Ir w (mimpl phi1 phi2).
Proof.
  intros phi1 phi2 H1 H2.
  destruct (vsSahlq_full_SO_loc 0 phi1 phi2 H1 H2) as [alpha [Hun [Hc SOt]]].
  exists alpha. exists (Var 0). apply conj. assumption.
  apply conj. assumption.
  intros. split; intros HH.
    apply (correctness_ST_loc _ _ (Var 0) Iv Ip).
    apply SOt. assumption.

    apply SOt.
    apply (correctness_ST_loc _ _ (Var 0) Iv Ip).
    assumption.
Defined.

Theorem vsSahlq_full_Modal_loc_changing_the_name : forall phi,
  vsSahlq phi ->
  existsT2 (alpha : SecOrder),
  exists (x : FOvariable),
is_unary_predless alpha = true /\
closed_except alpha x /\
forall W Iv Ip Ir w,
  SOturnst W (alt_Iv Iv w x) Ip Ir alpha <->
  mturnst_frame_loc W Ir w phi.
Proof.
  intros phi H. destruct phi; try contradiction.
  simpl in H. case_eq (vsSahlq_ante phi1); intros Hs;
    rewrite Hs in *. 2 : contradiction.
  apply vsSahlq_full_Modal_sep_loc; assumption.
Defined.

Theorem vsSahlq_full_Modal : forall phi,
  vsSahlq phi ->
  existsT (alpha : SecOrder),
is_unary_predless alpha = true /\
forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir alpha <->
  mturnst_frame W Ir phi.
Proof.
  intros phi H. destruct phi; try contradiction.
  simpl in H. case_eq (vsSahlq_ante phi1); intros Hs;
    rewrite Hs in *. 2 : contradiction.
  apply vsSahlq_full_Modal_sep; assumption.
Defined.

(* Print All Dependencies vsSahlq_full_Modal. *)