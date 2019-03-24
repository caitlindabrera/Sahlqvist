Require Export high_mods.
Require Import SO_facts3 vsS_syn_sem consistent.

Fixpoint newnew_pre alpha lv ln : SecOrder :=
  match lv, ln with
  | nil, _ => alpha
  | _, nil => alpha
  | cons x lv', cons n ln' =>
    replace_FOv (newnew_pre alpha lv' ln') x (Var n)
  end.

Lemma newnew_pre_nil : forall l alpha,
  newnew_pre alpha l nil = alpha.
Proof. induction l; intros alpha; auto. Qed.

Lemma want16 : forall l beta n xn ym,
    ~ (Var xn) = (Var ym) ->
    free_FO beta (Var ym) = false ->
    ym <= n ->  In (Var ym) l ->
    ~ In (Var ym) (FOvars_in
        (newnew_pre beta (rem_FOv (Var xn) l)
        (rev_seq (S n)
        (length (rem_FOv (Var xn) l))))).
Proof.
  induction l; intros beta n xn ym Hneq Hfree Hleb Hin2. contradiction.
  simpl in Hin2. destruct Hin2.
  + subst. simpl. rewrite FOvariable_dec_r; auto.
    simpl.  rewrite rep__ren_list. apply rename_FOv_list_not_eq.
    apply FOv_not. lia.
  + simpl. destruct (FOvariable_dec (Var xn) a); subst.
    simpl. apply IHl; auto.
    simpl. rewrite rep__ren_list.
    destruct (FOvariable_dec a (Var (S (n + length (rem_FOv (Var xn) l))))).
      subst. rewrite rename_FOv_list_refl. apply IHl; auto.
    destruct (FOvariable_dec (Var ym) a). subst.
    apply rename_FOv_list_not_eq. apply FOv_not. lia.
    rewrite is_in_FOvar_rename_FOv_list; auto.
    apply FOv_not. lia.
Qed.

Lemma want15 : forall beta xn a alpha,
  free_FO beta a = false ->
  In a (FOvars_in beta) ->
  SOQFree beta = true ->
  ~ att_allFO_var alpha (Var xn) ->
  ~ (Var xn) = a ->
  In a (FOvars_in alpha) ->
  ~ In  a (FOvars_in
    (newnew_pre (instant_cons_empty' alpha beta)
       (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' alpha beta)) )
       (rev_seq (S (Nat.max (Nat.max (max_FOv alpha) (max_FOv beta)) xn))
          (length
             (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' alpha beta))))))).
Proof.
  intros beta xn [ym] alpha Hfree Hin3 Hno Hat Hneq Hin2.
  apply want16; auto.
  apply free_FO_instant_cons_empty'_f; auto. 
  unfold max_FOv. apply want19_pre in Hin2. 
  lia. apply kk1; auto.
Qed.

Lemma want14 : forall l beta xn a alpha,
  SOQFree beta = true ->
  free_FO beta a = false ->
  ~ Var xn = a ->
  In a (FOvars_in beta) ->
  incl l (FOvars_in alpha) ->
  ~ att_allFO_var alpha (Var xn) ->
  In a (FOvars_in alpha) ->
  ~  att_allFO_var
    (newnew_pre (instant_cons_empty' alpha beta)
       (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' alpha beta)))
       (rev_seq (S (Nat.max (Nat.max (max_FOv alpha) (max_FOv beta)) xn))
          (length
             (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' alpha beta)))))) a.
Proof.
  intros l beta xn [ym] alpha Hno Hfree Hin Hneq Hin3 Hat Hin2.
  apply in_FOvar_att_allFO_x.  apply want15; auto.
Qed.

Lemma aa23 : forall l alpha x n,
  ~ l = nil ->
  var_in_SO alpha x ->
  ~ In x l ->
  ~ att_allFO_var alpha x ->
  (max_FOv alpha) <= n ->
  ~ att_allFO_var (newnew_pre alpha l (rev_seq (S n) (length l))) x.
Proof.
  induction l; intros alpha x n Hnil Hocc Hin Hat Hleb. auto.
  simpl in *.
  pose proof Hocc as Hocc'.   pose proof Hleb as Hleb'.
  unfold var_in_SO in Hocc. unfold max_FOv in *.
  case_eq l. 
  + intros Hnil2. rewrite Hnil2 in *. simpl.
    rewrite <- plus_n_O.
    apply rep_FOv_att_allFO; try assumption.
    destruct x. intros H. inversion H. subst. 
    apply want19_pre in Hocc. lia.
  + intros z l' Heq. apply rep_FOv_att_allFO.  
    rewrite <- Heq. apply IHl; subst; firstorder.
    intros HH. destruct x. inversion HH. subst. 
    apply want19_pre in Hocc. lia.
Qed.

Lemma aa23_EX : forall l alpha x n,
  ~ l = nil ->
  var_in_SO alpha x ->
  ~ In x l ->
  ~ att_exFO_var alpha x ->
  (max_FOv alpha) <= n ->
  ~ att_exFO_var (newnew_pre alpha l
    (rev_seq (S n) (length l))) x.
Proof.
  induction l; intros alpha x n Hnil Hocc Hin Hat Hleb.
    simpl. assumption.

    simpl. simpl in Hin. apply not_or_and in Hin.
    case_eq l. intros Hnil2. rewrite Hnil2 in *. simpl.
      rewrite <- plus_n_O.
      apply rep_FOv_att_exFO; try assumption.
      unfold var_in_SO in Hocc. unfold max_FOv in Hleb.
      destruct x. apply want19_pre in Hocc. intros HH. inversion HH.
      subst. firstorder.

      intros z l' Heq. assert (~ l = nil) as HH.
      intros HH2. rewrite HH2 in Heq. discriminate.
      destruct Hin as [Hin' Hin].
      specialize (IHl _ _ n HH Hocc Hin Hat Hleb).
      apply rep_FOv_att_exFO. rewrite <- Heq. apply IHl.
      rewrite <- Heq.
      intros H. destruct x. inversion H as [H']. subst.
      unfold max_FOv in Hleb. unfold var_in_SO in Hocc.
      apply want19_pre in Hocc. firstorder.
Qed.

Lemma aa24 : forall l alpha beta ym n,
  In (Var ym) (FOvars_in alpha) ->
  ~ In (Var ym) (FOvars_in beta) ->
  ~ In (Var ym) l ->  ym <= n ->
~ att_allFO_var
    (newnew_pre (instant_cons_empty' alpha beta) l
       (rev_seq (S n) (length l))) (Var ym).
Proof.
  induction l; intros alpha beta ym n H1 H2 H3 Hleb.
    simpl. apply att_allFO_instant_cons_empty'.
    apply in_FOvar_att_allFO_x. assumption.

    simpl. apply rep_FOv_att_allFO. apply IHl; auto.
    firstorder. intros HH. inversion HH. lia.
Qed.

Lemma kk14'  : forall lx ln x alpha,
~ In x lx -> closed_except alpha x ->
(S (max_FOv alpha)) <= (min_l ln) ->
closed_except (newnew_pre alpha lx ln) x.
Proof.
  induction lx; intros ln [xn] alpha Hin Hc Hleb. auto.
  simpl in *. destruct a as [ym].
  destruct ln. assumption.
  apply not_or_and in Hin. destruct Hin as [Hin1 Hin2].
  case_eq (min_l (cons n ln)).
    intros Hmn; rewrite Hmn in *. inversion Hleb. 
  intros m Hmn.
  destruct (PeanoNat.Nat.eq_dec xn n) as [Hbeq2 | Hbeq2].
  + subst. apply kk19 in Hc.
    rewrite Hmn in Hleb.
    destruct (min_l_cons ln n) as [H1 | H2].
      rewrite H1 in Hmn. subst. lia. 
    rewrite H2 in Hmn. 
    apply min_l_leb_cons2 in H2. lia.
  + apply kk15; try assumption. auto.
    apply FOv_not. auto.
    case_eq ln.
      intros Hln. rewrite newnew_pre_nil.
      assumption.
    intros n' l' Hln. rewrite <- Hln.
    apply IHlx; try assumption.
    rewrite Hmn in Hleb.
    destruct (min_l_cons  ln n) as [H1 | H2].
    rewrite H1 in Hmn. 
    pose proof H1 as H1'.
    apply min_l_leb_cons1 in H1. lia.
    subst. discriminate. lia.
Qed.

Lemma aa3' : forall lx ln alpha,
  length lx = length ln ->
  (S (max_FOv alpha)) <= (min_l ln) ->
   (max_FOv (newnew_pre alpha lx ln)) <=
          (max (max_FOv alpha) (max_l ln)).
Proof.
  induction lx; intros ln alpha Hl Hleb; simpl in *.
  + destruct ln. 2 : discriminate. lia.
  + destruct ln. discriminate.
    simpl in *. case_eq ln.
    ++ intros Hln; rewrite Hln in *.
       destruct lx. 2 : discriminate.
       simpl. destruct (in_dec FOvariable_dec a (FOvars_in alpha)).
       rewrite aa18_t. lia. lia. firstorder.
       rewrite rep_FOv_not_in. lia. firstorder.
    ++ intros m lm Hln. rewrite <- Hln.
       destruct (in_dec FOvariable_dec a (FOvars_in (newnew_pre alpha lx ln))).
       eapply (PeanoNat.Nat.le_trans). apply le_max_FOv_replace_FOv.
       assert (max_FOv (newnew_pre alpha lx ln) <= 
               Nat.max (max_FOv alpha) (max_l ln)) as Hass.
         apply IHlx; firstorder. rewrite Hln in *. lia.
       lia.
       rewrite rep_FOv_not_in. eapply PeanoNat.Nat.le_trans.
       apply IHlx; firstorder. rewrite Hln in *. lia. lia.
       firstorder.
Qed.

Lemma aa : forall ln lx alpha n,
  length lx = length ln ->
  (S (max_FOv alpha)) <= (min_l ln)  ->
   (S (max_l ln)) <= n ->
   (S(max_FOv (newnew_pre alpha lx ln))) <= n.
Proof.
  intros ln lx alpha n Hl H1 H2.
  eapply PeanoNat.Nat.le_trans.
  + apply le_n_S. apply aa3'; auto.
  + pose proof (le_min__max_l ln). lia. 
Qed.

Lemma newnew_pre_extra_n : forall lx l1 l2 alpha,
  length lx = length l1 ->
  newnew_pre alpha lx (app l1 l2) = newnew_pre alpha lx l1.
Proof.
  induction lx; intros l1 l2 alpha Heq. auto.
  destruct l1. simpl in *. discriminate.
  simpl. rewrite IHlx. reflexivity.
  simpl in *. inversion Heq. reflexivity.
Qed.

Lemma newnew_pre_extra_x : forall ln l1 l2 alpha,
  length ln = length l1 ->
  newnew_pre alpha (app l1 l2) ln = newnew_pre alpha l1 ln.
Proof.
  induction ln; intros l1 l2 alpha Heq.
    do 2 rewrite newnew_pre_nil. reflexivity.

    destruct l1. simpl in *. discriminate.
    simpl. rewrite IHln. reflexivity.
    simpl in *. inversion Heq. reflexivity.
Qed.

Lemma kk10 : forall lx ln alpha x,
  closed_except alpha x ->
  ~ In x lx ->
  (S (max_FOv alpha)) <= (min_l ln) ->
  decr_strict ln ->
  forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir alpha <->
  SOturnst W Iv Ip Ir (newnew_pre alpha lx ln).
Proof.
  induction lx; intros ln alpha x Hc Hin Hleb Hd W Iv Ip Ir.
    simpl. apply iff_refl.
  simpl. destruct ln. apply iff_refl.
  simpl in Hin. apply not_or_and in Hin.
  destruct Hin. case_eq ln. 
  + intros Hln. subst. rewrite newnew_pre_nil.
    apply (kk10_nil _ x); auto. 

  + intros m ln' Hln. rewrite <- Hln.
    assert ((S (max_FOv alpha)) <= (min_l ln)) as Hleb2.
      simpl in *. subst. lia.
    inversion Hd. subst. remember (m :: ln') as ln.
    assert ((S(max_l ln)) <= n) as Hleb3.  lia.
    destruct (FOvariable_dec a (Var n)); subst.
      rewrite rep_FOv_rem. apply (IHlx _ _ x); auto.
    split; intros SOt. 
    ++ destruct (aa11' (m :: ln') lx) as [[ln1 [ln2 [H1 H2]]] | [lx1 [lx2 [H1 H2]]]].
         -- rewrite H2. rewrite newnew_pre_extra_n. 2 : assumption.
            case_eq lx. 
            * intros Hlx. simpl. destruct x as [xn].
              pose proof  (equiv_replace_FOv_free_FO_f alpha a (Var n)).
              unfold replace_FOv in H5.
              apply H5; try assumption.
              apply aa14 with (x := (Var xn));
              try assumption. auto.
              apply Hc.
              destruct (in_dec FOvariable_dec (Var xn) (FOvars_in alpha)).
              apply want19_pre in i. intros HH. inversion HH. subst.
              
              unfold max_FOv in Hleb. clear -Hleb i. simpl in *.
              lia. destruct Hc as [HH1 HH2]. apply free_FO_var_in in HH1.
              contradiction.
              intros HH. apply var_in_SO_max_FOv_gen2 in HH.
              apply HH. simpl in Hleb. clear -Hleb.
              destruct ln'; lia.

            * intros y lx' Hlx. rewrite <- Hlx.
              assert (~ var_in_SO (newnew_pre alpha lx ln1) (Var n)) as
                  Has. destruct n. simpl in *. destruct ln'; inversion Hleb. 
                intros HH.  apply var_in_SO_max_FOv_gen2 in HH. apply HH.
                apply aa; auto. rewrite H2 in *.
                destruct ln2. simpl in *. rewrite app_nil_r in *. auto.
                rewrite min_l_app in Hleb2.
                lia. destruct ln1. rewrite Hlx in *. simpl in *. discriminate.
                discriminate. discriminate.
                apply aa16 with (l2 := ln2).  rewrite <- H2.  lia.
              apply equiv_replace_FOv_free_FO_f; auto.
              ** pose proof (kk14' lx ln1) as H3'.
                 apply aa14 with (x := x); auto.
                 apply H3'; try assumption.
                 apply (aa15 _ _ ln2); auto.
                 intros H'. rewrite H' in H1. simpl in H1.
                 rewrite Hlx in H1. discriminate.
                 rewrite <- H2. assumption.
              ** apply var_in_SO_free_FO. assumption. 
              ** rewrite <- (newnew_pre_extra_n lx ln1 ln2).
                 rewrite <- H2. apply (IHlx _ alpha x).
                 all: try assumption. 
(* -- *)
          -- rewrite H2. rewrite newnew_pre_extra_x. 2 : assumption.
             assert (~ var_in_SO (newnew_pre alpha lx1 (m :: ln')) (Var n)) as
                 Has. intros HH. destruct n. simpl in *.
               apply var_in_SO_max_FOv_gen2 in HH. apply HH.
               simpl in Hleb. lia.   apply var_in_SO_max_FOv_gen2 in HH.
               apply HH. apply aa; auto. 
               apply equiv_replace_FOv_free_FO_f; auto.
             --- pose proof (kk14' lx1 (m :: ln')) as H3'.
                 apply aa14 with (x := x). apply H3'; try assumption.
                 subst. clear -H0. firstorder. auto.
             --- apply var_in_SO_free_FO. assumption. 
             --- rewrite <- (newnew_pre_extra_x _ _ lx2).
                 rewrite <- H2. apply (IHlx (m :: ln') alpha x).
                 all: try assumption.

(* -- *)

    ++  unfold lt in H3. remember (m :: ln') as ln.
       destruct (aa11' ln lx) as [[ln1 [ln2 [H1 H2]]] | [lx1 [lx2 [H1 H2]]]].
       - rewrite H2 in *. rewrite newnew_pre_extra_n in *. 2 : assumption.
         case_eq lx.
         -- intros Hlx. simpl. destruct x as [xn]. rewrite Hlx in *.
            pose proof  (equiv_replace_FOv_free_FO_f alpha a (Var n)) as H5.
            unfold replace_FOv in H5.
            apply H5; try assumption.
            apply aa14 with (x := (Var xn));
              try assumption; auto.
            rewrite <- H2 in *. 
            apply (aa17 _ ln n (Var xn)); try assumption. 
            intros HH. apply var_in_SO_max_FOv_gen2 in HH. apply HH.
            rewrite <- H2 in *. clear -Hleb. simpl in *.
            destruct ln; lia.
         -- intros y lx' Hlx.
            assert (~ var_in_SO (newnew_pre alpha lx ln1) (Var n)) as
                Has. intros HH. apply var_in_SO_max_FOv_gen2 in HH. 
              apply HH. apply aa; auto. destruct ln1. simpl in *. 
              destruct lx; discriminate.
              clear -Hleb H3. eapply PeanoNat.Nat.le_trans.
              apply Hleb. change (n :: (n1 :: ln1) ++ ln2) with ((n :: (n1 :: ln1)) ++ ln2). 
              destruct ln2. rewrite app_nil_r in *. simpl. lia.
              rewrite min_l_app. simpl. lia. discriminate. discriminate.
              destruct ln1.  simpl in *. destruct ln2. simpl in *.
              firstorder. simpl in *. destruct lx; discriminate.
              apply (aa16 _ ln2). rewrite <- H2 in *. lia. 
            apply equiv_replace_FOv_free_FO_f in SOt; auto.
            * rewrite <- (newnew_pre_extra_n _ ln1 ln2) in SOt.
              rewrite <- H2 in *. apply (IHlx ln alpha x) in SOt.
              all: try assumption. 
            * pose proof (kk14' lx ln1) as H4'.
              apply aa14 with (x := x).
              apply H4'; try assumption.
              apply (aa15 _ _ ln2).
              intros H'. rewrite H' in H1. simpl in H1.
              rewrite Hlx in H1. discriminate.
              assumption. auto.
            * apply var_in_SO_free_FO. assumption.

       - rewrite H2 in *. rewrite newnew_pre_extra_x in *. 2 : assumption.
         assert (~ var_in_SO (newnew_pre alpha lx1 ln) (Var n)) as
             Has. destruct n.
           simpl in *. destruct ln; firstorder. 
           intros HH.  apply var_in_SO_max_FOv_gen2 in HH.
           apply HH. apply aa; auto. 
         apply equiv_replace_FOv_free_FO_f in SOt; auto.
         -- rewrite <- (newnew_pre_extra_x _ _ lx2) in SOt.
            rewrite <- H2 in *. apply (IHlx ln alpha x).
            all: try assumption. 
         -- pose proof (kk14' lx1 ln) as H4'.
            apply aa14 with (x := x).
            apply H4'; try assumption.
            firstorder. auto.
         -- apply var_in_SO_free_FO. assumption.
Qed.

Lemma newnew_pre_rename_FOv_list_l : forall lv ln alpha,
  FOvars_in (newnew_pre alpha lv ln) = 
  rename_FOv_list_l (FOvars_in alpha) lv (FOvify ln). 
Proof.
  induction lv; intros ln alpha. auto.
  simpl. destruct ln. auto.
  simpl. rewrite rep__ren_list. rewrite IHlv. auto.
Qed.

Lemma SOQFree_newnew_pre : forall l1 l2 alpha,
  SOQFree alpha = true ->
  SOQFree (newnew_pre alpha l1 l2) = true.
Proof.
  induction l1; intros l2 alpha H; auto.
  simpl. destruct l2. assumption.
  apply SOQFree_rep_FOv. auto. 
Qed.

Lemma want3 : forall l alpha beta xn,
  SOQFree beta = true ->
  incl l (FOvars_in alpha) ->
  ~ att_allFO_var alpha (Var xn) ->
  closed_except beta (Var xn) ->
  ~ att_allFO_var beta (Var xn) ->
~ ex_att_allFO_lvar
  (newnew_pre (instant_cons_empty' alpha beta)
     (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' alpha beta)))
     (rev_seq (S (Nat.max (Nat.max (max_FOv alpha) (max_FOv beta)) xn))
        (length
           (rem_FOv 
              (Var xn) (FOvars_in (instant_cons_empty' alpha beta)))))) l.
Proof.
  induction l; intros alpha beta xn Hno Hin Hat Hcl Hat2.
    intros H. inversion H.
  simpl in *. pose proof (incl_hd _ _ _ _ Hin) as H4. apply incl_lcons in Hin. 
  intros H. inversion H; subst.
  + destruct a as [ym]. 
    destruct (FOvariable_dec (Var ym) (Var xn)) as [Heq | Heq].
    inversion Heq. subst.
    case_eq ( rem_FOv (Var xn) (FOvars_in (instant_cons_empty' alpha beta))).
      intros HH. rewrite HH in *. simpl in *.
      eapply att_allFO_instant_cons_empty' in H2; auto.
    intros mm lmm Hmm. 
    apply aa23 in H2; auto.
    ++ rewrite Hmm . discriminate.
    ++ apply var_in_SO_instant_cons_empty'.
       inversion Hcl as [Hcl1 Hcl2].
       pose proof (var_in_SO_free_FO beta (Var xn)) as H0. 
       rewrite Hcl1 in *. unfold var_in_SO in *.
       destruct (in_dec FOvariable_dec (Var xn) (FOvars_in beta)) as [H2' | H2']. 
       auto. apply H0 in H2'. discriminate.
    ++ apply is_in_FOvar_rem_FOv_f. 
    ++ apply att_allFO_instant_cons_empty'. auto.
    ++ rewrite max_FOv_instant_cons_empty'.
       unfold max_FOv. simpl.  lia.
    ++ destruct (in_dec FOvariable_dec (Var ym) (FOvars_in beta)).
    eapply want14 in H4; auto.
    unfold max_FOv in *. simpl in *. 
    simpl in *. contradiction (H4 H2).
    all : auto. inversion Hcl as [Hcl1 Hcl2].
    apply Hcl2. auto. apply Hin.
    eapply aa24. apply H4. apply n. 3 : apply H2.
    intros HH. apply want13 in HH. unfold instant_cons_empty' in HH.
    apply kk8 in HH; auto. auto.
    pose proof (want19_pre _ _ H4).
    unfold max_FOv in *. lia.
  + apply IHl in H2; auto.
Qed.

Lemma lem3 : forall beta rel atm xn P,
  REL rel = true ->
  AT atm = true ->
  SOQFree beta = true ->
  closed_except beta (Var xn) ->
  ~ att_allFO_var beta (Var xn) ->
~ ex_att_allFO_lvar
     (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)
        (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)))
        (rev_seq (S (Nat.max (Nat.max (Nat.max (max_FOv rel) (max_FOv atm)) (max_FOv beta)) xn))
           (length
              (rem_FOv  (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) beta))
                )))) (FOv_att_P (conjSO rel atm) P).
Proof.
  intros beta rel atm xn P HREL HAT Hno Hcl Hatt.
  rewrite <- max_FOv_conjSO.
  apply want3; try assumption. 
  apply incl_FOv_att_P. intros H.
  inversion H; subst.
  apply att_allFO_var_REL in H3; auto.
  apply att_allFO_var_AT in H3; auto.
Qed.

Lemma lem3_atm : forall beta atm xn P,
  AT atm = true ->
  SOQFree beta = true ->
  closed_except beta (Var xn) ->
  ~ att_allFO_var beta (Var xn) ->
~ ex_att_allFO_lvar
     (newnew_pre (instant_cons_empty' atm beta)
        (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta)))
        (rev_seq (S (Nat.max (Nat.max (max_FOv atm) (max_FOv beta)) xn))
           (length
              (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta))
                 )))) (FOv_att_P atm P).
Proof.
  intros beta  atm xn P  HAT Hno Hcl Hatt.
  apply want3; try assumption.  apply incl_FOv_att_P.
  simpl. intros H. apply att_allFO_var_AT in H; auto.
Qed.


Lemma want15_EX : forall beta xn a alpha,
  free_FO beta a = false ->
  In a (FOvars_in beta) ->
  SOQFree beta = true ->
  ~ att_exFO_var alpha (Var xn) ->
  ~ (Var xn) = a ->
  In a (FOvars_in alpha) ->
  ~ In a (FOvars_in
    (newnew_pre (instant_cons_empty' alpha beta)
       (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' alpha beta)))
       (rev_seq (S (Nat.max (Nat.max (max_FOv alpha) (max_FOv beta)) xn))
          (length
             (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' alpha beta))))))).
Proof.
  intros beta xn [ym] alpha Hfree Hin3 Hno Hat Hneq Hin2.
  apply want16; try assumption.
  apply free_FO_instant_cons_empty'_f; try assumption.
  unfold max_FOv. apply want19_pre in Hin2. lia.
  apply kk1; auto.
Qed.

Lemma want14_EX : forall l beta xn a alpha,
  SOQFree beta = true ->
  free_FO beta a = false ->
  ~ Var xn = a ->
  In a (FOvars_in beta) ->
  incl l (FOvars_in alpha) ->
  ~ att_exFO_var alpha (Var xn) ->
  In a (FOvars_in alpha) ->
 ~ att_exFO_var
    (newnew_pre (instant_cons_empty' alpha beta)
       (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' alpha beta)))
       (rev_seq (S (Nat.max (Nat.max (max_FOv alpha) (max_FOv beta)) xn))
          (length
             (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' alpha beta)) ))))
    a.
Proof.
  intros l beta xn [ym] alpha Hno Hfree Hin Hneq Hin3 Hat Hin2.
  apply is_in_FOvar_att_exFO_var_neg.
  apply want15_EX; try assumption.
Qed.

Lemma aa24_EX : forall l alpha beta ym n,
  In (Var ym) (FOvars_in alpha) ->
  ~ In (Var ym) (FOvars_in beta) ->
  ~ In (Var ym) l ->
  ym <= n ->
~ att_exFO_var
    (newnew_pre (instant_cons_empty' alpha beta) l
       (rev_seq (S n) (length l))) (Var ym).
Proof.
  induction l; intros alpha beta ym n H1 H2 H3 Hleb; simpl.
  + apply att_exFO_instant_cons_empty'.
    apply is_in_FOvar_att_exFO_var_neg. assumption.
  + destruct (PeanoNat.Nat.eq_dec (S (n + length l)) ym).
    subst. lia. 
    apply rep_FOv_att_exFO.
    apply IHl; try assumption. 
    simpl in H3. firstorder.
    apply FOv_not. auto.
Qed.

Lemma want3_EX : forall l alpha beta xn,
  SOQFree beta = true ->
  incl l (FOvars_in alpha) ->
  ~ att_exFO_var alpha (Var xn) ->
  closed_except beta (Var xn) ->
  ~ att_exFO_var beta (Var xn) ->
~ ex_att_exFO_lvar
  (newnew_pre (instant_cons_empty' alpha beta)
     (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' alpha beta)))
     (rev_seq (S (Nat.max (Nat.max (max_FOv alpha) (max_FOv beta)) xn))
        (length
           (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' alpha beta))
  )))) l.
Proof.
  induction l; intros alpha beta xn Hno Hin Hat Hcl Hat2.
  intros HH. inversion HH. pose proof (incl_hd _ _ _ _ Hin) as Hin'.
  apply incl_lcons in Hin.  destruct a as [ym].
  destruct (PeanoNat.Nat.eq_dec xn ym) as [Hbeq | Hbeq].
  + subst ym.
    case_eq (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' alpha beta))).
    intros H. simpl.
    intros HH. inversion HH; subst.
    apply att_exFO_instant_cons_empty' in H2;  auto.
    eapply IHl in Hat2; auto. rewrite H in Hat2.
    simpl in Hat2. contradiction. auto. auto.
    intros y l' Heq. rewrite <- Heq.
    intros HH. inversion HH; subst. apply aa23_EX in H1; auto.
    rewrite Heq. discriminate. 
    apply var_in_SO_instant_cons_empty'.
    apply free_FO_var_in. apply Hcl. apply is_in_FOvar_rem_FOv_f.
    apply att_exFO_instant_cons_empty'. assumption.
    rewrite max_FOv_instant_cons_empty'. lia. 
    apply IHl in H1; auto. 
  + destruct (in_dec FOvariable_dec (Var ym) (FOvars_in beta)).
    intros HH. inversion HH; subst.  
    eapply want14_EX in H1; auto.
    inversion Hcl as [Hcl1 Hcl2]. apply Hcl2. apply FOv_not. auto.
    apply FOv_not. auto.  apply Hin.
    apply IHl in H1; auto.
    intros HH. inversion HH; subst.
    eapply aa24_EX in H1; auto.
    intros HH2. apply want13 in HH2.
    eapply kk7. 2 : apply HH2. auto.
    apply FOv_not. auto.
    apply want19_pre in Hin'. unfold max_FOv. lia.
    apply IHl in H1; auto.
Qed.

Lemma lem5 : forall beta rel atm xn P,
  REL rel = true ->
  AT atm = true ->
  SOQFree beta = true ->
  closed_except beta (Var xn) ->
  ~ att_exFO_var beta (Var xn) ->
~ ex_att_exFO_lvar
     (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)
        (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)))
        (rev_seq (S (Nat.max (Nat.max (Nat.max (max_FOv rel) (max_FOv atm)) (max_FOv beta)) xn))
           (length
              (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) beta))
                )))) (FOv_att_P (conjSO rel atm) P).
Proof.
  intros beta rel atm xn P HREL HAT Hno Hcl Hatt.
  rewrite <- max_FOv_conjSO.
  apply want3_EX; try assumption.
  apply incl_FOv_att_P.
  intros HH; inversion HH; subst.
  apply att_exFO_var_REL in H2; auto.
  apply att_exFO_var_AT in H2; auto.
Qed. 

Lemma lem5_atm : forall beta atm xn P,
  AT atm = true ->
  SOQFree beta = true ->
  closed_except beta (Var xn) ->
  ~att_exFO_var beta (Var xn) ->
~ ex_att_exFO_lvar
     (newnew_pre (instant_cons_empty' atm beta)
        (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta)))
        (rev_seq (S (Nat.max (Nat.max (max_FOv atm) (max_FOv beta)) xn))
           (length
              (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta))
                )))) (FOv_att_P atm P).
Proof.
  intros beta atm xn P  HAT Hno Hcl Hatt.
  apply want3_EX; try assumption.
  apply incl_FOv_att_P.
  simpl. apply att_exFO_var_AT.
  all : try assumption.
Qed.

Lemma lem2 : forall lP beta rel atm xn,
  REL rel = true ->
  AT atm = true ->
  SOQFree beta = true ->
  ~ att_allFO_var beta (Var xn) ->
  closed_except beta (Var xn) ->
~ ex_att_allFO_llvar
  (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)
     (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)))
     (rev_seq
        (S (Nat.max (Nat.max (Nat.max (max_FOv rel) (max_FOv atm)) (max_FOv beta)) xn))
        (length (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) ))))
  (FOv_att_P_l (conjSO rel atm) lP).
Proof.
  induction lP; intros beta rel atm xn HREL HAT Hno Hat1 Hcl H.
    inversion H.
  simpl in *. inversion H; subst. 
  apply lem3 in H2; auto.
  apply IHlP in H2 ; assumption.
Qed.

Lemma lem2_atm : forall lP beta atm xn,
  AT atm = true ->
  SOQFree beta = true ->
  ~ att_allFO_var beta (Var xn) ->
  closed_except beta (Var xn) ->
~ ex_att_allFO_llvar
  (newnew_pre (instant_cons_empty' atm beta)
     (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta)))
     (rev_seq
        (S (Nat.max (Nat.max ( (max_FOv atm)) (max_FOv beta)) xn))
        (length (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta))))))
  (FOv_att_P_l atm lP).
Proof.
  induction lP; intros beta atm xn HAT Hno Hat1 Hcl H.
    inversion H.
  simpl in *. inversion H; subst. 
  apply lem3_atm in H2; auto. 
  apply IHlP in H2 ; assumption.
Qed.

Lemma lem4a : forall lP beta rel atm xn,
  REL rel = true ->
  AT atm = true ->
  SOQFree beta = true ->
  ~ att_exFO_var beta (Var xn) ->
  closed_except beta (Var xn) ->
~ ex_att_exFO_llvar
  (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)
     (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)))
     (rev_seq
        (S (Nat.max (Nat.max (Nat.max (max_FOv rel) (max_FOv atm)) (max_FOv beta)) xn))
        (length (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) beta))))))
  (FOv_att_P_l (conjSO rel atm) lP).
Proof.
  induction lP; intros beta rel atm xn HREL HAT Hno Hat1 Hcl.
  intros HH. inversion HH.
  simpl FOv_att_P_l. simpl.
  pose proof lem5 as H3. simpl in H3.
  intros HH. inversion HH; subst.
  eapply H3 in H1; try assumption.
  clear H3. apply IHlP in H1; assumption.
Qed.

Lemma lem4a_atm : forall lP beta atm xn,
  AT atm = true ->
  SOQFree beta = true ->
  ~ att_exFO_var beta (Var xn) ->
  closed_except beta (Var xn) ->
~ ex_att_exFO_llvar
  (newnew_pre (instant_cons_empty' atm beta)
     (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta)))
     (rev_seq
        (S (Nat.max (Nat.max ( (max_FOv atm)) (max_FOv beta)) xn))
        (length (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta))))))
  (FOv_att_P_l atm lP).
Proof.
  induction lP; intros beta atm xn HAT Hno Hat1 Hcl.
  intros HH. inversion HH.
  simpl FOv_att_P_l. simpl.
  pose proof lem5_atm as H3. simpl in H3.
  intros HH. inversion HH; subst.
  eapply H3 in H1; try assumption.
  clear H3. apply IHlP in H1; assumption.
Qed.

Lemma preds_in_newnew_pre : forall l1 l2 alpha,
  preds_in (newnew_pre alpha l1 l2) = (preds_in alpha).
Proof.
  induction l1; intros l2 alpha. auto.
  simpl. destruct l2. reflexivity.
  rewrite preds_in_rename_FOv. apply IHl1.
Qed.

Lemma hopeful2 : forall  lx rel atm y xn beta,
  FO_frame_condition (replace_pred_l (list_closed_allFO (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)  
      (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) beta)) xn))
        (length       (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) beta))))))) lx)
    (preds_in (list_closed_allFO
      (implSO (conjSO rel atm) beta) lx)) (list_var (length (preds_in (list_closed_allFO
      (implSO (conjSO rel atm) beta) lx))) y)
    (vsS_syn_l (FOv_att_P_l (conjSO rel atm) (preds_in (list_closed_allFO
      (implSO (conjSO rel atm) beta) lx))) y)) = true.
Proof.
  intros lx rel atm y xn beta.
  rewrite rep_pred_l_list_closed_allFO.
  rewrite FO_frame_condition_list_closed_allFO.
  rewrite rep_pred_l_implSO.
  simpl. rewrite preds_in_list_closed_allFO.
  rewrite please2.
  rewrite please2. reflexivity.
  rewrite preds_in_newnew_pre.
  apply (incl_trans _ _ _ _ (something3 _ _)).
  simpl. firstorder. 
  simpl.  firstorder. 
Qed.


Lemma hopeful2_atm : forall  lx atm y xn beta,
  FO_frame_condition (replace_pred_l (list_closed_allFO (implSO
    atm
    (newnew_pre (instant_cons_empty' atm beta)  
      (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta)))
      (rev_seq (S (max (max_FOv (implSO atm beta)) xn))
        (length       (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta))))))) lx)
    (preds_in (list_closed_allFO
      (implSO atm beta) lx)) (list_var (length (preds_in (list_closed_allFO
      (implSO atm beta) lx))) y)
    (vsS_syn_l (FOv_att_P_l atm (preds_in (list_closed_allFO
      (implSO atm beta) lx))) y)) = true.
Proof.
  intros lx atm y xn beta.
  rewrite rep_pred_l_list_closed_allFO.
  rewrite FO_frame_condition_list_closed_allFO.
  rewrite rep_pred_l_implSO.
  simpl. rewrite preds_in_list_closed_allFO.
  rewrite please2.
  rewrite please2. reflexivity.
  rewrite preds_in_newnew_pre.
  apply (incl_trans _ _ _ _ (something3 _ _)).
  simpl. firstorder. 
  simpl. firstorder.
Qed.