Require Export high_mods.
Require Import newnew vsS_syn_sem consistent nlist_sem_eg.
Require Import SO_facts3 Correctness_ST.

Open Scope type_scope.
 
Lemma equiv_new_simpl3_lP : forall lP llv x alpha W Iv Ip Ir pa0,
  length lP = length llv ->
  SOQFree alpha = true ->
  consistent_lP_llv lP llv ->
  @consistent_lP_lpa _ pa0 lP (vsS_pa_l Iv llv (list_var (length lP) x)) ->
  ~ ex_att_allFO_llvar alpha llv ->
  ~ ex_att_exFO_llvar alpha llv ->
    SOturnst W Iv (alt_Ip_list Ip (vsS_pa_l Iv llv (list_var (length lP) x)) lP) Ir alpha <->
    SOturnst W Iv Ip Ir (replace_pred_l alpha lP (list_var (length lP) x) (vsS_syn_l llv x)).
Proof.
  induction lP; intros llv x alpha W Iv Ip Ir pa0 Hl Hno Hcon Hind Hat1 Hat2.
  + simpl in *. destruct llv. simpl. apply iff_refl.
    discriminate.
  + simpl. case_eq llv. intros H; rewrite H in *. discriminate.
    intros lv llv' Heq.
    rewrite Heq in Hl. simpl in *. inversion Hl as [H0].
    assert (SOQFree (replace_pred alpha a x (disj_l lv x)) = true) as Hno'.
      apply SOQFree_rep_pred. assumption. apply SOQFree_disj_l.
    rewrite rep_pred__l_consistent.
    split; intros HSOt.
    * apply (IHlP llv' x _ W Iv Ip Ir pa0); auto.
      rewrite Heq in Hcon. apply consistent_lP_llv_cons in Hcon.
      assumption.
      intros P. specialize (Hind P).
      unfold consistent_lP_lpa_P in *.
      destruct Hind as [pa [ n Heq2]]. 
      destruct (predicate_dec P a); subst.
      - unfold indicies_l2 in Heq2; simpl in *.
        pred_dec_l_rep. simpl in Heq2.
        destruct n. discriminate. simpl  in Heq2.
        inversion Heq2. exists pa. exists n. rewrite ind_gen_pre_cons in H2.
        rewrite H1 in *.  assumption.
      - simpl in Heq2.
        exists pa. exists n. unfold indicies_l2 in Heq2. simpl in Heq2. 
        rewrite predicate_dec_r in Heq2. rewrite ind_gen_pre_cons in Heq2.
        auto. auto.
      - rewrite Heq in Hat1.
        apply ex_att_allFO_llvar_cons_not in Hat1. 
          apply ex_attached_allFO_llv_rep_pred. apply no_FOquant_disj_l. 
          apply Hat1.
      - rewrite Heq in Hat2. simpl in Hat2.
        if_then_else_hyp_tzf. 
        apply ex_att_exFO_llvar_rep_pred. apply no_FOquant_disj_l.        
        apply ex_att_exFO_llvar_cons_not in Hat2.        
        apply Hat2.
      - apply equiv_new_simpl3; try assumption.
        apply SOQFree__P. assumption.
        rewrite Heq in Hat1. simpl in Hat1. 
        apply ex_att_allFO_llvar_cons_not in Hat1. apply Hat1. 
        rewrite Heq in Hat2. simpl in Hat2. 
        apply ex_att_exFO_llvar_cons_not in Hat2. apply Hat2. 
    * apply (IHlP llv' x _ W Iv Ip Ir pa0) in HSOt; try assumption.
      - apply equiv_new_simpl3; try assumption.
        apply SOQFree__P. assumption.
        rewrite Heq in Hat1. simpl in Hat1.
        apply ex_att_allFO_llvar_cons_not in Hat1.
        apply Hat1.
        rewrite Heq in Hat2. simpl in Hat2.
        apply ex_att_exFO_llvar_cons_not in Hat2.
        apply Hat2.
      - rewrite Heq in *. clear H. apply consistent_lP_llv_cons in Hcon.
        assumption.
      - rewrite Heq in *. apply consistent_lP_lpa_vsS_pa_l in Hind.
        assumption.
      - rewrite Heq in Hat1. simpl in Hat1.
        apply ex_att_allFO_llvar_cons_not in Hat1.
        rewrite Heq in Hat2. simpl in Hat2.
        apply ex_attached_allFO_llv_rep_pred. apply no_FOquant_disj_l.
        apply Hat1.
      - rewrite Heq in Hat2. simpl in Hat2.
        apply ex_att_exFO_llvar_rep_pred. apply no_FOquant_disj_l.
        apply ex_att_exFO_llvar_cons_not in Hat2. apply Hat2.
    * apply FO_frame_condition_l_vsS_syn_l.
    * apply FO_frame_condition_disj_l.
    * rewrite Heq in Hcon. apply consistent_lP_llv__lcond_cons. assumption.
    * rewrite repeat_list_var.
        assert (cons x (repeat x (length lP)) =
                repeat x (length (cons a lP))) as Heq2.
          reflexivity.
      rewrite Heq2. apply consistent_lP_lx_repeat.  lia.
Qed. 

Lemma vsSahlq_instant_aim1_fwd4 : forall lP beta rel atm y xn W Iv Ip Ir,
  REL rel = true ->
  AT atm = true ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  ~ att_allFO_var beta (Var xn) ->
  ~ att_exFO_var beta (Var xn) ->
  closed_except beta (Var xn) ->
  var_in_SO (instant_cons_empty' (conjSO rel atm) beta) (Var xn) ->
  SOturnst W Iv Ip Ir (list_closed_SO (implSO (conjSO rel atm)
              (instant_cons_empty' (conjSO rel atm) beta)) lP) ->
  SOturnst W Iv Ip Ir (replace_pred_l (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)  
      (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) beta)) xn))
        (length       (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)))))))
    lP (list_var (length lP) y)
    (vsS_syn_l (FOv_att_P_l (conjSO rel atm) lP) y)).
Proof.
  intros lP beta rel atm y xn W Iv Ip Ir Hrel Hat Hun Hno Hat1 Hat2 Hc Hocc SOt.
  apply (equiv_new_simpl3_lP lP (FOv_att_P_l (conjSO rel atm) lP) y 
(implSO (conjSO rel atm)
        (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)
           (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)))
           (rev_seq (S (Nat.max (max_FOv (implSO (conjSO rel atm) beta)) xn))
              (length (rem_FOv (Var xn)(FOvars_in (instant_cons_empty' (conjSO rel atm) beta)))))))

      W Iv Ip Ir pa_f).
    apply length_FOv_att_P_l.

    simpl. rewrite SOQFree_rel.
    rewrite SOQFree_atm. apply SOQFree_newnew_pre.
    unfold instant_cons_empty'.
    apply Rep_Pred_FOv.SOQFree_rep_pred_l_nlist.
    all : try assumption. 

    apply consistent_lP_llv_FOv_att_P_l.

    apply lem1a_cons.

    intros HH. 
    eapply ex_att_allFO_llvar_implSO_fwd in HH. 
    destruct HH. apply ex_att_allFO_llvar_conjSO_fwd in H.
    destruct H as [H | H].
    apply ex_att_allFO_llvar_REL in H; auto.
    apply ex_att_allFO_llvar_AT in H; auto.
    rewrite max_FOv_implSO in H. rewrite max_FOv_conjSO in H.
    apply lem2 in H; auto.
    
    apply ex_att_exFO_llvar_implSO. apply att_exFO_var__llv.
    intros x HH. inversion HH; subst.
      apply att_exFO_var_REL in H2; auto.
      apply att_exFO_var_AT in H2; auto.
      simpl. rewrite max_FOv_implSO. rewrite max_FOv_conjSO.
      apply lem4a; assumption.


    destruct (nlist_list_closed_SO' W Iv Ir 
        (implSO (conjSO rel atm) (instant_cons_empty' (conjSO rel atm) beta)) lP Ip) as [fwd rev].
    specialize (fwd SOt). clear rev.
    case_eq (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) beta))).
      intros HH. simpl newnew_pre in *.
      destruct (nlist_list_ex (length lP) (vsS_pa_l Iv (FOv_att_P_l (conjSO rel atm) lP) (list_var (length lP) y))
        ) as [l Heq].

        rewrite length_vsS_pa_l.
        reflexivity.
      rewrite <- Heq. apply fwd.
    intros z ll Heq. rewrite <- Heq.

    intros SOt2.
    apply (kk10  (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)))
(rev_seq (S (Nat.max (max_FOv (implSO (conjSO rel atm) beta)) xn))
        (length (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)))))
      (instant_cons_empty' (conjSO rel atm) beta) (Var xn)).

        apply closed_except_inst_cons_empty'. assumption.

        apply is_in_FOvar_rem_FOv_f.

        rewrite Heq. simpl length.
        rewrite min_l_rev_seq.
        simpl. rewrite max_FOv_instant_cons_empty'.
        rewrite max_FOv_implSO. rewrite max_FOv_conjSO.
        lia.

        apply decr_strict_rev_seq.

      destruct (nlist_list_ex (length lP) (vsS_pa_l Iv (FOv_att_P_l (conjSO rel atm) lP) (list_var (length lP) y))
        ) as [l Heq'].

        rewrite length_vsS_pa_l.
        reflexivity.

        rewrite <- Heq'. apply fwd. rewrite Heq'.
        assumption.
Qed.

Lemma vsSahlq_instant_aim1_fwd4_atm : forall lP beta atm y xn W Iv Ip Ir,
  AT atm = true ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  ~ att_allFO_var beta (Var xn) ->
  ~att_exFO_var beta (Var xn) ->
  closed_except beta (Var xn) ->
  var_in_SO (instant_cons_empty' atm beta) (Var xn) ->
  SOturnst W Iv Ip Ir (list_closed_SO (implSO atm
              (instant_cons_empty' atm beta)) lP) ->
  SOturnst W Iv Ip Ir (replace_pred_l (implSO
    atm
    (newnew_pre (instant_cons_empty' atm beta)  
      (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta)))
      (rev_seq (S (max (max_FOv (implSO atm beta)) xn))
        (length       (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta)))))))
    lP (list_var (length lP) y)
    (vsS_syn_l (FOv_att_P_l atm lP) y)).
Proof.
  intros lP beta atm y xn W Iv Ip Ir Hat Hun Hno Hat1 Hat2 Hc Hocc SOt.
  apply (equiv_new_simpl3_lP lP (FOv_att_P_l atm lP) y 
(implSO atm
        (newnew_pre (instant_cons_empty' atm beta)
           (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta)))
           (rev_seq (S (Nat.max (max_FOv (implSO atm beta)) xn))
              (length (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta)))))))

      W Iv Ip Ir pa_f).
    apply length_FOv_att_P_l.

    simpl.
    rewrite SOQFree_atm.
 apply SOQFree_newnew_pre.    simpl.
    unfold instant_cons_empty'.
    apply Rep_Pred_FOv.SOQFree_rep_pred_l_nlist.
    all : try assumption. 

    apply consistent_lP_llv_FOv_att_P_l.

    apply lem1a_cons.

    apply ex_att_allFO_llvar_implSO. apply att_allFO_var__llv.
      intros x. 
      apply att_allFO_var_AT. assumption.
      simpl. rewrite max_FOv_implSO.
      apply lem2_atm; assumption.

    apply ex_att_exFO_llvar_implSO. apply att_exFO_var__llv.
      intros x.
      apply att_exFO_var_AT. assumption.
      simpl. rewrite max_FOv_implSO. 
      apply lem4a_atm; assumption.

    destruct (nlist_list_closed_SO' W Iv Ir 
        (implSO atm (instant_cons_empty' atm beta)) lP Ip) as [fwd rev].
    specialize (fwd SOt). clear rev.
    case_eq (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta))).
      intros HH. simpl newnew_pre in *.
      destruct (nlist_list_ex (length lP) (vsS_pa_l Iv (FOv_att_P_l atm lP) (list_var (length lP) y))
        ) as [l Heq].

        rewrite length_vsS_pa_l.
        reflexivity.
      rewrite <- Heq. apply fwd.
    intros z ll Heq. rewrite <- Heq.

    intros SOt2.
    apply (kk10  (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta)))
(rev_seq (S (Nat.max (max_FOv (implSO atm beta)) xn))
        (length (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta)))))
      (instant_cons_empty' atm beta) (Var xn)).

        apply closed_except_inst_cons_empty'. assumption.

        apply is_in_FOvar_rem_FOv_f.

        rewrite Heq. simpl length.
        rewrite min_l_rev_seq.
        simpl. rewrite max_FOv_instant_cons_empty'. 
        rewrite max_FOv_implSO. lia.

        apply decr_strict_rev_seq.

      destruct (nlist_list_ex (length lP) (vsS_pa_l Iv (FOv_att_P_l atm lP) (list_var (length lP) y))
        ) as [l Heq'].

        rewrite length_vsS_pa_l.
        reflexivity.

        rewrite <- Heq'. apply fwd. rewrite Heq'.
        assumption.
Qed.

Lemma vsSahlq_instant_aim1_fwd4_closer : forall lP beta rel atm y xn W Iv Ip Ir,
  REL rel = true ->
  AT atm = true ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  ~ att_allFO_var beta (Var xn) ->
  ~ att_exFO_var beta (Var xn) ->
  closed_except beta (Var xn) ->
  var_in_SO (instant_cons_empty' (conjSO rel atm) beta) (Var xn) ->
  incl (preds_in (implSO (conjSO rel atm) beta)) lP ->
  SOturnst W Iv Ip Ir (list_closed_SO (implSO (conjSO rel atm) beta) lP) ->
  SOturnst W Iv Ip Ir (replace_pred_l (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)  
      (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) beta)) xn))
        (length       (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) )))))
    lP (list_var (length lP) y)
    (vsS_syn_l (FOv_att_P_l (conjSO rel atm) lP) y)).
Proof.
  intros lP beta rel atm y xn W Iv Ip Ir Hrel Hat Hun Hno Hat1 Hat2 Hc Hocc Hin SOt.
  apply vsSahlq_instant_aim1_fwd4; try assumption.
  apply list_closed_SO_instant_cons_empty2; try assumption.
  simpl. rewrite Hno.
  rewrite SOQFree_rel.
  rewrite SOQFree_atm.
  reflexivity. all: assumption.
Qed.

Lemma vsSahlq_instant_aim1_fwd4_closer_atm : forall lP beta atm y xn W Iv Ip Ir,
  AT atm = true ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  ~ att_allFO_var beta (Var xn) ->
  ~ att_exFO_var beta (Var xn) ->
  closed_except beta (Var xn) ->
  var_in_SO (instant_cons_empty' atm beta) (Var xn) ->
  incl (preds_in (implSO atm beta)) lP ->
  SOturnst W Iv Ip Ir (list_closed_SO (implSO atm beta) lP) ->
  SOturnst W Iv Ip Ir (replace_pred_l (implSO
    atm
    (newnew_pre (instant_cons_empty' atm beta)  
      (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta)))
      (rev_seq (S (max (max_FOv (implSO atm beta)) xn))
        (length       (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta)))))))
    lP (list_var (length lP) y)
    (vsS_syn_l (FOv_att_P_l atm lP) y)).
Proof.
  intros lP beta atm y xn W Iv Ip Ir Hat Hun Hno Hat1 Hat2 Hc Hocc Hin SOt.
  apply vsSahlq_instant_aim1_fwd4_atm; try assumption.
  apply list_closed_SO_instant_cons_empty2; try assumption.
  simpl. rewrite Hno.
  rewrite SOQFree_atm.
  reflexivity. all: assumption.
Qed.

Lemma vsSahlq_instant_aim1_fwd4_closer2 : forall lx lP beta rel atm y xn W Iv Ip Ir,
  REL rel = true ->
  AT atm = true ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  ~ att_allFO_var beta (Var xn)  ->
  ~ att_exFO_var beta (Var xn) ->
  closed_except beta (Var xn) ->
  var_in_SO (instant_cons_empty' (conjSO rel atm) beta) (Var xn) ->
  incl (preds_in (implSO (conjSO rel atm) beta)) lP ->
  SOturnst W Iv Ip Ir (list_closed_SO (list_closed_allFO
      (implSO (conjSO rel atm) beta) lx) lP) ->
  SOturnst W Iv Ip Ir (replace_pred_l (list_closed_allFO (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)  
      (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) beta)) xn))
        (length       (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) beta))))))) lx)
    lP (list_var (length lP) y)
    (vsS_syn_l (FOv_att_P_l (conjSO rel atm) lP) y)).
Proof.
  intros lx lP beta rel atm y xn W Iv Ip Ir Hrel Hat Hun Hno Hat1 Hat2 Hc Hocc Hin SOt. 
  rewrite rep_pred_l_list_closed_allFO.
  pose proof equiv_list_closed_allFO.
  apply (impl_list_closed_allFO _ (list_closed_SO (implSO (conjSO rel atm) beta) lP)).
    intros.
    apply vsSahlq_instant_aim1_fwd4_closer.
    all : try assumption.
    apply equiv_list_closed_SO_list_closed_allFO.
    assumption.
Qed.

Lemma vsSahlq_instant_aim1_fwd4_closer2_atm : forall lx lP beta atm y xn W Iv Ip Ir,
  AT atm = true ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  ~ att_allFO_var beta (Var xn) ->
  ~ att_exFO_var beta (Var xn) ->
  closed_except beta (Var xn) ->
  var_in_SO (instant_cons_empty' atm beta) (Var xn) ->
  incl (preds_in (implSO atm beta)) lP ->
  SOturnst W Iv Ip Ir (list_closed_SO (list_closed_allFO
      (implSO atm beta) lx) lP) ->
  SOturnst W Iv Ip Ir (replace_pred_l (list_closed_allFO (implSO
    atm
    (newnew_pre (instant_cons_empty' atm beta)  
      (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta)))
      (rev_seq (S (max (max_FOv (implSO atm beta)) xn))
        (length       (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta))))))) lx)
    lP (list_var (length lP) y)
    (vsS_syn_l (FOv_att_P_l atm lP) y)).
Proof.
  intros lx lP beta atm y xn W Iv Ip Ir Hat Hun Hno Hat1 Hat2 Hc Hocc Hin SOt. 
  rewrite rep_pred_l_list_closed_allFO.
  pose proof equiv_list_closed_allFO.
  apply (impl_list_closed_allFO _ (list_closed_SO (implSO atm beta) lP)).
    intros.
    apply vsSahlq_instant_aim1_fwd4_closer_atm.
    all : try assumption.
    apply equiv_list_closed_SO_list_closed_allFO.
    assumption.
Qed.

(* ---------------------------------------- *)

Lemma preprocess_vsSahlq_ante_predSO_againTRY : forall p f,
  conjSO_exFO_relatSO (predSO p f) = true ->
existsT2 (lv : list FOvariable) (atm : SecOrder),
  (AT atm = true) *
  ((existsT rel : SecOrder,
      REL rel = true /\
      incl (preds_in (conjSO rel atm)) (preds_in (predSO p f))  /\
      (forall (W : Set) (Iv : FOvariable -> W)
         (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop),
       SOturnst W Iv Ip Ir (predSO p f) <->
       SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv))) +
   (incl (preds_in atm) (preds_in (predSO p f)) /\
   (forall (W : Set) (Iv : FOvariable -> W)
      (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop),
    SOturnst W Iv Ip Ir (predSO p f) <->
    SOturnst W Iv Ip Ir (list_closed_exFO atm lv)))).
Proof.
  intros p f H.  exists nil.  exists (predSO p f).
  simpl. apply pair. auto.
  right. destruct (in_predicate_dec p (p::nil)); firstorder.
Defined.

Lemma preprocess_vsSahlq_ante_exFO_againTRY : forall alpha f,
  conjSO_exFO_relatSO (exFO f alpha) = true ->
  (existsT P : predicate, Pred_in_SO (exFO f alpha) P ) ->
(conjSO_exFO_relatSO alpha = true ->
          (existsT P : predicate, Pred_in_SO alpha P ) ->
          existsT2 (lv : list FOvariable) (atm : SecOrder),
            (AT atm = true) *
            ((existsT rel : SecOrder,
                REL rel = true /\
                incl (preds_in (conjSO rel atm))
                  (preds_in alpha)  /\
                (forall (W : Set) (Iv : FOvariable -> W)
                   (Ip : predicate -> W -> Prop) 
                   (Ir : W -> W -> Prop),
                 SOturnst W Iv Ip Ir alpha <->
                 SOturnst W Iv Ip Ir
                   (list_closed_exFO (conjSO rel atm) lv))) +
             (incl (preds_in atm) (preds_in alpha) /\
             (forall (W : Set) (Iv : FOvariable -> W)
                (Ip : predicate -> W -> Prop) 
                (Ir : W -> W -> Prop),
              SOturnst W Iv Ip Ir alpha <->
              SOturnst W Iv Ip Ir (list_closed_exFO atm lv))))) ->
existsT2 (lv : list FOvariable) (atm : SecOrder),
  (AT atm = true) *
  ((existsT rel : SecOrder,
      REL rel = true /\
      incl (preds_in (conjSO rel atm))
        (preds_in (exFO f alpha)) /\
      (forall (W : Set) (Iv : FOvariable -> W)
         (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop),
       SOturnst W Iv Ip Ir (exFO f alpha) <->
       SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv))) +
   (incl (preds_in atm) (preds_in (exFO f alpha)) /\
   (forall (W : Set) (Iv : FOvariable -> W)
      (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop),
    SOturnst W Iv Ip Ir (exFO f alpha) <->
    SOturnst W Iv Ip Ir (list_closed_exFO atm lv)))).
Proof.
  intros alpha f H Hocc IHalpha.
    simpl in H.
    destruct Hocc as [P Hocc]. rewrite <- Pred_in_SO_exFO in Hocc.
    assert (existsT P, Pred_in_SO alpha P) as Hocc2.
      exists P. assumption.
    specialize (IHalpha H Hocc2).
    destruct IHalpha as [lv [atm [HAT [  [rel [HREL [Hin SOt]]] | [Hin SOt] ]]]];
      exists (cons f lv);
      exists atm;
      apply pair; try assumption.
      left.
      exists rel.
      apply conj. assumption.
      apply conj. simpl. auto. 

      intros W Iv Ip Ir.
      simpl list_closed_exFO.
      do 2 rewrite SOturnst_exFO.
      split; intros SOt2;
        destruct SOt2 as [d SOt2];
        exists d;
        apply SOt;
        assumption.

      right.
      apply conj. simpl. auto.
      intros W Iv Ip Ir.
      simpl list_closed_exFO. simpl.
      split; intros SOt2;
        destruct SOt2 as [d SOt2];
        exists d;  apply SOt;
        assumption.
Defined.

Lemma preprocess_vsSahlq_ante_5_againTRY : forall alpha1 alpha2 lv1 rel1 lv2 rel2,
  conjSO_exFO_relatSO alpha2 = true ->
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
  conjSO_exFO_relatSO alpha1 = true ->
existsT2 lv : list FOvariable,
  (existsT rel : SecOrder,
     REL rel = true /\
      (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
         (Ir : W -> W -> Prop),
       SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
       SOturnst W Iv Ip Ir (list_closed_exFO rel lv))).
Proof.
  intros alpha1 alpha2 lv1 rel1 lv2 rel2
         H HREL1 H_1 HREL2 H_2 H1.
     exists (app 
                (replace_FOv_A_list rel2 
                     (list_closed_exFO rel1 lv1) lv2)
(replace_FOv_A_list rel1 
                  (replace_FOv_A rel2
                     (list_closed_exFO rel1 lv1) lv2) lv1 )).

pose proof equiv3_3_struc2_both.
    exists (conjSO
                (replace_FOv_A rel1
                   (replace_FOv_A rel2 (list_closed_exFO rel1 lv1) lv2) lv1)
                (replace_FOv_A rel2 (list_closed_exFO rel1 lv1) lv2)).
    apply conj.
      pose proof (same_struc_replace_FOv_A rel2 (list_closed_exFO rel1 lv1)
         lv2) as Hsame2.
      pose proof (same_struc_replace_FOv_A rel1
         (replace_FOv_A rel2
            (list_closed_exFO rel1 lv1) lv2) lv1) as Hsame1.
      apply same_struc_comm in Hsame2.
      apply same_struc_REL in Hsame2; try assumption.
      apply same_struc_comm in Hsame1.
      apply same_struc_REL in Hsame1; try assumption.
      simpl; rewrite Hsame1; assumption.

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

Lemma trying2 : forall alpha,
  conjSO_exFO_relatSO alpha = true ->
  (forall P, ~ Pred_in_SO alpha P) ->
  existsT2 lv rel,
  REL rel = true /\
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha <->
      SOturnst W Iv Ip Ir (list_closed_exFO rel lv)).
Proof.
  induction alpha; intros H1 H2; try (    simpl in *; discriminate).
    simpl in *. specialize (H2 p).
    unfold Pred_in_SO in H2. firstorder.

    exists nil. exists (relatSO f f0). simpl. firstorder.

    assert (forall P, ~ Pred_in_SO (alpha) P) as H2'.
      intros P. specialize (H2 P).
      rewrite <- Pred_in_SO_exFO in H2.
      assumption.
    simpl in H1. destruct (IHalpha H1 H2') as [lv [rel [Hrel H]]].
    exists (cons f lv). exists rel.
    apply conj. assumption.
    intros. simpl list_closed_exFO.
    do 2 rewrite SOturnst_exFO. split; intros [d SOt];
      exists d; apply H; assumption.

    simpl in H1. case_eq (conjSO_exFO_relatSO alpha1);
      intros H3; rewrite H3 in H1. 2 : discriminate.
    destruct (IHalpha1 H3 (Pred_in_SO_conjSO_all_f_l _ _ H2))
      as [lv [rel [HREL H]]].
    destruct (IHalpha2 H1 (Pred_in_SO_conjSO_all_f_r _ _ H2))
      as [lv2 [rel2 [HREL2 H4]]].
    destruct (preprocess_vsSahlq_ante_5_againTRY alpha1 alpha2 lv rel lv2 rel2)
      as [lv' [rel' [Hrel' H']]];
      try assumption.
    exists lv'. exists rel'.
    apply conj. assumption.
    assumption.
Defined.

Lemma preprocess_vsSahlq_ante_notocc_againTRY : forall alpha,
  conjSO_exFO_relatSO alpha = true ->
  (forall P, ~ Pred_in_SO alpha P) ->
  existsT2 lv rel,
      (REL rel = true) /\
      (incl (preds_in rel) (preds_in alpha)) /\
        forall W Iv Ip Ir,
          SOturnst W Iv Ip Ir alpha <->
          SOturnst W Iv Ip Ir (list_closed_exFO rel lv).
Proof.
  intros alpha H1 H2. destruct (trying2 alpha H1 H2)
     as [lv [rel [Hrel H]]].
  exists lv. exists rel.
  apply conj. assumption. 
  apply conj. rewrite preds_in_rel.
  firstorder. all : auto.
Defined.

Lemma preprocess_vsSahlq_ante_4_againTRY : forall alpha1 alpha2 lv1 rel1 lv2 rel2 atm2,
  conjSO_exFO_relatSO alpha2 = true ->
  REL rel1 = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha1 <->
      SOturnst W Iv Ip Ir (list_closed_exFO rel1 lv1)) ->
  REL rel2 = true ->
  AT atm2 = true ->
  incl (preds_in (conjSO rel2 atm2)) (preds_in alpha2) ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha2 <->
      SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel2 atm2) lv2) ) ->
  conjSO_exFO_relatSO alpha1 = true ->
existsT2 lv : list FOvariable,
  (existsT2 atm : SecOrder,
         (AT atm = true) *
    (existsT rel : SecOrder,
       REL rel = true /\
          incl (preds_in (conjSO rel atm))
                       (preds_in (conjSO alpha1 alpha2)) /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
          SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv)))).
Proof.
  intros alpha1 alpha2 lv1 rel1 lv2 rel2 atm2
         H HREL1 H_1 HREL2 HAT2 Hin H_2 H1.
     destruct (same_struc_conjSO_ex _ _ _ (same_struc_replace_FOv_A (conjSO rel2 atm2) 
                                            (list_closed_exFO rel1 lv1)
                                             lv2)) as [rel2' [atm2' Heq2]].
     exists (app 
                (replace_FOv_A_list (conjSO rel2 atm2) 
                     (list_closed_exFO rel1 lv1) lv2)
(replace_FOv_A_list rel1 
                  (replace_FOv_A (conjSO rel2 atm2)
                     (list_closed_exFO rel1 lv1) lv2) lv1 )).
    exists  atm2'.
    apply pair.
      pose proof (same_struc_replace_FOv_A (conjSO rel2 atm2) (list_closed_exFO rel1 lv1)
         lv2) as Hsame2.
      pose proof (same_struc_replace_FOv_A rel1
         (replace_FOv_A (conjSO rel2 atm2)
            (list_closed_exFO rel1 lv1) lv2) lv1) as Hsame1.
      rewrite Heq2 in Hsame2.
      apply same_struc_conjSO_r in Hsame2.
      apply same_struc_comm in Hsame2.
      apply same_struc_AT in Hsame2; try assumption.
    exists (conjSO (replace_FOv_A rel1 (replace_FOv_A (conjSO rel2 atm2) 
                      (list_closed_exFO rel1 lv1) lv2) lv1) rel2').
    apply conj.
      pose proof (same_struc_replace_FOv_A (conjSO rel2 atm2) (list_closed_exFO rel1 lv1)
         lv2) as Hsame2.
      pose proof (same_struc_replace_FOv_A rel1
         (replace_FOv_A (conjSO rel2 atm2)
            (list_closed_exFO rel1 lv1) lv2) lv1) as Hsame1.
      rewrite Heq2 in Hsame2.
      apply same_struc_conjSO_l in Hsame2.
      apply same_struc_comm in Hsame2.
      apply same_struc_REL in Hsame2; try assumption.
      apply same_struc_comm in Hsame1.
      apply same_struc_REL in Hsame1; try assumption.
      simpl; rewrite Hsame1; assumption.

    apply conj.
      assert (preds_in (replace_FOv_A (conjSO rel2 atm2)   
                      (list_closed_exFO rel1 lv1) lv2) =
                       preds_in (conjSO rel2' atm2')) as Hpreds.
        rewrite Heq2. reflexivity.
      simpl. rewrite preds_in_replace_FOv_A in *.
      rewrite <- app_assoc.
      assert (preds_in (conjSO rel2' atm2') = 
              app (preds_in rel2') (preds_in atm2')) as Hpreds2.
        reflexivity.
      rewrite <- Hpreds2.
      rewrite <- Hpreds. simpl. 
      rewrite (preds_in_rel rel1). 
      simpl. apply incl_appr. auto. auto.

    intros W Iv Ip Ir.
    split; intros SOt.
      apply (equiv_list_closed_exFO (conjSO (conjSO (replace_FOv_A rel1 (replace_FOv_A (conjSO rel2 atm2) 
                      (list_closed_exFO rel1 lv1) lv2) lv1) rel2')  atm2')
                                    (conjSO (replace_FOv_A rel1 (replace_FOv_A (conjSO rel2 atm2) 
                      (list_closed_exFO rel1 lv1) lv2) lv1) (conjSO rel2' atm2'))).
        intros; split; intros; apply equiv_conjSO5; assumption.
      rewrite <- Heq2.
      rewrite list_closed_exFO_app.
      apply equiv3_3_struc2_both with (alpha := rel1).
      rewrite SOturnst_conjSO; apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.

      apply (equiv_list_closed_exFO (conjSO (conjSO (replace_FOv_A rel1 (replace_FOv_A (conjSO rel2 atm2) 
                      (list_closed_exFO rel1 lv1) lv2) lv1) rel2')  atm2')
                                    (conjSO (replace_FOv_A rel1 (replace_FOv_A (conjSO rel2 atm2) 
                      (list_closed_exFO rel1 lv1) lv2) lv1) (conjSO rel2' atm2'))) in SOt;
        try (intros; split; intros; apply equiv_conjSO5; assumption).
      rewrite <- Heq2 in SOt.
      rewrite list_closed_exFO_app in SOt.
      apply equiv3_3_struc2_both with (alpha := rel1) in SOt.
      rewrite SOturnst_conjSO; apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.
Defined.


Lemma preprocess_vsSahlq_ante_6_againTRY : forall alpha1 alpha2 lv1 rel1 
        lv2 atm2,
  conjSO_exFO_relatSO alpha2 = true ->
  REL rel1 = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha1 <->
      SOturnst W Iv Ip Ir (list_closed_exFO rel1 lv1)) ->
  AT atm2 = true ->
  incl (preds_in atm2) (preds_in alpha2) ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha2 <->
      SOturnst W Iv Ip Ir (list_closed_exFO atm2 lv2)) ->
  conjSO_exFO_relatSO alpha1 = true ->
existsT2 lv : list FOvariable,
    (existsT2 atm : SecOrder,
       (AT atm = true) *
      (existsT rel : SecOrder,
         REL rel = true /\
          incl (preds_in (conjSO rel atm))
                       (preds_in (conjSO alpha1 alpha2)) /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
          SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv)))).
Proof.
  intros alpha1 alpha2 lv1 rel1  lv2  atm2
        H HREL1 H_1  HAT2 Hin2 H_2 H1.
     exists (app 
                (replace_FOv_A_list atm2
                     (list_closed_exFO rel1 lv1) lv2)
(replace_FOv_A_list rel1 
                  (replace_FOv_A  atm2
                     (list_closed_exFO rel1 lv1) lv2) lv1 )).

    exists (replace_FOv_A atm2 (list_closed_exFO rel1 lv1) lv2).
    apply pair.
      pose proof (same_struc_replace_FOv_A atm2 (list_closed_exFO rel1 lv1)
         lv2) as Hsame2.
      apply same_struc_comm in Hsame2.
      apply same_struc_AT in Hsame2; try assumption.

    exists (replace_FOv_A rel1 (replace_FOv_A atm2 (list_closed_exFO rel1 lv1) lv2) lv1).
    apply conj.
      pose proof (same_struc_replace_FOv_A rel1
         (replace_FOv_A (atm2)
            (list_closed_exFO rel1 lv1) lv2) lv1) as Hsame1.
      apply same_struc_comm in Hsame1.
      apply same_struc_REL in Hsame1; try assumption.

    apply conj.
      simpl. do 2 rewrite preds_in_replace_FOv_A in *.
      apply incl_appr. rewrite (preds_in_rel rel1); auto.

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

Lemma preprocess_vsSahlq_ante_2_againTRY : forall alpha1 alpha2 lv1 rel1 atm1 
                                       lv2 rel2,
  conjSO_exFO_relatSO alpha2 = true ->
  REL rel1 = true ->
  AT atm1 = true ->
  incl (preds_in (conjSO rel1 atm1)) (preds_in alpha1) ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha1 <->
      SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel1 atm1) lv1)) ->
  REL rel2 = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha2 <->
      SOturnst W Iv Ip Ir (list_closed_exFO rel2 lv2)) ->
  conjSO_exFO_relatSO alpha1 = true ->
  existsT2 lv : list FOvariable,
   (existsT2 atm : SecOrder,
       (AT atm = true) *
      (existsT2 rel : SecOrder,
          REL rel = true /\
          incl (preds_in (conjSO rel atm))
                       (preds_in (conjSO alpha1 alpha2)) /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
          SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv)))). 
Proof.
  intros alpha1 alpha2 lv1 rel1 atm1 lv2 rel2 H HREL1 HAT1 Hin H_1
         HREL2 H_2 H1.
    destruct (same_struc_conjSO_ex _ _ _ (same_struc_replace_FOv_A (conjSO rel1 atm1) 
                                            (replace_FOv_A rel2 
                                               (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1))
      as [rel1' [atm1' Heq1]].
     exists (app 
                (replace_FOv_A_list rel2 
                     (list_closed_exFO (conjSO rel1 atm1) lv1) lv2)
(replace_FOv_A_list (conjSO rel1 atm1) 
                  (replace_FOv_A rel2
                     (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1 )).

    exists atm1'.
    apply pair.
      pose proof (same_struc_replace_FOv_A rel2 (list_closed_exFO (conjSO rel1 atm1) lv1)
         lv2) as Hsame2.
      pose proof (same_struc_replace_FOv_A (conjSO rel1 atm1)
         (replace_FOv_A rel2
            (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1) as Hsame1.
      rewrite Heq1 in Hsame1.
      apply same_struc_comm in Hsame2.
      apply same_struc_conjSO_r in Hsame1.
      apply same_struc_comm in Hsame1.
      apply same_struc_AT in Hsame1; try assumption.

    exists (conjSO rel1' (replace_FOv_A rel2 (list_closed_exFO (conjSO rel1 atm1) lv1) lv2)) .
    apply conj.
      pose proof (same_struc_replace_FOv_A rel2 (list_closed_exFO (conjSO rel1 atm1) lv1)
         lv2) as Hsame2.
      pose proof (same_struc_replace_FOv_A (conjSO rel1 atm1)
         (replace_FOv_A rel2
            (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1) as Hsame1.
      rewrite Heq1 in Hsame1.
      apply same_struc_comm in Hsame2.
      apply same_struc_REL in Hsame2; try assumption.
      apply same_struc_conjSO_l in Hsame1.
      apply same_struc_comm in Hsame1.
      apply same_struc_REL in Hsame1; try assumption.
      simpl; rewrite Hsame1; assumption. 

    apply conj.
      assert (preds_in (replace_FOv_A (conjSO rel1 atm1)
                        (replace_FOv_A rel2   
                      (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1) =
                       preds_in (conjSO rel1' atm1')) as Hpreds.
        rewrite Heq1. reflexivity.
      simpl. rewrite preds_in_replace_FOv_A in *.
      simpl in *. 
      
rem_preds_in_rel. rewrite <- app_assoc. simpl. rewrite <- Hpreds.
apply incl_appl. firstorder.

    intros W Iv Ip Ir.
    split; intros SOt.
      apply (equiv_list_closed_exFO 
                (conjSO (conjSO rel1' (replace_FOv_A rel2 (list_closed_exFO (conjSO rel1 atm1) lv1) lv2)) atm1')
                        (conjSO (conjSO rel1' atm1') (replace_FOv_A rel2 (list_closed_exFO (conjSO rel1 atm1) lv1) lv2))).
      apply equiv_conjSO4.
      rewrite <- Heq1.
      rewrite list_closed_exFO_app.
      apply equiv3_3_struc2_both with (alpha := conjSO rel1 atm1).
      simpl.
      apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.

      apply (equiv_list_closed_exFO (conjSO (conjSO rel1' (replace_FOv_A rel2 (list_closed_exFO (conjSO rel1 atm1) lv1) lv2)) atm1')
                                    (conjSO (conjSO rel1' atm1') (replace_FOv_A rel2 (list_closed_exFO (conjSO rel1 atm1) lv1) lv2)))
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


Lemma preprocess_vsSahlq_ante_8_againTRY : forall alpha1 alpha2 lv1 atm1 
        lv2 rel2,
  conjSO_exFO_relatSO alpha2 = true ->
  AT atm1 = true ->
  incl (preds_in atm1) (preds_in alpha1) ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha1 <->
      SOturnst W Iv Ip Ir (list_closed_exFO atm1 lv1)) ->
  REL rel2 = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha2 <->
      SOturnst W Iv Ip Ir (list_closed_exFO rel2 lv2)) ->
  conjSO_exFO_relatSO alpha1 = true ->
existsT2 lv : list FOvariable,
   (existsT2 atm : SecOrder,
       (AT atm = true) *
    (existsT rel : SecOrder,
       REL rel = true /\
          incl (preds_in (conjSO rel atm))
                       (preds_in (conjSO alpha1 alpha2)) /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
          SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv)))).
Proof.
  intros alpha1 alpha2 lv1 atm1 lv2 rel2
        H HAT1 Hin H_1 HREL2 H_2 H1.
     exists (app 
                (replace_FOv_A_list rel2 
                     (list_closed_exFO atm1 lv1) lv2)
(replace_FOv_A_list atm1
                  (replace_FOv_A rel2
                     (list_closed_exFO atm1 lv1) lv2) lv1 )).

    exists (replace_FOv_A atm1 (replace_FOv_A rel2 (list_closed_exFO atm1 lv1) lv2) lv1).
    apply pair.
      pose proof (same_struc_replace_FOv_A rel2 (list_closed_exFO atm1 lv1)
         lv2) as Hsame2.
      pose proof (same_struc_replace_FOv_A atm1
         (replace_FOv_A rel2
            (list_closed_exFO atm1 lv1) lv2) lv1) as Hsame1.
      apply same_struc_comm in Hsame1.
      apply same_struc_AT in Hsame1; try assumption.

    exists (replace_FOv_A rel2 (list_closed_exFO atm1 lv1) lv2).
    apply conj.
      pose proof (same_struc_replace_FOv_A rel2 (list_closed_exFO atm1 lv1)
         lv2) as Hsame2.
      apply same_struc_comm in Hsame2.
      apply same_struc_REL in Hsame2; try assumption.

    apply conj.
    simpl. do 2 rewrite preds_in_replace_FOv_A.
    rem_preds_in_rel. apply incl_appl. auto.

    intros W Iv Ip Ir.
    split; intros SOt.
      apply (equiv_list_closed_exFO (conjSO (replace_FOv_A rel2 (list_closed_exFO atm1 lv1) lv2) (replace_FOv_A atm1 (replace_FOv_A rel2 (list_closed_exFO atm1 lv1) lv2) lv1))
                                    (conjSO (replace_FOv_A atm1 (replace_FOv_A rel2 (list_closed_exFO atm1 lv1) lv2) lv1) (replace_FOv_A rel2 (list_closed_exFO atm1 lv1) lv2))).
        apply equiv_conjSO.
      rewrite list_closed_exFO_app.
      apply equiv3_3_struc2_both with (alpha := atm1).
      simpl.
      apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.

      apply (equiv_list_closed_exFO (conjSO (replace_FOv_A rel2 (list_closed_exFO atm1 lv1) lv2) (replace_FOv_A atm1 (replace_FOv_A rel2 (list_closed_exFO atm1 lv1) lv2) lv1))
                                    (conjSO (replace_FOv_A atm1 (replace_FOv_A rel2 (list_closed_exFO atm1 lv1) lv2) lv1) (replace_FOv_A rel2 (list_closed_exFO atm1 lv1) lv2))) in SOt.
        apply equiv_conjSO.
      rewrite list_closed_exFO_app in SOt.
      apply equiv3_3_struc2_both with (alpha := atm1) in SOt.
      simpl.
      apply conj.
        apply H_2. apply SOt.
        apply H_1. apply SOt.

        apply equiv_conjSO.
Defined. 

Lemma preprocess_vsSahlq_ante_1_againTRY : forall alpha1 alpha2 lv1 rel1 atm1 
        lv2 rel2 atm2,
  conjSO_exFO_relatSO alpha2 = true ->
  REL rel1 = true ->
  AT atm1 = true ->
  incl (preds_in (conjSO rel1 atm1)) (preds_in alpha1) ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha1 <->
      SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel1 atm1) lv1)) ->
  REL rel2 = true ->
  AT atm2 = true ->
  incl (preds_in (conjSO rel2 atm2)) (preds_in alpha2) ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha2 <->
      SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel2 atm2) lv2)) ->
  conjSO_exFO_relatSO alpha1 = true ->
existsT2 lv : list FOvariable,
    (existsT2 atm : SecOrder,
       (AT atm = true) *
      (existsT rel : SecOrder,
         REL rel = true /\
          incl (preds_in (conjSO rel atm))
                       (preds_in (conjSO alpha1 alpha2)) /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
          SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv)))).
Proof.
  intros alpha1 alpha2 lv1 rel1 atm1 lv2 rel2 atm2
        H HREL1 HAT1 Hin1 H_1 HREL2 HAT2 Hin2 H_2 H1.
    destruct (same_struc_conjSO_ex _ _ _ (same_struc_replace_FOv_A (conjSO rel1 atm1) 
                                            (replace_FOv_A (conjSO rel2 atm2) 
                                               (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1))
      as [rel1' [atm1' Heq1]].
    destruct (same_struc_conjSO_ex _ _ _ (same_struc_replace_FOv_A (conjSO rel2 atm2) 
                                            (list_closed_exFO (conjSO rel1 atm1) lv1)
                                             lv2)) as [rel2' [atm2' Heq2]].
     exists (app 
                (replace_FOv_A_list (conjSO rel2 atm2) 
                     (list_closed_exFO (conjSO rel1 atm1) lv1) lv2)
(replace_FOv_A_list (conjSO rel1 atm1) 
                  (replace_FOv_A (conjSO rel2 atm2)
                     (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1 )).

    exists (conjSO atm1' atm2').
    apply pair.
      pose proof (same_struc_replace_FOv_A (conjSO rel2 atm2) (list_closed_exFO (conjSO rel1 atm1) lv1)
         lv2) as Hsame2.
      pose proof (same_struc_replace_FOv_A (conjSO rel1 atm1)
         (replace_FOv_A (conjSO rel2 atm2)
            (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1) as Hsame1.
      rewrite Heq2 in Hsame2.
      rewrite Heq1 in Hsame1.
      apply same_struc_conjSO_r in Hsame2.
      apply same_struc_comm in Hsame2.
      apply same_struc_AT in Hsame2; try assumption.
      apply same_struc_conjSO_r in Hsame1.
      apply same_struc_comm in Hsame1.
      apply same_struc_AT in Hsame1; try assumption.
      simpl; rewrite Hsame1; assumption.

    exists (conjSO rel1' rel2').
    apply conj.
      pose proof (same_struc_replace_FOv_A (conjSO rel2 atm2) (list_closed_exFO (conjSO rel1 atm1) lv1)
         lv2) as Hsame2.
      pose proof (same_struc_replace_FOv_A (conjSO rel1 atm1)
         (replace_FOv_A (conjSO rel2 atm2)
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
      assert (preds_in (replace_FOv_A (conjSO rel1 atm1)
                        (replace_FOv_A (conjSO rel2 atm2)   
                      (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1) =
                       preds_in (conjSO rel1' atm1')) as Hpreds.
        rewrite Heq1. reflexivity.
      assert (preds_in (replace_FOv_A (conjSO rel2 atm2)
                      (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) =
                       preds_in (conjSO rel2' atm2')) as Hpreds0.
        rewrite Heq2. reflexivity.
        simpl. rewrite preds_in_replace_FOv_A in *.
        simpl in *. rem_preds_in_rel. simpl in *.
        apply incl_app_rearr1. rewrite <- Hpreds. rewrite <- Hpreds0.
        apply incl_app_gen; auto.

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

Lemma preprocess_vsSahlq_ante_3_againTRY : forall alpha1 alpha2 lv1 rel1 atm1 lv2 atm2,
  conjSO_exFO_relatSO alpha2 = true ->
  REL rel1 = true ->
  AT atm1 = true ->
  incl (preds_in (conjSO rel1 atm1)) (preds_in alpha1) ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha1 <->
      SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel1 atm1) lv1)) ->
  AT atm2 = true ->
  incl (preds_in atm2) (preds_in alpha2) ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha2 <->
      SOturnst W Iv Ip Ir (list_closed_exFO atm2 lv2)) ->
  conjSO_exFO_relatSO alpha1 = true ->
existsT2 lv : list FOvariable,
  (existsT2 atm : SecOrder,
     (AT atm = true) *
    (existsT rel : SecOrder,
       REL rel = true /\
          incl (preds_in (conjSO rel atm))
                       (preds_in (conjSO alpha1 alpha2)) /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
          SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv)))). 
Proof.
  intros alpha1 alpha2 lv1 rel1 atm1 lv2 atm2
         H HREL1 HAT1 Hin1 H_1 HAT2 Hin2 H_2 H1.
    destruct (same_struc_conjSO_ex _ _ _ (same_struc_replace_FOv_A (conjSO rel1 atm1) 
                                            (replace_FOv_A atm2
                                               (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1))
      as [rel1' [atm1' Heq1]].
     exists (app 
                (replace_FOv_A_list atm2 
                     (list_closed_exFO (conjSO rel1 atm1) lv1) lv2)
(replace_FOv_A_list (conjSO rel1 atm1) 
                  (replace_FOv_A atm2
                     (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1 )).

    exists (conjSO atm1' (replace_FOv_A atm2 (list_closed_exFO (conjSO rel1 atm1) lv1)
         lv2)).
    apply pair.
      pose proof (same_struc_replace_FOv_A atm2 (list_closed_exFO (conjSO rel1 atm1) lv1)
         lv2) as Hsame2.
      pose proof (same_struc_replace_FOv_A (conjSO rel1 atm1)
         (replace_FOv_A atm2
            (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1) as Hsame1.
      rewrite Heq1 in Hsame1.
      apply same_struc_conjSO_r in Hsame1.
      apply same_struc_comm in Hsame1.
      apply same_struc_comm in Hsame2.
      apply same_struc_AT in Hsame2; try assumption.
      apply same_struc_AT in Hsame1; try assumption.
      simpl; rewrite Hsame1; assumption.

    exists rel1'.
    apply conj.
      pose proof (same_struc_replace_FOv_A atm2 (list_closed_exFO (conjSO rel1 atm1) lv1)
         lv2) as Hsame2.
      pose proof (same_struc_replace_FOv_A (conjSO rel1 atm1)
         (replace_FOv_A atm2
            (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1) as Hsame1.
      rewrite Heq1 in Hsame1.
      apply same_struc_conjSO_l in Hsame1.
      apply same_struc_comm in Hsame1.
      apply same_struc_REL in Hsame1; try assumption.

    apply conj.
      simpl.
      assert (preds_in (replace_FOv_A (conjSO rel1 atm1)
                        (replace_FOv_A (atm2)   
                      (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1) =
                       preds_in (conjSO rel1' atm1')) as Hpreds.
        rewrite Heq1. reflexivity.
      simpl. rewrite preds_in_replace_FOv_A in *.
      rewrite app_assoc.
      assert (preds_in (conjSO rel1' atm1') = 
              app (preds_in rel1') (preds_in atm1')) as Hpreds1.
        reflexivity.
     rewrite <- Hpreds1.
     rewrite <- Hpreds. simpl in *. rem_preds_in_rel.
     simpl. apply incl_app_gen; auto.

    intros W Iv Ip Ir.
    split; intros SOt.
      apply (equiv_list_closed_exFO (conjSO rel1' (conjSO atm1' (replace_FOv_A atm2 
              (list_closed_exFO (conjSO rel1 atm1) lv1) lv2)))
                                    (conjSO (conjSO rel1' atm1')
              (replace_FOv_A atm2 (list_closed_exFO (conjSO rel1 atm1) lv1) lv2))).
        apply equiv_conjSO5.
      rewrite <- Heq1.
      rewrite list_closed_exFO_app.
      apply equiv3_3_struc2_both with (alpha := (conjSO rel1 atm1)).
      simpl.
      apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.

      apply (equiv_list_closed_exFO (conjSO rel1' (conjSO atm1' (replace_FOv_A atm2 
              (list_closed_exFO (conjSO rel1 atm1) lv1) lv2)))
                                    (conjSO (conjSO rel1' atm1') (replace_FOv_A atm2 
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

Lemma preprocess_vsSahlq_ante_7_againTRY : forall alpha1 alpha2 lv1 atm1 
                                                  lv2 rel2 atm2,
    conjSO_exFO_relatSO alpha2 = true ->
    AT atm1 = true ->
    incl (preds_in atm1) (preds_in alpha1) ->
    (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
        SOturnst W Iv Ip Ir alpha1 <->
        SOturnst W Iv Ip Ir (list_closed_exFO atm1 lv1)) ->
    REL rel2 = true ->
    AT atm2 = true ->
    incl (preds_in (conjSO rel2 atm2)) (preds_in alpha2) ->
    (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
        SOturnst W Iv Ip Ir alpha2 <->
        SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel2 atm2) lv2)) ->
    conjSO_exFO_relatSO alpha1 = true ->
    existsT2 lv : list FOvariable,
  (existsT2 atm : SecOrder,
                  (AT atm = true) *
                  (existsT rel : SecOrder,
                                 REL rel = true /\
                                 incl (preds_in (conjSO rel atm))
                                      (preds_in (conjSO alpha1 alpha2)) /\
                                 
                                 (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
                                         (Ir : W -> W -> Prop),
                                     SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
                                     SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv)))).
Proof.
  intros alpha1 alpha2 lv1 atm1 lv2 rel2 atm2
        H HAT1 Hin1 H_1 HREL2 HAT2 Hin2 H_2 H1.
    destruct (same_struc_conjSO_ex _ _ _ (same_struc_replace_FOv_A (conjSO rel2 atm2) 
                                            (list_closed_exFO atm1 lv1)
                                             lv2)) as [rel2' [atm2' Heq2]].
     exists (app 
                (replace_FOv_A_list (conjSO rel2 atm2) 
                     (list_closed_exFO atm1 lv1) lv2)
(replace_FOv_A_list  atm1
                  (replace_FOv_A (conjSO rel2 atm2)
                     (list_closed_exFO  atm1 lv1) lv2) lv1 )).

    exists (conjSO (replace_FOv_A atm1 (replace_FOv_A (conjSO rel2 atm2) 
                        (list_closed_exFO atm1 lv1) lv2) lv1) atm2').
    apply pair.
      pose proof (same_struc_replace_FOv_A (conjSO rel2 atm2) (list_closed_exFO atm1 lv1)
         lv2) as Hsame2.
      pose proof (same_struc_replace_FOv_A atm1
         (replace_FOv_A (conjSO rel2 atm2)
            (list_closed_exFO  atm1 lv1) lv2) lv1) as Hsame1.
      rewrite Heq2 in Hsame2.
      apply same_struc_conjSO_r in Hsame2.
      apply same_struc_comm in Hsame2.
      apply same_struc_AT in Hsame2; try assumption.
      apply same_struc_comm in Hsame1.
      apply same_struc_AT in Hsame1; try assumption.
      simpl; rewrite Hsame1; assumption.

    exists rel2'.
    apply conj.
      pose proof (same_struc_replace_FOv_A (conjSO rel2 atm2) (list_closed_exFO atm1 lv1)
         lv2) as Hsame2.
      rewrite Heq2 in Hsame2.
      apply same_struc_conjSO_l in Hsame2.
      apply same_struc_comm in Hsame2.
      apply same_struc_REL in Hsame2; try assumption.

    apply conj.
      simpl.
      assert (preds_in (replace_FOv_A (conjSO rel2 atm2)
                      (list_closed_exFO ( atm1) lv1) lv2) =
                       preds_in (conjSO rel2' atm2')) as Hpreds0.
        rewrite Heq2. reflexivity.
      simpl. rewrite preds_in_replace_FOv_A in *.
      rewrite app_assoc. simpl in *. rem_preds_in_rel.
      apply incl_app_rear2. rewrite <- Hpreds0. apply incl_app_gen; auto.

    intros W Iv Ip Ir.
    split; intros SOt.
      apply (equiv_list_closed_exFO (conjSO  rel2' (conjSO (replace_FOv_A atm1 (replace_FOv_A (conjSO rel2 atm2) 
                        (list_closed_exFO atm1 lv1) lv2) lv1) atm2'))
                                    (conjSO (replace_FOv_A atm1 (replace_FOv_A (conjSO rel2 atm2) 
                        (list_closed_exFO atm1 lv1) lv2) lv1) (conjSO rel2' atm2'))).
        apply equiv_conjSO6.
      rewrite <- Heq2.
      rewrite list_closed_exFO_app.
      apply equiv3_3_struc2_both with (alpha := (atm1)).
      simpl.
      apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.

      apply (equiv_list_closed_exFO (conjSO  rel2' (conjSO (replace_FOv_A atm1 (replace_FOv_A (conjSO rel2 atm2) 
                        (list_closed_exFO atm1 lv1) lv2) lv1) atm2'))
                                    (conjSO (replace_FOv_A atm1 (replace_FOv_A (conjSO rel2 atm2) 
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

Lemma preprocess_vsSahlq_ante_9_againTRY : forall alpha1 alpha2 lv1 atm1 
        lv2 atm2,
  conjSO_exFO_relatSO alpha2 = true ->
  AT atm1 = true ->
  incl (preds_in (atm1)) (preds_in alpha1) ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha1 <->
      SOturnst W Iv Ip Ir (list_closed_exFO  atm1 lv1)) ->
  AT atm2 = true ->
  incl (preds_in (atm2)) (preds_in alpha2) ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha2 <->
      SOturnst W Iv Ip Ir (list_closed_exFO atm2 lv2)) ->
  conjSO_exFO_relatSO alpha1 = true ->
existsT2 lv : list FOvariable,
   (existsT2 atm : SecOrder,
       (AT atm = true) *
          (incl (preds_in (atm))
                       (preds_in (conjSO alpha1 alpha2)) /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
          SOturnst W Iv Ip Ir (list_closed_exFO (atm) lv)))).
Proof.
  intros alpha1 alpha2 lv1 atm1 lv2 atm2
        H HAT1 Hin1 H_1 HAT2 Hin2 H_2 H1.
     exists (app 
                (replace_FOv_A_list atm2
                     (list_closed_exFO atm1 lv1) lv2)
(replace_FOv_A_list atm1
                  (replace_FOv_A atm2
                     (list_closed_exFO atm1 lv1) lv2) lv1 )).

    exists (conjSO (replace_FOv_A atm1 (replace_FOv_A atm2 (list_closed_exFO atm1 lv1) lv2)
              lv1) (replace_FOv_A atm2 (list_closed_exFO atm1 lv1) lv2)
).
    apply pair.
      pose proof (same_struc_replace_FOv_A atm2 (list_closed_exFO atm1 lv1)
         lv2) as Hsame2.
      pose proof (same_struc_replace_FOv_A atm1
         (replace_FOv_A atm2
            (list_closed_exFO atm1 lv1) lv2) lv1) as Hsame1.
      apply same_struc_comm in Hsame2.
      apply same_struc_AT in Hsame2; try assumption.
      apply same_struc_comm in Hsame1.
      apply same_struc_AT in Hsame1; try assumption.
      simpl; rewrite Hsame1. assumption.

    apply conj.
      simpl.
      simpl. do 2  rewrite preds_in_replace_FOv_A in *.
      apply incl_app_gen; auto.

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

Lemma preprocess_vsSahlq_ante_againTRY : forall alpha,
  conjSO_exFO_relatSO alpha = true ->
  (existsT P, Pred_in_SO alpha P) ->
  existsT2 lv atm,
    (AT atm = true) *
    ((existsT rel,
      REL rel = true /\
      incl (preds_in (conjSO rel atm)) (preds_in alpha)  /\
        forall W Iv Ip Ir,
          SOturnst W Iv Ip Ir alpha <->
          SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv)) +
     (incl (preds_in atm) (preds_in alpha) /\
        forall W Iv Ip Ir,
          SOturnst W Iv Ip Ir alpha <->
          SOturnst W Iv Ip Ir (list_closed_exFO atm lv))).
Proof.
  intros alpha H Hocc.
  induction alpha; try (simpl in *; discriminate).
    apply preprocess_vsSahlq_ante_predSO_againTRY; assumption.

    destruct Hocc as [[Pn] Hocc].
    unfold Pred_in_SO in Hocc. destruct f. destruct f0.
    simpl in Hocc. contradiction.

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
      apply Pred_in_SO_conjSO_comp in Hocc.
      destruct Hocc as [Hocc | Hocc]. contradiction (Hocc1 _ Hocc).
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

Lemma hopeful3 : forall lx lP beta alpha rel atm y xn W Iv Ip Ir,
  REL rel = true ->
  AT atm = true ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  ~ att_allFO_var beta (Var xn) ->
  ~ att_exFO_var beta (Var xn) ->
  closed_except beta (Var xn) ->
  var_in_SO (instant_cons_empty' (conjSO rel atm) beta) (Var xn) ->
  incl (preds_in (implSO (conjSO rel atm) beta)) lP ->
  (exists P, Pred_in_SO alpha P) ->
 (forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir alpha <-> SOturnst W Iv Ip Ir (list_closed_allFO (implSO (conjSO rel atm) beta) lx)) ->
  SOturnst W Iv Ip Ir (list_closed_SO alpha lP) ->
  SOturnst W Iv Ip Ir (replace_pred_l (list_closed_allFO (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)  
      (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) beta)) xn))
        (length       (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) beta))))))) lx)
    lP (list_var (length lP) y)
    (vsS_syn_l (FOv_att_P_l (conjSO rel atm) lP) y)).
Proof.
  intros lx lP beta alpha rel atm y xn W Iv Ip Ir HREL HAT Hun Hno Hat1 Hat2
    Hc Hocc Hin Hpocc Hequiv SOt.
  apply vsSahlq_instant_aim1_fwd4_closer2; try assumption.
  pose proof (equiv_list_closed_SO lP  _ _ Hequiv) as H.
  apply H.
  assumption.
Qed.

Lemma hopeful3_atm : forall lx lP beta alpha atm y xn W Iv Ip Ir,
  AT atm = true ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  ~ att_allFO_var beta (Var xn) ->
  ~ att_exFO_var beta (Var xn) ->
  closed_except beta (Var xn) ->
  var_in_SO (instant_cons_empty' atm beta) (Var xn) ->
  incl (preds_in (implSO atm beta)) lP ->
  (exists P, Pred_in_SO alpha P) ->
 (forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir alpha <-> SOturnst W Iv Ip Ir (list_closed_allFO (implSO atm beta) lx)) ->
  SOturnst W Iv Ip Ir (list_closed_SO alpha lP) ->
  SOturnst W Iv Ip Ir (replace_pred_l (list_closed_allFO (implSO
    atm
    (newnew_pre (instant_cons_empty' atm beta)  
      (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta)))
      (rev_seq (S (max (max_FOv (implSO atm beta)) xn))
        (length       (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm beta))))))) lx)
    lP (list_var (length lP) y)
    (vsS_syn_l (FOv_att_P_l atm lP) y)).
Proof.
  intros lx lP beta alpha atm y xn W Iv Ip Ir HAT Hun Hno Hat1 Hat2
    Hc Hocc Hin Hpocc Hequiv SOt.
  apply vsSahlq_instant_aim1_fwd4_closer2_atm; try assumption.
  pose proof (equiv_list_closed_SO lP  _ _ Hequiv) as H.
  apply H.
  assumption.
Qed.

(* -------------------------------------------- *)

Lemma hopeful6 : forall lP1 lP2 alpha beta x,
incl lP1 lP2 ->
FO_frame_condition (replace_pred_l alpha lP1 (list_var (length lP1) x) (vsS_syn_l (FOv_att_P_l beta lP1) x)) = true ->
FO_frame_condition (replace_pred_l alpha lP2 (list_var (length lP2) x) (vsS_syn_l (FOv_att_P_l beta lP2) x)) = true.
Proof.
  induction lP1; intros lP2 alpha beta x Hin Hun.
  + simpl in *. apply rep_pred_l_FO_frame_condition. assumption.
  + simpl in *. if_then_else_hyp_gen.
    destruct (in_dec predicate_dec a lP1) as [HH1 | HH1].
   ++ destruct (nlist_list_ex (length lP1) lP1 eq_refl) as [lP1' Heq1].
      destruct (nlist_list_ex (length lP1) (list_var (length lP1) x)) as [lvar Heq2].
      rewrite list_var_length. reflexivity.
      destruct (nlist_list_ex (length lP1) (vsS_syn_l (FOv_att_P_l beta lP1) x)) as [ldisj_l Heq3].
      rewrite <- length_vsS_syn_l'. rewrite <- length_FOv_att_P_l. reflexivity.
      rewrite <- Heq1 in Hun at 1. rewrite <- Heq2 in Hun at 1. rewrite <- Heq3 in Hun.
      rewrite rep_pred__l_is_in in Hun.
      rewrite Heq1 in Hun. rewrite Heq2 in Hun. rewrite Heq3 in Hun.
      apply IHlP1; try auto. firstorder.

      rewrite Heq1. assumption.
      rewrite Heq3. apply FO_frame_condition_l_vsS_syn_l.
      apply FO_frame_condition_disj_l.

   ++ simpl in Hun. rewrite rep_pred__l_switch in Hun; try auto.
      pose proof (incl_hd _ _ _ _ Hin) as Hin'.
      apply incl_lcons in Hin.
      specialize (IHlP1 _ _ _ _ Hin Hun).
      rewrite <- try2 in IHlP1.

      destruct (nlist_list_ex (length lP2) lP2 eq_refl) as [lP1' Heq1].
      destruct (nlist_list_ex (length lP2) (list_var (length lP2) x)) as [lvar Heq2].
      rewrite list_var_length. reflexivity.
      destruct (nlist_list_ex (length lP2) (vsS_syn_l (FOv_att_P_l beta lP2) x)) as [ldisj_l Heq3].
      rewrite <- length_vsS_syn_l'. rewrite <- length_FOv_att_P_l. reflexivity.
      rewrite <- Heq3 in *. rewrite <- Heq2 in *. rewrite <- Heq1 in *. rewrite <- Heq1 in IHlP1 at 1.

      rewrite rep_pred__l_is_in in IHlP1; try auto. rewrite <- Heq1 at 1. assumption.
      rewrite Heq3. all : try apply FO_frame_condition_l_vsS_syn_l.
      all : try apply FO_frame_condition_disj_l.
Qed.

Lemma FO_frame_condition_corresp : forall xn phi1 phi2 y lx atm rel,
    AT atm = true ->
    REL rel = true ->
    incl (preds_in (conjSO rel atm)) (preds_in (ST phi1 (Var xn))) ->
  FO_frame_condition ((replace_pred_l (list_closed_allFO (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))  
      (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn))))))))) lx)
    (preds_in (ST (mimpl phi1 phi2) (Var xn))) (list_var (length (preds_in (ST (mimpl phi1 phi2) (Var xn)))) y)
    (vsS_syn_l (FOv_att_P_l (conjSO rel atm) (preds_in (ST (mimpl phi1 phi2) (Var xn)))) y))) = true.
Proof.
  intros. pose proof (hopeful2 lx rel atm y xn (ST phi2 (Var xn))) as HH.
  apply hopeful6 with (lP1 := preds_in(list_closed_allFO (implSO (conjSO rel atm) (ST phi2 (Var xn))) lx)).
  rewrite preds_in_list_closed_allFO.
  simpl. simpl in *. apply incl_app_gen; auto.
  apply incl_refl.  auto.
Qed.

Lemma FO_frame_condition_corresp_atm : forall xn phi1 phi2 y lx atm,
    AT atm = true ->
    incl (preds_in atm) (preds_in (ST phi1 (Var xn))) ->
  FO_frame_condition ((replace_pred_l (list_closed_allFO (implSO
    atm
    (newnew_pre (instant_cons_empty' atm (ST phi2 (Var xn)))  
      (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))))
      (rev_seq (S (max (max_FOv (implSO atm (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (Var xn) (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn))))))))) lx)
    (preds_in (ST (mimpl phi1 phi2) (Var xn))) (list_var (length (preds_in (ST (mimpl phi1 phi2) (Var xn)))) y)
    (vsS_syn_l (FOv_att_P_l atm (preds_in (ST (mimpl phi1 phi2) (Var xn)))) y))) = true.
Proof.
  intros.
  pose proof (hopeful2_atm lx atm y xn (ST phi2 (Var xn))) as HH.
  apply hopeful6 with (lP1 := preds_in(list_closed_allFO (implSO atm (ST phi2 (Var xn))) lx)).
  rewrite preds_in_list_closed_allFO.
  simpl. apply incl_app_gen; auto.
  apply incl_refl. auto.
Qed.