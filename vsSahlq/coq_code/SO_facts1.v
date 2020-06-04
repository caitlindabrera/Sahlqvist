Require Export high_mods SO_sem_mods SO_facts_syn.
Require Import Correctness_ST.

Lemma  alt_Ip_rel : forall rel W Iv Ip1 Ip2 Ir,
  REL rel = true ->
  SOturnst W Iv Ip1 Ir rel =
  SOturnst W Iv Ip2 Ir rel.
Proof.
  induction rel; intros W Iv Ip1 Ip2 Ir Hrel; try discriminate.
    reflexivity. 

    simpl. rewrite IHrel1 with (Ip2 := Ip2).
    rewrite IHrel2 with (Ip2 := Ip2).
    reflexivity. apply REL_conjSO_r in Hrel. assumption.
    apply REL_conjSO_l in Hrel. assumption.
Qed.

Lemma P_not_occ_alt : forall (alpha : SecOrder) (P : predicate)
                              (W : Set) (Iv : FOvariable -> W)
                             (Ip : predicate -> W -> Prop)
                             (Ir : W -> W -> Prop)
                              (pa : W -> Prop),
  ~ Pred_in_SO alpha P -> 
    SOturnst W Iv Ip Ir alpha <->
      SOturnst W Iv (alt_Ip Ip pa P) Ir alpha.
Proof.
  induction alpha; intros P W Iv Ip Ir pa HPocc;
    try solve [ simpl; apply iff_refl].
    split; intros SOt.
      simpl in *. destruct (predicate_dec P p) as [H1 | H1].
      subst. firstorder.
      rewrite alt_Ip_neq; auto.

      simpl in *. destruct (predicate_dec P p) as [H1 | H1].
      subst. firstorder.
      rewrite alt_Ip_neq in SOt; auto.

      simpl; split; intros SOt d; apply (IHalpha P _ _ Ip _ pa);
        auto; firstorder.

      simpl; split; intros [d SOt]; exists d; apply (IHalpha P _ _ Ip _ pa);
        auto; firstorder.

      simpl; split; intros H1 H2; (apply H1;
      eapply IHalpha with (Ip := Ip); [apply HPocc|apply H2]).

      simpl. apply Pred_in_SO_conjSO_f in HPocc;
      split; intros [H1 H2];
        (apply conj; [eapply IHalpha1 with (Ip := Ip)|eapply IHalpha2 with (Ip := Ip)];
         try apply HPocc; [apply H1 | apply H2]).

      simpl. apply Pred_in_SO_conjSO_f in HPocc;
      split; (intros [H1 | H2];
      [left; eapply IHalpha1 with (Ip := Ip)| right; eapply IHalpha2 with (Ip := Ip)];
        try apply HPocc; [apply H1 | apply H2]).

      simpl. apply Pred_in_SO_conjSO_f in HPocc.
      split; (intros H1 H2; eapply IHalpha2 with (Ip := Ip); try apply HPocc;
        apply H1; eapply IHalpha1 with (Ip := Ip); [apply HPocc | apply H2 ]).

      simpl. destruct (predicate_dec p P) as [H1 | H1].
      subst. firstorder. 
      split; intros H pa2. rewrite alt_Ip_switch. apply IHalpha.
      intros H2.
      eapply Pred_in_SO_allSO3 in H2. contradiction (HPocc H2).
      auto. apply H. auto. eapply IHalpha with (Ip := (alt_Ip Ip pa2 p)).
      intros H2. eapply Pred_in_SO_allSO3 in H2. contradiction (HPocc H2).
      auto. rewrite alt_Ip_switch. apply H. auto.

      simpl. destruct (predicate_dec p P) as [H1 | H1].
      subst. firstorder. 
      split; intros [pa2 H]; exists pa2.
      rewrite alt_Ip_switch. apply IHalpha. intros H2.
      eapply Pred_in_SO_allSO3 in H2. contradiction (HPocc H2).
      auto. apply H. auto. eapply IHalpha with (Ip := (alt_Ip Ip pa2 p)).
      intros H2. eapply Pred_in_SO_allSO3 in H2. contradiction (HPocc H2).
      auto. rewrite alt_Ip_switch. apply H. auto.
Qed.


(* Towards alt_Iv_equiv *)

Lemma alt_Iv_equiv_allFO : forall alpha f x W Iv Ip Ir d,
(forall (x : FOvariable) (W : Set) (Iv : FOvariable -> W)
            (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop) 
            (d : W),
          free_FO alpha x = false ->
          SOturnst W Iv Ip Ir alpha <->
          SOturnst W (alt_Iv Iv d x) Ip Ir alpha) ->
(free_FO (allFO f alpha) x = false) ->
SOturnst W Iv Ip Ir (allFO f alpha) <->
SOturnst W (alt_Iv Iv d x) Ip Ir (allFO f alpha).
Proof.
  intros alpha f x W Iv Ip Ir d IHalpha Hfree.
  do 2 rewrite SOturnst_allFO.
  simpl in Hfree. destruct (FOvariable_dec x f).
  subst. split; intros H d2.  rewrite alt_Iv_rem; auto.
    erewrite <- alt_Iv_rem. apply H.

    split; intros H d2.
      rewrite alt_Iv_switch. apply IHalpha; auto. auto.

      specialize (H d2).  rewrite <- alt_Iv_switch in H.
      apply IHalpha in H; auto. auto.
Qed.

Lemma alt_Iv_equiv_negSO : forall alpha x W Iv Ip Ir d,
(forall (x : FOvariable) (W : Set) (Iv : FOvariable -> W)
            (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop) 
            (d : W),
          free_FO alpha x = false ->
          SOturnst W Iv Ip Ir alpha <->
          SOturnst W (alt_Iv Iv d x) Ip Ir alpha) ->
(free_FO (negSO alpha) x = false) ->
SOturnst W Iv Ip Ir (negSO alpha) <->
SOturnst W (alt_Iv Iv d x) Ip Ir (negSO alpha).
Proof.
  intros alpha x W Iv Ip Ir d IHalpha Hfree.
  destruct x as [xn].
  do 2 rewrite SOturnst_negSO.
  simpl in Hfree.
  split; intros H1 H2; apply H1.
    apply IHalpha in H2; auto.
    apply IHalpha; auto.
Qed.

Lemma alt_Iv_equiv_exFO : forall alpha f x W Iv Ip Ir d,
(forall (x : FOvariable) (W : Set) (Iv : FOvariable -> W)
            (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop) 
            (d : W),
          free_FO alpha x = false ->
          SOturnst W Iv Ip Ir alpha <->
          SOturnst W (alt_Iv Iv d x) Ip Ir alpha) ->
(free_FO (exFO f alpha) x = false) ->
SOturnst W Iv Ip Ir (exFO f alpha) <->
SOturnst W (alt_Iv Iv d x) Ip Ir (exFO f alpha).
Proof.
  intros alpha f x W Iv Ip Ir d IHalpha Hfree.
  do 2 rewrite SOturnst_exFO.
  simpl in Hfree. destruct (FOvariable_dec x f); subst;
  split; intros [d2 H]; exists d2.
  + rewrite alt_Iv_rem. auto.
  + rewrite alt_Iv_rem in H. auto.
  + rewrite alt_Iv_switch. apply IHalpha; auto. auto.
  + rewrite alt_Iv_switch in H; auto. apply IHalpha in H; auto.
Qed.

Lemma alt_Iv_equiv_conjSO : forall alpha1 alpha2 x W Iv Ip Ir d,
 (forall (x : FOvariable) (W : Set) (Iv : FOvariable -> W)
             (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop) 
             (d : W),
           free_FO alpha1 x = false ->
           SOturnst W Iv Ip Ir alpha1 <->
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha1) ->
  (forall (x : FOvariable) (W : Set) (Iv : FOvariable -> W)
             (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop) 
             (d : W),
           free_FO alpha2 x = false ->
           SOturnst W Iv Ip Ir alpha2 <->
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha2) ->
  free_FO (conjSO alpha1 alpha2) x = false ->
SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
SOturnst W (alt_Iv Iv d x) Ip Ir (conjSO alpha1 alpha2).
Proof.
  intros alpha1 alpha2 x Q Iv Ip Ir d IHalpha1 IHalpha2 Hfree.
  simpl in Hfree.
  do 2 rewrite SOturnst_conjSO.
  case_eq (free_FO alpha1 x); intros Hfree1; rewrite Hfree1 in *.
    discriminate.
  case_eq (free_FO alpha2 x); intros Hfree2; rewrite Hfree2 in *.
    discriminate.
  split; intros H;
  destruct H as [H1 H2];
  apply conj.
    apply IHalpha1; assumption.
    apply IHalpha2; assumption.
    apply IHalpha1 in H1; assumption.
    apply IHalpha2 in H2; assumption.
Qed.


Lemma alt_Iv_equiv_disjSO : forall alpha1 alpha2 x W Iv Ip Ir d,
 (forall (x : FOvariable) (W : Set) (Iv : FOvariable -> W)
             (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop) 
             (d : W),
           free_FO alpha1 x = false ->
           SOturnst W Iv Ip Ir alpha1 <->
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha1) ->
  (forall (x : FOvariable) (W : Set) (Iv : FOvariable -> W)
             (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop) 
             (d : W),
           free_FO alpha2 x = false ->
           SOturnst W Iv Ip Ir alpha2 <->
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha2) ->
  free_FO (disjSO alpha1 alpha2) x = false ->
SOturnst W Iv Ip Ir (disjSO alpha1 alpha2) <->
SOturnst W (alt_Iv Iv d x) Ip Ir (disjSO alpha1 alpha2).
Proof.
  intros alpha1 alpha2 x Q Iv Ip Ir d IHalpha1 IHalpha2 Hfree.
  simpl in Hfree.
  do 2 rewrite SOturnst_disjSO.
  case_eq (free_FO alpha1 x); intros Hfree1; rewrite Hfree1 in *.
    discriminate.
  case_eq (free_FO alpha2 x); intros Hfree2; rewrite Hfree2 in *.
    discriminate.
  split; intros H;
  destruct H as [H1 | H2].
    left; apply IHalpha1; assumption.
    right; apply IHalpha2; assumption.
    left; apply IHalpha1 in H1; assumption.
    right; apply IHalpha2 in H2; assumption.
Qed.

Lemma alt_Iv_equiv_implSO : forall alpha1 alpha2 x W Iv Ip Ir d,
 (forall (x : FOvariable) (W : Set) (Iv : FOvariable -> W)
             (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop) 
             (d : W),
           free_FO alpha1 x = false ->
           SOturnst W Iv Ip Ir alpha1 <->
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha1) ->
  (forall (x : FOvariable) (W : Set) (Iv : FOvariable -> W)
             (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop) 
             (d : W),
           free_FO alpha2 x = false ->
           SOturnst W Iv Ip Ir alpha2 <->
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha2) ->
  free_FO (implSO alpha1 alpha2) x = false ->
SOturnst W Iv Ip Ir (implSO alpha1 alpha2) <->
SOturnst W (alt_Iv Iv d x) Ip Ir (implSO alpha1 alpha2).
Proof.
  intros alpha1 alpha2 x Q Iv Ip Ir d IHalpha1 IHalpha2 Hfree.
  simpl in Hfree.
  do 2 rewrite SOturnst_implSO.
  case_eq (free_FO alpha1 x); intros Hfree1; rewrite Hfree1 in *.
    discriminate.
  case_eq (free_FO alpha2 x); intros Hfree2; rewrite Hfree2 in *.
    discriminate.
  split; intros H1 H2.
    apply IHalpha2; try assumption.
    apply H1.
    apply IHalpha1 in H2; try assumption.

    apply IHalpha2 with (d := d) (x := x); try assumption.
    apply H1.
    apply IHalpha1; try assumption.
Qed.

Lemma alt_Iv_equiv_allSO : forall alpha P x W Iv Ip Ir d,
 (forall (x : FOvariable) (W : Set) (Iv : FOvariable -> W)
             (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop) 
             (d : W),
           free_FO alpha x = false ->
           SOturnst W Iv Ip Ir alpha <->
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha) ->
  free_FO (allSO P alpha) x = false ->
  SOturnst W Iv Ip Ir (allSO P alpha) <->
  SOturnst W (alt_Iv Iv d x) Ip Ir (allSO P alpha).
Proof.
  intros alpha P x Q Iv Ip Ir d IHalpha Hfree.
  simpl in Hfree.
  do 2 rewrite SOturnst_allSO.
  split; intros H pa.
    apply IHalpha; try assumption.
    apply H.

    specialize (H pa).
    apply IHalpha in H; assumption.
Qed.

Lemma alt_Iv_equiv_exSO : forall alpha P x W Iv Ip Ir d,
 (forall (x : FOvariable) (W : Set) (Iv : FOvariable -> W)
             (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop) 
             (d : W),
           free_FO alpha x = false ->
           SOturnst W Iv Ip Ir alpha <->
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha) ->
  free_FO (exSO P alpha) x = false ->
  SOturnst W Iv Ip Ir (exSO P alpha) <->
  SOturnst W (alt_Iv Iv d x) Ip Ir (exSO P alpha).
Proof.
  intros alpha P x Q Iv Ip Ir d IHalpha Hfree.
  simpl in Hfree.
  do 2 rewrite SOturnst_exSO.
  split; intros H .
    destruct H as [pa H].
    exists pa.
    apply IHalpha; assumption.

    destruct H as [pa H].
    exists pa.
    apply IHalpha in H; assumption.
Qed.

Lemma alt_Iv_equiv : forall alpha x W Iv Ip Ir d,
  free_FO alpha x = false ->
  SOturnst W Iv Ip Ir alpha <->
  SOturnst W (alt_Iv Iv d x) Ip Ir alpha.
Proof.
  induction alpha; intros x W Iv Ip Ir d Hfree.
    simpl in *. unfold alt_Iv.
    destruct (FOvariable_dec x f). discriminate.
    firstorder.

    simpl in *. unfold alt_Iv.
    destruct (FOvariable_dec x f). discriminate.
    destruct (FOvariable_dec x f0). discriminate.
    firstorder.

    simpl in *. unfold alt_Iv.
    destruct (FOvariable_dec x f). discriminate.
    destruct (FOvariable_dec x f0). discriminate.
    firstorder.

    apply alt_Iv_equiv_allFO; auto.
    apply alt_Iv_equiv_exFO; auto.
    apply alt_Iv_equiv_negSO; auto.
    apply alt_Iv_equiv_conjSO; auto.
    apply alt_Iv_equiv_disjSO; auto.
    apply alt_Iv_equiv_implSO; auto.
    apply alt_Iv_equiv_allSO; auto.
    apply alt_Iv_equiv_exSO; auto.
Qed.

(* ----------------------------------------------------------- *)

(* Standard SO facts *)

Lemma equiv_conj_ex : forall alpha beta x W Iv Ip Ir,
  free_FO beta x = false ->
  SOturnst W Iv Ip Ir (conjSO (exFO x alpha) beta) <->
  SOturnst W Iv Ip Ir (exFO x (conjSO alpha beta)).
Proof.
  intros alpha beta x W Iv Ip Ir Hfree.
  rewrite SOturnst_conjSO.
  do 2 rewrite SOturnst_exFO.
  split; intros H2.
    destruct H2 as [SO1 SO2].
    destruct SO1 as [d SO1].
    exists d.
    simpl.
    apply conj; try assumption.
    apply alt_Iv_equiv; assumption.

    destruct H2 as [d H2].
    simpl in H2.
    destruct H2 as [SO1 SO2].
    apply conj.
      exists d; assumption.

      apply alt_Iv_equiv in SO2; assumption.
Qed.

Lemma equiv_conj_ex2 : forall alpha beta x W Iv Ip Ir,
  free_FO beta x = false ->
  SOturnst W Iv Ip Ir (conjSO beta (exFO x alpha)) <->
  SOturnst W Iv Ip Ir (exFO x (conjSO beta alpha)).
Proof.
  intros alpha beta x W Iv Ip Ir Hfree.
  rewrite SOturnst_conjSO.
  do 2 rewrite SOturnst_exFO.
  split; intros H2.
    destruct H2 as [SO2 SO1].
    destruct SO1 as [d SO1].
    exists d.
    simpl.
    apply conj; try assumption.
    apply alt_Iv_equiv; assumption.

    destruct H2 as [d H2].
    simpl in H2.
    destruct H2 as [SO2 SO1].
    apply conj.
      apply alt_Iv_equiv in SO2; assumption.

      exists d; assumption.
Qed.

Lemma equiv_impl_ex2 : forall alpha beta x W Iv Ip Ir,
  free_FO beta x = false ->
  SOturnst W Iv Ip Ir (implSO (exFO x alpha) beta) <->
  SOturnst W Iv Ip Ir (allFO x (implSO alpha beta)).
Proof.
  intros alpha beta x W Iv Ip Ir Hfree.
  rewrite SOturnst_implSO.
  rewrite SOturnst_exFO.
  rewrite SOturnst_allFO.
  split; intros H2.
    intros d SOt.
    assert (exists d : W, SOturnst W (alt_Iv Iv d x) Ip Ir alpha) as H3.
      exists d; assumption.
    specialize (H2 H3).
    apply alt_Iv_equiv; assumption.

    intros SOt.
    destruct SOt as [d SOt].
    specialize (H2 d).
    rewrite SOturnst_implSO in H2.
    specialize (H2 SOt).
    apply alt_Iv_equiv in H2; assumption.
Qed.

Lemma equiv_conjSO : forall alpha beta,
  forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir (conjSO alpha beta) <->
    SOturnst W Iv Ip Ir (conjSO beta alpha).
Proof.
  intros alpha beta W Iv Ip Ir.
  do 2 rewrite SOturnst_conjSO.
  split; intros H2;
    (apply conj;
      [apply H2 | apply H2]).
Qed.

Lemma equiv_conjSO2 : forall alpha beta gamma,
  (forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir beta <-> SOturnst W Iv Ip Ir gamma) ->
  forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir (conjSO alpha beta) <->
    SOturnst W Iv Ip Ir (conjSO alpha gamma).
Proof.
  intros alpha beta gamma H W Iv Ip Ir.
  do 2 rewrite SOturnst_conjSO.
  split; intros H2;
    (apply conj;
      [apply H2 | apply H; apply H2]).
Qed.

Lemma equiv_exFO : forall alpha beta,
  (forall W Iv Ip Ir, 
    SOturnst W Iv Ip Ir alpha <-> SOturnst W Iv Ip Ir beta) ->
  forall W Iv Ip Ir x,
    SOturnst W Iv Ip Ir (exFO x alpha) <->
    SOturnst W Iv Ip Ir (exFO x beta).
Proof.
  intros alpha beta H W Iv Ip Ir x.
  do 2 rewrite SOturnst_exFO.
  split; intros H2;
    destruct H2 as [d H2];
    exists d;
    apply H;
    assumption.
Qed.

Lemma equiv_list_closed_exFO : forall alpha beta lv,
  (forall W Iv Ip Ir, 
    SOturnst W Iv Ip Ir alpha <-> SOturnst W Iv Ip Ir beta) ->
  forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir (list_closed_exFO alpha lv) <->
    SOturnst W Iv Ip Ir (list_closed_exFO beta lv).
Proof.
  intros alpha beta lv. 
  induction lv; intros H W Iv Ip Ir.
    simpl; apply H.

    do 2 rewrite list_closed_exFO_cons.
    apply equiv_exFO. intros. apply IHlv.
    apply H.
Qed.

Lemma equiv_conjSO3 : forall alpha1 alpha2 beta1 beta2 W Iv Ip Ir,
  SOturnst W Iv Ip Ir (conjSO (conjSO alpha1 beta1) (conjSO alpha2 beta2)) <->
  SOturnst W Iv Ip Ir (conjSO (conjSO alpha1 alpha2) (conjSO beta1 beta2)).
Proof.
  intros alpha1 alpha2 beta1 beta2 W Iv Ip Ir.
  split; intros [[H1 H2] [H3 H4]]; apply conj;
    apply conj; assumption.
Qed.

Lemma equiv_conjSO4 : forall rel1' rel2 atm1' (W0 : Set) (Iv0 : FOvariable -> W0) (Ip0 : predicate -> W0 -> Prop)
  (Ir0 : W0 -> W0 -> Prop) ,
SOturnst W0 Iv0 Ip0 Ir0 (conjSO (conjSO rel1' rel2) atm1') <->
SOturnst W0 Iv0 Ip0 Ir0 (conjSO (conjSO rel1' atm1') rel2).
Proof.
  intros.
  simpl.
  split; intros [[H1 H2] H3];
   apply conj; try apply conj; assumption.
Qed.

Lemma equiv_conjSO5 : forall alpha beta gamma W Iv Ip Ir,
  SOturnst W Iv Ip Ir (conjSO alpha (conjSO beta gamma)) <->
  SOturnst W Iv Ip Ir (conjSO (conjSO alpha beta) gamma).
Proof.
  intros.
  simpl.
  split; [intros [H1 [H2 H3]] | intros [[H1 H2] H3]];
   apply conj; try apply conj; assumption.
Qed.

Lemma equiv_conjSO6 : forall (alpha beta gamma : SecOrder) (W : Set) 
       (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
       (Ir : W -> W -> Prop),
     SOturnst W Iv Ip Ir (conjSO alpha (conjSO beta gamma)) <->
     SOturnst W Iv Ip Ir (conjSO beta (conjSO alpha gamma)).
Proof.
  intros.
  simpl.
  split; [intros [H1 [H2 H3]] | intros [H1 [H2 H3]]];
   apply conj; try apply conj; assumption.
Qed.

Lemma exFO_rep_FOv_max_FOv_pre_predSO : forall p f,
forall (x : FOvariable) (m : nat),
(max_FOv (predSO p f)) <= m  ->
free_FO (predSO p f) x = false ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop),
SOturnst W Iv Ip Ir (predSO p f) <->
SOturnst W Iv Ip Ir (replace_FOv (predSO p f) x (Var (S m))).
Proof.
  intros p f x m Hleb Hfree W Iv Ip Ir.  simpl in *.
  destruct (FOvariable_dec x f). discriminate.
  simpl. firstorder.
Qed.

Lemma exFO_rep_FOv_max_FOv_pre_relatSO : forall f f0,
forall (x : FOvariable) (m : nat),
(max_FOv (relatSO f f0)) <= m  ->
free_FO (relatSO f f0) x = false ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop),
SOturnst W Iv Ip Ir (relatSO f f0) <->
SOturnst W Iv Ip Ir (replace_FOv (relatSO f f0) x (Var (S m))).
Proof.
  intros f0 f x m Hleb Hfree W Iv Ip Ir.
  simpl in *. destruct (FOvariable_dec x f0). discriminate.
  destruct (FOvariable_dec x f).  discriminate.
  simpl. firstorder.
Qed.

Lemma exFO_rep_FOv_max_FOv_pre_eqFO : forall f f0,
forall (x : FOvariable) (m : nat),
(max_FOv (eqFO f f0)) <= m ->
free_FO (eqFO f f0) x = false ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop),
SOturnst W Iv Ip Ir (eqFO f f0) <->
SOturnst W Iv Ip Ir (replace_FOv (eqFO f f0) x (Var (S m))).
Proof.
  intros f0 f x m Hleb Hfree W Iv Ip Ir.
  simpl in *. destruct (FOvariable_dec x f0). discriminate.
  destruct (FOvariable_dec x f).  discriminate.
  simpl. firstorder.
Qed.

Lemma exFO_rep_FOv_max_FOv_pre_allFO_1_predSO : forall p f ym,
(S (max_FOv (predSO p f))) <= ym ->
forall (x : FOvariable) (W : Set) (Iv : FOvariable -> W)
  (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop) (d : W),
SOturnst W (alt_Iv Iv d x) Ip Ir (predSO p f) <->
SOturnst W (alt_Iv Iv d (Var ym)) Ip Ir (replace_FOv (predSO p f) x (Var ym)).
Proof.
  intros p f ym Hleb x W  Iv Ip Ir d. simpl replace_FOv.
  destruct (FOvariable_dec x f). subst. simpl.
  do 2 rewrite alt_Iv_eq. firstorder.
  unfold max_FOv in *. simpl in *. destruct f.
  do 2 (rewrite alt_Iv_neq; auto). firstorder. 
  apply FOv_not. lia.
Qed.

Lemma exFO_rep_FOv_max_FOv_pre_allFO_1_relatSO : forall f f0,
forall (x : FOvariable) (ym : nat),
(max_FOv (relatSO f f0)) <= ym ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop) (d : W),
SOturnst W (alt_Iv Iv d x) Ip Ir (relatSO f f0) <->
SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
  (replace_FOv (relatSO f f0) x (Var (S ym))).
Proof.
  intros f f0 x ym Hleb W Iv Ip Ir d. simpl in Hleb.
  assert ( Var (S ym) <> f0) as Hass.
    unfold max_FOv in *. simpl in *. dest_FOv_blind. 
    apply FOv_not. lia. 
  assert ( Var (S ym) <> f) as Hass'.
    unfold max_FOv in *. simpl in *. dest_FOv_blind. 
    apply FOv_not. lia. 
  simpl. destruct (FOvariable_dec x f); subst; simpl;
  destruct (FOvariable_dec f f0); subst; simpl;
  repeat (rewrite alt_Iv_eq; auto). apply iff_refl.
  repeat (rewrite alt_Iv_neq; auto). apply iff_refl.
  rewrite FOvariable_dec_r; auto. simpl.
  repeat (rewrite alt_Iv_neq; auto). apply iff_refl.
  destruct (FOvariable_dec x f0); auto. subst. simpl.
  repeat (rewrite alt_Iv_eq; auto).
  repeat (rewrite alt_Iv_neq; auto). apply iff_refl. 
  simpl.
  repeat (rewrite alt_Iv_neq; auto). apply iff_refl. 
Qed. 

Lemma exFO_rep_FOv_max_FOv_pre_allFO_1_eqFO : forall f f0,
forall (x : FOvariable) (ym : nat),
 (max_FOv (eqFO f f0)) <= ym ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop) (d : W),
SOturnst W (alt_Iv Iv d x) Ip Ir (eqFO f f0) <->
SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
  (replace_FOv (eqFO f f0) x (Var (S ym))).
Proof.
  intros f f0 x ym Hleb W Iv Ip Ir d. simpl in Hleb.
  assert ( Var (S ym) <> f0) as Hass.
    unfold max_FOv in *. simpl in *. dest_FOv_blind. 
    apply FOv_not. lia. 
  assert ( Var (S ym) <> f) as Hass'.
    unfold max_FOv in *. simpl in *. dest_FOv_blind. 
    apply FOv_not. lia. 
  unfold max_FOv in *. simpl in *.
  destruct (FOvariable_dec x f); subst; simpl;
  destruct (FOvariable_dec f f0); subst; simpl;
  repeat (rewrite alt_Iv_eq in *; auto). apply iff_refl.
  repeat (rewrite alt_Iv_neq in *; auto). apply iff_refl.
  rewrite FOvariable_dec_r; auto. simpl.
  repeat (rewrite alt_Iv_neq; auto). apply iff_refl.
  destruct (FOvariable_dec x f0); auto. subst. simpl.
  repeat (rewrite alt_Iv_eq in *; auto).
  repeat (rewrite alt_Iv_neq in *; auto). apply iff_refl.
  simpl.
  repeat (rewrite alt_Iv_neq in *; auto). apply iff_refl.
Qed. 

Lemma exFO_rep_FOv_max_FOv_pre_allFO_1_allFO : forall alpha f,
  (forall (x : FOvariable) (ym : nat),
          (max_FOv alpha) <= ym ->
          forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop) (d : W),
          SOturnst W (alt_Iv Iv d x) Ip Ir alpha <->
          SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
            (replace_FOv alpha x (Var (S ym)))) ->
forall (x : FOvariable) (ym : nat),
 (max_FOv (allFO f alpha)) <= ym ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop) (d : W),
SOturnst W (alt_Iv Iv d x) Ip Ir (allFO f alpha) <->
SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
  (replace_FOv (allFO f alpha) x (Var (S ym))).
Proof.
  intros alpha f IHalpha x ym Hleb W Iv Ip Ir d.
  simpl in *. destruct (FOvariable_dec x f). subst.
  simpl. split; intros H d2; rewrite alt_Iv_rem.
  apply IHalpha; auto. destruct f.
  apply PeanoNat.Nat.max_lub_iff in Hleb. firstorder.
  specialize (H d2). rewrite alt_Iv_rem in H. auto.
  specialize (H d2). rewrite alt_Iv_rem in H.
  apply IHalpha in H; auto.  destruct f.
  apply PeanoNat.Nat.max_lub_iff in Hleb. firstorder.

  simpl. split; intros H d2.  rewrite alt_Iv_switch.
  apply IHalpha; auto. destruct f.
  apply PeanoNat.Nat.max_lub_iff in Hleb. firstorder.
  specialize (H d2). rewrite alt_Iv_switch in H. auto. auto.
  destruct f.   apply PeanoNat.Nat.max_lub_iff in Hleb.
  intros HH. inversion HH. firstorder.
  specialize (H d2). rewrite alt_Iv_switch in H.
  apply IHalpha in H; auto. rewrite alt_Iv_switch. auto.
  auto. destruct f.
  apply PeanoNat.Nat.max_lub_iff in Hleb. firstorder.
  intros HH. destruct f. inversion HH.
  apply PeanoNat.Nat.max_lub_iff in Hleb. firstorder.
Qed.

Lemma exFO_rep_FOv_max_FOv_pre_allFO_1_exFO : forall alpha f,
  (forall (x : FOvariable) (ym : nat),
          (max_FOv alpha) <= ym ->
          forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop) (d : W),
          SOturnst W (alt_Iv Iv d x) Ip Ir alpha <->
          SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
            (replace_FOv alpha x (Var (S ym)))) ->
forall (x : FOvariable) (ym : nat),
(max_FOv (exFO f alpha)) <= ym  ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop) (d : W),
SOturnst W (alt_Iv Iv d x) Ip Ir (exFO f alpha) <->
SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
  (replace_FOv (exFO f alpha) x (Var (S ym))).
Proof.
  intros alpha f IHalpha x ym Hleb W Iv Ip Ir d.
  simpl in *. destruct (FOvariable_dec x f); subst;
  simpl; split; intros [d2 H]; exists d2. rewrite alt_Iv_rem.
  apply IHalpha; auto. destruct f.
  apply PeanoNat.Nat.max_lub_iff in Hleb. firstorder.
  rewrite alt_Iv_rem in H. auto. rewrite alt_Iv_rem in H.
  apply IHalpha in H; auto.  rewrite alt_Iv_rem. auto. destruct f.
  apply PeanoNat.Nat.max_lub_iff in Hleb. firstorder.

  rewrite alt_Iv_switch. apply IHalpha; auto. destruct f.
  apply PeanoNat.Nat.max_lub_iff in Hleb. firstorder.
  rewrite alt_Iv_switch in H. auto. auto.
  destruct f.   apply PeanoNat.Nat.max_lub_iff in Hleb.
  intros HH. inversion HH. firstorder.
  rewrite alt_Iv_switch in H.
  apply IHalpha in H; auto. rewrite alt_Iv_switch. auto.
  auto. destruct f.
  apply PeanoNat.Nat.max_lub_iff in Hleb. firstorder.
  intros HH. destruct f. inversion HH.
  apply PeanoNat.Nat.max_lub_iff in Hleb. firstorder.
Qed.

Lemma exFO_rep_FOv_max_FOv_pre_allFO_1_conjSO : forall alpha1 alpha2,
  (forall (x : FOvariable) (ym : nat),
           (max_FOv alpha1) <= ym  ->
           forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
             (Ir : W -> W -> Prop) (d : W),
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha1 <->
           SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
             (replace_FOv alpha1 x (Var (S ym)))) ->
  (forall (x : FOvariable) (ym : nat),
           (max_FOv alpha2) <= ym  ->
           forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
             (Ir : W -> W -> Prop) (d : W),
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha2 <->
           SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
             (replace_FOv alpha2 x (Var (S ym)))) ->
  forall (x : FOvariable) (ym : nat),
    (max_FOv (conjSO alpha1 alpha2)) <= ym  ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop) (d : W),
SOturnst W (alt_Iv Iv d x) Ip Ir (conjSO alpha1 alpha2) <->
SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
  (replace_FOv (conjSO alpha1 alpha2) x (Var (S ym))).
Proof.
  intros alpha1 alpha2 IHalpha1 IHalpha2 x ym Hleb W Iv Ip Ir d.
  simpl in Hleb. rewrite max_FOv_conjSO in Hleb.
  split; intros [SOt1 SOt2];  apply conj.
      apply IHalpha1; auto; lia.
      apply IHalpha2; auto; lia.
      apply IHalpha1 in SOt1; auto; lia. 
      apply IHalpha2 in SOt2; auto; lia. 
Qed.

Lemma exFO_rep_FOv_max_FOv_pre_allFO_1_disjSO : forall alpha1 alpha2,
  (forall (x : FOvariable) (ym : nat),
           (max_FOv alpha1) <= ym ->
           forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
             (Ir : W -> W -> Prop) (d : W),
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha1 <->
           SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
             (replace_FOv alpha1 x (Var (S ym)))) ->
  (forall (x : FOvariable) (ym : nat),
           (max_FOv alpha2) <= ym ->
           forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
             (Ir : W -> W -> Prop) (d : W),
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha2 <->
           SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
             (replace_FOv alpha2 x (Var (S ym)))) ->
  forall (x : FOvariable) (ym : nat),
    (max_FOv (disjSO alpha1 alpha2)) <= ym  ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop) (d : W),
SOturnst W (alt_Iv Iv d x) Ip Ir (disjSO alpha1 alpha2) <->
SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
  (replace_FOv (disjSO alpha1 alpha2) x (Var (S ym))).
Proof.
  intros alpha1 alpha2 IHalpha1 IHalpha2 x ym Hleb W Iv Ip Ir d.
  simpl in Hleb. rewrite max_FOv_disjSO in Hleb.
  split; (intros [SOt1|SOt2]; [left | right]).
      apply IHalpha1; auto; lia.
      apply IHalpha2; auto; lia.
      apply IHalpha1 in SOt1; auto; lia. 
      apply IHalpha2 in SOt2; auto; lia. 
Qed.

Lemma exFO_rep_FOv_max_FOv_pre_allFO_1_implSO : forall alpha1 alpha2,
  (forall (x : FOvariable) (ym : nat),
           (max_FOv alpha1) <= ym ->
           forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
             (Ir : W -> W -> Prop) (d : W),
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha1 <->
           SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
             (replace_FOv alpha1 x (Var (S ym)))) ->
  (forall (x : FOvariable) (ym : nat),
           (max_FOv alpha2) <= ym ->
           forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
             (Ir : W -> W -> Prop) (d : W),
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha2 <->
           SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
             (replace_FOv alpha2 x (Var (S ym)))) ->
forall (x : FOvariable) (ym : nat),
 (max_FOv (implSO alpha1 alpha2)) <= ym ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop) (d : W),
SOturnst W (alt_Iv Iv d x) Ip Ir (implSO alpha1 alpha2) <->
SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
  (replace_FOv (implSO alpha1 alpha2) x (Var (S ym))).
Proof.
  intros alpha1 alpha2 IHalpha1 IHalpha2 x ym Hleb W Iv Ip Ir d.
  simpl in Hleb. rewrite max_FOv_implSO in Hleb.
  split; intros SOt H1.
    apply IHalpha2; auto. lia.
    apply SOt. apply IHalpha1 in H1; auto. lia.

    apply IHalpha2 with (ym := ym); auto. lia.
    apply SOt. apply IHalpha1; auto; lia.
Qed.

Lemma exFO_rep_FOv_max_FOv_pre_allFO_1 : forall alpha x ym,
  (max_FOv alpha) <= ym ->
  forall W Iv Ip Ir d,
  SOturnst W (alt_Iv Iv d x) Ip Ir alpha <->
  SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir (replace_FOv alpha x (Var (S ym))).
Proof.
 induction alpha.
  intros.
  apply exFO_rep_FOv_max_FOv_pre_allFO_1_predSO; auto. simpl in *. apply le_n_S. auto.
  apply exFO_rep_FOv_max_FOv_pre_allFO_1_relatSO; auto.
  apply exFO_rep_FOv_max_FOv_pre_allFO_1_eqFO; assumption.
  apply exFO_rep_FOv_max_FOv_pre_allFO_1_allFO; assumption.
  apply exFO_rep_FOv_max_FOv_pre_allFO_1_exFO; assumption.

  intros x ym Hleb W Iv Ip Ir d.
  simpl in Hleb. simpl. split; intros H1 H2. apply H1.
  apply IHalpha in H2; auto.
  apply H1. apply IHalpha; auto.
 
  apply exFO_rep_FOv_max_FOv_pre_allFO_1_conjSO; assumption.
  apply exFO_rep_FOv_max_FOv_pre_allFO_1_disjSO; assumption.
  apply exFO_rep_FOv_max_FOv_pre_allFO_1_implSO; assumption.

  intros x ym Hleb W Iv Ip Ir d.
  destruct x; destruct p. simpl in *.
  split; intros H pa. apply IHalpha; auto.
  specialize (H pa). apply IHalpha in H; auto.

  intros x ym Hleb W Iv Ip Ir d.
  destruct x; destruct p. simpl in *.
  split; intros [pa H]; exists pa. apply IHalpha; auto.
  apply IHalpha in H; auto.
Qed.

Lemma exFO_rep_FOv_max_FOv_pre_allFO : forall alpha f,
  (forall (x : FOvariable) (m : nat),
          (max_FOv alpha) <= m  ->
          free_FO alpha x = false ->
          forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir alpha <->
          SOturnst W Iv Ip Ir (replace_FOv alpha x (Var (S m)))) ->
forall (x : FOvariable) (m : nat),
(max_FOv (allFO f alpha)) <= m ->
free_FO (allFO f alpha) x = false ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop),
SOturnst W Iv Ip Ir (allFO f alpha) <->
SOturnst W Iv Ip Ir (replace_FOv (allFO f alpha) x (Var (S m))).
Proof.
  intros alpha f IHalpha x m Hleb Hfree W Iv Ip Ir. simpl in *.
  destruct (FOvariable_dec x f); simpl;
  subst; destruct f as [ym]; rewrite max_FOv_allFO in Hleb;
  split; intros SOt d. 
  - specialize (IHalpha (Var ym) m).
    apply exFO_rep_FOv_max_FOv_pre_allFO_1; auto. lia.
  - specialize (SOt d).
    apply exFO_rep_FOv_max_FOv_pre_allFO_1 in SOt; auto. lia.
  - apply IHalpha; auto. lia.
  - specialize (SOt d). apply IHalpha in SOt; auto. lia.
Qed.

Lemma exFO_rep_FOv_max_FOv_pre_exFO_1_predSO : forall p f ym,
 (S (max_FOv (predSO p f))) <= ym ->
forall (x : FOvariable) (W : Set) (Iv : FOvariable -> W)
  (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop) (d : W),
SOturnst W (alt_Iv Iv d x) Ip Ir (predSO p f) <->
SOturnst W (alt_Iv Iv d (Var ym)) Ip Ir (replace_FOv (predSO p f) x (Var ym)).
Proof.
  intros p f ym Hleb x W  Iv Ip Ir d. simpl.
  destruct (FOvariable_dec x f); subst; simpl.
  do 2 rewrite alt_Iv_eq. firstorder.

  simpl. rewrite alt_Iv_neq; auto.
  rewrite alt_Iv_neq; auto. firstorder.
  simpl in *. destruct f. intros H; inversion H.
  subst. rewrite max_FOv_predSO in Hleb. simpl in *. lia. 
Qed.

Lemma exFO_rep_FOv_max_FOv_pre_exFO_1_relatSO : forall f f0,
forall (x : FOvariable) (ym : nat),
(max_FOv (relatSO f f0)) <= ym ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop) (d : W),
SOturnst W (alt_Iv Iv d x) Ip Ir (relatSO f f0) <->
SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
  (replace_FOv (relatSO f f0) x (Var (S ym))).
Proof.
  intros f f0 x ym Hleb W Iv Ip Ir d.
  assert (Var (S ym) <> f0) as Hass1.
    destruct f0. apply FOv_not.
    rewrite max_FOv_relatSO in Hleb. simpl in *. lia.
  assert (Var (S ym) <> f) as Hass2.
    destruct f. apply FOv_not.
    rewrite max_FOv_relatSO in Hleb. simpl in *. lia.
  simpl in *. destruct (FOvariable_dec x f);
  destruct (FOvariable_dec x f0); subst.
  -  simpl. repeat (rewrite alt_Iv_eq; auto). firstorder.
  -  rewrite alt_Iv_eq; auto. rewrite alt_Iv_neq; auto.
     simpl. rewrite alt_Iv_eq; auto. rewrite alt_Iv_neq; auto.
     firstorder.
  - rewrite alt_Iv_neq; auto. rewrite alt_Iv_eq; auto. simpl.
    rewrite alt_Iv_neq; auto. rewrite alt_Iv_eq; auto. firstorder.
  - repeat (rewrite alt_Iv_neq; auto; simpl). firstorder.
Qed.

Lemma exFO_rep_FOv_max_FOv_pre_exFO_1_eqFO : forall f f0,
forall (x : FOvariable) (ym : nat),
(max_FOv (eqFO f f0)) <= ym ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop) (d : W),
SOturnst W (alt_Iv Iv d x) Ip Ir (eqFO f f0) <->
SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
  (replace_FOv (eqFO f f0) x (Var (S ym))).
Proof.
  intros f f0 x ym Hleb W Iv Ip Ir d.  simpl in *.
  assert (Var (S ym) <> f0) as Hass1.
    destruct f0. apply FOv_not.
    rewrite max_FOv_eqFO in Hleb. simpl in *. lia.
  assert (Var (S ym) <> f) as Hass2.
    destruct f. apply FOv_not.
    rewrite max_FOv_eqFO in Hleb. simpl in *. lia.
  simpl in *. destruct (FOvariable_dec x f);
  destruct (FOvariable_dec x f0); subst.
  -  simpl. repeat (rewrite alt_Iv_eq; auto). firstorder.
  -  rewrite alt_Iv_eq; auto. rewrite alt_Iv_neq; auto.
     simpl. rewrite alt_Iv_eq; auto. rewrite alt_Iv_neq; auto.
     firstorder.
  - rewrite alt_Iv_neq; auto. rewrite alt_Iv_eq; auto. simpl.
    rewrite alt_Iv_neq; auto. rewrite alt_Iv_eq; auto. firstorder.
  - repeat (rewrite alt_Iv_neq; auto; simpl). firstorder.
Qed.

Lemma exFO_rep_FOv_max_FOv_pre_exFO_1_allFO : forall alpha f,
  (forall (x : FOvariable) (ym : nat),
          (max_FOv alpha) <= ym  ->
          forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop) (d : W),
          SOturnst W (alt_Iv Iv d x) Ip Ir alpha <->
          SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
            (replace_FOv alpha x (Var (S ym)))) ->
forall (x : FOvariable) (ym : nat),
(max_FOv (allFO f alpha)) <= ym  ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop) (d : W),
SOturnst W (alt_Iv Iv d x) Ip Ir (allFO f alpha) <->
SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
  (replace_FOv (allFO f alpha) x (Var (S ym))).
Proof.
  intros alpha f IHalpha x ym Hleb W Iv Ip Ir d. simpl in *.
  assert (max_FOv alpha <= ym /\  Var (S ym) <> f) as Hass.
    destruct f. rewrite max_FOv_allFO in Hleb. simpl in *. 
    apply conj. lia. apply FOv_not. lia.
  destruct Hass as [Hass1 Hass2].
  destruct (FOvariable_dec x f); simpl; subst.
  - split; intros SOt d2; rewrite alt_Iv_rem; specialize (SOt d2);
    rewrite alt_Iv_rem in SOt. apply IHalpha; auto.
    apply IHalpha in SOt; auto.
  - split; intros SOt d2;  rewrite alt_Iv_switch; auto.
    apply IHalpha; auto. rewrite alt_Iv_switch; auto.
    specialize (SOt d2). rewrite alt_Iv_switch in SOt; auto.
    apply IHalpha in SOt; auto.
Qed.

Lemma exFO_rep_FOv_max_FOv_pre_exFO_1_exFO : forall alpha f,
  (forall (x : FOvariable) (ym : nat),
          (max_FOv alpha) <= ym ->
          forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop) (d : W),
          SOturnst W (alt_Iv Iv d x) Ip Ir alpha <->
          SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
            (replace_FOv alpha x (Var (S ym)))) ->
forall (x : FOvariable) (ym : nat),
 (max_FOv (exFO f alpha)) <= ym ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop) (d : W),
SOturnst W (alt_Iv Iv d x) Ip Ir (exFO f alpha) <->
SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
  (replace_FOv (exFO f alpha) x (Var (S ym))).
Proof.
  intros alpha f IHalpha x ym Hleb W Iv Ip Ir d. simpl in *.
  assert (max_FOv alpha <= ym /\  Var (S ym) <> f) as Hass.
    destruct f. rewrite max_FOv_exFO in Hleb. simpl in *. 
    apply conj. lia. apply FOv_not. lia.
  destruct Hass as [Hass1 Hass2].
  destruct (FOvariable_dec x f); simpl; subst.
  - split; intros [d2 SOt]; exists d2; rewrite alt_Iv_rem; 
    rewrite alt_Iv_rem in SOt. apply IHalpha; auto.
    apply IHalpha in SOt; auto.
  - split; intros [d2 SOt]; exists d2; rewrite alt_Iv_switch; auto.
    apply IHalpha; auto. rewrite alt_Iv_switch; auto.
    rewrite alt_Iv_switch in SOt; auto.
    apply IHalpha in SOt; auto.
Qed.

Lemma exFO_rep_FOv_max_FOv_pre_exFO_1_conjSO : forall alpha1 alpha2,
  (forall (x : FOvariable) (ym : nat),
           (max_FOv alpha1) <= ym ->
           forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
             (Ir : W -> W -> Prop) (d : W),
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha1 <->
           SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
             (replace_FOv alpha1 x (Var (S ym)))) ->
  (forall (x : FOvariable) (ym : nat),
           (max_FOv alpha2) <= ym ->
           forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
             (Ir : W -> W -> Prop) (d : W),
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha2 <->
           SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
             (replace_FOv alpha2 x (Var (S ym)))) ->
forall (x : FOvariable) (ym : nat),
 (max_FOv (conjSO alpha1 alpha2)) <= ym ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop) (d : W),
SOturnst W (alt_Iv Iv d x) Ip Ir (conjSO alpha1 alpha2) <->
SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
  (replace_FOv (conjSO alpha1 alpha2) x (Var (S ym))).
Proof.
  intros alpha1 alpha2 IHalpha1 IHalpha2 x ym Hleb W Iv Ip Ir d.
  simpl in Hleb. rewrite max_FOv_conjSO in Hleb.
  simpl. split; intros [SOt1 SOt2]; apply conj.
  - apply IHalpha1; auto. lia.
  - apply IHalpha2; auto. lia.
  - apply IHalpha1 in SOt1; auto. lia.
  -  apply IHalpha2 in SOt2; auto. lia.
Qed.

Lemma exFO_rep_FOv_max_FOv_pre_exFO_1_disjSO : forall alpha1 alpha2,
  (forall (x : FOvariable) (ym : nat),
            (max_FOv alpha1) <= ym ->
           forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
             (Ir : W -> W -> Prop) (d : W),
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha1 <->
           SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
             (replace_FOv alpha1 x (Var (S ym)))) ->

  (forall (x : FOvariable) (ym : nat),
           (max_FOv alpha2) <= ym ->
           forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
             (Ir : W -> W -> Prop) (d : W),
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha2 <->
           SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
             (replace_FOv alpha2 x (Var (S ym)))) ->
forall (x : FOvariable) (ym : nat),
(max_FOv (disjSO alpha1 alpha2)) <= ym ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop) (d : W),
SOturnst W (alt_Iv Iv d x) Ip Ir (disjSO alpha1 alpha2) <->
SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
  (replace_FOv (disjSO alpha1 alpha2) x (Var (S ym))).
Proof.
  intros alpha1 alpha2 IHalpha1 IHalpha2 x ym Hleb W Iv Ip Ir d.
  simpl in Hleb. rewrite max_FOv_disjSO in Hleb.
  simpl. split; (intros [SOt1 | SOt2]; [left | right]).
  - apply IHalpha1; auto. lia.
  - apply IHalpha2; auto. lia.
  - apply IHalpha1 in SOt1; auto. lia.
  -  apply IHalpha2 in SOt2; auto. lia.
Qed.

Lemma exFO_rep_FOv_max_FOv_pre_exFO_1_implSO : forall alpha1 alpha2,
  (forall (x : FOvariable) (ym : nat),
           (max_FOv alpha1) <= ym ->
           forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
             (Ir : W -> W -> Prop) (d : W),
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha1 <->
           SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
             (replace_FOv alpha1 x (Var (S ym)))) ->
  (forall (x : FOvariable) (ym : nat),
           (max_FOv alpha2) <= ym ->
           forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
             (Ir : W -> W -> Prop) (d : W),
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha2 <->
           SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
             (replace_FOv alpha2 x (Var (S ym)))) ->
forall (x : FOvariable) (ym : nat),
 (max_FOv (implSO alpha1 alpha2)) <= ym ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop) (d : W),
SOturnst W (alt_Iv Iv d x) Ip Ir (implSO alpha1 alpha2) <->
SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
  (replace_FOv (implSO alpha1 alpha2) x (Var (S ym))).
Proof.
  intros alpha1 alpha2 IHalpha1 IHalpha2 x ym Hleb W Iv Ip Ir d.
  simpl in Hleb. rewrite max_FOv_implSO in Hleb.
  simpl. split; intros SOt1 SOt2.
  - apply IHalpha2; auto. lia.
    apply SOt1. apply IHalpha1 in SOt2; auto. lia.
  - eapply IHalpha2. 2 : apply SOt1. lia.
    apply IHalpha1; auto. lia.
Qed.

Lemma exFO_rep_FOv_max_FOv_pre_exFO_1 : forall alpha x ym,
  (max_FOv alpha) <= ym ->
  forall W Iv Ip Ir d,
  SOturnst W (alt_Iv Iv d x) Ip Ir alpha <->
  SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir (replace_FOv alpha x (Var (S ym))).
Proof.
 induction alpha.
  intros.
  apply exFO_rep_FOv_max_FOv_pre_exFO_1_predSO; auto. lia.
  apply exFO_rep_FOv_max_FOv_pre_exFO_1_relatSO; assumption.
  apply exFO_rep_FOv_max_FOv_pre_exFO_1_eqFO; assumption.
  apply exFO_rep_FOv_max_FOv_pre_exFO_1_allFO; assumption.
  apply exFO_rep_FOv_max_FOv_pre_exFO_1_exFO; assumption.

  intros x ym Hleb W Iv Ip Ir d. simpl in *.
  split; intros H1 H2;  apply H1.
    apply IHalpha in H2; auto.
    apply IHalpha; auto.

  apply exFO_rep_FOv_max_FOv_pre_exFO_1_conjSO; assumption.
  apply exFO_rep_FOv_max_FOv_pre_exFO_1_disjSO; assumption.
  apply exFO_rep_FOv_max_FOv_pre_exFO_1_implSO; assumption.

  intros x ym Hleb W Iv Ip Ir d. simpl in *.
  split; intros SOt pa; specialize (SOt pa).
    apply IHalpha; auto. apply IHalpha in SOt; auto.

  intros x ym Hleb W Iv Ip Ir d. simpl in *.
  split; intros [pa SOt]; exists pa.
    apply IHalpha; auto. apply IHalpha in SOt; auto.
Qed.

Lemma exFO_rep_FOv_max_FOv_pre_exFO : forall alpha f,
  (forall (x : FOvariable) (m : nat),
          (max_FOv alpha) <= m ->
          free_FO alpha x = false ->
          forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir alpha <->
          SOturnst W Iv Ip Ir (replace_FOv alpha x (Var (S m)))) ->
forall (x : FOvariable) (m : nat),
 (max_FOv (exFO f alpha)) <= m  ->
free_FO (exFO f alpha) x = false ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop),
SOturnst W Iv Ip Ir (exFO f alpha) <->
SOturnst W Iv Ip Ir (replace_FOv (exFO f alpha) x (Var (S m))).
Proof.
  intros alpha f IHalpha x m Hleb Hfree W Iv Ip Ir.
  assert ( max_FOv alpha <= m) as Hass.
    rewrite max_FOv_exFO in Hleb. lia.
  simpl in *. destruct (FOvariable_dec x f); subst; simpl in *;
  split ;intros [d SOt]; exists d.
  - apply exFO_rep_FOv_max_FOv_pre_exFO_1;  auto.
  - apply exFO_rep_FOv_max_FOv_pre_exFO_1 in SOt; auto.
  - apply IHalpha; auto.
  - apply IHalpha in SOt; auto.
Qed.

Lemma exFO_rep_FOv_max_FOv_pre_conjSO : forall alpha1 alpha2,
  (forall (x : FOvariable) (m : nat),
            (max_FOv alpha1) <= m ->
           free_FO alpha1 x = false ->
           forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
             (Ir : W -> W -> Prop),
           SOturnst W Iv Ip Ir alpha1 <->
           SOturnst W Iv Ip Ir (replace_FOv alpha1 x (Var (S m)))) ->
  (forall (x : FOvariable) (m : nat),
            (max_FOv alpha2) <= m ->
           free_FO alpha2 x = false ->
           forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
             (Ir : W -> W -> Prop),
           SOturnst W Iv Ip Ir alpha2 <->
           SOturnst W Iv Ip Ir (replace_FOv alpha2 x (Var (S m)))) ->
forall (x : FOvariable) (m : nat),
 (max_FOv (conjSO alpha1 alpha2)) <= m ->
free_FO (conjSO alpha1 alpha2) x = false ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop),
SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
SOturnst W Iv Ip Ir (replace_FOv (conjSO alpha1 alpha2) x (Var (S m))).
Proof.
  intros alpha1 alpha2 IHalpha1 IHalpha2 x m Hleb Hfree W Iv Ip Ir.
  simpl in *. apply Bool.orb_false_elim in Hfree.
  rewrite max_FOv_conjSO in Hleb.
  split; intros [H1 H2]; apply conj.
  - apply IHalpha1; auto; firstorder; lia.
  - apply IHalpha2; auto; firstorder; lia.
  - apply IHalpha1 in H1; auto; firstorder; lia.
  - apply IHalpha2 in H2; auto; firstorder; lia.
Qed.  

Lemma exFO_rep_FOv_max_FOv_pre_disjSO : forall alpha1 alpha2,
  (forall (x : FOvariable) (m : nat),
            (max_FOv alpha1) <= m ->
           free_FO alpha1 x = false ->
           forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
             (Ir : W -> W -> Prop),
           SOturnst W Iv Ip Ir alpha1 <->
           SOturnst W Iv Ip Ir (replace_FOv alpha1 x (Var (S m)))) ->
  (forall (x : FOvariable) (m : nat),
           (max_FOv alpha2) <= m ->
           free_FO alpha2 x = false ->
           forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
             (Ir : W -> W -> Prop),
           SOturnst W Iv Ip Ir alpha2 <->
           SOturnst W Iv Ip Ir (replace_FOv alpha2 x (Var (S m)))) ->
forall (x : FOvariable) (m : nat),
(max_FOv (disjSO alpha1 alpha2))<=  m ->
free_FO (disjSO alpha1 alpha2) x = false ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop),
SOturnst W Iv Ip Ir (disjSO alpha1 alpha2) <->
SOturnst W Iv Ip Ir (replace_FOv (disjSO alpha1 alpha2) x (Var (S m))).
Proof.
  intros alpha1 alpha2 IHalpha1 IHalpha2 x m Hleb Hfree W Iv Ip Ir.
  simpl in *.  apply Bool.orb_false_iff in Hfree. destruct Hfree as [Hf1 Hf2].
  rewrite max_FOv_disjSO in Hleb.
  split; (intros [H1 | H2]; [left | right]).
  - apply IHalpha1; auto. lia.
  - apply IHalpha2; auto. lia.
  - apply IHalpha1 in H1; auto. lia.
  - apply IHalpha2 in H2; auto. lia.
Qed.  

Lemma exFO_rep_FOv_max_FOv_pre_implSO : forall alpha1 alpha2,
  (forall (x : FOvariable) (m : nat),
            (max_FOv alpha1) <= m ->
           free_FO alpha1 x = false ->
           forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
             (Ir : W -> W -> Prop),
           SOturnst W Iv Ip Ir alpha1 <->
           SOturnst W Iv Ip Ir (replace_FOv alpha1 x (Var (S m)))) ->
  (forall (x : FOvariable) (m : nat),
           (max_FOv alpha2) <= m  ->
           free_FO alpha2 x = false ->
           forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
             (Ir : W -> W -> Prop),
           SOturnst W Iv Ip Ir alpha2 <->
           SOturnst W Iv Ip Ir (replace_FOv alpha2 x (Var (S m)))) ->
forall (x : FOvariable) (m : nat),
 (max_FOv (implSO alpha1 alpha2))<= m ->
free_FO (implSO alpha1 alpha2) x = false ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop),
SOturnst W Iv Ip Ir (implSO alpha1 alpha2) <->
SOturnst W Iv Ip Ir (replace_FOv (implSO alpha1 alpha2) x (Var (S m))).
Proof.
  intros alpha1 alpha2 IHalpha1 IHalpha2 x m Hleb Hfree W Iv Ip Ir.
  simpl in *.  apply Bool.orb_false_iff in Hfree. destruct Hfree as [Hf1 Hf2].
  rewrite max_FOv_implSO in Hleb.
  split; intros H1 H2. 
  -  apply IHalpha2; auto. lia. apply H1. apply IHalpha1 in H2; auto. lia.
  - eapply IHalpha2. 3 : apply H1. lia. auto. apply IHalpha1; auto; lia. 
Qed.

Lemma exFO_rep_FOv_max_FOv_pre : forall alpha x m,
  (max_FOv alpha) <= m ->
  free_FO alpha x = false ->
  forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir alpha <->
  SOturnst W Iv Ip Ir (replace_FOv alpha x (Var (S m))).
Proof.
  induction alpha.
    apply exFO_rep_FOv_max_FOv_pre_predSO.
    apply exFO_rep_FOv_max_FOv_pre_relatSO.
    apply exFO_rep_FOv_max_FOv_pre_eqFO.
    apply exFO_rep_FOv_max_FOv_pre_allFO; assumption.
    apply exFO_rep_FOv_max_FOv_pre_exFO; assumption.

    intros x m Hleb Hfree W Iv Ip Ir. simpl in *.
    split; intros H1 H2; apply H1. 
      apply IHalpha in H2; assumption.
      apply IHalpha; assumption.

    apply exFO_rep_FOv_max_FOv_pre_conjSO; assumption.
    apply exFO_rep_FOv_max_FOv_pre_disjSO; assumption.
    apply exFO_rep_FOv_max_FOv_pre_implSO; assumption.

    intros x m Hleb Hfree W Iv Ip Ir. simpl in *.
    split; intros SOt pa. apply IHalpha; auto.
    specialize (SOt pa). apply IHalpha in SOt; auto.

    intros x m Hleb Hfree W Iv Ip Ir. simpl in *.
    split; intros [pa SOt]; exists pa. apply IHalpha; auto.
    apply IHalpha in SOt; auto.
Qed.

Lemma exFO_rep_FOv_max_FOv : forall alpha n m,
  (max_FOv (exFO (Var n) alpha)) <= m ->
  forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (exFO (Var n) alpha) <->
  SOturnst W Iv Ip Ir (exFO (Var (S m)) (replace_FOv alpha (Var n) (Var (S m)))).
Proof.
  intros alpha n m Hleb W Iv Ip Ir. 
  assert ((exFO (Var (S m)) (replace_FOv alpha (Var n) (Var (S m)))) =
          replace_FOv (exFO (Var n) alpha) (Var n) (Var (S m))) as Hass.
    simpl. rewrite FOvariable_dec_l; auto.
  rewrite Hass. remember (Var n) as t. split; intros HH.
  apply exFO_rep_FOv_max_FOv_pre; auto. simpl.
  rewrite FOvariable_dec_l; auto.
  apply exFO_rep_FOv_max_FOv_pre in HH; auto.
  simpl. rewrite FOvariable_dec_l; auto. 
Qed.

Lemma impl_list_closed_exFO : forall alpha lv W Iv Ip Ir,
  SOturnst W Iv Ip Ir alpha ->
  SOturnst W Iv Ip Ir (list_closed_exFO alpha lv).
Proof.
  intros alpha lv.
  induction lv; intros W Iv Ip Ir H.
    simpl; assumption.

    simpl list_closed_exFO.
    rewrite SOturnst_exFO.
    exists (Iv a).
    rewrite unalt_fun_Iv.
    apply IHlv.
    assumption.
Qed.

Lemma list_closed_SO_pa_choose : forall l beta W Iv Ip Ir,
(forall pa_l : nlist_pa W (length l),
     SOturnst W Iv
       (alt_Ip_list Ip
          (nlist_list_pa W (length l) pa_l) l) Ir beta) ->
SOturnst W Iv Ip Ir beta.
Proof. 
  induction l; intros beta W Iv Ip Ir H.
    specialize (H (niln_pa W)).
    simpl in *.
    assumption.

    simpl in *.
    apply IHl.
    intros pa_l.
    specialize (H (consn_pa _ _ ((alt_Ip_list Ip (nlist_list_pa W (length l) pa_l) l) a) pa_l) ).
    simpl in H.
    rewrite unalt_fun in H. 
    assumption.
Qed.

Lemma equiv_list_closed_SO_allFO : forall l alpha x W Iv Ip Ir,
  SOturnst W Iv Ip Ir (list_closed_SO (allFO x alpha) l) <->
  SOturnst W Iv Ip Ir (allFO x (list_closed_SO alpha l)).
Proof.
  intros l alpha [xn] W Iv Ip Ir.
  split; intros SOt.
    intros d.
    apply nlist_list_closed_SO.
    intros pa_l.
    destruct (nlist_list_closed_SO W Iv Ir (allFO (Var xn) alpha) l Ip) as [fwd rev].
    apply fwd.
    assumption.

    apply nlist_list_closed_SO.
    intros pa_l d.
    destruct (nlist_list_closed_SO W (alt_Iv Iv d (Var xn)) Ir alpha l Ip) as [fwd rev].
    apply fwd.
    apply SOt.
Qed.

Lemma equiv_uni_closed_SO_allFO : forall alpha x W Iv Ip Ir,
  SOturnst W Iv Ip Ir (uni_closed_SO (allFO x alpha)) <->
  SOturnst W Iv Ip Ir (allFO x (uni_closed_SO alpha)).
Proof.
  intros. unfold uni_closed_SO.
  apply equiv_list_closed_SO_allFO.
Qed.

Lemma equiv_list_closed_SO_list_closed_allFO : forall lv lP alpha W Iv Ip Ir,
  SOturnst W Iv Ip Ir (list_closed_SO (list_closed_allFO alpha lv) lP) <->
  SOturnst W Iv Ip Ir (list_closed_allFO (list_closed_SO alpha lP) lv).
Proof.
  induction lv; intros lP alpha W Iv Ip Ir.
    simpl. apply iff_refl.

    destruct a as [xn].
    simpl list_closed_allFO.
    split; intros SOt.
      apply equiv_list_closed_SO_allFO in SOt.
      intros d. apply IHlv. apply SOt.

      apply equiv_list_closed_SO_allFO.
      intros d. apply IHlv. apply SOt.
Qed.

Lemma equiv_uni_closed_SO_list_closed_allFO : forall lv alpha W Iv Ip Ir,
  SOturnst W Iv Ip Ir (uni_closed_SO (list_closed_allFO alpha lv)) <->
  SOturnst W Iv Ip Ir (list_closed_allFO (uni_closed_SO alpha) lv).
Proof.
  intros. unfold uni_closed_SO.
  rewrite preds_in_list_closed_allFO.
  apply equiv_list_closed_SO_list_closed_allFO.
Qed.

Lemma equiv_allFO : forall alpha beta,
  (forall W Iv Ip Ir, 
    SOturnst W Iv Ip Ir alpha <-> SOturnst W Iv Ip Ir beta) ->
  forall W Iv Ip Ir x,
    SOturnst W Iv Ip Ir (allFO x alpha) <->
    SOturnst W Iv Ip Ir (allFO x beta).
Proof.
  intros alpha beta H W Iv Ip Ir x.
  do 2 rewrite SOturnst_allFO.
  split; intros H2;
    intros d; apply H; apply H2.
Qed.

Lemma equiv_list_closed_allFO : forall alpha beta lv,
  (forall W Iv Ip Ir, 
    SOturnst W Iv Ip Ir alpha <-> SOturnst W Iv Ip Ir beta) ->
  forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir (list_closed_allFO alpha lv) <->
    SOturnst W Iv Ip Ir (list_closed_allFO beta lv).
Proof.
  intros alpha beta lv. 
  induction lv; intros H W Iv Ip Ir.
    simpl; apply H.

    do 2 rewrite list_closed_allFO_cons.
    apply equiv_allFO. intros. apply IHlv.
    apply H.
Qed.

Lemma list_closed_SO_impl : forall l alpha W Iv Ip Ir,
  SOturnst W Iv Ip Ir (list_closed_SO alpha l) ->
  SOturnst W Iv Ip Ir alpha.
Proof.
  induction l; intros alpha W Iv Ip Ir SOt.
    simpl in *.
    assumption.

    destruct a as [Qm]. simpl list_closed_SO in SOt.
    rewrite SOturnst_allSO in SOt.
    specialize (SOt (Ip (Pred Qm))).
    rewrite unalt_fun in SOt.
    apply IHl; assumption.
Qed.

Lemma uni_closed_SO_impl : forall alpha W Iv Ip Ir,
  SOturnst W Iv Ip Ir (uni_closed_SO alpha) ->
  SOturnst W Iv Ip Ir alpha.
Proof.
  intros. unfold uni_closed_SO in *.
  apply list_closed_SO_impl in H; assumption.
Qed.

Lemma uni__list_closed_SO : forall l alpha W Iv Ip Ir,
  SOturnst W Iv Ip Ir (uni_closed_SO alpha) ->
  SOturnst W Iv Ip Ir (list_closed_SO alpha l).
Proof.
  induction l; intros alpha W Iv Ip Ir SOt.
    simpl in *.
    apply uni_closed_SO_impl. assumption.

    destruct a as [Qm].
    intros pa.
    apply IHl.
    apply Ip_uni_closed with (Ip := Ip).
    assumption.
Qed.

Lemma is_in_pred_list_closed_SO : forall l alpha P W Iv Ip Ir pa,
  In P l ->
  SOturnst W Iv Ip Ir (list_closed_SO alpha l) ->
  SOturnst W Iv (alt_Ip Ip pa P) Ir (list_closed_SO alpha l).
Proof.
  induction l; intros alpha P W Iv Ip Ir pa Hin SOt. firstorder.
    simpl list_closed_SO in *.
    intros pa2. simpl in *.
    specialize (SOt pa2).
    destruct (predicate_dec a P). subst.
    rewrite alt_Ip_rem. auto.
    destruct Hin. firstorder.
    rewrite alt_Ip_switch. apply IHl. all: auto.
Qed.

Lemma list_closed_SO_switch : forall l alpha P Q W Iv Ip Ir,
  SOturnst W Iv Ip Ir (list_closed_SO alpha (cons P (cons Q l))) ->
  SOturnst W Iv Ip Ir (list_closed_SO alpha (cons Q (cons P l))).
Proof.
  intros l alpha P Q W Iv Ip Ir SOt paQ paP.
  destruct (predicate_dec P Q). subst.
  + specialize (SOt paP paP).
    rewrite alt_Ip_rem in *. auto.
  + rewrite alt_Ip_switch; auto.
    specialize (SOt paP paQ). auto.
Qed.

Lemma SOt_alt_SOQFree' : forall (alpha : SecOrder) (W : Set)
                      (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
                    (Ir : W -> W -> Prop)  (Q : predicate) x,
  SOQFree alpha = true ->
    (SOturnst W Iv (alt_Ip Ip pa_f Q) Ir alpha <->
      SOturnst W Iv Ip Ir (replace_pred alpha Q x
       (negSO (eqFO (Var 1) (Var 1))))).
Proof.
  induction alpha; intros W Iv Ip Ir Q y HallSO.
  unfold pa_f. simpl in *.
  destruct (predicate_dec Q p). subst.
  destruct (FOvariable_dec y (Var 1)); subst;
  simpl; rewrite alt_Ip_eq; split; intros H; firstorder.
  simpl. rewrite alt_Ip_neq; firstorder.


    simpl in *.
    destruct f as [xn]; destruct f0 as [xm].
    destruct Q as [Qm].
    simpl.
    apply iff_refl.

    destruct f as [xn]; destruct f0 as [xm].
    destruct Q as [Qm].
    simpl.
    apply iff_refl.

    rewrite rep_pred_allFO.
    do 2 rewrite SOturnst_allFO.
    pose proof (SOQFree_allFO alpha f HallSO) as HallSO'.
    split; intros H d.
      (apply IHalpha; [assumption | apply H]).
      specialize (H d).
      apply IHalpha in H. assumption. assumption.

    rewrite rep_pred_exFO.
    do 2 rewrite SOturnst_exFO.
    pose proof (SOQFree_exFO alpha f HallSO) as HallSO'.
    split; intros H; destruct H as [d H]; exists d.
      apply IHalpha; assumption.
      apply IHalpha in H; assumption.

    rewrite rep_pred_negSO.
    do 2 rewrite SOturnst_negSO.
    split; intros H;
      unfold not; intros H2;
      apply H.
      apply IHalpha in H2;
      assumption.
      apply IHalpha;
      assumption.

    rewrite rep_pred_conjSO.
    do 2 rewrite SOturnst_conjSO.
    pose proof (SOQFree_conjSO_l alpha1 alpha2 HallSO) as H1.
    pose proof (SOQFree_conjSO_r alpha1 alpha2 HallSO) as H2.
    simpl in HallSO.
    split; intros H; apply conj.
      apply IHalpha1; [assumption | apply H].
      apply IHalpha2; [assumption | apply H].
      destruct H as [Ha Hb].
      apply IHalpha1 in Ha; assumption.
      destruct H as [Ha Hb].
      apply IHalpha2 in Hb; assumption.

    rewrite rep_pred_disjSO.
    do 2 rewrite SOturnst_disjSO.
    pose proof (SOQFree_disjSO_l alpha1 alpha2 HallSO) as H1.
    pose proof (SOQFree_disjSO_r alpha1 alpha2 HallSO) as H2.
    split; intros H;
      destruct H as [H | H].
      left; apply IHalpha1; assumption.
      right; apply IHalpha2; assumption.
      left; apply IHalpha1 in H; assumption.
      right; apply IHalpha2 in H; assumption.

    rewrite rep_pred_implSO.
    do 2 rewrite SOturnst_implSO.
    pose proof (SOQFree_implSO_l alpha1 alpha2 HallSO) as H1.
    pose proof (SOQFree_implSO_r alpha1 alpha2 HallSO) as H2.
    split; intros H H3.
      apply IHalpha2; [assumption | apply H; apply IHalpha1 in H3;
          assumption].
      apply IHalpha1 with (x := y) in H3. specialize (H H3).
        apply IHalpha2 in H. all: try assumption.

    simpl in HallSO.
    destruct p; discriminate.

    simpl in HallSO.
    destruct p; discriminate.
Qed.


Lemma rep_pred_list_closed_pre : forall alpha P x W Iv Ip Ir,
  SOQFree alpha = true ->
  SOturnst W Iv Ip Ir (allSO P alpha) ->
  SOturnst W Iv Ip Ir (allSO P (replace_pred alpha P x (negSO (eqFO (Var 1) (Var 1))))).
Proof.
  intros alpha [Pn] [xn] W Iv Ip Ir Hno SOt.
  intros pa. apply SOt_alt_SOQFree'.
    assumption.

    rewrite alt_Ip_rem.
    apply SOt.
Qed.

Lemma rep_pred_list_closed : forall l alpha P x W Iv Ip Ir,
  SOQFree alpha = true ->
  SOturnst W Iv Ip Ir (list_closed_SO alpha (cons P l)) ->
  SOturnst W Iv Ip Ir (list_closed_SO (replace_pred alpha P x (negSO (eqFO (Var 1) (Var 1)))) (cons P l)).
Proof.
  induction l; intros alpha [Pn] x W Iv Ip Ir Hno SOt.
    simpl list_closed_SO in *.
    apply rep_pred_list_closed_pre; assumption.

    destruct a as [Qm].
    apply list_closed_SO_switch.
    intros pa.
    apply list_closed_SO_switch in SOt.
    specialize (SOt pa).
    apply IHl; assumption.
Qed.

Lemma rep_pred_list_closed_pre_predSO : forall p f,
  forall (P : predicate) (cond : SecOrder) (x : FOvariable) 
  (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop),
FO_frame_condition cond = true ->
SOturnst W Iv Ip Ir (allSO P (predSO p f)) ->
SOturnst W Iv Ip Ir
  (allSO P (replace_pred (predSO p f) P x (negSO (eqFO (Var 1) (Var 1))))).
Proof.
  intros Q y P cond x W Iv Iip Ir Hun SOt.
  simpl replace_pred. destruct (predicate_dec P Q).
  specialize (SOt pa_f). subst. rewrite alt_Ip_eq in SOt.
  firstorder. firstorder.
Qed.

Lemma rep_pred_list_closed_pre_relatSO : forall f f0 (P : predicate) (cond : SecOrder) (x : FOvariable) 
  (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop),
FO_frame_condition cond = true ->
SOturnst W Iv Ip Ir (allSO P (relatSO f f0)) ->
SOturnst W Iv Ip Ir
  (allSO P (replace_pred (relatSO f f0) P x (negSO (eqFO (Var 1) (Var 1))))).
Proof.
  intros [x1] [x2] [Pn] cond [x] W Iv Ip Ir Hun SOt.
  simpl in *.
  assumption.
Qed.

Lemma rep_pred_list_closed_pre_eqFO : forall f f0 (P : predicate) (cond : SecOrder) (x : FOvariable) 
  (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop),
FO_frame_condition cond = true ->
SOturnst W Iv Ip Ir (allSO P (eqFO f f0)) ->
SOturnst W Iv Ip Ir
  (allSO P (replace_pred (eqFO f f0) P x (negSO (eqFO (Var 1) (Var 1))))).
Proof.
  intros [x1] [x2] [Pn] cond [x] W Iv Ip Ir Hun SOt.
  simpl in *.
  assumption.
Qed.

Lemma list_closed_SO_rep_pred2 : forall l alpha Pn x W Iv Ip Ir,
In (Pred Pn) l ->
SOQFree alpha = true ->
SOturnst W Iv Ip Ir (list_closed_SO alpha l) ->
SOturnst W Iv Ip Ir (list_closed_SO (replace_pred alpha 
        (Pred Pn) x (negSO (eqFO (Var 1) (Var 1)))) l).
Proof.
  induction l; intros alpha Pn x W Iv Ip Ir Hin Hno SOt. firstorder.
  simpl in *. destruct Hin. subst.
  intros pa. apply rep_pred_list_closed; auto.
  intros pa. apply IHl; auto.
Qed.

Lemma list_closed_instant_one_f : forall n lP l alpha lx W Iv Ip Ir,
  incl (nlist_list n lP) l ->
  SOQFree alpha = true ->
  SOturnst W Iv Ip Ir (list_closed_SO alpha l) ->
  SOturnst W Iv Ip Ir (list_closed_SO (replace_pred_l alpha 
        (nlist_list n lP) (nlist_list n lx) 
        (nlist_list n (nlist_empty _))) l).
Proof.
  induction n; intros lP l alpha lx W Iv Ip Ir Hin Hno SOt.
    rewrite (nlist_nil2 lP) in *.
    simpl in *.
    assumption.

    destruct (nlist_cons2 _ lP) as [[Pn] [lP' HlP]].
    destruct (nlist_cons2 _ lx) as [[xn] [lx' Hlx]].
    destruct (nlist_cons2 _ lx) as [[cond2] [lcond' Hlcond]].
    rewrite HlP in *; rewrite Hlx in *; rewrite Hlcond in *.
    simpl.
    simpl in Hin.
    destruct (in_dec (predicate_dec) (Pred Pn) (nlist_list n lP')).
    destruct (in_predicate_dec (Pred Pn) l). 
    2 : (apply incl_hd in Hin; contradiction).
      rewrite rep_pred__l_is_in.
      simpl in Hin.
      apply IHn. all : try assumption.  

      apply incl_lcons in Hin. auto.

      apply FO_frame_condition_l_empty_n.
        reflexivity.

        rewrite rep_pred__l_switch; auto.
        pose proof (incl_hd _ _ _ _ Hin) as Hin'.
        apply IHn; try assumption.
        apply incl_lcons in Hin. auto.
        apply SOQFree_rep_pred_empty. assumption.
        apply list_closed_SO_rep_pred2; assumption.
        apply FO_frame_condition_l_empty_n.
Qed.

Lemma allSO_switch : forall alpha P Q W Iv Ip Ir,
  SOturnst W Iv Ip Ir (allSO P (allSO Q alpha)) ->
  SOturnst W Iv Ip Ir (allSO Q (allSO P alpha)).
Proof.
  intros alpha P Q W Iv Ip Ir SOt.
  rewrite SOturnst_allSO in *.
  intros paQ.
  rewrite SOturnst_allSO.
  intros paP. 
  destruct (predicate_dec P Q) as [Hbeq | Hbeq]. subst.
    rewrite alt_Ip_rem.  specialize (SOt paQ).
    rewrite SOturnst_allSO in SOt. specialize (SOt paP).
    rewrite alt_Ip_rem in SOt. auto.

    rewrite alt_Ip_switch. specialize (SOt paP).
    rewrite SOturnst_allSO in SOt. specialize (SOt paQ).
    all : auto.
Qed.

Lemma list_closed_SO_dup : forall l P alpha W Iv Ip Ir,
  In P l ->
  SOturnst W Iv Ip Ir (list_closed_SO alpha l) ->
  SOturnst W Iv Ip Ir (list_closed_SO alpha (cons P l)).
Proof.
  induction l; intros P alpha W Iv Ip Ir His SOt. contradiction.
  simpl in *. destruct His. subst. intros pa1 pa2. 
  rewrite alt_Ip_rem. apply SOt.
  intros pa1 p2. destruct (predicate_dec P a) as [H1 | H1].
  subst. rewrite alt_Ip_rem. apply SOt.
  rewrite alt_Ip_switch. apply IHl. auto. apply SOt. auto.
Qed.

Lemma vsSahlq_pp_Lemma3_pre : forall l1 l2 alpha W Iv Ip Ir,
  incl l1 l2 ->
  SOturnst W Iv Ip Ir (list_closed_SO alpha l2) ->
  SOturnst W Iv Ip Ir (list_closed_SO alpha l1).
Proof.
  induction l1; intros l2 alpha W Iv Ip Ir His SOt.
    simpl in *.
    apply list_closed_SO_impl in SOt; assumption.

    destruct a as [Pn].
    intros pa.
    apply IHl1 with (l2 := l2).
    apply incl_lcons in His. auto.
      apply list_closed_SO_dup with (P := Pred Pn) in SOt.
      specialize (SOt pa).
      all : auto. 
      apply incl_hd in His. auto.
Qed.

Lemma vsSahlq_pp_Lemma3 : forall l alpha W Iv Ip Ir,
  incl (preds_in alpha) l ->
  SOturnst W Iv Ip Ir (list_closed_SO alpha l) ->
  SOturnst W Iv Ip Ir (uni_closed_SO alpha).
Proof.
  intros.
  apply vsSahlq_pp_Lemma3_pre with (l2 := l); assumption.
Qed.

Lemma equiv_list_closed_SO : forall l alpha beta,
  (forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir alpha <-> SOturnst W Iv Ip Ir beta) ->
  forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir (list_closed_SO alpha l) <->
    SOturnst W Iv Ip Ir (list_closed_SO beta l).
Proof.
  induction l; intros alpha beta H W Iv Ip Ir.
    simpl in *. apply H.

    destruct a as [Pn].
    split; intros SOt pa.
      apply IHl with (alpha := alpha). assumption.
      apply SOt.

      apply IHl with (alpha := beta).
        intros; split; apply H; assumption.
      apply SOt.
Qed.

Lemma equiv_list_closed_SO_app_l : forall l alpha W Iv Ip Ir,
  SOturnst W Iv Ip Ir (list_closed_SO alpha (app l (preds_in alpha))) <->
  SOturnst W Iv Ip Ir (list_closed_SO alpha (preds_in alpha)).
Proof.
  induction l; intros alpha W Iv Ip Ir.
    simpl. apply iff_refl.

    simpl app. destruct a as [Pn].
    split; intros SOt.
      apply IHl.
      specialize (SOt (Ip (Pred Pn))).
      rewrite unalt_fun in SOt.
      assumption.

      intros pa.
      apply IHl.
      pose proof (Ip_uni_closed W alpha Iv Ip 
        (alt_Ip Ip pa (Pred Pn))) as H2.
      apply H2. assumption.
Qed.

Lemma equiv_list_closed_SO_app_cons : forall l P alpha W Iv Ip Ir,
  SOturnst W Iv Ip Ir (list_closed_SO alpha (app l (cons P nil))) <->
  SOturnst W Iv Ip Ir (list_closed_SO alpha (cons P l)).
Proof.
  induction l; intros [Pn] alpha W Iv Ip Ir.
    simpl. apply iff_refl.

    destruct a as [Qm].
    simpl list_closed_SO.
    split; intros SOt.
      apply allSO_switch.
      intros pa.
      apply IHl. apply SOt.

      apply allSO_switch in SOt.
      intros pa.
      apply IHl. simpl list_closed_SO.
      specialize (SOt pa). assumption.
Qed.

Lemma equiv_list_closed_SO_app : forall l1 l2 alpha W Iv Ip Ir,
  SOturnst W Iv Ip Ir (list_closed_SO alpha (app l1 l2)) <->
  SOturnst W Iv Ip Ir (list_closed_SO alpha (app l2 l1)).
Proof.
  induction l1; intros l2 alpha W Iv Ip Ir.
    simpl. rewrite app_nil_r. apply iff_refl.

    destruct a as [Pn]. simpl app.
    assert (app l2 (cons (Pred Pn) l1) = 
            app (app l2 (cons (Pred Pn) nil)) l1) as Heq.
      rewrite <- app_assoc.   auto.
    rewrite Heq.
    assert (app l1 (app l2 (cons (Pred Pn) nil)) =
            app (app l1 l2) (cons (Pred Pn) nil)) as Heq2.
      firstorder.
    split; intros SOt.
      apply IHl1.
      rewrite Heq2.
      apply equiv_list_closed_SO_app_cons.
      assumption.

      apply IHl1 in SOt.
      rewrite Heq2 in SOt.
      apply equiv_list_closed_SO_app_cons in SOt.
      assumption.
Qed.

Lemma equiv_list_closed_SO_app_r : forall l alpha W Iv Ip Ir,
  SOturnst W Iv Ip Ir (list_closed_SO alpha (app (preds_in alpha) l)) <->
  SOturnst W Iv Ip Ir (list_closed_SO alpha (preds_in alpha)).
Proof.
  intros l alpha W Iv Ip Ir.
  split; intros SOt.
    apply equiv_list_closed_SO_app in SOt.
    apply (equiv_list_closed_SO_app_l l alpha).
    assumption.

    apply equiv_list_closed_SO_app.
    apply (equiv_list_closed_SO_app_l l alpha).
    assumption.
Qed.

Lemma equiv_uni_closed_SO : forall alpha beta,
  (forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir alpha <-> SOturnst W Iv Ip Ir beta) ->
  forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir (uni_closed_SO alpha) <->
    SOturnst W Iv Ip Ir (uni_closed_SO beta).
Proof.
  intros alpha beta H W Iv Ip Ir.
  destruct (equiv_list_closed_SO (app (preds_in alpha) (preds_in beta))
      alpha beta H W Iv Ip Ir) as [fwd rev].
  unfold uni_closed_SO.
  split; intros SOt.
    apply equiv_list_closed_SO_app_l with (l := (preds_in alpha)).
    apply fwd.
    apply equiv_list_closed_SO_app_r.
    assumption.

    apply equiv_list_closed_SO_app_r with (l := (preds_in beta)).
    apply rev.
    apply equiv_list_closed_SO_app_l.
    assumption.
Qed.

Lemma equiv_impl_exFO : forall alpha beta x W Iv Ip Ir,
  free_FO beta x = false ->
  SOturnst W Iv Ip Ir (implSO (exFO x alpha) beta) <->
  SOturnst W Iv Ip Ir (allFO x (implSO alpha beta)).
Proof.
  intros alpha beta x W Iv Ip Ir Hfee.
  rewrite SOturnst_allFO.
  split; intros H.
    intros d SOt.
    assert (SOturnst W Iv Ip Ir (exFO x alpha)) as SOt'.
      rewrite SOturnst_exFO.
      exists d. assumption.
    specialize (H SOt').
    apply alt_Iv_equiv; assumption.

    intros SOt.
    rewrite SOturnst_exFO in SOt.
    destruct SOt as [d SOt].
    specialize (H d SOt).
    apply alt_Iv_equiv in H; assumption.
Qed.

Lemma equiv_implSO2 : forall alpha beta gamma,
  (forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir alpha <->
    SOturnst W Iv Ip Ir beta) ->
  forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir (implSO alpha gamma) <->
    SOturnst W Iv Ip Ir (implSO beta gamma).
Proof.
  intros alpha beta gamma H W Iv Ip Ir.
  simpl.
  split; intros H1 H2;
    apply H1;
    apply H;
    assumption.
Qed.

Lemma SOturnst_trans : forall alpha beta gamma,
  (forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir alpha <->
    SOturnst W Iv Ip Ir beta) ->
  (forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir beta <->
    SOturnst W Iv Ip Ir gamma) ->
  forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir alpha <->
    SOturnst W Iv Ip Ir gamma.
Proof.
  intros alpha beta gamma H1 H2 W Iv Ip Ir.
  split; intros SOt.
    apply H2; apply H1; assumption.
    apply H1; apply H2; assumption.
Qed.

Lemma SOturnst_equiv_Ip : forall alpha W Iv Ip Ip' Ir,
    (forall P w, Ip P w <-> Ip' P w) ->
  <W Iv Ip Ir> ⊨ alpha <-> <W Iv Ip' Ir> ⊨ alpha.
Proof.
  induction alpha; intros W Iv Ip Ip' Ir H;
    try (solve [firstorder]).

    simpl in *. split ; intros H1 w.
    eapply (IHalpha _ _ Ip Ip') . apply H. auto. 
    eapply (IHalpha _ _ Ip Ip') . apply H. auto. 

    simpl in *. split ; intros [w H1]; exists w.
    eapply (IHalpha _ _ Ip Ip') . apply H. auto. 
    eapply (IHalpha _ _ Ip Ip') . apply H. auto. 

    simpl. split; intros H1 H3; apply H1; eapply (IHalpha _ _ Ip Ip'); auto.
    
    simpl. split; intros [H1 H3]; eapply (IHalpha1 _ _ Ip Ip') in H1;
    eapply (IHalpha2 _ _ Ip Ip') in H3. 
    apply conj. apply H1. apply H3. 1-3 : firstorder. all : auto.
      all : try (eapply SOQFree_P_conjSO_r; apply H).
      all : try (eapply SOQFree_P_conjSO_l; apply H).
    
    simpl. split; (intros [H1 |H1]; [eapply (IHalpha1 _ _ Ip Ip') in H1 |
    eapply (IHalpha2 _ _ Ip Ip') in H1]); firstorder.
    all : try (eapply SOQFree_P_conjSO_r; apply H).
    all : try (eapply SOQFree_P_conjSO_l; apply H).

    simpl. split; intros H1 H3; eapply (IHalpha2 _ _ Ip Ip'); auto;
      try (eapply SOQFree_P_conjSO_r; apply H);
      apply H1; eapply (IHalpha1 _ _ Ip Ip'); firstorder;
      try (eapply SOQFree_P_conjSO_l; apply H).

    simpl in *. split; intros H1 pa;
    apply (IHalpha _ _ (alt_Ip Ip pa p) (alt_Ip Ip' pa p) ). intros P w.
    destruct (predicate_dec p P) as [H2 | H2].
    subst. do 2 rewrite alt_Ip_eq. firstorder.
    rewrite alt_Ip_neq. rewrite alt_Ip_neq. apply H. all : auto.
    intros P w. destruct (predicate_dec p P) as [H2 | H2].
    subst. do 2 rewrite alt_Ip_eq. firstorder.
    rewrite alt_Ip_neq. rewrite alt_Ip_neq. apply H. all : auto.
    
    simpl in *. split; intros [pa H1]; exists pa;
    apply (IHalpha _ _ (alt_Ip Ip pa p) (alt_Ip Ip' pa p) ). intros P w.
    destruct (predicate_dec p P) as [H2 | H2].
    subst. do 2 rewrite alt_Ip_eq. firstorder.
    rewrite alt_Ip_neq. rewrite alt_Ip_neq. apply H. all : auto.
    intros P w. destruct (predicate_dec p P) as [H2 | H2].
    subst. do 2 rewrite alt_Ip_eq. firstorder.
    rewrite alt_Ip_neq. rewrite alt_Ip_neq. apply H. all : auto.
Qed.

Lemma hopeful4 : forall alpha x y W Iv Ip Ir d,
  ~ var_in_SO alpha y ->
  SOturnst W (alt_Iv Iv d y) Ip Ir (replace_FOv alpha x y) <->
  SOturnst W (alt_Iv Iv d x) Ip Ir alpha.
Proof.
  induction alpha; intros x y W Iv Ip Ir d Hocc; unfold var_in_SO in *.
    
    simpl in *. destruct (FOvariable_dec x f). subst. simpl. 
    do 2 rewrite alt_Iv_eq. firstorder.
    simpl. rewrite alt_Iv_neq. rewrite alt_Iv_neq; auto.
    firstorder. firstorder.

    simpl in *. destruct (FOvariable_dec x f);
    destruct (FOvariable_dec x f0); subst; simpl;
    repeat (rewrite alt_Iv_eq; auto). firstorder.
    1-3 :repeat (rewrite alt_Iv_neq; auto); firstorder.

    simpl in *. destruct (FOvariable_dec x f);
    destruct (FOvariable_dec x f0); subst; simpl;
    repeat (rewrite alt_Iv_eq; auto). firstorder.
    1-3 :repeat (rewrite alt_Iv_neq; auto); firstorder.

    simpl in *. destruct (FOvariable_dec x f); subst; simpl.
    split ; intros SOt d2; specialize (SOt d2);
      rewrite alt_Iv_rem; rewrite alt_Iv_rem in SOt.
      apply IHalpha in SOt; auto.  apply IHalpha; auto.
    split; intros SOt d2; specialize (SOt d2);
      rewrite alt_Iv_switch; auto; rewrite alt_Iv_switch in SOt; auto.
      apply IHalpha in SOt; auto.       
      apply IHalpha; auto.

    simpl in *. destruct (FOvariable_dec x f); subst; simpl.
    split ; intros [d2 SOt]; exists d2;
      rewrite alt_Iv_rem; rewrite alt_Iv_rem in SOt.
      apply IHalpha in SOt; auto.  apply IHalpha; auto.
    split ; intros [d2 SOt]; exists d2;
      rewrite alt_Iv_switch; auto; rewrite alt_Iv_switch in SOt; auto.
      apply IHalpha in SOt; auto.       
      apply IHalpha; auto.

    simpl in *. split; intros H1 H2; apply H1.
    apply IHalpha; auto. apply IHalpha in H2; auto.

    simpl in *. split; intros [H1 H2]; apply conj.
    apply IHalpha1 in H1; auto. firstorder.
    apply IHalpha2 in H2; auto. firstorder.
    apply IHalpha1; auto. firstorder.
    apply IHalpha2; auto. firstorder.

    simpl in *. split; (intros [H1|H2]; [left | right]).
    apply IHalpha1 in H1; auto. firstorder.
    apply IHalpha2 in H2; auto. firstorder.
    apply IHalpha1; auto. firstorder.
    apply IHalpha2; auto. firstorder.

    simpl in *. split; intros H1 H2. eapply IHalpha2. 2: apply H1.
    firstorder. apply IHalpha1; auto. firstorder.
    apply IHalpha2; auto. firstorder. apply H1. apply IHalpha1 in H2.
    auto. firstorder.

    simpl in *. split; intros H pa; specialize (H pa).
    apply IHalpha in H; auto. apply IHalpha; auto.

    simpl in *. split; intros [pa H]; exists pa. 
    apply IHalpha in H; auto. apply IHalpha; auto.
Qed.

Lemma hopeful3_allFO : forall alpha x y W Iv Ip Ir,
  ~ var_in_SO alpha y ->
  SOturnst W Iv Ip Ir (replace_FOv (allFO x alpha) x y) <->
  SOturnst W Iv Ip Ir (allFO x alpha).
Proof.
  intros alpha x y W Iv Ip Ir Hocc. simpl in *. 
  rewrite FOvariable_dec_l. simpl. split; intros SOt d;
  specialize (SOt d). apply hopeful4 in SOt; auto.
  apply hopeful4; auto. auto.
Qed. 

Lemma hopeful3_exFO : forall alpha x y W Iv Ip Ir,
  ~ var_in_SO alpha y ->  
  SOturnst W Iv Ip Ir (replace_FOv (exFO x alpha) x y) <->
  SOturnst W Iv Ip Ir (exFO x alpha).
Proof.
  intros alpha x y W Iv Ip Ir Hocc. simpl in *. 
  rewrite FOvariable_dec_l. simpl. split; intros [d SOt];
  exists d. apply hopeful4 in SOt; auto.
  apply hopeful4; auto. auto.
Qed.

Lemma impl_list_closed_allFO : forall l alpha beta,
  (forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir alpha ->
    SOturnst W Iv Ip Ir beta) ->
  forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir (list_closed_allFO alpha l) ->
    SOturnst W Iv Ip Ir (list_closed_allFO beta l).
Proof.
  induction l; intros alpha beta H W Iv Ip Ir SOt.
    simpl in *. apply H. assumption.

    simpl list_closed_allFO in *.
    rewrite SOturnst_allFO in *.
    intros d. apply (IHl alpha). assumption.
    apply SOt.
Qed.

Lemma equiv_conjSO_exFO : forall alpha x gamma W Iv Ip Ir,
  SOturnst W Iv Ip Ir (conjSO gamma (exFO x alpha)) <->
  SOturnst W Iv Ip Ir (exFO (replace_FOv_max_conj_var alpha gamma x) (conjSO gamma (replace_FOv_max_conj alpha gamma x))).
Proof.
  intros alpha x gamma W Iv Ip Ir.
  unfold replace_FOv_max_conj_var. unfold replace_FOv_max_conj.
  destruct x as [xn].
  remember (max_FOv (conjSO gamma (exFO (Var xn) alpha))) as mx.
  assert ((max_FOv (exFO (Var xn) alpha)) <= mx) as Hle.
    rewrite Heqmx.
    apply le_max_FOv_exFO_conjSO.
  pose proof (exFO_rep_FOv_max_FOv alpha xn mx Hle) as H.
  pose proof (equiv_conjSO2 gamma _ _ H) as H2.  clear H.
  split; intros SOt.
    apply H2 in SOt. apply equiv_conj_ex2.
      rewrite Heqmx. apply free_FO_max_FOv_f.
    assumption.

    apply H2.  apply equiv_conj_ex2 in SOt.
      assumption.
    rewrite Heqmx. apply free_FO_max_FOv_f.
Qed.

Lemma equiv3_3_struc2_ind_nlist : forall n (lv : nlist n) alpha gamma,
  forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (conjSO gamma (list_closed_exFO alpha (nlist_list _ lv))) <->
  SOturnst W Iv Ip Ir (list_closed_exFO 
        (conjSO gamma (replace_FOv_A alpha gamma (nlist_list _ lv)))
                      (replace_FOv_A_list alpha gamma (nlist_list _ lv))).
Proof.
  induction n; intros lv alpha gamma.
    pose proof (nlist_nil2 lv) as Hnil.   
    rewrite Hnil.
    simpl.
    intros W Iv Ip Ir.
    apply iff_refl.

    destruct (nlist_cons2 _ lv) as [x [lvv Heq1]].
    pose proof (equiv_conjSO_exFO (list_closed_exFO alpha (nlist_list _ lvv)) x gamma) as SOt.
    pose proof (list_closed_exFO_strip_exFO (nlist_list _ lvv) alpha 
      ((replace_FOv_max_conj (list_closed_exFO alpha (nlist_list n lvv)) gamma x))) as [Hs' [Hl' Heq]].
      apply same_struc_replace_FOv_max_conj.
    rewrite Heq in *.
    pose proof Hl' as Hl''.
    rewrite <- Heq in Hl''.
    symmetry in Hl''.
    rewrite length_nlist_list in Hl'' at 2.
    destruct (nlist_list_ex _ (strip_exFO_list (replace_FOv_max_conj (list_closed_exFO alpha (nlist_list n lvv)) gamma x)
            (length (nlist_list n lvv))) Hl'') as [ln' H2].
    intros W Iv Ip Ir.
    rewrite Heq1.
    simpl nlist_list.
    unfold replace_FOv_A in *.
    simpl replace_FOv_A_list_pre.
    unfold replace_FOv_A_list in *.
    simpl replace_FOv_A_pre.
    simpl replace_FOv_A_list_pre.
    do 2 rewrite list_closed_exFO_cons.
    specialize (IHn ln'  (strip_exFO
               (replace_FOv_max_conj (list_closed_exFO alpha (nlist_list n lvv)) gamma x)
               (length (nlist_list n lvv))) gamma).
    rewrite H2 in *.
    rewrite Hl'' in *.
    rewrite length_nlist_list at 3.
    rewrite length_nlist_list at 5.
    split; intros H.
      apply (equiv_exFO _ _ (IHn)).
      apply SOt in H.
      assumption.

      apply (equiv_exFO _ _ (IHn)) in H.
      apply SOt.
      assumption.
Qed.

Lemma equiv3_3_struc2_ind_nlist2 : forall n (lv : nlist n) alpha gamma,
  forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (conjSO (list_closed_exFO alpha (nlist_list _ lv)) gamma) <->
  SOturnst W Iv Ip Ir (list_closed_exFO 
        (conjSO (replace_FOv_A alpha gamma (nlist_list _ lv)) gamma)
                (replace_FOv_A_list alpha gamma (nlist_list _ lv))).
Proof.
  intros n lv alpha gamma W Iv Ip Ir.
  split; intros H.
    apply (equiv_list_closed_exFO _
       (conjSO gamma (replace_FOv_A alpha gamma (nlist_list n lv)))
       (replace_FOv_A_list alpha gamma (nlist_list n lv))).
    apply equiv_conjSO.
    apply equiv3_3_struc2_ind_nlist.
    apply equiv_conjSO in H.
    assumption.

    apply (equiv_list_closed_exFO _
       (conjSO gamma (replace_FOv_A alpha gamma (nlist_list n lv)))
       (replace_FOv_A_list alpha gamma (nlist_list n lv))) in H.
    apply equiv_conjSO.
    apply equiv3_3_struc2_ind_nlist.
    assumption.
    apply equiv_conjSO.
Qed.

Lemma equiv3_3_struc2 : forall lv alpha gamma,
  forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (conjSO gamma (list_closed_exFO alpha lv)) <->
  SOturnst W Iv Ip Ir (list_closed_exFO 
        (conjSO gamma (replace_FOv_A alpha gamma lv))
                      (replace_FOv_A_list alpha gamma lv)).
Proof.
  intros lv.
  destruct (nlist_list_ex (length lv) lv eq_refl).
  rewrite <- H.
  apply equiv3_3_struc2_ind_nlist.
Qed.

Lemma equiv3_3_struc2_2 : forall lv alpha gamma,
  forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (conjSO (list_closed_exFO alpha lv) gamma) <->
  SOturnst W Iv Ip Ir (list_closed_exFO 
        (conjSO (replace_FOv_A alpha gamma lv) gamma)
                (replace_FOv_A_list alpha gamma lv)).
Proof.
  intros lv.
  destruct (nlist_list_ex (length lv) lv eq_refl).
  rewrite <- H.
  apply equiv3_3_struc2_ind_nlist2.
Qed.

Lemma equiv3_3_struc2_both : forall lv1 lv2 alpha beta,
  forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (conjSO (list_closed_exFO alpha lv1) 
                              (list_closed_exFO beta lv2)) <->
  SOturnst W Iv Ip Ir 
    (list_closed_exFO (list_closed_exFO (conjSO 
      (replace_FOv_A alpha (replace_FOv_A beta (list_closed_exFO alpha lv1) lv2) lv1)
      (replace_FOv_A beta (list_closed_exFO alpha lv1) lv2)) 
          (replace_FOv_A_list alpha (replace_FOv_A beta (list_closed_exFO alpha lv1) lv2) lv1))
          (replace_FOv_A_list beta (list_closed_exFO alpha lv1) lv2)).
Proof.
  intros lv1 lv2 alpha beta W Iv Ip Ir.
  pose proof (equiv3_3_struc2_2 lv1 alpha (replace_FOv_A beta (list_closed_exFO alpha lv1) lv2)) as H.
  split; intros SOt.
    apply equiv3_3_struc2 in SOt.
    apply (equiv_list_closed_exFO _ _ (replace_FOv_A_list beta (list_closed_exFO alpha lv1) lv2) H).
    assumption.

    apply equiv3_3_struc2.
    apply (equiv_list_closed_exFO _ _ (replace_FOv_A_list beta (list_closed_exFO alpha lv1) lv2) H).
    assumption.
Qed.