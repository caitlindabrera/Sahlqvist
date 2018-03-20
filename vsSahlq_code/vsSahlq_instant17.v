Require Export vsSahlq_instant16.

(* ---------------------------------------------------------- *)

Lemma lemma18 : forall l1 l2 (W : Set) (Iv : FOvariable -> W) x w,
  ~l1 = nil ->
  ~l2 = nil ->
 CM_pa2_l_gen Iv (app l1 l2) x w <->
 CM_pa2_l_gen Iv l1 x w \/  CM_pa2_l_gen Iv l2 x w.
Proof.
  induction l1; intros l2 W Iv x w H1 H2.
    contradiction (H1 eq_refl).

    simpl in *. case_eq l1.
      intros Hl. simpl. unfold CM_pa2_l_gen.
      simpl. destruct x as [xn]. destruct a as [ym].
      case_eq (beq_nat xn ym); intros Hbeq.
        split; intros H. left. assumption.
        unfold pa_t. exact I.

        case_eq (is_in_var (Var xn) l2); intros Hin.
          split; intros H; [right|]; unfold pa_t; exact I.

        destruct l2. contradiction (H2 eq_refl). apply bi_refl.

      intros y ly Hly. rewrite <- Hly. unfold CM_pa2_l_gen. simpl.
      simpl. destruct x as [xn]. destruct a as [ym].
      case_eq (beq_nat xn ym); intros Hbeq.
        split; intros H. left. assumption.
        unfold pa_t. exact I.

        rewrite <- is_in_FO_var.
        rewrite <- (is_in_FO_var l1 (Var xn)).
        rewrite <- (is_in_FO_var l2 (Var xn)).
        rewrite is_in_FOvar_app.
        case_eq (is_in_FOvar (Var xn) l1); intros Hin.
          split; intros H. left. assumption.
          unfold pa_t. exact I.

          case_eq (is_in_FOvar (Var xn) l2); intros Hin2.
            rewrite Hly. rewrite <- Hly.  
            split; intros; [right|]; unfold pa_t; exact I.

            rewrite Hly. case_eq (app (cons y ly) l2).
            intros H. discriminate.
            intros z lz Hlz. rewrite <- Hlz. rewrite <- Hly.
              assert (~ l1 = nil) as Hnil.
                rewrite Hly. intros. discriminate.
              specialize (IHl1 _ W Iv (Var xn) w Hnil H2).
              unfold CM_pa2_l_gen in IHl1. rewrite <- is_in_FO_var in *.
              rewrite <- (is_in_FO_var l1) in IHl1.
              rewrite <- (is_in_FO_var l2) in IHl1.
              rewrite is_in_FOvar_app in IHl1.
              rewrite Hin in IHl1. rewrite Hin2 in IHl1.
            split; intros H. destruct H. left. left. assumption.  
              apply IHl1 in H. destruct H. left. right. assumption.
                right. assumption.

              destruct H. destruct H. left. assumption.
                right. apply IHl1. left. assumption.
                right. apply IHl1. right. assumption.
Qed.

Lemma P_occurs_in_alpha_passing_predSO_l : forall l P Q,
  ~ l = nil ->
  P_occurs_in_alpha (passing_conj (passing_predSO_l Q l)) P = true ->
  P = Q.
Proof.
  induction l; intros [Pn] [Qm] H1 H2.
    contradiction (H1 eq_refl).

    case_eq l. intros Hl. rewrite Hl in *.
      simpl in *. unfold P_occurs_in_alpha in H2.
      destruct a. simpl in *.
      case_eq (beq_nat Pn Qm); intros Hbeq.
        rewrite (beq_nat_true _ _ Hbeq). reflexivity.

        rewrite Hbeq in *. discriminate.

      intros x lx Hlx. simpl in *.
      case_eq (passing_predSO_l (Pred Qm) l).
        intros Hp. rewrite Hlx in Hp. discriminate.
      intros beta lbeta Hlbeta.
        rewrite Hlbeta in H2. rewrite <- Hlbeta in H2.
      rewrite P_occurs_in_alpha_conjSO in H2.
      destruct H2.
        unfold P_occurs_in_alpha in H. destruct a.
        simpl in *.
        case_eq (beq_nat Pn Qm); intros Hbeq.
          rewrite (beq_nat_true _ _ Hbeq). reflexivity.

          rewrite Hbeq in *. discriminate.

        apply IHl. intros HH. rewrite Hlx in *. discriminate.
        assumption.
Qed.

Lemma lemma17_pre : forall l P x W Iv Ip Ir w pa,
  ~ l = nil ->
  is_in_FOvar x l = false ->
  SOturnst W Iv (altered_Ip Ip pa P) Ir (passing_conj (passing_predSO_l P l)) ->
  CM_pa2_l_gen Iv l x w ->
  pa w.
Proof.
  induction l; intros P x W Iv Ip Ir w pa Hnil Hin SOt CM.
    contradiction (Hnil eq_refl).

    simpl in *. case_eq (passing_predSO_l P l).
      intros Hp. rewrite Hp in  *. destruct l. 2 : discriminate.
      destruct P. destruct a as [ym]. simpl in *. rewrite <- beq_nat_refl in *.
      unfold CM_pa2_l_gen in *. simpl in *. destruct x as [xn].
      case_eq (beq_nat xn ym); intros Hbeq; rewrite Hbeq in *. discriminate.

        rewrite CM in *. assumption.

      intros beta lbeta Hlbeta.
      rewrite Hlbeta in *. rewrite <- Hlbeta in *.
      simpl in SOt. destruct P as [Pn]. destruct a as [ym].
      destruct SOt as [SOt1 SOt2].
      simpl in SOt1. rewrite <- beq_nat_refl in SOt1.
      unfold CM_pa2_l_gen in CM. simpl in CM.
      destruct x as [xn]. case_eq (beq_nat xn ym);
        intros Hbeq; rewrite Hbeq in *. discriminate.

        destruct l. rewrite CM. assumption.
        rewrite <- is_in_FO_var in *. rewrite Hin in *.
        destruct CM as [CM | CM]. rewrite CM. assumption.
        apply (IHl (Pred Pn) (Var xn) W Iv Ip Ir w pa).
          discriminate.
          assumption. assumption.
          unfold CM_pa2_l_gen. rewrite <- is_in_FO_var. rewrite Hin.
          assumption.
Qed.

Lemma SOQFree_passing_predSO_l : forall l P,
  SOQFree (passing_conj (passing_predSO_l P l)) = true.
Proof.
  induction l; intros P. reflexivity.
  simpl. destruct l. simpl. destruct P. destruct a. reflexivity.
  simpl in *. destruct P. destruct a. apply IHl.
Qed.

Lemma SOQFree_passing_predSO_ll : forall lP llx,
  SOQFree (passing_conj (passing_predSO_ll lP llx)) = true.
Proof.
  induction lP; intros llx. reflexivity.
  simpl. destruct llx. reflexivity.
  simpl. destruct lP.  simpl in *.
  apply SOQFree_passing_predSO_l.
  destruct llx. simpl. apply SOQFree_passing_predSO_l.
  simpl. rewrite SOQFree_passing_predSO_l.
  apply (IHlP (cons l0 llx)).
Qed.

Lemma  is_in_FOvar_app_r  : forall l1 l2 x,
  is_in_FOvar x (app l1 l2) = false ->
  is_in_FOvar x l2 = false.
Proof.
  induction l1; intros l2 x H.
    simpl in *. assumption.

    simpl in *.
    destruct x as [xn]; destruct a as [ym]. 
    simpl in H.
    case_eq (beq_nat xn ym); intros Hbeq;
      rewrite Hbeq in *. discriminate.
    apply (IHl1 l2). assumption.
Qed.

Lemma lemma17_again : forall lP llx P x W Iv Ip Ir pa w,
  ~ lP = nil ->
  length lP = length llx ->
  ex_nil_in_llv llx = false ->
  is_in_FOvar x (fun2 (passing_conj (passing_predSO_ll lP llx)) P)  = false ->
  P_occurs_in_alpha (passing_conj (passing_predSO_ll lP llx)) P = true ->
  SOturnst W Iv (altered_Ip Ip pa P) Ir (passing_conj (passing_predSO_ll lP llx)) ->
  CM_pa2_l_gen Iv (fun2 (passing_conj (passing_predSO_ll lP llx)) P) x w ->
  pa w.
Proof.
  induction lP; intros llx P x W Iv Ip Ir pa w Hnil Hlength Hex Hin Hpocc SOt CM.
    contradiction (Hnil eq_refl).
  simpl in Hin.
    case_eq lP. intros Hp. rewrite Hp in *.
      simpl in *. destruct llx. discriminate.
      destruct llx. 2 : discriminate. simpl in *.
      apply P_occurs_in_alpha_passing_predSO_l in Hpocc. rewrite Hpocc in *.
      rewrite lem_try10 in CM.
      rewrite lem_try10 in Hin.
      apply lemma17_pre with (x := x) (w := w) in SOt ; try assumption.
      all : try (      destruct l; discriminate).

      intros P' lP' HlP. destruct llx. discriminate.
      simpl in *. case_eq (passing_predSO_ll lP llx).
        intros Hp. rewrite Hp in *. rewrite HlP in *. destruct llx; discriminate.
      intros beta lbeta Hlbeta. rewrite Hlbeta in *. rewrite <- Hlbeta in *.
      simpl in *. destruct a as [Qm]. destruct P as [Pn].
      case_eq l. intros Hl. rewrite Hl in *. discriminate.
      intros y ly Hl. assert (~ l = nil) as Hlnil.
        rewrite Hl. discriminate.
      rewrite Hl in Hex.
      inversion Hlength as [Hlength'].
      assert (~ lP = nil) as HlPnil.
        rewrite HlP. discriminate.
      case_eq (beq_nat Pn Qm); intros Hbeq.
        rewrite (beq_nat_true _ _ Hbeq) in *. rewrite lem_try10 in *.
        case_eq (P_occurs_in_alpha (passing_conj (passing_predSO_ll lP llx)) (Pred Qm));
            intros Hpocc2.
            apply lemma18 in CM.
            destruct CM as [CM|CM].
              apply (lemma17_pre l (Pred Qm) x _ Iv Ip Ir); try assumption.
                apply is_in_FOvar_app_l in Hin. assumption.

              apply SOt.

              apply (IHlP llx (Pred Qm) x W Iv Ip Ir pa w); try assumption.
                apply is_in_FOvar_app_r in Hin. assumption.
              apply SOt. assumption.
              apply lem10; try assumption.
              apply SOQFree__P. apply SOQFree_passing_predSO_ll.

            rewrite lem1 in CM. rewrite List.app_nil_r in CM.
            apply (lemma17_pre l (Pred Qm) x _ Iv Ip Ir); try assumption.
              apply is_in_FOvar_app_l in Hin. assumption.
              apply SOt. assumption.

        rewrite lem1 in CM. simpl in CM.
        apply P_occurs_in_alpha_conjSO in Hpocc.
        destruct Hpocc. rewrite lem_try35 in *. discriminate.
        intros HH. inversion HH as [HHH]. rewrite HHH in *.
        rewrite <- beq_nat_refl in *. discriminate.

        apply (IHlP llx (Pred Pn) x W Iv Ip Ir pa w); try assumption.
          apply is_in_FOvar_app_r in Hin. assumption.
apply SOt.
apply lem_try35.
intros HH. inversion HH as [HHH]. rewrite HHH in *.
  rewrite <- beq_nat_refl in *. discriminate.
Qed.

Fixpoint atm_passing_predSO_ll_lP  atm : list predicate :=
  match atm with 
  | predSO P x => cons P nil
  | conjSO beta1 beta2 => app (atm_passing_predSO_ll_lP beta1)
                              (atm_passing_predSO_ll_lP beta2)
  | _ => nil
  end.

Fixpoint atm_passing_predSO_ll_llx  atm : list (list FOvariable) :=
  match atm with 
  | predSO P x => cons (cons x nil) nil
  | conjSO beta1 beta2 => app (atm_passing_predSO_ll_llx beta1)
                              (atm_passing_predSO_ll_llx beta2)
  | _ => nil
  end.

Lemma lem118'_length : forall atm,
  AT atm = true ->
length (atm_passing_predSO_ll_lP atm) = length (atm_passing_predSO_ll_llx atm).
Proof.
  induction atm; intros Hat; try discriminate. reflexivity.
  simpl. do 2 rewrite List.app_length. rewrite IHatm1. rewrite IHatm2.
  reflexivity. apply AT_conjSO_r in Hat. assumption.
  apply AT_conjSO_l in Hat. assumption.
Qed.

Lemma lem118'_preds_in : forall atm,
  AT atm = true ->
  preds_in atm = (atm_passing_predSO_ll_lP atm).
Proof.
  induction atm; intros Hat; try discriminate.
    destruct p; destruct f. reflexivity.

    simpl. rewrite IHatm1. rewrite IHatm2.
    reflexivity.
  apply AT_conjSO_r in Hat. assumption.
  apply AT_conjSO_l in Hat. assumption.
Qed.

Lemma passing_predSO_ll_app : forall l1 l2 l3 l4,
  length l1 = length l3 ->
  (passing_predSO_ll (app l1 l2) (app l3 l4)) =
  (app (passing_predSO_ll l1 l3) (passing_predSO_ll l2 l4)).
Proof.
  induction l1; intros l2 l3 l4 Hlength.
    simpl in *. destruct l3. reflexivity. discriminate.

    simpl in *. destruct l3. discriminate. simpl.
    rewrite IHl1. reflexivity. inversion Hlength. reflexivity.
Qed.

Lemma lem118'_not_nil : forall atm1,
AT atm1 = true ->
passing_predSO_ll (atm_passing_predSO_ll_lP atm1) (atm_passing_predSO_ll_llx atm1) <> nil.
Proof.
  induction atm1; intros Hat; try discriminate.
    simpl. rewrite passing_predSO_ll_app.
    intros H. apply app_rnil_l in H. contradiction (IHatm1_1 (AT_conjSO_l _ _ Hat)).
    apply lem118'_length.
    apply AT_conjSO_l in Hat. assumption.
Qed.

Lemma lem118'_equiv : forall atm W Iv Ip Ir,
  AT atm = true ->
  SOturnst W Iv Ip Ir atm <->
  SOturnst W Iv Ip Ir (passing_conj (passing_predSO_ll 
    (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm))).
Proof.
  induction atm; intros  W Iv Ip Ir Hat; try discriminate.    
    destruct p. destruct f. simpl. apply bi_refl.

    simpl.  rewrite passing_predSO_ll_app.
    rewrite passing_conj_app. simpl.
    pose proof (AT_conjSO_l _ _ Hat) as Hat1.
    pose proof (AT_conjSO_r _ _ Hat) as Hat2.
    split; intros SOt; apply conj.
      apply IHatm1. assumption.  apply SOt.

      apply IHatm2. assumption. apply SOt.

      apply IHatm1. assumption.  apply SOt.

      apply IHatm2. assumption. apply SOt.

      apply lem118'_not_nil. apply AT_conjSO_l in Hat.
      assumption.
      apply lem118'_not_nil. apply AT_conjSO_r in Hat.
      assumption.
      apply lem118'_length. apply AT_conjSO_l in Hat.
      assumption.
Qed.

Lemma fun2_passing_conj_app : forall l1 l2 P,
  fun2 (passing_conj (app l1 l2)) P =
  app (fun2 (passing_conj l1) P) (fun2 (passing_conj l2) P).
Proof.
  induction l1; intros l2 P.
    simpl. reflexivity.

    simpl. case_eq l1. intros Hl1. simpl. destruct l2. simpl.
      rewrite List.app_nil_r. reflexivity.

      simpl in *. reflexivity.

      intros beta lbeta Hlbeta. rewrite <- Hlbeta.
      case_eq (app l1 l2). intros Hnil.
        rewrite Hlbeta in *. discriminate.

        intros gamma lgamma Hlgamma. rewrite <- Hlgamma.
        simpl. rewrite IHl1. rewrite app_assoc. reflexivity.
Qed.

Lemma fun2_atm_passing_predSO_ll_nil : forall atm1 P,
  AT atm1 = true ->
  ((fun2
     (passing_conj
        (passing_predSO_ll (atm_passing_predSO_ll_lP atm1)
           (atm_passing_predSO_ll_llx atm1))) P) = nil) <->
  (fun2 atm1 P = nil).
Proof.
  induction atm1; intros [Pn] Hat; try discriminate.
    destruct p as [Qm]. destruct f as [xn].
    simpl in *. apply bi_refl.

    simpl. 
    pose proof (AT_conjSO_l _ _ Hat) as H1.
    pose proof (AT_conjSO_r _ _ Hat) as H2.
    destruct  (IHatm1_1 (Pred Pn) H1) as [Ha Hb].
    destruct  (IHatm1_2 (Pred Pn) H2) as [Hc Hd].
    rewrite passing_predSO_ll_app.
    rewrite fun2_passing_conj_app.
    simpl. split; intros H. 
      rewrite Ha. rewrite Hc. reflexivity.
        apply app_rnil_r in H. assumption.
        apply app_rnil_l in H. assumption.

      rewrite Hb. rewrite Hd. reflexivity.
        apply app_rnil_r in H. assumption.
        apply app_rnil_l in H. assumption.

        apply lem118'_length. apply AT_conjSO_l in Hat. assumption.
Qed.


Lemma lem118'_CM_pa2_l_gen : forall atm P x (W : Set) (Iv : FOvariable -> W) w,
  AT atm = true ->
  CM_pa2_l_gen Iv (fun2 atm P) x w ->
  CM_pa2_l_gen Iv  (fun2 ( (passing_conj
           (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm)))) P)  
              x w.
Proof.
  induction atm; intros [Pn] [xn] W Iv w Hat H; try discriminate.
    destruct p as [Qm]. destruct f as [ym]. simpl in *. assumption.

    simpl in *. rewrite passing_predSO_ll_app.
    rewrite fun2_passing_conj_app.
    pose proof (AT_conjSO_l _ _ Hat) as H1.
    pose proof (AT_conjSO_r _ _ Hat) as H2.
    case_eq (fun2 atm1 (Pred Pn)).
      intros Hf. rewrite Hf in *. simpl in *.
      apply fun2_atm_passing_predSO_ll_nil in Hf. rewrite Hf.
      simpl.
      case_eq (fun2 atm2 (Pred Pn)).
        intros Hf'. rewrite Hf' in *. simpl in *.
        apply fun2_atm_passing_predSO_ll_nil in Hf'. rewrite Hf'.
        all : try assumption.

        intros x lx Hlx.
        apply IHatm2; assumption.

      intros x lx Hlx. 
      case_eq (fun2 atm2 (Pred Pn)).
        intros Hf'. rewrite Hf' in *. 
        apply fun2_atm_passing_predSO_ll_nil in Hf'. rewrite Hf'.
        rewrite List.app_nil_r in *.
(*         rewrite List.app_nil_r in H. *)
        all : try assumption. apply IHatm1; try assumption.

        intros y ly Hly.
        apply lemma18.
        intros HH.
        apply fun2_atm_passing_predSO_ll_nil with (atm1 := atm1) in HH.
        rewrite HH in *. discriminate. all : try assumption.

        intros HH.
        apply fun2_atm_passing_predSO_ll_nil with (atm1 := atm2) in HH.
        rewrite HH in *. discriminate. all : try assumption.

        apply lemma18 in H. destruct H as [H|H]; [left|right].
          apply IHatm1; assumption.
          apply IHatm2; assumption.

          rewrite Hlx. discriminate.
          rewrite Hly. discriminate.
          rewrite lem118'_length.
          reflexivity.
          apply AT_conjSO_l in Hat. assumption.
Qed.

Lemma lem118'_not_nil_lP : forall atm,
  AT atm = true ->
  ~ atm_passing_predSO_ll_lP atm = nil.
Proof.
  induction atm; try discriminate.
  intros H.
  simpl. intros H2.
  apply app_rnil_l in H2. apply IHatm1.
    apply AT_conjSO_l in H. assumption.
    assumption.
Qed.

Lemma lem118'_not_nil_llx : forall atm,
  AT atm = true ->
  ~ atm_passing_predSO_ll_llx atm = nil.
Proof.
  induction atm; try discriminate.
  intros H.
  simpl. intros H2.
  apply app_rnil_l in H2. apply IHatm1.
    apply AT_conjSO_l in H. assumption.
    assumption.
Qed.

    
Lemma ex_nil_in_llv_app_f : forall l1 l2,
  ex_nil_in_llv (app l1 l2) = false <->
  ex_nil_in_llv l1 = false /\
  ex_nil_in_llv l2 = false.
Proof.
  induction l1; intros l2.
    simpl. split; intros H.
      apply conj. reflexivity.
        assumption.
      apply H.

    simpl. destruct a. split; intros H.
      discriminate. destruct H. discriminate.

      apply IHl1.
Qed.

Lemma lem118'_ex_nil_in_llv : forall atm,
  AT atm = true ->
  ex_nil_in_llv (atm_passing_predSO_ll_llx atm) = false.
Proof.
  induction atm; try (discriminate); intros Hat.
    reflexivity.

    simpl. apply ex_nil_in_llv_app_f. apply conj.
    apply IHatm1. apply AT_conjSO_l in Hat. assumption.
    apply IHatm2. apply AT_conjSO_r in Hat. assumption.
Qed.

Lemma P_occurs_in_alpha_passing_conj_app_f : forall l1 l2 P,
  ~ l1 = nil ->
  ~ l2 = nil ->
  P_occurs_in_alpha (passing_conj (app l1 l2)) P = false <->
  P_occurs_in_alpha (passing_conj l1) P = false /\
  P_occurs_in_alpha (passing_conj l2) P = false.
Proof. 
  induction l1; intros l2 P H1 H2. simpl.
    contradiction (H1 eq_refl).

    simpl. case_eq l1.
      intros Hl1. simpl. case_eq l2.
        intros Hl2. simpl. split; intros H.
          apply conj. assumption. unfold P_occurs_in_alpha.
            reflexivity.
          apply H.

        intros beta lbeta Hl2. rewrite <- Hl2. split; intros H.
          apply P_occurs_in_alpha_conjSO_f in H. assumption. 
          apply P_occurs_in_alpha_conjSO_f in H. assumption. 

      intros d ld Hl1. rewrite <- Hl1.
      assert (~ l1 = nil) as Hnil.
        rewrite Hl1. discriminate.
      case_eq (app l1 l2). intros Hl12. rewrite Hl1 in Hl12.
        discriminate.
      intros e le Hl12. rewrite <- Hl12.
      split; intros H.
        apply P_occurs_in_alpha_conjSO_f in H.
        destruct H as [Ha Hb].
        apply IHl1 in Hb. destruct Hb as [Hb1 Hb2].
        apply conj. apply P_occurs_in_alpha_conjSO_f.
          apply conj. all : try assumption.

        destruct H as [Ha Hb].
        apply P_occurs_in_alpha_conjSO_f in Ha.
        destruct Ha as [Ha1 Ha2].
        apply P_occurs_in_alpha_conjSO_f.
        apply conj. assumption. apply IHl1.
        all : try assumption.

        apply conj; assumption.
Qed.

Lemma P_occurs_in_alpha_passing_conj_app : forall l1 l2 P,
  ~ l1 = nil ->
  ~ l2 = nil ->
  P_occurs_in_alpha (passing_conj (app l1 l2)) P = true <->
  P_occurs_in_alpha (passing_conj l1) P = true \/
  P_occurs_in_alpha (passing_conj l2) P = true.
Proof. 
  induction l1; intros l2 P H1 H2. simpl.
    contradiction (H1 eq_refl).

    case_eq l1. intros Hl1. rewrite Hl1 in *.
      simpl. case_eq l2. intros Hl2. rewrite Hl2 in *.
        contradiction (H2 eq_refl).
      intros beta lbeta Hl2. rewrite <- Hl2.
      rewrite P_occurs_in_alpha_conjSO. apply bi_refl.

      intros beta lbeta Hl1. rewrite <- Hl1.
      simpl. case_eq (app l1 l2). intros Hl.
      rewrite Hl1 in *. discriminate.
      intros beta2 lbeta2 Hlbeta2. rewrite <- Hlbeta2.
      assert (~ l1 = nil) as Hnil1.
        rewrite Hl1. discriminate.
      rewrite Hl1. rewrite <- Hl1.
      rewrite P_occurs_in_alpha_conjSO.
      rewrite P_occurs_in_alpha_conjSO.
      split; intros H. destruct H.
        left. left. assumption.
        apply IHl1 in H. destruct H.
          left. right. assumption.

          right. assumption.

        all : try assumption.

      destruct H. destruct H.
        left. assumption.
        right. apply IHl1; try assumption.
        left. assumption.
        right. apply IHl1; try assumption.
        right. assumption.
Qed.

Lemma lem118'_P_occurs_in_alpha_gen : forall atm P,
AT atm = true ->
P_occurs_in_alpha atm P = 
P_occurs_in_alpha
  (passing_conj
     (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm)))
  P .
Proof.
  induction atm; intros [Pn] Hat; try discriminate.
    reflexivity.

    pose proof (AT_conjSO_l _ _ Hat) as Hat1.
    pose proof (AT_conjSO_r _ _ Hat) as Hat2.
    simpl. case_eq (P_occurs_in_alpha (conjSO atm1 atm2) (Pred Pn));  
      intros Hpocc.
      apply P_occurs_in_alpha_conjSO in Hpocc.
    rewrite passing_predSO_ll_app. symmetry.
    apply P_occurs_in_alpha_passing_conj_app.
      apply lem118'_not_nil. assumption.
      apply lem118'_not_nil. assumption.

      destruct Hpocc. rewrite IHatm1 in H. left. all : try assumption.
      rewrite IHatm2 in H. right. all : try assumption.

      apply lem118'_length. apply AT_conjSO_l in Hat.
      assumption.

      apply P_occurs_in_alpha_conjSO_f in Hpocc. symmetry.
      destruct Hpocc as [Hp1 Hp2]. rewrite IHatm1 in Hp1.
      rewrite IHatm2 in Hp2.
    rewrite passing_predSO_ll_app. 
    apply P_occurs_in_alpha_passing_conj_app_f.
      apply lem118'_not_nil. assumption.
      apply lem118'_not_nil. assumption.
    apply conj; assumption.
    
      apply lem118'_length. all : assumption.

Qed.

Lemma lem118'_P_occurs_in_alpha : forall atm P,
AT atm = true ->
P_occurs_in_alpha atm P = true ->
P_occurs_in_alpha
  (passing_conj
     (passing_predSO_ll (atm_passing_predSO_ll_lP atm) (atm_passing_predSO_ll_llx atm)))
  P = true.
Proof.
  induction atm; intros [Pn] Hat Hpocc; try discriminate.
    simpl in *. assumption.

    simpl. apply P_occurs_in_alpha_conjSO in Hpocc.
    rewrite passing_predSO_ll_app.
    apply P_occurs_in_alpha_passing_conj_app.
      apply lem118'_not_nil. apply AT_conjSO_l in Hat. assumption.
      apply lem118'_not_nil. apply AT_conjSO_r in Hat. assumption.

      destruct Hpocc. apply IHatm1 in H. left. assumption.
        apply AT_conjSO_l in Hat. assumption.
      apply IHatm2 in H. right. assumption.
        apply AT_conjSO_r in Hat. assumption.

      apply lem118'_length. apply AT_conjSO_l in Hat.
      assumption.
Qed.

Lemma is_in_FOvar_atm_passing_predSO_ll : forall atm P x,
  AT atm = true ->
  is_in_FOvar x (fun2 atm P) = false ->
  is_in_FOvar x (fun2 (passing_conj (passing_predSO_ll
      (atm_passing_predSO_ll_lP atm) 
      (atm_passing_predSO_ll_llx atm))) P) = false.
Proof.
  induction atm; intros [Pn] [xn] Hat Hin; try discriminate.
    destruct p as [Qm]. destruct f as [ym].
    simpl in *. assumption.

    simpl. rewrite passing_predSO_ll_app. rewrite fun2_passing_conj_app.
    rewrite is_in_FOvar_app in *. simpl in Hin.
    rewrite is_in_FOvar_app in Hin.
    case_eq (is_in_FOvar (Var xn) (fun2 atm1 (Pred Pn)));
      intros Hin1; rewrite Hin1 in *. discriminate.
    rewrite IHatm1. apply IHatm2. all : try assumption.
    apply AT_conjSO_r in Hat. assumption.
    apply AT_conjSO_l in Hat. assumption.
    apply lem118'_length. apply AT_conjSO_l in Hat. assumption.
Qed.

Lemma lemma17' : forall atm P x W Iv Ip Ir pa w,
  AT atm = true ->
  P_occurs_in_alpha atm P = true ->
  is_in_FOvar x (fun2 atm P) = false ->
  SOturnst W Iv (altered_Ip Ip pa P) Ir atm ->
  CM_pa2_l_gen Iv (fun2 atm P) x w ->
  pa w.
Proof.
  intros atm P x W Iv Ip Ir pa w Hat Hpocc Hin SOt CM.
  apply lem118'_equiv in SOt.
  apply lem118'_CM_pa2_l_gen in CM.
  apply (lemma17_again) with (Ip := Ip) (Ir := Ir) (pa := pa) in CM.
  assumption.
  apply lem118'_not_nil_lP. assumption.
  apply lem118'_length. assumption.
  apply lem118'_ex_nil_in_llv. assumption.



  apply is_in_FOvar_atm_passing_predSO_ll with (P := P); assumption.
  apply lem118'_P_occurs_in_alpha; assumption.
  all : assumption.
Qed.


Lemma P_occurs_in_rel : forall rel P,
  REL rel = true ->
  P_occurs_in_alpha rel P = false.
Proof.
  induction rel; intros P Hrel; try discriminate.
    destruct f. destruct f0. unfold P_occurs_in_alpha.
    reflexivity.

    pose proof (REL_conjSO_l _ _ Hrel).
    pose proof (REL_conjSO_r _ _ Hrel).
    apply P_occurs_in_alpha_conjSO_f. apply conj.
    apply IHrel1. assumption.
    apply IHrel2. assumption.
Qed.

Lemma preds_in_passing_conj_app : forall l1 l2,
  preds_in (passing_conj (app l1 l2)) =
  app (preds_in (passing_conj l1)) (preds_in (passing_conj l2)).
Proof.
  induction l1; intros l2. reflexivity.
  simpl. case_eq l1. intros Hl1. simpl.
    destruct l2. simpl. rewrite List.app_nil_r. reflexivity.
    simpl. reflexivity.

    intros beta lbeta Hl1. rewrite <- Hl1.
    simpl. case_eq (app l1 l2).
      rewrite Hl1. discriminate.
    intros d ld Hl12. rewrite <- Hl12.
    simpl. rewrite IHl1. rewrite app_assoc.
    reflexivity.
Qed.

Lemma lemma_try4 : forall lP alpha P x W Iv Ip w,
  P_occurs_in_l lP P = true ->
  @altered_Ip_list W Ip 
    (vsS_pa_l Iv (FOv_att_P_l alpha lP) (list_Var (length lP) x)) lP P w =
  altered_Ip Ip (CM_pa2_l_gen Iv (fun2 alpha P) x) P P w.
Proof.
  induction lP; intros alpha P x W Iv Ip w Hpocc.
    simpl in *. discriminate.

    simpl in  *. destruct P as [Pn]. destruct a as [Qm].
    simpl. rewrite <- beq_nat_refl. rewrite beq_nat_comm.
    case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *.
      rewrite (beq_nat_true _ _ Hbeq).
      reflexivity.

      rewrite IHlP. simpl. rewrite <- beq_nat_refl.
      reflexivity. assumption.
Qed.


(* Fixpoint at_gen {A : Type} {a : A} (n : nat) (l : list A) : A :=
  match n, l with 
  | 0, _ => a
  | _, nil => a
  | 1, (cons a l) => a
  | (S m), (cons _ l) => @at_gen A a m l
  end.

Fixpoint ind_gen {A : Type} {a : A} (l : list nat) (lx : list A) : list A :=
  match l with
  | nil => nil
  | cons n l' => cons (@at_gen A a n lx) (@ind_gen A a l' lx)
  end.

Definition consistent_lP_lpa_P {W : Set} {pa} lP lpa P : Prop :=
  is_constant (@ind_gen (W -> Prop) pa (indicies_l2 lP P) lpa).

Definition consistent_lP_lpa {W : Set} {pa} lP lpa : Prop :=
  forall P, @consistent_lP_lpa_P W pa lP lpa P. *)


(* Lemma ind_gen_pre_cons : forall {A : Type} lP P n (pa pa2 : A) lpa,
  @ind_gen A pa2 (indicies_l2_pre lP P (S n)) (cons pa lpa) =
  @ind_gen A pa2 (indicies_l2_pre lP P n) lpa.
Proof.
  induction lP; intros P n pa lpa.
    simpl. reflexivity.

    destruct a as [Qm]. destruct P as [Pn]. simpl.
    destruct n; intros lpa2;
    case_eq (beq_nat Pn Qm); intros Hbeq; simpl; try (rewrite IHlP;
      reflexivity).
Qed.

Lemma consistent_lP_lpa_P_cons_rem : forall lP P Q W lpa pa1 pa0,
  @consistent_lP_lpa_P W pa0 (cons P lP) (cons pa1 lpa) Q ->
  @consistent_lP_lpa_P W pa0 lP lpa Q.
Proof.
  unfold consistent_lP_lpa_P.
  unfold indicies_l2.
  intros lP [Pn] [Qm] W lpa pa1 p0.
  simpl.
  case_eq (beq_nat Qm Pn); intros Hbeq. simpl.
    rewrite ind_gen_pre_cons. unfold is_constant.
    intros [pa2 [n H]]. destruct n. discriminate.
    simpl in H. inversion H as [H'].
    exists pa2. exists n. assumption.

    rewrite ind_gen_pre_cons. intros. assumption.
Qed.

Lemma consistent_lP_lpa_cons_rem : forall lP P W lpa pa1 pa0,
  @consistent_lP_lpa W pa0 (cons P lP) (cons pa1 lpa) ->
  @consistent_lP_lpa W pa0 lP lpa.
Proof.
  unfold consistent_lP_lpa.
  intros until 0. intros H Q.
  specialize (H Q).
  apply consistent_lP_lpa_P_cons_rem in H.
  assumption.
Qed. *)


Fixpoint fun_change {A : Type} (l : list A) (n : nat) (a : A) :=
  match l, n with
  | nil, _ => nil
  | l, 0 => l
  | cons b l', 1 => cons a l'
  | cons b l', S m => cons b (fun_change l' m a)
  end.

Fixpoint fun_change_ln {A : Type} (l : list A) (ln : list nat) (a : A) :=
  match ln with
  | nil => l
  | cons n ln' => fun_change (fun_change_ln l ln' a) n a
  end.

Lemma fun_change_ln_nil : forall W l pa,
  @fun_change_ln W nil l pa = nil.
Proof.
  induction l; intros pa. reflexivity.
  simpl. rewrite IHl. reflexivity.
Qed.

Lemma fun_change_ln_cons_n : forall  lP n P (W : Set) lpa (pa pa2 : W -> Prop),
   ~ lP = nil -> 
  fun_change_ln (cons pa lpa) (indicies_l2_pre lP P (S n)) pa2 =
  cons pa (fun_change_ln lpa (indicies_l2_pre lP P n) pa2).
Proof.
  induction lP; intros n P W lpa pa pa2 Hnil.
     contradiction (Hnil eq_refl). 

    simpl. destruct P as [Pn]. destruct a as [Qm].
    case_eq lP. intros HlP. simpl;
      case_eq (beq_nat Pn Qm); intros Hbeq; try reflexivity.

      intros T lT HlT. rewrite <- HlT.
      assert (~ lP = nil) as Hnil2.
        rewrite HlT. discriminate.
      case_eq (beq_nat Pn Qm); intros Hbeq.
        simpl. rewrite IHlP. reflexivity. assumption.

        apply IHlP. assumption.
Qed.

Lemma lem_a2 : forall lP P Q W Ip pa lpa',
~ P = Q ->
@altered_Ip_list W Ip (fun_change_ln lpa' (indicies_l2 lP P) pa) lP Q
 = altered_Ip_list Ip lpa' lP Q.
Proof.
  induction lP; intros [Pn] [Qm] W Ip pa lpa' Hneq.
    simpl in *. reflexivity.

    destruct a as [Rn].
    unfold indicies_l2. simpl.
    destruct lpa'. simpl.
      rewrite fun_change_ln_nil. simpl. reflexivity.
    rename P into pa2.
    simpl.
    case_eq (beq_nat Pn Rn); intros Hbeq.
      simpl.
      case_eq (beq_nat Rn Qm); intros Hbeq2.
        rewrite (beq_nat_true _ _ Hbeq2) in *.
        apply neq_beq_nat in Hneq. rewrite Hbeq in Hneq. discriminate.
      case_eq lP. intros HlP. simpl. rewrite Hbeq2. reflexivity.
      intros U lU HlU. rewrite <- HlU.
      assert (~ lP = nil) as Hnil2.
        rewrite HlU. discriminate.
      rewrite <- IHlP with (P := (Pred Pn)) (pa := pa).
        rewrite fun_change_ln_cons_n. simpl. 
        rewrite Hbeq2. reflexivity. all : try assumption.

      case_eq lP. intros HlP.
        simpl. reflexivity.
      intros U lU HlU. rewrite <- HlU.
      rewrite fun_change_ln_cons_n. simpl. 
      case_eq (beq_nat Rn Qm); intros Hbeq2.
        reflexivity.
      unfold indicies_l2 in IHlP. apply IHlP.
      assumption.

      rewrite HlU. discriminate.
Qed.

Lemma lem_a1 : forall lP P W Ip pa lpa',
@altered_Ip W (altered_Ip_list Ip lpa' lP) pa P =
altered_Ip (altered_Ip_list Ip (fun_change_ln lpa' (indicies_l2 lP P) pa) lP)
  pa P.
Proof.
  intros.
  apply functional_extensionality. intros [Qm].
  destruct P as [Pn]. simpl. case_eq (beq_nat Pn Qm);
    intros Hbeq. reflexivity.

    symmetry. apply lem_a2.
    intros H. inversion H as [H'].
    rewrite H' in *. rewrite <- beq_nat_refl in *.
    discriminate.
Qed.

Lemma consistent_lP_lpa_P_nil_l : forall (W : Set) l P pa,
  @consistent_lP_lpa_P W pa nil l P.
Proof.
  intros W. unfold consistent_lP_lpa_P.
  unfold indicies_l2. simpl. intros.
  apply is_constant_nil. assumption.
Qed.

Lemma consistent_lP_lpa_nil_l : forall (W : Set) l pa,
  @consistent_lP_lpa W pa nil l.
Proof.
  unfold consistent_lP_lpa.
  intros W l pa P.
  apply consistent_lP_lpa_P_nil_l.
Qed.

Lemma lem_a7 : forall (lP : list predicate) (W : Set) (lpa : list (W -> Prop)) (pa pa2 : W -> Prop)
  (P Q : predicate),
~ P = Q ->
@is_constant (W -> Prop)
  (@ind_gen (W -> Prop) pa2 (indicies_l2 (P :: lP) Q)
     (@fun_change_ln (W -> Prop) (pa :: lpa) (indicies_l2 (P :: lP) P) pa)) <->
@is_constant (W -> Prop)
  (@ind_gen (W -> Prop) pa2 (indicies_l2 lP Q)
     (@fun_change_ln (W -> Prop) lpa (indicies_l2 lP P) pa)).
Proof.
  unfold is_constant. unfold indicies_l2.
  intros lP W lpa pa pa2 [Pn] [Qm] Hneq.
  split; intros H.
    destruct H as [a [ n H]].
    simpl in H.
    rewrite <- beq_nat_refl in *. simpl in *.
      case_eq lP.
        intros HlP. rewrite HlP in *.
        simpl in *. exists a. exists 0. reflexivity.
      intros T lT HlP. rewrite <- HlP.
      assert (~ lP = nil) as HH.
        rewrite HlP. discriminate.
    rewrite fun_change_ln_cons_n in H.
    simpl in H. 
    case_eq (beq_nat Qm Pn); intros Hbeq;
      rewrite Hbeq in *.
      destruct n. discriminate.
      simpl in H. inversion H as [[Ha Heq]].
      rewrite <- Ha in *.
      exists pa. exists n.
      rewrite ind_gen_pre_cons in Heq. assumption.

      rewrite ind_gen_pre_cons in H. exists a. exists n.
      all: try assumption. 

    destruct H as [a [ n H]].
    simpl.
    rewrite <- beq_nat_refl in *. simpl in *.
      case_eq lP.
        intros HlP. rewrite HlP in *.
        simpl in *. exists a. exists 0.
        rewrite beq_nat_comm.
        rewrite neq_beq_nat.
        reflexivity. assumption.
      intros T lT HlP. rewrite <- HlP.
      assert (~ lP = nil) as HH.
        rewrite HlP. discriminate.

    rewrite fun_change_ln_cons_n.
    simpl. 
    case_eq (beq_nat Qm Pn); intros Hbeq.
      apply neq_beq_nat in Hneq. rewrite beq_nat_comm in Hbeq.
      rewrite Hbeq in *. discriminate.
      exists a. exists n. 
      rewrite ind_gen_pre_cons. all : assumption.
Qed.

Lemma length_indicies_l2_pre : forall lP n m P,
  length (indicies_l2_pre lP P n) = 
  length (indicies_l2_pre lP P m).
Proof.
  induction lP; intros n m [Pn]. reflexivity.
  simpl. destruct a as [Qm]. case_eq (beq_nat Pn Qm); intros Hbeq.
    simpl. rewrite IHlP with (m := (S m)). reflexivity.

    apply IHlP.
Qed.

Lemma lem_a8_eq : forall (lP : list predicate) (W : Set) (lpa : list (W -> Prop)) (pa pa2 : W -> Prop)
  (P : predicate),
  length lP = length lpa ->
  (@ind_gen (W -> Prop) pa2 (indicies_l2 lP P)
     (@fun_change_ln (W -> Prop) lpa (indicies_l2 lP P) pa)) = 
    constant_l pa (length (indicies_l2 lP P)).
Proof.
  unfold indicies_l2.
  induction lP; intros W lpa pa p2 [Pn] Hlength. reflexivity.
  simpl. destruct a as [Qm].
  case_eq lP.
    intros HlP. simpl.
    case_eq (beq_nat Pn Qm); intros Hbeq.
      simpl. destruct lpa. discriminate.
      simpl. all : try reflexivity.
  intros PP lPP HlP.
  rewrite <- HlP.
  assert (~ lP = nil) as HH.
    rewrite HlP. discriminate.
  case_eq (beq_nat Pn Qm); intros Hbeq. simpl in *.
    destruct lpa. discriminate.
    simpl. rewrite fun_change_ln_cons_n. simpl.

    rewrite ind_gen_pre_cons. rewrite IHlP.
    rewrite length_indicies_l2_pre with (m := 1).
    reflexivity.

    inversion Hlength. reflexivity.

    assumption.

    destruct lpa. discriminate.
    simpl. rewrite fun_change_ln_cons_n.
    rewrite ind_gen_pre_cons. rewrite IHlP. 
    rewrite length_indicies_l2_pre with (m := 1).
      reflexivity.

    inversion Hlength. reflexivity.

    assumption.
Qed.

Lemma lem_a8 : forall (lP : list predicate) (W : Set) a n (lpa : list (W -> Prop)) (pa pa2 : W -> Prop)
  (P Q : predicate),
~ P = Q ->
 (@ind_gen (W -> Prop) pa2 (indicies_l2_pre lP Q 0) lpa) = constant_l a n ->
  (@ind_gen (W -> Prop) pa2 (indicies_l2 lP Q)
     (@fun_change_ln (W -> Prop) lpa (indicies_l2 lP P) pa)) = constant_l a n.
Proof.
  induction lP; intros W b n lpa pa pa2 [Pn] [Qm] Hneq Hn.
    simpl in *. assumption.

    unfold indicies_l2 in *.
    destruct a as [Rn]. simpl in *.
    case_eq lP. intros HlP; rewrite HlP in *. 
      simpl in *.
      case_eq (beq_nat Qm Rn); intros Hbeq;
        rewrite Hbeq in *.
        case_eq (beq_nat Pn Rn); intros Hbeq2.
          rewrite (beq_nat_true _ _ Hbeq2) in *.
          rewrite (beq_nat_true _ _ Hbeq) in *.
          contradiction (Hneq eq_refl).

          destruct lpa. simpl in *. assumption.
          simpl in *. assumption.

      case_eq (beq_nat Pn Rn); intros Hbeq2;  
        simpl in *; assumption.

    intros PP lPP HlP. rewrite <- HlP.
    assert (~ lP = nil) as HlPnil.
      rewrite HlP. discriminate.        
    case_eq (beq_nat Qm Rn); intros Hbeq; rewrite Hbeq in *.
      simpl in *. case_eq lpa. intros Hlpa. rewrite Hlpa in *.
      rewrite fun_change_ln_nil. assumption.

      intros pa3 lpa3 Hlpa. rewrite <- Hlpa.
      case_eq (beq_nat Pn Rn); intros Hbeq2.
        rewrite (beq_nat_true _ _ Hbeq2) in *. 
        rewrite (beq_nat_true _ _ Hbeq) in *.
        contradiction (Hneq eq_refl).

        rewrite Hlpa. simpl.
        rewrite fun_change_ln_cons_n. simpl.
        rewrite Hlpa in Hn. rewrite ind_gen_pre_cons in Hn.
        rewrite ind_gen_pre_cons. destruct n. simpl in *. discriminate.
        rewrite IHlP with (a := b) (n := n). inversion Hn as [[H1 H2]].
        rewrite H2. reflexivity.
all : try assumption. inversion Hn. reflexivity.

      simpl in *. case_eq lpa. intros Hlpa. rewrite Hlpa in *.
      rewrite fun_change_ln_nil. assumption.

      intros pa3 lpa3 Hlpa. rewrite <- Hlpa.
      case_eq (beq_nat Pn Rn); intros Hbeq2.
        simpl. rewrite Hlpa in *. simpl in *.
        rewrite fun_change_ln_cons_n in *. simpl.
        rewrite ind_gen_pre_cons in *.
        rewrite ind_gen_pre_cons in Hn.
        rewrite IHlP with (a := b) (n := n).
        reflexivity. all : try assumption.

        rewrite Hlpa in *. rewrite fun_change_ln_cons_n.
        rewrite ind_gen_pre_cons.
        rewrite ind_gen_pre_cons in Hn.
        apply IHlP. all : assumption.
Qed.

Lemma lem_a10 : forall (lP : list predicate) (W : Set) (lpa : list (W -> Prop)) (pa pa2 : W -> Prop)
  (P Q : predicate),
~ P = Q ->
@is_constant (W -> Prop) (@ind_gen (W -> Prop) pa2 (indicies_l2_pre lP Q 0) lpa) ->
@is_constant (W -> Prop)
  (@ind_gen (W -> Prop) pa2 (indicies_l2 lP Q)
     (@fun_change_ln (W -> Prop) lpa (indicies_l2 lP P) pa)).
Proof.
  unfold is_constant. intros until 0. intros Hneq Hcon.
  destruct Hcon as [a [n H]].
  exists a. exists n. apply lem_a8; assumption.
Qed.

Lemma lem_a10_eq : forall (lP : list predicate) (W : Set) (lpa : list (W -> Prop)) (pa pa2 : W -> Prop)
  (P : predicate),
  length lP = length lpa ->
@is_constant (W -> Prop)
  (@ind_gen (W -> Prop) pa2 (indicies_l2 lP P)
     (@fun_change_ln (W -> Prop) lpa (indicies_l2 lP P) pa)).
Proof.
  unfold is_constant. intros until 0. intros Hlength.
  exists pa. exists (length (indicies_l2 lP P)).
  unfold indicies_l2. apply lem_a8_eq.
  assumption.
Qed.

Lemma lem_a6 : forall (lP : list predicate) (W : Set) (lpa : list (W -> Prop)) (pa pa2 : W -> Prop)
  (P Q : predicate),
~ P = Q ->
@is_constant (W -> Prop) (@ind_gen (W -> Prop) pa2 (indicies_l2 lP Q) lpa) ->
@is_constant (W -> Prop)
  (@ind_gen (W -> Prop) pa2 (indicies_l2 (P :: lP) Q)
     (@fun_change_ln (W -> Prop) (pa :: lpa) (indicies_l2 (P :: lP) P) pa)).
Proof.
  unfold indicies_l2.
  intros. apply lem_a7. assumption.
  apply lem_a10; assumption.
Qed.

Lemma lem_a5 : forall lP W lpa pa pa2 P Q,
length lP = length lpa ->
@consistent_lP_lpa_P W pa2 lP lpa Q ->
@consistent_lP_lpa_P W pa2 (P :: lP) 
  (@fun_change_ln (W -> Prop) (cons pa lpa) (indicies_l2 (cons P lP) P) pa) Q.
Proof.
  unfold consistent_lP_lpa_P. intros until 0. intros Hlength Hcon.
  destruct P as [Pn]. destruct Q as [Qm].
  case_eq (beq_nat Pn Qm); intros Hbeq.
    rewrite (beq_nat_true _ _ Hbeq) in *.
    simpl.
    apply lem_a10_eq. simpl. rewrite Hlength.
    reflexivity.

  apply lem_a6.
  intros H. inversion H as [H']. rewrite H' in *.
  rewrite <- beq_nat_refl in Hbeq. discriminate.
  assumption.
Qed.

Lemma lem_a4 : forall lP W lpa pa pa2 P,
length lP = length lpa ->
@consistent_lP_lpa W pa2 lP lpa ->
@consistent_lP_lpa W pa2 (P :: lP)
  (@fun_change_ln (W -> Prop) (cons pa lpa) (indicies_l2 (cons P lP) P) pa).
Proof.
  unfold consistent_lP_lpa.
  intros until 0. intros H1 H2 Q. apply lem_a5. assumption.
  apply H2.
Qed.

Lemma lem_a11 : forall lP P (W : Set) lpa pa pa2,
(@fun_change_ln (W -> Prop) (cons pa lpa) (indicies_l2 (cons P lP) P) pa2) =
(cons pa2 (@fun_change_ln (W -> Prop) lpa (indicies_l2 lP P) pa2)).
Proof.
  intros. unfold indicies_l2. destruct P as [Pn].
  simpl. rewrite <- beq_nat_refl. simpl.
  destruct lP. simpl. reflexivity.
  rewrite fun_change_ln_cons_n. simpl. reflexivity.
  discriminate.
Qed.


Lemma length_fun_change : forall (W : Set) l n pa,
  length (@fun_change (W -> Prop) l n pa) = length l.
Proof.
 induction l; intros n pa. reflexivity.
  simpl. destruct n. reflexivity.
  destruct n. reflexivity.
  simpl. rewrite IHl. reflexivity.
Qed.

Lemma length_fun_change_ln : forall (W : Set) ln lpa pa,
  length (@fun_change_ln (W -> Prop) lpa ln pa) =
  length lpa.
Proof.
  induction ln; intros lpa pa. reflexivity.
  simpl. rewrite length_fun_change. apply IHln.
Qed. 

Lemma altered_Ip_list_consistent_lP_lpa' : forall lP (W : Set) Ip lpa pa2,
  length lP = length lpa ->
  exists lpa',
    @consistent_lP_lpa W pa2 lP lpa' /\
    length lP = length lpa' /\
    altered_Ip_list Ip lpa lP =
    altered_Ip_list Ip lpa' lP.
Proof.
  induction lP; intros W Ip lpa pa2 Hlength.
    exists nil. simpl. apply conj.
      apply consistent_lP_lpa_nil_l.
      apply conj. reflexivity.

      apply altered_Ip_list_nil.

    destruct lpa. discriminate.
    simpl. destruct (IHlP W Ip lpa pa2) as [lpa' [Hcon [Hl Halt]]].
inversion Hlength. reflexivity.
    rewrite Halt.
    rename P into pa. rename a into P.
    exists (cons pa (fun_change_ln lpa' (indicies_l2 lP P) pa)).
    simpl. apply conj.
      rewrite <- lem_a11 with (pa := pa).
      apply lem_a4. inversion Hlength. assumption.
      assumption.

      apply conj.
pose proof length_fun_change_ln. 
        rewrite length_fun_change_ln. rewrite Hl. reflexivity.

      apply lem_a1.
Qed.

Lemma lem_a15_pre_pre_pre_pre_pre_stronger : forall l P Q R W lpa2 pa pa0 pa1 pa2 n,
  @ind_gen (W -> Prop) pa2 (indicies_l2 (cons P (cons Q l)) R) (cons pa0 (cons pa1 lpa2)) = constant_l pa n ->
  @ind_gen _ pa2 (indicies_l2 (cons Q (cons P l)) R) (cons pa1 (cons pa0 lpa2)) = constant_l pa n.
Proof.
  unfold indicies_l2.
  intros l [Pn] [Qm] [Rn] W lpa2 pa pa0 pa1 pa2 n  H.
    simpl in *. case_eq (beq_nat Rn Qm); intros Hbeq;
      rewrite Hbeq in *.
      case_eq (beq_nat Rn Pn); intros Hbeq2;
        rewrite Hbeq2 in *; simpl in *.
        do 2 rewrite ind_gen_pre_cons.
        do 2 rewrite ind_gen_pre_cons in H.
        destruct n. discriminate. destruct n. discriminate.
        inversion H as [[H1 H2]]. rewrite H0. reflexivity.

        do 2 rewrite ind_gen_pre_cons.
        do 2 rewrite ind_gen_pre_cons in H.
        destruct n. discriminate.
        inversion H as [[H1 H2]]. rewrite H2. reflexivity.

    case_eq (beq_nat Rn Pn); intros Hbeq2; rewrite Hbeq2 in *.
      simpl in *.
      rewrite ind_gen_pre_cons in *.
      rewrite ind_gen_pre_cons in *.
      rewrite ind_gen_pre_cons in H.
      rewrite ind_gen_pre_cons in H.
      assumption.

      rewrite ind_gen_pre_cons in *.
      rewrite ind_gen_pre_cons in *.
      rewrite ind_gen_pre_cons in H.
      rewrite ind_gen_pre_cons in H.
      assumption.
Qed.

Lemma lem_a15_pre_pre_pre_pre_pre_stronger_rev : forall l P Q R W lpa2 pa pa0 pa1 pa2 n,
  @ind_gen _ pa2 (indicies_l2 (cons Q (cons P l)) R) (cons pa1 (cons pa0 lpa2)) = constant_l pa n ->
  @ind_gen (W -> Prop) pa2 (indicies_l2 (cons P (cons Q l)) R) (cons pa0 (cons pa1 lpa2)) = constant_l pa n.
Proof.
  unfold indicies_l2.
  intros l [Pn] [Qm] [Rn] W lpa2 pa pa0 pa1 pa2 n  H.
    simpl in *. case_eq (beq_nat Rn Qm); intros Hbeq;
      rewrite Hbeq in *.
      case_eq (beq_nat Rn Pn); intros Hbeq2;
        rewrite Hbeq2 in *; simpl in *.
        do 2 rewrite ind_gen_pre_cons.
        do 2 rewrite ind_gen_pre_cons in H.
        destruct n. discriminate. destruct n. discriminate.
        inversion H as [[H1 H2]]. rewrite H0. reflexivity.

        do 2 rewrite ind_gen_pre_cons.
        do 2 rewrite ind_gen_pre_cons in H.
        destruct n. discriminate.
        inversion H as [[H1 H2]]. rewrite H2. reflexivity.

    case_eq (beq_nat Rn Pn); intros Hbeq2; rewrite Hbeq2 in *.
      simpl in *.
      rewrite ind_gen_pre_cons in *.
      rewrite ind_gen_pre_cons in *.
      rewrite ind_gen_pre_cons in H.
      rewrite ind_gen_pre_cons in H.
      assumption.

      rewrite ind_gen_pre_cons in *.
      rewrite ind_gen_pre_cons in *.
      rewrite ind_gen_pre_cons in H.
      rewrite ind_gen_pre_cons in H.
      assumption.
Qed.

Lemma lem_a15_pre_pre_pre_pre_pre : forall l P Q R W lpa2 pa pa0 pa1 pa2 n,
  length l = length lpa2 ->
  @ind_gen (W -> Prop) pa2 (indicies_l2 (cons P (cons Q l)) R) (cons pa0 (cons pa1 lpa2)) = constant_l pa n ->
  @ind_gen _ pa2 (indicies_l2 (cons Q (cons P l)) R) (cons pa1 (cons pa0 lpa2)) = constant_l pa n.
Proof.
  unfold indicies_l2.
  intros l [Pn] [Qm] [Rn] W lpa2 pa pa0 pa1 pa2 n Hlength H.
    simpl in *. case_eq (beq_nat Rn Qm); intros Hbeq;
      rewrite Hbeq in *.
      case_eq (beq_nat Rn Pn); intros Hbeq2;
        rewrite Hbeq2 in *; simpl in *.
        do 2 rewrite ind_gen_pre_cons.
        do 2 rewrite ind_gen_pre_cons in H.
        destruct n. discriminate. destruct n. discriminate.
        inversion H as [[H1 H2]]. rewrite H0. reflexivity.

        do 2 rewrite ind_gen_pre_cons.
        do 2 rewrite ind_gen_pre_cons in H.
        destruct n. discriminate.
        inversion H as [[H1 H2]]. rewrite H2. reflexivity.

    case_eq (beq_nat Rn Pn); intros Hbeq2; rewrite Hbeq2 in *.
      simpl in *.
      rewrite ind_gen_pre_cons in *.
      rewrite ind_gen_pre_cons in *.
      rewrite ind_gen_pre_cons in H.
      rewrite ind_gen_pre_cons in H.
      assumption.

      rewrite ind_gen_pre_cons in *.
      rewrite ind_gen_pre_cons in *.
      rewrite ind_gen_pre_cons in H.
      rewrite ind_gen_pre_cons in H.
      assumption.
Qed.

Lemma consistent_lP_lpa_cons_cons_same : forall lP P W lpa pa1 pa2 pa3,
  @consistent_lP_lpa W pa3 (cons P (cons P lP)) (cons pa1 (cons pa2 lpa)) ->
  pa1 = pa2.
Proof.
  unfold consistent_lP_lpa.
  unfold consistent_lP_lpa_P.
  unfold is_constant. unfold indicies_l2.
  intros lP [Pn] W lpa pa1 pa2 pa3 H.
  specialize (H (Pred Pn)).
  simpl in H.
  rewrite <- beq_nat_refl in H. simpl in H.
  destruct H as [pa4 [n H]].
  destruct n. discriminate. destruct n. discriminate.
  inversion H as [[H1 H2]].
  reflexivity.
Qed.

Lemma altered_Ip_alt_list_alt_same : forall lP W Ip lpa pa pa2 P,
  @altered_Ip W (altered_Ip_list (altered_Ip Ip pa P) lpa lP) pa2 P =
  altered_Ip (altered_Ip_list Ip lpa lP) pa2 P.
Proof.
  induction lP; intros W Ip lpa pa pa2 P.
    rewrite altered_Ip_list_nil.
    rewrite altered_Ip_list_nil. rewrite altered_Ip_eq.
    reflexivity.

    destruct lpa. simpl. rewrite altered_Ip_eq.
      reflexivity.

      simpl. destruct a as [Qm]. destruct P as [Pn].
      case_eq (beq_nat Pn Qm); intros Hbeq.
        rewrite (beq_nat_true _ _ Hbeq).
        rewrite IHlP. reflexivity.

        rewrite <- altered_Ip_switch. rewrite IHlP.
        rewrite <- altered_Ip_switch. reflexivity.
        apply beq_nat_false. assumption.
        apply beq_nat_false. rewrite beq_nat_comm. assumption.
Qed.

Lemma consistent_lP_lpa_cons_cons_switch : forall lP P Q W lpa pa1 pa2 pa0,
  @consistent_lP_lpa W pa0 (cons P (cons Q lP)) (cons pa1 (cons pa2 lpa)) ->
  @consistent_lP_lpa W pa0 (cons Q (cons P lP)) (cons pa2 (cons pa1 lpa)).
Proof.
  unfold consistent_lP_lpa.
  unfold consistent_lP_lpa_P.
  unfold is_constant.
  intros lP P Q W lpa pa1 pa2 p0 H R.
  specialize (H R).
  destruct H as [pa3 [n H]].
  exists pa3. exists n.
  apply lem_a15_pre_pre_pre_pre_pre_stronger.
  assumption.
Qed.

Lemma altered_Ip__list_consistent_lP_lpa : forall lP P W Ip lpa pa pa2,
  @consistent_lP_lpa W pa2 (cons P lP) (cons pa lpa) ->
  altered_Ip (altered_Ip_list Ip lpa lP) pa P =
  altered_Ip_list (altered_Ip Ip pa P) lpa lP.
Proof.
  induction lP; intros P W Ip lpa pa pa2 Hcon .
    do 2 rewrite altered_Ip_list_nil. reflexivity.

    destruct lpa. simpl. reflexivity.
    simpl. destruct P as [Pn]. destruct a as [Qm].
    case_eq (beq_nat Pn Qm); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq) in *.
      apply consistent_lP_lpa_cons_cons_same in Hcon.
      rewrite Hcon. rewrite altered_Ip_eq.
      rewrite altered_Ip_alt_list_alt_same. reflexivity.

      specialize (IHlP (Pred Pn) W Ip lpa pa pa2).
      rewrite <- IHlP. rewrite altered_Ip_switch.
      reflexivity.

      intros H. rewrite H in *.  rewrite <- beq_nat_refl in *.
      discriminate.

      apply consistent_lP_lpa_cons_cons_switch in Hcon.
      apply consistent_lP_lpa_cons_rem in Hcon. assumption.
Qed.

Lemma lem_a15_pre_pre_pre_pre : forall l2 Q P W lpa2 (pa pa1 pa2: W -> Prop) n,
  length l2 = length lpa2 ->
  @ind_gen _ pa2 (indicies_l2 (app l2 (cons Q nil)) P) (app lpa2 (cons pa1 nil)) = constant_l pa n <->
  @ind_gen _ pa2 (indicies_l2 (cons Q l2) P) (cons pa1 lpa2) = constant_l pa n.
Proof.
  induction l2; intros [Qm] [Pn] W lpa2 pa pa1 pa2 n Hlength.
    simpl in *. destruct lpa2. simpl in *. apply bi_refl. discriminate.
    split; intros H.

    simpl in *. destruct lpa2. discriminate. simpl in *.
    apply lem_a15_pre_pre_pre_pre_pre. inversion Hlength. reflexivity.
    unfold indicies_l2 in H. unfold indicies_l2.
    destruct a as [Rn]. simpl in *. case_eq (beq_nat Pn Rn);
      intros Hbeq; rewrite Hbeq in *.
      simpl in *. rewrite ind_gen_pre_cons in H.
      unfold indicies_l2 in IHl2.
      destruct n. discriminate. inversion H as [[H1 H2]].
      apply  IHl2 in H2. simpl in H2.
      case_eq (beq_nat Pn Qm); intros Hbeq2; rewrite Hbeq2 in *.
        simpl in *. rewrite ind_gen_pre_cons. rewrite H2.
        reflexivity.

        rewrite ind_gen_pre_cons. rewrite H2. reflexivity.
          inversion Hlength. reflexivity.

      rewrite ind_gen_pre_cons in H. apply IHl2 in H.
      unfold indicies_l2 in H.
      simpl in H.
      case_eq (beq_nat Pn Qm); intros Hbeq2;
        rewrite Hbeq2 in *. simpl in *.
        rewrite ind_gen_pre_cons. assumption.

        rewrite ind_gen_pre_cons. assumption.
          inversion Hlength. reflexivity.

    simpl in *. destruct lpa2. discriminate. simpl in *.
    apply lem_a15_pre_pre_pre_pre_pre in H. 
      2 : (inversion Hlength; reflexivity).
    unfold indicies_l2 in H. unfold indicies_l2.
    destruct a as [Rn]. simpl in *. case_eq (beq_nat Pn Rn);
      intros Hbeq; rewrite Hbeq in *.
      simpl in *. rewrite ind_gen_pre_cons .
      unfold indicies_l2 in IHl2.
      destruct n. discriminate. inversion H as [[H1 H2]].
      case_eq (beq_nat Pn Qm); intros Hbeq2; rewrite Hbeq2 in *.
        simpl in *. rewrite ind_gen_pre_cons in H2.
        destruct n. discriminate. inversion H2 as [[H3 H4]].
        rewrite ind_gen_pre_cons in H4.
        specialize (IHl2 (Pred Qm) (Pred Pn) W lpa2 pa pa1 pa2 (S n)).
          simpl in IHl2. rewrite Hbeq2 in IHl2. simpl in *.
          rewrite H3 in IHl2. rewrite H3 in H2.
          apply IHl2 in H2. rewrite H2. reflexivity. 

          inversion Hlength. reflexivity.

      rewrite ind_gen_pre_cons in H2.
        specialize (IHl2 (Pred Qm) (Pred Pn) W lpa2 pa pa1 pa2 n).
          simpl in IHl2. rewrite Hbeq2 in IHl2. simpl in *.
          apply IHl2 in H2.  rewrite H2.  reflexivity. 
          inversion Hlength. reflexivity.

        rewrite ind_gen_pre_cons. apply IHl2.
          inversion Hlength. reflexivity.

        unfold indicies_l2. simpl. case_eq (beq_nat Pn Qm);
          intros Hbeq2; rewrite Hbeq2 in *.
          simpl in *. rewrite ind_gen_pre_cons in H.
          destruct n. discriminate. inversion H as [[H1 H2]].
          rewrite H2. reflexivity.

          rewrite ind_gen_pre_cons in H. assumption.
Qed.

Lemma lem_a15_pre_pre_pre : forall (lP1 lP2 : list predicate) a (W : Type) pa n
   (lpa1 lpa2 : list (W -> Prop))
  (pa2 pa1 : W -> Prop) (P : predicate),
length lP1 = length lpa1 ->
length lP2 = length lpa2 ->
@ind_gen _ pa2 (indicies_l2 ((a :: lP1) ++ lP2) P ) ((cons pa1 lpa1) ++ lpa2) = constant_l pa n ->
@ind_gen _ pa2 (indicies_l2 (lP1 ++ a :: lP2) P ) (lpa1 ++ (cons pa1 lpa2)) = constant_l pa n.
Proof.
   induction lP1; intros lP2 [Qm] W pa n lpa1 lpa2 pa2 pa1 [Pn] Hl1 Hl2 H.
    destruct lpa1. simpl in *. assumption. discriminate.

    simpl in H. destruct lpa1. discriminate.
    apply (lem_a15_pre_pre_pre_pre_pre (app lP1 lP2)) in H.
assert (forall (A : Type), (fix app (l m : list A) {struct l} : list A :=
          match l with
          | nil => m
          | cons a l1 => cons a (app l1 m)
          end) = @app A) as Hobvs2.
reflexivity.
    rewrite (Hobvs2 (W -> Prop)) in H.
clear Hobvs2.

    simpl.
    unfold indicies_l2. unfold indicies_l2 in H.
    simpl in *. destruct a as [Rn].
      case_eq (beq_nat Pn Rn); intros Hbeq;
        rewrite Hbeq in *. simpl in *.
    simpl in *.
    destruct n. discriminate.
    inversion H as [[H1 H2]].
    simpl in *. case_eq (beq_nat Pn Qm); intros Hbeq2;
      rewrite Hbeq2 in *. simpl in *.
      destruct n. discriminate. inversion H2.
      rewrite ind_gen_pre_cons in H4.
      rewrite ind_gen_pre_cons in H4.
      rewrite ind_gen_pre_cons. unfold indicies_l2 in IHlP1.
      rewrite IHlP1 with (pa := pa) (n := (S n)). reflexivity.
        all : try assumption.
        inversion Hl1. reflexivity.

        simpl. rewrite Hbeq2. simpl. rewrite ind_gen_pre_cons.
        rewrite H4. reflexivity.

      unfold indicies_l2 in IHlP1.  rewrite ind_gen_pre_cons.
      rewrite IHlP1 with (pa := pa) (n := n). reflexivity.
      inversion Hl1. reflexivity.
      all : try assumption.

      do 2 rewrite ind_gen_pre_cons in H2.
      simpl. rewrite Hbeq2.
      rewrite ind_gen_pre_cons. assumption.

      rewrite ind_gen_pre_cons.
      apply IHlP1; try assumption.
      inversion Hl1. reflexivity.

      unfold indicies_l2.
      simpl in *. case_eq (beq_nat Pn Qm); intros Hbeq2;
        rewrite Hbeq2 in *. simpl in *.
        rewrite ind_gen_pre_cons.
        do 2 rewrite ind_gen_pre_cons in H.
        assumption.

        rewrite ind_gen_pre_cons in H. assumption.

assert (forall (A : Type), (fix app (l m : list A) {struct l} : list A :=
          match l with
          | nil => m
          | cons a l1 => cons a (app l1 m)
          end) = @app A) as Hobvs2.
reflexivity.
    rewrite (Hobvs2 (W -> Prop)).
clear Hobvs2.
      do 2 rewrite List.app_length.
      inversion Hl1 as [H'].
      rewrite H'. rewrite Hl2. reflexivity.
Qed.
 
Lemma lem_a15_pre_pre_pre_stronger : forall (lP1 lP2 : list predicate) a (W : Type) pa n
   (lpa1 lpa2 : list (W -> Prop))
  (pa2 pa1 : W -> Prop) (P : predicate),
length lP1 = length lpa1 ->
@ind_gen _ pa2 (indicies_l2 ((a :: lP1) ++ lP2) P ) ((cons pa1 lpa1) ++ lpa2) = constant_l pa n ->
@ind_gen _ pa2 (indicies_l2 (lP1 ++ a :: lP2) P ) (lpa1 ++ (cons pa1 lpa2)) = constant_l pa n.
Proof.
   induction lP1; intros lP2 [Qm] W pa n lpa1 lpa2 pa2 pa1 [Pn] Hl1 H.
    destruct lpa1. simpl in *. assumption. discriminate.

    simpl in H. destruct lpa1. discriminate.
    apply (lem_a15_pre_pre_pre_pre_pre_stronger (app lP1 lP2)) in H.
assert (forall (A : Type), (fix app (l m : list A) {struct l} : list A :=
          match l with
          | nil => m
          | cons a l1 => cons a (app l1 m)
          end) = @app A) as Hobvs2.
reflexivity.
    rewrite (Hobvs2 (W -> Prop)) in H.
clear Hobvs2.

    simpl.
    unfold indicies_l2. unfold indicies_l2 in H.
    simpl in *. destruct a as [Rn].
      case_eq (beq_nat Pn Rn); intros Hbeq;
        rewrite Hbeq in *. simpl in *.

    simpl in *.
    destruct n. discriminate.
    inversion H as [[H1 H2]].
    simpl in *. case_eq (beq_nat Pn Qm); intros Hbeq2;
      rewrite Hbeq2 in *. simpl in *.
      destruct n. discriminate. inversion H2.
      rewrite ind_gen_pre_cons in H4.
      rewrite ind_gen_pre_cons in H4.
      rewrite ind_gen_pre_cons. unfold indicies_l2 in IHlP1.
      rewrite IHlP1 with (pa := pa) (n := (S n)). reflexivity.
        all : try assumption.
        inversion Hl1. reflexivity.

        simpl. rewrite Hbeq2. simpl. rewrite ind_gen_pre_cons.
        rewrite H4. reflexivity.

      unfold indicies_l2 in IHlP1.  rewrite ind_gen_pre_cons.
      rewrite IHlP1 with (pa := pa) (n := n). reflexivity.
      inversion Hl1. reflexivity.
      all : try assumption.

      do 2 rewrite ind_gen_pre_cons in H2.
      simpl. rewrite Hbeq2.
      rewrite ind_gen_pre_cons. assumption.

      rewrite ind_gen_pre_cons.
      apply IHlP1; try assumption.
      inversion Hl1. reflexivity.

      unfold indicies_l2.
      simpl in *. case_eq (beq_nat Pn Qm); intros Hbeq2;
        rewrite Hbeq2 in *. simpl in *.
        rewrite ind_gen_pre_cons.
        do 2 rewrite ind_gen_pre_cons in H.
        assumption.

        rewrite ind_gen_pre_cons in H. assumption.
Qed.

Lemma lem_a15_pre_pre_pre' : forall (lP1 lP2 : list predicate) (W : Type) pa n
   (lpa1 lpa2 : list (W -> Prop))
  (pa2 : W -> Prop) (P : predicate),
length lP1 = length lpa1 ->
length lP2 = length lpa2 ->
   @ind_gen _ pa2 (indicies_l2_pre (lP1 ++ lP2) P 0) (lpa1 ++ lpa2) = constant_l pa n ->
  @ind_gen _ pa2 (indicies_l2_pre (lP2 ++ lP1) P 0) (lpa2 ++ lpa1) = constant_l pa n.
Proof.
  induction lP1; intros lP2 W pa n lpa1 lpa2 pa2 P Hl1 Hl2 H.
    simpl in *. rewrite List.app_nil_r. destruct lpa1. 2 : discriminate.
    rewrite List.app_nil_r. simpl in *. assumption.

    destruct a as [Qm]. destruct P as [Pn]. simpl in *.
    destruct lpa1. discriminate.
    apply lem_a15_pre_pre_pre. assumption. inversion Hl1. reflexivity.
    unfold indicies_l2.  simpl.
    case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *.
      simpl in *. rewrite ind_gen_pre_cons in H. destruct n.
      discriminate. simpl in H.
      inversion H as [[H1 H2]].
      rewrite ind_gen_pre_cons.
      rewrite IHlP1 with (pa := pa) (n := n). reflexivity.  
        inversion Hl1. reflexivity. assumption.
      assumption.

      rewrite ind_gen_pre_cons.
      simpl in H.
      rewrite ind_gen_pre_cons in H.
      apply IHlP1; try assumption. 
      inversion Hl1. reflexivity.
Qed.


Lemma lem_a15_pre_pre : forall lP1 lP2 W lpa1 lpa2 (pa2 : W -> Prop) P,
length lP1 = length lpa1 ->
length lP2 = length lpa2 ->
is_constant (@ind_gen _ pa2 (indicies_l2 (app lP1 lP2) P) (app lpa1 lpa2)) ->
is_constant (@ind_gen _ pa2 (indicies_l2 (app lP2 lP1) P) (app lpa2  lpa1)).
Proof.
  unfold is_constant. unfold indicies_l2.
  intros until 0. intros H1 H2 H3.
  destruct H3 as [pa [n H3]].
  exists pa. exists n. apply lem_a15_pre_pre_pre';
  assumption.
Qed.

Lemma lem_a15_pre : forall lP1 lP2 W lpa1 lpa2 pa2 P,
  length lP1 = length lpa1 ->
  length lP2 = length lpa2 ->
  (@consistent_lP_lpa_P W pa2 (app lP1 lP2) (app lpa1 lpa2) P ->
  @consistent_lP_lpa_P _ pa2 (app lP2 lP1) (app lpa2 lpa1) P).
Proof.
  unfold consistent_lP_lpa_P.
  intros until 0. apply lem_a15_pre_pre.
Qed.

Lemma lem_a15 : forall lP1 lP2 W lpa1 lpa2 pa2,
  length lP1 = length lpa1 ->
  length lP2 = length lpa2 ->
  (@consistent_lP_lpa W pa2 (app lP1 lP2) (app lpa1 lpa2) ->
  @consistent_lP_lpa _ pa2 (app lP2 lP1) (app lpa2 lpa1)).
Proof.
  unfold consistent_lP_lpa.
  intros until 0. intros H1 H2 H P.
  apply lem_a15_pre; try assumption. apply H.
Qed.

Lemma lem_a16_pre_pre : forall lP1 lP2 (W : Set) lpa1 lpa2 (pa2 : W -> Prop) Q pa n,
  length lP1 = length lpa1 ->
   @ind_gen _ pa2 (indicies_l2 (lP1 ++ lP2) Q) (lpa1 ++ lpa2) = constant_l pa n ->
exists m, @ind_gen _ pa2 (indicies_l2 lP1 Q) lpa1 = constant_l pa m.
Proof.
  induction lP1; intros lP2 W lpa1 lpa2 pa2 [Qm] pa n Hlength Hind.
    simpl in *. exists 0. reflexivity.

    unfold indicies_l2 in *. destruct a as [Pn]. simpl in *.
    destruct lpa1. discriminate. simpl in *.
    inversion Hlength as [Hl].
    case_eq (beq_nat Qm Pn); intros Hbeq; rewrite Hbeq in *.
      simpl in *. rewrite ind_gen_pre_cons in *.
      rewrite ind_gen_pre_cons in Hind. 
      destruct n. discriminate.
      simpl in Hind. inversion Hind as [[H1 H2]].
      destruct (IHlP1 lP2 W lpa1 lpa2 pa2 (Pred Qm) pa n Hl H2)
        as [m H].
      exists (S m). rewrite H. reflexivity.

      simpl in *. rewrite ind_gen_pre_cons in *.
      rewrite ind_gen_pre_cons in Hind. 
      destruct (IHlP1 lP2 W lpa1 lpa2 pa2 (Pred Qm) pa n Hl Hind)
        as [m H].
      exists (m). rewrite H. reflexivity.
Qed.

Lemma lem_a16_pre : forall lP1 lP2 W lpa1 lpa2 pa2 Q,
  length lP1 = length lpa1 ->
  @consistent_lP_lpa_P W pa2 (app lP1 lP2) (app lpa1 lpa2) Q->
  @consistent_lP_lpa_P W pa2 lP1 lpa1 Q.
Proof.
  unfold consistent_lP_lpa_P.
  unfold is_constant.
  induction lP1; intros lP2 W lpa1 lpa2 pa2 [Qm] Hlength H.
    simpl. apply is_constant_nil. apply pa2.

    destruct H as [pa [n H]]. unfold indicies_l2 in *.
    simpl in *. destruct a as [Pn]. case_eq (beq_nat Qm Pn); intros Hbeq;
      rewrite Hbeq in *.
      simpl in *. destruct lpa1. discriminate. simpl in *.
      rewrite ind_gen_pre_cons in *.
      rewrite ind_gen_pre_cons in H. destruct n.
      discriminate. simpl in H. inversion H as [[H1 H2]].
      inversion Hlength as [Hlength'].
      destruct (lem_a16_pre_pre lP1 lP2 W lpa1 lpa2 pa2 (Pred Qm) pa n Hlength' H2)
        as [m H3].
      exists pa. exists (S m). unfold indicies_l2 in H3. rewrite H3.
      reflexivity.

      destruct lpa1. discriminate. rewrite ind_gen_pre_cons.
      inversion Hlength.
      apply IHlP1 with (lP2 := lP2) (lpa2 := lpa2);
        try assumption.
      simpl in H. rewrite ind_gen_pre_cons in H.
      exists pa. exists n. assumption.
Qed.

Lemma lem_a16 : forall lP1 lP2 W lpa1 lpa2 pa2,
  length lP1 = length lpa1 ->
  @consistent_lP_lpa W pa2 (app lP1 lP2) (app lpa1 lpa2) ->
  @consistent_lP_lpa W pa2 lP1 lpa1.
Proof.
  unfold consistent_lP_lpa.
  intros until 0. intros H1 H2 P.
  specialize (H2 P). apply lem_a16_pre in H2;
  assumption.
Qed.


Lemma lem_a13 : forall lP W Ip pa lpa P,
  length lP = length lpa ->
  is_in_pred P lP = true ->
  @altered_Ip_list W (altered_Ip Ip pa P) lpa lP =
  altered_Ip_list Ip lpa lP.
Proof.
  induction lP; intros W Ip pa lpa [Pn] Hlength Hin.
    simpl in *. discriminate.

    destruct a as [Qm]. simpl in Hin.
    destruct lpa. discriminate.
    inversion Hlength as [Hl].
    case_eq (beq_nat Pn Qm); intros Hbeq;
      rewrite Hbeq in *.
      rewrite altered_Ip_list_cons. 
      rewrite altered_Ip_list_cons. 
      rename P into pa2.
      case_eq (is_in_pred (Pred Pn) lP);
        intros Hin2.
        rewrite IHlP. reflexivity. assumption.
        assumption.

        rewrite altered_Ip__list_occ_f.
        rewrite (beq_nat_true _ _ Hbeq).
        rewrite altered_Ip_eq. reflexivity.
        rewrite occ_in_l_is_in_pred. assumption.


      rewrite altered_Ip_list_cons. 
      rewrite altered_Ip_list_cons. 
      rename P into pa2.
      rewrite IHlP. reflexivity. assumption.
      assumption.
Qed.

Lemma lem_a14_pre_pre_pre_pre : forall lP1 lP2 P W lpa1 lpa2 (pa0 pa2 : W -> Prop),
  length lP1 = length lpa1 ->
  ~@ind_gen _ pa0 (indicies_l2 (app lP1 (cons P lP2)) P) (app lpa1 (cons pa2 lpa2))
       = nil.
Proof.
  induction lP1; intros lP2 [Pn] W lpa1 lpa2 pa0 pa Hl H.
    destruct lpa1. unfold indicies_l2 in *. simpl in *.
    rewrite <- beq_nat_refl in H. simpl in *. all : try discriminate.

    simpl in *. destruct a as [Qm].
    unfold indicies_l2 in *. simpl in *.
    case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *.
      simpl in *. destruct lpa1. discriminate. simpl in *.
      rewrite ind_gen_pre_cons in H. discriminate.
      destruct lpa1. discriminate. simpl in H. 
      rewrite ind_gen_pre_cons in H.
      inversion Hl as [Hl'].
      contradiction (IHlP1 _ _ _ _ _ _ _ Hl' H).
Qed.

Lemma lem_a14_pre_pre_pre_rev: forall (lP1 lP2 : list predicate) n (P Q : predicate)
   (W : Set) (lpa1 lpa2 : list (W -> Prop)) (pa pa1 pa2 : W -> Prop),
length lP1 = length lpa1 ->
(@ind_gen _ pa2 (indicies_l2 (lP1 ++ P :: lP2) Q) (lpa1 ++ pa :: lpa2)) = constant_l pa1 n ->
(@ind_gen _ pa2 (indicies_l2 (P :: (lP1 ++ lP2)%list) Q) 
    (pa :: (lpa1 ++ lpa2)%list)) = constant_l pa1 n.
Proof.
   induction lP1; intros lP2 n [Pn] [Qm] W lpa1 lpa2 pa pa1 pa2 Hl H.
     destruct lpa1. simpl in *. assumption. discriminate.

    simpl in H. destruct lpa1. discriminate. 
    apply (lem_a15_pre_pre_pre_pre_pre_stronger_rev (app lP1 lP2)).
assert (forall (A : Type), (fix app (l m : list A) {struct l} : list A :=
          match l with
          | nil => m
          | cons a l1 => cons a (app l1 m)
          end) = @app A) as Hobvs2.
reflexivity.
    rewrite (Hobvs2 (W -> Prop)).
clear Hobvs2.

    simpl in *.
    unfold indicies_l2. unfold indicies_l2 in H.
    simpl in *. destruct a as [Rn].
      case_eq (beq_nat Qm Rn); intros Hbeq;
        rewrite Hbeq in *. simpl in *.

    simpl in *.
    destruct n. discriminate.
    inversion H as [[H1 H2]].
    simpl in *. case_eq (beq_nat Qm Pn); intros Hbeq2.
       simpl in *.
      destruct n. rewrite (beq_nat_true _ _ Hbeq2) in H2.
      simpl in H2. rewrite ind_gen_pre_cons in H2.
      inversion Hl as [Hl'].
      contradiction (lem_a14_pre_pre_pre_pre _ _ _ _ _ _ _ _ Hl' H2).

 rewrite ind_gen_pre_cons in H2.
        rewrite ind_gen_pre_cons.
        inversion Hl as [Hl'].
        unfold indicies_l2 in IHlP1.
        specialize (IHlP1 lP2 (S n) (Pred Pn) (Pred Qm) W _ lpa2 pa pa1 pa2 Hl' H2).
        simpl in IHlP1. rewrite Hbeq2 in IHlP1. simpl in IHlP1.
        rewrite IHlP1. reflexivity.

      rewrite ind_gen_pre_cons.
      rewrite ind_gen_pre_cons in H2.
        inversion Hl as [Hl'].
        unfold indicies_l2 in IHlP1.
        specialize (IHlP1 lP2 n (Pred Pn) (Pred Qm) W _ lpa2 pa pa1 pa2 Hl' H2).
        simpl in IHlP1. rewrite Hbeq2 in IHlP1. simpl in IHlP1.
        rewrite IHlP1. reflexivity.

    simpl in *.
    rewrite ind_gen_pre_cons in H.
    inversion Hl as [Hl'].
    unfold indicies_l2 in IHlP1.
    pose proof (IHlP1 lP2 n (Pred Pn) (Pred Qm) W lpa1 lpa2 pa pa1 pa2 Hl' H) as IH.
    simpl in *. case_eq (beq_nat Qm Pn); intros Hbeq2;
      rewrite Hbeq2 in *; simpl in *.
      simpl in IH. destruct n. discriminate.
      inversion IH as [[H1 H2]]. 
        rewrite ind_gen_pre_cons. rewrite H2.
        reflexivity.

      rewrite ind_gen_pre_cons. assumption.
Qed.

Lemma lem_a14_pre_pre : forall (lP1 lP2 : list predicate) (P Q : predicate) (W : Set)
  (lpa1 lpa2 : list (W -> Prop)) (pa pa2 : W -> Prop),
length lP1 = length lpa1 ->
is_constant (@ind_gen _ pa2 (indicies_l2 (P :: (lP1 ++ lP2)%list) Q) (pa :: (lpa1 ++ lpa2)%list)) <->
is_constant (@ind_gen _ pa2 (indicies_l2 (lP1 ++ P :: lP2) Q) (lpa1 ++ pa :: lpa2)).
Proof.
  unfold is_constant. intros until 0. intros Hlength.
  split; intros [pa1 [n H]]; exists pa1; exists n.
    apply lem_a15_pre_pre_pre_stronger; assumption.

    apply lem_a14_pre_pre_pre_rev; assumption.
Qed.

Lemma lem_a14_pre: forall lP1 lP2 P Q W lpa1 lpa2 pa pa2,
  length lP1 = length lpa1 ->
  (@consistent_lP_lpa_P W pa2 (cons P (app lP1 lP2)) (cons pa (app lpa1 lpa2)) Q <->
  @consistent_lP_lpa_P _ pa2 (app lP1 (cons P lP2)) (app lpa1 (cons pa lpa2)) Q).
Proof.
  unfold consistent_lP_lpa_P.
  apply lem_a14_pre_pre.
Qed.

 Lemma lem_a14  : forall lP1 lP2 P W lpa1 lpa2 pa pa2,
  length lP1 = length lpa1 ->
  (@consistent_lP_lpa W pa2 (cons P (app lP1 lP2)) (cons pa (app lpa1 lpa2)) <->
  @consistent_lP_lpa _ pa2 (app lP1 (cons P lP2)) (app lpa1 (cons pa lpa2))).
Proof.
  unfold consistent_lP_lpa.
  intros. split; intros HH Q;
    (apply lem_a14_pre; [ assumption| apply HH]).
Qed.

Lemma lemma_try7_again : forall lP atm W Ip Iv Ir pa_l x pa2 lP0 pa_l0,
  AT atm = true ->
  is_in_pred_l lP (preds_in atm) = true ->
  ex_FOvar_x_ll x (FOv_att_P_l atm lP) = false ->
  SOturnst W Iv (altered_Ip_list Ip pa_l0 lP0) Ir atm ->
  is_in_pred_l lP lP0 = true ->
  @consistent_lP_lpa _ pa2 (app lP lP0) (app pa_l pa_l0) ->
  length lP0 = length pa_l0 ->
  length lP = length pa_l ->
  @consistent_lP_lpa _ pa2 lP pa_l ->
Ip_extends_l W
  (altered_Ip_list Ip
     (vsS_pa_l Iv (FOv_att_P_l atm lP) (list_Var (length lP) x)) lP)
  (altered_Ip_list Ip pa_l lP) lP.
Proof.
  induction lP; intros atm W Ip Iv Ir lpa x pa2 lP0 lpa0 Hat Hin Hex SOt Hin4 Hcon4 Hlength4 Hlength Hcon.
    simpl in *. rewrite altered_Ip_list_nil. apply Ip_extends_l_refl.

    destruct lpa. discriminate. simpl in *.
    unfold Ip_extends_l. rename P into pa. rename a into P.
    case_eq (is_in_pred P (preds_in atm)); intros Hin2;
      rewrite Hin2 in *. 2 : discriminate.
    case_eq (is_in_FOvar x (fun2 atm P)); intros Hin3;
      rewrite Hin3 in *. discriminate.
assert (@consistent_lP_lpa _ pa2 lP lpa) as Hcon2.
  apply consistent_lP_lpa_cons_rem in Hcon. assumption.
    intros Q. apply conj; intros Hpocc.
      intros w Halt. destruct P as [Pn]. destruct Q as [Qm].
      simpl in Hpocc. simpl in Halt. simpl. rewrite beq_nat_comm in Hpocc.
      case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *.

        apply lemma17' with (Ip := (altered_Ip_list Ip lpa0 lP0)) (Ir := Ir) (pa := pa) in Halt;
        try assumption.

        rewrite <- P_occ_in_alpha_is_in_pred_equiv. assumption.

        inversion Hlength.
assert ((altered_Ip (altered_Ip_list Ip lpa0 lP0) pa (Pred Pn)) =
  ((altered_Ip_list (altered_Ip Ip pa (Pred Pn)) lpa0 lP0))) as Hass.
  apply lem_a14 in Hcon4.
  apply lem_a15 in Hcon4.
  apply lem_a16 in Hcon4.
  apply altered_Ip__list_consistent_lP_lpa with (pa2 := pa2).
  all : try assumption.
  simpl. rewrite Hlength4. reflexivity. simpl in *. rewrite Hlength4.
    reflexivity.


        rewrite Hass.
        case_eq (is_in_pred (Pred Pn) lP0); intros Hin5; rewrite Hin5 in *.
          2 : discriminate.
        rewrite lem_a13; assumption.

        assert (~ Pred Pn = Pred Qm) as Hneq2.
          intros HH. inversion HH as [HH']. rewrite HH' in *.
          rewrite <- beq_nat_refl in *. discriminate.
        inversion Hlength as [Hlength'].
        case_eq (is_in_pred (Pred Pn) lP0); intros Hin5; rewrite Hin5 in *.
          2 : discriminate.
        pose proof (consistent_lP_lpa_cons_rem _ _ _ _ _ _ Hcon4) as Hcon5.
        specialize (IHlP _ _ _ _ _ _ x pa2 lP0 lpa0 Hat Hin Hex SOt Hin4 Hcon5 Hlength4 Hlength' Hcon2 (Pred Qm)).
        destruct IHlP as [IH1 IH2].
        specialize (IH1 Hpocc w).
        specialize (IH1 Halt). assumption.

      destruct P as [Pn]; destruct Q as [Qm].
      simpl.
      case_eq (beq_nat Pn Qm); intros Hbeq.
        simpl in Hpocc. rewrite beq_nat_comm in Hpocc.
        rewrite Hbeq in Hpocc. discriminate.

        assert (~ Pred Pn = Pred Qm) as Hneq2.
          intros HH. inversion HH as [HH']. rewrite HH' in *.
          rewrite <- beq_nat_refl in *. discriminate.
        inversion Hlength as [Hlength'].
        case_eq (is_in_pred (Pred Pn) lP0); intros Hin5; rewrite Hin5 in *.
          2 : discriminate.
        pose proof (consistent_lP_lpa_cons_rem _ _ _ _ _ _ Hcon4) as Hcon5.
        specialize (IHlP _ _ _ _ _ _ x pa2 lP0 lpa0 Hat Hin Hex SOt Hin4 Hcon5 Hlength4 Hlength' Hcon2 (Pred Qm)).
        destruct IHlP as [IH1 IH2].
        simpl in Hpocc. rewrite beq_nat_comm in Hpocc.
        rewrite Hbeq in Hpocc.
        specialize (IH2 Hpocc). assumption.
Qed.


Lemma fun2_REL : forall rel P,
  REL rel = true ->
  fun2 rel P = nil.
Proof.
  induction rel; intros P H; try (discriminate). reflexivity.
  simpl in *.
  case_eq (REL rel1); intros H2; rewrite H2 in *. 2 : discriminate.
  simpl in *. rewrite IHrel1. rewrite IHrel2. all : try reflexivity.
  assumption.
Qed.

Lemma FOv_att_P_l_conjSO_rel : forall lP rel atm,
  REL rel = true ->
  FOv_att_P_l (conjSO rel atm) lP =
  FOv_att_P_l atm lP.
Proof.
  induction lP; intros rel atm Hrel. reflexivity.
  simpl. rewrite fun2_REL. 
  rewrite IHlP. reflexivity.  
  all : assumption.
Qed.

Lemma is_constant_list_Var : forall (lP : list predicate) (P : predicate) (x : FOvariable),
exists m, (ind_FOv (indicies_l2_pre lP P 0) (list_Var (length lP) x)) = constant_l x m.
Proof.
  induction lP; intros P x. exists 0. reflexivity.
  simpl. destruct P as [Pn]. destruct a as [Qm].
  case_eq (beq_nat Pn Qm); intros Hbeq.
    simpl. rewrite ind_FOv_ind_l2_pre_cons.
    destruct (IHlP (Pred Pn) x) as [m IH]. exists (S m).
    rewrite IH. reflexivity.

    rewrite ind_FOv_ind_l2_pre_cons.
    destruct (IHlP (Pred Pn) x) as [m IH]. exists m. assumption.
Qed.

Lemma consistent_lP_lx_P_list_Var : forall lP P x,
  consistent_lP_lx_P lP (list_Var (length lP) x) P.
Proof.
  unfold consistent_lP_lx_P. unfold indicies_l2.
  unfold is_constant. intros lP P x.
  destruct (is_constant_list_Var lP P x) as [m H].
  exists x. exists m. assumption.
Qed.

Lemma consistent_lP_lx_list_Var : forall lP x,
  consistent_lP_lx lP (list_Var (length lP) x).
Proof.
  unfold consistent_lP_lx.
  intros. apply consistent_lP_lx_P_list_Var.
Qed.

Lemma AT_passing_predSO_ll : forall lP llx,
  ~ lP = nil ->
  ~ llx = nil ->
  ex_nil_in_llv llx = false ->
  AT (passing_conj (passing_predSO_ll lP llx)) = true.
Proof.
  induction lP; intros llx H1 H2 Hex.
    contradiction (H1 eq_refl).

    simpl. case_eq llx. intros Hllx. rewrite Hllx in *.
      contradiction (H2 eq_refl).
    intros lx llx' Hllx.
    simpl.
    case_eq (passing_predSO_ll lP llx').
      intros Hp. rewrite <- lem4. apply AT_passing_conj_atm.
      rewrite Hllx in Hex. destruct lx; discriminate.
    intros beta lbeta Hp. rewrite <- Hp.
    simpl. rewrite <- lem4. rewrite AT_passing_conj_atm.
    apply IHlP.
    destruct lP. discriminate. discriminate.
    destruct llx'. destruct lP; discriminate. discriminate.
    rewrite Hllx in Hex. destruct lx. discriminate. simpl in Hex.
    assumption.
    rewrite Hllx in Hex. destruct lx; discriminate.
Qed.


Lemma lP_is_pos_SO_uni : forall lP beta,
  uniform_pos_SO beta ->
  ~ lP = nil ->
  (forall P, is_in_pred P lP = true -> (P_occurs_in_alpha beta P = true)) ->
  lP_is_pos_SO beta lP.
Proof.
  induction lP; intros beta Hun Hnil Hpocc.
    simpl in *. contradiction (Hnil eq_refl).

    simpl. destruct lP.
    unfold uniform_pos_SO in Hun. apply Hun.
    apply Hpocc. simpl. destruct a. rewrite <- beq_nat_refl.
    reflexivity.

    apply conj.    unfold uniform_pos_SO in Hun. apply Hun.
    apply Hpocc. simpl. destruct a. rewrite <- beq_nat_refl.
    reflexivity.

    apply IHlP; try assumption. discriminate.
    intros P Hin. apply Hpocc. destruct a as [Qm]. destruct P as [Pn].
    simpl. case_eq (beq_nat Pn Qm); intros Hbeq. reflexivity.
    assumption.
Qed.

Fixpoint cap_pred_lpa {W : Set} (lpa : list (W -> Prop)) l1 l2 :=
  match l1, lpa with
  | nil, _ => nil
  | _, nil => nil
  | cons P l1', cons pa lpa' => if is_in_pred P l2 then cons pa (cap_pred_lpa lpa' l1' l2)
          else cap_pred_lpa lpa' l1' l2
  end.

Lemma is_in_pred_l_cap_pred_refl : forall l1 l2,
  is_in_pred_l (cap_pred l1 l2) l1 = true.
Proof.
  induction l1; intros l2. reflexivity.
  simpl. case_eq (is_in_pred a l2); intros Hin.
    simpl. destruct a as [Qm]. rewrite <- beq_nat_refl.
    apply is_in_pred_l2. apply IHl1.

    apply is_in_pred_l2. apply IHl1.

Qed.

Lemma ind_gen_nil : forall l W (pa0 : W -> Prop),
  @ind_gen _ pa0 l nil = constant_l pa0 (length l).
Proof.
  induction l; intros W pa. reflexivity.
  simpl. rewrite IHl. simpl. destruct a. simpl.
  reflexivity. simpl. destruct a; reflexivity.
Qed.

Lemma length_cap_pred__lpa : forall lP l2 (W : Set) (lpa : list (W -> Prop)),
  length lP = length lpa ->
  length (cap_pred lP l2) = length (cap_pred_lpa lpa lP l2).
Proof.
  induction lP; intros l2 W lpa H.
    destruct lpa; reflexivity.

    destruct lpa. discriminate. inversion H.
    simpl. case_eq (is_in_pred a l2); intros Hin.
      simpl. rewrite <- IHlP.
      reflexivity. assumption.

      apply IHlP. assumption.
Qed.

Lemma ind_gen_ind_l2_cap_pred_app : forall l1 l2 P (W : Set) lpa ( pa pa0 : W -> Prop) n,
length l1 =  length lpa ->
@ind_gen _ pa0 (indicies_l2 l1 P) lpa = constant_l pa n ->
exists (n' : nat),
@ind_gen _ pa0 (indicies_l2 (app (cap_pred l1 l2) l1) P) (app (cap_pred_lpa lpa l1 l2) lpa) =
  constant_l pa n'.
Proof.
  induction l1; intros l2 [Pn] W lpa pa pa0 n Hl Hind.
    simpl in *. exists 0. reflexivity.

    unfold indicies_l2 in *. destruct a as [Qm].
    simpl in *. case_eq (is_in_pred (Pred Qm) l2); intros Hin2.
      simpl. case_eq (beq_nat Pn Qm); intros Hbeq;rewrite Hbeq in *.
        simpl in *. destruct lpa. simpl.
        rewrite ind_gen_nil. simpl.
        exists (S(length (indicies_l2_pre
            (cap_pred l1 l2 ++ Pred Qm :: l1) (Pred Pn) 1))).
        destruct n. discriminate. inversion Hind as [[H1 H2]].
        rewrite <- H1.
        reflexivity.

        simpl. rewrite Hin2. simpl. rewrite ind_gen_pre_cons.
        rewrite ind_gen_pre_cons in Hind.
        destruct n. discriminate. unfold indicies_l2 in IHl1.
        inversion Hind as [[H1 H2]].
        inversion Hl as [Hl'].
        specialize (IHl1 l2 _ _ _ _ _ _ Hl' H2).
        destruct IHl1 as [n' IH].

pose proof lem_a15_pre_pre_pre_stronger as Hlem.
        unfold indicies_l2 in Hlem.
        rewrite (Hlem (cap_pred l1 l2)
            l1 (Pred Qm) W pa (S n')).
        exists (S (S n')). reflexivity.
        apply length_cap_pred__lpa. assumption.
        clear Hlem. simpl. rewrite Hbeq. simpl. rewrite ind_gen_pre_cons.
        rewrite IH. reflexivity.

      destruct lpa. discriminate. simpl in *.
      rewrite ind_gen_pre_cons in Hind.
      rewrite Hin2. simpl. rewrite ind_gen_pre_cons. 
        inversion Hl as [Hl'].
        specialize (IHl1 l2 _ _ _ _ _ _ Hl' Hind).
        destruct IHl1 as [n' IH].

pose proof lem_a15_pre_pre_pre_stronger as Hlem.
        unfold indicies_l2 in Hlem.
        rewrite (Hlem (cap_pred l1 l2)
            l1 (Pred Qm) W pa (n')).
        exists ( n'). reflexivity.
        apply length_cap_pred__lpa. assumption.
        clear Hlem. simpl. rewrite Hbeq. simpl. rewrite ind_gen_pre_cons.
        rewrite IH. reflexivity.

    destruct lpa. discriminate. simpl in *.
    inversion Hl as [Hl'].
    case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *.
      rewrite Hin2. simpl in Hind. destruct n. discriminate.
      inversion Hind as [[H1 H2]].
      rewrite ind_gen_pre_cons in H2.
        specialize (IHl1 l2 _ _ _ _ _ _ Hl' H2).
        destruct IHl1 as [n' IH].
pose proof lem_a15_pre_pre_pre_stronger as Hlem.
        unfold indicies_l2 in Hlem.
        rewrite (Hlem (cap_pred l1 l2)
            l1 (Pred Qm) W pa (S n')).
        exists ((S n')). reflexivity.
        apply length_cap_pred__lpa. assumption.
        clear Hlem. simpl. rewrite Hbeq. simpl. rewrite ind_gen_pre_cons.
        rewrite IH. reflexivity.

      rewrite ind_gen_pre_cons in Hind.
      rewrite Hin2.
        specialize (IHl1 l2 _ _ _ _ _ _ Hl' Hind).
        destruct IHl1 as [n' IH].

pose proof lem_a15_pre_pre_pre_stronger as Hlem.
        unfold indicies_l2 in Hlem.
        rewrite (Hlem (cap_pred l1 l2)
            l1 (Pred Qm) W pa (n')).
        exists ( n'). reflexivity.
        apply length_cap_pred__lpa. assumption.
        clear Hlem. simpl. rewrite Hbeq. simpl. rewrite ind_gen_pre_cons.
        rewrite IH. reflexivity.
Qed.

Lemma is_constant_ind_gen_cap_pred_lpa_app : forall l1 l2 P (W : Set) (lpa : list (W -> Prop))
    (pa2 : W -> Prop),
length l1 = length lpa ->
is_constant (@ind_gen _ pa2 (indicies_l2 l1 P) lpa) ->
is_constant
  (@ind_gen _ pa2 (indicies_l2 (cap_pred l1 l2 ++ l1) P) (@cap_pred_lpa W lpa l1 l2 ++ lpa)).
Proof.
  unfold is_constant. intros until 0. intros Hl [pa [n H]].
  apply ind_gen_ind_l2_cap_pred_app with (l2 := l2) in H.
  destruct H as [n' H]. exists pa. exists n'. assumption.
  assumption.
Qed.

Lemma consistent_lP_lpa_P_cap_pred_lpa_app : forall l1 l2 P W lpa pa2,
  length l1 = length lpa ->
  @consistent_lP_lpa_P W pa2 l1 lpa P ->
  @consistent_lP_lpa_P W pa2 (app (cap_pred l1 l2) l1)
      (app (cap_pred_lpa lpa l1 l2) lpa) P.
Proof.
  unfold consistent_lP_lpa_P.
  intros until 0. intros Hl H.
  apply is_constant_ind_gen_cap_pred_lpa_app; assumption.
Qed.

Lemma consistent_lP_lpa_cap_pred_lpa_app : forall l1 l2 W lpa pa2,
  length l1 = length lpa ->
  @consistent_lP_lpa W pa2 l1 lpa ->
  @consistent_lP_lpa W pa2 (app (cap_pred l1 l2) l1)
      (app (cap_pred_lpa lpa l1 l2) lpa).
Proof.
  unfold consistent_lP_lpa.
  intros until 0. intros Hl H P. apply consistent_lP_lpa_P_cap_pred_lpa_app.
  assumption.
  apply H.
Qed.


Lemma ind_gen_indicies_l2_cap_pred : forall (lP : list predicate) n (P : predicate) (l2 : list predicate) 
  (W : Set) (lpa : list (W -> Prop)) (pa2 : W -> Prop) pa,
length lP = length lpa ->
(@ind_gen _ pa2 (indicies_l2 lP P) lpa) = constant_l pa n ->
(exists (n' : nat),
@ind_gen _ pa2 (indicies_l2 (cap_pred lP l2) P) (cap_pred_lpa lpa lP l2) =
  constant_l pa n').
Proof.
  induction lP; intros n [Pn] l2 W lpa pa2 pa Hl Hind.
    simpl in *. exists 0. reflexivity.

    simpl in *. unfold indicies_l2 in *.
    destruct a as [Qm]. simpl in *.
    case_eq (is_in_pred (Pred Qm) l2); intros Hin.
      simpl. case_eq (beq_nat Pn Qm); intros Hbeq;
        rewrite Hbeq in *. simpl in *. destruct lpa.
        simpl in *. rewrite ind_gen_nil.
        exists (S (length (indicies_l2_pre (cap_pred lP l2) (Pred Pn) 1))).
        destruct n. discriminate. inversion Hind as [[H1 H2]].
        reflexivity.

          simpl. rewrite Hin.
          rewrite ind_gen_pre_cons.
          rewrite ind_gen_pre_cons in Hind.
          destruct n. discriminate.
          inversion Hind as [[H1 H2]].
          inversion Hl as [Hl'].
          specialize (IHlP _ _ l2 _ _ _ _  Hl' H2).
          destruct IHlP as [n' IH].  rewrite IH.
          exists (S n'). reflexivity.

        destruct lpa. discriminate. simpl in *.
        simpl. rewrite Hin. rewrite ind_gen_pre_cons.
        inversion Hl as [Hl'].
        apply IHlP with (n := n). assumption.
        rewrite ind_gen_pre_cons in Hind. assumption.

      destruct lpa. discriminate. simpl. rewrite Hin.
      case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in Hind.
        simpl in Hind. destruct n. discriminate.
        inversion Hind as [[H1 H2]]. rewrite ind_gen_pre_cons in H2.
        inversion Hl as [Hl'].
        apply (IHlP) with (n := n);  assumption.

        inversion Hl as [Hl'].
        simpl in Hind. rewrite ind_gen_pre_cons in Hind.
        apply IHlP with (n := n); assumption.
Qed.

Lemma is_constant_ind_gen_cap_pred : forall (lP : list predicate) (P : predicate) (l2 : list predicate) 
  (W : Set) (lpa : list (W -> Prop)) (pa2 : W -> Prop),
length lP = length lpa ->
is_constant (@ind_gen _ pa2 (indicies_l2 lP P) lpa) ->
is_constant (@ind_gen _ pa2 (indicies_l2 (cap_pred lP l2) P) (cap_pred_lpa lpa lP l2)).
Proof.
  unfold is_constant.
  intros until 0. intros Hl [pa [n H]].
  apply ind_gen_indicies_l2_cap_pred with (l2 := l2) in H.
  destruct H as [n' H].
  exists pa. exists n'. assumption.
  assumption.
Qed.

Lemma consistent_lP_lpa_P_cap_pred : forall lP P l2 W lpa pa2,
length lP = length lpa ->
@consistent_lP_lpa_P W pa2 lP lpa P ->
@consistent_lP_lpa_P W pa2 (cap_pred lP l2) (cap_pred_lpa lpa lP l2) P.
Proof.
  unfold consistent_lP_lpa_P.
  intros until 0. apply is_constant_ind_gen_cap_pred.
Qed.

Lemma consistent_lP_lpa_cap_pred : forall lP l2 W lpa pa2,
length lP = length lpa ->
@consistent_lP_lpa W pa2 lP lpa ->
@consistent_lP_lpa W pa2 (cap_pred lP l2) (cap_pred_lpa lpa lP l2).
Proof.
  unfold consistent_lP_lpa. intros until 0.
  intros Hl H P. specialize (H P).
  apply consistent_lP_lpa_P_cap_pred; assumption.
Qed.

Lemma lem_a19 : forall lP W Iv Ip Ir pa_l beta pa2,
  length lP = length pa_l ->
  @consistent_lP_lpa W pa2 lP pa_l ->
  SOturnst W Iv (altered_Ip_list Ip pa_l lP) Ir beta <->
  SOturnst W Iv (altered_Ip_list Ip (cap_pred_lpa pa_l lP (preds_in beta)) 
     (cap_pred lP (preds_in beta))) Ir beta.
Proof.
  induction lP; intros W Iv Ip Ir pa_l beta pa2 Hl Hcon.
    simpl in *. do 2 rewrite altered_Ip_list_nil.
    apply bi_refl.

    destruct pa_l. simpl. apply bi_refl.
    inversion Hl as [Hl'].
    pose proof Hcon as Hcon'.
    apply consistent_lP_lpa_cons_rem in Hcon.
    simpl. case_eq (is_in_pred a (preds_in beta)); intros Hin.
      simpl. rewrite altered_Ip__list_consistent_lP_lpa with (pa2:=pa2).
      rewrite altered_Ip__list_consistent_lP_lpa with (pa2:=pa2).
      apply IHlP with (pa2 := pa2).  assumption. assumption. 

      pose proof (consistent_lP_lpa_cap_pred (cons a lP) (preds_in beta)  W (cons P pa_l) pa2) as H.
       simpl in H. rewrite Hin in H.
      apply H. all : try assumption. 

      split; intros SOt.
        apply P_not_occ_alt in SOt.
        apply (IHlP W Iv Ip Ir pa_l beta pa2); assumption.
          rewrite <- P_occ_in_alpha_is_in_pred_equiv. assumption.

        apply P_not_occ_alt.
          rewrite <- P_occ_in_alpha_is_in_pred_equiv. assumption.
        apply (IHlP W Iv Ip Ir pa_l beta pa2); assumption.
Qed.

Lemma lem_a26 : forall (lP : list predicate) (Q : predicate) (atm : SecOrder) 
  (W : Set) (Iv : FOvariable -> W) (x : FOvariable) (pa2 : W -> Prop),
exists (n : nat),
  @ind_gen (W -> Prop) pa2 (indicies_l2_pre lP Q 0)
    (vsS_pa_l Iv (FOv_att_P_l atm lP) (list_Var (length lP) x)) = 
  constant_l (CM_pa2_l_gen Iv (fun2 atm Q) x) n.
Proof.
  induction lP; intros [Qm] atm W Iv x pa2.
    simpl. exists 0. reflexivity.

    simpl. destruct a as [Pn]. simpl.
    simpl. destruct (IHlP (Pred Qm) atm W Iv x pa2) as [n H].
    case_eq (beq_nat Qm Pn); intros Hbeq.
      exists (S n). simpl. rewrite ind_gen_pre_cons. rewrite H.
      rewrite (beq_nat_true _ _ Hbeq).
      reflexivity.

      exists n. rewrite ind_gen_pre_cons. assumption.
Qed.

Lemma lem_a25 : forall lP Q atm W Iv x pa2,
  @consistent_lP_lpa_P W pa2 lP 
    (vsS_pa_l Iv (FOv_att_P_l atm lP) 
      (list_Var (length lP) x)) Q.
Proof.
  unfold consistent_lP_lpa_P. unfold is_constant.
  unfold indicies_l2.
  intros lP Q atm W Iv x pa2. exists (CM_pa2_l_gen Iv (fun2 atm Q) x).
  apply lem_a26.
Qed.


Lemma lem_a27 : forall lP atm W Iv x pa2,
  @consistent_lP_lpa W pa2 lP 
    (vsS_pa_l Iv (FOv_att_P_l atm lP) 
      (list_Var (length lP) x)).
Proof.
  unfold consistent_lP_lpa. intros.
  apply lem_a25.
Qed.

Lemma lem_a31 : forall lP l Q (W : Set) Iv atm x (pa2 : W -> Prop),
exists (n : nat),
   @ind_gen _ pa2 (indicies_l2_pre (cap_pred lP l) Q 0)
     (vsS_pa_l Iv (FOv_att_P_l atm (cap_pred lP l))
        (list_Var (length (cap_pred lP l)) x)) = 
   constant_l (CM_pa2_l_gen Iv (fun2 atm Q) x) n.
Proof.
  induction lP; intros l Q W Iv atm x pa2.
    simpl. exists 0. reflexivity.

    simpl. destruct Q as [Qm]. destruct a as [Pn].
    destruct (IHlP l (Pred Qm) W Iv atm x pa2) as [n H].
    case_eq (is_in_pred (Pred Pn) l); intros Hin.
      simpl. case_eq (beq_nat Qm Pn); intros Hbeq.
        simpl. rewrite ind_gen_pre_cons.
        exists (S n). rewrite H. rewrite (beq_nat_true _ _ Hbeq).
        reflexivity.

        exists n. rewrite ind_gen_pre_cons. assumption.

      simpl. apply IHlP.
Qed.

Lemma lem_a30 : forall lP l Q (W : Set) Iv atm x (pa2 : W -> Prop),
is_constant (@ind_gen _ pa2 (indicies_l2 (cap_pred lP l) Q)
  (vsS_pa_l Iv (FOv_att_P_l atm (cap_pred lP l)) 
  (list_Var (length (cap_pred lP l)) x))).
Proof.
  unfold is_constant.
  unfold indicies_l2.
  intros. exists (CM_pa2_l_gen Iv (fun2 atm Q) x).
  apply lem_a31.
Qed.

Lemma lem_a29 : forall lP Q l atm (W : Set) Iv pa2 x ,
@consistent_lP_lpa_P W pa2 (cap_pred lP l)
 (vsS_pa_l Iv (FOv_att_P_l atm (cap_pred lP l))
        (list_Var (length (cap_pred lP l)) x)) Q.
Proof.
  unfold consistent_lP_lpa_P.
  intros.
  apply lem_a30.
Qed.

Lemma lem_a28 : forall lP l atm (W : Set) Iv pa2 x ,
@consistent_lP_lpa W pa2 (cap_pred lP l)
 (vsS_pa_l Iv (FOv_att_P_l atm (cap_pred lP l))
        (list_Var (length (cap_pred lP l)) x)).
Proof.
  unfold consistent_lP_lpa.
  intros. apply lem_a29.
Qed.


Lemma lem_a21 : forall lP atm beta x W Iv Ip Ir,
AT atm = true ->
SOturnst W Iv (altered_Ip_list Ip
   (vsS_pa_l Iv (FOv_att_P_l atm lP) (list_Var (length lP) x)) lP) Ir beta ->
SOturnst W Iv
  (altered_Ip_list Ip
     (vsS_pa_l Iv (FOv_att_P_l atm (cap_pred lP (preds_in beta)))
        (list_Var (length (cap_pred lP (preds_in beta))) x))
     (cap_pred lP (preds_in beta))) Ir beta.
Proof.
  induction lP; intros atm beta x W Iv Ip Ir Hat SOt.
    simpl in *. assumption.
  
    simpl in *. case_eq (is_in_pred a (preds_in beta));
      intros Hin2. simpl.
      rewrite altered_Ip__list_consistent_lP_lpa with (pa2 := pa_t).
      rewrite altered_Ip__list_consistent_lP_lpa with (pa2 := pa_t) in SOt.
      apply IHlP; try assumption. 

      pose proof (lem_a27 (cons a lP)) as H. simpl in H.
      apply H.

      pose proof (lem_a28 (cons a lP) (preds_in beta) atm W Iv pa_t x) as H. simpl in H.
      rewrite Hin2 in H. apply H.

      apply P_not_occ_alt in SOt. apply IHlP; assumption.
      rewrite P_occ_in_alpha_is_in_pred_equiv in Hin2. assumption.
Qed.

Lemma is_in_pred_l_cap_pred_add : forall l1 l2 l3,
  is_in_pred_l l2 l3 = true ->
  is_in_pred_l (cap_pred l1 l2) l3 = true.
Proof.
  induction l1; intros l2 l3 Hin1. reflexivity.
  simpl. case_eq (is_in_pred a l2); intros Hin2.
    simpl. case_eq (is_in_pred a l3); intros Hin3.
      apply IHl1. assumption.

      rewrite is_in_pred_l_tft with (P := a) in Hin1. discriminate.
      all : try assumption.

    apply IHl1. assumption.
Qed.

Lemma lem_a23 : forall lP l2 atm x,
  ex_FOvar_x_ll x (FOv_att_P_l atm lP) = false ->
  ex_FOvar_x_ll x (FOv_att_P_l atm (cap_pred lP l2)) = false.
Proof.
  induction lP; intros l2 atm x Hex.
    simpl in *. reflexivity.

    simpl in *.
    case_eq (is_in_FOvar x (fun2 atm a)); intros Hin2;
      rewrite Hin2 in *. discriminate.
    case_eq (is_in_pred a l2); intros Hin.
      simpl. rewrite Hin2. apply IHlP. assumption.

      apply IHlP. assumption.
Qed.

Lemma altered_Ip_list_cap_pred_nil :  forall lP beta W Iv Ip Ir lpa,
  cap_pred lP (preds_in beta) = nil ->
  (SOturnst W Iv (altered_Ip_list Ip lpa lP) Ir beta <->
  SOturnst W Iv Ip Ir beta).
Proof.
  induction lP; intros beta W Iv Ip Ir lpa H.
    rewrite altered_Ip_list_nil. apply bi_refl.

    destruct lpa. simpl. apply bi_refl.
    simpl in H.
    case_eq (is_in_pred a (preds_in beta)); intros Hin;
      rewrite Hin in *. discriminate.
    simpl. split; intros SOt.
      apply P_not_occ_alt in SOt.
      apply IHlP in SOt. all : try assumption.
      rewrite P_occ_in_alpha_is_in_pred_equiv in Hin.
      assumption.

      apply P_not_occ_alt.
      rewrite P_occ_in_alpha_is_in_pred_equiv in Hin.
      assumption.
      apply IHlP. all : try assumption.
Qed.

Lemma length_nlist_list_pa : forall n W pa_l,
length (nlist_list_pa W n pa_l) = n.
Proof.
  induction n; intros W pa_l.
    rewrite (nlist_nil W pa_l). reflexivity.

    destruct (nlist_cons W n pa_l) as [pa [pa_l2 H2]].
    rewrite H2. simpl. rewrite IHn. reflexivity.
Qed.

Lemma is_in_pred__l_contrapos : forall l1 l2,
  (forall P, is_in_pred P l2 = false ->
  is_in_pred P l1 = false) ->
  (is_in_pred_l l1 l2 = true).
Proof.
  induction  l1; intros l2 H.
    simpl in *. reflexivity.

    simpl in *. case_eq (is_in_pred a l2); intros Hin.
      apply IHl1. intros P H2. specialize (H P H2).
      destruct P as [Pn]. destruct a as [Qm].
      case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *.
        discriminate.
      assumption.

      specialize (H a Hin). destruct a as [Pn].
      rewrite <- beq_nat_refl in H. discriminate.
Qed. 

Lemma lem_is_in : forall l beta,
is_in_pred_l
  (preds_in
     (replace_pred_l beta (list_pred_not_in l (preds_in beta))
        (nlist_list (length (list_pred_not_in l (preds_in beta)))
           (nlist_Var1 (length (list_pred_not_in l (preds_in beta)))))
        (nlist_list (length (list_pred_not_in l (preds_in beta)))
           (nlist_empty (length (list_pred_not_in l(preds_in beta))))))) l = true.
Proof.
  intros l beta. apply is_in_pred__l_contrapos. intros P H.
  apply jj7. assumption.
Qed. 

Lemma is_in_pred_passing_predSO_l : forall l Q,
  ~ l = nil ->
  is_in_pred Q (preds_in (passing_conj (passing_predSO_l Q l))) = true.
Proof.
  induction l; intros [Qm] Hnil. contradiction (Hnil eq_refl).
  simpl in *. destruct (passing_predSO_l (Pred Qm) l).
    simpl. destruct a. simpl. rewrite <- beq_nat_refl. reflexivity.
  
    simpl preds_in. destruct a. simpl. rewrite <- beq_nat_refl.
    reflexivity.
Qed.

Lemma is_in_pred_app_if : forall l1 l2 P,
  is_in_pred P (app l1 l2) = 
  if is_in_pred P l1 then true else is_in_pred P l2.
Proof.
  induction l1; intros l2 P.
    simpl. destruct P. reflexivity.

    simpl. destruct P as [Pn]. destruct a as [Qm].
    case_eq (beq_nat Pn Qm); intros Hbeq. reflexivity.
    apply IHl1.
Qed.

Lemma lem_is_in5 : forall lP llx P,
  length lP = length llx ->
  ex_nil_in_llv llx = false ->
  is_in_pred P (preds_in (passing_conj (passing_predSO_ll lP llx))) =
  is_in_pred P lP.
Proof.
  induction lP; intros llx [Pn] Hnil Hex. reflexivity.
  simpl. destruct llx. discriminate.
  destruct a as [Qm]. simpl.
  case_eq (passing_predSO_ll lP llx). intros Hp.
    case_eq (beq_nat Pn Qm); intros Hbeq. rewrite (beq_nat_true _ _ Hbeq).
      apply is_in_pred_passing_predSO_l. simpl in *. destruct l; discriminate.

      rewrite P_occ_in_alpha_is_in_pred_equiv.
      rewrite lem_try35. destruct lP. reflexivity.
      destruct llx; discriminate.

      intros H. inversion H as [H']. rewrite H' in *.
      rewrite <- beq_nat_refl in *. discriminate.

      intros beta lbeta Hlbeta.
      rewrite <- Hlbeta.
      case_eq (beq_nat Pn Qm); intros Hbeq.
        simpl. 
        apply is_in_pred_app_l. rewrite (beq_nat_true _ _ Hbeq) in *. 
        apply is_in_pred_passing_predSO_l. simpl in *. destruct l; discriminate.

        simpl.
        rewrite is_in_pred_app_if.
        rewrite P_occ_in_alpha_is_in_pred_equiv.
        rewrite lem_try35. apply IHlP. 
          inversion Hnil.  reflexivity. 
          simpl in Hex. destruct l. discriminate. assumption.
          intros H. inversion H as [H']. rewrite H' in *.
          rewrite <- beq_nat_refl in *. discriminate.
Qed.

Lemma lem_is_in4 : forall l lP llx,
  length lP = length llx ->
  ex_nil_in_llv llx = false ->
  is_in_pred_l l (preds_in (passing_conj (passing_predSO_ll lP llx))) =
  is_in_pred_l l lP.
Proof.
  induction l; intros lP llx Hnil Hex. reflexivity.
  simpl. case_eq (is_in_pred a (preds_in (passing_conj (passing_predSO_ll lP llx))));
    intros Hin; rewrite lem_is_in5 in Hin; try rewrite Hin.
    apply IHl. all : try assumption. reflexivity.
Qed.

Lemma list_pred_not_in_passing_predSO_ll : forall l lP llx,
length lP = length llx ->
ex_nil_in_llv llx = false ->
(list_pred_not_in (preds_in (passing_conj (passing_predSO_ll lP llx))) l) =
(list_pred_not_in lP l).
Proof.
  induction l; intros lP llx Hl Hex. simpl. reflexivity.
  simpl. rewrite lem_is_in5.
  case_eq (is_in_pred a lP); 
    intros Hin. apply IHl. all : try assumption.

    rewrite IHl. reflexivity. all: assumption.
Qed.

Lemma uniform_pos_SO_rep_pred_l : forall lP n beta,
  uniform_pos_SO beta ->
  uniform_pos_SO (replace_pred_l beta lP (nlist_list _ (nlist_Var1 n))
      (nlist_list _ (nlist_empty n))).
Proof.
  induction lP; intros n beta Hun.
    simpl. assumption.

    simpl. destruct n. simpl. assumption.
    simpl. apply uni_pos_rep_pred. reflexivity.
    apply IHlP. assumption.
Qed.

Lemma SOQFree_l_empty : forall n,
  SOQFree_l (nlist_list _ (nlist_empty n)) = true.
Proof.
  induction n. reflexivity.
  simpl. assumption.
Qed.

Lemma lem_a32 : forall lP rel atm,
REL rel = true ->
AT atm = true ->
ex_attached_allFO_llv (conjSO rel atm) (FOv_att_P_l (conjSO rel atm) lP) = false.
Proof.
  induction lP; intros rel atm Hrel Hat. reflexivity.

  simpl. rewrite ex_att_allFO_lv_conjSO_f_rev. apply IHlP.
  all : try assumption.
  apply ex_att_allFO_lv_REL. assumption.
  apply ex_att_allFO_lv_AT. assumption.
Qed.

Lemma ex_att_exFO_lv_conjSO_f_rev : forall lv alpha1 alpha2,
 (ex_attached_exFO_lv alpha1 lv = false) ->
 (ex_attached_exFO_lv alpha2 lv = false) ->
  ex_attached_exFO_lv (conjSO alpha1 alpha2) lv = false.
Proof.
  induction lv; intros alpha1 alpha2 Ha Hb.
    simpl in *. reflexivity.

    simpl in *.
    case_eq (attached_exFO_x alpha1 a); intros H1;
      simpl in Ha; rewrite H1 in Ha. discriminate.
    case_eq (attached_exFO_x alpha2 a); intros H2;
      rewrite H2 in Hb. discriminate.
    apply IHlv; assumption.
Qed.

Lemma  att_exFO_x_REL : forall rel x,
  REL rel = true ->
  attached_exFO_x rel x = false.
Proof.
  induction rel; intros [xn] H; try
    reflexivity;
    try (simpl in *; discriminate).

    simpl in *.
    case_eq (REL rel1); intros H1; rewrite H1 in H.
      2 : discriminate.
    rewrite IHrel1. apply IHrel2.
    all : assumption.
Qed.

Lemma ex_att_exFO_lv_REL : forall lv rel,
  REL rel = true ->
  ex_attached_exFO_lv rel lv = false.
Proof.
  induction lv; intros rel Hrel.
    simpl. reflexivity.

    simpl. rewrite att_exFO_x_REL.
    apply IHlv. all: assumption.
Qed.

Lemma  att_exFO_x_AT : forall rel x,
  AT rel = true ->
  attached_exFO_x rel x = false.
Proof.
  induction rel; intros [xn] H; try
    reflexivity;
    try (simpl in *; discriminate).

    simpl in *.
    case_eq (AT rel1); intros H1; rewrite H1 in H.
      2 : discriminate.
    rewrite IHrel1. apply IHrel2.
    all : assumption.
Qed.

Lemma ex_att_exFO_lv_AT : forall lv rel,
  AT rel = true ->
  ex_attached_exFO_lv rel lv = false.
Proof.
  induction lv; intros rel Hrel.
    simpl. reflexivity.

    simpl. rewrite att_exFO_x_AT.
    apply IHlv. all: assumption.
Qed.

Lemma lem_a33 : forall lP rel atm,
REL rel = true ->
AT atm = true ->
ex_attached_exFO_llv (conjSO rel atm) (FOv_att_P_l (conjSO rel atm) lP) = false.
Proof.
  induction lP; intros rel atm Hrel Hat. reflexivity.

  simpl. rewrite ex_att_exFO_lv_conjSO_f_rev. apply IHlP.
  all : try assumption.
  apply ex_att_exFO_lv_REL. assumption.
  apply ex_att_exFO_lv_AT. assumption.
Qed.