Require Export high_mods.
Require Import SO_facts2 nlist_sem_eg FunctionalExtensionality.
Require Import SO_facts_syn.

(* ----------------------------------- *)

(* creates long disjunction from list FOvariables *)
Fixpoint disj_l (lv : list FOvariable) x : SecOrder :=
  match lv with
  | nil => eqFO (Var 1) (Var 1) (* filler *)
  | cons y nil => eqFO x y
  | cons y lv' => disjSO (eqFO x y) (disj_l lv' x)
  end.

Fixpoint vsS_syn_l (llv : list (list FOvariable)) x : list SecOrder :=
  match llv with
  | nil => nil
  | cons lv llv' => cons (disj_l lv x) (vsS_syn_l llv' x)
  end.

Lemma length_vsS_syn_l : forall l x,
  length l = length (vsS_syn_l l x).
Proof.
  induction l; intros [xn]. reflexivity.
  simpl. rewrite <- IHl. reflexivity.
Qed.

Fixpoint pa_l_disj {W : Set} (Iv : FOvariable -> W) (lv : list FOvariable) (w : W) :=
  match lv with
  | nil => w = w
  | cons y nil => w = Iv y
  | cons y lv' => (w = Iv y) \/ (pa_l_disj Iv lv' w)
  end.

Lemma pa_l_disj_alt : forall lv x (W : Set) Iv (d : W),
  ~ In x lv ->
  pa_l_disj Iv lv = pa_l_disj (alt_Iv Iv d x) lv.
Proof.
  induction lv; intros x W Iv d Hin.
    simpl in *. reflexivity.

    apply functional_extensionality. intros w.
    simpl.
    destruct lv.
      simpl in *. destruct (FOvariable_dec x a). subst. firstorder.
      rewrite alt_Iv_neq; auto.

      remember (f :: lv) as lv'. simpl in Hin.
      apply not_or_and in Hin.  rewrite <- IHlv.
      rewrite alt_Iv_neq. all : firstorder.
Qed.

Inductive pa_l_disj_gen {W : Set} (Iv : FOvariable -> W) lv x : W -> Prop :=
  | pa_l_disj_gen_in : In x lv -> forall w, pa_l_disj_gen Iv lv x w
  | pa_l_disj_gen_tail w : ~ In x lv -> (pa_l_disj Iv lv w) -> pa_l_disj_gen Iv lv x w.

Lemma pa_l_disj_gen_in_pat: forall {W : Set} (Iv : FOvariable -> W) lv x,
  In x lv -> forall w, (pa_l_disj_gen Iv lv x w <-> pa_t w).
Proof.
  induction lv; intros x Hin w. inversion Hin.
  simpl in *. destruct Hin. subst.
  split; intros H. firstorder.
  constructor. firstorder.
  split; intros H2. firstorder.
  constructor. firstorder.
Qed.

Lemma pa_l_disj_gen_not_in : forall {W : Set} (Iv : FOvariable -> W) lv x,
    ~ In x lv ->
    forall w, ( pa_l_disj Iv lv w <-> pa_l_disj_gen Iv lv x w).
Proof.
  intros W Iv lv x H w.
  split; intros H2. constructor 2. auto. auto.
  inversion H2; subst. contradiction. auto.
Qed.

Lemma FO_frame_condition_disj_l : forall l x,
  FO_frame_condition (disj_l l x) = true.
Proof.
  induction l; intros x; simpl; auto.
  destruct l; auto. simpl in *. auto.
Qed.

Lemma FO_frame_condition_l_vsS_syn_l : forall lv x,
  FO_frame_condition_l (vsS_syn_l lv x) = true.
Proof.
  induction lv; intros x; simpl; auto.
  rewrite FO_frame_condition_disj_l. auto.
Qed.

Lemma SOQFree_disj_l : forall l x,
  SOQFree (disj_l l x) = true.
Proof.
  induction l; intros x.
    reflexivity.

    destruct x.
    simpl. destruct l.
      destruct a. reflexivity.

      destruct a.
      simpl. apply IHl.
Qed.

Lemma no_FOquant_disj_l : forall l x,
  FOQFree (disj_l l x) = true.
Proof.
  induction l; intros x. auto.
  simpl. destruct l.  auto. 
  simpl. apply IHl.
Qed.

Fixpoint vsS_pa_l {W : Set} (Iv : FOvariable -> W)  llv lx :=
  match llv, lx with
  | nil, _ => nil
  | _, nil => nil
  | cons lv llv', cons x lx' =>
      cons (pa_l_disj_gen Iv lv x) (vsS_pa_l Iv llv' lx')
  end.

Lemma length_vsS_pa_l : forall {W : Set} lP (Iv : FOvariable -> W) y alpha,
length (vsS_pa_l Iv (FOv_att_P_l alpha lP) (list_var (length lP) y)) = length lP.
Proof. induction lP; intros; simpl; auto. Qed.

Lemma length_vsS_syn_l' : forall l x,
  length l = length (vsS_syn_l l x).
Proof. induction l; simpl; auto. Qed.

Fixpoint passing_conj lalpha : SecOrder :=
  match lalpha with
  | nil => eqFO (Var 1) (Var 1)
  | cons alpha nil => alpha
  | cons alpha lalpha' => conjSO alpha (passing_conj lalpha')
  end.

Fixpoint passing_conj_atm P lx : SecOrder :=
  match lx with
  | nil => eqFO (Var 1) (Var 1)
  | cons x nil => predSO P x
  | cons x lx' => conjSO (predSO P x) (passing_conj_atm P lx')
  end.

Fixpoint passing_predSO_l P lx : list SecOrder :=
  match lx with
  | nil => nil
  | cons x lx' => cons (predSO P x) (passing_predSO_l P lx')
  end .

Fixpoint passing_predSO_ll lP llx : list SecOrder :=
  match lP, llx with
  | nil, _ => nil
  | _, nil => nil
  | cons P lP', cons lx llx' => cons (passing_conj (passing_predSO_l P lx))
                         (passing_predSO_ll lP' llx')
  end .

Lemma lem4 : forall lx P,
passing_conj_atm P lx =
passing_conj (passing_predSO_l P lx).
Proof.
  induction lx; intros P. reflexivity.
  simpl. destruct lx. simpl. reflexivity.
  simpl in *. rewrite IHlx. reflexivity.
Qed.
Lemma lem_try24 : forall l x (W : Set) (Iv : FOvariable -> W),
  In x l ->  pa_l_disj Iv l (Iv x).
Proof.
  induction l; intros x W Iv H. inversion H.
  simpl in *. destruct H. subst. destruct l; firstorder.
  destruct l. inversion H.
  right. apply IHl. auto.
Qed.

Lemma lem_try29_pre : forall l1 l2 {W : Set} Iv (w : W),
l1 <> nil -> incl l1 l2 ->
 pa_l_disj Iv l1 w -> pa_l_disj Iv l2 w.
Proof.
  induction l1; intros l2 W Iv w H1 H2 H3. contradiction.
  simpl in *. destruct l1. subst. apply lem_try24. firstorder.
  destruct H3. subst. apply lem_try24. firstorder. 
  apply IHl1. discriminate. firstorder. auto. 
Qed.

Lemma lem_try29 : forall l1 l2 x {W : Set} (w:W) Iv,
  ~ l1 = nil -> incl l1 l2 ->
  pa_l_disj_gen Iv l1 x w ->
  pa_l_disj_gen Iv l2 x w.
Proof.
  intros l1 l2 x W w Iv H1 H2 H3.
  inversion H3. subst. constructor.  firstorder.
  subst. destruct (in_dec FOvariable_dec x l2).
  constructor 1.  auto.  constructor 2. auto.
  apply (lem_try29_pre l1); auto.
Qed.

Lemma lem_try35 : forall l P Q,
~ P = Q ->
~ Pred_in_SO (passing_conj (passing_predSO_l Q l)) P.
Proof.
  induction l; intros P Q Hneq; unfold Pred_in_SO in *. auto.
  simpl. destruct l. simpl in *. firstorder.
  simpl. apply and_not_or. split; auto.
  apply IHl. auto.
Qed.

Lemma lem_try10 : forall l P,
  FOv_att_P (passing_conj (passing_predSO_l P l)) P = l.
Proof.
  induction l; intros P. auto.
  simpl. case_eq l. intros Hnil. simpl. pred_dec_l_rep.
  intros x lx Hlx. rewrite <- Hlx.
  rewrite Hlx at 1. simpl. pred_dec_l_rep.
  rewrite IHl. auto.
Qed.

Lemma lemma18 : forall l1 l2 (W : Set) (Iv : FOvariable -> W) x w,
  ~l1 = nil ->
  ~l2 = nil ->
 pa_l_disj_gen Iv (app l1 l2) x w <->
 pa_l_disj_gen Iv l1 x w \/  pa_l_disj_gen Iv l2 x w.
Proof.
  induction l1; intros l2 W Iv x w H1 H2. contradiction.
  simpl in *. case_eq l1.
  intros Hl. simpl. 
  simpl. destruct (FOvariable_dec x a); subst.
  + split; intros H; [left |]; constructor; firstorder.
  + split; intros H. destruct (in_dec FOvariable_dec x l2).
    ++ right. constructor. auto.
    ++ destruct l2 as [|y ly]. contradiction.
       remember (y :: ly) as l2.
       inversion H. subst w0. right. constructor.
       simpl in *. destruct H0. symmetry in H0. contradiction.
       auto. subst w0.
       simpl in *. rewrite Heql2 in H3. destruct H3.
       subst.  left. constructor 2. firstorder. apply lem_try24. firstorder.
       rewrite <- Heql2 in H3. right. constructor 2. firstorder. auto.
    ++ destruct H. inversion H. subst w0. constructor. firstorder.
       subst w0. destruct (in_dec FOvariable_dec x l2).
       constructor 1. firstorder. constructor 2. firstorder.
       simpl in *. destruct l2. auto. firstorder. inversion H. subst.
       constructor. firstorder. subst. constructor 2. firstorder.
       simpl in *. destruct l2. contradiction. firstorder.
  + intros y ly Hly. rewrite <- Hly. destruct l2 as [|z lz].
    contradiction. remember (z :: lz) as l2. split; intros H.
    ++ inversion H.
       - subst w0. simpl in H0. destruct H0.
         left. constructor. firstorder. apply in_app_or in H0. destruct H0.
         left. constructor. firstorder. right. constructor. firstorder.
       - subst w0. simpl in H3. rewrite Hly in H3. simpl app in H3.
         assert (match y :: ly ++ l2 with
                 | nil => w = Iv a
                 | _ :: _ => w = Iv a \/ pa_l_disj Iv (y :: ly ++ l2) w
                 end = (w = Iv a \/ pa_l_disj Iv (y :: ly ++ l2) w)) as Hass.
         reflexivity.
         rewrite Hass in H3. change (y :: ly ++ l2) with ((y :: ly) ++ l2) in *.
         rewrite <- Hly in *. destruct H3. subst w. left. constructor 2.
         simpl in *. firstorder. apply lem_try24. firstorder.
         clear Hass. assert (pa_l_disj_gen Iv (l1 ++ l2) x w) as Hass.
         constructor 2. firstorder. auto.
         apply IHl1 in Hass. destruct Hass. left. constructor 2.
         simpl in *. firstorder. simpl. rewrite Hly in *. rewrite <- Hly in *.
         inversion H4. subst. simpl in *. clear -H5 H0. simpl in *.
         destruct H5. firstorder. apply not_or_and in H0. destruct H0 as [H0 H1].
         apply not_or_and in H1. destruct H1 as [H1 H2].
         eapply or_introl in H. apply in_or_app in H. contradiction (H2 H).
         firstorder. firstorder. subst. discriminate. auto.
    ++ destruct H.
       - inversion H. subst. constructor. firstorder. simpl in H3.
         rewrite Hly in H3. rewrite <- Hly in H3. destruct H3. subst w.
         destruct (in_dec FOvariable_dec x l2).
         constructor. simpl in *. firstorder. constructor 2. simpl in *.
         intros HH. destruct HH. firstorder. apply in_app_or in H3. firstorder.
         apply lem_try24. firstorder.
         subst w0. assert (pa_l_disj_gen Iv l1 x w \/ pa_l_disj_gen Iv l2 x w) as Hass.
         left. constructor 2. firstorder. auto.
         apply IHl1 in Hass; auto. inversion Hass. subst. constructor. firstorder.
         subst w0. constructor 2. simpl in *. intros HH. destruct HH. firstorder.
         apply in_app_or in H6. firstorder. simpl.
         rewrite Hly. change ( match (y :: ly) ++ l2 with
  | nil => w = Iv a
  | _ :: _ => w = Iv a \/ pa_l_disj Iv ((y :: ly) ++ l2) w
                               end) with (w = Iv a \/ pa_l_disj Iv ((y :: ly) ++ l2) w).
         rewrite <- Hly. firstorder. rewrite Hly. discriminate.
       - eapply or_intror in H. apply IHl1 in H; auto. inversion H.
         subst. constructor. firstorder. subst w0.
         destruct (FOvariable_dec x a). subst. constructor. firstorder.
         constructor 2. firstorder. simpl. rewrite Hly.
          change ( match (y :: ly) ++ l2 with
  | nil => w = Iv a
  | _ :: _ => w = Iv a \/ pa_l_disj Iv ((y :: ly) ++ l2) w
                               end) with (w = Iv a \/ pa_l_disj Iv ((y :: ly) ++ l2) w).
          rewrite <- Hly. firstorder. rewrite Hly. discriminate.
Qed.

Lemma Pred_in_SO_passing_predSO_l : forall l P Q,
  ~ l = nil ->
  Pred_in_SO (passing_conj (passing_predSO_l Q l)) P ->
  P = Q.
Proof.
  induction l; intros P Q H1 H2. contradiction.
  case_eq l. intros Hl. rewrite Hl in *.
  simpl in *. inversion H2. auto. inversion H.
  intros x lx Hlx. simpl in *.
  case_eq (passing_predSO_l Q l).
    intros Hp. rewrite Hlx in Hp. discriminate.
  intros beta lbeta Hlbeta.
  rewrite Hlbeta in H2. rewrite <- Hlbeta in H2.
  rewrite Pred_in_SO_conjSO in H2.
  destruct H2. inversion H. auto. inversion H0.
  apply IHl. rewrite Hlx. discriminate. auto.
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