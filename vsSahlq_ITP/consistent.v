Require Import med_mods nlist_sem_eg vsS_syn_sem SO_facts1.

Open Scope nat_scope.

Definition is_constant {A : Type} (l : list A) : Prop :=
  exists a n,  l = repeat a n.

Lemma repeat_is_constant: forall {A : Type} (z:A) n,
  is_constant (repeat z n).
Proof.
  intros A z n. unfold is_constant.
  exists z. exists n. auto.
Qed.

Lemma repeat_cons: forall {A : Type} n l a b,
  (cons b l) = repeat (a:A) n ->  b = a.
Proof.
  intros A. destruct n; intros l a b H.
  discriminate.
  simpl in *. inversion H. auto.
Qed.

Lemma repeat_cons2: forall {A : Type} n l a b1 b2,
  (cons b1 (cons b2 l)) = repeat (a:A) n ->  b2 = a.
Proof.
  intros A. destruct n; intros l a b1 b2 H.
  discriminate. destruct n. discriminate.
  simpl in *. inversion H. auto. 
Qed.

Lemma is_constant_nil : forall {A : Type} (a : A),
  is_constant (@nil A).
Proof.
  intros A a. unfold is_constant. exists a.
  exists 0. auto.
Qed.

(* ------------------ *)

Fixpoint at_pa {W : Set} (n : nat) (l : list (W -> Prop)) : W -> Prop :=
  match n, l with 
  | 0, _ => pa_f
  | _, nil => pa_f
  | 1, (cons x l) => x
  | (S m), (cons x l) => at_pa m l
  end.

Fixpoint ind_pa {W : Set} (l : list nat) (lx : list (W -> Prop)) : 
    list (W -> Prop) :=
  match l with
  | nil => nil
  | cons n l' => cons (at_pa n lx) (ind_pa l' lx)
  end.

Fixpoint indicies_l2_pre lP P count :=
  match lP with
  | nil => nil
  | cons Q lP' => if predicate_dec P Q then cons (1 + count) (indicies_l2_pre lP' P (S count))
        else indicies_l2_pre lP' P (S count)
  end .

Definition indicies_l2 lP P :=
  indicies_l2_pre lP P 0.

Fixpoint at_FOv (n : nat) (l : list FOvariable) : FOvariable :=
  match n, l with 
  | 0, _ => (Var 1)
  | _, nil => (Var 1)
  | 1, (cons x l) => x
  | (S m), (cons x l) => at_FOv m l
  end.

Fixpoint ind_FOv (l : list nat) (lx : list FOvariable) : list FOvariable :=
  match l with
  | nil => nil
  | cons n l' => cons (at_FOv n lx) (ind_FOv l' lx)
  end.


Fixpoint at_cond (n : nat) (l : list SecOrder) : SecOrder :=
  match n, l with 
  | 0, _ => eqFO (Var 1) (Var 1)
  | _, nil => eqFO (Var 1) (Var 1)
  | 1, (cons x l) => x
  | (S m), (cons x l') => at_cond m l'
  end.

Fixpoint ind_cond (l : list nat) (lx : list SecOrder) : list SecOrder :=
  match l with
  | nil => nil
  | cons n l' => cons (at_cond n lx) (ind_cond l' lx)
  end.


Definition consistent_lP_lx_P lP lx P : Prop :=
  is_constant (ind_FOv (indicies_l2 lP P) lx).

Definition consistent_lP_lx lP lx : Prop :=
  forall P, consistent_lP_lx_P lP lx P.

Definition consistent_lP_lcond_P lP lx P : Prop :=
  is_constant (ind_cond (indicies_l2 lP P) lx).

Definition consistent_lP_lcond lP lx : Prop :=
  forall P, consistent_lP_lcond_P lP lx P.

Fixpoint at_llv (n : nat) (llv : list (list FOvariable)) : (list FOvariable) :=
  match n, llv with 
  | 0, _ => nil
  | _, nil => nil
  | 1, (cons x l) => x
  | (S m), (cons x l) => at_llv m l
  end.

Fixpoint ind_llv (l : list nat) (llv : list (list FOvariable))
     : list (list FOvariable) :=
  match l with
  | nil => nil
  | cons n l' => cons (at_llv n llv) (ind_llv l' llv)
  end.

Definition consistent_lP_llv_P lP llv P : Prop :=
  is_constant (ind_llv (indicies_l2 lP P) llv).

Definition consistent_lP_llv lP llv : Prop :=
  forall P, consistent_lP_llv_P lP llv P.

Lemma ind_pa_pre_cons : forall {W : Set} lP P n (pa : W -> Prop) lpa,
  ind_pa (indicies_l2_pre lP P (S n)) (cons pa lpa) =
  ind_pa (indicies_l2_pre lP P n) lpa.
Proof.
  induction lP; intros P n pa lpa. auto.
  simpl. destruct n; destruct lpa;
  destruct (predicate_dec P a); simpl; rewrite IHlP; auto.
Qed.

Lemma ind_cond_ind_l2_pre_cons : forall lP n lcond Q alpha,
  ind_cond (indicies_l2_pre lP Q (S n)) (cons alpha lcond) =
  ind_cond (indicies_l2_pre lP Q n) lcond.
Proof.
  induction lP; intros n lcond Q alpha. auto.
  simpl. destruct (predicate_dec Q a); [destruct n|]; simpl;
       rewrite IHlP; auto.
Qed.

Lemma ind_FOv_ind_l2_pre_cons : forall lP n lcond Q alpha,
  ind_FOv (indicies_l2_pre lP Q (S n)) (cons alpha lcond) =
  ind_FOv (indicies_l2_pre lP Q n) lcond.
Proof.
  induction lP; intros n lcond Q alpha. auto.
  simpl. destruct (predicate_dec Q a); [destruct n|]; simpl;
        rewrite IHlP; auto.
Qed.


Lemma is_constant_ind_FOv_switch : forall lP lx P Q R x y,
  is_constant (ind_FOv (indicies_l2_pre (cons P (cons Q lP)) R 0) (cons x (cons y lx))) ->
  is_constant (ind_FOv (indicies_l2_pre (cons Q (cons P lP)) R 0) (cons y (cons x lx))).
Proof.
  intros lP lx P Q R x y H.
  simpl in *. destruct (predicate_dec R Q); destruct (predicate_dec R P);
    subst; simpl in *; unfold is_constant in *; destruct H as [z [m Heq]];
    exists z, m. destruct m; try discriminate; destruct m; try discriminate.
    simpl in *. inversion Heq. auto.
      all : (repeat rewrite ind_FOv_ind_l2_pre_cons; auto;
        repeat rewrite ind_FOv_ind_l2_pre_cons in Heq; auto).
Qed. 

Lemma is_constant_ind_cond_switch : forall lP lx P Q R x y,
  is_constant (ind_cond (indicies_l2_pre (cons P (cons Q lP)) R 0) (cons x (cons y lx))) ->
  is_constant (ind_cond (indicies_l2_pre (cons Q (cons P lP)) R 0) (cons y (cons x lx))).
Proof.
  intros lP lx P Q R x y H.
  simpl in *. destruct (predicate_dec R Q); destruct (predicate_dec R P);
    subst; simpl in *; unfold is_constant in *; destruct H as [z [m Heq]];
    exists z, m. destruct m; try discriminate; destruct m; try discriminate.
    simpl in *. inversion Heq. auto.
      all : (repeat rewrite ind_cond_ind_l2_pre_cons; auto;
        repeat rewrite ind_cond_ind_l2_pre_cons in Heq; auto).
Qed. 

Lemma consistent_lP_lx_cons_switch : forall lP lx P Q x y,
  consistent_lP_lx (cons P (cons Q lP)) (cons x (cons y lx)) ->
  consistent_lP_lx (cons Q (cons P lP)) (cons y (cons x lx)).
Proof.
  intros lP lx P Q x y H. unfold consistent_lP_lx in *.
  intros R. unfold consistent_lP_lx_P in *.
  unfold indicies_l2 in *.
  specialize (H R).
  apply is_constant_ind_FOv_switch. assumption.
Qed.

Lemma consistent_lP_lcond_cons_switch : forall lP lx P Q x y,
  consistent_lP_lcond (cons P (cons Q lP)) (cons x (cons y lx)) ->
  consistent_lP_lcond (cons Q (cons P lP)) (cons y (cons x lx)).
Proof.
  intros lP lx P Q x y H. unfold consistent_lP_lcond in *.
  intros R. unfold consistent_lP_lcond_P in *.
  unfold indicies_l2 in *.
  specialize (H R).
  apply is_constant_ind_cond_switch. assumption.
Qed.

Lemma consistent_lP_lx_cons_rem : forall lP lx P Q x y,
  consistent_lP_lx (cons P (cons Q lP)) (cons x (cons y lx)) ->
  consistent_lP_lx (cons P lP) (cons x lx).
Proof.
  intros until 0. intros H.
  apply consistent_lP_lx_cons_switch in H.
  unfold consistent_lP_lx in *.
  intros R. specialize (H R).
  unfold consistent_lP_lx_P in *.
  unfold indicies_l2 in *.
  simpl in *.
  destruct (predicate_dec R Q); destruct (predicate_dec R P); subst;
    simpl in *; repeat rewrite ind_FOv_ind_l2_pre_cons in *; simpl in *;
    destruct H as [z [m Heq]];
    destruct m as [|m]; try discriminate;
      try solve [    rewrite Heq; apply repeat_is_constant].
  + destruct m; try discriminate;
    inversion Heq;  exists z, (S m); simpl; auto.
    rewrite H2. auto. 
  + simpl in Heq. inversion Heq. subst. rewrite H1.
    apply repeat_is_constant. 
Qed. 

Lemma consistent_lP_lcond_cons_rem : forall lP lcond P Q x y,
  consistent_lP_lcond (cons P (cons Q lP)) (cons x (cons y lcond)) ->
  consistent_lP_lcond (cons P lP) (cons x lcond).
Proof.
  intros until 0. intros H.
  apply consistent_lP_lcond_cons_switch in H.
  unfold consistent_lP_lcond in *.
  intros R. specialize (H R).
  unfold consistent_lP_lcond_P in *.
  unfold indicies_l2 in *.
  simpl in *. destruct (predicate_dec R Q); destruct (predicate_dec R P); 
                auto;  subst; simpl in *. 
  + rewrite ind_cond_ind_l2_pre_cons in H.
    destruct H as [z [n Heq]]. destruct n. discriminate.
    inversion Heq. exists z, n. assumption.
  + simpl in *. rewrite ind_cond_ind_l2_pre_cons in H.
    destruct H as [z [m Heq]].
    destruct m. discriminate.
    inversion Heq. exists z, m. auto.
  + rewrite ind_cond_ind_l2_pre_cons in H.
    destruct H as [z [m Heq]].
    destruct m. discriminate.
    inversion Heq. exists z, (S m). simpl. rewrite H1. auto.
  + simpl in *. rewrite ind_cond_ind_l2_pre_cons in H.
    destruct H as [z [m Heq]].
    rewrite Heq. apply repeat_is_constant.
Qed.

Lemma consistent_lP_lcond_cons_cons : forall lP lcond P cond,
  consistent_lP_lcond (cons P (cons P lP)) (cons cond (cons cond lcond)) ->
  consistent_lP_lcond (cons P lP) (cons cond lcond).
Proof.
  intros. simpl in *. intros Q. specialize (H Q).
  unfold indicies_l2 in *. simpl in *. unfold consistent_lP_lcond_P in *.
  unfold indicies_l2 in *. simpl in*. 
  destruct (predicate_dec Q P); subst; simpl in *.
  destruct H as [beta [n Heq]]. destruct n. discriminate.
  inversion Heq. exists beta. exists n.
    rewrite ind_cond_ind_l2_pre_cons in H1. assumption.
    rewrite ind_cond_ind_l2_pre_cons in H. assumption.
Qed.

Lemma consistent_lP_lx_cons_cons : forall lP lcond P cond,
  consistent_lP_lx (cons P (cons P lP)) (cons cond (cons cond lcond)) ->
  consistent_lP_lx (cons P lP) (cons cond lcond).
Proof.
  intros. simpl in *. intros Q. specialize (H Q).
  unfold indicies_l2 in *. simpl in *. unfold consistent_lP_lx_P in *.
  unfold indicies_l2 in *. simpl in*. 
  destruct (predicate_dec Q P); subst; simpl in *.
  destruct H as [beta [n Heq]]. destruct n. discriminate.
  inversion Heq. exists beta. exists n.
    rewrite ind_FOv_ind_l2_pre_cons in H1. assumption.
    rewrite ind_FOv_ind_l2_pre_cons in H. assumption.
Qed.

Lemma rep_pred__l_consistent: forall lP lcond lx alpha P cond x,
  FO_frame_condition_l lcond = true ->
  FO_frame_condition cond = true ->
  consistent_lP_lcond (cons P lP) (cons cond lcond) ->
  consistent_lP_lx (cons P lP) (cons x lx) ->
  (replace_pred (replace_pred_l alpha lP lx lcond)
                          P x cond) =
  (replace_pred_l (replace_pred alpha P x cond) 
                          lP lx lcond).
Proof.
  induction lP; intros lcond lx alpha P cond x Hun1 Hun2 Hc1 Hc2. auto.
  destruct lx. auto. destruct lcond. simpl. auto. simpl.
  pose proof Hc1 as Hc1'. pose proof Hc2 as Hc2'.
  unfold consistent_lP_lcond in Hc1.
  unfold consistent_lP_lx in Hc2.
  simpl in Hun1. if_then_else_hyp_zft.
  unfold consistent_lP_lx_P in *.
  unfold consistent_lP_lcond_P in *.
  destruct (predicate_dec P a). subst.
      specialize (Hc1 (a)). specialize (Hc2 (a)).
      simpl in Hc1. simpl in Hc2. 
      unfold indicies_l2 in *.
      simpl in Hc1. simpl in Hc2.  do 2 rewrite predicate_dec_l in Hc2.
      do 2 rewrite predicate_dec_l in Hc1.
      simpl in Hc1. simpl in Hc2. unfold is_constant in *.
      destruct Hc1 as [rep [n Heq1]]. destruct a.
      pose proof (repeat_cons _ _ _ _ Heq1) as Heq1'.
      pose proof (repeat_cons2 _ _ _ _ _ Heq1) as Heq1''.
      rewrite Heq1' in *. rewrite Heq1'' in *.
      destruct Hc2 as [rep2 [n2 Heq2]]. simpl in Heq2.
      pose proof (repeat_cons _ _ _ _ Heq2) as Heq2'.
      pose proof (repeat_cons2 _ _ _ _ _ Heq2) as Heq2''.
      rewrite Heq2' in *. rewrite Heq2'' in *. 

      rewrite IHlP; auto.
        apply consistent_lP_lcond_cons_cons. assumption.
        apply consistent_lP_lx_cons_cons. assumption.
        all : auto.
      pose proof (rep_pred_switch (replace_pred_l alpha lP lx lcond)
          f x s cond a P) as H'.
      simpl in H'. rewrite H'. rewrite IHlP. reflexivity.
        all : try assumption.
        apply consistent_lP_lcond_cons_rem in Hc1. assumption.
        apply consistent_lP_lx_cons_rem in Hc2. assumption.
        auto.
Qed.

Lemma at_cond_nil : forall a,
  at_cond a nil = (eqFO (Var 1) (Var 1)).
Proof.
  induction a. reflexivity.
  simpl. destruct a; reflexivity.
Qed.

Lemma at_llv_nil : forall a,
  at_llv a nil = nil.
Proof.
  induction a. reflexivity.
  simpl. destruct a; reflexivity.
Qed.

Lemma ind_llv_repeat: forall l,
  exists n,
  ind_llv l nil = repeat nil n.
Proof.
  induction l.
    simpl. exists 0. reflexivity.

    simpl. destruct IHl as [n IHl'].
    exists (S n). rewrite IHl'.
    simpl. rewrite at_llv_nil.
    reflexivity.
Qed. 

Lemma ind_llv_nil : forall l,
  is_constant (ind_llv l nil).
Proof.
  intros l. destruct (ind_llv_repeat l) as [n Heq].
    rewrite Heq. apply repeat_is_constant.
Qed.

Lemma consistent_lP_llv_nil : forall lP,
  consistent_lP_llv lP nil .
Proof.
  intros lP [Pn].
  unfold consistent_lP_llv_P.
  apply ind_llv_nil.
Qed.

Lemma ind_llv_pre_cons : forall lP P n cond lcond,
  ind_llv (indicies_l2_pre lP P (S n)) (cons cond lcond) =
  ind_llv (indicies_l2_pre lP P n) lcond.
Proof.
  induction lP; intros P n pa lpa. auto.
  simpl in *. destruct (predicate_dec P a); subst;
  simpl in *; destruct n; destruct lpa;
    rewrite IHlP; auto.
Qed.

Lemma consistent_lP_llv_cons : forall  llv lP P lv,
  consistent_lP_llv (cons P lP) (cons lv llv) ->
  consistent_lP_llv lP llv.
Proof.
  induction llv; intros lP Q lv H.
    apply consistent_lP_llv_nil.
  unfold consistent_lP_llv in *.
  intros P. specialize (H P).
  unfold consistent_lP_llv_P in *.
  unfold indicies_l2 in *.
  simpl in *. destruct (predicate_dec P Q).
  simpl in *. unfold is_constant in *.
  destruct H as [l [n H]].
  rewrite ind_llv_pre_cons in H.
  destruct n. simpl in *. discriminate.
  exists l. exists n. simpl in *. inversion H; auto.
  rewrite ind_llv_pre_cons in H. auto.
Qed.

Lemma at_cond_vsS_syn_l : forall llv n x,
  at_cond n (vsS_syn_l llv x) =
  disj_l (at_llv n llv) x.
Proof.
  induction llv; intros n x.
    simpl. rewrite at_llv_nil. rewrite at_cond_nil.
    simpl. reflexivity.

    simpl. destruct n. simpl. reflexivity.
    simpl. destruct n. reflexivity.
    apply IHllv.
Qed.

Lemma ind_llv_cond_vsS_syn_l : forall lP llv l n x,
  ind_llv lP llv = repeat l n ->
  ind_cond lP (vsS_syn_l llv x) = repeat (disj_l l x) n.
Proof.
  induction lP; intros llv l n x H.
    simpl in *. destruct n. reflexivity.
    simpl in *. discriminate.

    simpl in *. destruct n. discriminate. 
    simpl in *. inversion H as [[H1 H2]].
    rewrite H1 in *.
    rewrite IHlP with (l := l) (n := n).
    rewrite at_cond_vsS_syn_l. rewrite H1.
    reflexivity.

    assumption.
Qed.

Lemma consistent_lP_llv__lcond_P : forall lP llv x P,
  consistent_lP_llv_P lP llv P ->
  consistent_lP_lcond_P lP (vsS_syn_l llv x) P.
Proof.
  intros lP llv x P H.
  unfold consistent_lP_lcond_P in *.
  unfold consistent_lP_llv_P in H. 
  unfold is_constant in H.
  destruct H as [lv [n Heq]].
  apply ind_llv_cond_vsS_syn_l with (x := x) in Heq.
  rewrite Heq. apply repeat_is_constant.
Qed.

Lemma consistent_lP_llv__lcond: forall lP llv x,
  consistent_lP_llv lP llv ->
  consistent_lP_lcond lP (vsS_syn_l llv x).
Proof.
  intros lP llv x H P.
  apply consistent_lP_llv__lcond_P. apply H.
Qed.

Lemma consistent_lP_llv__lcond_cons: forall lP llv lv P x,
  consistent_lP_llv (cons P lP) (cons lv llv) ->
  consistent_lP_lcond (cons P lP) (cons (disj_l lv x) (vsS_syn_l llv x)).
Proof.
  intros. apply (consistent_lP_llv__lcond _ _ x) in H. simpl in H. assumption.
Qed.

Lemma at_FOv_repeat : forall n l2 m x,
   m <= (length l2) ->
  ~ m = 0 ->
  l2 = repeat x n ->
  at_FOv m l2 = x.
Proof.
  induction n; intros l2 m x Hleb Hneq Hcon; simpl in *.
  rewrite Hcon in *. simpl in *. lia.
  rewrite Hcon. destruct m. contradiction (Hneq eq_refl).
  destruct m. reflexivity. 
  rewrite Hcon in Hleb.
  assert (~ S m = 0) as Hneq2.
    intros. discriminate.
  apply (IHn (repeat x n) (S m) x); auto.
  simpl in *. lia.
Qed.

Inductive ex_ind_exceed l n : Prop :=
  | ind_exc m : In m l -> n < m -> ex_ind_exceed l n.

Lemma ex_ind_exceed_not : forall l n,
    ~ ex_ind_exceed l n -> forall m, In m l -> m <= n.
Proof. firstorder. Qed.

Lemma ex_ind_exceed_inv : forall l n,
    ex_ind_exceed l n -> exists m, In m l /\ n < m.
Proof. firstorder. Qed.

Lemma repeat_ind_FOv : forall l1 n l2 a,
  ~ In 0 l1 ->
   l2 = repeat a n ->
  ~ ex_ind_exceed l1 (length l2) ->
  exists m,
    ind_FOv l1 l2 = repeat a m.
Proof.
  induction l1; intros n l2 x Hin Hcon Hex;
    simpl in *. exists 0. reflexivity.
  specialize (ex_ind_exceed_not _ _ Hex) as Hex'.
  destruct n.
  + simpl in *. subst. simpl in *.
    specialize (Hex' a). destruct a. firstorder.
    pose proof (Nat.nle_succ_0 a). firstorder.
  + simpl in *. destruct l2. discriminate.
    inversion Hcon as [[H1 H2]]. subst.
    destruct (IHl1 (S n) (x :: repeat x n) x) as [m Heq]; auto.
    intros HH. inversion HH as [m H3 H4]. firstorder.
    simpl in *. exists (S m). simpl. rewrite Heq.
    pose proof (at_FOv_repeat (S n) (repeat x (S n)) a) as HH.
    simpl in HH. erewrite HH. all : auto. 
Qed.

Lemma is_constant_ind_FOv : forall l1 l2,
  ~ In 0 l1 ->
  is_constant l2 ->
  ~ ex_ind_exceed l1 (length l2) ->
  is_constant (ind_FOv l1 l2).
Proof.
  intros l1 l2 Hin Hcon Hex. unfold is_constant in Hcon.
  destruct Hcon as [x [n Heq]].
  destruct (repeat_ind_FOv l1 n l2 x Hin Heq Hex) as [m Heq'].
  rewrite Heq'. apply repeat_is_constant.
Qed.

Lemma is_in_nat_0_ind_l2_pre : forall lP P  m,
  ~ In 0 (indicies_l2_pre lP P m) ->
  ~ In 0 (indicies_l2_pre lP P (S m)).
Proof.
  induction lP; intros P m H. auto.
  simpl in *.  destruct (predicate_dec P a);
  simpl in *; firstorder. 
Qed.

Lemma is_in_nat_ind_l2 : forall lP P,
~ In 0 (indicies_l2 lP P).
Proof.
  induction lP; intros P; unfold indicies_l2 in *. auto.
  simpl. destruct (predicate_dec P a).
  simpl. intros HH; destruct HH as [H1 | H2]. lia.
  apply is_in_nat_0_ind_l2_pre in H2; auto. intros HH.
  apply is_in_nat_0_ind_l2_pre in HH; auto. 
Qed.

Lemma ex_ind_exceed_cons_fwd : forall l n m,
    ex_ind_exceed l n -> ex_ind_exceed (m :: l) n.
Proof.
  intros l n m [p H1 H2].
  apply (ind_exc _ _ p); firstorder.
Qed.

Lemma ex_ind_exceed_cons : forall l n m,
    ex_ind_exceed (m :: l) n <->
    n < m \/ ex_ind_exceed l n.
Proof.
  intros l n m; split; intros H.
  + inversion H as [p H1 H2].
    simpl in H1. destruct H1 as [H1 | H1].
    subst. firstorder. right.
    pose proof (ind_exc l n p H1 H2).
    apply (ind_exc _ _ p); auto.
  + destruct H as [H | H].
    apply (ind_exc _ _ m); firstorder.
    apply ex_ind_exceed_cons_fwd. auto.
Qed.

Lemma ex_ind_exceed_ind_l2_pre_suc : forall lP P n m,
  ex_ind_exceed (indicies_l2_pre lP P (S n)) (S m) <->
  ex_ind_exceed (indicies_l2_pre lP P n) m.
Proof.
  induction lP; intros P n m. firstorder.
  simpl.
  destruct (predicate_dec P a); subst.
  split; intros HH; apply ex_ind_exceed_cons in HH;
    destruct HH as [HH1 | HH1]; apply ex_ind_exceed_cons.
  firstorder. right. apply IHlP; auto.
  left. lia. right. apply IHlP in HH1. auto.
  auto.
Qed.

Lemma ex_ind_exceed_ind_l2 : forall lP P n,
  (length lP) <= n ->
  ~ ex_ind_exceed (indicies_l2 lP P) n.
Proof.
  induction lP; intros P n Hleb; auto;
    unfold indicies_l2.
  simpl in *. destruct n; inversion Hleb;
    simpl; firstorder.
  simpl in *. destruct (predicate_dec P a);
  subst; simpl. intros HH. apply ex_ind_exceed_cons in HH.
  destruct HH. lia. destruct n. lia.
  apply (ex_ind_exceed_ind_l2_pre_suc _ _ 0) in H.
  eapply IHlP. 2 : apply H. lia.
  destruct n. lia. intros HH.
  apply (ex_ind_exceed_ind_l2_pre_suc _ _ 0) in HH.
  eapply IHlP. 2 : apply HH. lia.
Qed.

Lemma consistent_lP_lx_repeat : forall lP n x,
   (length lP) <= n ->
consistent_lP_lx lP (repeat x n).
Proof.
  intros lP n x H P.
  unfold consistent_lP_lx_P.
  apply is_constant_ind_FOv.
    apply is_in_nat_ind_l2.
    apply repeat_is_constant.
    rewrite repeat_length.
    apply ex_ind_exceed_ind_l2.
    assumption.
Qed.

Fixpoint at_gen {A : Type} {a : A} (n : nat) (l : list A) : A :=
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
  forall P, @consistent_lP_lpa_P W pa lP lpa P.


Lemma ind_gen_pre_cons : forall {A : Type} lP P n (pa pa2 : A) lpa,
  @ind_gen A pa2 (indicies_l2_pre lP P (S n)) (cons pa lpa) =
  @ind_gen A pa2 (indicies_l2_pre lP P n) lpa.
Proof.
  induction lP; intros P n pa pa2 lpa. auto.
  destruct n; simpl;
  destruct (predicate_dec P a); simpl; subst; destruct lpa;
      simpl; rewrite IHlP; auto.
Qed.

Lemma consistent_lP_lpa_P_cons_rem : forall lP P Q W lpa pa1 pa0,
  @consistent_lP_lpa_P W pa0 (cons P lP) (cons pa1 lpa) Q ->
  @consistent_lP_lpa_P W pa0 lP lpa Q.
Proof.
  unfold consistent_lP_lpa_P.
  unfold indicies_l2. intros lP P Q W lpa pa1 p0.
  simpl in *. destruct (predicate_dec Q P); subst; simpl in *.
    rewrite ind_gen_pre_cons. intros [pa2 [n H]]. 
    destruct n. discriminate.
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

Lemma consistent_lP_lpa_vsS_pa_l : forall lP Q (W:Set) (Iv : FOvariable -> W) lv llv x pa0,
  @consistent_lP_lpa _ pa0 (cons Q lP) (vsS_pa_l Iv (cons lv llv) (list_var (length (cons Q lP)) x)) ->
  @consistent_lP_lpa _ pa0 lP (vsS_pa_l Iv llv (list_var (length lP) x)).
Proof.
  intros until 0. intros H. simpl in *. apply consistent_lP_lpa_cons_rem in H.
  assumption.
Qed.


Lemma something1: forall lP P alpha,
exists n,
(ind_llv (indicies_l2 lP P)
        (FOv_att_P_l alpha lP)) = repeat (FOv_att_P alpha P) n.
Proof.
  induction lP; intros P alpha. exists 0. auto.
  simpl. unfold indicies_l2. simpl.
  destruct (predicate_dec P a) as [H2|H2]; subst.
  destruct (IHlP a alpha) as [n H]; exists (S n);
  simpl in *; rewrite ind_llv_pre_cons; unfold indicies_l2 in H.
  rewrite H. auto.
  destruct (IHlP P alpha) as [n H]; exists n;
  simpl in *; rewrite ind_llv_pre_cons; unfold indicies_l2 in H.
  rewrite H. auto. 
Qed.

Lemma consistent_lP_llv_FOv_att_P_l : forall lP alpha,
  consistent_lP_llv lP (FOv_att_P_l alpha lP).
Proof.
  intros lP alpha P.
  unfold consistent_lP_llv_P.
  unfold is_constant.
  exists (FOv_att_P alpha P). apply something1.
Qed.

Lemma lem1a_pre : forall {W : Set} lP (Iv : FOvariable -> W) alpha y,
forall P : predicate,
exists (n : nat),
  ind_pa (indicies_l2 lP P) (vsS_pa_l Iv (FOv_att_P_l alpha lP) (list_var (length lP) y)) =
  repeat (pa_l_disj_gen Iv (FOv_att_P alpha P) y) n.
Proof.
  intros W. induction lP; intros Iv alpha y P. exists 0. auto.
  simpl. unfold indicies_l2. simpl. 
  destruct (predicate_dec P a) as [H2 | H2];
    subst; simpl; rewrite ind_pa_pre_cons.
  + destruct (IHlP Iv alpha y a) as [n H]; 
      unfold indicies_l2 in H. 
    exists (S n). rewrite H. auto. 
  + destruct (IHlP Iv alpha y P) as [n H]; 
      unfold indicies_l2 in H. 
    exists n. auto.
Qed.

Lemma lem1a : forall {W : Set} lP (Iv : FOvariable -> W) alpha y,
forall P : predicate,
exists (n : nat) (pa : W -> Prop),
  ind_pa (indicies_l2 lP P) (vsS_pa_l Iv (FOv_att_P_l alpha lP) (list_var (length lP) y)) =
  repeat pa n.
Proof.
  intros W lP Iv alpha y P. 
  destruct (lem1a_pre lP Iv alpha y P) as [n H].
  exists n. exists (pa_l_disj_gen Iv (FOv_att_P alpha P) y).
  rewrite H. reflexivity.
Qed.

Lemma at_pa_gen : forall (W : Set) (l : list (W -> Prop)) n,
  at_pa  n l = @at_gen (W -> Prop) pa_f n l.
Proof.
  induction l; intros n. destruct n; reflexivity.
  destruct n. reflexivity. simpl. destruct n. reflexivity.
  apply IHl. 
Qed.

Lemma ind_pa_gen : forall W l1 l2,
  @ind_pa W l1 l2 = @ ind_gen (W -> Prop) pa_f l1 l2.
Proof.
  induction l1; intros l2. reflexivity.
  simpl. rewrite IHl1. rewrite at_pa_gen. reflexivity.
Qed.

Lemma lem1a_cons : forall lP alpha (W :Set) (Iv : FOvariable -> W) y,
@consistent_lP_lpa W pa_f lP (vsS_pa_l Iv (FOv_att_P_l alpha lP) (list_var (length lP) y)).
Proof.
  intros until 0. intros P. unfold consistent_lP_lpa_P.
  unfold is_constant. destruct (lem1a lP Iv alpha y P) as [n [pa HH]].
  exists pa. exists n. rewrite ind_pa_gen in HH. assumption.
Qed.

Lemma consistent_lP_lcond_P_disj_l_FOv_att_P_l : forall P l beta y,
  consistent_lP_lcond_P l (vsS_syn_l (FOv_att_P_l beta l) y) P.
Proof.
  intros P l beta y.
  unfold consistent_lP_lcond_P.
  unfold is_constant.
  destruct (something1 l P beta) as [n H2].
  exists (disj_l (FOv_att_P beta P) y). exists n.
  apply ind_llv_cond_vsS_syn_l. assumption.
Qed.

Lemma consistent_lP_lcond_disj_l_FOv_att_P_l : forall l beta y,
  consistent_lP_lcond l (vsS_syn_l (FOv_att_P_l beta l) y).
Proof.
  unfold consistent_lP_lcond.
  intros. apply consistent_lP_lcond_P_disj_l_FOv_att_P_l.
Qed.

 Lemma something2 : forall n l1 P x,
length l1 = n ->
exists m,
ind_FOv (indicies_l2 l1 P) (repeat x n) =
repeat x m.
Proof.
  induction n; intros l1 P x H.
    simpl. unfold indicies_l2.
    destruct l1. simpl. exists 0. reflexivity.
    discriminate.

    destruct l1. discriminate. simpl in *.
    unfold indicies_l2 in *.
    simpl. destruct (predicate_dec P p); 
      simpl; rewrite ind_FOv_ind_l2_pre_cons;
      inversion H as [H'];
      destruct (IHn _ P x H') as [m IH].
    + exists (S m); rewrite H'; rewrite IH;
      reflexivity.
    + exists (m). rewrite H'; auto.
Qed.

Lemma please5 : forall n l1 x,
  length l1 = n ->
consistent_lP_lx l1 (repeat x n).
Proof.
  unfold consistent_lP_lx. unfold consistent_lP_lx_P.
  intros n l1 x H P. unfold is_constant.
  destruct (something2 n l1 P x H) as [m HH].
  exists x. exists m. assumption.
Qed.

Lemma please2 : forall l alpha beta y,
   incl (preds_in alpha) l ->
  FO_frame_condition
    (replace_pred_l alpha l
       (list_var (length l) y)
       (vsS_syn_l (FOv_att_P_l beta l) y)) = true.
Proof.
  induction l; intros alpha beta y H.
     simpl in *. apply incl_nil_r in H.
    apply FO_frame_condition_preds_in_rev. assumption.

    simpl. rewrite rep_pred__l_consistent.
    apply IHl. apply please4.
      apply FO_frame_condition_disj_l.
      assumption.
      apply FO_frame_condition_l_vsS_syn_l.
      apply FO_frame_condition_disj_l.
      pose proof (consistent_lP_lcond_disj_l_FOv_att_P_l (cons a l)) as H2.
      simpl in H2. apply H2.

      rewrite repeat_list_var.
      apply (please5 (length (cons a l)) (cons a l) y).
      apply eq_refl.
Qed.

Lemma lem_c8 : forall lP1 lP2 lx1 lx2 n P Q R x y z,
  length lP1 = length lx1 ->
  ind_FOv (indicies_l2 (app lP1 (cons P (cons Q lP2))) R)
          (app lx1 (cons x (cons y lx2))) = repeat z n ->
  exists m,
  ind_FOv (indicies_l2 (app lP1 (cons Q (cons P lP2))) R)
          (app lx1 (cons y (cons x lx2))) = repeat z m.
Proof.
  induction lP1; intros lP2 lx1 lx2 n P Q R x y z Hlength H.
    simpl in *. symmetry in Hlength.
    apply List.length_zero_iff_nil in Hlength.
    rewrite Hlength in *. unfold indicies_l2 in *. simpl  in *.
    destruct (predicate_dec R Q); destruct (predicate_dec R P);
        simpl in *. exists n. destruct n. discriminate. destruct n.
        discriminate. inversion H. rewrite H3. reflexivity.

        all : try (rewrite ind_FOv_ind_l2_pre_cons in *;
        rewrite ind_FOv_ind_l2_pre_cons in *;
        exists n; assumption).

    simpl in *. unfold indicies_l2 in *.
    simpl in *. destruct (predicate_dec R a).
      simpl in *. destruct lx1. discriminate.
      simpl in *. rewrite ind_FOv_ind_l2_pre_cons in *.
      destruct n. discriminate.
      inversion H as [[Ha Hb]].
      inversion Hlength as [Hlength'].
      destruct (IHlP1 _ _ _ _ _ _ _ _ _ _ Hlength' Hb) as [m Hm].
      exists (S m). rewrite Hm. reflexivity.

      destruct lx1. discriminate. simpl in *.
      rewrite ind_FOv_ind_l2_pre_cons in *.
      inversion Hlength as [Hlength'].
      destruct (IHlP1 _ _ _ _ _ _ _ _ _ _  Hlength' H) as [m Hm].
      exists m. assumption.
Qed.

Lemma ind_llv_ind_l2_pre_cons : forall lP n lcond Q alpha,
  ind_llv (indicies_l2_pre lP Q (S n)) (cons alpha lcond) =
  ind_llv (indicies_l2_pre lP Q n) lcond.
Proof.
  induction lP; intros n lcond Q alpha. auto.
  simpl. destruct (predicate_dec Q a); auto.  
  simpl. destruct n; rewrite IHlP; reflexivity.
Qed.

Lemma consistent_lP_lx_P_cons_switch_gen : forall lP0 lx0 lP lx P Q R x y,
  length lP0 = length lx0 ->
  consistent_lP_lx_P (app lP0 (cons P (cons Q lP))) (app lx0 (cons x (cons y lx))) R ->
  consistent_lP_lx_P (app lP0 (cons Q (cons P lP))) (app lx0 (cons y (cons x lx))) R.
Proof.
  intros until 0. intros Hlength Hcon.
  unfold consistent_lP_lx_P in *.
  unfold is_constant in *. destruct Hcon as [a [n H]].
  exists a.
  apply (lem_c8 lP0 lP lx0 lx n P Q R x y a Hlength). assumption.
Qed.

Lemma consistent_lP_lx_cons_switch_gen : forall lP0 lx0 lP lx P Q x y,
  length lP0 = length lx0 ->
  consistent_lP_lx (app lP0 (cons P (cons Q lP))) (app lx0 (cons x (cons y lx))) ->
  consistent_lP_lx (app lP0 (cons Q (cons P lP))) (app lx0 (cons y (cons x lx))).
Proof.
  intros until 0. intros Hlength Hcon.
  unfold consistent_lP_lx in *. intros R.
  apply consistent_lP_lx_P_cons_switch_gen.
  assumption. apply Hcon.
Qed.

Lemma lem_try26  : forall l l' P x y,
  consistent_lP_lx (cons P (cons P l)) (cons x (cons y l')) ->
  x = y.
Proof.
  induction l; intros l' P x y H.
  + unfold consistent_lP_lx in H.
    unfold consistent_lP_lx_P in H.
    specialize (H P). unfold indicies_l2 in H.
    simpl in *. pred_dec_l_rep. 
    simpl in *. unfold is_constant in H.
    destruct H as [z [n H]].
    destruct n. discriminate.
    destruct n. discriminate.
    simpl in *. inversion H. reflexivity.
  + destruct l'.
    ++ unfold consistent_lP_lx in *. pose proof H as H'.
       specialize (H a). unfold consistent_lP_lx_P in H. unfold indicies_l2 in *.
       simpl in *. destruct (predicate_dec a P) as [HH | HH]; simpl in *.
       * unfold is_constant in H. destruct H as [z [n H]]. 
         destruct n. discriminate.
         destruct n. discriminate. simpl in *. inversion H. reflexivity.
       * unfold is_constant in H. destruct H as [z [n H]]. pred_dec_l_rep.
         destruct n. discriminate. simpl in *. inversion H as [[H1 H2]].
         destruct l. simpl in *.  
         simpl in *. apply (IHl nil P x y).
         intros Q. unfold consistent_lP_lx_P in *.
         unfold is_constant in *. specialize (H' P).
         destruct H' as [x' [n' H']].
         unfold indicies_l2 in *. simpl in *.
         pred_dec_l_rep.
         destruct (predicate_dec Q P) as [HH2 | HH2]. subst.
         ** destruct n'. discriminate. destruct n'. discriminate.
            simpl in *. inversion H'. exists x'. exists (S (S n')). 
            rewrite predicate_dec_r in H4; auto. simpl in H4.  
            simpl. rewrite <- H4. auto.
         ** simpl. exists (Var 1). exists 0. reflexivity.
         ** rewrite ind_FOv_ind_l2_pre_cons in *.
            rewrite ind_FOv_ind_l2_pre_cons in H2.
            simpl in *. specialize (H' P).
            unfold consistent_lP_lx_P in H'. unfold indicies_l2 in H'. simpl in H'.
            pred_dec_l_rep. destruct (predicate_dec P a). symmetry in e. contradiction.
            destruct H' as [u [un Hun]]. destruct un. discriminate.
            destruct un. discriminate. inversion Hun. reflexivity.
    ++ apply (IHl l' P x y).
       change (cons P (cons P (cons a l))) with 
           (app (cons P nil) (cons P (cons a l))) in *.
       change (cons x (cons y (cons f l'))) with
           (app (cons x nil) (cons y (cons f l'))) in *.
       apply consistent_lP_lx_cons_switch_gen in H.
       simpl in H.
       apply consistent_lP_lx_cons_rem in H. assumption.
       reflexivity.
Qed.

Lemma consistent_lP_lx_cons_rem_gen : forall lP lx P x,
  consistent_lP_lx (cons P lP) (cons x lx) ->
  consistent_lP_lx lP lx.
Proof.
  intros until 0. intros H.
  unfold consistent_lP_lx in *.
  unfold consistent_lP_lx_P in *.
  unfold indicies_l2 in *.
  intros Q. specialize (H Q).
  unfold is_constant in *.
  destruct H as [y [n H]]. simpl in *.
  destruct (predicate_dec Q P).
    simpl in *. destruct n. discriminate.
    inversion H as [[H1 H2]].
    rewrite ind_FOv_ind_l2_pre_cons in *.
    exists y. exists n. assumption.

    rewrite ind_FOv_ind_l2_pre_cons in *.
    exists y. exists n. assumption.
Qed.

Lemma consistent_lP_llv_cons_rem_gen : forall lP lx P x,
  consistent_lP_llv (cons P lP) (cons x lx) ->
  consistent_lP_llv lP lx.
Proof.
  intros until 0. intros H.
  unfold consistent_lP_llv in *.
  unfold consistent_lP_llv_P in *.
  unfold indicies_l2 in *.
  intros Q. specialize (H Q).
  unfold is_constant in *.
  destruct H as [y [n H]]. simpl in *.
  destruct (predicate_dec Q P).
    simpl in *. destruct n. discriminate.
    inversion H as [[H1 H2]].
    rewrite ind_llv_ind_l2_pre_cons in *.
    exists y. exists n. assumption.

    rewrite ind_llv_ind_l2_pre_cons in *.
    exists y. exists n. assumption.
Qed.
