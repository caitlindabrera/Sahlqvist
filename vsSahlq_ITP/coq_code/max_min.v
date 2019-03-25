Require Export base_mods.
Require Import nlist_syn_eg ltac_SO FOvars_in.

Lemma max_eq0_l : forall a b,
  max a b = 0 -> a = 0.
Proof.  intros. lia. Qed.

Lemma max_eq0_r : forall a b,
  max a b = 0 -> b = 0.
Proof. intros. lia. Qed.

Fixpoint max_l l : nat :=
  match l with  
  | nil => 0
  | cons n l' => max n (max_l l')
  end.

Fixpoint min_l l : nat :=
  match l with  
  | nil => 0
  | cons n nil => n
  | cons n l' => min n (min_l l')
  end.


Fixpoint max_FOv_l (l : list FOvariable) : nat :=
  match l with
  | nil => 0
  | x :: l' => max (match x with Var xn => xn end) (max_FOv_l l')
  end.

Definition max_FOv alpha := max_FOv_l (FOvars_in alpha).

Lemma max_FOv_l_app : forall l1 l2,
    max_FOv_l (l1 ++ l2) = max (max_FOv_l l1) (max_FOv_l l2).
Proof.
  induction l1; intros l2; auto.
  simpl. dest_FOv_blind. rewrite IHl1.
  apply Nat.max_assoc.
Qed.

Lemma max_FOv_conjSO : forall alpha beta,
  max_FOv (conjSO alpha beta) = max (max_FOv alpha) (max_FOv beta).
Proof.
  intros. unfold max_FOv. simpl. 
  rewrite max_FOv_l_app. auto.
Qed.

Lemma max_FOv_disjSO : forall alpha beta,
  max_FOv (disjSO alpha beta) = max (max_FOv alpha) (max_FOv beta).
Proof.
  intros. unfold max_FOv. simpl. 
  rewrite max_FOv_l_app. auto.
Qed.

Lemma max_FOv_implSO : forall alpha beta,
  max_FOv (implSO alpha beta) = max (max_FOv alpha) (max_FOv beta).
Proof.
  intros. unfold max_FOv. simpl. 
  rewrite max_FOv_l_app. auto.
Qed.

Definition deFOv (x : FOvariable) : nat :=
  match x with Var xn => xn end.

Lemma max_FOv_allFO : forall alpha x,
  max_FOv (allFO x alpha) = max (deFOv x) (max_FOv alpha).
Proof.
  intros alpha x. unfold max_FOv.
  destruct x. simpl. auto.
Qed.

Lemma max_FOv_exFO : forall alpha x,
  max_FOv (exFO x alpha) = max (deFOv x) (max_FOv alpha).
Proof.
  intros alpha x. unfold max_FOv.
  destruct x. simpl. auto.
Qed.

Lemma max_FOv_negSO : forall alpha,
  max_FOv (negSO alpha) = max_FOv alpha.
Proof. unfold max_FOv. simpl. auto. Qed.

Lemma max_FOv_allSO : forall alpha P,
  max_FOv (allSO P alpha) = max_FOv alpha.
Proof. unfold max_FOv. simpl. auto. Qed.

Lemma max_FOv_exSO : forall alpha P,
  max_FOv (exSO P alpha) = max_FOv alpha.
Proof. unfold max_FOv. simpl. auto. Qed.

Lemma max_FOv_relatSO : forall x1 x2,
  max_FOv (relatSO x1 x2) = max (deFOv x1) (deFOv x2).
Proof.
  intros. dest_FOv_blind. 
  unfold max_FOv. simpl. lia. 
Qed.

Lemma max_FOv_eqFO : forall x1 x2,
  max_FOv (eqFO x1 x2) = max (deFOv x1) (deFOv x2).
Proof.
  intros. dest_FOv_blind. 
  unfold max_FOv. simpl. lia. 
Qed.

Lemma max_FOv_predSO : forall P x,
  max_FOv (predSO P x) = deFOv x.
Proof. intros P [xn]. unfold max_FOv. simpl. lia. Qed.

Lemma le_max_FOv_conjSO_l : forall alpha beta,
  max_FOv alpha <= max_FOv (conjSO alpha beta).
Proof. intros. rewrite max_FOv_conjSO. lia. Qed.

Lemma le_max_FOv_conjSO_r : forall alpha beta,
  max_FOv beta <= max_FOv (conjSO alpha beta).
Proof. intros. rewrite max_FOv_conjSO. lia. Qed.

Lemma le_max_FOv_exFO_conjSO: forall alpha gamma x,
(max_FOv (exFO x alpha)) <=  (max_FOv (conjSO gamma (exFO x alpha))).
Proof. intros. apply le_max_FOv_conjSO_r. Qed.

Lemma want19_pre : forall l xn,
    In (Var xn) l -> xn <= max_FOv_l l.
Proof.
  induction l; intros xn H. firstorder.
  simpl in *. destruct H; destruct a.
  inversion H. subst. firstorder.
  apply IHl in H. lia.
Qed.
  
Lemma want19 : forall alpha ym,
  In (Var ym) (FOvars_in alpha) -> ym <= (max_FOv alpha).
Proof. intros. unfold max_FOv. apply want19_pre; auto. Qed.

Lemma max_FOv_l_in_r : forall l n m,
In (Var n) l ->
 m <= max_FOv_l l -> max n m <= max_FOv_l l.
Proof.  intros. apply want19_pre in H. lia. Qed.

Lemma max_FOv_l_in_eq_fwd : forall l1 l2,
  incl l1 l2 -> max_FOv_l l1 <= max_FOv_l l2.
Proof.
  induction l1; intros l2 H1. firstorder.
  simpl in *. destruct a. pose proof (incl_hd _ _ _ _ H1).
  apply incl_lcons in H1.
  apply max_FOv_l_in_r with (m := (max_FOv_l l1)) in H;
  firstorder.
Qed.

Lemma max_FOv_l_in_eq : forall l1 l2,
  incl l1 l2 -> incl l2 l1 ->
  max_FOv_l l1 = max_FOv_l l2.
Proof.
  intros l1 l2 H1 H2. apply Nat.le_antisymm. 
  apply max_FOv_l_in_eq_fwd. auto.
  apply max_FOv_l_in_eq_fwd. auto.
Qed.

Lemma min_l_cons : forall l n,
  min_l (cons n l) = n \/  min_l (cons n l) = (min_l l).
Proof.
  induction l; intros n; simpl. auto.
  case_eq l. lia. intros m l' Hl.
  rewrite <- Hl.
  pose proof (IHl n) as IHl1.
  pose proof (IHl a) as IHl2.
  simpl in *. rewrite Hl in *.
  rewrite <- Hl in *.
  destruct IHl2 as [IHl2' | IHl2'];
    rewrite IHl2'; lia.
Qed.

Lemma min_l_leb_cons2 : forall l n,
  min_l (cons n l) = min_l l -> (min_l l) <= n.
Proof.
  induction l; intros n Hmin. firstorder.
  simpl in *. case_eq l. 
  + intros Hl. rewrite Hl in *. lia.
  + intros n' l' Hl. rewrite Hl in *. lia.
Qed.

Lemma min_l_leb_cons1 : forall ln n,
  ~ ln = nil ->  min_l (cons n ln) = n ->
   n <= (min_l ln).
Proof.
  induction ln; intros n Hnil Hmin.
    simpl in *. contradiction (Hnil eq_refl).

    simpl in *. case_eq ln.
      intros Hl. rewrite Hl in *.
      rewrite <- Hmin. firstorder.

      intros n' l' Hl.
      rewrite Hl in *.
      rewrite <- Hl in *.  lia.
Qed.

Lemma min_l_cons2 : forall l n,
  ~ l = nil ->
  min_l (cons n l) = min n (min_l l).
Proof.
  intros l n Heq.
  simpl. destruct l. contradiction (Heq eq_refl).
  simpl. reflexivity.
Qed.

Lemma aa2 : forall ln n,
(min_l (cons n ln)) <= n.
Proof. intros. simpl. destruct ln; lia. Qed.

Lemma le_min__max_l : forall l,
  (min_l l) <= (max_l l).
Proof. 
  induction l. auto. simpl.
  destruct l; lia.
Qed.

Lemma min_l_app : forall l1 l2,
  ~ l1 = nil ->
  ~ l2 = nil ->
  min_l (app l1 l2) =
  min (min_l l1) (min_l l2).
Proof.
  induction l1; intros l2 Hneq1 Hneq2.
    contradiction (Hneq1 eq_refl).

    simpl app.
    case_eq l1. intros Hl. simpl.
      destruct l2. contradiction (Hneq2 eq_refl).
      reflexivity.

    intros m l1' Hl1; rewrite <- Hl1.
    assert (~ l1 = nil) as H. 
      intros H2. rewrite H2 in Hl1. discriminate.
    rewrite min_l_cons2.
    rewrite min_l_cons2.
    rewrite IHl1.
    rewrite PeanoNat.Nat.min_assoc.
    reflexivity.
    all : try assumption.
    rewrite Hl1. intros. discriminate.
Qed.


Lemma max_l_app : forall l1 l2,
  max_l (app l1 l2) = max (max_l l1) (max_l l2).
Proof.
  induction l1; intros l2.
    reflexivity.

    simpl. rewrite IHl1.
    rewrite PeanoNat.Nat.max_assoc.
    reflexivity.
Qed.

Lemma aa15 : forall n l1 l2,
  ~ l1 = nil ->
  n <= (min_l (app l1 l2)) ->
  n <= (min_l l1).
Proof.
  intros n l1 l2 Hneq H.
  destruct l1. contradiction (Hneq eq_refl).
  destruct l2. rewrite List.app_nil_r in H. assumption.
  rewrite min_l_app in H. lia. discriminate. discriminate.
Qed.

Lemma aa16 : forall l1 l2 n,
   (S (max_l (app l1 l2))) <= n ->
   (S (max_l l1)) <= n.
Proof. intros ? ? ? H. rewrite max_l_app in H. lia. Qed.

Lemma max_FOv_l_list_var : forall n xn,
    max_FOv_l (list_var n (Var xn)) <= xn.
Proof.
  induction n; intros xn. firstorder.
  simpl in *. rewrite Max.max_l; firstorder.
Qed.

Lemma aa22_pre_2_pre_pre2 : forall l xn,
    (forall y : FOvariable, Var xn <> y -> ~ In y l) ->
  In (Var xn) l ->  (max_FOv_l l) <= xn.
Proof.
  intros l xn H1 H2.  apply not_in_list_var in H1.
  destruct H1 as [n H3]. subst. apply max_FOv_l_list_var.
Qed.

Lemma not_in_nil2 : forall l x,
(forall y : FOvariable, x <> y -> ~ In y l) ->
~ In x l -> l = nil.
Proof.
  destruct l ;intros x H1 H2. auto.
  simpl in *. specialize (H1 f). firstorder.
Qed.
  
Lemma aa22_pre_2_pre_pre3 : forall l xn,
(forall y : FOvariable, Var xn <> y -> ~ In y l) ->
  ~ In (Var xn) l ->  max_FOv_l l = 0.
Proof.
  intros l xn H1 H2. rewrite (not_in_nil2 _ _ H1 H2).
  auto.
Qed.

Lemma aa22_pre_2_pre : forall cond xn,
    (forall y : FOvariable, Var xn <> y -> ~ var_in_SO cond y) ->
    (var_in_SO cond (Var xn) ->  max_FOv cond = xn) /\
    (~ var_in_SO cond (Var xn) -> max_FOv cond = 0).
Proof.
  intros cond xn H. unfold max_FOv. unfold var_in_SO.
  split; intros H2.
  + apply PeanoNat.Nat.le_antisymm. apply aa22_pre_2_pre_pre2; auto.
    apply want19_pre. auto.
  + eapply aa22_pre_2_pre_pre3. apply H. apply H2.
Qed.

Lemma aa22_pre_2 : forall cond xn,
  (forall y : FOvariable, Var xn <> y -> ~ var_in_SO cond y) ->
  (var_in_SO cond (Var xn) ->  max_FOv cond = xn).
Proof.  intros. apply aa22_pre_2_pre; assumption. Qed.

