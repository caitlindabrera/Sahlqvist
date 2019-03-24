Require Export low_mods Modal_semantics SO_semantics.
Require Import pv_in at_pv occ_in_modal pv_in_modal FOvars_in.
Require Import FunctionalExtensionality.

Definition next_FOv (x : FOvariable) : FOvariable :=
  match x with Var xn => Var (xn + 1) end.

Lemma next_FOv_not : forall x,
    next_FOv x <> x.
Proof. intros [xn] H. inversion H. lia. Qed.

(* Definition of the standard translation from modal to SOL. *)
Fixpoint ST (phi: Modal) (x:FOvariable) : SecOrder :=
  match phi with
    atom (pv n) => predSO (Pred n) x
  | mneg psi => negSO (ST psi x)
  | mconj psi1 psi2 => conjSO (ST psi1 x) (ST psi2 x)
  | mdisj psi1 psi2 => disjSO (ST psi1 x) (ST psi2 x)
  | mimpl psi1 psi2 => implSO (ST psi1 x) (ST psi2 x)
  | box psi => allFO (next_FOv x) (implSO (relatSO x (next_FOv x)) (ST psi (next_FOv x)))
  | diam psi => exFO (next_FOv x) (conjSO (relatSO x (next_FOv x)) (ST psi (next_FOv x)))
    end.

Definition ST_pv (p : propvar) : predicate :=
  match p with
    pv n => Pred n
  end.

Lemma ST_pv_P : forall n : nat,
  Pred n = ST_pv (pv n).
Proof.
  intros n; reflexivity.
Qed.

Definition ST_pred (P : predicate) : propvar :=
  match P with
    Pred n => pv n
  end.

(* Converts modal valuation to SO interpretation on predicates. *)
Fixpoint V_to_Ip (W:Set) (V: propvar -> W -> Prop) (P: predicate) (w:W) : Prop :=
  match P with 
    Pred n => V (pv n) w
  end.

(* Converts SO interpretation on predicates to modal valuation. *)
Fixpoint Ip_to_V (W:Set) (Ip: predicate -> W -> Prop) (p: propvar) (w:W) : Prop :=
  match p with 
    pv n => Ip (Pred n) w
  end.

(* Lemmas that show going from V to Ip and back to V is just the same as V.
   And for Ip to V to Ip. *)
Lemma V_Ip_V: forall (W:Set) (V: propvar -> W -> Prop),
  Ip_to_V W (V_to_Ip W V) = V.
Proof.
  intros.
  apply functional_extensionality.
  intros p.
  apply functional_extensionality.
  intros w.
  destruct p.
  unfold V_to_Ip.
  unfold Ip_to_V.
  reflexivity.
Qed.

Lemma Ip_V_Ip: forall (W:Set) (Ip: predicate -> W -> Prop),
  V_to_Ip W (Ip_to_V W Ip) = Ip.
Proof.
  intros.
  apply functional_extensionality.
  intros p.
  apply functional_extensionality.
  intros w.
  destruct p.
  unfold V_to_Ip.
  unfold Ip_to_V.
  reflexivity.
Qed.

Lemma ST_conj: forall (psi_1 psi_2: Modal) (x:FOvariable), 
                   ST (mconj psi_1 psi_2) x = conjSO (ST psi_1 x) (ST psi_2 x).
Proof.
  simpl; reflexivity.
Qed.

Lemma simpl_alt_l : forall (W:Set) (u v:W) (Iv: FOvariable -> W) (Ip: predicate -> W -> Prop)
                  (xn: nat), 
                      (alt_Iv (alt_Iv Iv u (Var xn)) v (Var (xn+1))) (Var xn) = u.
Proof.
  intros W u v Iv Ip xn.
  unfold alt_Iv.
  rewrite FOvariable_dec_r. rewrite FOvariable_dec_l; firstorder.
  intros H. inversion H. firstorder.
Qed.

Lemma simpl_alt_r : forall (W:Set) (u v:W) (Iv: FOvariable -> W) (Ip: predicate -> W -> Prop)
                  (xn: nat), 
                      (alt_Iv (alt_Iv Iv u (Var xn)) v (Var (xn+1))) (Var (xn+1)) = v.
Proof.
  intros W u v Iv Ip xn.
  unfold alt_Iv. rewrite FOvariable_dec_l; auto.
Qed.

Lemma R_relatSO : forall (W:Set) (R: W -> W -> Prop) (u v:W) (Iv: FOvariable -> W) 
                         (Ip: predicate -> W -> Prop) (xn:nat),
       (R u v)
     <-> (SOturnst W (alt_Iv (alt_Iv Iv u (Var xn)) v (Var (xn+1))) Ip R (relatSO (Var xn) (Var (xn+1)))).
Proof.
  intros W R u v Iv Ip xn.
  unfold SOturnst.
  rewrite simpl_alt_l.
    rewrite simpl_alt_r.
      unfold iff; apply conj; intro H; exact H.

    exact Ip.
  exact Ip.
Qed.

Lemma preds_in_ST_FOv : forall (phi : Modal) (x y : FOvariable),
  preds_in (ST phi x) = preds_in (ST phi y).
Proof.
  induction phi; intros x y;
    try (simpl;
    rewrite (IHphi1 x y);
    rewrite (IHphi2 x y);
    reflexivity);
    try (simpl; destruct x as [xn]; destruct y as [ym];
    simpl;
    rewrite (IHphi (Var (xn + 1)) (Var (ym + 1)));
    reflexivity).

    destruct p as [n]; destruct x; destruct y;
    reflexivity.

    simpl; apply IHphi.
Qed.

Lemma pv_in__preds_in : forall (phi : Modal) ( x : FOvariable),
  length (pv_in phi) = length (preds_in (ST phi x)).
Proof.
  induction phi; intros x;
    try destruct p; destruct x;
    try (simpl;
    do 2  rewrite app_length;
    rewrite <- IHphi1;
    rewrite <- IHphi2;
    reflexivity);
    try (simpl;
    rewrite <- IHphi;
    reflexivity;
    simpl; apply IHphi);
    try reflexivity.
Qed.

Lemma at_pv_ST_nocon_app : forall phi1 phi2 x i,
 (forall (x : FOvariable) (i : nat),
       ST_pv (at_pv (pv_in phi1) i) = at_pred (preds_in (ST phi1 x)) i) ->
(forall (x : FOvariable) (i : nat),
           ST_pv (at_pv (pv_in phi2) i) = at_pred (preds_in (ST phi2 x)) i) ->
  ST_pv (at_pv (pv_in phi1 ++ pv_in phi2) i) =
  at_pred (preds_in (ST phi1 x) ++ preds_in (ST phi2 x)) i.
Proof.
  intros phi1 phi2 x i IH1 IH2.
  destruct (Compare_dec.le_lt_dec i (length (pv_in phi1))) as [H1|H1].
  rewrite at_pv_app_l. rewrite at_pred_app_l. apply IH1.
  rewrite <- pv_in__preds_in. all : try auto.
  assert (exists i', i = length (pv_in phi1) + i') as Hass.
    exists (i - length (pv_in phi1)). firstorder.
  destruct Hass as [i' Hass]. rewrite Hass in *.
  assert ( i' <> 0) as Hass2'.
    intros HH. subst. lia.
  rewrite at_pv_app_r. erewrite pv_in__preds_in. rewrite at_pred_app_r.
  apply IH2. all : auto.
Qed.
  
Lemma at_pv_ST_conjSO : forall (phi1 phi2 : Modal) ( x : FOvariable) (i : nat),
  (forall (x : FOvariable) (i : nat),
       ST_pv (at_pv (pv_in phi1) i) = at_pred (preds_in (ST phi1 x)) i) ->
  (forall (x : FOvariable) (i : nat),
       ST_pv (at_pv (pv_in phi2) i) = at_pred (preds_in (ST phi2 x)) i) ->
  ST_pv (at_pv (pv_in (mconj phi1 phi2)) i) = at_pred (preds_in (ST (mconj phi1 phi2) x)) i.
Proof.
  intros phi1 phi2 x i IHphi1 IHphi2;  simpl.
  destruct (Compare_dec.le_dec i (length (pv_in phi1))) as [H | H].
    rewrite at_pv_app_l; auto. rewrite at_pred_app_l. apply IHphi1.
    rewrite <- pv_in__preds_in. auto.
  assert (exists i', i = length (pv_in phi1) + i') as Hass.
    exists (i - length (pv_in phi1)). firstorder.
  destruct Hass as [i' Hass]. rewrite Hass in *.
  assert ( i' <> 0) as Hass2'.
    intros HH. subst. lia.
  rewrite at_pv_app_r; auto. 
  erewrite pv_in__preds_in. rewrite at_pred_app_r; auto.
Qed.

Lemma at_pv_ST : forall (phi : Modal) ( x : FOvariable) (i : nat),
  ST_pv (at_pv (pv_in phi) i) = at_pred (preds_in (ST phi x)) i.
Proof.
  induction phi; intros x i.
    destruct p as [pn]; destruct x as [xn];
    simpl; case i; [reflexivity|];
      intros i2; case i2; reflexivity.

    simpl; apply IHphi.
    apply at_pv_ST_conjSO; assumption.
    apply at_pv_ST_conjSO; assumption.
    apply at_pv_ST_conjSO; assumption.

    destruct x as [n];
    simpl; apply IHphi.

    destruct x as [n];
    simpl; apply IHphi.
Qed.

Lemma at_pv_ST_nocon : forall (phi : Modal) ( x : FOvariable) (i : nat),
  ST_pv (at_pv (pv_in phi) i) = at_pred (preds_in (ST phi x)) i.
Proof.
  induction phi; intros x i;
    try (    simpl; apply at_pv_ST_nocon_app; auto).
    destruct p as [pn]; destruct x as [xn];
    simpl; case i; [reflexivity|];
      intros i2; case i2; reflexivity.

    simpl; apply IHphi.

    destruct x. simpl. apply IHphi.

    destruct x. simpl. apply IHphi.
Qed.

Lemma ST_pred_p : forall n : nat,
  pv n = ST_pred (Pred n).
Proof.
  intros n; reflexivity.
Qed.

Lemma ST_atom_pred : forall p x W Iv Ip Ir,
    SOturnst W Iv Ip Ir (ST # p x) = SOturnst W Iv Ip Ir (predSO (ST_pv p) x).
Proof. intros [pn]. firstorder. Qed.  

Lemma V_to_Ip_ST_pv : forall W V p w,
    V p w <-> V_to_Ip W V (ST_pv p) w.
Proof. intros ? ? [Pn]. firstorder. Qed.

Lemma p_occ__ST_conjSO : forall (phi1 phi2 : Modal) (x : FOvariable) (p : propvar),
  (In (ST_pv p) (preds_in (ST phi1 x)) <-> In p (pv_in phi1)) ->
  (In (ST_pv p) (preds_in (ST phi2 x)) <-> In p (pv_in phi2)) ->
  (In (ST_pv p) (preds_in (ST (mconj phi1 phi2) x)) <-> In p (pv_in (mconj phi1 phi2))).
Proof.
  intros phi1 phi2 x p IHphi1 IHphi2; simpl; split; intros H;
  apply in_or_app; apply in_app_or in H; destruct H as [H | H];
  firstorder.
Qed.

Lemma ST_pv_inj : forall p1 p2,
    ST_pv p1 = ST_pv p2 -> p1 = p2.
Proof.
  intros [p1] [p2] H. simpl in *.
  inversion H. reflexivity.
Qed.



Lemma occ_in_SO_ST_FOv : forall (phi : Modal) (x y : FOvariable)
                                (i : nat),
  occ_in_SO (ST phi x) i <-> occ_in_SO (ST phi y) i.
Proof.
  intros phi x y i; split; intros [H1 H2]; constructor; try auto;
  erewrite (preds_in_ST_FOv); apply H2.
Qed.

Lemma occ_in_SO_box : forall (phi : Modal) (x : FOvariable)
                                ( i : nat),
  occ_in_SO (ST (box phi) x) i <-> occ_in_SO (ST phi x) i.
Proof.
  intros phi x i; simpl; split; intros [H1 H2]; constructor; try auto;
    destruct x as [n]; simpl in *; erewrite preds_in_ST_FOv in H2;
      apply H2.
Qed.

Lemma occ_in_SO_diam : forall (phi : Modal) (x : FOvariable)
                                ( i : nat),
  occ_in_SO (ST (diam phi) x) i <-> occ_in_SO (ST phi x) i.
Proof.
  intros phi x i; simpl; split; intros [H1 H2]; constructor; try auto;
    destruct x as [n]; simpl in *; erewrite preds_in_ST_FOv in H2;
      apply H2.
Qed.

Lemma occ_in_ST : forall (phi : Modal) (x : FOvariable) (i : nat),
  occ_in_modal phi i <-> occ_in_SO (ST phi x) i.
Proof.
  intros; split; intros [H1 H2]; constructor; try auto;
    rewrite <- pv_in__preds_in in *; auto.
Qed.

Lemma p_occ__ST : forall (phi : Modal) (x : FOvariable) (p : propvar),
  Pred_in_SO (ST phi x) (ST_pv p) <-> pv_in_modal phi p.
Proof.
  induction phi; intros x pp; unfold Pred_in_SO; unfold pv_in_modal;
    try   (simpl; split; intros H; apply in_app_or in H; apply in_or_app;
  (destruct H as [H|H]; [left; apply IHphi1|| apply IHphi1 in H |
  right; apply IHphi2 || apply IHphi2 in H]; auto)).

  simpl. destruct p. simpl. split; intros [H|H]. left.
  destruct pp. rewrite ST_pv_P in H.  inversion H. auto. auto.
  left. destruct pp. inversion H. apply ST_pv_P. auto.

  simpl. apply IHphi.
  destruct x. simpl. apply IHphi.
  destruct x. simpl. apply IHphi.
Qed.

Lemma pv_in_modal_Pred_in_SO_ST : forall (phi : Modal) (x : FOvariable)
                                     (P : predicate),
  Pred_in_SO (ST phi x) P <-> pv_in_modal phi (ST_pred P).
Proof.
  intros phi x [Pn].
  rewrite <- ST_pred_p.
  change (Pred Pn) with (ST_pv (pv Pn)).
  apply p_occ__ST.
Qed.

Lemma SOQFree_ST : forall (phi : Modal) (x : FOvariable),
  SOQFree (ST phi x) = true.
Proof.
  induction phi; intros x; simpl in *;
    try (destruct p; destruct x; reflexivity) ;
    try apply IHphi;
    try (rewrite IHphi1; rewrite IHphi2; reflexivity);
    try (destruct x; apply IHphi).
Qed.

Lemma FO_frame_condition_l_empty : forall (phi : Modal) (x : FOvariable),
  FO_frame_condition_l
    (nlist_list (length (preds_in (ST phi x)))
       (nlist_empty (length (preds_in (ST phi x))))) = true.
Proof.
  intros.
  apply FO_frame_condition_l_empty_n.
Qed.

Lemma FO_frame_condition_l_full : forall (phi : Modal) (x : FOvariable),
  FO_frame_condition_l
    (nlist_list (length (preds_in (ST phi x)))
       (nlist_full (length (preds_in (ST phi x))))) = true.
Proof.
  intros.
  apply FO_frame_condition_l_full_n.
Qed.

Lemma x_occ_in_alpha_ST : forall phi x,
  var_in_SO (ST phi x) x.
Proof.
  unfold var_in_SO. induction phi; intros x; simpl;
    try apply IHphi; try solve [firstorder].
  destruct p. simpl. firstorder.
Qed.

Lemma le_in_ST : forall phi n m,
 S m <= n ->  ~ In (Var m) (FOvars_in (ST phi (Var n))).
Proof.
  induction phi; intros n m H1 H2;
    try solve [simpl in *; firstorder].
  +  destruct p. simpl in *. destruct H2 as [H2 | H2]; auto.
     inversion H2. lia. 
  + simpl in *. apply in_app_or in H2. firstorder.
  + simpl in *. apply in_app_or in H2. firstorder.
  + simpl in *. apply in_app_or in H2. firstorder.
  + simpl in *. destruct H2 as [H2 | [H2 | [H2 | H2]]]; 
      try inversion H2; try lia. apply IHphi in H2; auto.
    lia.
  + simpl in *. destruct H2 as [H2 | [H2 | [H2 | H2]]]; 
      try inversion H2; try lia. apply IHphi in H2; auto.
    lia.
Qed.

Lemma var_in_SO_ST_le : forall phi m n,
  (S m) <= n -> ~ var_in_SO (ST phi (Var n)) (Var m) .
Proof.
  intros phi m n H. unfold var_in_SO.
  apply le_in_ST. auto. 
Qed.

Lemma ex_P_ST : forall phi x,
  existsT P, Pred_in_SO (ST phi x) P.
Proof.
  induction phi; intros x.
    exists (ST_pv p).
    simpl. destruct p. destruct x.
    unfold Pred_in_SO. simpl. auto.

    simpl. destruct (IHphi x) as [P H].
    exists P. rewrite <- Pred_in_SO_negSO.
    assumption.

    destruct (IHphi1 x) as [P H].
    exists P. simpl. apply Pred_in_SO_conjSO.
    left. assumption.

    destruct (IHphi1 x) as [P H].
    exists P. simpl. apply Pred_in_SO_conjSO.
    left. assumption.

    destruct (IHphi1 x) as [P H].
    exists P. simpl. apply Pred_in_SO_conjSO.
    left. assumption.

    simpl. destruct x as [xn]. destruct (IHphi (Var (xn + 1)))
      as [P H]. exists P. rewrite <- Pred_in_SO_allFO.
    destruct (Pred_in_SO_implSO (relatSO (Var xn) (Var (xn + 1)))
      (ST phi (Var (xn + 1))) P) as [fwd rev]. apply rev.
    right. assumption.

    simpl. destruct x as [xn]. destruct (IHphi (Var (xn + 1)))
      as [P H]. exists P. rewrite <- Pred_in_SO_exFO.
    apply Pred_in_SO_conjSO.
    right. assumption.
Defined.

Lemma ex_P_occ_in_alpha_ST : forall phi x,
  exists P, Pred_in_SO (ST phi x) P.
Proof.
  induction phi; intros [xn]; simpl.
    exists (ST_pv p). 
    destruct p. unfold Pred_in_SO. simpl. firstorder.

    destruct (IHphi (Var xn)) as [P IH].
    exists P. rewrite <- Pred_in_SO_negSO.
    assumption.

    destruct (IHphi1 (Var xn)) as [P IH1].
    exists P.  apply Pred_in_SO_conjSO.
    left. assumption.

    destruct (IHphi1 (Var xn)) as [P IH1].
    exists P.  apply Pred_in_SO_conjSO.
    left. assumption.

    simpl. destruct (IHphi1 (Var xn)) as [P IH1].
    exists P.  apply Pred_in_SO_conjSO.
    left. assumption.

    simpl. destruct (IHphi (Var (xn+1))) as [P IH].
    exists P. rewrite <- Pred_in_SO_allFO.
    destruct (Pred_in_SO_implSO (relatSO (Var xn) (Var (xn + 1)))
      (ST phi (Var (xn + 1))) P) as [fwd rev].
    apply rev. right. assumption.

    simpl. destruct (IHphi (Var (xn+1))) as [P IH].
    exists P. rewrite <- Pred_in_SO_exFO.
    apply Pred_in_SO_conjSO.
    right. assumption.
Qed.