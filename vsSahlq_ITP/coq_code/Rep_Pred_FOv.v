Require Export low_mods.

Fixpoint replace_FOv (alpha : SecOrder) (x y: FOvariable) : SecOrder :=
  match alpha with
    predSO P z => 
          if FOvariable_dec x z then predSO P y else alpha
  | relatSO z1 z2 => 
          if FOvariable_dec x z1 then if FOvariable_dec x z2
                                        then relatSO y y
                                        else relatSO y z2
                                 else if FOvariable_dec x z2 
                                         then relatSO z1 y
                                         else alpha
  | eqFO z1 z2 => 
          if FOvariable_dec x z1 then if FOvariable_dec x z2
                                        then eqFO y y
                                        else eqFO y z2
                                 else if FOvariable_dec x z2 
                                         then eqFO z1 y
                                      else alpha
  | allFO z beta =>
          if FOvariable_dec x z then allFO y (replace_FOv beta x y) 
                          else allFO z (replace_FOv beta x y) 
  | exFO z beta =>
          if FOvariable_dec x z then exFO y (replace_FOv beta x y) 
                          else exFO z (replace_FOv beta x y) 
  | negSO beta => negSO (replace_FOv beta x y)
  | conjSO beta1 beta2 => conjSO (replace_FOv beta1 x y) (replace_FOv beta2 x y)
  | disjSO beta1 beta2 => disjSO (replace_FOv beta1 x y) (replace_FOv beta2 x y)
  | implSO beta1 beta2 => implSO (replace_FOv beta1 x y) (replace_FOv beta2 x y)
  | allSO P beta => allSO P (replace_FOv beta x y)
  | exSO P beta => exSO P (replace_FOv beta x y)
  end.

(* Replaces all occurrences of P in alpha with a SecOrder condition.
Think of it like:

  Takes in:
     alpha = ...Px... ;
     {u | Ruy -> y=x} 
  Spits out:
     alpha' = ...(Rxy -> y=x)...

So, it takes in an alpha and a set where membership is determined by a SecOrder (ideally FO) fml.  *)

Fixpoint replace_pred (alpha : SecOrder) (P : predicate) 
                      (x : FOvariable) (cond : SecOrder) : SecOrder :=
  match alpha with 
    predSO Q z => if predicate_dec P Q then (replace_FOv cond x z) else alpha
  | relatSO _ _  => alpha
  | eqFO _ _ => alpha
  | allFO z beta => allFO z (replace_pred beta P x cond)
  | exFO z beta => exFO z (replace_pred beta P x cond)
  | negSO beta => negSO (replace_pred beta P x cond)
  | conjSO beta1 beta2 => conjSO (replace_pred beta1 P x cond) (replace_pred beta2 P x cond)
  | disjSO beta1 beta2 => disjSO (replace_pred beta1 P x cond) (replace_pred beta2 P x cond)
  | implSO beta1 beta2 => implSO (replace_pred beta1 P x cond) (replace_pred beta2 P x cond)
  | allSO Q beta => 
           if predicate_dec P Q then (replace_pred beta P x cond) 
                           else allSO Q (replace_pred beta P x cond)
  | exSO Q beta => 
           if predicate_dec P Q then (replace_pred beta P x cond) 
                           else exSO Q (replace_pred beta P x cond)
  end.

Fixpoint replace_pred_l (alpha : SecOrder) (lP : list predicate)
                        (lx : list FOvariable) (lcond : list SecOrder) 
                        : SecOrder :=
  match lP, lx, lcond with
  | cons P lP', cons x lx', cons cond lcond' => 
      replace_pred (replace_pred_l alpha lP' lx' lcond') P x cond
  | _, _, _ => alpha
  end.

(* -------------------------------------------------------------------- *)

Lemma rep_pred_eqFO : forall (x y z : FOvariable) (Q : predicate)
                             (cond : SecOrder),
  (replace_pred (eqFO x y) Q z cond) = (eqFO x y).
Proof.
  intros.
  destruct Q as [Qm]; destruct x as [xn]; destruct y.
  reflexivity.
Qed.

Lemma rep_pred_allFO : forall (alpha cond : SecOrder) (x y : FOvariable)
                              (Q : predicate),
  (replace_pred (allFO x alpha) Q y cond) =
    (allFO x (replace_pred alpha Q y cond)).
Proof.
  intros.
  simpl replace_pred.
  destruct Q as [Qm]; destruct x as [xn].
  reflexivity.
Qed.

Lemma rep_pred_exFO : forall (alpha cond : SecOrder) (x y : FOvariable)
                              (Q : predicate),
  (replace_pred (exFO x alpha) Q y cond) =
    (exFO x (replace_pred alpha Q y cond)).
Proof.
  intros.
  simpl replace_pred.
  destruct Q as [Qm]; destruct x as [xn].
  reflexivity.
Qed.

Lemma rep_pred_negSO : forall (alpha cond : SecOrder) (y : FOvariable)
                              (Q : predicate),
  (replace_pred (negSO alpha) Q y cond) =
    (negSO (replace_pred alpha Q y cond)).
Proof.
  intros.
  simpl replace_pred.
  destruct Q; destruct y.
  reflexivity.
Qed.

Lemma rep_pred_conjSO : forall (alpha1 alpha2 cond : SecOrder) (y : FOvariable)
                              (Q : predicate),
  (replace_pred (conjSO alpha1 alpha2) Q y cond) =
    (conjSO (replace_pred alpha1 Q y cond) (replace_pred alpha2 Q y cond)).
Proof.
  intros.
  simpl.
  destruct Q.
  reflexivity.
Qed.

Lemma rep_pred_disjSO : forall (alpha1 alpha2 cond : SecOrder) (y : FOvariable)
                              (Q : predicate),
  (replace_pred (disjSO alpha1 alpha2) Q y cond) =
    (disjSO (replace_pred alpha1 Q y cond) (replace_pred alpha2 Q y cond)).
Proof.
  intros.
  simpl.
  destruct Q.
  reflexivity.
Qed.

Lemma rep_pred_implSO : forall (alpha1 alpha2 cond : SecOrder) (y : FOvariable)
                              (Q : predicate),
  (replace_pred (implSO alpha1 alpha2) Q y cond) =
    (implSO (replace_pred alpha1 Q y cond) (replace_pred alpha2 Q y cond)).
Proof.
  intros.
  simpl.
  destruct Q.
  reflexivity.
Qed.

Lemma rep_pred_relatSO : forall (cond : SecOrder) (x1 x2 y : FOvariable)
                              (Q : predicate),
  (replace_pred (relatSO x1 x2) Q y cond) = relatSO x1 x2.
Proof.
  intros.
  simpl.
  destruct Q; destruct x1; destruct x2.
  reflexivity.
Qed.

Lemma rep_pred_allSO : forall (alpha cond : SecOrder) (y : FOvariable)
                              (P Q : predicate),
  (replace_pred (allSO P alpha) Q y cond) =
             if predicate_dec Q P then (replace_pred alpha Q y cond) 
                           else allSO P (replace_pred alpha Q y cond).
Proof. intros alpha cond y P Q.  reflexivity. Qed. 

Lemma rep_pred_exSO : forall (alpha cond : SecOrder) (y : FOvariable)
                              (P Q : predicate),
  (replace_pred (exSO P alpha) Q y cond) =
             if predicate_dec Q P then (replace_pred alpha Q y cond) 
                           else exSO P (replace_pred alpha Q y cond).
Proof. intros alpha cond y P Q.  reflexivity. Qed.

Lemma kk4 : forall beta P x cond,
  replace_pred (allSO P beta) P x cond =  replace_pred beta P x cond.
Proof.  intros. simpl. rewrite predicate_dec_l; auto. Qed.

Lemma kk4_exSO : forall beta P x cond,
  replace_pred (exSO P beta) P x cond =  replace_pred beta P x cond.
Proof.  intros. simpl. rewrite predicate_dec_l; auto. Qed.

(* -------------------------------------------------------------------- *)

Lemma rep_pred_l_negSO : forall (alpha : SecOrder) (lP : list predicate)
                                (lx : list FOvariable)
                                (lcond : list SecOrder),
  replace_pred_l (negSO alpha) lP lx lcond = 
    (negSO (replace_pred_l alpha lP lx lcond)).
Proof.
  induction lP; intros lx lcond;
    destruct lx; destruct lcond; try reflexivity.
  simpl. rewrite IHlP. reflexivity.
Qed.

Lemma rep_pred_l_allFO : forall (alpha : SecOrder) (lP : list predicate)
                        (lx : list FOvariable) (lcond : list SecOrder)
                        (x : FOvariable) ,
  replace_pred_l (allFO x alpha) lP lx lcond =
    allFO x (replace_pred_l alpha lP lx lcond).
Proof.
  induction lP; intros lx lcond x;
    destruct lx; destruct lcond; try reflexivity.
  simpl. rewrite IHlP. reflexivity.
Qed.

Lemma rep_pred_l_exFO : forall (alpha : SecOrder) (lP : list predicate)
                        (lx : list FOvariable) (lcond : list SecOrder)
                        (x : FOvariable) ,
  replace_pred_l (exFO x alpha) lP lx lcond =
    exFO x (replace_pred_l alpha lP lx lcond).
Proof.
  induction lP; intros lx lcond x;
    destruct lx; destruct lcond; try reflexivity.
  simpl. rewrite IHlP. reflexivity.
Qed.

Lemma rep_pred_l_eqFO : forall (lP : list predicate)
                        (lx : list FOvariable) (lcond : list SecOrder)
                        (x y : FOvariable) ,
  replace_pred_l (eqFO x y) lP lx lcond = (eqFO x y).
Proof.
  induction lP; intros lx lcond x y;
    destruct lx; destruct lcond; try reflexivity.
  simpl. rewrite IHlP. reflexivity.
Qed.

Lemma rep_pred_l_conjSO : forall (alpha1 alpha2 : SecOrder) (lP : list predicate)
                        (lx : list FOvariable) (lcond : list SecOrder),
  replace_pred_l (conjSO alpha1 alpha2) lP lx lcond =
    conjSO (replace_pred_l alpha1 lP lx lcond) 
           (replace_pred_l alpha2 lP lx lcond).
Proof.
  intros alpha1 alpha2 lP.
  induction lP.
    simpl; reflexivity.

    induction lx.
      simpl; reflexivity.

      induction lcond.
        simpl; reflexivity.

        simpl.
        rewrite IHlP.
        rewrite rep_pred_conjSO.
        reflexivity.
Qed.

Lemma rep_pred_l_disjSO : forall (alpha1 alpha2 : SecOrder) (lP : list predicate)
                        (lx : list FOvariable) (lcond : list SecOrder),
  replace_pred_l (disjSO alpha1 alpha2) lP lx lcond =
    disjSO (replace_pred_l alpha1 lP lx lcond) 
           (replace_pred_l alpha2 lP lx lcond).
Proof.
  intros alpha1 alpha2 lP.
  induction lP.
    simpl; reflexivity.

    induction lx.
      simpl; reflexivity.

      induction lcond.
        simpl; reflexivity.

        simpl.
        rewrite IHlP.
        rewrite rep_pred_disjSO.
        reflexivity.
Qed.

Lemma rep_pred_l_implSO : forall (alpha1 alpha2 : SecOrder) (lP : list predicate)
                        (lx : list FOvariable) (lcond : list SecOrder),
  replace_pred_l (implSO alpha1 alpha2) lP lx lcond =
    implSO (replace_pred_l alpha1 lP lx lcond) 
           (replace_pred_l alpha2 lP lx lcond).
Proof.
  intros alpha1 alpha2 lP.
  induction lP.
    simpl; reflexivity.

    induction lx.
      simpl; reflexivity.

      induction lcond.
        simpl; reflexivity.

        simpl.
        rewrite IHlP.
        rewrite rep_pred_implSO.
        reflexivity.
Qed.

Lemma rep_pred_l_relatSO : forall (x y : FOvariable) (lP : list predicate)
                        (lx : list FOvariable) (lcond : list SecOrder),
  replace_pred_l (relatSO x y) lP lx lcond = relatSO x y.
Proof.
  intros x y lP.
  induction lP.
    simpl; reflexivity.

    induction lx.
          simpl; reflexivity.

      induction lcond.
            simpl; reflexivity.

        simpl.
        rewrite IHlP.
        destruct a; destruct x; destruct y.
        simpl.
        reflexivity.
Qed.

(* ----------------------------------------------------------------------- *)


Lemma rep_pred_FO_frame_condition : forall (alpha : SecOrder) (P : predicate)
                              (x : FOvariable) (cond : SecOrder),
  FO_frame_condition alpha = true ->
    replace_pred alpha P x cond = alpha.
Proof.
  intros.
  destruct P as [Pn].
  induction alpha;
    try (simpl in *; destruct p; destruct f; discriminate);
    try (destruct f; destruct f0; reflexivity);
    try (simpl; destruct f;
         rewrite IHalpha; [reflexivity | assumption]);
    try (simpl; rewrite IHalpha;
          [reflexivity | assumption]);
    try (simpl in *;
      assert (FO_frame_condition alpha1 = true) as H1;
        try (case_eq (FO_frame_condition alpha1); intros H1';
        rewrite H1' in *; [reflexivity | discriminate]);
      rewrite H1 in H; rewrite IHalpha1; try assumption;
      rewrite IHalpha2; [reflexivity | assumption]);
    try (destruct p; simpl in *; discriminate).
Qed.

Lemma rep_FOv_FO_frame_condition : forall (cond : SecOrder) (x y :FOvariable),
  FO_frame_condition cond = true ->
    FO_frame_condition (replace_FOv cond x y) = true.
Proof.
  intros cond x y FO.
  induction cond; try discriminate;
    try (  simpl in *; case_eq (FOvariable_dec x f); case_eq (FOvariable_dec x f0);
           reflexivity);
    try (simpl in *; pose proof (IHcond FO);
         case_eq (FOvariable_dec x f); intros H1 H2; auto);
    try (simpl in *; apply IHcond; auto);
    try (simpl in *; apply andb_prop in FO; destruct FO as [FO1 FO2];
    rewrite IHcond1; [apply IHcond2|]; try auto).
Qed.

(* ----------------------------------------------------------------------- *)

Lemma rep_FOv_rem : forall alpha x, (replace_FOv alpha x x) = alpha.
Proof.
  induction alpha; intros x;
    try (simpl; rewrite IHalpha1; rewrite IHalpha2; auto); simpl;
    try solve [simpl; rewrite IHalpha; auto]; simpl.
  + destruct (FOvariable_dec x f); subst; firstorder.
  + destruct (FOvariable_dec x f); destruct (FOvariable_dec x f0);
             subst; simpl in *; auto.
  + destruct (FOvariable_dec x f); destruct (FOvariable_dec x f0);
             subst; simpl in *; auto.
  + destruct (FOvariable_dec x f); subst; simpl in *;
    rewrite IHalpha; auto.
  + destruct (FOvariable_dec x f); subst; simpl in *;
    rewrite IHalpha; auto.
Qed.

Lemma rep_pred_switch : forall (alpha : SecOrder) (x y : FOvariable)
                               (cond1 cond2 : SecOrder)
                                (P Q : predicate),
  FO_frame_condition cond1 = true -> FO_frame_condition cond2 = true ->
    ~ P = Q ->
       replace_pred (replace_pred alpha P x cond1) Q y cond2 = 
          replace_pred (replace_pred alpha Q y cond2) P x cond1.
Proof.
  induction alpha; intros x y cond1 cond2 P Q FO1 FO2 Hneq;
    try ( simpl; reflexivity);
    try (  simpl; rewrite IHalpha; solve [firstorder]);
  try (      simpl; rewrite IHalpha1; [rewrite IHalpha2| | |]; auto).
  try (simpl; rewrite IHalpha; reflexivity);
      try (simpl; rewrite IHalpha; reflexivity);
      try (simpl; rewrite IHalpha1; rewrite IHalpha2; reflexivity).

  simpl in *. destruct (predicate_dec P p) as [H1 | H1];
  destruct (predicate_dec Q p) as [H2 | H2].
  subst. contradiction. subst.
  simpl. destruct (predicate_dec p p); auto.
  rewrite rep_pred_FO_frame_condition. auto.
  apply rep_FOv_FO_frame_condition. auto.
  contradiction.
  subst. simpl. destruct (predicate_dec p p ); auto.
  rewrite rep_pred_FO_frame_condition. auto.
  apply rep_FOv_FO_frame_condition. auto.
  contradiction. simpl.
  destruct (predicate_dec Q p) as [H3 | H3]. firstorder.
      destruct (predicate_dec P p) as [H4 | H4];
  firstorder. 

  simpl. destruct (predicate_dec P p) as [H1 | H1];
  destruct (predicate_dec Q p) as [H2 | H2].
      firstorder. subst. simpl. destruct (predicate_dec p p) as [H3 | H3];
                                  firstorder. subst. simpl. destruct (predicate_dec p p ) as [H3 | H3].
  apply IHalpha; auto. firstorder.
  simpl. destruct (predicate_dec P p) as [H1' | H1']. firstorder.
  destruct (predicate_dec Q p) as [H2' | H2']. firstorder.
  simpl. rewrite IHalpha; auto.

    simpl. destruct (predicate_dec P p) as [H1 | H1];
  destruct (predicate_dec Q p) as [H2 | H2].
      firstorder. subst. simpl. destruct (predicate_dec p p) as [H3 | H3];
                                  firstorder. subst. simpl. destruct (predicate_dec p p ) as [H3 | H3].
  apply IHalpha; auto. firstorder.
  simpl. destruct (predicate_dec P p) as [H1' | H1']. firstorder.
  destruct (predicate_dec Q p) as [H2' | H2']. firstorder.
  simpl. rewrite IHalpha; auto.
Qed.

(* ----------------------------------------------------------------------- *)


Lemma rep_pred_l_FO_frame_condition : forall (alpha : SecOrder) (lP : list predicate)
                                (lx : list FOvariable) (lcond : list SecOrder),
  FO_frame_condition alpha = true ->
    FO_frame_condition (replace_pred_l alpha lP lx lcond) = true.
Proof.
  intros.
  induction alpha;
    try destruct p;
    try destruct f;
    try destruct f0;
    try rewrite rep_pred_l_relatSO;
    try rewrite rep_pred_l_eqFO;
    try rewrite rep_pred_l_allFO;
    try rewrite rep_pred_l_exFO;
    try rewrite rep_pred_l_negSO;
    try rewrite rep_pred_l_conjSO;
    try rewrite rep_pred_l_disjSO;
    try rewrite rep_pred_l_implSO;
    try assumption;
    try (simpl; apply IHalpha; apply H);
    try (simpl; rewrite IHalpha1;
      [rewrite IHalpha2; 
          [reflexivity |
           try exact (FO_frame_condition_conjSO_r _ _ H);
           try exact (FO_frame_condition_disjSO_r _ _ H);
           try exact (FO_frame_condition_implSO_r _ _ H);
           assumption] |
       try exact (FO_frame_condition_conjSO_l _ _ H);
       try exact (FO_frame_condition_disjSO_l _ _ H);
       try exact (FO_frame_condition_implSO_l _ _ H)]);
    try (simpl in *; discriminate).
Qed.

Lemma rep_pred_l_app : forall (alpha : SecOrder)
                              (l1 l2 : list predicate),
  replace_pred_l alpha (app l1 l2)
      (nlist_list (length (app l1 l2))
                  (nlist_var (length (app l1 l2)) (Var 1)))
      (nlist_list (length (app l1 l2))
                  (nlist_empty (length (app l1 l2)))) =
  replace_pred_l (replace_pred_l alpha l2 
                      (nlist_list (length l2)
                                  (nlist_var (length l2) (Var 1)))
                      (nlist_list (length l2)
                                  (nlist_empty (length l2)))) l1
      (nlist_list (length l1)
                  (nlist_var (length l1) (Var 1)))
      (nlist_list (length l1)
                  (nlist_empty (length l1))).
Proof.
  induction l1; intros; auto.
  simpl. rewrite IHl1. auto.
Qed.

(* ----------------------------------------------------------------------- *)


Lemma rep_pred__l_switch_empty : forall (alpha : SecOrder) (P : predicate)
                                  (l : list predicate),
replace_pred_l 
      (replace_pred alpha P (Var 1) (negSO (eqFO (Var 1) (Var 1))))
      l
      (nlist_list (length l) (nlist_var (length l) (Var 1)))
      (nlist_list (length l) (nlist_empty (length l))) =
replace_pred 
    (replace_pred_l alpha l 
      (nlist_list (length l) (nlist_var (length l) (Var 1)))
      (nlist_list (length l) (nlist_empty (length l))))
    P (Var 1) (negSO (eqFO (Var 1) (Var 1))).
Proof.
  induction l; auto.  simpl. rewrite IHl.
  destruct (predicate_dec P a). subst. auto.
  rewrite (rep_pred_switch _ (Var 1) _ _ _ P a); auto.
Qed.


Lemma rep_pred_l_switch : forall (alpha : SecOrder)
                                 (l1 l2 : list predicate),
replace_pred_l 
(replace_pred_l alpha l1 
      (nlist_list (length l1)
          (nlist_var (length l1) (Var 1)))
      (nlist_list (length l1)
          (nlist_empty (length l1)))) l2
    (nlist_list (length l2)
        (nlist_var (length l2) (Var 1)))
    (nlist_list (length l2)
        (nlist_empty (length l2))) =
replace_pred_l 
(replace_pred_l alpha l2 
      (nlist_list (length l2)
          (nlist_var (length l2) (Var 1)))
      (nlist_list (length l2)
          (nlist_empty (length l2)))) l1
    (nlist_list (length l1)
        (nlist_var (length l1) (Var 1)))
    (nlist_list (length l1)
        (nlist_empty (length l1))).
Proof.
  induction l1; auto.
  simpl. intros l2. rewrite <- IHl1.
  rewrite rep_pred__l_switch_empty. auto.
Qed.

Lemma rep_pred__l_switch_t : forall (alpha : SecOrder) (P : predicate)
                                  (l : list predicate),
replace_pred_l 
      (replace_pred alpha P (Var 1) (eqFO (Var 1) (Var 1)))
      l
      (nlist_list (length l) (nlist_var (length l) (Var 1)))
      (nlist_list (length l) (nlist_full (length l))) =
replace_pred 
    (replace_pred_l alpha l 
      (nlist_list (length l) (nlist_var (length l) (Var 1)))
      (nlist_list (length l) (nlist_full (length l))))
    P (Var 1) (eqFO (Var 1) (Var 1)).
Proof.
  induction l; auto.
  simpl. rewrite IHl.
  destruct (predicate_dec P a). subst. auto.
  rewrite (rep_pred_switch _ (Var 1) _ _ _ P a); auto.
Qed.

Lemma rep_pred_l_switch_t : forall (alpha : SecOrder)
                                 (l1 l2 : list predicate),
replace_pred_l 
(replace_pred_l alpha l1 
      (nlist_list (length l1)
          (nlist_var (length l1) (Var 1)))
      (nlist_list (length l1)
          (nlist_full (length l1)))) l2
    (nlist_list (length l2)
        (nlist_var (length l2) (Var 1)))
    (nlist_list (length l2)
        (nlist_full (length l2))) =
replace_pred_l 
(replace_pred_l alpha l2 
      (nlist_list (length l2)
          (nlist_var (length l2) (Var 1)))
      (nlist_list (length l2)
          (nlist_full (length l2)))) l1
    (nlist_list (length l1)
        (nlist_var (length l1) (Var 1)))
    (nlist_list (length l1)
        (nlist_full (length l1))).
Proof.
  induction l1; auto.
  simpl. intros l2. rewrite <- IHl1.
  rewrite rep_pred__l_switch_t. auto.
Qed.


(* ----------------------------------------------------------------------- *)


Lemma preds_in_rep_FOv : forall (cond : SecOrder) (x y : FOvariable),
  (preds_in (replace_FOv cond x y)) = preds_in cond.
Proof.
  induction cond; intros x y;
    try (  simpl; destruct (FOvariable_dec x f) as [H | H];
           destruct (FOvariable_dec x f0) as [H2 | H2]; auto);
    try ( simpl; destruct (FOvariable_dec x f) as [H | H]; auto);
    try (simpl; rewrite IHcond; auto);
    try (simpl; rewrite IHcond1; rewrite IHcond2; auto).
Qed.

(* ----------------------------------------------------------------------- *)

Lemma SOQFree_rep_FOv : forall alpha x y,
  SOQFree alpha = true ->
  SOQFree (replace_FOv alpha x y) = true.
Proof.
  induction alpha; intros x y H;
    try (simpl; if_then_else_reg);
    try (simpl; if_then_else_reg2);
    try (  simpl in H;  destruct_andb_t);
    try (  simpl; rewrite IHalpha1; [apply IHalpha2 |]; auto);
    try discriminate.

  simpl; apply IHalpha; auto.
Qed.

Lemma SOQFree_rep_pred : forall alpha cond P x,
  SOQFree alpha = true ->
  SOQFree cond = true ->
  SOQFree (replace_pred alpha P x cond) = true.
Proof.
  induction alpha; intros cond P x H1 H2; try reflexivity;
    try (    simpl; apply IHalpha; auto);
    try discriminate.
  
    simpl in *.
    destruct (predicate_dec P p) as [H | H].
    apply SOQFree_rep_FOv. auto. auto.

    simpl in H1. case_eq (SOQFree alpha1); intros H3;
                   rewrite H3 in *.
    simpl. rewrite IHalpha1. apply IHalpha2. all : try auto.
    discriminate.
    
    simpl in H1. case_eq (SOQFree alpha1); intros H3;
                   rewrite H3 in *.
    simpl. rewrite IHalpha1. apply IHalpha2. all : try auto.
    discriminate.

        simpl in H1. case_eq (SOQFree alpha1); intros H3;
                   rewrite H3 in *.
    simpl. rewrite IHalpha1. apply IHalpha2. all : try auto.
    discriminate.
Qed.

Lemma SOQFree_rep_pred_empty : forall (alpha : SecOrder) (Q : predicate) x y,
  SOQFree alpha = true -> 
    SOQFree (replace_pred alpha Q y (negSO (eqFO x x))) = true.
Proof.
  induction alpha; intros Q [xn] [ym] HSO; auto;
    try (  simpl in *; apply IHalpha; auto);
    try (  simpl in HSO; destruct_andb_t2;
           simpl; rewrite IHalpha1; try auto; [apply IHalpha2|]; auto);
    try (destruct_andb_t_simpl HSO HSO2;
         simpl; rewrite IHalpha1; try auto; apply IHalpha2; auto);
    try discriminate.

  simpl. dest_FOv_dec_blind; destruct (predicate_dec Q p) as [H1 | H1]; auto.
Qed.

Lemma SOQFree_rep_pred_t : forall (alpha : SecOrder) (Q : predicate),
  SOQFree alpha = true -> 
    SOQFree (replace_pred alpha Q (Var 1) 
      (eqFO (Var 1) (Var 1))) = true.
Proof.
  induction alpha; intros Q HSO; try reflexivity;
try (simpl; apply IHalpha; auto);
try (destruct_andb_t_simpl HSO HSO2; simpl; 
rewrite IHalpha1; try auto; apply IHalpha2; auto); try discriminate.

simpl; repeat (rewrite FOvariable_dec_l; auto); if_then_else_reg.
Qed.

Lemma SOQFree_rep_pred_l : forall lP lx lcond alpha,
  SOQFree_l lcond = true ->
  SOQFree alpha = true ->
  SOQFree (replace_pred_l alpha lP lx lcond) = true.
Proof.
  induction lP; intros lx lcond alpha H1 H2.
    simpl. assumption.

    simpl. destruct lx. assumption.
    destruct lcond. assumption.
    simpl in H1. case_eq (SOQFree s);
      intros Hs; rewrite Hs in *.
    apply SOQFree_rep_pred. apply IHlP.
    all : try assumption.
      discriminate.
Qed.


Lemma SOQFree_rep_pred_l_nlist : forall (l : list predicate) (alpha : SecOrder) ,
 SOQFree alpha = true ->
    SOQFree
  (replace_pred_l alpha l (nlist_list (length l) (nlist_var (length l) (Var 1)))
     (nlist_list (length l) (nlist_empty (length l)))) = true.
Proof.
  induction l; intros alpha HSO; simpl; auto.
  apply SOQFree_rep_pred_empty. auto.
Qed.

Lemma SOQFree_rep_pred_l_t : forall (l : list predicate) (alpha : SecOrder) ,
 SOQFree alpha = true ->
    SOQFree
  (replace_pred_l alpha l (nlist_list (length l) (nlist_var (length l) (Var 1)))
     (nlist_list (length l) (nlist_full (length l)))) = true.
Proof.
  induction l; intros alpha HSO; simpl; auto.
  apply SOQFree_rep_pred_t. auto.
Qed.

(* ----------------------------------------------------------- *)

Lemma rep_pred_Pred_in_SO_f : forall (alpha cond : SecOrder) (P : predicate)
                              (x : FOvariable),
  ~ Pred_in_SO alpha P ->
    replace_pred alpha P x cond = alpha.
Proof.
  induction alpha; intros cond P x H; try reflexivity;
try (    simpl in *; rewrite IHalpha; auto);
try (    apply Pred_in_SO_conjSO_f in H; destruct H as [H1 H2];
    simpl; rewrite IHalpha1; try auto; rewrite IHalpha2; auto).

    simpl. destruct (predicate_dec P p) as [H1 | H1].
    subst. contradiction (H (Pred_in_SO_predSO _ _)).
    auto.

    destruct (predicate_dec P p) as [H1 | H1]. subst.
    firstorder. auto. firstorder.

    destruct (predicate_dec P p) as [H1 | H1]. subst.
    firstorder. auto. firstorder.
Qed.

Lemma rep_pred_not_in : forall alpha P x cond,
  ~ In P (preds_in alpha) ->
  replace_pred alpha P x cond = alpha.
Proof.
  intros alpha P x cond H. apply rep_pred_Pred_in_SO_f.
  firstorder.
Qed.

Lemma preds_in_rep_pred_In  : forall alpha Q x cond P,
In P (preds_in (replace_pred alpha Q x cond)) ->
In P ((preds_in alpha) ++ (preds_in cond)).
Proof.
  induction alpha; intros Q x cond P H; try contradiction;
    try (    simpl in *; eapply IHalpha; apply H);
  try (    simpl in *; apply in_app_or in H; destruct H as [H1 | H1];
    [apply IHalpha1 in H1 | apply IHalpha2 in H1];
    apply in_app_or in H1; destruct H1 as [H2 | H2]; firstorder);
  try (    simpl in *; destruct (predicate_dec Q p) as [H1 | H1]; 
           solve [firstorder]).

    simpl in *. destruct (predicate_dec Q p) as [H1 | H1].
    subst. rewrite preds_in_rep_FOv in H. auto.
    simpl in *. firstorder.
Qed.

Lemma P_occ_rep_pred_f2_pre : forall (alpha cond : SecOrder) (P Q : predicate)
                                  (x : FOvariable), 
  P <> Q ->
  ~ Pred_in_SO cond P ->
    ~ Pred_in_SO alpha P ->
      ~ Pred_in_SO (replace_pred alpha Q x cond) P.
Proof.
  unfold Pred_in_SO. intros alpha cond P Q x H1 H2 H3 H4.
  apply preds_in_rep_pred_In in H4.
  apply in_app_or in H4. firstorder.
Qed.

Lemma In_preds_in_rep_pred: forall alpha P x cond,
 In P (preds_in (replace_pred alpha P x cond)) ->
 In P (preds_in cond).
Proof.
  induction alpha; intros P x cond H; try contradiction;
    try (    simpl in *; eapply IHalpha; apply H);
try (simpl in *;
apply in_app_or in H; destruct H as [H1 | H1]; [eapply IHalpha1 |
eapply IHalpha2]; apply H1).

    simpl in *. destruct (predicate_dec P p) as [H1 | H1].
    subst. rewrite preds_in_rep_FOv in H. auto.
    simpl in *. firstorder. subst. contradiction.

    simpl in *; destruct (predicate_dec P p) as [H1 | H1];
    subst; eapply IHalpha; try auto. apply H;
    simpl in H; destruct H; subst. 
    simpl in H. destruct H as [H2 | H2]. subst. contradiction. 
    apply H2. 

    simpl in *; destruct (predicate_dec P p) as [H1 | H1];
    subst; eapply IHalpha; try auto. apply H;
    simpl in H; destruct H; subst. 
    simpl in H. destruct H as [H2 | H2]. subst. contradiction. 
    apply H2. 
Qed.

Lemma In_preds_in_rep_pred_rev: forall alpha P x cond,
~ In P (preds_in cond) ->
~ In P (preds_in (replace_pred alpha P x cond)).
Proof.
  intros ? ? ? ? H1 H2. apply H1.
  apply In_preds_in_rep_pred in H2. auto.
Qed.

Lemma P_occ_rep_pred_l_empty : forall (l : list predicate) (alpha : SecOrder) 
                                (P : predicate),
  ~ Pred_in_SO alpha P ->
  ~ Pred_in_SO (replace_pred_l alpha l 
                        (nlist_list (length l) (nlist_var (length l) (Var 1)))
                        (nlist_list (length l) (nlist_empty (length l)))) P.
Proof.
  unfold Pred_in_SO.
  induction l; intros alpha P HPocc H. 
  simpl in *. contradiction.
  simpl in H. rewrite <- rep_pred__l_switch_empty in H.
  apply IHl in H. auto.
  intros H2. destruct (predicate_dec P a). subst. 
  apply In_preds_in_rep_pred in H2; auto.
  apply  P_occ_rep_pred_f2_pre in H2; auto.
Qed.

Lemma rep_pred__l_switch : forall lP alpha lx lcond P x cond,
  ~ In P lP ->
  FO_frame_condition cond = true ->
  FO_frame_condition_l lcond = true ->
  replace_pred (replace_pred_l alpha lP lx lcond) P x cond =
  replace_pred_l (replace_pred alpha P x cond) lP lx lcond.
Proof.
  induction lP; intros alpha lx lcond [Qm] [ym] cond Hin Hun1 Hun2.
    reflexivity.

    destruct a as [Pn].
    case_eq lx.
      intros Hlx. reflexivity.

      intros [xn] lx' Hlx.
      case_eq lcond.
        intros Hlcond. reflexivity.

        intros beta lcond' Hlcond.
        simpl.

        rewrite Hlcond in Hun2.
        simpl in Hun2.
        case_eq (FO_frame_condition beta); intros Hun3; 
          rewrite Hun3 in *; try discriminate.

        rewrite <- IHlP. apply not_in_cons in Hin.
          rewrite (rep_pred_switch _ (Var xn) (Var ym)
             beta cond (Pred Pn) (Pred Qm)).
          reflexivity. all: try assumption. firstorder.
          apply not_in_cons in Hin. apply Hin.
Qed.


Lemma rep_pred__l_is_in : forall n lP alpha lx lcond P x cond,
  In P (nlist_list n lP) ->
  FO_frame_condition_l (nlist_list n lcond) = true ->
  FO_frame_condition cond = true ->
  replace_pred (replace_pred_l alpha 
      (nlist_list n lP) (nlist_list n lx) (nlist_list n lcond)) P x cond =
  replace_pred_l alpha (nlist_list n lP) (nlist_list n lx) (nlist_list n lcond).
Proof.
  induction n; intros lP alpha lx lcond [Pn] [xn] cond Hin Hun Hun2. 
    rewrite (nlist_nil2 lP) in *. contradiction.

    destruct (nlist_cons2 _ lP) as [[Qm] [lP' lPeq]].
    destruct (nlist_cons2 _ lcond) as [beta [lcond' lcondeq]].
    destruct (nlist_cons2 _ lx) as [[xm] [lx' lxeq]].
    rewrite lPeq; rewrite lcondeq; rewrite lxeq.
    simpl. destruct (predicate_dec (Pred Pn) (Pred Qm)) as [Hbeq | Hbeq].
      rewrite rep_pred_Pred_in_SO_f. auto.
      rewrite lcondeq in Hun; simpl in Hun.
      case_eq (FO_frame_condition beta); intros Hun4;
          rewrite Hun4 in *; try discriminate.
      rewrite Hbeq in *. intros HH. unfold Pred_in_SO in HH.
      apply In_preds_in_rep_pred in HH.
      eapply Pred_in_SO_FO_frame_condition in Hun4.
      apply Hun4. apply HH.

          rewrite lPeq in Hin. simpl in *.
          destruct Hin as [Hin1 | Hin2].
          inversion Hin1. subst.  contradiction.
          
      rewrite lcondeq in Hun.
      simpl in *. 
      case_eq (FO_frame_condition beta); intros Hun3; rewrite Hun3 in *;
        try discriminate.
      pose proof (rep_pred_switch (replace_pred_l alpha (nlist_list n lP') (nlist_list n lx')
        (nlist_list n lcond')) (Var xm) (Var xn) beta cond
          (Pred Qm) (Pred Pn)) as Heq.
      simpl in Heq.
      rewrite Heq.
      rewrite IHn. reflexivity.
      all: try assumption.
      intros HH. inversion HH as [HH2]. subst.  contradiction.
Qed.

Lemma replace_FOv_disjSO: forall alpha beta x y,
  replace_FOv (disjSO alpha beta) x y =
  disjSO (replace_FOv alpha x y) (replace_FOv beta x y).
Proof.
  intros. destruct x. simpl. reflexivity.
Qed.

Lemma rep_FOv_not_in : forall alpha x y,
  ~ var_in_SO alpha x -> replace_FOv alpha x y = alpha.
Proof.
  induction alpha; intros x y Hocc; unfold var_in_SO in *;
    simpl in *. destruct (FOvariable_dec x f); simpl in *;
    subst; firstorder. 
  + rewrite FOvariable_dec_r. rewrite FOvariable_dec_r.
    auto. firstorder. firstorder.
  + rewrite FOvariable_dec_r. rewrite FOvariable_dec_r.
    auto. firstorder. firstorder.
  + rewrite FOvariable_dec_r. rewrite IHalpha; firstorder.
    firstorder.
  + rewrite FOvariable_dec_r. rewrite IHalpha; firstorder.
    firstorder.
  + rewrite IHalpha; auto.
  + rewrite IHalpha1. rewrite IHalpha2. auto.
    firstorder. firstorder.
  + rewrite IHalpha1. rewrite IHalpha2. auto.
    firstorder. firstorder.
  + rewrite IHalpha1. rewrite IHalpha2. auto.
    firstorder. firstorder.
  + rewrite IHalpha. auto.  firstorder. 
  + rewrite IHalpha. auto.  firstorder. 
Qed.

Lemma var_in_SO_rep_FOv : forall alpha x y,
  ~ x = y ->
  ~ var_in_SO (replace_FOv alpha x y) x.
Proof.
  induction alpha; intros x y Heq H; unfold var_in_SO in *;
    try (simpl in *; solve [firstorder]).

    simpl in *. destruct (FOvariable_dec x f).
    simpl in H. firstorder.
    simpl in *. firstorder.

    simpl in *. destruct (FOvariable_dec x f); 
                  destruct (FOvariable_dec x f0); subst;
    simpl in *; firstorder.

    simpl in *. destruct (FOvariable_dec x f); 
                  destruct (FOvariable_dec x f0); subst;
    simpl in *; firstorder.

    simpl in *. destruct (FOvariable_dec x f); simpl in *;
                  firstorder.

    simpl in *. destruct (FOvariable_dec x f); simpl in *;
                  firstorder.

    simpl in *. apply in_app_or in H. firstorder.

    simpl in *. apply in_app_or in H. firstorder.

    simpl in *. apply in_app_or in H. firstorder.
Qed.

Lemma kk3 : forall lP beta P,
(FOvars_in (replace_pred_l (allSO P beta) lP
               (nlist_list (length lP) (nlist_var (length lP) (Var 1)))
               (nlist_list (length lP) (nlist_empty (length lP))))) =
(FOvars_in (replace_pred_l beta lP
               (nlist_list (length lP) (nlist_var (length lP) (Var 1)))
               (nlist_list (length lP) (nlist_empty (length lP))))).
Proof.
  induction lP; intros beta P. auto.
  simpl in *. rewrite <- rep_pred__l_switch_empty.
  destruct (predicate_dec P a); subst.
  + rewrite kk4. rewrite rep_pred__l_switch_empty. auto.
  + simpl.  rewrite predicate_dec_r; auto. rewrite IHlP.
    rewrite rep_pred__l_switch_empty. auto.
Qed.

Lemma kk3_exSO : forall lP beta P,
(FOvars_in (replace_pred_l (exSO P beta) lP
               (nlist_list (length lP) (nlist_var (length lP) (Var 1)))
               (nlist_list (length lP) (nlist_empty (length lP))))) =
(FOvars_in (replace_pred_l beta lP
               (nlist_list (length lP) (nlist_var (length lP) (Var 1)))
               (nlist_list (length lP) (nlist_empty (length lP))))).
Proof.
  induction lP; intros beta P. auto.
  simpl in *. rewrite <- rep_pred__l_switch_empty.
  destruct (predicate_dec P a); subst.
  + rewrite kk4_exSO. rewrite rep_pred__l_switch_empty. auto.
  + simpl.  rewrite predicate_dec_r; auto. rewrite IHlP.
    rewrite rep_pred__l_switch_empty. auto.
Qed.

Lemma kk2 : forall lP beta P y,
  In y (FOvars_in (replace_pred_l (allSO P beta) lP
      (nlist_list (length lP) (nlist_var _ (Var 1)))
      (nlist_list (length lP) (nlist_empty _)))) <->
  In  y (FOvars_in (replace_pred_l  beta lP
      (nlist_list (length lP) (nlist_var _ (Var 1)))
      (nlist_list (length lP) (nlist_empty _)))).
Proof. intros. rewrite kk3. reflexivity. Qed.

Lemma kk2_exSO : forall lP beta P y,
  In y (FOvars_in (replace_pred_l (exSO P beta) lP
      (nlist_list (length lP) (nlist_var _ (Var 1)))
      (nlist_list (length lP) (nlist_empty _)))) <->
  In  y (FOvars_in (replace_pred_l  beta lP
      (nlist_list (length lP) (nlist_var _ (Var 1)))
      (nlist_list (length lP) (nlist_empty _)))).
Proof.  intros. rewrite kk3_exSO.  reflexivity. Qed.

Lemma kk5 : forall alpha P x,
  incl (FOvars_in (replace_pred alpha P x (negSO (eqFO x x))))
  (FOvars_in alpha).
Proof.
  induction alpha; intros P x; simpl; auto;
    try (apply incl_refl);
    try (apply incl_cons_cons; auto);
    try (apply incl_app_gen; auto);
    try solve [if_then_else_dest_blind; simpl; auto].
  FOv_dec_l_rep; destruct (predicate_dec P p); subst;
    simpl; repeat (constructor; firstorder). 
Qed.

Lemma kk6 : forall alpha P x,
  incl (FOvars_in alpha)
    (FOvars_in (replace_pred alpha P x (negSO (eqFO x x)))).
Proof.
  induction alpha; intros P x; simpl; auto;
    try (apply incl_refl);
    try (apply incl_cons_cons; auto);
    try (apply incl_app_gen; auto);
    try solve [if_then_else_dest_blind; simpl; auto].
  FOv_dec_l_rep. destruct (predicate_dec P p); subst;
    simpl; repeat (constructor; firstorder). 
Qed.

Lemma var_in_SO_instant_cons_empty'_pre_pre : forall beta P x y,
  var_in_SO beta x ->
  var_in_SO (replace_pred beta P y (negSO (eqFO y y ))) x .
Proof.
  induction beta; intros P x y Hocc; auto; simpl in *;
    try solve [firstorder];
    try (unfold var_in_SO in *; simpl in *; apply in_or_app;
    apply in_app_or in Hocc; firstorder).
  + FOv_dec_l_rep. destruct (predicate_dec P p); firstorder. 
  + destruct (predicate_dec P p); firstorder.
  + destruct (predicate_dec P p); firstorder.
Qed.

Lemma var_in_SO_instant_cons_empty'_pre : forall l beta x,
var_in_SO beta x ->
var_in_SO  (replace_pred_l beta l (nlist_list (length l) (nlist_var _ (Var 1)))
        (nlist_list (length l) (nlist_empty _))) x.
Proof.
  induction l; intros beta x Hocc. auto.
  simpl. apply var_in_SO_instant_cons_empty'_pre_pre.
  apply IHl. assumption.
Qed.