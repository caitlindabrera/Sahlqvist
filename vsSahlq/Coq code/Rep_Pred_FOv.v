Require Import Modal.
Require Import SecOrder.
Require Import p_is_pos.
Require Import p_occurs_in.
Require Import P_occurs_in_alpha.
Require Import ST_setup.
Require Import Correctness_ST.
Require Import Arith.EqNat.
Require Import List_machinery_impl my_bool.
Require Import Unary_Predless nList_egs pos_SO2.
(* 
  Uniform_Mod_Defns 
  Uniform_Mod_Lemmas8a
*)

(* ---------------------------------------------------------  *)

Fixpoint replace_FOv (alpha : SecOrder) (x y: FOvariable) : SecOrder :=
  match x with
  | Var xn =>
  match alpha with
    predSO (Pred n) (Var m) => 
          if EqNat.beq_nat xn m then predSO (Pred n) y else alpha
  | relatSO (Var n) (Var m) => 
          if EqNat.beq_nat xn n then if EqNat.beq_nat xn m
                                        then relatSO y y
                                        else relatSO y (Var m)
                                 else if EqNat.beq_nat xn m 
                                         then relatSO (Var n) y
                                         else alpha
  | eqFO (Var n) (Var m) =>
          if EqNat.beq_nat xn n then if EqNat.beq_nat xn m
                                        then eqFO y y
                                        else eqFO y (Var m)
                                else if EqNat.beq_nat xn m 
                                        then eqFO (Var n) y
                                        else alpha
  | allFO (Var n) beta =>
          if beq_nat xn n then allFO y (replace_FOv beta x y) 
                          else allFO (Var n) (replace_FOv beta x y) 
  | exFO (Var n) beta => 
          if beq_nat xn n then exFO y (replace_FOv beta x y)
                          else exFO (Var n) (replace_FOv beta x y)
  | negSO beta => negSO (replace_FOv beta x y)
  | conjSO beta1 beta2 => conjSO (replace_FOv beta1 x y) (replace_FOv beta2 x y)
  | disjSO beta1 beta2 => disjSO (replace_FOv beta1 x y) (replace_FOv beta2 x y)
  | implSO beta1 beta2 => implSO (replace_FOv beta1 x y) (replace_FOv beta2 x y)
  | allSO (Pred n) beta => allSO (Pred n) (replace_FOv beta x y)
  | exSO (Pred n) beta => exSO (Pred n) (replace_FOv beta x y)
  end
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
  match P with
  | Pred Pn =>
  match alpha with 
    predSO (Pred n) (Var m) => if EqNat.beq_nat Pn n then (replace_FOv cond x (Var m)) else alpha
  | relatSO (Var n) (Var m) => alpha
  | eqFO (Var n) (Var m) => alpha
  | allFO (Var n) beta => allFO (Var n) (replace_pred beta P x cond)
  | exFO (Var n) beta => exFO (Var n) (replace_pred beta P x cond)
  | negSO beta => negSO (replace_pred beta P x cond)
  | conjSO beta1 beta2 => conjSO (replace_pred beta1 P x cond) (replace_pred beta2 P x cond)
  | disjSO beta1 beta2 => disjSO (replace_pred beta1 P x cond) (replace_pred beta2 P x cond)
  | implSO beta1 beta2 => implSO (replace_pred beta1 P x cond) (replace_pred beta2 P x cond)
  | allSO (Pred n) beta => 
           if beq_nat Pn n then (replace_pred beta P x cond) 
                           else allSO (Pred n) (replace_pred beta P x cond)
  | exSO (Pred n) beta =>
           if beq_nat Pn n then (replace_pred beta P x cond) 
                           else exSO (Pred n) (replace_pred beta P x cond)
  end
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
    match P, Q with
    | Pred Pn, Pred Qm =>
    if beq_nat Pn Qm then (replace_pred alpha P y cond)
                 else allSO P (replace_pred alpha Q y cond)
    end.
Proof.
  intros.
  simpl.
  destruct Q; destruct y; destruct P.
  case_eq (beq_nat n n1); intros Hbeq.
    rewrite (beq_nat_true n n1 Hbeq).
    rewrite <- (beq_nat_refl n1).
    reflexivity.

    case_eq (beq_nat n1 n); intros Hbeq2.
      rewrite (beq_nat_true n1 n Hbeq2) in Hbeq.
      rewrite <- (beq_nat_refl n) in Hbeq; discriminate.

      reflexivity.
Qed.

Lemma rep_pred_exSO : forall (alpha cond : SecOrder) (y : FOvariable)
                              (P Q : predicate),
  (replace_pred (exSO P alpha) Q y cond) =
    match P, Q with
    | Pred Pn, Pred Qm =>
    if beq_nat Pn Qm then (replace_pred alpha P y cond)
                 else exSO P (replace_pred alpha Q y cond)
    end.
Proof.
  intros.
  simpl.
  destruct Q; destruct y; destruct P.
  case_eq (beq_nat n n1); intros Hbeq.
    rewrite (beq_nat_true n n1 Hbeq).
    rewrite <- (beq_nat_refl n1).
    reflexivity.

    case_eq (beq_nat n1 n); intros Hbeq2.
      rewrite (beq_nat_true n1 n Hbeq2) in Hbeq.
      rewrite <- (beq_nat_refl n) in Hbeq; discriminate.

      reflexivity.
Qed.

(* -------------------------------------------------------------------- *)


Lemma rep_pred_l_negSO : forall (alpha : SecOrder) (lP : list predicate)
                                (lx : list FOvariable)
                                (lcond : list SecOrder),
  replace_pred_l (negSO alpha) lP lx lcond = 
    (negSO (replace_pred_l alpha lP lx lcond)).
Proof.
  intros alpha.
  induction lP.
    simpl; reflexivity.

    induction lx.
      simpl; reflexivity.

      induction lcond.
        simpl; reflexivity.

        simpl.
        rewrite IHlP.
        rewrite rep_pred_negSO.
        reflexivity.
Qed.

Lemma rep_pred_l_allFO : forall (alpha : SecOrder) (lP : list predicate)
                        (lx : list FOvariable) (lcond : list SecOrder)
                        (x : FOvariable) ,
  replace_pred_l (allFO x alpha) lP lx lcond =
    allFO x (replace_pred_l alpha lP lx lcond).
Proof.
  intros alpha lP.
  induction lP.
    intros.
    simpl.
    reflexivity.

    intros.
    case_eq lx.
      intros Hlx.
      simpl.
      reflexivity.

      intros y lx' Hly.
      case_eq lcond.
        intros Hlcond.
        simpl.
        reflexivity.

        intros cond lcond' Hlcond.
        simpl.
        rewrite IHlP.
        rewrite rep_pred_allFO.
        reflexivity.
Qed.

Lemma rep_pred_l_exFO : forall (alpha : SecOrder) (lP : list predicate)
                        (lx : list FOvariable) (lcond : list SecOrder)
                        (x : FOvariable) ,
  replace_pred_l (exFO x alpha) lP lx lcond =
    exFO x (replace_pred_l alpha lP lx lcond).
Proof.
  intros alpha lP.
  induction lP.
    intros.
    simpl.
    reflexivity.

    intros.
    case_eq lx.
      intros Hlx.
      simpl.
      reflexivity.

      intros y lx' Hly.
      case_eq lcond.
        intros Hlcond.
        simpl.
        reflexivity.

        intros cond lcond' Hlcond.
        simpl.
        rewrite IHlP.
        rewrite rep_pred_exFO.
        reflexivity.
Qed.

Lemma rep_pred_l_eqFO : forall (lP : list predicate)
                        (lx : list FOvariable) (lcond : list SecOrder)
                        (x y : FOvariable) ,
  replace_pred_l (eqFO x y) lP lx lcond = (eqFO x y).
Proof.
  intros lP.
  induction lP.
    intros.
    simpl.
    reflexivity.

    intros.
    case_eq lx.
      intros Hlx.
      simpl.
      reflexivity.

      intros z lx' Hly.
      case_eq lcond.
        intros Hlcond.
        simpl.
        reflexivity.

        intros cond lcond' Hlcond.
        simpl.
        rewrite IHlP.
        rewrite rep_pred_eqFO.
        reflexivity.
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


Lemma rep_pred_is_unary_predless : forall (alpha : SecOrder) (P : predicate)
                              (x : FOvariable) (cond : SecOrder),
  is_unary_predless alpha = true ->
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
      assert (is_unary_predless alpha1 = true) as H1;
        try (case_eq (is_unary_predless alpha1); intros H1';
        rewrite H1' in *; [reflexivity | discriminate]);
      rewrite H1 in H; rewrite IHalpha1; try assumption;
      rewrite IHalpha2; [reflexivity | assumption]);
    try (destruct p; simpl in *; discriminate).
Qed.

Lemma rep_FOv_is_unary_predless : forall (cond : SecOrder) (x y :FOvariable),
  is_unary_predless cond = true ->
    is_unary_predless (replace_FOv cond x y) = true.
Proof.
  intros cond x y FO.
  induction cond;
    try (simpl; destruct x; destruct f;
    case (beq_nat n n0);
      destruct y; simpl;
      rewrite IHcond;
      try reflexivity;
      try assumption);
    try (simpl in *; destruct p; destruct f; discriminate);
    try (simpl in *; destruct f0; destruct f; discriminate);
    try ( simpl; destruct x; destruct f; destruct f0;
    case (beq_nat n n0);
      case (beq_nat n n1);
        simpl; destruct y; reflexivity);
    try (destruct x; simpl; apply IHcond; assumption);
    try (simpl in FO;
    assert (is_unary_predless cond1 = true);
      [case_eq (is_unary_predless cond1); intros Hbeq1 ;
        rewrite Hbeq1 in FO; [reflexivity |
        discriminate]|] ;
    rewrite H in FO;
    destruct x; simpl; rewrite IHcond1;
      [rewrite IHcond2; [reflexivity |] |];
      assumption);
    try (simpl in *; destruct x; destruct p;
      discriminate).
Qed.

(* ----------------------------------------------------------------------- *)


Lemma rep_pred_switch : forall (alpha : SecOrder) (x y : FOvariable)
                               (cond1 cond2 : SecOrder)
                                (P Q : predicate),
  is_unary_predless cond1 = true -> is_unary_predless cond2 = true ->
    match P, Q with
    | Pred Pn, Pred Qm =>
      ~(Pn = Qm) ->
       replace_pred (replace_pred alpha P x cond1) Q y cond2 = 
          replace_pred (replace_pred alpha Q y cond2) P x cond1
    end.
Proof.
  intros alpha x y cond1 cond2 P Q FO1 FO2.
  destruct P as [Pn]; destruct Q as [Qm].
  intros Hneq.
  case_eq (beq_nat Pn Qm); intros Hbeq.
    specialize (Hneq (beq_nat_true Pn Qm Hbeq));
    contradiction.

    induction alpha;
      try (destruct f; destruct f0; simpl; reflexivity);
      try (destruct f; simpl; rewrite IHalpha; reflexivity);
      try (simpl; rewrite IHalpha; reflexivity);
      try (simpl; rewrite IHalpha1; rewrite IHalpha2; reflexivity).

      simpl.
      destruct p; destruct f.
      case_eq (beq_nat Pn n); intros Hbeq1.
        case_eq (beq_nat Qm n); intros Hbeq2.
          rewrite (beq_nat_true Pn n Hbeq1) in Hbeq.
          rewrite (beq_nat_true Qm n Hbeq2) in Hbeq.
          rewrite <- beq_nat_refl in Hbeq; discriminate.

          simpl.
          rewrite Hbeq1.
          rewrite rep_pred_is_unary_predless.
            reflexivity.

            apply rep_FOv_is_unary_predless.
            assumption.

        case_eq (beq_nat Qm n); intros Hbeq2.
          simpl.
          rewrite Hbeq2.
          rewrite rep_pred_is_unary_predless.
            reflexivity.

            apply rep_FOv_is_unary_predless.
            assumption.

          simpl.
          rewrite Hbeq1.
          rewrite Hbeq2.
          reflexivity.

      simpl.
      destruct p.
      case_eq (beq_nat Pn n); intros Hbeq1.
        case_eq (beq_nat Qm n); intros Hbeq2.
          rewrite (beq_nat_true Pn n Hbeq1) in Hbeq.
          rewrite (beq_nat_true Qm n Hbeq2) in Hbeq.
          rewrite <- beq_nat_refl in Hbeq; discriminate.

          simpl.
          rewrite Hbeq1.
          assumption.

        case_eq (beq_nat Qm n); intros Hbeq2.
          simpl.
          rewrite Hbeq2.
          assumption.

          simpl.
          rewrite Hbeq1; rewrite Hbeq2.
          rewrite IHalpha.
          reflexivity.

      simpl.
      destruct p.
      case_eq (beq_nat Pn n); intros Hbeq1.
        case_eq (beq_nat Qm n); intros Hbeq2.
          rewrite (beq_nat_true Pn n Hbeq1) in Hbeq.
          rewrite (beq_nat_true Qm n Hbeq2) in Hbeq.
          rewrite <- beq_nat_refl in Hbeq; discriminate.

          simpl.
          rewrite Hbeq1.
          assumption.

        case_eq (beq_nat Qm n); intros Hbeq2.
          simpl.
          rewrite Hbeq2.
          assumption.

          simpl.
          rewrite Hbeq1; rewrite Hbeq2.
          rewrite IHalpha.
          reflexivity.
Qed.


(* ----------------------------------------------------------------------- *)


Lemma rep_pred_l_is_unary_predless : forall (alpha : SecOrder) (lP : list predicate)
                                (lx : list FOvariable) (lcond : list SecOrder),
  is_unary_predless alpha = true ->
    is_unary_predless (replace_pred_l alpha lP lx lcond) = true.
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
           try exact (is_unary_predless_conjSO_r _ _ H);
           try exact (is_unary_predless_disjSO_r _ _ H);
           try exact (is_unary_predless_implSO_r _ _ H);
           assumption] |
       try exact (is_unary_predless_conjSO_l _ _ H);
       try exact (is_unary_predless_disjSO_l _ _ H);
       try exact (is_unary_predless_implSO_l _ _ H)]);
    try (simpl in *; discriminate).
Qed.

Lemma rep_pred_l_app : forall (alpha : SecOrder)
                              (l1 l2 : list predicate),
  replace_pred_l alpha (app l1 l2)
      (nlist_list (length (app l1 l2))
                  (nlist_Var1 (length (app l1 l2))))
      (nlist_list (length (app l1 l2))
                  (nlist_empty (length (app l1 l2)))) =
  replace_pred_l (replace_pred_l alpha l2 
                      (nlist_list (length l2)
                                  (nlist_Var1 (length l2)))
                      (nlist_list (length l2)
                                  (nlist_empty (length l2)))) l1
      (nlist_list (length l1)
                  (nlist_Var1 (length l1)))
      (nlist_list (length l1)
                  (nlist_empty (length l1))).
Proof.
  intros.
  induction l1.
    simpl.
    reflexivity.

    simpl.
    rewrite IHl1.
    reflexivity.
Qed.

(* ----------------------------------------------------------------------- *)


Lemma rep_pred__l_switch_empty : forall (alpha : SecOrder) (P : predicate)
                                  (l : list predicate),
replace_pred_l 
      (replace_pred alpha P (Var 1) (negSO (eqFO (Var 1) (Var 1))))
      l
      (nlist_list (length l) (nlist_Var1 (length l)))
      (nlist_list (length l) (nlist_empty (length l))) =
replace_pred 
    (replace_pred_l alpha l 
      (nlist_list (length l) (nlist_Var1 (length l)))
      (nlist_list (length l) (nlist_empty (length l))))
    P (Var 1) (negSO (eqFO (Var 1) (Var 1))).
Proof.
  intros.
  induction l.
    simpl; reflexivity.

    simpl.
    rewrite IHl.
    destruct P as [Pn]; destruct a as [Qm].
    case_eq (beq_nat Pn Qm); intros Hbeq.
      rewrite (beq_nat_true Pn Qm Hbeq).
      reflexivity.

      rewrite (rep_pred_switch _ (Var 1) _ _
                _ (Pred Pn) (Pred Qm));
        simpl; try reflexivity.

        exact (beq_nat_false Pn Qm Hbeq).
Qed.


Lemma rep_pred_l_switch : forall (alpha : SecOrder)
                                 (l1 l2 : list predicate),
replace_pred_l 
(replace_pred_l alpha l1 
      (nlist_list (length l1)
          (nlist_Var1 (length l1)))
      (nlist_list (length l1)
          (nlist_empty (length l1)))) l2
    (nlist_list (length l2)
        (nlist_Var1 (length l2)))
    (nlist_list (length l2)
        (nlist_empty (length l2))) =
replace_pred_l 
(replace_pred_l alpha l2 
      (nlist_list (length l2)
          (nlist_Var1 (length l2)))
      (nlist_list (length l2)
          (nlist_empty (length l2)))) l1
    (nlist_list (length l1)
        (nlist_Var1 (length l1)))
    (nlist_list (length l1)
        (nlist_empty (length l1))).
Proof.
  intros.
  induction l1.
    simpl.
    reflexivity.

    simpl.
    rewrite <- IHl1.
    rewrite rep_pred__l_switch_empty.
    reflexivity.
Qed.


Lemma rep_pred__l_switch_t : forall (alpha : SecOrder) (P : predicate)
                                  (l : list predicate),
replace_pred_l 
      (replace_pred alpha P (Var 1) (eqFO (Var 1) (Var 1)))
      l
      (nlist_list (length l) (nlist_Var1 (length l)))
      (nlist_list (length l) (nlist_full (length l))) =
replace_pred 
    (replace_pred_l alpha l 
      (nlist_list (length l) (nlist_Var1 (length l)))
      (nlist_list (length l) (nlist_full (length l))))
    P (Var 1) (eqFO (Var 1) (Var 1)).
Proof.
  intros.
  induction l.
    simpl; reflexivity.

    simpl.
    rewrite IHl.
    destruct P as [Pn]; destruct a as [Qm].
    case_eq (beq_nat Pn Qm); intros Hbeq.
      rewrite (beq_nat_true Pn Qm Hbeq).
      reflexivity.

      rewrite (rep_pred_switch _ (Var 1) _ _
                _ (Pred Pn) (Pred Qm));
        simpl; try reflexivity.

        exact (beq_nat_false Pn Qm Hbeq).
Qed.


Lemma rep_pred_l_switch_t : forall (alpha : SecOrder)
                                 (l1 l2 : list predicate),
replace_pred_l 
(replace_pred_l alpha l1 
      (nlist_list (length l1)
          (nlist_Var1 (length l1)))
      (nlist_list (length l1)
          (nlist_full (length l1)))) l2
    (nlist_list (length l2)
        (nlist_Var1 (length l2)))
    (nlist_list (length l2)
        (nlist_full (length l2))) =
replace_pred_l 
(replace_pred_l alpha l2 
      (nlist_list (length l2)
          (nlist_Var1 (length l2)))
      (nlist_list (length l2)
          (nlist_full (length l2)))) l1
    (nlist_list (length l1)
        (nlist_Var1 (length l1)))
    (nlist_list (length l1)
        (nlist_full (length l1))).
Proof.
  intros.
  induction l1.
    simpl.
    reflexivity.

    simpl.
    rewrite <- IHl1.
    rewrite rep_pred__l_switch_t.
    reflexivity.
Qed.


(* ----------------------------------------------------------------------- *)


Lemma preds_in_rep_FOv : forall (cond : SecOrder) (x y : FOvariable),
  (preds_in (replace_FOv cond x y)) = preds_in cond.
Proof.
  intros.
  induction cond;
    try (destruct p; destruct f as [zn]; destruct x as [xn]; destruct y as [ym];
    simpl preds_in;
    case (beq_nat xn zn);
    simpl; reflexivity);
    try (destruct f as [x1]; destruct f0 as [x2]; 
    destruct x as [x3]; destruct y as [x4];
    simpl;
    case (beq_nat x3 x1); case (beq_nat x3 x2); simpl; reflexivity);
    try ( destruct f as [x1]; destruct x as [x2]; destruct y as [x3];
    simpl; case (beq_nat x2 x1); assumption);
    try (destruct x as [xn]; simpl; assumption);
    try (destruct x as [xn]; simpl; rewrite IHcond1; rewrite IHcond2;
          reflexivity);
    try (destruct x as [xn]; destruct p as [Pn]; simpl;
    rewrite IHcond; reflexivity).
Qed.

(* ----------------------------------------------------------------------- *)


Lemma SOt_alt_SOQFree : forall (alpha : SecOrder) (W : Set)
                      (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
                    (Ir : W -> W -> Prop)  (Q : predicate),
  SOQFree alpha = true ->
    (SOturnst W Iv (altered_Ip Ip pa_f Q) Ir alpha <->
      SOturnst W Iv Ip Ir (replace_pred alpha Q (Var 1)
       (negSO (eqFO (Var 1) (Var 1))))).
Proof.
  induction alpha; intros W Iv Ip Ir Q HallSO.
    unfold pa_f.
    simpl in *.
    destruct p as [Pn]; destruct f as [xn]; destruct Q as [Qm].
    case_eq (beq_nat Qm Pn); intros Hbeq.
      rewrite (beq_nat_true Qm Pn Hbeq).
      simpl.
      rewrite <- beq_nat_refl.
      split; intros H.
        contradiction.

        unfold not in *.
        specialize (H eq_refl).
        contradiction.

      simpl.
      rewrite Hbeq in *.
      apply iff_refl.

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
    split; intros H d;
      (apply IHalpha; [assumption | apply H]).

    rewrite rep_pred_exFO.
    do 2 rewrite SOturnst_exFO.
    pose proof (SOQFree_exFO alpha f HallSO) as HallSO'.
    split; intros H; destruct H as [d H]; exists d;
      (apply IHalpha; [assumption | apply H]).

    rewrite rep_pred_negSO.
    do 2 rewrite SOturnst_negSO.
    split; intros H;
      unfold not; intros H2;
      apply H;
      apply IHalpha;
      assumption.

    rewrite rep_pred_conjSO.
    do 2 rewrite SOturnst_conjSO.
    pose proof (SOQFree_conjSO_l alpha1 alpha2 HallSO) as H1.
    pose proof (SOQFree_conjSO_r alpha1 alpha2 HallSO) as H2.
    simpl in HallSO.
    split; intros H; apply conj;
      try (apply IHalpha1; [assumption | apply H]);
      try (apply IHalpha2; [assumption | apply H]).

    rewrite rep_pred_disjSO.
    do 2 rewrite SOturnst_disjSO.
    pose proof (SOQFree_disjSO_l alpha1 alpha2 HallSO) as H1.
    pose proof (SOQFree_disjSO_r alpha1 alpha2 HallSO) as H2.
    split; intros H;
      (destruct H as [H | H];
      [left; apply IHalpha1 |
      right; apply IHalpha2]; assumption;
      apply H).

    rewrite rep_pred_implSO.
    do 2 rewrite SOturnst_implSO.
    pose proof (SOQFree_implSO_l alpha1 alpha2 HallSO) as H1.
    pose proof (SOQFree_implSO_r alpha1 alpha2 HallSO) as H2.
    split; intros H H3;
      apply IHalpha2; [assumption | apply H | assumption | apply H];
      apply IHalpha1; assumption.

    simpl in HallSO.
    destruct p; discriminate.

    simpl in HallSO.
    destruct p; discriminate.
Qed.


Lemma SOt_alt_SOQFree_t : forall (alpha : SecOrder) (W : Set)
                      (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
                    (Ir : W -> W -> Prop)  (Q : predicate),
  SOQFree alpha = true ->
    (SOturnst W Iv (altered_Ip Ip pa_t Q) Ir alpha <->
      SOturnst W Iv Ip Ir (replace_pred alpha Q (Var 1)
       (eqFO (Var 1) (Var 1)))).
Proof.
  induction alpha; intros W Iv Ip Ir Q HallSO.
    unfold pa_f.
    simpl in *.
    destruct p as [Pn]; destruct f as [xn]; destruct Q as [Qm].
    case_eq (beq_nat Qm Pn); intros Hbeq.
      rewrite (beq_nat_true Qm Pn Hbeq).
      simpl.
      rewrite <- beq_nat_refl.
      unfold pa_t.
      split; reflexivity.

      simpl.
      rewrite Hbeq in *.
      apply iff_refl.

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
    split; intros H d;
      (apply IHalpha; [assumption | apply H]).

    rewrite rep_pred_exFO.
    do 2 rewrite SOturnst_exFO.
    pose proof (SOQFree_exFO alpha f HallSO) as HallSO'.
    split; intros H; destruct H as [d H]; exists d;
      (apply IHalpha; [assumption | apply H]).

    rewrite rep_pred_negSO.
    do 2 rewrite SOturnst_negSO.
    split; intros H;
      unfold not; intros H2;
      apply H;
      apply IHalpha;
      assumption.

    rewrite rep_pred_conjSO.
    do 2 rewrite SOturnst_conjSO.
    pose proof (SOQFree_conjSO_l alpha1 alpha2 HallSO) as H1.
    pose proof (SOQFree_conjSO_r alpha1 alpha2 HallSO) as H2.
    simpl in HallSO.
    split; intros H; apply conj;
      try (apply IHalpha1; [assumption | apply H]);
      try (apply IHalpha2; [assumption | apply H]).

    rewrite rep_pred_disjSO.
    do 2 rewrite SOturnst_disjSO.
    pose proof (SOQFree_disjSO_l alpha1 alpha2 HallSO) as H1.
    pose proof (SOQFree_disjSO_r alpha1 alpha2 HallSO) as H2.
    split; intros H;
      (destruct H as [H | H];
      [left; apply IHalpha1 |
      right; apply IHalpha2]; assumption;
      apply H).

    rewrite rep_pred_implSO.
    do 2 rewrite SOturnst_implSO.
    pose proof (SOQFree_implSO_l alpha1 alpha2 HallSO) as H1.
    pose proof (SOQFree_implSO_r alpha1 alpha2 HallSO) as H2.
    split; intros H H3;
      apply IHalpha2; [assumption | apply H | assumption | apply H];
      apply IHalpha1; assumption.

    simpl in HallSO.
    destruct p; discriminate.

    simpl in HallSO.
    destruct p; discriminate.
Qed.

Lemma SOQFree_rep_FOv : forall alpha x y,
  SOQFree alpha = true ->
  SOQFree (replace_FOv alpha x y) = true.
Proof.
  induction alpha; intros [xn] [ym] H.
    destruct p; destruct f as [zn].
    simpl. case_eq (beq_nat xn zn);
      intros Hbeq; reflexivity.

    destruct f as [z1]; destruct f0 as [z2]. simpl.
      case_eq (beq_nat xn z1); intros Hbeq;
        case_eq (beq_nat xn z2); intros Hbeq2;
          reflexivity.

    destruct f as [z1]; destruct f0 as [z2]. simpl.
      case_eq (beq_nat xn z1); intros Hbeq;
        case_eq (beq_nat xn z2); intros Hbeq2;
          reflexivity.

    destruct f as [z1]. simpl.
      case_eq (beq_nat xn z1); intros Hbeq;
        simpl; apply IHalpha; apply H.

    destruct f as [z1]. simpl.
      case_eq (beq_nat xn z1); intros Hbeq;
        simpl; apply IHalpha; apply H.

    simpl in *. apply IHalpha. assumption.

    pose proof (SOQFree_conjSO_r _ _ H) as H3.
    apply SOQFree_conjSO_l in H.
    simpl. rewrite IHalpha1.
    apply IHalpha2. all : try assumption.

    pose proof (SOQFree_conjSO_r _ _ H) as H3.
    apply SOQFree_conjSO_l in H.
    simpl. rewrite IHalpha1.
    apply IHalpha2. all : try assumption.

    pose proof (SOQFree_conjSO_r _ _ H) as H3.
    apply SOQFree_conjSO_l in H.
    simpl. rewrite IHalpha1.
    apply IHalpha2. all : try assumption.

    destruct p. simpl in *.
    discriminate.
    destruct p. simpl in *.
    discriminate.
Qed.


Lemma SOQFree_rep_pred : forall alpha cond P x,
  SOQFree alpha = true ->
  SOQFree cond = true ->
  SOQFree (replace_pred alpha P x cond) = true.
Proof.
  induction alpha; intros cond [Pn] [xn] H1 H2.
    destruct p as [Qm]; destruct f.
    simpl in *.
    case_eq (beq_nat Pn Qm); intros Hbeq.
      apply SOQFree_rep_FOv.
      assumption.

      simpl. reflexivity.

    destruct f. destruct f0. reflexivity.

    destruct f. destruct f0. reflexivity.

    destruct f. simpl in *. apply IHalpha;
    assumption.

    destruct f. simpl in *. apply IHalpha;
    assumption.

    simpl in *. apply IHalpha;
    assumption.

    pose proof (SOQFree_conjSO_r _ _ H1) as H3.
    apply SOQFree_conjSO_l in H1.
    simpl. rewrite IHalpha1.
    apply IHalpha2. all : try assumption.

    pose proof (SOQFree_conjSO_r _ _ H1) as H3.
    apply SOQFree_conjSO_l in H1.
    simpl. rewrite IHalpha1.
    apply IHalpha2. all : try assumption.

    pose proof (SOQFree_conjSO_r _ _ H1) as H3.
    apply SOQFree_conjSO_l in H1.
    simpl. rewrite IHalpha1.
    apply IHalpha2. all : try assumption.

    destruct p as [Qm].
    simpl in *. discriminate.

    destruct p as [Qm].
    simpl in *. discriminate.
Qed.

Lemma SOQFree_rep_pred_empty : forall (alpha : SecOrder) (Q : predicate),
  SOQFree alpha = true -> 
    SOQFree (replace_pred alpha Q (Var 1) 
      (negSO (eqFO (Var 1) (Var 1)))) = true.
Proof.
  induction alpha.
    intros Q HSO.
    destruct p as [Pn]; destruct f as [xn]; destruct Q as [Qm].
    simpl.
    case_eq (beq_nat Qm Pn); intros Hbeq.
      simpl; reflexivity.

      assumption.

    intros Q HSO.
    destruct f as [xn]; destruct f0 as [xm]; destruct Q as [Qm].
    simpl; reflexivity.

    intros Q HSO.
    destruct f as [xn]; destruct f0 as [xm]; destruct Q as [Qm].
    simpl; reflexivity.

    intros Q HSO.
    destruct Q as [Qm]; destruct f as [xn].
    simpl.
    apply IHalpha.
    assumption.

    intros Q HSO.
    destruct Q as [Qm]; destruct f as [xn].
    simpl.
    apply IHalpha.
    assumption.

    intros Q HSO.
    simpl.
    destruct Q as [Qm].
    simpl.
    apply IHalpha.
    assumption.

    intros Q HSO.
    simpl.
    destruct Q as [Qm].
    simpl.
    pose proof (SOQFree_conjSO_l _ _ HSO) as H1.
    pose proof (SOQFree_conjSO_r _ _ HSO) as H2.
    rewrite IHalpha1;
      [rewrite IHalpha2 | assumption];
      [reflexivity | assumption].

    intros Q HSO.
    simpl.
    destruct Q as [Qm].
    simpl.
    pose proof (SOQFree_disjSO_l _ _ HSO) as H1.
    pose proof (SOQFree_disjSO_r _ _ HSO) as H2.
    rewrite IHalpha1;
      [rewrite IHalpha2 | assumption];
      [reflexivity | assumption].

    intros Q HSO.
    simpl.
    destruct Q as [Qm].
    simpl.
    pose proof (SOQFree_implSO_l _ _ HSO) as H1.
    pose proof (SOQFree_implSO_r _ _ HSO) as H2.
    rewrite IHalpha1;
      [rewrite IHalpha2 | assumption];
      [reflexivity | assumption].

    intros Q HSO.
    simpl in HSO.
    destruct p; discriminate.

    intros Q HSO.
    simpl in HSO.
    destruct p; discriminate.
Qed.


Lemma SOQFree_rep_pred_t : forall (alpha : SecOrder) (Q : predicate),
  SOQFree alpha = true -> 
    SOQFree (replace_pred alpha Q (Var 1) 
      (eqFO (Var 1) (Var 1))) = true.
Proof.
  induction alpha.
    intros Q HSO.
    destruct p as [Pn]; destruct f as [xn]; destruct Q as [Qm].
    simpl.
    case_eq (beq_nat Qm Pn); intros Hbeq.
      simpl; reflexivity.

      assumption.

    intros Q HSO.
    destruct f as [xn]; destruct f0 as [xm]; destruct Q as [Qm].
    simpl; reflexivity.

    intros Q HSO.
    destruct f as [xn]; destruct f0 as [xm]; destruct Q as [Qm].
    simpl; reflexivity.

    intros Q HSO.
    destruct Q as [Qm]; destruct f as [xn].
    simpl.
    apply IHalpha.
    assumption.

    intros Q HSO.
    destruct Q as [Qm]; destruct f as [xn].
    simpl.
    apply IHalpha.
    assumption.

    intros Q HSO.
    simpl.
    destruct Q as [Qm].
    simpl.
    apply IHalpha.
    assumption.

    intros Q HSO.
    simpl.
    destruct Q as [Qm].
    simpl.
    pose proof (SOQFree_conjSO_l _ _ HSO) as H1.
    pose proof (SOQFree_conjSO_r _ _ HSO) as H2.
    rewrite IHalpha1;
      [rewrite IHalpha2 | assumption];
      [reflexivity | assumption].

    intros Q HSO.
    simpl.
    destruct Q as [Qm].
    simpl.
    pose proof (SOQFree_disjSO_l _ _ HSO) as H1.
    pose proof (SOQFree_disjSO_r _ _ HSO) as H2.
    rewrite IHalpha1;
      [rewrite IHalpha2 | assumption];
      [reflexivity | assumption].

    intros Q HSO.
    simpl.
    destruct Q as [Qm].
    simpl.
    pose proof (SOQFree_implSO_l _ _ HSO) as H1.
    pose proof (SOQFree_implSO_r _ _ HSO) as H2.
    rewrite IHalpha1;
      [rewrite IHalpha2 | assumption];
      [reflexivity | assumption].

    intros Q HSO.
    simpl in HSO.
    destruct p; discriminate.

    intros Q HSO.
    simpl in HSO.
    destruct p; discriminate.
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
  (replace_pred_l alpha l (nlist_list (length l) (nlist_Var1 (length l)))
     (nlist_list (length l) (nlist_empty (length l)))) = true.
Proof.
  induction l; intros alpha HSO.
    simpl.
    assumption.

    simpl.
    apply SOQFree_rep_pred_empty.
    apply IHl.
    assumption.
Qed.

Lemma SOQFree_rep_pred_l_t : forall (l : list predicate) (alpha : SecOrder) ,
 SOQFree alpha = true ->
    SOQFree
  (replace_pred_l alpha l (nlist_list (length l) (nlist_Var1 (length l)))
     (nlist_list (length l) (nlist_full (length l)))) = true.
Proof.
  induction l; intros alpha HSO.
    simpl.
    assumption.

    simpl.
    apply SOQFree_rep_pred_t.
    apply IHl.
    assumption.
Qed.

Lemma SOt_list_closed_SOQFree : forall (l : list predicate) (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
                    (Ir : W -> W -> Prop) (alpha : SecOrder) ,
  SOQFree alpha = true ->
    SOturnst W Iv Ip Ir (list_closed_SO alpha l) ->
      SOturnst W Iv Ip Ir (replace_pred_l alpha l
                          (nlist_list _ (nlist_Var1 (length l)))
                          (nlist_list _ (nlist_empty (length l)))).
Proof.
  induction l.
    intros W Iv Ip Ir alpha Hquant HSOt.
    simpl in *.
    assumption.

    intros W Iv Ip Ir alpha Hquant HSOt.
    simpl.
    apply SOt_alt_SOQFree.
      apply SOQFree_rep_pred_l_nlist.
      assumption.

      apply IHl.
        assumption.

        simpl list_closed_SO in HSOt.
        rewrite SOturnst_allSO in HSOt.
        apply HSOt.
Qed.

Lemma instant_uni_closed : forall (phi : Modal) (D : Set) (Iv:FOvariable -> D)
                               (Ip: predicate -> D -> Prop) (Ir: D -> D -> Prop)
                               (x : FOvariable),
  (SOturnst D Iv Ip Ir (uni_closed_SO (allFO x (ST phi x))) ->
    (SOturnst D Iv Ip Ir (replace_pred_l (allFO x (ST phi x))
          (preds_in (allFO x (ST phi x)))
          (nlist_list _ (nlist_Var1 (length (preds_in (ST phi x)))))
          (nlist_list _ (nlist_empty (length (preds_in (ST phi x)))) )))).
Proof.
  intros.
  unfold uni_closed_SO in H.
  assert (SOQFree (allFO x (ST phi x)) = true) as H2.
    simpl SOQFree.
    destruct x.
    apply SOQFree_ST.
  apply SOt_list_closed_SOQFree in H;  assumption.
Qed.


Lemma SOt_list_closed_SOQFree_t : forall (l : list predicate) (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
                    (Ir : W -> W -> Prop) (alpha : SecOrder) ,
  SOQFree alpha = true ->
    SOturnst W Iv Ip Ir (list_closed_SO alpha l) ->
      SOturnst W Iv Ip Ir (replace_pred_l alpha l
                          (nlist_list _ (nlist_Var1 (length l)))
                          (nlist_list _ (nlist_full (length l)))).
Proof.
  induction l.
    intros W Iv Ip Ir alpha Hquant HSOt.
    simpl in *.
    assumption.

    intros W Iv Ip Ir alpha Hquant HSOt.
    simpl.
    apply SOt_alt_SOQFree_t.
      apply SOQFree_rep_pred_l_t.
      assumption.

      apply IHl.
        assumption.

        simpl list_closed_SO in HSOt.
        rewrite SOturnst_allSO in HSOt.
        apply HSOt.
Qed.

Lemma instant_uni_closed_t : forall (phi : Modal) (D : Set) (Iv:FOvariable -> D)
                               (Ip: predicate -> D -> Prop) (Ir: D -> D -> Prop)
                               (x : FOvariable),
  (SOturnst D Iv Ip Ir (uni_closed_SO (allFO x (ST phi x))) ->
    (SOturnst D Iv Ip Ir (replace_pred_l (allFO x (ST phi x))
          (preds_in (allFO x (ST phi x)))
          (nlist_list _ (nlist_Var1 (length (preds_in (ST phi x)))))
          (nlist_list _ (nlist_full (length (preds_in (ST phi x)))) )))).
Proof.
  intros.
  unfold uni_closed_SO in H.
  assert (SOQFree (allFO x (ST phi x)) = true) as H2.
    simpl SOQFree.
    destruct x.
    apply SOQFree_ST.
  apply SOt_list_closed_SOQFree_t in H; assumption.
Qed.


Lemma rep_pred_false_pa_t : forall (alpha : SecOrder)  (W : Set) (Iv : FOvariable -> W)
                    (Ip : predicate -> W -> Prop)
                    (Ir : W -> W -> Prop)
                    (P : predicate),
  SOQFree alpha = true ->
  SOturnst W Iv Ip Ir (replace_pred alpha P (Var 1)
                          (eqFO (Var 1) (Var 1))) <->
  SOturnst W Iv (altered_Ip Ip pa_t P) Ir alpha.
Proof.
  induction alpha; intros W Iv Ip Ir P noSO;
    try destruct P as [Pn]; try destruct p as [Qm];
    try destruct f; try destruct f0.

    simpl; unfold pa_t.
    case_eq (beq_nat Pn Qm); intros Hbeq.
      simpl; split; intros H; reflexivity.
      simpl.
      apply iff_refl.

    simpl; apply iff_refl.
    simpl; apply iff_refl.

    rewrite rep_pred_allFO.
    do 2 rewrite SOturnst_allFO.
    simpl in noSO.
    split; (intros H d;
      apply IHalpha; [assumption | apply H]).

    rewrite rep_pred_exFO.
    do 2 rewrite SOturnst_exFO.
    split; intros H; destruct H as [d H];
      exists d; apply IHalpha;
      assumption.

    rewrite rep_pred_negSO.
    do 2 rewrite SOturnst_negSO.
    unfold not.
    split; intros H1 H2;
      apply H1; apply IHalpha;
      assumption.

    rewrite rep_pred_conjSO.
    do 2 rewrite SOturnst_conjSO.
    pose proof (SOQFree_conjSO_l _ _ noSO) as H1.
    pose proof (SOQFree_conjSO_r _ _ noSO) as H2.
    split; (intros H; apply conj;
      [apply IHalpha1 | apply IHalpha2]);
      try assumption; apply H.

    rewrite rep_pred_disjSO.
    pose proof (SOQFree_conjSO_l _ _ noSO) as H1.
    pose proof (SOQFree_conjSO_r _ _ noSO) as H2.
    do 2 rewrite SOturnst_disjSO.
    split; (intros H; destruct H;
      [left; apply IHalpha1 | 
        right; apply IHalpha2]);
      assumption.

    rewrite rep_pred_implSO.
    do 2 rewrite SOturnst_implSO.
    pose proof (SOQFree_conjSO_l _ _ noSO) as Hl.
    pose proof (SOQFree_conjSO_r _ _ noSO) as Hr.
    split; intros H1 H2; apply IHalpha2; try assumption;
      apply H1; apply IHalpha1; assumption.

    simpl in noSO; discriminate.
    simpl in noSO; discriminate.
Qed.

(* ----------------------------------------------------------- *)


Lemma P_occ_rep_pred_f : forall (alpha cond : SecOrder) (P : predicate)
                              (x : FOvariable),
  P_occurs_in_alpha alpha P = false ->
    replace_pred alpha P x cond = alpha.
Proof.
  intros.
  induction alpha;
    try destruct P as [Pn];
    try destruct Q as [Qm];
    try destruct p as [Sn];
    try destruct f as [xn];
    try destruct f0 as [xm];
    try (unfold P_occurs_in_alpha in H;
      simpl in *;
      case_eq (beq_nat Pn Sn); intros Hbeq; rewrite Hbeq in *;
        [discriminate | reflexivity]);
    try (simpl in *; reflexivity);
    try (simpl in *;
      rewrite IHalpha;
        [reflexivity |
        unfold P_occurs_in_alpha; simpl in *; assumption]);
    try (unfold P_occurs_in_alpha in H;
      simpl in *;
      pose proof (P_occurs_in_l_app (preds_in alpha1)
                                    (preds_in alpha2)
                                    (Pred Pn)) as H2;
      apply contrapos_bool_or in H2;
      apply H2 in H;
      rewrite IHalpha1;
        [rewrite IHalpha2|]; try reflexivity; apply H);
    try ( unfold P_occurs_in_alpha in H;
      simpl in *;
      case_eq (beq_nat Pn Sn); intros Hbeq; rewrite Hbeq in *;
        [discriminate | ];
        rewrite IHalpha; [reflexivity | assumption]).
Qed.

Lemma P_occ_rep_pred_f2 : forall (alpha cond : SecOrder) (P Q : predicate)
                                  (x : FOvariable), 
  P_occurs_in_alpha cond P = false ->
    P_occurs_in_alpha alpha P = false ->
      P_occurs_in_alpha (replace_pred alpha Q x cond) P = false.
Proof.
  intros alpha cond P Q x Hcond Halpha.
  induction alpha;
    try destruct P as [Pn];
    try destruct Q as [Qm];
    try destruct p as [Sn];
    try destruct f as [xn];
    try destruct f0 as [xm];
    try (unfold P_occurs_in_alpha;
      simpl in *; reflexivity);
    try (unfold P_occurs_in_alpha; simpl in *;
      apply IHalpha;
      assumption);
    try ( simpl in *;
      unfold P_occurs_in_alpha;
      case_eq (beq_nat Qm Sn); intros Hbeq;
        [rewrite preds_in_rep_FOv|  simpl];
        assumption);
    try ( simpl;
      pose proof (P_occurs_in_alpha_conjSO 
                    (replace_pred alpha1 (Pred Qm) x cond)
                    (replace_pred alpha2 (Pred Qm) x cond) (Pred Pn)) as H;
      apply contrapos_bool_or in H;
      apply H;
      pose proof (P_occurs_in_alpha_conjSO alpha1 alpha2 (Pred Pn)) as H2;
      apply contrapos_bool_or in H2;
      apply H2 in Halpha;
      apply conj; [apply IHalpha1 | apply IHalpha2]; apply Halpha);
    try ( unfold P_occurs_in_alpha in *;
      simpl in *;
        case_eq (beq_nat Pn Sn); intros Hbeq2; rewrite Hbeq2 in *;
          [discriminate | ];
          case_eq (beq_nat Qm Sn); intros Hbeq;
            [ | simpl; rewrite Hbeq2]; apply IHalpha; assumption).
Qed.

Lemma P_occ_rep_pred_l_empty : forall (l : list predicate) (alpha : SecOrder) 
                                (P : predicate),
  P_occurs_in_alpha alpha P = false ->
    P_occurs_in_alpha (replace_pred_l alpha l 
                        (nlist_list (length l) (nlist_Var1 (length l)))
                        (nlist_list (length l) (nlist_empty (length l)))) P
          = false.
Proof.
  induction l; intros alpha P HPocc.
    simpl.
    assumption.

    simpl.
    rewrite <- rep_pred__l_switch_empty.
    apply IHl.
    rewrite P_occ_rep_pred_f2.
      reflexivity.

      unfold P_occurs_in_alpha; simpl; reflexivity.

      assumption.
Qed.
