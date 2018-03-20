Require Import SecOrder.
Require Import P_occurs_in_alpha.
Require Import ST_setup.
Require Import Correctness_ST.
Require Import Arith.EqNat.
Require Import List_machinery_impl My_List_Map my_arith__my_leb_nat.
Require Import Unary_Predless nList_egs Rep_Pred_FOv Indicies Unary_Predless_l List.
(* 
  Uniform_Mod_Lemmas8a
*)

(* ---------------------------------------------------------  *)

Definition num_occ (alpha : SecOrder) (Q : predicate) : nat :=
  length (indicies alpha Q).

Lemma num_occ_conjSO2 : forall (alpha1 alpha2 : SecOrder) (Q : predicate),
  num_occ (conjSO alpha1 alpha2) Q =  (length (indicies alpha1 Q)) +
                                       (length (indicies alpha2 Q)).
Proof.
  intros.
  unfold num_occ.
  rewrite indicies_conjSO.
  rewrite app_length.
  unfold indicies.
  do 3 rewrite list_map_length.
  reflexivity.
Qed.

Lemma num_occ_disjSO2 : forall (alpha1 alpha2 : SecOrder) (Q : predicate),
  num_occ (disjSO alpha1 alpha2) Q =  (length (indicies alpha1 Q)) +
                                       (length (indicies alpha2 Q)).
Proof.
  intros.
  unfold num_occ.
  rewrite indicies_disjSO.
  rewrite app_length.
  unfold indicies.
  do 3 rewrite list_map_length.
  reflexivity.
Qed.

Lemma num_occ_predSO : forall (P Q : predicate) (x : FOvariable),
  num_occ (predSO P x) Q = match P, Q with
                           | Pred Pn, Pred Qm =>
                          if beq_nat Pn Qm then 1 else 0
                          end.
Proof.
  intros.
  destruct P as [Pn]; destruct Q as [Qm]; destruct x as [xn].
  unfold num_occ.
  unfold indicies.
  simpl.
  rewrite list_map_length.
  case (beq_nat Pn Qm); simpl; reflexivity.
Qed.
  

Lemma num_occ_allSO : forall (alpha : SecOrder) (P Q : predicate),
  num_occ (allSO P alpha) Q = match P, Q with
                           | Pred Pn, Pred Qm =>
                          if beq_nat Pn Qm then 1 + num_occ alpha Q else num_occ alpha Q
                          end.
Proof.
  intros.
  destruct P as [Pn]; destruct Q as [Qm].
  unfold num_occ.
  unfold indicies.
  simpl.
  do 2 rewrite list_map_length.
  case (beq_nat Pn Qm); simpl; reflexivity.
Qed.

(* ---------------------------------------------------------  *)

Fixpoint is_in_l (l : list nat) (i : nat) : bool :=
  match l with
  | nil => false
  | cons n l' => if beq_nat i n then true else is_in_l l' i
  end.

Lemma is_in_l_app : forall (l1 l2 : list nat) (i : nat),
  is_in_l (l1 ++ l2) i = if is_in_l l1 i 
                          then true
                          else is_in_l l2 i.
Proof.
  intros.
  induction l1.
    simpl; reflexivity.

    simpl.
    rewrite IHl1.
    case (beq_nat i a);
      reflexivity.
Qed.

(* ---------------------------------------------------------  *)

Fixpoint num_occ_diff_l (l : list nat) (i : nat) : nat :=
  if is_in_l l i then 0 else
  match l with
  | nil => 0
  | cons n l' => if Nat.leb n i 
                    then 1 + num_occ_diff_l l' i
                    else num_occ_diff_l l' i
  end.

Lemma num_occ_diff_l_defn : forall (l : list nat) (i : nat),
  num_occ_diff_l l i =
  if is_in_l l i then 0 else
  match l with
  | nil => 0
  | cons n l' => if Nat.leb n i 
                    then 1 + num_occ_diff_l l' i
                    else num_occ_diff_l l' i
  end.
Proof.
  intros.
  unfold num_occ_diff_l.
  induction l; simpl; reflexivity.
Qed.

Lemma num_occ_diff_l_cons : forall (l : list nat) (a i : nat),
  num_occ_diff_l (cons a l) i =
    if is_in_l (cons a l) i 
       then 0 
       else if Nat.leb a i 
               then 1 + num_occ_diff_l l i
               else num_occ_diff_l l i.
Proof.
  intros; simpl.
  reflexivity.
Qed.

Lemma num_occ_diff_l_app : forall (l1 l2 : list nat) (i : nat),
  is_in_l l1 i = false ->
    is_in_l l2 i = false ->
      num_occ_diff_l (app l1 l2) i =
        (num_occ_diff_l l1 i) + (num_occ_diff_l l2 i).
Proof.
  induction l1.
    intros.
    simpl; reflexivity.

    intros l2 i H1 H2.
    rewrite num_occ_diff_l_cons.
    rewrite H1.
    simpl in *.
    case_eq (beq_nat i a); intros Hbeq; rewrite Hbeq in *.
      discriminate.

      rewrite is_in_l_app.
      rewrite IHl1.
      rewrite H1.
      rewrite H2.
      case (Nat.leb a i).
        simpl; reflexivity.

        reflexivity.

      assumption.

      assumption.
Qed.

Definition num_occ_diff (alpha : SecOrder) (Q : predicate) (i : nat)
                                              : nat :=
  num_occ_diff_l (indicies alpha Q) i.


Lemma num_occ_diff_relatSO : forall ( x y : FOvariable)
                                   (Q : predicate) (i : nat),
  num_occ_diff (relatSO x y) Q i = 0.
Proof.
  intros x y Q i.
  unfold num_occ_diff.
  unfold indicies.
  destruct x; destruct y.
  simpl.
  reflexivity.
Qed.

Lemma num_occ_diff_eqFO : forall ( x y : FOvariable)
                                   (Q : predicate) (i : nat),
  num_occ_diff (eqFO x y) Q i = 0.
Proof.
  intros x y Q i.
  unfold num_occ_diff.
  unfold indicies.
  destruct x; destruct y.
  simpl.
  reflexivity.
Qed.


Lemma num_occ_diff_allFO : forall (alpha : SecOrder) (x : FOvariable)
                                  (Q : predicate) (i : nat),
  num_occ_diff (allFO x alpha) Q i = 
    num_occ_diff alpha Q i.
Proof.
  intros.
  unfold num_occ_diff.
  unfold num_occ_diff_l.
  reflexivity.
Qed.

Lemma num_occ_diff_exFO : forall (alpha : SecOrder) (x : FOvariable)
                                  (Q : predicate) (i : nat),
  num_occ_diff (exFO x alpha) Q i = 
    num_occ_diff alpha Q i.
Proof.
  intros.
  unfold num_occ_diff.
  unfold num_occ_diff_l.
  unfold indicies.
  simpl.
  destruct x.
  reflexivity.
Qed.

Lemma num_occ_diff_negSO : forall (alpha : SecOrder)
                                  (Q : predicate) (i : nat),
  num_occ_diff (negSO alpha) Q i = 
    num_occ_diff alpha Q i.
Proof.
  intros.
  unfold num_occ_diff.
  unfold num_occ_diff_l.
  unfold indicies.
  simpl.
  reflexivity.
Qed.

(* ------------------------------------------------------------- *)



Lemma num_occ_diff_l_nil : forall (l : list nat),
  (num_occ_diff_l l 0) = 0.
Proof.
  induction l.
    simpl; reflexivity.

    destruct a.
      reflexivity.

      simpl.
      rewrite IHl.
      case (is_in_l l 0); reflexivity.
Qed.

Lemma num_occ_diff_nil : forall (alpha : SecOrder) (P : predicate),
  (num_occ_diff alpha P 0) = 0.
Proof.
  intros.
  unfold num_occ_diff.
  apply num_occ_diff_l_nil.
Qed.


(* ------------------------------------------------------------- *)


Lemma num_occ_relatSO : forall (x y : FOvariable) (Q : predicate),
   num_occ (relatSO x y) Q = 0.
Proof.
  intros.
  destruct x; destruct y; destruct Q.
  unfold num_occ.
  unfold indicies.
  simpl.
  reflexivity.
Qed.


Lemma num_occ_eqFO : forall (x y : FOvariable) (Q : predicate),
   num_occ (eqFO x y) Q = 0.
Proof.
  intros.
  destruct x; destruct y; destruct Q.
  unfold num_occ.
  unfold indicies.
  simpl.
  reflexivity.
Qed.



Lemma num_occ_negSO : forall (alpha : SecOrder) (P : predicate),
  num_occ (negSO alpha) P = num_occ alpha P.
Proof.
   intros.
  unfold num_occ.
  unfold indicies.
  simpl.
  reflexivity.
Qed.

Lemma num_occ_allFO : forall (alpha : SecOrder) (x : FOvariable)
                             (P : predicate),
  num_occ (allFO x alpha) P = num_occ alpha P.
Proof.
   intros.
  unfold num_occ.
  unfold indicies.
  simpl.
  reflexivity.
Qed.

Lemma num_occ_exFO : forall (alpha : SecOrder) (x : FOvariable)
                             (P : predicate),
  num_occ (exFO x alpha) P = num_occ alpha P.
Proof.
   intros.
  unfold num_occ.
  unfold indicies.
  simpl.
  destruct x.
  reflexivity.
Qed.

Lemma num_occ_conjSO : forall (alpha1 alpha2 : SecOrder)
                             (P : predicate),
  num_occ (conjSO alpha1 alpha2) P = num_occ alpha1 P + num_occ alpha2 P.
Proof.
   intros.
  unfold num_occ.
  unfold indicies.
  simpl.
  rewrite app_length.
  rewrite list_map_length.
  rewrite list_map_length.
  rewrite list_map_length.
  rewrite indicies_l_rev_app.
  rewrite app_length.
  rewrite list_map_length.
  reflexivity.
Qed.

Lemma num_occ_disjSO : forall (alpha1 alpha2 : SecOrder)
                             (P : predicate),
  num_occ (disjSO alpha1 alpha2) P = num_occ alpha1 P + num_occ alpha2 P.
Proof.
   intros.
  unfold num_occ.
  unfold indicies.
  simpl.
  rewrite app_length.
  rewrite list_map_length.
  rewrite list_map_length.
  rewrite list_map_length.
  rewrite indicies_l_rev_app.
  rewrite app_length.
  rewrite list_map_length.
  reflexivity.
Qed.

Lemma num_occ_implSO : forall (alpha1 alpha2 : SecOrder)
                             (P : predicate),
  num_occ (implSO alpha1 alpha2) P = num_occ alpha1 P + num_occ alpha2 P.
Proof.
   intros.
  unfold num_occ.
  unfold indicies.
  simpl.
  rewrite app_length.
  rewrite list_map_length.
  rewrite list_map_length.
  rewrite list_map_length.
  rewrite indicies_l_rev_app.
  rewrite app_length.
  rewrite list_map_length.
  reflexivity.
Qed.

Lemma num_occ_preds_in : forall (alpha : SecOrder) (P : predicate),
  Nat.leb (num_occ alpha P) (length (preds_in alpha)) = true.
Proof.
  intros.
  induction alpha;
    try destruct p as [Qm]; try destruct f as [xn];
    try destruct P as [Pn]; try destruct f0 as [xm];
    try (unfold num_occ in *; unfold indicies in *; simpl);
    try reflexivity; try  rewrite list_map_length in *;
    try rewrite list_map_length in IHalpha;
    try rewrite list_map_length in IHalpha1;
    try rewrite list_map_length in IHalpha2;
    try (case (beq_nat Qm Pn); simpl; reflexivity);
    try assumption;
    try (rewrite indicies_l_rev_app;
    do 2 rewrite app_length;
    rewrite list_map_length;
    apply leb_plus_gen; assumption);
    (case_eq (beq_nat Qm Pn); intros Hbeq; [simpl | apply leb_suc_r];
      assumption).
Qed.


Lemma  num_occ_ind_l_rev : forall (alpha : SecOrder) (P : predicate),
  num_occ alpha P = length (indicies_l_rev (preds_in alpha) P).
Proof.
  intros alpha P.
  unfold num_occ.
  unfold indicies.
  rewrite list_map_length.
  reflexivity.
Qed.


Lemma num_occ_rep_pred : forall alpha cond P x,
is_unary_predless cond = true ->
num_occ (replace_pred alpha P x cond) P = 0.
Proof.
  intros alpha cond P x Hcond.
  unfold num_occ.
  rewrite length_ind.
  induction alpha;
    try destruct p as [Pn]; try destruct P as [Qm];
    try destruct f; try destruct f0;
    simpl in *; try reflexivity;
    try assumption;
    try (rewrite indicies_l_rev_app; rewrite app_length;
    rewrite list_map_length;
    rewrite IHalpha1; rewrite IHalpha2;
    reflexivity).
    case_eq (beq_nat Qm Pn); intros Hbeq.
      rewrite preds_in_rep_FOv.
      rewrite un_predless_preds_in; try assumption.
      reflexivity.

      simpl.
      rewrite beq_nat_comm.
      rewrite Hbeq.
      reflexivity.

    case_eq (beq_nat Qm Pn); intros Hbeq.
      assumption.

      simpl.
      rewrite beq_nat_comm.
      rewrite Hbeq.
      assumption.

    case_eq (beq_nat Qm Pn); intros Hbeq.
      assumption.

      simpl.
      rewrite beq_nat_comm.
      rewrite Hbeq.
      assumption.
Qed.

Lemma num_occ_rep_pred_0 : forall (alpha cond : SecOrder) (P Q : predicate)
                                  (x : FOvariable),
is_unary_predless cond = true ->
num_occ alpha P = 0 ->
num_occ (replace_pred alpha Q x cond) P = 0.
Proof.
  induction alpha; intros cond P Q x Hcond Hnum;
  unfold num_occ in *; rewrite length_ind in *;
  simpl in *;
    try destruct Q as [Qm]; try destruct p as [Pn];
    try destruct f as [xn]; try destruct f0; try destruct P as [Rn];
    try destruct x as [ym];
    try reflexivity;
    try (simpl in *;
    specialize (IHalpha cond (Pred Rn) (Pred Qm) (Var ym) Hcond);
    do 2 rewrite length_ind in *;
    apply IHalpha; assumption);

    try (simpl;
    rewrite indicies_l_rev_app in *;
    rewrite app_length in *;
    rewrite list_map_length;
    rewrite list_map_length in Hnum;
    specialize (IHalpha1 cond (Pred Rn) (Pred Qm) (Var ym) Hcond);
    specialize (IHalpha2 cond (Pred Rn) (Pred Qm) (Var ym) Hcond);
    do 2 rewrite length_ind in *;
    rewrite IHalpha1; [rewrite IHalpha2 | ];
      [reflexivity |
      rewrite arith_plus_comm in Hnum;
      apply eq_nat_zero in Hnum; assumption |
      apply eq_nat_zero in Hnum; assumption]);

   try (    simpl in *;
    specialize (IHalpha cond (Pred Rn) (Pred Qm) (Var ym) Hcond);
    do 2 rewrite length_ind in IHalpha;
    case_eq (beq_nat Pn Rn); intros Hbeq2; rewrite Hbeq2 in *;
      [simpl in *; discriminate |];

      case (beq_nat Qm Pn);
        [|simpl; rewrite Hbeq2];
        apply IHalpha; assumption).

    simpl in *; 
    case_eq (beq_nat Qm Pn); intros Hbeq.
      apply rep_FOv_is_unary_predless with (x := (Var ym)) (y := (Var xn)) in Hcond.
      apply un_predless_preds_in in Hcond.
      rewrite Hcond.
      reflexivity.

      simpl.
      case_eq (beq_nat Pn Rn); intros Hbeq2; rewrite Hbeq2 in *.
        simpl in *; discriminate.

        reflexivity.
Qed.

Lemma num_occ_rep_pred__l_0 : forall (alpha : SecOrder) l l1 l2 P Q x cond,
is_unary_predless_l l2 = true ->
is_unary_predless cond = true ->
num_occ (replace_pred_l alpha l l1 l2) P = 0 ->
num_occ (replace_pred (replace_pred_l alpha l l1 l2) Q x cond) P = 0.
Proof.
  intros alpha l l1 l2 P Q x cond Hun1 Hun2 Hnum.
  apply num_occ_rep_pred_0; assumption.
Qed.


Lemma num_occ_rep_pred2 : forall (alpha cond : SecOrder) 
                                 (P Q : predicate) (x : FOvariable),
is_unary_predless cond = true ->
match P, Q with
| Pred Pn, Pred Qm =>
beq_nat Pn Qm = false
end ->
num_occ (replace_pred alpha P x cond) Q =
num_occ alpha Q.
Proof.
  intros alpha cond P Q x Hcond Hbeq.
  destruct P as [Pn]; destruct Q as [Qm].
  unfold num_occ.
  do 2 rewrite length_ind.
  induction alpha;
    try destruct p as [Rn]; try destruct f;
    try destruct f0;
    try reflexivity;
    try (    simpl; assumption);
    try (simpl; do 2 rewrite indicies_l_rev_app;
    do 2 rewrite app_length;
    do 2 rewrite list_map_length;
    rewrite IHalpha1;
    rewrite IHalpha2;
    reflexivity);

    simpl;
    case_eq (beq_nat Rn Qm); intros Hbeq2;
      case_eq (beq_nat Pn Rn); intros Hbeq3.
        rewrite <- (beq_nat_true _ _ Hbeq2) in *;
        rewrite <- (beq_nat_true _ _ Hbeq3) in Hbeq;
        rewrite <- beq_nat_refl in Hbeq;
        discriminate.

        simpl; rewrite Hbeq2; reflexivity.

        simpl.
        apply rep_FOv_is_unary_predless with (x := x)
              (y := (Var n)) in Hcond.
        apply un_predless_preds_in in Hcond.
        rewrite Hcond.
        reflexivity.

        simpl.
        rewrite Hbeq2.
        reflexivity.
(* allSO *)
        rewrite <- (beq_nat_true _ _ Hbeq2) in *;
        rewrite <- (beq_nat_true _ _ Hbeq3) in Hbeq;
        rewrite <- beq_nat_refl in Hbeq;
        discriminate.

        simpl; rewrite Hbeq2; simpl;  rewrite IHalpha ; reflexivity.

        assumption.

        simpl; rewrite Hbeq2; assumption.
(* exSO *)
        rewrite <- (beq_nat_true _ _ Hbeq2) in *;
        rewrite <- (beq_nat_true _ _ Hbeq3) in Hbeq;
        rewrite <- beq_nat_refl in Hbeq;
        discriminate.

        simpl; rewrite Hbeq2; simpl;  rewrite IHalpha ; reflexivity.

        assumption.

        simpl; rewrite Hbeq2; assumption.
Qed.

