Require Import SecOrder.
Require Import P_occurs_in_alpha.
Require Import ST_setup.
Require Import Correctness_ST.
Require Import Arith.EqNat my_bool.
Require Import List_machinery_impl My_List_Map.
Require Import Unary_Predless nList_egs Rep_Pred_FOv Indicies Identify.
Require Import pos_SO2 Num_Occ Bool my_bool Is_Pos_Rep_Pred P_occ_rep_pred.
Require Import Unary_Predless_l Num_Occ.
Require Import Uniform_Defns Monotonicity_SO Pre_Sahlqvist_Uniform_Pos P_occ_rep_pred.
Require Import my_arith__my_leb_nat List.

(* 
  Uniform_Mod_Lemmas10e
*)



Fixpoint occ_in_l (l : list predicate) (P : predicate) : bool :=
  match l with
  | nil => false
  | cons Q l' => match P, Q with
                 | Pred Pn, Pred Qm =>
                    if beq_nat Pn Qm then true else occ_in_l l' P
                 end
  end.

Fixpoint rem_dups (l : list predicate) : list predicate :=
  match l with
  | nil => nil
  | cons P l' => if occ_in_l l' P then rem_dups l' else cons P (rem_dups l')
  end.



Fixpoint num_occ_l2_pre (alpha : SecOrder) (l : list predicate) : nat :=
  match l with
  | nil => 0
  | cons P l' => num_occ alpha P + num_occ_l2_pre alpha l'
  end.

Definition num_occ_l2 (alpha : SecOrder) (l : list predicate) := 
    num_occ_l2_pre alpha (rem_dups l).

Lemma num_occ_l2_0 : forall (alpha : SecOrder),
  num_occ_l2 alpha nil = 0.
Proof.
  induction alpha; reflexivity.
Qed.




Lemma num_occ_l2_cons_nil : forall (alpha : SecOrder) (P : predicate),
  num_occ_l2 alpha (cons P nil) = if occ_in_l nil P then num_occ_l2 alpha nil 
                                                else num_occ alpha P + num_occ_l2 alpha nil.
Proof.
  intros alpha P.
  unfold num_occ_l2.
  simpl.
  reflexivity.
Qed.


Lemma num_occ_l2_cons_same : forall (alpha : SecOrder) (P : predicate) (l : list predicate),
  num_occ_l2 alpha (cons P (cons P l)) = num_occ_l2 alpha (cons P l).
Proof.
  intros alpha P l.
  unfold num_occ_l2.
  simpl.
  destruct P as [Pn].
  rewrite <- beq_nat_refl.
  reflexivity.
Qed.

Lemma num_occ_l2_cons : forall (alpha : SecOrder) (l : list predicate) (P : predicate),
  num_occ_l2 alpha (cons P l) = if occ_in_l l P then num_occ_l2 alpha l 
                                                else num_occ alpha P + num_occ_l2 alpha l.
Proof.
  intros alpha l.
  induction l; intros P.
    apply num_occ_l2_cons_nil.

    destruct P as [Pn]; destruct a as [Qm].
    simpl.
    case_eq (beq_nat Pn Qm); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq).
      rewrite num_occ_l2_cons_same.
      reflexivity.

      unfold num_occ_l2.
      simpl in *.
      rewrite Hbeq.
      specialize (IHl (Pred Pn)).
      case_eq (occ_in_l l (Pred Pn)); intros Hocc; rewrite Hocc in *.
        reflexivity.

        simpl.
        reflexivity.
Qed.


Lemma num_occ__in_l_t : forall l alpha a l1 l2,
is_unary_predless_l (nlist_list _ l2) = true ->
occ_in_l l a = true ->
(num_occ (replace_pred_l alpha l (nlist_list (length l) l1) (nlist_list (length l) l2)) a) = 0.
Proof.
  intros l.
  induction l; intros  alpha P l1 l2 Hun Hocc.
    simpl in *.
    discriminate.

    destruct (nlist_cons2 _ l1) as [x [l1' H1]].
    destruct (nlist_cons2 _ l2) as [beta [l2' H2]].
    rewrite H1 in *.
    rewrite H2 in *.
    destruct P as [Pn]; destruct a as [Qm].
    
    simpl in *.
    case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *.
      rewrite (beq_nat_true _ _ Hbeq).
      apply num_occ_rep_pred.
      case_eq (is_unary_predless beta); intros H.
        reflexivity.
        rewrite H in *; discriminate.

      specialize (IHl alpha (Pred Pn) l1' l2').
      case_eq (is_unary_predless beta); intros Hbeta;
      rewrite Hbeta in *; try discriminate.
      specialize (IHl Hun Hocc).
      apply num_occ_rep_pred__l_0; assumption.
Qed.


Lemma num_occ__in_l_f : forall alpha l a l1' l2',
is_unary_predless_l (nlist_list _ l2') = true ->
occ_in_l l a = false ->
num_occ (replace_pred_l alpha l (nlist_list (length l) l1') 
    (nlist_list (length l) l2')) a = num_occ alpha a.
Proof.
  intros alpha l.
  induction l; intros P l1 l2 Hun Hocc.
    simpl in *.
    reflexivity.

    destruct (nlist_cons2 _ l1) as [x [l1' H1]].
    destruct (nlist_cons2 _ l2) as [beta [l2' H2]].
    rewrite H1 in *.
    rewrite H2 in *.
    destruct P as [Pn]; destruct a as [Qm].
    simpl in *.
    case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *.
      discriminate.

      specialize (IHl (Pred Pn) l1' l2').
      case_eq (is_unary_predless beta); intros Hbeta;
      rewrite Hbeta in *; try discriminate.
      specialize (IHl Hun Hocc).
      rewrite beq_nat_comm in Hbeq.
      rewrite num_occ_rep_pred2; try assumption.
Qed.


Lemma num_occ_l2_allFO: forall (alpha : SecOrder) (x : FOvariable) (l : list predicate),
  num_occ_l2 (allFO x alpha) l = num_occ_l2 alpha l.
Proof.
  intros.
  unfold num_occ_l2.
  induction l.
    reflexivity.

    simpl.
    case_eq (occ_in_l l a); intros Hocc.
      assumption.

      simpl.
      rewrite num_occ_allFO.
      rewrite IHl; reflexivity.
Qed.

Lemma num_occ_l2_exFO: forall (alpha : SecOrder) (x : FOvariable) (l : list predicate),
  num_occ_l2 (exFO x alpha) l = num_occ_l2 alpha l.
Proof.
  intros.
  unfold num_occ_l2.
  induction l.
    reflexivity.

    simpl.
    case_eq (occ_in_l l a); intros Hocc.
      assumption.

      simpl.
      rewrite num_occ_exFO.
      rewrite IHl; reflexivity.
Qed.

Lemma num_occ_l2_negSO: forall (alpha : SecOrder) (l : list predicate),
  num_occ_l2 (negSO alpha) l = num_occ_l2 alpha l.
Proof.
  intros.
  unfold num_occ_l2.
  induction l.
    reflexivity.

    simpl.
    case_eq (occ_in_l l a); intros Hocc.
      assumption.

      simpl.
      rewrite num_occ_negSO.
      rewrite IHl; reflexivity.
Qed.


Lemma num_occ_l2_conjSO : forall (alpha1 alpha2 : SecOrder) (l : list predicate),
  num_occ_l2 (conjSO alpha1 alpha2) l = num_occ_l2 alpha1 l + num_occ_l2 alpha2 l.
Proof.
  intros.
  induction l.
    unfold num_occ_l2.
    reflexivity.

    do 3 rewrite num_occ_l2_cons.
    case_eq (occ_in_l l a); intros Hocc.
      assumption.

      rewrite num_occ_conjSO.
      rewrite IHl.
      rewrite <- arith_plus_assoc.
      rewrite arith_plus_assoc with (a := num_occ alpha1 a).
      rewrite arith_plus_comm with (a := num_occ alpha2 a).
      rewrite <- arith_plus_assoc.
      rewrite arith_plus_assoc with
            (a := num_occ alpha1 a + num_occ_l2 alpha1 l ).
      reflexivity.
Qed.

Lemma num_occ_l2_disjSO : forall (alpha1 alpha2 : SecOrder) (l : list predicate),
  num_occ_l2 (disjSO alpha1 alpha2) l = num_occ_l2 alpha1 l + num_occ_l2 alpha2 l.
Proof.
  intros.
  induction l.
    unfold num_occ_l2.
    reflexivity.

    do 3 rewrite num_occ_l2_cons.
    case_eq (occ_in_l l a); intros Hocc.
      assumption.

      rewrite num_occ_disjSO.
      rewrite IHl.
      rewrite <- arith_plus_assoc.
      rewrite arith_plus_assoc with (a := num_occ alpha1 a).
      rewrite arith_plus_comm with (a := num_occ alpha2 a).
      rewrite <- arith_plus_assoc.
      rewrite arith_plus_assoc with
            (a := num_occ alpha1 a + num_occ_l2 alpha1 l ).
      reflexivity.
Qed.

Lemma num_occ_l2_implSO : forall (alpha1 alpha2 : SecOrder) (l : list predicate),
  num_occ_l2 (implSO alpha1 alpha2) l = num_occ_l2 alpha1 l + num_occ_l2 alpha2 l.
Proof.
  intros.
  induction l.
    unfold num_occ_l2.
    reflexivity.

    do 3 rewrite num_occ_l2_cons.
    case_eq (occ_in_l l a); intros Hocc.
      assumption.

      rewrite num_occ_implSO.
      rewrite IHl.
      rewrite <- arith_plus_assoc.
      rewrite arith_plus_assoc with (a := num_occ alpha1 a).
      rewrite arith_plus_comm with (a := num_occ alpha2 a).
      rewrite <- arith_plus_assoc.
      rewrite arith_plus_assoc with
            (a := num_occ alpha1 a + num_occ_l2 alpha1 l ).
      reflexivity.
Qed.


Lemma num_occ_l2_allSO : forall (alpha : SecOrder) (P : predicate) (l : list predicate),
  num_occ_l2 (allSO P alpha) l = if occ_in_l l P then num_occ_l2 alpha l + 1
                                                 else num_occ_l2 alpha l.
Proof.
  intros.
  induction l.
    unfold num_occ_l2.
    reflexivity.

    destruct P as [Pn]; destruct a as [Qm].
    simpl.
    do 2 rewrite num_occ_l2_cons.
    rewrite IHl.
    rewrite num_occ_allSO.
    case_eq (beq_nat Pn Qm); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq).
      case_eq (occ_in_l l (Pred Qm)); intros Hocc.
        reflexivity.

        rewrite arith_plus_comm with (b := 1).
        rewrite <- arith_plus_assoc.
        reflexivity.

      case_eq (occ_in_l l (Pred Qm)); intros Hocc.
        reflexivity.

        case_eq (occ_in_l l (Pred Pn)); intros Hocc2.
          rewrite <- arith_plus_assoc.
          reflexivity.

          reflexivity.
Qed.


Lemma num_occ_exSO : forall (alpha : SecOrder) (P Q : predicate),
  num_occ (exSO P alpha) Q = match P, Q with
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

Lemma num_occ_l2_exSO : forall (alpha : SecOrder) (P : predicate) (l : list predicate),
  num_occ_l2 (exSO P alpha) l = if occ_in_l l P then num_occ_l2 alpha l + 1
                                                 else num_occ_l2 alpha l.
Proof.
  intros.
  induction l.
    unfold num_occ_l2.
    reflexivity.

    destruct P as [Pn]; destruct a as [Qm].
    simpl.
    do 2 rewrite num_occ_l2_cons.
    rewrite IHl.
    rewrite num_occ_exSO.
    case_eq (beq_nat Pn Qm); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq).
      case_eq (occ_in_l l (Pred Qm)); intros Hocc.
        reflexivity.

        rewrite arith_plus_comm with (b := 1).
        rewrite <- arith_plus_assoc.
        reflexivity.

      case_eq (occ_in_l l (Pred Qm)); intros Hocc.
        reflexivity.

        case_eq (occ_in_l l (Pred Pn)); intros Hocc2.
          rewrite <- arith_plus_assoc.
          reflexivity.

          reflexivity.
Qed.


Lemma occ_in_l_app_f : forall (l1 l2 : list predicate) (P : predicate),
occ_in_l (app l1 l2) P = false ->
occ_in_l l1 P = false /\ occ_in_l l2 P = false.
Proof.
  induction l1; intros l2 P H.
    simpl. simpl in H.
    apply conj; [reflexivity | assumption].

    simpl in *.
    destruct P as [Pn]; destruct a as [Qm].
    case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *.
      discriminate.

      apply IHl1; assumption.
Qed.


Lemma occ_in_l_num_occ_f : forall (alpha : SecOrder) (P : predicate),
occ_in_l (preds_in alpha) P = false -> num_occ alpha P = 0.
Proof.
  intros alpha P Hocc.
  unfold num_occ.
  rewrite length_ind.
  induction alpha;
    try destruct p as [Qm]; try destruct f;
    try destruct f0; destruct P as [Pn];
    simpl in *; try reflexivity;
    try (apply IHalpha; assumption);
    try (destruct (occ_in_l_app_f _ _ _ Hocc) as [H1 H2];
    rewrite indicies_l_rev_app; rewrite app_length;
    rewrite list_map_length; rewrite IHalpha1; try assumption;
    rewrite IHalpha2; try assumption; reflexivity);
    try (rewrite beq_nat_comm;
    case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *;
      [discriminate | apply IHalpha; assumption]).
    rewrite beq_nat_comm in Hocc.
    case_eq (beq_nat Qm Pn); intros Hbeq; rewrite Hbeq in *.
      discriminate.

      reflexivity.
Qed.

Lemma num_occ_l2_app_l : forall (alpha : SecOrder) (l : list predicate),
num_occ_l2 alpha (app l (preds_in alpha)) = num_occ_l2 alpha (preds_in alpha).
Proof.
  intros alpha l.
  induction l.
    reflexivity.

    simpl.
    rewrite num_occ_l2_cons.
    case_eq (occ_in_l (app l (preds_in alpha)) a); intros Hocc.
      assumption.

      apply occ_in_l_app_f in Hocc.
      destruct Hocc as [H1 H2].
      apply occ_in_l_num_occ_f in H2.
      rewrite H2.
      simpl.
      assumption.
Qed.


Lemma num_occ_l2_cons_switch : forall (alpha : SecOrder) (P Q : predicate) (l : list predicate),
  num_occ_l2 alpha (cons P (cons Q l)) = num_occ_l2 alpha (cons Q (cons P l)).
Proof.
  intros.
  do 4 rewrite num_occ_l2_cons.
  simpl.
  destruct P as [Pn]; destruct Q as [Qm].
  case_eq (beq_nat Pn Qm); intros Hbeq.
    rewrite (beq_nat_true _ _ Hbeq).
    rewrite <- beq_nat_refl.
    reflexivity.

    rewrite beq_nat_comm.
    rewrite Hbeq.

    case_eq (occ_in_l l (Pred Pn)); intros Hocc.
      reflexivity.

      case_eq (occ_in_l l (Pred Qm)); intros Hocc2.
        reflexivity.

        do 2 rewrite <- arith_plus_assoc.
        rewrite arith_plus_comm with (a := num_occ alpha (Pred Pn)).
        reflexivity.
Qed.


Lemma occ_in_l_app_cons : forall (l1 l2 : list predicate)
                                   (P Q: predicate),
occ_in_l (app l1 (cons P l2)) Q = occ_in_l (cons P (app l1 l2)) Q.
Proof.
  intros.
  induction l1.
    reflexivity.

    simpl.
    destruct Q as [Qm]; destruct a as [Pn]; destruct P as [Rn].
    simpl in *.
    case_eq (beq_nat Qm Rn); intros Hbeq; rewrite Hbeq in *.
      rewrite IHl1.
      case (beq_nat Qm Pn); reflexivity.

      rewrite IHl1.
      reflexivity.
Qed.


Lemma num_occ_l2_app_cons : forall (alpha : SecOrder) (l1 l2 : list predicate)
                                   (P : predicate),
num_occ_l2 alpha (app l1 (cons P l2)) = num_occ_l2 alpha (cons P (app l1 l2)).
Proof.
  intros.
  induction l1.
    reflexivity.

    simpl.
    rewrite num_occ_l2_cons_switch.
    rewrite num_occ_l2_cons.
    rewrite num_occ_l2_cons.
    rewrite occ_in_l_app_cons.
    rewrite IHl1.
    reflexivity.
Qed.

Lemma num_occ_l2_app_r : forall (alpha : SecOrder) (l : list predicate),
num_occ_l2 alpha (app (preds_in alpha) l) = num_occ_l2 alpha (preds_in alpha).
Proof.
  intros.
  induction l.
    rewrite app_nil_r.
    reflexivity.

    rewrite num_occ_l2_app_cons.
    rewrite num_occ_l2_cons.
    case_eq (occ_in_l (app (preds_in alpha) l) a); intros Hocc.
      assumption.

      destruct (occ_in_l_app_f _ _ _ Hocc) as [H1 H2].
      apply occ_in_l_num_occ_f in H1.
      rewrite H1.
      simpl; assumption.
Qed.

Lemma num_occ_l2_preds_in : forall alpha : SecOrder,
  num_occ_l2 alpha (preds_in alpha) = length (preds_in alpha).
Proof.
  intros alpha.

  induction alpha;
    try destruct p; try destruct f; try destruct f0;
    simpl; unfold num_occ; simpl;
    try reflexivity; simpl.
        unfold num_occ_l2.
      simpl.
      unfold num_occ.
      rewrite length_ind.
      simpl.
      rewrite <- beq_nat_refl.
      reflexivity.
      unfold indicies.

      rewrite num_occ_l2_allFO.
      assumption.

      rewrite num_occ_l2_exFO.
      assumption.

      rewrite num_occ_l2_negSO.
      assumption.

      rewrite app_length.
      rewrite <- IHalpha1.
      rewrite <- IHalpha2.
      rewrite num_occ_l2_conjSO.
      rewrite num_occ_l2_app_l.
      rewrite num_occ_l2_app_r.
      reflexivity.

      rewrite app_length.
      rewrite <- IHalpha1.
      rewrite <- IHalpha2.
      rewrite num_occ_l2_disjSO.
      rewrite num_occ_l2_app_l.
      rewrite num_occ_l2_app_r.
      reflexivity.
      
      rewrite app_length.
      rewrite <- IHalpha1.
      rewrite <- IHalpha2.
      rewrite num_occ_l2_implSO.
      rewrite num_occ_l2_app_l.
      rewrite num_occ_l2_app_r.
      reflexivity.

      rewrite num_occ_l2_allSO.
      simpl.
      rewrite <- beq_nat_refl.
      rewrite num_occ_l2_cons.
      rewrite IHalpha.
      case_eq (occ_in_l (preds_in alpha) (Pred n)); intros Hocc.
        rewrite <- one_suc; reflexivity.

        rewrite <- one_suc.
        apply occ_in_l_num_occ_f in Hocc.
        rewrite Hocc.
        reflexivity.

      rewrite num_occ_l2_exSO.
      simpl.
      rewrite <- beq_nat_refl.
      rewrite num_occ_l2_cons.
      rewrite IHalpha.
      case_eq (occ_in_l (preds_in alpha) (Pred n)); intros Hocc.
        rewrite <- one_suc; reflexivity.

        rewrite <- one_suc.
        apply occ_in_l_num_occ_f in Hocc.
        rewrite Hocc.
        reflexivity.
Qed.

