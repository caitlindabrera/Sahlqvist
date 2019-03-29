Require Import SecOrder.
Require Import P_occurs_in_alpha.
Require Import ST_setup.
Require Import Correctness_ST.
Require Import Arith.EqNat.
Require Import List_machinery_impl.
Require Import Unary_Predless nList_egs Rep_Pred_FOv my_bool my_arith__my_leb_nat.
(* 
  Uniform_Mod_Lemmas8a
*)

(* ---------------------------------------------------------  *)


Lemma P_occ_rep_pred : forall (alpha cond : SecOrder) (x : FOvariable)
                              (P P2 : predicate),
  is_unary_predless cond = true ->
    P_occurs_in_alpha (replace_pred alpha P x cond) P2 = true ->
      P_occurs_in_alpha alpha P2 = true.
Proof.
  intros alpha cond x P P2 Hunary HPocc.
  unfold P_occurs_in_alpha in *.
  induction alpha;
    try destruct f as [x1];
    try destruct P as [Pn];
    try destruct P2 as [Pm];
    try destruct p as [Qm];
    try destruct f0 as [x2];
(*    destruct p as [Qm]; destruct f; destruct P as [Pn]; destruct P2 as [Pm]. *)
    try (case_eq (beq_nat Pn Qm); intros Hbeq1; simpl in *; rewrite Hbeq1 in *;
         [rewrite preds_in_rep_FOv in HPocc; 
         rewrite un_predless_preds_in in HPocc;
         simpl in * | ]; try assumption ; discriminate);
    try (simpl in *; discriminate);
    try (simpl in *; apply IHalpha; assumption);
    try (simpl in HPocc;
    apply P_occurs_in_l_app in HPocc;
    simpl; apply P_occurs_in_l_app;
    destruct HPocc as [Hl | Hr]; [left; apply IHalpha1 | right ; apply IHalpha2];
      assumption);
    try (simpl in *;
    case_eq (beq_nat Pm Qm); intros Hbeq; try reflexivity;
      apply IHalpha;
      case_eq (beq_nat Pn Qm); intros Hbeq2; rewrite Hbeq2 in *;
        [ | simpl in HPocc ; rewrite Hbeq in *]; assumption).
Qed.


Lemma P_occ_in_alpha_rep_pred_f : forall (alpha cond : SecOrder) (x : FOvariable)
                                    (Q : predicate),
  is_unary_predless cond = true ->
    P_occurs_in_alpha (replace_pred alpha Q x cond) Q = false.
Proof.
  intros alpha cond x Q Hcond.
  induction alpha;
    try destruct p as [Pn]; try destruct f;
    try destruct Q as [Qm]; try destruct f0;
    [ | rewrite rep_pred_relatSO | rewrite rep_pred_eqFO |
      rewrite rep_pred_allFO | rewrite rep_pred_exFO |
      rewrite rep_pred_negSO | rewrite rep_pred_conjSO |
      rewrite rep_pred_disjSO | rewrite rep_pred_implSO |
      rewrite rep_pred_allSO | rewrite rep_pred_exSO ];
    try (unfold P_occurs_in_alpha; simpl; 
        try reflexivity; try assumption);
    try (apply (contrapos_bool_or _ _ _ 
                  (P_occurs_in_alpha_conjSO _ _ _));
        apply conj; assumption).

    unfold P_occurs_in_alpha; simpl.
    case_eq (beq_nat Qm Pn); intros Hbeq.
      rewrite preds_in_rep_FOv.
      rewrite un_predless_preds_in.
        reflexivity.
        assumption.

      simpl.
      rewrite Hbeq; reflexivity.

    case_eq (beq_nat Pn Qm); intros Hbeq;
      simpl; unfold P_occurs_in_alpha in *.
      rewrite (beq_nat_true _ _ Hbeq).
      assumption.

      rewrite beq_nat_comm.
      rewrite Hbeq.
      assumption.

    case_eq (beq_nat Pn Qm); intros Hbeq;
      simpl; unfold P_occurs_in_alpha in *.
      rewrite (beq_nat_true _ _ Hbeq).
      assumption.

      rewrite beq_nat_comm.
      rewrite Hbeq.
      assumption.
Qed.
