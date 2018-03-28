Require Import SecOrder.
Require Import P_occurs_in_alpha.
Require Import ST_setup.
Require Import Correctness_ST.
Require Import Arith.EqNat my_bool My_Prop.
Require Import List_machinery_impl My_List_Map.
Require Import Unary_Predless nList_egs Rep_Pred_FOv Indicies Identify.
Require Import pos_SO2 Num_Occ Bool my_bool Is_Pos_Rep_Pred P_occ_rep_pred.

(* 
  Uniform_Mod_Lemmas10d
*)

Lemma uni_pos_rep_pred : forall (alpha : SecOrder) (P : predicate)
                                (cond : SecOrder) (x : FOvariable),
  is_unary_predless cond = true ->
    uniform_pos_SO alpha ->
      uniform_pos_SO (replace_pred alpha P x cond).
Proof.
  intros alpha P cond x Hunary Huni.
  intros P2 HPocc.
  apply P_is_pos_rep_pred; try assumption.
  unfold uniform_pos_SO in Huni.
  apply Huni.
  apply P_occ_rep_pred in HPocc;
      assumption.
Qed.



Lemma rep_pred_false_pa_f : forall (alpha : SecOrder)  (W : Set) (Iv : FOvariable -> W)
                    (Ip : predicate -> W -> Prop)
                    (Ir : W -> W -> Prop)
                    (P : predicate),
  SOQFree alpha = true ->
  SOturnst W Iv Ip Ir (replace_pred alpha P (Var 1)
                          (negSO (eqFO (Var 1) (Var 1)))) <->
  SOturnst W Iv (alt_Ip Ip pa_f P) Ir alpha.
Proof.
  induction alpha; intros W Iv Ip Ir P noSO;
    try destruct P as [Pn]; try destruct p as [Qm];
    try destruct f; try destruct f0.

    simpl; unfold pa_f.
    case_eq (beq_nat Pn Qm); intros Hbeq.
      simpl; split; intros H.
        unfold not in *;  
        specialize (H (eq_refl _)).
        contradiction.

        contradiction.
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