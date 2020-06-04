Require Export low_mods.
Require Import Rep_Pred_FOv list_rel_compl.


(* Instantiates any of the predicates that occur in the consequent of alpha
  but not in the antecedent of alpha with "falsum". *)
Definition instant_cons_empty alpha : SecOrder :=
  replace_pred_l alpha (list_rel_compl (preds_in (calc_cons_SO alpha))
                                       (preds_in (calc_ante_SO alpha)))
       (nlist_list _ (nlist_var (length
          (list_rel_compl (preds_in (calc_cons_SO alpha))
                          (preds_in (calc_ante_SO alpha)))) (Var 1)))
       (nlist_list _ (nlist_empty (length
          (list_rel_compl (preds_in (calc_cons_SO alpha))
                          (preds_in (calc_ante_SO alpha)))))).

Definition instant_cons_empty' alpha beta : SecOrder :=
  replace_pred_l beta (list_rel_compl (preds_in beta)  (preds_in alpha))
          (nlist_list _ (nlist_var (length
              (list_rel_compl (preds_in beta) (preds_in alpha))) (Var 1)))
          (nlist_list _ (nlist_empty (length 
              (list_rel_compl (preds_in beta) (preds_in alpha))))).

Lemma instant_cons_empty_predSO : forall P x,
    instant_cons_empty (predSO P x) = (predSO P x).
Proof.
  unfold instant_cons_empty. intros P x.
  simpl.  destruct (in_predicate_dec P (P :: nil)) as [H | H].
  reflexivity. simpl in *. firstorder.
Qed.

Lemma instant_cons_empty_relatSO : forall x y,
  instant_cons_empty (relatSO x y) = (relatSO x y).
Proof.
  unfold instant_cons_empty.
  intros [xn] [ym].
  reflexivity.
Qed.

Lemma instant_cons_empty_eqFO : forall x y,
  instant_cons_empty (eqFO x y) = (eqFO x y).
Proof.
  unfold instant_cons_empty.
  intros [xn] [ym].
  reflexivity.
Qed. 

Lemma instant_cons_empty'_allFO : forall alpha beta y,
  instant_cons_empty' alpha (allFO y beta) = 
  allFO y (instant_cons_empty' alpha beta).
Proof.
  intros.  unfold instant_cons_empty'.
  rewrite rep_pred_l_allFO. auto.
Qed.

Lemma instant_cons_empty'_exFO : forall alpha beta y,
  instant_cons_empty' alpha (exFO y beta) = 
  exFO y (instant_cons_empty' alpha beta).
Proof.
  intros. destruct y.  unfold instant_cons_empty'.
  rewrite rep_pred_l_exFO. auto.
Qed.

Lemma instant_cons_empty'_negSO : forall alpha beta,
  instant_cons_empty' alpha (negSO beta) = 
  negSO (instant_cons_empty' alpha beta).
Proof.
  intros.  unfold instant_cons_empty'.
  rewrite rep_pred_l_negSO. auto.
Qed.