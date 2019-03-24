Require Export base_mods preds_in Unary_Predless.
Require Import nlist_syn_eg.

Fixpoint FO_frame_condition_l (l : list SecOrder) : bool :=
  match l with
  | nil => true
  | cons cond l' => if FO_frame_condition cond 
                       then FO_frame_condition_l l'
                       else false
  end.

Lemma FO_frame_condition_l_empty_n : forall (n : nat),
  FO_frame_condition_l (nlist_list n (nlist_empty n)) = true.
Proof. induction n; auto. Qed.

Lemma FO_frame_condition_l_full_n : forall (n : nat),
  FO_frame_condition_l (nlist_list n (nlist_full n)) = true.
Proof. induction n; auto. Qed.

Fixpoint no_free_SO_l (alpha : SecOrder) (l : list predicate) :=
  match l with
  | nil => true
  | cons P l' => if free_SO alpha P then false else no_free_SO_l alpha l'
  end.