Require Export low_mods.

Fixpoint is_neg_SO_pre (alpha : SecOrder) (i : nat) : bool :=
  match alpha with
    predSO _ _  => false
  | relatSO _ _  => false
  | eqFO _ _  => false
  | allFO _  beta => is_neg_SO_pre beta i
  | negSO beta => negb (is_neg_SO_pre beta i)
  | exFO _  beta => is_neg_SO_pre beta i
  | conjSO beta1 beta2 => if le_dec i (length (preds_in beta1)) then is_neg_SO_pre beta1 i
                          else is_neg_SO_pre beta2 (i-(length (preds_in beta1)))
  | disjSO beta1 beta2 => if le_dec i (length (preds_in beta1)) then (is_neg_SO_pre beta1 i)
                          else is_neg_SO_pre beta2 (i-(length (preds_in beta1)))
  | implSO beta1 beta2 => if le_dec i (length (preds_in beta1)) then negb (is_neg_SO_pre beta1 i)
                          else is_neg_SO_pre beta2 (i-(length (preds_in beta1)))
  | allSO _ beta => match i with
                                     | 0 => false
                                     | S 0 => false
                                     | S j => is_neg_SO_pre beta j
                                     end
  | exSO _ beta => match i with
                                     | 0 => false
                                     | S 0 => false
                                     | S j => is_neg_SO_pre beta j
                                     end
  end.


Definition is_neg_SO alpha i : Prop :=
occ_in_SO alpha i /\ is_neg_SO_pre alpha i = true.
(*
Inductive is_neg_SO alpha i : Prop :=
| occ_neg_SO : occ_in_SO alpha i -> is_neg_SO_pre alpha i = true -> is_neg_SO alpha i.
*)