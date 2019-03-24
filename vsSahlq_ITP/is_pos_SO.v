Require Export low_mods.

Fixpoint is_pos_SO_pre (alpha : SecOrder) (i : nat) : bool :=
  match alpha with
    predSO _ _  => EqNat.beq_nat 1 i
  | relatSO _ _ => false
  | eqFO _ _ => false
  | allFO _ beta => is_pos_SO_pre beta i
  | negSO beta => negb (is_pos_SO_pre beta i)
  | exFO _ beta => is_pos_SO_pre beta i
  | conjSO beta1 beta2 => if le_dec i (length (preds_in beta1)) then is_pos_SO_pre beta1 i
                          else is_pos_SO_pre beta2 (i-(length (preds_in beta1)))
  | disjSO beta1 beta2 => if le_dec i (length (preds_in beta1)) then is_pos_SO_pre beta1 i
                          else is_pos_SO_pre beta2 (i-(length (preds_in beta1)))
  | implSO beta1 beta2 => if le_dec i (length (preds_in beta1)) then negb (is_pos_SO_pre beta1 i)
                          else is_pos_SO_pre beta2 (i-(length (preds_in beta1)))
  | allSO _ beta => match i with
                                     | 0 => false
                                     | S 0 => true
                                     | S j => is_pos_SO_pre beta j
                                     end
  | exSO _ beta => match i with
                                     | 0 => false
                                     | S 0 => true
                                     | S j => is_pos_SO_pre beta j
                                     end
  end.

Definition is_pos_SO alpha i : Prop :=
occ_in_SO alpha i /\ is_pos_SO_pre alpha i = true.

(*
Inductive is_pos_SO alpha i : Prop :=
| occ_pos_SO : occ_in_SO alpha i -> is_pos_SO_pre alpha i = true -> is_pos_SO alpha i.
*)
