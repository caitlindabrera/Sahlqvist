Require Export pv_in occ_in_modal.
Require Import Compare_dec.

Fixpoint is_pos_pre (phi : Modal) (i : nat) : bool :=
  match phi with
  | atom p => EqNat.beq_nat 1 i
  | mneg psi => negb (is_pos_pre psi i)
  | mconj psi1 psi2 => if le_dec i (length (pv_in psi1)) then is_pos_pre psi1 i
                          else is_pos_pre psi2 (i-(length (pv_in psi1)))
  | mdisj psi1 psi2 => if le_dec i (length (pv_in psi1)) then is_pos_pre psi1 i
                          else is_pos_pre psi2 (i-(length (pv_in psi1)))
  | mimpl psi1 psi2 => if le_dec i (length (pv_in psi1)) then negb (is_pos_pre psi1 i)
                          else is_pos_pre psi2 (i-(length (pv_in psi1)))
  | box psi => is_pos_pre psi i
  | diam psi => is_pos_pre psi i
  end.

Inductive is_pos phi i : Prop :=
| occ_pos : occ_in_modal phi i -> is_pos_pre phi i = true -> is_pos phi i.