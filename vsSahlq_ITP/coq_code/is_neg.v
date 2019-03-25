Require Import pv_in occ_in_modal.
Require Import Compare_dec.


Fixpoint is_neg_pre (phi : Modal) (i : nat) : bool :=
  match phi with
  | atom p => false
  | mneg psi => negb (is_neg_pre psi i)
  | mconj psi1 psi2 => if le_dec i (length (pv_in psi1)) then is_neg_pre psi1 i
                          else is_neg_pre psi2 (i-(length (pv_in psi1)))
  | mdisj psi1 psi2 => if le_dec i (length (pv_in psi1)) then is_neg_pre psi1 i
                          else is_neg_pre psi2 (i-(length (pv_in psi1)))
  | mimpl psi1 psi2 => if le_dec i (length (pv_in psi1)) then negb (is_neg_pre psi1 i)
                          else is_neg_pre psi2 (i-(length (pv_in psi1)))
  | box psi => is_neg_pre psi i
  | diam psi => is_neg_pre psi i
  end.

Inductive is_neg phi i : Prop :=
  | occ_neg : occ_in_modal phi i -> is_neg_pre phi i = true -> is_neg phi i.