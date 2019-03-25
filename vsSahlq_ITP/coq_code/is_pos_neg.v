Require Import Modal.
Require Import occ_in_phi.
Require Import Bool.
Require Import PeanoNat Nat Compare_dec.

(* is_pos *)

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

(* ----------------------------------------------------------------- *)

(* is_neg *)

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