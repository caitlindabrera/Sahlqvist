Require Import base_mods occ_in_SO preds_in.

Ltac occ_in_SO_fill :=
repeat match goal with
| [ H : occ_in_SO ?alpha ?i |- context[occ_in_SO_dec ?alpha ?i ] ] => 
  rewrite (occ_in_SO_dec_l _ _ _ _  H) in *
| [ H : ~ occ_in_SO ?alpha ?i |- context[occ_in_SO_dec ?alpha ?i] ] =>
  rewrite (occ_in_SO_dec_r _ _ _ _ H) in * end.
