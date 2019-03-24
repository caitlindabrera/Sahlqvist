Require Export low_mods.
Require Import Rel.

Ltac rem_preds_in_rel :=
repeat match goal with
| [H : REL ?rel = true |- context[preds_in ?rel] ] => rewrite (preds_in_rel rel H) in *
| [H : REL ?rel = true , H2 : context[preds_in ?rel] |- _ ] => rewrite (preds_in_rel rel H) in *
end.