Require Export base_mods SO_syntax.
Require Import Pred_in_SO.

Inductive lPred_in_SO (alpha : SecOrder) : list predicate -> Prop :=
| lPred_nil : lPred_in_SO alpha nil
| lPred_cons : forall P lP, Pred_in_SO alpha P -> lPred_in_SO alpha lP ->
                            lPred_in_SO alpha (P :: lP).