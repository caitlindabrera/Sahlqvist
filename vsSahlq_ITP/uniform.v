Require Import p_is_pos p_is_neg.

Definition uniform_pos (phi : Modal) : Prop :=
forall p, pv_in_modal phi p -> p_is_pos phi p.

Definition uniform_neg (phi : Modal) : Prop :=
forall p, pv_in_modal phi p -> p_is_neg phi p.

Definition uniform (phi : Modal) : Prop :=
forall p, pv_in_modal phi p -> p_is_pos phi p \/ p_is_neg phi p.

(*
Inductive uniform_pos (phi : Modal) : Prop :=
  | uni_pos_y : (forall p, pv_in_modal phi p -> p_is_pos phi p) -> uniform_pos phi.

Inductive uniform_neg (phi : Modal) : Prop :=
  | uni_neg_y : (forall p, pv_in_modal phi p -> p_is_neg phi p) -> uniform_neg phi.

Inductive uniform (phi : Modal) : Prop :=
| uni_y : (forall p, pv_in_modal phi p -> p_is_pos phi p \/ p_is_neg phi p) ->
          uniform phi.
*)
