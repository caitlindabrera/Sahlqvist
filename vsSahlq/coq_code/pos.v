Require Import p_is_pos p_is_neg.

Definition pos (ϕ : Modal) : Prop :=
forall p, pv_in_modal ϕ p -> p_is_pos ϕ p.

Definition neg (ϕ : Modal) : Prop :=
forall p, pv_in_modal ϕ p -> p_is_neg ϕ p.

Definition uniform (ϕ : Modal) : Prop :=
forall p, pv_in_modal ϕ p -> p_is_pos ϕ p \/ p_is_neg ϕ p.