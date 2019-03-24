Require Export is_pos pv_in at_pv occ_in_modal pv_in_modal.

(* All occurrences of p in phi are positive. *)

Definition p_is_pos (phi : Modal) (p : propvar) : Prop :=
  pv_in_modal phi p /\
  (forall i : nat, occ_in_modal phi i -> p = at_pv (pv_in phi) i -> is_pos phi i).


(*
Inductive p_is_pos (phi : Modal) (p : propvar) : Prop :=
  | p_is_pos_y :   pv_in_modal phi p ->
    (forall i : nat, occ_in_modal phi i ->
     p = at_pv (pv_in phi) i -> is_pos phi i) -> p_is_pos phi p.
*)