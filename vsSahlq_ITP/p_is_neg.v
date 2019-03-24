Require Export is_neg pv_in at_pv occ_in_modal pv_in_modal.

(* All occurrences of p in phi are negative. *)

Definition p_is_neg (phi : Modal) (p : propvar) : Prop :=
  pv_in_modal phi p /\
  (forall i : nat, occ_in_modal phi i -> p = at_pv (pv_in phi) i -> is_neg phi i).