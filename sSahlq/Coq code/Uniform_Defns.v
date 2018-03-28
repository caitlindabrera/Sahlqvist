Require Import Modal.
Require Import SecOrder.
Require Import p_is_pos.
Require Import p_occurs_in.
Require Import P_occurs_in_alpha.
Require Import ST_setup.
Require Import Correctness_ST.
Require Import Arith.EqNat.
Require Import List_machinery_impl.

(* Uniform_Mod_Defns *)

(* ---------------------------------------------------------  *)


Definition uniform_pos (phi : Modal) : Prop :=
  forall (p : propvar), p_occurs_in_phi phi p = true ->
    p_is_pos phi p.

Definition uniform_neg (phi : Modal) : Prop :=
  forall (p : propvar), p_occurs_in_phi phi p = true ->
    p_is_neg phi p.

Definition uniform (phi : Modal) : Prop :=
  forall (p : propvar), p_occurs_in_phi phi p = true ->
    p_is_pos phi p \/ p_is_neg phi p.


(*
Definition p_uniform_pos (phi : Modal) (p : propvar) : Prop :=
  (p_is_pos phi p /\ ~ p_is_neg phi p).

Definition p_uniform_neg (phi : Modal) (p : propvar) : Prop :=
  (p_is_pos phi p /\ ~ p_is_neg phi p).

Definition p_uniform (phi : Modal) (p : propvar) : Prop :=
  p_uniform_pos phi p \/ p_uniform_neg phi p.

(* I don't really care about these, I guess, since for uniform formulas
   we're okay with having a mixture of pos only and neg only. *)

Definition uniform_pos (phi : Modal) : Prop :=
  forall (p: propvar), p_occurs_in_phi phi p = true -> 
    p_uniform_pos phi p.

Definition uniform_neg (phi : Modal) : Prop :=
  forall (p: propvar), p_occurs_in_phi phi p = true -> 
    p_uniform_neg phi p.

Definition uniform (phi : Modal) : Prop :=
  forall (p: propvar), p_occurs_in_phi phi p = true -> 
    p_uniform phi p.
*)
(* ---------------------------------------------------------  *)