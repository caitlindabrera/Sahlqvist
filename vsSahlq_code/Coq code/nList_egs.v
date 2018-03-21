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


(* -------------------------------------------------------------------- *)

Fixpoint nlist_full (n : nat) : nlist n :=
  match n with
  | 0 => niln
  | S m => consn _ (eqFO (Var 1) (Var 1)) (nlist_full m)
  end.

Fixpoint nlist_empty (n : nat) : nlist n :=
  match n with
  | 0 => niln
  | S m => consn _ (negSO (eqFO (Var 1) (Var 1))) (nlist_empty m)
  end.

Fixpoint nlist_Var1 (n : nat) : nlist n :=
  match n with
  | 0 => niln
  | S m => consn _ (Var 1) (nlist_Var1 m)
  end.

Lemma nlist_Var1_length : forall n : nat,
  length (nlist_list _ (nlist_Var1 n)) = n.
Proof.
  induction n.
    reflexivity.

    simpl.
    rewrite IHn.
    reflexivity.
Qed.

Definition pa_f {W : Set} (w : W) : Prop := False.

Definition pa_t {W : Set} (w : W) : Prop := True.

Fixpoint nlist_pa_f (W : Set) (n : nat) : nlist n:=
  match n with
  | 0 => niln
  | S m => consn _ (@pa_f W) (nlist_pa_f W m)
  end.

Fixpoint nlist_pa_t (W : Set) (n : nat) : nlist n:=
  match n with
  | 0 => niln
  | S m => consn _ (@pa_t W) (nlist_pa_t W m)
  end.

Fixpoint alt_Ip_l {W : Set} (Ip : predicate -> W -> Prop) (l : list predicate)
                  (lpa : list (W -> Prop)) :=
  match l, lpa with
  | nil, _ => Ip
  | _, nil => Ip
  | cons P l', cons pa lpa' => alt_Ip_l (altered_Ip Ip pa P) l' lpa' 
  end.

Definition alt_Ip_pa_f {W : Set} (Ip : predicate -> W -> Prop) 
                       (l : list predicate) :=
  alt_Ip_l Ip l (nlist_list _ (nlist_pa_f W (length l))).