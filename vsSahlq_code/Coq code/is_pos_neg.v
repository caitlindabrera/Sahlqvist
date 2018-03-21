Require Import Modal.
Require Import occ_in_phi.
Require Import Bool.
Require Import my_arith__my_leb_nat.


Fixpoint is_pos (phi : Modal) (i : nat) : bool :=
  if occ_in_phi phi i then 
  match phi with
  | atom p => EqNat.beq_nat 1 i
  | mneg psi => eqb false (is_pos psi i)
  | mconj psi1 psi2 => if Nat.leb i (length (pv_in psi1)) then is_pos psi1 i
                          else is_pos psi2 (i-(length (pv_in psi1)))
  | mdisj psi1 psi2 => if Nat.leb i (length (pv_in psi1)) then is_pos psi1 i
                          else is_pos psi2 (i-(length (pv_in psi1)))
  | mimpl psi1 psi2 => if Nat.leb i (length (pv_in psi1)) then eqb false (is_pos psi1 i)
                          else is_pos psi2 (i-(length (pv_in psi1)))
  | box psi => is_pos psi i
  | diam psi => is_pos psi i
  end
  else false.

Lemma is_pos_defn_mconj : forall (phi1 phi2 : Modal) (i : nat),
  is_pos (mconj phi1 phi2) i =
  if occ_in_phi (mconj phi1 phi2) i 
     then if Nat.leb i (length (pv_in phi1)) 
             then is_pos phi1 i
             else is_pos phi2 (i-(length (pv_in phi1)))
     else false.
Proof.
  intros; simpl; reflexivity.
Qed.

Lemma is_pos_defn_mdisj : forall (phi1 phi2 : Modal) (i : nat),
  is_pos (mdisj phi1 phi2) i =
  if occ_in_phi (mdisj phi1 phi2) i 
     then if Nat.leb i (length (pv_in phi1)) 
             then is_pos phi1 i
             else is_pos phi2 (i-(length (pv_in phi1)))
     else false.
Proof.
  intros; simpl; reflexivity.
Qed.

Lemma is_pos_defn_mimpl : forall (phi1 phi2 : Modal) (i : nat),
  is_pos (mimpl phi1 phi2) i =
  if occ_in_phi (mimpl phi1 phi2) i 
     then if Nat.leb i (length (pv_in phi1)) 
             then eqb false (is_pos phi1 i)
             else is_pos phi2 (i-(length (pv_in phi1)))
     else false.
Proof.
  intros; simpl; reflexivity.
Qed.


(* ----------------------------------------------------------------- *)
(* is_neg *)


Fixpoint is_neg (phi : Modal) (i : nat) : bool :=
  if occ_in_phi phi i then 
  match phi with
  | atom p => false
  | mneg psi => eqb false (is_neg psi i)
  | mconj psi1 psi2 => if Nat.leb i (length (pv_in psi1)) then is_neg psi1 i
                          else is_neg psi2 (i-(length (pv_in psi1)))
  | mdisj psi1 psi2 => if Nat.leb i (length (pv_in psi1)) then is_neg psi1 i
                          else is_neg psi2 (i-(length (pv_in psi1)))
  | mimpl psi1 psi2 => if Nat.leb i (length (pv_in psi1)) then eqb false (is_neg psi1 i)
                          else is_neg psi2 (i-(length (pv_in psi1)))
  | box psi => is_neg psi i
  | diam psi => is_neg psi i
  end
  else false.
