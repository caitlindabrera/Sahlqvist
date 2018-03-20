Require Import Modal.
Require Import SecOrder.
Require Import p_is_pos.
Require Import p_occurs_in.
Require Import P_occurs_in_alpha.
Require Import ST_setup.
Require Import Correctness_ST.
Require Import Arith.EqNat.
Require Import List_machinery_impl.
Require Import Unary_Predless nList_egs My_List_Map.
Require Import my_arith__my_leb_nat List.
(* 
  Uniform_Mod_Lemmas8a
*)

(* Takes in a list of predicates and returns a list of reverse indicies at which Q occurs in l. *)
Fixpoint indicies_l_rev (l : list predicate) (Q : predicate) : list nat :=
  match l with 
  | nil => nil
  | cons P l' => match P, Q with
                 | Pred Pn, Pred Qm =>
                   if (beq_nat Pn Qm) then cons (length l) (indicies_l_rev l' Q)
                                      else indicies_l_rev l' Q
                 end
  end.

Lemma indicies_l_rev_cons : forall (l : list predicate) (P Q : predicate),
  indicies_l_rev (cons P l) Q
  = match P, Q with
    | Pred Pn, Pred Qm =>
      if beq_nat Pn Qm 
         then cons ((length l) + 1) (indicies_l_rev l Q)
         else indicies_l_rev l Q
    end.
Proof.
  intros.
  destruct P as [Pn]; destruct Q as [Qm].
  simpl.
  rewrite <- PeanoNat.Nat.add_1_r.
  reflexivity.
Qed.

Lemma indicies_l_rev_app : forall (l1 l2 : list predicate) (Q : predicate),
    indicies_l_rev (app l1 l2) Q 
  = app (list_map (fun n:nat => length l2 + n) (indicies_l_rev l1 Q))
                   (indicies_l_rev l2 Q).
Proof.
  intros.
  induction l1.
    simpl.
    reflexivity.

    simpl.
    destruct a; destruct Q.
    case (beq_nat n n0).
      rewrite IHl1.
      simpl.
      rewrite List.app_length.
      rewrite one_suc.
      rewrite one_suc with (n := length l1).
      rewrite arith_plus_comm with (a:= length l1).
      rewrite arith_plus_assoc.
      reflexivity.

      rewrite IHl1.
      reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)

(* Takes in a list of predicates and returns a list of indicies at which Q occurs in l. *)
Definition indicies (alpha :SecOrder) (Q : predicate) : list nat :=
  list_map (fun n:nat => length (preds_in alpha) + 1 - n)
           (indicies_l_rev (preds_in alpha) Q).


Lemma indicies_conjSO : forall (alpha1 alpha2 : SecOrder) (P : predicate),
  indicies (conjSO alpha1 alpha2) P
  = app (list_map (fun n:nat => length (preds_in alpha1) + 1 - n)
                (indicies_l_rev (preds_in alpha1) P))
        (list_map (fun n:nat => length (preds_in alpha1 ++ preds_in alpha2) + 1 - n)
                (indicies_l_rev (preds_in alpha2) P)).
Proof.
  intros.
  unfold indicies.
  simpl.
  rewrite indicies_l_rev_app.
  rewrite list_map_app.
  rewrite list_map_comp.
  rewrite app_length.
  rewrite fun_cancel.
  reflexivity.
Qed.

Lemma indicies_disjSO : forall (alpha1 alpha2 : SecOrder) (P : predicate),
  indicies (disjSO alpha1 alpha2) P
  = app (list_map (fun n:nat => length (preds_in alpha1) + 1 - n)
                (indicies_l_rev (preds_in alpha1) P))
        (list_map (fun n:nat => length (preds_in alpha1 ++ preds_in alpha2) + 1 - n)
                (indicies_l_rev (preds_in alpha2) P)).
Proof.
  intros.
  unfold indicies.
  simpl.
  rewrite indicies_l_rev_app.
  rewrite list_map_app.
  rewrite list_map_comp.
  rewrite app_length.
  rewrite fun_cancel.
  reflexivity.
Qed.

Lemma leb_nat_ind : forall (l : list predicate) (P : predicate),
  Nat.leb (length (indicies_l_rev l P)) (length l) = true.
Proof.
  intros l P.
  induction l.
    simpl; reflexivity.

    simpl.
   destruct a as [Pn]; destruct P as [Qm].
    case_eq (beq_nat Pn Qm); intros Hbeq.
      simpl.
      assumption.

      apply leb_suc_r.
      assumption.
Qed.


Lemma length_ind : forall (alpha : SecOrder) (P : predicate),
  length (indicies (alpha) P) = length (indicies_l_rev (preds_in alpha) P).
Proof.
  intros; unfold indicies.
  rewrite list_map_length.
  reflexivity.
Qed.
