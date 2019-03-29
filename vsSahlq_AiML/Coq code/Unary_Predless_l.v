Require Import SecOrder.
Require Import P_occurs_in_alpha.
Require Import ST_setup.
Require Import Correctness_ST.
Require Import Arith.EqNat my_bool.
Require Import List_machinery_impl My_List_Map.
Require Import Unary_Predless nList_egs.

(*Rep_Pred_FOv Indicies Identify.
Require Import pos_SO2 Num_Occ Bool my_bool Is_Pos_Rep_Pred P_occ_rep_pred.
Require Import Uniform_Defns Monotonicity_SO Pre_Sahlvist_Uniform P_occ_rep_pred.
*)


(* 
  Uniform_Mod_Lemmas10e
*)


Fixpoint is_unary_predless_l (l : list SecOrder) : bool :=
  match l with
  | nil => true
  | cons cond l' => if is_unary_predless cond 
                       then is_unary_predless_l l'
                       else false
  end.

Lemma un_predless_l_empty_n : forall (n : nat),
  is_unary_predless_l (nlist_list n (nlist_empty n)) = true.
Proof.
  induction n.
    reflexivity.

    simpl; assumption.
Qed.

Lemma un_predless_l_empty : forall (phi : Modal) (x : FOvariable),
  is_unary_predless_l
    (nlist_list (length (preds_in (ST phi x)))
       (nlist_empty (length (preds_in (ST phi x))))) = true.
Proof.
  intros.
  apply un_predless_l_empty_n.
Qed.

Lemma un_predless_l_full_n : forall (n : nat),
  is_unary_predless_l (nlist_list n (nlist_full n)) = true.
Proof.
  induction n.
    reflexivity.

    simpl; assumption.
Qed.

Lemma un_predless_l_full : forall (phi : Modal) (x : FOvariable),
  is_unary_predless_l
    (nlist_list (length (preds_in (ST phi x)))
       (nlist_full (length (preds_in (ST phi x))))) = true.
Proof.
  intros.
  apply un_predless_l_full_n.
Qed.


(* Lemma nlist_nil2 : forall {A : Type} (a : @nlist A 0), 
           (a = niln).
Proof.
  intros.
  apply nlist_nil2.
  refine (match a as a' in nlist m
            return forall pf: (m = 0), 
                   eq_rect m (nlist) a' 0 pf = a ->  
                     a = niln
            with
          | niln  => _
          | consn  _ _ _ => _
          end eq_refl eq_refl).
    intros.
    subst a.
    rewrite <- Eqdep_dec.eq_rect_eq_dec.
      reflexivity.

      apply Arith.Peano_dec.eq_nat_dec.

    intros.
    inversion pf.
Qed. *)