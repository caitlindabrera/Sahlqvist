(* Require Import Modal.
Require Import SecOrder.  *)
Require Export ST_setup.
Require Import Correctness_ST_world_model.
Require Import List_machinery_impl.

(* A specific choice of pa_l that doesn't alter Ip, as proved below in Lemmas ineffective_Ip
   and ineffective_Ip - used later in proof of correctness_ST *)
Fixpoint ineffective_pa_l (W : Set) (Ip : predicate -> W -> Prop) (n : nat) 
                     (l : nlist n (* nlist_pred n *)) : nlist_pa W n :=
  match l with 
  | niln => niln_pa W
  | consn m P l' => consn_pa W m (Ip P) (ineffective_pa_l W Ip m l')
  end.

Lemma  ineffective_Ip2 : forall (W : Set) (l : list predicate) (Ip : predicate -> W -> Prop) ,  
   alt_Ip_list Ip (nlist_list_pa W (length l) 
       (ineffective_pa_l W Ip (length l) (list_nlist(*_pred*) l))) l
   = Ip.
Proof.
  intros W l.
  induction l.
    intros.
    simpl.
    reflexivity.

    intros.
    simpl.
    rewrite (IHl Ip).
    rewrite unalt_fun.
    reflexivity.
Qed.

(* ---------------------------------------------------------------------------- *)

Theorem correctness_ST : forall (W:Set) (R: W -> W -> Prop) (x:FOvariable) 
                        (Iv: FOvariable -> W) (Ip: predicate -> W -> Prop) 
                        (phi:Modal) ,
       (mturnst_frame W R phi) <-> 
                (SOturnst W Iv Ip R (uni_closed_SO (allFO x (ST phi x)))).
Proof.
  intros.
  unfold mturnst_frame.
  split.
    unfold uni_closed_SO.
    intros.
    apply nlist_list_closed_SO.
    intros.
    rewrite <- (Ip_V_Ip W) with (Ip := (alt_Ip_list Ip
                  (nlist_list_pa W (length (preds_in (allFO x (ST phi x)))) pa_l)
                  (preds_in (allFO x (ST phi x))))).
    apply correctness_ST_model.
    apply H.

    intros.
    apply (correctness_ST_model W R V phi x Iv).
    remember (preds_in (allFO x (ST phi x))) as l.
    assert (alt_Ip_list (V_to_Ip W V)
       (nlist_list_pa W (length l)
          (ineffective_pa_l W (V_to_Ip W V) (length l) (list_nlist(*_pred*) l))) l = 
              V_to_Ip W V) as H0.
      rewrite Heql.
      apply ineffective_Ip2.
    rewrite <- H0.
    apply (nlist_list_closed_SO W Iv R (allFO x (ST phi x)) l (V_to_Ip W V)).
    rewrite Heql.
    pose proof (Ip_uni_closed W (allFO x (ST phi x)) Iv Ip (V_to_Ip W V) R H) as H1.
    apply H1.
Qed.

Theorem correctness_ST_loc : forall (W:Set) (R: W -> W -> Prop) (x:FOvariable) 
                        (Iv: FOvariable -> W) (Ip: predicate -> W -> Prop) (w : W)
                        (phi:Modal) ,
       (mturnst_frame_loc W R w phi) <-> 
                (SOturnst W (alt_Iv Iv w x) Ip R (uni_closed_SO (ST phi x))).
Proof.
  intros.
  unfold mturnst_frame.
  split.
    unfold uni_closed_SO.
    intros.
    apply nlist_list_closed_SO.
    intros.
    rewrite <- (Ip_V_Ip W) with (Ip := (alt_Ip_list Ip
                  (nlist_list_pa W (length (preds_in (ST phi x))) pa_l)
                  (preds_in (ST phi x)))).
    apply correctness_ST_world.
    apply H.

    intros. intros V.
    apply (correctness_ST_world W R V phi w x Iv).
    remember (preds_in (allFO x (ST phi x))) as l.
    assert (alt_Ip_list (V_to_Ip W V)
       (nlist_list_pa W (length l)
          (ineffective_pa_l W (V_to_Ip W V) (length l) (list_nlist(*_pred*) l))) l = 
              V_to_Ip W V) as H0.
      rewrite Heql.
      apply ineffective_Ip2.
    rewrite <- H0.
    apply (nlist_list_closed_SO W _ R (ST phi x) l (V_to_Ip W V)).
    rewrite Heql.
    pose proof (Ip_uni_closed W (ST phi x) _ Ip (V_to_Ip W V) R H) as H1.
    apply H1.
Qed.