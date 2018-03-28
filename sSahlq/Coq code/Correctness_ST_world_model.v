(* Require Import Modal.
Require Import SecOrder. *)
Require Export ST_setup.
Require Import Coq.Arith.PeanoNat my_arith.

(* SearchAbout iff.
Require Import My_Prop my_arith__my_leb_nat.
 *)
(* correctness_ST_world *)

Lemma correct_ST_world_box : forall (W:Set) (R: W -> W -> Prop) (V: propvar -> W -> Prop) (phi:Modal), 
                               (forall (w:W) (x:FOvariable) (Iv: FOvariable -> W), 
       (mturnst W R V w phi) <-> (SOturnst W (alt_Iv Iv w x) (V_to_Ip W V) R (ST phi x))) 
                                  -> (forall (w:W) (x:FOvariable) (Iv: FOvariable -> W), 
          (mturnst W R V w (box phi)) <-> (SOturnst W (alt_Iv Iv w x) (V_to_Ip W V) R (ST (box phi) x))).
Proof.
  intros W R V phi.
  intros IHphi.
  intros w x Iv.
  unfold iff; apply conj.
    destruct x.
    rewrite ST_box_phi.
    rewrite SOturnst_allFO.
    intros pf_mturnst.
    intros d.
    rewrite SOturnst_implSO.
    intros pf_relat.
    apply IHphi. 
    apply  R_relatSO in pf_relat.
    rewrite mturnst_box in pf_mturnst.
    apply pf_mturnst.    
    exact pf_relat.

    destruct x.
    intros pf_SOturnst.
    rewrite mturnst_box.
    intros d pf_R.
    apply (IHphi d (Var (n+1)) (alt_Iv Iv w (Var n))).
    apply (R_relatSO W R w d Iv (V_to_Ip W V) n) in pf_R.
    rewrite ST_box_phi in pf_SOturnst.
    rewrite SOturnst_allFO in pf_SOturnst.
    assert (SOturnst W
        (alt_Iv (alt_Iv Iv w (Var n)) d (Var (n + 1)))
          (V_to_Ip W V) R (implSO (relatSO (Var n) (Var (n + 1)))
            (ST phi (Var (n + 1)))))
              as pf_SOturnst_d.
      apply pf_SOturnst.
    rewrite SOturnst_implSO in pf_SOturnst_d.
    apply pf_SOturnst_d.
    exact pf_R.
Qed.



Lemma correct_ST_world_diam : forall (W:Set) (R: W -> W -> Prop) (V: propvar -> W -> Prop) (phi:Modal), 
                                 (forall (w:W) (x:FOvariable) (Iv: FOvariable -> W), 
      (mturnst W R V w phi) <-> (SOturnst W (alt_Iv Iv w x) (V_to_Ip W V) R (ST phi x))) 
                                   -> (forall (w:W) (x:FOvariable) (Iv: FOvariable -> W), 
         (mturnst W R V w (diam phi)) <-> (SOturnst W (alt_Iv Iv w x) (V_to_Ip W V) R (ST (diam phi) x))).
Proof.
  intros W R V phi.
  intros IHphi.
  intros w x Iv.
  destruct x.
  rewrite mturnst_diam.
  unfold iff; apply conj.
    intros pf_mturnst_diam.
    rewrite ST_diam.
    rewrite SOturnst_exFO.
    unfold not.
    destruct pf_mturnst_diam as [x pf_mturnst_diam' ].
    exists x.
    rewrite SOturnst_conjSO.
    split.
      simpl.
      do 2 rewrite <- EqNat.beq_nat_refl.
      rewrite beq_nat_comm.
      destruct (Nat.eqb_neq n (S n)) as [fwd rev].
      rewrite Nat.add_1_r. rewrite rev.
      2 : apply n_Sn. apply pf_mturnst_diam'.

      
(*       rewrite one_suc in rev.
      rewrite rev.
      rewrite Nat.eqb_neq.
SearchAbout beq_nat eq false not.
      rewrite n_Sn.
SearchAbout eq S.
      rewrite beq_nat_suc_false.
      apply pf_mturnst_diam'.
 *)
      apply IHphi.
      apply pf_mturnst_diam'.

    rewrite ST_diam. 
    rewrite SOturnst_exFO.
    intros pf_SOturnst.
    destruct pf_SOturnst as [d pf_SOturnst'].
    exists d.
    rewrite SOturnst_conjSO in pf_SOturnst'.
    destruct pf_SOturnst' as [H1 H2].
    simpl in H1.
    do 2 rewrite <- EqNat.beq_nat_refl in H1.

      rewrite beq_nat_comm in H1.
      destruct (Nat.eqb_neq n (S n)) as [fwd rev].
      rewrite Nat.add_1_r in H1. rewrite rev in H1.
      2 : apply n_Sn.

(*  apply pf_mturnst_diam'.

    rewrite beq_nat_suc_false in H1. *)
    split.
      exact H1.

      apply (IHphi d (Var (n+1)) (alt_Iv Iv w (Var n))).
      apply H2.
Qed.

Theorem correctness_ST_world : forall (W:Set) (R: W -> W -> Prop) (V: propvar -> W -> Prop) 
                                      (phi:Modal) (w:W) (x:FOvariable) (Iv: FOvariable -> W),
              (mturnst W R V w phi) <-> 
                    (SOturnst W (alt_Iv Iv w x) (V_to_Ip W V) R (ST phi x)).
Proof.
  intros W R V phi.
  induction phi.
    intros w x Iv.
    destruct p as [np].
    destruct x as [nx].
    unfold mturnst.
    unfold ST.
    unfold SOturnst.
    unfold alt_Iv.
    unfold V_to_Ip.
    rewrite <- EqNat.beq_nat_refl.
    apply iff_refl.

    intros w x Iv.
    simpl.

    apply bi_contrapos.
    exact (IHphi w x Iv).

    intros w x Iv.
    simpl.
    apply bi_conj.
    apply conj.
      exact (IHphi1 w x Iv).

      exact (IHphi2 w x Iv).

    intros w x Iv.
    simpl.
    split.
      intros.
      destruct H.
        left.
        apply IHphi1.
        apply H.

        right.
        apply IHphi2.
        apply H.

      intros.
      destruct H.
        left.
        apply (IHphi1 w x Iv).
        apply H.

        right.
        apply (IHphi2 w x Iv).
        apply H.

    intros.
    simpl mturnst.
    simpl ST.
    rewrite SOturnst_implSO.
    unfold iff; apply conj.
      intros pf_mturnst pf_SOturnst.
      apply IHphi2.
      apply pf_mturnst.
      apply (IHphi1 w x Iv).
      exact pf_SOturnst.

      intros pf_SOturnst pf_mturnst.
      apply (IHphi2 w x Iv).
      apply pf_SOturnst.
      apply IHphi1.
      exact pf_mturnst.

    apply correct_ST_world_box.
    exact IHphi.

    apply correct_ST_world_diam.
    exact IHphi.
Qed.

(* ----------------------------------------------------------------------------- *)

(* correctness_ST_model *)

Theorem correctness_ST_model: forall (W:Set) (R: W -> W -> Prop) (V: propvar -> W -> Prop) 
                             (phi:Modal) (x:FOvariable) (Iv: FOvariable -> W),
                                 (mturnst_model W R V phi) <-> 
                                        (SOturnst W Iv (V_to_Ip W V) R (allFO x (ST phi x))).
Proof.
  intros.
  unfold mturnst_model.
  unfold iff; apply conj.
    intros.
    destruct x.
    rewrite SOturnst_allFO.
    intros d.
    apply correctness_ST_world.
    apply H.

    intros.
    eapply correctness_ST_world.
    rewrite SOturnst_allFO in H.
    apply H.
Qed.