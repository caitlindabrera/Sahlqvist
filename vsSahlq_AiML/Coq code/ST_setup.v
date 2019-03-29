Require Export Modal at_pv.
Require Export SecOrder at_pred.
Require Import Coq.Lists.List.
Require Import Coq.Arith.EqNat. 
Require Import Coq.Init.Nat.

(* Definition of the standard translation from modal to SOL. *)
Fixpoint ST (phi: Modal) (x:FOvariable) : SecOrder :=
  match phi with
    atom (pv n) => predSO (Pred n) x
  | mneg psi => negSO (ST psi x)
  | mconj psi1 psi2 => conjSO (ST psi1 x) (ST psi2 x)
  | mdisj psi1 psi2 => disjSO (ST psi1 x) (ST psi2 x)
  | mimpl psi1 psi2 => implSO (ST psi1 x) (ST psi2 x)
  | box psi => 
      match x with
        Var n => allFO (Var (n+1)) (implSO (relatSO (Var n) (Var (n+1))) (ST psi (Var (n+1))))
      end  
  | diam psi =>
      match x with
        Var n => exFO (Var (n+1)) (conjSO (relatSO (Var n) (Var (n+1))) (ST psi (Var (n+1))))
      end
  end.

Definition ST_pv (p : propvar) : predicate :=
  match p with
    pv n => Pred n
  end.

Lemma ST_pv_P : forall n : nat,
  Pred n = ST_pv (pv n).
Proof.
  intros n; reflexivity.
Qed.

Definition ST_pred (P : predicate) : propvar :=
  match P with
    Pred n => pv n
  end.

(* Converts modal valuation to SO interpretation on predicates. *)
Fixpoint V_to_Ip (W:Set) (V: propvar -> W -> Prop) (P: predicate) (w:W) : Prop :=
  match P with 
    Pred n => V (pv n) w
  end.

(* Converts SO interpretation on predicates to modal valuation. *)
Fixpoint Ip_to_V (W:Set) (Ip: predicate -> W -> Prop) (p: propvar) (w:W) : Prop :=
  match p with 
    pv n => Ip (Pred n) w
  end.

(* Lemmas that show going from V to Ip and back to V is just the same as V.
   And for Ip to V to Ip. *)
Lemma V_Ip_V: forall (W:Set) (V: propvar -> W -> Prop),
  Ip_to_V W (V_to_Ip W V) = V.
Proof.
  intros.
  apply functional_extensionality.
  intros p.
  apply functional_extensionality.
  intros w.
  destruct p.
  unfold V_to_Ip.
  unfold Ip_to_V.
  reflexivity.
Qed.

Lemma Ip_V_Ip: forall (W:Set) (Ip: predicate -> W -> Prop),
  V_to_Ip W (Ip_to_V W Ip) = Ip.
Proof.
  intros.
  apply functional_extensionality.
  intros p.
  apply functional_extensionality.
  intros w.
  destruct p.
  unfold V_to_Ip.
  unfold Ip_to_V.
  reflexivity.
Qed.

(*--------------------------------------------------------------------------------*)

(* "By definition" lemmas of ST *)

Lemma ST_box_phi : forall (phi:Modal) (x:FOvariable), (ST (box phi) x) = 
      match x with
        Var n => allFO (Var (n+1)) (implSO (relatSO (Var n) (Var (n+1))) (ST phi (Var (n+1))))
      end.
Proof.
  simpl; reflexivity.
Qed.

Lemma ST_diam : forall (phi:Modal) (x:FOvariable), (ST (diam phi) x) =
      match x with
        Var n => exFO (Var (n+1)) (conjSO (relatSO (Var n) (Var (n+1))) (ST phi (Var (n+1))))
      end.
Proof.
  simpl; reflexivity.
Qed.

Lemma ST_conj: forall (psi_1 psi_2: Modal) (x:FOvariable), 
                   ST (mconj psi_1 psi_2) x = conjSO (ST psi_1 x) (ST psi_2 x).
Proof.
  simpl; reflexivity.
Qed.

(*--------------------------------------------------------------------------------*)

Lemma simpl_alt_l : forall (W:Set) (u v:W) (Iv: FOvariable -> W) (Ip: predicate -> W -> Prop)
                  (xn: nat), 
                      (alt_Iv (alt_Iv Iv u (Var xn)) v (Var (xn+1))) (Var xn) = u.
Proof.
  intros W u v Iv Ip xn.
  unfold alt_Iv.
  assert (EqNat.beq_nat (xn+1) xn = false).
    induction xn.
      simpl; reflexivity.

      simpl; exact IHxn.

    rewrite H.
    rewrite <- EqNat.beq_nat_refl; reflexivity.
Qed.

Lemma simpl_alt_r : forall (W:Set) (u v:W) (Iv: FOvariable -> W) (Ip: predicate -> W -> Prop)
                  (xn: nat), 
                      (alt_Iv (alt_Iv Iv u (Var xn)) v (Var (xn+1))) (Var (xn+1)) = v.
Proof.
  intros W u v Iv Ip xn.
  unfold alt_Iv.
  rewrite <- EqNat.beq_nat_refl; reflexivity.
Qed.

(*-----------------------------------------------------------------------------------------*)

Lemma R_relatSO : forall (W:Set) (R: W -> W -> Prop) (u v:W) (Iv: FOvariable -> W) 
                         (Ip: predicate -> W -> Prop) (xn:nat),
       (R u v)
     <-> (SOturnst W (alt_Iv (alt_Iv Iv u (Var xn)) v (Var (xn+1))) Ip R (relatSO (Var xn) (Var (xn+1)))).
Proof.
  intros W R u v Iv Ip xn.
  unfold SOturnst.
  rewrite simpl_alt_l.
    rewrite simpl_alt_r.
      unfold iff; apply conj; intro H; exact H.

    exact Ip.
  exact Ip.
Qed.


(* ---------------------------------------------------------------------------------------- *)


Lemma preds_in_ST_FOv : forall (phi : Modal) (x y : FOvariable),
  preds_in (ST phi x) = preds_in (ST phi y).
Proof.
  induction phi; intros x y;
    try (simpl;
    rewrite (IHphi1 x y);
    rewrite (IHphi2 x y);
    reflexivity);
    try (simpl; destruct x as [xn]; destruct y as [ym];
    simpl;
    rewrite (IHphi (Var (xn + 1)) (Var (ym + 1)));
    reflexivity).

    destruct p as [n]; destruct x; destruct y;
    reflexivity.

    simpl; apply IHphi.
Qed.



Lemma pv_in__preds_in : forall (phi : Modal) ( x : FOvariable),
  length (pv_in phi) = length (preds_in (ST phi x)).
Proof.
  induction phi; intros x;
    try destruct p; destruct x;
    try (simpl;
    do 2  rewrite app_length;
    rewrite <- IHphi1;
    rewrite <- IHphi2;
    reflexivity);
    try (simpl;
    rewrite <- IHphi;
    reflexivity;
    simpl; apply IHphi);
    try reflexivity.
Qed.

Lemma at_pv_ST_conjSO : forall (phi1 phi2 : Modal) ( x : FOvariable) (i : nat),
  (forall (x : FOvariable) (i : nat),
         match at_pv (pv_in phi1) i with
         | pv n => match at_pred (preds_in (ST phi1 x)) i with
                     | Pred m => n = m
                     end
         end) ->
  (forall (x : FOvariable) (i : nat),
         match at_pv (pv_in phi2) i with
         | pv n => match at_pred (preds_in (ST phi2 x)) i with
                     | Pred m => n = m
                     end
         end) ->
  match at_pv (pv_in (mconj phi1 phi2)) i with
  | pv n => match at_pred (preds_in (ST (mconj phi1 phi2) x)) i with
            | Pred m => n = m
            end
  end.
Proof.
  intros phi1 phi2 x i IHphi1 IHphi2;  simpl.
  case_eq (leb i (length (pv_in phi1))); intro Hleb.
    rewrite at_pv_app_l; try assumption.
    case_eq (leb i (length (preds_in (ST phi1 x)))); intros Hleb2.
      rewrite at_pred_app_l; try assumption.
      apply IHphi1.

(* 
  destruct (PeanoNat.Nat.le_ge_cases i (length (pv_in phi1)))
    as [Hleb | Hleb].
    rewrite at_pv_app_l; try assumption.
    destruct (PeanoNat.Nat.le_ge_cases i (length (preds_in (ST phi1 x))))
      as [Hleb2 | Hleb2].
 *)
(*       rewrite at_pred_app_l; try assumption.
      apply IHphi1.

Search le not.

 *)
(* PeanoNat.Nat.leb_nle *)
      apply PeanoNat.Nat.leb_le. assumption.

       rewrite <- pv_in__preds_in in Hleb2.
      rewrite Hleb2 in Hleb; discriminate.
      apply PeanoNat.Nat.leb_le. assumption.

    case_eq (leb i (length (preds_in (ST phi1 x)))); intros Hleb2.
      rewrite <- pv_in__preds_in in Hleb2.
      rewrite Hleb2 in Hleb; discriminate.
      apply PeanoNat.Nat.leb_nle in Hleb.
      apply PeanoNat.Nat.nle_gt in Hleb.
      apply PeanoNat.Nat.lt_le_incl in Hleb.
      apply Minus.le_plus_minus in Hleb.

      rewrite Hleb.
      rewrite at_pv_app_r; try assumption.
      rewrite pv_in__preds_in with (x := x).
      rewrite at_pred_app_r; try assumption.
      apply IHphi2.
        apply PeanoNat.Nat.eqb_neq. intros H.
        rewrite Hleb in Hleb2.
        rewrite <- pv_in__preds_in in *. rewrite H in *.
        rewrite <- plus_n_O in Hleb2.
        rewrite PeanoNat.Nat.leb_refl in Hleb2. discriminate.

        apply PeanoNat.Nat.eqb_neq. intros H.
        rewrite Hleb in Hleb2.
        rewrite <- pv_in__preds_in in *. rewrite H in *.
        rewrite <- plus_n_O in Hleb2.
        rewrite PeanoNat.Nat.leb_refl in Hleb2. discriminate.
Qed.

(*
Search leb true.
Search plus 0.
        simpl in Hleb2.
Search eqb false.
admit.
admit.

      destruct 
SearchAbout le .
(*       apply PeanoNat.Nat.leb_nle in Hleb.
Search leb false. *)
      apply PeanoNat.Nat.leb_nle in Hleb.
Search not le.
Search leb false.
      apply leb_nat_switch in Hleb.
      pose proof (leb_nat_ex _ _ Hleb) as H.
      destruct H as [j H].
      case_eq (beq_nat j 0); intros Hbeq.
        rewrite (beq_nat_true _ _ Hbeq) in *.
        rewrite plus_zero in H.
        rewrite <- H in *.
        rewrite <- pv_in__preds_in in Hleb2.
        rewrite leb_nat_refl in Hleb2.
        discriminate.
      rewrite <- H.
      rewrite at_pv_app_r; try assumption.
      rewrite pv_in__preds_in with (x := x).
      rewrite at_pred_app_r; try assumption.
      apply IHphi2.
Qed. *)

Lemma at_pv_ST : forall (phi : Modal) ( x : FOvariable) (i : nat),
  match at_pv (pv_in phi) i, at_pred (preds_in (ST phi x)) i with
   | pv n, Pred m => n = m
  end.
Proof.
  induction phi; intros x i.
    destruct p as [pn]; destruct x as [xn];
    simpl; case i; [reflexivity|];
      intros i2; case i2; reflexivity.

    simpl; apply IHphi.
    apply at_pv_ST_conjSO; assumption.
    apply at_pv_ST_conjSO; assumption.
    apply at_pv_ST_conjSO; assumption.

    destruct x as [n];
    simpl; apply IHphi.

    destruct x as [n];
    simpl; apply IHphi.
Qed.

Lemma ST_pred_p : forall n : nat,
  pv n = ST_pred (Pred n).
Proof.
  intros n; reflexivity.
Qed.
