Require Import Modal.
Require Import SecOrder.
Require Import p_is_pos.
Require Import p_occurs_in.
Require Import P_occurs_in_alpha.
Require Import ST_setup.
Require Import Correctness_ST.
Require Import Coq.Arith.EqNat.
Require Import List_machinery_impl my_arith__my_leb_nat.

(* Uniform_Mod_Defns *)

(* ---------------------------------------------------------  *)

Fixpoint SOQFree (alpha : SecOrder) : bool :=
  match alpha with
    predSO _ _ => true
  | relatSO _ _ =>  true
  | eqFO _ _ => true
  | allFO _ beta => SOQFree beta
  | exFO _ beta => SOQFree beta
  | negSO beta => SOQFree beta
  | conjSO beta1 beta2 => if SOQFree beta1 then SOQFree beta2 else false
  | disjSO beta1 beta2 => if SOQFree beta1 then SOQFree beta2 else false
  | implSO beta1 beta2 => if SOQFree beta1 then SOQFree beta2 else false
  | allSO _ _ => false
  | exSO _ _ => false
  end.

Fixpoint SOQFree_l (l : list SecOrder) : bool :=
  match l with
  | nil => true
  | cons alpha l' => if SOQFree alpha then SOQFree_l l' else false
  end.

Fixpoint is_unary_predless (alpha : SecOrder) : bool :=
  match alpha with
    predSO _ _ => false
  | relatSO _ _ =>  true
  | eqFO _ _ => true
  | allFO _ beta => is_unary_predless beta
  | exFO _ beta => is_unary_predless beta
  | negSO beta => is_unary_predless beta
  | conjSO beta1 beta2 => if is_unary_predless beta1 then is_unary_predless beta2 else false
  | disjSO beta1 beta2 => if is_unary_predless beta1 then is_unary_predless beta2 else false
  | implSO beta1 beta2 => if is_unary_predless beta1 then is_unary_predless beta2 else false
  | allSO _ beta => false
  | exSO _ beta => false
  end.

(* -------------------------------------------------------------------- *)


Lemma is_unary_predless_predSO : forall (P : predicate)
                                        (x : FOvariable),
  is_unary_predless (predSO P x) = false.
Proof.
  intros. reflexivity.
Qed.


Lemma is_unary_predless_conjSO_l: forall (alpha1 alpha2 : SecOrder),
  is_unary_predless (conjSO alpha1 alpha2) = true ->
    is_unary_predless alpha1 = true.
Proof.
  intros alpha1 alpha2.
  simpl.
  case (is_unary_predless alpha1);
    case (is_unary_predless alpha2);
      intros H; try reflexivity; try discriminate.
Qed.

Lemma is_unary_predless_conjSO_r: forall (alpha1 alpha2 : SecOrder),
  is_unary_predless (conjSO alpha1 alpha2) = true ->
    is_unary_predless alpha2 = true.
Proof.
  intros alpha1 alpha2.
  simpl.
  case (is_unary_predless alpha1);
    case (is_unary_predless alpha2);
      intros H; try reflexivity; try discriminate.
Qed.


Lemma un_predless_preds_in2 : forall alpha : SecOrder,
  length (preds_in alpha) = 0 <-> is_unary_predless alpha = true.
Proof.
  intros.
  induction alpha;
    try destruct p; try destruct f;
    try destruct f0;
    simpl;
    try (split; intros; discriminate);
    try (split; intros; reflexivity);
    try assumption;
    try (rewrite List.app_length;
    case_eq (is_unary_predless alpha1); intros H1;
      [apply IHalpha1 in H1; rewrite H1;
      simpl; assumption |
      case_eq (length (preds_in alpha1));
        [intros H;  apply IHalpha1 in H;
        rewrite H in *; discriminate |
        intros n H; simpl;
        split; intros; discriminate]]).
Qed.


Lemma un_predless_preds_in : forall (cond : SecOrder),
  is_unary_predless cond = true ->
    (preds_in cond = nil).
Proof.
  intros cond Hun.
  induction cond;
    try (destruct p; destruct f; simpl in *; discriminate);
    try (destruct f; destruct f0; simpl; reflexivity);
    try (destruct f; simpl in *; apply IHcond; assumption);
    try (simpl in *; apply IHcond; assumption);
    try (pose proof (is_unary_predless_conjSO_l _ _ Hun) as Hun1;
         pose proof (is_unary_predless_conjSO_r _ _ Hun) as Hun2);
    try (pose proof (is_unary_predless_disjSO_l _ _ Hun) as Hun1;
         pose proof (is_unary_predless_disjSO_r _ _ Hun) as Hun2);
    try (pose proof (is_unary_predless_implSO_l _ _ Hun) as Hun1;
         pose proof (is_unary_predless_implSO_r _ _ Hun) as Hun2);
    try (simpl in *; rewrite IHcond1; try rewrite IHcond2; try reflexivity;
        assumption);
    destruct p; simpl in *; discriminate.
Qed.

Lemma un_predless_preds_in_f : forall (alpha : SecOrder),
  is_unary_predless alpha = false -> ~ (length (preds_in alpha) = 0).
Proof.
  intros alpha H.
  unfold not; intros H2.
  induction alpha;
    try destruct p; try destruct f; try destruct f0; try destruct Q;
    simpl in *; try  discriminate;
    try (apply IHalpha; assumption);

    try (rewrite List.app_length in H2; destruct (beq_nat_0 _ _ H2);
    case_eq (is_unary_predless alpha1); intros Hun; rewrite Hun in *;
      [apply IHalpha2 | apply IHalpha1]; assumption).
Qed.


(* -------------------------------------------------------------------- *)


Lemma SOQFree_allFO : forall (alpha : SecOrder) (x : FOvariable),
  SOQFree (allFO x alpha) = true -> (SOQFree alpha = true).
Proof.
  intros alpha x H. assumption.
Qed.

Lemma SOQFree_allFO2 : forall (alpha : SecOrder) (x : FOvariable),
  (SOQFree alpha = true) -> SOQFree (allFO x alpha) = true. 
Proof.
  intros alpha x H.
  simpl.
  destruct x as [xn].
  assumption.
Qed.

Lemma SOQFree_exFO : forall (alpha : SecOrder) (x : FOvariable),
  SOQFree (exFO x alpha) = true -> (SOQFree alpha = true).
Proof.
  intros alpha x H.
  simpl in H.
  destruct x as [xn].
  case_eq (SOQFree alpha); intros H2; rewrite H2 in *;
    [reflexivity | discriminate].
Qed.
(*
Lemma SOQFree_negSO : forall (alpha : SecOrder),
  SOQFree (negSO alpha) = true -> (SOQFree alpha = true).
Proof.
  intros alpha H.
  simpl in H.
  case_eq (SOQFree alpha); intros H2; rewrite H2 in *;
    [reflexivity | discriminate].
Qed.
*)
Lemma SOQFree_conjSO_l : forall (alpha1 alpha2 : SecOrder),
  SOQFree (conjSO alpha1 alpha2) = true -> (SOQFree alpha1 = true).
Proof.
  intros alpha1 alpha2 H.
  simpl in H.
  case_eq (SOQFree alpha1); intros H2; rewrite H2 in *;
    [reflexivity | discriminate].
Qed.

Lemma SOQFree_conjSO_r : forall (alpha1 alpha2 : SecOrder),
  SOQFree (conjSO alpha1 alpha2) = true -> (SOQFree alpha2 = true).
Proof.
  intros alpha1 alpha2 H.
  simpl in H.
  case_eq (SOQFree alpha1); intros H2; rewrite H2 in *;
    [case_eq (SOQFree alpha2); intros H3;
      [reflexivity | rewrite H3 in *]; 
      discriminate | discriminate].
Qed.

Lemma SOQFree_disjSO_l : forall (alpha1 alpha2 : SecOrder),
  SOQFree (disjSO alpha1 alpha2) = true -> (SOQFree alpha1 = true).
Proof.
  intros alpha1 alpha2 H.
  simpl in H.
  case_eq (SOQFree alpha1); intros H2; rewrite H2 in *;
    [reflexivity | discriminate].
Qed.

Lemma SOQFree_disjSO_r : forall (alpha1 alpha2 : SecOrder),
  SOQFree (disjSO alpha1 alpha2) = true -> (SOQFree alpha2 = true).
Proof.
  intros alpha1 alpha2 H.
  simpl in H.
  case_eq (SOQFree alpha1); intros H2; rewrite H2 in *;
    [case_eq (SOQFree alpha2); intros H3;
      [reflexivity | rewrite H3 in *]; 
      discriminate | discriminate].
Qed.

Lemma SOQFree_implSO_l : forall (alpha1 alpha2 : SecOrder),
  SOQFree (implSO alpha1 alpha2) = true -> (SOQFree alpha1 = true).
Proof.
  intros alpha1 alpha2 H.
  simpl in H.
  case_eq (SOQFree alpha1); intros H2; rewrite H2 in *;
    [reflexivity | discriminate].
Qed.

Lemma SOQFree_implSO_r : forall (alpha1 alpha2 : SecOrder),
  SOQFree (implSO alpha1 alpha2) = true -> (SOQFree alpha2 = true).
Proof.
  intros alpha1 alpha2 H.
  simpl in H.
  case_eq (SOQFree alpha1); intros H2; rewrite H2 in *;
    [case_eq (SOQFree alpha2); intros H3;
      [reflexivity | rewrite H3 in *]; 
      discriminate | discriminate].
Qed.


Lemma SOQFree_ST : forall (phi : Modal) (x : FOvariable),
  SOQFree (ST phi x) = true.
Proof.
  induction phi; intros x; simpl in *;
    try (destruct p; destruct x; reflexivity) ;
    try apply IHphi;
    try (rewrite IHphi1; rewrite IHphi2; reflexivity);
    try (destruct x; apply IHphi).
Qed.

(* -------------------------------------------------------------------- *)

Lemma un_predless_SOQFree : forall alpha,
  is_unary_predless alpha = true ->
  SOQFree alpha = true.
Proof.
  intros alpha Hun.
  induction alpha;
    try destruct p; try destruct f;
    try destruct f0;
    try reflexivity;
    try (simpl in *;
    apply IHalpha;
    assumption);
    try (simpl in *;
    case_eq (is_unary_predless alpha1); intros Hun1;
      rewrite Hun1 in *; try discriminate;
      rewrite IHalpha1;
        [apply IHalpha2;
        assumption |
        reflexivity]);
     simpl in *; discriminate.
Qed.

Lemma P_occ_in_alpha_un_predless : forall beta P,
  is_unary_predless beta = true ->
  P_occurs_in_alpha beta P = false.
Proof.
  intros beta P Hun.
  induction beta;
    try destruct p; try destruct f; destruct P; try destruct f0;
    try (simpl in *; discriminate);
    try (unfold P_occurs_in_alpha; reflexivity);
    try (    apply P_occurs_in_alpha_conjSO_f;
    pose proof (is_unary_predless_conjSO_l _ _ Hun) as H1;
    pose proof (is_unary_predless_conjSO_r _ _ Hun) as H2;
    apply conj; [apply IHbeta1 | apply IHbeta2];
    assumption).

    rewrite <- P_occurs_in_alpha_allFO.
    apply IHbeta.
    simpl in Hun.
    assumption.

    rewrite <- P_occurs_in_alpha_exFO.
    apply IHbeta.
    simpl in Hun.
    assumption.

    rewrite <- P_occurs_in_alpha_negSO.
    apply IHbeta.
    simpl in Hun.
    assumption.
Qed.