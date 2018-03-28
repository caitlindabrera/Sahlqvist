Require Import SecOrder.
Require Import P_occurs_in_alpha.
Require Import ST_setup.
Require Import Correctness_ST.
Require Import Arith.EqNat my_bool.
Require Import List_machinery_impl My_List_Map.
Require Import Unary_Predless nList_egs Rep_Pred_FOv Indicies.
Require Import pos_SO2 Num_Occ Bool my_bool at_pred Occ_In_Alpha .
Require Import my_arith__my_leb_nat List My_Prop.

(* 
  Uniform_Mod_Lemmas8a
  Uniform_Mod_Lemmas8b
*)

(* ---------------------------------------------------------  *)



Fixpoint identify_fwd (alpha : SecOrder) (P : predicate) (i : nat) : nat :=
  if occ_in_alpha alpha i then
  match alpha with
    predSO (Pred n) (Var m) => match P with Pred m => 
                                if beq_nat m n then 0 else i
                               end
  | relatSO (Var n) (Var m) => 0
  | eqFO (Var n) (Var m) => 0
  | allFO x beta => identify_fwd beta P i
  | exFO x beta => identify_fwd beta P i
  | negSO beta => identify_fwd beta P i
  | conjSO beta1 beta2 => if occ_in_alpha beta1 i
                               then identify_fwd beta1 P i
                               else identify_fwd beta2 P 
                                        (i - (length (preds_in beta1)))
                                      + (length (preds_in beta1))
                                      - num_occ beta1 P
  | disjSO beta1 beta2 => if occ_in_alpha beta1 i
                               then identify_fwd beta1 P i
                               else identify_fwd beta2 P 
                                        (i - (length (preds_in beta1)))
                                      + (length (preds_in beta1))
                                      - num_occ beta1 P
  | implSO beta1 beta2 => if occ_in_alpha beta1 i
                               then identify_fwd beta1 P i
                               else identify_fwd beta2 P 
                                        (i - (length (preds_in beta1)))
                                      + (length (preds_in beta1))
                                      - num_occ beta1 P
  | allSO (Pred n) beta => match P with Pred m =>
                            if beq_nat m n
                               then identify_fwd beta P (i - 1)
                               else identify_fwd beta P (i - 1) + 1
                           end
  | exSO (Pred n) beta => match P with Pred m =>
                            if beq_nat m n
                               then identify_fwd beta P (i - 1)
                               else identify_fwd beta P (i - 1) + 1
                           end
  end
  else i.



Lemma identify_fwd_0 : forall (alpha : SecOrder) (P :predicate),
  identify_fwd alpha P 0 = 0.
Proof.
  intros;
  destruct alpha;
  simpl; reflexivity.
Qed.


Fixpoint identify_rev_l (l : list predicate) (P : predicate) (i : nat)
                                          : nat :=
  match i, l with
  | 0, _ => 0
  | _, nil => 0
  | S j, cons Q l' =>
        match P, Q with
        | Pred n, Pred m => 1 + if beq_nat n m 
                                   then identify_rev_l l' P i
                                   else identify_rev_l l' P j
        end
  end.

Lemma identify_rev_l_0 : forall (l : list predicate) (P : predicate),
  identify_rev_l l P 0 = 0.
Proof.
  intros.
  induction l;
    simpl; reflexivity.
Qed.

Lemma identify_rev_l_cons : forall (l : list predicate) (P Q : predicate)
                                   (i : nat),
  beq_nat i 0 = false ->
  identify_rev_l (cons Q l) P i =
    match P, Q with
    | Pred Pn, Pred Qm =>
      if beq_nat Pn Qm
         then 1 + identify_rev_l l P i
         else match i with
              | 0 => 0
              | S 0 => S 0
              | S n => 1 + identify_rev_l l P n
              end
   end.
Proof.
  intros l P Q i Hbeq.
  destruct P as [Pn]; destruct Q as [Qm].
  simpl.
  case (beq_nat Pn Qm).
    case_eq i.
      intros Hi.
      rewrite Hi in Hbeq; simpl in Hbeq; discriminate.

      intros n Hi.
      reflexivity.

    case_eq i.
      reflexivity.

      intros n Hi.
      case_eq n.
        rewrite identify_rev_l_0.
        reflexivity.

        intros m Hn.
        reflexivity.
Qed.


Lemma identify_rev_l_cons_S0 : forall (l : list predicate)
                                      (P Q : predicate),
  match P, Q with
  | Pred Pn, Pred Qm =>
  beq_nat Pn Qm = false
  end ->
  identify_rev_l (cons Q l) P 1 = 1.
Proof.
  intros l P Q Hbeq.
  destruct P as [Pn]; destruct Q as [Qm].
  simpl.
  rewrite Hbeq.
  rewrite identify_rev_l_0.
  reflexivity.
Qed.

Lemma identify_rev_l_app_S0 : forall (l1 l2 : list predicate)
                                     (P : predicate),
Nat.leb 1 (length l1 - (length (indicies_l_rev l1 P))) = true ->
    identify_rev_l (app l1 l2) P 1 = identify_rev_l l1 P 1.
Proof.
  intros l1 l2 P Hleb.
  induction l1.
    simpl in *.
    discriminate.

    simpl app.
    destruct P as [Pn]; destruct a as [Qm].
    case_eq (beq_nat Pn Qm); intros Hbeq.
      simpl in *.
      rewrite Hbeq.
      rewrite IHl1.
        reflexivity.

        rewrite beq_nat_comm in Hleb.
        rewrite Hbeq in Hleb.
        simpl in Hleb.
        assumption.

      rewrite identify_rev_l_cons_S0.
      rewrite identify_rev_l_cons_S0.
      reflexivity.

      assumption. assumption.
Qed.

Lemma identify_rev_l_app_1_cons : forall ( l2 : list predicate)
                                         (P Q : predicate) (i : nat),
  beq_nat i 0 = false ->
    Nat.leb i (length (cons Q nil) - 
          (length (indicies_l_rev (cons Q nil) P))) = true ->
      identify_rev_l (cons Q l2) P i = 1.
Proof.
  intros l2 P Q i Hbeq Hleb.
  rewrite identify_rev_l_cons in *.
  rewrite indicies_l_rev_cons in *.
  destruct P as [Pn]; destruct Q as [Qm].
  simpl in *.
  rewrite beq_nat_comm in Hleb.
  case_eq (beq_nat Pn Qm); intros Hbeq2; rewrite Hbeq2 in *.
    simpl in *.
    destruct i.
      rewrite identify_rev_l_0.
      reflexivity.

      simpl in *.
      discriminate.

    simpl in *.
    destruct i.
      discriminate.

      simpl in *.
      destruct i.
        reflexivity.

        simpl in *.
        discriminate.

    assumption.
Qed.


Lemma lemma_ind : forall (l1 l2: list predicate) 
                         (P Q : predicate) (i : nat),
  (forall (l2 : list predicate) (P' : predicate) (i : nat),
       PeanoNat.Nat.eqb i 0 = false ->
       Nat.leb i (length l1 + length l2 - 
              length (indicies_l_rev (l1 ++ l2) P')) = true ->
       Nat.leb i (length l1 - length (indicies_l_rev l1 P')) = true ->
       identify_rev_l (l1 ++ l2) P' i = identify_rev_l l1 P' i) ->
   (Nat.leb i (length (Q :: l1) + length l2 -
               length (indicies_l_rev ((Q :: l1) ++ l2) 
                        P)) = true) ->
   (Nat.leb i (length (Q :: l1) -
               length (indicies_l_rev (Q :: l1) P)) = true) ->
   (match i with
    | 0 => 0
    | 1 => 1
    | S (S _ as n) => 1 + identify_rev_l (l1 ++ l2) P n
    end =
    match i with
    | 0 => 0
    | 1 => 1
    | S (S _ as n) => 1 + identify_rev_l l1 P n
    end).
Proof.
  intros l1 l2 P Q i IHl1 Hleb1 Hleb2.
  destruct P as [Pn]; destruct Q as [Qm].
  case_eq i.
    reflexivity.
    intros n Hi.
    case_eq n. reflexivity.
      intros m Hn.
      rewrite IHl1; try reflexivity.
        simpl in Hleb1.
        case_eq (beq_nat Qm Pn); intros Hbeq; rewrite Hbeq in *.
          simpl in Hleb1;
          rewrite Hi in Hleb1;
          rewrite <- Hn.
          apply leb_suc_l.
          assumption.

          rewrite <- Hn.
          rewrite Hi in *.
          case_eq (length (indicies_l_rev (app l1 l2) (Pred Pn))).
            intros H; rewrite H in *.
            rewrite arith_minus_zero.
            simpl in *; assumption.

            intros a H; rewrite H in *.
            apply leb_suc.
            assumption.

        simpl in Hleb2.
        rewrite <- Hn; rewrite Hi in *.
        case_eq (beq_nat Qm Pn); intros Hbeq; rewrite Hbeq in *.
          simpl in Hleb2; apply leb_suc_l.
          assumption.

          case_eq (length (indicies_l_rev l1 (Pred Pn))).
            intros H; rewrite H in *.
            rewrite arith_minus_zero.
            simpl in *; assumption.

            intros a H; rewrite H in *.
            apply leb_suc.
            assumption.
Qed.

Lemma identify_rev_l_app_l : forall (l1 l2 : list predicate) (P : predicate)
                                   (i : nat),
  beq_nat i 0 = false ->
  Nat.leb i (length l1 + length l2 - (length 
                            (indicies_l_rev (app l1 l2) P))) = true ->
    Nat.leb i ((length l1) - (length (indicies_l_rev l1 P))) = true ->
             identify_rev_l (app l1 l2) P i = identify_rev_l l1 P i.
Proof.
  intros l1.
  induction l1.
    intros  l2 P i Hbeq Hleb1 Hleb2.
    simpl in *; rewrite leb_beq_zero in Hleb2.
    rewrite Hleb2 in *;  discriminate.

    intros  l2 P i Hbeq Hleb1 Hleb2.
    simpl app.
    rewrite identify_rev_l_cons;
    try rewrite identify_rev_l_cons; try assumption.
    destruct P as [Pn]; destruct a as [Qm].
    case_eq (beq_nat Pn Qm); intros Hbeq2.
      rewrite IHl1; simpl in *.
        reflexivity. assumption.

        rewrite (beq_nat_comm_t _ _ Hbeq2) in *.
        simpl in Hleb1;  assumption.

        rewrite (beq_nat_comm_t _ _ Hbeq2) in *.
        simpl in Hleb2; assumption.

      apply lemma_ind with (Q := (Pred Qm));
      assumption.

Qed.


Lemma identify_rev_l_app_r_1 : forall (l1 l2 : list predicate) (P : predicate),
  Nat.leb 1 (length l1 + length l2 - (length 
                            (indicies_l_rev (app l1 l2) P))) = true ->
    Nat.leb 1 ((length l1) - (length (indicies_l_rev l1 P))) = false ->
             identify_rev_l (app l1 l2) P 1 = 
                 (identify_rev_l l2 P (1 - ((length l1) - 
                                      (length (indicies_l_rev l1 P))))) +
                  (length l1).
Proof.
  induction l1;
    intros l2 P Hleb1 Hleb2; simpl in *.
    rewrite plus_zero; reflexivity.

    destruct P as [Pn]; destruct a as [Qm].
    case_eq (beq_nat Qm Pn); intros Hbeq.
      rewrite (beq_nat_comm_t _ _ Hbeq) in *. 
      rewrite Hbeq in *.
      simpl in *.
      rewrite IHl1; try assumption. 
        rewrite one_suc.
        rewrite (one_suc (length l1)).
        rewrite arith_plus_assoc.
        reflexivity.

      rewrite (beq_nat_comm_f _ _ Hbeq) in *.
      rewrite Hbeq in *.
      rewrite identify_rev_l_0.
      case_eq (length (indicies_l_rev l1 (Pred Pn))).
        intros H; rewrite H in *.
        discriminate.

        intros n H; rewrite H in *.
        case_eq (length l1 - n).
          intros H2; rewrite H2 in *.
          rewrite indicies_l_rev_app in Hleb1.
          rewrite app_length in Hleb1.
          rewrite list_map_length in Hleb1.
          rewrite H in Hleb1.
          simpl in Hleb1.

          assert (n = S n - 1) as Hn.
            simpl; rewrite arith_minus_zero; reflexivity.

          rewrite Hn in H2.
          rewrite <- H in H2.
          rewrite arith_minus_exp2 in H2.
            rewrite <- one_suc in H2.
            discriminate.

            apply leb_nat_ind.

            rewrite H.
            simpl; reflexivity.

          intros m H2; rewrite H2 in *; discriminate.
Qed.


(* For later:
   Redo this proof by extracting smaller lemmas. *)

Lemma identify_rev_l_app_r : forall (l1 l2 : list predicate) (P : predicate)
                                   (i : nat),
  beq_nat i 0 = false ->
  Nat.leb i (length l1 + length l2 - (length 
                            (indicies_l_rev (app l1 l2) P))) = true ->
    Nat.leb i ((length l1) - (length (indicies_l_rev l1 P))) = false ->
             identify_rev_l (app l1 l2) P i = 
                 (identify_rev_l l2 P (i - ((length l1) - 
                                      (length (indicies_l_rev l1 P))))) +
                  (length l1).
Proof.
  intros l1 l2 P.
  induction l1.
    intros  i Hbeq Hleb1 Hleb2.
    simpl in *.
    rewrite arith_minus_zero.
    rewrite plus_zero.
    reflexivity.

    intros  i Hbeq Hleb1 Hleb2.
    case_eq (beq_nat i 1); intros Hbeq4.
      rewrite (beq_nat_true _ _ Hbeq4) in *.
    destruct P as [Pn]; destruct a as [Qm].
    case_eq (beq_nat Qm Pn); intros Hbeq2.
      simpl; rewrite Hbeq2.
      rewrite (beq_nat_comm_t _ _ Hbeq2) in *.
      simpl; rewrite identify_rev_l_app_r_1.
      simpl; rewrite one_suc.
      rewrite (one_suc (length l1)).
      rewrite arith_plus_assoc.
      reflexivity.

        simpl in *; rewrite Hbeq2 in *.
        simpl in *; assumption.

        simpl in *; rewrite Hbeq2 in *.
        simpl in *; assumption.

      rewrite identify_rev_l_app_r_1; try assumption.
      reflexivity. 

    case_eq i.
      intros Hi.
      rewrite Hi in *; simpl in *; discriminate.

      intros n Hi; rewrite Hi in *.
      case_eq n.
        intros Hn.
        rewrite Hn in *; simpl in *; discriminate.

        intros m Hn.

        destruct P as [Pn]; destruct a as [Qm].
        simpl app.
        rewrite identify_rev_l_cons.
        simpl app in *.
        rewrite indicies_l_rev_cons in *.
        case_eq (beq_nat Qm Pn); intros Hbeq2;
          rewrite Hbeq2 in *.
          simpl length in *.
          rewrite arith_minus_suc3 in *.
          rewrite (beq_nat_comm_t _ _ Hbeq2) in *.
          rewrite <- Hn.
          rewrite <- Hi.
          rewrite IHl1.

          case_eq (length l1 - length (indicies_l_rev l1 (Pred Pn))).
            intros H.
            rewrite H in *.
            rewrite arith_minus_zero.
            rewrite one_suc.
            rewrite (one_suc (length l1)).
            rewrite arith_plus_assoc.
            reflexivity.

            intros j H.
            rewrite H in *.
            simpl in Hleb2.
            case_eq j.
              intros Hj.
              rewrite Hi.
              simpl.
              rewrite arith_minus_zero.
              rewrite one_suc.
              rewrite (one_suc (length l1)).
              rewrite arith_plus_assoc.
              reflexivity.

              intros k Hj.
              rewrite Hi.
              simpl.
              rewrite Hn.
              simpl.
              rewrite one_suc.
              rewrite (one_suc (length l1)).
              rewrite arith_plus_assoc.
              reflexivity.

              rewrite Hi.
              simpl; reflexivity. 

              case_eq (length l1 + length l2 - length (indicies_l_rev
                            (app l1 l2) (Pred Pn))).
                intros H.
                simpl in *.
                rewrite H in *; discriminate.

                intros m' H.
                simpl in *.
                rewrite H in *.
                rewrite Hi.
                simpl; assumption.

                case_eq (length l1 - length (indicies_l_rev l1 (Pred Pn))).
                  intros H.
                  rewrite H in *.
                  rewrite Hi.
                  simpl; reflexivity.

                  intros j H.
                  rewrite Hi.
                  simpl.
                  rewrite H in *.
                  assumption.

                  rewrite (beq_nat_comm_f _ _ Hbeq2) in *.
                  case_eq (length (indicies_l_rev l1 (Pred Pn))).
                    intros H; rewrite H in *.
                    simpl length in *.
                    rewrite arith_minus_zero in *.
                    case_eq (length l1).
                      intros H2.
                      rewrite H2 in *.
                      rewrite one_suc.
                      simpl.
                      rewrite IHl1.
                      rewrite arith_minus_zero.
                      rewrite plus_zero.
                      reflexivity.

                      simpl; reflexivity.
                      simpl plus.
                      case_eq ( length (indicies_l_rev
                                (app l1 l2) (Pred Pn))).
                        intros H3.
                        rewrite H3 in *.
                        rewrite arith_minus_zero in *.
                        rewrite <- Hn.
                        apply Hleb1.

                        intros j H3.
                        rewrite H3 in *.
                        rewrite (one_suc j).
                        rewrite arith_minus_exp.
                        case_eq (length l2 - j).
                          intros H4.
                          simpl.
                          simpl in Hleb1.
                          rewrite H4 in *.
                          discriminate.

                          intros k H4.
                          simpl in Hleb1.
                          rewrite H4 in *.
                          simpl minus.
                          rewrite arith_minus_zero.
                          rewrite <- Hn.
                          assumption.

                          simpl; reflexivity.

                          intros j H2.
                          rewrite H2 in *.
                          rewrite IHl1.
                            simpl.
                            rewrite one_suc.
                            rewrite (one_suc (S j)).
                            rewrite arith_plus_assoc.
                            reflexivity.

                            simpl; reflexivity.
                            rewrite <- Hn.
                            rewrite <- H2 in *.
                            rewrite (one_suc (length l1)) in Hleb1.
                            rewrite arith_plus_assoc in Hleb1.
                            rewrite (arith_plus_comm 1 (length l2)) in Hleb1.
                            rewrite <- arith_plus_assoc in Hleb1.
                            rewrite <- one_suc in Hleb1.
                            apply leb_suc3.
                            assumption.

                            pose proof (leb_nat_ind (app l1 l2) (Pred Pn)) as H3.
                            rewrite app_length in H3.
                            assumption.

                            rewrite <- Hn.
                            simpl in *.
                            assumption.

                  intros j H.
                    rewrite H in *.
                    simpl length in *.
                    rewrite arith_minus_suc3 in *.
                    case_eq (length l1).
                      intros H2.
                      rewrite H2 in *.
                      rewrite one_suc.
                      simpl.
                      apply length_zero_iff_nil in H2.
                      rewrite H2 in H. discriminate.

                      intros k H2.
                      rewrite H2 in *.
                      rewrite arith_minus_suc3 in *.
                      rewrite IHl1.
                        rewrite <- (arith_minus_suc k j).
                        rewrite arith_minus_suc3.
                        rewrite <- Hn.
                        rewrite (one_suc (S k)).
                        rewrite arith_plus_comm.
                        rewrite arith_plus_assoc.
                        reflexivity.

                        pose proof (leb_nat_ind l1 (Pred Pn)) as H3.
                        rewrite H in H3.
                        rewrite H2 in H3.
                        apply H3.

                        simpl; reflexivity.

                        rewrite <- H2 in *.
                        rewrite <- Hn.
                        apply leb_suc3.
                          simpl in *.
                          assumption.

                          pose proof (leb_nat_ind (app l1 l2) (Pred Pn)) as H3.
                          rewrite app_length in H3; assumption.

                          rewrite <- Hn.
                          rewrite <- (arith_minus_suc k j) in Hleb2.
                            apply Hleb2.
                            pose proof (leb_nat_ind l1 (Pred Pn)) as H3.
                            rewrite H in H3; rewrite H2 in H3.
                            apply H3.

                            simpl; reflexivity.
Qed.


Lemma identify_rev_l_app : forall (l1 l2 : list predicate) (P : predicate)
                                   (i : nat),
  beq_nat i 0 = false ->
  Nat.leb i (length l1 + length l2 - (length 
                            (indicies_l_rev (app l1 l2) P))) = true ->
    identify_rev_l (app l1 l2) P i = 
      if Nat.leb i ((length l1) - (length (indicies_l_rev l1 P)))
         then identify_rev_l l1 P i
         else (identify_rev_l l2 P (i - ((length l1) - 
                                      (length (indicies_l_rev l1 P)))) + (length l1)).
Proof.
  intros l1 l2 P i Hbeq Hleb1.
  case_eq (Nat.leb i ((length l1) - (length (indicies_l_rev l1 P))));
    intros H;
    [apply identify_rev_l_app_l | apply identify_rev_l_app_r];
    assumption.
Qed.

(* --------------------------------------------------------------------- *)

Definition identify_rev (alpha : SecOrder) (P : predicate) (i : nat) : nat :=
  identify_rev_l (preds_in alpha) P i.

Lemma identify_rev_allFO : forall (alpha : SecOrder) (x : FOvariable) (P : predicate) (i : nat),
  identify_rev (allFO x alpha) P i = identify_rev alpha P i.
Proof.
  intros.
  unfold identify_rev.
  reflexivity.
Qed.

Lemma identify_rev_exFO : forall (alpha : SecOrder) (x : FOvariable) (P : predicate) (i : nat),
  identify_rev (exFO x alpha) P i = identify_rev alpha P i.
Proof.
  intros.
  unfold identify_rev.
  destruct x.
  reflexivity.
Qed.

Lemma identify_rev_negSO : forall (alpha : SecOrder) (P : predicate) (i : nat),
  identify_rev (negSO alpha) P i = identify_rev alpha P i.
Proof.
  intros.
  unfold identify_rev.
  reflexivity.
Qed.

Lemma identify_rev_predSO : forall (P Q : predicate) (x : FOvariable) (i : nat),
  beq_nat i 0 = false ->
  identify_rev (predSO P x) Q i = 
    match P, Q with
    | Pred Pn, Pred Qm => 1
    end.
Proof.
  intros P Q x i Hbeq.
  destruct P as [Pn]; destruct Q as [Qm]; destruct x as [xn].
  unfold identify_rev.
  simpl preds_in.
  simpl.
  case_eq i.
    intros Hi; rewrite Hi in *.
    simpl in *; discriminate.

    intros j Hi.
    case (beq_nat Qm Pn).
      reflexivity.

      case j; reflexivity.
Qed.

(* --------------------------------------------------------- *)

Fixpoint num_occ_l (l : list predicate) (P : predicate) : nat :=
  match l with
  | nil => 0
  | cons Q l' => match P, Q with Pred Pn, Pred Qm =>
                  if beq_nat Pn Qm then 1 + num_occ_l l' P
                                   else num_occ_l l' P
                 end
  end.

Lemma identify_rev_l_app2 : forall (l1 l2 : list predicate)
                                    (P : predicate) (i : nat),
  (Nat.leb i ((length l1)- (num_occ_l l1 P)) = true ->
    identify_rev_l (app l1 l2) P i = identify_rev_l l1 P i).
Proof.
  induction l1.
    intros.
    simpl in *.
    case_eq i.
      intros Hi.
      rewrite identify_rev_l_0.
      reflexivity.

      intros n Hi; rewrite Hi in *; simpl in *; discriminate.

    intros l2 P i Hleb.
    simpl.
    case_eq i.
      reflexivity.

      intros n Hi.
      destruct P as [Pn]; destruct a as [Qm].
      simpl in *.
      case_eq (beq_nat Pn Qm); intros Hbeq;
        rewrite Hbeq in *.
        rewrite IHl1.
          reflexivity.

          simpl.
          case_eq (length l1 - num_occ_l l1 (Pred Pn)).
            intros Heq.
            rewrite Heq in *.
            rewrite Hi in Hleb.
            simpl in *; discriminate.

            intros m Heq.
            rewrite Heq in Hleb.
            rewrite Hi in Hleb.
            simpl in Hleb.
            assumption.

        rewrite IHl1.
          reflexivity.

          case_eq (num_occ_l l1 (Pred Pn)).
            intros Heq.
            rewrite Heq in *.
            rewrite Hi in Hleb.
            simpl in Hleb.
            rewrite arith_minus_zero.
            assumption.

            intros m Heq.
            rewrite Heq in *.
            rewrite Hi in Hleb.
            simpl in Hleb.
            rewrite one_suc.
            rewrite arith_minus_exp.
            case_eq (length l1 - m).
              intros Heq2; rewrite Heq2 in *.
              discriminate.

              intros m' Heq2.
              rewrite Heq2 in *.
              rewrite one_suc.
              rewrite arith_plus_comm.
              rewrite arith_plus_3.
              assumption.
Qed.

Lemma num_occ_l_app : forall (l1 l2 : list predicate) (P : predicate),
  num_occ_l (app l1 l2) P = num_occ_l l1 P + num_occ_l l2 P.
Proof.
  induction l1.
    intros.
    simpl.
    reflexivity.

    intros l2 P.
    simpl.
    destruct P as [Pn]; destruct a as [Qm].
    rewrite IHl1.
      rewrite one_suc.
      rewrite one_suc with (n := num_occ_l l1 (Pred Pn)).
      rewrite arith_plus_assoc.
      rewrite arith_plus_comm with (b := 1).
      rewrite <- arith_plus_assoc.
    case_eq (beq_nat Pn Qm); intros Hbeq; reflexivity.
Qed.

Lemma leb_num_occ : forall (alpha : SecOrder) (P : predicate),
  Nat.leb (num_occ_l (preds_in alpha) P) (length (preds_in alpha)) = true.
Proof.
  intros alpha P.
  induction alpha;
    try destruct p as [Qm];
    try destruct f as [xn];
    destruct P as [Pn];
    try destruct f0 as [xm];
    simpl;
    try case (beq_nat Pn Qm); simpl in *;
    try reflexivity;
    try assumption;
    try (rewrite num_occ_l_app; rewrite app_length; 
        apply leb_plus_gen; assumption);
    try (apply leb_suc_r; assumption).
Qed.

Lemma leb_id_fwd_plus : forall (alpha1 alpha2: SecOrder) (P : predicate) 
                                    (n: nat),
  Nat.leb n
      (length (preds_in alpha1) - num_occ_l (preds_in alpha1) P) = true ->
  Nat.leb n
      (length (preds_in alpha1) + length (preds_in alpha2) -
        (num_occ_l (preds_in alpha1) P + 
           num_occ_l (preds_in alpha2) P)) = true.
Proof.
  intros alpha1 alpha2 P n Hleb.
  rewrite leb_plus_minus.
    reflexivity.

    assumption.

    apply leb_num_occ.

    apply leb_num_occ.
Qed.

Lemma num_occ__l : forall (alpha : SecOrder) (P : predicate),
  (num_occ_l (preds_in alpha) P) = (num_occ alpha P).
Proof.
  intros.
  unfold num_occ.
  unfold indicies.
  rewrite list_map_length.
  induction alpha;
    try destruct p as [Qm]; 
    try destruct f as [xn]; 
    destruct P as [Pn];
    try destruct f0 as [xm];
    simpl;
    try reflexivity;
    try assumption;
    try (rewrite num_occ_l_app;
    rewrite indicies_l_rev_app;
    rewrite app_length;
    rewrite list_map_length;
    rewrite IHalpha1;
    rewrite IHalpha2;
    reflexivity);
    try (case_eq (beq_nat Pn Qm); intros Hbeq);
    try  (rewrite (beq_nat_true Pn Qm Hbeq);
    rewrite <- beq_nat_refl; simpl; reflexivity);
    try (rewrite beq_nat_comm; rewrite Hbeq; reflexivity);
    try (rewrite beq_nat_comm; rewrite Hbeq; simpl;
         rewrite IHalpha; reflexivity).
Qed.


(* ----------------------------------------------------------------------------- *)


Lemma leb_id_fwd_allSO : forall (alpha : SecOrder) (P Q : predicate) (i : nat),
  (forall (i : nat),occ_in_alpha alpha i = true ->
       Nat.leb (identify_fwd alpha P i) (length (preds_in alpha) - num_occ alpha P) = true) ->
    occ_in_alpha (allSO Q alpha) i = true ->
       Nat.leb (identify_fwd (allSO Q alpha) P i) (length (preds_in (allSO Q alpha)) 
              - num_occ (allSO Q alpha) P) = true.
Proof.
  intros alpha P Q i IHalpha H; simpl; rewrite H.
  destruct Q as [Qm]; destruct P as [Pn];
  rewrite num_occ_allSO.
  case_eq (beq_nat i 1); intros Hbeq2.
    rewrite (beq_nat_true _ _ Hbeq2).
    simpl.
    case_eq (beq_nat Pn Qm); intros Hbeq;
      rewrite beq_nat_comm; rewrite Hbeq;
      rewrite identify_fwd_0; simpl.
      reflexivity.

      case_eq (num_occ alpha (Pred Pn)).
        intros Hnum; reflexivity.

        intros n Hnum.
        case_eq (length (preds_in alpha) - n).
          intros Hl; specialize (IHalpha 1).
          rewrite Hnum in IHalpha; rewrite (one_suc n) in IHalpha.
          rewrite arith_minus_exp in IHalpha; rewrite Hl in IHalpha.
          simpl in IHalpha.
          pose proof (num_occ_preds_in alpha (Pred Pn)) as H2.
          rewrite Hnum in H2.
          assert (beq_nat (length (preds_in alpha) - n) 0 = true) as H3.
            rewrite Hl.
            simpl; reflexivity.
          apply beq_nat_leb in H3.
          pose proof (leb_trans _ _ _ H2 H3)  as H4.
          rewrite leb_suc_f in H4; discriminate.

          intros m Hl; reflexivity.

      case_eq (beq_nat Pn Qm); intros Hbeq;
        simpl; rewrite beq_nat_comm;
        rewrite Hbeq; simpl;
        rewrite occ_in_alpha_allSO in H.
        apply IHalpha.
        rewrite Hbeq2 in H.
        assumption.

        rewrite Hbeq2 in H.
        specialize (IHalpha (i - 1)).
        case_eq (num_occ alpha (Pred Pn)).
          intros Hnum; rewrite <- one_suc.
          simpl; rewrite Hnum in IHalpha.
          rewrite arith_minus_zero in IHalpha.
          apply IHalpha; assumption.

          intros n Hnum.
          rewrite Hnum in IHalpha.
          rewrite (one_suc n) in IHalpha.
          rewrite arith_minus_exp in IHalpha.
          assert (n = n + 1 - 1) as Hn.
            rewrite <- arith_plus_minus_assoc2.
            simpl; rewrite plus_zero; reflexivity.

            simpl; reflexivity.

            rewrite Hn; rewrite <- arith_plus_minus_assoc.
            rewrite <- leb_plus; rewrite arith_minus_exp.
            apply IHalpha; assumption.

            rewrite <- one_suc; rewrite <- Hnum.
            apply num_occ_preds_in.

            rewrite <- one_suc.
            reflexivity.
Qed.

Lemma leb_id_fwd : forall (alpha : SecOrder) (P : predicate) (i : nat),
  occ_in_alpha alpha i = true ->
    Nat.leb (identify_fwd alpha P i) 
          (length (preds_in alpha) - (num_occ alpha P)) = true.
Proof.
  intros alpha P; induction alpha;
    intros i H;
    try (apply leb_id_fwd_allSO;
    [intros i' Hocc; apply IHalpha |];
    assumption);
    try destruct p as [Qm]; try destruct f as [xn];
    destruct P as [Pn]; try destruct f0 as [xm];
    simpl;
    try rewrite H;
    [ | | | rewrite num_occ_allFO; rewrite occ_in_alpha_allFO in H |
        rewrite num_occ_exFO | | rewrite num_occ_conjSO | 
        rewrite num_occ_disjSO | rewrite num_occ_implSO];
    try (apply IHalpha; assumption);
    try reflexivity;
    try (    case_eq (occ_in_alpha alpha1 i); intros Heq;
      rewrite app_length);
    try (do 2 rewrite <- num_occ__l;
      apply leb_id_fwd_plus;
      rewrite num_occ__l;
      apply IHalpha1; assumption);
    try (rewrite arith_plus_comm;
      rewrite arith_minus_exp;
      rewrite arith_plus_comm;
      rewrite <- arith_plus_minus_assoc2;
        try         apply num_occ_preds_in;
      rewrite arith_plus_comm with (a := length (preds_in alpha1));
      rewrite <- arith_plus_minus_assoc2;
        try         apply num_occ_preds_in;
      rewrite arith_plus_comm;
      rewrite arith_plus_comm with (a := length (preds_in alpha2));
      rewrite <- arith_plus_minus_assoc2 with (b := length (preds_in alpha2));
      [rewrite <- leb_plus_pre;
      apply IHalpha2;
        apply (occ_in_alpha_conjSO2_fwd alpha1 alpha2 i) in H |] ;
        [destruct H as [fwd | rev] ;
          [rewrite fwd in *; discriminate|
          assumption]|];

        apply num_occ_preds_in);
    case_eq (beq_nat Pn Qm); intros Hbeq;
      simpl; try reflexivity;

      unfold num_occ in *; simpl;
      unfold indicies in *;
      rewrite list_map_length in *;
      simpl; rewrite (beq_nat_comm);
      rewrite Hbeq; simpl;

      try (rewrite (occ_in_alpha_predSO _ _ _ H);
      reflexivity).
Qed.

Lemma identify_fwd_rev_predSO : forall (P Q : predicate) (x : FOvariable) (i : nat),
  ~((identify_fwd (predSO Q x) P i) = 0) ->
    occ_in_alpha (predSO Q x) i = true ->
      identify_rev (predSO Q x) P (identify_fwd (predSO Q x) P i) =  i.
Proof.
  intros P Q x i Hid Hocc; simpl.
  destruct Q as [Qm]; destruct x as [xn]; destruct P as [Pn].
  simpl in *; rewrite occ_in_alpha_defn in Hocc.
  unfold identify_rev;  simpl in *.
  case_eq (beq_nat Pn Qm); intros Hbeq;
    rewrite Hbeq in *.
    unfold not in Hid.
    case_eq (occ_in_alpha (predSO (Pred Qm) (Var xn)) i); intros Hocc2;
      rewrite Hocc2 in *.
      specialize (Hid (eq_refl _)); contradiction.

      case_eq i.
        reflexivity.

        intros n Hi; rewrite Hi in *.
        simpl in *.
        case_eq n.
          reflexivity.

          intros m Hn; rewrite Hn in *.
          simpl in *;  discriminate.

      rewrite if_then_else_same in *.
      unfold not in Hid.
      rewrite if_then_else_same in Hid.
      case_eq i.
        reflexivity.

        intros n Hi; rewrite Hi in *; simpl in *.
        case_eq n.
          reflexivity.

          intros m Hn; rewrite Hn in *; simpl in *.
          discriminate.
Qed.



Lemma id_fwd_beq_nat_conjSO : forall (alpha1 alpha2 : SecOrder) (n : nat) (P : predicate),
  (forall (n : nat) (P : predicate),
           occ_in_alpha alpha1 n = true ->
           match at_pred (preds_in alpha1) n with
           | Pred Qm => match P with
                        | Pred Pn => PeanoNat.Nat.eqb Pn Qm = false
                        end
           end -> PeanoNat.Nat.eqb (identify_fwd alpha1 P n) 0 = false) ->
  (forall (n : nat) (P : predicate),
           occ_in_alpha alpha2 n = true ->
           match at_pred (preds_in alpha2) n with
           | Pred Qm => match P with
                        | Pred Pn => PeanoNat.Nat.eqb Pn Qm = false
                        end
           end -> PeanoNat.Nat.eqb (identify_fwd alpha2 P n) 0 = false) ->
    occ_in_alpha (conjSO alpha1 alpha2) n = true ->
      (match at_pred (preds_in (conjSO alpha1 alpha2)) n, P with
       | Pred Qm, Pred Pn => PeanoNat.Nat.eqb Pn Qm = false
       end) ->
          PeanoNat.Nat.eqb (identify_fwd (conjSO alpha1 alpha2) 
                  P n) 0 = false.
Proof.
  intros alpha1 alpha2 n P IHalpha1 IHalpha2 Hocc Hbeq;
  destruct P as [Pn].
    simpl in *.
    rewrite Hocc.
    pose proof (occ_in_alpha_conjSO2_fwd2 _ _ _ Hocc) as H.
    destruct H.
      rewrite H.
      rewrite at_pred_occ_l in Hbeq; try assumption.
      apply IHalpha1; assumption.

      destruct H as [H1 H2].
      rewrite at_pred_occ_r in Hbeq; try assumption.
      rewrite H1.
      rewrite <- arith_plus_minus_assoc2.
      case_eq (length (preds_in alpha1) - num_occ alpha1 (Pred Pn)).
        intros H; rewrite plus_zero.
        apply IHalpha2; assumption.

        intros m H.
        rewrite one_suc.
        rewrite <- arith_plus_assoc.
        rewrite <- one_suc.
        simpl.
        reflexivity.

        apply num_occ_preds_in.
Qed.

Lemma id_fwd_beq_nat_allSO : forall (alpha : SecOrder) (n : nat) (P Q : predicate),
  (forall (n : nat) (P : predicate),
     occ_in_alpha alpha n = true ->
          match at_pred (preds_in alpha) n with
          | Pred Qm => match P with
                       | Pred Pn => PeanoNat.Nat.eqb Pn Qm = false
                       end
          end -> PeanoNat.Nat.eqb (identify_fwd alpha P n) 0 = false) ->
    occ_in_alpha (allSO Q alpha) n = true ->
       (match at_pred (preds_in (allSO Q alpha)) n, P with
       | Pred Qm, Pred Pn => PeanoNat.Nat.eqb Pn Qm = false
       end) ->
           PeanoNat.Nat.eqb (identify_fwd (allSO Q alpha)
                     P n) 0 = false.
Proof.
  intros alpha n P Q IHalpha Hocc Hbeq.
  destruct P as [Pn]; destruct Q as [Qm].
  simpl in *.
  rewrite Hocc.
  case_eq n.
    intros Hn; rewrite Hn in *.
    rewrite occ_in_alpha_0 in Hocc.
    discriminate.

    intros m Hn; rewrite Hn in *.
    rewrite occ_in_alpha_allSO in Hocc.
    simpl in Hocc.
    case_eq m.
      intros Hm; rewrite Hm in *.
      simpl in *.
      rewrite Hbeq.
      rewrite identify_fwd_0; simpl; reflexivity.

      intros j Hm; rewrite Hm in *.
      simpl in *.
      rewrite <- Hm in *.
      case_eq (beq_nat Pn Qm); intros Hbeq2.
        apply IHalpha; assumption.

        rewrite <- one_suc.
        simpl; reflexivity.
Qed.


Lemma id_fwd_beq_nat : forall (alpha : SecOrder) (n : nat) (P : predicate),
  occ_in_alpha alpha n = true ->
    match at_pred (preds_in alpha) n, P with
       | Pred Qm, Pred Pn => PeanoNat.Nat.eqb Pn Qm = false
    end ->
      PeanoNat.Nat.eqb (identify_fwd alpha P n) 0 = false.
Proof.
  induction alpha;
    intros n P Hocc Hbeq;     destruct P as [Pn];
    try (apply id_fwd_beq_nat_conjSO; assumption);
    try (apply id_fwd_beq_nat_allSO; assumption).
    simpl in *.
    destruct p as [Qm]; destruct f as [xn].
    rewrite Hocc.
    simpl in Hbeq.
    case_eq n.
      intros Hn; rewrite Hn in *.
      apply occ_in_alpha_predSO in Hocc.
      discriminate.

      intros m Hn; rewrite Hn in *.
      case_eq m.
        intros Hm; rewrite Hm in *.
        rewrite Hbeq.
        simpl; reflexivity.

        intros j Hm; rewrite Hm in *.
        apply occ_in_alpha_predSO in Hocc.
        simpl in *; discriminate.

    rewrite occ_in_alpha_relatSO in Hocc.
    discriminate.

    rewrite occ_in_alpha_eqFO in Hocc.
    discriminate.

    simpl in *.
    rewrite Hocc.
    rewrite occ_in_alpha_allFO in Hocc.
    apply IHalpha; assumption.

    simpl in *; destruct f.
    rewrite Hocc.
    rewrite occ_in_alpha_exFO in Hocc.
    apply IHalpha; assumption.

    simpl in *; rewrite Hocc.
    rewrite occ_in_alpha_negSO in Hocc.
    apply IHalpha; assumption.

Qed.


Lemma id_fwd_not_conjSO  : forall (alpha1 alpha2 : SecOrder) (n : nat) (P : predicate),
  (forall (n : nat) (P : predicate),
    match at_pred (preds_in alpha1) n , P with
    | Pred Qm, Pred Pn => PeanoNat.Nat.eqb Pn Qm = false
    end ->
      beq_nat n 0 = false ->
        occ_in_alpha alpha1 n = true ->
          identify_fwd alpha1 P n <> 0) ->
    (forall (n : nat) (P : predicate),
      match at_pred (preds_in alpha2) n , P with
      | Pred Qm, Pred Pn => PeanoNat.Nat.eqb Pn Qm = false
      end ->
        beq_nat n 0 = false ->
          occ_in_alpha alpha2 n = true ->
            identify_fwd alpha2 P n <> 0) ->
    match at_pred (preds_in (conjSO alpha1 alpha2)) n , P with
    | Pred Qm, Pred Pn => PeanoNat.Nat.eqb Pn Qm = false
    end ->
      beq_nat n 0 = false ->
        occ_in_alpha (conjSO alpha1 alpha2) n = true ->
          identify_fwd (conjSO alpha1 alpha2) P n <> 0.
Proof.
  intros alpha1 alpha2 n P IHalpha1 IHalpha2 Hbeq1 Hbeq2 Hocc.
  unfold not in *; intros H;
  destruct P as [Pn].
  simpl in Hbeq1;
    simpl in H;
    rewrite Hocc in *;
    destruct (occ_in_alpha_conjSO2_fwd2 _ _ _ Hocc) as [Hocc1 | Hocc2];
      [rewrite Hocc1 in *;
      rewrite at_pred_occ_l in Hbeq1; try assumption;
      apply IHalpha1 with (n := n) (P := (Pred Pn));
        try assumption |

      destruct Hocc2 as [Hocc1 Hocc2];
      rewrite Hocc1 in *;
      rewrite at_pred_occ_r in Hbeq1; try assumption;
      apply IHalpha2 with (n := n - length (preds_in alpha1)) 
                          (P := Pred Pn) ; try assumption;
        apply occ_in_alpha_leb2 in Hocc2;
          [apply Hocc2 |

          rewrite <- arith_plus_minus_assoc2 in H;
            [apply eq_plus_zero in H;
            assumption |
            apply num_occ_preds_in]]].
Qed.

Lemma id_fwd_not_allSO  : forall (alpha : SecOrder) (n : nat) (P Q : predicate),
  (forall (n : nat) (P : predicate),
    match at_pred (preds_in alpha) n , P with
    | Pred Qm, Pred Pn => PeanoNat.Nat.eqb Pn Qm = false
    end ->
      beq_nat n 0 = false ->
        occ_in_alpha alpha n = true ->
          identify_fwd alpha P n <> 0) ->
    match at_pred (preds_in (allSO Q alpha)) n , P with
    | Pred Qm, Pred Pn => PeanoNat.Nat.eqb Pn Qm = false
    end ->
      beq_nat n 0 = false ->
        occ_in_alpha (allSO Q alpha) n = true ->
          identify_fwd (allSO Q alpha) P n <> 0.
Proof.
  intros alpha n P Q IHalpha Hbeq1 Hbeq2 Hocc.
  unfold not in *; intros H.
  pose proof Hocc as Hocc2.
  rewrite occ_in_alpha_allSO in Hocc.
  destruct P as [Pn]; destruct Q as [Qm].
  case_eq n.
    intros Hn; rewrite Hn in *; simpl in *;
    discriminate.

    intros m Hn.
    rewrite Hn in *.
    simpl in Hocc.
    case_eq m.
      intros Hm; rewrite Hm in *.
      simpl in Hbeq1.
      simpl in H.
      rewrite Hbeq1 in H.
      rewrite identify_fwd_0 in H.
      simpl in H; discriminate.

      intros j Hm.
      rewrite Hm in Hocc.
      simpl in Hocc.
      rewrite <- Hm in *.
      simpl in H.
      rewrite Hocc2 in H.
      rewrite Hm in Hbeq1.
      simpl in Hbeq1.
      rewrite arith_minus_zero in H.
      case_eq (beq_nat Pn Qm); intros Hbeq.
        rewrite Hbeq in *.
        apply (IHalpha m (Pred Pn)).
          rewrite <- Hm in Hbeq1; assumption.

          rewrite Hm; assumption.

          assumption.

          assumption.

        rewrite Hbeq in *.
        rewrite <- one_suc in H.
        simpl in *; discriminate.
Qed.

Lemma id_fwd_not_exSO  : forall (alpha : SecOrder) (n : nat) (P Q : predicate),
  (forall (n : nat) (P : predicate),
    match at_pred (preds_in alpha) n , P with
    | Pred Qm, Pred Pn => PeanoNat.Nat.eqb Pn Qm = false
    end ->
      beq_nat n 0 = false ->
        occ_in_alpha alpha n = true ->
          identify_fwd alpha P n <> 0) ->
    match at_pred (preds_in (exSO Q alpha)) n , P with
    | Pred Qm, Pred Pn => PeanoNat.Nat.eqb Pn Qm = false
    end ->
      beq_nat n 0 = false ->
        occ_in_alpha (exSO Q alpha) n = true ->
          identify_fwd (exSO Q alpha) P n <> 0.
Proof.
  intros alpha n P Q IHalpha Hbeq1 Hbeq2 Hocc.
  unfold not in *; intros H.
  pose proof Hocc as Hocc2.
  rewrite occ_in_alpha_exSO in Hocc.
  destruct P as [Pn]; destruct Q as [Qm].
  case_eq n.
    intros Hn; rewrite Hn in *; simpl in *;
    discriminate.

    intros m Hn.
    rewrite Hn in *.
    simpl in Hocc.
    case_eq m.
      intros Hm; rewrite Hm in *.
      simpl in Hbeq1.
      simpl in H.
      rewrite Hbeq1 in H.
      rewrite identify_fwd_0 in H.
      simpl in H; discriminate.

      intros j Hm.
      rewrite Hm in Hocc.
      simpl in Hocc.
      rewrite <- Hm in *.
      simpl in H.
      rewrite Hocc2 in H.
      rewrite Hm in Hbeq1.
      simpl in Hbeq1.
      rewrite arith_minus_zero in H.
      case_eq (beq_nat Pn Qm); intros Hbeq.
        rewrite Hbeq in *.
        apply (IHalpha m (Pred Pn)).
          rewrite <- Hm in Hbeq1; assumption.

          rewrite Hm; assumption.

          assumption.

          assumption.

        rewrite Hbeq in *.
        rewrite <- one_suc in H.
        simpl in *; discriminate.
Qed.

Lemma id_fwd_not  : forall (alpha : SecOrder) (n : nat) (P : predicate),
  match at_pred (preds_in alpha) n , P with
  | Pred Qm, Pred Pn => PeanoNat.Nat.eqb Pn Qm = false
  end ->
    beq_nat n 0 = false ->
      occ_in_alpha alpha n = true ->
        identify_fwd alpha P n <> 0.
Proof.
  induction alpha;
    intros n P Hbeq1 Hbeq2 Hocc;
    try destruct p as [Qm]; try destruct P as [Pn];
    try destruct f as [xn]; try destruct f0 as [xm];
    try (apply id_fwd_not_conjSO; assumption);
    try (apply id_fwd_not_allSO; assumption);
    try (apply id_fwd_not_exSO; assumption);
    unfold not in *; intros H;
    simpl in *; try rewrite Hocc in *.

    case_eq n.
      intros Hn; rewrite Hn in *.
      simpl in *; discriminate.

      intros m Hn; rewrite Hn in *.
      case_eq m.
        intros Hm; rewrite Hm in *.
        simpl in *.
        rewrite Hbeq1 in *.
        discriminate.

        intros j Hm; rewrite Hm in *.
        apply occ_in_alpha_predSO in Hocc.
        simpl in *; discriminate.

    rewrite occ_in_alpha_relatSO in Hocc;
    discriminate.

    rewrite occ_in_alpha_eqFO in Hocc;
    discriminate.

    rewrite occ_in_alpha_allFO in Hocc;
    apply (IHalpha n (Pred Pn)); assumption.

    rewrite occ_in_alpha_exFO in Hocc;
    apply (IHalpha n (Pred Pn)); assumption.

    rewrite occ_in_alpha_negSO in Hocc;
    apply (IHalpha n (Pred Pn)); assumption.
Qed.

Lemma ind_l_rev_app_length : forall (l1 l2 : list _) (P : predicate),
  length (indicies_l_rev (app l1 l2) P) =
    (length (indicies_l_rev l1 P)) +
      length (indicies_l_rev l2 P).
Proof.
  intros.
  rewrite indicies_l_rev_app.
  rewrite app_length.
  rewrite list_map_length.
  reflexivity.
Qed.


Lemma identify_fwd_rev_conjSO: forall (alpha1 alpha2 : SecOrder) (P : predicate) (i : nat),
  (forall (P : predicate) (i : nat),
     identify_fwd alpha1 P i <> 0 ->
       occ_in_alpha alpha1 i = true ->
         match at_pred (preds_in alpha1) i, P with
         | Pred Qm, Pred Pn => PeanoNat.Nat.eqb Pn Qm = false
         end ->
           identify_rev alpha1 P (identify_fwd alpha1 P i) = i) ->
   (forall (P : predicate) (i : nat),
     identify_fwd alpha2 P i <> 0 ->
       occ_in_alpha alpha2 i = true ->
         match at_pred (preds_in alpha2) i, P with
         | Pred Qm, Pred Pn => PeanoNat.Nat.eqb Pn Qm = false
         end ->
    identify_rev alpha2 P (identify_fwd alpha2 P i) = i) ->
      identify_fwd (conjSO alpha1 alpha2) P i <> 0 ->
        occ_in_alpha (conjSO alpha1 alpha2) i = true ->
          (match at_pred (preds_in (conjSO alpha1 alpha2)) i, P with
          | Pred Qm, Pred Pn => PeanoNat.Nat.eqb Pn Qm = false
           end) ->
       identify_rev (conjSO alpha1 alpha2) P
         (identify_fwd (conjSO alpha1 alpha2) P i) = i.
Proof.
  intros alpha1 alpha2 P i IHalpha1 IHalpha2 Hid Hocc Hbeq.
  pose proof (occ_in_alpha_conjSO2_fwd2 _ _ _ Hocc) as H.
  destruct H as [Hocc2 | Hocc2].
    unfold identify_rev.
    simpl in Hid; simpl.
    rewrite Hocc2 in *.
    rewrite Hocc in *.
    rewrite identify_rev_l_app.
      rewrite <- num_occ_ind_l_rev.
      rewrite leb_id_fwd; try assumption.
        unfold identify_rev in IHalpha1.
        apply IHalpha1; try assumption.
          simpl in Hbeq.
          rewrite at_pred_app_l in Hbeq.
            assumption.

            apply occ_in_alpha_leb2 in Hocc2.
            apply PeanoNat.Nat.leb_le.
            apply Hocc2.

      apply not_beq_nat.
      assumption.

      rewrite ind_l_rev_app_length.
      apply leb_plus_minus.
        rewrite <- num_occ_ind_l_rev.
        apply leb_id_fwd.
        assumption.

        rewrite <- num_occ_ind_l_rev.
        apply num_occ_preds_in.

        rewrite <- num_occ_ind_l_rev.
        apply num_occ_preds_in.

      destruct Hocc2 as [Hocc2 Hocc3].
      simpl in Hid.
      unfold identify_rev.
      simpl.
      rewrite identify_rev_l_app in *.
      rewrite Hocc2 in *.
      rewrite Hocc in *.
      rewrite <- arith_plus_minus_assoc2.
        assert (i = i - length (preds_in alpha1) 
                      + length (preds_in alpha1)) as Hi.
          rewrite arith_plus_minus_assoc.
            rewrite arith_minus_refl.
            rewrite arith_minus_zero.
            reflexivity.

          apply (occ_in_alpha_leb3 alpha2); assumption.

          apply leb_refl.
      case_eq (Nat.leb
    (identify_fwd alpha2 P (i - length (preds_in alpha1)) +
     (length (preds_in alpha1) - num_occ alpha1 P))
    (length (preds_in alpha1) -
     length (indicies_l_rev (preds_in alpha1) P))); intros Hleb2.
        rewrite arith_plus_comm in Hleb2.
        rewrite num_occ_ind_l_rev in Hleb2.
        rewrite leb_plus_l in Hleb2.
        rewrite leb_beq_zero in Hleb2.
        rewrite (beq_nat_true _ _ Hleb2).
        simpl.
        simpl in Hbeq.
        rewrite Hi in Hbeq.
        rewrite arith_plus_comm in Hbeq.
        rewrite at_pred_app_r in Hbeq.
        rewrite id_fwd_beq_nat in Hleb2.
          discriminate.

          assumption.

          assumption.

        apply occ_in_alpha_leb2 in Hocc3.
        apply Hocc3.

        rewrite  num_occ_ind_l_rev.
        rewrite <- arith_plus_minus_assoc2.
        rewrite arith_minus_refl.
        rewrite plus_zero.
        unfold identify_rev in IHalpha2.
        rewrite IHalpha2;
        try (simpl in Hbeq;
        rewrite Hi in Hbeq;
        rewrite arith_plus_comm in Hbeq;
        rewrite at_pred_app_r in Hbeq);
          try rewrite arith_plus_minus_assoc;
          try (rewrite arith_minus_refl;
          rewrite arith_minus_zero; reflexivity);
          try (apply occ_in_alpha_leb2 in Hocc3;
          apply Hocc3).
          apply occ_in_alpha_leb2 in Hocc3.
          destruct Hocc3 as [H1 H2].
          apply beq_nat_leb_f.
          assumption.

          apply leb_refl.
          apply id_fwd_not; try assumption. 
          apply occ_in_alpha_leb2 in Hocc3.
          apply Hocc3.

          assumption.
          assumption.
          apply leb_refl.
          apply num_occ_preds_in.

        rewrite Hocc in *.
        rewrite Hocc2 in *.
        apply not_true_is_false.
        apply (contrapos _ _ (beq_nat_true _ _)).
        assumption.

        rewrite Hocc in *.
        rewrite Hocc2 in *.
        rewrite indicies_l_rev_app.
        rewrite app_length.
        rewrite list_map_length.
        rewrite arith_plus_minus_rearr;
          try (rewrite <- num_occ_ind_l_rev; 
          apply num_occ_preds_in).
          rewrite (arith_plus_comm (length (preds_in alpha1)
                   - length (indicies_l_rev (preds_in alpha1) P))).
          rewrite num_occ_ind_l_rev.
          rewrite <- arith_plus_minus_assoc2.
          rewrite <- leb_plus.
          rewrite <- num_occ_ind_l_rev.
          apply leb_id_fwd; assumption.

          rewrite <- num_occ_ind_l_rev.
          apply num_occ_preds_in.
Qed.

Lemma identify_fwd_rev_allSO : forall (alpha : SecOrder) (P Q : predicate) (i : nat),
  (forall (P : predicate) (i : nat),
          identify_fwd alpha P i <> 0 ->
          occ_in_alpha alpha i = true ->
          match at_pred (preds_in alpha) i, P with
          | Pred Qm , Pred Pn => PeanoNat.Nat.eqb Pn Qm = false
          end -> identify_rev alpha P (identify_fwd alpha P i) = i) ->
    identify_fwd (allSO Q alpha) P i <> 0 ->
      occ_in_alpha (allSO Q alpha) i = true ->
        (match at_pred (preds_in (allSO Q alpha)) i , P with
         | Pred Qm, Pred Pn => PeanoNat.Nat.eqb Pn Qm = false
         end) ->
            identify_rev (allSO Q alpha) P 
               (identify_fwd (allSO Q alpha) P i) = i.
Proof.
  intros alpha P Q i IHalpha Hid Hocc Hbeq.
  simpl.
  destruct Q as [Qm]; destruct P as [Pn].
  rewrite Hocc.
  unfold identify_rev in *.
  simpl preds_in.
  rewrite identify_rev_l_cons.
  case_eq (beq_nat Pn Qm); intros Hbeq2.
    case_eq i.
      intros Hi; rewrite Hi in *.
      rewrite occ_in_alpha_0 in *.
      discriminate.

      intros j Hi.
      simpl.
      rewrite arith_minus_zero.
      case_eq j.
        intros Hj; rewrite Hj in *.
        rewrite Hi in Hbeq; simpl in Hbeq.
        rewrite Hbeq in Hbeq2; discriminate.
        intros k Hj.
        case_eq (identify_fwd alpha (Pred Pn) (S k)).
          intros H; simpl in Hbeq.
          rewrite Hj in *; rewrite Hi in *.
          simpl in Hbeq.
          pose proof (id_fwd_not alpha (S k) (Pred Pn) Hbeq) as H2.
          unfold not in H2; apply H2 in H.
          contradiction.

          simpl; reflexivity.

          rewrite occ_in_alpha_allSO in Hocc.
          simpl in Hocc.
          assumption.

          intros a H; rewrite <-H.
          rewrite IHalpha.
            reflexivity.

            rewrite H.
            unfold not; intros; discriminate.

            rewrite Hi in Hocc; simpl in Hocc.
            rewrite occ_in_alpha_allSO in Hocc.
            rewrite Hj in *; simpl in *.
            assumption.

            rewrite Hi in *; rewrite Hj in *.
            simpl in *; assumption.

    rewrite <- one_suc.
    case_eq i.
      intros Hi; rewrite Hi in *.
      rewrite occ_in_alpha_allSO in Hocc.
      simpl in *.
      unfold not in Hid; specialize (Hid (eq_refl _)).
      contradiction.

      intros j Hi.
      simpl.
      rewrite arith_minus_zero.
      case_eq j.
        intros Hj.
        rewrite identify_fwd_0.
        reflexivity.

        intros k Hj.
        case_eq (identify_fwd alpha (Pred Pn) (S k)).
          intros H.
          rewrite Hi in *.
          simpl in Hbeq.
          rewrite Hj in *.
          rewrite arith_minus_zero in Hbeq.
          simpl in Hid.
          rewrite Hocc in Hid.
          rewrite Hbeq2 in Hid.
          pose proof (id_fwd_not alpha (S k) (Pred Pn) Hbeq) as H2.
          simpl in H2; unfold not in H2.
          rewrite occ_in_alpha_allSO in Hocc.
          simpl in Hocc. 
          specialize (H2 (eq_refl _) Hocc H).
          contradiction.

          intros a H.
          rewrite <- H.
          rewrite IHalpha.
            reflexivity.

            rewrite Hi in *.
            rewrite <- Hj.
            simpl in Hid.
            rewrite Hocc in Hid.
            rewrite Hbeq2 in Hid.
            rewrite arith_minus_zero in Hid.
            apply id_fwd_not.
              simpl in Hbeq.
              rewrite Hj in *.
              rewrite <- Hj in *.
              rewrite arith_minus_zero in Hbeq.
              assumption.

              rewrite Hj; simpl; reflexivity.

              rewrite occ_in_alpha_allSO in Hocc.
              rewrite Hj in *.
              simpl in *.
              assumption.

              rewrite Hi in Hocc.
              rewrite occ_in_alpha_allSO in Hocc.
              rewrite Hj in Hocc.
              simpl in Hocc.
              assumption.

              simpl in Hbeq.
              rewrite Hi in *.
              rewrite Hj in *.
              simpl in Hbeq.
              assumption.

    case_eq (beq_nat Pn Qm); intros Hbeq2.
      case_eq i.
        intros Hi.
        rewrite Hi in *.
        rewrite occ_in_alpha_0 in Hocc; discriminate.

        intros j Hi.
        simpl.
        rewrite arith_minus_zero.
        case_eq j.
          intros Hj.
          rewrite Hj in *.
          rewrite Hi in *.
          simpl in Hbeq.
          rewrite Hbeq in Hbeq2.
          discriminate.

          intros k Hj.
          rewrite Hi in *.
          simpl in Hid.
          rewrite Hocc in Hid.
          rewrite Hbeq2 in Hid.
          rewrite arith_minus_zero in *.
          rewrite <- Hj.
          apply not_true_is_false.
          apply (contrapos _ _ (beq_nat_true _ _) Hid).

          rewrite <- one_suc.
          simpl; reflexivity.
Qed.


Lemma identify_fwd_rev : forall (alpha : SecOrder) (P : predicate) (i : nat),
  ~((identify_fwd alpha P i) = 0) ->
    occ_in_alpha alpha i = true ->
      match at_pred (preds_in alpha) i, P with
      | Pred Qm, Pred Pn => beq_nat Pn Qm = false
      end ->
        identify_rev alpha P (identify_fwd alpha P i) =  i.
Proof.
  intros alpha.
  induction alpha;
    intros P i Hid Hocc Hbeq;
    try destruct f as [xn]; try destruct f0 as [xm];
    [apply identify_fwd_rev_predSO; assumption | rewrite occ_in_alpha_relatSO in *|
      rewrite occ_in_alpha_eqFO in * | simpl in *; rewrite occ_in_alpha_allFO in * |
      simpl in *; rewrite occ_in_alpha_exFO in * | simpl in *; rewrite occ_in_alpha_negSO in * | | | | |];
    try (simpl in *; discriminate);
    try (simpl in *; rewrite Hocc in *; discriminate);
    try (apply IHalpha; assumption);
    try (unfold identify_rev in *; simpl; rewrite Hocc in *;
       apply IHalpha; assumption).
    apply identify_fwd_rev_conjSO; assumption.
    apply identify_fwd_rev_conjSO; assumption.
    apply identify_fwd_rev_conjSO; assumption.
    apply identify_fwd_rev_allSO; assumption.
    apply identify_fwd_rev_allSO; assumption.
Qed.

(* ---------------------------------------------------------------------- *)


Lemma occ_rep_pred2_relatSO : forall (cond: SecOrder) (Q : predicate)
                            (i : nat) (x1 x2 y: FOvariable),
  is_unary_predless cond = true ->
    occ_in_alpha (replace_pred (relatSO x1 x2) Q y cond) i = true ->
      occ_in_alpha (relatSO x1 x2) (identify_rev (relatSO x1 x2) Q i) = true.
Proof.
  intros cond Q i x1 x2 y Hun Hocc.
  destruct x1; destruct x2; destruct Q as [Qm].
  rewrite rep_pred_relatSO in Hocc.
  rewrite occ_in_alpha_relatSO in Hocc.
  discriminate.
Qed.


Lemma occ_rep_pred2_eqFO : forall (cond: SecOrder) (Q : predicate)
                            (i : nat) (x1 x2 y: FOvariable),
  is_unary_predless cond = true ->
    occ_in_alpha (replace_pred (eqFO x1 x2) Q y cond) i = true ->
      occ_in_alpha (eqFO x1 x2) (identify_rev (eqFO x1 x2) Q i) = true.
Proof.
  intros cond Q i x1 x2 y Hun Hocc.
  destruct x1; destruct x2; destruct Q as [Qm].
  rewrite rep_pred_eqFO in Hocc.
  rewrite occ_in_alpha_eqFO in Hocc.
  discriminate.
Qed.

(* ----------------------------------------------------------------------- *)

Lemma preds_in_rep_pred_allSO : forall (alpha cond : SecOrder) (P Q : predicate)
                                 (x : FOvariable),
  (length (preds_in (replace_pred alpha Q x cond)) =
          length (preds_in alpha) -
          length (indicies_l_rev (preds_in alpha) Q)) ->
    length (preds_in (replace_pred (allSO P alpha) Q x cond)) =
      length (preds_in (allSO P alpha)) -
        length (indicies_l_rev (preds_in (allSO P alpha)) Q).
Proof.
  intros alpha cond P Q x IHalpha.
  destruct P as [Pn]; destruct Q as [Qm].
  simpl.
  case_eq (beq_nat Pn Qm); intros Hbeq.
    rewrite (beq_nat_comm_t _ _ Hbeq).
    simpl; apply IHalpha.

    rewrite (beq_nat_comm_f _ _ Hbeq); simpl.
    pose proof (num_occ_preds_in alpha (Pred Qm)).
    unfold num_occ in H.
    rewrite length_ind in H.
    case_eq (length (indicies_l_rev (preds_in alpha) (Pred Qm))).
      intros H2;  rewrite H2 in *.
      rewrite arith_minus_zero in *.
      rewrite IHalpha; reflexivity.

      intros m H2; rewrite H2 in *.
      rewrite IHalpha.
      do 2 rewrite one_suc.
      rewrite arith_minus_exp.
      case_eq (length (preds_in alpha) - m).
        intros H3.
        rewrite one_suc in IHalpha; 
        rewrite arith_minus_exp in IHalpha.
        rewrite H3 in *.
        apply (leb_minus (length (preds_in alpha))) in H.
        rewrite arith_minus_refl in H.
        rewrite leb_beq_zero in H.
        apply beq_nat_leb in H.
        apply (leb_minus m) in H.
        rewrite one_suc in H; rewrite arith_plus_3 in H.
        rewrite H3 in *; simpl in *; discriminate.

        intros n H3; simpl.
        rewrite arith_minus_zero; rewrite <- one_suc.
        reflexivity.
Qed.

Lemma preds_in_rep_pred_exSO : forall (alpha cond : SecOrder) (P Q : predicate)
                                 (x : FOvariable),
  (length (preds_in (replace_pred alpha Q x cond)) =
          length (preds_in alpha) -
          length (indicies_l_rev (preds_in alpha) Q)) ->
    length (preds_in (replace_pred (exSO P alpha) Q x cond)) =
      length (preds_in (exSO P alpha)) -
        length (indicies_l_rev (preds_in (exSO P alpha)) Q).
Proof.
  intros alpha cond P Q x IHalpha.
  destruct P as [Pn]; destruct Q as [Qm].
  simpl.
  case_eq (beq_nat Pn Qm); intros Hbeq.
    rewrite (beq_nat_comm_t _ _ Hbeq).
    simpl; apply IHalpha.

    rewrite (beq_nat_comm_f _ _ Hbeq); simpl.
    pose proof (num_occ_preds_in alpha (Pred Qm)).
    unfold num_occ in H.
    rewrite length_ind in H.
    case_eq (length (indicies_l_rev (preds_in alpha) (Pred Qm))).
      intros H2;  rewrite H2 in *.
      rewrite arith_minus_zero in *.
      rewrite IHalpha; reflexivity.

      intros m H2; rewrite H2 in *.
      rewrite IHalpha.
      do 2 rewrite one_suc.
      rewrite arith_minus_exp.
      case_eq (length (preds_in alpha) - m).
        intros H3.
        rewrite one_suc in IHalpha; 
        rewrite arith_minus_exp in IHalpha.
        rewrite H3 in *.
        apply (leb_minus (length (preds_in alpha))) in H.
        rewrite arith_minus_refl in H.
        rewrite leb_beq_zero in H.
        apply beq_nat_leb in H.
        apply (leb_minus m) in H.
        rewrite one_suc in H; rewrite arith_plus_3 in H.
        rewrite H3 in *; simpl in *; discriminate.

        intros n H3; simpl.
        rewrite arith_minus_zero; rewrite <- one_suc.
        reflexivity.
Qed.


Lemma preds_in_rep_pred : forall (alpha cond : SecOrder) (Q : predicate)
                                 (x : FOvariable),
  is_unary_predless cond = true ->
    (length (preds_in (replace_pred alpha Q x cond)))
      = length (preds_in alpha) - num_occ alpha Q.
Proof.
  intros alpha cond Q x Hcond.
  unfold num_occ.
  rewrite length_ind.
  induction alpha;
    try destruct p as [Pn]; try destruct Q as [Qm];
    try destruct f as [xn]; try destruct f0 as [xm];
    try (simpl; reflexivity);
    try (simpl; rewrite IHalpha; reflexivity);
    try (      simpl; rewrite indicies_l_rev_app;
      do 3 rewrite app_length;
      rewrite list_map_length;
      rewrite IHalpha1; rewrite IHalpha2;
      pose proof num_occ_preds_in as H;
      unfold num_occ in H;
      rewrite arith_plus_minus_rearr;
        try (rewrite <- length_ind; apply H);
        reflexivity).
      simpl; rewrite beq_nat_comm; case_eq (beq_nat Pn Qm); intros Hbeq.
      rewrite un_predless_preds_in.
        reflexivity.

        apply rep_FOv_is_unary_predless.
        assumption.

      reflexivity.

    apply preds_in_rep_pred_allSO; assumption.
    apply preds_in_rep_pred_exSO; assumption.
Qed.

(* ---------------------------------------------------------------------------- *)

Lemma id_rev_conjSO_l : forall (alpha1 alpha2 cond : SecOrder)
                             (Q : predicate) (x : FOvariable) (i : nat),
  is_unary_predless cond = true ->
    occ_in_alpha (replace_pred alpha1 Q x cond) i = true ->
      (identify_rev (conjSO alpha1 alpha2) Q i) =
         identify_rev alpha1 Q i.
Proof.
  intros alpha1 alpha2 cond Q x i Hun Hocc.
  unfold identify_rev.
  simpl.
  pose proof (num_occ_preds_in) as Hl.
  unfold num_occ in Hl.
  apply occ_in_alpha_leb2 in Hocc.
  destruct Hocc as [H1 H2].
  rewrite identify_rev_l_app.
    pose proof (preds_in_rep_pred alpha1 cond Q x Hun).
    rewrite <- length_ind.
    unfold num_occ in H.
    rewrite <- H.
    rewrite H2.
    reflexivity.

    assumption.
    rewrite indicies_l_rev_app.
    rewrite app_length.
    rewrite list_map_length.
    rewrite arith_plus_minus_rearr.
      rewrite preds_in_rep_pred in H2.
        unfold num_occ in H2.
        do 2 rewrite <- length_ind.
        apply leb_plus_r.
        assumption.

        assumption.

        rewrite <- length_ind; apply Hl.

        rewrite <- length_ind; apply Hl.
Qed.

Lemma id_rev_disjSO_l : forall (alpha1 alpha2 cond : SecOrder)
                             (Q : predicate) (x : FOvariable) (i : nat),
  is_unary_predless cond = true ->
    occ_in_alpha (replace_pred alpha1 Q x cond) i = true ->
      (identify_rev (disjSO alpha1 alpha2) Q i) =
         identify_rev alpha1 Q i.
Proof.
  intros alpha1 alpha2 cond Q x i Hun Hocc.
  unfold identify_rev.
  simpl.
  pose proof (num_occ_preds_in) as Hl.
  unfold num_occ in Hl.
  apply occ_in_alpha_leb2 in Hocc.
  destruct Hocc as [H1 H2].
  rewrite identify_rev_l_app.
    pose proof (preds_in_rep_pred alpha1 cond Q x Hun).
    rewrite <- length_ind.
    unfold num_occ in H.
    rewrite <- H.
    rewrite H2.
    reflexivity.

    assumption.
    rewrite indicies_l_rev_app.
    rewrite app_length.
    rewrite list_map_length.
    rewrite arith_plus_minus_rearr.
      rewrite preds_in_rep_pred in H2.
        unfold num_occ in H2.
        do 2 rewrite <- length_ind.
        apply leb_plus_r.
        assumption.

        assumption.

        rewrite <- length_ind; apply Hl.

        rewrite <- length_ind; apply Hl.
Qed.

Lemma id_rev_implSO_l : forall (alpha1 alpha2 cond : SecOrder)
                             (Q : predicate) (x : FOvariable) (i : nat),
  is_unary_predless cond = true ->
    occ_in_alpha (replace_pred alpha1 Q x cond) i = true ->
      (identify_rev (implSO alpha1 alpha2) Q i) =
         identify_rev alpha1 Q i.
Proof.
  intros alpha1 alpha2 cond Q x i Hun Hocc.
  unfold identify_rev.
  simpl.
  pose proof (num_occ_preds_in) as Hl.
  unfold num_occ in Hl.
  apply occ_in_alpha_leb2 in Hocc.
  destruct Hocc as [H1 H2].
  rewrite identify_rev_l_app.
    pose proof (preds_in_rep_pred alpha1 cond Q x Hun).
    rewrite <- length_ind.
    unfold num_occ in H.
    rewrite <- H.
    rewrite H2.
    reflexivity.

    assumption.
    rewrite indicies_l_rev_app.
    rewrite app_length.
    rewrite list_map_length.
    rewrite arith_plus_minus_rearr.
      rewrite preds_in_rep_pred in H2.
        unfold num_occ in H2.
        do 2 rewrite <- length_ind.
        apply leb_plus_r.
        assumption.

        assumption.

        rewrite <- length_ind; apply Hl.

        rewrite <- length_ind; apply Hl.
Qed.


Lemma id_rev_conjSO_r : forall (alpha1 alpha2 cond : SecOrder)
                             (Q : predicate) (x : FOvariable) (i : nat),
  is_unary_predless cond = true ->
    occ_in_alpha (replace_pred alpha1 Q x cond) i = false ->
      occ_in_alpha (replace_pred alpha2 Q x cond)
         (i - length (preds_in (replace_pred alpha1 Q x cond))) = true ->
      (identify_rev (conjSO alpha1 alpha2) Q i) =
         identify_rev alpha2 Q 
            (i - length (preds_in (replace_pred alpha1 Q x cond)))
             + length (preds_in alpha1).
Proof.
  intros alpha1 alpha2 cond Q x i Hun Hocc1 Hocc2.
  unfold identify_rev.
  simpl.
  case_eq (beq_nat i 0); intros Hbeq.
    rewrite (beq_nat_true _ _ Hbeq) in *; simpl in *; discriminate.
  pose proof (num_occ_preds_in) as Hl.
  unfold num_occ in Hl.
  apply occ_in_alpha_leb2 in Hocc2.
  destruct Hocc2 as [H1 H2].
  rewrite identify_rev_l_app.
  pose proof H1 as Hocc2a.
  apply beq_nat_leb_f in H1.
  apply leb_switch2 in H1.
    rewrite preds_in_rep_pred in *; try assumption.
    unfold num_occ in *.
    rewrite length_ind in *.
    rewrite H1.
    reflexivity.

    case_eq (beq_nat (length (preds_in (replace_pred alpha1 Q x cond))) i);
      intros Hbeq2.
      rewrite (beq_nat_true _ _ Hbeq2) in Hocc2a.
      rewrite arith_minus_refl in Hocc2a.
      simpl in *; discriminate.

      reflexivity.

    case_eq (beq_nat i 0); intros Hbeq2.
      rewrite (beq_nat_true _ _ Hbeq2) in *; simpl in *; discriminate.

      reflexivity.

    rewrite indicies_l_rev_app.
    rewrite app_length.
    rewrite list_map_length.
    pose proof H2 as H.
    rewrite arith_plus_minus_rearr.
      do 2 rewrite preds_in_rep_pred in H2; try assumption.
      unfold num_occ in H2.
      do 2 rewrite length_ind in H2.
      rewrite (leb_plus _ _ (length (preds_in alpha1) - length 
                (indicies_l_rev (preds_in alpha1) Q))) in H2. 
      rewrite arith_plus_minus_assoc in H2.
      rewrite arith_minus_refl in H2.
      rewrite arith_minus_zero in H2.
      rewrite arith_plus_comm.
      assumption.

      unfold occ_in_alpha in Hocc1.
      rewrite Hbeq in *.
      case_eq (Nat.leb i (length (preds_in (replace_pred alpha1 Q x cond))));
        intros Hleb.
        rewrite Hleb in *; discriminate.

        apply leb_switch.
        rewrite preds_in_rep_pred in Hleb.
        unfold num_occ in Hleb.
        rewrite length_ind in Hleb.
        assumption.

        assumption.

        apply leb_refl.

        rewrite <- length_ind.
        apply Hl.

        rewrite <- length_ind.
        apply Hl.
Qed.

Lemma id_rev_implSO_r : forall (alpha1 alpha2 cond : SecOrder)
                             (Q : predicate) (x : FOvariable) (i : nat),
  is_unary_predless cond = true ->
    occ_in_alpha (replace_pred alpha1 Q x cond) i = false ->
      occ_in_alpha (replace_pred alpha2 Q x cond)
         (i - length (preds_in (replace_pred alpha1 Q x cond))) = true ->
      (identify_rev (implSO alpha1 alpha2) Q i) =
         identify_rev alpha2 Q 
            (i - length (preds_in (replace_pred alpha1 Q x cond)))
             + length (preds_in alpha1).
Proof.
  intros alpha1 alpha2 cond Q x i Hun Hocc1 Hocc2.
  unfold identify_rev.
  simpl.
  case_eq (beq_nat i 0); intros Hbeq.
    rewrite (beq_nat_true _ _ Hbeq) in *; simpl in *; discriminate.
  pose proof (num_occ_preds_in) as Hl.
  unfold num_occ in Hl.
  apply occ_in_alpha_leb2 in Hocc2.
  destruct Hocc2 as [H1 H2].
  rewrite identify_rev_l_app.
  pose proof H1 as Hocc2a.
  apply beq_nat_leb_f in H1.
  apply leb_switch2 in H1.
    rewrite preds_in_rep_pred in *; try assumption.
    unfold num_occ in *.
    rewrite length_ind in *.
    rewrite H1.
    reflexivity.

    case_eq (beq_nat (length (preds_in (replace_pred alpha1 Q x cond))) i);
      intros Hbeq2.
      rewrite (beq_nat_true _ _ Hbeq2) in Hocc2a.
      rewrite arith_minus_refl in Hocc2a.
      simpl in *; discriminate.

      reflexivity.

    case_eq (beq_nat i 0); intros Hbeq2.
      rewrite (beq_nat_true _ _ Hbeq2) in *; simpl in *; discriminate.

      reflexivity.

    rewrite indicies_l_rev_app.
    rewrite app_length.
    rewrite list_map_length.
    pose proof H2 as H.
    rewrite arith_plus_minus_rearr.
      do 2 rewrite preds_in_rep_pred in H2; try assumption.
      unfold num_occ in H2.
      do 2 rewrite length_ind in H2.
      rewrite (leb_plus _ _ (length (preds_in alpha1) - length 
                (indicies_l_rev (preds_in alpha1) Q))) in H2. 
      rewrite arith_plus_minus_assoc in H2.
      rewrite arith_minus_refl in H2.
      rewrite arith_minus_zero in H2.
      rewrite arith_plus_comm.
      assumption.

      unfold occ_in_alpha in Hocc1.
      rewrite Hbeq in *.
      case_eq (Nat.leb i (length (preds_in (replace_pred alpha1 Q x cond))));
        intros Hleb.
        rewrite Hleb in *; discriminate.

        apply leb_switch.
        rewrite preds_in_rep_pred in Hleb.
        unfold num_occ in Hleb.
        rewrite length_ind in Hleb.
        assumption.

        assumption.

        apply leb_refl.

        rewrite <- length_ind.
        apply Hl.

        rewrite <- length_ind.
        apply Hl.
Qed.



Lemma id_rev_disjSO_r : forall (alpha1 alpha2 cond : SecOrder)
                             (Q : predicate) (x : FOvariable) (i : nat),
  is_unary_predless cond = true ->
    occ_in_alpha (replace_pred alpha1 Q x cond) i = false ->
      occ_in_alpha (replace_pred alpha2 Q x cond)
         (i - length (preds_in (replace_pred alpha1 Q x cond))) = true ->
      (identify_rev (disjSO alpha1 alpha2) Q i) =
         identify_rev alpha2 Q 
            (i - length (preds_in (replace_pred alpha1 Q x cond)))
             + length (preds_in alpha1).
Proof.
  intros alpha1 alpha2 cond Q x i Hun Hocc1 Hocc2.
  unfold identify_rev.
  simpl.
  case_eq (beq_nat i 0); intros Hbeq.
    rewrite (beq_nat_true _ _ Hbeq) in *; simpl in *; discriminate.
  pose proof (num_occ_preds_in) as Hl.
  unfold num_occ in Hl.
  apply occ_in_alpha_leb2 in Hocc2.
  destruct Hocc2 as [H1 H2].
  rewrite identify_rev_l_app.
  pose proof H1 as Hocc2a.
  apply beq_nat_leb_f in H1.
  apply leb_switch2 in H1.
    rewrite preds_in_rep_pred in *; try assumption.
    unfold num_occ in *.
    rewrite length_ind in *.
    rewrite H1.
    reflexivity.

    case_eq (beq_nat (length (preds_in (replace_pred alpha1 Q x cond))) i);
      intros Hbeq2.
      rewrite (beq_nat_true _ _ Hbeq2) in Hocc2a.
      rewrite arith_minus_refl in Hocc2a.
      simpl in *; discriminate.

      reflexivity.

    case_eq (beq_nat i 0); intros Hbeq2.
      rewrite (beq_nat_true _ _ Hbeq2) in *; simpl in *; discriminate.

      reflexivity.

    rewrite indicies_l_rev_app.
    rewrite app_length.
    rewrite list_map_length.
    pose proof H2 as H.
    rewrite arith_plus_minus_rearr.
      do 2 rewrite preds_in_rep_pred in H2; try assumption.
      unfold num_occ in H2.
      do 2 rewrite length_ind in H2.
      rewrite (leb_plus _ _ (length (preds_in alpha1) - length 
                (indicies_l_rev (preds_in alpha1) Q))) in H2. 
      rewrite arith_plus_minus_assoc in H2.
      rewrite arith_minus_refl in H2.
      rewrite arith_minus_zero in H2.
      rewrite arith_plus_comm.
      assumption.

      unfold occ_in_alpha in Hocc1.
      rewrite Hbeq in *.
      case_eq (Nat.leb i (length (preds_in (replace_pred alpha1 Q x cond))));
        intros Hleb.
        rewrite Hleb in *; discriminate.

        apply leb_switch.
        rewrite preds_in_rep_pred in Hleb.
        unfold num_occ in Hleb.
        rewrite length_ind in Hleb.
        assumption.

        assumption.

        apply leb_refl.

        rewrite <- length_ind.
        apply Hl.

        rewrite <- length_ind.
        apply Hl.
Qed.


Lemma occ_rep_pred2_predSO : forall (cond: SecOrder) (P Q : predicate)
                            (i : nat) (x y: FOvariable),
  is_unary_predless cond = true ->
    occ_in_alpha (replace_pred (predSO P y) Q x cond) i = true ->
      occ_in_alpha (predSO P y) (identify_rev (predSO P y) Q i) = true. 
Proof.
  intros cond P Q i x y Hun Hocc.
  simpl in *.
  destruct Q as [Qm]; destruct P as [Pn].
  destruct y as [xn].
  case_eq (beq_nat i 0); intros Hbeq.
    rewrite (beq_nat_true _ _ Hbeq) in *.
    rewrite occ_in_alpha_0 in Hocc; discriminate.

    rewrite identify_rev_predSO.
    unfold occ_in_alpha.
      simpl; reflexivity.

      assumption.
Qed.


Lemma occ_rep_pred2_conjSO : forall (alpha1 alpha2 cond : SecOrder)
                                    (Q : predicate) (i : nat)
                                    (x : FOvariable),
  (forall (cond : SecOrder) (Q : predicate) (i : nat) (x : FOvariable),
           is_unary_predless cond = true ->
           occ_in_alpha (replace_pred alpha1 Q x cond) i = true ->
           occ_in_alpha alpha1 (identify_rev alpha1 Q i) = true) ->
  (forall (cond : SecOrder) (Q : predicate) (i : nat) (x : FOvariable),
           is_unary_predless cond = true ->
           occ_in_alpha (replace_pred alpha2 Q x cond) i = true ->
           occ_in_alpha alpha2 (identify_rev alpha2 Q i) = true) ->
    is_unary_predless cond = true ->
      occ_in_alpha (replace_pred (conjSO alpha1 alpha2) Q x cond) i = true ->
        occ_in_alpha (conjSO alpha1 alpha2) 
           (identify_rev (conjSO alpha1 alpha2) Q i) = true.
Proof.
  intros alpha1 alpha2 cond Q i x IHalpha1 IHalpha2 Hun Hocc.
  rewrite rep_pred_conjSO in Hocc.
  apply occ_in_alpha_conjSO2_fwd2 in Hocc.
  destruct Hocc.
    rewrite (id_rev_conjSO_l _ _ cond _ x); try assumption.
      rewrite occ_in_alpha_conjSO2; try assumption.
        left.
        apply (IHalpha1 cond _ _ x); assumption.

    destruct H as [H1 H2].
    apply occ_in_alpha_conjSO2_rev.
    right.
    rewrite (id_rev_conjSO_r _ _ cond _ x); try assumption.
    rewrite arith_plus_comm.
    rewrite arith_plus_3.
    apply (IHalpha2 cond _ _ x); assumption.
Qed.



Lemma occ_rep_pred2_disjSO : forall (alpha1 alpha2 cond : SecOrder)
                                    (Q : predicate) (i : nat)
                                    (x : FOvariable),
  (forall (cond : SecOrder) (Q : predicate) (i : nat) (x : FOvariable),
           is_unary_predless cond = true ->
           occ_in_alpha (replace_pred alpha1 Q x cond) i = true ->
           occ_in_alpha alpha1 (identify_rev alpha1 Q i) = true) ->
  (forall (cond : SecOrder) (Q : predicate) (i : nat) (x : FOvariable),
           is_unary_predless cond = true ->
           occ_in_alpha (replace_pred alpha2 Q x cond) i = true ->
           occ_in_alpha alpha2 (identify_rev alpha2 Q i) = true) ->
    is_unary_predless cond = true ->
      occ_in_alpha (replace_pred (disjSO alpha1 alpha2) Q x cond) i = true ->
        occ_in_alpha (disjSO alpha1 alpha2) 
           (identify_rev (disjSO alpha1 alpha2) Q i) = true.
Proof.
  intros alpha1 alpha2 cond Q i x IHalpha1 IHalpha2 Hun Hocc.
  rewrite rep_pred_disjSO in Hocc.
  apply occ_in_alpha_conjSO2_fwd2 in Hocc.
  destruct Hocc.
    rewrite (id_rev_disjSO_l _ _ cond _ x); try assumption.
      rewrite occ_in_alpha_disjSO2; left; try assumption.
        apply (IHalpha1 cond _ _ x); assumption.

    destruct H as [H1 H2].
    apply occ_in_alpha_conjSO2_rev.
    right.
    rewrite (id_rev_disjSO_r _ _ cond _ x); try assumption.
    rewrite arith_plus_comm.
    rewrite arith_plus_3.
    apply (IHalpha2 cond _ _ x); assumption.
Qed.

Lemma occ_rep_pred2_implSO : forall (alpha1 alpha2 cond : SecOrder)
                                    (Q : predicate) (i : nat)
                                    (x : FOvariable),
  (forall (cond : SecOrder) (Q : predicate) (i : nat) (x : FOvariable),
           is_unary_predless cond = true ->
           occ_in_alpha (replace_pred alpha1 Q x cond) i = true ->
           occ_in_alpha alpha1 (identify_rev alpha1 Q i) = true) ->
  (forall (cond : SecOrder) (Q : predicate) (i : nat) (x : FOvariable),
           is_unary_predless cond = true ->
           occ_in_alpha (replace_pred alpha2 Q x cond) i = true ->
           occ_in_alpha alpha2 (identify_rev alpha2 Q i) = true) ->
    is_unary_predless cond = true ->
      occ_in_alpha (replace_pred (implSO alpha1 alpha2) Q x cond) i = true ->
        occ_in_alpha (implSO alpha1 alpha2) 
           (identify_rev (implSO alpha1 alpha2) Q i) = true.
Proof.
  intros alpha1 alpha2 cond Q i x IHalpha1 IHalpha2 Hun Hocc.
  rewrite rep_pred_implSO in Hocc.
  apply occ_in_alpha_conjSO2_fwd2 in Hocc.
  destruct Hocc.
    rewrite (id_rev_implSO_l _ _ cond _ x); try assumption.
      rewrite occ_in_alpha_implSO2; left; try assumption.
        apply (IHalpha1 cond _ _ x); assumption.

    destruct H as [H1 H2].
    apply occ_in_alpha_conjSO2_rev.
    right.
    rewrite (id_rev_implSO_r _ _ cond _ x); try assumption.
    rewrite arith_plus_comm.
    rewrite arith_plus_3.
    apply (IHalpha2 cond _ _ x); assumption.
Qed.

Lemma occ_rep_pred2_allSO : forall (alpha cond : SecOrder) (P Q : predicate)
                                    (x : FOvariable) (i : nat),
    (forall (cond : SecOrder) (Q : predicate) (i : nat) (x : FOvariable),
          is_unary_predless cond = true ->
          occ_in_alpha (replace_pred alpha Q x cond) i = true ->
          occ_in_alpha alpha (identify_rev alpha Q i) = true) ->
    is_unary_predless cond = true ->
      (occ_in_alpha (replace_pred (allSO P alpha) Q x cond) i = true) ->
        (occ_in_alpha (allSO P alpha) 
              (identify_rev (allSO P alpha) Q i) = true).
Proof.
  intros alpha cond P Q x i IHalpha Hun Hocc.
  destruct P as [Pn]; destruct Q as [Qm].
  rewrite occ_in_alpha_allSO.
  rewrite rep_pred_allSO in Hocc.
  unfold identify_rev; simpl.
  case_eq (beq_nat Qm Pn); intros Hbeq.
    rewrite (beq_nat_comm_t _ _ Hbeq) in *.
    case_eq i.
      intros Hi; rewrite Hi in *.
      rewrite occ_in_alpha_0 in Hocc; discriminate.

      intros n Hi; rewrite Hi in *.
      simpl; rewrite arith_minus_zero.
      destruct (occ_in_alpha_leb2 _ _ Hocc) as [Hbeq2 Hleb].
      rewrite preds_in_rep_pred in Hleb; try assumption.
      unfold num_occ in Hleb.
      rewrite length_ind in Hleb. 
      case_eq (beq_nat (identify_rev_l (preds_in alpha)
                  (Pred Qm) (S n)) 0); intros Hbeq3.
        reflexivity.

        unfold identify_rev in IHalpha.
        rewrite (IHalpha cond _ _ x); try assumption.
          reflexivity.

          rewrite (beq_nat_true _ _ Hbeq).
          assumption.

    rewrite (beq_nat_comm_f _ _ Hbeq) in *.
    rewrite occ_in_alpha_allSO in Hocc.
    case_eq i.
      intros Hi; rewrite Hi in *; simpl in *.
      rewrite occ_in_alpha_0 in Hocc.
      discriminate.

      intros n Hi; rewrite Hi in *.
      simpl.
      case_eq (identify_rev_l (preds_in alpha) (Pred Qm) n).
        reflexivity.

        intros m H; simpl.
        rewrite <- H.
        unfold identify_rev in IHalpha.
        rewrite (IHalpha cond _ _ x); try assumption.
          reflexivity.

          case_eq n.
            intros Hn; rewrite Hn in *.
            rewrite identify_rev_l_0 in H.
            discriminate.

            intros j Hn; rewrite Hn in *.
            simpl in *; assumption.
Qed.

Lemma occ_rep_pred2_exSO : forall (alpha cond : SecOrder) (P Q : predicate)
                                    (x : FOvariable) (i : nat),
    (forall (cond : SecOrder) (Q : predicate) (i : nat) (x : FOvariable),
          is_unary_predless cond = true ->
          occ_in_alpha (replace_pred alpha Q x cond) i = true ->
          occ_in_alpha alpha (identify_rev alpha Q i) = true) ->
    is_unary_predless cond = true ->
      (occ_in_alpha (replace_pred (exSO P alpha) Q x cond) i = true) ->
        (occ_in_alpha (exSO P alpha) 
              (identify_rev (exSO P alpha) Q i) = true).
Proof.
  intros alpha cond P Q x i IHalpha Hun Hocc.
  destruct P as [Pn]; destruct Q as [Qm].
  rewrite occ_in_alpha_exSO.
  rewrite rep_pred_exSO in Hocc.
  unfold identify_rev; simpl.
  case_eq (beq_nat Qm Pn); intros Hbeq.
    rewrite (beq_nat_comm_t _ _ Hbeq) in *.
    case_eq i.
      intros Hi; rewrite Hi in *.
      rewrite occ_in_alpha_0 in Hocc; discriminate.

      intros n Hi; rewrite Hi in *.
      simpl; rewrite arith_minus_zero.
      destruct (occ_in_alpha_leb2 _ _ Hocc) as [Hbeq2 Hleb].
      rewrite preds_in_rep_pred in Hleb; try assumption.
      unfold num_occ in Hleb.
      rewrite length_ind in Hleb. 
      case_eq (beq_nat (identify_rev_l (preds_in alpha)
                  (Pred Qm) (S n)) 0); intros Hbeq3.
        reflexivity.

        unfold identify_rev in IHalpha.
        rewrite (IHalpha cond _ _ x); try assumption.
          reflexivity.

          rewrite (beq_nat_true _ _ Hbeq).
          assumption.

    rewrite (beq_nat_comm_f _ _ Hbeq) in *.
    rewrite occ_in_alpha_exSO in Hocc.
    case_eq i.
      intros Hi; rewrite Hi in *; simpl in *.
      rewrite occ_in_alpha_0 in Hocc.
      discriminate.

      intros n Hi; rewrite Hi in *.
      simpl.
      case_eq (identify_rev_l (preds_in alpha) (Pred Qm) n).
        reflexivity.

        intros m H; simpl.
        rewrite <- H.
        unfold identify_rev in IHalpha.
        rewrite (IHalpha cond _ _ x); try assumption.
          reflexivity.

          case_eq n.
            intros Hn; rewrite Hn in *.
            rewrite identify_rev_l_0 in H.
            discriminate.

            intros j Hn; rewrite Hn in *.
            simpl in *; assumption.
Qed.

Lemma occ_rep_pred2 : forall (alpha cond: SecOrder) (Q : predicate)
                            (i : nat) (x : FOvariable),
  is_unary_predless cond = true ->
    occ_in_alpha (replace_pred alpha Q x cond) i = true ->
      occ_in_alpha alpha (identify_rev alpha Q i) = true. 
Proof.
  induction alpha;
    intros cond Q i x Hun Hocc.
    apply (occ_rep_pred2_predSO cond _ _ _ x); assumption.
    apply (occ_rep_pred2_relatSO cond _ _ _ _ x); assumption.
    apply (occ_rep_pred2_eqFO cond _ _ _ _ x); assumption.

    destruct f as [xn]; destruct Q as [Qm].
    rewrite identify_rev_allFO.
    rewrite rep_pred_allFO in Hocc.
    rewrite occ_in_alpha_allFO in *.
    apply (IHalpha cond _ _ x); assumption.

    destruct f as [xn]; destruct Q as [Qm].
    rewrite identify_rev_exFO.
    rewrite rep_pred_exFO in Hocc.
    rewrite occ_in_alpha_exFO in *.
    apply (IHalpha cond _ _ x); assumption.

    rewrite rep_pred_negSO in Hocc.
    rewrite identify_rev_negSO.
    rewrite occ_in_alpha_negSO in *.
    apply (IHalpha cond _ _ x); assumption.

    apply (occ_rep_pred2_conjSO _ _ cond _ _ x); assumption.
    apply (occ_rep_pred2_disjSO _ _ cond _ _ x); assumption.
    apply (occ_rep_pred2_implSO _ _ cond _ _ x); assumption.
    apply (occ_rep_pred2_allSO _ cond _ _ x); assumption.
    apply (occ_rep_pred2_exSO _ cond _ _ x); assumption.
Qed.

(* --------------------------------------------------------------------- *)

Lemma id_rev_1_predSO : forall (cond : SecOrder) (i : nat) (P Q : predicate) (x y : FOvariable),
  is_unary_predless cond = true ->
    occ_in_alpha (replace_pred (predSO P y) Q x cond) i = true -> 
      identify_rev (predSO P y) Q i = 1 -> 
        i = 0 \/ i = 1.
Proof.
  intros cond i P Q x y Hun Hocc Hid.
  destruct P as [Pn]; destruct Q as [Qm];
  destruct x as [xn]; destruct y as [ym].
  unfold occ_in_alpha in *; unfold identify_rev in *.
  case_eq (beq_nat i 0); intros Hbeq; rewrite Hbeq in *.
    discriminate.

    simpl in *.
    case_eq i.
      intros; left; reflexivity.

      intros j Hi; rewrite Hi in *.
      case_eq (beq_nat Qm Pn); intros Hbeq2; rewrite Hbeq2 in *.
        simpl in *.
        pose proof (un_predless_preds_in _
                    (rep_FOv_is_unary_predless cond (Var xn) (Var ym) Hun)) as H.
        rewrite H in *.
        simpl in *.
        discriminate.

        simpl in *.
        case_eq j.
          intros Hj; right; reflexivity.

          intros k Hj; rewrite Hj in *; simpl in *; discriminate.
Qed.

Lemma id_rev_1_allFO : forall (alpha cond : SecOrder) (i : nat) (Q : predicate) (x y : FOvariable),
  (forall (cond : SecOrder) (i : nat) (Q : predicate) (x : FOvariable),
          is_unary_predless cond = true ->
          occ_in_alpha (replace_pred alpha Q x cond) i = true -> 
          identify_rev alpha Q i = 1 -> i = 0 \/ i = 1) ->
    is_unary_predless cond = true ->
      occ_in_alpha (replace_pred (allFO y alpha) Q x cond) i = true ->
        identify_rev (allFO y alpha) Q i = 1 ->
            i = 0 \/ i = 1.
Proof.
  intros alpha cond i Q x y IHalpha Hun Hocc Hid.
  rewrite rep_pred_allFO in Hocc.
  rewrite occ_in_alpha_allFO in Hocc.
  unfold identify_rev in *.
  simpl in Hid.
  specialize (IHalpha cond i Q x Hun Hocc Hid).
  assumption.
Qed.

Lemma id_rev_1_negSO : forall (alpha cond : SecOrder) (i : nat) (Q : predicate) (x y : FOvariable),
  (forall (cond : SecOrder) (i : nat) (Q : predicate) (x : FOvariable),
          is_unary_predless cond = true ->
          occ_in_alpha (replace_pred alpha Q x cond) i = true -> 
          identify_rev alpha Q i = 1 -> i = 0 \/ i = 1) ->
    is_unary_predless cond = true ->
      occ_in_alpha (replace_pred (negSO alpha) Q x cond) i = true ->
        identify_rev (negSO alpha) Q i = 1 ->
            i = 0 \/ i = 1.
Proof.
  intros alpha cond i Q x y IHalpha Hun Hocc Hid.
  rewrite rep_pred_negSO in Hocc.
  rewrite occ_in_alpha_negSO in Hocc.
  unfold identify_rev in *.
  simpl in Hid.
  specialize (IHalpha cond i Q x Hun Hocc Hid).
  assumption.
Qed.


Lemma id_rev_0 : forall (alpha : SecOrder) (Q : predicate ) (i : nat),
  is_unary_predless alpha = false ->
  identify_rev alpha Q i = 0 ->
    i = 0.
Proof.
  unfold identify_rev.
  intros alpha Q i Hun Hid.
 apply un_predless_preds_in_f in Hun.
  case_eq i.
    reflexivity.

    intros j Hi; rewrite Hi in *.
    case_eq (preds_in alpha).
      intros H; rewrite H in *.
      simpl in *.
      unfold not in Hun; specialize (Hun (eq_refl _)).
      contradiction.

      intros P l Hl.
      rewrite Hl in *.
      simpl in *.
      destruct P as [Pn]; destruct Q as [Qm].
      discriminate.
Qed.

Lemma id_rev_1_conjSO : forall (alpha1 alpha2 cond : SecOrder) (i : nat) (Q : predicate) (x : FOvariable),
  (forall (cond : SecOrder) (i : nat) (Q : predicate) (x : FOvariable),
           is_unary_predless cond = true ->
           occ_in_alpha (replace_pred alpha1 Q x cond) i = true -> 
           identify_rev alpha1 Q i = 1 -> i = 0 \/ i = 1) ->
  (forall (cond : SecOrder) (i : nat) (Q : predicate) (x : FOvariable),
           is_unary_predless cond = true ->
           occ_in_alpha (replace_pred alpha2 Q x cond) i = true -> 
           identify_rev alpha2 Q i = 1 -> i = 0 \/ i = 1) ->
    is_unary_predless cond = true ->
      occ_in_alpha (replace_pred (conjSO alpha1 alpha2) Q x cond) i = true ->
        identify_rev (conjSO alpha1 alpha2) Q i = 1 ->
           i = 0 \/ i = 1.
Proof.
  intros alpha1 alpha2 cond i Q x IHalpha1 IHalpha2 Hun Hocc Hid.
  rewrite rep_pred_conjSO in Hocc.
  apply occ_in_alpha_conjSO2_fwd2 in Hocc.
  destruct Hocc as [Hocc | Hocc].
    rewrite (id_rev_conjSO_l alpha1 alpha2 cond _ x) in Hid; try assumption.
    apply (IHalpha1 cond i Q x); try assumption.

    destruct Hocc as [H1 H2].
    rewrite (id_rev_conjSO_r alpha1 alpha2 cond _ x) in Hid; try assumption.
    case_eq (length (preds_in alpha1)).
      intros H; rewrite H in *.
      rewrite plus_zero in Hid.
      rewrite preds_in_rep_pred in *; try assumption.
      rewrite H in *; simpl in *.
      rewrite arith_minus_zero in *.
      apply (IHalpha2 cond i Q x); assumption.

      intros n H; rewrite H in *.
      rewrite one_suc in Hid.
      rewrite <- arith_plus_assoc in Hid.
      rewrite (one_suc 0) in Hid at 2.
      do 2 rewrite <- one_suc in Hid.
      injection Hid; intros Hid'.
      case_eq n.
        intros Hn; rewrite Hn in *.
        rewrite plus_zero in *.
        pose proof H2 as H2'.

        case_eq (is_unary_predless alpha2); intros Hun2.
          rewrite rep_pred_is_unary_predless in H2'; try assumption.
          rewrite is_un_predless_occ_in_alpha in H2'; try assumption.
          discriminate.

          apply id_rev_0 in Hid'; try assumption.
          rewrite preds_in_rep_pred in Hid'; try assumption.
          rewrite H in *.
          case_eq (num_occ alpha1 Q).
            intros Hnum; rewrite Hnum in *.
            rewrite arith_minus_zero in *.
            case_eq i.
              intros; left; reflexivity.

              intros j Hi; rewrite Hi in *.
              simpl in Hid'; rewrite arith_minus_zero in *.
              rewrite Hid';  right; reflexivity.

            intros m Hnum; rewrite Hnum in *.
            rewrite preds_in_rep_pred in H2; try assumption.
            rewrite H in *; simpl in *.
            rewrite arith_minus_zero in *.
            left; assumption.

        intros m Hn; rewrite Hn in *.
        rewrite one_suc in Hid'.
        rewrite <- arith_plus_assoc in Hid'.
        rewrite <- one_suc in Hid'.
        discriminate.
Qed.

Lemma id_rev_1_allSO : forall (alpha cond : SecOrder) (i : nat) (P Q : predicate) (x : FOvariable),
  (forall (cond : SecOrder) (i : nat) (Q : predicate) (x : FOvariable),
          is_unary_predless cond = true ->
          occ_in_alpha (replace_pred alpha Q x cond) i = true -> 
          identify_rev alpha Q i = 1 -> i = 0 \/ i = 1) ->
    is_unary_predless cond = true ->
      occ_in_alpha (replace_pred (allSO P alpha) Q x cond) i = true ->
        identify_rev (allSO P alpha) Q i = 1 ->
          i = 0 \/ i = 1.
Proof.
  intros alpha cond i P Q x IHalpha Hun Hocc Hid.
  destruct P as [Pn]; destruct Q as [Qm].
  unfold identify_rev in *.
  simpl in *.
  case_eq i.
    intros; left; reflexivity.

    intros j Hi; rewrite Hi in *.
    case_eq j.
      intros; right; reflexivity.

      intros k Hj; rewrite Hj in *.
      case_eq (beq_nat Qm Pn); intros Hbeq; rewrite Hbeq in *;
        injection Hid; intros Hid';
        case_eq (is_unary_predless alpha); intros Hun2;
          (rewrite is_un_predless_occ_in_alpha in Hocc;
            [discriminate |
            rewrite rep_pred_is_unary_predless; try assumption]);

          try (apply id_rev_0 in Hid'; try assumption;
          try discriminate).
          rewrite occ_in_alpha_allSO in Hocc.
          simpl in *.
          rewrite is_un_predless_occ_in_alpha in Hocc.
            discriminate.

            rewrite rep_pred_is_unary_predless; assumption.
Qed.

Lemma id_rev_1_exSO : forall (alpha cond : SecOrder) (i : nat) (P Q : predicate) (x : FOvariable),
  (forall (cond : SecOrder) (i : nat) (Q : predicate) (x : FOvariable),
          is_unary_predless cond = true ->
          occ_in_alpha (replace_pred alpha Q x cond) i = true -> 
          identify_rev alpha Q i = 1 -> i = 0 \/ i = 1) ->
    is_unary_predless cond = true ->
      occ_in_alpha (replace_pred (exSO P alpha) Q x cond) i = true ->
        identify_rev (exSO P alpha) Q i = 1 ->
          i = 0 \/ i = 1.
Proof.
  intros alpha cond i P Q x IHalpha Hun Hocc Hid.
  destruct P as [Pn]; destruct Q as [Qm].
  unfold identify_rev in *.
  simpl in *.
  case_eq i.
    intros; left; reflexivity.

    intros j Hi; rewrite Hi in *.
    case_eq j.
      intros; right; reflexivity.

      intros k Hj; rewrite Hj in *.
      case_eq (beq_nat Qm Pn); intros Hbeq; rewrite Hbeq in *;
        injection Hid; intros Hid';
        case_eq (is_unary_predless alpha); intros Hun2;
          (rewrite is_un_predless_occ_in_alpha in Hocc;
            [discriminate |
            rewrite rep_pred_is_unary_predless; try assumption]);

          try (apply id_rev_0 in Hid'; try assumption;
          try discriminate).
          rewrite occ_in_alpha_exSO in Hocc.
          simpl in *.
          rewrite is_un_predless_occ_in_alpha in Hocc.
            discriminate.

            rewrite rep_pred_is_unary_predless; assumption.
Qed.

(* Can this be proved without induction? *)

Lemma id_rev_1 : forall (alpha cond: SecOrder) (i : nat) (Q : predicate) (x : FOvariable),
  is_unary_predless cond = true ->
    occ_in_alpha (replace_pred alpha Q x cond) i = true ->
      identify_rev alpha Q i = 1 -> i = 0 \/ i = 1.
Proof.
  induction alpha;
    intros cond i Q x Hun Hocc Hid;
    try destruct p as [Pn]; try destruct Q as [Qm];
    try destruct f as [xn]; try destruct f0 as [xm].

    apply (id_rev_1_predSO cond i (Pred Pn) (Pred Qm) x (Var xn));
      assumption.

    unfold occ_in_alpha in *; unfold identify_rev in *;
    simpl in *; case_eq i;
      [intros; left; reflexivity |
      intros n Hi; rewrite Hi in *; discriminate].

    unfold occ_in_alpha in *; unfold identify_rev in *;
    simpl in *; case_eq i;
      [intros; left; reflexivity |
      intros n Hi; rewrite Hi in *; discriminate].

    apply (id_rev_1_allFO alpha cond i (Pred Qm) x (Var xn)); assumption.
    apply (id_rev_1_allFO alpha cond i (Pred Qm) x (Var xn)); assumption.
    apply (id_rev_1_negSO alpha cond i (Pred Qm) x ); assumption.
    apply (id_rev_1_conjSO alpha1 alpha2 cond i (Pred Qm) x ); assumption.
    apply (id_rev_1_conjSO alpha1 alpha2 cond i (Pred Qm) x ); assumption.
    apply (id_rev_1_conjSO alpha1 alpha2 cond i (Pred Qm) x ); assumption.
    apply (id_rev_1_allSO alpha cond i (Pred Pn) (Pred Qm) x ); assumption.
    apply (id_rev_1_exSO alpha cond i (Pred Pn) (Pred Qm) x ); assumption.
Qed.



Lemma id_rev_leb_predSO : forall (P Q : predicate) (x : FOvariable) (i : nat),
  Nat.leb i (length (preds_in (predSO P x)) - num_occ (predSO P x) Q) = true ->
    Nat.leb i (identify_rev (predSO P x) Q i) = true.
Proof.
  unfold identify_rev_l.
  intros P Q x i Hleb.
  destruct P as [Pn]; destruct x; destruct Q as [Qm].
  simpl identify_rev_l.
  simpl in Hleb.
  rewrite num_occ_predSO in Hleb.
  case_eq i.
    simpl; reflexivity.

    intros j Hi.
    rewrite Hi in *.
    rewrite beq_nat_comm in Hleb.
    case_eq (beq_nat Qm Pn); intros Hbeq;
      rewrite Hbeq in Hleb.
      simpl in *; discriminate.

      case_eq j.
        intros Hj; rewrite Hj in *.
        reflexivity.

        intros k Hj; rewrite Hj in *.
        simpl in Hleb; discriminate.
Qed.

Lemma id_rev_leb_conjSO : forall (alpha1 alpha2 : SecOrder) (Q : predicate)
                                    (i : nat),
  (forall (Q : predicate) (i : nat),
           Nat.leb i (length (preds_in alpha1) - num_occ alpha1 Q) = true ->
           Nat.leb i (identify_rev_l (preds_in alpha1) Q i) = true) ->
  (forall (Q : predicate) (i : nat),
           Nat.leb i (length (preds_in alpha2) - num_occ alpha2 Q) = true ->
           Nat.leb i (identify_rev_l (preds_in alpha2) Q i) = true) ->
  Nat.leb i (length (preds_in (conjSO alpha1 alpha2)) - 
                  num_occ (conjSO alpha1 alpha2) Q) = true ->
  Nat.leb i (identify_rev_l (preds_in (conjSO alpha1 alpha2)) Q i) = true.
Proof.
  intros alpha1 alpha2 Q i IHalpha1 IHalpha2 Hleb.
  case_eq (beq_nat i 0); intros Hbeq.
    rewrite (beq_nat_true _ _ Hbeq) in *.
    reflexivity.
  simpl in *.
  rewrite num_occ_conjSO in *.
  rewrite app_length in Hleb.
  rewrite arith_plus_minus_rearr in Hleb.
  rewrite identify_rev_l_app.
  case_eq (Nat.leb i (length (preds_in alpha1) - length (indicies_l_rev (preds_in alpha1) Q)));
    intros Hleb2.
    apply IHalpha1; unfold num_occ;
    rewrite length_ind; assumption.

  assert (Nat.leb (i - (length (preds_in alpha1) - length (indicies_l_rev (preds_in alpha1) Q)))
             (length (preds_in alpha2) - num_occ alpha2 Q) = true ) as H.
  apply leb_minus with (i := (length (preds_in alpha1) - length (indicies_l_rev (preds_in alpha1) Q)))
          in Hleb.
    unfold num_occ in *; do 2 rewrite length_ind in *.
    rewrite arith_plus_3 in Hleb; assumption.

  specialize (IHalpha2 Q (i - (length (preds_in alpha1) - 
            length (indicies_l_rev (preds_in alpha1) Q))) H).
  rewrite leb_plus with (m:= (length (preds_in alpha1) - 
            length (indicies_l_rev (preds_in alpha1) Q))) in IHalpha2.
  rewrite arith_plus_minus_assoc in IHalpha2.
  rewrite arith_minus_refl in IHalpha2.
  rewrite arith_minus_zero in IHalpha2.
  rewrite arith_plus_minus_assoc2 in IHalpha2.
  apply leb_plus_r with (m:= length (indicies_l_rev (preds_in alpha1) Q)) in IHalpha2.
  rewrite arith_plus_minus_assoc in IHalpha2.
  rewrite arith_minus_refl in IHalpha2.
  rewrite arith_minus_zero in IHalpha2.
  assumption.

  pose proof (num_occ_preds_in alpha1 Q) as H0.
  unfold num_occ in H0.
  rewrite length_ind in H0.
  apply leb_plus_r with (m := 
        (identify_rev_l (preds_in alpha2) Q
     (i - (length (preds_in alpha1) - length (indicies_l_rev (preds_in alpha1) Q)))))
       in H0.
  rewrite arith_plus_comm; assumption.

  apply leb_refl.
  pose proof (num_occ_preds_in alpha1 Q) as H0.
  unfold num_occ in H0.
  rewrite length_ind in H0.
  assumption.

  apply leb_switch; assumption.
  apply leb_refl.
  assumption.

  unfold num_occ in Hleb; rewrite indicies_l_rev_app.
  rewrite app_length; rewrite list_map_length.
  do 2 rewrite length_ind in Hleb.
  rewrite arith_plus_minus_rearr.
    assumption.

    pose proof (num_occ_preds_in alpha1 Q) as H.
    unfold num_occ in H.
    rewrite length_ind in H.
    assumption.

    pose proof (num_occ_preds_in alpha2 Q) as H.
    unfold num_occ in H.
    rewrite length_ind in H.
    assumption.

  apply num_occ_preds_in.
  apply num_occ_preds_in.
Qed.


Lemma id_rev_num_occ_0 : forall (alpha : SecOrder) (Q : predicate)
                                (i : nat),
  num_occ alpha Q = 0 ->
    identify_rev alpha Q i = i.
Admitted.


Lemma id_rev_leb_allSO : forall (alpha : SecOrder) (P Q : predicate)
                                    (i : nat),
  (forall (Q : predicate) (i : nat),
          Nat.leb i (length (preds_in alpha) - num_occ alpha Q) = true ->
          Nat.leb i (identify_rev_l (preds_in alpha) Q i) = true) ->
      Nat.leb i (length (preds_in (allSO P alpha)) - num_occ (allSO P alpha) Q) = true ->
        Nat.leb i (identify_rev_l (preds_in (allSO P alpha)) Q i) = true.
Proof.
  intros alpha P Q i IHalpha Hleb.
  destruct P as [Pn]; destruct Q as [Qm].
  simpl in *.
  rewrite num_occ_allSO in Hleb.
  rewrite beq_nat_comm in Hleb.
  case_eq i.
    reflexivity.

    intros j Hi; rewrite Hi in *.
    case_eq (beq_nat Qm Pn); intros Hbeq; rewrite Hbeq in *.
      simpl in *.
      case_eq (length (preds_in alpha) - num_occ alpha (Pred Qm)).
        intros H; rewrite H in *.
        discriminate.

        intros n H; rewrite H in *.
        specialize (IHalpha (Pred Qm) (S j)).
        rewrite H in IHalpha.
        simpl Nat.leb at 1 in IHalpha.
        apply leb_suc_l.
        apply IHalpha.
        assumption.

    case_eq (num_occ alpha (Pred Qm)).
      intros H; rewrite H in *. 
      simpl in Hleb.
      simpl.
      pose proof id_rev_num_occ_0 as H2.
      unfold identify_rev in H2.
      rewrite H2;
        [apply leb_refl | assumption].

      intros n H; rewrite H in *.
      simpl.
      apply IHalpha.
      rewrite H.
      rewrite one_suc.
      rewrite arith_minus_exp.
      apply leb_minus with (i := 1) in Hleb.
      simpl in Hleb.
      rewrite arith_minus_zero in Hleb.
      assumption.
Qed.

Lemma id_rev_leb : forall (alpha : SecOrder) (Q : predicate)
                              (i : nat),
  Nat.leb i (length (preds_in alpha) - num_occ alpha Q) = true ->
    Nat.leb i (identify_rev alpha Q i) = true.
Proof.
  unfold identify_rev.
  induction alpha;
    intros  Q i Hleb;
    try  (simpl; simpl in *; apply IHalpha); try assumption.

    apply id_rev_leb_predSO in Hleb; assumption.

    destruct f; destruct f0.
    simpl in *.
    rewrite (leb_beq_zero) in Hleb.
    rewrite (beq_nat_true _ _ Hleb).
    reflexivity.

    destruct f; destruct f0.
    simpl in *.
    rewrite (leb_beq_zero) in Hleb.
    rewrite (beq_nat_true _ _ Hleb).
    reflexivity.

    apply id_rev_leb_conjSO; assumption.
    apply id_rev_leb_conjSO; assumption.
    apply id_rev_leb_conjSO; assumption.
    apply id_rev_leb_allSO; assumption.
    apply id_rev_leb_allSO; assumption.
Qed.


Lemma length_ind_l_rev : forall (l : list predicate) (Q : predicate),
  Nat.leb (length (indicies_l_rev l Q)) (length l) = true.
Proof.
  intros l Q.
  induction l.
    reflexivity.

    simpl.
    destruct a as [Pn]; destruct Q as [Qm].
    case_eq (beq_nat Pn Qm); intros Hbeq.
      simpl; assumption.

      apply leb_suc_r.
      assumption.
Qed.


Lemma id_rev_preds_in_l : forall (l : list predicate) (Q : predicate) (i : nat),
  beq_nat i 0 = false ->
    Nat.leb i (length l - length (indicies_l_rev l Q)) = true ->
      Nat.leb (identify_rev_l l Q i) (length l) = true.
Proof.
  induction l;
    intros Q i Hbeq Hleb.
    simpl in *.
    case i; reflexivity.

    destruct a as [Pn]; destruct Q as [Qm].
    rewrite identify_rev_l_cons.
    simpl length in *.
    rewrite beq_nat_comm in Hleb.
    case_eq (beq_nat Qm Pn); intros Hbeq1;
      rewrite Hbeq1 in *.
      simpl in *.
      apply IHl; assumption.

      case_eq i.
        reflexivity.

        intros j Hi; rewrite Hi in *.
        case_eq j.
          reflexivity.

          intros k Hj; rewrite Hj in *.
          simpl.
          apply IHl.
          reflexivity.
          rewrite <- arith_minus_suc in Hleb.
            simpl in *.
            assumption.

            apply length_ind_l_rev.

            assumption.
Qed.

Lemma id_rev_preds_in : forall (alpha : SecOrder) (Q : predicate) (i : nat),
  Nat.leb i (length (preds_in alpha) - num_occ alpha Q) = true ->
    Nat.leb (identify_rev alpha Q i) (length (preds_in alpha)) = true.
Proof.
  intros alpha Q i Hleb.
  case_eq (beq_nat i 0); intros Hbeq.
    rewrite (beq_nat_true _ _ Hbeq) in *.
    unfold identify_rev.
    rewrite identify_rev_l_0.
    reflexivity.
  unfold identify_rev.
  unfold num_occ in Hleb.
  rewrite length_ind in Hleb.
  apply id_rev_preds_in_l; assumption.
Qed.


Lemma occ_in_alpha_id_rev : forall (alpha cond : SecOrder) (Q : predicate) (i : nat)
                                (x : FOvariable),
  is_unary_predless cond = true ->
    occ_in_alpha (replace_pred alpha Q x cond) i = true ->
      occ_in_alpha alpha (identify_rev alpha Q i) = true.
Proof.
  intros alpha cond Q i x Hcond Hocc.
  case_eq (is_unary_predless alpha); intros Hun.
    rewrite rep_pred_is_unary_predless in Hocc; try assumption.
    rewrite is_un_predless_occ_in_alpha in Hocc; try assumption.
    discriminate.
  apply occ_in_alpha_leb2 in Hocc.
  unfold occ_in_alpha.
  case_eq (beq_nat (identify_rev alpha Q i) 0); intros Hbeq.
    rewrite (id_rev_0 _ _ _ Hun (beq_nat_true _ _ Hbeq)) in *.
    simpl in *.
    destruct Hocc;  discriminate.

    case_eq (Nat.leb (identify_rev alpha Q i ) (length (preds_in alpha)));
      intros Hleb.
      reflexivity.

      destruct Hocc as [H1 H2].
      rewrite id_rev_preds_in in Hleb.
        discriminate.

        rewrite preds_in_rep_pred in H2;
          assumption.
Qed.

(* ------------------------------------------------------------------------------------ *)

Lemma at_pred_rep_pred_conjSO : forall (alpha1 alpha2 cond : SecOrder)
                                (Q : predicate) (x : FOvariable)
                                (i : nat),
  (forall (cond : SecOrder) (Q : predicate) (x : FOvariable) (i : nat),
           is_unary_predless cond = true ->
           occ_in_alpha (replace_pred alpha1 Q x cond) i = true ->
           at_pred (preds_in (replace_pred alpha1 Q x cond)) i =
           at_pred (preds_in alpha1) (identify_rev alpha1 Q i)) ->
  (forall (cond : SecOrder) (Q : predicate) (x : FOvariable) (i : nat),
           is_unary_predless cond = true ->
           occ_in_alpha (replace_pred alpha2 Q x cond) i = true ->
           at_pred (preds_in (replace_pred alpha2 Q x cond)) i =
           at_pred (preds_in alpha2) (identify_rev alpha2 Q i)) ->
    is_unary_predless cond = true ->
      occ_in_alpha (replace_pred (conjSO alpha1 alpha2) 
              Q x cond) i =  true ->
      at_pred (preds_in (replace_pred (conjSO alpha1 alpha2) 
                    Q x cond)) i =
        at_pred (preds_in (conjSO alpha1 alpha2))
                    (identify_rev (conjSO alpha1 alpha2) Q i).
Proof.
  intros alpha1 alpha2 cond Q x i IHalpha1 IHalpha2 Hcond
    Hocc.
  destruct Q as [Qm].
  unfold identify_rev in *; simpl.
  rewrite identify_rev_l_app.
  rewrite rep_pred_conjSO in Hocc.
  apply occ_in_alpha_conjSO2_fwd2 in Hocc.
  destruct Hocc as [Hocc | Hocc].
    pose proof (occ_in_alpha_leb2 _ _ Hocc) as Hleb.
    destruct Hleb as [Hbeq Hleb]. 
    rewrite preds_in_rep_pred in Hleb;
    try assumption.
    unfold num_occ in Hleb; rewrite length_ind in Hleb.
    rewrite Hleb.
    rewrite at_pred_app_l.
    rewrite at_pred_app_l.
    apply IHalpha1; assumption.
      pose proof id_rev_preds_in as H.
      unfold identify_rev in H.
      apply PeanoNat.Nat.leb_le.
      apply H.
        unfold num_occ; rewrite length_ind.
        assumption.

        rewrite preds_in_rep_pred;
        try assumption.
        unfold num_occ; rewrite length_ind.
        apply PeanoNat.Nat.leb_le.
        assumption.

      destruct Hocc as [Hocc1 Hocc2].
      pose proof (occ_in_alpha_f _ _ Hocc1) as H.
      destruct H as [H | H].
        rewrite (beq_nat_true _ _ H) in *.
        rewrite occ_in_alpha_0 in Hocc2.
        discriminate.

        rewrite preds_in_rep_pred in H;
        try assumption.
        unfold num_occ in H.
        rewrite length_ind in H.
        rewrite H.
        rewrite arith_plus_comm.
        rewrite at_pred_app_r.
        rewrite <- IHalpha2 with (cond := cond) (x := x);
        try assumption.
        assert (i = length (preds_in (replace_pred alpha1 (Pred Qm)
                                       x cond)) + (i
                     - length (preds_in (replace_pred alpha1 (Pred Qm)
                                       x cond)))) as H2.
          rewrite arith_plus_minus_assoc2.
          rewrite arith_plus_3.
          reflexivity.

          rewrite preds_in_rep_pred;
          try assumption.
          unfold num_occ; rewrite length_ind.
          apply leb_switch; assumption.
        rewrite H2 at 1; rewrite at_pred_app_r.
        rewrite preds_in_rep_pred; try assumption.
        unfold num_occ; rewrite length_ind.
        reflexivity.
          case_eq (beq_nat (i - 
              length (preds_in (replace_pred alpha1
                 (Pred Qm) x cond))) 0); intros Hbeq.
            rewrite (beq_nat_true _ _ Hbeq) in Hocc2.
            rewrite occ_in_alpha_0 in Hocc2.
            discriminate.

            reflexivity.

            rewrite preds_in_rep_pred in Hocc2;
            try assumption.
            unfold num_occ in Hocc2.
            rewrite length_ind in Hocc2.
            assumption.

          case_eq (is_unary_predless alpha2); intros Hun.
            rewrite is_un_predless_occ_in_alpha in Hocc2.
              discriminate.

              rewrite rep_pred_is_unary_predless;
              assumption.

            case_eq (beq_nat  (identify_rev_l (preds_in alpha2) (Pred Qm)
                        (i - (length (preds_in alpha1) -
                        length (indicies_l_rev (preds_in alpha1) 
                        (Pred Qm))))) 0); intros Hbeq.
              apply beq_nat_true in Hbeq.
              pose proof id_rev_0 as H2.
              unfold identify_rev in H2.
              pose proof (H2 _ _ _ Hun Hbeq) as H3.
              pose proof beq_nat_leb.
              case_eq (beq_nat (i - (length (preds_in alpha1) -
                        length (indicies_l_rev (preds_in alpha1) 
                        (Pred Qm)))) 0); intros Hbeq2.
                apply beq_nat_leb in Hbeq2.
                rewrite H in Hbeq2.
                discriminate.

                pose proof (beq_nat_false _ _ Hbeq2) as H4.
                unfold not in H4; specialize (H4 H3).
                contradiction.

              reflexivity.
              case_eq (beq_nat i 0); intros Hbeq.
                rewrite (beq_nat_true _ _ Hbeq) in Hocc;
                rewrite occ_in_alpha_0 in Hocc.
                discriminate.

                reflexivity.

              apply occ_in_alpha_leb2 in Hocc.
              destruct Hocc as [Hocc1 Hocc2].
              rewrite preds_in_rep_pred in Hocc2;
              try assumption.
              unfold num_occ in Hocc2.
              rewrite length_ind in Hocc2.
              simpl in *.
              rewrite app_length in Hocc2.
              assumption.
Qed.

Lemma at_pred_rep_pred_disjSO : forall (alpha1 alpha2 cond : SecOrder)
                                (Q : predicate) (x : FOvariable)
                                (i : nat),
  (forall (cond : SecOrder) (Q : predicate) (x : FOvariable) (i : nat),
           is_unary_predless cond = true ->
           occ_in_alpha (replace_pred alpha1 Q x cond) i = true ->
           at_pred (preds_in (replace_pred alpha1 Q x cond)) i =
           at_pred (preds_in alpha1) (identify_rev alpha1 Q i)) ->
  (forall (cond : SecOrder) (Q : predicate) (x : FOvariable) (i : nat),
           is_unary_predless cond = true ->
           occ_in_alpha (replace_pred alpha2 Q x cond) i = true ->
           at_pred (preds_in (replace_pred alpha2 Q x cond)) i =
           at_pred (preds_in alpha2) (identify_rev alpha2 Q i)) ->
    is_unary_predless cond = true ->
      occ_in_alpha (replace_pred (disjSO alpha1 alpha2) 
              Q x cond) i =  true ->
      at_pred (preds_in (replace_pred (disjSO alpha1 alpha2) 
                    Q x cond)) i =
        at_pred (preds_in (disjSO alpha1 alpha2))
                    (identify_rev (disjSO alpha1 alpha2) Q i).
Proof.
  intros alpha1 alpha2 cond Q x i IHalpha1 IHalpha2 Hcond
    Hocc.
  destruct Q as [Qm].
  unfold identify_rev in *; simpl.
  rewrite identify_rev_l_app.
  rewrite rep_pred_disjSO in Hocc.
  apply occ_in_alpha_conjSO2_fwd2 in Hocc.
  destruct Hocc as [Hocc | Hocc].
    pose proof (occ_in_alpha_leb2 _ _ Hocc) as Hleb.
    destruct Hleb as [Hbeq Hleb]. 
    rewrite preds_in_rep_pred in Hleb;
    try assumption.
    unfold num_occ in Hleb; rewrite length_ind in Hleb.
    rewrite Hleb.
    rewrite at_pred_app_l.
    rewrite at_pred_app_l.
    apply IHalpha1; assumption.
      pose proof id_rev_preds_in as H.
      unfold identify_rev in H.
      apply PeanoNat.Nat.leb_le.
      apply H.
        unfold num_occ; rewrite length_ind.
        assumption.

        rewrite preds_in_rep_pred;
        try assumption.
        unfold num_occ; rewrite length_ind.
        apply PeanoNat.Nat.leb_le.
        assumption.

      destruct Hocc as [Hocc1 Hocc2].
      pose proof (occ_in_alpha_f _ _ Hocc1) as H.
      destruct H as [H | H].
        rewrite (beq_nat_true _ _ H) in *.
        rewrite occ_in_alpha_0 in Hocc2.
        discriminate.

        rewrite preds_in_rep_pred in H;
        try assumption.
        unfold num_occ in H.
        rewrite length_ind in H.
        rewrite H.
        rewrite arith_plus_comm.
        rewrite at_pred_app_r.
        rewrite <- IHalpha2 with (cond := cond) (x := x);
        try assumption.
        assert (i = length (preds_in (replace_pred alpha1 (Pred Qm)
                                       x cond)) + (i
                     - length (preds_in (replace_pred alpha1 (Pred Qm)
                                       x cond)))) as H2.
          rewrite arith_plus_minus_assoc2.
          rewrite arith_plus_3.
          reflexivity.

          rewrite preds_in_rep_pred;
          try assumption.
          unfold num_occ; rewrite length_ind.
          apply leb_switch; assumption.
        rewrite H2 at 1; rewrite at_pred_app_r.
        rewrite preds_in_rep_pred; try assumption.
        unfold num_occ; rewrite length_ind.
        reflexivity.
          case_eq (beq_nat (i - 
              length (preds_in (replace_pred alpha1
                 (Pred Qm) x cond))) 0); intros Hbeq.
            rewrite (beq_nat_true _ _ Hbeq) in Hocc2.
            rewrite occ_in_alpha_0 in Hocc2.
            discriminate.

            reflexivity.

            rewrite preds_in_rep_pred in Hocc2;
            try assumption.
            unfold num_occ in Hocc2.
            rewrite length_ind in Hocc2.
            assumption.

          case_eq (is_unary_predless alpha2); intros Hun.
            rewrite is_un_predless_occ_in_alpha in Hocc2.
              discriminate.

              rewrite rep_pred_is_unary_predless;
              assumption.

            case_eq (beq_nat  (identify_rev_l (preds_in alpha2) (Pred Qm)
                        (i - (length (preds_in alpha1) -
                        length (indicies_l_rev (preds_in alpha1) 
                        (Pred Qm))))) 0); intros Hbeq.
              apply beq_nat_true in Hbeq.
              pose proof id_rev_0 as H2.
              unfold identify_rev in H2.
              pose proof (H2 _ _ _ Hun Hbeq) as H3.
              pose proof beq_nat_leb.
              case_eq (beq_nat (i - (length (preds_in alpha1) -
                        length (indicies_l_rev (preds_in alpha1) 
                        (Pred Qm)))) 0); intros Hbeq2.
                apply beq_nat_leb in Hbeq2.
                rewrite H in Hbeq2.
                discriminate.

                pose proof (beq_nat_false _ _ Hbeq2) as H4.
                unfold not in H4; specialize (H4 H3).
                contradiction.

              reflexivity.
              case_eq (beq_nat i 0); intros Hbeq.
                rewrite (beq_nat_true _ _ Hbeq) in Hocc;
                rewrite occ_in_alpha_0 in Hocc.
                discriminate.

                reflexivity.

              apply occ_in_alpha_leb2 in Hocc.
              destruct Hocc as [Hocc1 Hocc2].
              rewrite preds_in_rep_pred in Hocc2;
              try assumption.
              unfold num_occ in Hocc2.
              rewrite length_ind in Hocc2.
              simpl in *.
              rewrite app_length in Hocc2.
              assumption.
Qed.

Lemma at_pred_rep_pred_implSO : forall (alpha1 alpha2 cond : SecOrder)
                                (Q : predicate) (x : FOvariable)
                                (i : nat),
  (forall (cond : SecOrder) (Q : predicate) (x : FOvariable) (i : nat),
           is_unary_predless cond = true ->
           occ_in_alpha (replace_pred alpha1 Q x cond) i = true ->
           at_pred (preds_in (replace_pred alpha1 Q x cond)) i =
           at_pred (preds_in alpha1) (identify_rev alpha1 Q i)) ->
  (forall (cond : SecOrder) (Q : predicate) (x : FOvariable) (i : nat),
           is_unary_predless cond = true ->
           occ_in_alpha (replace_pred alpha2 Q x cond) i = true ->
           at_pred (preds_in (replace_pred alpha2 Q x cond)) i =
           at_pred (preds_in alpha2) (identify_rev alpha2 Q i)) ->
    is_unary_predless cond = true ->
      occ_in_alpha (replace_pred (implSO alpha1 alpha2) 
              Q x cond) i =  true ->
      at_pred (preds_in (replace_pred (implSO alpha1 alpha2) 
                    Q x cond)) i =
        at_pred (preds_in (implSO alpha1 alpha2))
                    (identify_rev (implSO alpha1 alpha2) Q i).
Proof.
  intros alpha1 alpha2 cond Q x i IHalpha1 IHalpha2 Hcond
    Hocc.
  destruct Q as [Qm].
  unfold identify_rev in *; simpl.
  rewrite identify_rev_l_app.
  rewrite rep_pred_implSO in Hocc.
  apply occ_in_alpha_conjSO2_fwd2 in Hocc.
  destruct Hocc as [Hocc | Hocc].
    pose proof (occ_in_alpha_leb2 _ _ Hocc) as Hleb.
    destruct Hleb as [Hbeq Hleb]. 
    rewrite preds_in_rep_pred in Hleb;
    try assumption.
    unfold num_occ in Hleb; rewrite length_ind in Hleb.
    rewrite Hleb.
    rewrite at_pred_app_l.
    rewrite at_pred_app_l.
    apply IHalpha1; assumption.
      pose proof id_rev_preds_in as H.
      unfold identify_rev in H.
      apply PeanoNat.Nat.leb_le.
      apply H.
        unfold num_occ; rewrite length_ind.
        assumption.

        rewrite preds_in_rep_pred;
        try assumption.
        unfold num_occ; rewrite length_ind.
        apply PeanoNat.Nat.leb_le.
        assumption.

      destruct Hocc as [Hocc1 Hocc2].
      pose proof (occ_in_alpha_f _ _ Hocc1) as H.
      destruct H as [H | H].
        rewrite (beq_nat_true _ _ H) in *.
        rewrite occ_in_alpha_0 in Hocc2.
        discriminate.

        rewrite preds_in_rep_pred in H;
        try assumption.
        unfold num_occ in H.
        rewrite length_ind in H.
        rewrite H.
        rewrite arith_plus_comm.
        rewrite at_pred_app_r.
        rewrite <- IHalpha2 with (cond := cond) (x := x);
        try assumption.
        assert (i = length (preds_in (replace_pred alpha1 (Pred Qm)
                                       x cond)) + (i
                     - length (preds_in (replace_pred alpha1 (Pred Qm)
                                       x cond)))) as H2.
          rewrite arith_plus_minus_assoc2.
          rewrite arith_plus_3.
          reflexivity.

          rewrite preds_in_rep_pred;
          try assumption.
          unfold num_occ; rewrite length_ind.
          apply leb_switch; assumption.
        rewrite H2 at 1; rewrite at_pred_app_r.
        rewrite preds_in_rep_pred; try assumption.
        unfold num_occ; rewrite length_ind.
        reflexivity.
          case_eq (beq_nat (i - 
              length (preds_in (replace_pred alpha1
                 (Pred Qm) x cond))) 0); intros Hbeq.
            rewrite (beq_nat_true _ _ Hbeq) in Hocc2.
            rewrite occ_in_alpha_0 in Hocc2.
            discriminate.

            reflexivity.

            rewrite preds_in_rep_pred in Hocc2;
            try assumption.
            unfold num_occ in Hocc2.
            rewrite length_ind in Hocc2.
            assumption.

          case_eq (is_unary_predless alpha2); intros Hun.
            rewrite is_un_predless_occ_in_alpha in Hocc2.
              discriminate.

              rewrite rep_pred_is_unary_predless;
              assumption.

            case_eq (beq_nat  (identify_rev_l (preds_in alpha2) (Pred Qm)
                        (i - (length (preds_in alpha1) -
                        length (indicies_l_rev (preds_in alpha1) 
                        (Pred Qm))))) 0); intros Hbeq.
              apply beq_nat_true in Hbeq.
              pose proof id_rev_0 as H2.
              unfold identify_rev in H2.
              pose proof (H2 _ _ _ Hun Hbeq) as H3.
              pose proof beq_nat_leb.
              case_eq (beq_nat (i - (length (preds_in alpha1) -
                        length (indicies_l_rev (preds_in alpha1) 
                        (Pred Qm)))) 0); intros Hbeq2.
                apply beq_nat_leb in Hbeq2.
                rewrite H in Hbeq2.
                discriminate.

                pose proof (beq_nat_false _ _ Hbeq2) as H4.
                unfold not in H4; specialize (H4 H3).
                contradiction.

              reflexivity.
              case_eq (beq_nat i 0); intros Hbeq.
                rewrite (beq_nat_true _ _ Hbeq) in Hocc;
                rewrite occ_in_alpha_0 in Hocc.
                discriminate.

                reflexivity.

              apply occ_in_alpha_leb2 in Hocc.
              destruct Hocc as [Hocc1 Hocc2].
              rewrite preds_in_rep_pred in Hocc2;
              try assumption.
              unfold num_occ in Hocc2.
              rewrite length_ind in Hocc2.
              simpl in *.
              rewrite app_length in Hocc2.
              assumption.
Qed.




Lemma at_pred_rep_pred_allSO : forall (alpha cond : SecOrder)
                                (P Q : predicate) (x : FOvariable)
                                (i : nat),
  (forall (cond : SecOrder) (Q : predicate) (x : FOvariable) (i : nat),
          is_unary_predless cond = true ->
          occ_in_alpha (replace_pred alpha Q x cond) i = true ->
          at_pred (preds_in (replace_pred alpha Q x cond)) i =
          at_pred (preds_in alpha) (identify_rev alpha Q i)) ->
      is_unary_predless cond = true ->
        occ_in_alpha (replace_pred (allSO P alpha) Q x cond) i =
            true ->
      at_pred (preds_in (replace_pred (allSO P alpha) Q x cond)) i =
         at_pred (preds_in (allSO P alpha)) 
             (identify_rev (allSO P alpha) Q i).
Proof.
  intros alpha cond P Q x i IHalpha Hcond Hocc.
  destruct P as [Pn]; destruct Q as [Qm].
  rewrite rep_pred_allSO in *.
  unfold identify_rev in *.
  simpl preds_in in *.
  case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *.
    rewrite IHalpha; try assumption.
    rewrite identify_rev_l_cons.
    rewrite beq_nat_comm; rewrite Hbeq.
    simpl.
    rewrite (beq_nat_true _ _ Hbeq).
    case_eq (is_unary_predless alpha); intros Hun.
      rewrite is_un_predless_occ_in_alpha in Hocc.
        discriminate.

        rewrite rep_pred_is_unary_predless; assumption.

    case_eq (identify_rev_l (preds_in alpha) (Pred Qm) i).
      intros H.
      pose proof id_rev_0 as H2.
      unfold identify_rev in H2.
      rewrite (H2 _ _ _ Hun H) in  Hocc.
      rewrite occ_in_alpha_0 in Hocc.
      discriminate.

      intros n H.
      rewrite arith_minus_zero.
      reflexivity.

    case_eq (beq_nat i 0); intros Hbeq2.
      rewrite (beq_nat_true _ _ Hbeq2) in Hocc.
      rewrite occ_in_alpha_0 in Hocc.
      discriminate.

      reflexivity.

   simpl preds_in.
    case_eq i.
      intros Hi; rewrite Hi in *.
      rewrite occ_in_alpha_0 in Hocc; discriminate.

      intros j Hi; rewrite Hi in *.
      case_eq j.
        intros Hj; rewrite Hj in *.
        simpl.
        rewrite (beq_nat_comm).
        rewrite Hbeq.
        case_eq (identify_rev_l (preds_in alpha) (Pred Qm) 0).
          reflexivity.

          intros n H.
          rewrite arith_minus_zero.
          rewrite identify_rev_l_0 in H.
          discriminate.

        intros k Hj; rewrite Hj in *.
        rewrite occ_in_alpha_allSO in Hocc.
        simpl in Hocc.
        case_eq (is_unary_predless alpha); intros Hun.
          rewrite is_un_predless_occ_in_alpha in Hocc.
            discriminate.

            rewrite rep_pred_is_unary_predless;
            assumption.
        rewrite at_pred_cons.
        rewrite IHalpha; try assumption.
          simpl.
          rewrite beq_nat_comm.
          rewrite Hbeq.
          rewrite arith_minus_zero.
          case_eq (identify_rev_l (preds_in alpha) (Pred Qm) (S k)).
            intros H.
            pose proof (id_rev_0 _ _ _ Hun H) as H2.
            discriminate.

            reflexivity.
Qed.

Lemma at_pred_rep_pred_exSO : forall (alpha cond : SecOrder)
                                (P Q : predicate) (x : FOvariable)
                                (i : nat),
  (forall (cond : SecOrder) (Q : predicate) (x : FOvariable) (i : nat),
          is_unary_predless cond = true ->
          occ_in_alpha (replace_pred alpha Q x cond) i = true ->
          at_pred (preds_in (replace_pred alpha Q x cond)) i =
          at_pred (preds_in alpha) (identify_rev alpha Q i)) ->
      is_unary_predless cond = true ->
        occ_in_alpha (replace_pred (exSO P alpha) Q x cond) i =
            true ->
      at_pred (preds_in (replace_pred (exSO P alpha) Q x cond)) i =
         at_pred (preds_in (exSO P alpha)) 
             (identify_rev (exSO P alpha) Q i).
Proof.
  intros alpha cond P Q x i IHalpha Hcond Hocc.
  destruct P as [Pn]; destruct Q as [Qm].
  rewrite rep_pred_exSO in *.
  unfold identify_rev in *.
  simpl preds_in in *.
  case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *.
    rewrite IHalpha; try assumption.
    rewrite identify_rev_l_cons.
    rewrite beq_nat_comm; rewrite Hbeq.
    simpl.
    rewrite (beq_nat_true _ _ Hbeq).
    case_eq (is_unary_predless alpha); intros Hun.
      rewrite is_un_predless_occ_in_alpha in Hocc.
        discriminate.

        rewrite rep_pred_is_unary_predless; assumption.

    case_eq (identify_rev_l (preds_in alpha) (Pred Qm) i).
      intros H.
      pose proof id_rev_0 as H2.
      unfold identify_rev in H2.
      rewrite (H2 _ _ _ Hun H) in  Hocc.
      rewrite occ_in_alpha_0 in Hocc.
      discriminate.

      intros n H.
      rewrite arith_minus_zero.
      reflexivity.

    case_eq (beq_nat i 0); intros Hbeq2.
      rewrite (beq_nat_true _ _ Hbeq2) in Hocc.
      rewrite occ_in_alpha_0 in Hocc.
      discriminate.

      reflexivity.

   simpl preds_in.
    case_eq i.
      intros Hi; rewrite Hi in *.
      rewrite occ_in_alpha_0 in Hocc; discriminate.

      intros j Hi; rewrite Hi in *.
      case_eq j.
        intros Hj; rewrite Hj in *.
        simpl.
        rewrite (beq_nat_comm).
        rewrite Hbeq.
        case_eq (identify_rev_l (preds_in alpha) (Pred Qm) 0).
          reflexivity.

          intros n H.
          rewrite arith_minus_zero.
          rewrite identify_rev_l_0 in H.
          discriminate.

        intros k Hj; rewrite Hj in *.
        rewrite occ_in_alpha_exSO in Hocc.
        simpl in Hocc.
        case_eq (is_unary_predless alpha); intros Hun.
          rewrite is_un_predless_occ_in_alpha in Hocc.
            discriminate.

            rewrite rep_pred_is_unary_predless;
            assumption.
        rewrite at_pred_cons.
        rewrite IHalpha; try assumption.
          simpl.
          rewrite beq_nat_comm.
          rewrite Hbeq.
          rewrite arith_minus_zero.
          case_eq (identify_rev_l (preds_in alpha) (Pred Qm) (S k)).
            intros H.
            pose proof (id_rev_0 _ _ _ Hun H) as H2.
            discriminate.

            reflexivity.
Qed.

Lemma at_pred_rep_pred : forall (alpha cond : SecOrder)
                                (Q : predicate) (x : FOvariable)
                                (i : nat),
  is_unary_predless cond = true ->
    occ_in_alpha (replace_pred alpha Q x cond) i = true ->
    at_pred (preds_in (replace_pred alpha Q x cond)) i 
     = at_pred (preds_in alpha) (identify_rev alpha Q i).
Proof.
  induction alpha;
    intros cond Q x i Hcond Hocc;
    try destruct f; try destruct f0;
    try destruct Q as [Qm]; try destruct p as [Pn];
    try reflexivity;
    try (    simpl in *; unfold identify_rev in *;
    simpl preds_in; apply IHalpha; try assumption). 

    unfold identify_rev.
    simpl preds_in.
    rewrite identify_rev_l_cons.
    simpl identify_rev_l.
    simpl in Hocc.
    case_eq (beq_nat Qm Pn); intros Hbeq;
      rewrite Hbeq in *.
      rewrite is_un_predless_occ_in_alpha in Hocc.
        discriminate.

        apply rep_FOv_is_unary_predless;
        assumption.

      case_eq i.
        intros Hi.
        simpl; reflexivity.

        intros j Hi; rewrite Hi in *.
        case_eq j.
          intros Hj.
          reflexivity.

          intros k Hj; rewrite Hj in *.
          apply occ_in_alpha_predSO in Hocc.
          discriminate.

          apply occ_in_alpha_leb2 in Hocc.
          apply Hocc.

    apply at_pred_rep_pred_conjSO; assumption.
    apply at_pred_rep_pred_disjSO; assumption.
    apply at_pred_rep_pred_implSO; assumption.
    apply at_pred_rep_pred_allSO; assumption.
    apply at_pred_rep_pred_exSO; assumption.
Qed.

Lemma at_pred_occ_id_fwd_conjSO : forall (alpha1 alpha2 : SecOrder) (i : nat) (Q : predicate),
  (forall (i : nat) (Q : predicate),
           occ_in_alpha alpha1 i = true -> 
           identify_fwd alpha1 Q i = 0 ->
           at_pred (preds_in alpha1) i = Q) ->
  (forall (i : nat) (Q : predicate),
           occ_in_alpha alpha2 i = true -> 
           identify_fwd alpha2 Q i = 0 -> 
           at_pred (preds_in alpha2) i = Q) ->
  occ_in_alpha (conjSO alpha1 alpha2) i = true ->
  identify_fwd (conjSO alpha1 alpha2) Q i = 0 ->
  at_pred (preds_in (conjSO alpha1 alpha2)) i = Q.
Proof.
  intros alpha1 alpha2 i Q IHalpha1 IHalpha2 Hocc Hid.
    simpl in *.
    rewrite Hocc in Hid.
    apply occ_in_alpha_conjSO2_fwd2 in Hocc.
    destruct Hocc as [Hocc | Hocc].
      rewrite Hocc in *.
      rewrite at_pred_app_l.
        apply IHalpha1; assumption.

        destruct (occ_in_alpha_leb2 _ _ Hocc) as [H1 H2].
        apply PeanoNat.Nat.leb_le.
        assumption.

      destruct Hocc as [Hl Hr].
      rewrite Hl in *.
      assert (i - length (preds_in alpha1) + length (preds_in alpha1) = i) as H.
        rewrite arith_plus_minus_assoc.
          rewrite arith_minus_refl; rewrite arith_minus_zero.
          reflexivity.

          apply occ_in_alpha_f in Hl.
          destruct Hl as [Hl | Hl].
            rewrite (beq_nat_true _ _ Hl) in *.
            simpl in *.
            rewrite occ_in_alpha_0 in Hr; discriminate.

            apply leb_switch; assumption.

          apply leb_refl.

      rewrite <- H.
      rewrite arith_plus_comm.
      rewrite at_pred_app_r.
        apply IHalpha2; try assumption.
        rewrite <- arith_plus_minus_assoc2 in Hid.
          case_eq (beq_nat (identify_fwd alpha2 Q (i - length (preds_in alpha1))
                             + (length (preds_in alpha1) - num_occ alpha1 Q)) 0); intros Hbeq.
            apply beq_nat_zero in Hbeq.
            apply beq_nat_true; assumption.

            rewrite Hid in Hbeq; simpl in *; discriminate.

          apply num_occ_preds_in.

          case_eq (beq_nat (i - length( preds_in alpha1)) 0); intros Hbeq.
            rewrite (beq_nat_true _ _ Hbeq) in *.
            rewrite occ_in_alpha_0 in Hr; discriminate.

            reflexivity.
Qed.

Lemma at_pred_occ_id_fwd_allSO : forall (alpha : SecOrder) (i : nat) (Q P : predicate),
  (forall (i : nat) (Q : predicate),
          occ_in_alpha alpha i = true -> 
          identify_fwd alpha Q i = 0 -> 
          at_pred (preds_in alpha) i = Q) ->
   occ_in_alpha (allSO P alpha) i = true ->
   identify_fwd (allSO P alpha) Q i = 0 ->
   at_pred (preds_in (allSO P alpha)) i = Q.
Proof.
  intros alpha i Q P IHalpha Hocc Hid.
  destruct P as [Pn]; destruct Q as [Qm].
  simpl preds_in in *.
  simpl in Hid.
  rewrite Hocc in *.
  rewrite occ_in_alpha_allSO in Hocc.
  case_eq i.
    intros Hi; rewrite Hi in *.
    simpl in *.
    rewrite occ_in_alpha_0 in Hocc; discriminate.

    intros j Hi; rewrite Hi in *.
    simpl in *.
    rewrite arith_minus_zero in *.
    case_eq j.
      intros Hj; rewrite Hj in *.
      simpl in *.
      case_eq (beq_nat Qm Pn); intros Hbeq; rewrite Hbeq in *.
        rewrite (beq_nat_true _ _ Hbeq); reflexivity.

        rewrite <- one_suc in Hid.
        discriminate.

      intros k Hj; rewrite Hj in *.
      simpl in *.
      apply IHalpha; try assumption.
      case_eq (beq_nat Qm Pn); intros Hbeq;
        rewrite Hbeq in *.
        assumption.

        rewrite <- one_suc in *; discriminate.
Qed.

Lemma at_pred_occ_id_fwd : forall (alpha : SecOrder) (i : nat) (Q : predicate),
  occ_in_alpha alpha i = true ->
    identify_fwd alpha Q i = 0 ->
      at_pred (preds_in alpha) i = Q.
Proof.
  induction alpha; intros i Q Hocc Hid.
    try destruct p as [Pn]; try destruct f;
    try destruct Q as [Qm]; try destruct f0.
    simpl in *.
    rewrite Hocc in *.
    apply occ_in_alpha_predSO in Hocc.
    rewrite Hocc in *.
    case_eq (beq_nat Qm Pn); intros Hbeq; rewrite Hbeq in *.
      rewrite (beq_nat_true _ _ Hbeq).
      reflexivity.

      discriminate.

    rewrite occ_in_alpha_relatSO in *; discriminate.
    rewrite occ_in_alpha_eqFO in *; discriminate.

    simpl in *; rewrite Hocc in Hid.
    rewrite occ_in_alpha_allFO in Hocc.
    apply IHalpha; assumption.

    simpl in *; rewrite Hocc in Hid.
    rewrite occ_in_alpha_exFO in Hocc;
    destruct f;
    apply IHalpha; assumption.

    simpl in *; rewrite Hocc in Hid.
    rewrite occ_in_alpha_negSO in Hocc.
    apply IHalpha; assumption.

    apply at_pred_occ_id_fwd_conjSO; assumption.
    apply at_pred_occ_id_fwd_conjSO; assumption.
    apply at_pred_occ_id_fwd_conjSO; assumption.
    apply at_pred_occ_id_fwd_allSO; assumption.
    apply at_pred_occ_id_fwd_allSO; assumption.
Qed.


Lemma at_pred_occ_rep_pred_predSO : forall (cond : SecOrder) (i : nat) (x y: FOvariable)
                                    (P Q : predicate),
  is_unary_predless cond = true ->
  occ_in_alpha (predSO P y) i = true ->
  occ_in_alpha (replace_pred (predSO P y) Q x cond) (identify_fwd (predSO P y) Q i) = false ->
  at_pred (preds_in (predSO P y)) i = Q.
Proof.
  intros cond i x y P Q Hcond Hocc1 Hocc2.
  apply at_pred_occ_id_fwd; try assumption.
  destruct P as [Pn]; destruct y;
  destruct Q as [Qm].
  simpl; rewrite Hocc1.
  case_eq (beq_nat Qm Pn); intros Hbeq.
    reflexivity.

    simpl in Hocc2; rewrite Hbeq in Hocc2;
    rewrite Hocc1 in Hocc2; rewrite Hocc1 in Hocc2.
    discriminate.
Qed.

Lemma at_pred_occ_rep_pred_conjSO : forall (alpha1 alpha2 cond : SecOrder) (i : nat) (x: FOvariable)
                                    (Q : predicate),
  (forall (cond : SecOrder) (i : nat) (x : FOvariable) (Q : predicate),
           is_unary_predless cond = true ->
           occ_in_alpha alpha1 i = true ->
           occ_in_alpha (replace_pred alpha1 Q x cond) (identify_fwd alpha1 Q i) = false ->
           at_pred (preds_in alpha1) i = Q) ->
  (forall (cond : SecOrder) (i : nat) (x : FOvariable) (Q : predicate),
           is_unary_predless cond = true ->
           occ_in_alpha alpha2 i = true ->
           occ_in_alpha (replace_pred alpha2 Q x cond) (identify_fwd alpha2 Q i) = false ->
           at_pred (preds_in alpha2) i = Q) ->
  is_unary_predless cond = true ->
  occ_in_alpha (conjSO alpha1 alpha2) i = true ->
  occ_in_alpha (replace_pred (conjSO alpha1 alpha2) Q x cond)
          (identify_fwd (conjSO alpha1 alpha2) Q i) = false ->
  at_pred (preds_in (conjSO alpha1 alpha2)) i = Q.
Proof.
  intros alpha1 alpha2 cond i x Q IHalpha1 IHalpha2 Hcond Hocc1 Hocc2.
  simpl in *; rewrite Hocc1 in *; destruct Q as [Qm].
  apply occ_in_alpha_conjSO2_fwd2 in Hocc1.
  apply occ_in_alpha_f in Hocc2.
  destruct Hocc1 as [Hocc1 | Hocc1].
    rewrite Hocc1 in *.
    destruct Hocc2.
      rewrite at_pred_app_l.
        apply at_pred_occ_id_fwd.
          assumption.
          apply beq_nat_true.
          assumption.
          apply occ_in_alpha_leb2 in Hocc1.
          apply PeanoNat.Nat.leb_le.
          apply Hocc1.

        rewrite at_pred_app_l.
          apply IHalpha1 with (cond := cond) (x := x);
            try assumption.
          unfold occ_in_alpha.
          simpl in H.
          rewrite app_length in H.
          rewrite (contrapos_bool_tt _ _ (leb_plus_r _ _ _) H).
          apply if_then_else_false.

          apply occ_in_alpha_leb2 in Hocc1.
          apply PeanoNat.Nat.leb_le.
          apply Hocc1.

    destruct Hocc1 as [Hl Hr].
    assert (i - length (preds_in alpha1) + length (preds_in alpha1) = i).
      rewrite arith_plus_minus_assoc.
      rewrite arith_minus_refl.
      rewrite arith_minus_zero.
      reflexivity.

      destruct (occ_in_alpha_f _ _ Hl) as [H1 | H2].
        rewrite (beq_nat_true _ _ H1) in *.
        simpl in Hr; rewrite occ_in_alpha_0 in Hr; discriminate.

        apply leb_switch; assumption.

        apply leb_refl.

    rewrite <- H.
    rewrite arith_plus_comm.
    case_eq (beq_nat (i - length (preds_in alpha1)) 0); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq) in *.
      rewrite occ_in_alpha_0 in Hr.
      discriminate.
    rewrite at_pred_app_r.
    destruct Hocc2 as [Hocc2 | Hocc2].
      rewrite <- arith_plus_minus_assoc2 in Hocc2.
        rewrite Hl in Hocc2.
        apply beq_nat_zero in Hocc2.
        apply beq_nat_true in Hocc2.
        apply at_pred_occ_id_fwd; try assumption.

        apply num_occ_preds_in.

      rewrite Hl in Hocc2.
      apply IHalpha2 with (cond := cond) (x := x); try assumption.
        unfold occ_in_alpha.
        simpl in Hocc2.
        rewrite app_length in Hocc2.
        rewrite preds_in_rep_pred in Hocc2; try assumption.
        rewrite <- arith_plus_minus_assoc2 in Hocc2.
          rewrite arith_plus_comm in Hocc2.
          rewrite <- leb_plus_pre in Hocc2.
          rewrite Hocc2.
          rewrite if_then_else_false.
          reflexivity.

          apply num_occ_preds_in.

          assumption.
Qed.

Lemma at_pred_occ_rep_pred_allSO : forall (alpha cond : SecOrder) (i : nat) (x : FOvariable)
                                    (P Q : predicate),
  (forall (cond : SecOrder) (i : nat) (x : FOvariable) (Q : predicate),
          is_unary_predless cond = true ->
          occ_in_alpha alpha i = true ->
          occ_in_alpha (replace_pred alpha Q x cond) (identify_fwd alpha Q i) = false ->
          at_pred (preds_in alpha) i = Q) ->
  is_unary_predless cond = true ->
  occ_in_alpha (allSO P alpha) i = true ->
  occ_in_alpha (replace_pred (allSO P alpha) Q x cond) (identify_fwd (allSO P alpha) Q i) =
        false ->
  at_pred (preds_in (allSO P alpha)) i = Q.
Proof.
  intros alpha cond i x P Q IHalpha Hcond Hocc1 Hocc2.
  rewrite occ_in_alpha_allSO in *.
  rewrite rep_pred_allSO in Hocc2.
  destruct P as [Pn]; destruct Q as [Qm].
  simpl preds_in in *.
  case_eq i.
    intros Hi; rewrite Hi in *.
    simpl in *; rewrite occ_in_alpha_0 in Hocc1.
    discriminate.

    intros j Hi; rewrite Hi in *.
    simpl in Hocc1; rewrite arith_minus_zero in *.
    case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *.
    simpl identify_fwd in Hocc2.
    rewrite occ_in_alpha_allSO in Hocc2.
    simpl in Hocc2.
    rewrite arith_minus_zero in Hocc2.
    rewrite beq_nat_comm in Hbeq.
    rewrite Hbeq in *.
    case_eq j.
      intros Hj; rewrite Hj in *.
      simpl in *.
      rewrite (beq_nat_true _ _ Hbeq).
      reflexivity.

      intros k Hj; rewrite Hj in *.
      simpl in *.
      rewrite <- (beq_nat_true _ _ Hbeq) in Hocc2.
      rewrite Hocc1 in *.
      apply IHalpha with (cond := cond) (x := x);
        assumption.

    rewrite occ_in_alpha_allSO in Hocc2.
    simpl in Hocc2.
    rewrite occ_in_alpha_allSO in *.
    simpl in *.
    rewrite arith_minus_zero in *.
    rewrite beq_nat_comm in Hbeq.
    rewrite Hbeq in *.
    case_eq j.
      intros Hj; rewrite Hj in *.
      simpl in *; rewrite identify_fwd_0 in Hocc2.
      simpl in *; discriminate.

      intros k Hj; rewrite Hj in *.
      simpl in *;  rewrite Hocc1 in *.
      case_eq (identify_fwd alpha (Pred Qm) (S k)).
        intros H; rewrite H in *.
        simpl in *;  discriminate.

        intros n H; rewrite H in *; simpl in *.
        rewrite <- one_suc in Hocc2; simpl in *.
        apply IHalpha with (cond := cond) (x := x); try assumption.
        rewrite H; assumption.
Qed.

Lemma at_pred_occ_rep_pred_exSO : forall (alpha cond : SecOrder) (i : nat) (x : FOvariable)
                                    (P Q : predicate),
  (forall (cond : SecOrder) (i : nat) (x : FOvariable) (Q : predicate),
          is_unary_predless cond = true ->
          occ_in_alpha alpha i = true ->
          occ_in_alpha (replace_pred alpha Q x cond) (identify_fwd alpha Q i) = false ->
          at_pred (preds_in alpha) i = Q) ->
  is_unary_predless cond = true ->
  occ_in_alpha (exSO P alpha) i = true ->
  occ_in_alpha (replace_pred (exSO P alpha) Q x cond) (identify_fwd (exSO P alpha) Q i) =
        false ->
  at_pred (preds_in (exSO P alpha)) i = Q.
Proof.
  intros alpha cond i x P Q IHalpha Hcond Hocc1 Hocc2.
  rewrite occ_in_alpha_exSO in *.
  rewrite rep_pred_exSO in Hocc2.
  destruct P as [Pn]; destruct Q as [Qm].
  simpl preds_in in *.
  case_eq i.
    intros Hi; rewrite Hi in *.
    simpl in *; rewrite occ_in_alpha_0 in Hocc1.
    discriminate.

    intros j Hi; rewrite Hi in *.
    simpl in Hocc1; rewrite arith_minus_zero in *.
    case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *.
    simpl identify_fwd in Hocc2.
    rewrite occ_in_alpha_exSO in Hocc2.
    simpl in Hocc2.
    rewrite arith_minus_zero in Hocc2.
    rewrite beq_nat_comm in Hbeq.
    rewrite Hbeq in *.
    case_eq j.
      intros Hj; rewrite Hj in *.
      simpl in *.
      rewrite (beq_nat_true _ _ Hbeq).
      reflexivity.

      intros k Hj; rewrite Hj in *.
      simpl in *.
      rewrite <- (beq_nat_true _ _ Hbeq) in Hocc2.
      rewrite Hocc1 in *.
      apply IHalpha with (cond := cond) (x := x);
        assumption.

    rewrite occ_in_alpha_exSO in Hocc2.
    simpl in Hocc2.
    rewrite occ_in_alpha_exSO in *.
    simpl in *.
    rewrite arith_minus_zero in *.
    rewrite beq_nat_comm in Hbeq.
    rewrite Hbeq in *.
    case_eq j.
      intros Hj; rewrite Hj in *.
      simpl in *; rewrite identify_fwd_0 in Hocc2.
      simpl in *; discriminate.

      intros k Hj; rewrite Hj in *.
      simpl in *;  rewrite Hocc1 in *.
      case_eq (identify_fwd alpha (Pred Qm) (S k)).
        intros H; rewrite H in *.
        simpl in *;  discriminate.

        intros n H; rewrite H in *; simpl in *.
        rewrite <- one_suc in Hocc2; simpl in *.
        apply IHalpha with (cond := cond) (x := x); try assumption.
        rewrite H; assumption.
Qed.



Lemma at_pred_occ_rep_pred : forall (alpha cond : SecOrder) (i : nat) (x : FOvariable)
                                    (Q : predicate),
  is_unary_predless cond = true ->
    occ_in_alpha alpha i = true ->
      occ_in_alpha (replace_pred alpha Q x cond) (identify_fwd alpha Q i) = false ->
        at_pred (preds_in alpha) i = Q.
Proof.
  induction alpha; intros  cond i x Q Hcond Hocc1 Hocc2;
  destruct Q as [Qm]; try destruct f.

    apply at_pred_occ_rep_pred_predSO with (cond := cond) (x := x); assumption.

    rewrite occ_in_alpha_relatSO in Hocc1; discriminate.
    rewrite occ_in_alpha_eqFO in Hocc1; discriminate.

    simpl in *.
    rewrite occ_in_alpha_allFO in *.
    rewrite occ_in_alpha_allFO in Hocc2.
    rewrite Hocc1 in *.
    apply (IHalpha _ _ _ _ Hcond Hocc1 Hocc2).

    simpl in *.
    rewrite occ_in_alpha_exFO in *.
    rewrite occ_in_alpha_exFO in Hocc2.
    rewrite Hocc1 in *.
    apply (IHalpha _ _ _ _ Hcond Hocc1 Hocc2).

    simpl in *.
    rewrite occ_in_alpha_negSO in *.
    rewrite occ_in_alpha_negSO in Hocc2.
    rewrite Hocc1 in *.
    apply (IHalpha _ _ _ _ Hcond Hocc1 Hocc2).

    apply at_pred_occ_rep_pred_conjSO with (cond := cond) (x := x); assumption.
    apply at_pred_occ_rep_pred_conjSO with (cond := cond) (x := x); assumption.
    apply at_pred_occ_rep_pred_conjSO with (cond := cond) (x := x); assumption.
    apply at_pred_occ_rep_pred_allSO with (cond := cond) (x := x); assumption.
    apply at_pred_occ_rep_pred_exSO with (cond := cond) (x := x); assumption.
Qed.
