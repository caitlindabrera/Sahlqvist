Add LoadPath "~/Nextcloud/Coq Files/Sahlqvist/Sahlq_Modules/vsSahlq local".

Require Import  my_arith__my_leb_nat List.
Require Import Arith.EqNat my_bool My_Prop.
Require Export vsSahlq_preprocessing1.

(* Given aa conditional, return the antecedent. Don't care about other
   inputs. *)
Fixpoint vsSahlq_dest_SO_ante alpha :=
  match alpha with
  | predSO _ _ => alpha
  | relatSO _ _ => alpha
  | eqFO _ _ => alpha
  | allFO x beta => alpha
  | exFO x beta => alpha
  | negSO beta => alpha
  | conjSO beta1 beta2 => alpha
  | disjSO beta1 beta2 => alpha
  | implSO beta1 beta2 => beta1
  | allSO Q beta => alpha
  | exSO Q beta => alpha
  end.

(* Given aa conditional, return the consequent. Don't care about other
   inputs. *)
Fixpoint vsSahlq_dest_SO_cons alpha :=
  match alpha with
  | predSO _ _ => alpha
  | relatSO _ _ => alpha
  | eqFO _ _ => alpha
  | allFO x beta => alpha
  | exFO x beta => alpha
  | negSO beta => alpha
  | conjSO beta1 beta2 => alpha
  | disjSO beta1 beta2 => alpha
  | implSO beta1 beta2 => beta2
  | allSO Q beta => alpha
  | exSO Q beta => alpha
  end.

Fixpoint predSO_vars_list alpha P : list FOvariable :=
  match alpha with
    predSO Q x => match P, Q with Pred Pn, Pred Qm =>
      if beq_nat Pn Qm then cons x nil else nil
                  end
  | relatSO _ _ => nil
  | eqFO _ _ => nil
  | allFO x beta => predSO_vars_list beta P
  | exFO x beta => predSO_vars_list beta P
  | negSO beta => predSO_vars_list beta P
  | conjSO beta1 beta2 => app (predSO_vars_list beta1 P) (predSO_vars_list beta2 P)
  | disjSO beta1 beta2 => app (predSO_vars_list beta1 P) (predSO_vars_list beta2 P)
  | implSO beta1 beta2 => app (predSO_vars_list beta1 P) (predSO_vars_list beta2 P)
  | allSO Q beta => predSO_vars_list beta P
  | exSO Q beta => predSO_vars_list beta P
  end.

Fixpoint is_in (n : nat) (l : list nat) : bool :=
  match l with
  | nil => false
  | cons m l' => if beq_nat n m then true else is_in n l'
  end.

Fixpoint is_in_pred (P : predicate) (l : list predicate) : bool :=
  match P with Pred Pn =>
  match l with
  | nil => false
  | cons (Pred Qm) l' => if beq_nat Pn Qm then true else is_in_pred P l'
  end end.

(* Returns a list of preds that are in l2 but not l1 *)
Fixpoint list_pred_not_in (l1 l2 : list predicate) : list predicate :=
  match l2 with
  | nil => nil
  | cons P l2' => if is_in_pred P l1 then list_pred_not_in l1 l2'
                                else cons P (list_pred_not_in l1 l2')
  end.

(* Instantiates any of the predicates that occur in the consequent of alpha
  but not in the antecedent of alpha with "falsum". *)
Definition instant_cons_empty alpha : SecOrder :=
  replace_pred_l alpha (list_pred_not_in (preds_in (vsSahlq_dest_SO_ante alpha))
                                         (preds_in (vsSahlq_dest_SO_cons alpha)))
          (nlist_list _ (nlist_Var1 (length
              (list_pred_not_in (preds_in (vsSahlq_dest_SO_ante alpha))
                                (preds_in (vsSahlq_dest_SO_cons alpha))))))
          (nlist_list _ (nlist_empty (length 
              (list_pred_not_in (preds_in (vsSahlq_dest_SO_ante alpha))
                                (preds_in (vsSahlq_dest_SO_cons alpha)))))).

Lemma instant_cons_empty_predSO : forall P x,
  instant_cons_empty (predSO P x) = (predSO P x).
Proof.
  unfold instant_cons_empty.
  intros [Pn] [xn].
  simpl; rewrite <- beq_nat_refl.
  reflexivity.
Qed.

Lemma instant_cons_empty_relatSO : forall x y,
  instant_cons_empty (relatSO x y) = (relatSO x y).
Proof.
  unfold instant_cons_empty.
  intros [xn] [ym].
  reflexivity.
Qed.

Lemma instant_cons_empty_eqFO : forall x y,
  instant_cons_empty (eqFO x y) = (eqFO x y).
Proof.
  unfold instant_cons_empty.
  intros [xn] [ym].
  reflexivity.
Qed.


Lemma list_pred_not_in_contains : forall l2 l1,
  (forall P, is_in_pred P l2 = true -> is_in_pred P l1 = true) ->
  list_pred_not_in l1 l2 = nil.
Proof.
  induction l2; intros l1 H.
    reflexivity.

    simpl in *.
    destruct a as [Qm].
    pose proof H as H'.
    specialize (H (Pred Qm)).
    simpl in *.
    rewrite <- beq_nat_refl in H.
    rewrite H; try reflexivity.
    apply IHl2.
    intros [Pn] H2.
    specialize (H' (Pred Pn)).
    apply H'.
    rewrite H2.
    apply if_then_else_true.
Qed.

Lemma list_pred_not_in_refl : forall l,
  list_pred_not_in l l = nil.
Proof.
  intros l.
  apply list_pred_not_in_contains.
  intros P H.
  assumption.
Qed.

Lemma P_occ_in_l_is_in_pred : forall l P,
  is_in_pred P l = false ->
  P_occurs_in_l l P = false.
Proof.
  induction l; intros P H.
    reflexivity.

    destruct P as [Pn]; destruct a as [Qm].
    simpl in *.
    case_eq (beq_nat Pn Qm); intros Hbeq;
      rewrite Hbeq in *. discriminate.
    apply IHl.
    assumption.
Qed.

Lemma P_occ_in_alpha_is_in_pred : forall alpha P,
  is_in_pred P (preds_in alpha) = false ->
  P_occurs_in_alpha alpha P = false.
Proof.
  intros alpha P.
  unfold P_occurs_in_alpha.
  apply P_occ_in_l_is_in_pred.
Qed.

Lemma rep_pred_not_in : forall alpha P x cond,
  is_in_pred P (preds_in alpha) = false ->
  replace_pred alpha P x cond = alpha.
Proof.
  intros alpha P x cond H.
  apply P_occ_rep_pred_f.
  apply P_occ_in_alpha_is_in_pred.
  assumption.
Qed.

Lemma rep_pred_l_not_in : forall l2 alpha,
  replace_pred_l alpha (list_pred_not_in (preds_in alpha) l2)
    (nlist_list _ (nlist_Var1 (length (list_pred_not_in (preds_in alpha) l2))))
    (nlist_list _ (nlist_empty (length (list_pred_not_in (preds_in alpha) l2)))) =
  alpha.
Proof.
  induction l2; intros alpha.
    reflexivity.

    simpl.
    destruct a as [Pn].
    case_eq (is_in_pred (Pred Pn) (preds_in alpha)); intros H1.
      apply IHl2.

      simpl.
      rewrite IHl2.
      apply rep_pred_not_in. assumption.
Qed.

Lemma instant_cons_empty_implSO : forall alpha beta,
  instant_cons_empty (implSO alpha beta) =
    implSO alpha
  (replace_pred_l beta (list_pred_not_in (preds_in alpha) (preds_in beta))
     (nlist_list _
        (nlist_Var1 (length (list_pred_not_in (preds_in alpha) (preds_in beta)))))
     (nlist_list _
        (nlist_empty (length (list_pred_not_in (preds_in alpha) (preds_in beta)))))).
Proof.
  intros alpha beta.
  unfold instant_cons_empty.
  simpl.
  rewrite rep_pred_l_implSO.
  rewrite rep_pred_l_not_in.
  reflexivity.
Qed.

Lemma list_closed_SO_pa_choose : forall l beta W Iv Ip Ir,
(forall pa_l : nlist_pa W (length l),
     SOturnst W Iv
       (altered_Ip_list Ip
          (nlist_list_pa W (length l) pa_l) l) Ir beta) ->
SOturnst W Iv Ip Ir beta.
Proof. 
  induction l; intros beta W Iv Ip Ir H.
    specialize (H (niln_pa W)).
    simpl in *.
    assumption.

    simpl in *.
    apply IHl.
    intros pa_l.
    specialize (H (consn_pa _ _ ((altered_Ip_list Ip (nlist_list_pa W (length l) pa_l) l) a) pa_l) ).
    simpl in H.
    rewrite unaltered_fun in H. 
    assumption.
Qed.

Lemma uni_pos_SO_SOturnst_f_gen : forall beta l W Iv Ip Ir,
  SOQFree beta = true ->
  uniform_pos_SO beta ->
   SOturnst W Iv Ip Ir (replace_pred_l beta (list_pred_not_in l (preds_in beta))
     (nlist_list _
        (nlist_Var1 (length (list_pred_not_in l (preds_in beta)))))
     (nlist_list _
        (nlist_empty (length (list_pred_not_in l (preds_in beta)))))) ->
    SOturnst W Iv Ip Ir beta.
Proof. 
  intros beta l W Iv Ip Ir Hno Hun SOt.
  pose proof (step2_empty _ _ _ _ _ _ Hno Hun SOt) as H.
  apply list_closed_SO_pa_choose in H.
  assumption.
Qed.

Lemma try3a : forall l beta W Iv Ip Ir,
(forall pa_l : nlist_pa W (length l),
     SOturnst W Iv
       (altered_Ip_list Ip
          (nlist_list_pa W (length l) pa_l) l) Ir beta) ->
SOturnst W Iv Ip Ir beta.
Proof. 
  induction l; intros beta W Iv Ip Ir H.
    specialize (H (niln_pa W)).
    simpl in *.
    assumption.

    simpl in *.
    apply IHl.
    intros pa_l.
    specialize (H (consn_pa _ _ ((altered_Ip_list Ip (nlist_list_pa W (length l) pa_l) l) a) pa_l) ).
    simpl in H.
    rewrite unaltered_fun in H. 
    assumption.
Qed.

Lemma try1 : forall beta l W Iv Ip Ir,
  SOQFree beta = true ->
  uniform_pos_SO beta ->
   SOturnst W Iv Ip Ir (replace_pred_l beta (list_pred_not_in l (preds_in beta))
     (nlist_list _
        (nlist_Var1 (length (list_pred_not_in l (preds_in beta)))))
     (nlist_list _
        (nlist_empty (length (list_pred_not_in l (preds_in beta)))))) ->
    SOturnst W Iv Ip Ir beta.
Proof. 
  intros beta l W Iv Ip Ir Hno Hun SOt.
  pose proof (step2_empty _ _ _ _ _ _ Hno Hun SOt) as H.
  apply try3a in H.
  assumption.
Qed.

Lemma instant_cons_empty_equiv : forall alpha beta W Iv Ip Ir,
  SOQFree beta = true ->
  uniform_pos_SO beta ->
  SOturnst W Iv Ip Ir (instant_cons_empty (implSO alpha beta)) ->
  SOturnst W Iv Ip Ir (implSO alpha beta).
Proof.
  intros alpha beta W Iv Ip Ir Hno Hun.
  rewrite instant_cons_empty_implSO.
  simpl.
  intros H1 H2;
    specialize (H1 H2).
    apply try1 in H1; assumption.
Qed.


Lemma instant_cons_empty_equiv_list1 : forall l alpha beta W Iv Ip Ir,
  SOQFree beta = true ->
  uniform_pos_SO beta ->
  SOturnst W Iv Ip Ir (list_closed_SO (instant_cons_empty (implSO alpha beta)) l) ->
  SOturnst W Iv Ip Ir (list_closed_SO (implSO alpha beta) l).
Proof.
  induction l; intros alpha beta W Iv Ip Ir Hno Hun SOt.
    simpl in SOt.
    simpl list_closed_SO.
    apply instant_cons_empty_equiv; assumption.

    destruct a as [Pn].
    simpl list_closed_SO in *.
    rewrite SOturnst_allSO in *.
    intros pa.
    specialize (SOt pa).
    apply IHl; assumption.
Qed.


(* ----------------------------------------------- *)

Fixpoint is_in_pred_l l1 l2 : bool :=
  match l1 with
  | nil => true
  | cons P l1' => if is_in_pred P l2 then is_in_pred_l l1' l2 else false
  end.

Lemma is_in_pred_l_nil : forall l,
  is_in_pred_l l nil = true -> l = nil.
Proof.
  induction l; intros H.
    reflexivity.

    destruct a.
    simpl in *.
    discriminate.
Qed.

Lemma app_rnil_l : forall {A : Type} l1 l2,
  app l1 l2 = nil -> l1 = (@nil A).
Proof.
  intros A l1; induction l1; intros l2 H.
    reflexivity.

    simpl in *.
    inversion H.
Qed.

Lemma app_rnil_r : forall {A : Type} l1 l2,
  app l1 l2 = nil -> l2 = (@nil A).
Proof.
  intros A l1; induction l1; intros l2 H.
    simpl in *. assumption.

    simpl in *.
    inversion H.
Qed.

Lemma instant_cons_empty_nil : forall alpha beta,
  preds_in alpha = nil ->
  preds_in beta = nil ->
  instant_cons_empty (implSO alpha beta) = implSO alpha beta.
Proof.
  intros alpha beta H1 H2.
  unfold instant_cons_empty.  
  simpl.
  rewrite H1.
  rewrite H2.
  simpl.
  reflexivity.
Qed.

Lemma is_in_pred_l_cons : forall l1 l2 P,
  is_in_pred P l1 = false ->
  is_in_pred_l l1 (cons P l2) = true ->
  is_in_pred_l l1 l2 = true.
Proof.
  induction l1; intros l2 [Pn] H1 H2.
    reflexivity.

    destruct a as [Qm].
    simpl in *.
    case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *.
      discriminate.
    rewrite beq_nat_comm in Hbeq.
    rewrite Hbeq in *.
    case_eq (is_in_pred (Pred Qm) l2); intros H;
      rewrite H in *.
      apply IHl1 with (P := (Pred Pn)); assumption.

      discriminate.
Qed. 

Lemma is_in_pred_l_app_r : forall l1 l2 l,
  is_in_pred_l (app l1 l2) l = true ->
  is_in_pred_l l2 l = true.
Proof.
  induction l1; intros l2 l H.
    simpl in *.
    assumption.

    destruct a as [Qm].
    simpl in *.
    case_eq (is_in_pred (Pred Qm) l); intros Hin;
      rewrite Hin in *.
      apply IHl1; assumption.

      discriminate.
Qed.

Fixpoint nlist_P n (P : predicate) : nlist n :=
  match n with
  | 0 => niln
  | S m => consn _ P (nlist_P m P)
  end.

Lemma nlist_P_plus : forall n m P,
  nlist_list _ (nlist_P (n + m) P) = app (nlist_list _ (nlist_P n P))
                                       (nlist_list _ (nlist_P m P)).
Proof.
  induction n; intros m P.
    reflexivity.

    simpl.
    rewrite IHn.  
    reflexivity.
Qed.

Lemma is_in_pred_l_cons_nil_allSO : forall alpha Qm Pn,
  (forall P : predicate,
          is_in_pred_l (preds_in alpha) (P :: nil) = true ->
          preds_in alpha = nil \/
          (exists n : nat, preds_in alpha = nlist_list n (nlist_P n P))) ->
  (is_in_pred_l (preds_in (allSO (Pred Qm) alpha)) (Pred Pn :: nil) = true) ->
preds_in (allSO (Pred Qm) alpha) = nil \/
(exists n : nat,
   preds_in (allSO (Pred Qm) alpha) = nlist_list n (nlist_P n (Pred Pn))).
Proof.
  intros alpha Qm Pn IHalpha H.
    simpl in *.
    case_eq (beq_nat Qm Pn); intros Hbeq; rewrite Hbeq in *;
      try discriminate.
    destruct (IHalpha _ H) as [IH | IH];
    rewrite (beq_nat_true _ _ Hbeq).
      right.
      exists 1. rewrite IH.
      reflexivity.

      destruct IH as [n IH].
      right. rewrite IH.
      exists (S n).
      reflexivity.
Qed.

Lemma is_in_pred_nlist_P : forall n P,
  is_in_pred P (nlist_list (S n) (nlist_P (S n) P)) = true.
Proof.
  induction n; intros [Pn].
    simpl.
    rewrite <- beq_nat_refl.
    reflexivity.

    simpl.
    rewrite <- beq_nat_refl.
    reflexivity.
Qed.

Lemma is_in_pred_l_f_l : forall l1 l2 P,
  is_in_pred_l l1 l2 = false ->
  is_in_pred_l l1 (cons P l2) = true ->
  is_in_pred P l1 = true.
Proof.
  induction l1; intros l2 [Pn] H1 H2.
    simpl in *. discriminate.

    destruct a as [Qm].
    simpl in *.
    case_eq (beq_nat Pn Qm); intros Hbeq.
      reflexivity.

      rewrite beq_nat_comm in Hbeq.
      rewrite Hbeq in *.
      case_eq (is_in_pred (Pred Qm) l2); intros H3;
        rewrite H3 in *.
        apply IHl1 with (l2 := l2); assumption.

        discriminate.
Qed.

Lemma is_in_pred_l_cons_f : forall l1 l2 P,
  is_in_pred_l l1 (cons P l2) = false ->
  is_in_pred_l l1 l2 = false.
Proof.
  induction l1; intros l2 [Pn] H.
    simpl in *. discriminate.

    destruct a as [Qm].
    simpl in *.
    case_eq (beq_nat Qm Pn); intros Hbeq;
      rewrite Hbeq in *.
      rewrite IHl1 with (P := (Pred Pn)); try assumption.
      rewrite if_then_else_false.
      reflexivity.

      case_eq (is_in_pred (Pred Qm) l2); intros H2;
        rewrite H2 in *.
        apply IHl1 with (P := (Pred Pn)); assumption.
        reflexivity.
Qed.

Lemma list_closed_SO_impl : forall l alpha W Iv Ip Ir,
  SOturnst W Iv Ip Ir (list_closed_SO alpha l) ->
  SOturnst W Iv Ip Ir alpha.
Proof.
  induction l; intros alpha W Iv Ip Ir SOt.
    simpl in *.
    assumption.

    destruct a as [Qm]. simpl list_closed_SO in SOt.
    rewrite SOturnst_allSO in SOt.
    specialize (SOt (Ip (Pred Qm))).
    rewrite unaltered_fun in SOt.
    apply IHl; assumption.
Qed.

Lemma uni_closed_SO_impl : forall alpha W Iv Ip Ir,
  SOturnst W Iv Ip Ir (uni_closed_SO alpha) ->
  SOturnst W Iv Ip Ir alpha.
Proof.
  intros. unfold uni_closed_SO in *.
  apply list_closed_SO_impl in H; assumption.
Qed.

Lemma uni__list_closed_SO : forall l alpha W Iv Ip Ir,
  SOturnst W Iv Ip Ir (uni_closed_SO alpha) ->
  SOturnst W Iv Ip Ir (list_closed_SO alpha l).
Proof.
  induction l; intros alpha W Iv Ip Ir SOt.
    simpl in *.
    apply uni_closed_SO_impl. assumption.

    destruct a as [Qm].
    intros pa.
    apply IHl.
    apply Ip_uni_closed with (Ip := Ip).
    assumption.
Qed.

Lemma instant_cons_empty_equiv_list2 : forall alpha beta W Iv Ip Ir,
  SOturnst W Iv Ip Ir (list_closed_SO (instant_cons_empty (implSO alpha beta))
                            (preds_in (instant_cons_empty (implSO alpha beta)))) ->
  SOturnst W Iv Ip Ir (list_closed_SO (instant_cons_empty (implSO alpha beta))
                            (preds_in (implSO alpha beta))).
Proof.
  intros alpha beta W Iv Ip Ir SOt.
  apply uni__list_closed_SO.
  unfold uni_closed_SO.
  assumption.
Qed.


Lemma list_pred_not_in_nil : forall l,
  list_pred_not_in nil l = l.
Proof.
  induction l.
    reflexivity.

    destruct a as [Pn].
    simpl.
    rewrite IHl.
    reflexivity.
Qed.


Fixpoint free_SO (alpha : SecOrder) (P : predicate)  : bool :=
  match alpha with
    predSO Q y => match P, Q with 
                     | Pred Pn, Pred Qm => beq_nat Pn Qm
                     end
  | relatSO _ _ => false
  | eqFO _ _ => false
  | allFO y beta => free_SO beta P
  | exFO y beta => free_SO beta P
  | negSO beta => free_SO beta P
  | conjSO beta1 beta2 => if free_SO beta1 P then true
                             else free_SO beta2 P
  | disjSO beta1 beta2 => if free_SO beta1 P then true
                             else free_SO beta2 P
  | implSO beta1 beta2 => if free_SO beta1 P then true
                             else free_SO beta2 P
  | allSO Q beta => if match P, Q with 
                       | Pred Pn, Pred Qm => beq_nat Pn Qm
                       end  
                       then false else free_SO beta P
  | exSO Q beta => if match P, Q with 
                       | Pred Pn, Pred Qm => beq_nat Pn Qm
                       end  
                       then false else free_SO beta P
  end.

Fixpoint no_free_SO_l (alpha : SecOrder) (l : list predicate) :=
  match l with
  | nil => true
  | cons P l' => if free_SO alpha P then false else no_free_SO_l alpha l'
  end.

Lemma list_pred_not_in_nlist_P_cons : forall n P,
  list_pred_not_in (cons P nil) (nlist_list n (nlist_P _ P)) = nil.
Proof.
  induction n; intros [Pn].
    reflexivity.

    simpl.
    rewrite <- beq_nat_refl.
    apply IHn.
Qed.

Lemma list_pred_not_in_cons_cons : forall l l2 P,
  list_pred_not_in (cons P (cons P l)) l2 = list_pred_not_in (cons P l) l2.
Proof.
  induction l; intros l2 [Pn].
    induction l2.
      reflexivity.

      destruct a as [Qm].
      simpl.
      case_eq (beq_nat Qm Pn); intros Hbeq.
        apply IHl2.

        rewrite IHl2.
        reflexivity.

    destruct a as [Qm].
    induction l2.
      reflexivity.

      destruct a as [Rn].
      simpl.
      case_eq (beq_nat Rn Pn); intros Hbeq2.
        apply IHl2.

        case_eq (beq_nat Rn Qm); intros Hbeq3.
          apply IHl2.

          rewrite IHl2.
          reflexivity.
Qed.

Lemma list_pred_not_in_P : forall n1 n2 P,
  list_pred_not_in (nlist_list (S n1) (nlist_P _ P))
                   (nlist_list (S n2) (nlist_P _ P)) = nil.
Proof.
  induction n1; intros n2 [Pn].
    simpl.
    rewrite <- beq_nat_refl.
    apply list_pred_not_in_nlist_P_cons.

    simpl in *.
    rewrite <- beq_nat_refl.
    rewrite list_pred_not_in_cons_cons.
    specialize (IHn1 n2 (Pred Pn)).
    simpl in IHn1.
    rewrite <- beq_nat_refl in IHn1.
    assumption.
Qed.

Lemma is_in_pred_list_closed_SO : forall l alpha P W Iv Ip Ir pa,
  is_in_pred P l = true ->
  SOturnst W Iv Ip Ir (list_closed_SO alpha l) ->
  SOturnst W Iv (altered_Ip Ip pa P) Ir (list_closed_SO alpha l).
Proof.
  induction l; intros alpha [Pn] W Iv Ip Ir pa Hin SOt.
    simpl in *. discriminate.

    simpl list_closed_SO in *.
    destruct a as [Qm].
    intros pa2.
    specialize (SOt pa2).
    case_eq (beq_nat Pn Qm); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq) in *.
      rewrite altered_Ip_eq.
      assumption.

      rewrite altered_Ip_switch.
      apply IHl.
        simpl in Hin.
        rewrite Hbeq in Hin.
        assumption.

        assumption.

      intros H; rewrite H in *.
      rewrite <- beq_nat_refl in Hbeq.
      discriminate.
Qed.

Lemma is_in_pred_cons_f : forall l Q P,
  is_in_pred Q (cons P l) = false ->
  is_in_pred Q l = false.
Proof.
  induction l; intros [Qm] [Pn] H.
    reflexivity.

    destruct a as [Rn].
    simpl in *.
    case_eq (beq_nat Qm Rn); intros Hbeq; rewrite Hbeq in *.
      rewrite if_then_else_true in H.
      discriminate.

      apply IHl with (P := Pred Pn).
      case_eq (beq_nat Qm Pn); intros Hbeq2; rewrite Hbeq2 in *.
        discriminate.

        assumption.
Qed.

Lemma rep_pred__l_switch : forall lP alpha lx lcond P x cond,
  is_in_pred P lP = false ->
  is_unary_predless cond = true ->
  is_unary_predless_l lcond = true ->
  replace_pred (replace_pred_l alpha lP lx lcond) P x cond =
  replace_pred_l (replace_pred alpha P x cond) lP lx lcond.
Proof.
  induction lP; intros alpha lx lcond [Qm] [ym] cond Hin Hun1 Hun2.
    reflexivity.

    destruct a as [Pn].
    case_eq lx.
      intros Hlx. reflexivity.

      intros [xn] lx' Hlx.
      case_eq lcond.
        intros Hlcond. reflexivity.

        intros beta lcond' Hlcond.
        simpl.

        rewrite Hlcond in Hun2.
        simpl in Hun2.
        case_eq (is_unary_predless beta); intros Hun3; 
          rewrite Hun3 in *; try discriminate.

        rewrite <- IHlP.
        case_eq (beq_nat Pn Qm); intros Hbeq.
          rewrite (beq_nat_true _ _ Hbeq) in Hin.
          simpl in Hin.
          rewrite <- beq_nat_refl in Hin.
          discriminate.

          rewrite (rep_pred_switch _ (Var xn) (Var ym)
             beta cond (Pred Pn) (Pred Qm)).
          reflexivity. all: try assumption.

          intros H; rewrite H in Hbeq; rewrite <- beq_nat_refl in Hbeq.
          discriminate.

          apply is_in_pred_cons_f with (P := (Pred Pn)).
          assumption.
Qed.

Lemma rep_pred__l_is_in : forall n lP alpha lx lcond P x cond,
  is_in_pred P (nlist_list n lP) = true ->
  is_unary_predless_l (nlist_list n lcond) = true ->
  is_unary_predless cond = true ->
  replace_pred (replace_pred_l alpha 
      (nlist_list n lP) (nlist_list n lx) (nlist_list n lcond)) P x cond =
  replace_pred_l alpha (nlist_list n lP) (nlist_list n lx) (nlist_list n lcond).
Proof.
  induction n; intros lP alpha lx lcond [Pn] [xn] cond Hin Hun Hun2.
    rewrite (nlist_nil2 lP) in *.
    simpl in *. discriminate.

    destruct (nlist_cons2 _ lP) as [[Qm] [lP' lPeq]].
    destruct (nlist_cons2 _ lcond) as [beta [lcond' lcondeq]].
    destruct (nlist_cons2 _ lx) as [[xm] [lx' lxeq]].
    rewrite lPeq; rewrite lcondeq; rewrite lxeq.
    simpl.
    case_eq (beq_nat Pn Qm); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq) in *.
      rewrite P_occ_rep_pred_f.
        reflexivity.
        apply P_occ_in_alpha_rep_pred_f.
        rewrite lcondeq in Hun; simpl in Hun.
        case_eq (is_unary_predless beta); intros Hun4;
          rewrite Hun4 in *; try discriminate.
          reflexivity.

      rewrite lPeq in Hin.
      rewrite lcondeq in Hun.
      simpl in *.
      rewrite Hbeq in *.
      case_eq (is_unary_predless beta); intros Hun3; rewrite Hun3 in *;
        try discriminate.
      pose proof (rep_pred_switch (replace_pred_l alpha (nlist_list n lP') (nlist_list n lx')
        (nlist_list n lcond')) (Var xm) (Var xn) beta cond
          (Pred Qm) (Pred Pn)) as Heq.
      simpl in Heq.
      rewrite Heq.
      rewrite IHn. reflexivity.
      all: try assumption.
      intros H; rewrite H in Hbeq; rewrite <- beq_nat_refl in Hbeq.
      discriminate.
Qed.

Lemma rep_pred_list_closed_pre_predSO : forall p f,
  forall (P : predicate) (cond : SecOrder) (x : FOvariable) 
  (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop),
is_unary_predless cond = true ->
SOturnst W Iv Ip Ir (allSO P (predSO p f)) ->
SOturnst W Iv Ip Ir
  (allSO P (replace_pred (predSO p f) P x (negSO (eqFO (Var 1) (Var 1))))).
Proof.
  intros [Qm] [ym] [Pn] cond [xn] W Iv Iip Ir Hun SOt.
  simpl replace_pred.
  case_eq (beq_nat Pn Qm); intros Hbeq.
    simpl in SOt.
    rewrite Hbeq in SOt.
    intros pa.
    specialize (SOt pa_f).
    unfold pa_f in SOt.
    contradiction.

    assumption.
Qed.

Lemma rep_pred_list_closed_pre_relatSO : forall f f0 (P : predicate) (cond : SecOrder) (x : FOvariable) 
  (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop),
is_unary_predless cond = true ->
SOturnst W Iv Ip Ir (allSO P (relatSO f f0)) ->
SOturnst W Iv Ip Ir
  (allSO P (replace_pred (relatSO f f0) P x (negSO (eqFO (Var 1) (Var 1))))).
Proof.
  intros [x1] [x2] [Pn] cond [x] W Iv Ip Ir Hun SOt.
  simpl in *.
  assumption.
Qed.

Lemma rep_pred_list_closed_pre_eqFO : forall f f0 (P : predicate) (cond : SecOrder) (x : FOvariable) 
  (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop),
is_unary_predless cond = true ->
SOturnst W Iv Ip Ir (allSO P (eqFO f f0)) ->
SOturnst W Iv Ip Ir
  (allSO P (replace_pred (eqFO f f0) P x (negSO (eqFO (Var 1) (Var 1))))).
Proof.
  intros [x1] [x2] [Pn] cond [x] W Iv Ip Ir Hun SOt.
  simpl in *.
  assumption.
Qed.

Lemma SOt_alt_SOQFree' : forall (alpha : SecOrder) (W : Set)
                      (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
                    (Ir : W -> W -> Prop)  (Q : predicate) x,
  SOQFree alpha = true ->
    (SOturnst W Iv (altered_Ip Ip pa_f Q) Ir alpha <->
      SOturnst W Iv Ip Ir (replace_pred alpha Q x
       (negSO (eqFO (Var 1) (Var 1))))).
Proof.
  induction alpha; intros W Iv Ip Ir Q [ym] HallSO.
    unfold pa_f.
    simpl in *.
    destruct p as [Pn]; destruct f as [xn]; destruct Q as [Qm].
    case_eq (beq_nat Qm Pn); intros Hbeq.
      rewrite (beq_nat_true Qm Pn Hbeq).
      simpl.
      rewrite <- beq_nat_refl.
      split; intros H.
        contradiction.

        unfold not in *.
        case_eq (beq_nat ym 1); intros Hbeq2; rewrite Hbeq2 in *;
          simpl in H; contradiction (H eq_refl).

      simpl.
      rewrite Hbeq in *.
      apply bi_refl.

    simpl in *.
    destruct f as [xn]; destruct f0 as [xm].
    destruct Q as [Qm].
    simpl.
    apply bi_refl.

    destruct f as [xn]; destruct f0 as [xm].
    destruct Q as [Qm].
    simpl.
    apply bi_refl.

    rewrite rep_pred_allFO.
    do 2 rewrite SOturnst_allFO.
    pose proof (SOQFree_allFO alpha f HallSO) as HallSO'.
    split; intros H d.
      (apply IHalpha; [assumption | apply H]).
      specialize (H d).
      apply IHalpha in H. assumption. assumption.

    rewrite rep_pred_exFO.
    do 2 rewrite SOturnst_exFO.
    pose proof (SOQFree_exFO alpha f HallSO) as HallSO'.
    split; intros H; destruct H as [d H]; exists d.
      apply IHalpha; assumption.
      apply IHalpha in H; assumption.

    rewrite rep_pred_negSO.
    do 2 rewrite SOturnst_negSO.
    split; intros H;
      unfold not; intros H2;
      apply H.
      apply IHalpha in H2;
      assumption.
      apply IHalpha;
      assumption.

    rewrite rep_pred_conjSO.
    do 2 rewrite SOturnst_conjSO.
    pose proof (SOQFree_conjSO_l alpha1 alpha2 HallSO) as H1.
    pose proof (SOQFree_conjSO_r alpha1 alpha2 HallSO) as H2.
    simpl in HallSO.
    split; intros H; apply conj.
      apply IHalpha1; [assumption | apply H].
      apply IHalpha2; [assumption | apply H].
      destruct H as [Ha Hb].
      apply IHalpha1 in Ha; assumption.
      destruct H as [Ha Hb].
      apply IHalpha2 in Hb; assumption.

    rewrite rep_pred_disjSO.
    do 2 rewrite SOturnst_disjSO.
    pose proof (SOQFree_disjSO_l alpha1 alpha2 HallSO) as H1.
    pose proof (SOQFree_disjSO_r alpha1 alpha2 HallSO) as H2.
    split; intros H;
      destruct H as [H | H].
      left; apply IHalpha1; assumption.
      right; apply IHalpha2; assumption.
      left; apply IHalpha1 in H; assumption.
      right; apply IHalpha2 in H; assumption.

    rewrite rep_pred_implSO.
    do 2 rewrite SOturnst_implSO.
    pose proof (SOQFree_implSO_l alpha1 alpha2 HallSO) as H1.
    pose proof (SOQFree_implSO_r alpha1 alpha2 HallSO) as H2.
    split; intros H H3.
      apply IHalpha2; [assumption | apply H; apply IHalpha1 in H3;
          assumption].
      apply IHalpha1 with (x := (Var ym)) in H3. specialize (H H3).
        apply IHalpha2 in H. all: try assumption.

    simpl in HallSO.
    destruct p; discriminate.

    simpl in HallSO.
    destruct p; discriminate.
Qed.



Lemma rep_pred_list_closed_pre : forall alpha P x W Iv Ip Ir,
  SOQFree alpha = true ->
  SOturnst W Iv Ip Ir (allSO P alpha) ->
  SOturnst W Iv Ip Ir (allSO P (replace_pred alpha P x (negSO (eqFO (Var 1) (Var 1))))).
Proof.
  intros alpha [Pn] [xn] W Iv Ip Ir Hno SOt.
  intros pa. apply SOt_alt_SOQFree'.
    assumption.

    rewrite altered_Ip_eq.
    apply SOt.
Qed.


Lemma list_closed_SO_switch : forall l alpha P Q W Iv Ip Ir,
  SOturnst W Iv Ip Ir (list_closed_SO alpha (cons P (cons Q l))) ->
  SOturnst W Iv Ip Ir (list_closed_SO alpha (cons Q (cons P l))).
Proof.
  intros l alpha [Pn] [Qm]  W Iv Ip Ir SOt.
  intros paQ paP.
  case_eq (beq_nat Pn Qm); intros Hbeq.
    rewrite (beq_nat_true _ _ Hbeq) in *.
    specialize (SOt paP paP).
    rewrite altered_Ip_eq in *.
    assumption.

    rewrite altered_Ip_switch.
    specialize (SOt paP paQ).
    assumption.

    intros H; rewrite H in *; rewrite <- beq_nat_refl in Hbeq.
    discriminate.
Qed.

Lemma rep_pred_list_closed : forall l alpha P x W Iv Ip Ir,
  SOQFree alpha = true ->
  SOturnst W Iv Ip Ir (list_closed_SO alpha (cons P l)) ->
  SOturnst W Iv Ip Ir (list_closed_SO (replace_pred alpha P x (negSO (eqFO (Var 1) (Var 1)))) (cons P l)).
Proof.
  induction l; intros alpha [Pn] x W Iv Ip Ir Hno SOt.
    simpl list_closed_SO in *.
    apply rep_pred_list_closed_pre; assumption.

    destruct a as [Qm].
    apply list_closed_SO_switch.
    intros pa.
    apply list_closed_SO_switch in SOt.
    specialize (SOt pa).
    apply IHl; assumption.
Qed.


Lemma list_closed_SO_rep_pred2 : forall l alpha Pn x W Iv Ip Ir,
is_in_pred (Pred Pn) l = true ->
SOQFree alpha = true ->
SOturnst W Iv Ip Ir (list_closed_SO alpha l) ->
SOturnst W Iv Ip Ir (list_closed_SO (replace_pred alpha 
        (Pred Pn) x (negSO (eqFO (Var 1) (Var 1)))) l).
Proof.
  induction l; intros alpha Pn x W Iv Ip Ir Hin Hno SOt.
    simpl in *. discriminate.

    destruct a as [Qm].
    simpl in Hin.
    case_eq (beq_nat Pn Qm); intros Hbeq;
      rewrite Hbeq in *.
      case_eq (is_in_pred (Pred Pn) l); intros Hin2.
        intros pa.
        specialize (SOt pa).
        apply IHl; assumption.

        rewrite (beq_nat_true _ _ Hbeq) in *.
        simpl list_closed_SO.
        apply rep_pred_list_closed; assumption.

      intros pa.
      specialize (SOt pa).
      apply IHl; assumption.
Qed.


Lemma SOQFree_rep_pred' : forall (alpha : SecOrder) (Q : predicate) x,
  SOQFree alpha = true -> 
    SOQFree (replace_pred alpha Q x 
      (negSO (eqFO (Var 1) (Var 1)))) = true.
Proof.
  induction alpha.
    intros Q [ym] HSO.
    destruct p as [Pn]; destruct f as [xn]; destruct Q as [Qm].
    simpl.
    case_eq (beq_nat Qm Pn); intros Hbeq.
      case_eq (beq_nat ym 1); intros Hbeq2;
      simpl; reflexivity.

      assumption.

    intros Q HSO.
    destruct f as [xn]; destruct f0 as [xm]; destruct Q as [Qm].
    simpl; reflexivity.

    intros Q HSO.
    destruct f as [xn]; destruct f0 as [xm]; destruct Q as [Qm].
    simpl; reflexivity.

    intros Q x HSO.
    destruct Q as [Qm]; destruct f as [xn].
    simpl.
    apply IHalpha.
    assumption.

    intros Q x HSO.
    destruct Q as [Qm]; destruct f as [xn].
    simpl.
    apply IHalpha.
    assumption.

    intros Q x HSO.
    simpl.
    destruct Q as [Qm].
    simpl.
    apply IHalpha.
    assumption.

    intros Q x HSO.
    simpl.
    destruct Q as [Qm].
    simpl.
    pose proof (SOQFree_conjSO_l _ _ HSO) as H1.
    pose proof (SOQFree_conjSO_r _ _ HSO) as H2.
    rewrite IHalpha1;
      [rewrite IHalpha2 | assumption];
      [reflexivity | assumption].

    intros Q x HSO.
    simpl.
    destruct Q as [Qm].
    simpl.
    pose proof (SOQFree_disjSO_l _ _ HSO) as H1.
    pose proof (SOQFree_disjSO_r _ _ HSO) as H2.
    rewrite IHalpha1;
      [rewrite IHalpha2 | assumption];
      [reflexivity | assumption].

    intros Q x HSO.
    simpl.
    destruct Q as [Qm].
    simpl.
    pose proof (SOQFree_implSO_l _ _ HSO) as H1.
    pose proof (SOQFree_implSO_r _ _ HSO) as H2.
    rewrite IHalpha1;
      [rewrite IHalpha2 | assumption];
      [reflexivity | assumption].

    intros Q x HSO.
    simpl in HSO.
    destruct p; discriminate.

    intros Q x HSO.
    simpl in HSO.
    destruct p; discriminate.
Qed.

Lemma list_closed_instant_one_f : forall n lP l alpha lx W Iv Ip Ir,
  is_in_pred_l (nlist_list n lP) l = true ->
  SOQFree alpha = true ->
  SOturnst W Iv Ip Ir (list_closed_SO alpha l) ->
  SOturnst W Iv Ip Ir (list_closed_SO (replace_pred_l alpha 
        (nlist_list n lP) (nlist_list n lx) 
        (nlist_list n (nlist_empty _))) l).
Proof.
  induction n; intros lP l alpha lx W Iv Ip Ir Hin Hno SOt.
    rewrite (nlist_nil2 lP) in *.
    simpl in *.
    assumption.

    destruct (nlist_cons2 _ lP) as [[Pn] [lP' HlP]].
    destruct (nlist_cons2 _ lx) as [[xn] [lx' Hlx]].
    destruct (nlist_cons2 _ lx) as [[cond2] [lcond' Hlcond]].
    rewrite HlP in *; rewrite Hlx in *; rewrite Hlcond in *.
    simpl.
    simpl in Hin.
    case_eq (is_in_pred (Pred Pn) l); intros Hin5; rewrite Hin5 in *;
      try discriminate.
    case_eq (is_in_pred (Pred Pn) (nlist_list _ lP')); intros Hin2.
      rewrite rep_pred__l_is_in.
      simpl in Hin.
      case_eq (is_in_pred (Pred Pn) l); intros Hin3;
        rewrite Hin3 in *; try discriminate.
      apply IHn. all : try assumption.  
        apply un_predless_l_empty_n.
        reflexivity.

      rewrite rep_pred__l_switch.
      simpl in Hin.
      case_eq (is_in_pred (Pred Pn) l); intros Hin3;
            rewrite Hin3 in *; try discriminate.
      apply IHn; try assumption.
        apply SOQFree_rep_pred'. assumption.
        apply list_closed_SO_rep_pred2; assumption.

        assumption.
        reflexivity. apply un_predless_l_empty_n.
Qed.

Lemma is_in_pred_l_refl : forall l,
  is_in_pred_l l l = true.
Proof.
  induction l.
    reflexivity.

    destruct a.
    simpl.
    rewrite <- beq_nat_refl.
    apply (contrapos_bool_ff _ _ (is_in_pred_l_cons_f _ _ _)).
    assumption.
Qed.

Lemma is_in_pred3 : forall l P Q,
  is_in_pred P (cons Q l) = true ->
  is_in_pred P l = false ->
  P = Q.
Proof.
  intros l [Pn] [Qm] H1 H2.
  simpl in *.
  case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *.
    rewrite (beq_nat_true _ _ Hbeq).
    reflexivity.

    rewrite H1 in H2.
    discriminate.
Qed.

Lemma list_pred_not_in_is_in_t : forall l1 l2 P,
  is_in_pred P l1 = true ->
  list_pred_not_in l1 (cons P l2) = list_pred_not_in l1 l2.
Proof.
  induction l1; intros l2 [Pn] Hin.
    simpl in *. discriminate.

    destruct a as [Qm].
    simpl.
    case_eq (beq_nat Pn Qm); intros Hbeq.
      reflexivity.

      case_eq (is_in_pred (Pred Pn) l1); intros Hin2.
        reflexivity.

        apply is_in_pred3 in Hin.
        inversion Hin as [H].
        rewrite H in Hbeq.
        rewrite <- beq_nat_refl in Hbeq.
        discriminate.

      assumption.
Qed.

Lemma is_in_pred4 : forall l P,
  is_in_pred P (cons P l) = true.
Proof.
  intros l [Pn].
  simpl.
  rewrite <- beq_nat_refl.
  reflexivity.
Qed.

Lemma list_pred_not_in_is_in_f : forall l1 l2 P,
  is_in_pred P l1 = false ->
  list_pred_not_in l1 (cons P l2) = cons P (list_pred_not_in l1 l2).
Proof.
  induction l1; intros l2 [Pn] Hin.
    simpl in *. reflexivity.

    destruct a as [Qm].
    simpl.
    case_eq (beq_nat Pn Qm); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq) in *.
      rewrite is_in_pred4 in Hin.
      discriminate.

      case_eq (is_in_pred (Pred Pn) l1); intros Hin2.
        rewrite is_in_pred_cons_f with (P := Pred Qm) in Hin2.
        discriminate.

        assumption.

        reflexivity.
Qed.

Lemma is_in_pred_l2 : forall l1 l2 P,
  is_in_pred_l l1 l2 = true ->
  is_in_pred_l l1 (cons P l2) = true.
Proof.
  induction l1; intros l2 [Pn] Hin.
    reflexivity.

    destruct a as [Qm].
    simpl in *.
    case_eq (beq_nat Qm Pn); intros Hbeq.
      case_eq (is_in_pred (Pred Qm) l2); intros Hin2;
        rewrite Hin2 in *; try discriminate.
      apply IHl1.
      assumption.

      case_eq (is_in_pred (Pred Qm) l2); intros Hin2;
        rewrite Hin2 in *; try discriminate.
      apply IHl1.
      assumption.
Qed.

Lemma is_in_pred_l_add : forall l2 l1 P,
  is_in_pred_l l1 l2 = true ->
  is_in_pred_l (cons P l1) (cons P l2) = true.
Proof.
  induction l2; intros l1 [Pn] Hin.
    apply is_in_pred_l_nil in Hin.
    rewrite Hin.
    simpl. rewrite <- beq_nat_refl.
    reflexivity.

    destruct a as [Qm].
    simpl in *.
    rewrite <- beq_nat_refl.
    apply is_in_pred_l2.
    assumption.
Qed.

Lemma is_in_pred_l_list_pred_not_in : forall l2 l1,
  is_in_pred_l (list_pred_not_in l1 l2) l2 = true.
Proof.
  induction l2; intros l1.
    reflexivity.
    destruct a as [Pn].
    case_eq (is_in_pred (Pred Pn) l1); intros Hin.
      rewrite list_pred_not_in_is_in_t; try assumption.
      apply is_in_pred_l2.
      apply IHl2.

      rewrite list_pred_not_in_is_in_f; try assumption.
      apply is_in_pred_l_add.
      apply IHl2.
Qed.

Lemma is_in_pred_l_tft : forall l2 l3 P,
  is_in_pred P l2 = true ->
  is_in_pred P l3 = false ->
  is_in_pred_l l2 l3 = false.
Proof.
  induction l2; intros l3 [Pn] H1 H2.
    simpl in *. discriminate.

    destruct a as [Qm].
    simpl in *.
    case_eq (beq_nat Pn Qm); intros Hbeq;
      rewrite Hbeq in *.
      rewrite (beq_nat_true _ _ Hbeq) in *.
      rewrite H2.
      reflexivity.

      rewrite IHl2 with (P := (Pred Pn));
      try assumption.
      apply if_then_else_false.
Qed.


Lemma is_in_pred_l_trans : forall l1 l2 l3,
  is_in_pred_l l1 l2 = true ->
  is_in_pred_l l2 l3 = true ->
  is_in_pred_l l1 l3 = true.
Proof.
  induction l1; intros l2 l3 H1 H2.
    reflexivity.

    destruct a as [Pn].
    simpl in *.
    case_eq (is_in_pred (Pred Pn) l2); intros H3;
      rewrite H3 in *; try discriminate.
    case_eq (is_in_pred (Pred Pn) l3); intros H4.
      apply IHl1 with (l2 := l2); assumption.
    rewrite is_in_pred_l_tft with (P := (Pred Pn)) in H2;
      try assumption.
Qed.


Lemma list_closed_SO_instant_cons_empty : forall l alpha beta W Iv Ip Ir,
  is_in_pred_l (preds_in (implSO alpha beta)) l = true ->
  SOQFree (implSO alpha beta) = true ->
  SOturnst W Iv Ip Ir (list_closed_SO (implSO alpha beta) l) ->
  SOturnst W Iv Ip Ir (list_closed_SO (instant_cons_empty (implSO alpha beta)) l).
Proof.
  intros.
  unfold instant_cons_empty.
  simpl.
  destruct (nlist_list_ex (length (list_pred_not_in 
      (preds_in alpha) (preds_in beta)))
      (list_pred_not_in (preds_in alpha) (preds_in beta)) eq_refl)
    as [lP' HlP'].
  rewrite <- HlP'.
  rewrite length_nlist_list.
  apply list_closed_instant_one_f. 
  rewrite HlP'.
    simpl in H.
    apply is_in_pred_l_app_r in H.
    apply is_in_pred_l_trans with (l2 := preds_in beta).
    apply is_in_pred_l_list_pred_not_in.
    all:assumption.
Qed.

Lemma vsSahlq_pp_Lemma1 : forall alpha beta W Iv Ip Ir,
  SOQFree (implSO alpha beta) = true ->
  SOturnst W Iv Ip Ir (uni_closed_SO (implSO alpha beta)) ->
  SOturnst W Iv Ip Ir (list_closed_SO (instant_cons_empty (implSO alpha beta))
                        (preds_in (implSO alpha beta))).
Proof.
  unfold uni_closed_SO.
  unfold instant_cons_empty.
  simpl.
  intros.
  apply list_closed_SO_instant_cons_empty; try assumption.
    simpl.
    apply is_in_pred_l_refl.
Qed.

Lemma is_in_pred_l_consl1 : forall l1 l2 P,
  is_in_pred_l (cons P l1) l2 = true ->
  is_in_pred_l l1 l2 = true.
Proof.
  induction l1; intros l2 [Pn] H.
    reflexivity.

    destruct a as [Qm].
    simpl in *.
    case_eq (is_in_pred (Pred Pn) l2); intros His;
      rewrite His in *.
      case_eq (is_in_pred (Pred Qm) l2); intros His2;
        rewrite His2 in *. assumption.
        discriminate.

      discriminate.
Qed.

Lemma is_in_pred_l_consl2 : forall l1 l2 P,
  is_in_pred_l (cons P l1) l2 = true ->
  is_in_pred P l2 = true.
Proof.
  induction l1; intros l2 [Pn] His.
    simpl in *.
    case_eq (is_in_pred (Pred Pn) l2); intros His2;
      rewrite His2 in *. assumption. discriminate.

    destruct a as [Qm]; simpl in *.
    case_eq (is_in_pred (Pred Pn) l2); intros His2;
      rewrite His2 in *.
      reflexivity.

      discriminate.
Qed.      

Lemma allSO_switch : forall alpha P Q W Iv Ip Ir,
  SOturnst W Iv Ip Ir (allSO P (allSO Q alpha)) ->
  SOturnst W Iv Ip Ir (allSO Q (allSO P alpha)).
Proof.
  intros alpha [Pn] [Qm] W Iv Ip Ir SOt.
  rewrite SOturnst_allSO in *.
  intros paQ.
  rewrite SOturnst_allSO.
  case_eq (beq_nat Pn Qm); intros Hbeq.
    rewrite (beq_nat_true _ _ Hbeq) in *.
    intros pa2.
    rewrite altered_Ip_eq.
    specialize (SOt pa2 pa2).
    rewrite altered_Ip_eq in *.
    assumption.

    intros paP.
    specialize (SOt paP paQ).
    rewrite altered_Ip_switch. assumption.
    intros H; rewrite H in Hbeq.
    rewrite <- beq_nat_refl in Hbeq.
    discriminate.
Qed.

Lemma list_closed_SO_dup : forall l P alpha W Iv Ip Ir,
  is_in_pred P l = true ->
  SOturnst W Iv Ip Ir (list_closed_SO alpha l) ->
  SOturnst W Iv Ip Ir (list_closed_SO alpha (cons P l)).
Proof.
  induction l; intros [Pn] alpha W Iv Ip Ir His SOt.
    simpl in *.
    discriminate.

    destruct a as [Qm].
    simpl in His.
    case_eq (beq_nat Pn Qm); intros Hbeq;
      rewrite Hbeq in *.
      rewrite (beq_nat_true _ _ Hbeq) in *.
      intros pa1 pa2.
      rewrite altered_Ip_eq.
      specialize (SOt pa2).
      assumption.

      assert (SOturnst W Iv Ip Ir (list_closed_SO alpha 
                  (cons (Pred Qm) (Pred Pn :: l))) ->
              SOturnst W Iv Ip Ir (list_closed_SO alpha 
                  (cons (Pred Pn) (cons (Pred Qm) l)))) as H.
        simpl list_closed_SO; intros H. apply allSO_switch.
        assumption.
      apply H.
      intros pa.
      apply IHl.
        assumption.

        specialize (SOt pa).
        assumption.
Qed.

Lemma vsSahlq_pp_Lemma3_pre : forall l1 l2 alpha W Iv Ip Ir,
  is_in_pred_l l1 l2 = true ->
  SOturnst W Iv Ip Ir (list_closed_SO alpha l2) ->
  SOturnst W Iv Ip Ir (list_closed_SO alpha l1).
Proof.
  induction l1; intros l2 alpha W Iv Ip Ir His SOt.
    simpl in *.
    apply list_closed_SO_impl in SOt; assumption.

    destruct a as [Pn].
    intros pa.
    apply IHl1 with (l2 := l2).
      apply is_in_pred_l_consl1 in His.
      assumption.

      apply is_in_pred_l_consl2 in His.
      apply list_closed_SO_dup with (P := Pred Pn) in SOt.
      specialize (SOt pa).
      all : assumption.
Qed.

Lemma vsSahlq_pp_Lemma3 : forall l alpha W Iv Ip Ir,
  is_in_pred_l (preds_in alpha) l = true ->
  SOturnst W Iv Ip Ir (list_closed_SO alpha l) ->
  SOturnst W Iv Ip Ir (uni_closed_SO alpha).
Proof.
  intros.
  apply vsSahlq_pp_Lemma3_pre with (l2 := l); assumption.
Qed.


Lemma list_app_cons : forall {A : Type} (l1 l2 : list A) (a : A),
  app (app l1 (cons a nil)) l2 = app l1 (cons a l2).
Proof.
  intros A l1; induction l1; intros l2 b.
    reflexivity.

    simpl.
    rewrite IHl1.
    reflexivity.
Qed.

Lemma is_in_pred_cons : forall l P Q,
  match P, Q with Pred Pn, Pred Qm =>
    beq_nat Pn Qm = false  
  end ->
  is_in_pred P (cons Q l) = true ->
  is_in_pred P l = true.
Proof.
  induction l; intros [Pn] [Qm] H1 H2.
    simpl in *.
    rewrite H1 in H2.
    discriminate.

    destruct a as [Rn].
    simpl in *.
    rewrite H1 in *.
    case_eq (beq_nat Pn Rn); intros Hbeq2.
      reflexivity.

      rewrite Hbeq2 in H2.
      assumption.
Qed.

Lemma is_in_pred_app_l : forall l l' P,
  is_in_pred P l = true ->
  is_in_pred P (app l l') = true.
Proof.
  induction l; intros l' [Pn] H.
    simpl in *. discriminate.

    destruct a as [Qm].
    simpl.
    case_eq (beq_nat Pn Qm); intros Hbeq.
      reflexivity.

      apply IHl.
      apply is_in_pred_cons in H;
      assumption.
Qed.

Lemma is_in_pred_app_cons : forall l1 l2 Q,
is_in_pred Q (l1 ++ Q :: l2) = true.
Proof.
  induction l1; intros l2 [Pn].
    simpl.
    rewrite <- beq_nat_refl.
    reflexivity.

    destruct a as [Qm].
    simpl.
    case_eq (beq_nat Pn Qm); intros Hbeq.
      reflexivity.
      apply IHl1.
Qed.

Lemma is_in_pred_app_cons2 : forall l P Q,
  match P, Q with Pred Pn, Pred Qm =>
    beq_nat Pn Qm = false
  end ->
  is_in_pred P (app l (cons Q nil)) = is_in_pred P l.
Proof.
  induction l; intros [Pn] [Qm] Hbeq.
    simpl.
    rewrite Hbeq.
    reflexivity.

    destruct a as [Rn].
    simpl.
    case_eq (beq_nat Pn Rn); intros Hbeq2.
      reflexivity.
    apply IHl.
    assumption.
Qed.

Lemma app_assoc : forall {A : Type} (l1 l2 l3 : list A),
  app (app l1 l2) l3 = app l1 (app l2 l3).
Proof.
  intros A l1; induction l1; intros l2 l3.
    reflexivity.

    simpl.
    rewrite IHl1.
    reflexivity.
Qed.

Lemma is_in_pred_app_switch : forall l1 l2 P,
  is_in_pred P (app l1 l2) = is_in_pred P (app l2 l1).
Proof.
  induction l1; intros l2 [Pn].
    simpl.
    rewrite app_nil_r.
    reflexivity.

    destruct a as [Qm].
    simpl.
    case_eq (beq_nat Pn Qm); intros Hbeq.
      symmetry. rewrite (beq_nat_true _ _ Hbeq).
      apply is_in_pred_app_cons.

      rewrite <- list_app_cons.
      rewrite <- IHl1.
      rewrite <- is_in_pred_app_cons2 with (Q := (Pred Qm)).
      rewrite app_assoc.
      reflexivity.
      assumption.
Qed.

Lemma is_in_pred_app_r : forall l l' P,
  is_in_pred P l' = true ->
  is_in_pred P (app l l') = true.
Proof.
  intros l l' P H.
  rewrite is_in_pred_app_switch.
  apply is_in_pred_app_l.
  assumption.
Qed.

Lemma is_in_pred_l_app_2r : forall l l1 l2 : list predicate,
  is_in_pred_l l l2 = true ->
  is_in_pred_l l (l1 ++ l2) = true.
Proof.
  induction l; intros l1 l2 H.
    reflexivity.

    destruct a as [Pn].
    simpl in *.
    case_eq (is_in_pred (Pred Pn) l2); intros His;
      rewrite His in *; try discriminate.
    rewrite IHl; try assumption.
    rewrite is_in_pred_app_r.
      reflexivity.
      assumption.
Qed.

Lemma is_in_pred_l_2app : forall l1 l2 l3 l4,
  is_in_pred_l l1 l2 = true ->
  is_in_pred_l l3 l4 = true ->
  is_in_pred_l (app l1 l3) (app l2 l4) = true.
Proof.
  induction l1; intros l2 l3 l4 H1 H2.
    simpl in *.
    apply is_in_pred_l_app_2r.
    assumption.

    destruct a as [Pn].
    simpl in *.
    case_eq (is_in_pred (Pred Pn) l2); intros H3;
      rewrite H3 in *.
      rewrite IHl1; try assumption.
      rewrite is_in_pred_app_l.
        reflexivity.
        assumption.

      discriminate.
Qed.

Lemma is_in_pred_rep_pred_allSO : forall alpha Pn x cond Qm,
  (forall (P : predicate) (x : FOvariable) (cond : SecOrder),
          is_unary_predless cond = true ->
          is_in_pred_l (preds_in (replace_pred alpha P x cond)) (preds_in alpha) =
          true) ->
  is_unary_predless cond = true ->
is_in_pred_l (preds_in (replace_pred (allSO (Pred Qm) alpha) (Pred Pn) x cond))
  (preds_in (allSO (Pred Qm) alpha)) = true.
Proof.
  intros alpha Pn x cond Qm IHalpha Hun.
    simpl.
    case_eq (beq_nat Pn Qm); intros Hbeq.
      assert (cons (Pred Qm) (preds_in alpha) = 
        app (cons (Pred Qm) nil) (preds_in alpha)) as H by
        reflexivity.
      rewrite H.
      apply is_in_pred_l_app_2r.
      apply IHalpha; assumption.

      simpl.
      rewrite <- beq_nat_refl.
      assert (cons (Pred Qm) (preds_in alpha) = 
        app (cons (Pred Qm) nil) (preds_in alpha)) as H by
        reflexivity.
      rewrite H.
      apply is_in_pred_l_app_2r.
      apply IHalpha; assumption.
Qed.

Lemma is_in_pred_rep_pred_exSO : forall alpha Pn x cond Qm,
  (forall (P : predicate) (x : FOvariable) (cond : SecOrder),
          is_unary_predless cond = true ->
          is_in_pred_l (preds_in (replace_pred alpha P x cond)) (preds_in alpha) =
          true) ->
  is_unary_predless cond = true ->
is_in_pred_l (preds_in (replace_pred (exSO (Pred Qm) alpha) (Pred Pn) x cond))
  (preds_in (exSO (Pred Qm) alpha)) = true.
Proof.
  intros alpha Pn x cond Qm IHalpha Hun.
    simpl.
    case_eq (beq_nat Pn Qm); intros Hbeq.
      assert (cons (Pred Qm) (preds_in alpha) = 
        app (cons (Pred Qm) nil) (preds_in alpha)) as H by
        reflexivity.
      rewrite H.
      apply is_in_pred_l_app_2r.
      apply IHalpha; assumption.

      simpl.
      rewrite <- beq_nat_refl.
      assert (cons (Pred Qm) (preds_in alpha) = 
        app (cons (Pred Qm) nil) (preds_in alpha)) as H by
        reflexivity.
      rewrite H.
      apply is_in_pred_l_app_2r.
      apply IHalpha; assumption.
Qed.

Lemma is_in_pred_rep_pred : forall alpha P x cond,
  is_unary_predless cond = true ->
  is_in_pred_l (preds_in (replace_pred alpha P x cond)) 
               (preds_in alpha) = true.
Proof.
  induction alpha; intros [Pn] x cond Hun;
    try destruct p as [Qm]; try destruct f;
    try destruct f0;
    try reflexivity;
    try (simpl;  apply IHalpha; assumption);
    try (simpl; apply is_in_pred_l_2app;
      [apply IHalpha1 | apply IHalpha2];
      assumption).
    simpl.
    case_eq (beq_nat Pn Qm); intros Hbeq.
      rewrite preds_in_rep_FOv.
      apply un_predless_preds_in in Hun.
      rewrite Hun.
      reflexivity.

      simpl.
      rewrite <- beq_nat_refl.
      reflexivity.

    apply is_in_pred_rep_pred_allSO; assumption.
    apply is_in_pred_rep_pred_exSO; assumption.
Qed.



Lemma is_in_pred_l_rep_pred_l : forall lP lv lcond alpha,
  is_unary_predless_l lcond = true ->
  is_in_pred_l (preds_in (replace_pred_l alpha lP lv lcond))
               (preds_in alpha) = true.
Proof.
  induction lP; intros lv lcond alpha Hun.
    simpl.
    apply is_in_pred_l_refl.

    destruct a as [Pn].
    destruct lv.
      simpl in *.
      apply is_in_pred_l_refl.

      destruct f as [xn].
      destruct lcond.
        simpl in *.
        apply is_in_pred_l_refl.

        simpl.
        pose proof (is_in_pred_rep_pred (replace_pred_l alpha lP lv lcond)
          (Pred Pn) (Var xn) s) as H.
        simpl in Hun.
        case_eq (is_unary_predless s); intros Hun2; rewrite Hun2 in Hun;
          try discriminate.
          specialize (H Hun2).
          specialize (IHlP lv lcond alpha Hun).
          apply is_in_pred_l_trans with (l2 := (preds_in (replace_pred_l alpha lP lv lcond)));
          assumption.
Qed.

Lemma is_unary_predless_l_nlist_empty : forall n,
  is_unary_predless_l (nlist_list n (nlist_empty n)) = true.
Proof.
  induction n.
    reflexivity.

    simpl.
    assumption.
Qed.

Lemma vsSahlq_pp_Lemma4 : forall alpha beta,
  is_in_pred_l (preds_in (instant_cons_empty (implSO alpha beta)))
               (preds_in (implSO alpha beta)) = true.
Proof.
  intros alpha beta.
  unfold instant_cons_empty.
  simpl.
  apply is_in_pred_l_rep_pred_l.
  apply is_unary_predless_l_nlist_empty.
Qed.


Lemma vsSahlq_pp_Lemma2 : forall alpha beta W Iv Ip Ir,
  SOturnst W Iv Ip Ir (list_closed_SO (instant_cons_empty (implSO alpha beta))
                        (preds_in (implSO alpha beta))) ->
  SOturnst W Iv Ip Ir (uni_closed_SO (instant_cons_empty (implSO alpha beta))).
Proof.
  intros alpha beta W Iv Ip Ir Sot.
  apply vsSahlq_pp_Lemma3 with (l := (preds_in (implSO alpha beta))).
    apply vsSahlq_pp_Lemma4.
    assumption.
Qed.


Lemma instant_cons_empty_equiv2_fwd : forall alpha beta W Iv Ip Ir,
  SOQFree (implSO alpha beta) = true ->
  SOturnst W Iv Ip Ir (uni_closed_SO (implSO alpha beta)) ->
  SOturnst W Iv Ip Ir (uni_closed_SO (instant_cons_empty (implSO alpha beta))).
Proof.
  intros alpha beta W Iv Ip Ir Hno SOt.
  apply vsSahlq_pp_Lemma2.
  apply vsSahlq_pp_Lemma1;
  assumption.
Qed.

Lemma instant_cons_empty_equiv2_rev : forall alpha beta W Iv Ip Ir,
  SOQFree beta = true ->
  uniform_pos_SO beta ->
  SOturnst W Iv Ip Ir (uni_closed_SO (instant_cons_empty (implSO alpha beta))) ->
  SOturnst W Iv Ip Ir (uni_closed_SO (implSO alpha beta)).
Proof.
  intros alpha beta W Iv Ip Ir Hno Hun SOt.
  unfold uni_closed_SO in *.
  pose proof instant_cons_empty_equiv_list1.
  apply instant_cons_empty_equiv_list2 in SOt.
  apply instant_cons_empty_equiv_list1; assumption.
Qed.

Lemma instant_cons_empty_equiv2 : forall alpha beta W Iv Ip Ir,
  SOQFree (implSO alpha beta) = true ->
  uniform_pos_SO beta ->
  SOturnst W Iv Ip Ir (uni_closed_SO (implSO alpha beta)) <->
  SOturnst W Iv Ip Ir (uni_closed_SO (instant_cons_empty (implSO alpha beta))).
Proof.
  intros. split; intros SOt.
    apply instant_cons_empty_equiv2_fwd; assumption.
    apply SOQFree_implSO_r in H.
    apply instant_cons_empty_equiv2_rev; assumption.
Qed.

Lemma equiv_list_closed_SO_allFO : forall l alpha x W Iv Ip Ir,
  SOturnst W Iv Ip Ir (list_closed_SO (allFO x alpha) l) <->
  SOturnst W Iv Ip Ir (allFO x (list_closed_SO alpha l)).
Proof.
  intros l alpha [xn] W Iv Ip Ir.
  split; intros SOt.
    intros d.
    apply nlist_list_closed_SO.
    intros pa_l.
    destruct (nlist_list_closed_SO W Iv Ir (allFO (Var xn) alpha) l Ip) as [fwd rev].
    apply fwd.
    assumption.

    apply nlist_list_closed_SO.
    intros pa_l d.
    destruct (nlist_list_closed_SO W (altered_Iv Iv d (Var xn)) Ir alpha l Ip) as [fwd rev].
    apply fwd.
    apply SOt.
Qed.

Lemma equiv_uni_closed_SO_allFO : forall alpha x W Iv Ip Ir,
  SOturnst W Iv Ip Ir (uni_closed_SO (allFO x alpha)) <->
  SOturnst W Iv Ip Ir (allFO x (uni_closed_SO alpha)).
Proof.
  intros.
  unfold uni_closed_SO.
  apply equiv_list_closed_SO_allFO.
Qed.

Lemma equiv_list_closed_SO_list_closed_allFO : forall lv lP alpha W Iv Ip Ir,
  SOturnst W Iv Ip Ir (list_closed_SO (list_closed_allFO alpha lv) lP) <->
  SOturnst W Iv Ip Ir (list_closed_allFO (list_closed_SO alpha lP) lv).
Proof.
  induction lv; intros lP alpha W Iv Ip Ir.
    simpl. apply bi_refl.

    destruct a as [xn].
    simpl list_closed_allFO.
    split; intros SOt.
      apply equiv_list_closed_SO_allFO in SOt.
      intros d. apply IHlv. apply SOt.

      apply equiv_list_closed_SO_allFO.
      intros d. apply IHlv. apply SOt.
Qed.

Lemma preds_in_list_closed_allFO : forall l alpha,
  preds_in (list_closed_allFO alpha l) = preds_in alpha.
Proof.
  induction l; intros alpha.
    reflexivity.

    simpl.
    apply IHl.
Qed.

Lemma equiv_uni_closed_SO_list_closed_allFO : forall lv alpha W Iv Ip Ir,
  SOturnst W Iv Ip Ir (uni_closed_SO (list_closed_allFO alpha lv)) <->
  SOturnst W Iv Ip Ir (list_closed_allFO (uni_closed_SO alpha) lv).
Proof.
  intros. unfold uni_closed_SO.
  rewrite preds_in_list_closed_allFO.
  apply equiv_list_closed_SO_list_closed_allFO.
Qed.

Lemma equiv_allFO : forall alpha beta,
  (forall W Iv Ip Ir, 
    SOturnst W Iv Ip Ir alpha <-> SOturnst W Iv Ip Ir beta) ->
  forall W Iv Ip Ir x,
    SOturnst W Iv Ip Ir (allFO x alpha) <->
    SOturnst W Iv Ip Ir (allFO x beta).
Proof.
  intros alpha beta H W Iv Ip Ir x.
  do 2 rewrite SOturnst_allFO.
  split; intros H2;
    intros d; apply H; apply H2.
Qed.

Lemma equiv_list_closed_allFO : forall alpha beta lv,
  (forall W Iv Ip Ir, 
    SOturnst W Iv Ip Ir alpha <-> SOturnst W Iv Ip Ir beta) ->
  forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir (list_closed_allFO alpha lv) <->
    SOturnst W Iv Ip Ir (list_closed_allFO beta lv).
Proof.
  intros alpha beta lv. 
  induction lv; intros H W Iv Ip Ir.
    simpl; apply H.

    do 2 rewrite list_closed_allFO_cons.
    apply equiv_allFO. intros. apply IHlv.
    apply H.
Qed.

Lemma instant_cons_empty_equiv2_list_closed_allFO : forall l alpha beta W Iv Ip Ir,
  SOQFree (implSO alpha beta) = true ->
  uniform_pos_SO beta ->
  SOturnst W Iv Ip Ir (uni_closed_SO (list_closed_allFO (implSO alpha beta) l)) <->
  SOturnst W Iv Ip Ir (uni_closed_SO (list_closed_allFO (instant_cons_empty (implSO alpha beta)) l)).
Proof.
  intros l alpha beta W Iv Ip Ir Hno Hun.
  split; intros SOt.
    apply equiv_uni_closed_SO_list_closed_allFO.
    apply equiv_list_closed_allFO with 
        (alpha := (uni_closed_SO (implSO alpha beta))).
      intros.
      apply instant_cons_empty_equiv2; assumption.
    apply equiv_uni_closed_SO_list_closed_allFO.
    assumption.

    apply equiv_uni_closed_SO_list_closed_allFO.
    apply equiv_list_closed_allFO with 
        (alpha := (uni_closed_SO (instant_cons_empty (implSO alpha beta)))).
      intros. split; intros H;
      apply instant_cons_empty_equiv2; assumption.
    apply equiv_uni_closed_SO_list_closed_allFO.
    assumption.
Qed.

Lemma instant_cons_empty_equiv2_list_closed__allFO : forall l alpha beta x W Iv Ip Ir,
  SOQFree (implSO alpha beta) = true ->
  uniform_pos_SO beta ->
  SOturnst W Iv Ip Ir (uni_closed_SO (allFO x (list_closed_allFO (implSO alpha beta) l))) <->
  SOturnst W Iv Ip Ir (uni_closed_SO (allFO x (list_closed_allFO (instant_cons_empty (implSO alpha beta)) l))).
Proof.
  intros l alpha beta [xn] W Iv Ip Ir.
  split; intros SOt;
    apply equiv_uni_closed_SO_allFO;
    apply equiv_uni_closed_SO_allFO in SOt;
    intros d; specialize (SOt d);
    apply instant_cons_empty_equiv2_list_closed_allFO;
    assumption.
Qed.
