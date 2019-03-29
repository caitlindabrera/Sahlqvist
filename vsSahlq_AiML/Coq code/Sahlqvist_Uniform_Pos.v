Require Export Classical.

(* Require Import SecOrder. *)
Require Export P_occurs_in_alpha.
Require Export ST_setup.
Require Export Correctness_ST.
Require Export Coq.Arith.EqNat my_bool.
Require Export List_machinery_impl My_List_Map.
Require Export Unary_Predless nList_egs Rep_Pred_FOv Indicies Identify.
Require Export pos_SO2 Num_Occ Bool my_bool Is_Pos_Rep_Pred P_occ_rep_pred.
Require Export Uniform_Defns Monotonicity_SO Pre_Sahlqvist_Uniform_Pos P_occ_rep_pred.
Require Export Unary_Predless_l Num_Occ_l2 my_arith__my_leb_nat.

Notation "'existsT' x .. y , p" := (sig (fun x => .. (sig (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'existsT'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope. 

Notation "'existsT2' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'existsT2'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.


Lemma is_un_predless_rep_pred_l_pre : forall 
                          (l : list predicate)
                          (alpha : SecOrder)
                          (l1: nlist (length l))
                          (l2 : nlist (length l)),
is_unary_predless_l (nlist_list _ l2) = true ->
length (preds_in (replace_pred_l alpha l
                (nlist_list _ l1)
                (nlist_list _ l2))) =  length (preds_in alpha) - num_occ_l2 alpha l.
Proof.
  intros l. induction l; intros alpha l1 l2 Hun.
    simpl in *.
    rewrite num_occ_l2_0.
    rewrite arith_minus_zero.
    reflexivity.

    simpl in *.
    destruct (nlist_cons2 _ l1) as [x [l1' H1]].
    destruct (nlist_cons2 _ l2) as [beta [l2' H2]].
    rewrite H1 in *; rewrite H2 in *.
    simpl in *.
    case_eq (is_unary_predless beta); intros Hun2; rewrite Hun2 in *.
    rewrite preds_in_rep_pred; try assumption.
    rewrite num_occ_l2_cons.
    case_eq (occ_in_l l a); intros Hocc.
      rewrite IHl; try assumption.
      rewrite num_occ__in_l_t; try assumption.
      rewrite arith_minus_zero.
      reflexivity.

      rewrite IHl; try assumption.
      rewrite num_occ__in_l_f; try assumption.
      rewrite arith_plus_comm.
      rewrite arith_minus_exp.
      reflexivity.

    discriminate.
Qed.



Lemma is_un_predless_rep_pred_l : forall (alpha : SecOrder)
                          (l1: nlist (length (preds_in alpha)))
                          (l2 : nlist (length (preds_in alpha))),
is_unary_predless_l (nlist_list _ l2) = true ->
is_unary_predless (replace_pred_l alpha (preds_in alpha)
                (nlist_list _ l1)
                (nlist_list _ l2)) = true.
Proof.
  pose proof is_un_predless_rep_pred_l_pre as H2.
  intros alpha l1 l2 H.
  specialize (H2 (preds_in alpha) alpha l1 l2 H).
  rewrite num_occ_l2_preds_in in H2.
  rewrite arith_minus_refl in H2.
  apply un_predless_preds_in2 in H2.
  assumption.
Qed.



Lemma Ip_ext_pa_f : forall (W : Set) 
                    (Ip : predicate -> W -> Prop)
                    (P : predicate)
                    (pa : W -> Prop),
  Ip_extends W (alt_Ip Ip pa_f P) (alt_Ip Ip pa P) P.
Proof.
  intros W Ip P pa.
  unfold Ip_extends.
  apply conj.
    intros w H.
    unfold pa_f in *.
    destruct P.
    simpl in *.
    rewrite <- beq_nat_refl in *.
    contradiction.

    intros Q.
    destruct P as [Pn]; destruct Q as [Qm].
    intros H.
    unfold not in *.
    unfold pa_f.
    simpl.
    case_eq (beq_nat Pn Qm); intros Hbeq.
      specialize (H (beq_nat_true _ _ Hbeq)).
      contradiction.

      reflexivity.
Qed.

Lemma mono1 : forall (W : Set) (Iv : FOvariable -> W)
                    (Ip : predicate -> W -> Prop)
                    (Ir : W -> W -> Prop)
                    (alpha : SecOrder) (P : predicate)
                    (pa : W -> Prop),
  P_is_pos_SO alpha P ->
  SOturnst W Iv (alt_Ip Ip pa_f P) Ir alpha ->
  SOturnst W Iv (alt_Ip Ip pa P) Ir alpha.
Proof.
  intros W Iv Ip Ir alpha P pa Hpos Hf.
  pose proof monotonicity_SO as H.
  unfold alpha_upward_monotone_P in H.
  pose proof (P_is_pos_occ _ _ Hpos) as H2.
  specialize (H alpha P H2).
  destruct H as [Ha Hb].
  apply Ha with (Ip := (alt_Ip Ip pa_f P));
  try assumption.
  apply Ip_ext_pa_f.
Qed.

Lemma step1_empty : forall (W : Set) (Iv : FOvariable -> W)
                    (Ip : predicate -> W -> Prop)
                    (Ir : W -> W -> Prop)
                    (alpha : SecOrder) (P : predicate),
  SOQFree alpha = true ->
  P_is_pos_SO alpha P ->
  SOturnst W Iv Ip Ir (replace_pred alpha P (Var 1)
                          (negSO (eqFO (Var 1) (Var 1)))) ->
    forall pa : W -> Prop,
      SOturnst W Iv (alt_Ip Ip pa P) Ir alpha.
Proof.
  intros W Iv Ip Ir alpha P SOQFree Hpos SOt pa.
  apply rep_pred_false_pa_f in SOt; try assumption.
  apply mono1; assumption.
Qed.

Lemma step2_empty : forall (l : list predicate)
                    (W : Set) (Iv : FOvariable -> W)
                    (Ip : predicate -> W -> Prop)
                    (Ir : W -> W -> Prop)
                    (alpha : SecOrder),
  SOQFree alpha = true ->
  uniform_pos_SO alpha ->
    (SOturnst W Iv Ip Ir (replace_pred_l alpha l
          (nlist_list _ (nlist_Var1 (length l)))
          (nlist_list _ (nlist_empty (length l))))) ->
  forall pa_l : nlist_pa W (length l),
    SOturnst W Iv (alt_Ip_list Ip
     (nlist_list_pa W (length l) pa_l) l) Ir alpha.
Proof.
  induction l;
    intros W Iv Ip Ir alpha Hno Huni SOt pa_l.
    simpl in *.
    rewrite alt_Ip_list_nil.
    apply SOt.

    simpl in pa_l.
    destruct (nlist_cons W (length l) pa_l) as [pa [pa_l' Heq]].
    rewrite Heq in *.
    simpl nlist_list_pa in *.
    simpl alt_Ip_list in *.
    simpl nlist_list in *.
    simpl replace_pred_l in *.
    case_eq (P_occurs_in_alpha alpha a); intros HPocc.
      apply step1_empty; try assumption.
        unfold uniform_pos_SO in Huni.
        apply Huni.
        assumption.

        apply IHl.
          apply SOQFree_rep_pred_empty.
          assumption. (* reflexivity.*)
        apply uni_pos_rep_pred.
          simpl; reflexivity.
          assumption.

        rewrite rep_pred__l_switch_empty.
        apply SOt.

      apply P_not_occ_alt.
        assumption.

        apply IHl; try assumption.

          rewrite P_occ_rep_pred_f in SOt.
            assumption.

            apply P_occ_rep_pred_l_empty;
            assumption.
Qed.

Lemma step3_empty : forall (W : Set) (Iv : FOvariable -> W)
                    (Ip : predicate -> W -> Prop)
                    (Ir : W -> W -> Prop)
                    (alpha : SecOrder),
  SOQFree alpha = true ->
  uniform_pos_SO alpha ->
    (SOturnst W Iv Ip Ir (replace_pred_l alpha (preds_in alpha)
          (nlist_list _ (nlist_Var1 (length (preds_in alpha))))
          (nlist_list _ (nlist_empty (length (preds_in alpha)))))) ->
  SOturnst W Iv Ip Ir (uni_closed_SO alpha).
Proof.
  intros. 
  unfold uni_closed_SO.
  apply nlist_list_closed_SO.
  apply step2_empty; assumption.
Qed.


Lemma Sahlqvist_uniform_pos_pre : forall (phi : Modal) (x : FOvariable),
  uniform_pos phi ->
    exists (alpha : SecOrder),
      (forall (D : Set) (Iv:FOvariable -> D) (Ip: predicate -> D -> Prop)
             (Ir: D -> D -> Prop),
      SOturnst D Iv Ip Ir (uni_closed_SO (allFO x (ST phi x))) <->
        SOturnst D Iv Ip Ir alpha) /\
      is_unary_predless alpha = true.
Proof.
  intros phi x Hun.
  exists (replace_pred_l (allFO x (ST phi x))
          (preds_in (allFO x (ST phi x)))
          (nlist_list _ (nlist_Var1 (length (preds_in (ST phi x)))))
          (nlist_list _ (nlist_empty (length (preds_in (ST phi x)))) )).
  apply conj.
    intros D Iv Ip Ir.
    apply conj.
      apply instant_uni_closed; assumption.

    simpl; intros H.
    apply step3_empty.
      destruct x; simpl.
      apply SOQFree_ST.

      apply uni_pos_SO_allFO.
      apply uni_pos__SO ; assumption.

      apply H.

      rewrite rep_pred_l_allFO.
      destruct x.       simpl.
      apply is_un_predless_rep_pred_l.
      apply un_predless_l_empty.
Defined.

Lemma Sahlqvist_uniform_pos : forall (phi : Modal),
  uniform_pos phi ->
    exists (alpha : SecOrder),
    ((forall (W : Set) (R : W -> W -> Prop) (Iv : FOvariable -> W)
           (Ip : predicate -> W -> Prop),
    mturnst_frame W R phi <-> SOturnst W Iv Ip R alpha) /\
    is_unary_predless alpha = true).
Proof.
  intros phi Hpos.
  apply Sahlqvist_uniform_pos_pre with (x := (Var 1)) in Hpos.
  destruct Hpos as [alpha H].
  exists alpha. 
  apply conj.
    intros W R Iv Ip.
    split; intros H2.
      apply H.
      apply correctness_ST; assumption.

      destruct (correctness_ST W R (Var 1) Iv Ip phi) as [fwd rev].
      apply rev.
      apply H.
      assumption.

      apply H.
Defined.

(*
Extraction Language Haskell.
Extraction "Testing_Sahlq_un_pos" Sahlqvist_uniform_pos.
*)

(*
Print Assumptions Sahlqvist_uniform_pos.

Extraction Language Haskell.
Extraction "Test_Sahlq_Uniform2" Sahlqvist_uniform_pos.
Extraction Library Modal.
*)