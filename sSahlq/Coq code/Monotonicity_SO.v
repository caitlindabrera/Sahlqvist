Require Import SecOrder Modal ST_setup p_is_pos P_occurs_in_alpha p_occurs_in.
Require Import P_occurs_in_alpha nList_egs Occ_In_Alpha.
Require Import Arith.EqNat my_bool pos_SO2 neg_SO2 my_arith__my_leb_nat.

(* ---------------------------------------------------------------------------- *)
(* Monotonicity *)

Definition Ip_extends (W : Set) (Ip Ip' : predicate -> W -> Prop) 
                     (P : predicate) :=
  (forall (w : W), (Ip P w) -> (Ip' P w))
    /\ forall (Q : predicate),
         (match P, Q with
            Pred n, Pred m =>
              ~(n = m) -> (Ip Q = Ip' Q)
          end).

Definition alpha_upward_monotone_P (alpha : SecOrder) (P : predicate) :=
    forall (W : Set) (Iv : FOvariable -> W) (R : W -> W -> Prop)
           (Ip Ip' : predicate -> W -> Prop),
   Ip_extends W Ip Ip' P
      -> (SOturnst W Iv Ip R alpha) ->
                          (SOturnst W Iv Ip' R alpha).

Definition alpha_downward_monotone_P (alpha : SecOrder) (P : predicate) :=
    forall (W : Set) (Iv : FOvariable -> W) (R : W -> W -> Prop)
           (Ip Ip' : predicate -> W -> Prop),
   Ip_extends W Ip' Ip P
      -> (SOturnst W Iv Ip R alpha) ->
                          (SOturnst W Iv Ip' R alpha).

Definition ST_p (p : propvar) : predicate :=
  match p with
    pv n => Pred n
  end.


(* ---------------------------------------------------------------------------- *)

Lemma up_not_occ_SO : forall (alpha : SecOrder) (P : predicate),
  P_occurs_in_alpha alpha P = false ->
    (alpha_upward_monotone_P alpha P /\ alpha_downward_monotone_P alpha P).
Proof.
  intros alpha P; induction alpha;
  unfold alpha_upward_monotone_P in *;
  unfold alpha_downward_monotone_P in *;
    intros Hocc.
    apply conj; intros W Iv R Ip Ip' Ipext SOt;
    unfold P_occurs_in_alpha in Hocc;
    unfold Ip_extends in Ipext;
    destruct Ipext as [l r];
    destruct P as [Pn]; destruct p as [Qm];
    destruct f as [xn];
      simpl in *;
      case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *;
        try discriminate;
      apply beq_nat_false in Hbeq;
      specialize (r (Pred Qm)); simpl in r;
      specialize (r Hbeq);
      apply equal_f with (x := (Iv (Var xn))) in r.
        rewrite r in SOt. assumption.
        rewrite r. assumption.

    destruct f; destruct f0.
    apply conj; intros W Iv R Ip Ip' Ipext SOt;
    simpl in *; assumption.

    destruct f; destruct f0.
    apply conj; intros W Iv R Ip Ip' Ipext SOt;
    simpl in *; assumption.

    apply conj; intros W Iv R Ip Ip' Ipext SOt;
      rewrite SOturnst_allFO in *;
      intros d; specialize (SOt d);
      rewrite <- P_occurs_in_alpha_allFO in Hocc;
      destruct (IHalpha Hocc) as [l r].
      apply l with (Ip := Ip); assumption.
      apply r with (Ip := Ip); assumption.

    apply conj; intros W Iv R Ip Ip' Ipext SOt;
      rewrite SOturnst_exFO in *;
      destruct SOt as [d SOt]; exists d;
      rewrite <- P_occurs_in_alpha_exFO in Hocc;
      destruct (IHalpha Hocc) as [l r].
      apply l with (Ip := Ip); assumption.
      apply r with (Ip := Ip); assumption.

    apply conj; intros W Iv R Ip Ip' Ipext SOt;
      rewrite SOturnst_negSO in *;
      unfold not in *; intros H;
      apply SOt;
      destruct (IHalpha Hocc) as [l r].
      apply r with (Ip := Ip'); assumption.
      apply l with (Ip := Ip'); assumption.

    apply conj; intros W Iv R Ip Ip' Ipext SOt;
    rewrite SOturnst_conjSO in *;
    pose proof (P_occurs_in_alpha_conjSO alpha1 alpha2 P) as H;
    apply contrapos_bool_or in H;
    apply H in Hocc;
    destruct Hocc as [H1 H2]; destruct SOt as [Ha Hb];
    apply conj.
      destruct (IHalpha1 H1) as [l r].
      apply l with (Ip := Ip); assumption.

      destruct (IHalpha2 H2) as [l r].
      apply l with (Ip := Ip); assumption.

      destruct (IHalpha1 H1) as [l r].
      apply r with (Ip := Ip); assumption.

      destruct (IHalpha2 H2) as [l r].
      apply r with (Ip := Ip); assumption.

    apply conj; intros W Iv R Ip Ip' Ipext SOt;
    rewrite SOturnst_disjSO in *;
    pose proof (P_occurs_in_alpha_disjSO alpha1 alpha2 P) as H;
    apply contrapos_bool_or in H;
    apply H in Hocc;
    destruct Hocc as [H1 H2]; destruct SOt as [Ha | Hb].
      left; destruct (IHalpha1 H1) as [l r].
      apply l with (Ip := Ip); assumption.

      right; destruct (IHalpha2 H2) as [l r].
      apply l with (Ip := Ip); assumption.

      left; destruct (IHalpha1 H1) as [l r].
      apply r with (Ip := Ip); assumption.

      right; destruct (IHalpha2 H2) as [l r].
      apply r with (Ip := Ip); assumption.

    apply conj; intros W Iv R Ip Ip' Ipext SOt SOt1;
    rewrite SOturnst_implSO in *;
    pose proof (P_occurs_in_alpha_implSO alpha1 alpha2 P) as H;
    apply contrapos_bool_or in H;
    apply H in Hocc;
    destruct Hocc as [H1 H2]; destruct (IHalpha1 H1) as [l r];
      destruct (IHalpha2 H2) as [l2 r2].
      apply l2 with (Ip := Ip);
      try assumption; apply SOt; apply r with (Ip := Ip'); assumption.

      apply r2 with (Ip := Ip); try assumption.
      apply SOt; apply l with (Ip := Ip'); assumption.

    apply conj; intros W Iv R Ip Ip' Ipext SOt;
    rewrite SOturnst_allSO in *;
    intros pa; specialize (SOt pa);
    pose proof P_occurs_in_alpha_allSO as H;
    specialize (H alpha p P);
    destruct p as [Qm]; destruct P as [Pn];
    apply contrapos_bool_or in H ;
    apply H in Hocc;
    destruct Hocc as [Hbeq Hocc];
    clear H;  
    destruct (IHalpha Hocc) as [l r].
    apply l with (Ip := alt_Ip Ip pa (Pred Qm)).
      unfold Ip_extends.
      apply conj.
        intros w H.
        simpl; simpl in H.
        rewrite beq_nat_comm. rewrite beq_nat_comm in H.
        rewrite Hbeq in *.
        unfold Ip_extends in Ipext.
        apply Ipext; assumption. 

        intros Q; destruct Q as [Rm]; intros Heq.
        simpl.
        case_eq (beq_nat Qm Rm); intros Hbeq2.
          reflexivity.

          unfold Ip_extends in Ipext.
          destruct Ipext as [H1 H2].
          specialize (H2 (Pred Rm)).
          simpl in H2.
          apply H2; assumption.

        assumption.

      apply r with (Ip := alt_Ip Ip pa (Pred Qm)).
        unfold Ip_extends in *.
        apply conj.
          simpl.
          rewrite beq_nat_comm.          
          intros w H.
          rewrite Hbeq in *.
          apply Ipext; assumption.

          intros Q; destruct Q as [Rn].
          intros Heq.
          simpl.
          case (beq_nat Qm Rn).
            reflexivity.

            destruct Ipext as [H1 H2].
            specialize (H2 (Pred Rn)).
            apply H2; assumption.

        assumption.

    apply conj; intros W Iv R Ip Ip' Ipext SOt;
    rewrite SOturnst_exSO in *;
    destruct SOt as [pa SOt]; exists pa;
    pose proof P_occurs_in_alpha_exSO as H;
    specialize (H alpha p P);
    destruct p as [Qm]; destruct P as [Pn];
    apply contrapos_bool_or in H ;
    apply H in Hocc;
    destruct Hocc as [Hbeq Hocc];
    clear H;  
    destruct (IHalpha Hocc) as [l r].
    apply l with (Ip := alt_Ip Ip pa (Pred Qm)).
      unfold Ip_extends.
      apply conj.
        intros w H.
        simpl; simpl in H.
        rewrite beq_nat_comm. rewrite beq_nat_comm in H.
        rewrite Hbeq in *.
        unfold Ip_extends in Ipext.
        apply Ipext; assumption. 

        intros Q; destruct Q as [Rm]; intros Heq.
        simpl.
        case_eq (beq_nat Qm Rm); intros Hbeq2.
          reflexivity.

          unfold Ip_extends in Ipext.
          destruct Ipext as [H1 H2].
          specialize (H2 (Pred Rm)).
          simpl in H2.
          apply H2; assumption.

        assumption.

      apply r with (Ip := alt_Ip Ip pa (Pred Qm)).
        unfold Ip_extends in *.
        apply conj.
          simpl.
          rewrite beq_nat_comm.          
          intros w H.
          rewrite Hbeq in *.
          apply Ipext; assumption.

          intros Q; destruct Q as [Rn].
          intros Heq.
          simpl.
          case (beq_nat Qm Rn).
            reflexivity.

            destruct Ipext as [H1 H2].
            specialize (H2 (Pred Rn)).
            apply H2; assumption.

        assumption.
Qed.



(* -------------------------------------------------------------------- *)

Lemma up_negSO : forall (alpha: SecOrder) (P : predicate),
  alpha_upward_monotone_P alpha P ->
    alpha_downward_monotone_P (negSO alpha) P.
Proof.
  intros alpha P H.
  case_eq (P_occurs_in_alpha (negSO alpha) P); intros Hocc;
    [ | apply up_not_occ_SO; exact Hocc].
  unfold alpha_upward_monotone_P in *.
  intros W Iv Ir Ip Ip' Ipext.
  simpl in *.
  unfold not; intros SOt' H2; apply SOt'.
  apply H with (Ip := Ip'); assumption.
Qed.

Lemma up_conjSO12 : forall (alpha1 alpha2 : SecOrder) (P : predicate),
  alpha_upward_monotone_P alpha1 P ->
    alpha_upward_monotone_P alpha2 P ->
      alpha_upward_monotone_P (conjSO alpha1 alpha2) P.
Proof.
  intros alpha1 alpha2 P H1 H2.
  case_eq (P_occurs_in_alpha (conjSO alpha1 alpha2) P); intros Hocc;
    [ | apply up_not_occ_SO; exact Hocc].
  unfold alpha_upward_monotone_P in *.
  intros W Iv Ir Ip Ip' Ipext SOt.
  simpl in *.
  apply conj; [apply H1 with (Ip := Ip) | apply H2 with (Ip := Ip)];
   try apply SOt; try assumption.
Qed.


Lemma up_disjSO12 : forall (alpha1 alpha2 : SecOrder) (P : predicate),
  alpha_upward_monotone_P alpha1 P ->
    alpha_upward_monotone_P alpha2 P ->
      alpha_upward_monotone_P (disjSO alpha1 alpha2) P.
Proof.
  intros alpha1 alpha2 P H1 H2.
  case_eq (P_occurs_in_alpha (disjSO alpha1 alpha2) P); intros Hocc;
    [ | apply up_not_occ_SO; exact Hocc].
  unfold alpha_upward_monotone_P in *.
  intros W Iv Ir Ip Ip' Ipext SOt.
  simpl in *.
  destruct SOt as [SOt | SOt];
    [left ;apply H1 with (Ip := Ip) |
    right ; apply H2 with (Ip := Ip)]; assumption.
Qed. 


Lemma up_implSO12 : forall (alpha1 alpha2 : SecOrder) (P : predicate),
  alpha_downward_monotone_P alpha1 P ->
    alpha_upward_monotone_P alpha2 P ->
      alpha_upward_monotone_P (implSO alpha1 alpha2) P.
Proof.
  intros alpha1 alpha2 P H1 H2.
  case_eq (P_occurs_in_alpha (implSO alpha1 alpha2) P); intros Hocc;
    [ | apply up_not_occ_SO; exact Hocc].
  unfold alpha_upward_monotone_P in *.
  intros W Iv Ir Ip Ip' Ipext SOt.
  simpl in *; intros H.
  apply H2 with (Ip := Ip); try assumption.
  apply SOt.
  apply H1 with (Ip := Ip'); assumption.
Qed. 

Lemma up_allFO : forall (alpha : SecOrder) (x : FOvariable)
                         (P : predicate),
    ((alpha_upward_monotone_P alpha P) ->
     (alpha_upward_monotone_P (allFO x alpha) P)).
Proof.
  intros alpha x P Hmono.
  unfold alpha_upward_monotone_P in *.
  intros W Iv R Ip Ip' Ipext SOt.
  simpl in *.
  destruct x as [xn]; intros d.
  specialize (SOt d).
  specialize (Hmono W (alt_Iv Iv d (Var xn)) R Ip Ip' Ipext).
  apply Hmono.
  assumption.
Qed.

Lemma up_exFO : forall (alpha : SecOrder) (x : FOvariable)
                         (P : predicate),
    ((alpha_upward_monotone_P alpha P) ->
     (alpha_upward_monotone_P (exFO x alpha) P)).
Proof.
  intros alpha x P Hmono.
  unfold alpha_upward_monotone_P in *.
  intros W Iv R Ip Ip' Ipext SOt.
  simpl in *.
  destruct x as [xn]; destruct SOt as [d SOt].
  exists d.
  specialize (Hmono W (alt_Iv Iv d (Var xn)) R Ip Ip' Ipext).
  apply Hmono.
  assumption.
Qed.

Lemma Ip_ext_alt_Ip : forall (W : Set) (Ip Ip' : predicate -> W -> Prop)
                             (pa : W -> Prop) (P Q : predicate),
  Ip_extends W Ip Ip' P ->
  Ip_extends W (alt_Ip Ip pa Q) (alt_Ip Ip' pa Q) P.
Proof.
  intros W Ip Ip' pa P Q Ipext.
  unfold Ip_extends in *.
  destruct Ipext as [Ipext1 Ipext2].
  destruct P as [Pn]; destruct Q as [Qm].
  apply conj.
    intros w Halt.
    simpl in *.
    case_eq (beq_nat Qm Pn); intros Hbeq; rewrite Hbeq in *.
      assumption.

      apply Ipext1.
      assumption.

    intros R; destruct R as [Rn].
    intros Hneq.
    simpl.
    case_eq (beq_nat Qm Rn); intros Hbeq2.
      reflexivity.

      specialize (Ipext2 (Pred Rn)).
      simpl in *.
      apply Ipext2.
      assumption.
Qed.

Lemma up_allSO : forall (alpha : SecOrder) (P Q: predicate),
    ((alpha_upward_monotone_P alpha P) ->
     (alpha_upward_monotone_P (allSO Q alpha) P)).
Proof.
  intros alpha P Q Hmono.
  unfold alpha_upward_monotone_P in *.
  intros W Iv R Ip Ip' Ipext SOt.
  simpl in *.
  destruct Q as [Qm]; destruct P as [Pn].
  intros pa.
  specialize (SOt pa).
  specialize (Hmono W Iv R (alt_Ip Ip pa (Pred Qm))
        (alt_Ip Ip' pa (Pred Qm))).
  apply Hmono.
  apply Ip_ext_alt_Ip; assumption.

  assumption.
Qed.

Lemma up_exSO : forall (alpha : SecOrder) (P Q: predicate),
    ((alpha_upward_monotone_P alpha P) ->
     (alpha_upward_monotone_P (exSO Q alpha) P)).
Proof.
  intros alpha P Q Hmono.
  unfold alpha_upward_monotone_P in *.
  intros W Iv R Ip Ip' Ipext SOt.
  simpl in *.
  destruct Q as [Qm]; destruct P as [Pn].
  destruct SOt as [pa SOt].
  exists pa.
  specialize (Hmono W Iv R (alt_Ip Ip pa (Pred Qm))
        (alt_Ip Ip' pa (Pred Qm))).
  apply Hmono.
  apply Ip_ext_alt_Ip; assumption.

  assumption.
Qed.

(*
Lemma up_allFOx : forall (alpha : SecOrder) (x : FOvariable)
                         (P : predicate),
  P_is_pos_SO alpha P ->
  (alpha_upward_monotone_P (allFO x alpha) P <->
    alpha_upward_monotone_P alpha P).
Proof.
  intros alpha x P Hpos.
  split; intros H.
    unfold alpha_upward_monotone_P in *.
    intros W Iv R Ip Ip' Ipext SOt.
    specialize (H W Iv R Ip Ip' Ipext).
    simpl in H.
    destruct x as [xn].
    simpl in *.
*)

(* -------------------------------------------------------------------- *)

Lemma down_negSO : forall (alpha: SecOrder) (P : predicate),
  alpha_downward_monotone_P alpha P ->
    alpha_upward_monotone_P (negSO alpha) P.
Proof.
  intros alpha P H.
  case_eq (P_occurs_in_alpha (negSO alpha) P); intros Hocc;
    [ | apply up_not_occ_SO; exact Hocc].
  unfold alpha_upward_monotone_P in *.
  intros W Iv Ir Ip Ip' Ipext.
  simpl in *.
  unfold not; intros SOt' H2; apply SOt'.
  apply H with (Ip := Ip'); assumption.
Qed.

Lemma down_conjSO12 : forall (alpha1 alpha2 : SecOrder) (P : predicate),
  alpha_downward_monotone_P alpha1 P ->
    alpha_downward_monotone_P alpha2 P ->
      alpha_downward_monotone_P (conjSO alpha1 alpha2) P.
Proof.
  intros alpha1 alpha2 P H1 H2.
  case_eq (P_occurs_in_alpha (conjSO alpha1 alpha2) P); intros Hocc;
    [ | apply up_not_occ_SO; exact Hocc].
  unfold alpha_upward_monotone_P in *.
  intros W Iv Ir Ip Ip' Ipext SOt.
  simpl in *.
  apply conj; [apply H1 with (Ip := Ip) | apply H2 with (Ip := Ip)];
   try apply SOt; try assumption.
Qed.


Lemma down_disjSO12 : forall (alpha1 alpha2 : SecOrder) (P : predicate),
  alpha_downward_monotone_P alpha1 P ->
    alpha_downward_monotone_P alpha2 P ->
      alpha_downward_monotone_P (disjSO alpha1 alpha2) P.
Proof.
  intros alpha1 alpha2 P H1 H2.
  case_eq (P_occurs_in_alpha (disjSO alpha1 alpha2) P); intros Hocc;
    [ | apply up_not_occ_SO; exact Hocc].
  unfold alpha_downward_monotone_P in *.
  intros W Iv Ir Ip Ip' Ipext SOt.
  simpl in *.
  destruct SOt as [SOt | SOt];
    [left ;apply H1 with (Ip := Ip) |
    right ; apply H2 with (Ip := Ip)]; try assumption.
Qed. 


Lemma down_implSO12 : forall (alpha1 alpha2 : SecOrder) (P : predicate),
  alpha_upward_monotone_P alpha1 P ->
    alpha_downward_monotone_P alpha2 P ->
      alpha_downward_monotone_P (implSO alpha1 alpha2) P.
Proof.
  intros alpha1 alpha2 P H1 H2.
  case_eq (P_occurs_in_alpha (implSO alpha1 alpha2) P); intros Hocc;
    [ | apply up_not_occ_SO; exact Hocc].
  unfold alpha_upward_monotone_P in *.
  intros W Iv Ir Ip Ip' Ipext SOt.
  simpl in *; intros H.
  apply H2 with (Ip := Ip); try assumption.
  apply SOt.
  apply H1 with (Ip := Ip'); assumption.
Qed.

Lemma down_allFO : forall (alpha : SecOrder) (x : FOvariable)
                         (P : predicate),
    ((alpha_downward_monotone_P alpha P) ->
     (alpha_downward_monotone_P (allFO x alpha) P)).
Proof.
  intros alpha x P Hmono.
  unfold alpha_downward_monotone_P in *.
  intros W Iv R Ip Ip' Ipext SOt.
  simpl in *.
  destruct x as [xn]; intros d.
  specialize (SOt d).
  specialize (Hmono W (alt_Iv Iv d (Var xn)) R Ip Ip' Ipext).
  apply Hmono.
  assumption.
Qed. 

Lemma down_exFO : forall (alpha : SecOrder) (x : FOvariable)
                         (P : predicate),
    ((alpha_downward_monotone_P alpha P) ->
     (alpha_downward_monotone_P (exFO x alpha) P)).
Proof.
  intros alpha x P Hmono.
  unfold alpha_downward_monotone_P in *.
  intros W Iv R Ip Ip' Ipext SOt.
  simpl in *.
  destruct x as [xn]; destruct SOt as [d SOt];
  exists d.
  specialize (Hmono W (alt_Iv Iv d (Var xn)) R Ip Ip' Ipext).
  apply Hmono.
  assumption.
Qed. 


Lemma down_allSO : forall (alpha : SecOrder) (P Q: predicate),
    ((alpha_downward_monotone_P alpha P) ->
     (alpha_downward_monotone_P (allSO Q alpha) P)).
Proof.
  intros alpha P Q Hmono.
  unfold alpha_downward_monotone_P in *.
  intros W Iv R Ip Ip' Ipext SOt.
  simpl in *.
  destruct Q as [Qm]; destruct P as [Pn].
  intros pa.
  specialize (SOt pa).
  specialize (Hmono W Iv R (alt_Ip Ip pa (Pred Qm))
        (alt_Ip  Ip' pa (Pred Qm))).
  apply Hmono.
  apply Ip_ext_alt_Ip; assumption.

  assumption.
Qed.

Lemma down_exSO : forall (alpha : SecOrder) (P Q: predicate),
    ((alpha_downward_monotone_P alpha P) ->
     (alpha_downward_monotone_P (exSO Q alpha) P)).
Proof.
  intros alpha P Q Hmono.
  unfold alpha_downward_monotone_P in *.
  intros W Iv R Ip Ip' Ipext SOt.
  simpl in *.
  destruct Q as [Qm]; destruct P as [Pn].
  destruct SOt as [pa SOt].
  exists pa.
  specialize (Hmono W Iv R (alt_Ip Ip pa (Pred Qm))
        (alt_Ip Ip' pa (Pred Qm))).
  apply Hmono.
  apply Ip_ext_alt_Ip; assumption.

  assumption.
Qed.

(* ------------------------------------------------------------- *)
(* Outdated coment: Can't prove this using induction since the negSO case requires
   the downward_monotone IH. So it is true and is okay to assume,
   but need to prove downward for is_neg at the same time. *)
Lemma monotonicity_SO_predSO : forall (P Q : predicate) (x : FOvariable),
  P_occurs_in_alpha (predSO Q x) P = true ->
  (P_is_pos_SO (predSO Q x) P -> alpha_upward_monotone_P (predSO Q x) P) /\
  (P_is_neg_SO (predSO Q x) P -> alpha_downward_monotone_P (predSO Q x) P).
Proof.
  intros P Q x HPocc.
  apply conj; intros H.
    unfold alpha_upward_monotone_P.
    intros W Iv R Ip Ip' Ipext SOt.
    simpl in *.
    destruct Q as [Qm]; destruct P as [Pn];
    destruct x as [xn].
    unfold Ip_extends in Ipext.
    destruct Ipext as [Ha Hb].
    case_eq (beq_nat Pn Qm); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq) in *.
      apply Ha.
      assumption.

      specialize (Hb (Pred Qm) (beq_nat_false _ _ Hbeq)).
      apply equal_f with (x := (Iv (Var xn))) in Hb.
      rewrite Hb in *.
      assumption.

    unfold alpha_downward_monotone_P.
    intros W Iv R Ip Ip' Ipext SOt.
    simpl in *.
    destruct Q as [Qm]; destruct P as [Pn];
    destruct x as [xn].
    unfold Ip_extends in Ipext.
    destruct Ipext as [Ha Hb].
    case_eq (beq_nat Pn Qm); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq) in *.
      unfold P_is_neg_SO in H.
      simpl in H.
      destruct H as [H _].
      specialize (H HPocc 1).
      simpl in H.
      unfold occ_in_alpha in H.
      simpl in *.
      specialize (H (eq_refl _) (eq_refl _)); discriminate.

      unfold P_occurs_in_alpha in HPocc.
      simpl in *.
      rewrite Hbeq in *.
      discriminate.
Qed.

Lemma monotonicity_SO_relatSO : forall (P: predicate) (x y : FOvariable),
  P_occurs_in_alpha (relatSO x y) P = true ->
  (P_is_pos_SO (relatSO x y) P -> alpha_upward_monotone_P (relatSO x y) P) /\
  (P_is_neg_SO (relatSO x y) P -> alpha_downward_monotone_P (relatSO x y) P).
Proof.
  intros P  x y HPocc.
  unfold P_occurs_in_alpha in HPocc.
  destruct x; destruct y.
  simpl in *.
  discriminate.
Qed.

Lemma monotonicity_SO_eqFO : forall (P: predicate) (x y : FOvariable),
  P_occurs_in_alpha (eqFO x y) P = true ->
  (P_is_pos_SO (eqFO x y) P -> alpha_upward_monotone_P (eqFO x y) P) /\
  (P_is_neg_SO (eqFO x y) P -> alpha_downward_monotone_P (eqFO x y) P).
Proof.
  intros P  x y HPocc.
  unfold P_occurs_in_alpha in HPocc.
  destruct x; destruct y.
  simpl in *.
  discriminate.
Qed.

Lemma monotonicity_SO_allFO : forall (alpha : SecOrder) (P: predicate)
                                     (x : FOvariable),
  (P_occurs_in_alpha alpha P = true ->
          (P_is_pos_SO alpha P -> alpha_upward_monotone_P alpha P) /\
          (P_is_neg_SO alpha P -> alpha_downward_monotone_P alpha P)) ->
  P_occurs_in_alpha (allFO x alpha) P = true ->
    (P_is_pos_SO (allFO x alpha) P -> alpha_upward_monotone_P (allFO x alpha) P) /\
    (P_is_neg_SO (allFO x alpha) P -> alpha_downward_monotone_P (allFO x alpha) P).
Proof.
  intros alpha P x IHalpha HPocc.
  rewrite <- P_occurs_in_alpha_allFO with (x := x) in HPocc.
  specialize (IHalpha HPocc).
  apply conj; intros H.
    rewrite P_is_pos_SO_allFO in H.
    apply up_allFO; apply IHalpha;
      assumption.

    rewrite P_is_neg_SO_allFO in H.
    apply down_allFO; apply IHalpha;
      assumption.
Qed.

Lemma monotonicity_SO_exFO : forall (alpha : SecOrder) (P: predicate)
                                     (x : FOvariable),
  (P_occurs_in_alpha alpha P = true ->
          (P_is_pos_SO alpha P -> alpha_upward_monotone_P alpha P) /\
          (P_is_neg_SO alpha P -> alpha_downward_monotone_P alpha P)) ->
  P_occurs_in_alpha (exFO x alpha) P = true ->
    (P_is_pos_SO (exFO x alpha) P -> alpha_upward_monotone_P (exFO x alpha) P) /\
    (P_is_neg_SO (exFO x alpha) P -> alpha_downward_monotone_P (exFO x alpha) P).
Proof.
  intros alpha P x IHalpha HPocc.
  rewrite <- P_occurs_in_alpha_exFO with (x := x) in HPocc.
  specialize (IHalpha HPocc).
  apply conj; intros H.
    rewrite P_is_pos_SO_exFO in H.
    apply up_exFO; apply IHalpha;
      assumption.

    rewrite P_is_neg_SO_exFO in H.
    apply down_exFO; apply IHalpha;
      assumption.
Qed.


Lemma monotonicity_SO_negSO : forall (alpha : SecOrder) (P: predicate),
    (P_occurs_in_alpha alpha P = true ->
          (P_is_pos_SO alpha P -> alpha_upward_monotone_P alpha P) /\
          (P_is_neg_SO alpha P -> alpha_downward_monotone_P alpha P)) ->
     P_occurs_in_alpha (negSO alpha) P = true ->
    ((P_is_pos_SO (negSO alpha) P -> alpha_upward_monotone_P (negSO alpha) P) /\
     (P_is_neg_SO (negSO alpha) P -> alpha_downward_monotone_P (negSO alpha) P)).
Proof.
  intros alpha P IHalpha Hpocc.
  rewrite <- P_occurs_in_alpha_negSO in Hpocc.
  specialize (IHalpha Hpocc).
  split; intros H.
    apply down_negSO.
    apply IHalpha.
    apply P_pos_negSO.
    assumption.

    apply up_negSO.
    apply IHalpha.
    apply P_neg_negSO.
    assumption.
Qed.

Lemma monotonicity_SO_conjSO : forall (alpha1 alpha2 : SecOrder) (P: predicate),
  (P_occurs_in_alpha alpha1 P = true ->
           (P_is_pos_SO alpha1 P -> alpha_upward_monotone_P alpha1 P) /\
           (P_is_neg_SO alpha1 P -> alpha_downward_monotone_P alpha1 P)) ->
  (P_occurs_in_alpha alpha2 P = true ->
           (P_is_pos_SO alpha2 P -> alpha_upward_monotone_P alpha2 P) /\
           (P_is_neg_SO alpha2 P -> alpha_downward_monotone_P alpha2 P)) ->
  P_occurs_in_alpha (conjSO alpha1 alpha2) P = true ->
  (P_is_pos_SO (conjSO alpha1 alpha2) P ->
   alpha_upward_monotone_P (conjSO alpha1 alpha2) P) /\
  (P_is_neg_SO (conjSO alpha1 alpha2) P ->
   alpha_downward_monotone_P (conjSO alpha1 alpha2) P).
Proof.
  intros alpha1 alpha2 P IHalpha1 IHalpha2 Hpocc.
  case_eq (P_occurs_in_alpha alpha1 P); intros Hpocc1.
      apply conj; intros H.
        apply up_conjSO12.
          apply P_is_pos_SO_conjSO_l in H;
            try apply IHalpha1; try assumption.
    case_eq (P_occurs_in_alpha alpha2 P); intros Hpocc2. 
          apply P_is_pos_SO_conjSO_r in H;
            try apply IHalpha2; try assumption.

      apply up_not_occ_SO in Hpocc2.
      apply Hpocc2.

        apply down_conjSO12.
          apply P_is_neg_SO_conjSO_l in H;
            try apply IHalpha1; try assumption.
    case_eq (P_occurs_in_alpha alpha2 P); intros Hpocc2. 
          apply P_is_neg_SO_conjSO_r in H;
            try apply IHalpha2; try assumption.

      apply up_not_occ_SO in Hpocc2.
      apply Hpocc2.

    case_eq (P_occurs_in_alpha alpha2 P); intros Hpocc2.
      apply conj; intros H.
        apply up_conjSO12.
          apply up_not_occ_SO in Hpocc1.
          apply Hpocc1.

          apply P_is_pos_SO_conjSO_r in H;
          try apply IHalpha2; try assumption.

        apply down_conjSO12.
          apply up_not_occ_SO in Hpocc1.
          apply Hpocc1.

          apply P_is_neg_SO_conjSO_r in H;
          try apply IHalpha2; try assumption.

      apply conj; intros H.
        apply up_conjSO12; apply up_not_occ_SO;
          assumption.

        apply down_conjSO12; apply up_not_occ_SO;
          assumption.
Qed.

Lemma monotonicity_SO_disjSO : forall (alpha1 alpha2 : SecOrder) (P: predicate),
  (P_occurs_in_alpha alpha1 P = true ->
           (P_is_pos_SO alpha1 P -> alpha_upward_monotone_P alpha1 P) /\
           (P_is_neg_SO alpha1 P -> alpha_downward_monotone_P alpha1 P)) ->
  (P_occurs_in_alpha alpha2 P = true ->
           (P_is_pos_SO alpha2 P -> alpha_upward_monotone_P alpha2 P) /\
           (P_is_neg_SO alpha2 P -> alpha_downward_monotone_P alpha2 P)) ->
  P_occurs_in_alpha (disjSO alpha1 alpha2) P = true ->
  (P_is_pos_SO (disjSO alpha1 alpha2) P ->
   alpha_upward_monotone_P (disjSO alpha1 alpha2) P) /\
  (P_is_neg_SO (disjSO alpha1 alpha2) P ->
   alpha_downward_monotone_P (disjSO alpha1 alpha2) P).
Proof.
  intros alpha1 alpha2 P IHalpha1 IHalpha2 Hpocc.
  case_eq (P_occurs_in_alpha alpha1 P); intros Hpocc1.
      apply conj; intros H.
        apply up_disjSO12.
          apply P_is_pos_SO_conjSO_l in H;
            try apply IHalpha1; try assumption.
    case_eq (P_occurs_in_alpha alpha2 P); intros Hpocc2. 
          apply P_is_pos_SO_conjSO_r in H;
            try apply IHalpha2; try assumption.

      apply up_not_occ_SO in Hpocc2.
      apply Hpocc2.

        apply down_disjSO12.
          apply P_is_neg_SO_conjSO_l in H;
            try apply IHalpha1; try assumption.
    case_eq (P_occurs_in_alpha alpha2 P); intros Hpocc2. 
          apply P_is_neg_SO_conjSO_r in H;
            try apply IHalpha2; try assumption.

      apply up_not_occ_SO in Hpocc2.
      apply Hpocc2.

    case_eq (P_occurs_in_alpha alpha2 P); intros Hpocc2.
      apply conj; intros H.
        apply up_disjSO12.
          apply up_not_occ_SO in Hpocc1.
          apply Hpocc1.

          apply P_is_pos_SO_conjSO_r in H;
          try apply IHalpha2; try assumption.

        apply down_disjSO12.
          apply up_not_occ_SO in Hpocc1.
          apply Hpocc1.

          apply P_is_neg_SO_conjSO_r in H;
          try apply IHalpha2; try assumption.

      apply conj; intros H.
        apply up_disjSO12; apply up_not_occ_SO;
          assumption.

        apply down_disjSO12; apply up_not_occ_SO;
          assumption.
Qed.

Lemma monotonicity_SO_implSO : forall (alpha1 alpha2 : SecOrder) (P: predicate),
  (P_occurs_in_alpha alpha1 P = true ->
           (P_is_pos_SO alpha1 P -> alpha_upward_monotone_P alpha1 P) /\
           (P_is_neg_SO alpha1 P -> alpha_downward_monotone_P alpha1 P)) ->
  (P_occurs_in_alpha alpha2 P = true ->
           (P_is_pos_SO alpha2 P -> alpha_upward_monotone_P alpha2 P) /\
           (P_is_neg_SO alpha2 P -> alpha_downward_monotone_P alpha2 P)) ->
  P_occurs_in_alpha (implSO alpha1 alpha2) P = true ->
  (P_is_pos_SO (implSO alpha1 alpha2) P ->
   alpha_upward_monotone_P (implSO alpha1 alpha2) P) /\
  (P_is_neg_SO (implSO alpha1 alpha2) P ->
   alpha_downward_monotone_P (implSO alpha1 alpha2) P).
Proof.
  intros alpha1 alpha2 P IHalpha1 IHalpha2 Hpocc.
  case_eq (P_occurs_in_alpha alpha1 P); intros Hpocc1.
      apply conj; intros H.
        apply up_implSO12.
          apply P_is_pos_SO_implSO_l in H;
            try apply IHalpha1; try assumption.
    case_eq (P_occurs_in_alpha alpha2 P); intros Hpocc2. 
          apply P_is_pos_SO_implSO_r in H;
            try apply IHalpha2; try assumption.

      apply up_not_occ_SO in Hpocc2.
      apply Hpocc2.

        apply down_implSO12.
          apply P_is_neg_SO_implSO_l in H;
            try apply IHalpha1; try assumption.
    case_eq (P_occurs_in_alpha alpha2 P); intros Hpocc2. 
          apply P_is_neg_SO_implSO_r in H;
            try apply IHalpha2; try assumption.

      apply up_not_occ_SO in Hpocc2.
      apply Hpocc2.

    case_eq (P_occurs_in_alpha alpha2 P); intros Hpocc2.
      apply conj; intros H.
        apply up_implSO12.
          apply up_not_occ_SO in Hpocc1.
          apply Hpocc1.

          apply P_is_pos_SO_implSO_r in H;
          try apply IHalpha2; try assumption.

        apply down_implSO12.
          apply up_not_occ_SO in Hpocc1.
          apply Hpocc1.

          apply P_is_neg_SO_implSO_r in H;
          try apply IHalpha2; try assumption.

      apply conj; intros H.
        apply up_implSO12; apply up_not_occ_SO;
          assumption.

        apply down_implSO12; apply up_not_occ_SO;
          assumption.
Qed.

Lemma monotonicity_SO_allSO : forall (alpha : SecOrder) (P Q: predicate),
  (P_occurs_in_alpha alpha P = true ->
          (P_is_pos_SO alpha P -> alpha_upward_monotone_P alpha P) /\
          (P_is_neg_SO alpha P -> alpha_downward_monotone_P alpha P)) ->
  P_occurs_in_alpha (allSO Q alpha) P = true ->
  (P_is_pos_SO (allSO Q alpha) P -> alpha_upward_monotone_P (allSO Q alpha) P) /\
  (P_is_neg_SO (allSO Q alpha) P -> alpha_downward_monotone_P (allSO Q alpha) P).
Proof.
  intros alpha P Q IHalpha Hpocc.
  destruct P as [Pn]; destruct Q as [Qm].
  apply conj; intros H.
    apply up_allSO.
    case_eq (P_occurs_in_alpha alpha (Pred Pn)); intros Hpocc2.
      apply IHalpha; try assumption.
      apply P_is_pos_SO_allSO in H; assumption.

      apply up_not_occ_SO.
      assumption.

    apply down_allSO.
    case_eq (P_occurs_in_alpha alpha (Pred Pn)); intros Hpocc2.
      apply IHalpha; try assumption.
      apply P_is_neg_SO_allSO in H; assumption.

      apply up_not_occ_SO.
      assumption.
Qed.

Lemma monotonicity_SO_exSO : forall (alpha : SecOrder) (P Q: predicate),
  (P_occurs_in_alpha alpha P = true ->
          (P_is_pos_SO alpha P -> alpha_upward_monotone_P alpha P) /\
          (P_is_neg_SO alpha P -> alpha_downward_monotone_P alpha P)) ->
  P_occurs_in_alpha (allSO Q alpha) P = true ->
  (P_is_pos_SO (exSO Q alpha) P -> alpha_upward_monotone_P (exSO Q alpha) P) /\
  (P_is_neg_SO (exSO Q alpha) P -> alpha_downward_monotone_P (exSO Q alpha) P).
Proof.
  intros alpha P Q IHalpha Hpocc.
  destruct P as [Pn]; destruct Q as [Qm].
  apply conj; intros H.
    apply up_exSO.
    case_eq (P_occurs_in_alpha alpha (Pred Pn)); intros Hpocc2.
      apply IHalpha; try assumption.
      apply P_is_pos_SO_exSO in H; assumption.

      apply up_not_occ_SO.
      assumption.

    apply down_exSO.
    case_eq (P_occurs_in_alpha alpha (Pred Pn)); intros Hpocc2.
      apply IHalpha; try assumption.
      apply P_is_neg_SO_exSO in H; assumption.

      apply up_not_occ_SO.
      assumption.
Qed.


Lemma monotonicity_SO : forall (alpha : SecOrder) (P : predicate),
  P_occurs_in_alpha alpha P = true ->
    (P_is_pos_SO alpha P ->
      alpha_upward_monotone_P alpha P) /\
    (P_is_neg_SO alpha P ->
      alpha_downward_monotone_P alpha P).
Proof.
  intros alpha P.
  induction alpha.
    apply monotonicity_SO_predSO.
    apply monotonicity_SO_relatSO.
    apply monotonicity_SO_eqFO.
    apply monotonicity_SO_allFO; assumption. 
    apply monotonicity_SO_exFO; assumption.
    apply monotonicity_SO_negSO; assumption.
    apply monotonicity_SO_conjSO; assumption.
    apply monotonicity_SO_disjSO; assumption.
    apply monotonicity_SO_implSO; assumption.
    apply monotonicity_SO_allSO; assumption.
    apply monotonicity_SO_exSO; assumption.
Qed.





(* ---------------------------------------------------------------------------- *)


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
