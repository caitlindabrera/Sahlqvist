Require Export SecOrder.
Require Export P_occurs_in_alpha.
Require Export ST_setup.
Require Export Correctness_ST.
Require Import Arith.EqNat my_bool.
Require Export List_machinery_impl My_List_Map.
Require Export Unary_Predless nList_egs Rep_Pred_FOv Indicies Identify.
Require Export pos_SO2 neg_SO2 Num_Occ Bool my_bool Is_Pos_Rep_Pred P_occ_rep_pred.
Require Export Uniform_Defns Monotonicity_SO Pre_Sahlqvist_Uniform_Pos P_occ_rep_pred.
Require Export Unary_Predless_l Num_Occ_l2 Occ_In_Alpha My_Prop.
Require Import my_arith__my_leb_nat.
Require Export Sahlqvist_Uniform_Pos.

Fixpoint vsSahlq_ante (phi : Modal) : bool :=
  match phi with
  | atom p => true
  | mconj psi1 psi2 => if (vsSahlq_ante psi1) then (vsSahlq_ante psi2)
                                              else false
  | diam psi => vsSahlq_ante psi
  | _ => false
  end.

Definition vsSahlq (phi : Modal) : Prop :=
  match phi with 
  | mimpl phi1 phi2 => if vsSahlq_ante phi1 then uniform_pos phi2
                                            else False
  | _ => False
  end.

Lemma vsSahlq_ex : forall phi,
  vsSahlq phi ->
  exists phi1 phi2, vsSahlq_ante phi1 = true /\ uniform_pos phi2.
Proof.
  intros phi H.
  destruct phi; simpl in *;
    try contradiction.
    case_eq (vsSahlq_ante phi1); intros Hvs;
      rewrite Hvs in *.
      exists phi1.
      exists phi2.
      apply conj; assumption.

      contradiction.
Qed.

Fixpoint free_FO (alpha : SecOrder) (x : FOvariable)  : bool :=
  match alpha with
    predSO P y => match x,y with 
                     | Var xn, Var yn => beq_nat xn yn
                     end
  | relatSO y1 y2 => match x, y1, y2 with 
                     | Var xn, Var y1n, Var y2n => 
                      if beq_nat xn y1n then true
                          else beq_nat xn y2n
                     end
  | eqFO y1 y2 => match x, y1, y2 with 
                     | Var xn, Var y1n, Var y2n => 
                      if beq_nat xn y1n then true
                          else beq_nat xn y2n
                  end
  | allFO y beta => if match x, y with 
                       | Var xn, Var yn => beq_nat xn yn
                       end 
                       then false
                       else free_FO beta x
  | exFO y beta => if match x, y with 
                       | Var xn, Var yn => beq_nat xn yn
                       end 
                       then false
                       else free_FO beta x
  | negSO beta => free_FO beta x
  | conjSO beta1 beta2 => if free_FO beta1 x then true
                             else free_FO beta2 x
  | disjSO beta1 beta2 => if free_FO beta1 x then true
                             else free_FO beta2 x
  | implSO beta1 beta2 => if free_FO beta1 x then true
                             else free_FO beta2 x
  | allSO P beta => free_FO beta x
  | exSO P beta => free_FO beta x
  end.

Fixpoint no_free_FO_l (alpha : SecOrder) (l : list FOvariable) :=
  match l with
  | nil => true
  | cons x l' => if free_FO alpha x then false else no_free_FO_l alpha l'
  end.

(* ------------------------------------------------------------------- *)

Lemma alt_Iv_eq : forall W Iv d d2 x,
  alt_Iv (@alt_Iv W Iv d x) d2 x =
  alt_Iv Iv d2 x.
Proof.
  intros W Iv d d2 x.
  apply functional_extensionality.
  intros y.
  destruct x as [xn].
  destruct y as [yn].
  simpl.
  case_eq (beq_nat xn yn); intros Hbeq;
    reflexivity.
Qed.

Lemma alt_Iv_switch : forall (W : Set) Iv dx dy x y,
  x <> y ->
  alt_Iv (@alt_Iv W Iv dx x) dy y =
  alt_Iv (alt_Iv Iv dy y) dx x.
Proof.
  intros W Iv dx dt x y H.
  apply functional_extensionality.
  intros z.
  destruct x as [xn]; destruct y as [yn];
  destruct z as [zn].
  simpl.
  case_eq (beq_nat yn zn); intros Hbeq.
    case_eq (beq_nat xn zn); intros Hbeq2.
      rewrite (beq_nat_true _ _ Hbeq) in H.
      rewrite (beq_nat_true _ _ Hbeq2) in H.
      contradiction (H eq_refl).

      reflexivity.

    reflexivity.
Qed.

Lemma alt_Iv_equiv_allFO : forall alpha f x W Iv Ip Ir d,
(forall (x : FOvariable) (W : Set) (Iv : FOvariable -> W)
            (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop) 
            (d : W),
          free_FO alpha x = false ->
          SOturnst W Iv Ip Ir alpha <->
          SOturnst W (alt_Iv Iv d x) Ip Ir alpha) ->
(free_FO (allFO f alpha) x = false) ->
SOturnst W Iv Ip Ir (allFO f alpha) <->
SOturnst W (alt_Iv Iv d x) Ip Ir (allFO f alpha).
Proof.
  intros alpha f x W Iv Ip Ir d IHalpha Hfree.
  destruct f as [yn]; destruct x as [xn].
  do 2 rewrite SOturnst_allFO.
  simpl in Hfree.
  case_eq (beq_nat xn yn); intros Hbeq;
    rewrite Hbeq in *.
    split; intros H.
      intros d2.
      rewrite (beq_nat_true _ _ Hbeq).
      rewrite alt_Iv_eq.
      apply H.

      intros d2.
      specialize (H d2).
      rewrite (beq_nat_true _ _ Hbeq) in H.
      rewrite alt_Iv_eq in H.
      assumption.

    split; intros H.
      intros d2.
      rewrite alt_Iv_switch.
        apply IHalpha; try assumption.
        apply H.

        intros H2; inversion H2 as [H3];
        rewrite H3 in *; rewrite <- beq_nat_refl in Hbeq;
        discriminate.

      intros d2.
      specialize (H d2).
      rewrite alt_Iv_switch in H.
        apply IHalpha in H; try assumption.
          intros H2; inversion H2 as [H3];
          rewrite H3 in *; rewrite <- beq_nat_refl in Hbeq;
          discriminate.
Qed.

Lemma alt_Iv_equiv_negSO : forall alpha x W Iv Ip Ir d,
(forall (x : FOvariable) (W : Set) (Iv : FOvariable -> W)
            (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop) 
            (d : W),
          free_FO alpha x = false ->
          SOturnst W Iv Ip Ir alpha <->
          SOturnst W (alt_Iv Iv d x) Ip Ir alpha) ->
(free_FO (negSO alpha) x = false) ->
SOturnst W Iv Ip Ir (negSO alpha) <->
SOturnst W (alt_Iv Iv d x) Ip Ir (negSO alpha).
Proof.
  intros alpha x W Iv Ip Ir d IHalpha Hfree.
  destruct x as [xn].
  do 2 rewrite SOturnst_negSO.
  simpl in Hfree.
  split; intros H1 H2.
    apply H1.
    apply IHalpha in H2; try assumption.

    apply H1.
    apply IHalpha; assumption.
Qed.

Lemma alt_Iv_equiv_exFO : forall alpha f x W Iv Ip Ir d,
(forall (x : FOvariable) (W : Set) (Iv : FOvariable -> W)
            (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop) 
            (d : W),
          free_FO alpha x = false ->
          SOturnst W Iv Ip Ir alpha <->
          SOturnst W (alt_Iv Iv d x) Ip Ir alpha) ->
(free_FO (exFO f alpha) x = false) ->
SOturnst W Iv Ip Ir (exFO f alpha) <->
SOturnst W (alt_Iv Iv d x) Ip Ir (exFO f alpha).
Proof.
  intros alpha f x W Iv Ip Ir d IHalpha Hfree.
  destruct f as [yn]; destruct x as [xn].
  do 2 rewrite SOturnst_exFO.
  simpl in Hfree.
  case_eq (beq_nat xn yn); intros Hbeq;
    rewrite Hbeq in *.
    split; intros H.
      destruct H as [d2 H].
      exists d2.
      rewrite (beq_nat_true _ _ Hbeq).
      rewrite alt_Iv_eq.
      apply H.

      destruct H as [d2 H].
      exists d2.
      rewrite (beq_nat_true _ _ Hbeq) in H.
      rewrite alt_Iv_eq in H.
      assumption.

    split; intros H.
      destruct H as [d2 H].
      exists d2.
      rewrite alt_Iv_switch.
        apply IHalpha; try assumption.
        intros H2; inversion H2 as [H3];
        rewrite H3 in *; rewrite <- beq_nat_refl in Hbeq;
        discriminate.

        destruct H as [d2 H].
        exists d2.
        rewrite alt_Iv_switch in H;
        try assumption.
          apply IHalpha in H; try assumption.
          intros H2; inversion H2 as [H3];
          rewrite H3 in *; rewrite <- beq_nat_refl in Hbeq;
          discriminate.
Qed.

Lemma alt_Iv_equiv_conjSO : forall alpha1 alpha2 x W Iv Ip Ir d,
 (forall (x : FOvariable) (W : Set) (Iv : FOvariable -> W)
             (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop) 
             (d : W),
           free_FO alpha1 x = false ->
           SOturnst W Iv Ip Ir alpha1 <->
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha1) ->
  (forall (x : FOvariable) (W : Set) (Iv : FOvariable -> W)
             (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop) 
             (d : W),
           free_FO alpha2 x = false ->
           SOturnst W Iv Ip Ir alpha2 <->
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha2) ->
  free_FO (conjSO alpha1 alpha2) x = false ->
SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
SOturnst W (alt_Iv Iv d x) Ip Ir (conjSO alpha1 alpha2).
Proof.
  intros alpha1 alpha2 x Q Iv Ip Ir d IHalpha1 IHalpha2 Hfree.
  simpl in Hfree.
  do 2 rewrite SOturnst_conjSO.
  case_eq (free_FO alpha1 x); intros Hfree1; rewrite Hfree1 in *.
    discriminate.
  case_eq (free_FO alpha2 x); intros Hfree2; rewrite Hfree2 in *.
    discriminate.
  split; intros H;
    destruct H as [H1 H2];
    apply conj.
      apply IHalpha1; assumption.
      apply IHalpha2; assumption.

      apply IHalpha1 in H1; assumption.
      apply IHalpha2 in H2; assumption.
Qed.


Lemma alt_Iv_equiv_disjSO : forall alpha1 alpha2 x W Iv Ip Ir d,
 (forall (x : FOvariable) (W : Set) (Iv : FOvariable -> W)
             (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop) 
             (d : W),
           free_FO alpha1 x = false ->
           SOturnst W Iv Ip Ir alpha1 <->
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha1) ->
  (forall (x : FOvariable) (W : Set) (Iv : FOvariable -> W)
             (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop) 
             (d : W),
           free_FO alpha2 x = false ->
           SOturnst W Iv Ip Ir alpha2 <->
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha2) ->
  free_FO (disjSO alpha1 alpha2) x = false ->
SOturnst W Iv Ip Ir (disjSO alpha1 alpha2) <->
SOturnst W (alt_Iv Iv d x) Ip Ir (disjSO alpha1 alpha2).
Proof.
  intros alpha1 alpha2 x Q Iv Ip Ir d IHalpha1 IHalpha2 Hfree.
  simpl in Hfree.
  do 2 rewrite SOturnst_disjSO.
  case_eq (free_FO alpha1 x); intros Hfree1; rewrite Hfree1 in *.
    discriminate.
  case_eq (free_FO alpha2 x); intros Hfree2; rewrite Hfree2 in *.
    discriminate.
  split; intros H;
    destruct H as [H1 | H2].
      left; apply IHalpha1; assumption.
      right; apply IHalpha2; assumption.

      left; apply IHalpha1 in H1; assumption.
      right; apply IHalpha2 in H2; assumption.
Qed.


Lemma alt_Iv_equiv_implSO : forall alpha1 alpha2 x W Iv Ip Ir d,
 (forall (x : FOvariable) (W : Set) (Iv : FOvariable -> W)
             (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop) 
             (d : W),
           free_FO alpha1 x = false ->
           SOturnst W Iv Ip Ir alpha1 <->
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha1) ->
  (forall (x : FOvariable) (W : Set) (Iv : FOvariable -> W)
             (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop) 
             (d : W),
           free_FO alpha2 x = false ->
           SOturnst W Iv Ip Ir alpha2 <->
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha2) ->
  free_FO (implSO alpha1 alpha2) x = false ->
SOturnst W Iv Ip Ir (implSO alpha1 alpha2) <->
SOturnst W (alt_Iv Iv d x) Ip Ir (implSO alpha1 alpha2).
Proof.
  intros alpha1 alpha2 x Q Iv Ip Ir d IHalpha1 IHalpha2 Hfree.
  simpl in Hfree.
  do 2 rewrite SOturnst_implSO.
  case_eq (free_FO alpha1 x); intros Hfree1; rewrite Hfree1 in *.
    discriminate.
  case_eq (free_FO alpha2 x); intros Hfree2; rewrite Hfree2 in *.
    discriminate.
  split; intros H1 H2.
    apply IHalpha2; try assumption.
    apply H1.
    apply IHalpha1 in H2; try assumption.

    apply IHalpha2 with (d := d) (x := x); try assumption.
    apply H1.
    apply IHalpha1; try assumption.
Qed.

Lemma alt_Iv_equiv_allSO : forall alpha P x W Iv Ip Ir d,
 (forall (x : FOvariable) (W : Set) (Iv : FOvariable -> W)
             (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop) 
             (d : W),
           free_FO alpha x = false ->
           SOturnst W Iv Ip Ir alpha <->
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha) ->
  free_FO (allSO P alpha) x = false ->
  SOturnst W Iv Ip Ir (allSO P alpha) <->
  SOturnst W (alt_Iv Iv d x) Ip Ir (allSO P alpha).
Proof.
  intros alpha P x Q Iv Ip Ir d IHalpha Hfree.
  simpl in Hfree.
  do 2 rewrite SOturnst_allSO.
  split; intros H pa.
    apply IHalpha; try assumption.
    apply H.

    specialize (H pa).
    apply IHalpha in H; assumption.
Qed.


Lemma alt_Iv_equiv_exSO : forall alpha P x W Iv Ip Ir d,
 (forall (x : FOvariable) (W : Set) (Iv : FOvariable -> W)
             (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop) 
             (d : W),
           free_FO alpha x = false ->
           SOturnst W Iv Ip Ir alpha <->
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha) ->
  free_FO (exSO P alpha) x = false ->
  SOturnst W Iv Ip Ir (exSO P alpha) <->
  SOturnst W (alt_Iv Iv d x) Ip Ir (exSO P alpha).
Proof.
  intros alpha P x Q Iv Ip Ir d IHalpha Hfree.
  simpl in Hfree.
  do 2 rewrite SOturnst_exSO.
  split; intros H .
    destruct H as [pa H].
    exists pa.
    apply IHalpha; assumption.

    destruct H as [pa H].
    exists pa.
    apply IHalpha in H; assumption.
Qed.

Lemma alt_Iv_equiv : forall alpha x W Iv Ip Ir d,
  free_FO alpha x = false ->
  SOturnst W Iv Ip Ir alpha <->
  SOturnst W (alt_Iv Iv d x) Ip Ir alpha.
Proof.
  induction alpha; intros x W Iv Ip Ir d Hfree.
    destruct p as [Pn]; destruct x as [xn];
    destruct f as [xm].
    simpl in *.
    case_eq (beq_nat xn xm); intros Hbeq;
      rewrite Hbeq in *.
      discriminate.

      apply iff_refl.

    destruct f as [yn]; destruct f0 as [ym];
    destruct x as [xn].
    simpl in *.
    case_eq (beq_nat xn yn); intros Hbeq1;
      rewrite Hbeq1 in *.
      discriminate.
      rewrite Hfree.
      apply iff_refl.
    destruct f as [yn]; destruct f0 as [ym];
    destruct x as [xn].
    simpl in *.
    case_eq (beq_nat xn yn); intros Hbeq1;
      rewrite Hbeq1 in *.
      discriminate.
      rewrite Hfree.
      apply iff_refl.

    apply alt_Iv_equiv_allFO; assumption.
    apply alt_Iv_equiv_exFO; assumption.
    apply alt_Iv_equiv_negSO; assumption.
    apply alt_Iv_equiv_conjSO; assumption.
    apply alt_Iv_equiv_disjSO; assumption.
    apply alt_Iv_equiv_implSO; assumption.
    apply alt_Iv_equiv_allSO; assumption.
    apply alt_Iv_equiv_exSO; assumption.
Qed.

(* ------------------------------------------------------- *)

Lemma equiv_conj_ex : forall alpha beta x W Iv Ip Ir,
  free_FO beta x = false ->
  SOturnst W Iv Ip Ir (conjSO (exFO x alpha) beta) <->
  SOturnst W Iv Ip Ir (exFO x (conjSO alpha beta)).
Proof.
  intros alpha beta x W Iv Ip Ir Hfree.
  rewrite SOturnst_conjSO.
  do 2 rewrite SOturnst_exFO.
  split; intros H2.
    destruct H2 as [SO1 SO2].
    destruct SO1 as [d SO1].
    exists d.
    simpl.
    apply conj; try assumption.
    apply alt_Iv_equiv; assumption.

    destruct H2 as [d H2].
    simpl in H2.
    destruct H2 as [SO1 SO2].
    apply conj.
      exists d; assumption.

      apply alt_Iv_equiv in SO2; assumption.
Qed.

Lemma equiv_conj_ex2 : forall alpha beta x W Iv Ip Ir,
  free_FO beta x = false ->
  SOturnst W Iv Ip Ir (conjSO beta (exFO x alpha)) <->
  SOturnst W Iv Ip Ir (exFO x (conjSO beta alpha)).
Proof.
  intros alpha beta x W Iv Ip Ir Hfree.
  rewrite SOturnst_conjSO.
  do 2 rewrite SOturnst_exFO.
  split; intros H2.
    destruct H2 as [SO2 SO1].
    destruct SO1 as [d SO1].
    exists d.
    simpl.
    apply conj; try assumption.
    apply alt_Iv_equiv; assumption.

    destruct H2 as [d H2].
    simpl in H2.
    destruct H2 as [SO2 SO1].
    apply conj.
      apply alt_Iv_equiv in SO2; assumption.

      exists d; assumption.
Qed.

Lemma equiv_impl_ex2 : forall alpha beta x W Iv Ip Ir,
  free_FO beta x = false ->
  SOturnst W Iv Ip Ir (implSO (exFO x alpha) beta) <->
  SOturnst W Iv Ip Ir (allFO x (implSO alpha beta)).
Proof.
  intros alpha beta x W Iv Ip Ir Hfree.
  rewrite SOturnst_implSO.
  rewrite SOturnst_exFO.
  rewrite SOturnst_allFO.
  split; intros H2.
    intros d SOt.
    assert (exists d : W, SOturnst W (alt_Iv Iv d x) Ip Ir alpha) as H3.
      exists d; assumption.
    specialize (H2 H3).
    apply alt_Iv_equiv; assumption.

    intros SOt.
    destruct SOt as [d SOt].
    specialize (H2 d).
    rewrite SOturnst_implSO in H2.
    specialize (H2 SOt).
    apply alt_Iv_equiv in H2; assumption.
Qed.


(* ---------------------------------------------------------- *)

Fixpoint rename_FOv_n (alpha : SecOrder) (n1 n2 : nat) : SecOrder :=
  match alpha with  
  | predSO P (Var m) => if beq_nat n1 m then predSO P (Var n2) else alpha
  | relatSO (Var m1) (Var m2) => if beq_nat n1 m1 then
                                    if beq_nat n1 m2 then relatSO (Var n2) (Var n2)
                                       else relatSO (Var n2) (Var m2)
                                    else if beq_nat n1 m2 then relatSO (Var m1) (Var n2)
                                            else alpha
  | eqFO (Var m1) (Var m2) => if beq_nat n1 m1 then
                                    if beq_nat n1 m2 then eqFO (Var n2) (Var n2)
                                       else eqFO (Var n2) (Var m2)
                                    else if beq_nat n1 m2 then eqFO (Var m1) (Var n2)
                                            else alpha
  | negSO beta => negSO (rename_FOv_n beta n1 n2)
  | allFO (Var m) beta => if beq_nat m n1 then allFO (Var n2) (rename_FOv_n beta n1 n2)
                             else allFO (Var m) (rename_FOv_n beta n1 n2)
  | exFO (Var m) beta => if beq_nat m n1 then exFO (Var n2) (rename_FOv_n beta n1 n2)
                             else exFO (Var m) (rename_FOv_n beta n1 n2)
  | conjSO beta1 beta2 => conjSO (rename_FOv_n beta1 n1 n2) (rename_FOv_n beta2 n1 n2)
  | disjSO beta1 beta2 => disjSO (rename_FOv_n beta1 n1 n2) (rename_FOv_n beta2 n1 n2)
  | implSO beta1 beta2 => implSO (rename_FOv_n beta1 n1 n2) (rename_FOv_n beta2 n1 n2)
  | allSO P beta => allSO P (rename_FOv_n beta n1 n2)
  | exSO P beta => exSO P (rename_FOv_n beta n1 n2)
  end.

Definition rename_FOv (alpha : SecOrder) (x y : FOvariable) :=
  match x, y with
  | Var xn, Var yn => rename_FOv_n alpha xn yn
  end.

(* rename_FOv lemmas *)

Lemma rename_FOv_negSO : forall alpha x y,
  rename_FOv (negSO alpha) x y =
  negSO (rename_FOv alpha x y).
Proof.
  intros alpha x y.
  destruct x as [xn]; destruct y as [ym].
  simpl.
  reflexivity.
Qed.

Lemma rename_FOv_conjSO : forall alpha beta x y,
  rename_FOv (conjSO alpha beta) x y =
  conjSO (rename_FOv alpha x y) (rename_FOv beta x y).
Proof.
  intros alpha beta x y.
  destruct x as [xn]; destruct y as [ym].
  simpl.
  reflexivity.
Qed.

Lemma rename_FOv_disjSO : forall alpha beta x y,
  rename_FOv (disjSO alpha beta) x y =
  disjSO (rename_FOv alpha x y) (rename_FOv beta x y).
Proof.
  intros alpha beta x y.
  destruct x as [xn]; destruct y as [ym].
  simpl.
  reflexivity.
Qed.

Lemma rename_FOv_implSO : forall alpha beta x y,
  rename_FOv (implSO alpha beta) x y =
  implSO (rename_FOv alpha x y) (rename_FOv beta x y).
Proof.
  intros alpha beta x y.
  destruct x as [xn]; destruct y as [ym].
  simpl.
  reflexivity.
Qed.

(* ----------------------------------------------------------- *)

Fixpoint max_FOv (alpha : SecOrder) : nat :=
  match alpha with
    predSO P (Var m) => m
  | relatSO (Var m1) (Var m2) => (max m1 m2)
  | eqFO (Var m1) (Var m2) => (max m1 m2)
  | allFO (Var m) beta => max m (max_FOv beta)
  | exFO (Var m) beta => max m (max_FOv beta)
  | negSO beta => max_FOv beta
  | conjSO beta1 beta2 => max (max_FOv beta1) (max_FOv beta2)
  | disjSO beta1 beta2 => max (max_FOv beta1) (max_FOv beta2)
  | implSO beta1 beta2 => max (max_FOv beta1) (max_FOv beta2)
  | allSO P beta => max_FOv beta
  | exSO P beta => max_FOv beta 
  end.

(* Function that quantifies over the predicates in the given list. *)
Fixpoint list_closed_exFO (alpha:SecOrder) (l: list FOvariable) : SecOrder :=
  match l with
    nil => alpha
  | cons x ls => exFO x (list_closed_exFO alpha ls)
  end.

Fixpoint list_closed_allFO (alpha:SecOrder) (l: list FOvariable) : SecOrder :=
  match l with
    nil => alpha
  | cons x ls => allFO x (list_closed_allFO alpha ls)
  end.

Lemma list_closed_exFO_cons : forall alpha l x,
  list_closed_exFO alpha (cons x l) =
  exFO x (list_closed_exFO alpha l).
Proof.
  reflexivity.
Qed.

Lemma list_closed_allFO_cons : forall alpha l x,
  list_closed_allFO alpha (cons x l) =
  allFO x (list_closed_allFO alpha l).
Proof.
  reflexivity.
Qed.

Fixpoint REL (alpha : SecOrder) : bool :=
  match alpha with
  | relatSO _ _ => true
  | conjSO alpha1 alpha2 => if REL alpha1 then REL alpha2 else false
  | _ => false
  end.

Fixpoint AT (alpha : SecOrder) : bool :=
  match alpha with
  | predSO _ _ => true
  | conjSO alpha1 alpha2 => if AT alpha1 then AT alpha2 else false
  | _ => false
  end.

Fixpoint no_exFO (alpha : SecOrder) : bool :=
  match alpha with
  | predSO _ _ => true
  | relatSO _ _ => true
  | eqFO _ _ => true
  | negSO beta => no_exFO beta
  | allFO _ beta => no_exFO beta
  | exFO _ _ => false
  | conjSO beta1 beta2 => if no_exFO beta1 then no_exFO beta2 else false
  | disjSO beta1 beta2 => if no_exFO beta1 then no_exFO beta2 else false
  | implSO beta1 beta2 => if no_exFO beta1 then no_exFO beta2 else false
  | allSO _ beta => no_exFO beta
  | exSO _ beta => no_exFO beta
  end.

Fixpoint exFO_front (alpha : SecOrder) : bool :=
  match alpha with 
  | exFO _ alpha => exFO_front alpha
  | predSO _ _ => true
  | relatSO _ _ => true
  | eqFO _ _ => true
  | _ => no_exFO alpha
  end.

Lemma vsSahlq_ante_mconj : forall phi1 phi2,
  vsSahlq_ante (mconj phi1 phi2) = true ->
  (vsSahlq_ante phi1 = true /\ vsSahlq_ante phi2 = true).
Proof.
  intros phi1 phi2 H.
  simpl in *.
  case_eq (vsSahlq_ante phi1); intros H1;
    rewrite H1 in *.
    apply conj.
      reflexivity.

      assumption.

    discriminate.
Qed.

(* ----------------------------------------------------- *)
(* same_struc *)

Fixpoint same_struc (alpha beta : SecOrder) : bool :=
  match alpha, beta with
  | predSO P _, predSO Q _ => 
    match P, Q with Pred n, Pred m => beq_nat n m end
  | relatSO _ _, relatSO _ _ => true
  | eqFO _ _, eqFO _ _ => true
  | allFO _ alpha', allFO _ beta' => same_struc alpha' beta'
  | exFO _ alpha', exFO _ beta' => same_struc alpha' beta'
  | negSO alpha', negSO beta' => same_struc alpha' beta'
  | conjSO alpha1 alpha2, conjSO beta1 beta2 => 
    if same_struc alpha1 beta1 then same_struc alpha2 beta2 else false
  | disjSO alpha1 alpha2, disjSO beta1 beta2 => 
    if same_struc alpha1 beta1 then same_struc alpha2 beta2 else false
  | implSO alpha1 alpha2, implSO beta1 beta2 => 
    if same_struc alpha1 beta1 then same_struc alpha2 beta2 else false
  | allSO P alpha', allSO Q beta' => 
    match P, Q with Pred n, Pred m =>
    if beq_nat n m then same_struc alpha' beta' else false end
  | exSO P alpha', exSO Q beta' => 
    match P, Q with Pred n, Pred m =>
    if beq_nat n m then same_struc alpha' beta' else false end
  | _ , _=> false
  end.

Lemma same_struc_refl : forall alpha,
  same_struc alpha alpha = true.
Proof.
  induction alpha; 
    try reflexivity;
    try (simpl; assumption);
    try (simpl; rewrite IHalpha1;
    rewrite IHalpha2; reflexivity).

    destruct p.
    simpl. symmetry.
    apply beq_nat_refl.

    simpl. destruct p.
    rewrite <- beq_nat_refl.
    assumption.

    simpl. destruct p.
    rewrite <- beq_nat_refl.
    assumption.
Qed.

Lemma same_struc_trans : forall alpha beta gamma,
  same_struc alpha beta = true ->
  same_struc beta gamma = true ->
  same_struc alpha gamma = true.
Proof.
  intros alpha; induction alpha; intros beta gamma H1 H2;
  destruct beta; destruct gamma; simpl in *; try discriminate;
    try reflexivity;
    try (    apply IHalpha with (beta := beta); assumption).

    destruct p as [n1]; destruct p0 as [n2];
    destruct p1 as [n3].
    rewrite <- (beq_nat_true _ _ H1) in H2.
    assumption.

    case_eq (same_struc alpha1 beta1); intros Hs1;
      rewrite Hs1 in *; try discriminate.
    case_eq (same_struc alpha2 beta2); intros Hs2;
      rewrite Hs2 in *; try discriminate.
    case_eq (same_struc beta1 gamma1); intros Hs3;
      rewrite Hs3 in *; try discriminate.
    case_eq (same_struc beta2 gamma2); intros Hs4;
      rewrite Hs4 in *; try discriminate.
    rewrite IHalpha1 with (beta := beta1); try assumption.
    rewrite IHalpha2 with (beta := beta2); assumption.
  
    case_eq (same_struc alpha1 beta1); intros Hs1;
      rewrite Hs1 in *; try discriminate.
    case_eq (same_struc alpha2 beta2); intros Hs2;
      rewrite Hs2 in *; try discriminate.
    case_eq (same_struc beta1 gamma1); intros Hs3;
      rewrite Hs3 in *; try discriminate.
    case_eq (same_struc beta2 gamma2); intros Hs4;
      rewrite Hs4 in *; try discriminate.
    rewrite IHalpha1 with (beta := beta1); try assumption.
    rewrite IHalpha2 with (beta := beta2); assumption.

    case_eq (same_struc alpha1 beta1); intros Hs1;
      rewrite Hs1 in *; try discriminate.
    case_eq (same_struc alpha2 beta2); intros Hs2;
      rewrite Hs2 in *; try discriminate.
    case_eq (same_struc beta1 gamma1); intros Hs3;
      rewrite Hs3 in *; try discriminate.
    case_eq (same_struc beta2 gamma2); intros Hs4;
      rewrite Hs4 in *; try discriminate.
    rewrite IHalpha1 with (beta := beta1); try assumption.
    rewrite IHalpha2 with (beta := beta2); assumption.

    destruct p as [n1]; destruct p0 as [n2]; destruct p1 as [n3].
    case_eq (beq_nat n1 n2); intros Hbeq; rewrite Hbeq in *;
      try discriminate.
    case_eq (beq_nat n2 n3); intros Hbeq2; rewrite Hbeq2 in *;    
      try discriminate.
    rewrite <- (beq_nat_true _ _ Hbeq) in Hbeq2.
    rewrite Hbeq2.
    apply IHalpha with (beta := beta);
    assumption.

    destruct p as [n1]; destruct p0 as [n2]; destruct p1 as [n3].
    case_eq (beq_nat n1 n2); intros Hbeq; rewrite Hbeq in *;
      try discriminate.
    case_eq (beq_nat n2 n3); intros Hbeq2; rewrite Hbeq2 in *;    
      try discriminate.
    rewrite <- (beq_nat_true _ _ Hbeq) in Hbeq2.
    rewrite Hbeq2.
    apply IHalpha with (beta := beta);
    assumption.
Qed.

(* -------------------------------------------------------- *)
(* max lemmas *)

Lemma leb_max_suc : forall a b,
  Nat.leb (max a (S b)) b = false.
Proof.
  induction a; intros b.
    rewrite PeanoNat.Nat.max_0_l.
    apply leb_suc_f.

    simpl max.
    case_eq b.
      intros Hb.
      reflexivity.

      intros b' Hb.
      simpl.
      apply IHa.
Qed.

Lemma max_eq0_l : forall a b,
  max a b = 0 -> a = 0.
Proof.
  intros a b H.
  case_eq a.
    reflexivity.

    intros a' Ha.
    rewrite Ha in H.
    case_eq b.
      intros Hb; rewrite Hb in H.
      simpl in H.
      discriminate.

      intros b' Hb; rewrite Hb in *.
      simpl in H.
      discriminate.
Qed.

Lemma max_eq0_r : forall a b,
  max a b = 0 -> b = 0.
Proof.
  intros a b H.
  rewrite PeanoNat.Nat.max_comm in H.
  apply max_eq0_l in H.
  assumption.
Qed.

Lemma max_leb_l : forall c a b,
  max a b = c -> Nat.leb a c = true.
Proof.
  induction c; intros a b H.
    apply max_eq0_l in H.
    rewrite H.
    reflexivity.

    case_eq a.
      reflexivity.

      intros a' Ha.
      simpl.
      case_eq b.
        intros Hb. rewrite Hb in H.
        rewrite PeanoNat.Nat.max_0_r in H.
        rewrite H in Ha.
        inversion Ha as [Ha'].
        apply leb_refl.

        intros b' Hb.
        apply IHc with (b := b').
        rewrite Ha in *; rewrite Hb in *.
        simpl in H.
        inversion H. reflexivity.
Qed.

Lemma max_leb_r : forall a b c,
  max a b = c -> Nat.leb b c = true.
Proof.
  intros a b c H.
  rewrite PeanoNat.Nat.max_comm in H.
  apply max_leb_l in H.
  assumption.
Qed.

Lemma leb_max : forall c a b,
  Nat.leb (max a b) c = true ->
  Nat.leb a c = true /\
  Nat.leb b c = true.
Proof.
  induction c; intros a b H.
    rewrite leb_beq_zero in H.
    apply beq_nat_true in H.
    apply conj.
      rewrite (max_eq0_l _ _ H).
      reflexivity.

      rewrite (max_eq0_r _ _ H).
      reflexivity.

    apply leb_suc2 in H.  
    destruct H as [H | H].
      destruct (IHc a b H) as [Hleb1 Hleb2].
      apply conj.
        apply leb_suc_r.
        assumption.

        apply leb_suc_r.
        assumption.

      apply conj.
        apply max_leb_l in H.
        assumption.

        apply max_leb_r in H.
        assumption.
Qed.

Lemma leb_max_suc3 : forall n m n',
  Nat.leb n n' = true ->
  Nat.leb n (max n' m) = true.
Proof.
  induction n; intros m n' Hleb.
    reflexivity.

    case_eq m.
      intros Hm.
      simpl.
      case_eq n'.
        intros Hn'; rewrite Hn' in *.
        simpl in Hleb.
        discriminate.

        intros n'' Hn'.
        simpl.
        rewrite Hn' in Hleb.
        simpl in Hleb.
        assumption.

      intros m' Hm.
        case_eq n'.
          intros Hn'; rewrite Hn' in *.
          simpl in Hleb.
          discriminate.

          intros n'' Hn'.
          simpl.
          apply IHn.
          rewrite Hn' in Hleb.
          assumption.
Qed.

(* ---------------------------------------------------- *)

Lemma same_struc_rename_FOv : forall alpha x y,
  same_struc alpha (rename_FOv alpha x y) = true.
Proof.
  intros alpha x y; destruct x as [xn]; destruct y as [ym].
  induction alpha . 
    destruct p as [Pn]; destruct f as [z1]. simpl.
    case (beq_nat xn z1); simpl; rewrite <- beq_nat_refl;
    reflexivity.

    destruct f as [z1]; destruct f0 as [z2].
    simpl. case (beq_nat xn z1); case (beq_nat xn z2);
    reflexivity.

    destruct f as [z1]; destruct f0 as [z2].
    simpl. case (beq_nat xn z1); case (beq_nat xn z2);
    reflexivity.

    destruct f as [zn]. simpl.
    case (beq_nat zn xn); simpl; assumption.

    destruct f as [zn]. simpl.
    case (beq_nat zn xn); simpl; assumption.

    simpl. assumption.

    simpl. unfold rename_FOv in *.
    rewrite IHalpha1. rewrite IHalpha2.
    reflexivity.

    simpl. unfold rename_FOv in *.
    rewrite IHalpha1. rewrite IHalpha2.
    reflexivity.

    simpl. unfold rename_FOv in *.
    rewrite IHalpha1. rewrite IHalpha2.
    reflexivity.

    simpl. destruct p. rewrite <- beq_nat_refl.
    assumption.

    simpl. destruct p. rewrite <- beq_nat_refl.
    assumption.
Qed.

Lemma exFO_rename_FOv_max_FOv_pre_predSO : forall p f,
forall (x : FOvariable) (m : nat),
Nat.leb (max_FOv (predSO p f)) m = true ->
free_FO (predSO p f) x = false ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop),
SOturnst W Iv Ip Ir (predSO p f) <->
SOturnst W Iv Ip Ir (rename_FOv (predSO p f) x (Var (S m))).
Proof.
  intros p f x m Hleb Hfree W Iv Ip Ir.
  destruct p as [Pn]; destruct f as [ym]; destruct x as [xn].
  simpl in *.
  rewrite Hfree.
  simpl.
  apply iff_refl.
Qed.

Lemma exFO_rename_FOv_max_FOv_pre_relatSO : forall f f0,
forall (x : FOvariable) (m : nat),
Nat.leb (max_FOv (relatSO f f0)) m = true ->
free_FO (relatSO f f0) x = false ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop),
SOturnst W Iv Ip Ir (relatSO f f0) <->
SOturnst W Iv Ip Ir (rename_FOv (relatSO f f0) x (Var (S m))).
Proof.
  intros f0 f x m Hleb Hfree W Iv Ip Ir.
  destruct f0 as [zn]; destruct f as [ym]; destruct x as [xn].
  simpl in *.
  case_eq (beq_nat xn zn); intros Hbeq1; rewrite Hbeq1 in *.
    discriminate.

    rewrite Hfree.
    simpl.
    apply iff_refl.
Qed.

Lemma exFO_rename_FOv_max_FOv_pre_eqFO : forall f f0,
forall (x : FOvariable) (m : nat),
Nat.leb (max_FOv (eqFO f f0)) m = true ->
free_FO (eqFO f f0) x = false ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop),
SOturnst W Iv Ip Ir (eqFO f f0) <->
SOturnst W Iv Ip Ir (rename_FOv (eqFO f f0) x (Var (S m))).
Proof.
  intros f0 f x m Hleb Hfree W Iv Ip Ir.
  destruct f0 as [zn]; destruct f as [ym]; destruct x as [xn].
  simpl in *.
  case_eq (beq_nat xn zn); intros Hbeq1; rewrite Hbeq1 in *.
    discriminate.

    rewrite Hfree.
    simpl.
    apply iff_refl.
Qed.

Lemma exFO_rename_FOv_max_FOv_pre_allFO_1_predSO : forall p f ym,
Nat.leb (S (max_FOv (predSO p f))) ym = true ->
forall (x : FOvariable) (W : Set) (Iv : FOvariable -> W)
  (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop) (d : W),
SOturnst W (alt_Iv Iv d x) Ip Ir (predSO p f) <->
SOturnst W (alt_Iv Iv d (Var ym)) Ip Ir (rename_FOv (predSO p f) x (Var ym)).
Proof.
  intros p f ym Hleb x W  Iv Ip Ir d.
  destruct p; destruct f as [zn]; destruct x as [xn].
  simpl rename_FOv.
  case_eq (beq_nat xn zn); intros Hbeq1.
    simpl.
    rewrite Hbeq1.
    rewrite <- beq_nat_refl.
    apply iff_refl.

    simpl.
    rewrite Hbeq1.
    simpl in Hleb.
    case_eq ym.
      intros Hy.
      rewrite Hy in *.
      discriminate.

      intros yy Hy; rewrite Hy in *.
      case_eq (beq_nat (S yy) zn); intros Hbeq2.
        rewrite <- (beq_nat_true _ _ Hbeq2) in Hleb.
        rewrite leb_suc_f in Hleb.
        discriminate.

        apply iff_refl.
Qed.

Lemma exFO_rename_FOv_max_FOv_pre_allFO_1_relatSO : forall f f0,
forall (x : FOvariable) (ym : nat),
Nat.leb (max_FOv (relatSO f f0)) ym = true ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop) (d : W),
SOturnst W (alt_Iv Iv d x) Ip Ir (relatSO f f0) <->
SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
  (rename_FOv (relatSO f f0) x (Var (S ym))).
Proof.
  intros f f0 x ym Hleb W Iv Ip Ir d.
  destruct x as [xn]; destruct f as [z1]; destruct f0 as [z2].
  simpl in Hleb.
  simpl rename_FOv.
  simpl.
  case_eq (beq_nat xn z1); intros Hbeq1;
    case_eq (beq_nat xn z2); intros Hbeq2.
      simpl. rewrite <- beq_nat_refl.
      apply iff_refl.

      simpl. rewrite <- beq_nat_refl.
      apply iff_refl.

      case_eq z2.
        intros; apply iff_refl.
 
        intros zz2 Hz2.
        case_eq (beq_nat ym zz2); intros Hbeq3.
          rewrite (beq_nat_true _ _ Hbeq3) in Hleb.
          rewrite Hz2 in Hleb.
          rewrite leb_max_suc in Hleb.
          discriminate.

          apply iff_refl.

      simpl.
      case_eq z1.
        intros. rewrite <- beq_nat_refl. apply iff_refl.
 
        intros zz1 Hz1.
        case_eq (beq_nat ym zz1); intros Hbeq3.
          rewrite (beq_nat_true _ _ Hbeq3) in Hleb.
          rewrite Hz1 in Hleb.
          rewrite PeanoNat.Nat.max_comm with (m := z2) in Hleb.
          rewrite leb_max_suc in Hleb.
          discriminate.

          rewrite <- beq_nat_refl.
          apply iff_refl.

      simpl.
      case_eq z2.
        intros. 
        case_eq z1.
          intros. apply iff_refl.
   
          intros zz1 Hz1.
          case_eq (beq_nat ym zz1); intros Hbeq3.
            rewrite (beq_nat_true _ _ Hbeq3) in Hleb.
            rewrite Hz1 in Hleb.
            rewrite PeanoNat.Nat.max_comm with (m := z2) in Hleb.
            rewrite leb_max_suc in Hleb.
            discriminate.

            apply iff_refl.
 
        intros zz2 Hz2.
        case_eq (beq_nat ym zz2); intros Hbeq3.
          rewrite (beq_nat_true _ _ Hbeq3) in Hleb.
          rewrite Hz2 in Hleb.
          rewrite leb_max_suc in Hleb.
          discriminate.

          case_eq z1.
            intros. apply iff_refl.
     
            intros zz1 Hz1.
            case_eq (beq_nat ym zz1); intros Hbeq4.
              rewrite (beq_nat_true _ _ Hbeq4) in Hleb.
              rewrite Hz1 in Hleb.
              rewrite PeanoNat.Nat.max_comm with (m := z2) in Hleb.
              rewrite leb_max_suc in Hleb.
              discriminate.
              apply iff_refl.
Qed.


Lemma exFO_rename_FOv_max_FOv_pre_allFO_1_eqFO : forall f f0,
forall (x : FOvariable) (ym : nat),
Nat.leb (max_FOv (eqFO f f0)) ym = true ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop) (d : W),
SOturnst W (alt_Iv Iv d x) Ip Ir (eqFO f f0) <->
SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
  (rename_FOv (eqFO f f0) x (Var (S ym))).
Proof.
  intros f f0 x ym Hleb W Iv Ip Ir d.
  destruct x as [xn]; destruct f as [z1]; destruct f0 as [z2].
  simpl in Hleb.
  simpl rename_FOv.
  simpl.
  case_eq (beq_nat xn z1); intros Hbeq1;
    case_eq (beq_nat xn z2); intros Hbeq2.
      simpl. rewrite <- beq_nat_refl.
      apply iff_refl.

      simpl. rewrite <- beq_nat_refl.
      apply iff_refl.

      case_eq z2.
        intros; apply iff_refl.
 
        intros zz2 Hz2.
        case_eq (beq_nat ym zz2); intros Hbeq3.
          rewrite (beq_nat_true _ _ Hbeq3) in Hleb.
          rewrite Hz2 in Hleb.
          rewrite leb_max_suc in Hleb.
          discriminate.

          apply iff_refl.

      simpl.
      case_eq z1.
        intros. rewrite <- beq_nat_refl. apply iff_refl.
 
        intros zz1 Hz1.
        case_eq (beq_nat ym zz1); intros Hbeq3.
          rewrite (beq_nat_true _ _ Hbeq3) in Hleb.
          rewrite Hz1 in Hleb.
          rewrite PeanoNat.Nat.max_comm with (m := z2) in Hleb.
          rewrite leb_max_suc in Hleb.
          discriminate.

          rewrite <- beq_nat_refl.
          apply iff_refl.

      simpl.
      case_eq z2.
        intros. 
        case_eq z1.
          intros. apply iff_refl.
   
          intros zz1 Hz1.
          case_eq (beq_nat ym zz1); intros Hbeq3.
            rewrite (beq_nat_true _ _ Hbeq3) in Hleb.
            rewrite Hz1 in Hleb.
            rewrite PeanoNat.Nat.max_comm with (m := z2) in Hleb.
            rewrite leb_max_suc in Hleb.
            discriminate.

            apply iff_refl.
 
        intros zz2 Hz2.
        case_eq (beq_nat ym zz2); intros Hbeq3.
          rewrite (beq_nat_true _ _ Hbeq3) in Hleb.
          rewrite Hz2 in Hleb.
          rewrite leb_max_suc in Hleb.
          discriminate.

          case_eq z1.
            intros. apply iff_refl.
     
            intros zz1 Hz1.
            case_eq (beq_nat ym zz1); intros Hbeq4.
              rewrite (beq_nat_true _ _ Hbeq4) in Hleb.
              rewrite Hz1 in Hleb.
              rewrite PeanoNat.Nat.max_comm with (m := z2) in Hleb.
              rewrite leb_max_suc in Hleb.
              discriminate.
              apply iff_refl.
Qed.

Lemma exFO_rename_FOv_max_FOv_pre_allFO_1_allFO : forall alpha f,
  (forall (x : FOvariable) (ym : nat),
          Nat.leb (max_FOv alpha) ym = true ->
          forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop) (d : W),
          SOturnst W (alt_Iv Iv d x) Ip Ir alpha <->
          SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
            (rename_FOv alpha x (Var (S ym)))) ->
forall (x : FOvariable) (ym : nat),
Nat.leb (max_FOv (allFO f alpha)) ym = true ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop) (d : W),
SOturnst W (alt_Iv Iv d x) Ip Ir (allFO f alpha) <->
SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
  (rename_FOv (allFO f alpha) x (Var (S ym))).
Proof.
  intros alpha f IHalpha x ym Hleb W Iv Ip Ir d.
  destruct f as [zn]; destruct x as [xn].
  simpl rename_FOv.
        simpl in Hleb.
        apply leb_max in Hleb.
  case_eq (beq_nat zn xn); intros Hbeq.
    do 2 rewrite SOturnst_allFO.
    split; intros SOt.
      intros d2.
      rewrite alt_Iv_eq.
      assert ((rename_FOv_n alpha xn (S ym)) = 
              (rename_FOv alpha (Var xn) (Var (S ym)))) as H.
        reflexivity.
      rewrite H.
      apply IHalpha. apply Hleb.
      specialize (SOt d2).
      rewrite (beq_nat_true _ _ Hbeq) in SOt.
      rewrite alt_Iv_eq in SOt.
      apply SOt.

      intros d2.
      specialize (SOt d2).
      rewrite alt_Iv_eq in SOt.
      assert ((rename_FOv_n alpha xn (S ym)) = 
              (rename_FOv alpha (Var xn) (Var (S ym)))) as H.
        reflexivity.
      rewrite H in SOt.
      apply IHalpha in SOt.
        rewrite (beq_nat_true _ _ Hbeq).
        rewrite alt_Iv_eq.
        assumption. apply Hleb.
  
    assert (Var xn <> Var zn) as Hneq.
      intros H. inversion H as [H2].
      rewrite H2 in *.
      rewrite <- beq_nat_refl in *.
      discriminate.
    assert (Var (S ym) <> Var zn) as Hneq2.
      intros H. inversion H as [H2].
      rewrite <- H2 in Hleb.
      rewrite leb_suc_f in Hleb.
      destruct Hleb; discriminate.
    do 2 rewrite SOturnst_allFO.
    split; intros SOt.
      intros d2.
      specialize (SOt d2).
      rewrite alt_Iv_switch in *.
      assert ((rename_FOv_n alpha xn (S ym)) = 
              (rename_FOv alpha (Var xn) (Var (S ym)))) as H.
        reflexivity.
      rewrite H.
      apply IHalpha. apply Hleb.
      assumption. apply Hneq. apply Hneq2. apply Hneq.

      intros d2.
      specialize (SOt d2).
      rewrite alt_Iv_switch in *.
      assert ((rename_FOv_n alpha xn (S ym)) = 
              (rename_FOv alpha (Var xn) (Var (S ym)))) as H.
        reflexivity.
      rewrite H in SOt.
      apply IHalpha in SOt.
      assumption.
        apply Hleb. all : assumption.
Qed.

Lemma exFO_rename_FOv_max_FOv_pre_allFO_1_exFO : forall alpha f,
  (forall (x : FOvariable) (ym : nat),
          Nat.leb (max_FOv alpha) ym = true ->
          forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop) (d : W),
          SOturnst W (alt_Iv Iv d x) Ip Ir alpha <->
          SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
            (rename_FOv alpha x (Var (S ym)))) ->
forall (x : FOvariable) (ym : nat),
Nat.leb (max_FOv (exFO f alpha)) ym = true ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop) (d : W),
SOturnst W (alt_Iv Iv d x) Ip Ir (exFO f alpha) <->
SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
  (rename_FOv (exFO f alpha) x (Var (S ym))).
Proof.
  intros alpha f IHalpha x ym Hleb W Iv Ip Ir d.
  destruct f as [zn]; destruct x as [xn].
  simpl rename_FOv.
        simpl in Hleb.
        apply leb_max in Hleb.
  case_eq (beq_nat zn xn); intros Hbeq.
    do 2 rewrite SOturnst_exFO.
    split; intros SOt;
      destruct SOt as [d2 SOt];
      exists d2.
      rewrite alt_Iv_eq.
      assert ((rename_FOv_n alpha xn (S ym)) = 
              (rename_FOv alpha (Var xn) (Var (S ym)))) as H.
        reflexivity.
      rewrite H.
      apply IHalpha. apply Hleb.
      rewrite (beq_nat_true _ _ Hbeq) in SOt.
      rewrite alt_Iv_eq in SOt.
      apply SOt.

      rewrite alt_Iv_eq in SOt.
      assert ((rename_FOv_n alpha xn (S ym)) = 
              (rename_FOv alpha (Var xn) (Var (S ym)))) as H.
        reflexivity.
      rewrite H in SOt.
      apply IHalpha in SOt.
        rewrite (beq_nat_true _ _ Hbeq).
        rewrite alt_Iv_eq.
        assumption. apply Hleb.
  
    assert (Var xn <> Var zn) as Hneq.
      intros H. inversion H as [H2].
      rewrite H2 in *.
      rewrite <- beq_nat_refl in *.
      discriminate.
    assert (Var (S ym) <> Var zn) as Hneq2.
      intros H. inversion H as [H2].
      rewrite <- H2 in Hleb.
      rewrite leb_suc_f in Hleb.
      destruct Hleb; discriminate.

    do 2 rewrite SOturnst_exFO.
    split; intros SOt;
      destruct SOt as [d2 SOt];
      exists d2.
      rewrite alt_Iv_switch in *.
      assert ((rename_FOv_n alpha xn (S ym)) = 
              (rename_FOv alpha (Var xn) (Var (S ym)))) as H.
        reflexivity.
      rewrite H.
      apply IHalpha. apply Hleb.
      assumption. apply Hneq. apply Hneq2. apply Hneq.

      rewrite alt_Iv_switch in *.
      assert ((rename_FOv_n alpha xn (S ym)) = 
              (rename_FOv alpha (Var xn) (Var (S ym)))) as H.
        reflexivity.
      rewrite H in SOt.
      apply IHalpha in SOt.
      assumption.
        apply Hleb. all : assumption.
Qed.

Lemma exFO_rename_FOv_max_FOv_pre_allFO_1_conjSO : forall alpha1 alpha2,
  (forall (x : FOvariable) (ym : nat),
           Nat.leb (max_FOv alpha1) ym = true ->
           forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
             (Ir : W -> W -> Prop) (d : W),
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha1 <->
           SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
             (rename_FOv alpha1 x (Var (S ym)))) ->
  (forall (x : FOvariable) (ym : nat),
           Nat.leb (max_FOv alpha2) ym = true ->
           forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
             (Ir : W -> W -> Prop) (d : W),
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha2 <->
           SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
             (rename_FOv alpha2 x (Var (S ym)))) ->
forall (x : FOvariable) (ym : nat),
Nat.leb (max_FOv (conjSO alpha1 alpha2)) ym = true ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop) (d : W),
SOturnst W (alt_Iv Iv d x) Ip Ir (conjSO alpha1 alpha2) <->
SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
  (rename_FOv (conjSO alpha1 alpha2) x (Var (S ym))).
Proof.
  intros alpha1 alpha2 IHalpha1 IHalpha2 x ym Hleb W Iv Ip Ir d.
  simpl in Hleb.
  destruct (leb_max _ _ _ Hleb) as [Hleb1 Hleb2].
  rewrite rename_FOv_conjSO.
  do 2 rewrite SOturnst_conjSO.
  split; intros SOt;
    destruct SOt as [SOt1 SOt2];
    apply conj.
      apply IHalpha1; assumption.
      apply IHalpha2; assumption.
      apply IHalpha1 in SOt1; assumption.
      apply IHalpha2 in SOt2; assumption.
Qed.

Lemma exFO_rename_FOv_max_FOv_pre_allFO_1_disjSO : forall alpha1 alpha2,
  (forall (x : FOvariable) (ym : nat),
           Nat.leb (max_FOv alpha1) ym = true ->
           forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
             (Ir : W -> W -> Prop) (d : W),
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha1 <->
           SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
             (rename_FOv alpha1 x (Var (S ym)))) ->
  (forall (x : FOvariable) (ym : nat),
           Nat.leb (max_FOv alpha2) ym = true ->
           forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
             (Ir : W -> W -> Prop) (d : W),
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha2 <->
           SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
             (rename_FOv alpha2 x (Var (S ym)))) ->
forall (x : FOvariable) (ym : nat),
Nat.leb (max_FOv (disjSO alpha1 alpha2)) ym = true ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop) (d : W),
SOturnst W (alt_Iv Iv d x) Ip Ir (disjSO alpha1 alpha2) <->
SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
  (rename_FOv (disjSO alpha1 alpha2) x (Var (S ym))).
Proof.
  intros alpha1 alpha2 IHalpha1 IHalpha2 x ym Hleb W Iv Ip Ir d.
  simpl in Hleb.
  destruct (leb_max _ _ _ Hleb) as [Hleb1 Hleb2].
  rewrite rename_FOv_disjSO.
  do 2 rewrite SOturnst_disjSO.
  split; intros SOt;
    destruct SOt as [SOt1 | SOt2].
      left; apply IHalpha1; assumption.
      right; apply IHalpha2; assumption.

      left; apply IHalpha1 in SOt1; assumption.
      right; apply IHalpha2 in SOt2; assumption.
Qed.

Lemma exFO_rename_FOv_max_FOv_pre_allFO_1_implSO : forall alpha1 alpha2,
  (forall (x : FOvariable) (ym : nat),
           Nat.leb (max_FOv alpha1) ym = true ->
           forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
             (Ir : W -> W -> Prop) (d : W),
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha1 <->
           SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
             (rename_FOv alpha1 x (Var (S ym)))) ->
  (forall (x : FOvariable) (ym : nat),
           Nat.leb (max_FOv alpha2) ym = true ->
           forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
             (Ir : W -> W -> Prop) (d : W),
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha2 <->
           SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
             (rename_FOv alpha2 x (Var (S ym)))) ->
forall (x : FOvariable) (ym : nat),
Nat.leb (max_FOv (implSO alpha1 alpha2)) ym = true ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop) (d : W),
SOturnst W (alt_Iv Iv d x) Ip Ir (implSO alpha1 alpha2) <->
SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
  (rename_FOv (implSO alpha1 alpha2) x (Var (S ym))).
Proof.
  intros alpha1 alpha2 IHalpha1 IHalpha2 x ym Hleb W Iv Ip Ir d.
  simpl in Hleb.
  destruct (leb_max _ _ _ Hleb) as [Hleb1 Hleb2].
  rewrite rename_FOv_implSO.
  do 2 rewrite SOturnst_implSO.
  split; intros SOt H1.
    apply IHalpha2; try assumption.
    apply SOt. apply IHalpha1 in H1; assumption.

    apply IHalpha2 with (ym := ym); try assumption.
    apply SOt. apply IHalpha1; assumption.
Qed.

Lemma exFO_rename_FOv_max_FOv_pre_allFO_1 : forall alpha x ym,
  Nat.leb (max_FOv alpha) ym = true ->
  forall W Iv Ip Ir d,
  SOturnst W (alt_Iv Iv d x) Ip Ir alpha <->
  SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir (rename_FOv alpha x (Var (S ym))).
Proof.
 induction alpha.
  intros.
  apply exFO_rename_FOv_max_FOv_pre_allFO_1_predSO; assumption.
  apply exFO_rename_FOv_max_FOv_pre_allFO_1_relatSO; assumption.
  apply exFO_rename_FOv_max_FOv_pre_allFO_1_eqFO; assumption.
  apply exFO_rename_FOv_max_FOv_pre_allFO_1_allFO; assumption.
  apply exFO_rename_FOv_max_FOv_pre_allFO_1_exFO; assumption.

  intros x ym Hleb W Iv Ip Ir d.
  simpl in Hleb.
  rewrite rename_FOv_negSO.
  do 2 rewrite SOturnst_negSO.
  split; intros H1 H2;
    apply H1.
    apply IHalpha in H2; assumption.

    apply IHalpha; assumption.

  apply exFO_rename_FOv_max_FOv_pre_allFO_1_conjSO; assumption.
  apply exFO_rename_FOv_max_FOv_pre_allFO_1_disjSO; assumption.
  apply exFO_rename_FOv_max_FOv_pre_allFO_1_implSO; assumption.

  intros x ym Hleb W Iv Ip Ir d.
  destruct x; destruct p.
  simpl rename_FOv.
  simpl in Hleb.
  do 2 rewrite SOturnst_allSO.
  specialize (IHalpha (Var n)).
  unfold rename_FOv in IHalpha.
  split; intros H pa.
    apply IHalpha; try assumption.
    apply H.

    specialize (H pa).
    apply IHalpha in H; try assumption.

  intros x ym Hleb W Iv Ip Ir d.
  destruct x; destruct p.
  simpl rename_FOv.
  simpl in Hleb.
  do 2 rewrite SOturnst_exSO.
  specialize (IHalpha (Var n)).
  unfold rename_FOv in IHalpha.
  split; intros H; destruct H as [pa H];
    exists pa.
    apply IHalpha; try assumption.
    apply IHalpha in H; try assumption.
Qed.

Lemma exFO_rename_FOv_max_FOv_pre_allFO : forall alpha f,
  (forall (x : FOvariable) (m : nat),
          Nat.leb (max_FOv alpha) m = true ->
          free_FO alpha x = false ->
          forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir alpha <->
          SOturnst W Iv Ip Ir (rename_FOv alpha x (Var (S m)))) ->
forall (x : FOvariable) (m : nat),
Nat.leb (max_FOv (allFO f alpha)) m = true ->
free_FO (allFO f alpha) x = false ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop),
SOturnst W Iv Ip Ir (allFO f alpha) <->
SOturnst W Iv Ip Ir (rename_FOv (allFO f alpha) x (Var (S m))).
Proof.
  intros alpha f IHalpha x m Hleb Hfree W Iv Ip Ir.
  destruct f as [ym]; destruct x as [xn].
  simpl rename_FOv.
  simpl in Hleb.
  simpl in Hfree.
  rewrite beq_nat_comm.
  case_eq (beq_nat xn ym); intros Hbeq; rewrite Hbeq in *.
    split; intros SOt d.  
      apply leb_max in Hleb.
      destruct Hleb as [Hleb1 Hleb2].
      specialize (IHalpha (Var xn) m Hleb2).
      assert (rename_FOv_n alpha xn (S m) = 
              rename_FOv alpha (Var xn) (Var (S m))) as Heq.
        reflexivity.
      rewrite Heq.
      apply exFO_rename_FOv_max_FOv_pre_allFO_1.
        assumption.
      rewrite (beq_nat_true _ _ Hbeq).
      apply SOt.

      assert (rename_FOv_n alpha xn (S m) = 
              rename_FOv alpha (Var xn) (Var (S m))) as Heq.
        reflexivity.
      rewrite Heq in SOt.
      specialize (SOt d).
      apply exFO_rename_FOv_max_FOv_pre_allFO_1 in SOt.
      rewrite (beq_nat_true _ _ Hbeq) in SOt.
      apply SOt.
        apply leb_max in Hleb. apply Hleb.

    split; intros H.
      intros d.
      assert (rename_FOv_n alpha xn (S m) = 
              rename_FOv alpha (Var xn) (Var (S m))) as Heq.
        reflexivity.
      rewrite Heq.
      apply IHalpha; try assumption.
        apply leb_max in Hleb.
        apply Hleb.

        apply H.

      intros d.
      assert (rename_FOv_n alpha xn (S m) = 
              rename_FOv alpha (Var xn) (Var (S m))) as Heq.
        reflexivity.
      rewrite Heq in H.
      specialize (H d).
      apply IHalpha in H; try assumption.
        apply leb_max in Hleb.
        apply Hleb.
Qed.

Lemma exFO_rename_FOv_max_FOv_pre_exFO_1_predSO : forall p f ym,
Nat.leb (S (max_FOv (predSO p f))) ym = true ->
forall (x : FOvariable) (W : Set) (Iv : FOvariable -> W)
  (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop) (d : W),
SOturnst W (alt_Iv Iv d x) Ip Ir (predSO p f) <->
SOturnst W (alt_Iv Iv d (Var ym)) Ip Ir (rename_FOv (predSO p f) x (Var ym)).
Proof.
  intros p f ym Hleb x W  Iv Ip Ir d.
  destruct p; destruct f as [zn]; destruct x as [xn].
  simpl rename_FOv.
  case_eq (beq_nat xn zn); intros Hbeq1.
    simpl.
    rewrite Hbeq1.
    rewrite <- beq_nat_refl.
    apply iff_refl.

    simpl.
    rewrite Hbeq1.
    simpl in Hleb.
    case_eq ym.
      intros Hy.
      rewrite Hy in *.
      discriminate.

      intros yy Hy; rewrite Hy in *.
      case_eq (beq_nat (S yy) zn); intros Hbeq2.
        rewrite <- (beq_nat_true _ _ Hbeq2) in Hleb.
        rewrite leb_suc_f in Hleb.
        discriminate.

        apply iff_refl.
Qed.

Lemma exFO_rename_FOv_max_FOv_pre_exFO_1_relatSO : forall f f0,
forall (x : FOvariable) (ym : nat),
Nat.leb (max_FOv (relatSO f f0)) ym = true ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop) (d : W),
SOturnst W (alt_Iv Iv d x) Ip Ir (relatSO f f0) <->
SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
  (rename_FOv (relatSO f f0) x (Var (S ym))).
Proof.
  intros f f0 x ym Hleb W Iv Ip Ir d.
  destruct x as [xn]; destruct f as [z1]; destruct f0 as [z2].
  simpl in Hleb.
  simpl rename_FOv.
  simpl.
  case_eq (beq_nat xn z1); intros Hbeq1;
    case_eq (beq_nat xn z2); intros Hbeq2.
      simpl. rewrite <- beq_nat_refl.
      apply iff_refl.

      simpl. rewrite <- beq_nat_refl.
      apply iff_refl.

      case_eq z2.
        intros; apply iff_refl.
 
        intros zz2 Hz2.
        case_eq (beq_nat ym zz2); intros Hbeq3.
          rewrite (beq_nat_true _ _ Hbeq3) in Hleb.
          rewrite Hz2 in Hleb.
          rewrite leb_max_suc in Hleb.
          discriminate.

          apply iff_refl.

      simpl.
      case_eq z1.
        intros. rewrite <- beq_nat_refl. apply iff_refl.
 
        intros zz1 Hz1.
        case_eq (beq_nat ym zz1); intros Hbeq3.
          rewrite (beq_nat_true _ _ Hbeq3) in Hleb.
          rewrite Hz1 in Hleb.
          rewrite PeanoNat.Nat.max_comm with (m := z2) in Hleb.
          rewrite leb_max_suc in Hleb.
          discriminate.

          rewrite <- beq_nat_refl.
          apply iff_refl.

      simpl.
      case_eq z2.
        intros. 
        case_eq z1.
          intros. apply iff_refl.
   
          intros zz1 Hz1.
          case_eq (beq_nat ym zz1); intros Hbeq3.
            rewrite (beq_nat_true _ _ Hbeq3) in Hleb.
            rewrite Hz1 in Hleb.
            rewrite PeanoNat.Nat.max_comm with (m := z2) in Hleb.
            rewrite leb_max_suc in Hleb.
            discriminate.

            apply iff_refl.
 
        intros zz2 Hz2.
        case_eq (beq_nat ym zz2); intros Hbeq3.
          rewrite (beq_nat_true _ _ Hbeq3) in Hleb.
          rewrite Hz2 in Hleb.
          rewrite leb_max_suc in Hleb.
          discriminate.

          case_eq z1.
            intros. apply iff_refl.
     
            intros zz1 Hz1.
            case_eq (beq_nat ym zz1); intros Hbeq4.
              rewrite (beq_nat_true _ _ Hbeq4) in Hleb.
              rewrite Hz1 in Hleb.
              rewrite PeanoNat.Nat.max_comm with (m := z2) in Hleb.
              rewrite leb_max_suc in Hleb.
              discriminate.
              apply iff_refl.
Qed.


Lemma exFO_rename_FOv_max_FOv_pre_exFO_1_eqFO : forall f f0,
forall (x : FOvariable) (ym : nat),
Nat.leb (max_FOv (eqFO f f0)) ym = true ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop) (d : W),
SOturnst W (alt_Iv Iv d x) Ip Ir (eqFO f f0) <->
SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
  (rename_FOv (eqFO f f0) x (Var (S ym))).
Proof.
  intros f f0 x ym Hleb W Iv Ip Ir d.
  destruct x as [xn]; destruct f as [z1]; destruct f0 as [z2].
  simpl in Hleb.
  simpl rename_FOv.
  simpl.
  case_eq (beq_nat xn z1); intros Hbeq1;
    case_eq (beq_nat xn z2); intros Hbeq2.
      simpl. rewrite <- beq_nat_refl.
      apply iff_refl.

      simpl. rewrite <- beq_nat_refl.
      apply iff_refl.

      case_eq z2.
        intros; apply iff_refl.
 
        intros zz2 Hz2.
        case_eq (beq_nat ym zz2); intros Hbeq3.
          rewrite (beq_nat_true _ _ Hbeq3) in Hleb.
          rewrite Hz2 in Hleb.
          rewrite leb_max_suc in Hleb.
          discriminate.

          apply iff_refl.

      simpl.
      case_eq z1.
        intros. rewrite <- beq_nat_refl. apply iff_refl.
 
        intros zz1 Hz1.
        case_eq (beq_nat ym zz1); intros Hbeq3.
          rewrite (beq_nat_true _ _ Hbeq3) in Hleb.
          rewrite Hz1 in Hleb.
          rewrite PeanoNat.Nat.max_comm with (m := z2) in Hleb.
          rewrite leb_max_suc in Hleb.
          discriminate.

          rewrite <- beq_nat_refl.
          apply iff_refl.

      simpl.
      case_eq z2.
        intros. 
        case_eq z1.
          intros. apply iff_refl.
   
          intros zz1 Hz1.
          case_eq (beq_nat ym zz1); intros Hbeq3.
            rewrite (beq_nat_true _ _ Hbeq3) in Hleb.
            rewrite Hz1 in Hleb.
            rewrite PeanoNat.Nat.max_comm with (m := z2) in Hleb.
            rewrite leb_max_suc in Hleb.
            discriminate.

            apply iff_refl.
 
        intros zz2 Hz2.
        case_eq (beq_nat ym zz2); intros Hbeq3.
          rewrite (beq_nat_true _ _ Hbeq3) in Hleb.
          rewrite Hz2 in Hleb.
          rewrite leb_max_suc in Hleb.
          discriminate.

          case_eq z1.
            intros. apply iff_refl.
     
            intros zz1 Hz1.
            case_eq (beq_nat ym zz1); intros Hbeq4.
              rewrite (beq_nat_true _ _ Hbeq4) in Hleb.
              rewrite Hz1 in Hleb.
              rewrite PeanoNat.Nat.max_comm with (m := z2) in Hleb.
              rewrite leb_max_suc in Hleb.
              discriminate.
              apply iff_refl.
Qed.

Lemma exFO_rename_FOv_max_FOv_pre_exFO_1_allFO : forall alpha f,
  (forall (x : FOvariable) (ym : nat),
          Nat.leb (max_FOv alpha) ym = true ->
          forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop) (d : W),
          SOturnst W (alt_Iv Iv d x) Ip Ir alpha <->
          SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
            (rename_FOv alpha x (Var (S ym)))) ->
forall (x : FOvariable) (ym : nat),
Nat.leb (max_FOv (allFO f alpha)) ym = true ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop) (d : W),
SOturnst W (alt_Iv Iv d x) Ip Ir (allFO f alpha) <->
SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
  (rename_FOv (allFO f alpha) x (Var (S ym))).
Proof.
  intros alpha f IHalpha x ym Hleb W Iv Ip Ir d.
  destruct f as [zn]; destruct x as [xn].
  simpl rename_FOv.
        simpl in Hleb.
        apply leb_max in Hleb.
  case_eq (beq_nat zn xn); intros Hbeq.
    do 2 rewrite SOturnst_allFO.
    split; intros SOt.
      intros d2.
      rewrite alt_Iv_eq.
      assert ((rename_FOv_n alpha xn (S ym)) = 
              (rename_FOv alpha (Var xn) (Var (S ym)))) as H.
        reflexivity.
      rewrite H.
      apply IHalpha. apply Hleb.
      specialize (SOt d2).
      rewrite (beq_nat_true _ _ Hbeq) in SOt.
      rewrite alt_Iv_eq in SOt.
      apply SOt.

      intros d2.
      specialize (SOt d2).
      rewrite alt_Iv_eq in SOt.
      assert ((rename_FOv_n alpha xn (S ym)) = 
              (rename_FOv alpha (Var xn) (Var (S ym)))) as H.
        reflexivity.
      rewrite H in SOt.
      apply IHalpha in SOt.
        rewrite (beq_nat_true _ _ Hbeq).
        rewrite alt_Iv_eq.
        assumption. apply Hleb.
  
    assert (Var xn <> Var zn) as Hneq.
      intros H. inversion H as [H2].
      rewrite H2 in *.
      rewrite <- beq_nat_refl in *.
      discriminate.
    assert (Var (S ym) <> Var zn) as Hneq2.
      intros H. inversion H as [H2].
      rewrite <- H2 in Hleb.
      rewrite leb_suc_f in Hleb.
      destruct Hleb; discriminate.
    do 2 rewrite SOturnst_allFO.
    split; intros SOt.
      intros d2.
      specialize (SOt d2).
      rewrite alt_Iv_switch in *.
      assert ((rename_FOv_n alpha xn (S ym)) = 
              (rename_FOv alpha (Var xn) (Var (S ym)))) as H.
        reflexivity.
      rewrite H.
      apply IHalpha. apply Hleb.
      assumption. apply Hneq. apply Hneq2. apply Hneq.

      intros d2.
      specialize (SOt d2).
      rewrite alt_Iv_switch in *.
      assert ((rename_FOv_n alpha xn (S ym)) = 
              (rename_FOv alpha (Var xn) (Var (S ym)))) as H.
        reflexivity.
      rewrite H in SOt.
      apply IHalpha in SOt.
      assumption.
        apply Hleb. all : assumption.
Qed.

Lemma exFO_rename_FOv_max_FOv_pre_exFO_1_exFO : forall alpha f,
  (forall (x : FOvariable) (ym : nat),
          Nat.leb (max_FOv alpha) ym = true ->
          forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop) (d : W),
          SOturnst W (alt_Iv Iv d x) Ip Ir alpha <->
          SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
            (rename_FOv alpha x (Var (S ym)))) ->
forall (x : FOvariable) (ym : nat),
Nat.leb (max_FOv (exFO f alpha)) ym = true ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop) (d : W),
SOturnst W (alt_Iv Iv d x) Ip Ir (exFO f alpha) <->
SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
  (rename_FOv (exFO f alpha) x (Var (S ym))).
Proof.
  intros alpha f IHalpha x ym Hleb W Iv Ip Ir d.
  destruct f as [zn]; destruct x as [xn].
  simpl rename_FOv.
        simpl in Hleb.
        apply leb_max in Hleb.
  case_eq (beq_nat zn xn); intros Hbeq.
    do 2 rewrite SOturnst_exFO.
    split; intros SOt;
      destruct SOt as [d2 SOt];
      exists d2.
      rewrite alt_Iv_eq.
      assert ((rename_FOv_n alpha xn (S ym)) = 
              (rename_FOv alpha (Var xn) (Var (S ym)))) as H.
        reflexivity.
      rewrite H.
      apply IHalpha. apply Hleb.
      rewrite (beq_nat_true _ _ Hbeq) in SOt.
      rewrite alt_Iv_eq in SOt.
      apply SOt.

      rewrite alt_Iv_eq in SOt.
      assert ((rename_FOv_n alpha xn (S ym)) = 
              (rename_FOv alpha (Var xn) (Var (S ym)))) as H.
        reflexivity.
      rewrite H in SOt.
      apply IHalpha in SOt.
        rewrite (beq_nat_true _ _ Hbeq).
        rewrite alt_Iv_eq.
        assumption. apply Hleb.
  
    assert (Var xn <> Var zn) as Hneq.
      intros H. inversion H as [H2].
      rewrite H2 in *.
      rewrite <- beq_nat_refl in *.
      discriminate.
    assert (Var (S ym) <> Var zn) as Hneq2.
      intros H. inversion H as [H2].
      rewrite <- H2 in Hleb.
      rewrite leb_suc_f in Hleb.
      destruct Hleb; discriminate.

    do 2 rewrite SOturnst_exFO.
    split; intros SOt;
      destruct SOt as [d2 SOt];
      exists d2.
      rewrite alt_Iv_switch in *.
      assert ((rename_FOv_n alpha xn (S ym)) = 
              (rename_FOv alpha (Var xn) (Var (S ym)))) as H.
        reflexivity.
      rewrite H.
      apply IHalpha. apply Hleb.
      assumption. apply Hneq. apply Hneq2. apply Hneq.

      rewrite alt_Iv_switch in *.
      assert ((rename_FOv_n alpha xn (S ym)) = 
              (rename_FOv alpha (Var xn) (Var (S ym)))) as H.
        reflexivity.
      rewrite H in SOt.
      apply IHalpha in SOt.
      assumption.
        apply Hleb. all : assumption.
Qed.

Lemma exFO_rename_FOv_max_FOv_pre_exFO_1_conjSO : forall alpha1 alpha2,
  (forall (x : FOvariable) (ym : nat),
           Nat.leb (max_FOv alpha1) ym = true ->
           forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
             (Ir : W -> W -> Prop) (d : W),
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha1 <->
           SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
             (rename_FOv alpha1 x (Var (S ym)))) ->
  (forall (x : FOvariable) (ym : nat),
           Nat.leb (max_FOv alpha2) ym = true ->
           forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
             (Ir : W -> W -> Prop) (d : W),
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha2 <->
           SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
             (rename_FOv alpha2 x (Var (S ym)))) ->
forall (x : FOvariable) (ym : nat),
Nat.leb (max_FOv (conjSO alpha1 alpha2)) ym = true ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop) (d : W),
SOturnst W (alt_Iv Iv d x) Ip Ir (conjSO alpha1 alpha2) <->
SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
  (rename_FOv (conjSO alpha1 alpha2) x (Var (S ym))).
Proof.
  intros alpha1 alpha2 IHalpha1 IHalpha2 x ym Hleb W Iv Ip Ir d.
  simpl in Hleb.
  destruct (leb_max _ _ _ Hleb) as [Hleb1 Hleb2].
  rewrite rename_FOv_conjSO.
  do 2 rewrite SOturnst_conjSO.
  split; intros SOt;
    destruct SOt as [SOt1 SOt2];
    apply conj.
      apply IHalpha1; assumption.
      apply IHalpha2; assumption.
      apply IHalpha1 in SOt1; assumption.
      apply IHalpha2 in SOt2; assumption.
Qed.

Lemma exFO_rename_FOv_max_FOv_pre_exFO_1_disjSO : forall alpha1 alpha2,
  (forall (x : FOvariable) (ym : nat),
           Nat.leb (max_FOv alpha1) ym = true ->
           forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
             (Ir : W -> W -> Prop) (d : W),
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha1 <->
           SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
             (rename_FOv alpha1 x (Var (S ym)))) ->
  (forall (x : FOvariable) (ym : nat),
           Nat.leb (max_FOv alpha2) ym = true ->
           forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
             (Ir : W -> W -> Prop) (d : W),
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha2 <->
           SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
             (rename_FOv alpha2 x (Var (S ym)))) ->
forall (x : FOvariable) (ym : nat),
Nat.leb (max_FOv (disjSO alpha1 alpha2)) ym = true ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop) (d : W),
SOturnst W (alt_Iv Iv d x) Ip Ir (disjSO alpha1 alpha2) <->
SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
  (rename_FOv (disjSO alpha1 alpha2) x (Var (S ym))).
Proof.
  intros alpha1 alpha2 IHalpha1 IHalpha2 x ym Hleb W Iv Ip Ir d.
  simpl in Hleb.
  destruct (leb_max _ _ _ Hleb) as [Hleb1 Hleb2].
  rewrite rename_FOv_disjSO.
  do 2 rewrite SOturnst_disjSO.
  split; intros SOt;
    destruct SOt as [SOt1 | SOt2].
      left; apply IHalpha1; assumption.
      right; apply IHalpha2; assumption.

      left; apply IHalpha1 in SOt1; assumption.
      right; apply IHalpha2 in SOt2; assumption.
Qed.

Lemma exFO_rename_FOv_max_FOv_pre_exFO_1_implSO : forall alpha1 alpha2,
  (forall (x : FOvariable) (ym : nat),
           Nat.leb (max_FOv alpha1) ym = true ->
           forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
             (Ir : W -> W -> Prop) (d : W),
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha1 <->
           SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
             (rename_FOv alpha1 x (Var (S ym)))) ->
  (forall (x : FOvariable) (ym : nat),
           Nat.leb (max_FOv alpha2) ym = true ->
           forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
             (Ir : W -> W -> Prop) (d : W),
           SOturnst W (alt_Iv Iv d x) Ip Ir alpha2 <->
           SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
             (rename_FOv alpha2 x (Var (S ym)))) ->
forall (x : FOvariable) (ym : nat),
Nat.leb (max_FOv (implSO alpha1 alpha2)) ym = true ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop) (d : W),
SOturnst W (alt_Iv Iv d x) Ip Ir (implSO alpha1 alpha2) <->
SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir
  (rename_FOv (implSO alpha1 alpha2) x (Var (S ym))).
Proof.
  intros alpha1 alpha2 IHalpha1 IHalpha2 x ym Hleb W Iv Ip Ir d.
  simpl in Hleb.
  destruct (leb_max _ _ _ Hleb) as [Hleb1 Hleb2].
  rewrite rename_FOv_implSO.
  do 2 rewrite SOturnst_implSO.
  split; intros SOt H1.
    apply IHalpha2; try assumption.
    apply SOt. apply IHalpha1 in H1; assumption.

    apply IHalpha2 with (ym := ym); try assumption.
    apply SOt. apply IHalpha1; assumption.
Qed.

Lemma exFO_rename_FOv_max_FOv_pre_exFO_1 : forall alpha x ym,
  Nat.leb (max_FOv alpha) ym = true ->
  forall W Iv Ip Ir d,
  SOturnst W (alt_Iv Iv d x) Ip Ir alpha <->
  SOturnst W (alt_Iv Iv d (Var (S ym))) Ip Ir (rename_FOv alpha x (Var (S ym))).
Proof.
 induction alpha.
  intros.
  apply exFO_rename_FOv_max_FOv_pre_exFO_1_predSO; assumption.
  apply exFO_rename_FOv_max_FOv_pre_exFO_1_relatSO; assumption.
  apply exFO_rename_FOv_max_FOv_pre_exFO_1_eqFO; assumption.
  apply exFO_rename_FOv_max_FOv_pre_exFO_1_allFO; assumption.
  apply exFO_rename_FOv_max_FOv_pre_exFO_1_exFO; assumption.

  intros x ym Hleb W Iv Ip Ir d.
  simpl in Hleb.
  rewrite rename_FOv_negSO.
  do 2 rewrite SOturnst_negSO.
  split; intros H1 H2;
    apply H1.
    apply IHalpha in H2; assumption.

    apply IHalpha; assumption.

  apply exFO_rename_FOv_max_FOv_pre_exFO_1_conjSO; assumption.
  apply exFO_rename_FOv_max_FOv_pre_exFO_1_disjSO; assumption.
  apply exFO_rename_FOv_max_FOv_pre_exFO_1_implSO; assumption.

  intros x ym Hleb W Iv Ip Ir d.
  destruct x; destruct p.
  simpl rename_FOv.
  simpl in Hleb.
  do 2 rewrite SOturnst_allSO.
  specialize (IHalpha (Var n)).
  unfold rename_FOv in IHalpha.
  split; intros H pa.
    apply IHalpha; try assumption.
    apply H.

    specialize (H pa).
    apply IHalpha in H; try assumption.

  intros x ym Hleb W Iv Ip Ir d.
  destruct x; destruct p.
  simpl rename_FOv.
  simpl in Hleb.
  do 2 rewrite SOturnst_exSO.
  specialize (IHalpha (Var n)).
  unfold rename_FOv in IHalpha.
  split; intros H; destruct H as [pa H];
    exists pa.
    apply IHalpha; try assumption.
    apply IHalpha in H; try assumption.
Qed.

Lemma exFO_rename_FOv_max_FOv_pre_exFO : forall alpha f,
  (forall (x : FOvariable) (m : nat),
          Nat.leb (max_FOv alpha) m = true ->
          free_FO alpha x = false ->
          forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir alpha <->
          SOturnst W Iv Ip Ir (rename_FOv alpha x (Var (S m)))) ->
forall (x : FOvariable) (m : nat),
Nat.leb (max_FOv (exFO f alpha)) m = true ->
free_FO (exFO f alpha) x = false ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop),
SOturnst W Iv Ip Ir (exFO f alpha) <->
SOturnst W Iv Ip Ir (rename_FOv (exFO f alpha) x (Var (S m))).
Proof.
  intros alpha f IHalpha x m Hleb Hfree W Iv Ip Ir.
  destruct f as [ym]; destruct x as [xn].
  simpl rename_FOv.
  simpl in Hleb.
  simpl in Hfree.
  rewrite beq_nat_comm.
  case_eq (beq_nat xn ym); intros Hbeq; rewrite Hbeq in *;
    do 2 rewrite SOturnst_exFO.
    split; intros SOt; destruct SOt as [d SOt];
     exists d.
      apply leb_max in Hleb.
      destruct Hleb as [Hleb1 Hleb2].
      specialize (IHalpha (Var xn) m Hleb2).
      assert (rename_FOv_n alpha xn (S m) = 
              rename_FOv alpha (Var xn) (Var (S m))) as Heq.
        reflexivity.
      rewrite Heq.
      apply exFO_rename_FOv_max_FOv_pre_exFO_1.
        assumption.
      rewrite (beq_nat_true _ _ Hbeq).
      apply SOt.

      assert (rename_FOv_n alpha xn (S m) = 
              rename_FOv alpha (Var xn) (Var (S m))) as Heq.
        reflexivity.
      rewrite Heq in SOt.
      apply exFO_rename_FOv_max_FOv_pre_exFO_1 in SOt.
      rewrite (beq_nat_true _ _ Hbeq) in SOt.
      apply SOt.
        apply leb_max in Hleb. apply Hleb.

    split; intros H; destruct H as [d H]; exists d.
      assert (rename_FOv_n alpha xn (S m) = 
              rename_FOv alpha (Var xn) (Var (S m))) as Heq.
        reflexivity.
      rewrite Heq.
      apply IHalpha; try assumption.
        apply leb_max in Hleb.
        apply Hleb.

      assert (rename_FOv_n alpha xn (S m) = 
              rename_FOv alpha (Var xn) (Var (S m))) as Heq.
        reflexivity.
      rewrite Heq in H.
      apply IHalpha in H; try assumption.
        apply leb_max in Hleb.
        apply Hleb.
Qed.

Lemma exFO_rename_FOv_max_FOv_pre_conjSO : forall alpha1 alpha2,
  (forall (x : FOvariable) (m : nat),
           Nat.leb (max_FOv alpha1) m = true ->
           free_FO alpha1 x = false ->
           forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
             (Ir : W -> W -> Prop),
           SOturnst W Iv Ip Ir alpha1 <->
           SOturnst W Iv Ip Ir (rename_FOv alpha1 x (Var (S m)))) ->
  (forall (x : FOvariable) (m : nat),
           Nat.leb (max_FOv alpha2) m = true ->
           free_FO alpha2 x = false ->
           forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
             (Ir : W -> W -> Prop),
           SOturnst W Iv Ip Ir alpha2 <->
           SOturnst W Iv Ip Ir (rename_FOv alpha2 x (Var (S m)))) ->
forall (x : FOvariable) (m : nat),
Nat.leb (max_FOv (conjSO alpha1 alpha2)) m = true ->
free_FO (conjSO alpha1 alpha2) x = false ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop),
SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
SOturnst W Iv Ip Ir (rename_FOv (conjSO alpha1 alpha2) x (Var (S m))).
Proof.
  intros alpha1 alpha2 IHalpha1 IHalpha2 x m Hleb Hfree W Iv Ip Ir.
  rewrite rename_FOv_conjSO.
  do 2 rewrite SOturnst_conjSO.
  simpl in Hfree.
  case_eq (free_FO alpha1 x); intros Hfree1;
    rewrite Hfree1 in *. discriminate.
  simpl in Hleb.
  apply leb_max in Hleb.
  destruct Hleb as [Hleb1 Hleb2].
  split; intros H; apply conj; destruct H as [H1 H2].
    apply IHalpha1; try assumption.
    apply IHalpha2; try assumption.
    apply IHalpha1 in H1; try assumption.
    apply IHalpha2 in H2; try assumption.
Qed.

Lemma exFO_rename_FOv_max_FOv_pre_disjSO : forall alpha1 alpha2,
  (forall (x : FOvariable) (m : nat),
           Nat.leb (max_FOv alpha1) m = true ->
           free_FO alpha1 x = false ->
           forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
             (Ir : W -> W -> Prop),
           SOturnst W Iv Ip Ir alpha1 <->
           SOturnst W Iv Ip Ir (rename_FOv alpha1 x (Var (S m)))) ->
  (forall (x : FOvariable) (m : nat),
           Nat.leb (max_FOv alpha2) m = true ->
           free_FO alpha2 x = false ->
           forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
             (Ir : W -> W -> Prop),
           SOturnst W Iv Ip Ir alpha2 <->
           SOturnst W Iv Ip Ir (rename_FOv alpha2 x (Var (S m)))) ->
forall (x : FOvariable) (m : nat),
Nat.leb (max_FOv (disjSO alpha1 alpha2)) m = true ->
free_FO (disjSO alpha1 alpha2) x = false ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop),
SOturnst W Iv Ip Ir (disjSO alpha1 alpha2) <->
SOturnst W Iv Ip Ir (rename_FOv (disjSO alpha1 alpha2) x (Var (S m))).
Proof.
  intros alpha1 alpha2 IHalpha1 IHalpha2 x m Hleb Hfree W Iv Ip Ir.
  rewrite rename_FOv_disjSO.
  do 2 rewrite SOturnst_disjSO.
  simpl in Hfree.
  case_eq (free_FO alpha1 x); intros Hfree1;
    rewrite Hfree1 in *. discriminate.
  simpl in Hleb.
  apply leb_max in Hleb.
  destruct Hleb as [Hleb1 Hleb2].
  split; intros H; destruct H as [H1 | H2].
    left; apply IHalpha1; try assumption.
    right; apply IHalpha2; try assumption.
    left; apply IHalpha1 in H1; try assumption.
    right; apply IHalpha2 in H2; try assumption.
Qed.

Lemma exFO_rename_FOv_max_FOv_pre_implSO : forall alpha1 alpha2,
  (forall (x : FOvariable) (m : nat),
           Nat.leb (max_FOv alpha1) m = true ->
           free_FO alpha1 x = false ->
           forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
             (Ir : W -> W -> Prop),
           SOturnst W Iv Ip Ir alpha1 <->
           SOturnst W Iv Ip Ir (rename_FOv alpha1 x (Var (S m)))) ->
  (forall (x : FOvariable) (m : nat),
           Nat.leb (max_FOv alpha2) m = true ->
           free_FO alpha2 x = false ->
           forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
             (Ir : W -> W -> Prop),
           SOturnst W Iv Ip Ir alpha2 <->
           SOturnst W Iv Ip Ir (rename_FOv alpha2 x (Var (S m)))) ->
forall (x : FOvariable) (m : nat),
Nat.leb (max_FOv (implSO alpha1 alpha2)) m = true ->
free_FO (implSO alpha1 alpha2) x = false ->
forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
  (Ir : W -> W -> Prop),
SOturnst W Iv Ip Ir (implSO alpha1 alpha2) <->
SOturnst W Iv Ip Ir (rename_FOv (implSO alpha1 alpha2) x (Var (S m))).
Proof.
  intros alpha1 alpha2 IHalpha1 IHalpha2 x m Hleb Hfree W Iv Ip Ir.
  rewrite rename_FOv_implSO.
  do 2 rewrite SOturnst_implSO.
  simpl in Hfree.
  case_eq (free_FO alpha1 x); intros Hfree1;
    rewrite Hfree1 in *. discriminate.
  simpl in Hleb.
  apply leb_max in Hleb.
  destruct Hleb as [Hleb1 Hleb2].
  split; intros H; intros H2.
    apply IHalpha2; try assumption;
      apply H; apply IHalpha1 in H2; assumption.
    apply IHalpha2 with (m := m) (x := x); try assumption;
      apply H; apply IHalpha1; assumption.
Qed.


Lemma exFO_rename_FOv_max_FOv_pre : forall alpha x m,
  Nat.leb (max_FOv alpha) m = true ->
  free_FO alpha x = false ->
  forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir alpha <->
  SOturnst W Iv Ip Ir (rename_FOv alpha x (Var (S m))).
Proof.
  induction alpha.
    apply exFO_rename_FOv_max_FOv_pre_predSO.
    apply exFO_rename_FOv_max_FOv_pre_relatSO.
    apply exFO_rename_FOv_max_FOv_pre_eqFO.
    apply exFO_rename_FOv_max_FOv_pre_allFO; assumption.
    apply exFO_rename_FOv_max_FOv_pre_exFO; assumption.

    intros x m Hleb Hfree W Iv Ip Ir.
    rewrite rename_FOv_negSO; simpl.
    split; intros H1 H2; apply H1. 
      apply IHalpha in H2; assumption.

      apply IHalpha; assumption.

    apply exFO_rename_FOv_max_FOv_pre_conjSO; assumption.
    apply exFO_rename_FOv_max_FOv_pre_disjSO; assumption.
    apply exFO_rename_FOv_max_FOv_pre_implSO; assumption.

    intros x m Hleb Hfree W Iv Ip Ir.
    destruct x as [n]; destruct p.
    simpl rename_FOv.
    do 2 rewrite SOturnst_allSO.
    simpl in Hfree. simpl in Hleb.
    specialize (IHalpha (Var n)).
    unfold rename_FOv in IHalpha.
    split; intros H pa; specialize (H pa).
      apply IHalpha; assumption.
      apply IHalpha in H; assumption.

      intros x m Hleb Hfree W Iv Ip Ir.
    destruct x as [n]; destruct p.
    simpl rename_FOv.
    do 2 rewrite SOturnst_exSO.
    simpl in Hfree. simpl in Hleb.
    specialize (IHalpha (Var n)).
    unfold rename_FOv in IHalpha.
    split; intros H; destruct H as [pa H]; exists pa.
      apply IHalpha; assumption.
      apply IHalpha in H; assumption.
Qed.

Lemma exFO_rename_FOv_max_FOv : forall alpha n m,
  Nat.leb (max_FOv (exFO (Var n) alpha)) m = true->
  forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (exFO (Var n) alpha) <->
  SOturnst W Iv Ip Ir (exFO (Var (S m)) (rename_FOv alpha (Var n) (Var (S m)))).
Proof.
  intros alpha n m Hleb W Iv Ip Ir.
  assert ((exFO (Var (S m)) (rename_FOv alpha (Var n) (Var (S m)))) =
          rename_FOv (exFO (Var n) alpha) (Var n) (Var (S m))) as H2.
    simpl.
    rewrite <- beq_nat_refl.
    reflexivity.
  rewrite H2.
  apply exFO_rename_FOv_max_FOv_pre.
    assumption.
  simpl.
  rewrite <- beq_nat_refl.
  reflexivity.
Qed.

Lemma equiv_conjSO : forall alpha beta,
  forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir (conjSO alpha beta) <->
    SOturnst W Iv Ip Ir (conjSO beta alpha).
Proof.
  intros alpha beta W Iv Ip Ir.
  do 2 rewrite SOturnst_conjSO.
  split; intros H2;
    (apply conj;
      [apply H2 | apply H2]).
Qed.

Lemma equiv_conjSO2 : forall alpha beta gamma,
  (forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir beta <-> SOturnst W Iv Ip Ir gamma) ->
  forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir (conjSO alpha beta) <->
    SOturnst W Iv Ip Ir (conjSO alpha gamma).
Proof.
  intros alpha beta gamma H W Iv Ip Ir.
  do 2 rewrite SOturnst_conjSO.
  split; intros H2;
    (apply conj;
      [apply H2 | apply H; apply H2]).
Qed.

Lemma free_FO_max_FOv_f_pre2_relatSO : forall f f0 n,
Nat.leb (max_FOv (relatSO f f0)) n = true ->
free_FO (relatSO f f0) (Var (S n)) = false.
Proof.
  intros f f0 n Hleb.
  destruct f as [m1]; destruct f0 as [m2].  
  simpl in *.
  case_eq m1.
    intros Hm1; rewrite Hm1 in *.
    case_eq m2.
      reflexivity.

      intros m2' Hm2.
      case_eq (beq_nat n m2'); intros Hbeq.
        rewrite (beq_nat_true _ _ Hbeq) in Hleb.
        rewrite Hm2 in Hleb.
        rewrite PeanoNat.Nat.max_0_l in Hleb.
        rewrite leb_suc_f in Hleb.
        discriminate.

        reflexivity.

    intros m1' Hm1.
    case_eq (beq_nat n m1'); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq) in Hleb.
      rewrite Hm1 in Hleb.
      rewrite PeanoNat.Nat.max_comm with (m := m2) in Hleb.
      rewrite leb_max_suc in Hleb.
      discriminate.

      case_eq m2.
        reflexivity.

        intros m2' Hm2.
        case_eq (beq_nat n m2'); intros Hbeq2.
          rewrite (beq_nat_true _ _ Hbeq2) in Hleb.
          rewrite Hm2 in Hleb.
          rewrite leb_max_suc in Hleb.
          discriminate.

          reflexivity.
Qed.

Lemma free_FO_max_FOv_f_pre2_allFO : forall gamma f n, 
  (forall n : nat,
          Nat.leb (max_FOv gamma) n = true -> 
          free_FO gamma (Var (S n)) = false) ->
Nat.leb (max_FOv (allFO f gamma)) n = true ->
free_FO (allFO f gamma) (Var (S n)) = false.
Proof.
  intros gamma x n IHalpha Hleb.
  destruct x as [xn].
  simpl in *.
  case_eq xn.
    intros Hxn.
    rewrite Hxn in *.
    simpl in *.
    apply IHalpha; assumption.

    intros xn' Hxn.
    case_eq (beq_nat n xn'); intros Hbeq.
      reflexivity.

      apply IHalpha.
      apply leb_max in Hleb.
      apply Hleb.
Qed.

Lemma free_FO_max_FOv_f_pre2_conjSO : forall gamma1 gamma2 n,
  (forall n : nat,
           Nat.leb (max_FOv gamma1) n = true ->
           free_FO gamma1 (Var (S n)) = false) ->
  (forall n : nat,
           Nat.leb (max_FOv gamma2) n = true ->
           free_FO gamma2 (Var (S n)) = false) ->
Nat.leb (max_FOv (conjSO gamma1 gamma2)) n = true ->
free_FO (conjSO gamma1 gamma2) (Var (S n)) = false.
Proof.
  intros gamma1 gamm2 n IHgamma1 IHgamma2 Hleb.
  simpl.
  simpl in Hleb.
  apply leb_max in Hleb.
  destruct Hleb as [Hleb1 Hleb2].
  case_eq (free_FO gamma1 (Var (S n))); intros Hfree1.
    rewrite (IHgamma1 _ Hleb1) in Hfree1.
    discriminate.

    apply IHgamma2.
    assumption.
Qed.

Lemma free_FO_max_FOv_f_pre2 : forall gamma n,
  Nat.leb (max_FOv gamma) n = true ->
  free_FO gamma (Var (S n)) = false.
Proof.
  induction gamma; intros n Hleb;
    try (    simpl in *; apply IHgamma; assumption).
    destruct f as [m].
    simpl in *.
    case_eq m.
      reflexivity.

      intros m' Hm.
      rewrite Hm in Hleb.
      case_eq (beq_nat n m'); intros Hbeq.
        rewrite (beq_nat_true _ _ Hbeq) in Hleb.
        rewrite leb_suc_f in Hleb.
        discriminate.

        reflexivity.

    apply free_FO_max_FOv_f_pre2_relatSO; assumption.
    apply free_FO_max_FOv_f_pre2_relatSO; assumption.
    apply free_FO_max_FOv_f_pre2_allFO; assumption.
    apply free_FO_max_FOv_f_pre2_allFO; assumption.
    apply free_FO_max_FOv_f_pre2_conjSO; assumption.
    apply free_FO_max_FOv_f_pre2_conjSO; assumption.
    apply free_FO_max_FOv_f_pre2_conjSO; assumption.
Qed.

Lemma free_FO_max_FOv_f : forall alpha gamma x,
free_FO gamma (Var (S (max_FOv (conjSO gamma (exFO x alpha))))) = false.
Proof.
  intros alpha gamma x.
  destruct x as [xn].
  simpl.
  apply free_FO_max_FOv_f_pre2.
  apply leb_max_suc3.
  apply leb_refl.
Qed.

Lemma leb_max_FOv_exFO_conjSO: forall alpha gamma x,
Nat.leb (max_FOv (exFO x alpha))
  (max_FOv (conjSO gamma (exFO x alpha))) = true.
Proof.
  intros alpha gamma x.
  destruct x as [xn].
  simpl.
  rewrite PeanoNat.Nat.max_comm with (n := max_FOv gamma).
  apply leb_max_suc3.
  apply leb_refl.
Qed.

Definition rename_FOv_max_conj alpha gamma x : SecOrder :=
  rename_FOv alpha x (Var (S (max_FOv (conjSO gamma (exFO x alpha))))).

Definition rename_FOv_max_conj_var alpha gamma x : FOvariable :=
  Var (S (max_FOv (conjSO gamma (exFO x alpha)))).

Lemma same_struc_rename_FOv_max_conj : forall alpha gamma x,
  same_struc alpha (rename_FOv_max_conj alpha gamma x) = true.
Proof.
  intros.
  apply same_struc_rename_FOv.
Qed.

Lemma equiv_conjSO_exFO : forall alpha x gamma W Iv Ip Ir,
  SOturnst W Iv Ip Ir (conjSO gamma (exFO x alpha)) <->
  SOturnst W Iv Ip Ir (exFO (rename_FOv_max_conj_var alpha gamma x) (conjSO gamma (rename_FOv_max_conj alpha gamma x))).
Proof.
  intros alpha x gamma W Iv Ip Ir.
  unfold rename_FOv_max_conj_var. unfold rename_FOv_max_conj.
  destruct x as [xn].
  remember (max_FOv (conjSO gamma (exFO (Var xn) alpha))) as mx.
  assert (Nat.leb (max_FOv (exFO (Var xn) alpha)) mx = true) as Hleb.
    rewrite Heqmx.
    apply leb_max_FOv_exFO_conjSO.
  pose proof (exFO_rename_FOv_max_FOv alpha xn mx Hleb) as H.
  pose proof (equiv_conjSO2 gamma _ _ H) as H2.  clear H.
  split; intros SOt.
    apply H2 in SOt.
    apply equiv_conj_ex2.
      rewrite Heqmx. apply free_FO_max_FOv_f.
    assumption.

    apply H2.
    apply equiv_conj_ex2 in SOt.
      assumption.
    rewrite Heqmx. apply free_FO_max_FOv_f.
Qed.

(* ---------------------- *)

Lemma equiv_exFO : forall alpha beta,
  (forall W Iv Ip Ir, 
    SOturnst W Iv Ip Ir alpha <-> SOturnst W Iv Ip Ir beta) ->
  forall W Iv Ip Ir x,
    SOturnst W Iv Ip Ir (exFO x alpha) <->
    SOturnst W Iv Ip Ir (exFO x beta).
Proof.
  intros alpha beta H W Iv Ip Ir x.
  do 2 rewrite SOturnst_exFO.
  split; intros H2;
    destruct H2 as [d H2];
    exists d;
    apply H;
    assumption.
Qed.

Lemma equiv_list_closed_exFO : forall alpha beta lv,
  (forall W Iv Ip Ir, 
    SOturnst W Iv Ip Ir alpha <-> SOturnst W Iv Ip Ir beta) ->
  forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir (list_closed_exFO alpha lv) <->
    SOturnst W Iv Ip Ir (list_closed_exFO beta lv).
Proof.
  intros alpha beta lv. 
  induction lv; intros H W Iv Ip Ir.
    simpl; apply H.

    do 2 rewrite list_closed_exFO_cons.
    apply equiv_exFO. intros. apply IHlv.
    apply H.
Qed.

(* ------------------------- *)

Lemma same_struc_list_closed_exFO_pre : forall n alpha beta l1 l2,
  length l1 = n ->
  length l2 = n ->
  same_struc (list_closed_exFO alpha l1) (list_closed_exFO beta l2) = true ->
  same_struc alpha beta = true.
Proof.
  induction n; intros alpha beta l1 l2 Hl1 Hl2 H.
    apply List.length_zero_iff_nil in Hl1.
    apply List.length_zero_iff_nil in Hl2.
    rewrite Hl1 in *. rewrite Hl2 in *.
    simpl in *.
    assumption.

    case_eq l1.
      intros Hl1'; rewrite Hl1' in Hl1.
      simpl in Hl1.
      discriminate.

      intros x l1' Hl1'.
      rewrite Hl1' in *.
      case_eq l2.
        intros Hl2'; rewrite Hl2' in Hl2.
        simpl in Hl2.
        discriminate.

        intros y l2' Hl2'.
        rewrite Hl2' in *.
        inversion Hl1 as [Hl1''].
        inversion Hl2 as [Hl2''].
        simpl in H.
        apply IHn with (l1 := l1') (l2 := l2');
          try assumption.
Qed.

Lemma same_struc_list_closed_exFO : forall alpha beta l1 l2,
  length l1 = length l2 ->
  same_struc (list_closed_exFO alpha l1) (list_closed_exFO beta l2) = true ->
  same_struc alpha beta = true.
Proof.
  intros alpha beta l1 l2 H1 H2.
  apply (same_struc_list_closed_exFO_pre (length l2) _ _ l1 l2);  
    try assumption. reflexivity.
Qed.



Fixpoint strip_exFO alpha n : SecOrder :=
  match n with
  | 0 => alpha
  | S m => match alpha with
           | exFO x beta => strip_exFO beta m
           | _ => alpha
           end
  end.

Lemma strip_exFO_0 : forall alpha,
  strip_exFO alpha 0 = alpha.
Proof.
  destruct alpha;
  reflexivity.
Qed.

Fixpoint strip_exFO_list alpha n : list FOvariable :=
  match n with
  | 0 => nil
  | S m => match alpha with
           | exFO x beta => cons x (strip_exFO_list beta m)
           | _ => nil
           end
  end.

Lemma strip_exFO_list_0 : forall alpha,
  strip_exFO_list alpha 0 = nil.
Proof.
  destruct alpha;
  reflexivity.
Qed.

Lemma list_closed_exFO_strip_exFO : forall lv alpha beta ,
  same_struc (list_closed_exFO alpha lv) beta = true ->
  (same_struc alpha (strip_exFO beta (length lv)) = true /\
  length lv = length (strip_exFO_list beta (length lv)) /\
  beta = list_closed_exFO (strip_exFO beta (length lv)) (strip_exFO_list beta (length lv))).
Proof.
  induction lv; intros alpha beta Hs.
    simpl in *.
    rewrite strip_exFO_0. rewrite strip_exFO_list_0.
    apply conj. assumption.
    apply conj; reflexivity.

    simpl.
    rewrite list_closed_exFO_cons in Hs.
    destruct beta; simpl in Hs; try discriminate.
    destruct (IHlv alpha beta Hs) as [H1 [H2 H3]].
    apply conj. simpl. assumption.
    apply conj. simpl. rewrite H2. rewrite H2 at 1. reflexivity.
    simpl. rewrite H3 at 1. reflexivity.
Qed.

Lemma same_struc_strip_exFO : forall n alpha beta,
  same_struc alpha beta = true ->
  same_struc (strip_exFO alpha n) (strip_exFO beta n) = true.
Proof.
  induction n; intros alpha beta H.
    do 2 rewrite strip_exFO_0.
    assumption.

    destruct alpha; destruct beta; simpl in *; try discriminate;
      try assumption.
    apply IHn.
    assumption.
Qed.

Lemma same_struc_strip_exFO_list_closed_exFO : forall alpha l,
  same_struc alpha
    (strip_exFO (list_closed_exFO alpha l) (length l)) = true.
Proof.
  intros alpha l.
  induction l.
    simpl.
    rewrite strip_exFO_0.
    apply same_struc_refl.

    simpl in *.
    assumption.
Qed.

Fixpoint rename_FOv_A_pre alpha gamma lv n: SecOrder :=
  match n with
  | 0 => alpha
  | S m =>
  match lv with
  | nil => alpha
  | cons x lv' => rename_FOv_A_pre (strip_exFO (rename_FOv_max_conj (list_closed_exFO alpha 
           lv') gamma x) (length lv'))  gamma 
           (strip_exFO_list (rename_FOv_max_conj (list_closed_exFO alpha lv') gamma x)
           (length lv')) m 
  end
  end.

Definition rename_FOv_A alpha gamma lv : SecOrder :=
  rename_FOv_A_pre alpha gamma lv (length lv).

Fixpoint rename_FOv_A_list_pre alpha gamma lv n: list FOvariable :=
  match n with
  | 0 => nil
  | S m =>
  match lv with
  | nil => nil
  | cons x lv' => cons (rename_FOv_max_conj_var (list_closed_exFO alpha lv') gamma x) 
       (rename_FOv_A_list_pre (strip_exFO (rename_FOv_max_conj (list_closed_exFO alpha lv') gamma x)
       (length lv')) gamma (strip_exFO_list (rename_FOv_max_conj (list_closed_exFO alpha lv')
        gamma x) (length lv')) m)
  end
  end.

Definition rename_FOv_A_list alpha gamma lv :=
  rename_FOv_A_list_pre alpha gamma lv (length lv).

Lemma equiv3_3_struc2_ind_nlist : forall n (lv : nlist n) alpha gamma,
  forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (conjSO gamma (list_closed_exFO alpha (nlist_list _ lv))) <->
  SOturnst W Iv Ip Ir (list_closed_exFO 
        (conjSO gamma (rename_FOv_A alpha gamma (nlist_list _ lv)))
                      (rename_FOv_A_list alpha gamma (nlist_list _ lv))).
Proof.
  induction n; intros lv alpha gamma.
    pose proof (nlist_nil2 lv) as Hnil.   
    rewrite Hnil.
    simpl.
    intros W Iv Ip Ir.
    apply iff_refl.

    destruct (nlist_cons2 _ lv) as [x [lvv Heq1]].
    pose proof (equiv_conjSO_exFO (list_closed_exFO alpha (nlist_list _ lvv)) x gamma) as SOt.
    pose proof (list_closed_exFO_strip_exFO (nlist_list _ lvv) alpha 
      ((rename_FOv_max_conj (list_closed_exFO alpha (nlist_list n lvv)) gamma x))) as [Hs' [Hl' Heq]].
      apply same_struc_rename_FOv_max_conj.
    rewrite Heq in *.
    pose proof Hl' as Hl''.
    rewrite <- Heq in Hl''.
    symmetry in Hl''.
    rewrite length_nlist_list in Hl'' at 2.
    destruct (nlist_list_ex _ (strip_exFO_list (rename_FOv_max_conj (list_closed_exFO alpha (nlist_list n lvv)) gamma x)
            (length (nlist_list n lvv))) Hl'') as [ln' H2].
    intros W Iv Ip Ir.
    rewrite Heq1.
    simpl nlist_list.
    unfold rename_FOv_A in *.
    simpl rename_FOv_A_list_pre.
    unfold rename_FOv_A_list in *.
    simpl rename_FOv_A_pre.
    simpl rename_FOv_A_list_pre.
    do 2 rewrite list_closed_exFO_cons.
    specialize (IHn ln'  (strip_exFO
               (rename_FOv_max_conj (list_closed_exFO alpha (nlist_list n lvv)) gamma x)
               (length (nlist_list n lvv))) gamma).
    rewrite H2 in *.
    rewrite Hl'' in *.
    rewrite length_nlist_list at 3.
    rewrite length_nlist_list at 5.
    split; intros H.
      apply (equiv_exFO _ _ (IHn)).
      apply SOt in H.
      assumption.

      apply (equiv_exFO _ _ (IHn)) in H.
      apply SOt.
      assumption.
Qed.

Lemma equiv3_3_struc2_ind_nlist2 : forall n (lv : nlist n) alpha gamma,
  forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (conjSO (list_closed_exFO alpha (nlist_list _ lv)) gamma) <->
  SOturnst W Iv Ip Ir (list_closed_exFO 
        (conjSO (rename_FOv_A alpha gamma (nlist_list _ lv)) gamma)
                (rename_FOv_A_list alpha gamma (nlist_list _ lv))).
Proof.
  intros n lv alpha gamma W Iv Ip Ir.
  split; intros H.
    apply (equiv_list_closed_exFO _
       (conjSO gamma (rename_FOv_A alpha gamma (nlist_list n lv)))
       (rename_FOv_A_list alpha gamma (nlist_list n lv))).
    apply equiv_conjSO.
    apply equiv3_3_struc2_ind_nlist.
    apply equiv_conjSO in H.
    assumption.

    apply (equiv_list_closed_exFO _
       (conjSO gamma (rename_FOv_A alpha gamma (nlist_list n lv)))
       (rename_FOv_A_list alpha gamma (nlist_list n lv))) in H.
    apply equiv_conjSO.
    apply equiv3_3_struc2_ind_nlist.
    assumption.
    apply equiv_conjSO.
Qed.

Lemma equiv3_3_struc2 : forall lv alpha gamma,
  forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (conjSO gamma (list_closed_exFO alpha lv)) <->
  SOturnst W Iv Ip Ir (list_closed_exFO 
        (conjSO gamma (rename_FOv_A alpha gamma lv))
                      (rename_FOv_A_list alpha gamma lv)).
Proof.
  intros lv.
  destruct (nlist_list_ex (length lv) lv eq_refl).
  rewrite <- H.
  apply equiv3_3_struc2_ind_nlist.
Qed.

Lemma equiv3_3_struc2_2 : forall lv alpha gamma,
  forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (conjSO (list_closed_exFO alpha lv) gamma) <->
  SOturnst W Iv Ip Ir (list_closed_exFO 
        (conjSO (rename_FOv_A alpha gamma lv) gamma)
                (rename_FOv_A_list alpha gamma lv)).
Proof.
  intros lv.
  destruct (nlist_list_ex (length lv) lv eq_refl).
  rewrite <- H.
  apply equiv3_3_struc2_ind_nlist2.
Qed.

Lemma equiv3_3_struc2_both : forall lv1 lv2 alpha beta,
  forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir (conjSO (list_closed_exFO alpha lv1) 
                              (list_closed_exFO beta lv2)) <->
  SOturnst W Iv Ip Ir 
    (list_closed_exFO (list_closed_exFO (conjSO 
      (rename_FOv_A alpha (rename_FOv_A beta (list_closed_exFO alpha lv1) lv2) lv1)
      (rename_FOv_A beta (list_closed_exFO alpha lv1) lv2)) 
          (rename_FOv_A_list alpha (rename_FOv_A beta (list_closed_exFO alpha lv1) lv2) lv1))
          (rename_FOv_A_list beta (list_closed_exFO alpha lv1) lv2)).
Proof.
  intros lv1 lv2 alpha beta W Iv Ip Ir.
  pose proof (equiv3_3_struc2_2 lv1 alpha (rename_FOv_A beta (list_closed_exFO alpha lv1) lv2)) as H.
  split; intros SOt.
    apply equiv3_3_struc2 in SOt.
    apply (equiv_list_closed_exFO _ _ (rename_FOv_A_list beta (list_closed_exFO alpha lv1) lv2) H).
    assumption.

    apply equiv3_3_struc2.
    apply (equiv_list_closed_exFO _ _ (rename_FOv_A_list beta (list_closed_exFO alpha lv1) lv2) H).
    assumption.
Qed.

(* ------------------ *)


Fixpoint conjSO_exFO alpha : bool :=
  match alpha with
    predSO _ _ => true 
  | relatSO _ _ => true
  | eqFO _ _ => true
  | allFO _ _ => false
  | exFO x beta => conjSO_exFO beta
  | negSO _ => false 
  | conjSO beta1 beta2 => 
    if conjSO_exFO beta1 then conjSO_exFO beta2 else false
  | disjSO _ _ => false
  | implSO _ _ => false
  | allSO _ _ => false
  | exSO _ _ => false
  end.

Fixpoint conjSO_exFO_relatSO alpha : bool :=
  match alpha with
    predSO _ _ => true 
  | relatSO _ _ => true
  | eqFO _ _ => false
  | allFO _ _ => false
  | exFO x beta => conjSO_exFO_relatSO beta
  | negSO _ => false 
  | conjSO beta1 beta2 => 
    if conjSO_exFO_relatSO beta1 then conjSO_exFO_relatSO beta2 else false
  | disjSO _ _ => false
  | implSO _ _ => false
  | allSO _ _ => false
  | exSO _ _ => false
  end.


Fixpoint strip_exFO_gen alpha : SecOrder :=
  match alpha with
    predSO _ _ => alpha 
  | relatSO _ _ => alpha
  | eqFO _ _ => alpha
  | allFO _ _ => alpha
  | exFO x beta => (strip_exFO_gen beta)
  | negSO _ => alpha 
  | conjSO _ _ => alpha
  | disjSO _ _ => alpha
  | implSO _ _ => alpha
  | allSO _ _ => alpha
  | exSO _ _ => alpha
  end.

Fixpoint size_SO alpha : nat :=
  match alpha with
    predSO _ _ => 1 
  | relatSO _ _ => 1
  | eqFO _ _ => 1
  | allFO _ _ => 1
  | exFO _ beta => S(size_SO beta)
  | negSO beta => S(size_SO beta) 
  | conjSO beta1 beta2 => (size_SO beta1) + (size_SO beta2)
  | disjSO beta1 beta2 => (size_SO beta1) + (size_SO beta2)
  | implSO beta1 beta2 => (size_SO beta1) + (size_SO beta2)
  | allSO _ beta => S(size_SO beta)
  | exSO _ beta => S(size_SO beta)
  end.
  
Lemma strip_exFO__gen : forall alpha,
  strip_exFO alpha (size_SO alpha) = strip_exFO_gen alpha.
Proof.
  induction alpha; try reflexivity;
    try (simpl; assumption);
    simpl; case (size_SO alpha1 + size_SO alpha2); 
      reflexivity.
Qed.

Fixpoint strip_exFO_list_gen alpha : list FOvariable :=
  match alpha with
    predSO _ _ => nil 
  | relatSO _ _ => nil
  | eqFO _ _ => nil
  | allFO _ _ => nil
  | exFO x beta => cons x (strip_exFO_list_gen beta)
  | negSO _ =>  nil
  | conjSO _ _ => nil
  | disjSO _ _ => nil
  | implSO _ _ => nil
  | allSO _ _ => nil
  | exSO _ _ => nil
  end.

Lemma strip_exFO_list__gen : forall alpha,
  strip_exFO_list alpha (size_SO alpha) = 
  strip_exFO_list_gen alpha.
Proof.
  induction alpha; try reflexivity;
    try (simpl; rewrite IHalpha; reflexivity);
    try (simpl; case ( size_SO alpha1 + size_SO alpha2 );
    reflexivity).
Qed.

Fixpoint funC alpha : SecOrder :=
  match alpha with
    predSO _ _ => alpha 
  | relatSO _ _ => alpha
  | eqFO _ _ => alpha
  | allFO x beta => alpha
  | exFO x beta => exFO x (funC beta)
  | negSO _ => alpha 
  | conjSO beta1 beta2 => 
    (list_closed_exFO (list_closed_exFO (conjSO 
      (rename_FOv_A (strip_exFO_gen beta1) 
        (rename_FOv_A (strip_exFO_gen beta2) 
          (list_closed_exFO (strip_exFO_gen beta1) (strip_exFO_list_gen beta1)) 
        (strip_exFO_list_gen beta2)) (strip_exFO_list_gen beta1))
      (rename_FOv_A (strip_exFO_gen beta2) 
        (list_closed_exFO (strip_exFO_gen beta1) (strip_exFO_list_gen beta1)) 
          (strip_exFO_list_gen beta2))) 
      (rename_FOv_A_list (strip_exFO_gen beta1) 
        (rename_FOv_A (strip_exFO_gen beta2) 
          (list_closed_exFO (strip_exFO_gen beta1) (strip_exFO_list_gen beta1)) 
          (strip_exFO_list_gen beta2)) (strip_exFO_list_gen beta1)))
      (rename_FOv_A_list (strip_exFO_gen beta2) 
          (list_closed_exFO (strip_exFO_gen beta1) (strip_exFO_list_gen beta1))
          (strip_exFO_list_gen beta2)))
  | disjSO _ _ => alpha
  | implSO _ _ => alpha
  | allSO _ _ => alpha
  | exSO _ _ => alpha
  end.

Lemma list_closed_exFO_app : forall alpha l1 l2,
  list_closed_exFO alpha (app l1 l2) =
  list_closed_exFO (list_closed_exFO alpha l2) l1.
Proof.
  intros alpha l1.
  induction l1; intros l2.
    reflexivity.

    simpl in *.
    rewrite IHl1.
    reflexivity.
Qed.

Lemma impl_list_closed_exFO : forall alpha lv W Iv Ip Ir,
  SOturnst W Iv Ip Ir alpha ->
  SOturnst W Iv Ip Ir (list_closed_exFO alpha lv).
Proof.
  intros alpha lv.
  induction lv; intros W Iv Ip Ir H.
    simpl; assumption.

    simpl list_closed_exFO.
    rewrite SOturnst_exFO.
    exists (Iv a).
    rewrite unalt_fun_Iv.
    apply IHlv.
    assumption.
Qed.

Lemma same_struc_conjSO_ex : forall gamma alpha beta,
  same_struc gamma (conjSO alpha beta) = true ->
  existsT2 alpha' beta',
    gamma = conjSO alpha' beta'.
Proof.
  induction gamma; intros alpha beta H;
    try (simpl in *; discriminate).
    exists gamma1. exists gamma2. reflexivity.
Defined.

Definition fun_return_conj_l (alpha : SecOrder) : SecOrder :=
  match alpha with
    predSO _ _ => alpha 
  | relatSO _ _ => alpha
  | eqFO _ _ => alpha
  | allFO x beta => alpha
  | exFO x beta => alpha
  | negSO _ => alpha 
  | conjSO beta1 beta2 => beta1
  | disjSO _ _ => alpha
  | implSO _ _ => alpha
  | allSO _ _ => alpha
  | exSO _ _ => alpha
  end.

Definition fun_return_conj_r (alpha : SecOrder) : SecOrder :=
  match alpha with
    predSO _ _ => alpha 
  | relatSO _ _ => alpha
  | eqFO _ _ => alpha
  | allFO x beta => alpha
  | exFO x beta => alpha
  | negSO _ => alpha 
  | conjSO beta1 beta2 => beta2
  | disjSO _ _ => alpha
  | implSO _ _ => alpha
  | allSO _ _ => alpha
  | exSO _ _ => alpha
  end.

Lemma same_struc_conjSO_ex2 : forall gamma alpha beta,
  same_struc gamma (conjSO alpha beta) = true ->
    gamma = conjSO (fun_return_conj_l gamma) (fun_return_conj_r gamma).
Proof.
  induction gamma; intros alpha beta H;
    try (simpl in *; discriminate).
    reflexivity.
Qed.

Lemma same_struc_strip_exFO_l_length : forall n alpha beta,
  same_struc alpha beta = true ->
  length (strip_exFO_list alpha n) = length (strip_exFO_list beta n).
Proof.
  induction n; intros alpha beta Hss.
    do 2 rewrite strip_exFO_list_0.
    reflexivity.

    unfold strip_exFO_list.
    destruct alpha; destruct beta; simpl in *; try reflexivity;
    try discriminate.
    rewrite IHn with (beta := beta).
    fold strip_exFO_list.
    reflexivity.

    assumption.
Qed.

Lemma same_struc_comm : forall alpha beta,
  same_struc alpha beta = true ->
  same_struc beta alpha = true.
Proof.
  induction alpha; intros beta Hss; destruct beta;
    simpl in *; try discriminate; try reflexivity;
    try (    apply IHalpha; assumption).

    destruct p; destruct p0.
    rewrite (beq_nat_comm).
    assumption.

    case_eq (same_struc alpha1 beta1); intros H1;
      rewrite H1 in *; try discriminate.
    case_eq (same_struc alpha2 beta2); intros H2;
      rewrite H2 in *; try discriminate.
    rewrite IHalpha1. apply IHalpha2.
    assumption. assumption.

    case_eq (same_struc alpha1 beta1); intros H1;
      rewrite H1 in *; try discriminate.
    case_eq (same_struc alpha2 beta2); intros H2;
      rewrite H2 in *; try discriminate.
    rewrite IHalpha1. apply IHalpha2.
    assumption. assumption.

    case_eq (same_struc alpha1 beta1); intros H1;
      rewrite H1 in *; try discriminate.
    case_eq (same_struc alpha2 beta2); intros H2;
      rewrite H2 in *; try discriminate.
    rewrite IHalpha1. apply IHalpha2.
    assumption. assumption.

    destruct p0 as [Pn]; destruct p as [Qm].
    rewrite beq_nat_comm in Hss.
    case_eq (beq_nat Pn Qm); intros Hbeq;
      rewrite Hbeq in Hss. 2:discriminate.
      apply IHalpha.
      assumption.

    destruct p0 as [Pn]; destruct p as [Qm].
    rewrite beq_nat_comm in Hss.
    case_eq (beq_nat Pn Qm); intros Hbeq;
      rewrite Hbeq in Hss. 2:discriminate.
      apply IHalpha.
      assumption.
Qed.

Lemma length_strip_exFO_list_closed_exFO : forall l alpha,
  length (strip_exFO_list (list_closed_exFO alpha l) (length l)) =
  length l.
Proof.
  induction l; intros alpha.
    simpl.
    rewrite strip_exFO_list_0.
    reflexivity.

    simpl.
    rewrite IHl.
    reflexivity.
Qed.

Lemma length_strip_exFO_list_rename_FOv_pre : forall n l alpha beta xn,
  length (strip_exFO_list (rename_FOv_max_conj
      (list_closed_exFO alpha (nlist_list n l)) beta xn) n) = n.
Proof.
  intros n l alpha beta xn.
    pose proof same_struc_rename_FOv_max_conj as Hss.
  rewrite same_struc_strip_exFO_l_length with 
      (beta :=(list_closed_exFO alpha (nlist_list n l))).
  pose proof  (length_nlist_list n l) as Heq.
  rewrite <- Heq at 2.
  rewrite length_strip_exFO_list_closed_exFO.
  assumption.

    apply same_struc_comm.
    apply Hss.
Qed.

Lemma length_strip_exFO_list_rename_FOv : forall l alpha beta xn,
  length (strip_exFO_list (rename_FOv_max_conj
      (list_closed_exFO alpha l) beta xn) (length l)) = length l.
Proof.
  intros l alpha beta xn.
  destruct (nlist_list_ex (length l) l eq_refl) as [ln Heq].
  rewrite <- Heq.
  rewrite (length_nlist_list (length l) ln).
  apply length_strip_exFO_list_rename_FOv_pre.
Qed.

Lemma same_struc_strip_exFO_list_closed : forall l alpha,
  same_struc alpha (strip_exFO (list_closed_exFO alpha l) 
      (length l)) = true.
Proof.
  induction l; intros alpha.
    simpl.
    rewrite strip_exFO_0.
    apply same_struc_refl.

    simpl.
    apply IHl.
Qed.

(* Lemma same_struc_rename_FOv_A_pre_nlist : forall n alpha beta lv,
  same_struc (rename_FOv_A alpha beta (nlist_list n lv)) alpha = true.
Proof.
  induction n; intros alpha beta lv.
    rewrite (nlist_nil2 lv).
    unfold rename_FOv_A.
    simpl. apply same_struc_refl.

    destruct (nlist_cons2 _ lv) as [xn [lv' Hlv]].
    rewrite Hlv.
    simpl.
    unfold rename_FOv_A.
    simpl.
    unfold rename_FOv_A in IHn.
    rewrite (length_nlist_list n lv').
    destruct (nlist_list_ex n (strip_exFO_list
        (rename_FOv_max_conj (list_closed_exFO alpha (nlist_list n lv')) beta xn) n)
) as [ln Heq].
      apply length_strip_exFO_list_rename_FOv_pre.
    assert (length (nlist_list n ln) = n) as Heq2.
      apply length_nlist_list.
    rewrite <- Heq2 at 5.
    rewrite <- Heq.
    specialize (IHn (strip_exFO
        (rename_FOv_max_conj (list_closed_exFO alpha (nlist_list n lv')) beta xn) n)
        beta ln).
    pose proof (same_struc_strip_exFO_list_closed (nlist_list n lv')
        alpha ) as H.
    pose proof (same_struc_strip_exFO (length (nlist_list n lv')) _ _ 
      (same_struc_rename_FOv_max_conj 
          (list_closed_exFO alpha (nlist_list n lv'))
           beta xn)) as H1.
    rewrite (length_nlist_list n lv') in H1 at 2.
    apply same_struc_trans with (alpha := alpha) in H1.
      2: assumption.
    apply same_struc_comm in H1.
    apply same_struc_trans with (gamma := alpha) in IHn;
      assumption.
Qed. *)

Lemma same_struc_rename_FOv_max_conj_list_closed_exFO : forall lv alpha beta x,
  same_struc (rename_FOv_max_conj (list_closed_exFO alpha lv) beta x)
             (list_closed_exFO (rename_FOv_max_conj alpha beta x) lv) = true.
Proof.
  induction lv; intros alpha beta x.
    simpl in *.
    apply same_struc_refl.

    simpl.
    assert (same_struc (rename_FOv_max_conj (exFO a (list_closed_exFO alpha lv)) beta x)
              (exFO x ((rename_FOv_max_conj (list_closed_exFO alpha lv) beta x)))=true) as H3.
      pose proof (same_struc_rename_FOv_max_conj (exFO a (list_closed_exFO alpha lv))
          beta x) as H3.
      apply same_struc_trans with (beta := exFO a (list_closed_exFO alpha lv)).
        apply same_struc_comm. assumption.
        apply same_struc_rename_FOv_max_conj.

    apply same_struc_trans with 
      (beta := (exFO x (rename_FOv_max_conj (list_closed_exFO alpha lv) beta x))).  
      assumption.
    simpl.
    apply IHlv.
Qed.

Lemma same_struc_rename_FOv_A_pre : forall n lv alpha beta,
  same_struc alpha (rename_FOv_A_pre alpha beta lv n) = true.
Proof.
  induction n; intros lv alpha beta.
    simpl. apply same_struc_refl.

    induction lv.
      simpl. apply same_struc_refl.

      simpl.
      specialize (IHn (strip_exFO_list (rename_FOv_max_conj (list_closed_exFO alpha lv) beta a)
        (length lv)) (strip_exFO (rename_FOv_max_conj (list_closed_exFO alpha lv) beta a)
        (length lv)) beta)  .
      assert (same_struc alpha (strip_exFO (rename_FOv_max_conj (list_closed_exFO alpha lv) beta a)
           (length lv)) =  true) as H.
        pose proof (same_struc_rename_FOv_max_conj_list_closed_exFO
          lv alpha beta a) as H2.
        apply same_struc_strip_exFO with (n := length lv) in H2.
        pose proof (same_struc_strip_exFO_list_closed lv (rename_FOv_max_conj alpha beta a)) as H3.
        pose proof (same_struc_trans _ _ _ (same_struc_rename_FOv_max_conj _ _ _)
               H3 ) as H4.
        apply same_struc_comm in H2.
        apply (same_struc_trans _ _ _ H4 H2).

      apply (same_struc_trans _ _ _ H IHn).
Qed.

Lemma same_struc_rename_FOv_A : forall alpha beta lv,
  same_struc (rename_FOv_A alpha beta lv) alpha = true.
Proof.
  intros alpha beta lv. unfold rename_FOv_A.
  apply same_struc_comm.
(*   destruct (nlist_list_ex (length lv) lv eq_refl) as [ln Heq].
  rewrite <- Heq. *)
  apply same_struc_rename_FOv_A_pre.
Qed.

Lemma equiv_conjSO3 : forall alpha1 alpha2 beta1 beta2 W Iv Ip Ir,
  SOturnst W Iv Ip Ir (conjSO (conjSO alpha1 beta1) (conjSO alpha2 beta2)) <->
  SOturnst W Iv Ip Ir (conjSO (conjSO alpha1 alpha2) (conjSO beta1 beta2)).
Proof.
  intros alpha1 alpha2 beta1 beta2 W Iv Ip Ir.
  split; intros [[H1 H2] [H3 H4]]; apply conj;
    apply conj; assumption.
Qed.

Lemma same_struc_conjSO_l : forall alpha1 alpha2 beta1 beta2,
  same_struc (conjSO alpha1 beta1) (conjSO alpha2 beta2) = true ->
  same_struc alpha1 alpha2 = true.
Proof.
  intros alpha1 alpha2 beta1 beta2 Hss.
  simpl in Hss.
  case_eq (same_struc alpha1 alpha2); intros Hss2;
    rewrite Hss2 in *.
    reflexivity. discriminate.
Qed.

Lemma same_struc_conjSO_r : forall alpha1 alpha2 beta1 beta2,
  same_struc (conjSO alpha1 beta1) (conjSO alpha2 beta2) = true ->
  same_struc beta1 beta2 = true.
Proof.
  intros alpha1 alpha2 beta1 beta2 Hss.
  simpl in Hss.
  case_eq (same_struc alpha1 alpha2); intros Hss2;
    rewrite Hss2 in *.
    assumption. discriminate.
Qed.

Lemma same_struc_conjSO : forall alpha1 alpha2 beta1 beta2,
  same_struc (conjSO alpha1 beta1) (conjSO alpha2 beta2) = true ->
  same_struc alpha1 alpha2 = true /\ same_struc beta1 beta2 = true.
Proof.
  intros alpha1 alpha2 beta1 beta2 Hss. 
  apply conj.
    apply same_struc_conjSO_l in Hss; assumption.
    apply same_struc_conjSO_r in Hss; assumption.
Qed.

Lemma same_struc_REL : forall alpha beta,
  same_struc alpha beta = true ->
  REL alpha = true ->
  REL beta = true.
Proof.
  induction alpha; intros beta Hss HREL;
    simpl in *; try discriminate.

    destruct beta; try discriminate.
    reflexivity.

    case_eq (REL alpha1); intros HREL1;
      rewrite HREL1 in *; try discriminate.
    destruct beta; try discriminate.
    case_eq (same_struc alpha1 beta1); intros Hss1;
      rewrite Hss1 in *; try discriminate.

    simpl.
    rewrite IHalpha1; try assumption.
    apply IHalpha2; try assumption.
    reflexivity.
Qed. 

Lemma same_struc_AT : forall alpha beta,
  same_struc alpha beta = true ->
  AT alpha = true ->
  AT beta = true.
Proof.
  induction alpha; intros beta Hss HREL;
    simpl in *; try discriminate.

    destruct beta; try discriminate.
    reflexivity.

    case_eq (AT alpha1); intros HAT1;
      rewrite HAT1 in *; try discriminate.
    destruct beta; try discriminate.
    case_eq (same_struc alpha1 beta1); intros Hss1;
      rewrite Hss1 in *; try discriminate.

    simpl.
    rewrite IHalpha1; try assumption.
    apply IHalpha2; try assumption.
    reflexivity.
Qed.



Lemma equiv_conjSO4 : forall rel1' rel2 atm1' (W0 : Set) (Iv0 : FOvariable -> W0) (Ip0 : predicate -> W0 -> Prop)
  (Ir0 : W0 -> W0 -> Prop) ,
SOturnst W0 Iv0 Ip0 Ir0 (conjSO (conjSO rel1' rel2) atm1') <->
SOturnst W0 Iv0 Ip0 Ir0 (conjSO (conjSO rel1' atm1') rel2).
Proof.
  intros.
  simpl.
  split; intros [[H1 H2] H3];
   apply conj; try apply conj; assumption.
Qed.

Lemma equiv_conjSO5 : forall alpha beta gamma W Iv Ip Ir,
  SOturnst W Iv Ip Ir (conjSO alpha (conjSO beta gamma)) <->
  SOturnst W Iv Ip Ir (conjSO (conjSO alpha beta) gamma).
Proof.
  intros.
  simpl.
  split; [intros [H1 [H2 H3]] | intros [[H1 H2] H3]];
   apply conj; try apply conj; assumption.
Qed.

Lemma preprocess_vsSahlq_ante_1 : forall alpha1 alpha2 lv1 rel1 atm1 
        lv2 rel2 atm2,
  conjSO_exFO_relatSO alpha2 = true ->
  REL rel1 = true ->
  AT atm1 = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha1 <->
      SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel1 atm1) lv1)) ->
  REL rel2 = true ->
  AT atm2 = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha2 <->
      SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel2 atm2) lv2)) ->
  conjSO_exFO_relatSO alpha1 = true ->
exists lv : list FOvariable,
  (exists rel : SecOrder,
     REL rel = true /\
     ((exists atm : SecOrder,
         AT atm = true /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
          SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv))) \/
      (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
         (Ir : W -> W -> Prop),
       SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
       SOturnst W Iv Ip Ir (list_closed_exFO rel lv)))) \/
  (exists atm : SecOrder,
     AT atm = true /\
     (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
      SOturnst W Iv Ip Ir (list_closed_exFO atm lv))).
Proof.
  intros alpha1 alpha2 lv1 rel1 atm1 lv2 rel2 atm2
        H HREL1 HAT1 H_1 HREL2 HAT2 H_2 H1.
    destruct (same_struc_conjSO_ex _ _ _ (same_struc_rename_FOv_A (conjSO rel1 atm1) 
                                            (rename_FOv_A (conjSO rel2 atm2) 
                                               (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1))
      as [rel1' [atm1' Heq1]].
    destruct (same_struc_conjSO_ex _ _ _ (same_struc_rename_FOv_A (conjSO rel2 atm2) 
                                            (list_closed_exFO (conjSO rel1 atm1) lv1)
                                             lv2)) as [rel2' [atm2' Heq2]].
     exists (app 
                (rename_FOv_A_list (conjSO rel2 atm2) 
                     (list_closed_exFO (conjSO rel1 atm1) lv1) lv2)
(rename_FOv_A_list (conjSO rel1 atm1) 
                  (rename_FOv_A (conjSO rel2 atm2)
                     (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1 )).

    left.
    exists (conjSO rel1' rel2').
    apply conj.
      pose proof (same_struc_rename_FOv_A (conjSO rel2 atm2) (list_closed_exFO (conjSO rel1 atm1) lv1)
         lv2) as Hsame2.
      pose proof (same_struc_rename_FOv_A (conjSO rel1 atm1)
         (rename_FOv_A (conjSO rel2 atm2)
            (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1) as Hsame1.
      rewrite Heq2 in Hsame2.
      rewrite Heq1 in Hsame1.
      apply same_struc_conjSO_l in Hsame2.
      apply same_struc_comm in Hsame2.
      apply same_struc_REL in Hsame2; try assumption.
      apply same_struc_conjSO_l in Hsame1.
      apply same_struc_comm in Hsame1.
      apply same_struc_REL in Hsame1; try assumption.
      simpl; rewrite Hsame1; assumption.

    left.
    exists (conjSO atm1' atm2').
    apply conj.
      pose proof (same_struc_rename_FOv_A (conjSO rel2 atm2) (list_closed_exFO (conjSO rel1 atm1) lv1)
         lv2) as Hsame2.
      pose proof (same_struc_rename_FOv_A (conjSO rel1 atm1)
         (rename_FOv_A (conjSO rel2 atm2)
            (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1) as Hsame1.
      rewrite Heq2 in Hsame2.
      rewrite Heq1 in Hsame1.
      apply same_struc_conjSO_r in Hsame2.
      apply same_struc_comm in Hsame2.
      apply same_struc_AT in Hsame2; try assumption.
      apply same_struc_conjSO_r in Hsame1.
      apply same_struc_comm in Hsame1.
      apply same_struc_AT in Hsame1; try assumption.
      simpl; rewrite Hsame1; assumption.

    intros W Iv Ip Ir.
    split; intros SOt.
      apply (equiv_list_closed_exFO (conjSO (conjSO rel1' rel2') (conjSO atm1' atm2'))
                                    (conjSO (conjSO rel1' atm1') (conjSO rel2' atm2'))).
        apply equiv_conjSO3.
      rewrite <- Heq1.
      rewrite <- Heq2.
      rewrite list_closed_exFO_app.
      apply equiv3_3_struc2_both with (alpha := (conjSO rel1 atm1)).
      simpl.
      apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.

      apply (equiv_list_closed_exFO (conjSO (conjSO rel1' rel2') (conjSO atm1' atm2'))
                                    (conjSO (conjSO rel1' atm1') (conjSO rel2' atm2')))
              in SOt.
      rewrite <- Heq1 in SOt.
      rewrite <- Heq2 in SOt.
      rewrite list_closed_exFO_app in SOt.
      apply equiv3_3_struc2_both with (alpha := (conjSO rel1 atm1)) in SOt.
      simpl.
      apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.

        apply equiv_conjSO3.
Qed.

Lemma preprocess_vsSahlq_ante_2 : forall alpha1 alpha2 lv1 rel1 atm1 
                                       lv2 rel2,
  conjSO_exFO_relatSO alpha2 = true ->
  REL rel1 = true ->
  AT atm1 = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha1 <->
      SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel1 atm1) lv1)) ->
  REL rel2 = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha2 <->
      SOturnst W Iv Ip Ir (list_closed_exFO rel2 lv2)) ->
  conjSO_exFO_relatSO alpha1 = true ->
  exists lv : list FOvariable,
  (exists rel : SecOrder,
     REL rel = true /\
     ((exists atm : SecOrder,
         AT atm = true /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
          SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv))) \/
      (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
         (Ir : W -> W -> Prop),
       SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
       SOturnst W Iv Ip Ir (list_closed_exFO rel lv)))) \/
  (exists atm : SecOrder,
     AT atm = true /\
     (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
      SOturnst W Iv Ip Ir (list_closed_exFO atm lv))).
Proof.
  intros alpha1 alpha2 lv1 rel1 atm1 lv2 rel2 H HREL1 HAT1 H_1
         HREL2 H_2 H1.
    destruct (same_struc_conjSO_ex _ _ _ (same_struc_rename_FOv_A (conjSO rel1 atm1) 
                                            (rename_FOv_A rel2 
                                               (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1))
      as [rel1' [atm1' Heq1]].
(*     destruct (same_struc_conjSO_ex _ _ _ (same_struc_rename_FOv_A rel2  
                                            (list_closed_exFO (conjSO rel1 atm1) lv1)
                                             lv2)) as [rel2' [atm2' Heq2]].
 *)
     exists (app 
                (rename_FOv_A_list rel2 
                     (list_closed_exFO (conjSO rel1 atm1) lv1) lv2)
(rename_FOv_A_list (conjSO rel1 atm1) 
                  (rename_FOv_A rel2
                     (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1 )).

    left.
    exists (conjSO rel1' (rename_FOv_A rel2 (list_closed_exFO (conjSO rel1 atm1) lv1) lv2)) .
    apply conj.
      pose proof (same_struc_rename_FOv_A rel2 (list_closed_exFO (conjSO rel1 atm1) lv1)
         lv2) as Hsame2.
      pose proof (same_struc_rename_FOv_A (conjSO rel1 atm1)
         (rename_FOv_A rel2
            (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1) as Hsame1.
(*       rewrite Heq2 in Hsame2. *)
      rewrite Heq1 in Hsame1.
(*       apply same_struc_conjSO_l in Hsame2.
 *)      apply same_struc_comm in Hsame2.
      apply same_struc_REL in Hsame2; try assumption.
      apply same_struc_conjSO_l in Hsame1.
      apply same_struc_comm in Hsame1.
      apply same_struc_REL in Hsame1; try assumption.
      simpl; rewrite Hsame1; assumption. 
      

    left.
    exists atm1'.
    apply conj.
      pose proof (same_struc_rename_FOv_A rel2 (list_closed_exFO (conjSO rel1 atm1) lv1)
         lv2) as Hsame2.
      pose proof (same_struc_rename_FOv_A (conjSO rel1 atm1)
         (rename_FOv_A rel2
            (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1) as Hsame1.
(*       rewrite Heq2 in Hsame2.
 *)      rewrite Heq1 in Hsame1.
(*       apply same_struc_conjSO_r in Hsame2.
 *)      apply same_struc_comm in Hsame2.
(*       apply same_struc_AT in Hsame2; try assumption.
 *)      apply same_struc_conjSO_r in Hsame1.
      apply same_struc_comm in Hsame1.
      apply same_struc_AT in Hsame1; try assumption.
(*       simpl; rewrite Hsame1; assumption.
 *)
    intros W Iv Ip Ir.
    split; intros SOt.
      apply (equiv_list_closed_exFO 
                (conjSO (conjSO rel1' (rename_FOv_A rel2 (list_closed_exFO (conjSO rel1 atm1) lv1) lv2)) atm1')
                        (conjSO (conjSO rel1' atm1') (rename_FOv_A rel2 (list_closed_exFO (conjSO rel1 atm1) lv1) lv2))).
      apply equiv_conjSO4.
      rewrite <- Heq1.
(*       rewrite <- Heq2.
 *)      rewrite list_closed_exFO_app.
      apply equiv3_3_struc2_both with (alpha := conjSO rel1 atm1).
      simpl.
      apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.

      apply (equiv_list_closed_exFO (conjSO (conjSO rel1' (rename_FOv_A rel2 (list_closed_exFO (conjSO rel1 atm1) lv1) lv2)) atm1')
                                    (conjSO (conjSO rel1' atm1') (rename_FOv_A rel2 (list_closed_exFO (conjSO rel1 atm1) lv1) lv2)))
              in SOt.
      rewrite <- Heq1 in SOt.
      rewrite list_closed_exFO_app in SOt.
      apply equiv3_3_struc2_both with (alpha := (conjSO rel1 atm1)) in SOt.
      simpl.
      apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.

        apply equiv_conjSO4.
Qed.

Lemma preprocess_vsSahlq_ante_3 : forall alpha1 alpha2 lv1 rel1 atm1 lv2 atm2,
  conjSO_exFO_relatSO alpha2 = true ->
  REL rel1 = true ->
  AT atm1 = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha1 <->
      SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel1 atm1) lv1)) ->
  AT atm2 = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha2 <->
      SOturnst W Iv Ip Ir (list_closed_exFO atm2 lv2)) ->
  conjSO_exFO_relatSO alpha1 = true ->
exists lv : list FOvariable,
  (exists rel : SecOrder,
     REL rel = true /\
     ((exists atm : SecOrder,
         AT atm = true /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
          SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv))) \/
      (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
         (Ir : W -> W -> Prop),
       SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
       SOturnst W Iv Ip Ir (list_closed_exFO rel lv)))) \/
  (exists atm : SecOrder,
     AT atm = true /\
     (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
      SOturnst W Iv Ip Ir (list_closed_exFO atm lv))).
Proof.
  intros alpha1 alpha2 lv1 rel1 atm1 lv2 atm2
         H HREL1 HAT1 H_1 HAT2 H_2 H1.
    destruct (same_struc_conjSO_ex _ _ _ (same_struc_rename_FOv_A (conjSO rel1 atm1) 
                                            (rename_FOv_A atm2
                                               (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1))
      as [rel1' [atm1' Heq1]].
     exists (app 
                (rename_FOv_A_list atm2 
                     (list_closed_exFO (conjSO rel1 atm1) lv1) lv2)
(rename_FOv_A_list (conjSO rel1 atm1) 
                  (rename_FOv_A atm2
                     (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1 )).

    left.
    exists rel1'.
    apply conj.
      pose proof (same_struc_rename_FOv_A atm2 (list_closed_exFO (conjSO rel1 atm1) lv1)
         lv2) as Hsame2.
      pose proof (same_struc_rename_FOv_A (conjSO rel1 atm1)
         (rename_FOv_A atm2
            (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1) as Hsame1.
(*       rewrite Heq2 in Hsame2.
 *)      rewrite Heq1 in Hsame1.
      apply same_struc_conjSO_l in Hsame1.
      apply same_struc_comm in Hsame1.
      apply same_struc_REL in Hsame1; try assumption.

    left.
    exists (conjSO atm1' (rename_FOv_A atm2 (list_closed_exFO (conjSO rel1 atm1) lv1)
         lv2)).
    apply conj.
      pose proof (same_struc_rename_FOv_A atm2 (list_closed_exFO (conjSO rel1 atm1) lv1)
         lv2) as Hsame2.
      pose proof (same_struc_rename_FOv_A (conjSO rel1 atm1)
         (rename_FOv_A atm2
            (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1) as Hsame1.
      rewrite Heq1 in Hsame1.
      apply same_struc_conjSO_r in Hsame1.
      apply same_struc_comm in Hsame1.
      apply same_struc_comm in Hsame2.
      apply same_struc_AT in Hsame2; try assumption.
      apply same_struc_AT in Hsame1; try assumption.
      simpl; rewrite Hsame1; assumption.

    intros W Iv Ip Ir.
    split; intros SOt.
      apply (equiv_list_closed_exFO (conjSO rel1' (conjSO atm1' (rename_FOv_A atm2 
              (list_closed_exFO (conjSO rel1 atm1) lv1) lv2)))
                                    (conjSO (conjSO rel1' atm1')
              (rename_FOv_A atm2 (list_closed_exFO (conjSO rel1 atm1) lv1) lv2))).
        apply equiv_conjSO5.
      rewrite <- Heq1.
      rewrite list_closed_exFO_app.
      apply equiv3_3_struc2_both with (alpha := (conjSO rel1 atm1)).
      simpl.
      apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.

      apply (equiv_list_closed_exFO (conjSO rel1' (conjSO atm1' (rename_FOv_A atm2 
              (list_closed_exFO (conjSO rel1 atm1) lv1) lv2)))
                                    (conjSO (conjSO rel1' atm1') (rename_FOv_A atm2 
              (list_closed_exFO (conjSO rel1 atm1) lv1) lv2)))
              in SOt.
      rewrite <- Heq1 in SOt.
      rewrite list_closed_exFO_app in SOt.
      apply equiv3_3_struc2_both with (alpha := (conjSO rel1 atm1)) in SOt.
      simpl.
      apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.

        apply equiv_conjSO5.
Qed.

Lemma preprocess_vsSahlq_ante_4 : forall alpha1 alpha2 lv1 rel1 lv2 rel2 atm2,
  conjSO_exFO_relatSO alpha2 = true ->
  REL rel1 = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha1 <->
      SOturnst W Iv Ip Ir (list_closed_exFO rel1 lv1)) ->
  REL rel2 = true ->
  AT atm2 = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha2 <->
      SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel2 atm2) lv2) ) ->
  conjSO_exFO_relatSO alpha1 = true ->
exists lv : list FOvariable,
  (exists rel : SecOrder,
     REL rel = true /\
     ((exists atm : SecOrder,
         AT atm = true /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
          SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv))) \/
      (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
         (Ir : W -> W -> Prop),
       SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
       SOturnst W Iv Ip Ir (list_closed_exFO rel lv)))) \/
  (exists atm : SecOrder,
     AT atm = true /\
     (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
      SOturnst W Iv Ip Ir (list_closed_exFO atm lv))).
Proof.
  intros alpha1 alpha2 lv1 rel1 lv2 rel2 atm2
         H HREL1 H_1 HREL2 HAT2 H_2 H1.
(*     destruct (same_struc_conjSO_ex _ _ _ (same_struc_rename_FOv_A (conjSO rel1 atm1) 
                                            (rename_FOv_A (conjSO rel2 atm2) 
                                               (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1))
      as [rel1' [atm1' Heq1]].
 *)    destruct (same_struc_conjSO_ex _ _ _ (same_struc_rename_FOv_A (conjSO rel2 atm2) 
                                            (list_closed_exFO rel1 lv1)
                                             lv2)) as [rel2' [atm2' Heq2]].
     exists (app 
                (rename_FOv_A_list (conjSO rel2 atm2) 
                     (list_closed_exFO rel1 lv1) lv2)
(rename_FOv_A_list rel1 
                  (rename_FOv_A (conjSO rel2 atm2)
                     (list_closed_exFO rel1 lv1) lv2) lv1 )).

    left.
    exists (conjSO (rename_FOv_A rel1 (rename_FOv_A (conjSO rel2 atm2) 
                      (list_closed_exFO rel1 lv1) lv2) lv1) rel2').
    apply conj.
      pose proof (same_struc_rename_FOv_A (conjSO rel2 atm2) (list_closed_exFO rel1 lv1)
         lv2) as Hsame2.
      pose proof (same_struc_rename_FOv_A rel1
         (rename_FOv_A (conjSO rel2 atm2)
            (list_closed_exFO rel1 lv1) lv2) lv1) as Hsame1.
      rewrite Heq2 in Hsame2.
(*       rewrite Heq1 in Hsame1. *)
      apply same_struc_conjSO_l in Hsame2.
      apply same_struc_comm in Hsame2.
      apply same_struc_REL in Hsame2; try assumption.
(*       apply same_struc_conjSO_l in Hsame1. *)
      apply same_struc_comm in Hsame1.
      apply same_struc_REL in Hsame1; try assumption.
      simpl; rewrite Hsame1; assumption.

    left.
    exists  atm2'.
    apply conj.
      pose proof (same_struc_rename_FOv_A (conjSO rel2 atm2) (list_closed_exFO rel1 lv1)
         lv2) as Hsame2.
      pose proof (same_struc_rename_FOv_A rel1
         (rename_FOv_A (conjSO rel2 atm2)
            (list_closed_exFO rel1 lv1) lv2) lv1) as Hsame1.
      rewrite Heq2 in Hsame2.
(*       rewrite Heq1 in Hsame1. *)
      apply same_struc_conjSO_r in Hsame2.
      apply same_struc_comm in Hsame2.
      apply same_struc_AT in Hsame2; try assumption.

    intros W Iv Ip Ir.
    split; intros SOt.
      apply (equiv_list_closed_exFO (conjSO (conjSO (rename_FOv_A rel1 (rename_FOv_A (conjSO rel2 atm2) 
                      (list_closed_exFO rel1 lv1) lv2) lv1) rel2')  atm2')
                                    (conjSO (rename_FOv_A rel1 (rename_FOv_A (conjSO rel2 atm2) 
                      (list_closed_exFO rel1 lv1) lv2) lv1) (conjSO rel2' atm2'))).
        intros; split; intros; apply equiv_conjSO5; assumption.
      rewrite <- Heq2.
      rewrite list_closed_exFO_app.
      apply equiv3_3_struc2_both with (alpha := rel1).
      rewrite SOturnst_conjSO; apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.

      apply (equiv_list_closed_exFO (conjSO (conjSO (rename_FOv_A rel1 (rename_FOv_A (conjSO rel2 atm2) 
                      (list_closed_exFO rel1 lv1) lv2) lv1) rel2')  atm2')
                                    (conjSO (rename_FOv_A rel1 (rename_FOv_A (conjSO rel2 atm2) 
                      (list_closed_exFO rel1 lv1) lv2) lv1) (conjSO rel2' atm2'))) in SOt;
        try (intros; split; intros; apply equiv_conjSO5; assumption).
      rewrite <- Heq2 in SOt.
      rewrite list_closed_exFO_app in SOt.
      apply equiv3_3_struc2_both with (alpha := rel1) in SOt.
      rewrite SOturnst_conjSO; apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.
Qed.

Lemma preprocess_vsSahlq_ante_5 : forall alpha1 alpha2 lv1 rel1 lv2 rel2,
  conjSO_exFO_relatSO alpha2 = true ->
  REL rel1 = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha1 <->
      SOturnst W Iv Ip Ir (list_closed_exFO rel1 lv1)) ->
  REL rel2 = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha2 <->
      SOturnst W Iv Ip Ir (list_closed_exFO rel2 lv2)) ->
  conjSO_exFO_relatSO alpha1 = true ->
exists lv : list FOvariable,
  (exists rel : SecOrder,
     REL rel = true /\
     ((exists atm : SecOrder,
         AT atm = true /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
          SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv))) \/
      (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
         (Ir : W -> W -> Prop),
       SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
       SOturnst W Iv Ip Ir (list_closed_exFO rel lv)))) \/
  (exists atm : SecOrder,
     AT atm = true /\
     (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
      SOturnst W Iv Ip Ir (list_closed_exFO atm lv))).
Proof.
  intros alpha1 alpha2 lv1 rel1 lv2 rel2
         H HREL1 H_1 HREL2 H_2 H1.
     exists (app 
                (rename_FOv_A_list rel2 
                     (list_closed_exFO rel1 lv1) lv2)
(rename_FOv_A_list rel1 
                  (rename_FOv_A rel2
                     (list_closed_exFO rel1 lv1) lv2) lv1 )).

    left.
pose proof equiv3_3_struc2_both.
    exists (conjSO
                (rename_FOv_A rel1
                   (rename_FOv_A rel2 (list_closed_exFO rel1 lv1) lv2) lv1)
                (rename_FOv_A rel2 (list_closed_exFO rel1 lv1) lv2)).
    apply conj.
      pose proof (same_struc_rename_FOv_A rel2 (list_closed_exFO rel1 lv1)
         lv2) as Hsame2.
      pose proof (same_struc_rename_FOv_A rel1
         (rename_FOv_A rel2
            (list_closed_exFO rel1 lv1) lv2) lv1) as Hsame1.
      apply same_struc_comm in Hsame2.
      apply same_struc_REL in Hsame2; try assumption.
      apply same_struc_comm in Hsame1.
      apply same_struc_REL in Hsame1; try assumption.
      simpl; rewrite Hsame1; assumption.

    right.
    intros W Iv Ip Ir.
    split; intros SOt.
(*       apply (equiv_list_closed_exFO (conjSO (conjSO rel1' rel2') (conjSO atm1' atm2'))
                                    (conjSO (conjSO rel1' atm1') (conjSO rel2' atm2'))).
        apply equiv_conjSO3.
      rewrite <- Heq1.
      rewrite <- Heq2. *)
      rewrite list_closed_exFO_app.
      apply equiv3_3_struc2_both with (alpha := rel1).
      simpl.
      apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.

      rewrite list_closed_exFO_app in SOt.
      apply equiv3_3_struc2_both with (alpha := rel1) in SOt.
      simpl.
      apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.
Qed.

Lemma preprocess_vsSahlq_ante_6 : forall alpha1 alpha2 lv1 rel1 
        lv2 atm2,
  conjSO_exFO_relatSO alpha2 = true ->
  REL rel1 = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha1 <->
      SOturnst W Iv Ip Ir (list_closed_exFO rel1 lv1)) ->
  AT atm2 = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha2 <->
      SOturnst W Iv Ip Ir (list_closed_exFO atm2 lv2)) ->
  conjSO_exFO_relatSO alpha1 = true ->
exists lv : list FOvariable,
  (exists rel : SecOrder,
     REL rel = true /\
     ((exists atm : SecOrder,
         AT atm = true /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
          SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv))) \/
      (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
         (Ir : W -> W -> Prop),
       SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
       SOturnst W Iv Ip Ir (list_closed_exFO rel lv)))) \/
  (exists atm : SecOrder,
     AT atm = true /\
     (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
      SOturnst W Iv Ip Ir (list_closed_exFO atm lv))).
Proof.
  intros alpha1 alpha2 lv1 rel1  lv2  atm2
        H HREL1  H_1  HAT2 H_2 H1.
     exists (app 
                (rename_FOv_A_list atm2
                     (list_closed_exFO rel1 lv1) lv2)
(rename_FOv_A_list rel1 
                  (rename_FOv_A  atm2
                     (list_closed_exFO rel1 lv1) lv2) lv1 )).

    left.
    exists (rename_FOv_A rel1 (rename_FOv_A atm2 (list_closed_exFO rel1 lv1) lv2) lv1).
    apply conj.
      pose proof (same_struc_rename_FOv_A rel1
         (rename_FOv_A (atm2)
            (list_closed_exFO rel1 lv1) lv2) lv1) as Hsame1.
      apply same_struc_comm in Hsame1.
      apply same_struc_REL in Hsame1; try assumption.

    left.
    exists (rename_FOv_A atm2 (list_closed_exFO rel1 lv1) lv2).
    apply conj.
      pose proof (same_struc_rename_FOv_A atm2 (list_closed_exFO rel1 lv1)
         lv2) as Hsame2.
      apply same_struc_comm in Hsame2.
      apply same_struc_AT in Hsame2; try assumption.

    intros W Iv Ip Ir.
    split; intros SOt.
      rewrite list_closed_exFO_app.
      apply equiv3_3_struc2_both with (alpha := rel1).
      simpl.
      apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.

      rewrite list_closed_exFO_app in SOt.
      apply equiv3_3_struc2_both with (alpha := rel1) in SOt.
      simpl.
      apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.
Qed.

Lemma equiv_conjSO6 : forall (alpha beta gamma : SecOrder) (W : Set) 
       (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
       (Ir : W -> W -> Prop),
     SOturnst W Iv Ip Ir (conjSO alpha (conjSO beta gamma)) <->
     SOturnst W Iv Ip Ir (conjSO beta (conjSO alpha gamma)).
Proof.
  intros.
  simpl.
  split; [intros [H1 [H2 H3]] | intros [H1 [H2 H3]]];
   apply conj; try apply conj; assumption.
Qed.

Lemma preprocess_vsSahlq_ante_7 : forall alpha1 alpha2 lv1 atm1 
        lv2 rel2 atm2,
  conjSO_exFO_relatSO alpha2 = true ->
  AT atm1 = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha1 <->
      SOturnst W Iv Ip Ir (list_closed_exFO atm1 lv1)) ->
  REL rel2 = true ->
  AT atm2 = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha2 <->
      SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel2 atm2) lv2)) ->
  conjSO_exFO_relatSO alpha1 = true ->
exists lv : list FOvariable,
  (exists rel : SecOrder,
     REL rel = true /\
     ((exists atm : SecOrder,
         AT atm = true /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
          SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv))) \/
      (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
         (Ir : W -> W -> Prop),
       SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
       SOturnst W Iv Ip Ir (list_closed_exFO rel lv)))) \/
  (exists atm : SecOrder,
     AT atm = true /\
     (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
      SOturnst W Iv Ip Ir (list_closed_exFO atm lv))).
Proof.
  intros alpha1 alpha2 lv1 atm1 lv2 rel2 atm2
        H HAT1 H_1 HREL2 HAT2 H_2 H1.
    destruct (same_struc_conjSO_ex _ _ _ (same_struc_rename_FOv_A (conjSO rel2 atm2) 
                                            (list_closed_exFO atm1 lv1)
                                             lv2)) as [rel2' [atm2' Heq2]].
     exists (app 
                (rename_FOv_A_list (conjSO rel2 atm2) 
                     (list_closed_exFO atm1 lv1) lv2)
(rename_FOv_A_list  atm1
                  (rename_FOv_A (conjSO rel2 atm2)
                     (list_closed_exFO  atm1 lv1) lv2) lv1 )).

    left.
    exists rel2'.
    apply conj.
      pose proof (same_struc_rename_FOv_A (conjSO rel2 atm2) (list_closed_exFO atm1 lv1)
         lv2) as Hsame2.
      rewrite Heq2 in Hsame2.
      apply same_struc_conjSO_l in Hsame2.
      apply same_struc_comm in Hsame2.
      apply same_struc_REL in Hsame2; try assumption.

    left.
    exists (conjSO (rename_FOv_A atm1 (rename_FOv_A (conjSO rel2 atm2) 
                        (list_closed_exFO atm1 lv1) lv2) lv1) atm2').
    apply conj.
      pose proof (same_struc_rename_FOv_A (conjSO rel2 atm2) (list_closed_exFO atm1 lv1)
         lv2) as Hsame2.
      pose proof (same_struc_rename_FOv_A atm1
         (rename_FOv_A (conjSO rel2 atm2)
            (list_closed_exFO  atm1 lv1) lv2) lv1) as Hsame1.
      rewrite Heq2 in Hsame2.
      apply same_struc_conjSO_r in Hsame2.
      apply same_struc_comm in Hsame2.
      apply same_struc_AT in Hsame2; try assumption.
      apply same_struc_comm in Hsame1.
      apply same_struc_AT in Hsame1; try assumption.
      simpl; rewrite Hsame1; assumption.

    intros W Iv Ip Ir.
    split; intros SOt.
      apply (equiv_list_closed_exFO (conjSO  rel2' (conjSO (rename_FOv_A atm1 (rename_FOv_A (conjSO rel2 atm2) 
                        (list_closed_exFO atm1 lv1) lv2) lv1) atm2'))
                                    (conjSO (rename_FOv_A atm1 (rename_FOv_A (conjSO rel2 atm2) 
                        (list_closed_exFO atm1 lv1) lv2) lv1) (conjSO rel2' atm2'))).
        apply equiv_conjSO6.
      rewrite <- Heq2.
      rewrite list_closed_exFO_app.
      apply equiv3_3_struc2_both with (alpha := (atm1)).
      simpl.
      apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.

      apply (equiv_list_closed_exFO (conjSO  rel2' (conjSO (rename_FOv_A atm1 (rename_FOv_A (conjSO rel2 atm2) 
                        (list_closed_exFO atm1 lv1) lv2) lv1) atm2'))
                                    (conjSO (rename_FOv_A atm1 (rename_FOv_A (conjSO rel2 atm2) 
                        (list_closed_exFO atm1 lv1) lv2) lv1) (conjSO rel2' atm2'))) in SOt;
        try apply equiv_conjSO6.
      rewrite <- Heq2 in SOt.
      rewrite list_closed_exFO_app in SOt.
      apply equiv3_3_struc2_both with (alpha := (atm1)) in SOt.
      simpl.
      apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.
Qed.

Lemma preprocess_vsSahlq_ante_8 : forall alpha1 alpha2 lv1 atm1 
        lv2 rel2,
  conjSO_exFO_relatSO alpha2 = true ->
  AT atm1 = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha1 <->
      SOturnst W Iv Ip Ir (list_closed_exFO atm1 lv1)) ->
  REL rel2 = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha2 <->
      SOturnst W Iv Ip Ir (list_closed_exFO rel2 lv2)) ->
  conjSO_exFO_relatSO alpha1 = true ->
exists lv : list FOvariable,
  (exists rel : SecOrder,
     REL rel = true /\
     ((exists atm : SecOrder,
         AT atm = true /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
          SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv))) \/
      (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
         (Ir : W -> W -> Prop),
       SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
       SOturnst W Iv Ip Ir (list_closed_exFO rel lv)))) \/
  (exists atm : SecOrder,
     AT atm = true /\
     (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
      SOturnst W Iv Ip Ir (list_closed_exFO atm lv))).
Proof.
  intros alpha1 alpha2 lv1 atm1 lv2 rel2
        H HAT1 H_1 HREL2 H_2 H1.
     exists (app 
                (rename_FOv_A_list rel2 
                     (list_closed_exFO atm1 lv1) lv2)
(rename_FOv_A_list atm1
                  (rename_FOv_A rel2
                     (list_closed_exFO atm1 lv1) lv2) lv1 )).

    left.
    exists (rename_FOv_A rel2 (list_closed_exFO atm1 lv1) lv2).
    apply conj.
      pose proof (same_struc_rename_FOv_A rel2 (list_closed_exFO atm1 lv1)
         lv2) as Hsame2.
      apply same_struc_comm in Hsame2.
      apply same_struc_REL in Hsame2; try assumption.

    left.
    exists (rename_FOv_A atm1 (rename_FOv_A rel2 (list_closed_exFO atm1 lv1) lv2) lv1).
    apply conj.
      pose proof (same_struc_rename_FOv_A rel2 (list_closed_exFO atm1 lv1)
         lv2) as Hsame2.
      pose proof (same_struc_rename_FOv_A atm1
         (rename_FOv_A rel2
            (list_closed_exFO atm1 lv1) lv2) lv1) as Hsame1.
      apply same_struc_comm in Hsame1.
      apply same_struc_AT in Hsame1; try assumption.

    intros W Iv Ip Ir.
    split; intros SOt.
      apply (equiv_list_closed_exFO (conjSO (rename_FOv_A rel2 (list_closed_exFO atm1 lv1) lv2) (rename_FOv_A atm1 (rename_FOv_A rel2 (list_closed_exFO atm1 lv1) lv2) lv1))
                                    (conjSO (rename_FOv_A atm1 (rename_FOv_A rel2 (list_closed_exFO atm1 lv1) lv2) lv1) (rename_FOv_A rel2 (list_closed_exFO atm1 lv1) lv2))).
        apply equiv_conjSO.
      rewrite list_closed_exFO_app.
      apply equiv3_3_struc2_both with (alpha := atm1).
      simpl.
      apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.

      apply (equiv_list_closed_exFO (conjSO (rename_FOv_A rel2 (list_closed_exFO atm1 lv1) lv2) (rename_FOv_A atm1 (rename_FOv_A rel2 (list_closed_exFO atm1 lv1) lv2) lv1))
                                    (conjSO (rename_FOv_A atm1 (rename_FOv_A rel2 (list_closed_exFO atm1 lv1) lv2) lv1) (rename_FOv_A rel2 (list_closed_exFO atm1 lv1) lv2))) in SOt.
        apply equiv_conjSO.
      rewrite list_closed_exFO_app in SOt.
      apply equiv3_3_struc2_both with (alpha := atm1) in SOt.
      simpl.
      apply conj.
        apply H_2. apply SOt.
        apply H_1. apply SOt.

        apply equiv_conjSO.
Qed.

Lemma preprocess_vsSahlq_ante_9 : forall alpha1 alpha2 lv1 atm1 
        lv2 atm2,
  conjSO_exFO_relatSO alpha2 = true ->
  AT atm1 = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha1 <->
      SOturnst W Iv Ip Ir (list_closed_exFO  atm1 lv1)) ->
  AT atm2 = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha2 <->
      SOturnst W Iv Ip Ir (list_closed_exFO atm2 lv2)) ->
  conjSO_exFO_relatSO alpha1 = true ->
exists lv : list FOvariable,
  (exists rel : SecOrder,
     REL rel = true /\
     ((exists atm : SecOrder,
         AT atm = true /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
          SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv))) \/
      (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
         (Ir : W -> W -> Prop),
       SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
       SOturnst W Iv Ip Ir (list_closed_exFO rel lv)))) \/
  (exists atm : SecOrder,
     AT atm = true /\
     (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
      SOturnst W Iv Ip Ir (list_closed_exFO atm lv))).
Proof.
  intros alpha1 alpha2 lv1 atm1 lv2 atm2
        H HAT1 H_1 HAT2 H_2 H1.
     exists (app 
                (rename_FOv_A_list atm2
                     (list_closed_exFO atm1 lv1) lv2)
(rename_FOv_A_list atm1
                  (rename_FOv_A atm2
                     (list_closed_exFO atm1 lv1) lv2) lv1 )).

    right.
    exists (conjSO (rename_FOv_A atm1 (rename_FOv_A atm2 (list_closed_exFO atm1 lv1) lv2)
              lv1) (rename_FOv_A atm2 (list_closed_exFO atm1 lv1) lv2)
).
    apply conj.
      pose proof (same_struc_rename_FOv_A atm2 (list_closed_exFO atm1 lv1)
         lv2) as Hsame2.
      pose proof (same_struc_rename_FOv_A atm1
         (rename_FOv_A atm2
            (list_closed_exFO atm1 lv1) lv2) lv1) as Hsame1.
      apply same_struc_comm in Hsame2.
      apply same_struc_AT in Hsame2; try assumption.
      apply same_struc_comm in Hsame1.
      apply same_struc_AT in Hsame1; try assumption.
      simpl; rewrite Hsame1; assumption.

    intros W Iv Ip Ir.
    split; intros SOt.
(*       apply (equiv_list_closed_exFO (conjSO atm1' atm2')
                                    (conjSO (conjSO rel1' atm1') (conjSO rel2' atm2'))).
        apply equiv_conjSO3.
      rewrite <- Heq1.
      rewrite <- Heq2.*)
      rewrite list_closed_exFO_app.
      apply equiv3_3_struc2_both with (alpha :=  atm1).
      simpl.
      apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.

(*       apply (equiv_list_closed_exFO (conjSO (conjSO rel1' rel2') (conjSO atm1' atm2'))
                                    (conjSO (conjSO rel1' atm1') (conjSO rel2' atm2')))
              in SOt.
      rewrite <- Heq1 in SOt.
      rewrite <- Heq2 in SOt. *)
      rewrite list_closed_exFO_app in SOt.
      apply equiv3_3_struc2_both with (alpha := atm1) in SOt.
      simpl.
      apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.
Qed.

Lemma preprocess_vsSahlq_ante_predSO : forall p f,
  conjSO_exFO_relatSO (predSO p f) = true ->
exists lv : list FOvariable,
  (exists rel : SecOrder,
     REL rel = true /\
     ((exists atm : SecOrder,
         AT atm = true /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (predSO p f) <->
          SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv))) \/
      (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
         (Ir : W -> W -> Prop),
       SOturnst W Iv Ip Ir (predSO p f) <->
       SOturnst W Iv Ip Ir (list_closed_exFO rel lv)))) \/
  (exists atm : SecOrder,
     AT atm = true /\
     (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir (predSO p f) <->
      SOturnst W Iv Ip Ir (list_closed_exFO atm lv))).
Proof.
  intros p f H.
    exists nil.
    right.
    exists (predSO p f).
    destruct p as [Pn].
    destruct f as [xn].
    simpl.
    apply conj.
      reflexivity.
      intros.
      apply iff_refl.
Qed.

Lemma preprocess_vsSahlq_ante_relatSO : forall f f0,
  conjSO_exFO_relatSO (relatSO f f0) = true ->
exists lv : list FOvariable,
  (exists rel : SecOrder,
     REL rel = true /\
     ((exists atm : SecOrder,
         AT atm = true /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (relatSO f f0) <->
          SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv))) \/
      (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
         (Ir : W -> W -> Prop),
       SOturnst W Iv Ip Ir (relatSO f f0) <->
       SOturnst W Iv Ip Ir (list_closed_exFO rel lv)))) \/
  (exists atm : SecOrder,
     AT atm = true /\
     (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir (relatSO f f0) <->
      SOturnst W Iv Ip Ir (list_closed_exFO atm lv))).
Proof.
  intros f f0 H.
    exists nil.
    left.
    exists (relatSO f f0).
    apply conj.
      reflexivity.
    right.
    intros.
    destruct f as [xn]; destruct f0 as [xm].
    simpl.
    apply iff_refl.
Qed.

Lemma preprocess_vsSahlq_ante_exFO : forall alpha f,
  conjSO_exFO_relatSO (exFO f alpha) = true ->
  (conjSO_exFO_relatSO alpha = true ->
          exists lv : list FOvariable,
            (exists rel : SecOrder,
               REL rel = true /\
               ((exists atm : SecOrder,
                   AT atm = true /\
                   (forall (W : Set) (Iv : FOvariable -> W)
                      (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop),
                    SOturnst W Iv Ip Ir alpha <->
                    SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv))) \/
                (forall (W : Set) (Iv : FOvariable -> W)
                   (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop),
                 SOturnst W Iv Ip Ir alpha <->
                 SOturnst W Iv Ip Ir (list_closed_exFO rel lv)))) \/
            (exists atm : SecOrder,
               AT atm = true /\
               (forall (W : Set) (Iv : FOvariable -> W)
                  (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop),
                SOturnst W Iv Ip Ir alpha <->
                SOturnst W Iv Ip Ir (list_closed_exFO atm lv)))) ->
exists lv : list FOvariable,
  (exists rel : SecOrder,
     REL rel = true /\
     ((exists atm : SecOrder,
         AT atm = true /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (exFO f alpha) <->
          SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv))) \/
      (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
         (Ir : W -> W -> Prop),
       SOturnst W Iv Ip Ir (exFO f alpha) <->
       SOturnst W Iv Ip Ir (list_closed_exFO rel lv)))) \/
  (exists atm : SecOrder,
     AT atm = true /\
     (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir (exFO f alpha) <->
      SOturnst W Iv Ip Ir (list_closed_exFO atm lv))).
Proof.
  intros alpha f H IHalpha.
    simpl in H.
    specialize (IHalpha H).
    destruct IHalpha as [lv [[rel [Hrel [[atm [HAT H1]] | H2]]] | [atm [HAT H2]]]].
      exists (cons f lv).
      left.
      exists rel.
      apply conj. assumption.
      left.
      exists atm.
      apply conj. assumption.
      intros W Iv Ip Ir.
      simpl list_closed_exFO.
      do 2 rewrite SOturnst_exFO.
      split; intros SOt;
        destruct SOt as [d SOt];
        exists d;
        apply H1;
        assumption.

      exists (cons f lv).
      left.
      exists rel.
      apply conj. assumption.
      right.
      intros W Iv Ip Ir.
      simpl list_closed_exFO.
      do 2 rewrite SOturnst_exFO.
      split; intros SOt;
        destruct SOt as [d SOt];
        exists d;
        apply H2; 
        assumption.

      exists (cons f lv).
      right. 
      exists atm.
      apply conj. assumption.
      intros W Iv Ip Ir.
      simpl list_closed_exFO.
      do 2 rewrite SOturnst_exFO.
      split; intros SOt;
        destruct SOt as [d SOt];
        exists d;
        apply H2;
        assumption.
Qed.

Lemma preprocess_vsSahlq_ante : forall alpha,
  conjSO_exFO_relatSO alpha = true ->
  exists lv,
    (exists rel, REL rel = true /\
      ((exists atm, AT atm = true /\
        forall W Iv Ip Ir,
          SOturnst W Iv Ip Ir alpha <->
          SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv)) \/
     (forall W Iv Ip Ir,
        SOturnst W Iv Ip Ir alpha <->
        SOturnst W Iv Ip Ir (list_closed_exFO rel lv)))) \/
    exists atm, AT atm = true /\
      forall W Iv Ip Ir,
        SOturnst W Iv Ip Ir alpha <->
        SOturnst W Iv Ip Ir (list_closed_exFO atm lv).
Proof.
  intros alpha H.
  induction alpha; try (simpl in *; discriminate).
    apply preprocess_vsSahlq_ante_predSO; assumption.
    apply preprocess_vsSahlq_ante_relatSO; assumption.
    apply preprocess_vsSahlq_ante_exFO; assumption.

    simpl in H.
    case_eq (conjSO_exFO_relatSO alpha1); intros H1;
      rewrite H1 in H; try discriminate.
    specialize (IHalpha1 H1).
    specialize (IHalpha2 H).
    destruct IHalpha1 as [lv1 [[rel1 [HREL1 [[atm1 [HAT1 H_1]] | H_1]]] | [atm1 [HAT1 H_1]]]];
    destruct IHalpha2 as [lv2 [[rel2 [HREL2 [[atm2 [HAT2 H_2]] | H_2]]] | [atm2 [HAT2 H_2]]]].

  apply (preprocess_vsSahlq_ante_1 alpha1 alpha2 lv1 rel1 atm1 lv2 rel2 atm2); assumption.
  apply (preprocess_vsSahlq_ante_2 alpha1 alpha2 lv1 rel1 atm1 lv2 rel2); assumption.
  apply (preprocess_vsSahlq_ante_3 alpha1 alpha2 lv1 rel1 atm1 lv2 atm2); assumption.
  apply (preprocess_vsSahlq_ante_4 alpha1 alpha2 lv1 rel1 lv2 rel2 atm2); assumption.
  apply (preprocess_vsSahlq_ante_5 alpha1 alpha2 lv1 rel1 lv2 rel2); assumption.
  apply (preprocess_vsSahlq_ante_6 alpha1 alpha2 lv1 rel1 lv2 atm2); assumption.
  apply (preprocess_vsSahlq_ante_7 alpha1 alpha2 lv1 atm1 lv2 rel2 atm2); assumption.
  apply (preprocess_vsSahlq_ante_8 alpha1 alpha2 lv1 atm1 lv2 rel2); assumption.
  apply (preprocess_vsSahlq_ante_9 alpha1 alpha2 lv1 atm1 lv2 atm2); assumption.
Qed.


Lemma preprocess_vsSahlq_ante2_1 : forall alpha1 alpha2 lv1 rel1 atm1 
        lv2 rel2 atm2,
  conjSO_exFO_relatSO alpha2 = true ->
  REL rel1 = true ->
  AT atm1 = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha1 <->
      SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel1 atm1) lv1)) ->
  REL rel2 = true ->
  AT atm2 = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha2 <->
      SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel2 atm2) lv2)) ->
  conjSO_exFO_relatSO alpha1 = true ->
exists lv : list FOvariable,
  (exists rel : SecOrder,
     REL rel = true /\
     ((exists atm : SecOrder,
         AT atm = true /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
          SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv))) \/
      (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
         (Ir : W -> W -> Prop),
       SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
       SOturnst W Iv Ip Ir (list_closed_exFO rel lv)))) \/
  (exists atm : SecOrder,
     AT atm = true /\
     (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
      SOturnst W Iv Ip Ir (list_closed_exFO atm lv))).
Proof.
  intros alpha1 alpha2 lv1 rel1 atm1 lv2 rel2 atm2
        H HREL1 HAT1 H_1 HREL2 HAT2 H_2 H1.
pose proof (same_struc_conjSO_ex2 _ _ _ (same_struc_rename_FOv_A (conjSO rel1 atm1) 
                                            (rename_FOv_A (conjSO rel2 atm2) 
                                               (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1)) as Heq1.

pose proof (same_struc_conjSO_ex2 _ _ _ (same_struc_rename_FOv_A(conjSO rel2 atm2) 
                                            (list_closed_exFO (conjSO rel1 atm1) lv1) lv2)) as Heq2.
     exists (app 
                (rename_FOv_A_list (conjSO rel2 atm2) 
                     (list_closed_exFO (conjSO rel1 atm1) lv1) lv2)
(rename_FOv_A_list (conjSO rel1 atm1) 
                  (rename_FOv_A (conjSO rel2 atm2)
                     (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1 )).

    left.
    exists (conjSO (fun_return_conj_l
          (rename_FOv_A (conjSO rel1 atm1)
             (rename_FOv_A (conjSO rel2 atm2)
                (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1)) (fun_return_conj_l
            (rename_FOv_A (conjSO rel2 atm2)
               (list_closed_exFO (conjSO rel1 atm1) lv1) lv2))).
    apply conj.
      pose proof (same_struc_rename_FOv_A (conjSO rel2 atm2) (list_closed_exFO (conjSO rel1 atm1) lv1)
         lv2) as Hsame2.
      pose proof (same_struc_rename_FOv_A (conjSO rel1 atm1)
         (rename_FOv_A (conjSO rel2 atm2)
            (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1) as Hsame1.
      rewrite Heq2 in Hsame2.
      rewrite Heq1 in Hsame1.
      apply same_struc_conjSO_l in Hsame2.
      apply same_struc_comm in Hsame2.
      apply same_struc_REL in Hsame2; try assumption.
      apply same_struc_conjSO_l in Hsame1.
      apply same_struc_comm in Hsame1.
      apply same_struc_REL in Hsame1; try assumption.
      simpl; rewrite Hsame1; assumption.

    left.
    exists (conjSO       (fun_return_conj_r
          (rename_FOv_A (conjSO rel1 atm1)
             (rename_FOv_A (conjSO rel2 atm2)
                (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1)) (fun_return_conj_r
            (rename_FOv_A (conjSO rel2 atm2)
               (list_closed_exFO (conjSO rel1 atm1) lv1) lv2))).
    apply conj.
      pose proof (same_struc_rename_FOv_A (conjSO rel2 atm2) (list_closed_exFO (conjSO rel1 atm1) lv1)
         lv2) as Hsame2.
      pose proof (same_struc_rename_FOv_A (conjSO rel1 atm1)
         (rename_FOv_A (conjSO rel2 atm2)
            (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1) as Hsame1.
      rewrite Heq2 in Hsame2.
      rewrite Heq1 in Hsame1.
      apply same_struc_conjSO_r in Hsame2.
      apply same_struc_comm in Hsame2.
      apply same_struc_AT in Hsame2; try assumption.
      apply same_struc_conjSO_r in Hsame1.
      apply same_struc_comm in Hsame1.
      apply same_struc_AT in Hsame1; try assumption.
      simpl; rewrite Hsame1; assumption.

    intros W Iv Ip Ir.
    split; intros SOt.
      apply (equiv_list_closed_exFO (conjSO (conjSO (fun_return_conj_l
          (rename_FOv_A (conjSO rel1 atm1)
             (rename_FOv_A (conjSO rel2 atm2)
                (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1)) (fun_return_conj_l
            (rename_FOv_A (conjSO rel2 atm2)
               (list_closed_exFO (conjSO rel1 atm1) lv1) lv2))) (conjSO       (fun_return_conj_r
          (rename_FOv_A (conjSO rel1 atm1)
             (rename_FOv_A (conjSO rel2 atm2)
                (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1)) (fun_return_conj_r
            (rename_FOv_A (conjSO rel2 atm2)
               (list_closed_exFO (conjSO rel1 atm1) lv1) lv2))))
                                    (conjSO (conjSO (fun_return_conj_l
          (rename_FOv_A (conjSO rel1 atm1)
             (rename_FOv_A (conjSO rel2 atm2)
                (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1))       (fun_return_conj_r
          (rename_FOv_A (conjSO rel1 atm1)
             (rename_FOv_A (conjSO rel2 atm2)
                (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1))) (conjSO (fun_return_conj_l
            (rename_FOv_A (conjSO rel2 atm2)
               (list_closed_exFO (conjSO rel1 atm1) lv1) lv2)) (fun_return_conj_r
            (rename_FOv_A (conjSO rel2 atm2)
               (list_closed_exFO (conjSO rel1 atm1) lv1) lv2))))).
        apply equiv_conjSO3.
      rewrite <- Heq1.
      rewrite <- Heq2.
      rewrite list_closed_exFO_app.
      apply equiv3_3_struc2_both with (alpha := (conjSO rel1 atm1)).
      simpl.
      apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.

      apply (equiv_list_closed_exFO (conjSO (conjSO (fun_return_conj_l
          (rename_FOv_A (conjSO rel1 atm1)
             (rename_FOv_A (conjSO rel2 atm2)
                (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1)) (fun_return_conj_l
            (rename_FOv_A (conjSO rel2 atm2)
               (list_closed_exFO (conjSO rel1 atm1) lv1) lv2))) (conjSO       (fun_return_conj_r
          (rename_FOv_A (conjSO rel1 atm1)
             (rename_FOv_A (conjSO rel2 atm2)
                (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1)) (fun_return_conj_r
            (rename_FOv_A (conjSO rel2 atm2)
               (list_closed_exFO (conjSO rel1 atm1) lv1) lv2))))
                                    (conjSO (conjSO (fun_return_conj_l
          (rename_FOv_A (conjSO rel1 atm1)
             (rename_FOv_A (conjSO rel2 atm2)
                (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1))       (fun_return_conj_r
          (rename_FOv_A (conjSO rel1 atm1)
             (rename_FOv_A (conjSO rel2 atm2)
                (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1))) (conjSO (fun_return_conj_l
            (rename_FOv_A (conjSO rel2 atm2)
               (list_closed_exFO (conjSO rel1 atm1) lv1) lv2)) (fun_return_conj_r
            (rename_FOv_A (conjSO rel2 atm2)
               (list_closed_exFO (conjSO rel1 atm1) lv1) lv2)))))
              in SOt.
      rewrite <- Heq1 in SOt.
      rewrite <- Heq2 in SOt.
      rewrite list_closed_exFO_app in SOt.
      apply equiv3_3_struc2_both with (alpha := (conjSO rel1 atm1)) in SOt.
      simpl.
      apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.

        apply equiv_conjSO3.
Qed.
