Require Import SecOrder.
Require Import P_occurs_in_alpha.
Require Import ST_setup.
Require Import Correctness_ST.
Require Import Arith.EqNat my_bool.
Require Import List_machinery_impl My_List_Map.
Require Import Unary_Predless nList_egs Rep_Pred_FOv Indicies Identify.
Require Import pos_SO2 neg_SO2 Num_Occ Bool my_bool Is_Pos_Rep_Pred P_occ_rep_pred.
Require Import Uniform_Defns Monotonicity_SO Pre_Sahlqvist_Uniform_Pos P_occ_rep_pred.
Require Import Unary_Predless_l Num_Occ_l2 Occ_In_Alpha My_Prop Sahlqvist_Uniform_Pos.
Require Import vsSahlq_preprocessing1 vsSahlq_preprocessing2 vsSahlq_preprocessing3.
Require Import vsSahlq_instant3 vsSahlq_instant9 vsSahlq_instant_pre_to_be_sorted.
Require Import vsSahlq_instant10 vsSahlq_instant13 vsSahlq_instant15 vsSahlq_instant16 vsSahlq_instant17.
Require Import vsSahlq_instant19.
Require Import p_occurs_in occ_in_phi my_arith__my_leb_nat.

(* sSahlq3_3 but with added and changed things to incorporate instantiation function. *)

(* Modal :  boxed atom *)
Fixpoint bxatm (phi : Modal) : bool :=
  match phi with
  | atom p => true
  | box psi => bxatm psi
  | _ => false
  end.

(* Modal : conjunction of boxed atoms *)
Fixpoint is_bxatm_conj (phi : Modal) : bool :=
  match phi with
  | mconj psi1 psi2 => if is_bxatm_conj psi1 then is_bxatm_conj psi2 else false
  | _ => if bxatm phi then true else false
  end.

Fixpoint sSahlq_ante (phi : Modal) : bool :=
  match phi with
  | atom p => true
  | mneg psi => false
  | mconj psi1 psi2 => if sSahlq_ante psi1 then sSahlq_ante psi2 else false
  | mdisj _ _ => false
  | mimpl _ _ => false
  | box psi => bxatm psi
  | diam psi => sSahlq_ante psi 
  end.

(* ----- *)

(* SecOrder : object boxed atom *)
Fixpoint BOXATM2 (P : predicate) 
    x (lx : list FOvariable) : SecOrder :=
  match lx with
  | nil => predSO P x
  | cons y lx' => allFO y (implSO (relatSO x y) (BOXATM2 P y lx'))
  end.

(* SecOrder : boxed atom *)
(* naming of variables increments by 1 *)
Fixpoint BOXATM_flag_strong (alpha : SecOrder) (x : FOvariable) : bool :=
  match alpha with
    predSO P y => match x, y with Var xn, Var ym => 
      beq_nat xn ym end
  | allFO y (implSO (relatSO z1 z2) beta) =>
    match x, y, z1, z2 with
    | Var xn, Var ym, Var n1, Var n2 =>
      if beq_nat xn n1 then if beq_nat ym n2 then 
        if beq_nat n2 (S n1) then BOXATM_flag_strong beta y
        else false else false else false
    end
  | _ => false
  end.

(* Just like BOXATM_flag_strong but without extra suc condition. *)
Fixpoint BOXATM_flag_weak (alpha : SecOrder) (x : FOvariable) : bool :=
  match alpha with
    predSO P y => match x, y with Var xn, Var ym => 
      beq_nat xn ym end
  | allFO y (implSO (relatSO z1 z2) beta) =>
    match x, y, z1, z2 with
    | Var xn, Var ym, Var n1, Var n2 =>
      if beq_nat xn n1 then if beq_nat ym n2 then 
          BOXATM_flag_weak beta y
        else false else false
    end
  | _ => false
  end.

Definition batm_comp_x1 (batm : SecOrder) : FOvariable :=
  match batm with
  | predSO P x => x
  | allFO x (implSO (relatSO y1 y2) beta) => y1
  | _ => Var 0
  end.



(* SecOrder : conjunction of boxed atoms *)
Fixpoint is_BOXATM_flag_strong_CONJ (alpha : SecOrder) : bool :=
  match alpha with  
  | predSO _ _ => true
  |conjSO alpha1 alpha2 => if is_BOXATM_flag_strong_CONJ alpha1 then
    is_BOXATM_flag_strong_CONJ alpha2 else false
  | allFO y beta => match y with Var ym =>
      match ym with
      | 0 => false
      | S n =>  BOXATM_flag_strong alpha (Var n)
      end end
  | _ => false
  end.

(* Just like is_BOXATM_flag_strong_CONJ but without extra suc condition. *)
Fixpoint BAT (alpha : SecOrder) : bool :=
  match alpha with  
  | predSO _ _ => true
  |conjSO alpha1 alpha2 => if BAT alpha1 then
    BAT alpha2 else false
  | allFO _ _ => BOXATM_flag_weak alpha (batm_comp_x1 alpha)
  | _ => false
  end.

Fixpoint BOXATM2_lP (lP : list predicate) 
    (lx : list FOvariable) (llv : list (list FOvariable)) : SecOrder :=
  match lP, lx, llv with
  | nil, _, _ => eqFO (Var 1) (Var 1)
  | _, nil, _ => eqFO (Var 1) (Var 1)
  | _, _, nil => eqFO (Var 1) (Var 1) 
  | cons P nil, cons x _, cons lv _ => BOXATM2 P x lv
  | cons P _, cons x nil, cons lv _ => BOXATM2 P x lv
  | cons P _, cons x _, cons lv nil => BOXATM2 P x lv
  | cons P lP', cons x lx', cons lv llv' => 
    conjSO (BOXATM2 P x lv) (BOXATM2_lP lP' lx' llv')
  end.

(* ---------- *)

Fixpoint rel_conj (x : FOvariable) (lx : list FOvariable) :=
  match lx with
  | nil => eqFO x x
  | cons y nil => relatSO x y
  | cons y lx' => conjSO (relatSO x y) (rel_conj y lx')
  end.

Fixpoint rel_conj2 (x y : FOvariable) (lx : list FOvariable) :=
  match lx with
  | nil => relatSO x y
(*   | cons y nil => relatSO x y *)
  | cons z lx' => conjSO (relatSO x z) (rel_conj2 z y lx')
  end.

Definition fun3_pre (x1 xn : FOvariable) (lx : list FOvariable) :=
match lx with
| nil => eqFO (Var 1) (Var 1)
| _ =>
  (list_closed_exFO (rel_conj x1 lx) lx)
end.

Definition fun3 (P : predicate) (x1 xn : FOvariable) (lx : list FOvariable) :=
match lx with
| nil => predSO P xn
| _ =>
  allFO xn (implSO (list_closed_exFO (rel_conj x1 lx) lx) (predSO P xn))
end.

Definition fun3' (P : predicate) (x1 xn : FOvariable) (lx : list FOvariable) :=
match lx with
| nil => predSO P xn
| _ =>
  allFO xn (implSO (fun3_pre x1 xn lx) (predSO P xn))
end.

(* Fixpoint fun5 P x1 xn lx :=
  match lx with 
  | nil => predSO P xn
  | cons x lx' => allFO x (implSO (relatSO x1 x) (fun5 P x xn lx'))
  end. *)

Fixpoint fun5'' P x1 lx :=
  match lx with 
  | nil => predSO P x1
  | cons x lx' => allFO x (implSO (relatSO x1 x) (fun5'' P x  lx'))
  end.

Definition next_FOvar (x : FOvariable) :=
  match x with  Var xn => Var (S xn) end.

(* Fixpoint fun5' P x1 n :=
  match n with 
  | 0 => predSO P x1
  | S m => allFO (next_FOvar x1) (implSO (relatSO x1 (next_FOvar x1)) (fun5' P (next_FOvar x1) m))
  end.
 *)
(* Fixpoint fun5_l lP lx1 lxn llx :=
  match lP, lx1, lxn, llx with
  | nil, _ , _, _ => eqFO (Var 1) (Var 1)
  | _, nil, _, _ => eqFO (Var 1) (Var 1)
  | _, _, nil, _ => eqFO (Var 1) (Var 1)
  |_, _, _, nil => eqFO (Var 1) (Var 1)
  |cons P nil, cons x1 _, cons xn _, cons lx _ => fun5 P x1 xn lx
  |cons P _, cons x1 nil, cons xn _, cons lx _ => fun5 P x1 xn lx
  |cons P _, cons x1 _, cons xn nil, cons lx _ => fun5 P x1 xn lx
  |cons P _, cons x1 _, cons xn _, cons lx nil => fun5 P x1 xn lx
  |cons P lP', cons x1 lx1', cons xn lxn', cons lx llx' => 
    conjSO (fun5 P x1 xn lx) (fun5_l lP' lx1' lxn' llx')
  end. *)

Fixpoint fun5_l'' lP lx1 llx :=
  match lP, lx1, llx with
  | nil, _ , _ => eqFO (Var 1) (Var 1)
  | _, nil, _ => eqFO (Var 1) (Var 1)
  |_, _, nil => eqFO (Var 1) (Var 1)
  |cons P nil, cons x1 _, cons lx _ => fun5'' P x1 lx
  |cons P _, cons x1 nil, cons lx _ => fun5'' P x1 lx
  |cons P _, cons x1 _, cons lx nil => fun5'' P x1 lx
  |cons P lP', cons x1 lx1',  cons lx llx' => 
    conjSO (fun5'' P x1 lx) (fun5_l'' lP' lx1' llx')
  end.

(* 
Fixpoint fun5_l' lP lx1 ln :=
  match lP, lx1, ln with
  | nil, _ , _ => eqFO (Var 1) (Var 1)
  | _, nil, _ => eqFO (Var 1) (Var 1)
  | _, _, nil => eqFO (Var 1) (Var 1)
  |cons P nil, cons x1 _, cons xn _ => fun5' P x1 xn
  |cons P _, cons x1 nil, cons xn _ => fun5' P x1 xn
  |cons P _, cons x1 _, cons xn nil=> fun5' P x1 xn
  |cons P lP', cons x1 lx1', cons xn lxn' => 
    conjSO (fun5' P x1 xn) (fun5_l' lP' lx1' lxn')
  end. *)

Definition fun4 (x1 xn : FOvariable) (lx : list FOvariable) :=
  (list_closed_exFO (rel_conj2 x1 xn lx) lx).

Fixpoint fun4' (x1 xn : FOvariable) (lx : list FOvariable) :=
  match lx with
  | nil => relatSO x1 xn
  | cons y lx' => exFO y (conjSO (relatSO x1 y) (fun4' y xn lx'))
  end.



Fixpoint batm_comp_xn (batm : SecOrder) : FOvariable :=
  match batm with
  | predSO P x => x
  | allFO x (implSO (relatSO y1 y2) beta) => batm_comp_xn beta
  | _ => Var 1
  end.

Fixpoint batm_comp_lx (batm : SecOrder) : list FOvariable :=
  match batm with
  | predSO P x => nil
  | allFO x (implSO _ beta) => cons x (batm_comp_lx beta)
  | _ => nil
  end.

Fixpoint batm_comp_ln (batm : SecOrder) : nat :=
  match batm with
  | predSO P x => 0
  | allFO x (implSO _ beta) => S (batm_comp_ln beta) 
  | _ => 0
  end.

Fixpoint batm_comp_P (batm : SecOrder) : predicate :=
  match batm with
  | predSO P x => P
  | allFO x (implSO _ beta) => (batm_comp_P beta)
  | _ => Pred 1
  end.

Fixpoint batm_conj_comp_x1 (batm : SecOrder) : list FOvariable :=
  match batm with
  |conjSO batm1 batm2 => app (batm_conj_comp_x1 batm1) (batm_conj_comp_x1 batm2)
  | _ => cons (batm_comp_x1 batm) nil
  end.

Fixpoint batm_conj_comp_xn (batm : SecOrder) : list FOvariable :=
  match batm with
  |conjSO batm1 batm2 => app (batm_conj_comp_xn batm1) (batm_conj_comp_xn batm2)
  | _ => cons (batm_comp_xn batm) nil
  end.

Fixpoint batm_conj_comp_lx (batm : SecOrder) : list (list FOvariable) :=
  match batm with
  |conjSO batm1 batm2 => app (batm_conj_comp_lx batm1) (batm_conj_comp_lx batm2)
  | _ => cons (batm_comp_lx batm) nil
  end.

Fixpoint batm_conj_comp_ln (batm : SecOrder) : (list nat) :=
  match batm with
  |conjSO batm1 batm2 => app (batm_conj_comp_ln batm1) (batm_conj_comp_ln batm2)
  | _ => cons (batm_comp_ln batm) nil
  end.

Fixpoint batm_conj_comp_P (batm : SecOrder) : list predicate :=
  match batm with
  |conjSO batm1 batm2 => app (batm_conj_comp_P batm1) (batm_conj_comp_P batm2)
  | _ => cons (batm_comp_P batm) nil
  end.




Fixpoint num_conn alpha : nat :=
  match alpha with
    predSO _ _ => 0
  | relatSO _ _ => 0 
  | eqFO _ _ => 0
  | allFO _ beta => S (num_conn beta)
  | exFO _ beta => S (num_conn beta)
  | negSO beta => S (num_conn beta)
  | conjSO beta1 beta2 => S( (num_conn beta1) + (num_conn beta2))
  | disjSO beta1 beta2 => S( (num_conn beta1) + (num_conn beta2))
  | implSO beta1 beta2 => S ((num_conn beta1) + (num_conn beta2))
  | allSO P beta => S (num_conn beta)
  | exSO P beta => S (num_conn beta)
  end.

Lemma try2 : forall m n batm2 x,
  n = num_conn batm2 ->
  Nat.leb n m = true ->
  BOXATM_flag_strong batm2 x = true ->
  batm_comp_x1 batm2 = x.
Proof.
  induction m; intros n batm2 x Hnum Hleb Hbox; try discriminate.
    destruct n. 2 : discriminate. destruct batm2; try discriminate.
    simpl in *. destruct x as [xn]. destruct f as [ym].
    rewrite (beq_nat_true _ _ Hbox). reflexivity.

    destruct n. destruct batm2; try discriminate.
    simpl in *. destruct x as [xn]. destruct f as [ym].
    rewrite (beq_nat_true _ _ Hbox). reflexivity.

    destruct batm2; try discriminate. destruct batm2; try discriminate.
    destruct batm2_1; try discriminate.
    simpl. destruct f as [x1]. destruct f0 as [x2]. destruct f1 as [x3].
    simpl in *. destruct x as [xn]. case_eq (beq_nat xn x2);
      intros Hbeq; rewrite Hbeq in *. 2 :discriminate.
    case_eq (beq_nat x1 x3); intros Hbeq2; rewrite Hbeq2 in *.
      2 : discriminate.
    case_eq (beq_nat x3 (S x2)); intros Hbeq3; rewrite Hbeq3 in *.
      2 : discriminate.
    inversion Hnum as [Hnum']. destruct n. discriminate.
    rewrite (beq_nat_true _ _ Hbeq). reflexivity.
Qed.

Lemma try2_BAT : forall m n batm2 x,
  n = num_conn batm2 ->
  Nat.leb n m = true ->
  BOXATM_flag_weak batm2 x = true ->
  batm_comp_x1 batm2 = x.
Proof.
  induction m; intros n batm2 x Hnum Hleb Hbox; try discriminate.
    destruct n. 2 : discriminate. destruct batm2; try discriminate.
    simpl in *. destruct x as [xn]. destruct f as [ym].
    rewrite (beq_nat_true _ _ Hbox). reflexivity.

    destruct n. destruct batm2; try discriminate.
    simpl in *. destruct x as [xn]. destruct f as [ym].
    rewrite (beq_nat_true _ _ Hbox). reflexivity.

    destruct batm2; try discriminate. destruct batm2; try discriminate.
    destruct batm2_1; try discriminate.
    simpl. destruct f as [x1]. destruct f0 as [x2]. destruct f1 as [x3].
    simpl in *. destruct x as [xn]. case_eq (beq_nat xn x2);
      intros Hbeq; rewrite Hbeq in *. 2 :discriminate.
    case_eq (beq_nat x1 x3); intros Hbeq2; rewrite Hbeq2 in *.
      2 : discriminate.
(*     case_eq (beq_nat x3 (S x2)); intros Hbeq3; rewrite Hbeq3 in *.
      2 : discriminate. *)
    inversion Hnum as [Hnum']. destruct n. discriminate.
    rewrite (beq_nat_true _ _ Hbeq). reflexivity.
Qed.

Lemma try3 : forall batm2 x,
  BOXATM_flag_strong batm2 x = true ->
  batm_comp_x1 batm2 = x.
Proof.
  intros batm2 x. apply (try2 (num_conn batm2) (num_conn batm2)).
  reflexivity. apply leb_refl.
Qed.

Lemma try3_BAT : forall batm2 x,
  BOXATM_flag_weak batm2 x = true ->
  batm_comp_x1 batm2 = x.
Proof.
  intros batm2 x. apply (try2_BAT (num_conn batm2) (num_conn batm2)).
  reflexivity. apply leb_refl.
Qed.

Lemma length_batm_conj_comp_P_x1 : forall batm,
  is_BOXATM_flag_strong_CONJ batm = true ->
  length (batm_conj_comp_P batm) =
  length (batm_conj_comp_x1 batm).
Proof.
  induction batm; intros H; try discriminate; try reflexivity.
  simpl in *. case_eq (is_BOXATM_flag_strong_CONJ batm1);
    intros H1; rewrite H1 in *. 2 : discriminate.
  case_eq (is_BOXATM_flag_strong_CONJ batm1); intros H2;
    rewrite H2 in *. 2 : discriminate.
  do 2 rewrite List.app_length.
  rewrite IHbatm1. rewrite IHbatm2.
  reflexivity. assumption. reflexivity.
Qed.

Lemma length_batm_conj_comp_P_x1_BAT : forall batm,
  BAT batm = true ->
  length (batm_conj_comp_P batm) =
  length (batm_conj_comp_x1 batm).
Proof.
  induction batm; intros H; try discriminate; try reflexivity.
  simpl in *. case_eq (BAT batm1);
    intros H1; rewrite H1 in *. 2 : discriminate.
  case_eq (BAT batm1); intros H2;
    rewrite H2 in *. 2 : discriminate.
  do 2 rewrite List.app_length.
  rewrite IHbatm1. rewrite IHbatm2.
  reflexivity. assumption. reflexivity.
Qed.

Lemma length_batm_conj_comp_P_xn : forall batm,
  is_BOXATM_flag_strong_CONJ batm = true ->
  length (batm_conj_comp_P batm) =
  length (batm_conj_comp_xn batm).
Proof.
  induction batm; intros H; try discriminate; try reflexivity.
  simpl in *. case_eq (is_BOXATM_flag_strong_CONJ batm1);
    intros H1; rewrite H1 in *. 2 : discriminate.
  case_eq (is_BOXATM_flag_strong_CONJ batm1); intros H2;
    rewrite H2 in *. 2 : discriminate.
  do 2 rewrite List.app_length.
  rewrite IHbatm1. rewrite IHbatm2.
  reflexivity. assumption. reflexivity.
Qed.

Lemma length_batm_conj_comp_P_xn_BAT : forall batm,
  BAT batm = true ->
  length (batm_conj_comp_P batm) =
  length (batm_conj_comp_xn batm).
Proof.
  induction batm; intros H; try discriminate; try reflexivity.
  simpl in *. case_eq (BAT batm1);
    intros H1; rewrite H1 in *. 2 : discriminate.
  case_eq (BAT batm1); intros H2;
    rewrite H2 in *. 2 : discriminate.
  do 2 rewrite List.app_length.
  rewrite IHbatm1. rewrite IHbatm2.
  reflexivity. assumption. reflexivity.
Qed.

Lemma length_batm_conj_comp_P_lx : forall batm,
  is_BOXATM_flag_strong_CONJ batm = true ->
  length (batm_conj_comp_P batm) =
  length (batm_conj_comp_lx batm).
Proof.
  induction batm; intros H; try discriminate; try reflexivity.
  simpl in *. case_eq (is_BOXATM_flag_strong_CONJ batm1);
    intros H1; rewrite H1 in *. 2 : discriminate.
  case_eq (is_BOXATM_flag_strong_CONJ batm1); intros H2;
    rewrite H2 in *. 2 : discriminate.
  do 2 rewrite List.app_length.
  rewrite IHbatm1. rewrite IHbatm2.
  reflexivity. assumption. reflexivity.
Qed.

Lemma length_batm_conj_comp_P_lx_BAT : forall batm,
  BAT batm = true ->
  length (batm_conj_comp_P batm) =
  length (batm_conj_comp_lx batm).
Proof.
  induction batm; intros H; try discriminate; try reflexivity.
  simpl in *. case_eq (BAT batm1);
    intros H1; rewrite H1 in *. 2 : discriminate.
  case_eq (BAT batm1); intros H2;
    rewrite H2 in *. 2 : discriminate.
  do 2 rewrite List.app_length.
  rewrite IHbatm1. rewrite IHbatm2.
  reflexivity. assumption. reflexivity.
Qed.

Lemma is_BOXATM_flag_strong_CONJ_conjSO_l : forall batm1 batm2,
  is_BOXATM_flag_strong_CONJ (conjSO batm1 batm2) = true ->
  is_BOXATM_flag_strong_CONJ batm1 = true.
Proof.
  intros batm1 batm2 H.
  simpl in H. 
  case_eq (is_BOXATM_flag_strong_CONJ batm1); intros H2;
    rewrite H2 in *. reflexivity. discriminate.
Qed.

Lemma BAT_conjSO_l : forall batm1 batm2,
  BAT (conjSO batm1 batm2) = true ->
  BAT batm1 = true.
Proof.
  intros batm1 batm2 H.
  simpl in H. 
  case_eq (BAT batm1); intros H2;
    rewrite H2 in *. reflexivity. discriminate.
Qed.

Lemma BAT_conjSO_r : forall batm1 batm2,
  BAT (conjSO batm1 batm2) = true ->
  BAT batm2 = true.
Proof.
  intros batm1 batm2 H.
  simpl in H. 
  case_eq (BAT batm1); intros H2;
    rewrite H2 in *. assumption. discriminate.
Qed.

Lemma is_BOXATM_flag_strong_CONJ_conjSO_r : forall batm1 batm2,
  is_BOXATM_flag_strong_CONJ (conjSO batm1 batm2) = true ->
  is_BOXATM_flag_strong_CONJ batm2 = true.
Proof.
  intros batm1 batm2 H.
  simpl in H. 
  case_eq (is_BOXATM_flag_strong_CONJ batm1); intros H2;
    rewrite H2 in *. assumption. discriminate.
Qed.

Lemma try7 : forall beta n,
BOXATM_flag_strong beta (Var (S n)) = true ->
(batm_comp_x1 beta) = Var (S n).
Proof.
  induction beta; intros n H; try discriminate.
    destruct p. destruct f as [m]. destruct m. discriminate.
    simpl in *. rewrite (beq_nat_true _ _ H). reflexivity.

    simpl in *. destruct beta; try discriminate.
    destruct beta1; try discriminate. destruct f as [n1].
    destruct f0 as [n2]. destruct f1 as [n3].
    destruct n2. discriminate.
    case_eq (beq_nat n n2); intros Hbeq; rewrite Hbeq in *.
      rewrite (beq_nat_true _ _ Hbeq). reflexivity. discriminate.
Qed.

Lemma try7_BAT : forall beta n,
BOXATM_flag_weak beta (Var (S n)) = true ->
(batm_comp_x1 beta) = Var (S n).
Proof.
  induction beta; intros n H; try discriminate.
    destruct p. destruct f as [m]. destruct m. discriminate.
    simpl in *. rewrite (beq_nat_true _ _ H). reflexivity.

(*     simpl in *. rewrite (beq_nat_true _ _ H). reflexivity. *)

    destruct beta; try discriminate.
    destruct beta1; try discriminate. destruct f as [n1].
    destruct f0 as [n2]. destruct f1 as [n3].
    destruct n2. discriminate. simpl in *.
    case_eq (beq_nat n n2); intros Hbeq; rewrite Hbeq in *.
      rewrite (beq_nat_true _ _ Hbeq). reflexivity. discriminate.
Qed.

Lemma try6 : forall beta x y1 y2,
is_BOXATM_flag_strong_CONJ (allFO x (implSO (relatSO y1 y2) beta)) = true ->
next_FOvar (batm_comp_x1 (allFO x (implSO (relatSO y1 y2) beta))) =
(batm_comp_x1 beta).
Proof.
  intros beta [x1] [x2] [x3] H.
  simpl in *. destruct x1. discriminate.
  case_eq (beq_nat x1 x2); intros Hbeq; rewrite Hbeq in *. 2: discriminate.
  case_eq (beq_nat (S x1) x3); intros Hbeq2; rewrite Hbeq2 in *. 2: discriminate.
  case_eq (beq_nat x3 (S x2)); intros Hbeq3; rewrite Hbeq3 in *. 2: discriminate.
  rewrite try7 with (n := x1).
  rewrite (beq_nat_true _ _ Hbeq). reflexivity. assumption.
Qed.

(* Lemma try6_BAT : forall beta x y1 y2,
BAT (allFO x (implSO (relatSO y1 y2) beta)) = true ->
next_FOvar (batm_comp_x1 (allFO x (implSO (relatSO y1 y2) beta))) =
(batm_comp_x1 beta).
Proof.
  intros beta [x1] [x2] [x3] H.
  simpl in *. (* destruct x1. discriminate. *)
  rewrite <- beq_nat_refl in H.
  case_eq (beq_nat x1 x3); intros Hbeq; rewrite Hbeq in *.
   2: discriminate.
(*   case_eq (beq_nat (S x1) x3); intros Hbeq2; rewrite Hbeq2 in *. 2: discriminate.
  case_eq (beq_nat x3 (S x2)); intros Hbeq3; rewrite Hbeq3 in *. 2: discriminate. *)
  rewrite try7_BAT with (n := x1).
  rewrite (beq_nat_true _ _ Hbeq). reflexivity. assumption.
Qed. *)

(* Lemma try6_BAT : forall beta x y1 y2,
BAT (allFO x (implSO (relatSO y1 y2) beta)) = true ->
next_FOvar (batm_comp_x1 (allFO x (implSO (relatSO y1 y2) beta))) =
(batm_comp_x1 beta).
Proof.
  intros beta [x1] [x2] [x3] H.
  simpl in *. rewrite <- beq_nat_refl in H.
  case_eq (beq_nat x1 x3); intros Hbeq; rewrite Hbeq in *. 2: discriminate.
(*   case_eq (beq_nat (S x1) x3); intros Hbeq2; rewrite Hbeq2 in *. 2: discriminate. *)
(*   case_eq (beq_nat x3 (S x2)); intros Hbeq3; rewrite Hbeq3 in *. 2: discriminate. *)
  rewrite try7_BAT with (n := x1).
  rewrite (beq_nat_true _ _ Hbeq). reflexivity. assumption.
Qed. *)

Lemma length_batm_conj_comp_P_ln: forall batm,
is_BOXATM_flag_strong_CONJ batm = true ->
length (batm_conj_comp_P batm) = length (batm_conj_comp_ln batm).
Proof.
  induction batm; intros H; try discriminate. reflexivity. reflexivity.
  simpl. do 2 rewrite List.app_length.
  simpl in H. case_eq (is_BOXATM_flag_strong_CONJ batm1);
    intros H1; rewrite H1 in H. 2: discriminate.
  rewrite IHbatm1. rewrite IHbatm2. reflexivity.
  all : assumption.
Qed.

Lemma length_batm_conj_comp_P_ln_BAT : forall batm,
BAT batm = true ->
length (batm_conj_comp_P batm) = length (batm_conj_comp_ln batm).
Proof.
  induction batm; intros H; try discriminate. reflexivity. reflexivity.
  simpl. do 2 rewrite List.app_length.
  simpl in H. case_eq (BAT batm1);
    intros H1; rewrite H1 in H. 2: discriminate.
  rewrite IHbatm1. rewrite IHbatm2. reflexivity.
  all : assumption.
Qed.

Lemma leb_plus_take1 : forall a b c,
  Nat.leb (a + b) c = true ->
  Nat.leb a c = true.
Proof.
  induction a; intros b c H.
    reflexivity.
  simpl in *. destruct c. discriminate.
  apply IHa in H. assumption.
Qed.

Lemma leb_plus_take2 : forall a b c,
  Nat.leb (a + b) c = true ->
  Nat.leb b c = true.
Proof.
  intros a b c H.
  rewrite PeanoNat.Nat.add_comm in H.
  apply leb_plus_take1 in H. assumption.
Qed.

Fixpoint fun3_l (P :predicate) (lx1 lxn : list FOvariable) (llx : list (list FOvariable)) :=
  match lx1, lxn, llx with
  | nil , _, _ => eqFO (Var 1) (Var 1)
  | _ , nil, _ => eqFO (Var 1) (Var 1)
  | _ , _, nil => eqFO (Var 1) (Var 1)
  | cons x1 nil, cons xn _, cons lx _ => fun3 P x1 xn lx
  | cons x1 _, cons xn nil, cons lx _ => fun3 P x1 xn lx
  | cons x1 _, cons xn _, cons lx nil => fun3 P x1 xn lx
  | cons x1 lx1', cons xn lxn', cons lx llx' => 
    conjSO (fun3 P x1 xn lx) (fun3_l P lx1' lxn' llx')
  end.

Fixpoint fun4_l2 (lx1 lxn : list FOvariable) (llx : list (list FOvariable)) :=
  match lx1, lxn, llx with
  | nil , _, _ => eqFO (Var 1) (Var 1)
  | _ , nil, _  => eqFO (Var 1) (Var 1)
  | _, _, nil => eqFO (Var 1) (Var 1)
  | cons x1 nil, cons xn _, cons lx _ => fun4' x1 xn lx
  | cons x1 _, cons xn nil, cons lx _ => fun4' x1 xn lx
  | cons x1 _, cons xn _, cons lx nil => fun4' x1 xn lx
  | cons x1 lx1', cons xn lxn', cons lx llx' => 
    disjSO (fun4' x1 xn lx) (fun4_l2 lx1' lxn' llx')
  end.

Fixpoint fun4_l2' (lx1 : list FOvariable) (xn : FOvariable) (llx : list (list FOvariable)) :=
  match lx1, llx with
  | nil, _ => eqFO (Var 1) (Var 1)
  | _, nil => eqFO (Var 1) (Var 1)
  | cons x1 nil, cons lx _ => fun4' x1 xn lx
  | cons x1 _, cons lx nil => fun4' x1 xn lx
  | cons x1 lx1', cons lx llx' => 
    disjSO (fun4' x1 xn lx) (fun4_l2' lx1' xn llx')
  end.

Fixpoint fun4_l2_lP' (llx1 : list (list FOvariable)) (lxn : list FOvariable) (lllx : list (list (list FOvariable))) :=
  match llx1, lxn, lllx with
  | nil , _, _ => nil
  | _ , nil, _  => nil
  | _, _, nil => nil
  | cons x1 lx1', cons xn lxn', cons lx llx' => 
    cons (fun4_l2' x1 xn lx) (fun4_l2_lP' lx1' lxn' llx')
  end.

Fixpoint fun4_l2_lP (llx1 llxn : list (list FOvariable)) (lllx : list (list (list FOvariable))) :=
  match llx1, llxn, lllx with
  | nil , _, _ => nil
  | _ , nil, _  => nil
  | _, _, nil => nil
  | cons x1 lx1', cons xn lxn', cons lx llx' => 
    cons (fun4_l2 x1 xn lx) (fun4_l2_lP lx1' lxn' llx')
  end.

Fixpoint fun3_l_lP (lP : list predicate) (llx1 llxn: list (list FOvariable))
    (lllx : list (list (list FOvariable))) :=
  match lP, llx1, llxn, lllx with
  | nil, _, _, _ => eqFO (Var 1) (Var 1)
  | _, nil, _, _ => eqFO (Var 1) (Var 1)
  | _, _, nil, _ => eqFO (Var 1) (Var 1)
  | _, _, _, nil => eqFO (Var 1) (Var 1)
  | cons P nil, cons lx1 _, cons lxn _, cons llx _ =>
      fun3_l P lx1 lxn llx 
  | cons P _, cons lx1 nil, cons lxn _, cons llx _ =>
      fun3_l P lx1 lxn llx 
  | cons P _, cons lx1 _, cons lxn nil, cons llx _ =>
      fun3_l P lx1 lxn llx 
  | cons P _, cons lx1 _, cons lxn _, cons llx nil =>
      fun3_l P lx1 lxn llx 
  | cons P lP', cons lx1 llx1', cons lxn llxn', cons llx lllx' =>
      conjSO (fun3_l P lx1 lxn llx) (fun3_l_lP lP' llx1' llxn' lllx') 
  end.

Fixpoint sSahlq_pa_pre {W : Set} (Iv : FOvariable -> W) (Ir : W -> W -> Prop)
     (lv : list FOvariable) (x1 : FOvariable) (w : W) :=
  match lv with
  | nil => Ir (Iv x1) w
(*   | cons y nil => exists y ((Ir (Iv x1) (Iv y)) /\ (Ir (Iv y) w)) *)
  | cons y lv' =>  exists y, ((Ir (Iv x1) (Iv y)) /\ (sSahlq_pa_pre Iv Ir lv' y w))
  end.

Fixpoint sSahlq_pa_pre2 {W : Set} (Iv : FOvariable -> W) (Ir : W -> W -> Prop)
     (lv : list FOvariable) (w : W) :=
  match lv with
  | nil => w = w
  | cons y nil => Ir (Iv y) w
(*   | cons y nil => exists y ((Ir (Iv x1) (Iv y)) /\ (Ir (Iv y) w)) *)
  | cons y lv' =>  exists z, ((Ir (Iv y) (Iv z)) /\ (sSahlq_pa_pre2 Iv Ir lv' w))
  end.

Fixpoint sSahlq_pa_pre3 {W : Set} (Iv : FOvariable -> W) (Ir : W -> W -> Prop)
     (lv : list FOvariable) (w : W) :=
  match lv with
  | nil => w = w
  | cons y nil => Ir (Iv y) w
(*   | cons y nil => exists y ((Ir (Iv x1) (Iv y)) /\ (Ir (Iv y) w)) *)
  | cons y lv' =>  exists u, ((Ir (Iv y) u) /\ (sSahlq_pa_pre3 Iv Ir lv' w))
  end.

Fixpoint sSahlq_pa_pre5_pre {W : Set} (* (Iv : FOvariable -> W) *) (Ir : W -> W -> Prop)
     n (u1 w : W) :=
  match n with 
  | 0 => Ir u1 w
  | S m => exists v, ( (Ir u1 v) /\ (sSahlq_pa_pre5_pre Ir m v w))
  end.

Definition sSahlq_pa_pre5 {W : Set} (* (Iv : FOvariable -> W) *) (Ir : W -> W -> Prop)
     (lv : list FOvariable) := sSahlq_pa_pre5_pre Ir (length lv).


Fixpoint sSahlq_pa5 {W : Set} (* (Iv : FOvariable -> W) *) (Ir : W -> W -> Prop)
     (llv : list (list FOvariable)) (u1 w : W) :=
  match llv with 
  | nil => True
  | cons lv nil => sSahlq_pa_pre5 Ir lv u1 w
  | cons lv ln' => (sSahlq_pa_pre5 Ir lv u1 w) \/ (sSahlq_pa5 Ir ln' u1 w)
  end.

Fixpoint sSahlq_pa5' {W : Set} (* (Iv : FOvariable -> W) *) (Ir : W -> W -> Prop)
     (llv : list (list FOvariable)) (lu1 : list W) ( w : W) : Prop :=
  match llv, lu1 with 
  | nil, _ => True
  | _, nil => True
  | cons lv nil, cons u1 _ => sSahlq_pa_pre5 Ir lv u1 w
  | cons lv _, cons u1 nil => sSahlq_pa_pre5 Ir lv u1 w
  | cons lv ln', cons u1 lu1' => 
    (sSahlq_pa_pre5 Ir lv u1 w) \/ (sSahlq_pa5' Ir ln' lu1' w)
  end.

Lemma sSahlq_pa5'_cons : forall (W : Set) (Ir : W -> W -> Prop) llv lu1 w lv u1,
  ~ llv = nil ->
  ~ lu1 = nil ->
  (sSahlq_pa5' Ir (cons lv llv) (cons u1 lu1) w) =
  ((sSahlq_pa_pre5 Ir lv u1 w) \/ (sSahlq_pa5' Ir llv lu1 w)).
Proof.
  intros until 0. intros H1 H2.
  simpl.
  destruct llv. contradiction (H1 eq_refl).
  destruct lu1. contradiction (H2 eq_refl).
  reflexivity.
Qed.

Lemma sSahlq_pa5'_cons2 : forall (W : Set) (Ir : W -> W -> Prop) llv lu1 lv u1,
  ~ llv = nil ->
  ~ lu1 = nil ->
  (sSahlq_pa5' Ir (cons lv llv) (cons u1 lu1)) =
  (fun w => (sSahlq_pa_pre5 Ir lv u1 w) \/ (sSahlq_pa5' Ir llv lu1 w)).
Proof.
  intros until 0. intros H1 H2.
  apply functional_extensionality. intros w.
  apply sSahlq_pa5'_cons; assumption.
Qed.

Fixpoint sSahlq_pa_l5 {W : Set} (Ir : W -> W -> Prop)
  (lllv :  list (list (list FOvariable))) (lu1 : list W) :=
  match lllv, lu1 with
  | nil, _ => nil
  | _, nil => nil
(*   | cons llv nil, cons lx1 _ => sSahlq_pa Iv Ir llv lx1 w *)
  | cons llv lllv', cons u1 lu1' => 
      cons (sSahlq_pa5 Ir llv u1) (sSahlq_pa_l5 Ir lllv' lu1')
  end.

Fixpoint sSahlq_pa_l5' {W : Set} (Ir : W -> W -> Prop)
  (lllv :  list (list (list FOvariable))) (llu1 : (list (list W))) :=
  match lllv, llu1 with
  | nil, _ => nil
  | _, nil => nil
(*   | cons llv nil, cons lx1 _ => sSahlq_pa Iv Ir llv lx1 w *)
  | cons llv lllv', cons lu1 llu1' => 
      cons (sSahlq_pa5' Ir llv lu1) (sSahlq_pa_l5' Ir lllv' llu1')
  end.

Fixpoint sSahlq_pa_pre6 {W : Set} (Iv : FOvariable -> W) (Ir : W -> W -> Prop)
     lv (u1 w : W) :=
  match lv with
  | nil => w = w  
  | cons y nil => ((Iv y = u1) -> Ir u1 u1) /\ ( ~(Iv y = u1) -> Ir u1 w)
  | cons y lv' => ((Iv y = u1) -> ( exists v, ( (Ir u1 u1) /\ (sSahlq_pa_pre6 Iv Ir lv' v w)))) /\
     (~(Iv y = u1) -> ( exists v, ( (Ir u1 v) /\ (sSahlq_pa_pre6 Iv Ir lv' v w))))
  end.

Fixpoint rel_conj2_meta {W : Set} Iv (Ir : W -> W -> Prop) 
  (x y : FOvariable) (lx : list FOvariable) :=
  match lx with
  | nil => Ir (Iv x) (Iv y)
(*   | cons y nil => relatSO x y *)
  | cons z lx' => (Ir (Iv x) (Iv z)) /\ (rel_conj2_meta Iv Ir z y lx')
  end.

Fixpoint sSahlq_pa {W : Set} (Iv : FOvariable -> W) (Ir : W -> W -> Prop)
  (llv : list (list FOvariable)) (lx1 : list FOvariable) (w : W) :=
  match llv, lx1 with
  | nil, _ => True
  | _, nil => True
  | cons lx nil, cons x1 _ =>
    sSahlq_pa_pre Iv Ir lx x1 w 
  | cons lx _, cons x1 nil =>
    sSahlq_pa_pre Iv Ir lx x1 w
  | cons lx llx', cons x1 lx1' =>
    (sSahlq_pa_pre Iv Ir lx x1 w) /\ sSahlq_pa Iv Ir llx' lx1' w
  end.


Fixpoint sSahlq_pa2 {W : Set} (Iv : FOvariable -> W) (Ir : W -> W -> Prop)
  (llv : list (list FOvariable)) (w : W) :=
  match llv with
  | nil => True
  | cons lx nil =>
    sSahlq_pa_pre2 Iv Ir lx w 
  | cons lx llx' =>
    (sSahlq_pa_pre2 Iv Ir lx w) \/ sSahlq_pa2 Iv Ir llx' w
  end.

Fixpoint sSahlq_pa3 {W : Set} (Iv : FOvariable -> W) (Ir : W -> W -> Prop)
  (llv : list (list FOvariable)) (w : W) :=
  match llv with
  | nil => True
  | cons lx nil =>
    sSahlq_pa_pre3 Iv Ir lx w 
  | cons lx llx' =>
    (sSahlq_pa_pre3 Iv Ir lx w) \/ sSahlq_pa3 Iv Ir llx' w
  end.



Fixpoint sSahlq_pa_l {W : Set} (Iv : FOvariable -> W) (Ir : W -> W -> Prop)
  (lllv : list (list (list FOvariable))) (llx1 : list (list FOvariable)) :=
  match lllv, llx1 with
  | nil, _ => nil
  | _, nil => nil
(*   | cons llv nil, cons lx1 _ => sSahlq_pa Iv Ir llv lx1 w *)
  | cons llv lllv', cons lx1 llx1' => 
      cons (sSahlq_pa Iv Ir llv lx1) (sSahlq_pa_l Iv Ir lllv' llx1')
  end.

(* ------------------- *)

Lemma sSahlq_pa_l_nil : forall {W : Set} Iv (Ir : W -> W -> Prop) lllv,
  sSahlq_pa_l Iv Ir lllv nil = nil.
Proof.
  intros W Iv Ir lllv. destruct lllv; reflexivity.
Qed.

Lemma sSahlq_pa_nil : forall l (W : Set) Iv Ir (w : W),
  sSahlq_pa Iv Ir l nil w.
Proof.
  induction l; intros W Iv Ir w. exact I.

    simpl. destruct l; exact I.
Qed.

Lemma alt_Iv_neq : forall {W : Set} (Iv : FOvariable -> W) d x a,
  ~ x = a ->
 alt_Iv Iv d x a = Iv a.
Proof.
  intros W Iv d [xn] [ym] H.
  simpl. rewrite FOvar_neq. reflexivity.
  assumption.
Qed.

Lemma sSahlq_try : forall lv x (W : Set) Iv Ir (d : W),
  is_in_var x lv = false -> 
  sSahlq_pa_pre3 (alt_Iv Iv d x) Ir lv =
  sSahlq_pa_pre3 Iv Ir lv.
Proof.
  induction lv; intros x W Iv Ir d Hin.
    simpl in *. reflexivity.

    apply functional_extensionality. intros w.
    simpl.
    destruct lv.
      simpl in *.
      destruct x as [xn]; destruct a as [ym].
      simpl. case_eq (beq_nat xn ym); intros Hbeq;
        rewrite Hbeq in *. discriminate.
        reflexivity.

        rewrite (IHlv x W Iv Ir d).
        rewrite <- is_in_FO_var in Hin.
        apply is_in_FOvar_cons_f in Hin.
        destruct Hin as [H1 H2].
        rewrite alt_Iv_neq. reflexivity.

      assumption.
      rewrite <- is_in_FO_var in Hin.
      apply is_in_FOvar_cons_f in Hin.
      apply Hin.
Qed.

Lemma lem_z1 : forall alpha x P W Iv Ip Ir d, 
  SOturnst W (alt_Iv Iv d x) (alt_Ip Ip (fun w => Ir (Iv x) w) P) Ir alpha =
  SOturnst W (alt_Iv Iv d x) (alt_Ip Ip (fun w => Ir d w) P) Ir alpha.
Proof.
  induction alpha; intros  x P W Iv Ip Ir d.
    destruct p as [Qm]; destruct P as [Pn]; destruct f as [ym];
    destruct x as [xn]. simpl.
    case_eq (beq_nat xn ym); intros H.
Abort.

Lemma sSahlq_equiv_new_simpl_try3_pre : forall alpha  P x1 u W Iv Ip Ir,
  SOQFree_P alpha P = true ->
  ~ x1 = u ->
  attached_exFO_x alpha x1 = false ->
  attached_allFO_x alpha x1 = false ->
SOturnst W Iv
  (alt_Ip Ip (sSahlq_pa_pre3 Iv Ir (cons x1 nil)) P) Ir alpha <->
SOturnst W Iv Ip Ir
  (replace_pred alpha P u (fun4' x1 u nil)).
Proof.
  induction alpha; intros P x1 u W Iv Ip Ir Hno Hneq Hat1 Hat2.
    simpl. destruct p as [Qm]. destruct P as [Pn].
    destruct x1 as [xn]. destruct u as [un].
    destruct f as [zn]. rewrite <- beq_nat_refl.
    case_eq (beq_nat Pn Qm); intros Hbeq.
      case_eq (beq_nat un xn); intros Hbeq2.
        rewrite (beq_nat_true _ _ Hbeq2) in *.
        contradiction (Hneq eq_refl).

        simpl. rewrite Hbeq. apply iff_refl.

    simpl. rewrite Hbeq. apply iff_refl.

    destruct f. destruct f0. simpl. destruct P.
    apply iff_refl.

    destruct f. destruct f0. simpl. destruct P.
    apply iff_refl.

    rewrite rep_pred_allFO.
    do 2 rewrite SOturnst_allFO. destruct P.
    destruct f as [zn]; destruct x1 as [xn].
    simpl in Hat2.
    case_eq (beq_nat xn zn); intros Hbeq;
      rewrite Hbeq in *. discriminate.    
    simpl in Hat1.
    split; intros SOt d.
      apply IHalpha; try assumption.
      rewrite sSahlq_try. apply SOt.
      simpl. rewrite beq_nat_comm. rewrite Hbeq.
      reflexivity.

      specialize (SOt d).
      apply IHalpha in SOt; try assumption.
      rewrite sSahlq_try in SOt. apply SOt.
      simpl. rewrite beq_nat_comm. rewrite Hbeq.
      reflexivity.

    rewrite rep_pred_exFO.
    do 2 rewrite SOturnst_exFO. destruct P.
    destruct f as [zn]; destruct x1 as [xn].
    simpl in Hat1.
    case_eq (beq_nat xn zn); intros Hbeq;
      rewrite Hbeq in *. discriminate.    
    simpl in Hat2.
    split; intros [d SOt]; exists d.
      apply IHalpha; try assumption.
      rewrite sSahlq_try. apply SOt.
      simpl. rewrite beq_nat_comm. rewrite Hbeq.
      reflexivity.

      apply IHalpha in SOt; try assumption.
      rewrite sSahlq_try in SOt. apply SOt.
      simpl. rewrite beq_nat_comm. rewrite Hbeq.
      reflexivity.

    rewrite rep_pred_negSO. do 2 rewrite SOturnst_negSO.
    destruct P.
    simpl in Hno. simpl in Hat2. simpl in Hat1.
    split ;intros H1 H2; apply H1. apply IHalpha in H2;
      assumption. apply IHalpha; assumption.

    rewrite rep_pred_conjSO. do 2 rewrite SOturnst_conjSO.
    pose proof (attached_exFO_x_conjSO_r _ _ _ Hat1).
    pose proof (attached_exFO_x_conjSO_l _ _ _ Hat1).
    pose proof (attached_allFO_x_conjSO_r _ _ _ Hat2).
    pose proof (attached_allFO_x_conjSO_l _ _ _ Hat2).
    pose proof (SOQFree_P_conjSO_l _ _ _ Hno).
    pose proof (SOQFree_P_conjSO_r _ _ _ Hno).
    split; intros [HH1 HH2]; apply conj.
      apply IHalpha1; assumption.
      apply IHalpha2; assumption.
      apply IHalpha1 in HH1; assumption.
      apply IHalpha2 in HH2; assumption.

    rewrite rep_pred_disjSO. do 2 rewrite SOturnst_disjSO.
    pose proof (attached_exFO_x_conjSO_r _ _ _ Hat1).
    pose proof (attached_exFO_x_conjSO_l _ _ _ Hat1).
    pose proof (attached_allFO_x_conjSO_r _ _ _ Hat2).
    pose proof (attached_allFO_x_conjSO_l _ _ _ Hat2).
    pose proof (SOQFree_P_conjSO_l _ _ _ Hno).
    pose proof (SOQFree_P_conjSO_r _ _ _ Hno).
    split; (intros [HH | HH]; [left | right]).
      apply IHalpha1; assumption.
      apply IHalpha2; assumption.
      apply IHalpha1 in HH; assumption.
      apply IHalpha2 in HH; assumption.

    rewrite rep_pred_implSO. do 2 rewrite SOturnst_implSO.
    pose proof (attached_exFO_x_conjSO_r _ _ _ Hat1).
    pose proof (attached_exFO_x_conjSO_l _ _ _ Hat1).
    pose proof (attached_allFO_x_conjSO_r _ _ _ Hat2).
    pose proof (attached_allFO_x_conjSO_l _ _ _ Hat2).
    pose proof (SOQFree_P_conjSO_l _ _ _ Hno).
    pose proof (SOQFree_P_conjSO_r _ _ _ Hno).
    split; intros HH1 HH2.
      apply IHalpha2; try assumption.
      apply HH1; try assumption.
      apply IHalpha1 in HH2; assumption.

      apply IHalpha2 with (u := u); try assumption.
      apply HH1; try assumption.
      apply IHalpha1; assumption.

    destruct p as [Qm]. destruct P as [Pn].
    rewrite rep_pred_allSO.
    simpl in Hno. 
    case_eq (beq_nat Pn Qm); intros Hbeq;
      rewrite Hbeq in *. discriminate.
    rewrite beq_nat_comm. rewrite Hbeq.
    do 2 rewrite SOturnst_allSO.
    simpl in Hat1. simpl in Hat2.
    split; intros HH pa; specialize (HH pa).
      apply IHalpha; try assumption.
      rewrite alt_Ip_switch. assumption.
        apply beq_nat_false. assumption.
      apply IHalpha in HH; try assumption.
      rewrite <- alt_Ip_switch. assumption.
        apply beq_nat_false. assumption.

    destruct p as [Qm]. destruct P as [Pn].
    rewrite rep_pred_exSO.
    simpl in Hno. 
    case_eq (beq_nat Pn Qm); intros Hbeq;
      rewrite Hbeq in *. discriminate.
    rewrite beq_nat_comm. rewrite Hbeq.
    do 2 rewrite SOturnst_exSO.
    simpl in Hat1. simpl in Hat2.
    split; intros [pa HH]; exists pa.
      apply IHalpha; try assumption.
      rewrite alt_Ip_switch. assumption.
        apply beq_nat_false. assumption.
      apply IHalpha in HH; try assumption.
      rewrite <- alt_Ip_switch. assumption.
        apply beq_nat_false. assumption.
Qed.

Fixpoint is_all_diff_FOv (l : list FOvariable) : bool :=
  match l with
  | nil => true
  | cons y l' => if is_in_FOvar y l' then false else is_all_diff_FOv l'
  end.

Fixpoint is_all_diff_FOv2 (ll : list (list FOvariable)) : bool :=
  match ll with
  | nil => true
  | cons l ll' => if is_all_diff_FOv l then is_all_diff_FOv2 ll'
    else false
  end.

Fixpoint is_all_diff_FOv3 (lx : list FOvariable) (llv : list (list FOvariable)) : bool :=
  match lx, llv with
  | nil, _ => true 
  | _, nil => true
  | cons x lx', cons lv llv' => if is_all_diff_FOv (cons x lv) then
      is_all_diff_FOv3 lx' llv' else false
  end.

(* ------------- *)


Definition comp_cond_x1 (alpha : SecOrder) : FOvariable :=
  batm_comp_x1 alpha.

Definition comp_cond_x1_l (alpha : SecOrder) : list FOvariable :=
  batm_conj_comp_x1 alpha.

Fixpoint comp_cond_xn (alpha : SecOrder): FOvariable :=
  match alpha with
  | predSO P x => x 
  | allFO x beta => comp_cond_xn beta
  | implSO beta1 beta2 => comp_cond_xn beta2 
  | _ => (Var 0)
  end.


Fixpoint comp_cond_xn_l (alpha : SecOrder): list FOvariable :=
  match alpha with
  | predSO P x => cons x nil 
  | allFO x beta => cons (comp_cond_xn beta) nil
  | implSO beta1 beta2 => cons (comp_cond_xn beta2) nil
  | conjSO beta1 beta2 => app (comp_cond_xn_l beta1) (comp_cond_xn_l beta2)
  | _ => nil
  end.

Fixpoint comp_cond_lx (alpha : SecOrder): list FOvariable :=
  match alpha with
  | allFO y (implSO beta1 (predSO P z)) => nil
  | predSO P y => nil
  | allFO y beta => cons y (comp_cond_lx beta)
  | _ => nil
  end.

Fixpoint comp_cond_lx2 (alpha : SecOrder): list FOvariable :=
  match alpha with
  | allFO y (implSO beta1 (predSO P z)) => nil
  | predSO P y => nil
  | allFO y (implSO _ beta) => cons y (comp_cond_lx2 beta)
  | _ => nil
  end.

Fixpoint comp_cond_lx_l (alpha : SecOrder): list (list FOvariable) :=
  match alpha with
  | allFO y (implSO beta1 (predSO P z)) => cons nil nil
  | predSO P y => cons nil nil
  | allFO y beta => (cons (cons y (comp_cond_lx beta)) nil)
  | conjSO beta1 beta2 => app (comp_cond_lx_l beta1) (comp_cond_lx_l beta2)
  | _ => nil
  end.

Fixpoint comp_cond_lx_l2 (alpha : SecOrder): list (list FOvariable) :=
  match alpha with
  | conjSO beta1 beta2 =>  app (comp_cond_lx_l2 beta1) (comp_cond_lx_l2 beta2)
  | allFO x beta => cons (comp_cond_lx2 (allFO x beta)) nil
  | _ => nil
  end.



Fixpoint P_branch_allFO alpha P : bool :=
  match alpha with
  | allFO _ (implSO _ beta) => P_branch_allFO beta P
  | predSO Q x => match P, Q with Pred Pn, Pred Qm =>
      beq_nat Pn Qm end
  | _ => false
  end.


Fixpoint calc_lx1_P alpha P : list FOvariable :=
  match alpha with
  | conjSO beta1 beta2 => app (calc_lx1_P beta1 P) (calc_lx1_P beta2 P)
  | allFO _ _ => if P_branch_allFO alpha P then cons (comp_cond_x1 alpha) nil
      else nil
  | _ => nil
  end.

Fixpoint calc_lx1_lP alpha lP : list (list FOvariable) :=
  match lP with
  | nil => nil
  | cons P lP' => cons (calc_lx1_P alpha P) (calc_lx1_lP alpha lP')
  end.


Fixpoint calc_llv_P alpha P : list (list FOvariable) :=
  match alpha with
  | conjSO beta1 beta2 => app (calc_llv_P beta1 P) (calc_llv_P beta2 P)
  | allFO _ _ => if P_branch_allFO alpha P then cons (comp_cond_lx2 alpha) nil
      else nil
  | _ => nil
  end.

Fixpoint calc_llv_lP alpha lP : list (list (list FOvariable)) :=
  match lP with
  | nil => nil
  | cons P lP' => cons (calc_llv_P alpha P) (calc_llv_lP alpha lP')
  end.


Fixpoint calc_lP alpha lP : list SecOrder :=
  match lP with
  | nil => nil
  | cons P lP' => cons (fun4_l2' (calc_lx1_P alpha P) (Var (new_FOv_pp_pre2 alpha)) (calc_llv_P alpha P)) (calc_lP alpha lP')
  end.

Fixpoint new_FOvars_SO alpha xmin : SecOrder :=
  match xmin with
  | Var n =>
  match alpha with
  | predSO P x => predSO P (Var (n + (match x with Var m => m end)))
  | relatSO x y => relatSO (Var (n + (match x with Var xn => xn end)))
    (Var (n + (match y with Var ym => ym end)))
  | eqFO x y => eqFO (Var (n + (match x with Var xn => xn end)))
    (Var (n + (match y with Var ym => ym end)))
  | negSO beta => negSO (new_FOvars_SO beta xmin)
  | allFO x beta => allFO (Var (n + (match x with Var m => m end))) (new_FOvars_SO beta xmin)
  | exFO x beta => exFO (Var (n + (match x with Var m => m end))) (new_FOvars_SO beta xmin)
  | conjSO beta1 beta2 => conjSO (new_FOvars_SO beta1 xmin) (new_FOvars_SO beta2 xmin)
  | disjSO beta1 beta2 => disjSO (new_FOvars_SO beta1 xmin) (new_FOvars_SO beta2 xmin)
  | implSO beta1 beta2 => implSO (new_FOvars_SO beta1 xmin) (new_FOvars_SO beta2 xmin)
  | allSO P beta => allSO P (new_FOvars_SO beta xmin)
  | exSO P beta => allSO P (new_FOvars_SO beta xmin)
  end end.

Fixpoint new_FOvars_l l xmin  :=
  match xmin with
  | Var n =>
  match l with
  | nil => nil
  | cons x l' => cons (Var (n + (match x with Var xn => xn end))) (new_FOvars_l l' xmin)
  end end.

Fixpoint new_FOvars_ll ll xmin :=
  match ll with
  | nil => nil
  | cons l ll' => cons (new_FOvars_l l xmin) (new_FOvars_ll ll' xmin)
  end .

Fixpoint new_FOvars_lll lll xmin :=
  match lll with
  | nil => nil
  | cons ll lll' => cons (new_FOvars_ll ll xmin) (new_FOvars_lll lll' xmin)
  end .

(* --------------------------- *)

Lemma  sSahlq_equiv_new_simpl_try3_base_pre : forall lv x1 y u W Iv Ip Ir,
(* is_in_var x1 lv = false -> *)
is_in_var u (x1 :: lv) = false ->
is_in_var y (x1 :: lv) = false ->
is_in_var x1 lv = false ->
is_all_diff_FOv lv = true ->
sSahlq_pa_pre5_pre Ir (length lv) (Iv x1) (Iv y) <-> SOturnst W Iv Ip Ir (replace_FOv (fun4' x1 u lv) u y).
Proof.
  induction lv; intros [xn] [ym] [zn] W Iv Ip Ir (* Hin0 *) Hin1 Hin2 Hin3 Hall.
    simpl in *. rewrite <- beq_nat_refl.
    case_eq (beq_nat zn xn); intros Hbeq; rewrite Hbeq in *.
      discriminate.
    apply iff_refl.
(*     simpl. split ;intros SOt. assumption.
      destruct SOt as [H1 H2].
      apply H1.
    apply iff_refl. *)

    destruct a as [un].
    apply is_in_FOvar_cons_f in Hin1. destruct Hin1 as [H1 H2].
    apply is_in_FOvar_cons_f in H1. destruct H1 as [H1 H3].
    apply is_in_FOvar_cons_f in Hin2. destruct Hin2 as [H1' H2'].
    apply is_in_FOvar_cons_f in H1'. destruct H1' as [H1' H3'].
    simpl. rewrite (FOvar_neq _ _ H3).
    rewrite (FOvar_neq _ _ H2). rewrite SOturnst_exFO.
    split; intros [d SOt].
      exists d.
      rewrite SOturnst_conjSO.
      apply conj.
        simpl. rewrite <- beq_nat_refl.
        case_eq (beq_nat un xn); intros Hbeq.
          simpl in Hin3. rewrite beq_nat_comm in Hbeq.
          rewrite Hbeq in Hin3. discriminate.

          apply SOt.

          simpl in Hall.
          case_eq (is_in_FOvar (Var un) lv);
            intros H; rewrite H in *. discriminate.
        apply IHlv. 

       simpl. rewrite (FOvar_neq _ _ H3). assumption.
          simpl. rewrite (FOvar_neq _ _ H3'). assumption.
           rewrite <- is_in_FO_var. assumption.
          assumption.
        destruct SOt as [SOt1 SOt2].
        simpl. rewrite <- beq_nat_refl.
        rewrite beq_nat_comm. rewrite (FOvar_neq _ _ H3'). assumption.

      exists d.
      rewrite SOturnst_conjSO in SOt. simpl in SOt.
      apply conj.
        simpl. rewrite <- beq_nat_refl in SOt.
        case_eq (beq_nat un xn); intros Hbeq; rewrite Hbeq in *.
          simpl in Hin3. rewrite beq_nat_comm in Hbeq.
          rewrite Hbeq in Hin3. discriminate.

          apply SOt.

          simpl in Hall.
          case_eq (is_in_FOvar (Var un) lv);
            intros H; rewrite H in *. discriminate.

        destruct SOt as [SOt1 SOt2].
        apply IHlv in SOt2. rewrite <- beq_nat_refl in *.
        rewrite beq_nat_comm in SOt2.     
        rewrite (FOvar_neq _ _ H3') in SOt2. assumption.

       simpl. rewrite (FOvar_neq _ _ H3). assumption.
          simpl. rewrite (FOvar_neq _ _ H3'). assumption.
           rewrite <- is_in_FO_var. assumption.
          assumption.
Qed.

Lemma  sSahlq_equiv_new_simpl_try3_base_pre' : forall lv x1 y u W Iv Ip Ir,
(* is_in_var x1 lv = false -> *)
is_in_var u (x1 :: lv) = false ->
is_in_var y (lv) = false ->
is_in_var x1 lv = false ->
is_all_diff_FOv lv = true ->
sSahlq_pa_pre5_pre Ir (length lv) (Iv x1) (Iv y) <-> SOturnst W Iv Ip Ir (replace_FOv (fun4' x1 u lv) u y).
Proof.
  induction lv; intros [xn] [ym] [zn] W Iv Ip Ir (* Hin0 *) Hin1  Hin2 Hin3 Hall.
    simpl in *. rewrite <- beq_nat_refl.
    case_eq (beq_nat zn xn); intros Hbeq; rewrite Hbeq in *.
      discriminate.
    apply iff_refl.
(*     simpl. split ;intros SOt. assumption.
      destruct SOt as [H1 H2].
      apply H1.
    apply iff_refl. *)

    destruct a as [un].
    apply is_in_FOvar_cons_f in Hin1. destruct Hin1 as [H1 H2].
    apply is_in_FOvar_cons_f in H1. destruct H1 as [H1 H3].
(*     apply is_in_FOvar_cons_f in Hin2. destruct Hin2 as [H1' H2'].
    apply is_in_FOvar_cons_f in H1'. destruct H1' as [H1' H3']. *)
    simpl. rewrite (FOvar_neq _ _ H3).
    rewrite (FOvar_neq _ _ H2). rewrite SOturnst_exFO.
    split; intros [d SOt].
      exists d.
      rewrite SOturnst_conjSO.
      apply conj.
        simpl. rewrite <- beq_nat_refl.
        case_eq (beq_nat un xn); intros Hbeq.
          simpl in Hin3. rewrite beq_nat_comm in Hbeq.
          rewrite Hbeq in Hin3. discriminate.

          apply SOt.

          simpl in Hall.
          case_eq (is_in_FOvar (Var un) lv);
            intros H; rewrite H in *. discriminate.
        apply IHlv. 

       simpl. rewrite (FOvar_neq _ _ H3). assumption.
          apply is_in_FOvar_cons_f in Hin2. destruct Hin2 as [H1' H2'].
          rewrite <- is_in_FO_var. assumption.
(*          rewrite H1'. 
Search is_in_FOvar cons false.
           simpl in Hin2. rewrite (FOvar_neq _ _ H3'). assumption.
           rewrite <- is_in_FO_var. assumption. *)
          assumption. assumption.
        destruct SOt as [SOt1 SOt2].
        simpl. rewrite <- beq_nat_refl.
          apply is_in_FOvar_cons_f in Hin2. destruct Hin2 as [H1' H2'].
        rewrite beq_nat_comm. rewrite (FOvar_neq _ _ H2'). assumption.

      exists d.
      rewrite SOturnst_conjSO in SOt. simpl in SOt.
      apply conj.
        simpl. rewrite <- beq_nat_refl in SOt.
        case_eq (beq_nat un xn); intros Hbeq; rewrite Hbeq in *.
          simpl in Hin3. rewrite beq_nat_comm in Hbeq.
          rewrite Hbeq in Hin3. discriminate.

          apply SOt.

          simpl in Hall.
          case_eq (is_in_FOvar (Var un) lv);
            intros H; rewrite H in *. discriminate.

        destruct SOt as [SOt1 SOt2].
        apply IHlv in SOt2. rewrite <- beq_nat_refl in *.
        rewrite beq_nat_comm in SOt2.     
          apply is_in_FOvar_cons_f in Hin2. destruct Hin2 as [H1' H2'].
        rewrite (FOvar_neq _ _ H2') in SOt2. assumption.

       simpl. rewrite (FOvar_neq _ _ H3). assumption.
          apply is_in_FOvar_cons_f in Hin2. destruct Hin2 as [H1' H2'].
          assumption. assumption. assumption.
Qed.

Lemma sSahlq_equiv_new_simpl_try3_base : forall lv x1 P p f W Iv Ip Ir u,
SOQFree_P (predSO p f) P = true ->
is_in_var u (x1 :: lv) = false ->
is_in_var f (x1 :: lv) = false ->
is_all_diff_FOv (cons x1 lv) = true ->
ex_attached_exFO_lv (predSO p f) (x1 :: lv) = false ->
ex_attached_allFO_lv (predSO p f) (x1 :: lv) = false ->
SOturnst W Iv (alt_Ip Ip (sSahlq_pa_pre5_pre Ir (length lv) (Iv x1)) P) Ir (predSO p f) <->
SOturnst W Iv Ip Ir (replace_pred (predSO p f) P u (fun4' x1 u lv)).
Proof.
  intros lv x1 P p f W Iv Ip Ir u Hno Hin Hin2 Hall Hat1 Hat2.
  destruct P as [Pn]. destruct p as [Qm]. destruct f as [ym].
  simpl. case_eq (beq_nat Pn Qm); intros Hbeq.
      simpl in Hall.
      case_eq (is_in_FOvar x1 lv); intro H; rewrite H in *.
        discriminate.
    apply sSahlq_equiv_new_simpl_try3_base_pre; try assumption.
    simpl in Hat1. simpl in Hall.

    simpl. apply iff_refl.
Qed.

Fixpoint cap_FOv l1 l2 :=
  match l1 with
  | nil => nil
  | cons P l1' => if is_in_FOvar P l2 then cons P (cap_FOv l1' l2)
          else cap_FOv l1' l2
  end.

Lemma cap_FOv_app_nil : forall l1 l2 l3,
cap_FOv (app l1 l2) l3 = nil ->
(cap_FOv l1 l3 = nil /\ cap_FOv l2 l3 = nil).
Proof.
  induction l1; intros l2 l3 H.
    simpl in *. apply conj. reflexivity. assumption.

    simpl in *. case_eq (is_in_FOvar a l3);
      intros H2; rewrite H2 in *. discriminate.
    apply conj; apply (IHl1 l2 l3); assumption.
Qed.

Lemma sSahlq_equiv_new_simpl_try3 : forall alpha lv x1 P u W Iv Ip Ir,
  SOQFree_P alpha P = true ->
(*   ~ x1 = u -> *)
  is_in_var u (cons x1 lv) = false ->
  ex_attached_exFO_lv alpha (cons x1 lv) = false ->
  ex_attached_allFO_lv alpha (cons x1 lv) = false ->
  cap_FOv (FOvars_in alpha) lv = nil ->
  is_all_diff_FOv (cons x1 lv) = true ->
(*   ex_attached_allFO_lv alpha lv = false ->
  ex_attached_exFO_lv alpha lv = false -> *)
(*     SOturnst W Iv (alt_Ip Ip (CM_pa2_l_gen Iv lv x) P) Ir alpha <->
    SOturnst W Iv Ip Ir (replace_pred alpha P x (fun1 lv x)).
 *)
(* is_in_FOvar x (FOvars_in alpha) = false -> *)
SOturnst W Iv
  (alt_Ip Ip (sSahlq_pa_pre5_pre Ir (length lv) (Iv x1)) P) Ir alpha <->
SOturnst W Iv Ip Ir
  (replace_pred alpha P u (fun4' x1 u lv)).
Proof.
  induction alpha; intros lv x1 P u W Iv Ip Ir Hno Hneq Hat1 Hat2 Hcap Hall.
    destruct p as [Qm]. destruct P as [Pn].
    destruct x1 as [xn]. destruct u as [un].
    destruct f as [zn].
    simpl. case_eq (beq_nat Pn Qm); intros Hbeq.
      apply sSahlq_equiv_new_simpl_try3_base_pre';
        try assumption.
      simpl in Hcap. simpl. case_eq (is_in_FOvar (Var zn) lv);
        intros Hin; rewrite Hin in *. discriminate. assumption.
      
        simpl in Hall. rewrite <- is_in_FO_var. case_eq (is_in_FOvar (Var xn) lv);
          intros Hbeq2; rewrite Hbeq2 in *. discriminate.
        reflexivity.

        simpl in Hall. case_eq (is_in_FOvar (Var xn) lv);
          intros Hbeq2; rewrite Hbeq2 in *. discriminate.
        assumption.

        simpl. apply iff_refl.

    destruct f. destruct f0. destruct P. simpl. apply iff_refl.

    destruct f. destruct f0. destruct P. simpl. apply iff_refl.

    rewrite rep_pred_allFO. do 2 rewrite SOturnst_allFO.
    simpl in Hno. destruct P.  apply ex_attached_allFO_lv_allFO in Hat2.
    apply ex_attached_exFO_lv_allFO in Hat1. destruct Hat2 as [H1 H2].
    simpl in Hcap. case_eq (is_in_FOvar f lv);
      intros H3; rewrite H3 in *. discriminate.
    split; intros SOt d; specialize (SOt d).
      apply IHalpha; try assumption.
      simpl in H2. destruct f as [zn]. destruct x1 as [xn].
      case_eq (beq_nat zn xn); intros Hbeq; rewrite Hbeq in *.
        discriminate.
      rewrite alt_Iv_neq. assumption. 
      apply beq_nat_false_FOv. assumption.

      simpl in H2. destruct f as [zn]. destruct x1 as [xn].
      case_eq (beq_nat zn xn); intros Hbeq; rewrite Hbeq in *.
        discriminate.
      rewrite <- (alt_Iv_neq Iv d (Var zn)).
      apply IHalpha in SOt; assumption. apply beq_nat_false_FOv.
      assumption.

    rewrite rep_pred_exFO. do 2 rewrite SOturnst_exFO.
    simpl in Hno. destruct P.  apply ex_attached_allFO_lv_exFO in Hat2.
    apply ex_attached_exFO_lv_exFO in Hat1. destruct Hat1 as [H1 H2].
    simpl in Hcap. case_eq (is_in_FOvar f lv);
      intros H3; rewrite H3 in *. discriminate.
    split; intros [d SOt]; exists d.
      apply IHalpha; try assumption.
      simpl in H2. destruct f as [zn]. destruct x1 as [xn].
      case_eq (beq_nat zn xn); intros Hbeq; rewrite Hbeq in *.
        discriminate.
      rewrite alt_Iv_neq. assumption. 
      apply beq_nat_false_FOv. assumption.

      simpl in H2. destruct f as [zn]. destruct x1 as [xn].
      case_eq (beq_nat zn xn); intros Hbeq; rewrite Hbeq in *.
        discriminate.
      rewrite <- (alt_Iv_neq Iv d (Var zn)).
      apply IHalpha in SOt; assumption. apply beq_nat_false_FOv.
      assumption.

    rewrite rep_pred_negSO. do 2 rewrite SOturnst_negSO.  
    simpl in Hno. destruct P. rewrite ex_att_exFO_lv_negSO in Hat1.
    rewrite ex_att_allFO_lv_negSO in Hat2.
    split ;intros SOt H; apply SOt. apply IHalpha in H;
      assumption.
      apply IHalpha; assumption.

    rewrite rep_pred_conjSO. do 2 rewrite SOturnst_conjSO.
    pose proof (SOQFree_P_conjSO_l _ _ _ Hno).
    pose proof (SOQFree_P_conjSO_r _ _ _ Hno).
    apply ex_att_exFO_lv_conjSO_f in Hat1. destruct Hat1.
    apply ex_att_allFO_lv_conjSO_f in Hat2. destruct Hat2.
    simpl in Hcap.
    apply cap_FOv_app_nil in Hcap. destruct Hcap.
    split; intros [HH1 HH2]; 
      (apply conj; [apply (IHalpha1 _ _ _ u) | apply (IHalpha2 _ _ _ u)]);
      try assumption.

    rewrite rep_pred_disjSO. do 2 rewrite SOturnst_disjSO.
    pose proof (SOQFree_P_conjSO_l _ _ _ Hno).
    pose proof (SOQFree_P_conjSO_r _ _ _ Hno).
    apply ex_att_exFO_lv_disjSO_f in Hat1. destruct Hat1.
    apply ex_att_allFO_lv_disjSO_f in Hat2. destruct Hat2.
    simpl in Hcap.
    apply cap_FOv_app_nil in Hcap. destruct Hcap.
    split; (intros [HH1 | HH2]; 
      [left; apply (IHalpha1 _ _ _ u) | right; apply (IHalpha2 _ _ _ u)];
      try assumption).

    rewrite rep_pred_implSO. do 2 rewrite SOturnst_implSO.
    pose proof (SOQFree_P_conjSO_l _ _ _ Hno).
    pose proof (SOQFree_P_conjSO_r _ _ _ Hno).
    apply ex_att_exFO_lv_implSO_f in Hat1. destruct Hat1.
    apply ex_att_allFO_lv_implSO_f in Hat2. destruct Hat2.
    simpl in Hcap.
    apply cap_FOv_app_nil in Hcap. destruct Hcap.
    split; intros HH1 HH2; 
      apply (IHalpha2 _ _ _ u); try assumption;
      apply HH1; apply (IHalpha1 _ _ _ u); try assumption.

    destruct P as [Pn]. destruct p as [Qm].
    simpl in Hno. case_eq (beq_nat Pn Qm); intros Hbeq;
      rewrite Hbeq in *. discriminate.
    rewrite ex_att_exFO_lv_allSO in Hat1.
    rewrite ex_att_allFO_lv_allSO in Hat2.
    simpl FOvars_in in Hcap.
    rewrite rep_pred_allSO. rewrite beq_nat_comm. rewrite Hbeq.
    do 2 rewrite SOturnst_allSO.
    split; intros SOt pa; specialize (SOt pa).
      apply (IHalpha _ _ _ u); try assumption;
      rewrite alt_Ip_switch; try assumption.
      apply beq_nat_false. assumption.

      rewrite alt_Ip_switch; try assumption.
      apply (IHalpha _ _ _ u); try assumption.
      apply beq_nat_false. rewrite beq_nat_comm. assumption.

    destruct P as [Pn]. destruct p as [Qm].
    simpl in Hno. case_eq (beq_nat Pn Qm); intros Hbeq;
      rewrite Hbeq in *. discriminate.
    rewrite ex_att_exFO_lv_exSO in Hat1.
    rewrite ex_att_allFO_lv_exSO in Hat2.
    simpl FOvars_in in Hcap.
    rewrite rep_pred_exSO. rewrite beq_nat_comm. rewrite Hbeq.
    do 2 rewrite SOturnst_exSO.
    split; intros [pa SOt]; exists pa.
      apply (IHalpha _ _ _ u); try assumption;
      rewrite alt_Ip_switch; try assumption.
      apply beq_nat_false. assumption.

      rewrite alt_Ip_switch; try assumption.
      apply (IHalpha _ _ _ u); try assumption.
      apply beq_nat_false. rewrite beq_nat_comm. assumption.
Qed.

Definition Iv_ify {W : Set} (Iv : FOvariable -> W) (x : FOvariable) : W :=
  Iv x.
Require Import List.
Fixpoint map2 {A B : Type} (f : A -> B) (ll:list (list A)) : list (list B) :=
  match ll with
    | nil => nil
    | l :: ll' => (map f l) :: (map2 f ll')
  end.

Lemma rep_pred_false_pa_t2:
  forall (alpha : SecOrder) (W : Set) (Iv : FOvariable -> W)
    (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop) (P : predicate) x,
  SOQFree alpha = true ->
  SOturnst W Iv Ip Ir (replace_pred alpha P x (eqFO (Var 1) (Var 1))) <->
  SOturnst W Iv (alt_Ip Ip pa_t P) Ir alpha.
Proof.
  induction alpha; intros W Iv Ip Ir P [xn] noSO;
    try destruct P as [Pn]; try destruct p as [Qm];
    try destruct f; try destruct f0.

    simpl; unfold pa_t.
    case_eq (beq_nat Pn Qm); intros Hbeq.
      case_eq (beq_nat xn 1); intros Hbeq2;
      simpl; split; intros H; reflexivity.
      simpl.
      apply iff_refl.

    simpl; apply iff_refl.
    simpl; apply iff_refl.

    rewrite rep_pred_allFO.
    do 2 rewrite SOturnst_allFO.
    simpl in noSO.
    split; (intros H d;
      apply (IHalpha _ _ _ _ _ (Var xn)); [assumption | apply H]).

    rewrite rep_pred_exFO.
    do 2 rewrite SOturnst_exFO.
    split; intros H; destruct H as [d H];
      exists d; apply (IHalpha _ _ _ _ _ (Var xn));
      assumption.

    rewrite rep_pred_negSO.
    do 2 rewrite SOturnst_negSO.
    unfold not.
    split; intros H1 H2;
      apply H1; apply (IHalpha _ _ _ _ _ (Var xn));
      assumption.

    rewrite rep_pred_conjSO.
    do 2 rewrite SOturnst_conjSO.
    pose proof (SOQFree_conjSO_l _ _ noSO) as H1.
    pose proof (SOQFree_conjSO_r _ _ noSO) as H2.
    split; (intros H; apply conj;
      [apply (IHalpha1 _ _ _ _ _ (Var xn)) | apply (IHalpha2 _ _ _ _ _ (Var xn))]);
      try assumption; apply H.

    rewrite rep_pred_disjSO.
    pose proof (SOQFree_conjSO_l _ _ noSO) as H1.
    pose proof (SOQFree_conjSO_r _ _ noSO) as H2.
    do 2 rewrite SOturnst_disjSO.
    split; (intros H; destruct H;
      [left; apply (IHalpha1 _ _ _ _ _ (Var xn)) | 
        right; apply (IHalpha2 _ _ _ _ _ (Var xn))]);
      assumption.

    rewrite rep_pred_implSO.
    do 2 rewrite SOturnst_implSO.
    pose proof (SOQFree_conjSO_l _ _ noSO) as Hl.
    pose proof (SOQFree_conjSO_r _ _ noSO) as Hr.
    split; intros H1 H2; apply (IHalpha2 _ _ _ _ _ (Var xn)); try assumption;
      apply H1; apply (IHalpha1 _ _ _ _ _ (Var xn)); assumption.

    simpl in noSO; discriminate.
    simpl in noSO; discriminate.
Qed.

Lemma sSahlq_equiv_new_simpl_try3_LP'_pre_predSO_pre_pre : 
forall a f xn ym W Iv Ip Ir,
is_in_FOvar (Var ym) (f :: nil) = false ->
is_in_FOvar (Var xn) a = false ->
is_in_FOvar (Var ym) a = false ->
is_in_FOvar f a = false ->
is_all_diff_FOv a = true ->
sSahlq_pa_pre5 Ir a (Iv f) (Iv (Var xn)) <->
SOturnst W Iv Ip Ir (replace_FOv (fun4' f (Var ym) a) (Var ym) (Var xn)).
Proof.
  induction a; intros [zn] xn ym W Iv Ip Ir Hin Hin2 Hin3 Hin4 Hall.
    simpl. rewrite <- beq_nat_refl.
    unfold sSahlq_pa_pre5. simpl.   
    simpl in Hin. 
    case_eq (beq_nat ym zn); intros Hbeq. rewrite Hbeq in *.
      discriminate.

      apply iff_refl.

    simpl. destruct a as [un]. 
    simpl in Hall. case_eq (is_in_FOvar (Var un) a0);
      intros Hin5; rewrite Hin5 in *. discriminate.
    unfold Iv_ify. unfold sSahlq_pa_pre5.
    simpl in Hin. 
    case_eq (beq_nat ym zn); intros Hbeq. rewrite Hbeq in *.
      discriminate.
    simpl in Hin3. 
    case_eq (beq_nat ym un); intros Hbeq4; rewrite Hbeq4 in *.
      discriminate.

      simpl. rewrite <- beq_nat_refl.
      simpl in Hin4. case_eq (beq_nat zn un); intros Hbeq5;
        rewrite Hbeq5 in *. discriminate.
      split ;intros H.
        destruct H as [v H].
        exists v. apply conj.
        rewrite beq_nat_comm. rewrite Hbeq5.

          apply H.

        apply IHa. simpl. rewrite Hbeq4. reflexivity.
simpl in Hin2. case_eq (beq_nat xn un); intros Hbeq3;
  rewrite Hbeq3 in *. discriminate. assumption.
assumption.
assumption.
assumption.
        unfold sSahlq_pa_pre5.
        rewrite <- beq_nat_refl.
simpl in Hin2. case_eq (beq_nat xn un); intros Hbeq3;
  rewrite Hbeq3 in *. discriminate.
rewrite beq_nat_comm. rewrite Hbeq3.
(*         case_eq (beq_nat un xn); intros Hbeq3.
admit. *)
            apply H.

        destruct H as [v H].
        exists v. apply conj.
        rewrite beq_nat_comm in H. rewrite Hbeq5 in H.

          apply H.

        destruct H as [H1 H2]. apply IHa in H2.
simpl in Hin2. rewrite <- beq_nat_refl in H2.
 rewrite beq_nat_comm in H2. case_eq (beq_nat xn un); intros Hbeq3;
  rewrite Hbeq3 in *. discriminate. assumption.
  simpl. rewrite Hbeq4. reflexivity.

simpl in Hin2. case_eq (beq_nat xn un); intros Hbeq3;
 rewrite Hbeq3 in *. discriminate. assumption.
all : try assumption.
Qed.
    
Lemma sSahlq_equiv_new_simpl_try3_LP'_pre_predSO_pre : forall llv lx1 W Iv Ip Ir y xn,
length lx1 = length llv ->
is_in_FOvar y lx1 = false ->
ex_FOvar_x_ll (Var xn) llv = false ->
ex_FOvar_x_ll y llv = false ->
is_all_diff_FOv3 lx1 llv = true ->
(* ex_FOvar_x_ll f llv = false -> *)
sSahlq_pa5' Ir llv (map (Iv_ify Iv) lx1) (Iv (Var xn)) <->
SOturnst W Iv Ip Ir (replace_FOv (fun4_l2' lx1 y llv) y (Var xn)).
Proof.
  induction llv; intros lx1 W Iv Ip Ir [ym] xn Hl Hin Hex Hex2 Hall(* Hex3 *).
    destruct lx1. 2 : discriminate. simpl.
    case_eq (beq_nat ym 1); intros;
      (split; intros; [reflexivity |  exact I]).

    destruct lx1. discriminate. simpl. 
    case_eq lx1. intros Hlx1. rewrite Hlx1 in *. destruct llv.
      unfold Iv_ify.
simpl in Hex. case_eq (is_in_FOvar (Var xn) a);
  intros Hin2; rewrite Hin2 in *. discriminate.
(* unfold sSahlq_pa_pre5.
pose proof sSahlq_equiv_new_simpl_try3. *)
      apply sSahlq_equiv_new_simpl_try3_LP'_pre_predSO_pre_pre; try assumption.
simpl in Hex2. case_eq (is_in_FOvar (Var ym) a); intros HH; rewrite HH in *.
  discriminate. assumption.
simpl in Hall. case_eq (is_in_FOvar f a); intros HH; rewrite HH in *. 
  discriminate. reflexivity.

simpl in Hall. case_eq (is_in_FOvar f a); intros HH; rewrite HH in *. 
  discriminate. 
case_eq (is_all_diff_FOv a); intros HH2; rewrite HH2 in *.
  reflexivity. discriminate. discriminate.

    intros x1 lx1' Hlx1. rewrite <- Hlx1.
    case_eq llv. intros Hllv. rewrite Hllv in *. rewrite Hlx1 in *. discriminate.
    intros lv llv' Hllv. rewrite <- Hllv. 
    case_eq (map (Iv_ify Iv) lx1).
      intros H. rewrite Hlx1 in H. discriminate.
    intros w lw Hlw. rewrite <- Hlw.
    rewrite replace_FOv_disjSO. rewrite SOturnst_disjSO.
    split; (intros [H1 | H2]; [left | right]).
      apply sSahlq_equiv_new_simpl_try3_LP'_pre_predSO_pre_pre.
      simpl in *. destruct f as [zn].
      case_eq (beq_nat ym zn); intros HH; rewrite HH in *. discriminate.
      reflexivity. simpl in Hex. case_eq (is_in_FOvar (Var xn) a);
        intros HH; rewrite HH in *. discriminate. reflexivity.
simpl in Hex2. case_eq (is_in_FOvar (Var ym) a); intros HH; rewrite HH in *.
  discriminate. reflexivity.
simpl in Hall. case_eq (is_in_FOvar f a); intros HH; rewrite HH in *. 
  discriminate. reflexivity.

simpl in Hall. case_eq (is_in_FOvar f a); intros HH; rewrite HH in *. 
  discriminate. 
case_eq (is_all_diff_FOv a); intros HH2; rewrite HH2 in *.
  reflexivity. discriminate.

 assumption.

      simpl in Hl. inversion Hl as [Hl']. apply IHllv; try assumption.

      destruct f as [un]. simpl in Hin. case_eq (beq_nat ym un);
        intros HH; rewrite HH in *. discriminate. assumption.
simpl in Hex. case_eq (is_in_FOvar (Var xn) a);
  intros Hin2; rewrite Hin2 in *. discriminate.
assumption.

simpl in Hex2. case_eq (is_in_FOvar (Var ym) a); intros HH; rewrite HH in *.
  discriminate. assumption.
simpl in Hall. case_eq (is_in_FOvar f a); intros HH; rewrite HH in *.
  discriminate.
case_eq (is_all_diff_FOv a); intros HH2; rewrite HH2 in *.
  assumption. all : try discriminate.

      apply sSahlq_equiv_new_simpl_try3_LP'_pre_predSO_pre_pre in H1. assumption.

      simpl.
      destruct f as [un]. simpl in Hin. case_eq (beq_nat ym un);
        intros HH; rewrite HH in *. discriminate. reflexivity.

        simpl in Hex. case_eq (is_in_FOvar (Var xn) a);
          intros HH; rewrite HH in *. discriminate. reflexivity.

simpl in Hex2. case_eq (is_in_FOvar (Var ym) a); intros HH; rewrite HH in *.
  discriminate. reflexivity.
simpl in Hall. case_eq (is_in_FOvar f a); intros HH; rewrite HH in *. 
  discriminate. reflexivity.

simpl in Hall. case_eq (is_in_FOvar f a); intros HH; rewrite HH in *. 
  discriminate. 
case_eq (is_all_diff_FOv a); intros HH2; rewrite HH2 in *.
  reflexivity. discriminate.

      simpl in Hl. inversion Hl as [Hl'].
 apply IHllv in H2; try assumption.
      destruct f as [un]. simpl in Hin. case_eq (beq_nat ym un);
        intros HH; rewrite HH in *. discriminate. assumption.
simpl in Hex. case_eq (is_in_FOvar (Var xn) a);
  intros Hin2; rewrite Hin2 in *. discriminate.
assumption.

simpl in Hex2. case_eq (is_in_FOvar (Var ym) a); intros HH; rewrite HH in *.
  discriminate. assumption. 

simpl in Hall. case_eq (is_in_FOvar f a); intros HH; rewrite HH in *. 
  discriminate. 
case_eq (is_all_diff_FOv a); intros HH2; rewrite HH2 in *. assumption.
discriminate.
Qed.

(* Lemma sSahlq_equiv_new_simpl_try3_LP'_pre_predSO_pre_pre_NEW : 
forall a f xn W Iv Ip Ir,
(*  is_in_FOvar (Var ym) (f :: nil) = false -> *)
(* is_in_FOvar (Var xn) a = false ->
is_in_FOvar (Var ym) a = false -> *)
is_in_FOvar f a = false ->
 is_all_diff_FOv a = true -> 
(* is_in_FOvar (Var xn) a = false -> *)
sSahlq_pa_pre5 Ir a (Iv f) (Iv (Var xn)) <->
SOturnst W Iv Ip Ir (fun4' f (Var xn) a).
Proof.
  induction a; intros [zn] xn W Iv Ip Ir Hin2 Hall (* Hin1 *).
    unfold sSahlq_pa_pre5. simpl. apply iff_refl.

    destruct a as [un]. simpl fun4'.
    unfold sSahlq_pa_pre5. simpl sSahlq_pa_pre5_pre.
    simpl in Hin2.  apply if_then_else_tf in Hin2.
    destruct Hin2 as [Hin3 Hin4].
(*     apply is_in_FOvar_cons_f in Hin1.
    destruct Hin1 as [Hin1a Hin1b]. *)
    rewrite SOturnst_exFO. split; intros [d SOt].
      exists d. rewrite SOturnst_conjSO.
      apply conj.
        simpl. rewrite <- beq_nat_refl.
        rewrite beq_nat_comm. rewrite Hin3. apply SOt.

        simpl in Hall.
        case_eq (is_in_FOvar (Var un) a0 );
          intros Hin5; rewrite Hin5 in *. discriminate.
        apply IHa; try assumption.
        simpl. rewrite <- beq_nat_refl.
        rewrite FOvar_neq. apply SOt.
        apply not_eq_sym. assumption.


      exists d. rewrite SOturnst_conjSO in SOt.
      apply conj.
        simpl in SOt. rewrite <- beq_nat_refl in SOt.
        rewrite beq_nat_comm in SOt. rewrite Hin3 in SOt. apply SOt.

        simpl in Hall.
        case_eq (is_in_FOvar (Var un) a0 );
          intros Hin5; rewrite Hin5 in *. discriminate.
        destruct SOt as [SOt1 SOt2].
        apply IHa in SOt2; try assumption.
        simpl in SOt2. rewrite <- beq_nat_refl in SOt2.
        rewrite FOvar_neq in SOt2. assumption.
        apply not_eq_sym. assumption.
Qed. *)

Lemma sSahlq_equiv_new_simpl_try3_LP'_pre_predSO_pre_pre_NEW : 
forall a f xn W Iv Ip Ir,
(*  is_in_FOvar (Var ym) (f :: nil) = false -> *)
(* is_in_FOvar (Var xn) a = false ->
is_in_FOvar (Var ym) a = false -> *)
is_in_FOvar f a = false ->
 is_all_diff_FOv a = true -> 
is_in_FOvar (Var xn) a = false ->
sSahlq_pa_pre5 Ir a (Iv f) (Iv (Var xn)) <->
SOturnst W Iv Ip Ir (fun4' f (Var xn) a).
Proof.
  induction a; intros [zn] xn W Iv Ip Ir Hin2 Hall Hin1.
    unfold sSahlq_pa_pre5. simpl. apply iff_refl.

    destruct a as [un]. simpl fun4'.
    unfold sSahlq_pa_pre5. simpl sSahlq_pa_pre5_pre.
    simpl in Hin2.  apply if_then_else_tf in Hin2.
    destruct Hin2 as [Hin3 Hin4].
    apply is_in_FOvar_cons_f in Hin1.
    destruct Hin1 as [Hin1a Hin1b].
    rewrite SOturnst_exFO. split; intros [d SOt].
      exists d. rewrite SOturnst_conjSO.
      apply conj.
        simpl. rewrite <- beq_nat_refl.
        rewrite beq_nat_comm. rewrite Hin3. apply SOt.

        simpl in Hall.
        case_eq (is_in_FOvar (Var un) a0 );
          intros Hin5; rewrite Hin5 in *. discriminate.
        apply IHa; try assumption.
        simpl. rewrite <- beq_nat_refl.
        rewrite FOvar_neq. apply SOt.
        apply not_eq_sym. assumption.


      exists d. rewrite SOturnst_conjSO in SOt.
      apply conj.
        simpl in SOt. rewrite <- beq_nat_refl in SOt.
        rewrite beq_nat_comm in SOt. rewrite Hin3 in SOt. apply SOt.

        simpl in Hall.
        case_eq (is_in_FOvar (Var un) a0 );
          intros Hin5; rewrite Hin5 in *. discriminate.
        destruct SOt as [SOt1 SOt2].
        apply IHa in SOt2; try assumption.
        simpl in SOt2. rewrite <- beq_nat_refl in SOt2.
        rewrite FOvar_neq in SOt2. assumption.
        apply not_eq_sym. assumption.
Qed.
(*
Lemma sSahlq_equiv_new_simpl_try3_LP'_pre_predSO_pre_pre_NEW2 : 
forall a f xn W Iv Ip Ir,
(*  is_in_FOvar (Var ym) (f :: nil) = false -> *)
(* is_in_FOvar (Var xn) a = false ->
is_in_FOvar (Var ym) a = false -> *)
is_in_FOvar f a = false ->
 is_all_diff_FOv a = true -> 
(* is_in_FOvar (Var xn) a = false -> *)
sSahlq_pa_pre5 Ir a (Iv f) (Iv (Var xn)) <->
SOturnst W Iv Ip Ir (fun4' f (Var xn) a).
Proof.
  induction a; intros [zn] xn W Iv Ip Ir Hin2 Hall (* Hin1 *).
    unfold sSahlq_pa_pre5. simpl. apply iff_refl.

    destruct a as [un]. simpl fun4'.
    unfold sSahlq_pa_pre5. simpl sSahlq_pa_pre5_pre.
    simpl in Hin2.  apply if_then_else_tf in Hin2.
    destruct Hin2 as [Hin3 Hin4].
(*     apply is_in_FOvar_cons_f in Hin1.
    destruct Hin1 as [Hin1a Hin1b]. *)
    rewrite SOturnst_exFO. split; intros [d SOt].
      exists d. rewrite SOturnst_conjSO.
      apply conj.
        simpl. rewrite <- beq_nat_refl.
        rewrite beq_nat_comm. rewrite Hin3. apply SOt.

        simpl in Hall.
        case_eq (is_in_FOvar (Var un) a0 );
          intros Hin5; rewrite Hin5 in *. discriminate.
        apply IHa; try assumption.
        simpl. rewrite <- beq_nat_refl.
        rewrite FOvar_neq. apply SOt.
        apply not_eq_sym. assumption.


      exists d. rewrite SOturnst_conjSO in SOt.
      apply conj.
        simpl in SOt. rewrite <- beq_nat_refl in SOt.
        rewrite beq_nat_comm in SOt. rewrite Hin3 in SOt. apply SOt.

        simpl in Hall.
        case_eq (is_in_FOvar (Var un) a0 );
          intros Hin5; rewrite Hin5 in *. discriminate.
        destruct SOt as [SOt1 SOt2].
        apply IHa in SOt2; try assumption.
        simpl in SOt2. rewrite <- beq_nat_refl in SOt2.
        rewrite FOvar_neq in SOt2. assumption.
        apply not_eq_sym. assumption.
Qed.
*)
(*   induction a; intros [zn] xn ym W Iv Ip Ir Hin (* Hin2 Hin3 Hin4 Hall *);
    simpl in Hin; apply if_then_else_true_false in Hin.
    simpl. rewrite <- beq_nat_refl. rewrite Hin.
    unfold sSahlq_pa_pre5. simpl. apply iff_refl. 

    simpl. destruct a as [un]. rewrite Hin.
    unfold sSahlq_pa_pre5. simpl.
    case_eq (beq_nat ym un); intros Hbeq.   
      rewrite SOturnst_exFO.
      split; intros [d SOt].
        exists d. rewrite SOturnst_conjSO.
        apply conj. simpl. rewrite <- beq_nat_refl.
        
        simpl.
    simpl.
     
    simpl in Hall. case_eq (is_in_FOvar (Var un) a0);
      intros Hin5; rewrite Hin5 in *. discriminate.
    unfold Iv_ify. unfold sSahlq_pa_pre5.
    simpl in Hin. 
    case_eq (beq_nat ym zn); intros Hbeq. rewrite Hbeq in *.
      discriminate.
    simpl in Hin3. 
    case_eq (beq_nat ym un); intros Hbeq4; rewrite Hbeq4 in *.
      discriminate.

      simpl. rewrite <- beq_nat_refl.
      simpl in Hin4. case_eq (beq_nat zn un); intros Hbeq5;
        rewrite Hbeq5 in *. discriminate.
      split ;intros H.
        destruct H as [v H].
        exists v. apply conj.
        rewrite beq_nat_comm. rewrite Hbeq5.

          apply H.

        apply IHa. simpl. rewrite Hbeq4. reflexivity.
simpl in Hin2. case_eq (beq_nat xn un); intros Hbeq3;
  rewrite Hbeq3 in *. discriminate. assumption.
assumption.
assumption.
assumption.
        unfold sSahlq_pa_pre5.
        rewrite <- beq_nat_refl.
simpl in Hin2. case_eq (beq_nat xn un); intros Hbeq3;
  rewrite Hbeq3 in *. discriminate.
rewrite beq_nat_comm. rewrite Hbeq3.
(*         case_eq (beq_nat un xn); intros Hbeq3.
admit. *)
            apply H.

        destruct H as [v H].
        exists v. apply conj.
        rewrite beq_nat_comm in H. rewrite Hbeq5 in H.

          apply H.

        destruct H as [H1 H2]. apply IHa in H2.
simpl in Hin2. rewrite <- beq_nat_refl in H2.
 rewrite beq_nat_comm in H2. case_eq (beq_nat xn un); intros Hbeq3;
  rewrite Hbeq3 in *. discriminate. assumption.
  simpl. rewrite Hbeq4. reflexivity.

simpl in Hin2. case_eq (beq_nat xn un); intros Hbeq3;
 rewrite Hbeq3 in *. discriminate. assumption.
all : try assumption.
Qed. *)

Fixpoint length_id_1 {A : Type} (l1 l2 : (list A)) : bool :=
  match l1, l2 with
  | nil, nil => true
  | cons _ _, nil => false
  | nil, _ => false
  | cons a1 l1', cons a2 l2' => length_id_1 l1' l2'
  end.

Fixpoint length_id_1_gen {A B : Type} (l1 : (list A)) (l2 : list B) : bool :=
  match l1, l2 with
  | nil, nil => true
  | cons _ _, nil => false
  | nil, _ => false
  | cons a1 l1', cons a2 l2' => length_id_1_gen l1' l2'
  end.


Fixpoint length_id_2 {A : Type} (l1 l2 : list (list A)) : bool :=
  match l1, l2 with
  | nil, nil => true
  | cons _ _, nil => true
  | nil, _ => true
  | cons a1 l1', cons a2 l2' => if length_id_1 a1 a2 then
    length_id_2 l1' l2' else false
  end.

Fixpoint length_id_2_gen {A B : Type} (l1 : list (list A)) (l2 : list (list B)) : bool :=
  match l1, l2 with
  | nil, nil => true
  | cons _ _, nil => true
  | nil, _ => true
  | cons a1 l1', cons a2 l2' => if length_id_1_gen a1 a2 then
    length_id_2_gen l1' l2' else false
  end.

(* Left it here 12/12
Try defining general definitiion of closed_except for any finite number of
FOvars.
Then try proving lemtry2.

There may be a problem with getting our variable lists directly from alpha,
but I don't think there should be because of the closed nature of the formulas
we're instantiating with. *)

Fixpoint free_FO_l (alpha : SecOrder) (lx : list FOvariable)  : bool :=
  match lx with
  | nil => true
  | cons x lx' => if free_FO alpha x then free_FO_l alpha lx' else false
  end.

 Definition closed_except_gen (alpha : SecOrder) (l: list FOvariable) : Prop :=
  free_FO_l alpha l = true /\
  forall y, is_in_FOvar y l = false -> free_FO alpha y = false.

Lemma closed_except_gen_relatSO : forall x y,
  closed_except_gen (relatSO x y) (cons x (cons y nil)).
Proof.
  intros [xn] [ym].
  unfold closed_except_gen.
  simpl. 
  do 2 rewrite <- beq_nat_refl.
  apply conj.
    case_eq (beq_nat ym xn); intros Hbeq; reflexivity.
    intros [zn] H.
    case_eq (beq_nat zn xn); intros Hbeq2; rewrite Hbeq2 in *.
      discriminate.
    apply if_then_else_true_false in H. assumption.
Qed.

Lemma is_in_FOvar_fun4'_1 : forall l x y,
  is_in_FOvar x l = false ->
  free_FO (fun4' x y l) x = true.
Proof.
  induction l ;intros [xn] [ym] Hin.
    simpl in *. rewrite <- beq_nat_refl. reflexivity.

    destruct a as [un].
    apply is_in_FOvar_cons_f in Hin.
    destruct Hin as [Hin1 Hin2].
    simpl. rewrite (FOvar_neq xn un).
    rewrite <- beq_nat_refl. reflexivity.
    assumption.
Qed.

Lemma is_in_FOvar_fun4'_2 : forall l x y,
  is_in_FOvar y l = false ->
  free_FO (fun4' x y l) y = true.
Proof.
  induction l ;intros [xn] [ym] Hin.
    simpl in *. rewrite <- beq_nat_refl.
    rewrite if_then_else_same. reflexivity.

    destruct a as [un].
    apply is_in_FOvar_cons_f in Hin.
    destruct Hin as [Hin1 Hin2].
    simpl. rewrite (FOvar_neq ym un).
    case_eq (beq_nat ym xn); intros Hbeq. reflexivity.
    apply IHl. all : assumption.
Qed.

Lemma free_FO__l_2 : forall alpha x y,
  free_FO alpha x = true ->
  free_FO alpha y = true ->
  free_FO_l alpha (cons x (cons y nil)) = true.
Proof.
  intros alpha [xn] [ym] H1 H2.
  simpl. rewrite H1. rewrite H2. reflexivity.
Qed.

Lemma free_FO_fun4'_not : forall l x y,
forall y0 : FOvariable, is_in_FOvar y0 (x :: y :: nil) = false -> free_FO (fun4' x y l) y0 = false.
Proof.
  induction l; intros [xn] [ym] [zn] Hin.
    simpl in *. case_eq (beq_nat zn xn); intros Hbeq; rewrite Hbeq in *.
      discriminate.
    apply if_then_else_true_false in Hin. assumption.

    simpl in *. destruct a as [un].
    case_eq (beq_nat zn xn); intros Hbeq; rewrite Hbeq in *. discriminate.
    case_eq (beq_nat zn un); intros Hbeq2. reflexivity.
    apply IHl. apply if_then_else_true_false in Hin. rewrite Hin.
    rewrite Hbeq2. reflexivity.
Qed.

Lemma closed_except_fun4' : forall l x y,
  is_in_FOvar x l = false ->
  is_in_FOvar y l = false ->
  closed_except_gen (fun4' x y l) (cons x (cons y nil)).
Proof.
  unfold closed_except_gen.
  intros l x y Hin1 Hin2.
  apply conj.
    apply free_FO__l_2.
      apply is_in_FOvar_fun4'_1. assumption.
      apply is_in_FOvar_fun4'_2. assumption.

    apply free_FO_fun4'_not.
Qed.

Lemma x_occ_in_alpha_fun4' : forall l x a b,
  ~ x = a ->
  ~ x = b ->
  is_in_FOvar x l = false ->
(x_occ_in_alpha (fun4' a b l) x) = false.
Proof.
  induction l; intros [xn] [an] [bn] Hnot1 Hno2 Hin.
    simpl in *. rewrite FOvar_neq. apply FOvar_neq.
    all : try assumption.

    apply is_in_FOvar_cons_f in Hin. destruct Hin as [Hin1 Hin2].
    simpl in *. destruct a as [un].
    rewrite (FOvar_neq _ _ Hin2).
    rewrite (FOvar_neq _ _ Hnot1).
    apply IHl; try assumption.
Qed.

Fixpoint max_FOv_l (l : list FOvariable) : nat :=
  match l with
  | nil => 0
  | cons (Var ym) l' => max ym (max_FOv_l l')
  end.

Lemma lem12 : forall l n,
  Nat.leb (S(max_FOv_l l)) n = true ->
  is_in_FOvar (Var n) l = false.
Proof.
  induction l; intros n H. reflexivity.
  destruct a. simpl. case_eq (beq_nat n n0);
    intros Hbeq.
    simpl max_FOv_l in H.
    rewrite PeanoNat.Nat.succ_max_distr in H.
    rewrite <- (beq_nat_true _ _ Hbeq) in H.
    rewrite max_comm in H. rewrite leb_max_suc in H.
    discriminate.


    simpl max_FOv_l in H. 
    destruct (max_or n0 (max_FOv_l l)) as [H1 | H2].
      rewrite H1 in *. apply max_leb_r in H1.
      rewrite <- leb_defn_suc in H1.
      pose proof (leb_trans _ _ _ H1 H) as H3.
      apply (IHl _ H3).

      rewrite H2 in H. apply IHl. assumption.
Qed.

Lemma lem13 : forall l2 x y,
  Nat.leb (max_FOv_l l2) (max_FOv (fun4' x y l2)) = true.
Proof.
  induction l2; intros [xn] [ym]. reflexivity.
  simpl. destruct a as [zn].
  rewrite (max_comm _ (max_FOv_l l2)).  
  rewrite (max_comm _ (max (max xn zn) _)) .
  apply leb_max_max.
  destruct (max_or (max xn zn) (max_FOv (fun4' (Var zn) (Var ym) l2))) as [H | H];
    rewrite H. apply max_leb_r in H. 
    apply (leb_trans _ _ _ (IHl2 _ _) H).

    apply IHl2.
Qed.

Lemma lemtry5 : forall l x y alpha,
is_in_FOvar (Var (new_FOv_pp_pre2 (conjSO alpha (fun4' x y l)))) l = false.
Proof.
  unfold new_FOv_pp_pre2.
  intros l x y alpha.
  apply lem12.
  simpl. rewrite max_comm. apply leb_max_suc3.
  apply lem13.
Qed.

Lemma lemtry6 : forall l x y alpha,
is_in_FOvar (Var (new_FOv_pp_pre2 (conjSO (fun4' x y l) alpha))) l = false.
Proof.
  unfold new_FOv_pp_pre2.
  intros l x y alpha.
  apply lem12.
  simpl. apply leb_max_suc3.
  apply lem13.
Qed.

Lemma lemtry3  : forall l b c xn W Iv Ip Ir d,
  ~ b = xn ->
  ~ c = xn ->
  is_in_FOvar b l = false ->
  is_in_FOvar c l = false ->
  SOturnst W (alt_Iv Iv d b) Ip Ir (fun4' b xn l) ->
  SOturnst W (alt_Iv Iv d c) Ip Ir (fun4' c xn l).
Proof.
  induction l; intros [bn] [cn] [xn] W Iv Ip Ir d Hnot1 Hnot2 Hin1 Hin2 SOt.
    simpl in *. rewrite <- beq_nat_refl in *.
    rewrite FOvar_neq. rewrite FOvar_neq in SOt.
    all : try assumption.

    simpl fun4' in *. destruct a as [an].
    apply is_in_FOvar_cons_f in Hin1.
    apply is_in_FOvar_cons_f in Hin2. 
    destruct Hin1 as [Hin1a Hin1b].
    destruct Hin2 as [Hin2a Hin2b].
    rewrite SOturnst_exFO in *.
    destruct SOt as [d2 SOt].
    exists d2. rewrite SOturnst_conjSO in *.
    destruct SOt as [SOt1 SOt2].
    apply conj.
      simpl in *. do 2 rewrite <- beq_nat_refl in *.
      rewrite beq_nat_comm. rewrite FOvar_neq.
      rewrite beq_nat_comm in SOt1. rewrite FOvar_neq in SOt1.
      all : try assumption.
      rewrite alt_Iv_switch.
      rewrite alt_Iv_switch in SOt2.
      apply (hopeful4 _ _ (Var bn)).
        apply x_occ_in_alpha_fun4'; assumption.

      rewrite rename_FOv_not_occ. all : try assumption.
        apply x_occ_in_alpha_fun4'; assumption.
Qed.

Lemma max_FOv_fun4' : forall l xn ym,
  max_FOv (fun4' (Var xn) (Var ym) l) = max xn (max ym (max_FOv_l l)).
Proof.
  induction l; intros xn ym.
    simpl. rewrite PeanoNat.Nat.max_0_r.
    reflexivity.

    simpl. destruct a as [zn].
    rewrite IHl. rewrite (max_comm xn zn).
    rewrite (PeanoNat.Nat.max_assoc zn (max zn xn)).
    rewrite (PeanoNat.Nat.max_assoc zn zn xn).
    rewrite max_refl. rewrite (max_comm zn xn).
    rewrite <- (PeanoNat.Nat.max_assoc xn zn).
    rewrite (PeanoNat.Nat.max_assoc zn zn).
    rewrite max_refl. rewrite (PeanoNat.Nat.max_assoc zn ym).
    rewrite (max_comm zn ym). 
    rewrite <-  (PeanoNat.Nat.max_assoc ym zn).
    reflexivity.
Qed.


Lemma lemtry4 : forall l x z beta,
Var (new_FOv_pp_pre2 (conjSO (fun4' x z l) beta)) <> z.
Proof.
  unfold new_FOv_pp_pre2. simpl.
  intros l [xn] [zn] beta H.
  inversion H as [H'].
  destruct zn. discriminate.
  inversion H' as [H''].
  rewrite max_FOv_fun4' in H''.
  apply max_leb_l in H''.
  rewrite (PeanoNat.Nat.max_assoc xn) in H''.
  rewrite (max_comm xn) in H''.
  rewrite <- (PeanoNat.Nat.max_assoc _ xn) in H''.
  rewrite (max_comm (S zn)) in H''.
  rewrite leb_max_suc in H''. discriminate.
Qed.


Lemma lemtry2 : forall a l f z W Iv Ip Ir,
  length a = length l ->
  is_in_FOvar f a = false ->
  is_in_FOvar f l = false ->
  is_in_FOvar z a = false ->
  is_in_FOvar z l = false ->
  is_all_diff_FOv a = true ->
  is_all_diff_FOv l = true ->
  SOturnst W Iv Ip Ir (fun4' f z a) ->
  SOturnst W Iv Ip Ir (fun4' f z l).
Proof.
  induction a; intros l [xn] [zn] W Iv Ip Ir Hl Hin1 Hin2 
      Hin4 Hin5 Hall1 Hall2 SOt.
    destruct l. simpl. assumption.
    discriminate.

    destruct l. discriminate.
    simpl fun4' in *.
    rewrite SOturnst_exFO in *.
    destruct SOt as [d SOt].
    exists d.
    apply is_in_FOvar_cons_f in Hin1.
    apply is_in_FOvar_cons_f in Hin2.
    apply is_in_FOvar_cons_f in Hin4.
    apply is_in_FOvar_cons_f in Hin5.
    destruct Hin1 as [Hin1a Hin1b].
    destruct Hin2 as [Hin2a Hin2b].
    destruct Hin4 as [Hin4a Hin4b].
    destruct Hin5 as [Hin5a Hin5b].
    destruct f as [y1]. destruct a as [y2].
    rewrite SOturnst_conjSO.
    apply conj.
      simpl in *. rewrite <- beq_nat_refl in *.
      rewrite beq_nat_comm.
      rewrite (FOvar_neq _ _ Hin2b) in *.
      rewrite beq_nat_comm in SOt.
      rewrite (FOvar_neq _ _ Hin1b) in *.
      apply SOt.

      simpl in Hall1.
      case_eq (is_in_FOvar (Var y2) a0); intros HH; rewrite HH in *. discriminate.
      simpl in Hall2.
      case_eq (is_in_FOvar (Var y1) l); intros HH2; rewrite HH2 in *. discriminate.
      apply lemtry3 with (b := Var (new_FOv_pp_pre2 (conjSO (fun4' (Var y2) (Var zn) a0) (fun4' (Var y1) (Var zn) l))));
        try assumption.
        apply lemtry4.

    apply not_eq_sym. assumption.
    apply lemtry5.

    apply IHa; try assumption.
      simpl in Hl. inversion Hl. reflexivity.
      apply lemtry6.
      apply lemtry5.

      destruct SOt as [SOt1 SOt2].
      apply lemtry3 with (c := Var (new_FOv_pp_pre2 (conjSO (fun4' (Var y2) (Var zn) a0) (fun4' (Var y1) (Var zn) l)))) in SOt2;
      try assumption.
    apply not_eq_sym. assumption.
      apply lemtry4.
      apply lemtry6.
Qed.

Lemma length_id_1_eq : forall {A : Type} (l1 l2 : list A),
  length_id_1 l1 l2 = true <->
  length l1 = length l2.
Proof.
  intros A. induction l1; intros l2.
    simpl. destruct l2. split; reflexivity.
    split; discriminate.

    simpl. destruct l2. split; discriminate.
    simpl. split; intros H.
      apply IHl1 in H.
      rewrite H. reflexivity.

      apply IHl1. inversion H. reflexivity.
Qed.

(* Lemma length_id_1_eq_gen : forall {A B: Type} (l1 : list A) (l2 : list B),
  length_id_1 l1 l2 = true <->
  length l1 = length l2.
Proof.
  intros A. induction l1; intros l2.
    simpl. destruct l2. split; reflexivity.
    split; discriminate.

    simpl. destruct l2. split; discriminate.
    simpl. split; intros H.
      apply IHl1 in H.
      rewrite H. reflexivity.

      apply IHl1. inversion H. reflexivity.
Qed.
 *)

Lemma lemtry : forall llv llv2 lx1 z W Iv Ip Ir,
length llv = length llv2 ->
length_id_2 llv llv2 = true->
is_all_diff_FOv3 lx1 llv = true ->
is_all_diff_FOv3 lx1 llv2 = true ->
ex_FOvar_x_ll z llv = false ->
ex_FOvar_x_ll z llv2 = false ->
SOturnst W Iv Ip Ir (fun4_l2' lx1 z llv) ->
SOturnst W Iv Ip Ir (fun4_l2' lx1 z llv2).
Proof.
  induction llv; intros llv2 lx1 z W Iv Ip Ir Hl Hl2 H1 H2 H3 H4 SOt.
    simpl in *. destruct llv2. 2 : discriminate.
    destruct lx1. reflexivity. simpl in *;
    destruct lx1; reflexivity.

    simpl in *. destruct llv2. discriminate.
    destruct lx1. reflexivity. simpl in *.
    apply if_then_else_tf in H3.
    apply if_then_else_tf in H4.
    destruct H3 as [H3a H3b].
    destruct H4 as [H4a H4b].
    case_eq (is_in_FOvar f a); intros H1'; rewrite H1' in *.
      discriminate.
    case_eq (is_in_FOvar f l); intros H2'; rewrite H2' in *.
      discriminate.
    case_eq (length_id_1 a l); intros Hl3; rewrite Hl3 in *.
      2 : discriminate.
(*     apply if_then_else_tf in H1. *)
    apply length_id_1_eq in Hl3.
    destruct lx1. simpl in *.
    apply (lemtry2 a); try assumption.
      case_eq (is_all_diff_FOv a); intros HH.
        reflexivity.
      rewrite HH in *. discriminate.

      case_eq (is_all_diff_FOv l); intros HH.
        reflexivity.
      rewrite HH in *. discriminate.

    destruct llv2. destruct llv. 2 : discriminate.
    simpl in *.
    apply (lemtry2 a); try assumption.
      case_eq (is_all_diff_FOv a); intros HH.
        reflexivity.
      rewrite HH in *. discriminate.

      case_eq (is_all_diff_FOv l); intros HH.
        reflexivity.
      rewrite HH in *. discriminate.

    destruct llv. discriminate.
    rewrite SOturnst_disjSO in *.
    destruct SOt as [SOt | SOt].
      left.
      apply (lemtry2 a); try assumption.
        case_eq (is_all_diff_FOv a); intros HH.
          reflexivity.
        rewrite HH in *. discriminate.

        case_eq (is_all_diff_FOv l); intros HH.
          reflexivity.
        rewrite HH in *. discriminate.

      right.
      apply (IHllv); try assumption. 
        simpl in *. inversion Hl. reflexivity.
        case_eq (is_all_diff_FOv a); intros HH;
          rewrite HH in *. 2 : discriminate.
          assumption.

        case_eq (is_all_diff_FOv l); intros HH;
          rewrite HH in *. 2 : discriminate.
          assumption.
Qed.

Lemma sSahlq_equiv_new_simpl_try3_LP'_pre_predSO : forall p f llv lx1 x P W Iv Ip Ir,
length lx1 = length llv ->
ex_FOvar_x_ll f llv = false ->
is_in_FOvar x lx1 = false ->
ex_FOvar_x_ll x llv = false ->
is_all_diff_FOv3 lx1 llv = true ->
SOturnst W Iv (alt_Ip Ip (sSahlq_pa5' Ir llv (map (Iv_ify Iv) lx1)) P) Ir
  (predSO p f) <->
SOturnst W Iv Ip Ir (replace_pred (predSO p f) P x (fun4_l2' lx1 x llv)).
Proof.
  intros [Qm] [xn] llv lx1 x [Pn] W Iv Ip Ir Hl Hex Hin Hin2 Hall.
    simpl in *.
    case_eq (beq_nat Pn Qm); intros Hbeq.

      apply sSahlq_equiv_new_simpl_try3_LP'_pre_predSO_pre; try assumption.

      apply iff_refl.
Qed.

Lemma rep_FOv_fun4'_eq2 : forall l x y u,
  (replace_FOv (fun4' u y l) y x) =
  (replace_FOv (fun4' u x l) y x).
Proof.
  induction l; intros [xn] [ym] [un].
    simpl. rewrite <- beq_nat_refl.
    case_eq (beq_nat ym un); intros Hbeq;
      case_eq (beq_nat ym xn); reflexivity.

    simpl. destruct a as [zn]. 
    case_eq (beq_nat ym un); intros Hbeq;
      case_eq (beq_nat ym zn); intros Hbeq2; 
        rewrite IHl;try reflexivity.
Qed.

Lemma rep_FOv_fun4'_eq1 : forall l x y u,
  (replace_FOv (fun4' y u l) y x) =
  (replace_FOv (fun4' x u l) y x).
Proof.
  induction l; intros [xn] [ym] [un].
    simpl. rewrite <- beq_nat_refl.
    case_eq (beq_nat ym un); intros Hbeq;
      case_eq (beq_nat ym xn); try reflexivity.

    simpl. destruct a as [zn].
    rewrite <- beq_nat_refl. 
    case_eq (beq_nat ym xn); intros Hbeq;
      case_eq (beq_nat ym zn); intros Hbeq2;
        try reflexivity.
Qed.

Lemma rep_FOv_refl : forall alpha x ,
  replace_FOv alpha x x = alpha.
Admitted.

Lemma rep_FOv_fun4'_eq5 : forall l  z1 z2 y x,
  ~ y = z1 ->
  ~ y = z2 ->
  replace_FOv (fun4' z1 z2 l) y x =
  fun4' z1 z2 (rename_FOv_list l y x).
Proof.
  induction l; intros [z1] [z2] [ym] [xn] H1 H2.
    simpl in *. rewrite FOvar_neq.
    rewrite FOvar_neq. reflexivity.
    all : try assumption.

    simpl. destruct a as [un].
    rewrite (FOvar_neq ym z1 H1).
    case_eq (beq_nat ym un); intros Hbeq.
      simpl. rewrite (beq_nat_true _ _ Hbeq) in *.
      rewrite rep_FOv_fun4'_eq1.
Admitted.

Lemma rep_FOv_fun4'_eq4 : forall l x y,
  replace_FOv (fun4' x x l) y x =
  fun4' x x (rename_FOv_list l y x).
Proof.
  induction l; intros [xn] [ym].
    simpl. case_eq (beq_nat ym xn);
      reflexivity.

    simpl in *. destruct a as[zn].
    case_eq (beq_nat ym zn); intros Hbeq;
      case_eq (beq_nat ym xn); intros Hbeq2.
        simpl. rewrite (beq_nat_true _ _ Hbeq) in *.
        rewrite (beq_nat_true _ _ Hbeq2) in *.
        rewrite IHl. reflexivity.

        simpl. rewrite (beq_nat_true _ _ Hbeq) in *.
        rewrite rep_FOv_fun4'_eq1.
        rewrite <- IHl. reflexivity.

      simpl. rewrite (beq_nat_true _ _ Hbeq2).
      rewrite rep_FOv_refl. rewrite rename_FOv_list_refl.
      reflexivity.
Admitted.

Lemma rep_FOv_fun4'_eq3 : forall l x y z,
  ~ z = y ->
  replace_FOv (fun4' z x l) y x =
  fun4' z x (rename_FOv_list l y x).
Proof.
  induction l; intros [xn] [ym] [zn] Hnot.
    simpl.
    rewrite (FOvar_neq ym zn).
    simpl. case_eq (beq_nat ym xn); intros Hbeq;
      reflexivity.

      apply not_eq_sym. assumption.

    simpl in *. destruct a as [un].
    rewrite (FOvar_neq ym zn).
    case_eq (beq_nat ym un); intros Hbeq.
      simpl. rewrite (beq_nat_true _ _ Hbeq).
      rewrite rep_FOv_fun4'_eq1.
Admitted.

Lemma rep_FOv_fun4'_eq6 : forall l x y,
  replace_FOv (fun4' x x l) y x =
  fun4' x x (rename_FOv_list l y x).
Proof.
  induction l; intros [xn] [ym].
    simpl. do 2 rewrite if_then_else_same.
    reflexivity.

    simpl. destruct a as [zn].
    case_eq (beq_nat ym zn); intros Hbeq;
      case_eq (beq_nat ym xn); intros Hbeq2.
        simpl. rewrite <- IHl.
        rewrite (beq_nat_true _ _ Hbeq) in *.
        rewrite (beq_nat_true _ _ Hbeq2) in *.
        reflexivity.

        simpl. rewrite <- IHl.
        rewrite (beq_nat_true _ _ Hbeq).
        rewrite rep_FOv_fun4'_eq1. reflexivity.

        simpl fun4'.
Admitted. 

Lemma trying : forall a xn ym f (W : Set) (Iv : FOvariable  -> W) Ip Ir,
is_in_FOvar (Var ym) (f :: nil) = false ->
is_in_FOvar (Var xn) a = false ->
ex_FOvar_x_ll (Var ym) (a :: nil) = false ->
is_all_diff_FOv3 (f :: nil) (a :: nil) = true ->
sSahlq_pa_pre5 Ir a (Iv f) (Iv (Var xn)) <->
SOturnst W Iv Ip Ir (replace_FOv (fun4' f (Var ym) a) (Var ym) (Var xn)).
Proof.
  induction a; intros xn ym [zn] W Iv Ip Ir H1 Hin2 H2 H3.
    simpl in *. rewrite <- beq_nat_refl.
    case_eq (beq_nat ym zn); intros Hbeq; rewrite Hbeq in *.
      discriminate. apply iff_refl.

    simpl in *. destruct a as [un].
    case_eq (beq_nat ym zn); intros Hbeq; rewrite Hbeq in *.
      discriminate.
    case_eq (beq_nat ym un); intros Hbeq2; rewrite Hbeq2 in *.
      discriminate.
    unfold sSahlq_pa_pre5. simpl sSahlq_pa_pre5_pre.
    rewrite SOturnst_exFO.
    case_eq (beq_nat zn un); intros Hbeq3; rewrite Hbeq3 in *.
      discriminate.
    split; intros [d SOt].
      exists d. rewrite SOturnst_conjSO. apply conj.
        simpl.
        rewrite (beq_nat_comm un zn).
        rewrite <- beq_nat_refl.
        rewrite Hbeq3. apply SOt.

        case_eq (beq_nat xn un); intros Hbeq4; rewrite Hbeq4 in *.
          discriminate.
        apply IHa. rewrite Hbeq2. reflexivity.
        assumption. assumption.
        case_eq (is_in_FOvar (Var zn) a0); intros HH; rewrite HH in *.
          discriminate. assumption.

        simpl. rewrite <- beq_nat_refl. rewrite beq_nat_comm.
        rewrite Hbeq4. apply SOt.

      exists d. rewrite SOturnst_conjSO in SOt. apply conj.
        simpl in *.
        rewrite (beq_nat_comm un zn) in SOt.
        rewrite <- beq_nat_refl in SOt.
        rewrite Hbeq3 in SOt. apply SOt.

        case_eq (beq_nat xn un); intros Hbeq4; rewrite Hbeq4 in *.
          discriminate.
        destruct SOt as [SOt1 SOt2].
        apply IHa in SOt2. simpl in SOt2.
        rewrite <- beq_nat_refl in SOt2.
        rewrite beq_nat_comm in SOt2.
        rewrite Hbeq4 in SOt2. assumption.
        rewrite Hbeq2. reflexivity.
        assumption. assumption.
        case_eq (is_in_FOvar (Var zn) a0); intros HH; rewrite HH in *.
          discriminate. assumption.
Qed.

Lemma lemtry8 : forall llv lx1 beta z P W Iv Ip Ir d,
  free_FO beta z = false ->
(*   length llv = length lx1 -> *)
  SOturnst W Iv (alt_Ip Ip (sSahlq_pa5' Ir llv (map (Iv_ify Iv) lx1)) P) Ir
    beta <->
  SOturnst W (alt_Iv Iv d z) (alt_Ip Ip 
    (sSahlq_pa5' Ir llv (map (Iv_ify (alt_Iv Iv d z)) lx1)) P) Ir
    beta.
Proof.
Admitted.
(*
  induction llv; intros lx1 beta [zn] P W Iv Ip Ir d Hfree.
    simpl sSahlq_pa5' in *. apply alt_Iv_equiv. assumption.

    destruct lx1. simpl sSahlq_pa5' in *.
      destruct llv; apply alt_Iv_equiv; assumption.
      destruct f as [xn]. simpl map. fold (alt_Iv Iv d (Var zn)).
      rewrite sSahlq_pa5'_cons2.
      rewrite sSahlq_pa5'_cons2.
      simpl Iv_ify.

    simpl sSahlq_pa5'.
      destruct llv.
        split; intros SOt.
          apply IHllv.
 apply alt_Iv_equiv; assumption.


 destruct llv.
      
    destruct llv. simpl in *.
Search free_FO alt_Iv.
    simpl in *. 
*)
Lemma rep_FOv_fun4'_eq7 : forall l x y z,
  ~ x = y ->
  is_in_FOvar y l = false ->
  replace_FOv (fun4' x y l) y z =
  fun4' x z l.
Proof.
  induction l; intros [xn] [ym] [zn] Hnot Hin.
    simpl in *. rewrite <- beq_nat_refl. rewrite FOvar_neq.
    reflexivity. apply not_eq_sym. assumption.

    simpl. destruct a as [un].
    rewrite (FOvar_neq ym xn).
    apply is_in_FOvar_cons_f in Hin.
    destruct Hin as [Hin1 Hin2].
    rewrite (FOvar_neq _ _ Hin2).
    rewrite IHl. reflexivity. apply not_eq_sym.
    assumption. assumption.
    apply not_eq_sym. assumption.
Qed.

Lemma rep_FOv_fun4_l2' : forall llv lx1 x y,
  length lx1 = length llv ->
  is_in_FOvar y lx1 = false ->
  ex_FOvar_x_ll y llv = false ->
  ~ lx1 = nil ->
  replace_FOv (fun4_l2' lx1 y llv) y x =
  fun4_l2' lx1 x llv.
Proof.
  induction llv; intros lx1 [xn] [ym] Hl Hin Hex Hnil.
    destruct lx1. contradiction (Hnil eq_refl). discriminate.

    destruct lx1. discriminate.
    destruct lx1. destruct llv. 2 : discriminate.
    apply is_in_FOvar_cons_f in Hin.
    destruct Hin as [Hin1 Hin2].
    simpl. apply rep_FOv_fun4'_eq7.
      apply not_eq_sym. assumption.
      simpl in Hex. 
      case_eq (is_in_FOvar (Var ym) a); intros Hin3; rewrite Hin3 in *.
       discriminate. assumption.

    destruct llv. discriminate.
    remember (cons f0 lx1) as t1.
    remember (cons l llv) as t2.    
    simpl. rewrite Heqt1. rewrite <- Heqt1.
    rewrite Heqt2. rewrite <- Heqt2.
    apply is_in_FOvar_cons_f in Hin.
    destruct Hin as [Hin1 Hin2].
    simpl in Hex. case_eq ( is_in_FOvar (Var ym) a); intros Hin3;
      rewrite Hin3 in *. discriminate.
    apply not_eq_sym in Hin2.
    simpl. rewrite IHllv. rewrite rep_FOv_fun4'_eq7.
    reflexivity.  
    all : try assumption.
    simpl in Hl. inversion Hl. reflexivity.
    rewrite Heqt1. discriminate.
Qed.

Fixpoint ex_att_predSO alpha x : bool := 
  match alpha with
  | predSO _ y => match x, y with Var xn, Var ym => beq_nat xn ym end
  | negSO beta => ex_att_predSO beta x
  | allFO _ beta => ex_att_predSO beta x
  | exFO _ beta => ex_att_predSO beta x
  | conjSO beta1 beta2 => if ex_att_predSO beta1 x then true else ex_att_predSO beta2 x
  | disjSO beta1 beta2 => if ex_att_predSO beta1 x then true else ex_att_predSO beta2 x
  | implSO beta1 beta2 => if ex_att_predSO beta1 x then true else ex_att_predSO beta2 x
  | allSO _ beta => ex_att_predSO beta x
  | exSO _ beta => ex_att_predSO beta x 
  | _ => false
  end.


Fixpoint ex_att_predSO_l alpha l : bool := 
  match l with  
  | nil => false
  | cons x l' => if ex_att_predSO alpha x then true else ex_att_predSO_l alpha l'
  end.

Fixpoint ex_att_predSO_ll alpha ll : bool := 
  match ll with  
  | nil => false
  | cons lx ll' => if ex_att_predSO_l alpha lx then true else ex_att_predSO_ll alpha ll'
  end.


Lemma sSahlq_equiv_new_simpl_try3_LP'_pre_rid_hyp_predSO_pre_pre : forall llv lx1 W Iv Ip Ir xn,
length lx1 = length llv ->
(*  ex_FOvar_x_ll (Var xn) llv = false ->  *)
is_all_diff_FOv3 lx1 llv = true ->
 ex_FOvar_x_ll (Var xn) llv = false ->
sSahlq_pa5' Ir llv (map (Iv_ify Iv) lx1) (Iv (Var xn)) <->
SOturnst W Iv Ip Ir (fun4_l2' lx1 (Var xn) llv).
Proof.
  induction llv; intros until 0; intros Hl Hex Hall.
    destruct lx1. 2 : discriminate.
    simpl in *. split. reflexivity.
    intros. exact I.

    destruct lx1. discriminate.
    simpl in *.
    case_eq llv. intros Hnil.
      destruct lx1.
      destruct f as [zn].
 
      case_eq (is_in_FOvar (Var zn) a ); intros HH1; rewrite HH1 in *.
        discriminate.
      case_eq (is_all_diff_FOv a);intros HH2; rewrite HH2 in *.
        2 : discriminate.
      case_eq (is_in_FOvar (Var xn) a); intros HH3; rewrite HH3 in *.
        discriminate.

      apply sSahlq_equiv_new_simpl_try3_LP'_pre_predSO_pre_pre_NEW;
      try assumption.

      rewrite Hnil in *. discriminate.
  
      intros lv llv' Hllv. rewrite <- Hllv.
      case_eq lx1. intros Hnil. rewrite Hnil in *.
        rewrite Hllv in *. discriminate.
      intros x1 lx1' Hlx1. simpl map. rewrite <- Hlx1.
      simpl.
      case_eq (is_in_FOvar f a ); intros HH1; rewrite HH1 in *.
        discriminate.
      case_eq (is_all_diff_FOv a);intros HH2; rewrite HH2 in *.
        2 : discriminate.
      case_eq (is_in_FOvar (Var xn) a); intros HH3; rewrite HH3 in *.
        discriminate.
      split; intros [SOt1 | SOt2].
        left. 
        apply sSahlq_equiv_new_simpl_try3_LP'_pre_predSO_pre_pre_NEW;
      try assumption.

        right. apply IHllv; try assumption.
inversion Hl. reflexivity.

        rewrite Hlx1. apply SOt2.

        left. 
        apply sSahlq_equiv_new_simpl_try3_LP'_pre_predSO_pre_pre_NEW in SOt1;
      try assumption.

        right. apply IHllv in SOt2; try assumption.
        rewrite Hlx1 in SOt2. apply SOt2.
inversion Hl. reflexivity.
Qed.


Lemma sSahlq_equiv_new_simpl_try3_LP'_pre_rid_hyp_2_predSO_pre : forall llv lx1 W Iv Ip Ir y xn,
length lx1 = length llv ->
is_in_FOvar y lx1 = false ->
(* ex_FOvar_x_ll (Var xn) llv = false -> *)
ex_FOvar_x_ll y llv = false ->
is_all_diff_FOv3 lx1 llv = true ->
(*  ex_FOvar_x_ll (Var xn) llv = false ->  *)
ex_FOvar_x_ll (Var xn) llv = false ->
sSahlq_pa5' Ir llv (map (Iv_ify Iv) lx1) (Iv (Var xn)) <->
SOturnst W Iv Ip Ir (replace_FOv (fun4_l2' lx1 y llv) y (Var xn)).
Proof.
  intros until 0. intros Hl Hin Hex Hall Hex2.
  destruct lx1. destruct llv. 2 : discriminate.
  simpl. destruct y as [ym].
  case_eq (beq_nat ym 1); intros Hbeq.
    split. reflexivity. intros. exact I.
    split. reflexivity. intros. exact I.

  rewrite rep_FOv_fun4_l2'; try assumption.
apply sSahlq_equiv_new_simpl_try3_LP'_pre_rid_hyp_predSO_pre_pre;
try assumption.
discriminate.
Qed.


Fixpoint ex_FOvar_l_ll l llx :=
  match l with
  | nil => false
  | cons x lx' => if ex_FOvar_x_ll x llx then true else ex_FOvar_l_ll lx' llx
  end.


Lemma ex_att_predSO_l_FOvar_x_l : forall lv P x,
  ex_att_predSO_l (predSO P x) lv = false ->
  is_in_FOvar x lv = false.
Proof.
  induction lv; intros P [xn] H. reflexivity.
  simpl in *. destruct a as [ym].
  rewrite beq_nat_comm in H.
  case_eq (beq_nat xn ym); intros Hbeq;
    rewrite Hbeq in H. discriminate.
  apply IHlv in H. assumption.
Qed.

Lemma ex_att_predSO_ll_FOvar_x_ll : forall llv P x,
  ex_att_predSO_ll (predSO P x) llv = false ->
  ex_FOvar_x_ll x llv = false.
Proof.
  induction llv; intros P [xn] H. reflexivity.
  simpl in *. case_eq (ex_att_predSO_l (predSO P (Var xn)) a);
    intros H2; rewrite H2 in *. discriminate.
  apply ex_att_predSO_l_FOvar_x_l in H2. rewrite H2.
  apply IHllv in H. assumption.
Qed.

Lemma sSahlq_equiv_new_simpl_try3_LP'_pre_rid_hyp_2_predSO : forall p f llv lx1 x P W Iv Ip Ir,
length lx1 = length llv ->
(* ex_FOvar_x_ll f llv = false -> *)
is_in_FOvar x lx1 = false ->
ex_FOvar_x_ll x llv = false ->
is_all_diff_FOv3 lx1 llv = true ->
 ex_att_predSO_ll (predSO p f) llv = false ->
SOturnst W Iv (alt_Ip Ip (sSahlq_pa5' Ir llv (map (Iv_ify Iv) lx1)) P) Ir
  (predSO p f) <->
SOturnst W Iv Ip Ir (replace_pred (predSO p f) P x (fun4_l2' lx1 x llv)).
Proof.
  intros [Qm] [ym] llv lx1 x [Pn] W Iv Ip Ir Hl Hin Hex Hall Hex2.
    simpl in *.
    apply ex_att_predSO_ll_FOvar_x_ll in Hex2.
    case_eq (beq_nat Pn Qm); intros Hbeq.
      simpl in Hex2.
      apply sSahlq_equiv_new_simpl_try3_LP'_pre_rid_hyp_2_predSO_pre; try assumption.
      apply iff_refl.
Qed.


Lemma sSahlq_equiv_new_simpl_try3_LP'_pre_relatSO : forall llv lx1 f f0 x P W Iv Ip Ir,
SOturnst W Iv (alt_Ip Ip (sSahlq_pa5' Ir llv (map (Iv_ify Iv) lx1)) P) Ir
  (relatSO f f0) <->
SOturnst W Iv Ip Ir (replace_pred (relatSO f f0) P x (fun4_l2' lx1 x llv)).
Proof.
  intros llv lx1 [z1] [z2] [xn] [Pn] W Iv Ip Ir.
  apply iff_refl.
Qed. 

Lemma sSahlq_equiv_new_simpl_try3_LP'_pre_eqFO : forall llv lx1 f f0 x P W Iv Ip Ir,
SOturnst W Iv (alt_Ip Ip (sSahlq_pa5' Ir llv (map (Iv_ify Iv) lx1)) P) Ir
  (eqFO f f0) <->
SOturnst W Iv Ip Ir (replace_pred (eqFO f f0) P x (fun4_l2' lx1 x llv)).
Proof.
  intros llv lx1 [z1] [z2] [xn] [Pn] W Iv Ip Ir.
  apply iff_refl.
Qed. 

Lemma ex_att_allFO_llv_allFO : forall llv alpha x,
  ex_attached_allFO_llv (allFO x alpha) llv = false ->
  ex_attached_allFO_llv alpha llv = false /\
  ex_FOvar_x_ll x llv = false.
Proof.
  induction llv; intros alpha x H.
    apply conj; reflexivity.
  simpl in *. case_eq (ex_attached_allFO_lv (allFO x alpha) a);
    intros H3; rewrite H3 in *. discriminate.
  apply ex_attached_allFO_lv_allFO in H3. destruct H3 as [HH1 HH2].
  rewrite HH1. rewrite is_in_FO_var. rewrite HH2.
  apply IHllv. assumption.
Qed.

Lemma ex_att_exFO_llv_exFO : forall llv alpha x,
  ex_attached_exFO_llv (exFO x alpha) llv = false ->
  ex_attached_exFO_llv alpha llv = false /\
  ex_FOvar_x_ll x llv = false.
Proof.
  induction llv; intros alpha x H.
    apply conj; reflexivity.
  simpl in *. case_eq (ex_attached_exFO_lv (exFO x alpha) a);
    intros H3; rewrite H3 in *. discriminate.
  apply ex_attached_exFO_lv_exFO in H3. destruct H3 as [HH1 HH2].
  rewrite HH1. rewrite is_in_FO_var. rewrite HH2.
  apply IHllv. assumption.
Qed.

Lemma ex_attached_exFO_lv_allFO2 : forall lv alpha x,
  ex_attached_exFO_lv (allFO x alpha) lv = 
    ex_attached_exFO_lv alpha lv.
Proof.
  induction lv; intros alpha x.
     reflexivity.

    simpl in *. destruct a as [ym]; destruct x as [xn].
    case_eq (attached_exFO_x alpha (Var ym)); intros H2.
      reflexivity.
    apply IHlv with (x := (Var xn)).
Qed.

Lemma ex_attached_allFO_lv_exFO2 : forall lv alpha x,
  ex_attached_allFO_lv (exFO x alpha) lv = 
    ex_attached_allFO_lv alpha lv.
Proof.
  induction lv; intros alpha x.
     reflexivity.

    simpl in *. destruct a as [ym]; destruct x as [xn].
    case_eq (attached_allFO_x alpha (Var ym)); intros H2.
      reflexivity.
    apply IHlv with (x := (Var xn)).
Qed.

Lemma ex_att_exFO_llv_allFO : forall llv x alpha,
ex_attached_exFO_llv (allFO x alpha) llv = 
ex_attached_exFO_llv alpha llv.
Proof.
  induction llv; intros [xn] alpha. reflexivity.
  simpl. rewrite IHllv.
  rewrite ex_attached_exFO_lv_allFO2. reflexivity.
Qed.

Lemma ex_att_allFO_llv_exFO : forall llv alpha x,
  ex_attached_allFO_llv (exFO x alpha) llv = 
  ex_attached_allFO_llv alpha llv.
Proof.
  induction llv; intros alpha x. reflexivity.
  simpl in *.
  rewrite ex_attached_allFO_lv_exFO2.
  rewrite IHllv. reflexivity.
Qed.

Lemma Iv_ify_alt_Iv_not : forall lx1 W Iv d z,
  is_in_FOvar z lx1 = false ->
  map (Iv_ify (@alt_Iv W Iv d z)) lx1 = 
  map (Iv_ify Iv) lx1.
Proof.
  induction lx1; intros W Iv d [zn] Hin. reflexivity.
  destruct a as [xn].
  rewrite map_cons. unfold Iv_ify in *.
  simpl in Hin.
  case_eq (beq_nat zn xn); intros Hbeq; rewrite Hbeq in *.
    discriminate.
  rewrite IHlx1. simpl. rewrite Hbeq. reflexivity.
  assumption.
Qed.

Lemma ex_att_allFO_llv_negSO : forall llv alpha,
ex_attached_allFO_llv (negSO alpha) llv = 
ex_attached_allFO_llv ( alpha) llv.
Proof.
  induction llv; intros alpha. reflexivity.
  simpl. rewrite IHllv. rewrite ex_att_allFO_lv_negSO.
  reflexivity.
Qed.

Lemma ex_att_exFO_llv_negSO : forall llv alpha,
ex_attached_exFO_llv (negSO alpha) llv = 
ex_attached_exFO_llv ( alpha) llv.
Proof.
  induction llv; intros alpha. reflexivity.
  simpl. rewrite IHllv. rewrite ex_att_exFO_lv_negSO.
  reflexivity.
Qed.

Lemma ex_att_allFO_llv_conjSO_f_l : forall llv alpha1 alpha2,
  ex_attached_allFO_llv (conjSO alpha1 alpha2) llv = false ->
  ex_attached_allFO_llv alpha1 llv = false.
Proof.
  induction llv; intros alpha1 alpha2 H. reflexivity.
  simpl in *. 
  case_eq (ex_attached_allFO_lv (conjSO alpha1 alpha2) a);
    intros H2; rewrite H2 in *. discriminate.
  apply ex_att_allFO_lv_conjSO_f in H2.
  destruct H2 as [H3 H4]. rewrite H3.
  apply IHllv with (alpha2 := alpha2).
  assumption.
Qed.

Lemma ex_att_allFO_llv_conjSO_f_r : forall llv alpha1 alpha2,
  ex_attached_allFO_llv (conjSO alpha1 alpha2) llv = false ->
  ex_attached_allFO_llv alpha2 llv = false.
Proof.
  induction llv; intros alpha1 alpha2 H. reflexivity.
  simpl in *. 
  case_eq (ex_attached_allFO_lv (conjSO alpha1 alpha2) a);
    intros H2; rewrite H2 in *. discriminate.
  apply ex_att_allFO_lv_conjSO_f in H2.
  destruct H2 as [H3 H4]. rewrite H4.
  apply IHllv with (alpha1 := alpha1).
  assumption.
Qed.

Lemma ex_att_allFO_llv_conjSO_f_rev : forall llv alpha1 alpha2,
  ex_attached_allFO_llv alpha1 llv = false ->
  ex_attached_allFO_llv alpha2 llv = false ->
  ex_attached_allFO_llv (conjSO alpha1 alpha2) llv = false.
Proof.
  induction llv; intros alpha1 alpha2 H0 H1. reflexivity.
  simpl in *.
  case_eq ( ex_attached_allFO_lv alpha1 a); intros H2;
    rewrite H2 in *. discriminate.
  case_eq ( ex_attached_allFO_lv alpha2 a); intros H3;
    rewrite H3 in *. discriminate.
  rewrite ex_att_allFO_lv_conjSO_f_rev;
  try apply IHllv; assumption.
Qed.

Lemma ex_att_exFO_llv_conjSO_f_rev : forall llv alpha1 alpha2,
  ex_attached_exFO_llv alpha1 llv = false ->
  ex_attached_exFO_llv alpha2 llv = false ->
  ex_attached_exFO_llv (conjSO alpha1 alpha2) llv = false.
Proof.
  induction llv; intros alpha1 alpha2 H0 H1. reflexivity.
  simpl in *.
  case_eq ( ex_attached_exFO_lv alpha1 a); intros H2;
    rewrite H2 in *. discriminate.
  case_eq ( ex_attached_exFO_lv alpha2 a); intros H3;
    rewrite H3 in *. discriminate.
  rewrite ex_att_exFO_lv_conjSO_f_rev;
  try apply IHllv; assumption.
Qed.

Lemma ex_att_allFO_llv_disjSO_f_l : forall llv alpha1 alpha2,
  ex_attached_allFO_llv (disjSO alpha1 alpha2) llv = false ->
  ex_attached_allFO_llv alpha1 llv = false.
Proof.
  induction llv; intros alpha1 alpha2 H. reflexivity.
  simpl in *. 
  case_eq (ex_attached_allFO_lv (disjSO alpha1 alpha2) a);
    intros H2; rewrite H2 in *. discriminate.
  apply ex_att_allFO_lv_disjSO_f in H2.
  destruct H2 as [H3 H4]. rewrite H3.
  apply IHllv with (alpha2 := alpha2).
  assumption.
Qed.

Lemma ex_att_allFO_llv_disjSO_f_r : forall llv alpha1 alpha2,
  ex_attached_allFO_llv (disjSO alpha1 alpha2) llv = false ->
  ex_attached_allFO_llv alpha2 llv = false.
Proof.
  induction llv; intros alpha1 alpha2 H. reflexivity.
  simpl in *. 
  case_eq (ex_attached_allFO_lv (disjSO alpha1 alpha2) a);
    intros H2; rewrite H2 in *. discriminate.
  apply ex_att_allFO_lv_disjSO_f in H2.
  destruct H2 as [H3 H4]. rewrite H4.
  apply IHllv with (alpha1 := alpha1).
  assumption.
Qed.

Lemma ex_att_allFO_llv_implSO_f_l : forall llv alpha1 alpha2,
  ex_attached_allFO_llv (implSO alpha1 alpha2) llv = false ->
  ex_attached_allFO_llv alpha1 llv = false.
Proof.
  induction llv; intros alpha1 alpha2 H. reflexivity.
  simpl in *. 
  case_eq (ex_attached_allFO_lv (implSO alpha1 alpha2) a);
    intros H2; rewrite H2 in *. discriminate.
  apply ex_att_allFO_lv_implSO_f in H2.
  destruct H2 as [H3 H4]. rewrite H3.
  apply IHllv with (alpha2 := alpha2).
  assumption.
Qed.

Lemma ex_att_allFO_llv_implSO_f_r : forall llv alpha1 alpha2,
  ex_attached_allFO_llv (implSO alpha1 alpha2) llv = false ->
  ex_attached_allFO_llv alpha2 llv = false.
Proof.
  induction llv; intros alpha1 alpha2 H. reflexivity.
  simpl in *. 
  case_eq (ex_attached_allFO_lv (implSO alpha1 alpha2) a);
    intros H2; rewrite H2 in *. discriminate.
  apply ex_att_allFO_lv_implSO_f in H2.
  destruct H2 as [H3 H4]. rewrite H4.
  apply IHllv with (alpha1 := alpha1).
  assumption.
Qed.

Lemma ex_att_exFO_llv_conjSO_f_l : forall llv alpha1 alpha2,
  ex_attached_exFO_llv (conjSO alpha1 alpha2) llv = false ->
  ex_attached_exFO_llv alpha1 llv = false.
Proof.
  induction llv; intros alpha1 alpha2 H. reflexivity.
  simpl in *. 
  case_eq (ex_attached_exFO_lv (conjSO alpha1 alpha2) a);
    intros H2; rewrite H2 in *. discriminate.
  apply ex_att_exFO_lv_conjSO_f in H2.
  destruct H2 as [H3 H4]. rewrite H3.
  apply IHllv with (alpha2 := alpha2).
  assumption.
Qed.

Lemma ex_att_exFO_llv_conjSO_f_r : forall llv alpha1 alpha2,
  ex_attached_exFO_llv (conjSO alpha1 alpha2) llv = false ->
  ex_attached_exFO_llv alpha2 llv = false.
Proof.
  induction llv; intros alpha1 alpha2 H. reflexivity.
  simpl in *. 
  case_eq (ex_attached_exFO_lv (conjSO alpha1 alpha2) a);
    intros H2; rewrite H2 in *. discriminate.
  apply ex_att_exFO_lv_conjSO_f in H2.
  destruct H2 as [H3 H4]. rewrite H4.
  apply IHllv with (alpha1 := alpha1).
  assumption.
Qed.

Lemma ex_att_exFO_llv_disjSO_f_l : forall llv alpha1 alpha2,
  ex_attached_exFO_llv (disjSO alpha1 alpha2) llv = false ->
  ex_attached_exFO_llv alpha1 llv = false.
Proof.
  induction llv; intros alpha1 alpha2 H. reflexivity.
  simpl in *. 
  case_eq (ex_attached_exFO_lv (disjSO alpha1 alpha2) a);
    intros H2; rewrite H2 in *. discriminate.
  apply ex_att_exFO_lv_disjSO_f in H2.
  destruct H2 as [H3 H4]. rewrite H3.
  apply IHllv with (alpha2 := alpha2).
  assumption.
Qed.

Lemma ex_att_exFO_llv_disjSO_f_r : forall llv alpha1 alpha2,
  ex_attached_exFO_llv (disjSO alpha1 alpha2) llv = false ->
  ex_attached_exFO_llv alpha2 llv = false.
Proof.
  induction llv; intros alpha1 alpha2 H. reflexivity.
  simpl in *. 
  case_eq (ex_attached_exFO_lv (disjSO alpha1 alpha2) a);
    intros H2; rewrite H2 in *. discriminate.
  apply ex_att_exFO_lv_disjSO_f in H2.
  destruct H2 as [H3 H4]. rewrite H4.
  apply IHllv with (alpha1 := alpha1).
  assumption.
Qed.

Lemma ex_att_exFO_llv_implSO_f_l : forall llv alpha1 alpha2,
  ex_attached_exFO_llv (implSO alpha1 alpha2) llv = false ->
  ex_attached_exFO_llv alpha1 llv = false.
Proof.
  induction llv; intros alpha1 alpha2 H. reflexivity.
  simpl in *. 
  case_eq (ex_attached_exFO_lv (implSO alpha1 alpha2) a);
    intros H2; rewrite H2 in *. discriminate.
  apply ex_att_exFO_lv_implSO_f in H2.
  destruct H2 as [H3 H4]. rewrite H3.
  apply IHllv with (alpha2 := alpha2).
  assumption.
Qed.

Lemma ex_att_exFO_llv_implSO_f_r : forall llv alpha1 alpha2,
  ex_attached_exFO_llv (implSO alpha1 alpha2) llv = false ->
  ex_attached_exFO_llv alpha2 llv = false.
Proof.
  induction llv; intros alpha1 alpha2 H. reflexivity.
  simpl in *. 
  case_eq (ex_attached_exFO_lv (implSO alpha1 alpha2) a);
    intros H2; rewrite H2 in *. discriminate.
  apply ex_att_exFO_lv_implSO_f in H2.
  destruct H2 as [H3 H4]. rewrite H4.
  apply IHllv with (alpha1 := alpha1).
  assumption.
Qed.

Lemma ex_FOvar_l_ll_app_f_l : forall l1 l l2,
ex_FOvar_l_ll (app l1 l2) l = false ->
ex_FOvar_l_ll l1 l = false.
Proof.
  induction l1; intros l l2 H. reflexivity.
  simpl in *.
  case_eq (ex_FOvar_x_ll a l); intros HH; rewrite HH in *.
    discriminate.
  apply IHl1 in H. assumption.
Qed.

Lemma ex_FOvar_l_ll_app_f_r : forall l1 l l2,
ex_FOvar_l_ll (app l1 l2) l = false ->
ex_FOvar_l_ll l2 l = false.
Proof.
  induction l1; intros l l2 H. apply H.
  simpl in *.
  case_eq (ex_FOvar_x_ll a l); intros HH; rewrite HH in *.
    discriminate.
  apply IHl1 in H. assumption.
Qed.

Fixpoint no_bound_FO_l (alpha : SecOrder) (l : list FOvariable) :=
  match l with
  | nil => true
  | cons x l' => if x_occ_in_alpha alpha x then 
(if free_FO alpha x then no_bound_FO_l alpha l' else false) else 
  no_bound_FO_l alpha l'
  end.

Fixpoint list_quant_FOv alpha : list FOvariable :=
  match alpha with
  | allFO x beta => cons x (list_quant_FOv beta)
  | exFO x beta => cons x (list_quant_FOv beta)
  | conjSO beta1 beta2 => app (list_quant_FOv beta1) (list_quant_FOv beta2)
  | disjSO beta1 beta2 => app (list_quant_FOv beta1) (list_quant_FOv beta2)
  | implSO beta1 beta2 => app (list_quant_FOv beta1) (list_quant_FOv beta2)
  | allSO P beta => list_quant_FOv beta
  | exSO P beta => list_quant_FOv beta
  | negSO beta => list_quant_FOv beta
  | _ => nil
  end.

Definition bound_FO alpha x : bool :=
  is_in_FOvar x (list_quant_FOv alpha).

Fixpoint ex_bound_FO_l alpha l : bool :=
  match l with
  | nil => false
  | cons x l' => if bound_FO alpha x then true else ex_bound_FO_l alpha l'
  end.

Fixpoint ex_bound_FO_ll alpha ll : bool :=
  match ll with
  | nil => false
  | cons lx ll' => if ex_bound_FO_l alpha lx then true else ex_bound_FO_ll alpha ll'
  end.

Fixpoint list_quant_FOv_overP alpha : list FOvariable :=
  match alpha with
  | allFO x beta => if is_unary_predless beta then (list_quant_FOv_overP beta)
                        else cons x (list_quant_FOv_overP beta)
  | exFO x beta => if is_unary_predless beta then (list_quant_FOv_overP beta)
                        else cons x (list_quant_FOv_overP beta)
  | conjSO beta1 beta2 => app (list_quant_FOv_overP beta1) (list_quant_FOv_overP beta2)
  | disjSO beta1 beta2 => app (list_quant_FOv_overP beta1) (list_quant_FOv_overP beta2)
  | implSO beta1 beta2 => app (list_quant_FOv_overP beta1) (list_quant_FOv_overP beta2)
  | allSO P beta => list_quant_FOv_overP beta
  | exSO P beta => list_quant_FOv_overP beta
  | negSO beta => list_quant_FOv_overP beta
  | _ => nil
  end.

Definition bound_FO_overP alpha x : bool :=
  is_in_FOvar x (list_quant_FOv_overP alpha).

Fixpoint ex_bound_FO_overP_l alpha l : bool :=
  match l with
  | nil => false
  | cons x l' => if bound_FO_overP alpha x then true else ex_bound_FO_overP_l alpha l'
  end.

Fixpoint ex_bound_FO_overP_ll alpha ll : bool :=
  match ll with
  | nil => false
  | cons lx ll' => if ex_bound_FO_overP_l alpha lx then true else ex_bound_FO_overP_ll alpha ll'
  end.


Lemma bound_FO_conjSO_l : forall alpha1 alpha2 x,
  bound_FO (conjSO alpha1 alpha2) x = false ->
  bound_FO alpha1 x = false.
Proof.
  unfold bound_FO.
  intros alpha1 alpha2 x H.
  simpl in H. apply is_in_FOvar_app_l in H.
  assumption.
Qed.

Lemma bound_FO_conjSO_r : forall alpha1 alpha2 x,
  bound_FO (conjSO alpha1 alpha2) x = false ->
  bound_FO alpha2 x = false.
Proof.
  unfold bound_FO.
  intros alpha1 alpha2 x H.
  simpl in H. apply is_in_FOvar_app_r in H.
  assumption.
Qed.

Lemma bound_FO_disjSO_l : forall alpha1 alpha2 x,
  bound_FO (disjSO alpha1 alpha2) x = false ->
  bound_FO alpha1 x = false.
Proof.
  unfold bound_FO.
  intros alpha1 alpha2 x H.
  simpl in H. apply is_in_FOvar_app_l in H.
  assumption.
Qed.

Lemma bound_FO_disjSO_r : forall alpha1 alpha2 x,
  bound_FO (disjSO alpha1 alpha2) x = false ->
  bound_FO alpha2 x = false.
Proof.
  unfold bound_FO.
  intros alpha1 alpha2 x H.
  simpl in H. apply is_in_FOvar_app_r in H.
  assumption.
Qed.


Lemma bound_FO_implSO_l : forall alpha1 alpha2 x,
  bound_FO (implSO alpha1 alpha2) x = false ->
  bound_FO alpha1 x = false.
Proof.
  unfold bound_FO.
  intros alpha1 alpha2 x H.
  simpl in H. apply is_in_FOvar_app_l in H.
  assumption.
Qed.

Lemma bound_FO_implSO_r : forall alpha1 alpha2 x,
  bound_FO (implSO alpha1 alpha2) x = false ->
  bound_FO alpha2 x = false.
Proof.
  unfold bound_FO.
  intros alpha1 alpha2 x H.
  simpl in H. apply is_in_FOvar_app_r in H.
  assumption.
Qed.

Lemma bound_FO_conjSO : forall alpha1 alpha2 x,
  bound_FO (conjSO alpha1 alpha2) x = false <->
  bound_FO alpha1 x = false /\   bound_FO alpha2 x = false.
Proof.
  unfold bound_FO.
  intros alpha1 alpha2 x. simpl.
  split; intros H. apply conj.
    apply is_in_FOvar_app_l in H. assumption.
    apply is_in_FOvar_app_r in H. assumption.

    destruct H as [H1 H2].
    rewrite is_in_FOvar_app.
    rewrite H1. assumption.
Qed.

Lemma bound_FO_overP_conjSO : forall alpha1 alpha2 x,
  bound_FO_overP (conjSO alpha1 alpha2) x = false <->
  bound_FO_overP alpha1 x = false /\   bound_FO_overP alpha2 x = false.
Proof.
  unfold bound_FO.
  intros alpha1 alpha2 x. simpl.
  split; intros H. apply conj.
    apply is_in_FOvar_app_l in H. assumption.
    apply is_in_FOvar_app_r in H. assumption.

    destruct H as [H1 H2].
    unfold bound_FO_overP in *. simpl in *.
    rewrite is_in_FOvar_app. rewrite H1. assumption.
Qed.

Lemma bound_FO_disjSO : forall alpha1 alpha2 x,
  bound_FO (disjSO alpha1 alpha2) x = false <->
  bound_FO alpha1 x = false /\   bound_FO alpha2 x = false.
Proof.
  unfold bound_FO.
  intros alpha1 alpha2 x. simpl.
  split; intros H. apply conj.
    apply is_in_FOvar_app_l in H. assumption.
    apply is_in_FOvar_app_r in H. assumption.

    destruct H as [H1 H2].
    rewrite is_in_FOvar_app.
    rewrite H1. assumption.
Qed.

Lemma bound_FO_implSO : forall alpha1 alpha2 x,
  bound_FO (implSO alpha1 alpha2) x = false <->
  bound_FO alpha1 x = false /\   bound_FO alpha2 x = false.
Proof.
  unfold bound_FO.
  intros alpha1 alpha2 x. simpl.
  split; intros H. apply conj.
    apply is_in_FOvar_app_l in H. assumption.
    apply is_in_FOvar_app_r in H. assumption.

    destruct H as [H1 H2].
    rewrite is_in_FOvar_app.
    rewrite H1. assumption.
Qed.

Lemma bound_FO_overP_disjSO : forall alpha1 alpha2 x,
  bound_FO_overP (disjSO alpha1 alpha2) x = false <->
  bound_FO_overP alpha1 x = false /\   bound_FO_overP alpha2 x = false.
Proof.
  unfold bound_FO.
  intros alpha1 alpha2 x. simpl.
  split; intros H. apply conj.
    apply is_in_FOvar_app_l in H. assumption.
    apply is_in_FOvar_app_r in H. assumption.

    destruct H as [H1 H2].
    unfold bound_FO_overP in *. simpl.
    rewrite is_in_FOvar_app.
    rewrite H1. assumption.
Qed.

Lemma bound_FO_overP_implSO : forall alpha1 alpha2 x,
  bound_FO_overP (implSO alpha1 alpha2) x = false <->
  bound_FO_overP alpha1 x = false /\   bound_FO_overP alpha2 x = false.
Proof.
  unfold bound_FO.
  intros alpha1 alpha2 x. simpl.
  split; intros H. apply conj.
    apply is_in_FOvar_app_l in H. assumption.
    apply is_in_FOvar_app_r in H. assumption.

    destruct H as [H1 H2].
    unfold bound_FO_overP in *.
    simpl.
    rewrite is_in_FOvar_app.
    rewrite H1. assumption.
Qed.

Lemma ex_bound_FO_l_conjSO_l : forall l alpha1 alpha2,
  ex_bound_FO_l (conjSO alpha1 alpha2) l = false ->
  ex_bound_FO_l alpha1 l = false.
Proof.
  induction l; intros alpha1 alpha2 H.
    simpl in *. assumption.

    simpl in *.
    case_eq (bound_FO (conjSO alpha1 alpha2) a); intros Hb;
      rewrite Hb in *. discriminate.
      apply bound_FO_conjSO in Hb. destruct Hb as [H1 H2].
      rewrite H1. apply IHl in H. assumption.
Qed.

Lemma ex_bound_FO_l_conjSO_r : forall l alpha1 alpha2,
  ex_bound_FO_l (conjSO alpha1 alpha2) l = false ->
  ex_bound_FO_l alpha2 l = false.
Proof.
  induction l; intros alpha1 alpha2 H.
    simpl in *. assumption.

    simpl in *.
    case_eq (bound_FO (conjSO alpha1 alpha2) a); intros Hb;
      rewrite Hb in *. discriminate.
      apply bound_FO_conjSO in Hb. destruct Hb as [H1 H2].
      rewrite H2. apply IHl in H. assumption.
Qed.

Lemma ex_bound_FO_overP_l_conjSO_r : forall l alpha1 alpha2,
  ex_bound_FO_overP_l (conjSO alpha1 alpha2) l = false ->
  ex_bound_FO_overP_l alpha2 l = false.
Proof.
  induction l; intros alpha1 alpha2 H.
    simpl in *. assumption.

    simpl in *.
    case_eq (bound_FO_overP (conjSO alpha1 alpha2) a); intros Hb;
      rewrite Hb in *. discriminate.
      apply bound_FO_overP_conjSO in Hb. destruct Hb as [H1 H2].
      rewrite H2. apply IHl in H. assumption.
Qed.

Lemma ex_bound_FO_overP_l_conjSO_l : forall l alpha1 alpha2,
  ex_bound_FO_overP_l (conjSO alpha1 alpha2) l = false ->
  ex_bound_FO_overP_l alpha1 l = false.
Proof.
  induction l; intros alpha1 alpha2 H.
    simpl in *. assumption.

    simpl in *.
    case_eq (bound_FO_overP (conjSO alpha1 alpha2) a); intros Hb;
      rewrite Hb in *. discriminate.
      apply bound_FO_overP_conjSO in Hb. destruct Hb as [H1 H2].
      rewrite H1. apply IHl in H. assumption.
Qed.

Lemma ex_bound_FO_l_disjSO_l : forall l alpha1 alpha2,
  ex_bound_FO_l (disjSO alpha1 alpha2) l = false ->
  ex_bound_FO_l alpha1 l = false.
Proof.
  induction l; intros alpha1 alpha2 H.
    simpl in *. assumption.

    simpl in *.
    case_eq (bound_FO (disjSO alpha1 alpha2) a); intros Hb;
      rewrite Hb in *. discriminate.
      apply bound_FO_disjSO in Hb. destruct Hb as [H1 H2].
      rewrite H1. apply IHl in H. assumption.
Qed.

Lemma ex_bound_FO_l_disjSO_r : forall l alpha1 alpha2,
  ex_bound_FO_l (disjSO alpha1 alpha2) l = false ->
  ex_bound_FO_l alpha2 l = false.
Proof.
  induction l; intros alpha1 alpha2 H.
    simpl in *. assumption.

    simpl in *.
    case_eq (bound_FO (disjSO alpha1 alpha2) a); intros Hb;
      rewrite Hb in *. discriminate.
      apply bound_FO_disjSO in Hb. destruct Hb as [H1 H2].
      rewrite H2. apply IHl in H. assumption.
Qed.

Lemma ex_bound_FO_overP_l_disjSO_l : forall l alpha1 alpha2,
  ex_bound_FO_overP_l (disjSO alpha1 alpha2) l = false ->
  ex_bound_FO_overP_l alpha1 l = false.
Proof.
  induction l; intros alpha1 alpha2 H.
    simpl in *. assumption.

    simpl in *.
    case_eq (bound_FO_overP (disjSO alpha1 alpha2) a); intros Hb;
      rewrite Hb in *. discriminate.
      apply bound_FO_overP_disjSO in Hb. destruct Hb as [H1 H2].
      rewrite H1. apply IHl in H. assumption.
Qed.

Lemma ex_bound_FO_overP_l_disjSO_r : forall l alpha1 alpha2,
  ex_bound_FO_overP_l (disjSO alpha1 alpha2) l = false ->
  ex_bound_FO_overP_l alpha2 l = false.
Proof.
  induction l; intros alpha1 alpha2 H.
    simpl in *. assumption.

    simpl in *.
    case_eq (bound_FO_overP (disjSO alpha1 alpha2) a); intros Hb;
      rewrite Hb in *. discriminate.
      apply bound_FO_overP_disjSO in Hb. destruct Hb as [H1 H2].
      rewrite H2. apply IHl in H. assumption.
Qed.

Lemma ex_bound_FO_l_implSO_l : forall l alpha1 alpha2,
  ex_bound_FO_l (implSO alpha1 alpha2) l = false ->
  ex_bound_FO_l alpha1 l = false.
Proof.
  induction l; intros alpha1 alpha2 H.
    simpl in *. assumption.

    simpl in *.
    case_eq (bound_FO (implSO alpha1 alpha2) a); intros Hb;
      rewrite Hb in *. discriminate.
      apply bound_FO_implSO in Hb. destruct Hb as [H1 H2].
      rewrite H1. apply IHl in H. assumption.
Qed.

Lemma ex_bound_FO_l_implSO_r : forall l alpha1 alpha2,
  ex_bound_FO_l (implSO alpha1 alpha2) l = false ->
  ex_bound_FO_l alpha2 l = false.
Proof.
  induction l; intros alpha1 alpha2 H.
    simpl in *. assumption.

    simpl in *.
    case_eq (bound_FO (implSO alpha1 alpha2) a); intros Hb;
      rewrite Hb in *. discriminate.
      apply bound_FO_implSO in Hb. destruct Hb as [H1 H2].
      rewrite H2. apply IHl in H. assumption.
Qed.

Lemma ex_bound_FO_overP_l_implSO_l : forall l alpha1 alpha2,
  ex_bound_FO_overP_l (implSO alpha1 alpha2) l = false ->
  ex_bound_FO_overP_l alpha1 l = false.
Proof.
  induction l; intros alpha1 alpha2 H.
    simpl in *. assumption.

    simpl in *.
    case_eq (bound_FO_overP (implSO alpha1 alpha2) a); intros Hb;
      rewrite Hb in *. discriminate.
      apply bound_FO_overP_implSO in Hb. destruct Hb as [H1 H2].
      rewrite H1. apply IHl in H. assumption.
Qed.

Lemma ex_bound_FO_overP_l_implSO_r : forall l alpha1 alpha2,
  ex_bound_FO_overP_l (implSO alpha1 alpha2) l = false ->
  ex_bound_FO_overP_l alpha2 l = false.
Proof.
  induction l; intros alpha1 alpha2 H.
    simpl in *. assumption.

    simpl in *.
    case_eq (bound_FO_overP (implSO alpha1 alpha2) a); intros Hb;
      rewrite Hb in *. discriminate.
      apply bound_FO_overP_implSO in Hb. destruct Hb as [H1 H2].
      rewrite H2. apply IHl in H. assumption.
Qed.



Lemma bound_FO_conjSO_t : forall alpha1 alpha2 x,
  bound_FO (conjSO alpha1 alpha2) x = true ->
  bound_FO alpha1 x = true \/ bound_FO alpha2 x = true.
Proof.
  unfold bound_FO.
  intros until 0. intros H.
  simpl in H.
  rewrite is_in_FOvar_app in H.
  case_eq (is_in_FOvar x (list_quant_FOv alpha1)); intros HH; rewrite HH in *.
    left. reflexivity.

    right. assumption.
Qed.

Lemma ex_bound_FO_l_conjSO : forall l alpha1 alpha2,
  ex_bound_FO_l (conjSO alpha1 alpha2) l = false <->
  ex_bound_FO_l alpha1 l = false /\   ex_bound_FO_l alpha2 l = false.
Proof.
  induction l; intros alpha1 alpha2.
    simpl in *. split. apply conj. all : try reflexivity.

    simpl in *.
    case_eq (bound_FO (conjSO alpha1 alpha2) a); intros Hb.
      apply bound_FO_conjSO_t in Hb.
      destruct Hb as [Hb | Hb]; rewrite Hb.
        split; intros H. discriminate.
          destruct H. discriminate.

        split; intros H. discriminate.
          destruct H. discriminate.

        apply bound_FO_conjSO in Hb.
        destruct Hb as [Hb1 Hb2].
        rewrite Hb1. rewrite Hb2. apply IHl.
Qed.

Lemma free_FO_l_allFO_l : forall lx1 alpha x,
  free_FO_l (allFO x alpha) lx1 = true ->
  is_in_FOvar x lx1 = false.
Proof.
  induction lx1; intros alpha [xn] H. reflexivity.
  destruct a as [ym]. simpl in *.
  rewrite beq_nat_comm.
  case_eq (beq_nat ym xn); intros Hbeq;rewrite Hbeq in *.
    discriminate.
  case_eq (free_FO alpha (Var ym) );intros H2; rewrite H2 in *.
    2 : discriminate.
  apply IHlx1 in H. assumption.
Qed.

Lemma no_bound_FO_l_allFO_l : forall lx1 alpha x,
  no_bound_FO_l (allFO x alpha) lx1 = true ->
  is_in_FOvar x lx1 = false. 
Proof.
  induction lx1; intros alpha [xn] H. reflexivity.
  destruct a as [ym]. simpl in *.
  rewrite beq_nat_comm.
  case_eq (beq_nat ym xn); intros Hbeq;rewrite Hbeq in *.
    discriminate.
  case_eq (free_FO alpha (Var ym) );intros H2; rewrite H2 in *.
    rewrite if_then_else_same in H.
    apply IHlx1 in H. assumption. 

    case_eq (x_occ_in_alpha alpha (Var ym) ); intros H3;
      rewrite H3 in *. discriminate.
    apply IHlx1 in H. assumption.
Qed.

Lemma free_FO_l_allFO_r : forall lx1 alpha x,
  free_FO_l (allFO x alpha) lx1 = true ->
  free_FO_l (alpha) lx1 = true.
Proof.
  induction lx1; intros alpha [xn] H. reflexivity.
  destruct a as [ym]. simpl in *.
  case_eq (beq_nat ym xn); intros Hbeq;rewrite Hbeq in *.
    discriminate.
  case_eq (free_FO alpha (Var ym) );intros H2; rewrite H2 in *.
    2 : discriminate.
  apply IHlx1 in H. assumption.
Qed.

Lemma no_bound_FO_l_allFO_r : forall lx1 alpha x,
  no_bound_FO_l (allFO x alpha) lx1 = true ->
  no_bound_FO_l (alpha) lx1 = true.
Proof.
  induction lx1; intros alpha [xn] H. reflexivity.
  destruct a as [ym]. simpl in *.
  case_eq (beq_nat ym xn); intros Hbeq;rewrite Hbeq in *.
    discriminate.
  case_eq (x_occ_in_alpha alpha (Var ym)); intros Hocc;
    rewrite Hocc in *.
    case_eq (free_FO alpha (Var ym) );intros H2; rewrite H2 in *.
      2 : discriminate.
    apply IHlx1 in H. assumption.

    apply IHlx1 in H. assumption.
Qed.

Lemma bound_FO_allFO_noteq : forall alpha x y,
  ~ x = y ->
  bound_FO (allFO x alpha) y = bound_FO alpha y.
Proof.
  unfold bound_FO. intros alpha [xn] [ym] Hneq.
  simpl. rewrite beq_nat_comm.
  rewrite FOvar_neq. reflexivity. assumption.
Qed.

Lemma bound_FO_allFO_eq : forall alpha x,
  bound_FO (allFO x alpha) x = true.
Proof.
  unfold bound_FO. intros alpha [xn].
  simpl. rewrite <- beq_nat_refl. reflexivity.
Qed.

Lemma bound_FO_exFO_noteq : forall alpha x y,
  ~ x = y ->
  bound_FO (exFO x alpha) y = bound_FO alpha y.
Proof.
  unfold bound_FO. intros alpha [xn] [ym] Hneq.
  simpl. rewrite beq_nat_comm.
  rewrite FOvar_neq. reflexivity. assumption.
Qed.

Lemma bound_FO_exFO_eq : forall alpha x,
  bound_FO (exFO x alpha) x = true.
Proof.
  unfold bound_FO. intros alpha [xn].
  simpl. rewrite <- beq_nat_refl. reflexivity.
Qed.

Lemma ex_bound_FO_l_allFO_r : forall lx1 alpha x,
  ex_bound_FO_l (allFO x alpha) lx1 = false ->
  ex_bound_FO_l (alpha) lx1 = false.
Proof.
  induction lx1; intros alpha [xn] H. reflexivity.
  destruct a as [ym]. simpl in *.
  case_eq (beq_nat xn ym); intros Hbeq. 
    rewrite (beq_nat_true _ _ Hbeq) in *.
    rewrite bound_FO_allFO_eq in H. discriminate.

    rewrite bound_FO_allFO_noteq in H.
    case_eq (bound_FO alpha (Var ym));
      intros Hb; rewrite Hb in H. discriminate.

      apply IHlx1 in H. assumption.
      apply beq_nat_false_FOv. assumption.
Qed.

Lemma ex_bound_FO_l_allFO_l : forall lx1 alpha x,
  ex_bound_FO_l (allFO x alpha) lx1 = false ->
  is_in_FOvar x lx1 = false.
Proof.
  induction lx1; intros alpha [xn] H. reflexivity.
  destruct a as [ym]. simpl in *.
  rewrite beq_nat_comm.
  case_eq (beq_nat ym xn); intros Hbeq.
    rewrite (beq_nat_true _ _ Hbeq) in *.
    rewrite bound_FO_allFO_eq in H. discriminate.

    rewrite bound_FO_allFO_noteq in H.
    apply if_then_else_tf in H.
    apply (IHlx1 alpha). apply H.
    apply beq_nat_false_FOv.
    rewrite beq_nat_comm. assumption.
Qed.

Lemma ex_bound_FO_overP_l_allFO_r : forall lx1 alpha x,
  ex_bound_FO_overP_l (allFO x alpha) lx1 = false ->
  ex_bound_FO_overP_l (alpha) lx1 = false.
Proof.
  induction lx1; intros alpha [xn] H. reflexivity.
  destruct a as [ym]. simpl in *.
  case_eq (beq_nat xn ym); intros Hbeq. 
    rewrite (beq_nat_true _ _ Hbeq) in *.
    unfold bound_FO_overP in *. simpl in *.
    case_eq (is_unary_predless alpha); intros Hun;
      rewrite Hun in *.
      case_eq (is_in_FOvar (Var ym) (list_quant_FOv_overP alpha));
        intros Hin; rewrite Hin in *. discriminate.
      apply IHlx1 in H. assumption.

      simpl in H. rewrite <- beq_nat_refl in H. discriminate.

    unfold bound_FO_overP in *. simpl in *.
    case_eq (is_unary_predless alpha); intros Hun;
      rewrite Hun in *.
      case_eq (is_in_FOvar (Var ym) (list_quant_FOv_overP alpha));
        intros Hin; rewrite Hin in *. discriminate.
      apply IHlx1 in H. assumption.

      simpl in H. rewrite beq_nat_comm in H. rewrite Hbeq in H.
      case_eq (is_in_FOvar (Var ym) (list_quant_FOv_overP alpha));
        intros Hin; rewrite Hin in *. discriminate.
      apply IHlx1 in H. assumption.
Qed.

Lemma ex_bound_FO_overP_l_exFO_r : forall lx1 alpha x,
  ex_bound_FO_overP_l (exFO x alpha) lx1 = false ->
  ex_bound_FO_overP_l (alpha) lx1 = false.
Proof.
  induction lx1; intros alpha [xn] H. reflexivity.
  destruct a as [ym]. simpl in *.
  case_eq (beq_nat xn ym); intros Hbeq. 
    rewrite (beq_nat_true _ _ Hbeq) in *.
    unfold bound_FO_overP in *. simpl in *.
    case_eq (is_unary_predless alpha); intros Hun;
      rewrite Hun in *.
      case_eq (is_in_FOvar (Var ym) (list_quant_FOv_overP alpha));
        intros Hin; rewrite Hin in *. discriminate.
      apply IHlx1 in H. assumption.

      simpl in H. rewrite <- beq_nat_refl in H. discriminate.

    unfold bound_FO_overP in *. simpl in *.
    case_eq (is_unary_predless alpha); intros Hun;
      rewrite Hun in *.
      case_eq (is_in_FOvar (Var ym) (list_quant_FOv_overP alpha));
        intros Hin; rewrite Hin in *. discriminate.
      apply IHlx1 in H. assumption.

      simpl in H. rewrite beq_nat_comm in H. rewrite Hbeq in H.
      case_eq (is_in_FOvar (Var ym) (list_quant_FOv_overP alpha));
        intros Hin; rewrite Hin in *. discriminate.
      apply IHlx1 in H. assumption.
Qed.

Lemma ex_bound_FO_l_exFO_r : forall lx1 alpha x,
  ex_bound_FO_l (exFO x alpha) lx1 = false ->
  ex_bound_FO_l (alpha) lx1 = false.
Proof.
  induction lx1; intros alpha [xn] H. reflexivity.
  destruct a as [ym]. simpl in *.
  case_eq (beq_nat xn ym); intros Hbeq. 
    rewrite (beq_nat_true _ _ Hbeq) in *.
    rewrite bound_FO_exFO_eq in H. discriminate.

    rewrite bound_FO_exFO_noteq in H.
    case_eq (bound_FO alpha (Var ym));
      intros Hb; rewrite Hb in H. discriminate.

      apply IHlx1 in H. assumption.
      apply beq_nat_false_FOv. assumption.
Qed.

Lemma ex_bound_FO_l_exFO_l : forall lx1 alpha x,
  ex_bound_FO_l (exFO x alpha) lx1 = false ->
  is_in_FOvar x lx1 = false.
Proof.
  induction lx1; intros alpha [xn] H. reflexivity.
  destruct a as [ym]. simpl in *.
  rewrite beq_nat_comm.
  case_eq (beq_nat ym xn); intros Hbeq.
    rewrite (beq_nat_true _ _ Hbeq) in *.
    rewrite bound_FO_exFO_eq in H. discriminate.

    rewrite bound_FO_exFO_noteq in H.
    apply if_then_else_tf in H.
    apply (IHlx1 alpha). apply H.
    apply beq_nat_false_FOv.
    rewrite beq_nat_comm. assumption.
Qed.

Lemma bound_FO_negSO : forall alpha x,
  bound_FO (negSO alpha) x = bound_FO alpha x.
Proof.
  unfold bound_FO.
  intros alpha x.
  simpl. reflexivity.
Qed.

Lemma bound_FO_overP_negSO : forall alpha x,
  bound_FO_overP (negSO alpha) x = bound_FO_overP alpha x.
Proof.
  unfold bound_FO.
  intros alpha x.
  simpl. reflexivity.
Qed.

Lemma ex_bound_FO_l_negSO : forall l alpha,
  ex_bound_FO_l (negSO alpha) l = ex_bound_FO_l alpha l.
Proof.
  induction l; intros alpha. reflexivity.
  simpl in *.  rewrite IHl. rewrite bound_FO_negSO.
  reflexivity.
Qed.

Lemma ex_bound_FO_overP_l_negSO : forall l alpha,
  ex_bound_FO_overP_l (negSO alpha) l = ex_bound_FO_overP_l alpha l.
Proof.
  induction l; intros alpha. reflexivity.
  simpl in *.  rewrite IHl. rewrite bound_FO_overP_negSO.
  reflexivity.
Qed.

Lemma no_free_FO_l_allFO_r : forall lx1 alpha x,
  no_free_FO_l (allFO x alpha) lx1 = false ->
  no_free_FO_l (alpha) lx1 = false.
Proof.
  induction lx1; intros alpha [xn] H. discriminate.
  destruct a as [ym]. simpl in *.
  case_eq (beq_nat ym xn); intros Hbeq;rewrite Hbeq in *.
    apply IHlx1 in H. rewrite H. apply if_then_else_false.

    case_eq (free_FO alpha (Var ym) );intros H2; rewrite H2 in *.
      reflexivity.
    apply IHlx1 in H. assumption.
Qed.

Lemma free_FO_l_exFO_l : forall lx1 alpha x,
  free_FO_l (exFO x alpha) lx1 = true ->
  is_in_FOvar x lx1 = false.
Proof.
  induction lx1; intros alpha [xn] H. reflexivity.
  destruct a as [ym]. simpl in *.
  rewrite beq_nat_comm.
  case_eq (beq_nat ym xn); intros Hbeq;rewrite Hbeq in *.
    discriminate.
  case_eq (free_FO alpha (Var ym) );intros H2; rewrite H2 in *.
    2 : discriminate.
  apply IHlx1 in H. assumption.
Qed.

Lemma no_bound_FO_l_exFO_l : forall lx1 alpha x,
  no_bound_FO_l (exFO x alpha) lx1 = true ->
  is_in_FOvar x lx1 = false.
Proof.
  induction lx1; intros alpha [xn] H. reflexivity.
  destruct a as [ym]. simpl in *.
  rewrite beq_nat_comm.
  case_eq (beq_nat ym xn); intros Hbeq;rewrite Hbeq in *.
    discriminate.
  case_eq (x_occ_in_alpha alpha (Var ym)); intros Hocc; rewrite Hocc in *.
  case_eq (free_FO alpha (Var ym) );intros H2; rewrite H2 in *.
    2 : discriminate.
  apply IHlx1 in H. assumption.
  apply IHlx1 in H. assumption.
Qed.

Lemma free_FO_l_exFO_r : forall lx1 alpha x,
  free_FO_l (exFO x alpha) lx1 = true ->
  free_FO_l (alpha) lx1 = true.
Proof.
  induction lx1; intros alpha [xn] H. reflexivity.
  destruct a as [ym]. simpl in *.
  case_eq (beq_nat ym xn); intros Hbeq;rewrite Hbeq in *.
    discriminate.
  case_eq (free_FO alpha (Var ym) );intros H2; rewrite H2 in *.
    2 : discriminate.
  apply IHlx1 in H. assumption.
Qed.

Lemma no_bound_FO_l_exFO_r : forall lx1 alpha x,
  no_bound_FO_l (exFO x alpha) lx1 = true ->
  no_bound_FO_l (alpha) lx1 = true.
Proof.
  induction lx1; intros alpha [xn] H. reflexivity.
  destruct a as [ym]. simpl in *.
  case_eq (beq_nat ym xn); intros Hbeq;rewrite Hbeq in *.
    discriminate.
  case_eq (x_occ_in_alpha alpha (Var ym)); intros Hoc;rewrite Hoc in *.
  case_eq (free_FO alpha (Var ym) );intros H2; rewrite H2 in *.
    2 : discriminate.
  apply IHlx1 in H. assumption.
  apply IHlx1 in H. assumption.
Qed.

Lemma free_FO_l_negSO : forall l alpha,
  free_FO_l (negSO alpha) l = free_FO_l alpha l.
Proof.
  induction l; intros alpha.
    reflexivity.

    simpl. rewrite IHl. reflexivity.
Qed.

Lemma no_bound_FO_l_negSO : forall l alpha,
  no_bound_FO_l (negSO alpha) l = no_bound_FO_l alpha l.
Proof.
  induction l; intros alpha.
    reflexivity.

    simpl. rewrite IHl. reflexivity.
Qed.

Lemma ex_att_predSO_allFO : forall alpha v x,
  ex_att_predSO (allFO x alpha) v = false ->
  ex_att_predSO alpha v = false.
Proof.
  intros alpha [ym] [xn] H.
  simpl in *. assumption.
Qed.

Lemma ex_att_predSO_exFO : forall alpha v x,
  ex_att_predSO (exFO x alpha) v = false ->
  ex_att_predSO alpha v = false.
Proof.
  intros alpha [ym] [xn] H.
  simpl in *. assumption.
Qed.

Lemma ex_att_predSO_negSO : forall alpha v,
  ex_att_predSO (negSO alpha) v = false ->
  ex_att_predSO alpha v = false.
Proof.
  intros alpha [xn] H.
  simpl in *. assumption.
Qed.

Lemma ex_att_predSO_l_allFO : forall lv alpha x,
  ex_att_predSO_l (allFO x alpha) lv = false ->
  ex_att_predSO_l alpha lv = false.
Proof.
  induction lv; intros alpha x H. reflexivity.
  simpl in *. case_eq (ex_att_predSO alpha a);
    intros H2; rewrite H2 in *. discriminate.
  apply IHlv in H. assumption.
Qed.

Lemma ex_att_predSO_l_exFO : forall lv alpha x,
  ex_att_predSO_l (exFO x alpha) lv = false ->
  ex_att_predSO_l alpha lv = false.
Proof.
  induction lv; intros alpha x H. reflexivity.
  simpl in *. case_eq (ex_att_predSO alpha a);
    intros H2; rewrite H2 in *. discriminate.
  apply IHlv in H. assumption.
Qed.

Lemma ex_att_predSO_l_negSO : forall lv alpha,
  ex_att_predSO_l (negSO alpha) lv = false ->
  ex_att_predSO_l alpha lv = false.
Proof.
  induction lv; intros alpha H. reflexivity.
  simpl in *. case_eq (ex_att_predSO alpha a);
    intros H2; rewrite H2 in *. discriminate.
  apply IHlv in H. assumption.
Qed.

Lemma ex_att_predSO_ll_allFO : forall llv alpha x,
  ex_att_predSO_ll (allFO x alpha) llv = false ->
  ex_att_predSO_ll alpha llv = false.
Proof.
  induction llv; intros alpha x H. reflexivity.
  simpl in *. case_eq (ex_att_predSO_l (allFO x alpha) a);
    intros H2; rewrite H2 in *.
    discriminate.
    apply ex_att_predSO_l_allFO in H2. rewrite H2.
    apply IHllv in H. assumption.
Qed.

Lemma ex_att_predSO_ll_exFO : forall llv alpha x,
  ex_att_predSO_ll (exFO x alpha) llv = false ->
  ex_att_predSO_ll alpha llv = false.
Proof.
  induction llv; intros alpha x H. reflexivity.
  simpl in *. case_eq (ex_att_predSO_l (exFO x alpha) a);
    intros H2; rewrite H2 in *.
    discriminate.
    apply ex_att_predSO_l_exFO in H2. rewrite H2.
    apply IHllv in H. assumption.
Qed.

Lemma ex_att_predSO_ll_negSO : forall llv alpha,
  ex_att_predSO_ll (negSO alpha) llv = false ->
  ex_att_predSO_ll alpha llv = false.
Proof.
  induction llv; intros alpha H. reflexivity.
  simpl in *. case_eq (ex_att_predSO_l (negSO alpha) a);
    intros H2; rewrite H2 in *.
    discriminate.
    apply ex_att_predSO_l_negSO in H2. rewrite H2.
    apply IHllv. assumption.
Qed.

Lemma ex_bound_FO_overP_l_allFO_l : forall lx alpha z,
  ex_bound_FO_overP_l (allFO z alpha) lx = false ->
  is_in_FOvar z lx = false \/ is_unary_predless alpha = true.
Proof.
  induction lx; intros alpha z H.
    simpl in *. left. reflexivity.

    simpl in *. destruct z as [zn]. destruct a as [ym].
    unfold bound_FO_overP in *. simpl in *.
    case_eq (is_unary_predless alpha); intros Hun;
      rewrite Hun in *. right. reflexivity.

      left.
      simpl in *. rewrite beq_nat_comm in H.
      case_eq (beq_nat zn ym); intros Hbeq;
        rewrite Hbeq in H. discriminate.

        case_eq (is_in_FOvar (Var ym) (list_quant_FOv_overP alpha));
          intros H2; rewrite H2 in *. discriminate.
        apply IHlx in H. destruct H. assumption.
        rewrite Hun in *. discriminate.
Qed.

Lemma ex_bound_FO_overP_l_exFO_l : forall lx alpha z,
  ex_bound_FO_overP_l (exFO z alpha) lx = false ->
  is_in_FOvar z lx = false \/ is_unary_predless alpha = true.
Proof.
  induction lx; intros alpha z H.
    simpl in *. left. reflexivity.

    simpl in *. destruct z as [zn]. destruct a as [ym].
    unfold bound_FO_overP in *. simpl in *.
    case_eq (is_unary_predless alpha); intros Hun;
      rewrite Hun in *. right. reflexivity.

      left.
      simpl in *. rewrite beq_nat_comm in H.
      case_eq (beq_nat zn ym); intros Hbeq;
        rewrite Hbeq in H. discriminate.

        case_eq (is_in_FOvar (Var ym) (list_quant_FOv_overP alpha));
          intros H2; rewrite H2 in *. discriminate.
        apply IHlx in H. destruct H. assumption.
        rewrite Hun in *. discriminate.
Qed.


Lemma sSahlq_equiv_new_simpl_try3_LP'_pre_rid_hyp_3_allFO_bound_pre : forall llv lx1 alpha P W Iv Ip Ir d z,
  ex_bound_FO_overP_l (allFO z alpha) lx1 = false ->
  SOturnst W (alt_Iv Iv d z) (alt_Ip Ip (sSahlq_pa5' Ir llv
    (map (Iv_ify Iv) lx1)) P) Ir alpha <->
  SOturnst W (alt_Iv Iv d z) (alt_Ip Ip (sSahlq_pa5' Ir llv 
    (map (Iv_ify (alt_Iv Iv d z)) lx1)) P) Ir alpha.
Proof.
  intros until 0. intros H.
  apply ex_bound_FO_overP_l_allFO_l in H.
  destruct H as [H | H].
    rewrite Iv_ify_alt_Iv_not. apply iff_refl. assumption.

    apply (P_occ_in_alpha_un_predless _ P) in H.
    split; intros SOt; apply P_not_occ_alt; apply P_not_occ_alt in SOt.
     all : try assumption.
Qed.


Lemma sSahlq_equiv_new_simpl_try3_LP'_pre_rid_hyp_3_exFO_bound_pre : forall llv lx1 alpha P W Iv Ip Ir d z,
  ex_bound_FO_overP_l (exFO z alpha) lx1 = false ->
  SOturnst W (alt_Iv Iv d z) (alt_Ip Ip (sSahlq_pa5' Ir llv
    (map (Iv_ify Iv) lx1)) P) Ir alpha <->
  SOturnst W (alt_Iv Iv d z) (alt_Ip Ip (sSahlq_pa5' Ir llv 
    (map (Iv_ify (alt_Iv Iv d z)) lx1)) P) Ir alpha.
Proof.
  intros until 0. intros H.
  apply ex_bound_FO_overP_l_exFO_l in H.
  destruct H as [H | H].
    rewrite Iv_ify_alt_Iv_not. apply iff_refl. assumption.

    apply (P_occ_in_alpha_un_predless _ P) in H.
    split; intros SOt; apply P_not_occ_alt; apply P_not_occ_alt in SOt.
     all : try assumption.
Qed.

Lemma sSahlq_equiv_new_simpl_try3_LP'_pre_rid_hyp_3_allFO_bound : forall llv lx1 f alpha x P W Iv Ip Ir,
(forall (llv : list (list FOvariable)) (lx1 : list FOvariable) 
            (x : FOvariable) (P : predicate) (W : Set) (Iv : FOvariable -> W)
            (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop),
         SOQFree alpha = true ->
          length lx1 = length llv ->
          ex_bound_FO_overP_l alpha lx1 = false ->
ex_att_predSO_ll (alpha) llv = false ->
          ex_FOvar_x_ll x llv = false ->
(*           ex_FOvar_l_ll (FOvars_in alpha) llv = false -> *)
          is_in_FOvar x lx1 = false ->
          is_all_diff_FOv3 lx1 llv = true ->
          SOturnst W Iv (alt_Ip Ip (sSahlq_pa5' Ir llv (map (Iv_ify Iv) lx1)) P) Ir
            alpha <-> SOturnst W Iv Ip Ir (replace_pred alpha P x (fun4_l2' lx1 x llv))) ->
SOQFree (allFO f alpha) = true ->
length lx1 = length llv ->
is_in_FOvar x lx1 = false ->
(* ex_FOvar_l_ll (FOvars_in (allFO f alpha)) llv = false -> *)
(* ex_FOvar_l_ll (FOvars_in (allFO f alpha)) (cons lx1 nil) = false -> *)
ex_att_predSO_ll (allFO f alpha) llv = false ->
ex_FOvar_x_ll x llv = false ->
is_all_diff_FOv3 lx1 llv = true ->
ex_bound_FO_overP_l (allFO f alpha) lx1 = false ->
SOturnst W Iv (alt_Ip Ip (sSahlq_pa5' Ir llv (map (Iv_ify Iv) lx1)) P) Ir
  (allFO f alpha) <->
SOturnst W Iv Ip Ir (replace_pred (allFO f alpha) P x (fun4_l2' lx1 x llv)).
Proof.
  intros llv lx1 [zn] alpha [xn] P W Iv Ip Ir IH Hno Hl Hin Hex1 Hin2 (* Hex1 *)  Hall Hf.
  rewrite rep_pred_allFO. do 2 rewrite SOturnst_allFO.
  simpl in Hno.
  simpl in Hin2.
(*  case_eq (ex_FOvar_x_ll (Var zn) llv);
    intros Hex3; rewrite Hex3 in *. discriminate. *)
  simpl in Hf.
  pose proof (ex_bound_FO_overP_l_allFO_r _ _ _ Hf) as Hf2.
  split; intros SOt d; specialize (SOt d).
    apply IH; try assumption.

    apply ex_att_predSO_ll_allFO in Hex1. assumption.

apply sSahlq_equiv_new_simpl_try3_LP'_pre_rid_hyp_3_allFO_bound_pre; try assumption.

(*     rewrite Iv_ify_alt_Iv_not. assumption. *)
(*     apply (ex_bound_FO_l_allFO_l _ _ _ Hf). *)

    apply IH in SOt; try assumption.
apply sSahlq_equiv_new_simpl_try3_LP'_pre_rid_hyp_3_allFO_bound_pre; try assumption.
(* 
    rewrite Iv_ify_alt_Iv_not in SOt. assumption.
    apply (ex_bound_FO_l_allFO_l _ _ _ Hf).
*)    apply ex_att_predSO_ll_allFO in Hex1. assumption.
Qed.


Lemma sSahlq_equiv_new_simpl_try3_LP'_pre_rid_hyp_3_exFO_bound : forall llv lx1 f alpha x P W Iv Ip Ir,
(forall (llv : list (list FOvariable)) (lx1 : list FOvariable) 
            (x : FOvariable) (P : predicate) (W : Set) (Iv : FOvariable -> W)
            (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop),
         SOQFree alpha = true ->
          length lx1 = length llv ->
          ex_bound_FO_overP_l alpha lx1 = false ->
ex_att_predSO_ll (alpha) llv = false ->
          ex_FOvar_x_ll x llv = false ->
(*           ex_FOvar_l_ll (FOvars_in alpha) llv = false -> *)
          is_in_FOvar x lx1 = false ->
          is_all_diff_FOv3 lx1 llv = true ->
          SOturnst W Iv (alt_Ip Ip (sSahlq_pa5' Ir llv (map (Iv_ify Iv) lx1)) P) Ir
            alpha <-> SOturnst W Iv Ip Ir (replace_pred alpha P x (fun4_l2' lx1 x llv))) ->
SOQFree (exFO f alpha) = true ->
length lx1 = length llv ->
is_in_FOvar x lx1 = false ->
(* ex_FOvar_l_ll (FOvars_in (allFO f alpha)) llv = false -> *)
(* ex_FOvar_l_ll (FOvars_in (allFO f alpha)) (cons lx1 nil) = false -> *)
ex_att_predSO_ll (exFO f alpha) llv = false ->
ex_FOvar_x_ll x llv = false ->
is_all_diff_FOv3 lx1 llv = true ->
ex_bound_FO_overP_l (exFO f alpha) lx1 = false ->
SOturnst W Iv (alt_Ip Ip (sSahlq_pa5' Ir llv (map (Iv_ify Iv) lx1)) P) Ir
  (exFO f alpha) <->
SOturnst W Iv Ip Ir (replace_pred (exFO f alpha) P x (fun4_l2' lx1 x llv)).
Proof.
  intros llv lx1 [zn] alpha [xn] P W Iv Ip Ir IH Hno Hl Hin Hex1 Hin2 (* Hex1 *)  Hall Hf.
  rewrite rep_pred_exFO. do 2 rewrite SOturnst_exFO.
  simpl in Hno.
  simpl in Hin2.
(*  case_eq (ex_FOvar_x_ll (Var zn) llv);
    intros Hex3; rewrite Hex3 in *. discriminate. *)
  simpl in Hf.
  pose proof (ex_bound_FO_overP_l_exFO_r _ _ _ Hf) as Hf2.
  split; intros [d SOt];  exists d. 
    apply IH; try assumption.

    apply ex_att_predSO_ll_exFO in Hex1. assumption.

apply sSahlq_equiv_new_simpl_try3_LP'_pre_rid_hyp_3_exFO_bound_pre; try assumption.

    apply IH in SOt; try assumption.
apply sSahlq_equiv_new_simpl_try3_LP'_pre_rid_hyp_3_exFO_bound_pre; try assumption.
    apply ex_att_predSO_ll_exFO in Hex1. assumption.
Qed.

Lemma sSahlq_equiv_new_simpl_try3_LP'_pre_rid_hyp_negSO : forall llv lx1 alpha x P W Iv Ip Ir,
(forall (llv : list (list FOvariable)) (lx1 : list FOvariable) 
            (x : FOvariable) (P : predicate) (W : Set) (Iv : FOvariable -> W)
            (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop),
         SOQFree alpha = true ->
          length lx1 = length llv ->
          ex_bound_FO_overP_l alpha lx1 = false ->
ex_att_predSO_ll ( alpha) llv = false -> 
          ex_FOvar_x_ll x llv = false ->

          is_in_FOvar x lx1 = false ->
          is_all_diff_FOv3 lx1 llv = true ->
          SOturnst W Iv (alt_Ip Ip (sSahlq_pa5' Ir llv (map (Iv_ify Iv) lx1)) P) Ir
            alpha <-> SOturnst W Iv Ip Ir (replace_pred alpha P x (fun4_l2' lx1 x llv))) ->
SOQFree (negSO alpha) = true ->
length lx1 = length llv ->
is_in_FOvar x lx1 = false ->
ex_att_predSO_ll (negSO alpha) llv = false -> 
ex_FOvar_x_ll x llv = false ->
is_all_diff_FOv3 lx1 llv = true ->
ex_bound_FO_overP_l (negSO  alpha) lx1 = false ->
SOturnst W Iv (alt_Ip Ip (sSahlq_pa5' Ir llv (map (Iv_ify Iv) lx1)) P) Ir
  (negSO alpha) <->
SOturnst W Iv Ip Ir (replace_pred (negSO alpha) P x (fun4_l2' lx1 x llv)).
Proof.
  intros alpha llv lx1 x P W Iv Ip Ir IH Hno Hl Hin (* Hex *) Hex3 Hex2 Hall Hf.
  rewrite rep_pred_negSO. do 2 rewrite SOturnst_negSO.  
  simpl in Hno.
  simpl FOvars_in in *.
  rewrite ex_bound_FO_overP_l_negSO in Hf.
  split; intros SOt H; apply SOt.
    apply IH in H; try assumption.
    apply ex_att_predSO_ll_negSO in Hex3. assumption.
    apply IH; try assumption.
    apply ex_att_predSO_ll_negSO in Hex3. assumption.
Qed.

Lemma no_free_FO_l_conjSO : forall lx1 alpha1 alpha2,
  no_free_FO_l (conjSO alpha1 alpha2) lx1 = false <->
  no_free_FO_l ( alpha1 ) lx1 = false \/  no_free_FO_l ( alpha2 ) lx1 = false.
Proof.
  induction lx1; intros alpha1 alpha2.
    simpl. split; intros. discriminate.
    destruct H; discriminate.
(* 
 left. all : try reflexivity.
 *)
    simpl. case_eq (free_FO alpha1 a); intros H1;
      case_eq (free_FO alpha2 a); intros H2;
        split; intros H; try reflexivity;
          try (left; reflexivity); try (right; reflexivity);
          try (apply IHlx1; assumption).
Qed.


Lemma no_bound_FO_l_x_occ_in_alpha_free_FO : forall l alpha x,
  no_bound_FO_l alpha l = true ->
  x_occ_in_alpha alpha x = true ->
  is_in_FOvar x l = true ->
  free_FO alpha x = true.
Proof.
  induction l; intros alpha [xn] Hb Hocc Hin.
    simpl in *. discriminate.

    simpl in *. destruct a as [ym].
    case_eq (x_occ_in_alpha alpha (Var ym));
      intros Hocc2; rewrite Hocc2 in *.
      case_eq (free_FO alpha (Var ym)); intros Hf;
        rewrite Hf in *. 2 : discriminate.
      case_eq (beq_nat xn ym); intros Hbeq.
        rewrite (beq_nat_true _ _ Hbeq) . assumption.

        rewrite Hbeq in *. apply IHl; assumption.

      case_eq (beq_nat xn ym); intros Hbeq; rewrite Hbeq in *.
        rewrite (beq_nat_true _ _ Hbeq) in *. rewrite Hocc in *.
        discriminate.
        apply IHl; assumption.
Qed.


Lemma no_bound_FO_l_alt_defn : forall l alpha,
  no_bound_FO_l alpha l = true <->
  (forall x,
    is_in_FOvar x l = true -> 
    x_occ_in_alpha alpha x = true ->
    free_FO alpha x = true).
Proof.
  induction l; intros alpha.
    simpl. split; intros H. discriminate.
    reflexivity.

    simpl in *. destruct a as [ym]; split; intros H. 
      intros [xn] H2 H3. case_eq (beq_nat xn ym);
        intros Hbeq. rewrite (beq_nat_true _ _ Hbeq) in *.
          case_eq (free_FO alpha (Var ym)); intros Hf;
            rewrite Hf in *. reflexivity.
            rewrite H3 in H. discriminate.

          rewrite Hbeq in H2.
          case_eq (x_occ_in_alpha alpha (Var ym));
            intros Hocc; rewrite Hocc in *.
            case_eq (free_FO alpha (Var ym)); intros Hf; rewrite Hf in *.
              2 : discriminate.
            apply IHl; assumption.

            apply IHl; assumption.

          case_eq (x_occ_in_alpha alpha (Var ym)).
            intros Hocc.
            pose proof H as H'.
            specialize (H (Var ym)). simpl in H.
            rewrite <- beq_nat_refl in H. specialize (H eq_refl).
            rewrite (H Hocc). apply IHl.
              intros [zn] H1 H2. specialize (H' (Var zn)).
              simpl in H'. case_eq (beq_nat zn ym); intros Hbeq;
                rewrite Hbeq in *. rewrite (beq_nat_true _ _ Hbeq) in *.
                apply H'. reflexivity. assumption.

                apply H'; assumption.

              intros Hocc. apply IHl. intros [zn] H1 H2.
              specialize (H (Var zn)). simpl in H.
              case_eq (beq_nat zn ym); intros Hbeq; rewrite Hbeq in *.
                rewrite (beq_nat_true _ _ Hbeq) in *. apply H; try assumption.
                reflexivity.

                apply H; assumption.
Qed.

Lemma ex_att_predSO_conjSO_l : forall llv alpha1 alpha2,
  ex_att_predSO (conjSO alpha1 alpha2) llv = false ->
  ex_att_predSO alpha1 llv = false.
Proof.
  intros [xn] alpha1 alpha2 H.
  simpl in *. case_eq (ex_att_predSO alpha1 (Var xn));
    intros H2; rewrite H2 in *. discriminate.
    reflexivity.
Qed.

Lemma ex_att_predSO_conjSO_r : forall llv alpha1 alpha2,
  ex_att_predSO (conjSO alpha1 alpha2) llv = false ->
  ex_att_predSO alpha2 llv = false.
Proof.
  intros [xn] alpha1 alpha2 H.
  simpl in *. case_eq (ex_att_predSO alpha2 (Var xn));
    intros H2; rewrite H2 in *.
    rewrite if_then_else_same in H. discriminate.
    reflexivity.
Qed.

Lemma ex_att_predSO_disjSO_l : forall llv alpha1 alpha2,
  ex_att_predSO (disjSO alpha1 alpha2) llv = false ->
  ex_att_predSO alpha1 llv = false.
Proof.
  intros [xn] alpha1 alpha2 H.
  simpl in *. case_eq (ex_att_predSO alpha1 (Var xn));
    intros H2; rewrite H2 in *. discriminate.
    reflexivity.
Qed.


Lemma ex_att_predSO_disjSO_r : forall llv alpha1 alpha2,
  ex_att_predSO (disjSO alpha1 alpha2) llv = false ->
  ex_att_predSO alpha2 llv = false.
Proof.
  intros [xn] alpha1 alpha2 H.
  simpl in *. case_eq (ex_att_predSO alpha2 (Var xn));
    intros H2; rewrite H2 in *.
    rewrite if_then_else_same in H. discriminate.
    reflexivity.
Qed.

Lemma ex_att_predSO_implSO_l : forall llv alpha1 alpha2,
  ex_att_predSO (implSO alpha1 alpha2) llv = false ->
  ex_att_predSO alpha1 llv = false.
Proof.
  intros [xn] alpha1 alpha2 H.
  simpl in *. case_eq (ex_att_predSO alpha1 (Var xn));
    intros H2; rewrite H2 in *. discriminate.
    reflexivity.
Qed.


Lemma ex_att_predSO_implSO_r : forall llv alpha1 alpha2,
  ex_att_predSO (implSO alpha1 alpha2) llv = false ->
  ex_att_predSO alpha2 llv = false.
Proof.
  intros [xn] alpha1 alpha2 H.
  simpl in *. case_eq (ex_att_predSO alpha2 (Var xn));
    intros H2; rewrite H2 in *.
    rewrite if_then_else_same in H. discriminate.
    reflexivity.
Qed.

Lemma ex_att_predSO_l_conjSO_l : forall llv alpha1 alpha2,
  ex_att_predSO_l (conjSO alpha1 alpha2) llv = false ->
  ex_att_predSO_l alpha1 llv = false.
Proof.
  induction llv; intros alpha1 alpha2 H. reflexivity.
  simpl in *.
  case_eq (ex_att_predSO alpha1 a); intros H1; rewrite H1 in *.
    discriminate.
  case_eq (ex_att_predSO alpha2 a); intros H2; rewrite H2 in *.
    discriminate.
  apply IHllv in H. assumption.
Qed.

Lemma ex_att_predSO_l_conjSO_r : forall llv alpha1 alpha2,
  ex_att_predSO_l (conjSO alpha1 alpha2) llv = false ->
  ex_att_predSO_l alpha2 llv = false.
Proof.
  induction llv; intros alpha1 alpha2 H. reflexivity.
  simpl in *.
  case_eq (ex_att_predSO alpha1 a); intros H1; rewrite H1 in *.
    discriminate.
  case_eq (ex_att_predSO alpha2 a); intros H2; rewrite H2 in *.
    discriminate.
  apply IHllv in H. assumption.
Qed.

Lemma ex_att_predSO_l_disjSO_l : forall llv alpha1 alpha2,
  ex_att_predSO_l (disjSO alpha1 alpha2) llv = false ->
  ex_att_predSO_l alpha1 llv = false.
Proof.
  induction llv; intros alpha1 alpha2 H. reflexivity.
  simpl in *.
  case_eq (ex_att_predSO alpha1 a); intros H1; rewrite H1 in *.
    discriminate.
  case_eq (ex_att_predSO alpha2 a); intros H2; rewrite H2 in *.
    discriminate.
  apply IHllv in H. assumption.
Qed.

Lemma ex_att_predSO_l_disjSO_r : forall llv alpha1 alpha2,
  ex_att_predSO_l (disjSO alpha1 alpha2) llv = false ->
  ex_att_predSO_l alpha2 llv = false.
Proof.
  induction llv; intros alpha1 alpha2 H. reflexivity.
  simpl in *.
  case_eq (ex_att_predSO alpha1 a); intros H1; rewrite H1 in *.
    discriminate.
  case_eq (ex_att_predSO alpha2 a); intros H2; rewrite H2 in *.
    discriminate.
  apply IHllv in H. assumption.
Qed.


Lemma ex_att_predSO_l_implSO_l : forall llv alpha1 alpha2,
  ex_att_predSO_l (implSO alpha1 alpha2) llv = false ->
  ex_att_predSO_l alpha1 llv = false.
Proof.
  induction llv; intros alpha1 alpha2 H. reflexivity.
  simpl in *.
  case_eq (ex_att_predSO alpha1 a); intros H1; rewrite H1 in *.
    discriminate.
  case_eq (ex_att_predSO alpha2 a); intros H2; rewrite H2 in *.
    discriminate.
  apply IHllv in H. assumption.
Qed.

Lemma ex_att_predSO_l_implSO_r : forall llv alpha1 alpha2,
  ex_att_predSO_l (implSO alpha1 alpha2) llv = false ->
  ex_att_predSO_l alpha2 llv = false.
Proof.
  induction llv; intros alpha1 alpha2 H. reflexivity.
  simpl in *.
  case_eq (ex_att_predSO alpha1 a); intros H1; rewrite H1 in *.
    discriminate.
  case_eq (ex_att_predSO alpha2 a); intros H2; rewrite H2 in *.
    discriminate.
  apply IHllv in H. assumption.
Qed.


Lemma ex_att_predSO_ll_conjSO_l : forall llv alpha1 alpha2,
  ex_att_predSO_ll (conjSO alpha1 alpha2) llv = false ->
  ex_att_predSO_ll alpha1 llv = false.
Proof.
  induction llv; intros alpha1 alpha2 H. reflexivity.
  simpl in *. case_eq (ex_att_predSO_l (conjSO alpha1 alpha2) a);
    intros H2; rewrite H2 in *. discriminate.
  apply IHllv in H. apply ex_att_predSO_l_conjSO_l in H2.
  rewrite H2. assumption.
Qed.

Lemma ex_att_predSO_ll_conjSO_r : forall llv alpha1 alpha2,
  ex_att_predSO_ll (conjSO alpha1 alpha2) llv = false ->
  ex_att_predSO_ll alpha2 llv = false.
Proof.
  induction llv; intros alpha1 alpha2 H. reflexivity.
  simpl in *. case_eq (ex_att_predSO_l (conjSO alpha1 alpha2) a);
    intros H2; rewrite H2 in *. discriminate.
  apply IHllv in H. apply ex_att_predSO_l_conjSO_r in H2.
  rewrite H2. assumption.
Qed.

Lemma ex_att_predSO_ll_disjSO_l : forall llv alpha1 alpha2,
  ex_att_predSO_ll (disjSO alpha1 alpha2) llv = false ->
  ex_att_predSO_ll alpha1 llv = false.
Proof.
  induction llv; intros alpha1 alpha2 H. reflexivity.
  simpl in *. case_eq (ex_att_predSO_l (disjSO alpha1 alpha2) a);
    intros H2; rewrite H2 in *. discriminate.
  apply IHllv in H. apply ex_att_predSO_l_disjSO_l in H2.
  rewrite H2. assumption.
Qed.

Lemma ex_att_predSO_ll_disjSO_r : forall llv alpha1 alpha2,
  ex_att_predSO_ll (disjSO alpha1 alpha2) llv = false ->
  ex_att_predSO_ll alpha2 llv = false.
Proof.
  induction llv; intros alpha1 alpha2 H. reflexivity.
  simpl in *. case_eq (ex_att_predSO_l (disjSO alpha1 alpha2) a);
    intros H2; rewrite H2 in *. discriminate.
  apply IHllv in H. apply ex_att_predSO_l_disjSO_r in H2.
  rewrite H2. assumption.
Qed.

Lemma ex_att_predSO_ll_implSO_l : forall llv alpha1 alpha2,
  ex_att_predSO_ll (implSO alpha1 alpha2) llv = false ->
  ex_att_predSO_ll alpha1 llv = false.
Proof.
  induction llv; intros alpha1 alpha2 H. reflexivity.
  simpl in *. case_eq (ex_att_predSO_l (implSO alpha1 alpha2) a);
    intros H2; rewrite H2 in *. discriminate.
  apply IHllv in H. apply ex_att_predSO_l_implSO_l in H2.
  rewrite H2. assumption.
Qed.

Lemma ex_att_predSO_ll_implSO_r : forall llv alpha1 alpha2,
  ex_att_predSO_ll (implSO alpha1 alpha2) llv = false ->
  ex_att_predSO_ll alpha2 llv = false.
Proof.
  induction llv; intros alpha1 alpha2 H. reflexivity.
  simpl in *. case_eq (ex_att_predSO_l (implSO alpha1 alpha2) a);
    intros H2; rewrite H2 in *. discriminate.
  apply IHllv in H. apply ex_att_predSO_l_implSO_r in H2.
  rewrite H2. assumption.
Qed.

Lemma sSahlq_equiv_new_simpl_try3_LP'_pre_rid_hyp_3_conjSO : forall llv lx1 alpha1 alpha2 x P W Iv Ip Ir,
(forall (llv : list (list FOvariable)) (lx1 : list FOvariable) 
            (x : FOvariable) (P : predicate) (W : Set) (Iv : FOvariable -> W)
            (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop),
         SOQFree alpha1 = true ->
          length lx1 = length llv ->
          ex_bound_FO_overP_l alpha1 lx1 = false ->
          ex_att_predSO_ll alpha1 llv = false ->
          ex_FOvar_x_ll x llv = false ->
          is_in_FOvar x lx1 = false ->
          is_all_diff_FOv3 lx1 llv = true ->
          SOturnst W Iv (alt_Ip Ip (sSahlq_pa5' Ir llv (map (Iv_ify Iv) lx1)) P) Ir
            alpha1 <-> SOturnst W Iv Ip Ir (replace_pred alpha1 P x (fun4_l2' lx1 x llv))) ->
(forall (llv : list (list FOvariable)) (lx1 : list FOvariable) 
            (x : FOvariable) (P : predicate) (W : Set) (Iv : FOvariable -> W)
            (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop),
         SOQFree alpha2 = true ->
          length lx1 = length llv ->
          ex_bound_FO_overP_l alpha2 lx1 = false ->
          ex_att_predSO_ll alpha2 llv = false ->
          ex_FOvar_x_ll x llv = false ->
          is_in_FOvar x lx1 = false ->
          is_all_diff_FOv3 lx1 llv = true ->
          SOturnst W Iv (alt_Ip Ip (sSahlq_pa5' Ir llv (map (Iv_ify Iv) lx1)) P) Ir
            alpha2 <-> SOturnst W Iv Ip Ir (replace_pred alpha2 P x (fun4_l2' lx1 x llv))) ->
SOQFree (conjSO alpha1 alpha2) = true ->
length lx1 = length llv ->
is_in_FOvar x lx1 = false ->
          ex_att_predSO_ll (conjSO alpha1 alpha2) llv = false ->
(* ex_FOvar_l_ll (FOvars_in (allFO f alpha)) (cons lx1 nil) = false -> *)
ex_FOvar_x_ll x llv = false ->
is_all_diff_FOv3 lx1 llv = true ->
ex_bound_FO_overP_l (conjSO  alpha1 alpha2) lx1 = false ->
SOturnst W Iv (alt_Ip Ip (sSahlq_pa5' Ir llv (map (Iv_ify Iv) lx1)) P) Ir
  (conjSO alpha1 alpha2) <->
SOturnst W Iv Ip Ir (replace_pred (conjSO alpha1 alpha2) P x (fun4_l2' lx1 x llv)).
Proof.
intros  llv lx1 alpha1 alpha2 x P W Iv Ip Ir IH1 IH2 Hno Hl Hin Hex1 Hex2 Hall Hf. 
  rewrite rep_pred_conjSO. do 2 rewrite SOturnst_conjSO.
  pose proof (SOQFree_conjSO_l _ _ Hno).
  pose proof (SOQFree_conjSO_r _ _ Hno).
  pose proof (ex_bound_FO_overP_l_conjSO_l _ _ _ Hf).
  pose proof (ex_bound_FO_overP_l_conjSO_r _ _ _ Hf).
  pose proof (ex_att_predSO_ll_conjSO_l _ _ _ Hex1).
  pose proof (ex_att_predSO_ll_conjSO_r _ _ _ Hex1).


  split; intros [HH1 HH2]; apply conj.
    apply IH1; try assumption.
    apply IH2; assumption.
    apply IH1 in HH1; assumption.
    apply IH2 in HH2; assumption.
Qed.

Lemma sSahlq_equiv_new_simpl_try3_LP'_pre_rid_hyp_3_disjSO : forall llv lx1 alpha1 alpha2 x P W Iv Ip Ir,
(forall (llv : list (list FOvariable)) (lx1 : list FOvariable) 
            (x : FOvariable) (P : predicate) (W : Set) (Iv : FOvariable -> W)
            (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop),
         SOQFree alpha1 = true ->
          length lx1 = length llv ->
          ex_bound_FO_overP_l alpha1 lx1 = false ->
          ex_att_predSO_ll alpha1 llv = false ->
          ex_FOvar_x_ll x llv = false ->
          is_in_FOvar x lx1 = false ->
          is_all_diff_FOv3 lx1 llv = true ->
          SOturnst W Iv (alt_Ip Ip (sSahlq_pa5' Ir llv (map (Iv_ify Iv) lx1)) P) Ir
            alpha1 <-> SOturnst W Iv Ip Ir (replace_pred alpha1 P x (fun4_l2' lx1 x llv))) ->
(forall (llv : list (list FOvariable)) (lx1 : list FOvariable) 
            (x : FOvariable) (P : predicate) (W : Set) (Iv : FOvariable -> W)
            (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop),
         SOQFree alpha2 = true ->
          length lx1 = length llv ->
          ex_bound_FO_overP_l alpha2 lx1 = false ->
          ex_att_predSO_ll alpha2 llv = false ->
          ex_FOvar_x_ll x llv = false ->
          is_in_FOvar x lx1 = false ->
          is_all_diff_FOv3 lx1 llv = true ->
          SOturnst W Iv (alt_Ip Ip (sSahlq_pa5' Ir llv (map (Iv_ify Iv) lx1)) P) Ir
            alpha2 <-> SOturnst W Iv Ip Ir (replace_pred alpha2 P x (fun4_l2' lx1 x llv))) ->
SOQFree (conjSO alpha1 alpha2) = true ->
length lx1 = length llv ->
is_in_FOvar x lx1 = false ->
          ex_att_predSO_ll (disjSO alpha1 alpha2) llv = false ->
(* ex_FOvar_l_ll (FOvars_in (allFO f alpha)) (cons lx1 nil) = false -> *)
ex_FOvar_x_ll x llv = false ->
is_all_diff_FOv3 lx1 llv = true ->
ex_bound_FO_overP_l (disjSO  alpha1 alpha2) lx1 = false ->
SOturnst W Iv (alt_Ip Ip (sSahlq_pa5' Ir llv (map (Iv_ify Iv) lx1)) P) Ir
  (disjSO alpha1 alpha2) <->
SOturnst W Iv Ip Ir (replace_pred (disjSO alpha1 alpha2) P x (fun4_l2' lx1 x llv)).
Proof.
intros  llv lx1 alpha1 alpha2 x P W Iv Ip Ir IH1 IH2 Hno Hl Hin Hex1 Hex2 Hall Hf. 
  rewrite rep_pred_disjSO. do 2 rewrite SOturnst_disjSO.
  pose proof (SOQFree_conjSO_l _ _ Hno).
  pose proof (SOQFree_conjSO_r _ _ Hno).
  pose proof (ex_bound_FO_overP_l_disjSO_l _ _ _ Hf).
  pose proof (ex_bound_FO_overP_l_disjSO_r _ _ _ Hf).
  pose proof (ex_att_predSO_ll_disjSO_l _ _ _ Hex1).
  pose proof (ex_att_predSO_ll_disjSO_r _ _ _ Hex1).


  split; (intros [HH1 | HH2]; [left | right]).
    apply IH1; try assumption.
    apply IH2; assumption.
    apply IH1 in HH1; assumption.
    apply IH2 in HH2; assumption.
Qed.

Lemma sSahlq_equiv_new_simpl_try3_LP'_pre_rid_hyp_3_implSO : forall llv lx1 alpha1 alpha2 x P W Iv Ip Ir,
(forall (llv : list (list FOvariable)) (lx1 : list FOvariable) 
            (x : FOvariable) (P : predicate) (W : Set) (Iv : FOvariable -> W)
            (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop),
         SOQFree alpha1 = true ->
          length lx1 = length llv ->
          ex_bound_FO_overP_l alpha1 lx1 = false ->
          ex_att_predSO_ll alpha1 llv = false ->
          ex_FOvar_x_ll x llv = false ->
          is_in_FOvar x lx1 = false ->
          is_all_diff_FOv3 lx1 llv = true ->
          SOturnst W Iv (alt_Ip Ip (sSahlq_pa5' Ir llv (map (Iv_ify Iv) lx1)) P) Ir
            alpha1 <-> SOturnst W Iv Ip Ir (replace_pred alpha1 P x (fun4_l2' lx1 x llv))) ->
(forall (llv : list (list FOvariable)) (lx1 : list FOvariable) 
            (x : FOvariable) (P : predicate) (W : Set) (Iv : FOvariable -> W)
            (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop),
         SOQFree alpha2 = true ->
          length lx1 = length llv ->
          ex_bound_FO_overP_l alpha2 lx1 = false ->
          ex_att_predSO_ll alpha2 llv = false ->
          ex_FOvar_x_ll x llv = false ->
          is_in_FOvar x lx1 = false ->
          is_all_diff_FOv3 lx1 llv = true ->
          SOturnst W Iv (alt_Ip Ip (sSahlq_pa5' Ir llv (map (Iv_ify Iv) lx1)) P) Ir
            alpha2 <-> SOturnst W Iv Ip Ir (replace_pred alpha2 P x (fun4_l2' lx1 x llv))) ->
SOQFree (conjSO alpha1 alpha2) = true ->
length lx1 = length llv ->
is_in_FOvar x lx1 = false ->
          ex_att_predSO_ll (implSO alpha1 alpha2) llv = false ->
(* ex_FOvar_l_ll (FOvars_in (allFO f alpha)) (cons lx1 nil) = false -> *)
ex_FOvar_x_ll x llv = false ->
is_all_diff_FOv3 lx1 llv = true ->
ex_bound_FO_overP_l (implSO  alpha1 alpha2) lx1 = false ->
SOturnst W Iv (alt_Ip Ip (sSahlq_pa5' Ir llv (map (Iv_ify Iv) lx1)) P) Ir
  (implSO alpha1 alpha2) <->
SOturnst W Iv Ip Ir (replace_pred (implSO alpha1 alpha2) P x (fun4_l2' lx1 x llv)).
Proof.
intros  llv lx1 alpha1 alpha2 x P W Iv Ip Ir IH1 IH2 Hno Hl Hin Hex1 Hex2 Hall Hf. 
  rewrite rep_pred_implSO. do 2 rewrite SOturnst_implSO.
  pose proof (SOQFree_conjSO_l _ _ Hno).
  pose proof (SOQFree_conjSO_r _ _ Hno).
  pose proof (ex_bound_FO_overP_l_implSO_l _ _ _ Hf).
  pose proof (ex_bound_FO_overP_l_implSO_r _ _ _ Hf).
  pose proof (ex_att_predSO_ll_implSO_l _ _ _ Hex1).
  pose proof (ex_att_predSO_ll_implSO_r _ _ _ Hex1).


  split; intros HH1 HH2.
    apply IH2; try assumption.
    apply HH1.
    apply IH1 in HH2; try assumption.
 
    apply (IH2 llv lx1 x); try assumption.
    apply HH1. 
    apply (IH1 llv lx1 x); try assumption.
Qed.

(* Left it here 20/12/17 7pm *)
(* Keep going! Up to disj *)
Lemma sSahlq_equiv_new_simpl_try3_LP'_pre_rid_hyp_3 : forall alpha  llv lx1 x P W Iv Ip Ir,
(*   length lP = length llv -> *)
  SOQFree alpha = true ->
    length lx1 = length llv ->
ex_bound_FO_overP_l alpha lx1 = false ->
(* ex_attached_allFO_lv ( alpha) lx1 = false ->
ex_attached_exFO_lv (alpha) lx1 = false -> *)
ex_att_predSO_ll alpha llv = false ->
ex_FOvar_x_ll x llv = false ->
is_in_FOvar x lx1 = false ->
is_all_diff_FOv3 lx1 llv = true ->
    SOturnst W Iv (alt_Ip Ip (sSahlq_pa5' Ir llv (map (Iv_ify Iv) lx1) ) P) Ir alpha <->
    SOturnst W Iv Ip Ir (replace_pred alpha P x (fun4_l2' lx1 x llv)).
Proof.
  induction alpha; intros llv lx1 x P W Iv Ip Ir Hno Hl Hf Hex1 Hex2 Hin Hall .
    apply sSahlq_equiv_new_simpl_try3_LP'_pre_rid_hyp_2_predSO; try assumption.

    apply sSahlq_equiv_new_simpl_try3_LP'_pre_relatSO; assumption.

    apply sSahlq_equiv_new_simpl_try3_LP'_pre_eqFO; assumption.

    apply sSahlq_equiv_new_simpl_try3_LP'_pre_rid_hyp_3_allFO_bound; try assumption.

    apply sSahlq_equiv_new_simpl_try3_LP'_pre_rid_hyp_3_exFO_bound; try assumption.

    apply sSahlq_equiv_new_simpl_try3_LP'_pre_rid_hyp_negSO; try assumption.

    apply sSahlq_equiv_new_simpl_try3_LP'_pre_rid_hyp_3_conjSO; try assumption.

    apply sSahlq_equiv_new_simpl_try3_LP'_pre_rid_hyp_3_disjSO; try assumption.

    apply sSahlq_equiv_new_simpl_try3_LP'_pre_rid_hyp_3_implSO; try assumption.

    simpl in Hno. destruct p. discriminate.
    simpl in Hno. destruct p. discriminate.
Qed.

Fixpoint ex_attached_allFO_lllv alpha lllv : bool :=
  match lllv with
  | nil => false
  | cons llv lllv' => if ex_attached_allFO_llv alpha llv then true else 
      ex_attached_allFO_lllv alpha lllv'
  end.

Fixpoint ex_attached_exFO_lllv alpha lllv : bool :=
  match lllv with
  | nil => false
  | cons llv lllv' => if ex_attached_exFO_llv alpha llv then true else 
      ex_attached_exFO_lllv alpha lllv'
  end.

Lemma is_un_predless_fun4' : forall l a x,
is_unary_predless (fun4' a x l) = true.
Proof.
  induction l; intros [ym] [xn]. reflexivity.
  simpl. destruct a. apply IHl.
Qed.

Lemma is_un_predless_fun4_l2' : forall l x l0,
  is_unary_predless (fun4_l2' l x l0) = true.
Proof.
  induction l; intros x l0. reflexivity.
  case_eq l. intros Hnil. simpl.
    destruct l0. reflexivity. apply is_un_predless_fun4'.

    intros y ly Hly.
    rewrite <- Hly. 
    simpl. destruct l0. rewrite Hly. reflexivity.
    rewrite Hly. rewrite <- Hly.
    case_eq l1. intros Hnil. apply is_un_predless_fun4'.
    intros l2 ll2 Hll2. rewrite <- Hll2.
    simpl. rewrite IHl. rewrite is_un_predless_fun4'.
    reflexivity.
Qed.

Lemma is_all_diff_FOv2_app_l : forall l1 l2,
  is_all_diff_FOv (flat_map (fun l => l) (app l1 l2)) = true ->
  is_all_diff_FOv (flat_map (fun l => l) l1) = true.
Admitted.

Lemma ex_att_allFO_llv_app_f_l: forall l1 l2 alpha,
  ex_attached_allFO_llv alpha (app l1 l2) = false ->
  ex_attached_allFO_llv alpha l1 = false .
Proof.
  induction l1; intros l2 alpha H2. reflexivity.
  simpl in *. case_eq (ex_attached_allFO_lv alpha a);
  intros H; rewrite H in *. discriminate.
  apply (IHl1 l2 _ H2).
Qed.

Lemma ex_att_exFO_llv_app_f_l: forall l1 l2 alpha,
  ex_attached_exFO_llv alpha (app l1 l2) = false ->
  ex_attached_exFO_llv alpha l1 = false .
Proof.
  induction l1; intros l2 alpha H2. reflexivity.
  simpl in *. case_eq (ex_attached_exFO_lv alpha a);
  intros H; rewrite H in *. discriminate.
  apply (IHl1 l2 _ H2).
Qed.

Lemma ex_att_allFO_llv_app_f_r: forall l1 l2 alpha,
  ex_attached_allFO_llv alpha (app l1 l2) = false ->
  ex_attached_allFO_llv alpha l2 = false .
Proof.
  induction l1; intros l2 alpha H2. assumption.
  simpl in *. case_eq (ex_attached_allFO_lv alpha a);
    intros H; rewrite H in *. discriminate.
  apply (IHl1 _ _ H2).
Qed.

Lemma ex_att_exFO_llv_app_f_r: forall l1 l2 alpha,
  ex_attached_exFO_llv alpha (app l1 l2) = false ->
  ex_attached_exFO_llv alpha l2 = false .
Proof.
  induction l1; intros l2 alpha H2. assumption.
  simpl in *. case_eq (ex_attached_exFO_lv alpha a);
    intros H; rewrite H in *. discriminate.
  apply (IHl1 _ _ H2).
Qed.


Lemma attached_allFO_x_rep_pred2 : forall alpha cond y Q x,
  attached_allFO_x cond y = false ->
  attached_allFO_x cond x = false ->
  attached_allFO_x alpha y = false ->
  attached_allFO_x (replace_pred alpha Q x cond) y = false.
Proof.
  induction alpha; intros cond [ym] [Qm] [xn] H1 H2 H3.
    destruct p as [Rn]. destruct f as [zn]. simpl.
    case_eq (beq_nat Qm Rn); intros Hbeq.
      apply attached_allFO_x_rep_FOv ;
        try assumption.

      reflexivity.

    destruct f. destruct f0. reflexivity.

    destruct f. destruct f0. reflexivity.

    destruct f as [zn]. simpl.
    case_eq (beq_nat ym zn); intros Hbeq;
      simpl in H3; rewrite Hbeq in H3. discriminate.
    apply IHalpha; try assumption.

    destruct f as [zn]. simpl.
    apply IHalpha; try assumption.

    simpl. apply IHalpha; assumption.

    simpl. rewrite IHalpha1. apply IHalpha2.
    all : try assumption.
      case_eq (attached_allFO_x alpha2 (Var ym));
        simpl in *;
        intros H; rewrite H in *.
        rewrite if_then_else_true in H3. discriminate.

        reflexivity.

      case_eq (attached_allFO_x alpha1 (Var ym));
        simpl in *;
        intros H; rewrite H in *. discriminate.

        reflexivity.

    simpl. rewrite IHalpha1. apply IHalpha2.
    all : try assumption.
      case_eq (attached_allFO_x alpha2 (Var ym));
        simpl in *;
        intros H; rewrite H in *.
        rewrite if_then_else_true in H3. discriminate.

        reflexivity.

      case_eq (attached_allFO_x alpha1 (Var ym));
        simpl in *;
        intros H; rewrite H in *. discriminate.

        reflexivity.

    simpl. rewrite IHalpha1. apply IHalpha2.
    all : try assumption.
      case_eq (attached_allFO_x alpha2 (Var ym));
        simpl in *;
        intros H; rewrite H in *.
        rewrite if_then_else_true in H3. discriminate.

        reflexivity.

      case_eq (attached_allFO_x alpha1 (Var ym));
        simpl in *;
        intros H; rewrite H in *. discriminate.

        reflexivity.

    destruct p as [Pn]. simpl.
    case_eq (beq_nat Qm Pn); intros Hbeq.
      apply IHalpha; assumption.

      simpl. apply IHalpha; assumption.

    destruct p as [Pn]. simpl.
    case_eq (beq_nat Qm Pn); intros Hbeq.
      apply IHalpha; assumption.

      simpl. apply IHalpha; assumption.
Qed.

Lemma attached_exFO_x_rep_pred2 : forall alpha cond y Q x,
  attached_exFO_x cond y = false ->
  attached_exFO_x cond x = false ->
  attached_exFO_x alpha y = false ->
  attached_exFO_x (replace_pred alpha Q x cond) y = false.
Proof.
  induction alpha; intros cond [ym] [Qm] [xn] H1 H2 H3.
    destruct p as [Rn]. destruct f as [zn]. simpl.
    case_eq (beq_nat Qm Rn); intros Hbeq.
      apply attached_exFO_x_rep_FOv ;
        try assumption.

      reflexivity.

    destruct f. destruct f0. reflexivity.

    destruct f. destruct f0. reflexivity.

    destruct f as [zn]. simpl.
    apply IHalpha; try assumption.

    destruct f as [zn]. simpl.
    case_eq (beq_nat ym zn); intros Hbeq;
      simpl in H3; rewrite Hbeq in H3. discriminate.
    apply IHalpha; try assumption.

    simpl. apply IHalpha; assumption.

    simpl. rewrite IHalpha1. apply IHalpha2.
    all : try assumption.
      case_eq (attached_exFO_x alpha2 (Var ym));
        simpl in *;
        intros H; rewrite H in *.
        rewrite if_then_else_true in H3. discriminate.

        reflexivity.

      case_eq (attached_exFO_x alpha1 (Var ym));
        simpl in *;
        intros H; rewrite H in *. discriminate.

        reflexivity.

    simpl. rewrite IHalpha1. apply IHalpha2.
    all : try assumption.
      case_eq (attached_exFO_x alpha2 (Var ym));
        simpl in *;
        intros H; rewrite H in *.
        rewrite if_then_else_true in H3. discriminate.

        reflexivity.

      case_eq (attached_exFO_x alpha1 (Var ym));
        simpl in *;
        intros H; rewrite H in *. discriminate.

        reflexivity.

    simpl. rewrite IHalpha1. apply IHalpha2.
    all : try assumption.
      case_eq (attached_exFO_x alpha2 (Var ym));
        simpl in *;
        intros H; rewrite H in *.
        rewrite if_then_else_true in H3. discriminate.

        reflexivity.

      case_eq (attached_exFO_x alpha1 (Var ym));
        simpl in *;
        intros H; rewrite H in *. discriminate.

        reflexivity.

    destruct p as [Pn]. simpl.
    case_eq (beq_nat Qm Pn); intros Hbeq.
      apply IHalpha; assumption.

      simpl. apply IHalpha; assumption.

    destruct p as [Pn]. simpl.
    case_eq (beq_nat Qm Pn); intros Hbeq.
      apply IHalpha; assumption.

      simpl. apply IHalpha; assumption.
Qed.

Lemma ex_attached_allFO_lv_rep_pred2 : forall lv alpha cond P x,
  ex_attached_allFO_lv cond lv = false ->
  ex_attached_allFO_lv alpha lv = false ->
  attached_allFO_x cond x = false ->
  ex_attached_allFO_lv (replace_pred alpha P x cond) lv = false.
Proof.
  induction lv; intros alpha cond P x H1 H2 H4.
    reflexivity.

    simpl in *.
    case_eq (attached_allFO_x alpha a); intros H2a;
      rewrite H2a in *. discriminate.
    case_eq (attached_allFO_x cond a); intros H3; rewrite H3 in *. discriminate.
    rewrite (attached_allFO_x_rep_pred2 _ _ _ _ _ H3  H4 H2a).
    apply IHlv; assumption.
Qed.

Lemma ex_attached_exFO_lv_rep_pred2 : forall lv alpha cond P x,
  ex_attached_exFO_lv cond lv = false ->
  ex_attached_exFO_lv alpha lv = false ->
  attached_exFO_x cond x = false ->
  ex_attached_exFO_lv (replace_pred alpha P x cond) lv = false.
Proof.
  induction lv; intros alpha cond P x H1 H2 H4.
    reflexivity.

    simpl in *.
    case_eq (attached_exFO_x alpha a); intros H2a;
      rewrite H2a in *. discriminate.
    case_eq (attached_exFO_x cond a); intros H3; rewrite H3 in *. discriminate.
    rewrite (attached_exFO_x_rep_pred2 _ _ _ _ _ H3  H4 H2a).
    apply IHlv; assumption.
Qed.



Lemma ex_attached_allFO_llv_rep_pred2 :
  forall (llv : list (list FOvariable)) (alpha cond : SecOrder) 
    (P : predicate) (x : FOvariable),
  ex_attached_allFO_llv cond llv = false ->
  ex_attached_allFO_llv alpha llv = false ->
  attached_allFO_x cond x = false ->
  ex_attached_allFO_llv (replace_pred alpha P x cond) llv = false.
Proof.
  induction llv; intros alpha cond P x Hat1 Hat2 Hat3.
    simpl in *. reflexivity.

    simpl in *. case_eq (ex_attached_allFO_lv cond a); intros H1; rewrite H1 in *.
      discriminate.
    case_eq (ex_attached_allFO_lv alpha a); intros H2; rewrite H2 in *. discriminate.
    rewrite (ex_attached_allFO_lv_rep_pred2 _ _ _ _ _ H1 H2 Hat3).
    apply IHllv; assumption.
Qed.

Lemma ex_attached_exFO_llv_rep_pred2 :
  forall (llv : list (list FOvariable)) (alpha cond : SecOrder) 
    (P : predicate) (x : FOvariable),
  ex_attached_exFO_llv cond llv = false ->
  ex_attached_exFO_llv alpha llv = false ->
  attached_exFO_x cond x = false ->
  ex_attached_exFO_llv (replace_pred alpha P x cond) llv = false.
Proof.
  induction llv; intros alpha cond P x Hat1 Hat2 Hat3.
    simpl in *. reflexivity.

    simpl in *. case_eq (ex_attached_exFO_lv cond a); intros H1; rewrite H1 in *.
      discriminate.
    case_eq (ex_attached_exFO_lv alpha a); intros H2; rewrite H2 in *. discriminate.
    rewrite (ex_attached_exFO_lv_rep_pred2 _ _ _ _ _ H1 H2 Hat3).
    apply IHllv; assumption.
Qed.

Lemma ex_att_allFO_lv_disjSO_f_rev : 
  forall (lv : list FOvariable) (alpha1 alpha2 : SecOrder),
  ex_attached_allFO_lv alpha1 lv = false ->
  ex_attached_allFO_lv alpha2 lv = false ->
  ex_attached_allFO_lv (disjSO alpha1 alpha2) lv = false.
Proof.
  induction lv; intros alpha1 alpha2 H1 H2. reflexivity.
  simpl in *.
  case_eq (attached_allFO_x alpha1 a); intros HH1;
    rewrite HH1 in *. discriminate.
  case_eq (attached_allFO_x alpha2 a); intros HH2;
    rewrite HH2 in *. discriminate.
  apply IHlv; assumption.
Qed.

Lemma ex_att_exFO_lv_disjSO_f_rev : 
  forall (lv : list FOvariable) (alpha1 alpha2 : SecOrder),
  ex_attached_exFO_lv alpha1 lv = false ->
  ex_attached_exFO_lv alpha2 lv = false ->
  ex_attached_exFO_lv (disjSO alpha1 alpha2) lv = false.
Proof.
  induction lv; intros alpha1 alpha2 H1 H2. reflexivity.
  simpl in *.
  case_eq (attached_exFO_x alpha1 a); intros HH1;
    rewrite HH1 in *. discriminate.
  case_eq (attached_exFO_x alpha2 a); intros HH2;
    rewrite HH2 in *. discriminate.
  apply IHlv; assumption.
Qed.

Lemma ex_att_allFO_llv_disjSO_f_rev:
  forall (llv : list (list FOvariable)) (alpha1 alpha2 : SecOrder),
  ex_attached_allFO_llv alpha1 llv = false ->
  ex_attached_allFO_llv alpha2 llv = false ->
  ex_attached_allFO_llv (disjSO alpha1 alpha2) llv = false.
Proof.
  induction llv; intros alpha1 alpha2 H1 H2. reflexivity.
  simpl in *.
  case_eq (ex_attached_allFO_lv alpha1 a); intros HH1;
    rewrite HH1 in *. discriminate.
  case_eq (ex_attached_allFO_lv alpha2 a); intros HH2;
    rewrite HH2 in *. discriminate.
  rewrite ex_att_allFO_lv_disjSO_f_rev.
  apply IHllv. all : assumption.
Qed.

Lemma ex_att_exFO_llv_disjSO_f_rev:
  forall (llv : list (list FOvariable)) (alpha1 alpha2 : SecOrder),
  ex_attached_exFO_llv alpha1 llv = false ->
  ex_attached_exFO_llv alpha2 llv = false ->
  ex_attached_exFO_llv (disjSO alpha1 alpha2) llv = false.
Proof.
  induction llv; intros alpha1 alpha2 H1 H2. reflexivity.
  simpl in *.
  case_eq (ex_attached_exFO_lv alpha1 a); intros HH1;
    rewrite HH1 in *. discriminate.
  case_eq (ex_attached_exFO_lv alpha2 a); intros HH2;
    rewrite HH2 in *. discriminate.
  rewrite ex_att_exFO_lv_disjSO_f_rev.
  apply IHllv. all : assumption.
Qed.

Lemma ex_att_allFO_lv_relatSO : forall l x y,
  ex_attached_allFO_lv (relatSO x y) l = false.
Proof.
  induction l; intros [xn] [ym]. reflexivity.
  simpl. apply IHl.
Qed.

Lemma ex_att_exFO_lv_relatSO : forall l x y,
  ex_attached_exFO_lv (relatSO x y) l = false.
Proof.
  induction l; intros [xn] [ym]. reflexivity.
  simpl. apply IHl.
Qed.

Lemma ex_att_allFO_llv_relatSO : forall l x y,
  ex_attached_allFO_llv (relatSO x y) l = false.
Proof.
  induction l; intros x y. reflexivity.
  simpl. rewrite IHl. rewrite ex_att_allFO_lv_relatSO.
  reflexivity.
Qed.

Lemma ex_att_exFO_llv_relatSO : forall l x y,
  ex_attached_exFO_llv (relatSO x y) l = false.
Proof.
  induction l; intros x y. reflexivity.
  simpl. rewrite IHl. rewrite ex_att_exFO_lv_relatSO.
  reflexivity.
Qed.

Lemma ex_att_allFO_llv_fun4'_all_diff : forall l0 llv a x,
  is_all_diff_FOv (flat_map (fun l => l) (cons l0 llv)) = true ->
  ex_attached_allFO_llv (fun4' a x l0) llv = false.
Proof.
  induction l0; intros llv y x Hall.
    simpl in *. apply ex_att_allFO_llv_relatSO.

    simpl in *.
    case_eq (is_in_FOvar a (l0 ++ flat_map (fun l : list FOvariable => l) llv));
      intros Hin; rewrite Hin in *. discriminate.
      rewrite ex_att_allFO_llv_exFO.
      apply ex_att_allFO_llv_conjSO_f_rev.
        apply ex_att_allFO_llv_relatSO.
        apply IHl0. assumption.
Qed. 

Lemma ex_attached_exFO_lv_exFO_rev : forall lv x alpha,
  ex_attached_exFO_lv alpha lv = false ->
  is_in_FOvar x lv = false ->
  ex_attached_exFO_lv (exFO x alpha) lv = false.
Proof.
  induction lv; intros x alpha H1 H2. reflexivity.
  simpl in *. destruct x as [xn]. destruct a as [ym].
  rewrite beq_nat_comm. case_eq (beq_nat xn ym);
    intros Hbeq; rewrite Hbeq in *. discriminate.
  case_eq (attached_exFO_x alpha (Var ym));
    intros H3; rewrite H3 in *. discriminate.
  apply IHlv; assumption.
Qed.

Lemma ex_attached_exFO_llv_exFO : forall llv a alpha,
  ex_attached_exFO_llv alpha llv = false ->
  ex_FOvar_x_ll a llv = false ->
  ex_attached_exFO_llv (exFO a alpha) llv = false.
Proof.
  induction llv; intros x alpha H1 H2. reflexivity.
  simpl in *. case_eq (ex_attached_exFO_lv alpha a);
    intros Hex; rewrite Hex in *. discriminate.
  case_eq (is_in_FOvar x a); intros H3; rewrite H3 in *.
    discriminate.
  rewrite ex_attached_exFO_lv_exFO_rev. apply IHllv.
  all : assumption.
Qed.

Lemma is_in_FOvar_ex_Fovar_x_ll : forall l0 x,
  is_in_FOvar x (flat_map (fun l => l) l0) =
  ex_FOvar_x_ll x l0.
Proof.
  induction l0; intros x. reflexivity.
  simpl. rewrite is_in_FOvar_app.
  rewrite IHl0. reflexivity.
Qed.

Lemma ex_att_exFO_llv_fun4'_all_diff : forall l0 llv a x,
  is_all_diff_FOv (flat_map (fun l => l) (cons l0 llv)) = true ->
  ex_attached_exFO_llv (fun4' a x l0) llv = false.
Proof.
  induction l0; intros llv y x Hall.
    simpl in *. apply ex_att_exFO_llv_relatSO.

    simpl in *.
    case_eq (is_in_FOvar a (l0 ++ flat_map (fun l : list FOvariable => l) llv));
      intros Hin; rewrite Hin in *. discriminate.
    apply ex_attached_exFO_llv_exFO.
    apply ex_att_exFO_llv_conjSO_f_rev.
      apply ex_att_exFO_llv_relatSO.

      apply IHl0. assumption.
      apply is_in_FOvar_app_r in Hin.
      rewrite <- is_in_FOvar_ex_Fovar_x_ll. assumption.
Qed.

Lemma att_allFO_x_fun4' : forall l f x y,
  is_in_FOvar y l = false ->
  attached_allFO_x (fun4' f x l) y = false.
Proof.
  induction l; intros f x y Hin.
    simpl in *. reflexivity.

    simpl in *. destruct y as [ym]. destruct a as [zn].
    case_eq (beq_nat ym zn); intros Hbeq; rewrite Hbeq in *.
      discriminate.
    apply IHl. assumption.
Qed.

Lemma att_exFO_x_fun4' : forall l f x y,
  is_in_FOvar y l = false ->
  attached_exFO_x (fun4' f x l) y = false.
Proof.
  induction l; intros f x y Hin.
    simpl in *. reflexivity.

    simpl in *. destruct y as [ym]. destruct a as [zn].
    case_eq (beq_nat ym zn); intros Hbeq; rewrite Hbeq in *.
      discriminate.
    apply IHl. assumption.
Qed.



Lemma ex_att_allFO_llv_rep_pred_fun4' : forall llv l alpha x y P,
   ex_attached_allFO_llv alpha (cons l llv) = false ->
is_all_diff_FOv
         (flat_map (fun l : list FOvariable => l)
            (cons l llv)) = true ->
is_in_FOvar x l = false ->
ex_attached_allFO_llv (replace_pred alpha P x (fun4' y x l)) llv = false.
Proof.
  intros llv l alpha x y P Hex Hall Hin.
  apply ex_attached_allFO_llv_rep_pred2.
    apply ex_att_allFO_llv_fun4'_all_diff. assumption.

    simpl in Hex. case_eq (ex_attached_allFO_lv alpha l);
      intros H; rewrite H in *. discriminate.
      assumption.

    apply att_allFO_x_fun4'. assumption.
Qed.

Lemma ex_att_exFO_llv_rep_pred_fun4' : forall llv l alpha x y P,
   ex_attached_exFO_llv alpha (cons l llv) = false ->
is_all_diff_FOv
         (flat_map (fun l : list FOvariable => l)
            (cons l llv)) = true ->
is_in_FOvar x l = false ->
ex_attached_exFO_llv (replace_pred alpha P x (fun4' y x l)) llv = false.
Proof.
  intros llv l alpha x y P Hex Hall Hin.
  apply ex_attached_exFO_llv_rep_pred2.
    apply ex_att_exFO_llv_fun4'_all_diff. assumption.

    simpl in Hex. case_eq (ex_attached_exFO_lv alpha l);
      intros H; rewrite H in *. discriminate.
      assumption.

    apply att_exFO_x_fun4'. assumption.
Qed.

Lemma att_allFO_x_disjSO_rev : forall alpha1 alpha2 x,
  attached_allFO_x alpha1 x = false ->
  attached_allFO_x alpha2 x = false ->
  attached_allFO_x (disjSO alpha1 alpha2) x = false.
Proof.
  intros until 0. intros H1 H2.
  simpl. rewrite H1. rewrite H2. reflexivity.
Qed.

Lemma att_exFO_x_disjSO_rev : forall alpha1 alpha2 x,
  attached_exFO_x alpha1 x = false ->
  attached_exFO_x alpha2 x = false ->
  attached_exFO_x (disjSO alpha1 alpha2) x = false.
Proof.
  intros until 0. intros H1 H2.
  simpl. rewrite H1. rewrite H2. reflexivity.
Qed.

Lemma is_in_FOvar_rearr : forall l2 l1 x y,
  is_in_FOvar y (app l2 (cons x l1)) =
  is_in_FOvar y (cons x (app l2 l1)).
Proof.
  induction l2; intros l1 [xn] [ym]. simpl. reflexivity.
  simpl. destruct a as [zn]. rewrite IHl2. simpl.
  case_eq (beq_nat ym zn); case_eq (beq_nat ym xn); reflexivity.
Qed.

Lemma is_in_FOvar_app_comm : forall l1 l2 y,
  is_in_FOvar y (app l1 l2) =
  is_in_FOvar y (app l2 l1).
Proof.
  induction l1; intros l2 y. rewrite app_nil_r. reflexivity.
  rewrite is_in_FOvar_rearr.
  simpl. destruct y as [ym]. destruct a as [zn].
  rewrite IHl1. reflexivity.
Qed.

Lemma is_all_diff_FOv_rearr : forall l2 l1 x,
  is_all_diff_FOv (app l2 (cons x l1)) =
  is_all_diff_FOv (cons x (app l2 l1)).
Proof.
  induction l2; intros l1 x. reflexivity.
  simpl.
  rewrite is_in_FOvar_rearr.
  simpl.
 destruct x as [xn]. destruct a as [ym].
  rewrite (beq_nat_comm xn ym).
  rewrite is_in_FOvar_app_comm. rewrite IHl2.
  simpl. case_eq (beq_nat ym xn);
    case_eq (is_in_FOvar (Var ym) (app l1 l2));
    case_eq (is_in_FOvar (Var xn) (app l1 l2));
    try reflexivity;
    try rewrite if_then_else_false; reflexivity.
Qed.

Lemma is_all_diff_FOv_app_comm : forall l1 l2,
  is_all_diff_FOv (app l1 l2) = 
  is_all_diff_FOv (app l2 l1).
Proof.
  induction l1; intros l2. rewrite app_nil_r. reflexivity.
  simpl. rewrite is_all_diff_FOv_rearr. simpl.
  do 2 rewrite is_in_FOvar_app.
  rewrite IHl1. case_eq (is_in_FOvar a l1); 
    case_eq (is_in_FOvar a l2); reflexivity.
Qed.

Lemma is_all_diff_FOv_app_comm2 : forall l l1 l2,
  is_all_diff_FOv (app (app l1 l2) l) = 
  is_all_diff_FOv (app (app l2 l1) l).
Proof.
  induction l; intros l1 l2.
    do 2 rewrite app_nil_r. apply is_all_diff_FOv_app_comm.

    rewrite is_all_diff_FOv_app_comm.
    rewrite (is_all_diff_FOv_app_comm (app l2 l1) (cons a l)).
    simpl. rewrite is_all_diff_FOv_app_comm.
    rewrite (is_all_diff_FOv_app_comm l). rewrite IHl.
    do 4 rewrite is_in_FOvar_app.
    case_eq (is_in_FOvar a l); case_eq (is_in_FOvar a l1);
      case_eq (is_in_FOvar a l2); reflexivity.
Qed.

Lemma is_all_diff_FOv_app_t : forall l1 l2,
  is_all_diff_FOv (app l1 l2) = true ->
  (is_all_diff_FOv l1 = true) /\ (is_all_diff_FOv l2 = true).
Proof.
  induction l1; intros l2 H.
    simpl in *.
      apply conj. reflexivity. assumption.

    simpl in *.
    case_eq (is_in_FOvar a (app l1 l2)); intros Hin;
      rewrite Hin in *. discriminate.
    apply is_in_FOvar_app_l in Hin. rewrite Hin.
    apply IHl1. assumption.
Qed.

Lemma is_in_FOvar_flat_map_rearr : forall l2 l l3 a,
is_in_FOvar a (flat_map (fun l0 : list FOvariable => l0) (l2 ++ l :: l3)) = 
is_in_FOvar a (flat_map (fun l0 : list FOvariable => l0) ((cons l l2) ++ l3)).
Proof.
  induction l2; intros l l3 x. reflexivity.
  simpl in *.
  do 3 rewrite is_in_FOvar_app.
  rewrite IHl2.
  rewrite is_in_FOvar_app.
  case_eq (is_in_FOvar x a); case_eq (is_in_FOvar x l); reflexivity.
Qed.

Lemma is_in_FOvar_flat_map_rearr2 : forall l4 l2 l l3 a,
is_in_FOvar a (app l4 (flat_map (fun l0 : list FOvariable => l0) (l2 ++ l :: l3))) = 
is_in_FOvar a (app l4 (flat_map (fun l0 : list FOvariable => l0) ((cons l l2) ++ l3))).
Proof.
  induction l4; intros l2 l l3 x.
    simpl. apply is_in_FOvar_flat_map_rearr.

    simpl. destruct x as [xn]. destruct a as [ym].
    rewrite IHl4. simpl. reflexivity.
Qed.

Lemma is_all_diff_FOv_lem7 : forall l2 a0 l l3,
is_all_diff_FOv (flat_map (fun l0 : list FOvariable => l0) (l2 ++ (a0 ++ l) :: l3)) =
is_all_diff_FOv (flat_map (fun l0 : list FOvariable => l0) (l2 ++ cons (a0) (l :: l3))).
Proof.
  induction l2; intros a0 l l3.
    simpl. rewrite app_assoc. reflexivity.

    simpl. induction a. simpl. apply IHl2.
    simpl. rewrite IHa.
    rewrite is_in_FOvar_flat_map_rearr2. simpl. rewrite app_assoc.
    rewrite is_in_FOvar_flat_map_rearr2. simpl.
    rewrite (app_assoc a1 a0 (flat_map (fun l0 : list FOvariable => l0) (l2 ++ l :: l3))).
    rewrite is_in_FOvar_flat_map_rearr2. simpl.
    rewrite app_assoc.
    rewrite app_assoc.
    reflexivity.
Qed.

Lemma is_all_diff_FOv_app_flat_map2 : forall l2 a l3,
  is_all_diff_FOv (flat_map (fun l => l) (app l2 (cons a l3))) = 
  is_all_diff_FOv (flat_map (fun l => l) (cons a (app l2 l3))).
Proof.
  induction l2; intros l l3.
    simpl in *. reflexivity.

    simpl in *.
    rewrite app_assoc.
    rewrite is_all_diff_FOv_app_comm2.
    rewrite app_assoc_reverse.
    induction a.
      simpl. apply IHl2.
  
      simpl. rewrite <- IHl2.
      rewrite app_assoc. rewrite <- IHl2.
      rewrite is_all_diff_FOv_lem7.
      rewrite is_in_FOvar_flat_map_rearr2. simpl.
      rewrite app_assoc.
      reflexivity.
Qed.

Lemma is_all_diff_FOv_app_flat_map : forall l2 a l3,
  is_all_diff_FOv (flat_map (fun l => l) (app l2 (cons a l3))) = true ->
  is_all_diff_FOv a = true.
Proof.
  induction l2; intros l l3 H.
    simpl in *. apply is_all_diff_FOv_app_t in H. apply H.

    simpl in H. apply is_all_diff_FOv_app_t in H.
    destruct H as [H1 H2].
    apply IHl2 in H2. assumption.
Qed.

Lemma is_all_diff_FOv_lem1 : forall l1 a l2 llv,
  is_all_diff_FOv (l1 ++ flat_map (fun l : list FOvariable => l) (l2 ++ a :: llv)) =
       true ->
is_all_diff_FOv (l1 ++ a) = true.
Proof.
  intros l1 a l2 llv H.
assert
  (is_all_diff_FOv (app l1 (flat_map (fun l => l) (l2 ++ a :: llv))) =
  is_all_diff_FOv (flat_map (fun l => l) (cons l1 (l2 ++ a :: llv)))) as Hass.
  reflexivity.
  rewrite Hass in H.
  rewrite app_comm_cons in H.
  rewrite is_all_diff_FOv_app_flat_map2 in H.
  simpl in H. rewrite app_assoc in H.
 apply is_all_diff_FOv_app_t in H.
  rewrite is_all_diff_FOv_app_comm.
  apply H.
Qed.

Lemma flat_map_app : forall {A B : Type} (l1 l2 : list A) (f : A -> list B),
  flat_map f (app l1 l2) =
  app (flat_map f l1) (flat_map f l2).
Proof.
  induction l1; intros l2 f. reflexivity.
  simpl. rewrite IHl1. rewrite app_assoc. reflexivity.
Qed.

Lemma is_all_diff_FOv_lem6 : forall l1 l2 l3 l4,
  is_all_diff_FOv (app l1 (app l2 (app l3 l4))) = true ->
  is_all_diff_FOv (app l1 l4) = true.
Proof.
  intros l1 l2 l3 l4 H.
  rewrite is_all_diff_FOv_app_comm in H.
  rewrite app_assoc_reverse in H.
  apply is_all_diff_FOv_app_t in H.
  rewrite app_assoc_reverse in H.
  destruct H as [H1 H2].
  apply is_all_diff_FOv_app_t in H2. destruct H2 as [H3 H4].
  rewrite is_all_diff_FOv_app_comm. assumption.
Qed.

Lemma is_all_diff_FOv_lem2 : forall l1 l2 llv a,
  is_all_diff_FOv (l1 ++ flat_map (fun l : list FOvariable => l) (l2 ++ a :: llv)) =
       true ->
is_all_diff_FOv (flat_map (fun l : list FOvariable => l) (l1 :: llv)) = true.
Proof.
  induction l1; intros l2 llv l H.
    simpl in *. rewrite flat_map_app in H.
    apply is_all_diff_FOv_app_t in H. destruct H as [H1 H2].
    simpl in H2. apply is_all_diff_FOv_app_t in H2. apply H2.

    simpl in *. case_eq (is_in_FOvar a (app l1 (flat_map (fun l => l)
      (app l2 (cons l llv))))); intros Hin; rewrite Hin in *.
        discriminate.
    rewrite is_in_FOvar_app.
    pose proof (is_in_FOvar_app_l _ _ _ Hin) as Hass1.
    pose proof (is_in_FOvar_app_r _ _ _ Hin) as Hass2.
    rewrite Hass1. rewrite flat_map_app in Hass2. 
   apply is_in_FOvar_app_r in Hass2. simpl in Hass2. 
    apply is_in_FOvar_app_r in Hass2. rewrite Hass2.
    apply IHl1 in H. assumption.
Qed.

Lemma is_all_diff_FOv_lem3 : forall l1 llv l0 l2 a,
is_all_diff_FOv
         (l1 ++ flat_map (fun l : list FOvariable => l) ((l0 :: l2) ++ a :: llv)) = true ->
is_all_diff_FOv (flat_map (fun l3 : list FOvariable => l3) (l1 :: llv)) = true.
Proof.
  intros l1 llv l0 l2 a H.
  simpl in *. rewrite is_all_diff_FOv_app_comm in H.
  rewrite app_assoc_reverse in H.
  apply is_all_diff_FOv_app_t in H.
  destruct H as [H1 H2].
  rewrite is_all_diff_FOv_app_comm in H2.
  apply is_all_diff_FOv_lem2 in H2. assumption.
Qed.

Lemma is_all_diff_FOv_lem4 : forall l0 l2 llv l1 a,
is_all_diff_FOv
         (l1 ++ flat_map (fun l : list FOvariable => l) ((l0 :: l2) ++ a :: llv)) = true ->
is_all_diff_FOv (l0 ++ flat_map (fun l3 : list FOvariable => l3) (l2 ++ llv)) = true.
Proof.
  intros l0 l2 llv l1 a H.
  simpl in *. apply is_all_diff_FOv_app_t in H.
  destruct H as [H1 H2]. rewrite flat_map_app in H2.
  rewrite flat_map_app. simpl in H2.
  rewrite app_assoc in H2. rewrite is_all_diff_FOv_app_comm in H2.
  rewrite app_assoc_reverse in H2.
  apply is_all_diff_FOv_app_t in H2.
  rewrite is_all_diff_FOv_app_comm in H2.
  rewrite app_assoc_reverse in H2. apply H2.
Qed.

Lemma is_all_diff_FOv_lem5 : forall l0 l2 a llv l1,
is_all_diff_FOv
         (l1 ++ flat_map (fun l : list FOvariable => l) ((l0 :: l2) ++ a :: llv)) = true ->
is_all_diff_FOv (flat_map (fun l3 : list FOvariable => l3) ((l0 :: l2) ++ a :: nil)) =
true.
Proof.
  intros l0 l2 a llv l1 H.
  apply is_all_diff_FOv_app_t in H.
  destruct H as [H1 H2].
  rewrite is_all_diff_FOv_app_flat_map2 in H2.
  rewrite is_all_diff_FOv_app_flat_map2.
  simpl in *. rewrite app_nil_r.
  rewrite flat_map_app in H2.
  rewrite app_assoc  in H2.
  rewrite app_assoc  in H2.
  rewrite is_all_diff_FOv_app_comm in H2.
  apply is_all_diff_FOv_app_t in H2.
  rewrite app_assoc.
  apply H2.
Qed.

Lemma att_allFO_x_fun4_l2' : forall l2 a x l,
  is_all_diff_FOv (flat_map (fun l => l) (cons (cons a nil) l2)) = true ->
  attached_allFO_x (fun4_l2' l x l2) a = false.
Proof.
  induction l2; intros y x l Hall.
    simpl in *. destruct l. reflexivity. simpl.
    destruct l; reflexivity.

    destruct l. simpl. reflexivity.
    simpl. destruct l.

simpl in Hall.
     case_eq (is_in_FOvar y (app a  (flat_map (fun l : list FOvariable => l) l2)));
        intros Hin; rewrite Hin in *. discriminate.
    apply att_allFO_x_fun4'.
      apply is_in_FOvar_app_l in Hin. assumption.

    destruct l2. apply att_allFO_x_fun4'.
    simpl in Hall. rewrite app_nil_r in Hall.
    case_eq (is_in_FOvar y a); intros Hin; rewrite Hin in *. discriminate.
      reflexivity.

      apply att_allFO_x_disjSO_rev.
        apply att_allFO_x_fun4'.

    simpl in Hall.
    case_eq (is_in_FOvar y (a ++ l0 ++ flat_map (fun l : list FOvariable => l) l2));
      intros Hin; rewrite Hin in *. discriminate.
    apply is_in_FOvar_app_l in Hin. assumption.

        apply IHl2.

    simpl in *.
  case_eq (is_in_FOvar y (a ++ l0 ++ flat_map (fun l : list FOvariable => l) l2));
      intros Hin; rewrite Hin in *. discriminate.
    apply is_in_FOvar_app_r in Hin. rewrite Hin.
    apply is_all_diff_FOv_app_t in Hall. apply Hall.
Qed.

Lemma att_exFO_x_fun4_l2' : forall l2 a x l,
  is_all_diff_FOv (flat_map (fun l => l) (cons (cons a nil) l2)) = true ->
  attached_exFO_x (fun4_l2' l x l2) a = false.
Proof.
  induction l2; intros y x l Hall.
    simpl in *. destruct l. reflexivity. simpl.
    destruct l; reflexivity.

    destruct l. simpl. reflexivity.
    simpl. destruct l.

simpl in Hall.
     case_eq (is_in_FOvar y (app a  (flat_map (fun l : list FOvariable => l) l2)));
        intros Hin; rewrite Hin in *. discriminate.
    apply att_exFO_x_fun4'.
      apply is_in_FOvar_app_l in Hin. assumption.

    destruct l2. apply att_exFO_x_fun4'.
    simpl in Hall. rewrite app_nil_r in Hall.
    case_eq (is_in_FOvar y a); intros Hin; rewrite Hin in *. discriminate.
      reflexivity.

      apply att_exFO_x_disjSO_rev.
        apply att_exFO_x_fun4'.

    simpl in Hall.
    case_eq (is_in_FOvar y (a ++ l0 ++ flat_map (fun l : list FOvariable => l) l2));
      intros Hin; rewrite Hin in *. discriminate.
    apply is_in_FOvar_app_l in Hin. assumption.

        apply IHl2.

    simpl in *.
  case_eq (is_in_FOvar y (a ++ l0 ++ flat_map (fun l : list FOvariable => l) l2));
      intros Hin; rewrite Hin in *. discriminate.
    apply is_in_FOvar_app_r in Hin. rewrite Hin.
    apply is_all_diff_FOv_app_t in Hall. apply Hall.
Qed.

Lemma ex_att_allFO_lv_fun4_l2' : forall l3 l2 l x,
  is_all_diff_FOv (flat_map (fun l => l) (app l2 (cons l3 nil))) = true ->
  ex_attached_allFO_lv (fun4_l2' l x l2) l3 = false.
Proof.
  induction l3; intros l2 l x Hall.
    simpl in *. reflexivity.

    simpl in *. rewrite att_allFO_x_fun4_l2'. apply IHl3.
    rewrite flat_map_app. rewrite flat_map_app in Hall.
    simpl in *. rewrite app_nil_r in *.
    rewrite is_all_diff_FOv_app_comm in Hall.
    rewrite is_all_diff_FOv_app_comm.
    simpl in Hall.
    case_eq (is_in_FOvar a (l3 ++ flat_map (fun l : list FOvariable => l) l2));
        intros H; rewrite H in *. discriminate.
     assumption.

    rewrite flat_map_app in Hall. rewrite is_all_diff_FOv_app_comm in Hall.
    simpl in *. rewrite app_nil_r in *.
    case_eq ( is_in_FOvar a (l3 ++ flat_map (fun l : list FOvariable => l) l2));
      intros H; rewrite H in *. discriminate.
    apply is_in_FOvar_app_r in H. rewrite H. apply is_all_diff_FOv_app_t in Hall.
    apply Hall.
Qed.

Lemma ex_att_exFO_lv_fun4_l2' : forall l3 l2 l x,
  is_all_diff_FOv (flat_map (fun l => l) (app l2 (cons l3 nil))) = true ->
  ex_attached_exFO_lv (fun4_l2' l x l2) l3 = false.
Proof.
  induction l3; intros l2 l x Hall.
    simpl in *. reflexivity.

    simpl in *. rewrite att_exFO_x_fun4_l2'. apply IHl3.
    rewrite flat_map_app. rewrite flat_map_app in Hall.
    simpl in *. rewrite app_nil_r in *.
    rewrite is_all_diff_FOv_app_comm in Hall.
    rewrite is_all_diff_FOv_app_comm.
    simpl in Hall.
    case_eq (is_in_FOvar a (l3 ++ flat_map (fun l : list FOvariable => l) l2));
        intros H; rewrite H in *. discriminate.
     assumption.

    rewrite flat_map_app in Hall. rewrite is_all_diff_FOv_app_comm in Hall.
    simpl in *. rewrite app_nil_r in *.
    case_eq ( is_in_FOvar a (l3 ++ flat_map (fun l : list FOvariable => l) l2));
      intros H; rewrite H in *. discriminate.
    apply is_in_FOvar_app_r in H. rewrite H. apply is_all_diff_FOv_app_t in Hall.
    apply Hall.
Qed.


Lemma ex_att_allFO_lv_fun4' : forall a l1 f x,
  is_all_diff_FOv (app l1 a) = true ->
  ex_attached_allFO_lv (fun4' f x l1) a = false.
Proof.
  induction a; intros l1 f x Hall.
    simpl in *. reflexivity.

    simpl in *. rewrite att_allFO_x_fun4'.
    apply IHa.
      rewrite is_all_diff_FOv_app_comm in *. simpl in Hall.
      case_eq (is_in_FOvar a (app a0 l1)); intros Hin; rewrite Hin in *.
        discriminate.
      assumption.

      rewrite is_all_diff_FOv_app_comm in *. simpl in Hall.
      case_eq (is_in_FOvar a (app a0 l1)); intros Hin; rewrite Hin in *.
        discriminate.
      apply is_in_FOvar_app_r in Hin. assumption.
Qed.

Lemma ex_att_exFO_lv_fun4' : forall a l1 f x,
  is_all_diff_FOv (app l1 a) = true ->
  ex_attached_exFO_lv (fun4' f x l1) a = false.
Proof.
  induction a; intros l1 f x Hall.
    simpl in *. reflexivity.

    simpl in *. rewrite att_exFO_x_fun4'.
    apply IHa.
      rewrite is_all_diff_FOv_app_comm in *. simpl in Hall.
      case_eq (is_in_FOvar a (app a0 l1)); intros Hin; rewrite Hin in *.
        discriminate.
      assumption.

      rewrite is_all_diff_FOv_app_comm in *. simpl in Hall.
      case_eq (is_in_FOvar a (app a0 l1)); intros Hin; rewrite Hin in *.
        discriminate.
      apply is_in_FOvar_app_r in Hin. assumption.
Qed.

Lemma ex_att_allFO_llv_fun4_l2'_all_diff : forall llv l1 l2 l x f,
  is_all_diff_FOv (flat_map (fun l => l) (app (cons l1 l2) llv)) = true ->
  ex_attached_allFO_llv (fun4_l2' (cons f l) x (cons l1 l2)) llv = false.
Proof.
  induction llv; intros l1 l2 l x f Hall.
    simpl in *. reflexivity.

    simpl in *. destruct l.
    pose proof (ex_att_allFO_llv_fun4'_all_diff l1 (cons a nil) f x) as H.
    simpl in H.
assert (is_all_diff_FOv (app l1 (app a nil)) = true) as H2. 
  apply is_all_diff_FOv_lem1 in Hall. rewrite app_nil_r. assumption.

    specialize (H H2). apply if_then_else_true_false in H. rewrite H.
    apply ex_att_allFO_llv_fun4'_all_diff.
    apply is_all_diff_FOv_lem2 in Hall. assumption.

    destruct l2.
    pose proof (ex_att_allFO_llv_fun4'_all_diff l1 (cons a nil) f x) as H.
    simpl in H.
assert (is_all_diff_FOv (app l1 (app a nil)) = true) as H2.
apply is_all_diff_FOv_lem1 in Hall. rewrite app_nil_r. assumption.

    specialize (H H2). apply if_then_else_true_false in H. rewrite H.
    apply ex_att_allFO_llv_fun4'_all_diff.
    apply is_all_diff_FOv_lem2 in Hall. assumption.

    rewrite ex_att_allFO_lv_disjSO_f_rev.
    apply ex_att_allFO_llv_disjSO_f_rev.
      apply ex_att_allFO_llv_fun4'_all_diff.

        apply is_all_diff_FOv_lem3 in Hall. assumption.

      apply IHllv.

      apply is_all_diff_FOv_lem4 in Hall. assumption.

        apply ex_att_allFO_lv_fun4'.
        apply is_all_diff_FOv_lem1 in Hall. assumption.

        apply ex_att_allFO_lv_fun4_l2'.

        apply is_all_diff_FOv_lem5 in Hall. assumption.
Qed.

Lemma ex_att_exFO_llv_fun4_l2'_all_diff : forall llv l1 l2 l x f,
  is_all_diff_FOv (flat_map (fun l => l) (app (cons l1 l2) llv)) = true ->
  ex_attached_exFO_llv (fun4_l2' (cons f l) x (cons l1 l2)) llv = false.
Proof.
  induction llv; intros l1 l2 l x f Hall.
    simpl in *. reflexivity.

    simpl in *. destruct l.
    pose proof (ex_att_exFO_llv_fun4'_all_diff l1 (cons a nil) f x) as H.
    simpl in H.
assert (is_all_diff_FOv (app l1 (app a nil)) = true) as H2. 
  apply is_all_diff_FOv_lem1 in Hall. rewrite app_nil_r. assumption.

    specialize (H H2). apply if_then_else_true_false in H. rewrite H.
    apply ex_att_exFO_llv_fun4'_all_diff.
    apply is_all_diff_FOv_lem2 in Hall. assumption.

    destruct l2.
    pose proof (ex_att_exFO_llv_fun4'_all_diff l1 (cons a nil) f x) as H.
    simpl in H.
assert (is_all_diff_FOv (app l1 (app a nil)) = true) as H2.
apply is_all_diff_FOv_lem1 in Hall. rewrite app_nil_r. assumption.

    specialize (H H2). apply if_then_else_true_false in H. rewrite H.
    apply ex_att_exFO_llv_fun4'_all_diff.
    apply is_all_diff_FOv_lem2 in Hall. assumption.

    rewrite ex_att_exFO_lv_disjSO_f_rev.
    apply ex_att_exFO_llv_disjSO_f_rev.
      apply ex_att_exFO_llv_fun4'_all_diff.

        apply is_all_diff_FOv_lem3 in Hall. assumption.

      apply IHllv.

      apply is_all_diff_FOv_lem4 in Hall. assumption.

        apply ex_att_exFO_lv_fun4'.
        apply is_all_diff_FOv_lem1 in Hall. assumption.

        apply ex_att_exFO_lv_fun4_l2'.

        apply is_all_diff_FOv_lem5 in Hall. assumption.
Qed.

Lemma ex_att_allFO_llv_rep_pred_fun4_l2' : forall l l0 alpha x a P,
   ex_attached_allFO_llv alpha (app l0 a) = false ->
is_all_diff_FOv
         (app (cons x nil) (flat_map (fun l : list FOvariable => l)
            (app l0 a))) = true ->
ex_FOvar_x_ll x l0 = false ->
ex_attached_allFO_llv (replace_pred alpha P x (fun4_l2' l x l0)) a = false.
Proof.
  induction l; intros l0 alpha x llv P Hat Hall Hex.
    simpl in *.
    apply ex_att_allFO_llv_app_f_r in Hat.
    apply ex_attached_allFO_llv_rep_pred. reflexivity.
    assumption.

    simpl. destruct l. destruct l0.
      apply ex_attached_allFO_llv_rep_pred. reflexivity.
      assumption.

      apply ex_att_allFO_llv_rep_pred_fun4'.

        pose proof (ex_att_allFO_llv_app_f_l _ _ _ Hat) as H1.
        pose proof (ex_att_allFO_llv_app_f_r _ _ _ Hat) as H2.
        simpl in *. rewrite H2.
        case_eq (ex_attached_allFO_lv alpha l); intros HH;
          rewrite HH in *. discriminate. reflexivity.

        rewrite flat_map_app in Hall. simpl in *.
        rewrite app_assoc_reverse in Hall.
        rewrite is_all_diff_FOv_app_comm in Hall.
        rewrite app_assoc_reverse in Hall.
case_eq (is_in_FOvar x
           (l ++
            flat_map (fun l : list FOvariable => l) l0 ++
            flat_map (fun l : list FOvariable => l) llv)); intros HH;
    rewrite HH in *. discriminate.
        apply is_all_diff_FOv_app_t in Hall.
        destruct Hall as [H1 H2].
        rewrite is_all_diff_FOv_app_comm. assumption.

    simpl in Hex. case_eq (is_in_FOvar x l); intros H;
      rewrite H in *. discriminate. reflexivity.

    destruct l0. 
      apply ex_attached_allFO_llv_rep_pred. reflexivity.
      assumption.
    destruct l1. 
      apply ex_att_allFO_llv_rep_pred_fun4'.
        simpl in *. assumption.
        simpl in *.
case_eq (is_in_FOvar x (l0 ++ flat_map (fun l : list FOvariable => l) llv)); 
intros Hin; rewrite Hin in *. discriminate. assumption.

      simpl in Hex. case_eq (is_in_FOvar x l0);
        intros H; rewrite H in *. discriminate. reflexivity.

      apply ex_attached_allFO_llv_rep_pred2.
 
      apply ex_att_allFO_llv_disjSO_f_rev.
      apply ex_att_allFO_llv_fun4'_all_diff.

        simpl in Hall. rewrite is_all_diff_FOv_app_comm in Hall.
        rewrite app_assoc_reverse in Hall.
case_eq (is_in_FOvar x (l0 ++ l1 ++ flat_map (fun l : list FOvariable => l) (l2 ++ llv)));
  intros Hin; rewrite Hin in *. discriminate.
        apply is_all_diff_FOv_app_t in Hall. destruct Hall as [H1 H2].
        rewrite flat_map_app in H2. rewrite app_assoc_reverse in H2.
        apply is_all_diff_FOv_app_t in H2. destruct H2 as [H3 H4].
        rewrite is_all_diff_FOv_app_comm in H4.
        simpl. assumption.


      apply ex_att_allFO_llv_fun4_l2'_all_diff.
        simpl in Hall.
case_eq (is_in_FOvar x (l0 ++ l1 ++ flat_map (fun l : list FOvariable => l) (l2 ++ llv)));
intros Hin; rewrite Hin in *. discriminate.
        apply is_all_diff_FOv_app_t in Hall.
        apply Hall.

      apply ex_att_allFO_llv_app_f_r in Hat. assumption.
  
      apply att_allFO_x_disjSO_rev.
      apply att_allFO_x_fun4'. simpl in Hex.
      case_eq (is_in_FOvar x l0); intros H; rewrite H in *.
        discriminate. reflexivity.

      apply att_allFO_x_fun4_l2'. simpl in *.
      case_eq (is_in_FOvar x (l0 ++ l1 ++ flat_map (fun l : list FOvariable => l) (l2 ++ llv)));
          intros Hin; rewrite Hin in *. discriminate.
      apply is_in_FOvar_app_r in Hin. rewrite flat_map_app in Hin.
      rewrite app_assoc in Hin.
      apply is_in_FOvar_app_l in Hin. rewrite Hin.
      apply is_all_diff_FOv_app_t in Hall. destruct Hall as [H1 H2].
      rewrite flat_map_app in H2. rewrite app_assoc in H2.
      apply is_all_diff_FOv_app_t in H2. destruct H2 as [H3 H4].
      assumption.
Qed.

Lemma ex_att_exFO_llv_rep_pred_fun4_l2' : forall l l0 alpha x a P,
   ex_attached_exFO_llv alpha (app l0 a) = false ->
is_all_diff_FOv
         (app (cons x nil) (flat_map (fun l : list FOvariable => l)
            (app l0 a))) = true ->
ex_FOvar_x_ll x l0 = false ->
ex_attached_exFO_llv (replace_pred alpha P x (fun4_l2' l x l0)) a = false.
Proof.
  induction l; intros l0 alpha x llv P Hat Hall Hex.
    simpl in *.
    apply ex_att_exFO_llv_app_f_r in Hat.
    apply ex_attached_exFO_llv_rep_pred. reflexivity.
    assumption.

    simpl. destruct l. destruct l0.
      apply ex_attached_exFO_llv_rep_pred. reflexivity.
      assumption.

      apply ex_att_exFO_llv_rep_pred_fun4'.

        pose proof (ex_att_exFO_llv_app_f_l _ _ _ Hat) as H1.
        pose proof (ex_att_exFO_llv_app_f_r _ _ _ Hat) as H2.
        simpl in *. rewrite H2.
        case_eq (ex_attached_exFO_lv alpha l); intros HH;
          rewrite HH in *. discriminate. reflexivity.

        rewrite flat_map_app in Hall. simpl in *.
        rewrite app_assoc_reverse in Hall.
        rewrite is_all_diff_FOv_app_comm in Hall.
        rewrite app_assoc_reverse in Hall.
case_eq (is_in_FOvar x
           (l ++
            flat_map (fun l : list FOvariable => l) l0 ++
            flat_map (fun l : list FOvariable => l) llv)); intros HH;
    rewrite HH in *. discriminate.
        apply is_all_diff_FOv_app_t in Hall.
        destruct Hall as [H1 H2].
        rewrite is_all_diff_FOv_app_comm. assumption.

    simpl in Hex. case_eq (is_in_FOvar x l); intros H;
      rewrite H in *. discriminate. reflexivity.

    destruct l0. 
      apply ex_attached_exFO_llv_rep_pred. reflexivity.
      assumption.
    destruct l1. 
      apply ex_att_exFO_llv_rep_pred_fun4'.
        simpl in *. assumption.
        simpl in *.
case_eq (is_in_FOvar x (l0 ++ flat_map (fun l : list FOvariable => l) llv)); 
intros Hin; rewrite Hin in *. discriminate. assumption.

      simpl in Hex. case_eq (is_in_FOvar x l0);
        intros H; rewrite H in *. discriminate. reflexivity.

      apply ex_attached_exFO_llv_rep_pred2.
 
      apply ex_att_exFO_llv_disjSO_f_rev.
      apply ex_att_exFO_llv_fun4'_all_diff.

        simpl in Hall. rewrite is_all_diff_FOv_app_comm in Hall.
        rewrite app_assoc_reverse in Hall.
case_eq (is_in_FOvar x (l0 ++ l1 ++ flat_map (fun l : list FOvariable => l) (l2 ++ llv)));
  intros Hin; rewrite Hin in *. discriminate.
        apply is_all_diff_FOv_app_t in Hall. destruct Hall as [H1 H2].
        rewrite flat_map_app in H2. rewrite app_assoc_reverse in H2.
        apply is_all_diff_FOv_app_t in H2. destruct H2 as [H3 H4].
        rewrite is_all_diff_FOv_app_comm in H4.
        simpl. assumption.


      apply ex_att_exFO_llv_fun4_l2'_all_diff.
        simpl in Hall.
case_eq (is_in_FOvar x (l0 ++ l1 ++ flat_map (fun l : list FOvariable => l) (l2 ++ llv)));
intros Hin; rewrite Hin in *. discriminate.
        apply is_all_diff_FOv_app_t in Hall.
        apply Hall.

      apply ex_att_exFO_llv_app_f_r in Hat. assumption.
  
      apply att_exFO_x_disjSO_rev.
      apply att_exFO_x_fun4'. simpl in Hex.
      case_eq (is_in_FOvar x l0); intros H; rewrite H in *.
        discriminate. reflexivity.

      apply att_exFO_x_fun4_l2'. simpl in *.
      case_eq (is_in_FOvar x (l0 ++ l1 ++ flat_map (fun l : list FOvariable => l) (l2 ++ llv)));
          intros Hin; rewrite Hin in *. discriminate.
      apply is_in_FOvar_app_r in Hin. rewrite flat_map_app in Hin.
      rewrite app_assoc in Hin.
      apply is_in_FOvar_app_l in Hin. rewrite Hin.
      apply is_all_diff_FOv_app_t in Hall. destruct Hall as [H1 H2].
      rewrite flat_map_app in H2. rewrite app_assoc in H2.
      apply is_all_diff_FOv_app_t in H2. destruct H2 as [H3 H4].
      assumption.
Qed.

Lemma ex_att_allFO_llv_app_f_rev: forall l1 l2 alpha,
  ex_attached_allFO_llv alpha l1 = false ->
  ex_attached_allFO_llv alpha l2 = false ->
  ex_attached_allFO_llv alpha (app l1 l2) = false.
Proof.
  induction l1; intros l2 alpha H1 H2. assumption.
  simpl in *. case_eq (ex_attached_allFO_lv alpha a);
    intros H; rewrite H in *. discriminate.
  apply IHl1; assumption.
Qed.

Lemma ex_att_exFO_llv_app_f_rev: forall l1 l2 alpha,
  ex_attached_exFO_llv alpha l1 = false ->
  ex_attached_exFO_llv alpha l2 = false ->
  ex_attached_exFO_llv alpha (app l1 l2) = false.
Proof.
  induction l1; intros l2 alpha H1 H2. assumption.
  simpl in *. case_eq (ex_attached_exFO_lv alpha a);
    intros H; rewrite H in *. discriminate.
  apply IHl1; assumption.
Qed.

Lemma is_all_diff_FOv_lem8 : forall l0 a lllv,
is_all_diff_FOv
         (flat_map (fun l : list FOvariable => l)
            (l0 ++ a ++ flat_map (fun l : list (list FOvariable) => l) lllv)) = true ->
is_all_diff_FOv
  (flat_map (fun l1 : list FOvariable => l1)
     (l0 ++ flat_map (fun l1 : list (list FOvariable) => l1) lllv)) = true.
Proof.
  intros l0 a lllv H.
  rewrite flat_map_app.
  rewrite flat_map_app in H.
  rewrite is_all_diff_FOv_app_comm in H.
  rewrite flat_map_app in H. rewrite app_assoc_reverse in H.
  apply is_all_diff_FOv_app_t in H. 
  rewrite is_all_diff_FOv_app_comm in H. apply H.
Qed.

Lemma is_in_FOvar_flat_map_rearr3 : forall l0 a lllv x,
is_in_FOvar x
      (flat_map (fun l : list FOvariable => l)
         (l0 ++ a ++ flat_map (fun l : list (list FOvariable) => l) lllv)) = false ->
is_in_FOvar x
    (flat_map (fun l1 : list FOvariable => l1)
       (l0 ++ flat_map (fun l1 : list (list FOvariable) => l1) lllv)) = false.
Proof.
  intros l0 a lllv x H.
  rewrite flat_map_app.
  rewrite flat_map_app in H.
  rewrite is_in_FOvar_app.
  rewrite (is_in_FOvar_app_l _ _ _ H).
  rewrite flat_map_app in H.
  do 2 apply is_in_FOvar_app_r in H.
  assumption.
Qed.



Lemma ex_att_allFO_lllv_rep_pred_fun4_l2' : forall lllv alpha l0 l x a,
   ex_attached_allFO_lllv alpha (l0 :: lllv) = false ->
is_all_diff_FOv
         (app (cons x nil) (flat_map (fun l : list FOvariable => l)
            (flat_map (fun l : list (list FOvariable) => l) (l0 :: lllv)))) = true ->
ex_attached_allFO_lllv (replace_pred alpha a x (fun4_l2' l x l0)) lllv = false.
Proof.
  induction lllv; intros alpha l0 l x P Hat Hall.
    simpl in *. reflexivity.

    simpl in *. case_eq (ex_attached_allFO_llv alpha l0);
      intros Hat2; rewrite Hat2 in *. discriminate.
    case_eq (ex_attached_allFO_llv alpha a); intros Hat3;
      rewrite Hat3 in *. discriminate.
    rewrite ex_att_allFO_llv_rep_pred_fun4_l2'.
    apply IHlllv. rewrite Hat2. assumption.

    case_eq (is_in_FOvar x
           (flat_map (fun l : list FOvariable => l)
              (l0 ++ a ++ flat_map (fun l : list (list FOvariable) => l) lllv)));
      intros H; rewrite H in *. discriminate.

      rewrite is_in_FOvar_flat_map_rearr3 with (a := a).

apply is_all_diff_FOv_lem8 in Hall. all : try assumption.

    apply ex_att_allFO_llv_app_f_rev; assumption.

    simpl.
    case_eq (is_in_FOvar x
           (flat_map (fun l : list FOvariable => l)
              (l0 ++ a ++ flat_map (fun l : list (list FOvariable) => l) lllv)));
      intros H; rewrite H in *. discriminate.
      rewrite (flat_map_app l0). rewrite is_in_FOvar_app.
      rewrite flat_map_app in H. rewrite (is_in_FOvar_app_l _ _ _ H).
      apply is_in_FOvar_app_r in H. rewrite flat_map_app in H.
      rewrite (is_in_FOvar_app_l _ _ _ H).
      rewrite flat_map_app in Hall. rewrite flat_map_app in Hall.
      rewrite app_assoc in Hall. apply is_all_diff_FOv_app_t in Hall.
      apply Hall.

      case_eq (is_in_FOvar x
           (flat_map (fun l : list FOvariable => l)
              (l0 ++ a ++ flat_map (fun l : list (list FOvariable) => l) lllv)));
        intros Hin; rewrite Hin in *. discriminate.
      rewrite flat_map_app in Hin. apply is_in_FOvar_app_l in Hin.
      rewrite <- is_in_FOvar_ex_Fovar_x_ll. assumption.
Qed.

Lemma ex_att_exFO_lllv_rep_pred_fun4_l2' : forall lllv alpha l0 l x a,
   ex_attached_exFO_lllv alpha (l0 :: lllv) = false ->
is_all_diff_FOv
         (app (cons x nil) (flat_map (fun l : list FOvariable => l)
            (flat_map (fun l : list (list FOvariable) => l) (l0 :: lllv)))) = true ->
ex_attached_exFO_lllv (replace_pred alpha a x (fun4_l2' l x l0)) lllv = false.
Proof.
  induction lllv; intros alpha l0 l x P Hat Hall.
    simpl in *. reflexivity.

    simpl in *. case_eq (ex_attached_exFO_llv alpha l0);
      intros Hat2; rewrite Hat2 in *. discriminate.
    case_eq (ex_attached_exFO_llv alpha a); intros Hat3;
      rewrite Hat3 in *. discriminate.
    rewrite ex_att_exFO_llv_rep_pred_fun4_l2'.
    apply IHlllv. rewrite Hat2. assumption.

    case_eq (is_in_FOvar x
           (flat_map (fun l : list FOvariable => l)
              (l0 ++ a ++ flat_map (fun l : list (list FOvariable) => l) lllv)));
      intros H; rewrite H in *. discriminate.

      rewrite is_in_FOvar_flat_map_rearr3 with (a := a).

apply is_all_diff_FOv_lem8 in Hall. all : try assumption.

    apply ex_att_exFO_llv_app_f_rev; assumption.

    simpl.
    case_eq (is_in_FOvar x
           (flat_map (fun l : list FOvariable => l)
              (l0 ++ a ++ flat_map (fun l : list (list FOvariable) => l) lllv)));
      intros H; rewrite H in *. discriminate.
      rewrite (flat_map_app l0). rewrite is_in_FOvar_app.
      rewrite flat_map_app in H. rewrite (is_in_FOvar_app_l _ _ _ H).
      apply is_in_FOvar_app_r in H. rewrite flat_map_app in H.
      rewrite (is_in_FOvar_app_l _ _ _ H).
      rewrite flat_map_app in Hall. rewrite flat_map_app in Hall.
      rewrite app_assoc in Hall. apply is_all_diff_FOv_app_t in Hall.
      apply Hall.

      case_eq (is_in_FOvar x
           (flat_map (fun l : list FOvariable => l)
              (l0 ++ a ++ flat_map (fun l : list (list FOvariable) => l) lllv)));
        intros Hin; rewrite Hin in *. discriminate.
      rewrite flat_map_app in Hin. apply is_in_FOvar_app_l in Hin.
      rewrite <- is_in_FOvar_ex_Fovar_x_ll. assumption.
Qed.

(* Left it here. 19/09. Try strengthening hypothese (I think). *)

Lemma ex_FOvar_l_ll_rep_FOv_pre : forall a f ym xn lllv,
  is_in_FOvar (Var xn) a = false ->
  is_in_FOvar (Var ym) a = false ->
  ~ a = nil ->
  is_all_diff_FOv (app a (flat_map (fun l => l) (flat_map (fun l => l) lllv))) = true ->
ex_FOvar_x_ll f (flat_map (fun l : list (list FOvariable) => l) lllv) = false ->
  ex_FOvar_x_ll (Var xn) (flat_map (fun l => l) lllv) = false ->
  ex_FOvar_l_ll (FOvars_in (replace_FOv (fun4' f (Var ym) a) (Var ym) (Var xn)))
    (flat_map (fun l => l) lllv)  = false.
Proof.
  induction  a; intros [zn] ym xn lllv Hin1 Hin2 Hnil H2 H4 H3.
    contradiction (Hnil eq_refl).

    simpl in *. destruct a as [un]. case_eq (beq_nat xn un);
      intros Hbeq; rewrite Hbeq in *. discriminate.
    case_eq (beq_nat ym un); intros Hbeq2; rewrite Hbeq2 in *.
      discriminate.
    case_eq (is_in_FOvar (Var un)
         (a0 ++ flat_map (fun l : list FOvariable => l) (flat_map (fun l : list (list FOvariable) => l) lllv)));
      intros Hin3; rewrite Hin3 in *. discriminate.
    simpl.
    pose proof (is_in_FOvar_app_r _ _ _ Hin3) as Hin3'.
      rewrite is_in_FOvar_ex_Fovar_x_ll in Hin3'.
    rewrite Hin3'. case_eq (beq_nat ym zn); intros Hbeq3.
      simpl. rewrite H3. rewrite Hin3'.
    case_eq a0. intros Ha0. rewrite Ha0 in *.
      simpl. rewrite <- beq_nat_refl. rewrite Hbeq2. simpl. rewrite H3.
      rewrite Hin3'. reflexivity.
    intros aa laa Hlaa. rewrite <- Hlaa. apply IHa; try assumption.
    rewrite Hlaa. discriminate.
    simpl. rewrite Hin3'. rewrite H4.
    destruct a0. simpl in *. rewrite <- beq_nat_refl. rewrite Hbeq2.
    simpl. rewrite Hin3'. rewrite H3. reflexivity.
    apply IHa; try assumption. discriminate.
Qed.

Lemma ex_FOvar_l_ll_app_rev : forall l1 l2 l,
  ex_FOvar_l_ll l1 l = false ->
  ex_FOvar_l_ll l2 l = false ->
  ex_FOvar_l_ll (app l1 l2) l = false.
Proof.
  induction l1; intros l2 l H1 H2. assumption.
  simpl in *. case_eq (ex_FOvar_x_ll a l);
    intros Hex; rewrite Hex in *. discriminate.
  apply IHl1; assumption.
Qed.

Lemma fun4'_rep_FOv : forall l x y z,
  is_in_FOvar y l = false ->
  is_in_FOvar x l = false ->
  ~ x = z ->
  ~ y = z ->
  ~ l = nil ->
  replace_FOv (fun4' z y l) y x =
  fun4' z x l.
Proof.
  induction l; intros [xn] [ym] [zn] H1 H4 H2 H3 Hnil. simpl.
    contradiction (Hnil eq_refl).

    simpl. destruct a as [un]. 
    simpl in H1.
    case_eq (beq_nat ym un); intros Hbeq;
      rewrite Hbeq in *. discriminate.
    case_eq l. intros Hnil2.
      rewrite FOvar_neq. 2 : assumption.
      simpl. rewrite Hbeq. rewrite <- beq_nat_refl.
      reflexivity.
    intros v lv Hl. rewrite <- Hl.
    rewrite (FOvar_neq ym zn).
    rewrite IHl; try assumption. reflexivity.
    simpl in H4. case_eq (beq_nat xn un); intros HH; rewrite HH in *.
      discriminate. assumption.
    simpl in H4. case_eq (beq_nat xn un); intros HH; rewrite HH in *.
      discriminate. intros HH2. inversion HH2 as [HH3].
      rewrite HH3 in *. rewrite <- beq_nat_refl in *. discriminate.
    intros HH2. inversion HH2 as [HH3]. rewrite HH3 in *.
      rewrite <- beq_nat_refl in Hbeq. discriminate.
    rewrite Hl. discriminate.
    assumption.
Qed.

Lemma ex_FOvar_x_ll_app_l : forall l1 l2 x,
  ex_FOvar_x_ll x (app l1 l2) = false ->
  ex_FOvar_x_ll x l1 = false.
Proof.
  induction l1; intros l2 x H. reflexivity.
  simpl in *. case_eq (is_in_FOvar x a);
    intros Hin; rewrite Hin in *. discriminate.
    apply (IHl1 _ _ H).
Qed.

Lemma ex_FOvar_x_ll_app_r : forall l1 l2 x,
  ex_FOvar_x_ll x (app l1 l2) = false ->
  ex_FOvar_x_ll x l2 = false.
Proof.
  induction l1; intros l2 x H. assumption.
  simpl in *. case_eq (is_in_FOvar x a);
    intros Hin; rewrite Hin in *. discriminate.
    apply (IHl1 _ _ H).
Qed.

Lemma ex_FOvar_l_ll_rep_FOv : forall llv lllv l2 x xn,
is_in_FOvar x l2 = false ->
ex_FOvar_x_ll x llv = false ->
~ llv = nil ->
length l2 = length llv ->
 ex_FOvar_x_ll (Var xn) (llv ++ flat_map (fun l : list (list FOvariable) => l) lllv) =
     false ->
 is_all_diff_FOv
       (app l2 (flat_map (fun l : list FOvariable => l)
          (llv ++ flat_map (fun l : list (list FOvariable) => l) lllv)) )= true ->
ex_FOvar_l_ll (FOvars_in (replace_FOv (fun4_l2' l2 x llv) x (Var xn)))
  (flat_map (fun l : list (list FOvariable) => l) lllv) = false.
Proof.
  induction llv; intros lllv l2 [ym] xn Hin Hex Hnil Hl H1 H2.
    contradiction (Hnil eq_refl).

    case_eq a. intros Ha; rewrite Ha in *.
    simpl in *. case_eq llv. intros Hllv.
    rewrite Hllv in *. simpl in *. destruct l2. discriminate.
    destruct l2. 2 : discriminate. simpl. destruct f as [zn].
    simpl in Hin. case_eq (beq_nat ym zn); intros Hbeq;
      rewrite Hbeq in *. discriminate. rewrite <- beq_nat_refl.
    simpl. rewrite H1. simpl in H2.
    case_eq (is_in_FOvar (Var zn)
         (flat_map (fun l : list FOvariable => l)
            (flat_map (fun l : list (list FOvariable) => l) lllv)));
      intros HH; rewrite HH in *. discriminate.
    rewrite is_in_FOvar_ex_Fovar_x_ll in HH. rewrite HH.
    reflexivity.

    intros l ll Hllv. rewrite <- Hllv. destruct l2.
    simpl in *. rewrite Hllv in *. discriminate.
    simpl. destruct f as [zn].
    case_eq l2. intros Hl2. simpl.
      rewrite <- beq_nat_refl.
      case_eq (beq_nat ym zn); intros Hbeq.
        simpl in *.
        apply ex_FOvar_x_ll_app_r in H1. rewrite H1.
          reflexivity.

        simpl. simpl in H2.
        case_eq (is_in_FOvar (Var zn)
         (l2 ++
          flat_map (fun l : list FOvariable => l)
            (llv ++ flat_map (fun l : list (list FOvariable) => l) lllv)));
          intros HH; rewrite HH in *. discriminate.
        apply is_in_FOvar_app_r in HH. rewrite flat_map_app in HH.
        apply is_in_FOvar_app_r in HH. rewrite is_in_FOvar_ex_Fovar_x_ll in HH.
        rewrite HH. apply ex_FOvar_x_ll_app_r in H1. rewrite H1. reflexivity.

    intros v lv Hl2. rewrite <- Hl2. rewrite Hllv.
    rewrite <- Hllv. simpl. rewrite <- beq_nat_refl.
    simpl in Hin. case_eq (beq_nat ym zn); intros Hbeq; rewrite Hbeq in *.
      discriminate.
    simpl. pose proof (ex_FOvar_x_ll_app_r _ _ _ H1) as H1'.
    rewrite H1'. simpl in H2.
    case_eq (       is_in_FOvar (Var zn)
         (l2 ++
          flat_map (fun l : list FOvariable => l)
            (llv ++ flat_map (fun l : list (list FOvariable) => l) lllv)));
      intros HH; rewrite HH in *. discriminate.
    pose proof (is_in_FOvar_app_r _ _ _ HH) as HH'.
    rewrite is_in_FOvar_ex_Fovar_x_ll in HH'.
    pose proof (ex_FOvar_x_ll_app_r _ _ _ HH') as HH''. rewrite HH''.     
    apply IHllv; try assumption. rewrite Hllv. discriminate. 
    rewrite Hllv in *. rewrite Hl2 in *. simpl. inversion Hl.
    reflexivity.

    intros a' aa' Ha. rewrite <- Ha.
    case_eq l2. intros Hl2. rewrite Hl2 in *. discriminate.
    intros z lz Hl2. simpl.

    simpl in Hex. case_eq (is_in_FOvar (Var ym) a);
      intros Hin2; rewrite Hin2 in *. discriminate.
    rewrite Hl2 in Hl. simpl in Hl. inversion Hl as [HH].
    simpl in H1. case_eq (is_in_FOvar (Var xn) a);
      intros Hin3; rewrite Hin3 in *. discriminate.
    assert (~ a = nil) as Hanil. rewrite Ha. discriminate.
    pose proof (is_all_diff_FOv_app_t _ _ H2) as H2'.
    destruct H2' as [H2a H2b].
    simpl in *. case_eq llv. intros Hllv.
    rewrite Hllv in *. simpl in *. destruct lz. 
    simpl. apply ex_FOvar_l_ll_rep_FOv_pre with (lllv := lllv);
      try assumption.

rewrite Hl2 in H2. simpl in H2. case_eq (is_in_FOvar z
         (a ++ flat_map (fun l : list FOvariable => l) (flat_map (fun l : list (list FOvariable) => l) lllv)));
        intros HH2; rewrite HH2 in *. discriminate.
        apply is_in_FOvar_app_r in HH2. rewrite is_in_FOvar_ex_Fovar_x_ll in HH2. assumption.

    rewrite Hl2 in *. discriminate.

    intros lv llv' Hllv. rewrite <- Hllv.
    case_eq lz. intros Hlz. rewrite Hlz in *. rewrite Hllv in *.
    rewrite Hl2 in *. discriminate.
    intros z' lz' Hlz. rewrite <- Hlz.
    simpl.

    apply ex_FOvar_l_ll_app_rev.
      apply ex_FOvar_x_ll_app_r in H1.
      apply ex_FOvar_l_ll_rep_FOv_pre with (lllv := lllv);
        try assumption.

      rewrite flat_map_app in H2b. rewrite app_assoc in H2b.
      rewrite is_all_diff_FOv_app_comm2 in H2b.
      rewrite app_assoc_reverse in H2b.
      apply is_all_diff_FOv_app_t in H2b. apply H2b.

rewrite Hl2 in H2. simpl in H2. case_eq (is_in_FOvar z
         (lz ++
          a ++
          flat_map (fun l : list FOvariable => l) (llv ++ flat_map (fun l : list (list FOvariable) => l) lllv)));
        intros HH2; rewrite HH2 in *. discriminate.
        apply is_in_FOvar_app_r in HH2.
        apply is_in_FOvar_app_r in HH2. rewrite is_in_FOvar_ex_Fovar_x_ll in HH2.
        apply ex_FOvar_x_ll_app_r in HH2. assumption.

      apply IHllv; try assumption.
        rewrite Hl2 in Hin. simpl in Hin.
        destruct z as [vn]. case_eq (beq_nat ym vn);
          intros Hbeq2; rewrite Hbeq2 in *. discriminate.
        assumption.
        rewrite Hllv. discriminate.

        rewrite Hl2 in *.
        simpl in H2.
        case_eq (is_in_FOvar z
         (lz ++
          a ++
          flat_map (fun l : list FOvariable => l) (llv ++ flat_map (fun l : list (list FOvariable) => l) lllv)));
          intros Hin4; rewrite Hin4 in *. discriminate.
        clear Hin4. clear H2b.
        rewrite app_assoc in H2. rewrite is_all_diff_FOv_app_comm2 in H2.
        rewrite app_assoc_reverse in H2. apply is_all_diff_FOv_app_t in H2.
        apply H2.
Qed.

Lemma ex_FOvar_l_ll_app_f_l_rev : forall l1 l2 l,
ex_FOvar_l_ll l (l1 ++ l2) = false -> ex_FOvar_l_ll l l1 = false.
Proof.
  induction l1; intros l2 l H.
    simpl in *. induction l.
    reflexivity. simpl. apply IHl. simpl in H.  
    case_eq (ex_FOvar_x_ll a l2); intros Hex; rewrite Hex in *.
      discriminate. assumption.

    simpl in *. induction l. reflexivity.
    simpl in *. case_eq (is_in_FOvar a0 a); intros Hin;
      rewrite Hin in *. discriminate.
    case_eq (ex_FOvar_x_ll a0 (app l1 l2));
      intros H2; rewrite H2 in *. discriminate.
    apply ex_FOvar_x_ll_app_l in H2. rewrite H2.
    apply IHl.
    assumption.
Qed.

Lemma ex_FOvar_l_ll_rep_pred : forall alpha llv lllv l2 x a,
  is_in_FOvar x l2 = false ->
  ex_FOvar_x_ll x llv = false ->
  ~ llv = nil ->
  length l2 = length llv ->
  ex_FOvar_l_ll (FOvars_in alpha)
    (flat_map (fun l => l) (cons llv lllv)) = false ->
  is_all_diff_FOv (app l2 (flat_map (fun l => l) (flat_map (fun l => l)
    (cons llv lllv))) )= true ->
  ex_FOvar_l_ll (FOvars_in (replace_pred alpha a x (fun4_l2' l2 x llv)))
    (flat_map (fun l => l) lllv) = false.
Proof.
  induction alpha; intros llv lllv l2 x P Hin Hex Hllv Hl H1 H2.
    destruct p as [ Qm]; destruct f as [xn].
    destruct P as [Pn]. simpl in *.
    apply if_then_else_tf in H1. destruct H1 as [H1 Hc]. clear Hc.
    case_eq (beq_nat Pn Qm); intros Hbeq.
      apply ex_FOvar_l_ll_rep_FOv; try assumption.

      simpl. apply ex_FOvar_x_ll_app_r in H1.
      rewrite H1. reflexivity.

    destruct f as [xn]; destruct f0 as [ym]. destruct P. simpl in *.
    case_eq (ex_FOvar_x_ll (Var xn) (app llv (flat_map (fun l => l) lllv)));
      intros Hex1; rewrite Hex1 in *. discriminate.
    case_eq (ex_FOvar_x_ll (Var ym) (app llv (flat_map (fun l => l) lllv)));
      intros Hex2; rewrite Hex2 in *. discriminate.
    apply ex_FOvar_x_ll_app_r in Hex1.
    apply ex_FOvar_x_ll_app_r in Hex2.
    rewrite Hex1. rewrite Hex2. reflexivity.

    destruct f as [xn]; destruct f0 as [ym]. destruct P. simpl in *.
    case_eq (ex_FOvar_x_ll (Var xn) (app llv (flat_map (fun l => l) lllv)));
      intros Hex1; rewrite Hex1 in *. discriminate.
    case_eq (ex_FOvar_x_ll (Var ym) (app llv (flat_map (fun l => l) lllv)));
      intros Hex2; rewrite Hex2 in *. discriminate.
    apply ex_FOvar_x_ll_app_r in Hex1.
    apply ex_FOvar_x_ll_app_r in Hex2.
    rewrite Hex1. rewrite Hex2. reflexivity.

    destruct f as [xn]. destruct P. simpl in *.
    case_eq (ex_FOvar_x_ll (Var xn)
         (llv ++ flat_map (fun l : list (list FOvariable) => l) lllv));
      intros HH; rewrite HH in *. discriminate.
    apply ex_FOvar_x_ll_app_r in HH. rewrite HH.
    apply IHalpha; try assumption.

    destruct f as [xn]. destruct P. simpl in *.
    case_eq (ex_FOvar_x_ll (Var xn)
         (llv ++ flat_map (fun l : list (list FOvariable) => l) lllv));
      intros HH; rewrite HH in *. discriminate.
    apply ex_FOvar_x_ll_app_r in HH. rewrite HH.
    apply IHalpha; try assumption.

    rewrite rep_pred_negSO. simpl FOvars_in in *.
    apply IHalpha; assumption.

    rewrite rep_pred_conjSO. simpl in *.
    apply ex_FOvar_l_ll_app_rev.
      apply ex_FOvar_l_ll_app_f_l in H1.
      apply IHalpha1; try assumption.

      apply ex_FOvar_l_ll_app_f_r in H1.
      apply IHalpha2; try assumption.

    rewrite rep_pred_disjSO. simpl in *.
    apply ex_FOvar_l_ll_app_rev.
      apply ex_FOvar_l_ll_app_f_l in H1.
      apply IHalpha1; try assumption.

      apply ex_FOvar_l_ll_app_f_r in H1.
      apply IHalpha2; try assumption.

    rewrite rep_pred_implSO. simpl in *.
    apply ex_FOvar_l_ll_app_rev.
      apply ex_FOvar_l_ll_app_f_l in H1.
      apply IHalpha1; try assumption.

      apply ex_FOvar_l_ll_app_f_r in H1.
      apply IHalpha2; try assumption.

    destruct p as [Qm]. destruct P as [Pn].
    simpl in *. case_eq (beq_nat Pn Qm); intros Hbeq.
      apply IHalpha; assumption.

      simpl. apply IHalpha; assumption.

    destruct p as [Qm]. destruct P as [Pn].
    simpl in *. case_eq (beq_nat Pn Qm); intros Hbeq.
      apply IHalpha; assumption.

      simpl. apply IHalpha; assumption.
Qed.

Lemma SOt_alt_SOQFree_t_gen : forall (alpha : SecOrder) x y (W : Set)
                      (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
                    (Ir : W -> W -> Prop)  (Q : predicate),
  SOQFree alpha = true ->
    (SOturnst W Iv (alt_Ip Ip pa_t Q) Ir alpha <->
      SOturnst W Iv Ip Ir (replace_pred alpha Q y
       (eqFO x x ))).
Proof.
  induction alpha; intros [z1] [z2] W Iv Ip Ir Q HallSO.
    unfold pa_f.
    simpl in *.
    destruct p as [Pn]; destruct f as [xn]; destruct Q as [Qm].
    case_eq (beq_nat Qm Pn); intros Hbeq.
      rewrite (beq_nat_true Qm Pn Hbeq).
      simpl.
      rewrite <- beq_nat_refl.
      unfold pa_t.
      case_eq (beq_nat z2 z1); intros Hbeq2;
      split; reflexivity.

      simpl.
      rewrite Hbeq in *.
      apply iff_refl.

    simpl in *.
    destruct f as [xn]; destruct f0 as [xm].
    destruct Q as [Qm].
    simpl.
    apply iff_refl.

    destruct f as [xn]; destruct f0 as [xm].
    destruct Q as [Qm].
    simpl.
    apply iff_refl.

    rewrite rep_pred_allFO.
    do 2 rewrite SOturnst_allFO.
    pose proof (SOQFree_allFO alpha f HallSO) as HallSO'.
    split; intros H d;
      (apply (IHalpha (Var z1) (Var z2)); [assumption | apply H]).

    rewrite rep_pred_exFO.
    do 2 rewrite SOturnst_exFO.
    pose proof (SOQFree_exFO alpha f HallSO) as HallSO'.
    split; intros H; destruct H as [d H]; exists d;
      (apply (IHalpha (Var z1) (Var z2)); [assumption | apply H]).

    rewrite rep_pred_negSO.
    do 2 rewrite SOturnst_negSO.
    split; intros H;
      unfold not; intros H2;
      apply H;
      apply (IHalpha (Var z1) (Var z2));
      assumption.

    rewrite rep_pred_conjSO.
    do 2 rewrite SOturnst_conjSO.
    pose proof (SOQFree_conjSO_l alpha1 alpha2 HallSO) as H1.
    pose proof (SOQFree_conjSO_r alpha1 alpha2 HallSO) as H2.
    simpl in HallSO.
    split; intros H; apply conj;
      try (apply (IHalpha1 (Var z1) (Var z2)); [assumption | apply H]);
      try (apply (IHalpha2 (Var z1) (Var z2)); [assumption | apply H]).

    rewrite rep_pred_disjSO.
    do 2 rewrite SOturnst_disjSO.
    pose proof (SOQFree_disjSO_l alpha1 alpha2 HallSO) as H1.
    pose proof (SOQFree_disjSO_r alpha1 alpha2 HallSO) as H2.
    split; intros H;
      (destruct H as [H | H];
      [left; apply (IHalpha1 (Var z1) (Var z2)) |
      right; apply (IHalpha2 (Var z1) (Var z2))]; assumption;
      apply H).

    rewrite rep_pred_implSO.
    do 2 rewrite SOturnst_implSO.
    pose proof (SOQFree_implSO_l alpha1 alpha2 HallSO) as H1.
    pose proof (SOQFree_implSO_r alpha1 alpha2 HallSO) as H2.
    split; intros H H3;
      apply (IHalpha2 (Var z1) (Var z2)); [assumption | apply H | assumption | apply H];
      apply (IHalpha1 (Var z1) (Var z2)); assumption.

    simpl in HallSO.
    destruct p; discriminate.

    simpl in HallSO.
    destruct p; discriminate.
Qed.

Lemma is_all_diff_FOv_lem9 : forall l x llx1 l0 lllv,
is_all_diff_FOv
         ((x :: nil) ++
          flat_map (fun l : list FOvariable => l)
            ((l :: llx1) ++ flat_map (fun l : list (list FOvariable) => l) (l0 :: lllv)))
 = true ->
is_all_diff_FOv
  ((x :: nil) ++
   flat_map (fun l1 : list FOvariable => l1)
     (flat_map (fun l1 : list (list FOvariable) => l1) (l0 :: lllv))) = true.
Proof.
  intros l x llx1 l0 lllv H.
  simpl in *.
  case_eq (is_in_FOvar x
        (l ++
         flat_map (fun l : list FOvariable => l)
           (llx1 ++ l0 ++ flat_map (fun l : list (list FOvariable) => l) lllv)));
      intros Hin; rewrite Hin in *. discriminate.
  apply is_in_FOvar_app_r in Hin. rewrite flat_map_app in Hin.
  apply is_in_FOvar_app_r in Hin. rewrite Hin.
  rewrite flat_map_app in H. rewrite app_assoc in H.
  apply is_all_diff_FOv_app_t in H. apply H.
Qed.


Lemma is_all_diff_FOv_lem10 : forall l x llx1 l0 lllv,
is_all_diff_FOv
         ((x :: nil) ++
          flat_map (fun l : list FOvariable => l)
            ((l :: llx1) ++ flat_map (fun l : list (list FOvariable) => l) (l0 :: lllv))) = true ->
is_all_diff_FOv
  (l ++
   flat_map (fun l1 : list FOvariable => l1)
     (flat_map (fun l1 : list (list FOvariable) => l1) (l0 :: lllv))) = true.
Proof.
  intros l x llx1 l0 lllv H.
  simpl in *. 
  case_eq (is_in_FOvar x
        (l ++
         flat_map (fun l : list FOvariable => l)
           (llx1 ++ l0 ++ flat_map (fun l : list (list FOvariable) => l) lllv)));
    intros Hin; rewrite Hin in *. discriminate.
  rewrite flat_map_app in H. rewrite is_all_diff_FOv_app_comm in H.
  rewrite app_assoc_reverse in H. apply is_all_diff_FOv_app_t in H.
  rewrite is_all_diff_FOv_app_comm in H. apply H.
Qed.

Lemma is_all_diff_FOv_lem11 : forall l llx1 x l0 lllv,
is_all_diff_FOv
         ((x :: nil) ++
          flat_map (fun l : list FOvariable => l)
            ((l :: llx1) ++ flat_map (fun l : list (list FOvariable) => l) (l0 :: lllv))) =
       true ->
is_all_diff_FOv
  ((x :: nil) ++
   flat_map (fun l1 : list FOvariable => l1)
     (llx1 ++ flat_map (fun l1 : list (list FOvariable) => l1) lllv)) = true.
Proof.
  intros l llx1 x l0 lllv H.
  simpl in *.
  case_eq (is_in_FOvar x
        (l ++
         flat_map (fun l : list FOvariable => l)
           (llx1 ++ l0 ++ flat_map (fun l : list (list FOvariable) => l) lllv)));
    intros Hin; rewrite Hin in *. discriminate.
  apply is_in_FOvar_app_r in Hin. rewrite flat_map_app in Hin.
  rewrite flat_map_app in Hin. rewrite is_in_FOvar_app_comm in Hin.
  rewrite app_assoc_reverse in Hin. apply is_in_FOvar_app_r in Hin.
  rewrite flat_map_app at 1. rewrite is_in_FOvar_app_comm. rewrite Hin.
  clear Hin. apply is_all_diff_FOv_app_t in H.
  rewrite flat_map_app in H. rewrite flat_map_app in H. 
  rewrite is_all_diff_FOv_app_comm in H.
  rewrite app_assoc_reverse in H.
  destruct H as [H1 H2]. apply is_all_diff_FOv_app_t in H2.
  rewrite flat_map_app. rewrite is_all_diff_FOv_app_comm. apply H2.
Qed.

Lemma is_all_diff_FOv__3 : forall l1 l2,
  is_all_diff_FOv (app l1 (flat_map (fun l => l) l2)) = true ->
  is_all_diff_FOv3 l1 l2 = true.
Proof.
  induction l1; intros l2 H. reflexivity.
  simpl in *. destruct l2. reflexivity.
  case_eq (is_in_FOvar a (l1 ++ flat_map (fun l : list FOvariable => l) (l :: l2)));
    intros H2; rewrite H2 in *. discriminate.
  apply is_in_FOvar_app_r in H2. simpl in H2.
  apply is_in_FOvar_app_l in H2. rewrite H2.
  simpl in H. rewrite is_all_diff_FOv_app_comm in H.
  rewrite app_assoc_reverse in H. 
  apply is_all_diff_FOv_app_t in H.
  destruct H as [H1 H3]. rewrite H1. apply IHl1.
  rewrite is_all_diff_FOv_app_comm. assumption.
Qed.

Lemma is_all_diff_FOv__3_lem1 : forall l llx1 x l0 lllv,
is_all_diff_FOv
         ((x :: nil) ++
          flat_map (fun l : list FOvariable => l)
            ((l :: llx1) ++ flat_map (fun l : list (list FOvariable) => l) (l0 :: lllv))) =
       true ->
is_all_diff_FOv3 l l0 = true.
Proof.
  intros l llx1 x l0 lllv H.
  simpl in *. case_eq (is_in_FOvar x
        (l ++
         flat_map (fun l : list FOvariable => l)
           (llx1 ++ l0 ++ flat_map (fun l : list (list FOvariable) => l) lllv)));
    intros Hin; rewrite Hin in *. discriminate.
  clear Hin. rewrite flat_map_app in H.
  rewrite is_all_diff_FOv_app_comm in H. rewrite app_assoc_reverse in H.
  apply is_all_diff_FOv_app_t in H.
  destruct H as [H1 H2]. clear H1.
  rewrite flat_map_app in H2.
  rewrite app_assoc_reverse in H2. rewrite is_all_diff_FOv_app_comm in H2.
  rewrite app_assoc_reverse in H2. apply is_all_diff_FOv_app_t in H2.
  destruct H2 as [H1 H2]. clear H1.
  apply is_all_diff_FOv__3. assumption.
Qed.

Lemma is_all_diff_FOv_lem12 : forall l llx1 x l0 lllv,
is_all_diff_FOv
         ((x :: nil) ++
          flat_map (fun l : list FOvariable => l)
            ((l :: llx1) ++ flat_map (fun l : list (list FOvariable) => l) (l0 :: lllv))) =
       true ->
is_all_diff_FOv
  (l ++
   flat_map (fun l1 : list FOvariable => l1)
     (flat_map (fun l1 : list (list FOvariable) => l1) (l0 :: lllv))) = true.
Proof.
  intros l llx1 x l0 lllv H.
  simpl in *.
  case_eq (is_in_FOvar x
        (l ++
         flat_map (fun l : list FOvariable => l)
           (llx1 ++ l0 ++ flat_map (fun l : list (list FOvariable) => l) lllv)));
      intros Hin; rewrite Hin in *. discriminate.
  rewrite flat_map_app in H.
  rewrite is_all_diff_FOv_app_comm in H.
  rewrite app_assoc_reverse in H.
  apply is_all_diff_FOv_app_t in H.
  rewrite is_all_diff_FOv_app_comm. apply H.
Qed.

Lemma SOQFree_l_fun4_l2_lP' : forall llx1 lx lllv,
SOQFree_l (fun4_l2_lP' llx1 lx lllv) = true.
Admitted.

Lemma is_all_diff_FOv_lem13 : forall l llx1 x l0 lllv,
is_all_diff_FOv
         ((x :: nil) ++
          flat_map (fun l : list FOvariable => l)
            ((l :: llx1) ++ flat_map (fun l : list (list FOvariable) => l) (l0 :: lllv))) =
       true ->
is_all_diff_FOv ((x :: nil) ++ flat_map (fun l1 : list FOvariable => l1) (l0 ++ llx1)) = true.
Proof.
  intros l llx1 x l0 lllv H.
  simpl in *.
  case_eq (is_in_FOvar x
        (l ++
         flat_map (fun l : list FOvariable => l)
           (llx1 ++ l0 ++ flat_map (fun l : list (list FOvariable) => l) lllv)));
    intros Hin; rewrite Hin in *. discriminate.
  apply is_in_FOvar_app_r in Hin.
  rewrite app_assoc in Hin. rewrite flat_map_app in Hin.
  apply is_in_FOvar_app_l in Hin.
  rewrite flat_map_app in Hin.  rewrite flat_map_app.
  rewrite is_in_FOvar_app_comm. rewrite Hin.
  apply is_all_diff_FOv_app_t in H. destruct H as [H1 H2].
  rewrite app_assoc in  H2. rewrite flat_map_app in H2.
  apply is_all_diff_FOv_app_t in H2. rewrite flat_map_app in H2. 
  rewrite is_all_diff_FOv_app_comm. apply H2.
Qed.

Lemma SOQFree_fun4' : forall l x1 xn,
  SOQFree (fun4' x1 xn l) = true.
Proof.
  induction l; intros [x1] [xn]. reflexivity.
  simpl. destruct a; apply IHl.
Qed.

Lemma SOQFree_fun4_l2' : forall l x l0,
  SOQFree (fun4_l2' l x l0) = true.
Proof.
  induction l; intros x l0. reflexivity.
  destruct l0. simpl. destruct l; reflexivity.
  destruct l. simpl. apply SOQFree_fun4'.
  simpl. destruct l1. apply SOQFree_fun4'.
  simpl. rewrite SOQFree_fun4'.
  apply (IHl _ (cons l1 l2)).
Qed.

Lemma is_un_predless_l_fun4_l2_lP' : forall llx1 lx lllv,
is_unary_predless_l (fun4_l2_lP' llx1 lx lllv) = true.
Proof.
  induction llx1; intros lx lllv. reflexivity.
  destruct lx. reflexivity.
  destruct lllv. reflexivity.
  simpl. rewrite IHllx1. 
  rewrite is_un_predless_fun4_l2'. reflexivity.
Qed.

Definition consistent_lP_lllv_P {llx : list (list FOvariable)} lP (lllv : list (list (list FOvariable))) P : Prop :=
  is_constant (@ind_gen _ llx (indicies_l2 lP P) lllv).

Definition consistent_lP_lllv {llx} (lP : list predicate) lllv : Prop :=
  forall P, @consistent_lP_lllv_P llx lP lllv P.

Fixpoint contains_empty_llx (llx : list (list FOvariable)) :=
  match llx with
  | nil => false
  | cons nil _ => true
  | cons _ llx' => contains_empty_llx llx'
  end.

Fixpoint contains_empty_lllx (lllx : list (list (list FOvariable))) :=
  match lllx with
  | nil => false
  | cons nil _ => true
  | cons _ lllx' => contains_empty_lllx lllx'
  end.

Lemma ind_gen_nil_gen : forall l (A : Type) (pa0 : A),
  @ind_gen A pa0 l nil = constant_l pa0 (length l).
Proof.
  induction l; intros W pa. reflexivity.
  simpl. rewrite IHl. simpl. destruct a. simpl.
  reflexivity. simpl. destruct a; reflexivity.
Qed.

Lemma ind_cond_nil_gen : forall l ,
  ind_cond l nil = constant_l (eqFO (Var 1) (Var 1)) (length l).
Proof.
  induction l. reflexivity.
  simpl. rewrite IHl. simpl. destruct a. simpl.
  reflexivity. simpl. destruct a; reflexivity.
Qed.

Lemma ind_llv_nil_gen : forall l ,
  ind_llv l nil = constant_l nil (length l).
Proof.
  induction l. reflexivity.
  simpl. rewrite IHl. simpl. destruct a. simpl.
  reflexivity. simpl. destruct a; reflexivity.
Qed.

Lemma ind_FOv_nil_gen : forall l ,
  ind_FOv l nil = constant_l (Var 1) (length l).
Proof.
  induction l. reflexivity.
  simpl. rewrite IHl. simpl. destruct a. simpl.
  reflexivity. simpl. destruct a; reflexivity.
Qed.

Lemma constant_l_length_eq : forall n m A a b,
  @constant_l A a n = constant_l b m ->
  n = m.
Proof.
  induction n; intros m A a b H.
    destruct m. reflexivity. discriminate.

    simpl in *. destruct m. discriminate.
    inversion H as [[H1 H2]].
    rewrite (IHn _ _ _ _ H2).
    reflexivity.
Qed.

Lemma cons_lP_lpa_P_sSahlq_pa_l5'_cons_True_pre :forall lP  a1 a2 n1 n2 Q llx1 lllv (W : Set) (Iv : FOvariable -> W) Ir,
(*   ex_FOvar_l_ll nil llx1 = false -> *)
(*  contains_empty_llx llx1 = false -> 
 contains_empty_lllx lllv = false ->  *)
length llx1 = length lllv ->
~ llx1 = nil ->
~ lllv = nil ->
       ind_llv (indicies_l2 (lP) Q) (llx1) = constant_l a1 n1 ->
       @ind_gen _ nil (indicies_l2 (lP) Q) (lllv) = constant_l a2 n2 ->
exists (n : nat),
  @ind_gen _ pa_t (indicies_l2 ( lP) Q)
    ( sSahlq_pa_l5' Ir lllv (map2 (Iv_ify Iv) llx1)) = 
  constant_l (sSahlq_pa5' Ir a2 (map (Iv_ify Iv) a1)) n.
Proof.
  induction lP; intros a1 a2 n1 n2 Q llx1 lllv W Iv Ir Hll Hnil1 Hnil2 H1 H2.
    simpl in *. exists 0. reflexivity.

    destruct a as [Pn]. destruct Q as [Qm].
    unfold indicies_l2 in *.
    destruct llx1. contradiction (Hnil1 eq_refl).
    destruct lllv. contradiction (Hnil2 eq_refl).
    simpl in *.
    simpl in *. case_eq (beq_nat Qm Pn); intros Hbeq;
      rewrite Hbeq in *. simpl in *.
(* 
      destruct llx1. simpl. *)
(*  simpl in *. discriminate.
 *)
(* 
 destruct lllv. simpl in *.
admit.
admit.
    destruct lllv.
admit.
 *)
    simpl. destruct n1. discriminate. simpl in H1. inversion H1 as [[H1a H1b]].
    destruct n2. discriminate. simpl in H2. inversion H2 as [[H2a H2b]].
    rewrite ind_llv_ind_l2_pre_cons in H1b.
    rewrite ind_gen_pre_cons in H2b.
    destruct llx1. simpl in *. destruct lllv. simpl in *.
    exists (S n2). simpl. rewrite ind_gen_pre_cons. 
    rewrite ind_llv_ind_l2_pre_cons in H1.
    rewrite ind_gen_nil_gen.
    rewrite ind_gen_nil_gen in H2b. 
    destruct n2. simpl in H2b. 
    case_eq ((length (indicies_l2_pre lP (Pred Qm) 0))).
      intros Hl. rewrite Hl in *. simpl in *. reflexivity.
      intros n Hl. rewrite Hl in H2b. discriminate.
    case_eq ((length (indicies_l2_pre lP (Pred Qm) 0))).
      intros Hl. rewrite Hl in *. discriminate.
    intros n Hl. rewrite Hl in H2b.
    simpl in H2b. inversion H2b as [[H3a H3b]].
    simpl. rewrite (constant_l_length_eq _ _ _ _ _ H3b).
    unfold pa_t. reflexivity.

    discriminate. destruct lllv. discriminate.
    remember (cons l1 llx1) as t1.
    remember (cons l2 lllv) as t2.
    inversion Hll as [Hll'].
    assert (~ t1 = nil) as Hass1.
      rewrite Heqt1. discriminate.
    assert (~ t2 = nil) as Hass2.
      rewrite Heqt2. discriminate.
    simpl. destruct (IHlP _ _ _ _ _ _ _ W Iv Ir Hll' Hass1 Hass2 H1b H2b) as [n H].
    exists (S n). rewrite Heqt1 in *. rewrite Heqt2 in *.
    simpl in *. rewrite ind_gen_pre_cons. rewrite H. reflexivity.

    destruct llx1. simpl in *. destruct lllv. simpl in *.
    rewrite ind_llv_ind_l2_pre_cons in H1.
 rewrite ind_gen_pre_cons in H2.
    rewrite ind_gen_nil_gen in H2. 
    destruct n2. simpl in H2.
    case_eq ((length (indicies_l2_pre lP (Pred Qm) 0))).
      intros Hl. rewrite Hl in *.
      exists 0. simpl. rewrite ind_gen_pre_cons. 
      rewrite ind_gen_nil_gen. rewrite Hl. reflexivity.

      intros n Hl. rewrite Hl in H2. discriminate.
    case_eq ((length (indicies_l2_pre lP (Pred Qm) 0))).
      intros Hl. rewrite Hl in *. discriminate.
    intros n Hl. rewrite Hl in H2.
    simpl in H2. inversion H2 as [[H3a H3b]].
    simpl.

    exists (S n2). simpl. rewrite ind_gen_pre_cons. 
    rewrite ind_gen_nil_gen.
    rewrite <- (constant_l_length_eq _ _ _ _ _ H3b).
    rewrite Hl.
    unfold pa_t. reflexivity.

    discriminate. destruct lllv. discriminate.
    remember (cons l1 llx1) as t1.
    remember (cons l2 lllv) as t2.
    inversion Hll as [Hll'].
    assert (~ t1 = nil) as Hass1.
      rewrite Heqt1. discriminate.
    assert (~ t2 = nil) as Hass2.
      rewrite Heqt2. discriminate.
    rewrite ind_llv_pre_cons in H1.
    rewrite ind_gen_pre_cons in H2.
    simpl. destruct (IHlP _ _ _ _ _ _ _ W Iv Ir Hll' Hass1 Hass2 H1 H2) as [n H].
    exists (n). rewrite Heqt1 in *. rewrite Heqt2 in *.
    simpl in *. rewrite ind_gen_pre_cons. rewrite H. reflexivity.
Qed.

Lemma cons_lP_lpa_P_sSahlq_pa_l5'_cons_True_pre' :forall lP  a1 a2 n1 n2 Q llx1 lllv (W : Set) (Iv : FOvariable -> W) Ir,
(*   ex_FOvar_l_ll nil llx1 = false -> *)
(*  contains_empty_llx llx1 = false -> 
 contains_empty_lllx lllv = false ->  *)
length llx1 = length lllv ->
       ind_llv (indicies_l2 (lP) Q) (llx1) = constant_l a1 n1 ->
       @ind_gen _ nil (indicies_l2 (lP) Q) (lllv) = constant_l a2 n2 ->
exists (n : nat),
  @ind_gen _ pa_t (indicies_l2 ( lP) Q)
    ( sSahlq_pa_l5' Ir lllv (map2 (Iv_ify Iv) llx1)) = 
  constant_l (sSahlq_pa5' Ir a2 (map (Iv_ify Iv) a1)) n.
Proof.
  induction lP; intros a1 a2 n1 n2 Q llx1 lllv W Iv Ir Hll (* Hnil1 Hnil2 *) H1 H2.
    simpl in *. exists 0. reflexivity.

    destruct a as [Pn]. destruct Q as [Qm].
    unfold indicies_l2 in *.
    destruct llx1. simpl. destruct lllv.
      case_eq (beq_nat Qm Pn); intros Hbeq.
        simpl in *. rewrite Hbeq in *. simpl in *.
        destruct n1. discriminate. destruct n2. discriminate.
        simpl in *. inversion H1 as [[H1a H1b]].
        inversion H2 as [[H2a H2b]]. simpl.
        rewrite ind_gen_nil_gen in *.
        apply constant_l_length_eq in H2b. rewrite H2b.
        exists (S n2). reflexivity.

        simpl in *. rewrite Hbeq in *. simpl in *.
        rewrite ind_gen_nil_gen in H2. apply constant_l_length_eq in H2.
        rewrite ind_gen_nil_gen. rewrite H2.
        rewrite ind_llv_nil_gen in H1. rewrite H2 in H1. 
        destruct n1. destruct n2. simpl. exists 0. reflexivity. discriminate.
        destruct n2. simpl in *. discriminate.
        simpl in *. inversion H1. simpl. destruct a2. simpl.
        exists (S n2). reflexivity. simpl. destruct a2.
        exists (S n2). reflexivity. exists (S n2).  reflexivity.

        discriminate.
    destruct lllv. discriminate.
    simpl in *. case_eq (beq_nat Qm Pn); intros Hbeq;
      rewrite Hbeq in *. simpl in *.

    simpl. destruct n1. discriminate. simpl in H1. inversion H1 as [[H1a H1b]].
    destruct n2. discriminate. simpl in H2. inversion H2 as [[H2a H2b]].
    rewrite ind_llv_ind_l2_pre_cons in H1b.
    rewrite ind_gen_pre_cons in H2b.
    destruct llx1. simpl in *. destruct lllv. simpl in *.
    exists (S n2). simpl. rewrite ind_gen_pre_cons. 
    rewrite ind_llv_ind_l2_pre_cons in H1.
    rewrite ind_gen_nil_gen.
    rewrite ind_gen_nil_gen in H2b. 
    destruct n2. simpl in H2b. 
    case_eq ((length (indicies_l2_pre lP (Pred Qm) 0))).
      intros Hl. rewrite Hl in *. simpl in *. reflexivity.
      intros n Hl. rewrite Hl in H2b. discriminate.
    case_eq ((length (indicies_l2_pre lP (Pred Qm) 0))).
      intros Hl. rewrite Hl in *. discriminate.
    intros n Hl. rewrite Hl in H2b.
    simpl in H2b. inversion H2b as [[H3a H3b]].
    simpl. rewrite (constant_l_length_eq _ _ _ _ _ H3b).
    unfold pa_t. reflexivity.

    discriminate. destruct lllv. discriminate.
    remember (cons l1 llx1) as t1.
    remember (cons l2 lllv) as t2.
    inversion Hll as [Hll'].
    assert (~ t1 = nil) as Hass1.
      rewrite Heqt1. discriminate.
    assert (~ t2 = nil) as Hass2.
      rewrite Heqt2. discriminate.
    simpl. destruct (IHlP _ _ _ _ _ _ _ W Iv Ir Hll' H1b H2b) as [n H].
    exists (S n). rewrite Heqt1 in *. rewrite Heqt2 in *.
    simpl in *. rewrite ind_gen_pre_cons. rewrite H. reflexivity.

    destruct llx1. simpl in *. destruct lllv. simpl in *.
    rewrite ind_llv_ind_l2_pre_cons in H1.
 rewrite ind_gen_pre_cons in H2.
    rewrite ind_gen_nil_gen in H2. 
    destruct n2. simpl in H2.
    case_eq ((length (indicies_l2_pre lP (Pred Qm) 0))).
      intros Hl. rewrite Hl in *.
      exists 0. simpl. rewrite ind_gen_pre_cons. 
      rewrite ind_gen_nil_gen. rewrite Hl. reflexivity.

      intros n Hl. rewrite Hl in H2. discriminate.
    case_eq ((length (indicies_l2_pre lP (Pred Qm) 0))).
      intros Hl. rewrite Hl in *. discriminate.
    intros n Hl. rewrite Hl in H2.
    simpl in H2. inversion H2 as [[H3a H3b]].
    simpl.

    exists (S n2). simpl. rewrite ind_gen_pre_cons. 
    rewrite ind_gen_nil_gen.
    rewrite <- (constant_l_length_eq _ _ _ _ _ H3b).
    rewrite Hl.
    unfold pa_t. reflexivity.

    discriminate. destruct lllv. discriminate.
    remember (cons l1 llx1) as t1.
    remember (cons l2 lllv) as t2.
    inversion Hll as [Hll'].
    assert (~ t1 = nil) as Hass1.
      rewrite Heqt1. discriminate.
    assert (~ t2 = nil) as Hass2.
      rewrite Heqt2. discriminate.
    rewrite ind_llv_pre_cons in H1.
    rewrite ind_gen_pre_cons in H2.
    simpl. destruct (IHlP _ _ _ _ _ _ _ W Iv Ir Hll' H1 H2) as [n H].
    exists (n). rewrite Heqt1 in *. rewrite Heqt2 in *.
    simpl in *. rewrite ind_gen_pre_cons. rewrite H. reflexivity.
Qed.

Lemma cons_lP_lpa_P_sSahlq_pa_l5'_cons_True_pre'' :forall lP  a1 a2 n1 n2 Q llx1 lllv (W : Set) (Iv : FOvariable -> W) Ir,
       ind_llv (indicies_l2 (lP) Q) (llx1) = constant_l a1 n1 ->
       @ind_gen _ nil (indicies_l2 (lP) Q) (lllv) = constant_l a2 n2 ->
exists (n : nat),
  @ind_gen _ pa_t (indicies_l2 ( lP) Q)
    ( sSahlq_pa_l5' Ir lllv (map2 (Iv_ify Iv) llx1)) = 
  constant_l (sSahlq_pa5' Ir a2 (map (Iv_ify Iv) a1)) n.
Proof.
  induction lP; intros a1 a2 n1 n2 Q llx1 lllv W Iv Ir  (* Hnil1 Hnil2 *) H1 H2.
    simpl in *. exists 0. reflexivity.

    destruct a as [Pn]. destruct Q as [Qm].
    unfold indicies_l2 in *.
    destruct llx1. simpl. destruct lllv.
      case_eq (beq_nat Qm Pn); intros Hbeq.
        simpl in *. rewrite Hbeq in *. simpl in *.
        destruct n1. discriminate. destruct n2. discriminate.
        simpl in *. inversion H1 as [[H1a H1b]].
        inversion H2 as [[H2a H2b]]. simpl.
        rewrite ind_gen_nil_gen in *.
        apply constant_l_length_eq in H2b. rewrite H2b.
        exists (S n2). reflexivity.

        simpl in *. rewrite Hbeq in *. simpl in *.
        rewrite ind_gen_nil_gen in H2. apply constant_l_length_eq in H2.
        rewrite ind_gen_nil_gen. rewrite H2.
        rewrite ind_llv_nil_gen in H1. rewrite H2 in H1. 
        destruct n1. destruct n2. simpl. exists 0. reflexivity. discriminate.
        destruct n2. simpl in *. discriminate.
        simpl in *. inversion H1. simpl. destruct a2. simpl.
        exists (S n2). reflexivity. simpl. destruct a2.
        exists (S n2). reflexivity. exists (S n2).  reflexivity.

simpl in *. case_eq (beq_nat Qm Pn); intros Hbeq; rewrite Hbeq in *.
  simpl in *. destruct n1. discriminate.
  simpl in H1. inversion H1 as [[H1a H1b]].
  simpl. rewrite ind_gen_nil_gen. rewrite ind_llv_nil_gen in H1b.
  apply constant_l_length_eq in H1b. rewrite H1b. simpl.
  destruct a2. simpl.  exists (S n1). reflexivity.
  simpl. destruct a2; exists (S n1); reflexivity.

  rewrite ind_llv_nil_gen in H1.
  case_eq (length (indicies_l2_pre lP (Pred Qm) 1)).
    intros H. rewrite H in *. destruct n1.
    rewrite ind_gen_nil_gen. rewrite H. exists 0. reflexivity.
    discriminate.

    intros n Hl. rewrite Hl in *. simpl in H1. destruct n1. discriminate.
    simpl in *. inversion H1. simpl. rewrite ind_gen_nil_gen.
    rewrite Hl. destruct a2. simpl. exists (S n). reflexivity.
    simpl. destruct a2; simpl; exists (S n); reflexivity.

    destruct lllv.
      simpl in *.
      case_eq (beq_nat Qm Pn); intros Hbeq.
        simpl in *. rewrite Hbeq in *. simpl in *.
        destruct n1. discriminate. destruct n2. discriminate.
        simpl in *. inversion H1 as [[H1a H1b]].
        inversion H2 as [[H2a H2b]]. simpl.
        rewrite ind_gen_nil_gen in *.
        apply constant_l_length_eq in H2b. rewrite H2b.
        exists (S n2). reflexivity.

        simpl in *. rewrite Hbeq in *. simpl in *.
        rewrite ind_gen_nil_gen in H2. 
        case_eq ((length (indicies_l2_pre lP (Pred Qm) 1))).
          intros H. rewrite H in *. rewrite ind_gen_nil_gen.
          rewrite H. exists 0. reflexivity.

          intros n H. rewrite H in *. destruct n2. discriminate.
          simpl in *. inversion H2 as [[H2a H2b]].
          simpl. rewrite ind_gen_nil_gen. rewrite H.
          exists (S n). reflexivity.

    simpl in *.
    case_eq (beq_nat Qm Pn); intros Hbeq; rewrite Hbeq in *.
    simpl in *.
    rewrite ind_llv_pre_cons in H1.
    rewrite ind_gen_pre_cons in H2.
    destruct n1. discriminate.
    destruct n2. discriminate.
    simpl in *. inversion H1 as [[H1a H1b]].
    inversion H2 as [[H2a H2b]].
    simpl. destruct (IHlP _ _ _ _ _ _ _ W Iv Ir H1b H2b) as [n H].
    exists (S n). rewrite ind_gen_pre_cons. rewrite H. reflexivity.

    simpl in *.
    rewrite ind_llv_pre_cons in H1.
    rewrite ind_gen_pre_cons in H2.
    simpl. destruct (IHlP _ _ _ _ _ _ _ W Iv Ir H1 H2) as [n H].
    exists (n). rewrite ind_gen_pre_cons. rewrite H. reflexivity.
Qed.

Lemma cons_lP_lpa_P_sSahlq_pa_l5'_cons_True : forall lP P Q llx1 lllv (W : Set) (Iv : FOvariable -> W) Ir,
consistent_lP_llv_P (P :: lP) (nil :: llx1) Q ->
@consistent_lP_lllv_P nil (P :: lP) (nil :: lllv) Q ->
@consistent_lP_lpa_P _ pa_t (P :: lP)
  ((fun _ : W => True) :: sSahlq_pa_l5' Ir lllv (map2 (Iv_ify Iv) llx1)) Q.
Proof.
  intros lP P Q llx1 lllv W Iv Ir H1 H2.
  unfold consistent_lP_lpa_P.
  unfold consistent_lP_llv_P in H1.
  unfold consistent_lP_lllv_P in H2.
  unfold is_constant in *.
  destruct H1 as [a1 [n1 H1]].
  destruct H2 as [a2 [n2 H2]].
  pose proof (cons_lP_lpa_P_sSahlq_pa_l5'_cons_True_pre'' (cons P lP) a1 a2 n1 n2 Q (cons nil llx1) (cons nil lllv) W Iv Ir)
    as H.
  simpl in H. exists ((sSahlq_pa5' Ir a2 (map (Iv_ify Iv) a1))).
  apply H; assumption.
Qed.

Lemma cons_lP_lpa_sSahlq_pa_l5'_cons_True : forall lP a llx1 lllv (W : Set)  (Iv : FOvariable -> W) Ir,
  consistent_lP_llv (a :: lP) (nil :: llx1) ->
  @consistent_lP_lllv nil (a :: lP) (nil :: lllv) ->
@consistent_lP_lpa _ pa_t (a :: lP)
  ((fun _ : W => True) :: sSahlq_pa_l5' Ir lllv (map2 (Iv_ify Iv) llx1)).
Proof.
  intros lP P llx1 lllv W Iv Ir H1 H2 Q.
  unfold consistent_lP_llv in H1.
  unfold consistent_lP_lllv in H2.
  apply cons_lP_lpa_P_sSahlq_pa_l5'_cons_True.
    apply H1. apply H2.
Qed.

Lemma consistent_lP_P_pre_fun4_l2_lP' : forall lP llx1 lv lllv P a1 a2 a3 n1 n2 n3,
       ind_llv (indicies_l2 lP P) llx1 = constant_l a1 n1 ->
       ind_FOv (indicies_l2 lP P) lv = constant_l a2 n2 ->
       @ind_gen _ nil (indicies_l2 lP P) lllv = constant_l a3 n3 ->
length lP = length lv ->
exists (n : nat),
  ind_cond (indicies_l2 lP P) (fun4_l2_lP' llx1 lv lllv) = constant_l (fun4_l2' a1 a2 a3) n.
Proof.
  induction lP; intros llx1 lv llv P a1 a2 a3 n1 n2 n3 H1 H2 H3 Hl.
    simpl in *. exists 0. reflexivity.

    unfold indicies_l2 in *. simpl in *. destruct P as [Pn]. destruct a as [Qm].
    case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *.
      simpl in *. destruct llx1. simpl in *. rewrite ind_cond_nil_gen.
      destruct n1. discriminate. simpl in H1. inversion H1 as [[H1a H1b]].
      simpl. exists (S (length (indicies_l2_pre lP (Pred Pn) 1))). reflexivity.

destruct llv. simpl in *.
      destruct n3. discriminate. simpl in H3. inversion H3 as [[H3a H3b]].
      simpl. exists (S (length (indicies_l2_pre lP (Pred Pn) 1))).

      destruct lv. simpl in *. rewrite ind_cond_nil_gen.
      destruct n2. discriminate. simpl in H2. inversion H2 as [[H2a H2b]].
      simpl. rewrite ind_gen_nil_gen in H3b.

destruct a1; simpl. reflexivity. destruct a1; reflexivity.

      rewrite ind_cond_nil_gen.
      destruct a1; simpl. reflexivity. destruct a1; reflexivity.

      destruct lv. discriminate.


 simpl in *. rewrite ind_cond_ind_l2_pre_cons.
destruct n1. discriminate. destruct n2. discriminate. destruct n3. discriminate.
inversion H1 as [[H1a H1b]]. inversion H2 as [[H2a H2b]]. inversion H3 as [[H3a H3b]].
rewrite ind_llv_pre_cons in H1b. rewrite ind_FOv_ind_l2_pre_cons in H2b.
rewrite ind_gen_pre_cons in H3b. inversion Hl as [Hl'].
destruct (IHlP _ _ _ _ _ _ _ _ _ _ H1b H2b H3b Hl') as [n H].
exists (S n). rewrite H. reflexivity.

destruct lv. simpl in *. discriminate.
rewrite ind_FOv_ind_l2_pre_cons in H2.
destruct llx1. rewrite ind_llv_nil_gen in H1.
remember (length (indicies_l2_pre lP (Pred Pn) 1))  as t.
simpl. rewrite ind_cond_nil_gen. rewrite <- Heqt.  destruct n1.
  destruct t. exists 0. reflexivity.
  discriminate. destruct t. discriminate.
  simpl in H1. inversion H1. simpl. exists (S t). reflexivity.

destruct llv. rewrite ind_gen_nil_gen in H3.
remember (length (indicies_l2_pre lP (Pred Pn) 1))  as t.
simpl. rewrite ind_cond_nil_gen. rewrite <- Heqt.  destruct n3.
  destruct t. exists 0. reflexivity.
  discriminate. destruct t. discriminate.
  simpl in H3. inversion H3. simpl. exists (S t).
  destruct a1. reflexivity. simpl. destruct a1; reflexivity.

  simpl. rewrite ind_cond_ind_l2_pre_cons.
  inversion Hl as [Hl'].
  rewrite ind_llv_pre_cons in H1.
  rewrite ind_gen_pre_cons in H3.
  apply (IHlP _ _ _ _ _ _  _ _ _ _ H1 H2 H3 Hl' ).
Qed.

Lemma consistent_lP_P_fun4_l2_lP' : forall lP llx1 lv lllv P,
consistent_lP_llv_P lP llx1 P ->
consistent_lP_lx_P lP lv P ->
@consistent_lP_lllv_P nil lP lllv P ->
length lP = length lv ->
consistent_lP_lcond_P lP (fun4_l2_lP' llx1 lv lllv) P.
Proof.
  intros until 0. intros H1 H2 H3 H.
  unfold consistent_lP_lx_P in *.
  unfold consistent_lP_llv_P in *.
  unfold consistent_lP_lllv_P in *.
  unfold consistent_lP_lcond_P.
  unfold is_constant in *.
  destruct H1 as [a1 [n1 H1]]. destruct H2 as [a2 [n2 H2]]. destruct H3 as [a3 [n3 H3]].
  exists (fun4_l2' a1 a2 a3).
  apply (consistent_lP_P_pre_fun4_l2_lP' _ _ _ _ _ _ _ _ _ _ _ H1 H2 H3 H).
Qed.

Lemma consistent_lP_fun4_l2_lP' : forall lP llx1 lv lllv,
  consistent_lP_llv lP llx1 ->
  consistent_lP_lx lP lv ->
  @consistent_lP_lllv nil lP lllv ->
length lP = length lv ->
  consistent_lP_lcond lP (fun4_l2_lP' llx1 lv lllv).
Proof.
  intros until 0. intros H1 H2 H3 H4.
  unfold consistent_lP_lx in *.
  unfold consistent_lP_llv in *.
  unfold consistent_lP_lllv in *.
  unfold consistent_lP_lcond in *.
  intros P. apply consistent_lP_P_fun4_l2_lP'.
  apply H1. apply H2. apply H3. assumption.
Qed.

Lemma consistent_lP_lllv_nil : forall lP l,
  @consistent_lP_lllv l lP nil .
Proof.
  intros lP l [Pn].
  unfold consistent_lP_lllv_P.
  rewrite ind_gen_nil_gen.
  apply is__constant_l.
Qed.

Lemma consistent_lP_lllv_cons : forall  lllv lP P lv l,
  @consistent_lP_lllv l (cons P lP) (cons lv lllv) ->
  @consistent_lP_lllv l lP lllv.
Proof.
  induction lllv; intros lP [Pn] llv l' H.
    apply consistent_lP_lllv_nil.

    unfold consistent_lP_llv in *.
    intros P. specialize (H P).
    unfold consistent_lP_lllv_P in *.
    unfold indicies_l2 in *.
    simpl in *. destruct P as [Qm].
    case_eq (beq_nat Qm Pn); intros Hbeq;
      rewrite Hbeq in *.
      simpl in *. unfold is_constant in *.
      destruct H as [l [n H]].
      rewrite ind_gen_pre_cons in H.
      destruct n. simpl in *. discriminate.
      exists l. exists n. simpl in *.
      inversion H. reflexivity.

      rewrite ind_gen_pre_cons in H.
      assumption.
Qed.

Lemma length_calc_lx1__llv_P : forall alpha P,
  length (calc_lx1_P alpha P) = length (calc_llv_P alpha P).
Proof.
  induction alpha; intros [Pn]; try reflexivity.

    simpl. destruct alpha; try reflexivity.
    case_eq (P_branch_allFO alpha2 (Pred Pn)); intros H;
      destruct alpha1; destruct alpha2; try reflexivity.

    simpl. do 2 rewrite app_length. rewrite IHalpha1.
    rewrite IHalpha2. reflexivity.
Qed.

Lemma length_sSahlq_pa_l5' : forall lP alpha (W : Set) Iv (Ir : W -> W -> Prop),
 length lP = length (sSahlq_pa_l5' Ir (calc_llv_lP alpha lP) (map2 (Iv_ify Iv) (calc_lx1_lP alpha lP))).
Admitted.

Lemma length_calc_lP  : forall lP atm,
length (calc_lP atm lP) = length lP.
Proof.
  induction lP; intros atm. reflexivity.
  simpl. rewrite IHlP. reflexivity.
Qed.

Lemma ex_bound_FO_ll_rep_pred : forall llx1 alpha cond P y,
  is_in_FOvar_l (flat_map (fun l0 => l0) llx1) (FOvars_in cond) = false ->
  ex_bound_FO_ll alpha llx1 = false ->
  ex_bound_FO_ll (replace_pred alpha P y cond) llx1 = false.
Admitted.

Lemma is_in_FOvar_l_fun4_l2'  : forall l1 l2 l y,
  is_in_FOvar_l l (FOvars_in (fun4_l2' l1 y l2)) =
  is_in_FOvar_l l (cons y (app l1 (flat_map (fun l0 => l0) l2))).
Proof.
  
Admitted.

Lemma is_in_FOvar__l : forall l l2 y,
  is_in_FOvar y l = false ->
  is_in_FOvar_l l l2 = false ->
  is_in_FOvar_l l (cons y l2) = false.
Proof.
  induction l; intros l2 y H1 H2.
    simpl in *.
Admitted.

Lemma  ex_bound_FO_ll_all_diff_FOv3: forall llx1 lllv l1 l2 alpha P y,
is_all_diff_FOv3 (app l1 (flat_map (fun l0 => l0) llx1))
    (app l2 (flat_map (fun l0 => l0) lllv)) = true ->
ex_FOvar_x_ll y (flat_map (fun l : list (list FOvariable) => l) (l2 :: lllv)) =
       false ->
ex_FOvar_x_ll y (l1 :: llx1) = false ->
ex_bound_FO_ll alpha llx1 = false ->
ex_bound_FO_l alpha l1 = false ->
ex_bound_FO_ll (replace_pred alpha P y (fun4_l2' l1 y l2)) llx1 = false.
Proof.
  intros until 0. intros Hll Hex1 Hex2 Hb1 Hb2.
  destruct llx1. reflexivity.
  apply ex_bound_FO_ll_rep_pred; try assumption.
  rewrite is_in_FOvar_l_fun4_l2'. 
  simpl in *.
  case_eq (is_in_FOvar y l); intros Hin2; rewrite Hin2 in *.
    rewrite if_then_else_same in Hex2. discriminate.
  case_eq (ex_FOvar_x_ll y llx1); intros Hex3; rewrite Hex3 in *.
    rewrite if_then_else_same in Hex2. discriminate.
  apply if_then_else_tf in Hex2.
  apply is_in_FOvar__l.
  rewrite is_in_FOvar_app.
  rewrite Hin2. rewrite is_in_FOvar_ex_Fovar_x_ll.
  assumption.
Admitted.

Lemma length__id_1_gen : forall {A B : Type} (l :(list A)) (l0 : (list B)),
  length_id_1_gen l l0 = true <-> length l = length l0.
Proof.  
  intros A B. induction l; intros l0.
    simpl. destruct l0. split; reflexivity.
    split; discriminate.

    simpl in *. destruct l0. split; discriminate.
    split; intros H.
      apply IHl in H. rewrite H. reflexivity.

      apply IHl. simpl in H. inversion H.
      reflexivity.
Qed.

Lemma is_all_diff_FOv3_ex_FOvar_l_ll_app : forall l1 l2 l3 l4,
  length l1 = length l3 ->
  length l2 = length l4 ->
  is_all_diff_FOv3 (app l1 l2) (app l3 l4) = true ->
  ex_FOvar_l_ll l1 l4 = false.
Proof.
  induction l1; intros l2 l3 l4 Hl Hl2 H. reflexivity.
  simpl in *. destruct l3. discriminate.
  simpl in *. case_eq (is_in_FOvar a l);
      intros Hin; rewrite Hin in *. discriminate.
  
  simpl in *.
Admitted.

Lemma is_all_diff_FOv3_app_l : forall l1 l2 l3 l4,
(*   length l1 = l3 -> *)
  is_all_diff_FOv3 (app l1 l2) (app l3 l4) = true ->
  is_all_diff_FOv3 l1 l3 = true.
Proof.
  induction l1; intros l2 l3 l4 H. reflexivity.
  simpl in *. destruct l3. reflexivity.
  simpl in *. case_eq (is_in_FOvar a l);  
    intros H2; rewrite H2 in *. discriminate.
  case_eq (is_all_diff_FOv l); intros H3; 
    rewrite H3 in *. 2 : discriminate.
  apply IHl1 in H. assumption.
Qed.

Lemma is_all_diff_FOv3_app_r : forall l1 l2 l3 l4,
  length l1 = length l3 ->
  is_all_diff_FOv3 (app l1 l2) (app l3 l4) = true ->
  is_all_diff_FOv3 l2 l4 = true.
Proof.
  induction l1; intros l2 l3 l4 Hl H. destruct l3. assumption.
    discriminate.
  simpl in *. destruct l3. discriminate.
  simpl in *. case_eq (is_in_FOvar a l);  
    intros H2; rewrite H2 in *. discriminate.
  case_eq (is_all_diff_FOv l); intros H3; 
    rewrite H3 in *. 2 : discriminate.
  apply IHl1 in H. assumption.
  inversion Hl. reflexivity.
Qed.

Lemma ex_FOvar_l_ll_nil : forall l,
  ex_FOvar_l_ll l nil = false.
Proof.
  induction l. reflexivity.
  simpl. assumption.
Qed.

Lemma ex_FOvar_x_ll_app : forall l1 l2 x,
  ex_FOvar_x_ll x (app l1 l2) = 
  if ex_FOvar_x_ll x l1 then true else ex_FOvar_x_ll x l2.
Proof.
  induction l1; intros l2 [xn]. reflexivity.
  simpl. rewrite IHl1.
  case_eq (is_in_FOvar (Var xn) a); intros Hin;
    reflexivity.
Qed.

Lemma is_in_FOvar_new_FOvars_l: forall l xn ym,
  Nat.leb ( ym) xn = true ->
is_in_FOvar (Var ym) (new_FOvars_l l (Var (S xn))) = false.
Proof.
  induction l; intros xn ym H. reflexivity.
  simpl in *. destruct a as [zn]. (*  destruct xn. discriminate. *)
  rewrite IHl. 
  case_eq (beq_nat ym ( S( xn + zn))); intros Hbeq.
    2 : reflexivity.
  rewrite (beq_nat_true _ _ Hbeq) in H.
(*   apply leb_suc_l in H. *) simpl in H.
  destruct xn. discriminate.
  rewrite leb_suc_f2 in H. discriminate.
  assumption.
Qed.

Lemma ex_FOvar_x_ll_new_FOvars_ll: forall l2 xn ym,
  Nat.leb (S ym) xn = true ->
  ex_FOvar_x_ll (Var ym) (new_FOvars_ll l2 (Var xn)) = false.
Proof.
  induction l2; intros xn ym H. reflexivity.
  simpl in *. destruct xn. discriminate.
  rewrite IHl2.
  rewrite is_in_FOvar_new_FOvars_l. reflexivity.
  all : assumption.
Qed.

Lemma is_in_FOvar_new_FOvars_l_2: forall l xn ym,
  Nat.leb ( ym) xn = true ->
is_in_FOvar (Var 0)  l = false ->
is_in_FOvar (Var ym) (new_FOvars_l l (Var (xn))) = false.
Proof.
  induction l; intros xn ym H H2. reflexivity.
  simpl in *. destruct a as [zn]. (*  destruct xn. discriminate. *)
  rewrite IHl. 
  case_eq (beq_nat ym ( ( xn + zn))); intros Hbeq.
    2 : reflexivity.
  rewrite (beq_nat_true _ _ Hbeq) in H.
  destruct zn. discriminate.
  rewrite <- plus_n_Sm in H.
  rewrite <- plus_Sn_m in H.
  rewrite leb_suc_f2 in H. discriminate.
  assumption.
  destruct zn. discriminate. assumption.
Qed.

Lemma ex_FOvar_x_ll_new_FOvars_ll_2: forall l2 xn ym,
  Nat.leb  ym xn = true ->
  ex_FOvar_x_ll (Var 0) l2 = false ->
  ex_FOvar_x_ll (Var ym) (new_FOvars_ll l2 (Var xn)) = false.
Proof.
  induction l2; intros xn ym H H2. reflexivity.
  simpl in *.
  case_eq (is_in_FOvar (Var 0) a); intros Hin; rewrite Hin in *.
    discriminate.
  rewrite IHl2.
  rewrite is_in_FOvar_new_FOvars_l_2. reflexivity.
  all : try assumption.
Qed.

Lemma ex_FOvar_x_ll_new_FOvars_lll: forall l2 xn ym,
  Nat.leb (S ym) xn = true ->
  ex_FOvar_x_ll (Var ym)
    (flat_map (fun l1 : list (list FOvariable) => l1)
       (new_FOvars_lll l2 (Var xn))) = false.
Proof.
  induction l2; intros xn ym Hleb. reflexivity.
  simpl in *. destruct xn. discriminate.
  rewrite ex_FOvar_x_ll_app.
  rewrite IHl2. rewrite ex_FOvar_x_ll_new_FOvars_ll.
  reflexivity. all : assumption.
Qed.

Lemma ex_FOvar_x_ll_new_FOvars_lll_2: forall l2 xn ym,
  Nat.leb (ym) xn = true ->
  ex_FOvar_x_ll (Var 0) (flat_map (fun l => l) l2) = false ->
  ex_FOvar_x_ll (Var ym)
    (flat_map (fun l1 : list (list FOvariable) => l1)
       (new_FOvars_lll l2 (Var xn))) = false.
Proof.
  induction l2; intros xn ym Hleb H2. reflexivity.
  simpl in *.
  rewrite ex_FOvar_x_ll_app.
  rewrite IHl2. rewrite ex_FOvar_x_ll_new_FOvars_ll_2.
  reflexivity. all : try assumption.
  apply ex_FOvar_x_ll_app_l in H2. assumption.
  apply ex_FOvar_x_ll_app_r in H2. assumption.
Qed.

Lemma ex_FOvar_l_ll_app : forall l l1 l2,
  ex_FOvar_l_ll l (app l1 l2) = 
  if ex_FOvar_l_ll l l1 then true else ex_FOvar_l_ll l l2.
Proof.
  induction l; intros l1 l2. reflexivity.
  simpl. rewrite IHl. rewrite ex_FOvar_x_ll_app.
  case_eq ( ex_FOvar_x_ll a l1 ); intros H1.
    reflexivity.
  case_eq ( ex_FOvar_x_ll a l2); intros H2.
    rewrite if_then_else_true. reflexivity.
  reflexivity.
Qed.

Lemma ex_FOvar_l_ll_new_FOvars_pre : forall l l2 xn,
Nat.leb (S (max_FOv_l l)) xn = true ->
ex_FOvar_l_ll l
  (flat_map (fun l1 : list (list FOvariable) => l1)
     (new_FOvars_lll l2 (Var xn))) = false.
Proof.
  induction l; intros l2 xn H. reflexivity.
  simpl in *. destruct xn. discriminate.
  destruct a as [ym].
  rewrite ex_FOvar_x_ll_new_FOvars_lll.
  apply IHl.
  apply (leb_max _ _ _ H).
  simpl.
  apply (leb_max _ _ _ H).
Qed.

(* Left it here 18/12/17. Keep going! *)
Lemma ex_FOvar_l_ll_new_FOvars : forall l2 l  n,
ex_FOvar_l_ll l
  (flat_map (fun l1 : list (list FOvariable) => l1)
     (new_FOvars_lll l2 (Var (S(max_FOv_l l + n))))) = false.
Proof.
  intros l2 l n.
  apply ex_FOvar_l_ll_new_FOvars_pre.
  simpl. apply leb_plus_r. apply leb_refl.
Qed.

Lemma max_FOv_l_app : forall l1 l2,
  max_FOv_l (app l1 l2) = max (max_FOv_l l1) (max_FOv_l l2).
Proof.
  induction l1; intros l2.
    simpl. reflexivity.

    simpl. destruct a as [ym]. rewrite IHl1.
    apply PeanoNat.Nat.max_assoc.
Qed.

Lemma max_FOv__l : forall alpha,
  max_FOv alpha = max_FOv_l (FOvars_in alpha).
Proof.
  induction alpha; try assumption.
    simpl. destruct f. rewrite PeanoNat.Nat.max_0_r.
    reflexivity.

    destruct f. destruct f0. simpl. 
    rewrite PeanoNat.Nat.max_0_r. reflexivity.

    destruct f. destruct f0. simpl. 
    rewrite PeanoNat.Nat.max_0_r. reflexivity.

    destruct f. simpl.
    rewrite IHalpha. reflexivity.

    destruct f. simpl.
    rewrite IHalpha. reflexivity.

    simpl. rewrite IHalpha1. rewrite IHalpha2.
    rewrite max_FOv_l_app.
    reflexivity.

    simpl. rewrite IHalpha1. rewrite IHalpha2.
    rewrite max_FOv_l_app.
    reflexivity.

    simpl. rewrite IHalpha1. rewrite IHalpha2.
    rewrite max_FOv_l_app.
    reflexivity.
Qed.

(* Lemma ex_try  forall 
ex_FOvar_l_ll l
        (flat_map (fun l : list (list FOvariable) => l) lllv') = false ->
ex_FOvar_l_ll l
  (flat_map (fun l1 : list (list FOvariable) => l1)
     (new_FOvars_lll lllv'
        (Var (max_FOv_l l + n)))) = false. *)

Lemma ex_FOvar_l_ll_new_FOvars_2 : forall l lllv xn,
  Nat.leb (max_FOv_l l) xn = true ->
  ex_FOvar_x_ll (Var 0) (flat_map (fun l => l) lllv) = false ->
  ex_FOvar_l_ll l (flat_map (fun l => l) (new_FOvars_lll lllv (Var xn))) = false.
Proof.
  induction l; intros lllv xn Hleb H. reflexivity.
  simpl in *. destruct a as [ym]. rewrite IHl.

  rewrite ex_FOvar_x_ll_new_FOvars_lll_2. reflexivity.
    apply (leb_max _ _ _ Hleb).

    assumption.

    apply (leb_max _ _ _ Hleb).

    assumption.
Qed.

Lemma is_in_FOvar_new_FOvars_l_0 : forall l x,
  is_in_FOvar (Var 0) l = false ->
  is_in_FOvar (Var 0) (new_FOvars_l l x) = false.
Proof.
  induction l; intros [xn] H. reflexivity.
  simpl in *. destruct a as [ym].
  destruct ym. discriminate. rewrite <- plus_n_Sm.
  apply IHl. assumption.
Qed.

Lemma ex_FOvar_x_ll_new_FOvars_ll_0 : forall l x,
  ex_FOvar_x_ll (Var 0)  l = false ->
  ex_FOvar_x_ll (Var 0)  (new_FOvars_ll l x) = false.
Proof.
  induction l; intros [xn] H. reflexivity.
  simpl in *.
  case_eq (is_in_FOvar (Var 0) a); intros Hin; rewrite Hin in *.
    discriminate.
  rewrite IHl.
  rewrite is_in_FOvar_new_FOvars_l_0. reflexivity.
  all : assumption.
Qed.

Lemma ex_FOvar_x_ll_new_FOvars_lll_0 : forall l x,
  ex_FOvar_x_ll (Var 0) (flat_map (fun l => l) l) = false ->
  ex_FOvar_x_ll (Var 0) (flat_map (fun l => l) (new_FOvars_lll l x)) = false.
Proof.
  induction l; intros [xn] H. reflexivity.
  simpl in *. rewrite ex_FOvar_x_ll_app.
  rewrite IHl. rewrite ex_FOvar_x_ll_new_FOvars_ll_0.
  reflexivity. 
  apply (ex_FOvar_x_ll_app_l _ _ _ H).
  apply (ex_FOvar_x_ll_app_r _ _ _ H).
Qed.

Lemma length_new_FOvars_lll : forall lllv x,
  length (new_FOvars_lll lllv x) = length lllv.
Admitted.

Lemma is_un_predless_ex_att_predSO : forall alpha x,
  is_unary_predless alpha = true ->
  ex_att_predSO alpha x = false.
Proof.
  induction alpha; intros [xn] H; try reflexivity.
    simpl in *. destruct p. destruct f. discriminate.

    simpl in *. destruct f. apply IHalpha. assumption.
    simpl in *. destruct f. apply IHalpha. assumption.
    simpl in *.  apply IHalpha. assumption.

    simpl.
    rewrite (IHalpha1 _ (is_unary_predless_conjSO_l _ _ H)).
    apply (IHalpha2 _ (is_unary_predless_conjSO_r _ _ H)).

    simpl.
    rewrite (IHalpha1 _ (is_unary_predless_conjSO_l _ _ H)).
    apply (IHalpha2 _ (is_unary_predless_conjSO_r _ _ H)).

    simpl.
    rewrite (IHalpha1 _ (is_unary_predless_conjSO_l _ _ H)).
    apply (IHalpha2 _ (is_unary_predless_conjSO_r _ _ H)).

    destruct p. discriminate.
    destruct p. discriminate.
Qed.

Lemma ex_att_predSO_rep_pred : forall alpha y P x cond,
  is_unary_predless cond = true ->
  ex_att_predSO alpha y = false ->
  ex_att_predSO (replace_pred alpha P x cond) y = false.
Proof.
  induction alpha; intros [ym] [Pn] [xn] cond H1 H2.
    simpl. destruct p as [Qm]. destruct f as [zn].
    simpl in *. case_eq (beq_nat Pn Qm); intros Hbeq.
      apply is_un_predless_ex_att_predSO.
      apply rep_FOv_is_unary_predless. assumption.

      simpl. assumption.

    destruct f. destruct f0. reflexivity.

    destruct f. destruct f0. reflexivity.

    apply ex_att_predSO_allFO in H2.
    destruct f. simpl. apply IHalpha; assumption.

    apply ex_att_predSO_exFO in H2.
    destruct f. simpl. apply IHalpha; assumption.

    apply ex_att_predSO_negSO in H2.
    simpl. apply IHalpha; assumption.

    simpl. rewrite IHalpha1. apply IHalpha2.
    all : try assumption.
    apply (ex_att_predSO_conjSO_r _ _ _ H2).
    apply (ex_att_predSO_conjSO_l _ _ _ H2).

    simpl. rewrite IHalpha1. apply IHalpha2.
    all : try assumption.
    apply (ex_att_predSO_conjSO_r _ _ _ H2).
    apply (ex_att_predSO_conjSO_l _ _ _ H2).

    simpl. rewrite IHalpha1. apply IHalpha2.
    all : try assumption.
    apply (ex_att_predSO_conjSO_r _ _ _ H2).
    apply (ex_att_predSO_conjSO_l _ _ _ H2).

    destruct p as [Qm]. simpl in *.
    case_eq (beq_nat Pn Qm); intros Hbeq; simpl;
      apply IHalpha; assumption.

    destruct p as [Qm]. simpl in *.
    case_eq (beq_nat Pn Qm); intros Hbeq; simpl;
      apply IHalpha; assumption.
Qed.

Lemma ex_att_predSO_l_rep_pred : forall lv alpha P x cond,
  is_unary_predless cond = true ->
  ex_att_predSO_l alpha lv = false ->
  ex_att_predSO_l (replace_pred alpha P x cond) lv = false.
Proof.
  induction lv; intros alpha P [xn] cond H1 H2. reflexivity.
  destruct a as [ym]. simpl in *.
  case_eq (ex_att_predSO alpha (Var ym)); intros H3; rewrite H3 in *.
    discriminate.
  rewrite ex_att_predSO_rep_pred. apply IHlv. all : assumption.
Qed.

Lemma ex_att_predSO_ll_rep_pred : forall llv alpha P x cond,
  is_unary_predless cond = true ->
  ex_att_predSO_ll alpha llv = false ->
  ex_att_predSO_ll (replace_pred alpha P x cond) llv = false.
Proof.
  induction llv; intros alpha P x cond H2 H3. reflexivity.
  simpl in *. case_eq (ex_att_predSO_l alpha a);
    intros H4; rewrite H4 in *. discriminate.

    rewrite ex_att_predSO_l_rep_pred.
    apply IHllv. all : assumption.
Qed.

Lemma ex_att_predSO_ll_app_r : forall l1 l2 alpha,
  ex_att_predSO_ll alpha (app l1 l2) = false ->
  ex_att_predSO_ll alpha l2 = false.
Proof.
  induction l1; intros l2 alpha H.
    simpl in *. assumption.

    simpl in *.
    case_eq (ex_att_predSO_l alpha a); intros H2; rewrite H2 in *.
      discriminate.
    apply IHl1. assumption.
Qed.

Lemma ex_att_predSO_ll_app_l : forall l1 l2 alpha,
  ex_att_predSO_ll alpha (app l1 l2) = false ->
  ex_att_predSO_ll alpha l1 = false.
Proof.
  induction l1; intros l2 alpha H. reflexivity.
    simpl in *.
    case_eq (ex_att_predSO_l alpha a); intros H2; rewrite H2 in *.
      discriminate.
    apply IHl1 in H. assumption.
Qed.

Lemma ex_bound_FO_ll_cons : forall llx lx alpha,
  ex_bound_FO_ll alpha (cons lx llx) = false <->
  (ex_bound_FO_l alpha lx = false /\ ex_bound_FO_ll alpha llx = false).
Proof.
  intros.
  simpl. case_eq (ex_bound_FO_l alpha lx); intros H.
  split. discriminate.
    intros [SOt1 SOt2]. discriminate.
  split; intros SOt. apply conj. reflexivity. assumption.
  apply SOt.
Qed.

Lemma ex_bound_FO_overP_ll_cons : forall llx lx alpha,
  ex_bound_FO_overP_ll alpha (cons lx llx) = false <->
  (ex_bound_FO_overP_l alpha lx = false /\ ex_bound_FO_overP_ll alpha llx = false).
Proof.
  intros.
  simpl. case_eq (ex_bound_FO_overP_l alpha lx); intros H.
  split. discriminate.
    intros [SOt1 SOt2]. discriminate.
  split; intros SOt. apply conj. reflexivity. assumption.
  apply SOt.
Qed.


Lemma ex_FOvar_x_ll_cons : forall llx1 l x,
  ex_FOvar_x_ll x (cons l llx1) = false <->
  is_in_FOvar x l = false /\ ex_FOvar_x_ll x llx1 = false.
Proof.
  intros llx1 l x.
  simpl. case_eq (is_in_FOvar x l); intros H.
    split. discriminate.
    intros [H1 H2]. discriminate.

    split; intros H2. apply conj. reflexivity.
    all : apply H2.
Qed.

Lemma length_id_gen_2_1 : forall {A  B: Type} (l1 : list (list A)) (l2 : list (list B)),
  length_id_2_gen l1 l2 = true ->
  length_id_1_gen l1 l2 = true ->
  length_id_1_gen (flat_map (fun l => l) l1) (flat_map (fun l => l) l2) = true.
Proof.
  induction l1; intros l2 H1 H2. simpl. destruct l2. reflexivity.
    discriminate.

     simpl in *. destruct l2. discriminate.
    apply length__id_1_gen.
    case_eq (length_id_1_gen a l); intros H3; rewrite H3 in *.
      2 : discriminate.
    apply length__id_1_gen in H3. simpl.
    do 2 rewrite app_length. rewrite H3.
    specialize (IHl1 _ H1 H2).
    apply length__id_1_gen in IHl1. rewrite IHl1. reflexivity.
Qed. 

Lemma length_id_1_gen_cons : forall {A B : Type} (l1 : list A) (l2 : list B) a1 a2,
  length_id_1_gen (cons a1 l1) (cons a2 l2) = true ->
  length_id_1_gen l1 l2 = true.
Proof.
  intros until 0. intros H.
  simpl in H. assumption.
Qed.

Lemma list_quant_FOv_overP_is_un_predless : forall alpha,
  is_unary_predless alpha = true ->
  list_quant_FOv_overP alpha = nil.
Proof.
  induction alpha; intros H; try reflexivity;
    try (destruct f; simpl in *; rewrite H; apply IHalpha; assumption);
    try (simpl in *; rewrite H; apply IHalpha; assumption);
    try (simpl in *; apply IHalpha; assumption).

simpl. rewrite (IHalpha1 (is_unary_predless_conjSO_l _ _ H)).
 rewrite (IHalpha2 (is_unary_predless_conjSO_r _ _ H)).
reflexivity.

simpl. rewrite (IHalpha1 (is_unary_predless_conjSO_l _ _ H)).
 rewrite (IHalpha2 (is_unary_predless_conjSO_r _ _ H)).
reflexivity.

simpl. rewrite (IHalpha1 (is_unary_predless_conjSO_l _ _ H)).
 rewrite (IHalpha2 (is_unary_predless_conjSO_r _ _ H)).
reflexivity.

destruct p.
discriminate.
destruct p.
discriminate.
Qed.

Lemma is_in_FOvar_list_quant_FOv_overP_rep_pred : forall alpha cond P y x,
  is_unary_predless cond = true ->
is_in_FOvar x (list_quant_FOv_overP alpha) = false ->
is_in_FOvar x (list_quant_FOv_overP (replace_pred alpha P y cond)) = false.
Proof.
  induction alpha; intros cond [Pn] [ym] [xn] Hun H.
    simpl in *. destruct p as [Qm].
    destruct f as [zn].
    case_eq (beq_nat Pn Qm); intros Hbeq.
      rewrite list_quant_FOv_overP_is_un_predless. reflexivity.
      apply rep_FOv_is_unary_predless. assumption.

      reflexivity.

    destruct f. destruct f0. simpl. reflexivity.

    destruct f. destruct f0. simpl. reflexivity.

    destruct f as [zn]. simpl in *.
    case_eq (is_unary_predless alpha); intros Hun2; rewrite Hun2 in *.
      rewrite rep_pred_is_unary_predless. rewrite Hun2. assumption.
        assumption.

      apply is_in_FOvar_cons_f in H. destruct H as [H1 H2].
      case_eq (is_unary_predless (replace_pred alpha (Pred Pn) (Var ym) cond));
        intros H3. apply IHalpha; assumption.

        simpl. rewrite FOvar_neq. apply IHalpha. all : try assumption.

    destruct f as [zn]. simpl in *.
    case_eq (is_unary_predless alpha); intros Hun2; rewrite Hun2 in *.
      rewrite rep_pred_is_unary_predless. rewrite Hun2. assumption.
        assumption.

      apply is_in_FOvar_cons_f in H. destruct H as [H1 H2].
      case_eq (is_unary_predless (replace_pred alpha (Pred Pn) (Var ym) cond));
        intros H3. apply IHalpha; assumption.

        simpl. rewrite FOvar_neq. apply IHalpha. all : try assumption.

    simpl in *. apply IHalpha; assumption.

    simpl in *. rewrite is_in_FOvar_app.
    rewrite (IHalpha1 _ _ _ _ Hun (is_in_FOvar_app_l _ _ _ H)).
    apply (IHalpha2 _ _ _ _ Hun (is_in_FOvar_app_r _ _ _ H)).

    simpl in *. rewrite is_in_FOvar_app.
    rewrite (IHalpha1 _ _ _ _ Hun (is_in_FOvar_app_l _ _ _ H)).
    apply (IHalpha2 _ _ _ _ Hun (is_in_FOvar_app_r _ _ _ H)).

    simpl in *. rewrite is_in_FOvar_app.
    rewrite (IHalpha1 _ _ _ _ Hun (is_in_FOvar_app_l _ _ _ H)).
    apply (IHalpha2 _ _ _ _ Hun (is_in_FOvar_app_r _ _ _ H)).

    simpl in *. destruct p as [Qm]. case_eq (beq_nat Pn Qm);
      intros Hbeq. apply IHalpha; assumption.

      simpl. apply IHalpha; assumption.

    simpl in *. destruct p as [Qm]. case_eq (beq_nat Pn Qm);
      intros Hbeq. apply IHalpha; assumption.

      simpl. apply IHalpha; assumption.
Qed.

Lemma bound_FO_overP_rep_pred : forall alpha P y x cond,
  is_unary_predless cond = true ->
  bound_FO_overP alpha x = false ->
  bound_FO_overP (replace_pred alpha P y cond) x = false.
Proof.
  intros alpha P y x cond Hun H.
  unfold bound_FO_overP in *.
  apply is_in_FOvar_list_quant_FOv_overP_rep_pred;
  assumption.
Qed.

Lemma ex_bound_FO_overP_l_rep_pred : forall lx1 alpha cond P y,
  is_unary_predless cond = true ->
  ex_bound_FO_overP_l alpha lx1 = false ->
  ex_bound_FO_overP_l (replace_pred alpha P y cond) lx1 = false.
Proof.
  induction lx1; intros alpha cond P y Hun H. reflexivity.
  simpl in H. apply if_then_else_tf in H.
  destruct H as [H1 H2].
  simpl. rewrite bound_FO_overP_rep_pred.
  apply IHlx1. all : assumption.
Qed.

Lemma ex_bound_FO_overP_ll_rep_pred : forall llx1 alpha cond P y,
  is_unary_predless cond = true ->
  ex_bound_FO_overP_ll alpha llx1 = false ->
  ex_bound_FO_overP_ll (replace_pred alpha P y cond) llx1 = false.
Proof.
  induction llx1; intros alpha cond P y Hun Hex. reflexivity.
  apply ex_bound_FO_overP_ll_cons in Hex. destruct Hex as [Hex1 Hex2].  
  simpl in *. rewrite ex_bound_FO_overP_l_rep_pred.
  apply IHllx1. all : assumption .
Qed.

Lemma consistent_lP_lcond_P_fun4_l2_lP'_pre : forall lP lllv llx1 llx0 P y a1 n1 a2 n2,
length llx1 = length lllv ->
ind_llv (indicies_l2 lP P) llx1 = constant_l a1 n1 ->
@ind_gen _ llx0 (indicies_l2 lP P) lllv = constant_l a2 n2 ->
exists (n : nat),
  ind_cond (indicies_l2 lP P) (fun4_l2_lP' llx1 (list_Var (length lP) y) lllv) = constant_l (fun4_l2' a1 y a2) n.
Proof.
  induction lP; intros until 0; intros Hlength H1 H2.
    simpl in *. exists 0. reflexivity.

    simpl in *. unfold indicies_l2 in *. simpl in *.
    destruct P as [Pn]. destruct a as [Qm].
    case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *.
        simpl in *. destruct llx1. destruct n1.
        discriminate. destruct a1. 2 : discriminate. simpl.
        rewrite ind_cond_nil_gen.
        exists (S (length (indicies_l2_pre lP (Pred Pn) 1))).
        reflexivity.

        destruct n1. discriminate.
        simpl in H1. inversion H1 as [[H1' Hl'']].
        simpl. destruct lllv. discriminate.

        rewrite ind_cond_ind_l2_pre_cons.
        simpl in Hlength. inversion Hlength as [Hlength'].
        rewrite ind_llv_ind_l2_pre_cons in Hl''.
        rewrite ind_gen_pre_cons in H2. destruct n2. discriminate.
        inversion H2 as [[H2' H2'']].
        destruct (IHlP _ _ _ _ y _ _ _ _ Hlength' Hl'' H2'')
          as [n IH].
        exists (S n). rewrite IH. reflexivity.


        destruct llx1. simpl in *. rewrite ind_cond_nil_gen.
        rewrite ind_llv_nil_gen in H1.
        destruct lllv. 2 : discriminate.
        rewrite ind_gen_nil_gen in H2.
        destruct n1. case_eq (length (indicies_l2_pre lP (Pred Pn) 1)).
          simpl. intros. exists 0. reflexivity.
          intros m Hm; rewrite Hm in *. discriminate.

        destruct a1. simpl. exists (length (indicies_l2_pre lP (Pred Pn) 1)).
          reflexivity.

          destruct (length (indicies_l2_pre lP (Pred Pn) 1)); discriminate.

        destruct lllv. discriminate.
        simpl. rewrite ind_cond_ind_l2_pre_cons.
        rewrite ind_llv_ind_l2_pre_cons in H1.
        rewrite ind_gen_pre_cons in H2.
        simpl in Hlength. inversion Hlength as [Hlength2].
        apply (IHlP _ _ _ _ _ _ _ _ _ Hlength2 H1 H2) .
Qed.

Lemma consistent_lP_lcond_P_fun4_l2_lP' : forall lP llx1 lllv y llx0 P,
  length llx1 = length lllv ->
  consistent_lP_llv_P lP llx1 P->
  @consistent_lP_lllv_P llx0 lP lllv P ->
  consistent_lP_lcond_P lP  (fun4_l2_lP' llx1 (list_Var (length lP) y) lllv) P.
Proof.
  intros lP llx1 lllv y llx0 P Hlength H1 H2.
  unfold consistent_lP_lcond_P.
  unfold consistent_lP_llv_P in H1.
  unfold consistent_lP_lllv_P in H2.
  unfold is_constant in *.
  destruct H1 as [a1 [n1 H1]].
  destruct H2 as [a2 [n2 H2]].
  exists (fun4_l2' a1 y a2). 
  apply (consistent_lP_lcond_P_fun4_l2_lP'_pre _ _ _ _ _ _ _ _ _ _ Hlength H1 H2).
Qed.

Lemma consistent_lP_lcond_fun4_l2_lP' : forall lP llx1 lllv y llx0,
  length llx1 = length lllv ->
  consistent_lP_llv lP llx1 ->
  @consistent_lP_lllv llx0 lP lllv ->
  consistent_lP_lcond lP  (fun4_l2_lP' llx1 (list_Var (length lP) y) lllv).
Proof.
  intros until 0. intros H0 H1 H2.
  unfold consistent_lP_llv in *.
  unfold consistent_lP_lllv in H2.
  unfold consistent_lP_lcond.
  intros P.
  specialize (H1 P).
  specialize (H2 P).
  apply (consistent_lP_lcond_P_fun4_l2_lP' _ _ _ _ _ _ H0 H1 H2).
Qed.

(* This is good!!! 
Need to check it can now be applied. *)
Lemma sSahlq_equiv_new_simpl_try3_LP'_withextrahyp3 : forall lP lllv llx1 y W alpha Iv Ip Ir,
(*   length lP = length llv -> *)
  SOQFree alpha = true ->
consistent_lP_llv lP llx1 ->
@consistent_lP_lllv nil lP lllv ->
  length_id_2_gen llx1 lllv = true ->
  length_id_1_gen llx1 lllv = true ->
   ex_bound_FO_overP_ll alpha llx1 = false ->
  ex_FOvar_x_ll y (flat_map (fun l => l) lllv) = false ->
  ex_att_predSO_ll alpha (flat_map (fun l => l) lllv) = false ->
  ex_FOvar_x_ll y llx1 = false ->
  is_all_diff_FOv3 (flat_map (fun l => l) llx1) (flat_map (fun l => l) lllv) = true ->
    SOturnst W Iv (alt_Ip_list Ip (sSahlq_pa_l5' Ir lllv (map2 (Iv_ify Iv) llx1)) lP) Ir alpha <->
    SOturnst W Iv Ip Ir (replace_pred_l alpha lP (list_Var (length lP) y)
      (fun4_l2_lP' llx1 (list_Var (length lP) y) lllv)).
Proof.
  induction lP; intros lllv llx1 y W alpha Iv Ip Ir Hno Hcon1 Hcon2 Hl Hl1 Hb Hex1 Hex3 Hex2 Hall.
    simpl. rewrite alt_Ip_list_nil. apply iff_refl.

    destruct llx1. simpl. destruct lllv; apply iff_refl.
    destruct lllv. apply iff_refl.
    simpl sSahlq_pa_l5'. simpl alt_Ip_list.
    simpl replace_pred_l.

simpl in Hl. case_eq (length_id_1_gen l l0); intros Hl'; rewrite Hl' in *.
  2 : discriminate.
apply ex_bound_FO_overP_ll_cons in Hb. destruct Hb as [Hb1 Hb2].
simpl in Hex1.
pose proof (ex_FOvar_x_ll_app_l _ _ _ Hex1) as Hex1'.
pose proof (ex_FOvar_x_ll_app_r _ _ _ Hex1) as Hex1''.
apply (ex_FOvar_x_ll_cons) in Hex2. 
destruct Hex2 as [Hex2a Hex2b].
simpl in Hall.
pose proof (is_all_diff_FOv3_app_l _ _ _ _ Hall) as Hall'.
assert (length l  = length l0) as Hl''.
  apply (length__id_1_gen l l0). assumption.
pose proof (length_id_1_gen_cons _ _ _ _ Hl1) as Hl1'.
(* apply length__id_1_gen in Hl1'. *)
pose proof (length_id_gen_2_1 _ _ Hl Hl1') as Hl1''.
apply length__id_1_gen in Hl1''.
(* pose proof (is_all_diff_FOv3_ex_FOvar_l_ll_app _ _ _ _ Hl'' Hl1'' Hall) as Hall''. *)
    split; intros SOt.
(* destruct (equiv_rep_pred_l_fun4_l2_lP'_1 lP lllv llx1 (replace_pred alpha a y (fun4_l2' l y l0)) y) as [x [HH1 HH2]]. *)
      rewrite rep_pred__l_consistent.
      apply IHlP.
all : try assumption.

apply SOQFree_rep_pred. assumption. apply SOQFree_fun4_l2'.

apply consistent_lP_llv_cons_rem_gen in Hcon1. assumption.
apply consistent_lP_lllv_cons in Hcon2. assumption.

apply ex_bound_FO_overP_ll_rep_pred.
  apply is_un_predless_fun4_l2'.
  assumption.

apply ex_att_predSO_ll_rep_pred.
apply is_un_predless_fun4_l2'.
simpl in Hex3.
apply ex_att_predSO_ll_app_r in Hex3.
assumption.

(* Search is_all_diff_FOv3 app. *)

apply is_all_diff_FOv3_app_r in Hall; try assumption.

    apply sSahlq_equiv_new_simpl_try3_LP'_pre_rid_hyp_3;
      try assumption.

apply ex_att_predSO_ll_app_l in Hex3. assumption.
apply is_un_predless_l_fun4_l2_lP'.
apply is_un_predless_fun4_l2'.

apply (consistent_lP_lcond_fun4_l2_lP' (cons a lP) (cons l llx1) (cons l0 lllv) _ nil); try
assumption.
apply length__id_1_gen. assumption.

apply (consistent_lP_lx_list_Var (cons a lP)).

(* --- *)

      rewrite rep_pred__l_consistent in SOt.
      apply IHlP in SOt.
all : try assumption.

    apply sSahlq_equiv_new_simpl_try3_LP'_pre_rid_hyp_3 in SOt;
      try assumption.
apply ex_att_predSO_ll_app_l in Hex3. assumption.

apply SOQFree_rep_pred. assumption. apply SOQFree_fun4_l2'.

apply consistent_lP_llv_cons_rem_gen in Hcon1. assumption.

apply consistent_lP_lllv_cons in Hcon2. assumption.

apply ex_bound_FO_overP_ll_rep_pred.
  apply is_un_predless_fun4_l2'.
  assumption.

apply ex_att_predSO_ll_rep_pred.
apply is_un_predless_fun4_l2'.
simpl in Hex3.
apply ex_att_predSO_ll_app_r in Hex3.
assumption.

apply is_all_diff_FOv3_app_r in Hall; try assumption.

apply is_un_predless_l_fun4_l2_lP'.
apply is_un_predless_fun4_l2'.


apply (consistent_lP_lcond_fun4_l2_lP' (cons a lP) (cons l llx1) (cons l0 lllv) _ nil);
try assumption.

apply length__id_1_gen. assumption.


apply (consistent_lP_lx_list_Var (cons a lP)).
Qed.

Lemma calc_lP_fun4_l2_lP'_equiv : forall lP alpha,
 (calc_lP alpha lP) = (fun4_l2_lP' (calc_lx1_lP alpha lP)
     (list_Var (length lP) (Var (new_FOv_pp_pre2 alpha)))
     (calc_llv_lP alpha lP)).
Proof.
  induction lP; intros alpha. reflexivity.
  simpl. rewrite IHlP. reflexivity.
Qed.

Lemma SOQFree_BAT : forall alpha,
  BAT alpha = true ->
  SOQFree alpha = true.
Admitted.

Lemma consistent_lP_llv_calc_lx1_lP : forall lP alpha,
  consistent_lP_llv lP (calc_lx1_lP alpha lP).
Admitted.

Lemma consistent_lP_lllv_calc_llv_lP : forall lP alpha llx0,
  @consistent_lP_lllv llx0 lP (calc_llv_lP alpha lP).
Admitted.

Lemma length_id_1_gen_calc_lx1_llv_lP : forall lP alpha,
  length_id_1_gen (calc_lx1_lP alpha lP) (calc_llv_lP alpha lP) = true.
Proof.
  induction lP; intros alpha; try reflexivity.
  simpl. apply IHlP.
Qed.

Lemma length_id_1_gen_calc_lx1_llv_P : forall alpha P,
  length_id_1_gen (calc_lx1_P alpha P) (calc_llv_P alpha P) = true.
Proof.
  induction alpha; intros [Pn]; try reflexivity.
    simpl. destruct alpha; try reflexivity.
    case_eq (P_branch_allFO alpha2 (Pred Pn)); intros HP.
      destruct alpha1; try reflexivity.
      reflexivity.
 
    simpl. apply length__id_1_gen.
    do 2 rewrite app_length.
    specialize (IHalpha1 (Pred Pn)).
    specialize (IHalpha2 (Pred Pn)).
    apply length__id_1_gen in IHalpha1.
    apply length__id_1_gen in IHalpha2.
    rewrite IHalpha1. rewrite IHalpha2. reflexivity.
Qed.

Lemma length_id_2_gen_calc_lx1_llv_lP : forall lP alpha,
length_id_2_gen (calc_lx1_lP alpha lP) (calc_llv_lP alpha lP) = true.
Proof.
  induction lP; intros alpha. reflexivity.
  simpl. rewrite IHlP. rewrite length_id_1_gen_calc_lx1_llv_P.
  reflexivity.
Qed.
(* Search P_branch_allFO is_unary_predless. *)

Lemma P_branch_allFO_is_un_predless : forall alpha P,
  P_branch_allFO alpha P = true ->
  is_unary_predless alpha = false.
Admitted.

Lemma ex_bound_FO_overP_ll_calc_lx1_lP_allFO : forall alpha P f,
  is_in_FOvar (Var 0) (list_quant_FOv_overP (allFO f alpha)) = false ->
(forall P : predicate, ex_bound_FO_overP_l alpha (calc_lx1_P alpha P) = false) ->
ex_bound_FO_overP_l (allFO f alpha) (calc_lx1_P (allFO f alpha)P) = false.
Proof.
Admitted.
(*
  intros alpha P [xn] Hin IH.
  simpl. destruct alpha; try reflexivity.
  case_eq (P_branch_allFO alpha2 P); intros HP.
    2 : reflexivity.
  destruct alpha1; simpl; unfold bound_FO_overP. 
    simpl. destruct p as [Qm]. destruct f as [ym].
    simpl. destruct xn. discriminate. simpl in *.
    rewrite Hin. reflexivity.

    simpl. destruct f as [zn]. destruct f0. simpl in *.

    pose proof (P_branch_allFO_is_un_predless _ _ HP) as Hun.
    rewrite Hun in *. simpl.
    case_eq (is_unary_predless alpha2); intros Hun; rewrite Hun in *.
      rewrite list_quant_FOv_overP_is_un_predless. reflexivity. assumption.
      simpl.
      case_eq (beq_nat zn xn); intros Hbeq.
      rewrite Hin.
       simpl.
; try reflexivity.
admit.

    reflexivity.
    simpl.
*)
Lemma ex_bound_FO_overP_l_calc_lx1_lP : forall alpha P,
ex_bound_FO_overP_l alpha (calc_lx1_P alpha P) = false.
Proof.
Admitted.
(*
  induction alpha; intros [Pn]; try reflexivity.
    simpl. destruct alpha; try reflexivity.
    case_eq (P_branch_allFO alpha2 (Pred Pn));
      intros HP. destruct alpha1; try reflexivity.
simpl. unfold 
    simpl.
*)
Lemma ex_bound_FO_overP_ll_calc_lx1_lP : forall lP alpha,
  ex_bound_FO_overP_ll alpha (calc_lx1_lP alpha lP) = false.
Proof.
  induction lP; intros alpha. reflexivity.
  simpl. rewrite IHlP. rewrite ex_bound_FO_overP_l_calc_lx1_lP.
  reflexivity.
Qed.

Lemma sSahlq_equiv_new_simpl_try3_LP'_withextrahyp_BAT : forall lP W alpha Iv Ip Ir,
(*   length lP = length llv -> *)
  BAT alpha = true ->
(*   consistent_lP_llv lP llv ->
  (forall P, exists n pa, ind_pa (indicies_l2 lP P) 
      (CM_pa2_l_gen_l Iv llv (list_Var (length lP) x)) = constant_l pa n) ->
  ex_attached_allFO_llv alpha llv = false ->
  ex_attached_exFO_llv alpha llv = false -> *)
(* consistent_lP_llv ( lP) llx1 ->
@consistent_lP_lllv nil (lP) llv ->
  ex_attached_allFO_lllv alpha llv = false ->
  ex_attached_exFO_lllv alpha llv = false ->
  ex_attached_allFO_llv alpha llx1 = false ->
  ex_attached_exFO_llv alpha llx1 = false ->
  (map (@length FOvariable) llx1) = (map (@length (list FOvariable)) llv) -> *)
(*   ex_FOvar_x_ll x llx1 = false -> *)
(*   ex_FOvar_x_ll x (flat_map (fun l => l) llv) = false -> *)

(* ex_FOvar_l_ll (FOvars_in alpha) (flat_map (fun ll => ll) llv) = false -> *)

(*   is_all_diff_FOv (app (cons x nil) (flat_map (fun l => l) (app llx1 (flat_map (fun l => l) llv)))) = true -> *)
    SOturnst W Iv (alt_Ip_list Ip (sSahlq_pa_l5' Ir (calc_llv_lP alpha lP) (map2 (Iv_ify Iv) (calc_lx1_lP alpha lP))) lP) Ir alpha <->
    SOturnst W Iv Ip Ir (replace_pred_l alpha lP (list_Var (length lP) (Var (new_FOv_pp_pre2 alpha)))
      (calc_lP alpha lP)).
Proof.
  intros lP W alpha Iv Ip Ir Hbat.
  split; intros SOt.
apply (sSahlq_equiv_new_simpl_try3_LP'_withextrahyp3 lP (calc_llv_lP alpha lP) (calc_lx1_lP alpha lP) (Var (new_FOv_pp_pre2 alpha))) in SOt.
    rewrite calc_lP_fun4_l2_lP'_equiv.
    assumption.

    apply SOQFree_BAT. assumption.

    apply consistent_lP_llv_calc_lx1_lP.

    apply consistent_lP_lllv_calc_llv_lP.

    apply length_id_2_gen_calc_lx1_llv_lP.

    apply length_id_1_gen_calc_lx1_llv_lP.


admit. (* add in? *)
admit. (*true *)
admit. (* add in? *) 
admit. (* true *)
admit. (* add in? *)

apply (sSahlq_equiv_new_simpl_try3_LP'_withextrahyp3 lP (calc_llv_lP alpha lP) 
        (calc_lx1_lP alpha lP) (Var (new_FOv_pp_pre2 alpha))).

    apply SOQFree_BAT. assumption.

    apply consistent_lP_llv_calc_lx1_lP.

    apply consistent_lP_lllv_calc_llv_lP.

    apply length_id_2_gen_calc_lx1_llv_lP.

    apply length_id_1_gen_calc_lx1_llv_lP.
admit. (* add in? *)
admit. (*true *)
admit. (* add in? *) 
admit. (* true *)
admit. (* add in? *)

    rewrite <- calc_lP_fun4_l2_lP'_equiv.
    assumption.
Admitted.


(* --------------------------------- *)

(* Counts the number of outermost consecutive allFO *)
Fixpoint count_allFO (alpha : SecOrder) (n : nat) : nat :=
  match alpha with 
  | allFO _ beta => count_allFO beta (S n)
  | implSO beta1 beta2 => count_allFO beta2 n
  | _ => n
  end.


(* --- *)

(* Correctness from Modal to SecOrder *)
Lemma lem_bxatm12 : forall phi x,
  bxatm phi = true ->
  exists lx P,
  ST phi x = BOXATM2 P x lx.
Proof.
  induction phi; intros [xn] H; try discriminate.
    destruct p as [Pn]. simpl. exists nil. exists (Pred Pn).
    reflexivity.

    simpl in H. destruct (IHphi (Var (S xn)) H) as [lx [P  H2]].
    exists (cons (Var (S xn)) lx). exists P.
    simpl. rewrite <- one_suc. rewrite H2. reflexivity.
Qed.

Lemma lem_bxatm5 : forall alpha n,
  count_allFO alpha (S n) = S (count_allFO alpha n).
Proof.
  induction alpha; intros n; try reflexivity.
    destruct f. simpl. rewrite IHalpha. reflexivity.

    simpl. apply IHalpha2.
Qed.

Lemma lem_bxatm14_pre : forall m n alpha x,
  Nat.leb n m = true ->
  count_allFO alpha 0 = n ->
  BOXATM_flag_strong alpha x = true ->
  exists lx P,
    alpha = BOXATM2 P x lx.
Proof.
  induction m; intros n alpha x Hleb H1 H2.
  destruct n. destruct alpha; try discriminate.
    destruct p as [Pn]. destruct f as [ym]. simpl in *.
    destruct x as [xn]. rewrite (beq_nat_true _ _ H2).
    exists nil. exists (Pred Pn). reflexivity.

    (* simpl in H2. *) induction alpha; try discriminate.
    destruct alpha1; try discriminate.
    destruct x as [xn]; destruct f as [z1];
    destruct f0 as [z2]; destruct f1 as [z3].
    simpl in *. rewrite lem_bxatm5 in H1. discriminate.
      discriminate.
  
    apply leb_suc2 in Hleb. destruct Hleb as [Hleb | Hleb].
      apply IHm with (n := n); try assumption.

      rewrite Hleb in *.    
      destruct alpha; try discriminate.
        destruct alpha; try discriminate.
        destruct alpha1; try discriminate.
        simpl in H1. rewrite lem_bxatm5 in H1.
        inversion H1 as [H1'].

    destruct x as [xn]; destruct f as [z1];
    destruct f0 as [z2]; destruct f1 as [z3].
    simpl in H2.
    case_eq (beq_nat xn z2); intros H1''; rewrite H1'' in *. 2 : discriminate.
    case_eq (beq_nat z1 z3); intros H2'; rewrite H2' in *. 2 : discriminate.
    case_eq (beq_nat z3 (S z2)); intros H3'; rewrite H3' in *. 2 : discriminate.
    destruct (IHm m alpha2 (Var z1) (leb_refl _) H1' H2) as [lx [P IH]].
    exists (cons (Var z1) lx). exists P.
    simpl. rewrite IH. rewrite (beq_nat_true _ _ H1''). 
    rewrite (beq_nat_true _ _ H2'). reflexivity.
Qed.

(* Alignment of object BOXATM2 and bool function BOXATM_flag_strong *)
Lemma lem_bxatm14 : forall alpha x,
  BOXATM_flag_strong alpha x = true ->
  exists lx P,
    alpha = BOXATM2 P x lx.
Proof.
  intros alpha x.
  apply (lem_bxatm14_pre (count_allFO alpha 0) (count_allFO alpha 0) _ _
    (leb_refl _)).
  reflexivity.
Qed.

Lemma is_BOXATM_flag_strong__CONJ : forall alpha1 alpha2 f,
is_BOXATM_flag_strong_CONJ (allFO f (implSO alpha1 alpha2)) = true ->
BOXATM_flag_strong alpha2 f = true.
Proof.
  intros alpha1 alpha2 f H.
    destruct alpha1; try (destruct f as [n]; destruct n; discriminate).
  destruct f as [xn]; destruct f0 as [x1]; destruct f1 as [x2].
  simpl in H. destruct xn. discriminate.
  case_eq (beq_nat xn x1); intros Hbeq; rewrite Hbeq in *.
   2: discriminate.
  case_eq (beq_nat (S xn) x2); intros Hbeq2; rewrite Hbeq2 in *.
    2 : discriminate.
  case_eq (beq_nat x2 (S x1)); intros Hbeq3; rewrite Hbeq3 in *.
    2 : discriminate.
  assumption.
Qed.

Lemma is_BOXATM_flag_strong__CONJ_BAT : forall alpha1 alpha2 f,
BAT (allFO f (implSO alpha1 alpha2)) = true ->
BOXATM_flag_weak alpha2 f = true.
Proof.
  intros alpha1 alpha2 f H.
    destruct alpha1; try (destruct f as [n]; destruct n; discriminate).
  destruct f as [xn]; destruct f0 as [x1]; destruct f1 as [x2].
  simpl in H. rewrite <- beq_nat_refl in H.
  case_eq (beq_nat xn x2); intros Hbeq; rewrite Hbeq in *.
   2: discriminate.
(*   case_eq (beq_nat (S xn) x2); intros Hbeq2; rewrite Hbeq2 in *.
    2 : discriminate. *)
(*   case_eq (beq_nat x2 (S x1)); intros Hbeq3; rewrite Hbeq3 in *.
    2 : discriminate. *)
  assumption.
Qed.

Lemma is_BOXATM_flag_strong_CONJ_allFO_eq : forall f f0 f1 alpha,
  is_BOXATM_flag_strong_CONJ (allFO f (implSO (relatSO f0 f1) alpha)) = true ->
  f = f1.
Proof.
  intros [x1] [x2] [x3] alpha H.
  simpl in *. destruct x1. discriminate.
  case_eq (beq_nat x1 x2); intros Hbeq; rewrite Hbeq in *.
    2 : discriminate.
  case_eq (beq_nat (S x1) x3); intros Hbeq2; rewrite Hbeq2 in *.
    2 : discriminate. 
(*   apply beq_nat_true. *)
  apply beq_nat_true in Hbeq2. rewrite Hbeq2. reflexivity.
Qed.

Lemma is_BOXATM_flag_strong_CONJ_allFO_eq_BAT : forall f f0 f1 alpha,
  BAT (allFO f (implSO (relatSO f0 f1) alpha)) = true ->
  f = f1.
Proof.
  intros [x1] [x2] [x3] alpha H.
  simpl in *. rewrite <- beq_nat_refl in *.
  case_eq (beq_nat x1 x3); intros Hbeq; rewrite Hbeq in *.
    2 : discriminate.
(*   case_eq (beq_nat (S x1) x3); intros Hbeq2; rewrite Hbeq2 in *.
    2 : discriminate.  *)
(*   apply beq_nat_true. *)
  rewrite (beq_nat_true _ _ Hbeq). reflexivity.
Qed.

Lemma is_BOXATM_flag_strong_CONJ_conjSO_fwd : forall alpha1 alpha2,
is_BOXATM_flag_strong_CONJ (conjSO alpha1 alpha2) = true ->
is_BOXATM_flag_strong_CONJ (alpha1) = true /\
is_BOXATM_flag_strong_CONJ (alpha2) = true.
Proof.
  intros alpha1 alpha2 H.
  simpl in H. case_eq (is_BOXATM_flag_strong_CONJ alpha1);
    intros H1; rewrite H1 in *. 2: discriminate.
  apply conj. reflexivity. assumption.
Qed.

Lemma BAT_conjSO_fwd : forall alpha1 alpha2,
BAT (conjSO alpha1 alpha2) = true ->
BAT (alpha1) = true /\
BAT (alpha2) = true.
Proof.
  intros alpha1 alpha2 H.
  simpl in H. case_eq (BAT alpha1);
    intros H1; rewrite H1 in *. 2: discriminate.
  apply conj. reflexivity. assumption.
Qed.


Lemma BOXATM2_lP_app : forall lP1 lP2 lx1 lx2 llv1 llv2,
 length lP1 = length lx1 ->
length lP1 = length llv1 ->
length lP2 = length lx2 ->
length lP2 = length llv2 ->
~ lP1 = nil ->
~ lP2 = nil ->
forall W Iv Ip Ir,
SOturnst W Iv Ip Ir (BOXATM2_lP (lP1 ++ lP2) (lx1 ++ lx2) (llv1 ++ llv2)) <->
SOturnst W Iv Ip Ir (conjSO (BOXATM2_lP (lP1) (lx1) (llv1))
(BOXATM2_lP (lP2) (lx2) (llv2))).
Proof.
  induction lP1; intros lP2 lx1 lx2 llv1 llv2 H1 H2 H3 H4 Hnil1 Hnil2 W Iv Ip Ir.
    contradiction (Hnil1 eq_refl).

    destruct lx1. discriminate.
    destruct llv1. discriminate.
    simpl app. simpl.
      case_eq lP1. intros HlP1. rewrite HlP1 in *.
        case_eq lx1. intros Hlx1. rewrite Hlx1 in *.
          case_eq llv1. intros Hllv1; rewrite Hllv1 in *.
            simpl.
            case_eq lP2. intros HlP2. rewrite HlP2 in *.
              contradiction (Hnil2 eq_refl).
            intros P lP2' HlP2. rewrite HlP2 in *.

            case_eq lx2. intros Hlx2. rewrite Hlx2 in *.
              discriminate.

            intros x2 lx2' Hlx2.
            case_eq llv2. intros Hllv2.
              rewrite Hllv2 in *. discriminate.
            intros lv2 llv2' Hllv2. reflexivity.

          intros lv1 llv1' Hllv1. rewrite Hllv1 in *. discriminate.
          intros x1 lx1' Hlx1. rewrite Hlx1 in *. discriminate.

          intros P1 lP1' HlP1. rewrite <- HlP1.
          case_eq (app lP1 lP2); intros HH. 
            rewrite HlP1 in *. discriminate. 
          intros lP'. intros HlP.
          destruct lx1. rewrite HlP1 in *. discriminate.
          case_eq ((f0 :: lx1) ++ lx2). intros H.
            discriminate.
          intros x lx H. destruct llv1.
            rewrite HlP1 in *. discriminate.
          case_eq (app nil llv2). intros HH2.
            simpl in HH2.
            rewrite HH2 in *. destruct lP2. 2: discriminate.
            contradiction (Hnil2 eq_refl).

            intros ly lly Hy. simpl in Hy. rewrite Hy in *.
            case_eq ((l0 :: llv1) ++ ly :: lly ).
              intros HH3. discriminate.
            intros l1 l2 HH3. rewrite <- HlP. rewrite <- H.
            rewrite <- HH3.
            do 2 rewrite SOturnst_conjSO. split; intros [SOt1 SOt2].
            apply conj. apply conj. assumption.
              apply IHlP1 in SOt2. apply SOt2.
                rewrite HlP1 in *. simpl in *. inversion H1. reflexivity.
                rewrite HlP1 in *. simpl in *. inversion H2. reflexivity.
                assumption. assumption. rewrite HlP1. discriminate.
                assumption.

              apply IHlP1 in SOt2. apply SOt2.
                rewrite HlP1 in *. simpl in *. inversion H1. reflexivity.
                rewrite HlP1 in *. simpl in *. inversion H2. reflexivity.
                assumption. assumption. rewrite HlP1. discriminate.
                assumption.

            apply conj. destruct SOt1 as [SOt1 SOt3]. assumption.
              apply IHlP1. 
                rewrite HlP1 in *. simpl in *. inversion H1. reflexivity.
                rewrite HlP1 in *. simpl in *. inversion H2. reflexivity.
                assumption. assumption. rewrite HlP1. discriminate.
                assumption.
                simpl. apply conj. apply SOt1. assumption.
Qed.

Lemma lem_bxatm_lP : forall alpha,
  is_BOXATM_flag_strong_CONJ alpha = true ->
  exists lP lx llv,
    length lP = length lx /\
    length lP = length llv /\
    forall W Iv Ip Ir,
      SOturnst W Iv Ip Ir alpha <->
      SOturnst W Iv Ip Ir (BOXATM2_lP lP lx llv).
Proof.
  induction alpha; intros H; try discriminate.
    exists (cons p nil).
    exists (cons f nil).
    exists (cons nil nil). simpl.
    simpl in *. intros. apply conj. reflexivity.
    apply conj. reflexivity. intros. apply iff_refl.

    destruct alpha; try (destruct f as [n]; destruct n; discriminate).
    destruct alpha1; try (destruct f as [n]; destruct n; discriminate).
    pose proof H as H'.
    apply is_BOXATM_flag_strong__CONJ in H.
    apply lem_bxatm14 in H. destruct H as [lx [P H]].
    exists (cons P nil). exists (cons f0 nil). exists (cons (cons f lx) nil).
    simpl. rewrite (is_BOXATM_flag_strong_CONJ_allFO_eq _ _ _ _ H')  in *.
    rewrite H. apply conj. reflexivity.
    apply conj. reflexivity. intros. apply iff_refl.

    apply is_BOXATM_flag_strong_CONJ_conjSO_fwd in H.
    destruct H as [H1 H2].
    destruct (IHalpha1 H1) as [lP1 [lx1 [llv1 [Hl1a [Hl1b Ha]]]]].
    destruct (IHalpha2 H2) as [lP2 [lx2 [llv2 [Hl2a [Hl2b Hb]]]]].
    exists (app lP1 lP2). exists (app lx1 lx2). exists (app llv1 llv2).
    simpl. do 3 rewrite app_length. rewrite <- Hl1a. rewrite <- Hl1b.
    rewrite <- Hl2a. rewrite <- Hl2b. apply conj. reflexivity.
    apply conj. reflexivity.  
    case_eq lP1.
      intros HlP1. rewrite HlP1 in *. simpl in *.
      destruct lx1. destruct llv1. all : try discriminate.
      simpl.
      intros until 0. split; intros H. apply Hb. apply H.
      apply conj. apply Ha. reflexivity. apply Hb. assumption.

      intros P lP1' HlP1. rewrite <- HlP1.
      case_eq lP2. intros HlP2.
        rewrite HlP2 in *. simpl in *.
        destruct lx2. destruct llv2. all : try discriminate.
        simpl. do 3 rewrite app_nil_r.
        intros until 0. split; intros H. apply Ha. apply H.
        apply conj. apply Ha. assumption. apply Hb. reflexivity.

        intros Q lP2' HlP2. rewrite <- HlP2.

    intros until 0. split; intros H.
      apply BOXATM2_lP_app; try assumption.
        rewrite HlP1. discriminate.
        rewrite HlP2. discriminate.

      simpl in *. apply conj.
        apply Ha. apply H.
        apply Hb. apply H.

      apply BOXATM2_lP_app in H; try assumption.
      simpl in *. apply conj.
        apply Ha. apply H.
        apply Hb. apply H.
          rewrite HlP1. discriminate.
          rewrite HlP2. discriminate.
Qed.

(* --------------------------- *)
Fixpoint batm_paired (alpha : SecOrder) : bool :=
  match alpha with
  | allFO y (implSO (relatSO z1 z2) beta) =>
    match y, z1, z2 with
    | Var ym, Var zn1, Var zn2 =>
    if beq_nat ym zn2 then 
    if match (batm_comp_x1 beta) with Var xn =>
     beq_nat zn2 xn end
      then batm_paired beta
      else false else false
    end
  | conjSO beta1 beta2 => 
    if batm_paired beta1 then batm_paired beta2
    else false
  | exFO _ beta => batm_paired beta 
  | negSO beta => batm_paired beta
  | disjSO beta1 beta2 =>
    if batm_paired beta1 then batm_paired beta2
    else false
  | implSO beta1 beta2 =>
    if batm_paired beta1 then batm_paired beta2
    else false
  | allSO P beta => batm_paired beta
  | exSO P beta => batm_paired beta
  | _ => true
  end.

Fixpoint batm_paired_old (alpha : SecOrder) : bool :=
  match alpha with
  | allFO y (implSO (relatSO z1 z2) beta) =>
    match y, z1, z2 with
    | Var ym, Var zn1, Var zn2 =>
    if beq_nat ym zn2 then 
    if match (batm_comp_x1 beta) with Var xn =>
     beq_nat zn2 xn end
      then batm_paired_old beta
      else false else false
    end
  | conjSO beta1 beta2 => 
    if batm_paired_old beta1 then batm_paired_old beta2
    else false
  | _ => true
  end.


Definition same_struc_BAT (alpha beta : SecOrder) : bool :=
  if batm_paired alpha then 
    if batm_paired beta then
      same_struc alpha beta else false else false.

Definition same_struc_BAT2 (alpha beta : SecOrder) : bool :=
    andb (same_struc alpha beta)
    (andb (if batm_paired alpha then batm_paired beta else true)
         (if batm_paired beta then batm_paired alpha else true)).

Lemma same_struc__BAT : forall alpha beta,
  same_struc_BAT alpha beta = true ->
  same_struc alpha beta = true.
Proof.
  intros alpha beta H.
  unfold same_struc_BAT in H.
  case_eq (same_struc alpha beta); intros H2.
    reflexivity. rewrite H2 in H. 
    do 2 rewrite if_then_else_false in H.
    discriminate.
Qed.

Lemma same_struc__BAT2 : forall alpha beta,
  same_struc_BAT2 alpha beta = true ->
  same_struc alpha beta = true.
Proof.
  intros alpha beta H.
  unfold same_struc_BAT2 in H.
  case_eq (same_struc alpha beta); intros H2.
    reflexivity. rewrite H2 in H.
    rewrite andb_false_l in H. discriminate.
Qed.

Lemma same_struc_BAT_batm_paired : forall alpha beta,
  same_struc_BAT alpha beta = true ->
  batm_paired alpha = true.
Proof.
  intros alpha beta H.
  unfold same_struc_BAT in H.
  case_eq (batm_paired alpha); intros H2; rewrite H2 in H.
    reflexivity.
    discriminate.
Qed.

Lemma same_struc_BAT2_batm_paired : forall alpha beta,
  same_struc_BAT2 alpha beta = true ->
  (batm_paired alpha = true <-> batm_paired beta = true).
Proof.
  intros alpha beta H.
  unfold same_struc_BAT2 in H.
  apply andb_true_iff in H.
  destruct H as [H1 H2].  
  apply andb_true_iff in H2.
  destruct H2 as [H3 H4].
  case_eq (batm_paired alpha); intros H; rewrite H in *.
    split; intros. assumption. reflexivity.
    split; intros H5. discriminate. rewrite H5 in*. discriminate.
Qed. 

Lemma same_struc_BAT_batm_paired2 : forall alpha beta,
  same_struc_BAT alpha beta = true ->
  batm_paired beta = true.
Proof.
  intros alpha beta H.
  unfold same_struc_BAT in H.
  case_eq (batm_paired beta); intros H2; rewrite H2 in H.
    reflexivity.

    rewrite if_then_else_false in H.
    discriminate.
Qed.

Lemma BAT_allFO : forall alpha y z1 z2,
(*   is_in_FOvar (Var 0) (FOvars_in (allFO y (implSO (relatSO z1 z2) alpha))) = false -> *)
  BAT (allFO y (implSO (relatSO z1 z2) alpha)) = true <->
  y = z2 /\ BOXATM_flag_weak alpha y = true.
Proof.
  intros alpha [ym] [z1] [z2].
  simpl.
  rewrite <- beq_nat_refl.
  case_eq (beq_nat ym z2); intros Hbeq.
    rewrite (beq_nat_true _ _ Hbeq).
    split; intros SOt. apply conj. reflexivity. assumption.
    apply SOt.

    split; intros SOt. discriminate.
    destruct SOt as [SOt1 SOt2].
    inversion SOt1 as [SOt1'].
    rewrite SOt1' in *. rewrite <- beq_nat_refl in Hbeq.
    discriminate.
Qed.

Lemma batm_paired_allFO : forall alpha x y1 y2,
  batm_paired (allFO x (implSO (relatSO y1 y2) alpha)) = true ->
  batm_paired alpha = true.
Proof.
  intros alpha [xn] [y1] [y2] H.
  simpl in H. case_eq (beq_nat xn y2);
    intros Hbeq; rewrite Hbeq in H.
    case_eq (batm_comp_x1 alpha); intros zn Hzn.
      rewrite Hzn in H.
      2 : discriminate.
    case_eq (beq_nat y2 zn); intros Hbeq2; 
      rewrite Hbeq2 in *. 2 : discriminate.
    assumption.
Qed. 

Lemma same_struc_BAT_defn : forall alpha beta,
  same_struc_BAT alpha beta = true <->
  same_struc alpha beta = true /\
  batm_paired alpha = true /\
  batm_paired beta = true.
Proof.
  intros alpha beta.
  unfold same_struc_BAT.
  split; intros SOt.
    case_eq (batm_paired alpha);
      intros H; rewrite H in *. 2 : discriminate.

    case_eq (batm_paired beta); intros H2; rewrite H2 in *.
      2 : discriminate.
    apply conj. assumption.
    apply conj; reflexivity.

    destruct SOt as [SOt1 [SOt2 SOt3]].
    rewrite SOt1. rewrite SOt2. rewrite SOt3.
    reflexivity.
Qed.

Lemma same_struc_BAT2_defn : forall alpha beta,
  same_struc_BAT2 alpha beta = true <->
  (same_struc alpha beta = true /\
  (batm_paired alpha = true <-> batm_paired beta = true)).
Proof.
  intros alpha beta.
  unfold same_struc_BAT2.
  split; intros SOt.
    apply andb_true_iff in SOt.
    destruct SOt as [SOt1 SOt2].
    apply conj. assumption.
    apply andb_true_iff in SOt2.
    destruct SOt2 as [SOt3 SOt4].
    case_eq (batm_paired alpha ); intros H;
      rewrite H in *. split; intros. assumption. reflexivity.
    case_eq (batm_paired beta ); intros H2;
      rewrite H2 in *. discriminate.
      split; intros; discriminate.

    apply andb_true_iff.
    destruct SOt as [SOt1 SOt2].
    apply conj. assumption.
    apply andb_true_iff.
    destruct SOt2 as [SOt3 SOt4].
    case_eq (batm_paired alpha ); intros H;
      rewrite H in *. split; intros. apply SOt3. reflexivity.

      rewrite SOt3; reflexivity.

    apply conj. reflexivity.
    case_eq (batm_paired beta ); intros H2;
      rewrite H2 in *. apply SOt4. reflexivity.

      reflexivity.
Qed.

Lemma BOXATM_flag_weak_allFO : forall alpha x y1 y2 z,
  BOXATM_flag_weak (allFO x (implSO (relatSO y1 y2) alpha)) z = true ->
  BOXATM_flag_weak alpha x = true.
Proof.
  intros alpha [xn] [y1] [y2] [zn] H.
  simpl in H.
  case_eq (BOXATM_flag_weak alpha (Var xn)); intros H2;
    rewrite H2 in *. reflexivity.
  do 2 rewrite if_then_else_false in H.
  discriminate.
Qed.

(* Left it here 28/11/17. Check the definition for same_struc_BAT 
and try and keep going *)

Lemma same_struc_BAT2_pre_num_conn : forall m n alpha beta,
  n = num_conn alpha ->
  Nat.leb n m = true ->
(*   is_in_FOvar (Var 0) (FOvars_in beta) = false -> *)
  same_struc_BAT alpha beta = true ->
  BOXATM_flag_weak alpha (batm_comp_x1 alpha) = true ->
  BOXATM_flag_weak beta (batm_comp_x1 beta) = true.
Proof.
  induction m; intros n alpha beta Hnum Hleb Hss Hb;
    pose proof (same_struc__BAT alpha beta Hss) as Hss2;
    pose proof (same_struc_BAT_batm_paired alpha beta Hss) as Hss3;
    pose proof (same_struc_BAT_batm_paired2 alpha beta Hss) as Hss4.

    destruct n. 2 : discriminate.
    destruct alpha; try discriminate.
      simpl in *. destruct f as [xn]. 
      destruct beta; try discriminate.
        simpl in *. destruct f. symmetry. apply beq_nat_refl.

    destruct n.
    destruct alpha; try discriminate.
      simpl in *. destruct f as [xn]. 
      destruct beta; try discriminate.
        simpl in *. destruct f. symmetry. apply beq_nat_refl.

    destruct alpha; try discriminate.
    destruct alpha; try discriminate.
    destruct alpha1; try discriminate.
    destruct beta; try discriminate.
    destruct beta; try discriminate.
    destruct beta1; try discriminate.
    simpl.
    destruct f3 as [z1]. destruct f2 as [z2]. destruct f4 as [z3].
    rewrite <- beq_nat_refl. case_eq (beq_nat z2 z3);
      intros Hbeq. simpl in Hss4. 
      rewrite Hbeq in Hss4. case_eq (batm_comp_x1 beta2);
        intros xn Hxn. rewrite Hxn in Hss4.
      case_eq (beq_nat z3 xn); intros Hbeq2; rewrite Hbeq2 in Hss4.   
        2 : discriminate.
      rewrite (beq_nat_true _ _ Hbeq).
      rewrite (beq_nat_true _ _ Hbeq2).
      rewrite <- Hxn.
      apply (IHm (num_conn alpha2) alpha2).
reflexivity.

    inversion Hnum as [Hnum'].
    rewrite Hnum' in Hleb.
    destruct m. discriminate. apply leb_suc_r. assumption.

simpl in Hss2.
apply same_struc_BAT_defn. apply conj. assumption.
apply conj. 
apply batm_paired_allFO in Hss3.
 assumption.
assumption.

apply BOXATM_flag_weak_allFO in Hb.
rewrite (try3_BAT _ _ Hb). assumption.

 simpl in Hss4. rewrite Hbeq in *. discriminate.
Qed.

Lemma BOXATM_flag_weak_batm_paired_num_conn : forall m n alpha x,
  n = num_conn alpha ->
  Nat.leb n m = true ->
  BOXATM_flag_weak alpha x = true ->
  batm_paired alpha = true.
Proof.
  induction m; intros n alpha [xn] Hnum Hleb H; try discriminate.
    destruct n. 2 : discriminate. destruct alpha; try discriminate.
    reflexivity.

    destruct n. destruct alpha; try discriminate.
    reflexivity.

    destruct alpha; try discriminate.
    destruct alpha; try discriminate.
    destruct alpha1; try discriminate.
    destruct f as [y1]; destruct f0 as [z1]; destruct f1 as [z2].
    simpl in *. case_eq (beq_nat y1 z2); intros Hbeq; rewrite Hbeq in *.
    case_eq (beq_nat xn z1); intros Hbeq2; rewrite Hbeq2 in *.
     2 : discriminate.
    case_eq (batm_comp_x1 alpha2); intros zn Hzn.
    pose proof H as H'.
    apply try3_BAT in H.
    rewrite H in *. inversion Hzn as [Hzn'].
    rewrite Hzn' in *. rewrite beq_nat_comm. rewrite Hbeq.
    apply (IHm (num_conn alpha2) alpha2 (Var zn) eq_refl).

    inversion Hnum as [Hnum'].
    rewrite Hnum' in Hleb.
    destruct m. discriminate. apply leb_suc_r. assumption.

    assumption.

    rewrite if_then_else_false in H. discriminate.
Qed.

Lemma BOXATM_flag_weak_batm_paired : forall alpha x,
  BOXATM_flag_weak alpha x = true ->
  batm_paired alpha = true.
Proof.
  intros alpha x. 
  apply (BOXATM_flag_weak_batm_paired_num_conn (num_conn alpha) (num_conn alpha) _ _ eq_refl).
  apply leb_refl.
Qed.

Lemma BAT_BOXATM_flag_weak_allFO : forall alpha x,
  BAT (allFO x alpha) = BOXATM_flag_weak (allFO x alpha) (batm_comp_x1 (allFO x alpha)).
Proof.
  intros alpha [xn].
  simpl. destruct alpha; try reflexivity.
Qed.

Lemma BAT_paired_num_conn : forall m n alpha,
  n = num_conn alpha ->
  Nat.leb n m = true ->
  BAT alpha = true ->
  batm_paired alpha = true.
Proof.
  induction m; intros n alpha Hnum Hleb H; try discriminate.
    destruct n. 2 : discriminate. destruct alpha; try discriminate.
    reflexivity.

    destruct n. destruct alpha; try discriminate.
    reflexivity.

    destruct alpha; try discriminate.
    rewrite BAT_BOXATM_flag_weak_allFO in H. 
    apply (BOXATM_flag_weak_batm_paired (allFO f alpha) (batm_comp_x1 (allFO f alpha))).
    assumption.

    simpl. apply BAT_conjSO_fwd in H.
    destruct H as [H1 H2].
    rewrite (IHm (num_conn alpha1) alpha1 eq_refl).
    apply (IHm (num_conn alpha2) alpha2 eq_refl).
    all : try assumption.

        rewrite Hnum in Hleb. simpl in Hleb.
        apply leb_plus_take2 in Hleb. assumption.

        rewrite Hnum in Hleb. simpl in Hleb.
        apply leb_plus_take1 in Hleb. assumption.
Qed.

Lemma BAT_paired : forall alpha,
  BAT alpha = true ->
  batm_paired alpha = true.
Proof.
  intros alpha x. 
  apply (BAT_paired_num_conn (num_conn alpha) (num_conn alpha) _ eq_refl).
  apply leb_refl. assumption.
Qed.

Lemma same_struc_BAT2_2_pre_num_conn : forall m n alpha beta,
  n = num_conn alpha ->
  Nat.leb n m = true ->
(*   is_in_FOvar (Var 0) (FOvars_in beta) = false -> *)
  same_struc_BAT2 alpha beta = true ->
  BOXATM_flag_weak alpha (batm_comp_x1 alpha) = true ->
  BOXATM_flag_weak beta (batm_comp_x1 beta) = true.
Proof.
  induction m; intros n alpha beta Hnum Hleb Hss Hb;
    pose proof (same_struc__BAT2 alpha beta Hss) as Hss2;
    pose proof (same_struc_BAT2_batm_paired alpha beta Hss) as Hss3.
(*     pose proof (same_struc_BAT_batm_paired2 alpha beta Hss) as Hss4. *)

    destruct n. 2 : discriminate.
    destruct alpha; try discriminate.
      simpl in *. destruct f as [xn]. 
      destruct beta; try discriminate.
        simpl in *. destruct f. symmetry. apply beq_nat_refl.

    destruct n.
    destruct alpha; try discriminate.
      simpl in *. destruct f as [xn]. 
      destruct beta; try discriminate.
        simpl in *. destruct f. symmetry. apply beq_nat_refl.

    destruct alpha; try discriminate.
    destruct alpha; try discriminate.
    destruct alpha1; try discriminate.
    destruct beta; try discriminate.
    destruct beta; try discriminate.
    destruct beta1; try discriminate.
    simpl.
    destruct f3 as [z1]. destruct f2 as [z2]. destruct f4 as [z3].
    rewrite <- beq_nat_refl. case_eq (beq_nat z2 z3);
      intros Hbeq.
      case_eq (batm_comp_x1 beta2);
        intros xn Hxn.

        pose proof Hb as Hb'.
        apply BOXATM_flag_weak_batm_paired in Hb.
        apply Hss3 in Hb.
        simpl in Hb. rewrite Hxn in *. rewrite Hbeq in *.
        case_eq (beq_nat z3 xn); intros Hbeq2; rewrite Hbeq2 in *.
          2 : discriminate.
        rewrite (beq_nat_true _  _ Hbeq) in *.
        rewrite (beq_nat_true _ _ Hbeq2) in *. rewrite <- Hxn.
        apply (IHm (num_conn alpha2) alpha2). reflexivity.


    inversion Hnum as [Hnum'].
    rewrite Hnum' in Hleb.
    destruct m. discriminate. apply leb_suc_r. assumption.

        apply same_struc_BAT2_defn. apply conj. simpl in *. assumption.
        simpl in Hss3. rewrite <- beq_nat_refl in *. rewrite Hxn in *.
        rewrite <- beq_nat_refl in *.
        case_eq (batm_comp_x1 alpha2); intros un Hun; rewrite Hun in *.
        destruct f as [y1]. destruct f0 as [y2]. destruct f1 as [y3].
        case_eq (beq_nat y1 y3); intros Hbeq3; rewrite Hbeq3 in *.
          case_eq (beq_nat y3 un); intros Hbeq4; rewrite Hbeq4 in *.
            assumption.
          simpl in Hb'. rewrite <- beq_nat_refl in Hb'.
          rewrite Hbeq3 in Hb'. apply try3_BAT in Hb'.
          rewrite Hb' in *. inversion Hun as [Hun'].
          rewrite Hun' in *. rewrite beq_nat_comm in Hbeq4.
          rewrite Hbeq4 in *. discriminate.

          simpl in Hb'. rewrite Hbeq3 in *. rewrite <- beq_nat_refl in *.
          discriminate.

        apply BOXATM_flag_weak_allFO in Hb'.
        pose proof Hb' as Hb''.
        apply try3_BAT in Hb'. 
        rewrite Hb' in *. assumption.

      apply BOXATM_flag_weak_batm_paired in Hb. 
      destruct Hss3 as [Hss3 Hss5].
      specialize (Hss3 Hb). simpl in *.
      rewrite Hbeq in *. discriminate.
Qed.

Lemma same_struc_BAT2_pre : forall alpha beta,
(*   is_in_FOvar (Var 0) (FOvars_in beta) = false -> *)
  same_struc_BAT alpha beta = true ->
  BOXATM_flag_weak alpha (batm_comp_x1 alpha) = true ->
  BOXATM_flag_weak beta (batm_comp_x1 beta) = true.
Proof.
  intros alpha beta.
  apply (same_struc_BAT2_pre_num_conn (num_conn alpha) (num_conn alpha) _ _ eq_refl (leb_refl _)).
Qed.

Lemma same_struc_BAT2_2_pre : forall alpha beta,
(*   is_in_FOvar (Var 0) (FOvars_in beta) = false -> *)
  same_struc_BAT2 alpha beta = true ->
  BOXATM_flag_weak alpha (batm_comp_x1 alpha) = true ->
  BOXATM_flag_weak beta (batm_comp_x1 beta) = true.
Proof.
  intros alpha beta.
  apply (same_struc_BAT2_2_pre_num_conn (num_conn alpha) (num_conn alpha) _ _ eq_refl (leb_refl _)).
Qed.

Lemma  BAT_conjSO_t : forall beta1 beta2,
BAT (conjSO beta1 beta2) = true <->
BAT beta1 = true /\ BAT beta2 = true.
Proof.
  intros.
  simpl.
  split; intros H.    
    case_eq (BAT beta1 ); intros H2; rewrite H2 in *.
      apply conj. reflexivity. assumption.

      discriminate.

    destruct H as [H1 H2].
    rewrite H1. rewrite H2. reflexivity.
Qed.

Lemma same_struc_BAT2_2_num_conn : forall m n alpha beta,
  n = num_conn alpha ->
  Nat.leb n m = true ->
(*   is_in_FOvar (Var 0) (FOvars_in beta) = false -> *)
  same_struc_BAT2 alpha beta = true ->
  BAT alpha = true ->
  BAT beta = true.
Proof.
  induction m; intros n alpha beta Hnum Hleb (* Hin *) Hss Hb;
    pose proof (same_struc__BAT2 alpha beta Hss) as Hss2;
    pose proof (same_struc_BAT2_batm_paired alpha beta Hss) as Hss3.

    destruct n. 2 : discriminate.
    destruct alpha; try discriminate.
    destruct beta; try discriminate.

    reflexivity.

    destruct n. 
    simpl in *.
    destruct alpha; try discriminate.
    destruct beta; try discriminate.

    reflexivity.

    destruct alpha; try discriminate. destruct beta; try discriminate.
(*     destruct f as [xn]. destruct xn. discriminate. *)
    destruct alpha; try discriminate.
    destruct alpha1; try discriminate.
    destruct beta; try discriminate.
    destruct beta1;  try discriminate.

    rewrite BAT_BOXATM_flag_weak_allFO.
    rewrite BAT_BOXATM_flag_weak_allFO in Hb.
    simpl in Hss2.
    apply (same_struc_BAT2_2_pre (allFO f (implSO (relatSO f1 f2) alpha2)));
      assumption.

    destruct beta; try discriminate.

(*     apply batm_paired_conjSO_t in Hss3.
    apply batm_paired_conjSO_t in Hss4. *)
    apply same_struc_conjSO in Hss2.
    apply BAT_conjSO_t in Hb.
    apply BAT_conjSO_t.
    destruct Hb as [H0 H1]. destruct Hss2 as [H2 H3]. (*  destruct Hss3. destruct Hss4. *)
    apply conj.
      apply (IHm (num_conn alpha1) alpha1 beta1); try assumption.
      reflexivity.

        rewrite Hnum in Hleb. simpl in Hleb.
        apply leb_plus_take1 in Hleb. assumption.

      apply same_struc_BAT2_defn. apply conj. assumption.
      apply BAT_paired in H0.
      apply BAT_paired in H1.
      simpl in Hss3. rewrite H0 in *. rewrite H1 in *.
      case_eq  (batm_paired beta1 ); intros HH.
        split; reflexivity.
      rewrite HH in *. assumption.

      apply (IHm (num_conn alpha2) alpha2 beta2); try assumption.
      reflexivity.

        rewrite Hnum in Hleb. simpl in Hleb.
        apply leb_plus_take2 in Hleb. assumption.

      apply same_struc_BAT2_defn. apply conj. assumption.
      apply BAT_paired in H0.
      apply BAT_paired in H1.
      simpl in Hss3. rewrite H0 in *. rewrite H1 in *.
      case_eq  (batm_paired beta2 ); intros HH.
        split; reflexivity.
      rewrite HH in *. rewrite if_then_else_false in Hss3. assumption.
Qed.

Lemma same_struc_BAT2_2 : forall alpha beta,
(*   is_in_FOvar (Var 0) (FOvars_in beta) = false -> *)
  same_struc_BAT2 alpha beta = true ->
  BAT alpha = true ->
  BAT beta = true.
Proof.
  intros alpha beta.
  apply (same_struc_BAT2_2_num_conn (num_conn alpha) (num_conn alpha)
    _ _ eq_refl (leb_refl _)).
Qed.


(* --------------------------   *)

