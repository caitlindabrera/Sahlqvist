Require Export vsSahlq_preprocessing3.

(* ----------------------------------- *)

(* creates long disjunction from list FOvariables *)
Fixpoint fun1 (lv : list FOvariable) x : SecOrder :=
  match lv with
  | nil => eqFO (Var 1) (Var 1) (* filler *)
  | cons y nil => eqFO x y
  | cons y lv' => disjSO (eqFO x y) (fun1 lv' x)
  end.

Fixpoint vsS_syn_l (llv : list (list FOvariable)) x : list SecOrder :=
  match llv with
  | nil => nil
  | cons lv llv' => cons (fun1 lv x) (vsS_syn_l llv' x)
  end.

(* creates a list of FOvariables that are attached to P *)
Fixpoint fun2 alpha P : list FOvariable :=
  match alpha with
    predSO Q x => match P, Q with Pred Pn, Pred Qm =>
      if beq_nat Pn Qm then cons x nil else nil end
  | relatSO _ _ => nil
  | eqFO _ _ => nil
  | allFO _ beta => fun2 beta P
  | exFO _ beta => fun2 beta P
  | negSO beta => fun2 beta P
  | conjSO beta1 beta2 => app (fun2 beta1 P) (fun2 beta2 P)
  | disjSO beta1 beta2 => app (fun2 beta1 P) (fun2 beta2 P)
  | implSO beta1 beta2 => app (fun2 beta1 P) (fun2 beta2 P)
  | allSO _ beta => fun2 beta P
  | exSO _ beta => fun2 beta P
  end.

Fixpoint FOv_att_P_l alpha lP : list (list FOvariable) :=
  match lP with
  | nil => nil
  | cons P lP' => cons (fun2 alpha P) (FOv_att_P_l alpha lP')
  end.

Fixpoint nlist_Var (n : nat) (x : FOvariable) : nlist n :=
  match n with
  | 0 => niln
  | S m => consn _ x (nlist_Var m x)
  end.

Fixpoint list_Var (n : nat) (x : FOvariable) : list FOvariable :=
  match n with
  | 0 => nil
  | S m => cons x (list_Var m x)
  end.

Fixpoint SOQFree_P alpha P : bool :=
  match P with Pred Pn =>
  match alpha with
    predSO _ _ => true 
  | relatSO _ _ => true
  | eqFO _ _ => true 
  | allFO _ beta => SOQFree_P beta P
  | exFO _ beta => SOQFree_P beta P
  | negSO beta => SOQFree_P beta P
  | conjSO beta1 beta2 => if SOQFree_P beta1 P then SOQFree_P beta2 P
      else false
  | disjSO beta1 beta2 => if SOQFree_P beta1 P then SOQFree_P beta2 P
      else false
  | implSO beta1 beta2 => if SOQFree_P beta1 P then SOQFree_P beta2 P
      else false
  | allSO (Pred Qm) beta => if beq_nat Pn Qm then false else
      SOQFree_P beta P
  | exSO (Pred Qm) beta => if beq_nat Pn Qm then false else
      SOQFree_P beta P
  end end.


Lemma SOQFree_P_conjSO_l : forall (alpha1 alpha2 : SecOrder) P,
  SOQFree_P (conjSO alpha1 alpha2) P = true -> (SOQFree_P alpha1 P = true).
Proof.
  intros alpha1 alpha2 [Pn] H.
  simpl in H.
  case_eq (SOQFree_P alpha1 (Pred Pn)); intros H2; rewrite H2 in *;
    [reflexivity | discriminate].
Qed.

Lemma SOQFree_P_conjSO_r : forall (alpha1 alpha2 : SecOrder) P,
  SOQFree_P (conjSO alpha1 alpha2) P = true -> (SOQFree_P alpha2 P = true).
Proof.
  intros alpha1 alpha2 [Pn] H.
  simpl in H.
  case_eq (SOQFree_P alpha1 (Pred Pn)); intros H2; rewrite H2 in *;
    [case_eq (SOQFree_P alpha2 (Pred Pn)); intros H3;
      [reflexivity | rewrite H3 in *]; 
      discriminate | discriminate].
Qed.

Fixpoint no_FOquant (alpha : SecOrder) : bool :=
  match alpha with
    predSO _ _ => true
  | relatSO _ _  =>  true
  | eqFO _ _ => true
  | allFO _ beta => false
  | exFO _ beta => false
  | negSO beta => no_FOquant beta
  | conjSO beta1 beta2 => if no_FOquant beta1 then no_FOquant beta2 else false
  | disjSO beta1 beta2 => if no_FOquant beta1 then no_FOquant beta2 else false
  | implSO beta1 beta2 => if no_FOquant beta1 then no_FOquant beta2 else false
  | allSO _ beta => no_FOquant beta 
  | exSO _ beta => no_FOquant beta
  end.

Lemma no_FOquant_conjSO_l : forall (alpha1 alpha2 : SecOrder),
  no_FOquant (conjSO alpha1 alpha2) = true -> (no_FOquant alpha1 = true).
Proof.
  intros alpha1 alpha2 H.
  simpl in H.
  case_eq (no_FOquant alpha1); intros H2; rewrite H2 in *;
    [reflexivity | discriminate].
Qed.

Lemma no_FOquant_conjSO_r : forall (alpha1 alpha2 : SecOrder),
  no_FOquant (conjSO alpha1 alpha2) = true -> (no_FOquant alpha2 = true).
Proof.
  intros alpha1 alpha2 H.
  simpl in H.
  case_eq (no_FOquant alpha1); intros H2; rewrite H2 in *;
    [case_eq (no_FOquant alpha2); intros H3;
      [reflexivity | rewrite H3 in *]; 
      discriminate | discriminate].
Qed.

Definition CM_pa2 {W : Set} (Iv : FOvariable -> W) (y : FOvariable) (w : W) :=
  w = Iv y.

Lemma FOvar_neq : forall xn ym,
  ~ (Var xn) = (Var ym) -> beq_nat xn ym = false.
Proof.
  intros xn ym H.
  case_eq (beq_nat xn ym); intros Hbeq.
    rewrite (beq_nat_true _ _ Hbeq) in H.
    contradiction (H eq_refl).

    reflexivity.
Qed.

Fixpoint attached_allFO_x alpha x : bool :=
  match alpha with 
    predSO _ _ => false
  | relatSO _ _ => false
  | eqFO _ _ => false
  | allFO y beta => match x, y with Var xn, Var ym =>
      if beq_nat xn ym then true else attached_allFO_x beta x end
  | exFO _ beta => attached_allFO_x beta x
  | negSO beta => attached_allFO_x beta x
  | conjSO beta1 beta2 =>
      if attached_allFO_x beta1 x then true else
         attached_allFO_x beta2 x
  | disjSO beta1 beta2 =>
      if attached_allFO_x beta1 x then true else
         attached_allFO_x beta2 x
  | implSO beta1 beta2 =>
      if attached_allFO_x beta1 x then true else
         attached_allFO_x beta2 x
  | allSO _ beta => attached_allFO_x beta x
  | exSO _ beta => attached_allFO_x beta x
  end.

Fixpoint ex_attached_allFO_lv alpha lv : bool :=
  match lv with
  | nil => false
  | cons y lv' => if attached_allFO_x alpha y then true else 
      ex_attached_allFO_lv alpha lv'
  end.

Lemma attached_allFO_x_conjSO_l : forall alpha1 alpha2 x,
  attached_allFO_x (conjSO alpha1 alpha2) x = false ->
  attached_allFO_x alpha1 x = false.
Proof.
  intros until 0; intros H. simpl in H.
  case_eq (attached_allFO_x alpha1 x); intros H2;
    rewrite H2 in *. discriminate.
    reflexivity.
Qed.

Lemma attached_allFO_x_conjSO_r : forall alpha1 alpha2 x,
  attached_allFO_x (conjSO alpha1 alpha2) x = false ->
  attached_allFO_x alpha2 x = false.
Proof.
  intros until 0; intros H. simpl in H.
  case_eq (attached_allFO_x alpha2 x); intros H2;
    rewrite H2 in *. rewrite if_then_else_true in *. discriminate.
    reflexivity.
Qed.

Fixpoint attached_exFO_x alpha x : bool :=
  match alpha with 
    predSO _ _ => false
  | relatSO _ _ => false
  | eqFO _ _ => false
  | exFO y beta => match x, y with Var xn, Var ym =>
      if beq_nat xn ym then true else attached_exFO_x beta x end
  | allFO _ beta => attached_exFO_x beta x
  | negSO beta => attached_exFO_x beta x
  | conjSO beta1 beta2 =>
      if attached_exFO_x beta1 x then true else
         attached_exFO_x beta2 x
  | disjSO beta1 beta2 =>
      if attached_exFO_x beta1 x then true else
         attached_exFO_x beta2 x
  | implSO beta1 beta2 =>
      if attached_exFO_x beta1 x then true else
         attached_exFO_x beta2 x
  | allSO _ beta => attached_exFO_x beta x
  | exSO _ beta => attached_exFO_x beta x
  end.

Fixpoint ex_attached_exFO_lv alpha lv : bool :=
  match lv with
  | nil => false
  | cons y lv' => if attached_exFO_x alpha y then true else 
      ex_attached_exFO_lv alpha lv'
  end.

Lemma attached_exFO_x_conjSO_l : forall alpha1 alpha2 x,
  attached_exFO_x (conjSO alpha1 alpha2) x = false ->
  attached_exFO_x alpha1 x = false.
Proof.
  intros until 0; intros H. simpl in H.
  case_eq (attached_exFO_x alpha1 x); intros H2;
    rewrite H2 in *. discriminate.
    reflexivity.
Qed.

Lemma attached_exFO_x_conjSO_r : forall alpha1 alpha2 x,
  attached_exFO_x (conjSO alpha1 alpha2) x = false ->
  attached_exFO_x alpha2 x = false.
Proof.
  intros until 0; intros H. simpl in H.
  case_eq (attached_exFO_x alpha2 x); intros H2;
    rewrite H2 in *. rewrite if_then_else_true in *. discriminate.
    reflexivity.
Qed.

(* ---------------------------------------------------------- *)

Lemma attached_allFO_x_conjSO_f : forall alpha1 alpha2 x,
  attached_allFO_x alpha1 x = false ->
  attached_allFO_x alpha2 x = false ->
  attached_allFO_x (conjSO alpha1 alpha2) x = false.
Proof.
  intros alpha1 alpha2 x H1 H2.
  simpl. rewrite H1. assumption.
Qed.


Lemma attached_exFO_x_conjSO_f : forall alpha1 alpha2 x,
  attached_exFO_x alpha1 x = false ->
  attached_exFO_x alpha2 x = false ->
  attached_exFO_x (conjSO alpha1 alpha2) x = false.
Proof.
  intros alpha1 alpha2 x H1 H2.
  simpl. rewrite H1. assumption.
Qed.

Fixpoint x_occ_in_alpha alpha x : bool :=
  match alpha with
    predSO _ y => match x,y with Var xn, Var ym =>
      beq_nat xn ym end
  | relatSO y1 y2 => match x, y1, y2 with Var xn, Var y1', Var y2' =>
      if beq_nat xn y1' then true else beq_nat xn y2' end
  | eqFO y1 y2 => match x, y1, y2 with Var xn, Var y1', Var y2' =>
      if beq_nat xn y1' then true else beq_nat xn y2' end 
  | allFO y beta => match x,y with Var xn, Var ym =>
      if beq_nat xn ym then true else x_occ_in_alpha beta x
      end
  | exFO y beta => match x,y with Var xn, Var ym =>
      if beq_nat xn ym then true else x_occ_in_alpha beta x
      end  
  | negSO beta => x_occ_in_alpha beta x
  | conjSO beta1 beta2 => if x_occ_in_alpha beta1 x then true
      else x_occ_in_alpha beta2 x
  | disjSO beta1 beta2 => if x_occ_in_alpha beta1 x then true
      else x_occ_in_alpha beta2 x
  | implSO beta1 beta2 => if x_occ_in_alpha beta1 x then true
      else x_occ_in_alpha beta2 x
  | allSO _ beta => x_occ_in_alpha beta x
  | exSO _ beta => x_occ_in_alpha beta x
  end.

Lemma x_occ_in_alpha_max_FOv_gen : forall beta n,
  Nat.leb (max_FOv beta) n = true ->
  x_occ_in_alpha beta (Var (S n)) = false.
Proof.
  induction beta.
    destruct f as [xn]. destruct p as [Qm].
    induction xn; intros n Hleb;
      simpl in *.
      reflexivity.

      destruct n. discriminate.
      destruct xn. reflexivity.
      simpl. apply IHxn.
      assumption.

    intros n Hleb.
    destruct f as [y1]; destruct f0 as [y2].
    simpl in *.
    destruct y1.
      destruct y2.
        reflexivity.

        simpl in *. destruct n.
        discriminate.
        case_eq (beq_nat (S n) y2); intros Hbeq2.
          rewrite <- (beq_nat_true _ _ Hbeq2) in Hleb.
          rewrite leb_suc_f in Hleb.
          discriminate.

          reflexivity.

      case_eq (beq_nat n y1); intros Hbeq.
        rewrite (beq_nat_true _ _  Hbeq) in Hleb.
        rewrite PeanoNat.Nat.max_comm in Hleb.
        rewrite leb_max_suc in Hleb.
        discriminate.

        destruct y2.
          reflexivity.
        case_eq (beq_nat n y2); intros Hbeq2.
          rewrite (beq_nat_true _ _ Hbeq2) in Hleb.
          rewrite leb_max_suc in Hleb.
          discriminate.

          reflexivity.

    intros n Hleb.
    destruct f as [y1]; destruct f0 as [y2].
    simpl in *.
    destruct y1.
      destruct y2.
        reflexivity.

        simpl in *. destruct n.
        discriminate.
        case_eq (beq_nat (S n) y2); intros Hbeq2.
          rewrite <- (beq_nat_true _ _ Hbeq2) in Hleb.
          rewrite leb_suc_f in Hleb.
          discriminate.

          reflexivity.

      case_eq (beq_nat n y1); intros Hbeq.
        rewrite (beq_nat_true _ _  Hbeq) in Hleb.
        rewrite PeanoNat.Nat.max_comm in Hleb.
        rewrite leb_max_suc in Hleb.
        discriminate.

        destruct y2.
          reflexivity.
        case_eq (beq_nat n y2); intros Hbeq2.
          rewrite (beq_nat_true _ _ Hbeq2) in Hleb.
          rewrite leb_max_suc in Hleb.
          discriminate.

          reflexivity.

    destruct f as [xn]. simpl.
    intros n Hleb.
    destruct xn.
      apply IHbeta.
      apply Hleb.

      case_eq (beq_nat n xn); intros Hbeq.
        rewrite (beq_nat_true _ _ Hbeq) in *.
        rewrite PeanoNat.Nat.max_comm in Hleb.
        rewrite leb_max_suc in Hleb.
        discriminate.

        apply IHbeta.
        apply leb_max in Hleb.
        apply Hleb.

    destruct f as [xn]. simpl.
    intros n Hleb.
    destruct xn.
      apply IHbeta.
      apply Hleb.

      case_eq (beq_nat n xn); intros Hbeq.
        rewrite (beq_nat_true _ _ Hbeq) in *.
        rewrite PeanoNat.Nat.max_comm in Hleb.
        rewrite leb_max_suc in Hleb.
        discriminate.

        apply IHbeta.
        apply leb_max in Hleb.
        apply Hleb.

    simpl. assumption.

    simpl. intros n Hleb.
    apply leb_max in Hleb.
    rewrite IHbeta1. apply IHbeta2.
    all : try apply Hleb.

    simpl. intros n Hleb.
    apply leb_max in Hleb.
    rewrite IHbeta1. apply IHbeta2.
    all : try apply Hleb.

    simpl. intros n Hleb.
    apply leb_max in Hleb.
    rewrite IHbeta1. apply IHbeta2.
    all : try apply Hleb.

    all : assumption.
Qed.

Lemma max_or : forall a b,
  max a b = a \/ max a b = b.
Proof.
  induction a; intros b.
    simpl. right. reflexivity.

    simpl. destruct b.
      left. reflexivity.

      destruct (IHa b) as [H | H];
      rewrite H; [left | right];
      reflexivity.
Qed.

Lemma leb_max_max : forall a b c,
  Nat.leb a b = true ->
  Nat.leb(max a c) (max b c) = true.
Proof.
  induction a; intros b c H.
    simpl.
    destruct (max_or b c) as [H1 | H1];
      rewrite H1.
      apply max_leb_r in H1. assumption.

      apply leb_refl.

    simpl. destruct c.
      simpl. destruct b.
        simpl in H. discriminate.

        simpl in *. assumption.

      destruct b. simpl in *. discriminate.
        simpl. apply IHa. apply H.
Qed.

Lemma leb_max_max_gen : forall a b c d,
  Nat.leb a b = true ->
  Nat.leb c d = true ->
  Nat.leb(max a c) (max b d) = true.
Proof.
  induction a; intros b c d Hleb1 Hleb2.
    simpl. destruct (max_or b d) as [H | H];
      rewrite H.
      apply max_leb_r in H.
      apply leb_trans with (j := d).
      all : try assumption.

    simpl. destruct c.
      destruct b. simpl in *. discriminate.

      simpl in *. destruct d.
        assumption.

        destruct (max_or b d) as [H | H];
        rewrite H. assumption.  
          apply max_leb_l in H.
          apply leb_trans with (j := b);
          assumption.

      simpl. destruct b.
        simpl in *. discriminate.

        destruct d. simpl in *. discriminate.

        simpl. apply IHa; assumption.
Qed.

Fixpoint is_in_var (x : FOvariable) (lv : list FOvariable) : bool :=
  match lv with
  | nil => false
  | cons y lv' => match x, y with Var xn, Var ym =>
      if beq_nat xn ym then true else is_in_var x lv'
      end
  end.

Fixpoint CM_pa2_l {W : Set} (Iv : FOvariable -> W) (lv : list FOvariable) (w : W) :=
  match lv with
  | nil => w = w
  | cons y nil => w = Iv y
  | cons y lv' => (w = Iv y) \/ (CM_pa2_l Iv lv' w)
  end.

Lemma CM_pa2_l_base : forall lv xn zn W Iv Ip Ir,
  is_in_var (Var xn) lv = false ->
  CM_pa2_l Iv lv (Iv (Var zn)) <-> 
  SOturnst W Iv Ip Ir (replace_FOv (fun1 lv (Var xn)) (Var xn) (Var zn)).
Proof.
  induction lv; intros xn zn W Iv Ip Ir Hin.
    simpl. case_eq (beq_nat xn 1); intros Hbeq;
      simpl; apply bi_refl.
      split; intros; reflexivity.

    destruct a as [ym].
    simpl in Hin. case_eq (beq_nat xn ym); intros Hbeq;
      rewrite Hbeq in *. discriminate.
    destruct lv. simpl in *.
      rewrite <- beq_nat_refl.
      simpl. rewrite Hbeq. apply bi_refl.

      simpl. rewrite <- beq_nat_refl.
      split; intros [SOt | SOt].
        simpl in Hin. rewrite Hbeq.
        left. simpl. assumption.

        right. apply IHlv; assumption.

        left. rewrite Hbeq in SOt. apply SOt.

        right. apply IHlv in SOt. apply SOt.
        assumption.
Qed.

Lemma ex_attached_allFO_lv_allFO : forall lv alpha x,
  ex_attached_allFO_lv (allFO x alpha) lv = false ->
    ex_attached_allFO_lv alpha lv = false /\
    is_in_var x lv = false.
Proof.
  induction lv; intros alpha x H.
    simpl in *. apply conj; reflexivity.

    simpl in *. destruct a as [ym]; destruct x as [xn].
    rewrite beq_nat_comm in H.
    case_eq (beq_nat xn ym); intros Hbeq; rewrite Hbeq in H.
      discriminate.
    case_eq (attached_allFO_x alpha (Var ym)); intros Hat;
      rewrite Hat in *. discriminate.
    destruct (IHlv _ _ H) as [H1 H2].
    apply conj; assumption.
Qed.

Lemma ex_attached_exFO_lv_allFO : forall lv alpha x,
  ex_attached_exFO_lv (allFO x alpha) lv = false ->
    ex_attached_exFO_lv alpha lv = false.
Proof.
  induction lv; intros alpha x H.
     reflexivity.

    simpl in *. destruct a as [ym]; destruct x as [xn].
    case_eq (attached_exFO_x alpha (Var ym)); intros H2;
      rewrite H2 in *. discriminate.
    apply IHlv with (x := (Var xn)). assumption.
Qed.

Lemma ex_attached_exFO_lv_exFO : forall lv alpha x,
  ex_attached_exFO_lv (exFO x alpha) lv = false ->
    ex_attached_exFO_lv alpha lv = false /\
    is_in_var x lv = false.
Proof.
  induction lv; intros alpha x H.
    simpl in *. apply conj; reflexivity.

    simpl in *. destruct a as [ym]; destruct x as [xn].
    rewrite beq_nat_comm in H.
    case_eq (beq_nat xn ym); intros Hbeq; rewrite Hbeq in H.
      discriminate.
    case_eq (attached_exFO_x alpha (Var ym)); intros Hat;
      rewrite Hat in *. discriminate.
    destruct (IHlv _ _ H) as [H1 H2].
    apply conj; assumption.
Qed.

Lemma ex_attached_allFO_lv_exFO : forall lv alpha x,
  ex_attached_allFO_lv (exFO x alpha) lv = false ->
    ex_attached_allFO_lv alpha lv = false.
Proof.
  induction lv; intros alpha x H.
     reflexivity.

    simpl in *. destruct a as [ym]; destruct x as [xn].
    case_eq (attached_allFO_x alpha (Var ym)); intros H2;
      rewrite H2 in *. discriminate.
    apply IHlv with (x := (Var xn)). assumption.
Qed.


Lemma try : forall lv x (W : Set) Iv (d : W),
  is_in_var x lv = false ->
  CM_pa2_l Iv lv = CM_pa2_l (altered_Iv Iv d x) lv.
Proof.
  induction lv; intros x W Iv d Hin.
    simpl in *. reflexivity.

    apply functional_extensionality. intros w.
    simpl.
    destruct lv.
      simpl in *.
      destruct x as [xn]; destruct a as [ym].
      simpl. case_eq (beq_nat xn ym); intros Hbeq;
        rewrite Hbeq in *. discriminate.
        reflexivity.

        rewrite <- (IHlv x W Iv d).
        destruct x as [xn]; destruct a as [ym].
        simpl in *. case_eq (beq_nat xn ym); intros Hbeq;
        rewrite Hbeq in *. discriminate.
        reflexivity.

        simpl in Hin.
        destruct x as [xn]; destruct a as [ym].
        simpl in *. case_eq (beq_nat xn ym); intros Hbeq;
        rewrite Hbeq in *. discriminate.
        destruct f as [zn].
        case_eq (beq_nat xn zn); intros Hbeq2; rewrite Hbeq2 in *;
          assumption.
Qed.

Lemma ex_att_allFO_lv_negSO : forall lv alpha,
  ex_attached_allFO_lv (negSO alpha) lv =
  ex_attached_allFO_lv alpha lv.
Proof.
  induction lv; intros alpha.
    reflexivity.

    simpl. rewrite IHlv.
    reflexivity.
Qed.

Lemma ex_att_exFO_lv_negSO : forall lv alpha,
  ex_attached_exFO_lv (negSO alpha) lv =
  ex_attached_exFO_lv alpha lv.
Proof.
  induction lv; intros alpha.
    reflexivity.

    simpl. rewrite IHlv.
    reflexivity.
Qed.

Lemma ex_att_allFO_lv_conjSO_f : forall lv alpha1 alpha2,
  ex_attached_allFO_lv (conjSO alpha1 alpha2) lv = false ->
 (ex_attached_allFO_lv alpha1 lv = false) /\
 (ex_attached_allFO_lv alpha2 lv = false).
Proof.
  induction lv; intros alpha1 alpha2 H.
    simpl in *. apply conj; reflexivity.

    simpl.
    case_eq (attached_allFO_x alpha1 a); intros H1;
      simpl in H; rewrite H1 in H. discriminate.
    case_eq (attached_allFO_x alpha2 a); intros H2;
      rewrite H2 in H. discriminate.
    apply IHlv. assumption.
Qed.

Lemma ex_att_exFO_lv_conjSO_f : forall lv alpha1 alpha2,
  ex_attached_exFO_lv (conjSO alpha1 alpha2) lv = false ->
 (ex_attached_exFO_lv alpha1 lv = false) /\
 (ex_attached_exFO_lv alpha2 lv = false).
Proof.
  induction lv; intros alpha1 alpha2 H.
    simpl in *. apply conj; reflexivity.

    simpl.
    case_eq (attached_exFO_x alpha1 a); intros H1;
      simpl in H; rewrite H1 in H. discriminate.
    case_eq (attached_exFO_x alpha2 a); intros H2;
      rewrite H2 in H. discriminate.
    apply IHlv. assumption.
Qed.

Lemma ex_att_allFO_lv_disjSO_f : forall lv alpha1 alpha2,
  ex_attached_allFO_lv (disjSO alpha1 alpha2) lv = false ->
 (ex_attached_allFO_lv alpha1 lv = false) /\
 (ex_attached_allFO_lv alpha2 lv = false).
Proof.
  induction lv; intros alpha1 alpha2 H.
    simpl in *. apply conj; reflexivity.

    simpl.
    case_eq (attached_allFO_x alpha1 a); intros H1;
      simpl in H; rewrite H1 in H. discriminate.
    case_eq (attached_allFO_x alpha2 a); intros H2;
      rewrite H2 in H. discriminate.
    apply IHlv. assumption.
Qed.

Lemma ex_att_exFO_lv_disjSO_f : forall lv alpha1 alpha2,
  ex_attached_exFO_lv (disjSO alpha1 alpha2) lv = false ->
 (ex_attached_exFO_lv alpha1 lv = false) /\
 (ex_attached_exFO_lv alpha2 lv = false).
Proof.
  induction lv; intros alpha1 alpha2 H.
    simpl in *. apply conj; reflexivity.

    simpl.
    case_eq (attached_exFO_x alpha1 a); intros H1;
      simpl in H; rewrite H1 in H. discriminate.
    case_eq (attached_exFO_x alpha2 a); intros H2;
      rewrite H2 in H. discriminate.
    apply IHlv. assumption.
Qed.

Lemma ex_att_allFO_lv_implSO_f : forall lv alpha1 alpha2,
  ex_attached_allFO_lv (implSO alpha1 alpha2) lv = false ->
 (ex_attached_allFO_lv alpha1 lv = false) /\
 (ex_attached_allFO_lv alpha2 lv = false).
Proof.
  induction lv; intros alpha1 alpha2 H.
    simpl in *. apply conj; reflexivity.

    simpl.
    case_eq (attached_allFO_x alpha1 a); intros H1;
      simpl in H; rewrite H1 in H. discriminate.
    case_eq (attached_allFO_x alpha2 a); intros H2;
      rewrite H2 in H. discriminate.
    apply IHlv. assumption.
Qed.

Lemma ex_att_exFO_lv_implSO_f : forall lv alpha1 alpha2,
  ex_attached_exFO_lv (implSO alpha1 alpha2) lv = false ->
 (ex_attached_exFO_lv alpha1 lv = false) /\
 (ex_attached_exFO_lv alpha2 lv = false).
Proof.
  induction lv; intros alpha1 alpha2 H.
    simpl in *. apply conj; reflexivity.

    simpl.
    case_eq (attached_exFO_x alpha1 a); intros H1;
      simpl in H; rewrite H1 in H. discriminate.
    case_eq (attached_exFO_x alpha2 a); intros H2;
      rewrite H2 in H. discriminate.
    apply IHlv. assumption.
Qed.

Lemma ex_att_allFO_lv_allSO : forall lv alpha P,
  ex_attached_allFO_lv (allSO P alpha) lv = 
  ex_attached_allFO_lv alpha lv.
Proof.
  induction lv; intros alpha P.
    reflexivity.

    simpl. rewrite IHlv.
    reflexivity.
Qed.

Lemma ex_att_exFO_lv_allSO : forall lv alpha P,
  ex_attached_exFO_lv (allSO P alpha) lv = 
  ex_attached_exFO_lv alpha lv.
Proof.
  induction lv; intros alpha P.
    reflexivity.

    simpl. rewrite IHlv.
    reflexivity.
Qed.

Lemma ex_att_allFO_lv_exSO : forall lv alpha P,
  ex_attached_allFO_lv (exSO P alpha) lv = 
  ex_attached_allFO_lv alpha lv.
Proof.
  induction lv; intros alpha P.
    reflexivity.

    simpl. rewrite IHlv.
    reflexivity.
Qed.

Lemma ex_att_exFO_lv_exSO : forall lv alpha P,
  ex_attached_exFO_lv (exSO P alpha) lv = 
  ex_attached_exFO_lv alpha lv.
Proof.
  induction lv; intros alpha P.
    reflexivity.

    simpl. rewrite IHlv.
    reflexivity.
Qed.

Lemma SOQFree_P_conjSO_t : forall alpha1 alpha2 P,
  SOQFree_P (conjSO alpha1 alpha2) P = true ->
  SOQFree_P alpha1 P = true /\
  SOQFree_P alpha2 P = true.
Proof.
  intros alpha1 alpha2 [Pn] Hno.
  simpl in Hno.
  case_eq (SOQFree_P alpha1 (Pred Pn)); intros Hno1;
    rewrite Hno1 in Hno.
    apply conj. reflexivity. assumption.
    discriminate.
Qed.

Lemma SOQFree_P_disjSO_t : forall alpha1 alpha2 P,
  SOQFree_P (disjSO alpha1 alpha2) P = true ->
  SOQFree_P alpha1 P = true /\
  SOQFree_P alpha2 P = true.
Proof.
  intros alpha1 alpha2 [Pn] Hno.
  simpl in Hno.
  case_eq (SOQFree_P alpha1 (Pred Pn)); intros Hno1;
    rewrite Hno1 in Hno.
    apply conj. reflexivity. assumption.
    discriminate.
Qed.

Lemma SOQFree_P_implSO_t : forall alpha1 alpha2 P,
  SOQFree_P (implSO alpha1 alpha2) P = true ->
  SOQFree_P alpha1 P = true /\
  SOQFree_P alpha2 P = true.
Proof.
  intros alpha1 alpha2 [Pn] Hno.
  simpl in Hno.
  case_eq (SOQFree_P alpha1 (Pred Pn)); intros Hno1;
    rewrite Hno1 in Hno.
    apply conj. reflexivity. assumption.
    discriminate.
Qed.


Lemma equiv_new_simpl1 : forall alpha P lv x W Iv Ip Ir,
  is_in_var x lv = false ->
  SOQFree_P alpha P = true ->
  ex_attached_allFO_lv alpha lv = false ->
  ex_attached_exFO_lv alpha lv = false ->
    SOturnst W Iv (altered_Ip Ip (CM_pa2_l Iv lv) P) Ir alpha <->
    SOturnst W Iv Ip Ir (replace_pred alpha P x (fun1 lv x)).
Proof.
  induction alpha; intros [Pn] lv [xn] W Iv Ip Ir Hin HSO Hat1 Hat2.
    destruct p as [Qm]; destruct f as [zn].
    simpl.
    case_eq (beq_nat Pn Qm); intros Hbeq.
      apply CM_pa2_l_base. assumption.

      simpl. apply bi_refl.

    destruct f; destruct f0.
    simpl. apply bi_refl.

    destruct f; destruct f0.
    simpl. apply bi_refl.

    destruct f as [ym].
    apply ex_attached_allFO_lv_allFO in Hat1.
    destruct Hat1 as [Hat1a Hat1b].
    apply ex_attached_exFO_lv_allFO in Hat2.
    split; intros SOt d.
      apply IHalpha; try assumption.
      rewrite <- try.
      apply SOt. assumption.

      specialize (SOt d).
      apply IHalpha in SOt; try assumption.
      rewrite <- try in SOt.
      apply SOt. assumption.

    destruct f as [ym].
    apply ex_attached_allFO_lv_exFO in Hat1.
    apply ex_attached_exFO_lv_exFO in Hat2.
    destruct Hat2 as [Hat2a Hat2b].
    split; intros [d SOt]; exists d.
      apply IHalpha; try assumption.
      rewrite <- try.
      apply SOt. assumption.

      apply IHalpha in SOt; try assumption.
      rewrite <- try in SOt.
      apply SOt. assumption.

    rewrite ex_att_allFO_lv_negSO in Hat1.
    rewrite ex_att_exFO_lv_negSO in Hat2.
    simpl in *. split; intros H1 H2;
    apply H1; apply (IHalpha (Pred Pn) lv (Var xn)
        W Iv Ip Ir Hin HSO); assumption.

    destruct (ex_att_allFO_lv_conjSO_f _ _ _ Hat1)
      as [Hat1a Hat1b].
    destruct (ex_att_exFO_lv_conjSO_f _ _ _ Hat2)
      as [Hat2a Hat2b].
    destruct (SOQFree_P_conjSO_t _ _ _ HSO)
      as [HSOa HSOb].
    simpl in *. split; intros [H1 H2];
      (apply conj;
        [apply (IHalpha1 (Pred Pn) lv (Var xn)
          W Iv Ip Ir Hin HSOa); assumption |
        apply (IHalpha2 (Pred Pn) lv (Var xn)
          W Iv Ip Ir Hin HSOb); assumption]).

    destruct (ex_att_allFO_lv_disjSO_f _ _ _ Hat1)
      as [Hat1a Hat1b].
    destruct (ex_att_exFO_lv_disjSO_f _ _ _ Hat2)
      as [Hat2a Hat2b].
    destruct (SOQFree_P_disjSO_t _ _ _ HSO)
      as [HSOa HSOb].
    simpl in *. split; (intros [H1 | H2];
      [left; apply (IHalpha1 (Pred Pn) lv (Var xn)
          W Iv Ip Ir Hin HSOa); assumption |
      right; apply (IHalpha2 (Pred Pn) lv (Var xn)
          W Iv Ip Ir Hin HSOb); assumption]).

    destruct (ex_att_allFO_lv_implSO_f _ _ _ Hat1)
      as [Hat1a Hat1b].
    destruct (ex_att_exFO_lv_implSO_f _ _ _ Hat2)
      as [Hat2a Hat2b].
    destruct (SOQFree_P_implSO_t _ _ _ HSO)
      as [HSOa HSOb].
    simpl in *. split; intros H1 H2;
      apply (IHalpha2 (Pred Pn) lv (Var xn)
          W Iv Ip Ir Hin HSOb); try assumption;
      apply H1; apply (IHalpha1 (Pred Pn) lv (Var xn)
          W Iv Ip Ir Hin HSOa); assumption.

    rewrite ex_att_allFO_lv_allSO in Hat1.
    rewrite ex_att_exFO_lv_allSO in Hat2.
    simpl in HSO. destruct p as [Qm].
    case_eq (beq_nat Pn Qm); intros Hbeq;
      rewrite Hbeq in *. discriminate.
    simpl replace_pred. rewrite Hbeq.
    do 2 rewrite SOturnst_allSO.
    split; intros SOt pa.
      apply (IHalpha (Pred Pn) lv (Var xn)
          W Iv _ Ir Hin HSO); try assumption.
      rewrite altered_Ip_switch.
      apply SOt.
        intros H; rewrite H in Hbeq.
        rewrite <- beq_nat_refl in Hbeq. discriminate.

      rewrite altered_Ip_switch.
      apply (IHalpha (Pred Pn) lv (Var xn)
          W Iv _ Ir Hin HSO); try assumption.
      apply SOt.
        intros H; rewrite H in Hbeq.
        rewrite <- beq_nat_refl in Hbeq. discriminate.

    rewrite ex_att_allFO_lv_exSO in Hat1.
    rewrite ex_att_exFO_lv_exSO in Hat2.
    simpl in HSO. destruct p as [Qm].
    case_eq (beq_nat Pn Qm); intros Hbeq;
      rewrite Hbeq in *. discriminate.
    simpl replace_pred. rewrite Hbeq.
    do 2 rewrite SOturnst_exSO.
    split; intros [pa SOt]; exists pa.
      apply (IHalpha (Pred Pn) lv (Var xn)
          W Iv _ Ir Hin HSO); try assumption.
      rewrite altered_Ip_switch.
      apply SOt.
        intros H; rewrite H in Hbeq.
        rewrite <- beq_nat_refl in Hbeq. discriminate.

      rewrite altered_Ip_switch.
      apply (IHalpha (Pred Pn) lv (Var xn)
          W Iv _ Ir Hin HSO); try assumption.
        intros H; rewrite H in Hbeq.
        rewrite <- beq_nat_refl in Hbeq. discriminate.
Qed.

Lemma replace_FOv_disjSO: forall alpha beta x y,
  replace_FOv (disjSO alpha beta) x y =
  disjSO (replace_FOv alpha x y) (replace_FOv beta x y).
Proof.
  intros. destruct x. simpl. reflexivity.
Qed.

Lemma equiv_new_simpl_try2_pre : forall lv x y W Iv Ip Ir,
  is_in_var x lv = true ->
  (SOturnst W Iv Ip Ir (replace_FOv (fun1 lv x) x y)).
Proof.
  induction lv; intros [xn] [ym] W Iv Ip Ir Hin.
    simpl in *. discriminate.

    destruct a as [zn].
    simpl in *.
    case_eq (beq_nat xn zn); intros Hbeq;
      rewrite Hbeq in *.
      destruct lv.
        simpl. rewrite <- beq_nat_refl.
          rewrite Hbeq.
          simpl. reflexivity.
        rewrite replace_FOv_disjSO.
        rewrite SOturnst_disjSO.
        left. simpl. rewrite <- beq_nat_refl.
        rewrite Hbeq. reflexivity.

      destruct lv. discriminate.
        simpl in *. rewrite <-beq_nat_refl.
        rewrite Hbeq.
        right. apply IHlv. assumption.
Qed.

Lemma equiv_new_simpl_try2 : forall alpha P lv x W Iv Ip Ir,
  is_in_var x lv = true ->
  SOQFree_P alpha P = true ->
  ex_attached_allFO_lv alpha lv = false ->
  ex_attached_exFO_lv alpha lv = false ->
    SOturnst W Iv (altered_Ip Ip pa_t P) Ir alpha <->
    SOturnst W Iv Ip Ir (replace_pred alpha P x (fun1 lv x)).
Proof.
  induction alpha; intros [Pn] lv [xn] W Iv Ip Ir Hin HSO Hat1 Hat2.
    destruct p as [Qm]; destruct f as [ym].
    simpl in *.
    case_eq (beq_nat Pn Qm); intros Hbeq.
      unfold pa_t.
      split; intros H.
        apply equiv_new_simpl_try2_pre. assumption.
        exact I.

      simpl. apply bi_refl.

    destruct f; destruct f0.
    simpl. apply bi_refl.

    destruct f; destruct f0.
    simpl. apply bi_refl.

    destruct f as [zn].
    simpl replace_pred.
    simpl in HSO.
    destruct (ex_attached_allFO_lv_allFO _ _ _ Hat1)
      as [Hat1a Hat1b].
    apply ex_attached_exFO_lv_allFO in Hat2.
    split; intros SOt d;
      apply (IHalpha (Pred Pn) lv (Var xn) W _ Ip Ir); 
      try assumption; apply SOt.

    destruct f as [zn].
    simpl replace_pred.
    simpl in HSO.
    destruct (ex_attached_exFO_lv_exFO _ _ _ Hat2)
      as [Hat2a Hat2b].
    apply ex_attached_allFO_lv_exFO in Hat1.
    split; intros [d SOt]; exists d;
      apply (IHalpha (Pred Pn) lv (Var xn) W _ Ip Ir); 
      try assumption; apply SOt.

    simpl in *.
    rewrite ex_att_allFO_lv_negSO in Hat1.
    rewrite ex_att_exFO_lv_negSO in Hat2.
    split; intros H1 H2; apply H1;
      apply (IHalpha (Pred Pn) lv (Var xn) W Iv Ip Ir); 
      assumption.

    destruct (ex_att_allFO_lv_conjSO_f _ _ _ Hat1) as
      [Hat1a Hat1b].
    destruct (ex_att_exFO_lv_conjSO_f _ _ _ Hat2) as
      [Hat2a Hat2b].
    destruct (SOQFree_P_conjSO_t _ _ _ HSO) as
      [HSOa HSOb].
    simpl.
    split; intros [H1 H2]; (apply conj;
      [apply (IHalpha1 (Pred Pn) lv (Var xn) W Iv Ip Ir); 
      assumption |
      apply (IHalpha2 (Pred Pn) lv (Var xn) W Iv Ip Ir); 
      assumption]).

    destruct (ex_att_allFO_lv_disjSO_f _ _ _ Hat1) as
      [Hat1a Hat1b].
    destruct (ex_att_exFO_lv_disjSO_f _ _ _ Hat2) as
      [Hat2a Hat2b].
    destruct (SOQFree_P_disjSO_t _ _ _ HSO) as
      [HSOa HSOb].
    simpl.
    split; (intros [H | H];
      [left; apply (IHalpha1 (Pred Pn) lv (Var xn) W Iv Ip Ir); 
      assumption |
      right; apply (IHalpha2 (Pred Pn) lv (Var xn) W Iv Ip Ir); 
      assumption]).

    destruct (ex_att_allFO_lv_implSO_f _ _ _ Hat1) as
      [Hat1a Hat1b].
    destruct (ex_att_exFO_lv_implSO_f _ _ _ Hat2) as
      [Hat2a Hat2b].
    destruct (SOQFree_P_implSO_t _ _ _ HSO) as
      [HSOa HSOb].
    simpl.
    split; intros H1 H2;
      apply (IHalpha2 (Pred Pn) lv (Var xn) W Iv Ip Ir);
      try assumption;
      apply H1;
      apply (IHalpha1 (Pred Pn) lv (Var xn) W Iv Ip Ir); 
      assumption.

    destruct p as [Qm]. simpl in *.
    case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *.
      discriminate.
    rewrite ex_att_allFO_lv_allSO in Hat1.
    rewrite ex_att_exFO_lv_allSO in Hat2.
    split; intros SOt pa.
      apply (IHalpha (Pred Pn) lv (Var xn) W Iv _ Ir); try assumption.
      rewrite altered_Ip_switch.
      apply SOt.
        intros H; rewrite H in Hbeq; rewrite <- beq_nat_refl in Hbeq;
        discriminate.

      specialize (SOt pa).
      apply (IHalpha (Pred Pn) lv (Var xn) W Iv _ Ir) in SOt; try assumption.
      rewrite altered_Ip_switch in SOt.
      apply SOt.
        intros H; rewrite H in Hbeq; rewrite <- beq_nat_refl in Hbeq;
        discriminate.

    destruct p as [Qm]. simpl in *.
    case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *.
      discriminate.
    rewrite ex_att_allFO_lv_exSO in Hat1.
    rewrite ex_att_exFO_lv_exSO in Hat2.
    split; intros [pa SOt]; exists pa.
      apply (IHalpha (Pred Pn) lv (Var xn) W Iv _ Ir); try assumption.
      rewrite altered_Ip_switch.
      apply SOt.
        intros H; rewrite H in Hbeq; rewrite <- beq_nat_refl in Hbeq;
        discriminate.

      apply (IHalpha (Pred Pn) lv (Var xn) W Iv _ Ir) in SOt; try assumption.
      rewrite altered_Ip_switch in SOt.
      apply SOt.
        intros H; rewrite H in Hbeq; rewrite <- beq_nat_refl in Hbeq;
        discriminate.
Qed.

Definition CM_pa2_l_gen {W : Set} (Iv : FOvariable -> W) lv x : W -> Prop :=
  if is_in_var x lv then pa_t else CM_pa2_l Iv lv.

Lemma equiv_new_simpl3 : forall alpha P lv x W Iv Ip Ir,
  SOQFree_P alpha P = true ->
  ex_attached_allFO_lv alpha lv = false ->
  ex_attached_exFO_lv alpha lv = false ->
    SOturnst W Iv (altered_Ip Ip (CM_pa2_l_gen Iv lv x) P) Ir alpha <->
    SOturnst W Iv Ip Ir (replace_pred alpha P x (fun1 lv x)).
Proof.
  intros until 0.
  unfold CM_pa2_l_gen.
  case_eq (is_in_var x lv); intros Hin.
    apply equiv_new_simpl_try2. assumption.

    apply equiv_new_simpl1. assumption.
Qed.

(* Fixpoint CM_pa2_l_gen_l {W : Set} (Iv : FOvariable -> W) (llv : list (list FOvariable))
          (x : FOvariable) : list (W -> Prop) :=
  match llv with
  | nil => nil
  | cons lv llv' =>
    cons (CM_pa2_l_gen Iv lv x) (CM_pa2_l_gen_l Iv llv' x)
  end. *)

Fixpoint ex_attached_allFO_llv alpha llv : bool :=
  match llv with
  | nil => false
  | cons lv llv' => if ex_attached_allFO_lv alpha lv then true else 
      ex_attached_allFO_llv alpha llv'
  end.

Fixpoint ex_attached_exFO_llv alpha llv : bool :=
  match llv with
  | nil => false
  | cons lv llv' => if ex_attached_exFO_lv alpha lv then true else 
      ex_attached_exFO_llv alpha llv'
  end.

Lemma length_vsS_syn_l : forall l x,
  length l = length (vsS_syn_l l x).
Proof.
  induction l; intros [xn]. reflexivity.
  simpl. rewrite <- IHl. reflexivity.
Qed.

Lemma altered_Ip__list_occ_f : forall l W pa_l pa P Ip,
  occ_in_l l P = false ->
  altered_Ip_list (@altered_Ip W Ip pa P) pa_l l =
  altered_Ip (altered_Ip_list Ip pa_l l) pa P.
Proof.
  induction l; intros W pa_l pa P Ip Hocc.
    destruct pa_l; reflexivity.

    destruct pa_l. reflexivity.
    simpl.
    destruct P as [Pn].
    destruct a as [Qm].
    case_eq (beq_nat Pn Qm); intros Hbeq.
      simpl in Hocc.
      rewrite Hbeq in Hocc.
      discriminate.
    rewrite IHl.
    rewrite altered_Ip_switch.
      reflexivity.

      intros H. rewrite H in Hbeq.
      rewrite <- beq_nat_refl in Hbeq.
      discriminate.

      simpl in Hocc. rewrite Hbeq in Hocc.  
      assumption.
Qed.

Lemma un_predless_fun1 : forall l x,
  is_unary_predless (fun1 l x) = true.
Proof.
  induction l; intros x.
    reflexivity.

    simpl. destruct l. 
      destruct x; destruct a.
      reflexivity.

      simpl. destruct x. destruct a.
      simpl in *. apply IHl.
Qed.

Lemma un_predless_l_vsS_syn_l : forall lv x,
  is_unary_predless_l (vsS_syn_l lv x) = true.
Proof.
  induction lv; intros x.
    reflexivity.

    simpl. rewrite un_predless_fun1.
    apply IHlv.
Qed.

Lemma occ_in_l_is_in_pred : forall l P,
  occ_in_l l P = is_in_pred P l.
Proof.
  induction l; intros [Pn].
    reflexivity.

    destruct a as [Qm]. simpl.
    rewrite IHl. reflexivity.
Qed.

Lemma SOQFree__P : forall alpha P,
  SOQFree alpha = true ->
  SOQFree_P alpha P = true.
Proof.
  induction alpha; intros [Pn] H;
    try reflexivity.

    destruct f as [zn].
    simpl in *. apply IHalpha.
    assumption.

    destruct f as [zn].
    simpl in *. apply IHalpha.
    assumption.

    simpl in *. apply IHalpha. assumption.

    pose proof (SOQFree_conjSO_r _ _ H) as H2.
    apply SOQFree_conjSO_l in H.
    simpl. rewrite IHalpha1. apply IHalpha2.
    all : try assumption.

    pose proof (SOQFree_conjSO_r _ _ H) as H2.
    apply SOQFree_conjSO_l in H.
    simpl. rewrite IHalpha1. apply IHalpha2.
    all : try assumption.

    pose proof (SOQFree_conjSO_r _ _ H) as H2.
    apply SOQFree_conjSO_l in H.
    simpl. rewrite IHalpha1. apply IHalpha2.
    all : try assumption.

    destruct p. simpl in *. discriminate.

    destruct p. simpl in *. discriminate.
Qed.

Lemma SOQFree_fun1 : forall l x,
  SOQFree (fun1 l x) = true.
Proof.
  induction l; intros x.
    reflexivity.

    destruct x.
    simpl. destruct l.
      destruct a. reflexivity.

      destruct a.
      simpl. apply IHl.
Qed.

Lemma attached_allFO_x_rep_FOv : forall alpha x y z,
  attached_allFO_x alpha x = false ->
  attached_allFO_x alpha z = false ->
  attached_allFO_x (replace_FOv alpha x y) z = false.
Proof.
  induction alpha; intros [x1] [x2] [ym] H1 H2.
    destruct p; destruct f as [zn].
    simpl. case_eq (beq_nat x1 zn); intros Hbeq;
      reflexivity.

    destruct f as [z1]; destruct f0 as [z2]. simpl.
    case_eq (beq_nat x1 z1); intros Hbeq;
      case_eq (beq_nat x1 z2); intros Hbeq2;
        reflexivity.

    destruct f as [z1]; destruct f0 as [z2]. simpl.
    case_eq (beq_nat x1 z1); intros Hbeq;
      case_eq (beq_nat x1 z2); intros Hbeq2;
        reflexivity.

    destruct f as [zn]. simpl.
    case_eq (beq_nat x1 zn); intros Hbeq;
      simpl in H1; rewrite Hbeq in H1.
      discriminate.
    simpl.
    case_eq (beq_nat ym zn); intros Hbeq2;
      simpl in H2; rewrite Hbeq2 in H2.
      discriminate.
    apply IHalpha; assumption.

    destruct f as [zn]. simpl.
    simpl in *.
    case_eq (beq_nat x1 zn); intros Hbeq;
      simpl; apply IHalpha; assumption.

    simpl in *.
    apply IHalpha; assumption.

    pose proof (attached_allFO_x_conjSO_r _ _ _ H1) as H3.
    apply attached_allFO_x_conjSO_l in H1.
    pose proof (attached_allFO_x_conjSO_r _ _ _ H2) as H4.
    apply attached_allFO_x_conjSO_l in H2.
    simpl. rewrite IHalpha1. apply IHalpha2.
    all : try assumption.

    pose proof (attached_allFO_x_conjSO_r _ _ _ H1) as H3.
    apply attached_allFO_x_conjSO_l in H1.
    pose proof (attached_allFO_x_conjSO_r _ _ _ H2) as H4.
    apply attached_allFO_x_conjSO_l in H2.
    simpl. rewrite IHalpha1. apply IHalpha2.
    all : try assumption.

    pose proof (attached_allFO_x_conjSO_r _ _ _ H1) as H3.
    apply attached_allFO_x_conjSO_l in H1.
    pose proof (attached_allFO_x_conjSO_r _ _ _ H2) as H4.
    apply attached_allFO_x_conjSO_l in H2.
    simpl. rewrite IHalpha1. apply IHalpha2.
    all : try assumption.

    destruct p as [Qm]. simpl. apply IHalpha;
    simpl in *; assumption.

    destruct p as [Qm]. simpl. apply IHalpha;
    simpl in *; assumption.
Qed.

Lemma attached_exFO_x_rep_FOv : forall alpha x y z,
  attached_exFO_x alpha x = false ->
  attached_exFO_x alpha z = false ->
  attached_exFO_x (replace_FOv alpha x y) z = false.
Proof.
  induction alpha; intros [x1] [x2] [ym] H1 H2.
    destruct p; destruct f as [zn].
    simpl. case_eq (beq_nat x1 zn); intros Hbeq;
      reflexivity.

    destruct f as [z1]; destruct f0 as [z2]. simpl.
    case_eq (beq_nat x1 z1); intros Hbeq;
      case_eq (beq_nat x1 z2); intros Hbeq2;
        reflexivity.

    destruct f as [z1]; destruct f0 as [z2]. simpl.
    case_eq (beq_nat x1 z1); intros Hbeq;
      case_eq (beq_nat x1 z2); intros Hbeq2;
        reflexivity.

    destruct f as [zn]. simpl.
    simpl in *.
    case_eq (beq_nat x1 zn); intros Hbeq;
      simpl; apply IHalpha; assumption.

    destruct f as [zn]. simpl.
    case_eq (beq_nat x1 zn); intros Hbeq;
      simpl in H1; rewrite Hbeq in H1.
      discriminate.
    simpl.
    case_eq (beq_nat ym zn); intros Hbeq2;
      simpl in H2; rewrite Hbeq2 in H2.
      discriminate.
    apply IHalpha; assumption.

    simpl in *.
    apply IHalpha; assumption.

    pose proof (attached_exFO_x_conjSO_r _ _ _ H1) as H3.
    apply attached_exFO_x_conjSO_l in H1.
    pose proof (attached_exFO_x_conjSO_r _ _ _ H2) as H4.
    apply attached_exFO_x_conjSO_l in H2.
    simpl. rewrite IHalpha1. apply IHalpha2.
    all : try assumption.

    pose proof (attached_exFO_x_conjSO_r _ _ _ H1) as H3.
    apply attached_exFO_x_conjSO_l in H1.
    pose proof (attached_exFO_x_conjSO_r _ _ _ H2) as H4.
    apply attached_exFO_x_conjSO_l in H2.
    simpl. rewrite IHalpha1. apply IHalpha2.
    all : try assumption.

    pose proof (attached_exFO_x_conjSO_r _ _ _ H1) as H3.
    apply attached_exFO_x_conjSO_l in H1.
    pose proof (attached_exFO_x_conjSO_r _ _ _ H2) as H4.
    apply attached_exFO_x_conjSO_l in H2.
    simpl. rewrite IHalpha1. apply IHalpha2.
    all : try assumption.

    destruct p as [Qm]. simpl. apply IHalpha;
    simpl in *; assumption.

    destruct p as [Qm]. simpl. apply IHalpha;
    simpl in *; assumption.
Qed.

Lemma no_FOquant_att_allFO : forall alpha x,
  no_FOquant alpha = true ->
  attached_allFO_x alpha x = false.
Proof.
  induction alpha; intros x H; try reflexivity.

    destruct f as [ym]. destruct x as [xn].
    simpl in *. discriminate.

    destruct f as [ym]. destruct x as [xn].
    simpl in *. discriminate.

    simpl in *. apply IHalpha; assumption.

    pose proof (no_FOquant_conjSO_r _ _ H) as H2.
    apply no_FOquant_conjSO_l in H.
    simpl. rewrite IHalpha1. apply IHalpha2.
    all : try assumption.

    pose proof (no_FOquant_conjSO_r _ _ H) as H2.
    apply no_FOquant_conjSO_l in H.
    simpl. rewrite IHalpha1. apply IHalpha2.
    all : try assumption.

    pose proof (no_FOquant_conjSO_r _ _ H) as H2.
    apply no_FOquant_conjSO_l in H.
    simpl. rewrite IHalpha1. apply IHalpha2.
    all : try assumption.

    destruct p. simpl in *. apply IHalpha.
    assumption.

    destruct p. simpl in *. apply IHalpha.
    assumption.
Qed.

Lemma no_FOquant_att_exFO : forall alpha x,
  no_FOquant alpha = true ->
  attached_exFO_x alpha x = false.
Proof.
  induction alpha; intros x H; try reflexivity.

    destruct f as [ym]. destruct x as [xn].
    simpl in *. discriminate.

    destruct f as [ym]. destruct x as [xn].
    simpl in *. discriminate.

    simpl in *. apply IHalpha; assumption.

    pose proof (no_FOquant_conjSO_r _ _ H) as H2.
    apply no_FOquant_conjSO_l in H.
    simpl. rewrite IHalpha1. apply IHalpha2.
    all : try assumption.

    pose proof (no_FOquant_conjSO_r _ _ H) as H2.
    apply no_FOquant_conjSO_l in H.
    simpl. rewrite IHalpha1. apply IHalpha2.
    all : try assumption.

    pose proof (no_FOquant_conjSO_r _ _ H) as H2.
    apply no_FOquant_conjSO_l in H.
    simpl. rewrite IHalpha1. apply IHalpha2.
    all : try assumption.

    destruct p. simpl in *. apply IHalpha.
    assumption.

    destruct p. simpl in *. apply IHalpha.
    assumption.
Qed.


Lemma attached_allFO_x_rep_pred : forall alpha cond y Q x,
  no_FOquant cond = true ->
  attached_allFO_x alpha y = false ->
  attached_allFO_x (replace_pred alpha Q x cond) y = false.
Proof.
  induction alpha; intros cond [ym] [Qm] [xn] H1 H2.
    destruct p as [Rn]. destruct f as [zn]. simpl.
    case_eq (beq_nat Qm Rn); intros Hbeq.
      apply attached_allFO_x_rep_FOv;
        try assumption;
        apply no_FOquant_att_allFO; assumption.

      reflexivity.

    destruct f. destruct f0. reflexivity.

    destruct f. destruct f0. reflexivity.

    destruct f as [zn]. simpl.
    case_eq (beq_nat ym zn); intros Hbeq;
      simpl in H2; rewrite Hbeq in H2. discriminate.
    apply IHalpha; try assumption.

    destruct f as [zn]. simpl.
    apply IHalpha; try assumption.

    simpl. apply IHalpha; assumption.

    simpl. rewrite IHalpha1. apply IHalpha2.
    all : try assumption.
      case_eq (attached_allFO_x alpha2 (Var ym));
        simpl in *;
        intros H; rewrite H in *.
        rewrite if_then_else_true in H2. discriminate.

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
        rewrite if_then_else_true in H2. discriminate.

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
        rewrite if_then_else_true in H2. discriminate.

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

Lemma attached_exFO_x_rep_pred : forall alpha cond y Q x,
  no_FOquant cond = true ->
  attached_exFO_x alpha y = false ->
  attached_exFO_x (replace_pred alpha Q x cond) y = false.
Proof.
  induction alpha; intros cond [ym] [Qm] [xn] H1 H2.
    destruct p as [Rn]. destruct f as [zn]. simpl.
    case_eq (beq_nat Qm Rn); intros Hbeq.
      apply attached_exFO_x_rep_FOv;
        try assumption;
        apply no_FOquant_att_exFO; assumption.

      reflexivity.

    destruct f. destruct f0. reflexivity.

    destruct f. destruct f0. reflexivity.

    destruct f as [zn]. simpl.
    apply IHalpha; try assumption.

    destruct f as [zn]. simpl.
    case_eq (beq_nat ym zn); intros Hbeq;
      simpl in H2; rewrite Hbeq in H2. discriminate.
    apply IHalpha; try assumption.

    simpl. apply IHalpha; assumption.

    simpl. rewrite IHalpha1. apply IHalpha2.
    all : try assumption.
      case_eq (attached_exFO_x alpha2 (Var ym));
        simpl in *;
        intros H; rewrite H in *.
        rewrite if_then_else_true in H2. discriminate.

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
        rewrite if_then_else_true in H2. discriminate.

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
        rewrite if_then_else_true in H2. discriminate.

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


Lemma ex_attached_allFO_lv_rep_pred : forall lv alpha cond P x,
  no_FOquant cond = true ->
  ex_attached_allFO_lv alpha lv = false ->
  ex_attached_allFO_lv (replace_pred alpha P x cond) lv = false.
Proof.
  induction lv; intros alpha cond P x H1 H2.
    reflexivity.

    simpl in *.
    case_eq (attached_allFO_x alpha a); intros H2a;
      rewrite H2a in *. discriminate.
    rewrite (attached_allFO_x_rep_pred _ _ _ _ _ H1 H2a).
    apply IHlv; assumption.
Qed.

Lemma ex_attached_exFO_lv_rep_pred : forall lv alpha cond P x,
  no_FOquant cond = true ->
  ex_attached_exFO_lv alpha lv = false ->
  ex_attached_exFO_lv (replace_pred alpha P x cond) lv = false.
Proof.
  induction lv; intros alpha cond P x H1 H2.
    reflexivity.

    simpl in *.
    case_eq (attached_exFO_x alpha a); intros H2a;
      rewrite H2a in *. discriminate.
    rewrite (attached_exFO_x_rep_pred _ _ _ _ _ H1 H2a).
    apply IHlv; assumption.
Qed.

Lemma ex_attached_allFO_llv_rep_pred : forall llv alpha cond P x,
  no_FOquant cond = true ->
  ex_attached_allFO_llv alpha llv = false ->
  ex_attached_allFO_llv (replace_pred alpha P x cond) llv = false.
Proof.
  induction llv; intros alpha cond P x Hat1 Hat2.
    simpl in *. reflexivity.

    simpl in *.
    case_eq (ex_attached_allFO_lv alpha a); intros H2;
      rewrite H2 in *. discriminate.
    rewrite ex_attached_allFO_lv_rep_pred.
    apply IHllv. all : try assumption.
Qed.

Lemma ex_attached_exFO_llv_rep_pred : forall llv alpha cond P x,
  no_FOquant cond = true ->
  ex_attached_exFO_llv alpha llv = false ->
  ex_attached_exFO_llv (replace_pred alpha P x cond) llv = false.
Proof.
  induction llv; intros alpha cond P x Hat1 Hat2.
    simpl in *. reflexivity.

    simpl in *.
    case_eq (ex_attached_exFO_lv alpha a); intros H2;
      rewrite H2 in *. discriminate.
    rewrite ex_attached_exFO_lv_rep_pred.
    apply IHllv. all : try assumption.
Qed.

Lemma no_FOquant_fun1 : forall l x,
  no_FOquant (fun1 l x) = true.
Proof.
  induction l; intros x.
    reflexivity.

    simpl. destruct l. reflexivity.
    simpl. apply IHl.
Qed.

(* Lemma length_CM_pa2_l_gen_l : forall {W : Set} (Iv : FOvariable -> W)
        llv x,
  length (CM_pa2_l_gen_l Iv llv x) =
  length llv.
Proof.
  intros W Iv; induction llv; intros x.
    reflexivity.

    simpl. rewrite IHllv.
    reflexivity.
Qed. *)

Lemma x_occ_in_alpha_conjSO : forall alpha1 alpha2 x,
  x_occ_in_alpha (conjSO alpha1 alpha2) x = false ->
  x_occ_in_alpha alpha1 x = false /\ x_occ_in_alpha alpha2 x = false.
Proof.
  intros alpha1 alpha2 x Hocc.
    simpl in Hocc.
    case_eq (x_occ_in_alpha alpha1 x); intros H1;
      rewrite H1 in *. discriminate.
    apply conj. reflexivity. assumption.
Qed.