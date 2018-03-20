Require Export vsSahlq_instant10.

(* --------------------------------------------------------------------- *)

Fixpoint vsS_pa_l {W : Set} (Iv : FOvariable -> W)  llv lx :=
  match llv, lx with
  | nil, _ => nil
  | _, nil => nil
  | cons lv llv', cons x lx' =>
      cons (CM_pa2_l_gen Iv lv x) (vsS_pa_l Iv llv' lx')
  end. 

Fixpoint at_pa {W : Set} (n : nat) (l : list (W -> Prop)) : W -> Prop :=
  match n, l with 
  | 0, _ => pa_f
  | _, nil => pa_f
  | 1, (cons x l) => x
  | (S m), (cons x l) => at_pa m l
  end.

Fixpoint ind_pa {W : Set} (l : list nat) (lx : list (W -> Prop)) : 
    list (W -> Prop) :=
  match l with
  | nil => nil
  | cons n l' => cons (at_pa n lx) (ind_pa l' lx)
  end.

Fixpoint indicies_l2_pre lP P count :=
  match lP with
  | nil => nil
  | cons Q lP' => match P, Q with Pred Pn, Pred Qm =>
      if beq_nat Pn Qm then cons (1 + count) (indicies_l2_pre lP' P (S count))
        else indicies_l2_pre lP' P (S count)
  end end.

Definition indicies_l2 lP P :=
  indicies_l2_pre lP P 0.


Fixpoint constant_l {A : Type} (a : A) (n : nat) : list A :=
  match n with
  | 0 => nil
  | S m => cons a (constant_l a m)
  end.

Definition is_constant {A : Type} (l : list A) : Prop :=
  exists a n,
    l = constant_l a n.

Fixpoint at_FOv (n : nat) (l : list FOvariable) : FOvariable :=
  match n, l with 
  | 0, _ => (Var 1)
  | _, nil => (Var 1)
  | 1, (cons x l) => x
  | (S m), (cons x l) => at_FOv m l
  end.

Fixpoint ind_FOv (l : list nat) (lx : list FOvariable) : list FOvariable :=
  match l with
  | nil => nil
  | cons n l' => cons (at_FOv n lx) (ind_FOv l' lx)
  end.


Fixpoint at_cond (n : nat) (l : list SecOrder) : SecOrder :=
  match n, l with 
  | 0, _ => eqFO (Var 1) (Var 1)
  | _, nil => eqFO (Var 1) (Var 1)
  | 1, (cons x l) => x
  | (S m), (cons x l') => at_cond m l'
  end.

Fixpoint ind_cond (l : list nat) (lx : list SecOrder) : list SecOrder :=
  match l with
  | nil => nil
  | cons n l' => cons (at_cond n lx) (ind_cond l' lx)
  end.


Definition consistent_lP_lx_P lP lx P : Prop :=
  is_constant (ind_FOv (indicies_l2 lP P) lx).

Definition consistent_lP_lx lP lx : Prop :=
  forall P, consistent_lP_lx_P lP lx P.

Definition consistent_lP_lcond_P lP lx P : Prop :=
  is_constant (ind_cond (indicies_l2 lP P) lx).

Definition consistent_lP_lcond lP lx : Prop :=
  forall P, consistent_lP_lcond_P lP lx P.

Fixpoint at_llv (n : nat) (llv : list (list FOvariable)) : (list FOvariable) :=
  match n, llv with 
  | 0, _ => nil
  | _, nil => nil
  | 1, (cons x l) => x
  | (S m), (cons x l) => at_llv m l
  end.

Fixpoint ind_llv (l : list nat) (llv : list (list FOvariable))
     : list (list FOvariable) :=
  match l with
  | nil => nil
  | cons n l' => cons (at_llv n llv) (ind_llv l' llv)
  end.

Definition consistent_lP_llv_P lP llv P : Prop :=
  is_constant (ind_llv (indicies_l2 lP P) llv).

Definition consistent_lP_llv lP llv : Prop :=
  forall P, consistent_lP_llv_P lP llv P.

Lemma ind_pa_pre_cons : forall {W : Set} lP P n (pa : W -> Prop) lpa,
  ind_pa (indicies_l2_pre lP P (S n)) (cons pa lpa) =
  ind_pa (indicies_l2_pre lP P n) lpa.
Proof.
  induction lP; intros P n pa lpa.
    simpl. reflexivity.

    destruct a as [Qm]. destruct P as [Pn]. simpl.
    destruct n; destruct lpa;
    case_eq (beq_nat Pn Qm); intros Hbeq; simpl; rewrite IHlP;
      reflexivity.
Qed.

Lemma constant_l_cons: forall {A : Type} n l a b,
  (cons b l) = constant_l (a:A) n ->
  b = a.
Proof.
  intros A. destruct n; intros l a b H.
    simpl in *. discriminate.

    simpl in *. inversion H. reflexivity.
Qed.

Lemma constant_l_cons2: forall {A : Type} n l a b1 b2,
  (cons b1 (cons b2 l)) = constant_l (a:A) n ->
  b2 = a.
Proof.
  intros A. destruct n; intros l a b1 b2 H.
    simpl in *. discriminate.

    simpl in *. inversion H. destruct n. discriminate.
    inversion H2. reflexivity.
Qed.


Lemma ind_cond_ind_l2_pre_cons : forall lP n lcond Q alpha,
  ind_cond (indicies_l2_pre lP Q (S n)) (cons alpha lcond) =
  ind_cond (indicies_l2_pre lP Q n) lcond.
Proof.
  induction lP; intros n lcond Q alpha.
    reflexivity.

    simpl. destruct Q as [Pn]; destruct a as [Qm].
    case_eq (beq_nat Pn Qm); intros Hbeq.
      simpl. destruct n; rewrite IHlP; reflexivity.
      rewrite IHlP. reflexivity.
Qed.

Lemma ind_FOv_ind_l2_pre_cons : forall lP n lcond Q alpha,
  ind_FOv (indicies_l2_pre lP Q (S n)) (cons alpha lcond) =
  ind_FOv (indicies_l2_pre lP Q n) lcond.
Proof.
  induction lP; intros n lcond Q alpha.
    reflexivity.

    simpl. destruct Q as [Pn]; destruct a as [Qm].
    case_eq (beq_nat Pn Qm); intros Hbeq.
      simpl. destruct n; rewrite IHlP; reflexivity.
      rewrite IHlP. reflexivity.
Qed.

Lemma is_constant_ind_FOv_switch : forall lP lx P Q R x y,
  is_constant (ind_FOv (indicies_l2_pre (cons P (cons Q lP)) R 0) (cons x (cons y lx))) ->
  is_constant (ind_FOv (indicies_l2_pre (cons Q (cons P lP)) R 0) (cons y (cons x lx))).
Proof.
  intros lP lx [Pn] [Qm] [Rn] x y H.
  simpl in *. case_eq (beq_nat Rn Qm); intros Hbeq;
    rewrite Hbeq in *.
    case_eq (beq_nat Rn Pn); intros Hbeq2; rewrite Hbeq2 in *;
      simpl in *;
      unfold is_constant in *; destruct H as [z [n Heq]];
      exists z; exists n;
      destruct n; simpl in *; try discriminate;
      simpl in *; inversion Heq;
      destruct n; try discriminate;
      inversion H1. reflexivity.
        do 4 rewrite ind_FOv_ind_l2_pre_cons. reflexivity.
        do 4 rewrite ind_FOv_ind_l2_pre_cons. reflexivity.

    case_eq (beq_nat Rn Pn); intros Hbeq2; rewrite Hbeq2 in *;
      simpl in *;
      unfold is_constant in *; destruct H as [z [n Heq]];
      exists z; exists n;
      destruct n; simpl in *; try discriminate;
      simpl in *; inversion Heq.
        do 4 rewrite ind_FOv_ind_l2_pre_cons. reflexivity.
        do 4 rewrite ind_FOv_ind_l2_pre_cons. reflexivity.
        do 4 rewrite ind_FOv_ind_l2_pre_cons. reflexivity.
Qed.

Lemma is_constant_ind_cond_switch : forall lP lx P Q R x y,
  is_constant (ind_cond (indicies_l2_pre (cons P (cons Q lP)) R 0) (cons x (cons y lx))) ->
  is_constant (ind_cond (indicies_l2_pre (cons Q (cons P lP)) R 0) (cons y (cons x lx))).
Proof.
  intros lP lx [Pn] [Qm] [Rn] x y H.
  simpl in *. case_eq (beq_nat Rn Qm); intros Hbeq;
    rewrite Hbeq in *.
    case_eq (beq_nat Rn Pn); intros Hbeq2; rewrite Hbeq2 in *;
      simpl in *;
      unfold is_constant in *; destruct H as [z [n Heq]];
      exists z; exists n;
      destruct n; simpl in *; try discriminate;
      simpl in *; inversion Heq;
      destruct n; try discriminate;
      inversion H1. reflexivity.
        do 4 rewrite ind_cond_ind_l2_pre_cons. reflexivity.
        do 4 rewrite ind_cond_ind_l2_pre_cons. reflexivity.

    case_eq (beq_nat Rn Pn); intros Hbeq2; rewrite Hbeq2 in *;
      simpl in *;
      unfold is_constant in *; destruct H as [z [n Heq]];
      exists z; exists n;
      destruct n; simpl in *; try discriminate;
      simpl in *; inversion Heq.
        do 4 rewrite ind_cond_ind_l2_pre_cons. reflexivity.
        do 4 rewrite ind_cond_ind_l2_pre_cons. reflexivity.
        do 4 rewrite ind_cond_ind_l2_pre_cons. reflexivity.
Qed.

Lemma consistent_lP_lx_cons_switch : forall lP lx P Q x y,
  consistent_lP_lx (cons P (cons Q lP)) (cons x (cons y lx)) ->
  consistent_lP_lx (cons Q (cons P lP)) (cons y (cons x lx)).
Proof.
  intros lP lx P Q x y H. unfold consistent_lP_lx in *.
  intros R. unfold consistent_lP_lx_P in *.
  unfold indicies_l2 in *.
  specialize (H R).
  apply is_constant_ind_FOv_switch. assumption.
Qed.

Lemma consistent_lP_lcond_cons_switch : forall lP lx P Q x y,
  consistent_lP_lcond (cons P (cons Q lP)) (cons x (cons y lx)) ->
  consistent_lP_lcond (cons Q (cons P lP)) (cons y (cons x lx)).
Proof.
  intros lP lx P Q x y H. unfold consistent_lP_lcond in *.
  intros R. unfold consistent_lP_lcond_P in *.
  unfold indicies_l2 in *.
  specialize (H R).
  apply is_constant_ind_cond_switch. assumption.
Qed.

Lemma is__constant_l: forall {A : Type} (z:A) n,
  is_constant (constant_l z n).
Proof.
  intros A z n.
  unfold is_constant. exists z. exists n.
  reflexivity.
Qed.

Lemma consistent_lP_lx_cons_rem : forall lP lx P Q x y,
  consistent_lP_lx (cons P (cons Q lP)) (cons x (cons y lx)) ->
  consistent_lP_lx (cons P lP) (cons x lx).
Proof.
  intros until 0. intros H.
  apply consistent_lP_lx_cons_switch in H.
  unfold consistent_lP_lx in *.
  intros R. specialize (H R).
  unfold consistent_lP_lx_P in *.
  unfold indicies_l2 in *.
  simpl in *.
  destruct R as [Rn]. destruct Q as [Qm].
  destruct P as [Pn]. case_eq (beq_nat Rn Qm); intros Hbeq;
    rewrite Hbeq in *. case_eq (beq_nat Rn Pn); intros Hbeq2;
      rewrite Hbeq2 in *. simpl  in *.
      rewrite ind_FOv_ind_l2_pre_cons in H.
      destruct H as [z [n Heq]].
      destruct n. discriminate.
      inversion Heq.
      exists z. exists n. assumption.

      simpl in *.
      rewrite ind_FOv_ind_l2_pre_cons in H.
      destruct H as [z [n Heq]].
      destruct n. discriminate.
      inversion Heq.
      exists z. exists n. assumption.

    case_eq (beq_nat Rn Pn); intros Hbeq2;
      rewrite Hbeq2 in *. simpl  in *.
      rewrite ind_FOv_ind_l2_pre_cons in H.
      destruct H as [z [n Heq]].
      destruct n. discriminate.
      inversion Heq.
      exists z. exists (S n). simpl. rewrite H1.
      reflexivity.

      simpl in *.
      rewrite ind_FOv_ind_l2_pre_cons in H.
      destruct H as [z [n Heq]].
      rewrite Heq. apply is__constant_l.
Qed.

Lemma consistent_lP_lcond_cons_rem : forall lP lcond P Q x y,
  consistent_lP_lcond (cons P (cons Q lP)) (cons x (cons y lcond)) ->
  consistent_lP_lcond (cons P lP) (cons x lcond).
Proof.
  intros until 0. intros H.
  apply consistent_lP_lcond_cons_switch in H.
  unfold consistent_lP_lcond in *.
  intros R. specialize (H R).
  unfold consistent_lP_lcond_P in *.
  unfold indicies_l2 in *.
  simpl in *.
  destruct R as [Rn]. destruct Q as [Qm].
  destruct P as [Pn]. case_eq (beq_nat Rn Qm); intros Hbeq;
    rewrite Hbeq in *. case_eq (beq_nat Rn Pn); intros Hbeq2;
      rewrite Hbeq2 in *. simpl  in *.
      rewrite ind_cond_ind_l2_pre_cons in H.
      destruct H as [z [n Heq]].
      destruct n. discriminate.
      inversion Heq.
      exists z. exists n. assumption.

      simpl in *.
      rewrite ind_cond_ind_l2_pre_cons in H.
      destruct H as [z [n Heq]].
      destruct n. discriminate.
      inversion Heq.
      exists z. exists n. assumption.

    case_eq (beq_nat Rn Pn); intros Hbeq2;
      rewrite Hbeq2 in *. simpl  in *.
      rewrite ind_cond_ind_l2_pre_cons in H.
      destruct H as [z [n Heq]].
      destruct n. discriminate.
      inversion Heq.
      exists z. exists (S n). simpl. rewrite H1.
      reflexivity.

      simpl in *.
      rewrite ind_cond_ind_l2_pre_cons in H.
      destruct H as [z [n Heq]].
      rewrite Heq. apply is__constant_l.
Qed.

Lemma consistent_lP_lcond_cons_cons : forall lP lcond P cond,
  consistent_lP_lcond (cons P (cons P lP)) (cons cond (cons cond lcond)) ->
  consistent_lP_lcond (cons P lP) (cons cond lcond).
Proof.
  intros. simpl in *. intros Q. specialize (H Q).
  unfold indicies_l2 in *. simpl in *. destruct P as [Pn];
  destruct Q as [Qm]. unfold consistent_lP_lcond_P in *.
  unfold indicies_l2 in *. simpl in*. case_eq (beq_nat Qm Pn);
    intros Hbeq; rewrite Hbeq in *.
    simpl in *. unfold is_constant in *.
    destruct H as [beta [n Heq]]. destruct n.
      simpl in *. discriminate. simpl in *.
    inversion Heq. exists beta. exists n.
    rewrite ind_cond_ind_l2_pre_cons in H1. assumption.

    rewrite ind_cond_ind_l2_pre_cons in H. assumption.
Qed.

Lemma consistent_lP_lx_cons_cons : forall lP lcond P cond,
  consistent_lP_lx (cons P (cons P lP)) (cons cond (cons cond lcond)) ->
  consistent_lP_lx (cons P lP) (cons cond lcond).
Proof.
  intros. simpl in *. intros Q. specialize (H Q).
  unfold indicies_l2 in *. simpl in *. destruct P as [Pn];
  destruct Q as [Qm]. unfold consistent_lP_lx_P in *.
  simpl in *. unfold indicies_l2 in *. simpl in *. case_eq (beq_nat Qm Pn);
    intros Hbeq; rewrite Hbeq in *.
    simpl in *. unfold is_constant in *.
    destruct H as [beta [n Heq]]. destruct n.
      simpl in *. discriminate. simpl in *.
    inversion Heq. exists beta. exists n.
    rewrite ind_FOv_ind_l2_pre_cons in H1. assumption.

    rewrite ind_FOv_ind_l2_pre_cons in H. assumption.
Qed.

Lemma rep_pred__l_consistent: forall lP lcond lx alpha P cond x,
  is_unary_predless_l lcond = true ->
  is_unary_predless cond = true ->
  consistent_lP_lcond (cons P lP) (cons cond lcond) ->
  consistent_lP_lx (cons P lP) (cons x lx) ->
  (replace_pred (replace_pred_l alpha lP lx lcond)
                          P x cond) =
  (replace_pred_l (replace_pred alpha P x cond) 
                          lP lx lcond).
Proof.
  induction lP; intros lcond lx alpha P cond x Hun1 Hun2 Hc1 Hc2.
    simpl. reflexivity.

    destruct lx. simpl. reflexivity.
    destruct lcond. simpl. reflexivity.
    simpl.

    pose proof Hc1 as Hc1'. pose proof Hc2 as Hc2'.
    unfold consistent_lP_lcond in Hc1.
    unfold consistent_lP_lx in Hc2.
    simpl in Hun1.
    case_eq (is_unary_predless s); intros Hs; rewrite Hs in *.
      2 : discriminate.
    destruct P as [Pn]. destruct a as [Qm].
    unfold consistent_lP_lx_P in *.
    unfold consistent_lP_lcond_P in *.
    case_eq (beq_nat Pn Qm); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq) in *. 
      specialize (Hc1 (Pred Qm)). specialize (Hc2 (Pred Qm)).
      simpl in Hc1. simpl in Hc2. 
      unfold indicies_l2 in *.
      simpl in Hc1. simpl in Hc2. rewrite <- beq_nat_refl in *.
      simpl in Hc1. simpl in Hc2. unfold is_constant in *.
      destruct Hc1 as [rep [n Heq1]].
      pose proof (constant_l_cons _ _ _ _ Heq1) as Heq1'.
      pose proof (constant_l_cons2 _ _ _ _ _ Heq1) as Heq1''.
      rewrite Heq1' in *. rewrite Heq1'' in *.
      destruct Hc2 as [rep2 [n2 Heq2]]. simpl in Heq2.
      pose proof (constant_l_cons _ _ _ _ Heq2) as Heq2'.
      pose proof (constant_l_cons2 _ _ _ _ _ Heq2) as Heq2''.
      rewrite Heq2' in *. rewrite Heq2'' in *. rewrite IHlP. reflexivity.
      all : try assumption.

        apply consistent_lP_lcond_cons_cons. assumption.
        apply consistent_lP_lx_cons_cons. assumption.

      pose proof (rep_pred_switch (replace_pred_l alpha lP lx lcond)
          f x s cond (Pred Qm) (Pred Pn)) as H.
      simpl in H. rewrite H. rewrite IHlP. reflexivity.
        all : try assumption.
        apply consistent_lP_lcond_cons_rem in Hc1. assumption.
        apply consistent_lP_lx_cons_rem in Hc2. assumption.

        apply beq_nat_false. rewrite beq_nat_comm.
        assumption.
Qed.

Lemma if_then_else_tf : forall (a b : bool),
  (if a then true else b) = false ->
  a = false /\ b = false.
Proof.
  intros. destruct a. discriminate.
  apply conj. reflexivity.
  assumption.
Qed.

(* Lemma ind_pa_vsS_pa_l' : forall {W : Set} lP llv' lv Q x (Iv : FOvariable -> W),
  (forall P, exists n pa,
    ind_pa (indicies_l2 (cons Q lP) P)
           (vsS_pa_l Iv (cons lv llv') (cons x (list_Var (length lP) x))) =
    constant_l pa n) ->
  forall P : predicate, exists n pa,
    ind_pa (indicies_l2 lP P) 
           (vsS_pa_l Iv llv' (list_Var (length lP) x)) =
    constant_l pa n.
Proof.
  intros W lP llv' lv [Qm] x Iv H [Pn].
  unfold indicies_l2 in *. simpl in *.
  destruct (H (Pred Pn)) as [n [pa H2]].
  case_eq (beq_nat Pn Qm); intros Hbeq; rewrite Hbeq in *;
    simpl in *; rewrite ind_pa_pre_cons in H2. destruct n.
      simpl in *. discriminate.
    exists n. exists pa. simpl in H2. inversion H2. reflexivity.

    exists n. exists pa. assumption.
Qed.
 *)

Lemma at_cond_nil : forall a,
  at_cond a nil = (eqFO (Var 1) (Var 1)).
Proof.
  induction a. reflexivity.
  simpl. destruct a; reflexivity.
Qed.

Lemma at_llv_nil : forall a,
  at_llv a nil = nil.
Proof.
  induction a. reflexivity.
  simpl. destruct a; reflexivity.
Qed.


Lemma ind_llv_constant_l: forall l,
  exists n,
  ind_llv l nil = constant_l nil n.
Proof.
  induction l.
    simpl. exists 0. reflexivity.

    simpl. destruct IHl as [n IHl'].
    exists (S n). rewrite IHl'.
    simpl. rewrite at_llv_nil.
    reflexivity.
Qed. 

Lemma ind_llv_nil : forall l,
  is_constant (ind_llv l nil).
Proof.
  intros l. destruct (ind_llv_constant_l l) as [n Heq].
    rewrite Heq. apply is__constant_l.
Qed.

Lemma consistent_lP_llv_nil : forall lP,
  consistent_lP_llv lP nil .
Proof.
  intros lP [Pn].
  unfold consistent_lP_llv_P.
  apply ind_llv_nil.
Qed.

Lemma ind_llv_pre_cons : forall lP P n cond lcond,
  ind_llv (indicies_l2_pre lP P (S n)) (cons cond lcond) =
  ind_llv (indicies_l2_pre lP P n) lcond.
Proof.
  induction lP; intros P n pa lpa.
    simpl. reflexivity.

    destruct a as [Qm]. destruct P as [Pn]. simpl.
    destruct n; destruct lpa;
    case_eq (beq_nat Pn Qm); intros Hbeq; simpl; rewrite IHlP;
      reflexivity.
Qed.

Lemma consistent_lP_llv_cons : forall  llv lP P lv,
  consistent_lP_llv (cons P lP) (cons lv llv) ->
  consistent_lP_llv lP llv.
Proof.
  induction llv; intros lP [Pn] lv H.
    apply consistent_lP_llv_nil.

    unfold consistent_lP_llv in *.
    intros P. specialize (H P).
    unfold consistent_lP_llv_P in *.
    unfold indicies_l2 in *.
    simpl in *. destruct P as [Qm].
    case_eq (beq_nat Qm Pn); intros Hbeq;
      rewrite Hbeq in *.
      simpl in *. unfold is_constant in *.
      destruct H as [l [n H]].
      rewrite ind_llv_pre_cons in H.
      destruct n. simpl in *. discriminate.
      exists l. exists n. simpl in *.
      inversion H. reflexivity.

      rewrite ind_llv_pre_cons in H.
      assumption.
Qed.

Lemma at_cond_vsS_syn_l : forall llv n x,
  at_cond n (vsS_syn_l llv x) =
  fun1 (at_llv n llv) x.
Proof.
  induction llv; intros n x.
    simpl. rewrite at_llv_nil. rewrite at_cond_nil.
    simpl. reflexivity.

    simpl. destruct n. simpl. reflexivity.
    simpl. destruct n. reflexivity.
    apply IHllv.
Qed.

Lemma ind_llv_cond_vsS_syn_l : forall lP llv l n x,
  ind_llv lP llv = constant_l l n ->
  ind_cond lP (vsS_syn_l llv x) = constant_l (fun1 l x) n.
Proof.
  induction lP; intros llv l n x H.
    simpl in *. destruct n. reflexivity.
    simpl in *. discriminate.

    simpl in *. destruct n. discriminate. 
    simpl in *. inversion H as [[H1 H2]].
    rewrite H1 in *.
    rewrite IHlP with (l := l) (n := n).
    rewrite at_cond_vsS_syn_l. rewrite H1.
    reflexivity.

    assumption.
Qed.

Lemma consistent_lP_llv__lcond_P : forall lP llv x P,
  consistent_lP_llv_P lP llv P ->
  consistent_lP_lcond_P lP (vsS_syn_l llv x) P.
Proof.
  intros lP llv x P H.
  unfold consistent_lP_lcond_P in *.
  unfold consistent_lP_llv_P in H. 
  unfold is_constant in H.
  destruct H as [lv [n Heq]].
  apply ind_llv_cond_vsS_syn_l with (x := x) in Heq.
  rewrite Heq. apply is__constant_l.
Qed.

Lemma consistent_lP_llv__lcond: forall lP llv x,
  consistent_lP_llv lP llv ->
  consistent_lP_lcond lP (vsS_syn_l llv x).
Proof.
  intros lP llv x H P.
  apply consistent_lP_llv__lcond_P. apply H.
Qed.

Lemma consistent_lP_llv__lcond_cons: forall lP llv lv P x,
  consistent_lP_llv (cons P lP) (cons lv llv) ->
  consistent_lP_lcond (cons P lP) (cons (fun1 lv x) (vsS_syn_l llv x)).
Proof.
  intros. apply (consistent_lP_llv__lcond _ _ x) in H. simpl in H. assumption.
Qed.

Fixpoint ex_ind_exceed l n : bool :=
  match l with
  | nil => false  
  | cons m l' => if Nat.leb m n then ex_ind_exceed l' n
                 else true
  end.

Lemma length_constant_l : forall {A : Type} n (a : A),
  length (constant_l a n) = n.
Proof.
  intros A; induction n; intros a. reflexivity.
  simpl. rewrite IHn. reflexivity.
Qed.

Fixpoint is_in_nat n l : bool :=
  match l with 
  | nil => false
  | cons m l' => if beq_nat n m then true else is_in_nat n l'
  end.

Lemma at_FOv_constant_l : forall n l2 m x,
  Nat.leb m (length l2) = true ->
  ~ m = 0 ->
  l2 = constant_l x n ->
  at_FOv m l2 = x.
Proof.
  induction n; intros l2 m x Hleb Hneq Hcon.
    simpl in *. rewrite Hcon in *. simpl in *.
    rewrite leb_beq_zero in Hleb. rewrite (beq_nat_true _ _ Hleb) in Hneq.
    contradiction (Hneq eq_refl).

    simpl in *. rewrite Hcon. destruct m. contradiction (Hneq eq_refl).
    simpl. destruct m. reflexivity. 
    rewrite Hcon in Hleb.
    assert (~ S m = 0) as Hneq2.
      intros. discriminate.
    apply (IHn (constant_l x n) (S m) x Hleb Hneq2 eq_refl).
Qed.

Lemma constant_l_ind_FOv : forall l1 n l2 a,
  is_in_nat 0 l1 = false ->
   l2 = constant_l a n ->
  ex_ind_exceed l1 (length l2) = false ->
  exists m,
    ind_FOv l1 l2 = constant_l a m.
Proof.
  induction l1; intros n l2 x Hin Hcon Hex.
    simpl in *. exists 0. reflexivity.

    simpl in *. destruct a. discriminate.
    destruct l2. simpl in *. discriminate.
    simpl. destruct a. simpl in *.
    destruct l1. simpl. exists 1. destruct n. discriminate.
       simpl in *. inversion Hcon as [[H1 H2]].
       reflexivity.
    destruct n0. simpl in *. discriminate.
    destruct (IHl1 n (cons f l2) x Hin Hcon Hex) as [m Heq].  
    exists (S m). destruct n. discriminate.
    rewrite Heq.
    simpl in Hcon. inversion Hcon as [[Ha Hb]]. reflexivity.

    case_eq (Nat.leb (S (S a)) (length (cons f l2))); intros Hleb;  
      rewrite Hleb in *. 2 : discriminate.
    destruct (IHl1 n (cons f l2) x Hin Hcon Hex) as [m Heq].
    destruct n. discriminate.
    rewrite Heq. exists (S m). rewrite at_FOv_constant_l with (n := n) (x := x).
    reflexivity.

      simpl in *. assumption.
      intros H. discriminate.
      inversion Hcon. reflexivity.
Qed.

Lemma is_constant_ind_FOv : forall l1 l2,
  is_in_nat 0 l1 = false ->
  is_constant l2 ->
  ex_ind_exceed l1 (length l2) = false ->
  is_constant (ind_FOv l1 l2).
Proof.
  intros l1 l2 Hin Hcon Hex. unfold is_constant in Hcon.
  destruct Hcon as [x [n Heq]].
  destruct (constant_l_ind_FOv l1 n l2 x Hin Heq Hex) as [m Heq'].
  rewrite Heq'. apply is__constant_l.
Qed.

Lemma is_in_nat_0_ind_l2_pre : forall lP P  m,
  is_in_nat 0 (indicies_l2_pre lP P m) = false ->
  is_in_nat 0 (indicies_l2_pre lP P (S m)) = false.
Proof.
  induction lP; intros [Pn] m H.
    simpl in *. reflexivity.

    simpl in *. destruct a as [Qm].
    case_eq (beq_nat Pn Qm); intros Hbeq;
      rewrite Hbeq in *;
      simpl in *; apply IHlP; assumption.
Qed.

Lemma is_in_nat_ind_l2 : forall lP P,
is_in_nat 0 (indicies_l2 lP P) = false.
Proof.
  induction lP; intros P; unfold indicies_l2 in *.
    reflexivity.

    simpl. destruct P as [Pn]; destruct a as [Qm].    
    case_eq (beq_nat Pn Qm); intros Hbeq.
      simpl. apply is_in_nat_0_ind_l2_pre. apply IHlP.

      apply is_in_nat_0_ind_l2_pre. apply IHlP.
Qed.

Lemma ex_ind_exceed_ind_l2_pre_suc : forall lP P n m,
  ex_ind_exceed (indicies_l2_pre lP P (S n)) (S m) =
  ex_ind_exceed (indicies_l2_pre lP P n) m.
Proof.
  induction lP; intros [Pn] n m.
    simpl. reflexivity.
  
    simpl. destruct a as [Qm].
    case_eq (beq_nat Pn Qm); intros Hbeq.
      remember (S (S n)) as NN.
      remember (S n) as N.
      simpl. rewrite HeqNN. simpl.
      case_eq (Nat.leb N m); intros Hleb.
        apply IHlP. reflexivity.

      apply IHlP.
Qed.

Lemma ex_ind_exceed_ind_l2 : forall lP P n,
  Nat.leb (length lP) n = true ->
  ex_ind_exceed (indicies_l2 lP P) n = false.
Proof.
  induction lP; intros P n Hleb.
    simpl in *. reflexivity.

    simpl in *. destruct n. discriminate.
    unfold indicies_l2. simpl. destruct P as [Pn].
    destruct a as [Qm]. case_eq (beq_nat Pn Qm); intros Hbeq;
      simpl; rewrite ex_ind_exceed_ind_l2_pre_suc;
      apply IHlP; assumption.
Qed.

Lemma consistent_lP_lx_constant_l : forall lP n x,
  Nat.leb (length lP) n = true ->
consistent_lP_lx lP (constant_l x n).
Proof.
  intros lP n x H P.
  unfold consistent_lP_lx_P.
  apply is_constant_ind_FOv.
    apply is_in_nat_ind_l2.
    apply is__constant_l.
    rewrite length_constant_l.
    apply ex_ind_exceed_ind_l2.
    assumption.
Qed.

Lemma constant_l_list_Var : forall n x,
  list_Var n x = constant_l x n.
Proof.
  induction n; intros x.
    simpl. reflexivity.

    simpl. rewrite IHn.
    reflexivity.
Qed.



(* --- *)

Fixpoint at_gen {A : Type} {a : A} (n : nat) (l : list A) : A :=
  match n, l with 
  | 0, _ => a
  | _, nil => a
  | 1, (cons a l) => a
  | (S m), (cons _ l) => @at_gen A a m l
  end.

Fixpoint ind_gen {A : Type} {a : A} (l : list nat) (lx : list A) : list A :=
  match l with
  | nil => nil
  | cons n l' => cons (@at_gen A a n lx) (@ind_gen A a l' lx)
  end.

Definition consistent_lP_lpa_P {W : Set} {pa} lP lpa P : Prop :=
  is_constant (@ind_gen (W -> Prop) pa (indicies_l2 lP P) lpa).

Definition consistent_lP_lpa {W : Set} {pa} lP lpa : Prop :=
  forall P, @consistent_lP_lpa_P W pa lP lpa P.


Lemma ind_gen_pre_cons : forall {A : Type} lP P n (pa pa2 : A) lpa,
  @ind_gen A pa2 (indicies_l2_pre lP P (S n)) (cons pa lpa) =
  @ind_gen A pa2 (indicies_l2_pre lP P n) lpa.
Proof.
  induction lP; intros P n pa lpa.
    simpl. reflexivity.

    destruct a as [Qm]. destruct P as [Pn]. simpl.
    destruct n; intros lpa2;
    case_eq (beq_nat Pn Qm); intros Hbeq; simpl; try (rewrite IHlP;
      reflexivity).
Qed.

Lemma consistent_lP_lpa_P_cons_rem : forall lP P Q W lpa pa1 pa0,
  @consistent_lP_lpa_P W pa0 (cons P lP) (cons pa1 lpa) Q ->
  @consistent_lP_lpa_P W pa0 lP lpa Q.
Proof.
  unfold consistent_lP_lpa_P.
  unfold indicies_l2.
  intros lP [Pn] [Qm] W lpa pa1 p0.
  simpl.
  case_eq (beq_nat Qm Pn); intros Hbeq. simpl.
    rewrite ind_gen_pre_cons. unfold is_constant.
    intros [pa2 [n H]]. destruct n. discriminate.
    simpl in H. inversion H as [H'].
    exists pa2. exists n. assumption.

    rewrite ind_gen_pre_cons. intros. assumption.
Qed.

Lemma consistent_lP_lpa_cons_rem : forall lP P W lpa pa1 pa0,
  @consistent_lP_lpa W pa0 (cons P lP) (cons pa1 lpa) ->
  @consistent_lP_lpa W pa0 lP lpa.
Proof.
  unfold consistent_lP_lpa.
  intros until 0. intros H Q.
  specialize (H Q).
  apply consistent_lP_lpa_P_cons_rem in H.
  assumption.
Qed.

Lemma consistent_lP_lpa_vsS_pa_l : forall lP Q (W:Set) (Iv : FOvariable -> W) lv llv x pa0,
  @consistent_lP_lpa _ pa0 (cons Q lP) (vsS_pa_l Iv (cons lv llv) (list_Var (length (cons Q lP)) x)) ->
  @consistent_lP_lpa _ pa0 lP (vsS_pa_l Iv llv (list_Var (length lP) x)).
Proof.
  intros until 0. intros H. simpl in *. apply consistent_lP_lpa_cons_rem in H.
  assumption.
Qed.

(* -- *)

Lemma equiv_new_simpl3_lP : forall lP llv x alpha W Iv Ip Ir pa0,
  length lP = length llv ->
  SOQFree alpha = true ->
  consistent_lP_llv lP llv ->
  @consistent_lP_lpa _ pa0 lP (vsS_pa_l Iv llv (list_Var (length lP) x)) ->
  ex_attached_allFO_llv alpha llv = false ->
  ex_attached_exFO_llv alpha llv = false ->
    SOturnst W Iv (altered_Ip_list Ip (vsS_pa_l Iv llv (list_Var (length lP) x)) lP) Ir alpha <->
    SOturnst W Iv Ip Ir (replace_pred_l alpha lP (list_Var (length lP) x) (vsS_syn_l llv x)).
Proof.
  induction lP; intros llv x alpha W Iv Ip Ir pa0 Hl Hno Hcon Hind Hat1 Hat2.
    simpl in *. destruct llv. simpl. apply bi_refl.
    discriminate.

    simpl. case_eq llv. intros H; rewrite H in *. discriminate.
    intros lv llv' Heq.
    rewrite Heq in Hl. simpl in *. inversion Hl as [H0].
    assert (SOQFree (replace_pred alpha a x (fun1 lv x)) = true) as Hno'.
      apply SOQFree_rep_pred. assumption. apply SOQFree_fun1.
    destruct a as [Qm].
    rewrite rep_pred__l_consistent.
    split; intros HSOt.
      apply (IHlP llv' x _ W Iv Ip Ir pa0).  assumption.  assumption.

        rewrite Heq in Hcon. apply consistent_lP_llv_cons in Hcon.
        assumption.

      intros [Pn]. specialize (Hind (Pred Pn)).
      unfold consistent_lP_lpa_P in *.
      destruct Hind as [pa [ n Heq2]]. case_eq (beq_nat Pn Qm); intros Hbeq;
        rewrite Heq in Heq2;
        unfold indicies_l2 in Heq2; simpl in *.
        rewrite (beq_nat_true _ _ Hbeq) in *.
        rewrite <- beq_nat_refl in Heq2. simpl in Heq2. 
        destruct n. discriminate. simpl  in Heq2.
        inversion Heq2. exists pa. exists n. rewrite ind_gen_pre_cons in H2.
        rewrite H1 in *.  assumption.

        rewrite Hbeq in Heq2. rewrite ind_gen_pre_cons in Heq2.
        exists pa. exists n. assumption.
          rewrite Heq in Hat1. simpl in Hat1. 
          apply if_then_else_tf in Hat1.

          apply ex_attached_allFO_llv_rep_pred. apply no_FOquant_fun1. 
          apply Hat1.

          rewrite Heq in Hat2. simpl in Hat2.
          apply if_then_else_tf in Hat2.

          apply ex_attached_exFO_llv_rep_pred. apply no_FOquant_fun1.
            apply Hat2.

      apply equiv_new_simpl3; try assumption.
        apply SOQFree__P. assumption.

        rewrite Heq in Hat1. simpl in Hat1. 
        apply if_then_else_tf in Hat1. apply Hat1.

        rewrite Heq in Hat2. simpl in Hat2. 
        apply if_then_else_tf in Hat2. apply Hat2.

      apply (IHlP llv' x _ W Iv Ip Ir pa0) in HSOt; try assumption.
      apply equiv_new_simpl3; try assumption.
        apply SOQFree__P. assumption.

        rewrite Heq in Hat1. simpl in Hat1. 
        apply if_then_else_tf in Hat1. apply Hat1.

        rewrite Heq in Hat2. simpl in Hat2. 
        apply if_then_else_tf in Hat2. apply Hat2.

        rewrite Heq in *. clear H. apply consistent_lP_llv_cons in Hcon.
        assumption.

        rewrite Heq in *. apply consistent_lP_lpa_vsS_pa_l in Hind.
        assumption.

        rewrite Heq in Hat1. simpl in Hat1. 
        apply if_then_else_tf in Hat1.

        apply ex_attached_allFO_llv_rep_pred. apply no_FOquant_fun1.
        apply Hat1.

        rewrite Heq in Hat2. simpl in Hat2.
        apply if_then_else_tf in Hat2.
          apply ex_attached_exFO_llv_rep_pred. apply no_FOquant_fun1.
            apply Hat2.

        apply un_predless_l_vsS_syn_l.

        apply un_predless_fun1.

        rewrite Heq in Hcon. apply consistent_lP_llv__lcond_cons. assumption.

        rewrite constant_l_list_Var.
        assert (cons x (constant_l x (length lP)) =
                constant_l x (length (cons (Pred Qm) lP))) as Heq2.
          reflexivity.
        rewrite Heq2. apply consistent_lP_lx_constant_l.

      apply leb_refl.
Qed.


(* Lemma equiv_new_simpl_try3_LP' : forall lP llv x alpha W Iv Ip Ir,
  length lP = length llv ->
  SOQFree alpha = true ->
  consistent_lP_llv lP llv ->
  (forall P, exists n pa, ind_pa (indicies_l2 lP P) 
      (vsS_pa_l Iv llv (list_Var (length lP) x)) = constant_l pa n) ->
  ex_attached_allFO_llv alpha llv = false ->
  ex_attached_exFO_llv alpha llv = false ->
    SOturnst W Iv (altered_Ip_list Ip (vsS_pa_l Iv llv (list_Var (length lP) x)) lP) Ir alpha <->
    SOturnst W Iv Ip Ir (replace_pred_l alpha lP (list_Var (length lP) x) (vsS_syn_l llv x)).
Proof.
  induction lP; intros llv x alpha W Iv Ip Ir Hl Hno Hcon Hind Hat1 Hat2.
    simpl in *. destruct llv. simpl. apply bi_refl.
    discriminate.

    simpl. case_eq llv. intros H; rewrite H in *. discriminate.
    intros lv llv' Heq.
    rewrite Heq in Hl. simpl in *. inversion Hl as [H0].
    assert (SOQFree (replace_pred alpha a x (fun1 lv x)) = true) as Hno'.
      apply SOQFree_rep_pred. assumption. apply SOQFree_fun1.
    destruct a as [Qm].
    rewrite rep_pred__l_consistent.
    split; intros HSOt.
      apply (IHlP llv' x _ W Iv Ip Ir).  assumption.  assumption.

        rewrite Heq in Hcon. apply consistent_lP_llv_cons in Hcon.
        assumption.

      intros [Pn]. specialize (Hind (Pred Pn)).
      destruct Hind as [n Heq2]. case_eq (beq_nat Pn Qm); intros Hbeq;
        rewrite Heq in Heq2;
        unfold indicies_l2 in Heq2; simpl in *.
        rewrite (beq_nat_true _ _ Hbeq) in *.
        rewrite <- beq_nat_refl in Heq2. simpl in Heq2. 
        destruct n. destruct Heq2 as [pa Heq2]. discriminate. simpl in *.
        destruct Heq2 as [pa Heq2].
        inversion Heq2. exists n. rewrite ind_pa_pre_cons in H2.
        exists pa. rewrite H1 in *.  assumption.

        rewrite Hbeq in Heq2. rewrite ind_pa_pre_cons in Heq2.
        exists n. assumption.
          rewrite Heq in Hat1. simpl in Hat1. 
          apply if_then_else_tf in Hat1.

          apply ex_attached_allFO_llv_rep_pred. apply no_FOquant_fun1. 
          apply Hat1.

          rewrite Heq in Hat2. simpl in Hat2.
          apply if_then_else_tf in Hat2.

          apply ex_attached_exFO_llv_rep_pred. apply no_FOquant_fun1.
            apply Hat2.

      apply equiv_new_simpl_try3; try assumption.
        apply SOQFree__P. assumption.

        rewrite Heq in Hat1. simpl in Hat1. 
        apply if_then_else_tf in Hat1. apply Hat1.

        rewrite Heq in Hat2. simpl in Hat2. 
        apply if_then_else_tf in Hat2. apply Hat2.

      apply (IHlP llv' x _ W Iv Ip Ir) in HSOt; try assumption.
      apply equiv_new_simpl_try3; try assumption.
        apply SOQFree__P. assumption.

        rewrite Heq in Hat1. simpl in Hat1. 
        apply if_then_else_tf in Hat1. apply Hat1.

        rewrite Heq in Hat2. simpl in Hat2. 
        apply if_then_else_tf in Hat2. apply Hat2.

        rewrite Heq in *. clear H. apply consistent_lP_llv_cons in Hcon.
        assumption.

        clear H.  apply (ind_pa_vsS_pa_l' lP llv' lv (Pred Qm) x Iv).
        rewrite Heq in *. assumption.

        rewrite Heq in Hat1. simpl in Hat1. 
        apply if_then_else_tf in Hat1.

        apply ex_attached_allFO_llv_rep_pred. apply no_FOquant_fun1.
        apply Hat1.

        rewrite Heq in Hat2. simpl in Hat2.
        apply if_then_else_tf in Hat2.
          apply ex_attached_exFO_llv_rep_pred. apply no_FOquant_fun1.
            apply Hat2.

        apply un_predless_l_vsS_syn_l.

        apply un_predless_fun1.

        rewrite Heq in Hcon. apply consistent_lP_llv__lcond_cons. assumption.

        rewrite constant_l_list_Var.
        assert (cons x (constant_l x (length lP)) =
                constant_l x (length (cons (Pred Qm) lP))) as Heq2.
          reflexivity.
        rewrite Heq2. apply consistent_lP_lx_constant_l.

      apply leb_refl.
Qed.
 *)

Lemma length_FOv_att_P_l : forall lP alpha,
  length lP = length (FOv_att_P_l alpha lP).
Proof.
  induction lP; intros alpha.
    reflexivity.

    simpl. rewrite <- IHlP. reflexivity.
Qed.

Lemma something1: forall lP P alpha,
exists n,
(ind_llv (indicies_l2 lP P)
        (FOv_att_P_l alpha lP)) = constant_l (fun2 alpha P) n.
Proof.
  induction lP; intros [Pn] alpha.
    simpl. exists 0. reflexivity.

    simpl. unfold indicies_l2. simpl.
    destruct a as [Qm].
    case_eq (beq_nat Pn Qm); intros Hbeq; simpl;
      destruct (IHlP (Pred Pn) alpha) as [n H];
      rewrite ind_llv_pre_cons; unfold indicies_l2 in H;
      rewrite H. exists (S n). rewrite (beq_nat_true _ _ Hbeq).
      simpl. reflexivity.

      exists n. reflexivity.
Qed.

Lemma consistent_lP_llv_FOv_att_P_l : forall lP alpha,
  consistent_lP_llv lP (FOv_att_P_l alpha lP).
Proof.
  intros lP alpha P.
  unfold consistent_lP_llv_P.
  unfold is_constant.
  exists (fun2 alpha P). apply something1.
Qed.

Lemma lem1a_pre : forall {W : Set} lP (Iv : FOvariable -> W) alpha y,
forall P : predicate,
exists (n : nat),
  ind_pa (indicies_l2 lP P) (vsS_pa_l Iv (FOv_att_P_l alpha lP) (list_Var (length lP) y)) =
  constant_l (CM_pa2_l_gen Iv (fun2 alpha P) y) n.
Proof.
  intros W. induction lP; intros Iv alpha y [Pn].
    simpl. exists 0. reflexivity.

    simpl. unfold indicies_l2. simpl. destruct a as [Qm].
    case_eq (beq_nat Pn Qm); intros Hbeq;
      simpl; rewrite ind_pa_pre_cons;
      destruct (IHlP Iv alpha y (Pred Pn)) as [n H]; 
      unfold indicies_l2 in H; rewrite H.
      rewrite (beq_nat_true _ _ Hbeq). exists (S n). reflexivity.

      exists n. reflexivity.
Qed.

Lemma lem1a : forall {W : Set} lP (Iv : FOvariable -> W) alpha y,
forall P : predicate,
exists (n : nat) (pa : W -> Prop),
  ind_pa (indicies_l2 lP P) (vsS_pa_l Iv (FOv_att_P_l alpha lP) (list_Var (length lP) y)) =
  constant_l pa n.
Proof.
  intros W lP Iv alpha y P. 
  destruct (lem1a_pre lP Iv alpha y P) as [n H].
  exists n. exists (CM_pa2_l_gen Iv (fun2 alpha P) y).
  rewrite H. reflexivity.
Qed.

Lemma at_pa_gen : forall (W : Set) (l : list (W -> Prop)) n,
  at_pa  n l = @at_gen (W -> Prop) pa_f n l.
Proof.
  induction l; intros n. destruct n; reflexivity.
  destruct n. reflexivity. simpl. destruct n. reflexivity.
  apply IHl. 
Qed.

Lemma ind_pa_gen : forall W l1 l2,
  @ind_pa W l1 l2 = @ ind_gen (W -> Prop) pa_f l1 l2.
Proof.
  induction l1; intros l2. reflexivity.
  simpl. rewrite IHl1. rewrite at_pa_gen. reflexivity.
Qed.

Lemma lem1a_cons : forall lP alpha (W :Set) (Iv : FOvariable -> W) y,
@consistent_lP_lpa W pa_f lP (vsS_pa_l Iv (FOv_att_P_l alpha lP) (list_Var (length lP) y)).
Proof.
  intros until 0. intros P. unfold consistent_lP_lpa_P.
  unfold is_constant. destruct (lem1a lP Iv alpha y P) as [n [pa HH]].
  exists pa. exists n. rewrite ind_pa_gen in HH. assumption.
Qed. 

Lemma alt_alt_list_1' : forall (W : Set) (l : list predicate) (pa_l_hat : nlist (length l)) 
                            (pa_hat : W -> Prop) (P : predicate) (Ip : predicate -> W -> Prop) ,
      exists (pa : W -> Prop) (pa_l : nlist (length l)),
          (altered_Ip (altered_Ip_list Ip (nlist_list (length l) pa_l_hat) l) pa_hat P) 
        = (altered_Ip_list (@altered_Ip W Ip pa P) (nlist_list (length l) pa_l) l).
Proof.
  intros W l.
  induction l.
    intros.
    simpl.
    simpl in pa_l_hat.
    assert (pa_l_hat = niln).
      apply nlist_nil2.
    rewrite H.
    simpl.
    exists pa_hat.
    exists (niln).
    simpl.
    reflexivity.

    intros.
    simpl in pa_l_hat.
    assert (exists (pa : W -> Prop) (pa_l' : nlist (length l)), 
              (pa_l_hat = consn (length l) pa pa_l')).
       apply nlist_cons2.
    destruct H as [pa1 [pa_l1 H]].
    destruct a as [Qm]; destruct P as [Pn].
    case_eq (EqNat.beq_nat Qm Pn).
      intros.
      pose proof ((EqNat.beq_nat_true Qm Pn) H0).
      rewrite <- H1.
      rewrite H.
      simpl nlist_list.
      rewrite altered_Ip_list_cons.
      rewrite altered_Ip_eq.
      specialize (IHl pa_l1 pa_hat (Pred Qm) Ip).
      destruct IHl as [pa2 [pa_l2 IHl']].

      exists pa2.
      exists (consn (length l) pa_hat pa_l2).
      simpl nlist_list.
      rewrite altered_Ip_list_cons.
      rewrite <- IHl'.
      rewrite altered_Ip_eq.
      reflexivity.

      intros.
      pose proof ((EqNat.beq_nat_false Qm Pn) H0).
      rewrite H.
      simpl nlist_list.
      rewrite altered_Ip_list_cons.
      rewrite <- altered_Ip_switch.
      specialize (IHl pa_l1 pa_hat (Pred Pn) Ip).
      destruct IHl as [pa2 [pa_l2 IHl']].
      rewrite IHl'.
      assert (S (length l) = length (cons (Pred Pn) l)).
        simpl; reflexivity.
      rewrite <- altered_Ip_list_cons.
      exists pa2.
      exists (consn (length l) pa1 pa_l2).
      reflexivity.

        exact H1.
Qed.

Lemma altered_Ip_list_tail' : forall (W : Set) (Ip : predicate -> W -> Prop) (P : predicate)
                            (l : list predicate) (pa_l : nlist (length l)) 
                            (pa: W -> Prop),
         altered_Ip_list (altered_Ip Ip pa P) (nlist_list (length l) pa_l) l
            = altered_Ip_list Ip (app (nlist_list (length l) pa_l) (cons pa nil) ) (app l (cons P nil)).
Proof.
  intros.
  induction l.
    simpl.
    simpl length in pa_l.
    assert (pa_l = niln).
      apply nlist_nil2.
    rewrite H.
    simpl.
    reflexivity.

    assert (exists (pa1 : W -> Prop) (pa_l1 : nlist (length l)), 
              (pa_l = consn (length l) pa1 pa_l1)).
      apply nlist_cons2.
    destruct H as [pa1 [pa_l1 H]].
    rewrite H.
    simpl.
    rewrite IHl.
    reflexivity.
Qed.

Lemma altered_Ip_list_app' : forall (W : Set) (Ip : predicate -> W -> Prop) (P : predicate)
                            (l : list predicate) (pa_l : nlist (length l)) 
                            (pa : W -> Prop),
       (altered_Ip_list Ip (app (nlist_list (length l) pa_l) (cons pa nil)) (l ++ P :: nil))
     = (altered_Ip_list (altered_Ip_list Ip (nlist_list 1 (consn 0 pa (niln)))
          (P :: nil)) (nlist_list (length l) pa_l) l).
Proof.
  intros.
  induction l.
    simpl in pa_l.
    assert (pa_l = (niln)).
      apply nlist_nil2.
    rewrite H.
    simpl.
    reflexivity.

    simpl.
    assert (exists (pa1 : W -> Prop) (pa_l1 : nlist (length l)), 
              (pa_l = consn (length l) pa1 pa_l1)).
       apply nlist_cons2.
    destruct H as [pa1 [pa_l1 H]]. 
    rewrite H.
    specialize (IHl pa_l1).
    simpl.
    rewrite IHl.
    simpl.
    reflexivity.
Qed.

Lemma nlist_list_cons' : forall (W : Set) (pa : W -> Prop) (l : list predicate) 
                               (t : nlist (length l)),
      (nlist_list (S (length l) ) (consn (length l) pa t)) 
         = cons pa (nlist_list (length l) t).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma alt_alt_list_2' : forall (W : Set) (Ip : predicate -> W -> Prop) (P : predicate)
                            (l : list predicate) (pa_l_hat : nlist (length l)) 
                            (pa_hat : W -> Prop),
   exists (pa : W -> Prop) (pa_l : nlist (length l)),
     (altered_Ip (altered_Ip_list Ip (nlist_list (length l) pa_l) l) pa P) = 
        (altered_Ip_list (altered_Ip Ip pa_hat P) (nlist_list (length l) pa_l_hat) l).
Proof.
  intros.
  rewrite altered_Ip_list_tail'.
  induction l.
    simpl length in *.
    assert (pa_l_hat = niln).
      apply nlist_nil2.
    rewrite H.
    simpl.
    exists pa_hat.
    exists (niln).
    simpl.
    reflexivity.

    assert (exists (pa1 : W -> Prop) (pa_l1 : nlist (length l)), 
              (pa_l_hat = consn (length l) pa1 pa_l1)).
      apply nlist_cons2.
    destruct H as [pa1 [pa_l1 H']].
    rewrite H'.
    simpl.
    destruct a as [Qm].
    destruct P as [Pn].
    rewrite altered_Ip_list_app'.
    specialize (IHl pa_l1).
    destruct IHl as [pa2 [pa_l2 IHl']].
    case_eq (EqNat.beq_nat Qm Pn).
      intros.
      pose proof ((EqNat.beq_nat_true Qm Pn) H).
      rewrite <- H0.
      assert (nlist_list (length (cons (Pred Pn) nil))
                    (consn (length (nil: list predicate)) pa_hat (niln))
               = cons pa_hat (nlist_list (length (nil:list predicate)) (niln)))
              as list_cons.
        apply nlist_list_cons'.
      simpl length in list_cons.
      rewrite list_cons.
      rewrite altered_Ip_list_cons.
      rewrite altered_Ip_list_app' in IHl'.
      rewrite list_cons in IHl'.
      rewrite altered_Ip_list_cons in IHl'.
      rewrite altered_Ip_list_nil.
      rewrite altered_Ip_list_nil in IHl'.
      rewrite H0.
      rewrite <- IHl'.
      exists pa1. 
      exists (consn (length l) pa2 pa_l2).
      assert ((nlist_list (length (cons (Pred Pn) l)) (consn (length l) pa2 pa_l2))
                 =  cons pa2 (nlist_list (length l) pa_l2) ) as list_cons2.
        apply nlist_list_cons'.
      simpl length in list_cons2.
      rewrite list_cons2.
      rewrite altered_Ip_list_cons.
      reflexivity.

      intros.
      exists pa2.
      exists (consn (length l) pa1 pa_l2).
      assert ((nlist_list (length (cons (Pred Pn) l)) (consn (length l) pa1 pa_l2))
               = cons pa1 (nlist_list (length l) pa_l2)) as list_cons.
        apply nlist_list_cons'.  
      simpl length in list_cons.
      rewrite list_cons.
      rewrite altered_Ip_list_app' in IHl'.
      simpl nlist_list in IHl'.
      rewrite altered_Ip_list_cons in IHl'.
      simpl altered_Ip_list in IHl' at 3.
      rewrite altered_Ip_list_cons.
      assert ((nlist_list (length (cons (Pred Pn) nil)) 
              (consn (length (nil: list predicate)) pa_hat (niln)))
                 = cons pa_hat (nlist_list (length (nil:list predicate)) (niln)))
              as list_cons2.
        apply nlist_list_cons'.
      simpl length in list_cons2.
      rewrite list_cons2.
      rewrite altered_Ip_list_cons.
      unfold nlist_list at 2.
      unfold altered_Ip_list at 3.
      rewrite <- IHl'.
      apply altered_Ip_switch.
      pose proof ((EqNat.beq_nat_false Qm Pn) H).
      unfold not; intros.
      symmetry in H1.
      contradiction.
Qed.

Lemma  nlist_list_closed_SO'  : forall (W : Set) (Iv : FOvariable -> W) 
                           (Ir: W -> W -> Prop) (alpha: SecOrder) (l : list predicate) 
                           (Ip: predicate -> W -> Prop),
     SOturnst W Iv Ip Ir (list_closed_SO alpha l) <->
   forall pa_l : (nlist (length l)),
      SOturnst W Iv (altered_Ip_list Ip (nlist_list (length l) pa_l) l) Ir alpha.
Proof.
  intros W Iv Ir alpha l.
  induction l.
    simpl.
    split.
      intros H pa_l.
      rewrite altered_Ip_list_nil.
      exact H.

      intros H.
      specialize (H (niln)).
      rewrite altered_Ip_list_nil in H.
      exact H.

    intros.
    split.
      intros.
      assert (exists (pa1 : W -> Prop) (pa_l1 : nlist (length l)), 
              (pa_l = consn (length l) pa1 pa_l1)).
         apply nlist_cons2.
      destruct H0 as [pa1 [pa_l1 H0]].
      rewrite H0.
      simpl nlist_list_pa.
      simpl altered_Ip_list.
      assert (exists (pa : W -> Prop) (pa_l : nlist (length l)),
            (altered_Ip (altered_Ip_list Ip (nlist_list (length l) pa_l1) l) pa1 a) = 
            (altered_Ip_list (altered_Ip Ip pa a) (nlist_list (length l) pa_l) l)).
        apply alt_alt_list_1'.
      destruct H1 as [pa2 [pa_l2 H1]].
      rewrite H1.
      apply IHl.
      simpl list_closed_SO in H.
      rewrite SOturnst_allSO in H.
      specialize (H pa2).
      exact H.

      intros.
      simpl list_closed_SO.
      rewrite SOturnst_allSO.
      intros.
      apply IHl.
      intros.
      simpl in H.
      assert (exists (pred_asgmt1 : W -> Prop) (pa_l1 : nlist (length l)),
           (altered_Ip (altered_Ip_list Ip (nlist_list (length l) pa_l1) l)
              pred_asgmt1 a) = 
           (altered_Ip_list (altered_Ip Ip pred_asgmt a) 
              (nlist_list (length l) pa_l) l)).
         apply alt_alt_list_2'.
       destruct H0 as [pred_asgmt1 [pa_l1 H0]].
       rewrite <- H0.
       specialize (H (consn (length l) pred_asgmt1 pa_l1)).
       apply H.
Qed.


Lemma length_vsS_pa_l : forall {W : Set} lP (Iv : FOvariable -> W) y alpha,
length (vsS_pa_l Iv (FOv_att_P_l alpha lP) (list_Var (length lP) y)) = length lP.
Proof.
  intros W; induction lP; intros Iv y alpha.
    reflexivity.

    simpl. rewrite IHlP. reflexivity.
Qed.

Lemma SOQFree_rename_FOv : forall alpha x y,
  SOQFree alpha = true ->
  SOQFree (rename_FOv alpha x y) = true.
Proof.
  induction alpha; intros [xn] [ym] H.
    destruct f as [zn]. simpl.
    case_eq (beq_nat xn zn); intros Hbeq;
      destruct p; reflexivity.

    destruct f as [z1]; destruct f0 as [z2].
    simpl in *. case_eq (beq_nat xn z1);
      intros Hbeq; case_eq (beq_nat xn z2); intros Hbeq2;
      reflexivity.

    destruct f as [z1]; destruct f0 as [z2].
    simpl in *. case_eq (beq_nat xn z1);
      intros Hbeq; case_eq (beq_nat xn z2); intros Hbeq2;
      reflexivity.

    destruct f as [zn]. simpl in *. specialize (IHalpha (Var xn) (Var ym)).
    case_eq (beq_nat zn xn);
      intros Hbeq; simpl; apply IHalpha; assumption.

    destruct f as [zn]. simpl in *. specialize (IHalpha (Var xn) (Var ym)).
    case_eq (beq_nat zn xn);
      intros Hbeq; simpl; apply IHalpha; assumption.

    simpl in *. apply (IHalpha (Var xn) (Var ym)). assumption.

    simpl in *. case_eq (SOQFree alpha1); intros H2;
      rewrite H2 in *. 2 : discriminate.
      unfold rename_FOv in *.
      rewrite (IHalpha1 (Var xn) (Var ym)).
      apply (IHalpha2 (Var xn) (Var ym)).
      all : try assumption. reflexivity.

    simpl in *. case_eq (SOQFree alpha1); intros H2;
      rewrite H2 in *. 2 : discriminate.
      unfold rename_FOv in *.
      rewrite (IHalpha1 (Var xn) (Var ym)).
      apply (IHalpha2 (Var xn) (Var ym)).
      all : try assumption. reflexivity.

    simpl in *. case_eq (SOQFree alpha1); intros H2;
      rewrite H2 in *. 2 : discriminate.
      unfold rename_FOv in *.
      rewrite (IHalpha1 (Var xn) (Var ym)).
      apply (IHalpha2 (Var xn) (Var ym)).
      all : try assumption. reflexivity.
Qed.

Lemma SOQFree_newnew_pre : forall l1 l2 alpha,
  SOQFree alpha = true ->
  SOQFree (newnew_pre alpha l1 l2) = true.
Proof.
  induction l1; intros l2 alpha H.
    assumption.

    simpl. destruct l2. assumption.
    apply SOQFree_rename_FOv. apply IHl1.
    assumption.
Qed.

Lemma ex_att_allFO_lv_implSO : forall lv alpha beta,
  ex_attached_allFO_lv alpha lv = false ->
  ex_attached_allFO_lv beta lv = false ->
  ex_attached_allFO_lv (implSO alpha beta) lv = false.
Proof.
  induction lv; intros alpha beta H1 H2.
    reflexivity.

    simpl in *. apply if_then_else_tf in H1.
    apply if_then_else_tf in H2.
    destruct H1 as [H1a H1b]. destruct H2 as [H2a H2b].
    rewrite IHlv. rewrite H1a. rewrite H2a.
    reflexivity. all : assumption.
Qed.

Lemma ex_att_exFO_lv_implSO : forall lv alpha beta,
  ex_attached_exFO_lv alpha lv = false ->
  ex_attached_exFO_lv beta lv = false ->
  ex_attached_exFO_lv (implSO alpha beta) lv = false.
Proof.
  induction lv; intros alpha beta H1 H2.
    reflexivity.

    simpl in *. apply if_then_else_tf in H1.
    apply if_then_else_tf in H2.
    destruct H1 as [H1a H1b]. destruct H2 as [H2a H2b].
    rewrite IHlv. rewrite H1a. rewrite H2a.
    reflexivity. all : assumption.
Qed.

Lemma ex_att_exFO_llv_implSO : forall llv alpha beta,
  ex_attached_exFO_llv alpha llv = false ->
  ex_attached_exFO_llv beta llv = false ->
  ex_attached_exFO_llv (implSO alpha beta) llv = false.
Proof.
  induction llv; intros alpha beta H1 H2.
    simpl in *. reflexivity.

    simpl in *. apply if_then_else_tf in H1.
    apply if_then_else_tf in H2.
    destruct H1. destruct H2.
    rewrite ex_att_exFO_lv_implSO.
    apply IHllv. all : assumption.
Qed.

Lemma ex_att_allFO_llv_implSO : forall llv alpha beta,
  ex_attached_allFO_llv alpha llv = false ->
  ex_attached_allFO_llv beta llv = false ->
  ex_attached_allFO_llv (implSO alpha beta) llv = false.
Proof.
  induction llv; intros alpha beta H1 H2.
    simpl in *. reflexivity.

    simpl in *. apply if_then_else_tf in H1.
    apply if_then_else_tf in H2.
    destruct H1. destruct H2.
    rewrite ex_att_allFO_lv_implSO.
    apply IHllv. all : assumption.
Qed.

Lemma att_exFO_x__llv : forall l alpha,
  (forall x, attached_exFO_x alpha x = false) ->
  ex_attached_exFO_llv alpha l = false.
Proof.
  induction l; intros alpha H.
    simpl. reflexivity.

    simpl. induction a. simpl in *. apply IHl. assumption.
    simpl. rewrite H. assumption.
Qed.

Lemma att_allFO_x__llv : forall l alpha,
  (forall x, attached_allFO_x alpha x = false) ->
  ex_attached_allFO_llv alpha l = false.
Proof.
  induction l; intros alpha H.
    simpl. reflexivity.

    simpl. induction a. simpl in *. apply IHl. assumption.
    simpl. rewrite H. assumption.
Qed.

Lemma lem3 : forall beta rel atm xn P,
  REL rel = true ->
  AT atm = true ->
  SOQFree beta = true ->
  closed_except beta (Var xn) ->
  attached_allFO_x beta (Var xn) = false ->
ex_attached_allFO_lv
     (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)
        (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
        (rev_seq (S (Nat.max (max_FOv (implSO (conjSO rel atm) beta)) xn))
           (length
              (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta))
                 (Var xn))))) (fun2 (conjSO rel atm) P) = false.
Proof.
  intros beta rel atm xn P HREL HAT Hno Hcl Hatt.
  apply want3; try assumption.
  apply is_in_FOvar_l_fun2.
  simpl.
  rewrite att_allFO_x_REL. apply att_allFO_x_AT.
  all : try assumption.
Qed.

Lemma lem3_atm : forall beta atm xn P,
  AT atm = true ->
  SOQFree beta = true ->
  closed_except beta (Var xn) ->
  attached_allFO_x beta (Var xn) = false ->
ex_attached_allFO_lv
     (newnew_pre (instant_cons_empty' atm beta)
        (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn))
        (rev_seq (S (Nat.max (max_FOv (implSO atm beta)) xn))
           (length
              (rem_FOv (FOvars_in (instant_cons_empty' atm beta))
                 (Var xn))))) (fun2 atm P) = false.
Proof.
  intros beta  atm xn P  HAT Hno Hcl Hatt.
  apply want3; try assumption.
  apply is_in_FOvar_l_fun2.
  simpl. apply att_allFO_x_AT.
  all : try assumption.
Qed.

Lemma att_exFO_instant_cons_empty'_pre : forall beta P x y ,
  attached_exFO_x beta y = false ->
attached_exFO_x
  (replace_pred beta P x (negSO (eqFO x x))) y = false.
Proof.
  induction beta; intros [Pn] [ym] [xn] Hat.
    destruct p as [Qm]; destruct f as [zn]. simpl in *.
    rewrite <- beq_nat_refl. case_eq (beq_nat Pn Qm);
      intros Hbeq; reflexivity.

    destruct f as [z1]; destruct f0 as [z2].
    reflexivity.

    destruct f as [z1]; destruct f0 as [z2].
    reflexivity.

    destruct f as [zn]. simpl in *.
    apply IHbeta. assumption.

    destruct f as [zn]. simpl in *.
    case_eq (beq_nat xn zn); intros Hbeq;
      rewrite Hbeq in *. discriminate.
      apply IHbeta. assumption.

    simpl in *. apply IHbeta; assumption.

    simpl in *. case_eq (attached_exFO_x beta1 (Var xn));
      intros H1; rewrite H1 in *. discriminate.
      rewrite IHbeta1. apply IHbeta2. all : try assumption.

    simpl in *. case_eq (attached_exFO_x beta1 (Var xn));
      intros H1; rewrite H1 in *. discriminate.
      rewrite IHbeta1. apply IHbeta2. all : try assumption.

    simpl in *. case_eq (attached_exFO_x beta1 (Var xn));
      intros H1; rewrite H1 in *. discriminate.
      rewrite IHbeta1. apply IHbeta2. all : try assumption.

    destruct p as [Qm]. simpl in *.
    case_eq (beq_nat Pn Qm); intros Hbeq; simpl;
      apply IHbeta; assumption.

    destruct p as [Qm]. simpl in *.
    case_eq (beq_nat Pn Qm); intros Hbeq; simpl;
      apply IHbeta; assumption.
Qed.


Lemma att_exFO_instant_cons_empty'_pre_l : forall l beta x,
  attached_exFO_x beta x = false ->
attached_exFO_x
  (replace_pred_l beta l
     (nlist_list (length l) (nlist_Var1 _))
     (nlist_list (length l) (nlist_empty _))) x = false.
Proof.
  induction l; intros beta x H.
    simpl. assumption.

    simpl. apply att_exFO_instant_cons_empty'_pre.
    apply IHl. assumption.
Qed.

Lemma att_exFO_instant_cons_empty' : forall beta alpha x,
  attached_exFO_x beta x = false ->
  attached_exFO_x (instant_cons_empty' alpha beta) x = false.
Proof.
  intros beta alpha x H.
  unfold instant_cons_empty'.
  apply att_exFO_instant_cons_empty'_pre_l.
  assumption.
Qed.

Lemma rename_FOv_att_exFO: forall alpha x y z,
  attached_exFO_x alpha x = false ->
  ~z = x ->
  attached_exFO_x (rename_FOv alpha y z) x = false.
Proof.
  induction alpha; intros [xn] [ym] [zn] Hat Hneq.
    simpl in *. destruct f as [un].   
    case_eq (beq_nat ym un); intros Hbeq;
      reflexivity.

    destruct f as [un]. destruct f0 as [wn].
    simpl in *. case_eq (beq_nat ym un); intros Hbeq;
      case_eq (beq_nat ym wn); intros Hbeq2;
        reflexivity.

    destruct f as [un]. destruct f0 as [wn].
    simpl in *. case_eq (beq_nat ym un); intros Hbeq;
      case_eq (beq_nat ym wn); intros Hbeq2;
        reflexivity.

    destruct f as [un]. simpl in *.
    case_eq (beq_nat un ym); intros Hbeq.
      simpl.
      apply (IHalpha (Var xn) (Var ym) (Var zn)).
      all : try assumption.
      simpl.
      apply (IHalpha (Var xn) (Var ym) (Var zn)); assumption.

    destruct f as [un]. simpl in *.
    case_eq (beq_nat xn un); intros Hbeq3;
      rewrite Hbeq3 in *. discriminate.
    case_eq (beq_nat un ym); intros Hbeq.
      simpl. rewrite beq_nat_comm.
      rewrite FOvar_neq. unfold rename_FOv in IHalpha.
      apply (IHalpha (Var xn) (Var ym) (Var zn)).
      all : try assumption.

      simpl. rewrite Hbeq3.
      apply (IHalpha (Var xn) (Var ym) (Var zn)); assumption.

    simpl in *. apply (IHalpha (Var xn) (Var ym) (Var zn)); assumption.

    simpl in *. case_eq (attached_exFO_x alpha1 (Var xn));
      intros Hat2; rewrite Hat2 in *. discriminate.
    unfold rename_FOv in *.
    rewrite (IHalpha1 (Var xn) (Var ym) (Var zn)).
    apply (IHalpha2 (Var xn) (Var ym) (Var zn)).
    all : try assumption.

    simpl in *. case_eq (attached_exFO_x alpha1 (Var xn));
      intros Hat2; rewrite Hat2 in *. discriminate.
    unfold rename_FOv in *.
    rewrite (IHalpha1 (Var xn) (Var ym) (Var zn)).
    apply (IHalpha2 (Var xn) (Var ym) (Var zn)).
    all : try assumption.

    simpl in *. case_eq (attached_exFO_x alpha1 (Var xn));
      intros Hat2; rewrite Hat2 in *. discriminate.
    unfold rename_FOv in *.
    rewrite (IHalpha1 (Var xn) (Var ym) (Var zn)).
    apply (IHalpha2 (Var xn) (Var ym) (Var zn)).
    all : try assumption.

    destruct p; simpl in *. apply (IHalpha (Var xn) (Var ym) (Var zn));
    assumption.

    destruct p; simpl in *. apply (IHalpha (Var xn) (Var ym) (Var zn));
    assumption.
Qed.


Lemma aa23_EX : forall l alpha x n,
  ~ l = nil ->
  x_occ_in_alpha alpha x = true ->
  is_in_FOvar x l = false ->
  attached_exFO_x alpha x = false ->
  Nat.leb (max_FOv alpha) n = true ->
  attached_exFO_x (newnew_pre alpha l
    (rev_seq (S n) (length l))) x = false.
Proof.
  induction l; intros alpha x n Hnil Hocc Hin Hat Hleb.
    simpl. assumption.

    simpl. simpl in Hin. destruct x as [xn].
    destruct a as [ym]. case_eq (beq_nat xn ym);
      intros Hbeq; rewrite Hbeq in *. discriminate.
    case_eq l. intros Hnil2. rewrite Hnil2 in *. simpl.
      rewrite <- plus_n_O.
      rewrite <- rename_FOv__n.
      apply rename_FOv_att_exFO; try assumption.
      apply x_occ_in_alpha_max_FOv_gen in Hleb.
      intros H. rewrite H in *. rewrite Hleb in *.
      discriminate.

      intros z l' Heq. assert (~ l = nil) as HH.
        intros HH2. rewrite HH2 in Heq. discriminate.
      specialize (IHl _ _ n HH Hocc Hin Hat Hleb).
      apply rename_FOv_att_exFO. rewrite <- Heq. apply IHl.
      rewrite <- Heq.
      intros H. inversion H as [H'].
      rewrite <- H' in Hocc.
      rewrite x_occ_in_alpha_max_FOv_gen in Hocc.
        discriminate.
      apply (leb_trans _ n). assumption.
      apply leb_plus_r. apply leb_refl.
Qed.

Lemma is_in_FOvar_att_exFO_x : forall alpha x,
  is_in_FOvar x (FOvars_in alpha) = false ->
  attached_exFO_x alpha x = false.
Proof.
  induction alpha; intros [xn] H; try reflexivity.

    destruct f as [ym]. simpl in *.
    case_eq (beq_nat xn ym); intros Hbeq;
      rewrite Hbeq in *. discriminate.
      apply IHalpha. assumption.

    destruct f as [ym]. simpl in *.
    case_eq (beq_nat xn ym); intros Hbeq;
      rewrite Hbeq in *. discriminate.
      apply IHalpha. assumption.

    simpl in *. apply IHalpha; assumption.

    simpl in *. rewrite is_in_FOvar_app in H.
    case_eq (is_in_FOvar (Var xn) (FOvars_in alpha1));
      intros Hin; rewrite Hin in *. discriminate.
    rewrite IHalpha1. apply IHalpha2.
    all : try assumption.

    simpl in *. rewrite is_in_FOvar_app in H.
    case_eq (is_in_FOvar (Var xn) (FOvars_in alpha1));
      intros Hin; rewrite Hin in *. discriminate.
    rewrite IHalpha1. apply IHalpha2.
    all : try assumption.

    simpl in *. rewrite is_in_FOvar_app in H.
    case_eq (is_in_FOvar (Var xn) (FOvars_in alpha1));
      intros Hin; rewrite Hin in *. discriminate.
    rewrite IHalpha1. apply IHalpha2.
    all : try assumption.

    destruct p. simpl in *.
    apply IHalpha. assumption.

    destruct p. simpl in *.
    apply IHalpha. assumption.
Qed.

Lemma want15_EX : forall beta xn a alpha,
  free_FO beta a = false ->
  is_in_FOvar a (FOvars_in beta) = true ->
  SOQFree beta = true ->
  attached_exFO_x alpha (Var xn) = false ->
  ~ (Var xn) = a ->
  is_in_FOvar a (FOvars_in alpha) = true ->
  is_in_FOvar a (FOvars_in
    (newnew_pre (instant_cons_empty' alpha beta)
       (rem_FOv (FOvars_in (instant_cons_empty' alpha beta)) (Var xn))
       (rev_seq (S (Nat.max (Nat.max (max_FOv alpha) (max_FOv beta)) xn))
          (length
             (rem_FOv (FOvars_in (instant_cons_empty' alpha beta)) (Var xn))))))
      = false.
Proof.
  intros beta xn [ym] alpha Hfree Hin3 Hno Hat Hneq Hin2.
  apply want16; try assumption.
    apply free_FO_instant_cons_empty'_f; try assumption.

    apply leb_max_suc3.
    apply leb_max_suc3.
    apply want19. assumption.
    apply kk1; assumption.
Qed.

Lemma want14_EX : forall l beta xn a alpha,
  SOQFree beta = true ->
  free_FO beta a = false ->
  ~ Var xn = a ->
  is_in_FOvar a (FOvars_in beta) = true ->
  is_in_FOvar_l l (FOvars_in alpha) = true ->
  attached_exFO_x alpha (Var xn) = false ->
  is_in_FOvar a (FOvars_in alpha) = true ->
 attached_exFO_x
    (newnew_pre (instant_cons_empty' alpha beta)
       (rem_FOv (FOvars_in (instant_cons_empty' alpha beta)) (Var xn))
       (rev_seq (S (Nat.max (Nat.max (max_FOv alpha) (max_FOv beta)) xn))
          (length
             (rem_FOv (FOvars_in (instant_cons_empty' alpha beta)) (Var xn)))))
    a = false.
Proof.
  intros l beta xn [ym] alpha Hno Hfree Hin Hneq Hin3 Hat Hin2.
  apply is_in_FOvar_att_exFO_x.
  apply want15_EX; try assumption.
Qed.

Lemma aa24_EX : forall l alpha beta ym n,
  is_in_FOvar (Var ym) (FOvars_in alpha) = true ->
  is_in_FOvar (Var ym) (FOvars_in beta) = false ->
  is_in_FOvar (Var ym) l = false ->
  Nat.leb ym n = true ->
attached_exFO_x
    (newnew_pre (instant_cons_empty' alpha beta) l
       (rev_seq (S n) (length l))) (Var ym) = false.
Proof.
  induction l; intros alpha beta ym n H1 H2 H3 Hleb.
    simpl. apply att_exFO_instant_cons_empty'.
    apply is_in_FOvar_att_exFO_x. assumption.

    simpl.
    case_eq (beq_nat (S (n + length l)) ym); intros Hbeq2.
      rewrite <- (beq_nat_true _ _ Hbeq2) in Hleb.
      rewrite <- plus_Sn_m in Hleb.
      rewrite leb_suc_f2 in Hleb. discriminate.

      apply rename_FOv_att_exFO.
      apply IHl; try assumption.
      simpl in H3. destruct a as [xn].
      case_eq (beq_nat ym xn); intros Hbeq; 
        rewrite Hbeq in *. discriminate.
      assumption.

      apply beq_nat_false_FOv. assumption.
Qed.

Lemma want3_EX : forall l alpha beta xn,
  SOQFree beta = true ->
  is_in_FOvar_l l (FOvars_in alpha) = true ->
  attached_exFO_x alpha (Var xn) = false ->
  closed_except beta (Var xn) ->
  attached_exFO_x beta (Var xn) = false ->
ex_attached_exFO_lv
  (newnew_pre (instant_cons_empty' alpha beta)
     (rem_FOv (FOvars_in (instant_cons_empty' alpha beta)) (Var xn))
     (rev_seq (S (Nat.max (max_FOv (implSO alpha beta)) xn))
        (length
           (rem_FOv (FOvars_in (instant_cons_empty' alpha beta))
              (Var xn))))) l = false.
Proof.
   induction l; intros alpha beta xn Hno Hin Hat Hcl Hat2.
    simpl. reflexivity.

    simpl in Hin. case_eq (is_in_FOvar a (FOvars_in alpha)); intros Hin2;
        rewrite Hin2 in *. 2 : discriminate.
    simpl.
    destruct a as [ym]. case_eq (beq_nat xn ym); intros Hbeq.
      rewrite <- (beq_nat_true _ _ Hbeq).
    case_eq (rem_FOv (FOvars_in (instant_cons_empty' alpha beta)) (Var xn)).
      intros H. simpl.
      rewrite att_exFO_instant_cons_empty'. 2 : assumption.
      specialize (IHl alpha beta xn).
      rewrite H in IHl. simpl in *. apply IHl.
      all : try assumption.
    intros y l' Heq. rewrite <- Heq.
      rewrite aa23_EX.
     apply IHl. all : try assumption.
      rewrite Heq. intros. discriminate.
      apply x_occ_in_alpha_instant_cons_empty'.
      apply (contrapos_bool_ff _ _ (x_occ_in_free_FO _ _)).
      apply Hcl. apply is_in_FOvar_rem_FOv_f.

      apply att_exFO_instant_cons_empty'. assumption.

      rewrite max_FOv_instant_cons_empty'.
      apply leb_max_suc3. rewrite max_comm.
      apply leb_max_suc3.
      apply leb_refl.

      case_eq (is_in_FOvar (Var ym) (FOvars_in beta)); intros Hin3.

    rewrite want14_EX with (l := l); try assumption. 
     apply IHl. all : try assumption.

        unfold closed_except in Hcl.
        apply Hcl. apply beq_nat_false_FOv.
        assumption.

        apply beq_nat_false_FOv. assumption.

      rewrite aa24_EX; try assumption.
     apply IHl. all : try assumption.
        rewrite want13.
        apply kk7. assumption.

        apply beq_nat_false_FOv. assumption.

        apply leb_max_suc3.
        apply leb_max_suc3.

        apply want19. assumption.
Qed.

Lemma  att_exFO_x_REL : forall rel x,
  REL rel = true ->
  attached_exFO_x rel x = false.
Proof.
  induction rel; intros [xn] H; try
    reflexivity;
    try (simpl in *; discriminate).

    simpl in *.
    case_eq (REL rel1); intros H1; rewrite H1 in H.
      2 : discriminate.
    rewrite IHrel1. apply IHrel2.
    all : assumption.
Qed.

Lemma  att_exFO_x_AT : forall atm x,
  AT atm = true ->
  attached_exFO_x atm x = false.
Proof.
  induction atm; intros [xn] H; try
    reflexivity;
    try (simpl in *; discriminate).

    simpl in *.
    case_eq (AT atm1); intros H1; rewrite H1 in H.
      2 : discriminate.
    rewrite IHatm1. apply IHatm2.
    all : assumption.
Qed.

Lemma lem5 : forall beta rel atm xn P,
  REL rel = true ->
  AT atm = true ->
  SOQFree beta = true ->
  closed_except beta (Var xn) ->
  attached_exFO_x beta (Var xn) = false ->
ex_attached_exFO_lv
     (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)
        (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
        (rev_seq (S (Nat.max (max_FOv (implSO (conjSO rel atm) beta)) xn))
           (length
              (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta))
                 (Var xn))))) (fun2 (conjSO rel atm) P) = false.
Proof.
  intros beta rel atm xn P HREL HAT Hno Hcl Hatt.
  apply want3_EX; try assumption.
  apply is_in_FOvar_l_fun2.
  simpl.
  rewrite att_exFO_x_REL. apply att_exFO_x_AT.
  all : try assumption.
Qed.

Lemma lem5_atm : forall beta atm xn P,
  AT atm = true ->
  SOQFree beta = true ->
  closed_except beta (Var xn) ->
  attached_exFO_x beta (Var xn) = false ->
ex_attached_exFO_lv
     (newnew_pre (instant_cons_empty' atm beta)
        (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn))
        (rev_seq (S (Nat.max (max_FOv (implSO atm beta)) xn))
           (length
              (rem_FOv (FOvars_in (instant_cons_empty' atm beta))
                 (Var xn))))) (fun2 atm P) = false.
Proof.
  intros beta atm xn P  HAT Hno Hcl Hatt.
  apply want3_EX; try assumption.
  apply is_in_FOvar_l_fun2.
  simpl. apply att_exFO_x_AT.
  all : try assumption.
Qed.

Lemma lem2 : forall lP beta rel atm xn,
  REL rel = true ->
  AT atm = true ->
  SOQFree beta = true ->
  attached_allFO_x beta (Var xn) = false ->
  closed_except beta (Var xn) ->
ex_attached_allFO_llv
  (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)
     (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
     (rev_seq
        (S (Nat.max (Nat.max (Nat.max (max_FOv rel) (max_FOv atm)) (max_FOv beta)) xn))
        (length (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn)))))
  (FOv_att_P_l (conjSO rel atm) lP) = false.
Proof.
  induction lP; intros beta rel atm xn HREL HAT Hno Hat1 Hcl.
    simpl. reflexivity.

    simpl FOv_att_P_l. simpl.
    pose proof lem3 as H3. simpl in H3. rewrite H3; try assumption.
    clear H3. apply IHlP; assumption.
Qed.

Lemma lem2_atm : forall lP beta atm xn,
  AT atm = true ->
  SOQFree beta = true ->
  attached_allFO_x beta (Var xn) = false ->
  closed_except beta (Var xn) ->
ex_attached_allFO_llv
  (newnew_pre (instant_cons_empty' atm beta)
     (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn))
     (rev_seq
        (S (Nat.max (Nat.max ( (max_FOv atm)) (max_FOv beta)) xn))
        (length (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn)))))
  (FOv_att_P_l atm lP) = false.
Proof.
  induction lP; intros beta atm xn HAT Hno Hat1 Hcl.
    simpl. reflexivity.

    simpl FOv_att_P_l. simpl.
    pose proof lem3_atm as H3. simpl in H3. rewrite H3; try assumption.
    clear H3. apply IHlP; assumption.
Qed.

Lemma lem4a : forall lP beta rel atm xn,
  REL rel = true ->
  AT atm = true ->
  SOQFree beta = true ->
  attached_exFO_x beta (Var xn) = false ->
  closed_except beta (Var xn) ->
ex_attached_exFO_llv
  (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)
     (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
     (rev_seq
        (S (Nat.max (Nat.max (Nat.max (max_FOv rel) (max_FOv atm)) (max_FOv beta)) xn))
        (length (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn)))))
  (FOv_att_P_l (conjSO rel atm) lP) = false.
Proof.
  induction lP; intros beta rel atm xn HREL HAT Hno Hat1 Hcl.
    simpl. reflexivity.

    simpl FOv_att_P_l. simpl.
    pose proof lem5 as H3. simpl in H3. rewrite H3; try assumption.
    clear H3. apply IHlP; assumption.
Qed.

Lemma lem4a_atm : forall lP beta atm xn,
  AT atm = true ->
  SOQFree beta = true ->
  attached_exFO_x beta (Var xn) = false ->
  closed_except beta (Var xn) ->
ex_attached_exFO_llv
  (newnew_pre (instant_cons_empty' atm beta)
     (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn))
     (rev_seq
        (S (Nat.max (Nat.max ( (max_FOv atm)) (max_FOv beta)) xn))
        (length (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn)))))
  (FOv_att_P_l atm lP) = false.
Proof.
  induction lP; intros beta atm xn HAT Hno Hat1 Hcl.
    simpl. reflexivity.

    simpl FOv_att_P_l. simpl.
    pose proof lem5_atm as H3. simpl in H3. rewrite H3; try assumption.
    clear H3. apply IHlP; assumption.
Qed.

Lemma vsSahlq_instant_aim1_fwd4 : forall lP beta rel atm y xn W Iv Ip Ir,
  REL rel = true ->
  AT atm = true ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  attached_allFO_x beta (Var xn) = false ->
  attached_exFO_x beta (Var xn) = false ->
  closed_except beta (Var xn) ->
  x_occ_in_alpha (instant_cons_empty' (conjSO rel atm) beta) (Var xn) = true ->
  SOturnst W Iv Ip Ir (list_closed_SO (implSO (conjSO rel atm)
              (instant_cons_empty' (conjSO rel atm) beta)) lP) ->
  SOturnst W Iv Ip Ir (replace_pred_l (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)  
      (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) beta)) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))))))
    lP (list_Var (length lP) y)
    (vsS_syn_l (FOv_att_P_l (conjSO rel atm) lP) y)).
Proof.
  intros lP beta rel atm y xn W Iv Ip Ir Hrel Hat Hun Hno Hat1 Hat2 Hc Hocc SOt.
  apply (equiv_new_simpl3_lP lP (FOv_att_P_l (conjSO rel atm) lP) y 
(implSO (conjSO rel atm)
        (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)
           (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
           (rev_seq (S (Nat.max (max_FOv (implSO (conjSO rel atm) beta)) xn))
              (length (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))))))

      W Iv Ip Ir pa_f).
    apply length_FOv_att_P_l.

    simpl. rewrite SOQFree_rel.
    rewrite SOQFree_atm. apply SOQFree_newnew_pre.
    unfold instant_cons_empty'.
    apply Rep_Pred_FOv.SOQFree_rep_pred_l_nlist.
    all : try assumption. 

    apply consistent_lP_llv_FOv_att_P_l.

    apply lem1a_cons.

    apply ex_att_allFO_llv_implSO. apply att_allFO_x__llv.
      intros x. apply attached_allFO_x_conjSO_f.
      apply att_allFO_x_REL. assumption.
      apply att_allFO_x_AT. assumption.
      simpl. apply lem2; assumption.

    apply ex_att_exFO_llv_implSO. apply att_exFO_x__llv.
      intros x. apply attached_exFO_x_conjSO_f.
      apply att_exFO_x_REL. assumption.
      apply att_exFO_x_AT. assumption.
      simpl. apply lem4a; assumption.


    destruct (nlist_list_closed_SO' W Iv Ir 
        (implSO (conjSO rel atm) (instant_cons_empty' (conjSO rel atm) beta)) lP Ip) as [fwd rev].
    specialize (fwd SOt). clear rev.
    case_eq (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn)).
      intros HH. simpl newnew_pre in *.
      destruct (nlist_list_ex (length lP) (vsS_pa_l Iv (FOv_att_P_l (conjSO rel atm) lP) (list_Var (length lP) y))
        ) as [l Heq].

        rewrite length_vsS_pa_l.
        reflexivity.
      rewrite <- Heq. apply fwd.
    intros z ll Heq. rewrite <- Heq.

    intros SOt2.
    apply (kk10  (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
(rev_seq (S (Nat.max (max_FOv (implSO (conjSO rel atm) beta)) xn))
        (length (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))))
      (instant_cons_empty' (conjSO rel atm) beta) (Var xn)).

        apply closed_except_inst_cons_empty'. assumption.

        apply is_in_FOvar_rem_FOv_same.

        rewrite Heq. simpl length.
        rewrite min_l_rev_seq.
        simpl. rewrite max_FOv_instant_cons_empty'.
        apply leb_max_suc3. rewrite max_comm.
        apply leb_max_suc3. apply leb_refl.

        apply decr_strict_rev_seq.

      destruct (nlist_list_ex (length lP) (vsS_pa_l Iv (FOv_att_P_l (conjSO rel atm) lP) (list_Var (length lP) y))
        ) as [l Heq'].

        rewrite length_vsS_pa_l.
        reflexivity.

        rewrite <- Heq'. apply fwd. rewrite Heq'.
        assumption.
Qed.

Lemma vsSahlq_instant_aim1_fwd4_atm : forall lP beta atm y xn W Iv Ip Ir,
  AT atm = true ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  attached_allFO_x beta (Var xn) = false ->
  attached_exFO_x beta (Var xn) = false ->
  closed_except beta (Var xn) ->
  x_occ_in_alpha (instant_cons_empty' atm beta) (Var xn) = true ->
  SOturnst W Iv Ip Ir (list_closed_SO (implSO atm
              (instant_cons_empty' atm beta)) lP) ->
  SOturnst W Iv Ip Ir (replace_pred_l (implSO
    atm
    (newnew_pre (instant_cons_empty' atm beta)  
      (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn))
      (rev_seq (S (max (max_FOv (implSO atm beta)) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn))))))
    lP (list_Var (length lP) y)
    (vsS_syn_l (FOv_att_P_l atm lP) y)).
Proof.
  intros lP beta atm y xn W Iv Ip Ir Hat Hun Hno Hat1 Hat2 Hc Hocc SOt.
  apply (equiv_new_simpl3_lP lP (FOv_att_P_l atm lP) y 
(implSO atm
        (newnew_pre (instant_cons_empty' atm beta)
           (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn))
           (rev_seq (S (Nat.max (max_FOv (implSO atm beta)) xn))
              (length (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn))))))

      W Iv Ip Ir pa_f).
    apply length_FOv_att_P_l.

    simpl.
    rewrite SOQFree_atm.
 apply SOQFree_newnew_pre.    simpl.
    unfold instant_cons_empty'.
    apply Rep_Pred_FOv.SOQFree_rep_pred_l_nlist.
    all : try assumption. 

    apply consistent_lP_llv_FOv_att_P_l.

    apply lem1a_cons.

    apply ex_att_allFO_llv_implSO. apply att_allFO_x__llv.
      intros x. 
      apply att_allFO_x_AT. assumption.
      simpl. apply lem2_atm; assumption.

    apply ex_att_exFO_llv_implSO. apply att_exFO_x__llv.
      intros x.
      apply att_exFO_x_AT. assumption.
      simpl. apply lem4a_atm; assumption.


    destruct (nlist_list_closed_SO' W Iv Ir 
        (implSO atm (instant_cons_empty' atm beta)) lP Ip) as [fwd rev].
    specialize (fwd SOt). clear rev.
    case_eq (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn)).
      intros HH. simpl newnew_pre in *.
      destruct (nlist_list_ex (length lP) (vsS_pa_l Iv (FOv_att_P_l atm lP) (list_Var (length lP) y))
        ) as [l Heq].

        rewrite length_vsS_pa_l.
        reflexivity.
      rewrite <- Heq. apply fwd.
    intros z ll Heq. rewrite <- Heq.

    intros SOt2.
    apply (kk10  (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn))
(rev_seq (S (Nat.max (max_FOv (implSO atm beta)) xn))
        (length (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn))))
      (instant_cons_empty' atm beta) (Var xn)).

        apply closed_except_inst_cons_empty'. assumption.

        apply is_in_FOvar_rem_FOv_same.

        rewrite Heq. simpl length.
        rewrite min_l_rev_seq.
        simpl. rewrite max_FOv_instant_cons_empty'.
        apply leb_max_suc3. rewrite max_comm.
        apply leb_max_suc3. apply leb_refl.

        apply decr_strict_rev_seq.

      destruct (nlist_list_ex (length lP) (vsS_pa_l Iv (FOv_att_P_l atm lP) (list_Var (length lP) y))
        ) as [l Heq'].

        rewrite length_vsS_pa_l.
        reflexivity.

        rewrite <- Heq'. apply fwd. rewrite Heq'.
        assumption.
Qed.

Lemma instant_cons_empty__' : forall alpha beta,
  instant_cons_empty (implSO alpha beta) =
  implSO alpha (instant_cons_empty' alpha beta).
Proof.
  intros alpha beta.
  unfold instant_cons_empty.
  unfold instant_cons_empty'.
  simpl. rewrite rep_pred_l_implSO.
  rewrite rep_pred_l_not_in.
  reflexivity.
Qed.

Lemma list_closed_SO_instant_cons_empty2 : forall l alpha beta W Iv Ip Ir,
  is_in_pred_l (preds_in (implSO alpha beta)) l = true ->
  SOQFree (implSO alpha beta) = true ->
  SOturnst W Iv Ip Ir (list_closed_SO (implSO alpha beta) l) ->
  SOturnst W Iv Ip Ir (list_closed_SO (implSO alpha (instant_cons_empty' alpha beta)) l).
Proof.
  intros. rewrite <-instant_cons_empty__'.
  apply list_closed_SO_instant_cons_empty;
  assumption.
Qed.

Lemma vsSahlq_instant_aim1_fwd4_closer : forall lP beta rel atm y xn W Iv Ip Ir,
  REL rel = true ->
  AT atm = true ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  attached_allFO_x beta (Var xn) = false ->
  attached_exFO_x beta (Var xn) = false ->
  closed_except beta (Var xn) ->
  x_occ_in_alpha (instant_cons_empty' (conjSO rel atm) beta) (Var xn) = true ->
  is_in_pred_l (preds_in (implSO (conjSO rel atm) beta)) lP = true ->
  SOturnst W Iv Ip Ir (list_closed_SO (implSO (conjSO rel atm) beta) lP) ->
  SOturnst W Iv Ip Ir (replace_pred_l (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)  
      (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) beta)) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))))))
    lP (list_Var (length lP) y)
    (vsS_syn_l (FOv_att_P_l (conjSO rel atm) lP) y)).
Proof.
  intros lP beta rel atm y xn W Iv Ip Ir Hrel Hat Hun Hno Hat1 Hat2 Hc Hocc Hin SOt.
  apply vsSahlq_instant_aim1_fwd4; try assumption.
  apply list_closed_SO_instant_cons_empty2; try assumption.
  simpl. rewrite Hno.
  rewrite SOQFree_rel.
  rewrite SOQFree_atm.
  reflexivity. all: assumption.
Qed.

Lemma vsSahlq_instant_aim1_fwd4_closer_atm : forall lP beta atm y xn W Iv Ip Ir,
  AT atm = true ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  attached_allFO_x beta (Var xn) = false ->
  attached_exFO_x beta (Var xn) = false ->
  closed_except beta (Var xn) ->
  x_occ_in_alpha (instant_cons_empty' atm beta) (Var xn) = true ->
  is_in_pred_l (preds_in (implSO atm beta)) lP = true ->
  SOturnst W Iv Ip Ir (list_closed_SO (implSO atm beta) lP) ->
  SOturnst W Iv Ip Ir (replace_pred_l (implSO
    atm
    (newnew_pre (instant_cons_empty' atm beta)  
      (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn))
      (rev_seq (S (max (max_FOv (implSO atm beta)) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn))))))
    lP (list_Var (length lP) y)
    (vsS_syn_l (FOv_att_P_l atm lP) y)).
Proof.
  intros lP beta atm y xn W Iv Ip Ir Hat Hun Hno Hat1 Hat2 Hc Hocc Hin SOt.
  apply vsSahlq_instant_aim1_fwd4_atm; try assumption.
  apply list_closed_SO_instant_cons_empty2; try assumption.
  simpl. rewrite Hno.
  rewrite SOQFree_atm.
  reflexivity. all: assumption.
Qed.

Lemma rep_pred_l_list_closed_allFO : forall l lP lx lcond alpha,
  replace_pred_l (list_closed_allFO alpha l) lP lx lcond =
  list_closed_allFO (replace_pred_l alpha lP lx lcond) l.
Proof.
  induction l; intros lP lx lcond alpha.
    simpl. reflexivity.

    simpl. rewrite <- IHl. rewrite rep_pred_l_allFO.
    reflexivity.
Qed.

Lemma impl_list_closed_allFO : forall l alpha beta,
  (forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir alpha ->
    SOturnst W Iv Ip Ir beta) ->
  forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir (list_closed_allFO alpha l) ->
    SOturnst W Iv Ip Ir (list_closed_allFO beta l).
Proof.
  induction l; intros alpha beta H W Iv Ip Ir SOt.
    simpl in *. apply H. assumption.

    simpl list_closed_allFO in *.
    rewrite SOturnst_allFO in *.
    intros d. apply (IHl alpha). assumption.
    apply SOt.
Qed.

Lemma vsSahlq_instant_aim1_fwd4_closer2 : forall lx lP beta rel atm y xn W Iv Ip Ir,
  REL rel = true ->
  AT atm = true ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  attached_allFO_x beta (Var xn) = false ->
  attached_exFO_x beta (Var xn) = false ->
  closed_except beta (Var xn) ->
  x_occ_in_alpha (instant_cons_empty' (conjSO rel atm) beta) (Var xn) = true ->
  is_in_pred_l (preds_in (implSO (conjSO rel atm) beta)) lP = true ->
  SOturnst W Iv Ip Ir (list_closed_SO (list_closed_allFO
      (implSO (conjSO rel atm) beta) lx) lP) ->
  SOturnst W Iv Ip Ir (replace_pred_l (list_closed_allFO (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)  
      (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) beta)) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn)))))) lx)
    lP (list_Var (length lP) y)
    (vsS_syn_l (FOv_att_P_l (conjSO rel atm) lP) y)).
Proof.
  intros lx lP beta rel atm y xn W Iv Ip Ir Hrel Hat Hun Hno Hat1 Hat2 Hc Hocc Hin SOt. 
  rewrite rep_pred_l_list_closed_allFO.
  pose proof equiv_list_closed_allFO.
  apply (impl_list_closed_allFO _ (list_closed_SO (implSO (conjSO rel atm) beta) lP)).
    intros.
    apply vsSahlq_instant_aim1_fwd4_closer.
    all : try assumption.
    apply equiv_list_closed_SO_list_closed_allFO.
    assumption.
Qed.

Lemma is_un_predless_list_closed_allFO : forall lx alpha,
  is_unary_predless (list_closed_allFO alpha lx) =
  is_unary_predless alpha.
Proof.
  induction lx; intros alpha.
    simpl. reflexivity.

    simpl. destruct a. apply IHlx.
Qed.

Lemma un_predless_preds_in_rev : forall alpha,
preds_in alpha = nil ->
is_unary_predless alpha = true.
Proof.
  intros alpha H.
  case_eq (is_unary_predless alpha); intros H2.
    reflexivity.

    apply un_predless_preds_in_f in H2.
    rewrite H in H2. simpl in *.
    contradiction (H2 eq_refl).
Qed.

Lemma jj9_gen : forall alpha x P cond,
  is_unary_predless cond = true ->
  preds_in (replace_pred alpha P x cond) =
  rem_pred (preds_in alpha) P.
Proof.
  induction alpha; intros [xn] [Pn] cond Hun.
    destruct p as [Qm]; destruct f. simpl.
    case_eq (beq_nat Pn Qm); intros Hbeq;
      simpl. rewrite preds_in_rep_FOv.
      apply un_predless_preds_in. assumption.

      reflexivity.

    destruct f; destruct f0; reflexivity.

    destruct f; destruct f0; reflexivity.

    destruct f as [u1].
    simpl. apply IHalpha. assumption.

    destruct f as [u1].
    simpl. apply IHalpha. assumption.

    simpl. apply IHalpha. assumption.

    simpl. rewrite IHalpha1.
    rewrite IHalpha2.
    rewrite rem_pred_app. reflexivity.
    all : try assumption.

    simpl. rewrite IHalpha1.
    rewrite IHalpha2.
    rewrite rem_pred_app. reflexivity.
    all : try assumption.

    simpl. rewrite IHalpha1.
    rewrite IHalpha2.
    rewrite rem_pred_app. reflexivity.
    all : try assumption.

    destruct p as [Qm].
    simpl in *. case_eq (beq_nat Pn Qm); intros Hbeq.
      apply IHalpha. assumption.

      simpl. rewrite IHalpha. reflexivity.
      assumption.

    destruct p as [Qm].
    simpl in *. case_eq (beq_nat Pn Qm); intros Hbeq.
      apply IHalpha. assumption.

      simpl. rewrite IHalpha. reflexivity. assumption.
Qed.

Lemma is_in_pred_rem_pred : forall l P Q,
  is_in_pred P l = true ->
  ~ P = Q ->
  is_in_pred P (rem_pred l Q) = true.
Proof.
  induction l; intros [Pn] [Qm] H1 Hneq.
    simpl in *. discriminate.

    simpl in *. destruct a as [Rn].
    case_eq (beq_nat Qm Rn); intros Hbeq.
      case_eq (beq_nat Pn Rn); intros Hbeq2;
        rewrite Hbeq2 in *. rewrite (beq_nat_true _ _ Hbeq2) in *.
        rewrite (beq_nat_true _ _ Hbeq) in *. contradiction (Hneq eq_refl).

        apply IHl; assumption.

      case_eq (beq_nat Pn Rn); intros Hbeq2;
        rewrite Hbeq2 in *. simpl.
        rewrite Hbeq2. reflexivity.

        simpl. rewrite Hbeq2. apply IHl; assumption.
Qed.


Lemma is_in_pred_l_rep_pred : forall l1 l2 P,
  is_in_pred_l l1 l2 = true ->
  is_in_pred_l (rem_pred l1 P) (rem_pred l2 P) = true.
Proof.
  induction l1; intros l2 [Pn] H.
    simpl in *. reflexivity.

    simpl in *. destruct a as [Qm].
    case_eq (beq_nat Pn Qm); intros Hbeq.
      simpl in *.
      case_eq (is_in_pred (Pred Qm) l2); intros H2;
        rewrite H2 in *. 2 : discriminate.
      apply IHl1. assumption.

      simpl.
      case_eq (is_in_pred (Pred Qm) l2); intros H2;
        rewrite H2 in *. 2 : discriminate.
      rewrite is_in_pred_rem_pred.
      apply IHl1. all: try assumption.
      intros HH. inversion HH as [HH'].
      rewrite HH' in Hbeq.
      rewrite <- beq_nat_refl in Hbeq.
      discriminate.
Qed.

Lemma rem_pred_cons_same : forall l P,
  rem_pred (cons P l) P = rem_pred l P.
Proof.
  induction l; intros [Pn].
    simpl. rewrite <- beq_nat_refl. reflexivity.

    simpl. destruct a as [Qm].
    rewrite <- beq_nat_refl.
    case_eq (beq_nat Pn Qm); reflexivity.
Qed.

Lemma is_in_pred__l_cons_l : forall l1 l2 P,
  is_in_pred P l2 = true ->
  is_in_pred_l l1 l2 = true ->
  is_in_pred_l (cons P l1) l2 = true.
Proof.
  induction l1; intros l2 [Pn] H1 H2.
    simpl in *. rewrite H1. reflexivity.
  
    simpl in *. destruct a as [Qm].
    case_eq (is_in_pred (Pred Pn) l2); intros H3.
      case_eq (is_in_pred (Pred Qm) l2); intros H4;
        rewrite H4 in *; try discriminate.
        assumption.

        rewrite H3 in H1. discriminate.
Qed.


Lemma is_in_pred_l_rem_pred_cons : forall l1 l2 P Q,
  is_in_pred_l l1 (cons Q l2) = true ->
  is_in_pred_l (rem_pred l1 P) (cons Q (rem_pred l2 P)) = true.
Proof.
  induction l1; intros l2 [Pn] [Qm] H.
    simpl in *. reflexivity.

    simpl in *. destruct a as [Rn]. 
    case_eq (beq_nat Pn Rn); intros Hbeq.
      case_eq (beq_nat Rn Qm); intros Hbeq2;
        rewrite Hbeq2 in *. apply IHl1. assumption.

        case_eq (is_in_pred (Pred Rn) l2); intros H2;
          rewrite H2 in *. 2 : discriminate.
        apply IHl1. assumption.

      case_eq (beq_nat Rn Qm); intros Hbeq2;
        rewrite Hbeq2 in *.
        rewrite (beq_nat_true _ _ Hbeq2).
        apply is_in_pred__l_cons_l.
        simpl. rewrite <- beq_nat_refl. reflexivity.
        apply IHl1. assumption.

        case_eq (is_in_pred (Pred Rn) l2); intros H2;
          rewrite H2 in *. 2 : discriminate.
        apply is_in_pred__l_cons_l.
        simpl. rewrite Hbeq2.
        apply is_in_pred_rem_pred. assumption.
        intros HH. inversion HH as [HH']. rewrite HH' in Hbeq.
        rewrite <- beq_nat_refl in Hbeq. discriminate.

        apply IHl1. assumption.
Qed.

Lemma please3 : forall l alpha P x cond ,
  is_unary_predless cond = true ->
  is_in_pred_l (preds_in alpha) l = true ->
  is_in_pred_l (preds_in (replace_pred alpha P x cond)) (rem_pred l P) = true.
Proof.
  induction l; intros alpha P x cond Hun Hin.
    simpl in *. apply is_in_pred_l_nil in Hin.
    rewrite <- Hin.
    apply is_in_pred_rep_pred.
    assumption.

    destruct a as [Qm]. simpl. destruct P as [Pn].
    case_eq (beq_nat Pn Qm); intros Hbeq.
      case_eq (is_in_pred_l (preds_in alpha) l); intros Hin2.
        apply IHl; assumption.

        pose proof (is_in_pred_l_f_l _ _ _ Hin2 Hin) as H.
        rewrite jj9_gen.
        rewrite <- (rem_pred_cons_same l (Pred Pn)).
        apply is_in_pred_l_rep_pred. rewrite (beq_nat_true _ _ Hbeq) in *.
        all : try assumption.

      case_eq (is_in_pred_l (preds_in alpha) l); intros Hin2.
        apply is_in_pred_l2.
        apply IHl; assumption.

        pose proof (is_in_pred_l_f_l _ _ _ Hin2 Hin) as H.
        rewrite jj9_gen.
        apply is_in_pred_l_rem_pred_cons. all : try assumption.
Qed.

Lemma is_in_pred_l_rem_pred : forall l P,
  is_in_pred_l (rem_pred l P) l = true.
Proof.
  induction l; intros [Pn].
    simpl. reflexivity.

    destruct a as [Qm]. simpl.
    case_eq (beq_nat Pn Qm); intros Hbeq.
      apply is_in_pred_l2. apply IHl.

      simpl. rewrite <- beq_nat_refl.
      apply is_in_pred_l2. apply IHl.
Qed.

Lemma please4 : forall l alpha P x cond ,
  is_unary_predless cond = true ->
  is_in_pred_l (preds_in alpha) (cons P l) = true ->
  is_in_pred_l (preds_in (replace_pred alpha P x cond)) l = true.
Proof.
  intros l alpha P x cond Hun Hin.
  apply (please3 _ alpha P x cond) in Hin.
  rewrite rem_pred_cons_same in Hin.
  apply (is_in_pred_l_trans _ _ _ Hin (is_in_pred_l_rem_pred _ _)).
  assumption.
Qed.

Lemma consistent_lP_lcond_P_fun1_FOv_att_P_l : forall P l beta y,
  consistent_lP_lcond_P l (vsS_syn_l (FOv_att_P_l beta l) y) P.
Proof.
  intros P l beta y.
  unfold consistent_lP_lcond_P.
  unfold is_constant.
  destruct (something1 l P beta) as [n H2].
  exists (fun1 (fun2 beta P) y). exists n.
  apply ind_llv_cond_vsS_syn_l. assumption.
Qed.

Lemma consistent_lP_lcond_fun1_FOv_att_P_l : forall l beta y,
  consistent_lP_lcond l (vsS_syn_l (FOv_att_P_l beta l) y).
Proof.
  unfold consistent_lP_lcond.
  intros. apply consistent_lP_lcond_P_fun1_FOv_att_P_l.
Qed.

 Lemma something2 : forall n l1 P x,
length l1 = n ->
exists m,
ind_FOv (indicies_l2 l1 P) (constant_l x n) =
constant_l x m.
Proof.
  induction n; intros l1 P x H.
    simpl. unfold indicies_l2.
    destruct l1. simpl. exists 0. reflexivity.
    discriminate.

    destruct l1. discriminate.
    destruct p as [Qm]. destruct P as [Pn].
    simpl in *.
    unfold indicies_l2 in *.
    simpl. case_eq (beq_nat Pn Qm); intros Hbeq;
      simpl; rewrite ind_FOv_ind_l2_pre_cons;
      inversion H as [H'];
      destruct (IHn _ (Pred Pn) x H') as [m IH].
      exists (S m); rewrite H'; rewrite IH;
      reflexivity.

      exists ( m); rewrite H'; rewrite IH;
      reflexivity.
Qed.

Lemma please5 : forall n l1 x,
  length l1 = n ->
consistent_lP_lx l1 (constant_l x n).
Proof.
  unfold consistent_lP_lx. unfold consistent_lP_lx_P.
  intros n l1 x H P. unfold is_constant.
  destruct (something2 n l1 P x H) as [m HH].
  exists x. exists m. assumption.
Qed.

Lemma please2 : forall l alpha beta y,
   is_in_pred_l (preds_in alpha) l =true ->
  is_unary_predless
    (replace_pred_l alpha l
       (list_Var (length l) y)
       (vsS_syn_l (FOv_att_P_l beta l) y)) = true.
Proof.
  induction l; intros alpha beta y H.
     simpl in *. apply is_in_pred_l_nil in H.
    apply un_predless_preds_in_rev. assumption.

    simpl. rewrite rep_pred__l_consistent.
    apply IHl. apply please4.
      apply un_predless_fun1.
      assumption.
      apply un_predless_l_vsS_syn_l.
      apply un_predless_fun1.
      pose proof (consistent_lP_lcond_fun1_FOv_att_P_l (cons a l)) as H2.
      simpl in H2. apply H2.

      rewrite constant_l_list_Var.
      apply (please5 (length (cons a l)) (cons a l) y).
      apply eq_refl.
Qed.

Lemma preds_in_rename_FOv : forall alpha x y,
  preds_in (rename_FOv alpha x y) = preds_in alpha.
Proof.
  induction alpha; intros [xn] [ym].
    destruct p; destruct f as [zn]. simpl.
    case_eq (beq_nat xn zn); intros Hbeq; reflexivity.

    destruct f as [z1]; destruct f0 as [z2].
    simpl. case_eq (beq_nat xn z1); intros Hbeq1;
      case_eq (beq_nat xn z2); intros Hbeq2;
        reflexivity.

    destruct f as [z1]; destruct f0 as [z2].
    simpl. case_eq (beq_nat xn z1); intros Hbeq1;
      case_eq (beq_nat xn z2); intros Hbeq2;
        reflexivity.

    destruct f as [zn]. simpl. case_eq (beq_nat zn xn); intros Hbeq;
    simpl; apply (IHalpha (Var xn) (Var ym)).

    destruct f as [zn]. simpl. case_eq (beq_nat zn xn); intros Hbeq;
    simpl; apply (IHalpha (Var xn) (Var ym)).

    simpl in *. apply (IHalpha (Var xn) (Var ym)).

    simpl in *. unfold rename_FOv in *.
    rewrite (IHalpha1 (Var xn) (Var ym)).
    rewrite (IHalpha2 (Var xn) (Var ym)).
    reflexivity.

    simpl in *. unfold rename_FOv in *.
    rewrite (IHalpha1 (Var xn) (Var ym)).
    rewrite (IHalpha2 (Var xn) (Var ym)).
    reflexivity.

    simpl in *. unfold rename_FOv in *.
    rewrite (IHalpha1 (Var xn) (Var ym)).
    rewrite (IHalpha2 (Var xn) (Var ym)).
    reflexivity.

    destruct p. simpl. unfold rename_FOv in *.
    rewrite (IHalpha (Var xn) (Var ym)). reflexivity.

    destruct p. simpl. unfold rename_FOv in *.
    rewrite (IHalpha (Var xn) (Var ym)). reflexivity.
Qed.

Lemma preds_in_newnew_pre : forall l1 l2 alpha,
  preds_in (newnew_pre alpha l1 l2) = (preds_in alpha).
Proof.
  induction l1; intros l2 alpha.
    simpl. reflexivity.

    simpl. destruct l2. reflexivity.
    rewrite preds_in_rename_FOv. apply IHl1.
Qed.

Lemma something3 : forall beta alpha,
  is_in_pred_l (preds_in (instant_cons_empty' alpha beta))
    (preds_in beta) = true.
Proof.
  intros beta alpha.
  unfold instant_cons_empty'.
  rewrite jj8; apply jj10.
Qed.

Lemma is_in_pred_l_app_2l : forall l l1 l2 : list predicate,
  is_in_pred_l l l1 = true ->
  is_in_pred_l l (l1 ++ l2) = true.
Proof.
  induction l; intros l1 l2 H.
    reflexivity.

    destruct a as [Pn].
    simpl in *.
    case_eq (is_in_pred (Pred Pn) l1); intros His;
      rewrite His in *; try discriminate.
    rewrite IHl; try assumption.
    rewrite is_in_pred_app_l.
      reflexivity.
      assumption.
Qed.

Lemma hopeful2 : forall  lx rel atm y xn beta,
  is_unary_predless (replace_pred_l (list_closed_allFO (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)  
      (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) beta)) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn)))))) lx)
    (preds_in (list_closed_allFO
      (implSO (conjSO rel atm) beta) lx)) (list_Var (length (preds_in (list_closed_allFO
      (implSO (conjSO rel atm) beta) lx))) y)
    (vsS_syn_l (FOv_att_P_l (conjSO rel atm) (preds_in (list_closed_allFO
      (implSO (conjSO rel atm) beta) lx))) y)) = true.
Proof.
  intros lx rel atm y xn beta.
  rewrite rep_pred_l_list_closed_allFO.
  rewrite is_un_predless_list_closed_allFO.
  rewrite rep_pred_l_implSO.
  simpl. rewrite preds_in_list_closed_allFO.
  rewrite please2.
  rewrite please2. reflexivity.
  rewrite preds_in_newnew_pre.
  apply (is_in_pred_l_trans _ _ _ (something3 _ _)).
  simpl. apply is_in_pred_l_app_2r. apply is_in_pred_l_refl.
  simpl.  apply is_in_pred_l_app_2l. apply is_in_pred_l_refl.
Qed.

Lemma hopeful2_atm : forall  lx atm y xn beta,
  is_unary_predless (replace_pred_l (list_closed_allFO (implSO
    atm
    (newnew_pre (instant_cons_empty' atm beta)  
      (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn))
      (rev_seq (S (max (max_FOv (implSO atm beta)) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn)))))) lx)
    (preds_in (list_closed_allFO
      (implSO atm beta) lx)) (list_Var (length (preds_in (list_closed_allFO
      (implSO atm beta) lx))) y)
    (vsS_syn_l (FOv_att_P_l atm (preds_in (list_closed_allFO
      (implSO atm beta) lx))) y)) = true.
Proof.
  intros lx atm y xn beta.
  rewrite rep_pred_l_list_closed_allFO.
  rewrite is_un_predless_list_closed_allFO.
  rewrite rep_pred_l_implSO.
  simpl. rewrite preds_in_list_closed_allFO.
  rewrite please2.
  rewrite please2. reflexivity.
  rewrite preds_in_newnew_pre.
  apply (is_in_pred_l_trans _ _ _ (something3 _ _)).
  simpl. apply is_in_pred_l_app_2r. apply is_in_pred_l_refl.
  simpl.  apply is_in_pred_l_app_2l. apply is_in_pred_l_refl.
Qed.

Lemma vsSahlq_instant_aim1_fwd4_closer2_atm : forall lx lP beta atm y xn W Iv Ip Ir,
  AT atm = true ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  attached_allFO_x beta (Var xn) = false ->
  attached_exFO_x beta (Var xn) = false ->
  closed_except beta (Var xn) ->
  x_occ_in_alpha (instant_cons_empty' atm beta) (Var xn) = true ->
  is_in_pred_l (preds_in (implSO atm beta)) lP = true ->
  SOturnst W Iv Ip Ir (list_closed_SO (list_closed_allFO
      (implSO atm beta) lx) lP) ->
  SOturnst W Iv Ip Ir (replace_pred_l (list_closed_allFO (implSO
    atm
    (newnew_pre (instant_cons_empty' atm beta)  
      (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn))
      (rev_seq (S (max (max_FOv (implSO atm beta)) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn)))))) lx)
    lP (list_Var (length lP) y)
    (vsS_syn_l (FOv_att_P_l atm lP) y)).
Proof.
  intros lx lP beta atm y xn W Iv Ip Ir Hat Hun Hno Hat1 Hat2 Hc Hocc Hin SOt. 
  rewrite rep_pred_l_list_closed_allFO.
  pose proof equiv_list_closed_allFO.
  apply (impl_list_closed_allFO _ (list_closed_SO (implSO atm beta) lP)).
    intros.
    apply vsSahlq_instant_aim1_fwd4_closer_atm.
    all : try assumption.
    apply equiv_list_closed_SO_list_closed_allFO.
    assumption.
Qed.

(* ---------------------------------------- *)

Lemma preds_in_strip_exFO : forall alpha n,
  preds_in (strip_exFO alpha n) = preds_in alpha.
Proof.
  induction alpha; intros n; try (destruct n; reflexivity).
  destruct f. simpl. destruct n.  reflexivity. 
  apply IHalpha.
Qed.

Lemma preds_in_rename_FOv_max_conj : forall alpha beta x,
  preds_in (rename_FOv_max_conj alpha beta x) =
  preds_in alpha.
Proof.
  unfold rename_FOv_max_conj.
  intros. rewrite preds_in_rename_FOv.
  reflexivity.
Qed.

Lemma preds_in_list_closed_exFO : forall l alpha,
  preds_in (list_closed_exFO alpha l) = preds_in alpha.
Proof.
  induction l; intros alpha.
    simpl. reflexivity.

    simpl. destruct a. apply IHl.
Qed.

Lemma preds_in_rename_FOv_A_pre: forall  n l alpha beta,
  preds_in (rename_FOv_A_pre alpha beta l n) =
  preds_in alpha.
Proof.
  induction n; intros l alpha beta. 
    simpl. reflexivity.

    simpl. destruct l. reflexivity.
    rewrite IHn.
    rewrite preds_in_strip_exFO.
    rewrite preds_in_rename_FOv_max_conj.
    apply preds_in_list_closed_exFO.
Qed.

Lemma preds_in_rename_FOv_A : forall l alpha beta,
  preds_in (rename_FOv_A alpha beta l)  = 
  preds_in alpha.
Proof.
  induction l; intros alpha beta; unfold rename_FOv_A.
    simpl. reflexivity.
  
    simpl. rewrite preds_in_rename_FOv_A_pre.
    rewrite preds_in_strip_exFO.
    rewrite preds_in_rename_FOv_max_conj.
    apply preds_in_list_closed_exFO.
Qed. 

Open Scope type_scope.

Lemma preprocess_vsSahlq_ante_predSO_againTRY : forall p f,
  conjSO_exFO_relatSO (predSO p f) = true ->
existsT2 (lv : list FOvariable) (atm : SecOrder),
  (AT atm = true) *
  ((existsT rel : SecOrder,
      REL rel = true /\
      is_in_pred_l (preds_in (conjSO rel atm)) (preds_in (predSO p f)) =
      true /\
      (forall (W : Set) (Iv : FOvariable -> W)
         (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop),
       SOturnst W Iv Ip Ir (predSO p f) <->
       SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv))) +
   (is_in_pred_l (preds_in atm) (preds_in (predSO p f)) = true /\
   (forall (W : Set) (Iv : FOvariable -> W)
      (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop),
    SOturnst W Iv Ip Ir (predSO p f) <->
    SOturnst W Iv Ip Ir (list_closed_exFO atm lv)))).
Proof.
  intros p f H.
    exists nil.
    exists (predSO p f).
    destruct p as [Pn].
    destruct f as [xn].
    simpl.
    apply pair.
      reflexivity.
      right. rewrite <- beq_nat_refl.
      apply conj. reflexivity.
      intros.
      apply bi_refl.
Defined.

Lemma preds_in_exFO : forall alpha x,
  preds_in (exFO x alpha) = preds_in alpha.
Proof.
  intros. simpl. destruct x. reflexivity.
Qed.

Lemma preprocess_vsSahlq_ante_exFO_againTRY : forall alpha f,
  conjSO_exFO_relatSO (exFO f alpha) = true ->
  (existsT P : predicate, P_occurs_in_alpha (exFO f alpha) P = true) ->
(conjSO_exFO_relatSO alpha = true ->
          (existsT P : predicate, P_occurs_in_alpha alpha P = true) ->
          existsT2 (lv : list FOvariable) (atm : SecOrder),
            (AT atm = true) *
            ((existsT rel : SecOrder,
                REL rel = true /\
                is_in_pred_l (preds_in (conjSO rel atm))
                  (preds_in alpha) = true /\
                (forall (W : Set) (Iv : FOvariable -> W)
                   (Ip : predicate -> W -> Prop) 
                   (Ir : W -> W -> Prop),
                 SOturnst W Iv Ip Ir alpha <->
                 SOturnst W Iv Ip Ir
                   (list_closed_exFO (conjSO rel atm) lv))) +
             (is_in_pred_l (preds_in atm) (preds_in alpha) = true /\
             (forall (W : Set) (Iv : FOvariable -> W)
                (Ip : predicate -> W -> Prop) 
                (Ir : W -> W -> Prop),
              SOturnst W Iv Ip Ir alpha <->
              SOturnst W Iv Ip Ir (list_closed_exFO atm lv))))) ->
existsT2 (lv : list FOvariable) (atm : SecOrder),
  (AT atm = true) *
  ((existsT rel : SecOrder,
      REL rel = true /\
      is_in_pred_l (preds_in (conjSO rel atm))
        (preds_in (exFO f alpha)) = true /\
      (forall (W : Set) (Iv : FOvariable -> W)
         (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop),
       SOturnst W Iv Ip Ir (exFO f alpha) <->
       SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv))) +
   (is_in_pred_l (preds_in atm) (preds_in (exFO f alpha)) = true /\
   (forall (W : Set) (Iv : FOvariable -> W)
      (Ip : predicate -> W -> Prop) (Ir : W -> W -> Prop),
    SOturnst W Iv Ip Ir (exFO f alpha) <->
    SOturnst W Iv Ip Ir (list_closed_exFO atm lv)))).
Proof.
  intros alpha f H Hocc IHalpha.
    simpl in H.
    destruct Hocc as [P Hocc]. rewrite <- P_occurs_in_alpha_exFO in Hocc.
    assert (existsT P, P_occurs_in_alpha alpha P = true) as Hocc2.
      exists P. assumption.
    specialize (IHalpha H Hocc2).
    destruct IHalpha as [lv [atm [HAT [  [rel [HREL [Hin SOt]]] | [Hin SOt] ]]]];
      exists (cons f lv);
      exists atm;
      apply pair; try assumption.
      left.
      exists rel.
      apply conj. assumption.
      apply conj. rewrite preds_in_exFO. assumption.

      intros W Iv Ip Ir.
      simpl list_closed_exFO.
      do 2 rewrite SOturnst_exFO.
      split; intros SOt2;
        destruct SOt2 as [d SOt2];
        exists d;
        apply SOt;
        assumption.

      right.
      apply conj. rewrite preds_in_exFO. assumption.
      intros W Iv Ip Ir.
      simpl list_closed_exFO.
      do 2 rewrite SOturnst_exFO.
      split; intros SOt2;
        destruct SOt2 as [d SOt2];
        exists d;
        apply SOt;
        assumption.
Defined.

Lemma trying1 : forall alpha,
  (forall P, P_occurs_in_alpha alpha P = false) +
  (existsT P, P_occurs_in_alpha alpha P = true).
Proof.
  induction alpha.
    right. exists p. unfold P_occurs_in_alpha. destruct p as [Pn].
    destruct f. simpl. rewrite <- beq_nat_refl. reflexivity.

    left. intros P. unfold P_occurs_in_alpha. destruct f. destruct f0.  
    simpl. reflexivity.

    left. intros P. unfold P_occurs_in_alpha. destruct f. destruct f0.  
    simpl. reflexivity.

    destruct IHalpha as [IH1 | IH2].
      left. intros P. rewrite<- P_occurs_in_alpha_allFO. apply IH1.
      right. destruct IH2 as [P H]. exists P.
      rewrite<- P_occurs_in_alpha_allFO. assumption.

    destruct IHalpha as [IH1 | IH2].
      left. intros P. rewrite<- P_occurs_in_alpha_exFO. apply IH1.
      right. destruct IH2 as [P H]. exists P.
      rewrite<- P_occurs_in_alpha_exFO. assumption.

    destruct IHalpha as [IH1 | IH2]; [left | right].
      intros P. rewrite <-  P_occurs_in_alpha_negSO.
      apply IH1.

      destruct IH2 as [P IH2]. exists P.  rewrite <- P_occurs_in_alpha_negSO.
      assumption.

    destruct IHalpha1 as [IH1 | IH1].
    destruct IHalpha2 as [IH2 | IH2].
      left. intros P.
      apply P_occurs_in_alpha_conjSO_f.
      apply conj. apply IH1. apply IH2. 

      destruct IH2 as [P IH2].
      right. exists P. 
      apply P_occurs_in_alpha_conjSO.
      right. assumption.

      destruct IH1 as [P IH1].  
      right. exists P. apply P_occurs_in_alpha_conjSO.
      left. assumption.

    destruct IHalpha1 as [IH1 | IH1].
    destruct IHalpha2 as [IH2 | IH2].
      left. intros P.
      apply P_occurs_in_alpha_conjSO_f.
      apply conj. apply IH1. apply IH2. 

      destruct IH2 as [P IH2].
      right. exists P. 
      apply P_occurs_in_alpha_conjSO.
      right. assumption.

      destruct IH1 as [P IH1].  
      right. exists P. apply P_occurs_in_alpha_conjSO.
      left. assumption.

    destruct IHalpha1 as [IH1 | IH1].
    destruct IHalpha2 as [IH2 | IH2].
      left. intros P.
      apply P_occurs_in_alpha_conjSO_f.
      apply conj. apply IH1. apply IH2. 

      destruct IH2 as [P IH2].
      right. exists P. 
      apply P_occurs_in_alpha_conjSO.
      right. assumption.

      destruct IH1 as [P IH1].  
      right. exists P. apply P_occurs_in_alpha_conjSO.
      left. assumption.

    right. exists p. unfold P_occurs_in_alpha.
    simpl. destruct p as [Pn]. simpl.
    rewrite <- beq_nat_refl. reflexivity.

    right. exists p. unfold P_occurs_in_alpha.
    simpl. destruct p as [Pn]. simpl.
    rewrite <- beq_nat_refl. reflexivity.
Defined.

Lemma P_occurs_in_alpha_conjSO_all_f_l : forall alpha1 alpha2,
  (forall P, P_occurs_in_alpha (conjSO alpha1 alpha2) P = false) ->
  forall P, P_occurs_in_alpha alpha1 P = false.
Proof.
  intros alpha1 alpha2 H P.
  specialize (H P).
  apply P_occurs_in_alpha_conjSO_f in H.
  apply H.
Qed. 

Lemma P_occurs_in_alpha_conjSO_all_f_r : forall alpha1 alpha2,
  (forall P, P_occurs_in_alpha (conjSO alpha1 alpha2) P = false) ->
  forall P, P_occurs_in_alpha alpha2 P = false.
Proof.
  intros alpha1 alpha2 H P.
  specialize (H P).
  apply P_occurs_in_alpha_conjSO_f in H.
  apply H.
Qed. 

Lemma preprocess_vsSahlq_ante_5_againTRY : forall alpha1 alpha2 lv1 rel1 lv2 rel2,
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
existsT2 lv : list FOvariable,
  (existsT rel : SecOrder,
     REL rel = true /\
      (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
         (Ir : W -> W -> Prop),
       SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
       SOturnst W Iv Ip Ir (list_closed_exFO rel lv))).
Proof.
  intros alpha1 alpha2 lv1 rel1 lv2 rel2
         H HREL1 H_1 HREL2 H_2 H1.
     exists (app 
                (rename_FOv_A_list rel2 
                     (list_closed_exFO rel1 lv1) lv2)
(rename_FOv_A_list rel1 
                  (rename_FOv_A rel2
                     (list_closed_exFO rel1 lv1) lv2) lv1 )).

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
Defined.

Lemma trying2 : forall alpha,
  conjSO_exFO_relatSO alpha = true ->
  (forall P, P_occurs_in_alpha alpha P = false) ->
  existsT2 lv rel,
  REL rel = true /\
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha <->
      SOturnst W Iv Ip Ir (list_closed_exFO rel lv)).
Proof.
  induction alpha; intros H1 H2; try (    simpl in *; discriminate).
    simpl in *. specialize (H2 p).
    destruct p. unfold P_occurs_in_alpha in H2.
    destruct f. simpl in *. rewrite <- beq_nat_refl in H2.
    discriminate.

    exists nil. exists (relatSO f f0).
    apply conj. reflexivity.
    simpl. intros. apply bi_refl.

    assert (forall P, P_occurs_in_alpha (alpha) P = false) as H2'.
      intros P. specialize (H2 P).
      rewrite <- P_occurs_in_alpha_exFO in H2.
      assumption.
    simpl in H1. destruct (IHalpha H1 H2') as [lv [rel [Hrel H]]].
    exists (cons f lv). exists rel.
    apply conj. assumption.
    intros. simpl list_closed_exFO.
    do 2 rewrite SOturnst_exFO. split; intros [d SOt];
      exists d; apply H; assumption.

    simpl in H1. case_eq (conjSO_exFO_relatSO alpha1);
      intros H3; rewrite H3 in H1. 2 : discriminate.
    destruct (IHalpha1 H3 (P_occurs_in_alpha_conjSO_all_f_l _ _ H2))
      as [lv [rel [HREL H]]].
    destruct (IHalpha2 H1 (P_occurs_in_alpha_conjSO_all_f_r _ _ H2))
      as [lv2 [rel2 [HREL2 H4]]].
    destruct (preprocess_vsSahlq_ante_5_againTRY alpha1 alpha2 lv rel lv2 rel2)
      as [lv' [rel' [Hrel' H']]];
      try assumption.
    exists lv'. exists rel'.
    apply conj. assumption.
    assumption.
Defined.

Lemma preds_in_rel  : forall rel,
  REL rel = true ->
  preds_in rel = nil.
Proof.
  induction rel; intros H; try (simpl in *; discriminate).
    destruct f; destruct f0; reflexivity.

    simpl in *. rewrite IHrel1. rewrite IHrel2.
    reflexivity. 
      apply REL_conjSO_r in H. assumption.
      apply REL_conjSO_l in H. assumption.
Qed.

Lemma preprocess_vsSahlq_ante_notocc_againTRY : forall alpha,
  conjSO_exFO_relatSO alpha = true ->
  (forall P, P_occurs_in_alpha alpha P = false) ->
  existsT2 lv rel,
      (REL rel = true) /\
      (is_in_pred_l (preds_in rel) (preds_in alpha) = true) /\
        forall W Iv Ip Ir,
          SOturnst W Iv Ip Ir alpha <->
          SOturnst W Iv Ip Ir (list_closed_exFO rel lv).
Proof.
  intros alpha H1 H2. destruct (trying2 alpha H1 H2)
     as [lv [rel [Hrel H]]].
  exists lv. exists rel.
  apply conj. assumption. 
  apply conj. rewrite preds_in_rel. reflexivity.
  all :  assumption.
Defined.

Lemma preprocess_vsSahlq_ante_4_againTRY : forall alpha1 alpha2 lv1 rel1 lv2 rel2 atm2,
  conjSO_exFO_relatSO alpha2 = true ->
  REL rel1 = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha1 <->
      SOturnst W Iv Ip Ir (list_closed_exFO rel1 lv1)) ->
  REL rel2 = true ->
  AT atm2 = true ->
  is_in_pred_l (preds_in (conjSO rel2 atm2)) (preds_in alpha2) = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha2 <->
      SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel2 atm2) lv2) ) ->
  conjSO_exFO_relatSO alpha1 = true ->
existsT2 lv : list FOvariable,
  (existsT2 atm : SecOrder,
         (AT atm = true) *
    (existsT rel : SecOrder,
       REL rel = true /\
          is_in_pred_l (preds_in (conjSO rel atm))
                       (preds_in (conjSO alpha1 alpha2)) = true /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
          SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv)))).
Proof.
  intros alpha1 alpha2 lv1 rel1 lv2 rel2 atm2
         H HREL1 H_1 HREL2 HAT2 Hin H_2 H1.
     destruct (same_struc_conjSO_ex _ _ _ (same_struc_rename_FOv_A (conjSO rel2 atm2) 
                                            (list_closed_exFO rel1 lv1)
                                             lv2)) as [rel2' [atm2' Heq2]].
     exists (app 
                (rename_FOv_A_list (conjSO rel2 atm2) 
                     (list_closed_exFO rel1 lv1) lv2)
(rename_FOv_A_list rel1 
                  (rename_FOv_A (conjSO rel2 atm2)
                     (list_closed_exFO rel1 lv1) lv2) lv1 )).
    exists  atm2'.
    apply pair.
      pose proof (same_struc_rename_FOv_A (conjSO rel2 atm2) (list_closed_exFO rel1 lv1)
         lv2) as Hsame2.
      pose proof (same_struc_rename_FOv_A rel1
         (rename_FOv_A (conjSO rel2 atm2)
            (list_closed_exFO rel1 lv1) lv2) lv1) as Hsame1.
      rewrite Heq2 in Hsame2.
      apply same_struc_conjSO_r in Hsame2.
      apply same_struc_comm in Hsame2.
      apply same_struc_AT in Hsame2; try assumption.
    exists (conjSO (rename_FOv_A rel1 (rename_FOv_A (conjSO rel2 atm2) 
                      (list_closed_exFO rel1 lv1) lv2) lv1) rel2').
    apply conj.
      pose proof (same_struc_rename_FOv_A (conjSO rel2 atm2) (list_closed_exFO rel1 lv1)
         lv2) as Hsame2.
      pose proof (same_struc_rename_FOv_A rel1
         (rename_FOv_A (conjSO rel2 atm2)
            (list_closed_exFO rel1 lv1) lv2) lv1) as Hsame1.
      rewrite Heq2 in Hsame2.
      apply same_struc_conjSO_l in Hsame2.
      apply same_struc_comm in Hsame2.
      apply same_struc_REL in Hsame2; try assumption.
      apply same_struc_comm in Hsame1.
      apply same_struc_REL in Hsame1; try assumption.
      simpl; rewrite Hsame1; assumption.

    apply conj.
      assert (preds_in (rename_FOv_A (conjSO rel2 atm2)   
                      (list_closed_exFO rel1 lv1) lv2) =
                       preds_in (conjSO rel2' atm2')) as Hpreds.
        rewrite Heq2. reflexivity.
      simpl. rewrite preds_in_rename_FOv_A in *.
      rewrite app_assoc.
      assert (preds_in (conjSO rel2' atm2') = 
              app (preds_in rel2') (preds_in atm2')) as Hpreds2.
        reflexivity.
      rewrite <- Hpreds2.
      rewrite <- Hpreds.
      apply is_in_pred_l_2app.
      rewrite preds_in_rel. reflexivity. assumption.
      assumption.

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
Defined.


Lemma preprocess_vsSahlq_ante_6_againTRY : forall alpha1 alpha2 lv1 rel1 
        lv2 atm2,
  conjSO_exFO_relatSO alpha2 = true ->
  REL rel1 = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha1 <->
      SOturnst W Iv Ip Ir (list_closed_exFO rel1 lv1)) ->
  AT atm2 = true ->
  is_in_pred_l (preds_in atm2) (preds_in alpha2) = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha2 <->
      SOturnst W Iv Ip Ir (list_closed_exFO atm2 lv2)) ->
  conjSO_exFO_relatSO alpha1 = true ->
existsT2 lv : list FOvariable,
    (existsT2 atm : SecOrder,
       (AT atm = true) *
      (existsT rel : SecOrder,
         REL rel = true /\
          is_in_pred_l (preds_in (conjSO rel atm))
                       (preds_in (conjSO alpha1 alpha2)) = true /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
          SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv)))).
Proof.
  intros alpha1 alpha2 lv1 rel1  lv2  atm2
        H HREL1 H_1  HAT2 Hin2 H_2 H1.
     exists (app 
                (rename_FOv_A_list atm2
                     (list_closed_exFO rel1 lv1) lv2)
(rename_FOv_A_list rel1 
                  (rename_FOv_A  atm2
                     (list_closed_exFO rel1 lv1) lv2) lv1 )).

    exists (rename_FOv_A atm2 (list_closed_exFO rel1 lv1) lv2).
    apply pair.
      pose proof (same_struc_rename_FOv_A atm2 (list_closed_exFO rel1 lv1)
         lv2) as Hsame2.
      apply same_struc_comm in Hsame2.
      apply same_struc_AT in Hsame2; try assumption.

    exists (rename_FOv_A rel1 (rename_FOv_A atm2 (list_closed_exFO rel1 lv1) lv2) lv1).
    apply conj.
      pose proof (same_struc_rename_FOv_A rel1
         (rename_FOv_A (atm2)
            (list_closed_exFO rel1 lv1) lv2) lv1) as Hsame1.
      apply same_struc_comm in Hsame1.
      apply same_struc_REL in Hsame1; try assumption.

    apply conj.
      simpl. do 2 rewrite preds_in_rename_FOv_A in *.
      apply is_in_pred_l_2app.
      rewrite preds_in_rel. reflexivity. assumption.
      assumption.

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
Defined.

Lemma is_in_pred_l_app_cons_rear : forall l1 l2 a l,
  is_in_pred_l (app l1 (cons a l2)) l =
  is_in_pred_l (cons a (app l1 l2)) l.
Proof.
  induction l1; intros l2 P l.
    simpl. reflexivity.

    simpl. rewrite IHl1. simpl.
    case (is_in_pred a l). reflexivity.
    rewrite if_then_else_false. reflexivity.
Qed.

Lemma is_in_pred_l_app_comm_l : forall l1 l2 l,
  is_in_pred_l (app l1 l2) l =
  is_in_pred_l (app l2 l1) l.
Proof.
  induction l1; intros l2 l.
    simpl. rewrite List.app_nil_r.
    reflexivity.

    rewrite is_in_pred_l_app_cons_rear.
    simpl. rewrite IHl1. reflexivity.
Qed.

Lemma is_in_pred_l_app_rear1 : forall l1 l2 l3 l,
  is_in_pred_l (app (app l1 l2) l3) l =
  is_in_pred_l (app (app l1 l3) l2) l.
Proof.
  induction l1; intros l2 l3 l.
    simpl. apply is_in_pred_l_app_comm_l.
    simpl. rewrite IHl1. reflexivity.
Qed.

Lemma is_in_pred_l_app_rear2 : forall l1 l2 l3 l4 l,
  is_in_pred_l (app (app l1 l2) (app l3 l4)) l =
  is_in_pred_l (app (app l1 l3) (app l2 l4)) l.
Proof.
  induction l1; intros l2 l3 l4 l.
    simpl.
    rewrite is_in_pred_l_app_comm_l.
    rewrite is_in_pred_l_app_rear1.
    rewrite app_assoc. reflexivity.

    simpl. rewrite IHl1. reflexivity.
Qed.

Lemma preprocess_vsSahlq_ante_2_againTRY : forall alpha1 alpha2 lv1 rel1 atm1 
                                       lv2 rel2,
  conjSO_exFO_relatSO alpha2 = true ->
  REL rel1 = true ->
  AT atm1 = true ->
  is_in_pred_l (preds_in (conjSO rel1 atm1)) (preds_in alpha1) = true ->
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
  existsT2 lv : list FOvariable,
   (existsT2 atm : SecOrder,
       (AT atm = true) *
      (existsT2 rel : SecOrder,
          REL rel = true /\
          is_in_pred_l (preds_in (conjSO rel atm))
                       (preds_in (conjSO alpha1 alpha2)) = true /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
          SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv)))). 
Proof.
  intros alpha1 alpha2 lv1 rel1 atm1 lv2 rel2 H HREL1 HAT1 Hin H_1
         HREL2 H_2 H1.
    destruct (same_struc_conjSO_ex _ _ _ (same_struc_rename_FOv_A (conjSO rel1 atm1) 
                                            (rename_FOv_A rel2 
                                               (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1))
      as [rel1' [atm1' Heq1]].
     exists (app 
                (rename_FOv_A_list rel2 
                     (list_closed_exFO (conjSO rel1 atm1) lv1) lv2)
(rename_FOv_A_list (conjSO rel1 atm1) 
                  (rename_FOv_A rel2
                     (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1 )).

    exists atm1'.
    apply pair.
      pose proof (same_struc_rename_FOv_A rel2 (list_closed_exFO (conjSO rel1 atm1) lv1)
         lv2) as Hsame2.
      pose proof (same_struc_rename_FOv_A (conjSO rel1 atm1)
         (rename_FOv_A rel2
            (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1) as Hsame1.
      rewrite Heq1 in Hsame1.
      apply same_struc_comm in Hsame2.
      apply same_struc_conjSO_r in Hsame1.
      apply same_struc_comm in Hsame1.
      apply same_struc_AT in Hsame1; try assumption.

    exists (conjSO rel1' (rename_FOv_A rel2 (list_closed_exFO (conjSO rel1 atm1) lv1) lv2)) .
    apply conj.
      pose proof (same_struc_rename_FOv_A rel2 (list_closed_exFO (conjSO rel1 atm1) lv1)
         lv2) as Hsame2.
      pose proof (same_struc_rename_FOv_A (conjSO rel1 atm1)
         (rename_FOv_A rel2
            (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1) as Hsame1.
      rewrite Heq1 in Hsame1.
      apply same_struc_comm in Hsame2.
      apply same_struc_REL in Hsame2; try assumption.
      apply same_struc_conjSO_l in Hsame1.
      apply same_struc_comm in Hsame1.
      apply same_struc_REL in Hsame1; try assumption.
      simpl; rewrite Hsame1; assumption. 

    apply conj.
      assert (preds_in (rename_FOv_A (conjSO rel1 atm1)
                        (rename_FOv_A rel2   
                      (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1) =
                       preds_in (conjSO rel1' atm1')) as Hpreds.
        rewrite Heq1. reflexivity.
      simpl. rewrite preds_in_rename_FOv_A in *.
      rewrite is_in_pred_l_app_rear1. 
      assert (preds_in (conjSO rel1' atm1') = 
              app (preds_in rel1') (preds_in atm1')) as Hpreds1.
        reflexivity.
      rewrite <- Hpreds1.
      rewrite <- Hpreds.
      apply is_in_pred_l_2app.
        assumption.
      rewrite preds_in_rel. reflexivity. assumption.

    intros W Iv Ip Ir.
    split; intros SOt.
      apply (equiv_list_closed_exFO 
                (conjSO (conjSO rel1' (rename_FOv_A rel2 (list_closed_exFO (conjSO rel1 atm1) lv1) lv2)) atm1')
                        (conjSO (conjSO rel1' atm1') (rename_FOv_A rel2 (list_closed_exFO (conjSO rel1 atm1) lv1) lv2))).
      apply equiv_conjSO4.
      rewrite <- Heq1.
      rewrite list_closed_exFO_app.
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
Defined.


Lemma preprocess_vsSahlq_ante_8_againTRY : forall alpha1 alpha2 lv1 atm1 
        lv2 rel2,
  conjSO_exFO_relatSO alpha2 = true ->
  AT atm1 = true ->
  is_in_pred_l (preds_in atm1) (preds_in alpha1) = true ->
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
existsT2 lv : list FOvariable,
   (existsT2 atm : SecOrder,
       (AT atm = true) *
    (existsT rel : SecOrder,
       REL rel = true /\
          is_in_pred_l (preds_in (conjSO rel atm))
                       (preds_in (conjSO alpha1 alpha2)) = true /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
          SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv)))).
Proof.
  intros alpha1 alpha2 lv1 atm1 lv2 rel2
        H HAT1 Hin H_1 HREL2 H_2 H1.
     exists (app 
                (rename_FOv_A_list rel2 
                     (list_closed_exFO atm1 lv1) lv2)
(rename_FOv_A_list atm1
                  (rename_FOv_A rel2
                     (list_closed_exFO atm1 lv1) lv2) lv1 )).

    exists (rename_FOv_A atm1 (rename_FOv_A rel2 (list_closed_exFO atm1 lv1) lv2) lv1).
    apply pair.
      pose proof (same_struc_rename_FOv_A rel2 (list_closed_exFO atm1 lv1)
         lv2) as Hsame2.
      pose proof (same_struc_rename_FOv_A atm1
         (rename_FOv_A rel2
            (list_closed_exFO atm1 lv1) lv2) lv1) as Hsame1.
      apply same_struc_comm in Hsame1.
      apply same_struc_AT in Hsame1; try assumption.

    exists (rename_FOv_A rel2 (list_closed_exFO atm1 lv1) lv2).
    apply conj.
      pose proof (same_struc_rename_FOv_A rel2 (list_closed_exFO atm1 lv1)
         lv2) as Hsame2.
      apply same_struc_comm in Hsame2.
      apply same_struc_REL in Hsame2; try assumption.

    apply conj.
      simpl. do 2 rewrite preds_in_rename_FOv_A.
      rewrite is_in_pred_l_app_comm_l.
      apply is_in_pred_l_2app. assumption.
      rewrite preds_in_rel. reflexivity. assumption.

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
Defined.

Lemma preprocess_vsSahlq_ante_1_againTRY : forall alpha1 alpha2 lv1 rel1 atm1 
        lv2 rel2 atm2,
  conjSO_exFO_relatSO alpha2 = true ->
  REL rel1 = true ->
  AT atm1 = true ->
  is_in_pred_l (preds_in (conjSO rel1 atm1)) (preds_in alpha1) = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha1 <->
      SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel1 atm1) lv1)) ->
  REL rel2 = true ->
  AT atm2 = true ->
  is_in_pred_l (preds_in (conjSO rel2 atm2)) (preds_in alpha2) = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha2 <->
      SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel2 atm2) lv2)) ->
  conjSO_exFO_relatSO alpha1 = true ->
existsT2 lv : list FOvariable,
    (existsT2 atm : SecOrder,
       (AT atm = true) *
      (existsT rel : SecOrder,
         REL rel = true /\
          is_in_pred_l (preds_in (conjSO rel atm))
                       (preds_in (conjSO alpha1 alpha2)) = true /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
          SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv)))).
Proof.
  intros alpha1 alpha2 lv1 rel1 atm1 lv2 rel2 atm2
        H HREL1 HAT1 Hin1 H_1 HREL2 HAT2 Hin2 H_2 H1.
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

    exists (conjSO atm1' atm2').
    apply pair.
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

    apply conj.
      simpl.
      assert (preds_in (rename_FOv_A (conjSO rel1 atm1)
                        (rename_FOv_A (conjSO rel2 atm2)   
                      (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1) =
                       preds_in (conjSO rel1' atm1')) as Hpreds.
        rewrite Heq1. reflexivity.
      assert (preds_in (rename_FOv_A (conjSO rel2 atm2)
                      (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) =
                       preds_in (conjSO rel2' atm2')) as Hpreds0.
        rewrite Heq2. reflexivity.
      simpl. rewrite preds_in_rename_FOv_A in *.
      rewrite is_in_pred_l_app_rear2. 
      assert (preds_in (conjSO rel1' atm1') = 
              app (preds_in rel1') (preds_in atm1')) as Hpreds1.
        reflexivity.
       assert (preds_in (conjSO rel2' atm2') = 
              app (preds_in rel2') (preds_in atm2')) as Hpreds2.
        reflexivity.
     rewrite <- Hpreds1.
     rewrite <- Hpreds2.
      rewrite <- Hpreds.
      rewrite <- Hpreds0.
      apply is_in_pred_l_2app;
        assumption.

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
Defined.

Lemma preprocess_vsSahlq_ante_3_againTRY : forall alpha1 alpha2 lv1 rel1 atm1 lv2 atm2,
  conjSO_exFO_relatSO alpha2 = true ->
  REL rel1 = true ->
  AT atm1 = true ->
  is_in_pred_l (preds_in (conjSO rel1 atm1)) (preds_in alpha1) = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha1 <->
      SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel1 atm1) lv1)) ->
  AT atm2 = true ->
  is_in_pred_l (preds_in atm2) (preds_in alpha2) = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha2 <->
      SOturnst W Iv Ip Ir (list_closed_exFO atm2 lv2)) ->
  conjSO_exFO_relatSO alpha1 = true ->
existsT2 lv : list FOvariable,
  (existsT2 atm : SecOrder,
     (AT atm = true) *
    (existsT rel : SecOrder,
       REL rel = true /\
          is_in_pred_l (preds_in (conjSO rel atm))
                       (preds_in (conjSO alpha1 alpha2)) = true /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
          SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv)))). 
Proof.
  intros alpha1 alpha2 lv1 rel1 atm1 lv2 atm2
         H HREL1 HAT1 Hin1 H_1 HAT2 Hin2 H_2 H1.
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

    exists (conjSO atm1' (rename_FOv_A atm2 (list_closed_exFO (conjSO rel1 atm1) lv1)
         lv2)).
    apply pair.
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

    exists rel1'.
    apply conj.
      pose proof (same_struc_rename_FOv_A atm2 (list_closed_exFO (conjSO rel1 atm1) lv1)
         lv2) as Hsame2.
      pose proof (same_struc_rename_FOv_A (conjSO rel1 atm1)
         (rename_FOv_A atm2
            (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1) as Hsame1.
      rewrite Heq1 in Hsame1.
      apply same_struc_conjSO_l in Hsame1.
      apply same_struc_comm in Hsame1.
      apply same_struc_REL in Hsame1; try assumption.

    apply conj.
      simpl.
      assert (preds_in (rename_FOv_A (conjSO rel1 atm1)
                        (rename_FOv_A (atm2)   
                      (list_closed_exFO (conjSO rel1 atm1) lv1) lv2) lv1) =
                       preds_in (conjSO rel1' atm1')) as Hpreds.
        rewrite Heq1. reflexivity.
      simpl. rewrite preds_in_rename_FOv_A in *.
      rewrite <- app_assoc.
      assert (preds_in (conjSO rel1' atm1') = 
              app (preds_in rel1') (preds_in atm1')) as Hpreds1.
        reflexivity.
     rewrite <- Hpreds1.
      rewrite <- Hpreds.
      apply is_in_pred_l_2app;
        assumption.

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
Defined.


Lemma preprocess_vsSahlq_ante_7_againTRY : forall alpha1 alpha2 lv1 atm1 
        lv2 rel2 atm2,
  conjSO_exFO_relatSO alpha2 = true ->
  AT atm1 = true ->
  is_in_pred_l (preds_in atm1) (preds_in alpha1) = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha1 <->
      SOturnst W Iv Ip Ir (list_closed_exFO atm1 lv1)) ->
  REL rel2 = true ->
  AT atm2 = true ->
  is_in_pred_l (preds_in (conjSO rel2 atm2)) (preds_in alpha2) = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha2 <->
      SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel2 atm2) lv2)) ->
  conjSO_exFO_relatSO alpha1 = true ->
existsT2 lv : list FOvariable,
  (existsT2 atm : SecOrder,
       (AT atm = true) *
    (existsT rel : SecOrder,
       REL rel = true /\
          is_in_pred_l (preds_in (conjSO rel atm))
                       (preds_in (conjSO alpha1 alpha2)) = true /\

         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
          SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv)))).
Proof.
  intros alpha1 alpha2 lv1 atm1 lv2 rel2 atm2
        H HAT1 Hin1 H_1 HREL2 HAT2 Hin2 H_2 H1.
    destruct (same_struc_conjSO_ex _ _ _ (same_struc_rename_FOv_A (conjSO rel2 atm2) 
                                            (list_closed_exFO atm1 lv1)
                                             lv2)) as [rel2' [atm2' Heq2]].
     exists (app 
                (rename_FOv_A_list (conjSO rel2 atm2) 
                     (list_closed_exFO atm1 lv1) lv2)
(rename_FOv_A_list  atm1
                  (rename_FOv_A (conjSO rel2 atm2)
                     (list_closed_exFO  atm1 lv1) lv2) lv1 )).

    exists (conjSO (rename_FOv_A atm1 (rename_FOv_A (conjSO rel2 atm2) 
                        (list_closed_exFO atm1 lv1) lv2) lv1) atm2').
    apply pair.
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

    exists rel2'.
    apply conj.
      pose proof (same_struc_rename_FOv_A (conjSO rel2 atm2) (list_closed_exFO atm1 lv1)
         lv2) as Hsame2.
      rewrite Heq2 in Hsame2.
      apply same_struc_conjSO_l in Hsame2.
      apply same_struc_comm in Hsame2.
      apply same_struc_REL in Hsame2; try assumption.

    apply conj.
      simpl.
      assert (preds_in (rename_FOv_A (conjSO rel2 atm2)
                      (list_closed_exFO ( atm1) lv1) lv2) =
                       preds_in (conjSO rel2' atm2')) as Hpreds0.
        rewrite Heq2. reflexivity.
      simpl. rewrite preds_in_rename_FOv_A in *.
      rewrite <- app_assoc.
      rewrite <- is_in_pred_l_app_rear1.
      rewrite is_in_pred_l_app_comm_l.
       assert (preds_in (conjSO rel2' atm2') = 
              app (preds_in rel2') (preds_in atm2')) as Hpreds2.
        reflexivity.
     rewrite <- Hpreds2.
      rewrite <- Hpreds0.
      apply is_in_pred_l_2app;
        assumption.

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
Defined.

Lemma preprocess_vsSahlq_ante_9_againTRY : forall alpha1 alpha2 lv1 atm1 
        lv2 atm2,
  conjSO_exFO_relatSO alpha2 = true ->
  AT atm1 = true ->
  is_in_pred_l (preds_in (atm1)) (preds_in alpha1) = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha1 <->
      SOturnst W Iv Ip Ir (list_closed_exFO  atm1 lv1)) ->
  AT atm2 = true ->
  is_in_pred_l (preds_in (atm2)) (preds_in alpha2) = true ->
  (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
        (Ir : W -> W -> Prop),
      SOturnst W Iv Ip Ir alpha2 <->
      SOturnst W Iv Ip Ir (list_closed_exFO atm2 lv2)) ->
  conjSO_exFO_relatSO alpha1 = true ->
existsT2 lv : list FOvariable,
   (existsT2 atm : SecOrder,
       (AT atm = true) *
          (is_in_pred_l (preds_in (atm))
                       (preds_in (conjSO alpha1 alpha2)) = true /\
         (forall (W : Set) (Iv : FOvariable -> W) (Ip : predicate -> W -> Prop)
            (Ir : W -> W -> Prop),
          SOturnst W Iv Ip Ir (conjSO alpha1 alpha2) <->
          SOturnst W Iv Ip Ir (list_closed_exFO (atm) lv)))).
Proof.
  intros alpha1 alpha2 lv1 atm1 lv2 atm2
        H HAT1 Hin1 H_1 HAT2 Hin2 H_2 H1.
     exists (app 
                (rename_FOv_A_list atm2
                     (list_closed_exFO atm1 lv1) lv2)
(rename_FOv_A_list atm1
                  (rename_FOv_A atm2
                     (list_closed_exFO atm1 lv1) lv2) lv1 )).

    exists (conjSO (rename_FOv_A atm1 (rename_FOv_A atm2 (list_closed_exFO atm1 lv1) lv2)
              lv1) (rename_FOv_A atm2 (list_closed_exFO atm1 lv1) lv2)
).
    apply pair.
      pose proof (same_struc_rename_FOv_A atm2 (list_closed_exFO atm1 lv1)
         lv2) as Hsame2.
      pose proof (same_struc_rename_FOv_A atm1
         (rename_FOv_A atm2
            (list_closed_exFO atm1 lv1) lv2) lv1) as Hsame1.
      apply same_struc_comm in Hsame2.
      apply same_struc_AT in Hsame2; try assumption.
      apply same_struc_comm in Hsame1.
      apply same_struc_AT in Hsame1; try assumption.
      simpl; rewrite Hsame1. assumption.

    apply conj.
      simpl.
      simpl. do 2  rewrite preds_in_rename_FOv_A in *.
      apply is_in_pred_l_2app;
        assumption.

    intros W Iv Ip Ir.
    split; intros SOt.
      rewrite list_closed_exFO_app.
      apply equiv3_3_struc2_both with (alpha :=  atm1).
      simpl.
      apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.

      rewrite list_closed_exFO_app in SOt.
      apply equiv3_3_struc2_both with (alpha := atm1) in SOt.
      simpl.
      apply conj.
        apply H_1. apply SOt.
        apply H_2. apply SOt.
Defined.

Lemma preprocess_vsSahlq_ante_againTRY : forall alpha,
  conjSO_exFO_relatSO alpha = true ->
  (existsT P, P_occurs_in_alpha alpha P = true) ->
  existsT2 lv atm,
    (AT atm = true) *
    ((existsT rel,
      REL rel = true /\
      is_in_pred_l (preds_in (conjSO rel atm)) (preds_in alpha) = true /\
        forall W Iv Ip Ir,
          SOturnst W Iv Ip Ir alpha <->
          SOturnst W Iv Ip Ir (list_closed_exFO (conjSO rel atm) lv)) +
     (is_in_pred_l (preds_in atm) (preds_in alpha) = true /\
        forall W Iv Ip Ir,
          SOturnst W Iv Ip Ir alpha <->
          SOturnst W Iv Ip Ir (list_closed_exFO atm lv))).
Proof.
  intros alpha H Hocc.
  induction alpha; try (simpl in *; discriminate).
    apply preprocess_vsSahlq_ante_predSO_againTRY; assumption.

    destruct Hocc as [[Pn] Hocc].
    unfold P_occurs_in_alpha in Hocc. destruct f. destruct f0.
    simpl in Hocc. discriminate.

    apply preprocess_vsSahlq_ante_exFO_againTRY; assumption.

    simpl in H.
    case_eq (conjSO_exFO_relatSO alpha1); intros H1;
      rewrite H1 in H; try discriminate.
    specialize (IHalpha1 H1).
    specialize (IHalpha2 H).
    destruct (trying1 alpha1) as [Hocc1 | Hocc2].
    destruct (preprocess_vsSahlq_ante_notocc_againTRY _ H1 Hocc1)
      as [lv1 [rel1 [Hrel1 [Hin1 SOt]]]].
    destruct IHalpha2 as [lv2 [atm2 [Hat2 [[rel2 [Hrel2 [Hin H2]]] | [Hin H2]]]]].
      destruct Hocc as [P Hocc].
      apply P_occurs_in_alpha_conjSO_comp in Hocc.
      rewrite (Hocc1 P) in Hocc.
      destruct Hocc. discriminate.
      exists P. assumption.

      destruct (preprocess_vsSahlq_ante_4_againTRY alpha1 alpha2 lv1 rel1 lv2 rel2 atm2)
        as [lv' [atm' [Hat' [rel' [Hrel' [Hin' H']]]]]]; try assumption.
      exists lv'. exists atm'. apply pair. assumption.
      left. exists rel'. apply conj. assumption.
      apply conj. all: try assumption.

      destruct (preprocess_vsSahlq_ante_6_againTRY alpha1 alpha2 lv1 rel1 lv2 atm2)
        as [lv' [atm' [Hat' [rel' [Hrel' [Hin' H']]]]]]; try assumption.
      exists lv'. exists atm'. apply pair. assumption.
      left. exists rel'. apply conj. assumption.
      apply conj. all: try assumption.

    destruct (trying1 alpha2) as [Hocc1b | Hocc2b].
    destruct (preprocess_vsSahlq_ante_notocc_againTRY _ H Hocc1b)
      as [lv2 [rel2 [Hrel2 [Hin2 SOt]]]].
    destruct IHalpha1 as [lv1 [atm1 [Hat1 [[rel1 [Hrel1 [Hin H2]]] | [Hin H2]]]]].
      assumption.

      destruct (preprocess_vsSahlq_ante_2_againTRY alpha1 alpha2 lv1 rel1 atm1 lv2 rel2)
        as [lv' [atm' [Hat' [rel' [Hrel' [Hin' H']]]]]]; try assumption.
      exists lv'. exists atm'. apply pair. assumption.
      left. exists rel'. apply conj. assumption.
      apply conj. all: try assumption.

      destruct (preprocess_vsSahlq_ante_8_againTRY alpha1 alpha2 lv1 atm1 lv2 rel2)
        as [lv' [atm' [Hat' [rel' [Hrel' [Hin' H']]]]]]; try assumption.
      exists lv'. exists atm'. apply pair. assumption.
      left. exists rel'. apply conj. assumption.
      apply conj. all: try assumption.

      destruct (IHalpha1 Hocc2) as [lv1 [atm1 [Hatm1 [[rel1 [Hrel1 [Hin SOt]] ] | [Hin SOt ] ]]] ].
      destruct (IHalpha2 Hocc2b) as [lv2 [atm2 [Hatm2 [[rel2 [Hrel2 [Hin2 SOt2]] ] | [Hin2 SOt2 ] ]]] ].

      destruct (preprocess_vsSahlq_ante_1_againTRY alpha1 alpha2 lv1 rel1 atm1 lv2 rel2 atm2)
        as [lv' [atm' [Hat' [rel' [Hrel' [Hin' H']]]]]]; try assumption.
      exists lv'. exists atm'. apply pair. assumption.
      left. exists rel'. apply conj. assumption.
      apply conj. all: try assumption.

      destruct (preprocess_vsSahlq_ante_3_againTRY alpha1 alpha2 lv1 rel1 atm1 lv2 atm2)
        as [lv' [atm' [Hat' [rel' [Hrel' [Hin' H']]]]]]; try assumption.
      exists lv'. exists atm'. apply pair. assumption.
      left. exists rel'. apply conj. assumption.
      apply conj. all: try assumption.

      destruct (IHalpha2 Hocc2b) as [lv2 [atm2 [Hatm2 [[rel2 [Hrel2 [Hin2 SOt2]] ] | [Hin2 SOt2 ] ]]] ].

      destruct (preprocess_vsSahlq_ante_7_againTRY alpha1 alpha2 lv1 atm1 lv2 rel2 atm2)
        as [lv' [atm' [Hat' [rel' [Hrel' [Hin' H']]]]]]; try assumption.
      exists lv'. exists atm'. apply pair. assumption.
      left. exists rel'. apply conj. assumption.
      apply conj. all: try assumption.

      destruct (preprocess_vsSahlq_ante_9_againTRY alpha1 alpha2 lv1 atm1 lv2 atm2)
        as [lv' [atm' [Hat' [Hin' H']]]]; try assumption.
      exists lv'. exists atm'. apply pair. assumption.
      right. apply conj. assumption.
      assumption.
Defined.

Lemma ex_P_ST : forall phi x,
  existsT P, P_occurs_in_alpha (ST phi x) P = true.
Proof.
  induction phi; intros x.
    exists (ST_pv p).
    simpl. destruct p. destruct x.
    unfold P_occurs_in_alpha. simpl.
    rewrite <- beq_nat_refl. reflexivity.

    simpl. destruct (IHphi x) as [P H].
    exists P. rewrite <- P_occurs_in_alpha_negSO.
    assumption.

    destruct (IHphi1 x) as [P H].
    exists P. simpl. apply P_occurs_in_alpha_conjSO.
    left. assumption.

    destruct (IHphi1 x) as [P H].
    exists P. simpl. apply P_occurs_in_alpha_conjSO.
    left. assumption.

    destruct (IHphi1 x) as [P H].
    exists P. simpl. apply P_occurs_in_alpha_conjSO.
    left. assumption.

    simpl. destruct x as [xn]. destruct (IHphi (Var (xn + 1)))
      as [P H]. exists P. rewrite <- P_occurs_in_alpha_allFO.
    destruct (P_occurs_in_alpha_implSO (relatSO (Var xn) (Var (xn + 1)))
      (ST phi (Var (xn + 1))) P) as [fwd rev]. apply rev.
    right. assumption.

    simpl. destruct x as [xn]. destruct (IHphi (Var (xn + 1)))
      as [P H]. exists P. rewrite <- P_occurs_in_alpha_exFO.
    apply P_occurs_in_alpha_conjSO.
    right. assumption.
Defined.

Lemma hopeful3 : forall lx lP beta alpha rel atm y xn W Iv Ip Ir,
  REL rel = true ->
  AT atm = true ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  attached_allFO_x beta (Var xn) = false ->
  attached_exFO_x beta (Var xn) = false ->
  closed_except beta (Var xn) ->
  x_occ_in_alpha (instant_cons_empty' (conjSO rel atm) beta) (Var xn) = true ->
  is_in_pred_l (preds_in (implSO (conjSO rel atm) beta)) lP = true ->
  (exists P, P_occurs_in_alpha alpha P = true) ->
 (forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir alpha <-> SOturnst W Iv Ip Ir (list_closed_allFO (implSO (conjSO rel atm) beta) lx)) ->
  SOturnst W Iv Ip Ir (list_closed_SO alpha lP) ->
  SOturnst W Iv Ip Ir (replace_pred_l (list_closed_allFO (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) beta)  
      (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) beta)) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) beta)) (Var xn)))))) lx)
    lP (list_Var (length lP) y)
    (vsS_syn_l (FOv_att_P_l (conjSO rel atm) lP) y)).
Proof.
  intros lx lP beta alpha rel atm y xn W Iv Ip Ir HREL HAT Hun Hno Hat1 Hat2
    Hc Hocc Hin Hpocc Hequiv SOt.
  apply vsSahlq_instant_aim1_fwd4_closer2; try assumption.
  pose proof (equiv_list_closed_SO lP  _ _ Hequiv) as H.
  apply H.
  assumption.
Qed.

Lemma hopeful3_atm : forall lx lP beta alpha atm y xn W Iv Ip Ir,
  AT atm = true ->
  uniform_pos_SO beta ->
  SOQFree beta = true ->
  attached_allFO_x beta (Var xn) = false ->
  attached_exFO_x beta (Var xn) = false ->
  closed_except beta (Var xn) ->
  x_occ_in_alpha (instant_cons_empty' atm beta) (Var xn) = true ->
  is_in_pred_l (preds_in (implSO atm beta)) lP = true ->
  (exists P, P_occurs_in_alpha alpha P = true) ->
 (forall W Iv Ip Ir,
    SOturnst W Iv Ip Ir alpha <-> SOturnst W Iv Ip Ir (list_closed_allFO (implSO atm beta) lx)) ->
  SOturnst W Iv Ip Ir (list_closed_SO alpha lP) ->
  SOturnst W Iv Ip Ir (replace_pred_l (list_closed_allFO (implSO
    atm
    (newnew_pre (instant_cons_empty' atm beta)  
      (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn))
      (rev_seq (S (max (max_FOv (implSO atm beta)) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' atm beta)) (Var xn)))))) lx)
    lP (list_Var (length lP) y)
    (vsS_syn_l (FOv_att_P_l atm lP) y)).
Proof.
  intros lx lP beta alpha atm y xn W Iv Ip Ir HAT Hun Hno Hat1 Hat2
    Hc Hocc Hin Hpocc Hequiv SOt.
  apply vsSahlq_instant_aim1_fwd4_closer2_atm; try assumption.
  pose proof (equiv_list_closed_SO lP  _ _ Hequiv) as H.
  apply H.
  assumption.
Qed.

Lemma x_occ_in_alpha_att_allFO_x : forall alpha x,
 x_occ_in_alpha alpha x = false ->
  attached_allFO_x alpha x = false.
Proof.
  induction alpha; intros [xn] Hocc;
    try (simpl; reflexivity).

    destruct f as [ym]. simpl in *.
    case_eq (beq_nat xn ym); intros Hbeq;
      rewrite Hbeq in *. discriminate.
    apply IHalpha. assumption.

    destruct f as [ym]. simpl in *.
    case_eq (beq_nat xn ym); intros Hbeq;
      rewrite Hbeq in *. discriminate.
    apply IHalpha. assumption.

    simpl in *. apply IHalpha. assumption.

    apply x_occ_in_alpha_conjSO in Hocc.
    simpl. rewrite IHalpha1. apply IHalpha2.
    all : try apply Hocc.

    apply x_occ_in_alpha_conjSO in Hocc.
    simpl. rewrite IHalpha1. apply IHalpha2.
    all : try apply Hocc.

    apply x_occ_in_alpha_conjSO in Hocc.
    simpl. rewrite IHalpha1. apply IHalpha2.
    all : try apply Hocc.

    simpl in *. apply IHalpha. assumption.

    simpl in *. apply IHalpha. assumption.
Qed.

Lemma x_occ_in_alpha_att_exFO_x : forall alpha x,
 x_occ_in_alpha alpha x = false ->
  attached_exFO_x alpha x = false.
Proof.
  induction alpha; intros [xn] Hocc;
    try (simpl; reflexivity).

    destruct f as [ym]. simpl in *.
    case_eq (beq_nat xn ym); intros Hbeq;
      rewrite Hbeq in *. discriminate.
    apply IHalpha. assumption.

    destruct f as [ym]. simpl in *.
    case_eq (beq_nat xn ym); intros Hbeq;
      rewrite Hbeq in *. discriminate.
    apply IHalpha. assumption.

    simpl in *. apply IHalpha. assumption.

    apply x_occ_in_alpha_conjSO in Hocc.
    simpl. rewrite IHalpha1. apply IHalpha2.
    all : try apply Hocc.

    apply x_occ_in_alpha_conjSO in Hocc.
    simpl. rewrite IHalpha1. apply IHalpha2.
    all : try apply Hocc.

    apply x_occ_in_alpha_conjSO in Hocc.
    simpl. rewrite IHalpha1. apply IHalpha2.
    all : try apply Hocc.

    simpl in *. apply IHalpha. assumption.

    simpl in *. apply IHalpha. assumption.
Qed.

Lemma x_occ_in_alpha_ST_leb : forall phi m n,
  Nat.leb (S m) n = true ->
  x_occ_in_alpha (ST phi (Var n)) (Var m) = false.
Proof.
  induction phi; intros m n Hleb.
    destruct p. simpl.
    case_eq (beq_nat m n); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq) in *.
      rewrite leb_suc_f in Hleb. discriminate.

      reflexivity.

    simpl. apply IHphi. assumption.

    simpl. rewrite IHphi1. apply IHphi2.
    all : try assumption.

    simpl. rewrite IHphi1. apply IHphi2.
    all : try assumption.

    simpl. rewrite IHphi1. apply IHphi2.
    all : try assumption.

    simpl. case_eq (beq_nat m (n + 1)); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq) in Hleb.
      apply leb_suc_l in Hleb.
      rewrite <- one_suc in Hleb.
      rewrite leb_suc_f in Hleb.
      discriminate.

      case_eq (beq_nat m n); intros Hbeq2.
        rewrite (beq_nat_true _ _ Hbeq2) in Hleb.
        rewrite leb_suc_f in Hleb. discriminate.

        apply IHphi. rewrite <- one_suc.
        apply leb_suc_r. assumption.

    simpl. case_eq (beq_nat m (n + 1)); intros Hbeq.
      rewrite (beq_nat_true _ _ Hbeq) in Hleb.
      apply leb_suc_l in Hleb.
      rewrite <- one_suc in Hleb.
      rewrite leb_suc_f in Hleb.
      discriminate.

      case_eq (beq_nat m n); intros Hbeq2.
        rewrite (beq_nat_true _ _ Hbeq2) in Hleb.
        rewrite leb_suc_f in Hleb. discriminate.

        apply IHphi. rewrite <- one_suc.
        apply leb_suc_r. assumption.
Qed.



Lemma att_allFO_x_ST : forall phi x,
  attached_allFO_x (ST phi x) x = false.
Proof.
  induction phi; intros x.
    destruct p; destruct x. reflexivity.

    simpl. apply IHphi.

    simpl. rewrite IHphi1. rewrite IHphi2.
    reflexivity.

    simpl. rewrite IHphi1. rewrite IHphi2.
    reflexivity.

    simpl. rewrite IHphi1. rewrite IHphi2.
    reflexivity.

    simpl. destruct x. simpl.
    rewrite beq_nat_comm. rewrite beq_nat_suc_false.
    apply x_occ_in_alpha_att_allFO_x.
    apply x_occ_in_alpha_ST_leb.
    rewrite one_suc.
    apply leb_refl.

    simpl. destruct x. simpl.
    apply x_occ_in_alpha_att_allFO_x.
    apply x_occ_in_alpha_ST_leb.
    rewrite one_suc.
    apply leb_refl.
Qed.


Lemma att_exFO_x_ST : forall phi x,
  attached_exFO_x (ST phi x) x = false.
Proof.
  induction phi; intros x.
    destruct p; destruct x. reflexivity.

    simpl. apply IHphi.

    simpl. rewrite IHphi1. rewrite IHphi2.
    reflexivity.

    simpl. rewrite IHphi1. rewrite IHphi2.
    reflexivity.

    simpl. rewrite IHphi1. rewrite IHphi2.
    reflexivity.

    simpl. destruct x. simpl.
    apply x_occ_in_alpha_att_exFO_x.
    apply x_occ_in_alpha_ST_leb.
    rewrite one_suc.
    apply leb_refl.

    simpl. destruct x. simpl.
    rewrite beq_nat_comm. rewrite beq_nat_suc_false.
    apply x_occ_in_alpha_att_exFO_x.
    apply x_occ_in_alpha_ST_leb.
    rewrite one_suc.
    apply leb_refl.

Qed.

Lemma closed_except_ST : forall phi x,
  closed_except (ST phi x) x.
Proof.
  induction phi; intros [xn]; unfold closed_except in *.
    destruct p. simpl.
    apply conj. symmetry. apply beq_nat_refl.

    intros [ym]. rewrite beq_nat_comm. apply FOvar_neq.

    simpl. apply IHphi.

    destruct (IHphi1 (Var xn)) as [H1 H2].
    destruct (IHphi2 (Var xn)) as [H1' H2'].
    simpl.
    apply conj. rewrite H1. reflexivity.
    intros [ym] H. rewrite H2. apply H2'.
    all : try assumption.

    destruct (IHphi1 (Var xn)) as [H1 H2].
    destruct (IHphi2 (Var xn)) as [H1' H2'].
    simpl.
    apply conj. rewrite H1. reflexivity.
    intros [ym] H. rewrite H2. apply H2'.
    all : try assumption.

    destruct (IHphi1 (Var xn)) as [H1 H2].
    destruct (IHphi2 (Var xn)) as [H1' H2'].
    simpl.
    apply conj. rewrite H1. reflexivity.
    intros [ym] H. rewrite H2. apply H2'.
    all : try assumption.

    simpl. rewrite beq_nat_comm. rewrite beq_nat_suc_false.
    rewrite <- beq_nat_refl.
    apply conj. reflexivity.
    intros [ym] H. case_eq (beq_nat ym (xn + 1)); intros Hbeq.
      reflexivity.
    rewrite beq_nat_comm. rewrite FOvar_neq.
    apply IHphi. rewrite beq_nat_comm in Hbeq.
    apply beq_nat_false_FOv in Hbeq. all : try assumption.

    simpl. rewrite beq_nat_comm. rewrite beq_nat_suc_false.
    rewrite <- beq_nat_refl.
    apply conj. reflexivity.
    intros [ym] H. case_eq (beq_nat ym (xn + 1)); intros Hbeq.
      reflexivity.
    rewrite beq_nat_comm. rewrite FOvar_neq.
    apply IHphi. rewrite beq_nat_comm in Hbeq.
    apply beq_nat_false_FOv in Hbeq. all : try assumption.
Qed.

Lemma x_occ_in_alpha_ST : forall phi x,
  x_occ_in_alpha (ST phi x) x = true.
Proof.
  induction phi; intros [xn].
    destruct p.
    simpl. rewrite <- beq_nat_refl. reflexivity.

    simpl. apply IHphi.

    simpl. rewrite IHphi1. reflexivity.

    simpl. rewrite IHphi1. reflexivity.

    simpl. rewrite IHphi1. reflexivity.

    simpl. rewrite beq_nat_comm.
    rewrite beq_nat_suc_false.
    rewrite <- beq_nat_refl. reflexivity.

    simpl. rewrite beq_nat_comm.
    rewrite beq_nat_suc_false.
    rewrite <- beq_nat_refl. reflexivity.
Qed.

Lemma ex_P_occ_in_alpha_ST : forall phi x,
  exists P, P_occurs_in_alpha (ST phi x) P = true.
Proof.
  induction phi; intros [xn]. 
    exists (ST_pv p). 
    destruct p. unfold P_occurs_in_alpha. simpl.
    rewrite <- beq_nat_refl. reflexivity.

    simpl. destruct (IHphi (Var xn)) as [P IH].
    exists P. rewrite <- P_occurs_in_alpha_negSO.
    assumption.

    simpl. destruct (IHphi1 (Var xn)) as [P IH1].
    exists P.  apply P_occurs_in_alpha_conjSO.
    left. assumption.

    simpl. destruct (IHphi1 (Var xn)) as [P IH1].
    exists P.  apply P_occurs_in_alpha_conjSO.
    left. assumption.

    simpl. destruct (IHphi1 (Var xn)) as [P IH1].
    exists P.  apply P_occurs_in_alpha_conjSO.
    left. assumption.

    simpl. destruct (IHphi (Var (xn+1))) as [P IH].
    exists P. rewrite <- P_occurs_in_alpha_allFO.
    destruct (P_occurs_in_alpha_implSO (relatSO (Var xn) (Var (xn + 1)))
      (ST phi (Var (xn + 1))) P) as [fwd rev].
    apply rev. right. assumption.

    simpl. destruct (IHphi (Var (xn+1))) as [P IH].
    exists P. rewrite <- P_occurs_in_alpha_exFO.
    apply P_occurs_in_alpha_conjSO.
    right. assumption.
Qed.


(* -------------------------------------------- *)


Lemma try3 : forall alpha beta a x P,
  (replace_pred (replace_pred alpha a x (fun1 (fun2 beta a) x)) P x
     (fun1 (fun2 beta P) x)) =
(replace_pred (replace_pred alpha P x (fun1 (fun2 beta P) x)) a x
     (fun1 (fun2 beta a) x)).
Proof.
  intros alpha beta [Pn] [xn] [Qm].
  case_eq (beq_nat Pn Qm); intros Hbeq.
    rewrite (beq_nat_true _ _ Hbeq). reflexivity.

    rewrite (rep_pred_switch _ _ _ _ _(Pred Pn) (Pred Qm)).
    reflexivity.
      apply un_predless_fun1.
      apply un_predless_fun1.
      intros H. rewrite H in Hbeq. rewrite <-beq_nat_refl in Hbeq.
      discriminate.
Qed.
 
Lemma try2 : forall lP2 alpha beta P x,
  replace_pred (replace_pred_l  alpha lP2 (list_Var (length lP2) x) 
      (vsS_syn_l (FOv_att_P_l beta lP2) x)) P x (fun1 (fun2 beta P) x) =
  replace_pred_l (replace_pred alpha P x (fun1 (fun2 beta P) x))
      lP2 (list_Var (length lP2) x)  (vsS_syn_l (FOv_att_P_l beta lP2) x).
Proof.
  induction lP2; intros alpha beta P x. reflexivity.
  simpl. rewrite IHlP2. rewrite IHlP2. rewrite IHlP2.
  rewrite try3. reflexivity.
Qed.

Lemma length_list_Var : forall n x,
  length (list_Var n x) = n.
Proof.
  induction n; intros x. reflexivity.
  simpl. rewrite IHn. reflexivity.
Qed.

Lemma length_vsS_syn_l' : forall l x,
  length l = length (vsS_syn_l l x).
Proof.
  induction l; intros x.
    reflexivity.

    simpl. rewrite (IHl x).
    reflexivity.
Qed.

Lemma hopeful6 : forall lP1 lP2 alpha beta x,
is_in_pred_l lP1 lP2 = true ->
is_unary_predless (replace_pred_l alpha lP1 (list_Var (length lP1) x) (vsS_syn_l (FOv_att_P_l beta lP1) x)) = true ->
is_unary_predless (replace_pred_l alpha lP2 (list_Var (length lP2) x) (vsS_syn_l (FOv_att_P_l beta lP2) x)) = true.
Proof.
  induction lP1; intros lP2 alpha beta x Hin Hun.
    simpl in *. apply rep_pred_l_is_unary_predless. assumption.

    simpl in Hin. case_eq (is_in_pred a lP2); intros Hin6;
    rewrite Hin6 in *. 2: discriminate.
    case_eq (is_in_pred a lP1); intros Hin5.
      simpl in Hun.
    destruct (nlist_list_ex (length lP1) lP1 eq_refl) as [lP1' Heq1].
    destruct (nlist_list_ex (length lP1) (list_Var (length lP1) x)) as [lvar Heq2].
      rewrite length_list_Var. reflexivity.
    destruct (nlist_list_ex (length lP1) (vsS_syn_l (FOv_att_P_l beta lP1) x)) as [lfun1 Heq3].
      rewrite <- length_vsS_syn_l'. rewrite <- length_FOv_att_P_l. reflexivity.
    rewrite <- Heq1 in Hun at 1. rewrite <- Heq2 in Hun at 1. rewrite <- Heq3 in Hun.
    rewrite rep_pred__l_is_in in Hun.
    rewrite Heq1 in Hun. rewrite Heq2 in Hun. rewrite Heq3 in Hun.
    apply IHlP1; try assumption.

      rewrite Heq1. assumption.
      rewrite Heq3. apply un_predless_l_vsS_syn_l.
      apply un_predless_fun1.

    simpl in Hun. rewrite rep_pred__l_switch in Hun; try assumption.
    specialize (IHlP1 _ _ _ _ Hin Hun).
    rewrite <- try2 in IHlP1.


    destruct (nlist_list_ex (length lP2) lP2 eq_refl) as [lP1' Heq1].
    destruct (nlist_list_ex (length lP2) (list_Var (length lP2) x)) as [lvar Heq2].
      rewrite length_list_Var. reflexivity.
    destruct (nlist_list_ex (length lP2) (vsS_syn_l (FOv_att_P_l beta lP2) x)) as [lfun1 Heq3].
      rewrite <- length_vsS_syn_l'. rewrite <- length_FOv_att_P_l. reflexivity.
    rewrite <- Heq3 in *. rewrite <- Heq2 in *. rewrite <- Heq1 in *. rewrite <- Heq1 in IHlP1 at 1.
    rewrite rep_pred__l_is_in in IHlP1; try assumption. rewrite <- Heq1 at 1. assumption.
    rewrite Heq3. all : try apply un_predless_l_vsS_syn_l.
    all : try apply un_predless_fun1.
Qed.

Lemma is_un_predless_corresp : forall xn phi1 phi2 y lx atm rel,
    AT atm = true ->
    REL rel = true ->
    is_in_pred_l (preds_in (conjSO rel atm)) (preds_in (ST phi1 (Var xn))) = true ->
  is_unary_predless ((replace_pred_l (list_closed_allFO (implSO
    (conjSO rel atm)
    (newnew_pre (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO (conjSO rel atm) (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' (conjSO rel atm) (ST phi2 (Var xn)))) (Var xn)))))) lx)
    (preds_in (ST (mimpl phi1 phi2) (Var xn))) (list_Var (length (preds_in (ST (mimpl phi1 phi2) (Var xn)))) y)
    (vsS_syn_l (FOv_att_P_l (conjSO rel atm) (preds_in (ST (mimpl phi1 phi2) (Var xn)))) y))) = true.
Proof.
  intros.

  pose proof (hopeful2 lx rel atm y xn (ST phi2 (Var xn))) as HH.
  apply hopeful6 with (lP1 := preds_in(list_closed_allFO (implSO (conjSO rel atm) (ST phi2 (Var xn))) lx)).
  rewrite preds_in_list_closed_allFO.
  simpl.
  apply is_in_pred_l_2app.
  assumption.
  apply is_in_pred_l_refl.

  assumption.
Qed.

Lemma is_un_predless_corresp_atm : forall xn phi1 phi2 y lx atm,
    AT atm = true ->
    is_in_pred_l (preds_in atm) (preds_in (ST phi1 (Var xn))) = true ->
  is_unary_predless ((replace_pred_l (list_closed_allFO (implSO
    atm
    (newnew_pre (instant_cons_empty' atm (ST phi2 (Var xn)))  
      (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn))
      (rev_seq (S (max (max_FOv (implSO atm (ST phi2 (Var xn)))) xn))
        (length       (rem_FOv (FOvars_in (instant_cons_empty' atm (ST phi2 (Var xn)))) (Var xn)))))) lx)
    (preds_in (ST (mimpl phi1 phi2) (Var xn))) (list_Var (length (preds_in (ST (mimpl phi1 phi2) (Var xn)))) y)
    (vsS_syn_l (FOv_att_P_l atm (preds_in (ST (mimpl phi1 phi2) (Var xn)))) y))) = true.
Proof.
  intros.
  pose proof (hopeful2_atm lx atm y xn (ST phi2 (Var xn))) as HH.
  apply hopeful6 with (lP1 := preds_in(list_closed_allFO (implSO atm (ST phi2 (Var xn))) lx)).
  rewrite preds_in_list_closed_allFO.
  simpl.
  apply is_in_pred_l_2app.
  assumption.
  apply is_in_pred_l_refl.

  assumption.
Qed.

