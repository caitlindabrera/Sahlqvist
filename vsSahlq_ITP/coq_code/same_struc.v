Require Export low_mods.
Require Import Rep_Pred_FOv Rel At.

Fixpoint same_struc (alpha beta : SecOrder) : bool :=
  match alpha, beta with
  | predSO P _, predSO Q _ => if predicate_dec P Q then true else false 
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
    if predicate_dec P Q then same_struc alpha' beta' else false
  | exSO P alpha', exSO Q beta' => 
    if predicate_dec P Q then same_struc alpha' beta' else false
  | _ , _=> false
  end.

Lemma same_struc_refl : forall alpha,
  same_struc alpha alpha = true.
Proof.
  induction alpha;
    try reflexivity;
    try (simpl; assumption);
    try (simpl; rewrite IHalpha1;
    rewrite IHalpha2; reflexivity);
    try (simpl; rewrite predicate_dec_l; auto).
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

    destruct (predicate_dec p p0); subst;
    destruct (predicate_dec p0 p1); subst; auto.
    discriminate. discriminate.

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

    destruct (predicate_dec p p0); subst;
    destruct (predicate_dec p0 p1); subst; auto; try discriminate.
    apply IHalpha with (beta := beta); auto. 
    
    destruct (predicate_dec p p0); subst;
    destruct (predicate_dec p0 p1); subst; auto; try discriminate.
    apply IHalpha with (beta := beta); auto. 
Qed.

Lemma same_struc_replace_FOv : forall alpha x y,
  same_struc alpha (replace_FOv alpha x y) = true.
Proof.
  induction alpha; intros x y; simpl in *; auto;
    try (  destruct (FOvariable_dec x f); 
    destruct (FOvariable_dec x f0); auto);
    try (  destruct (FOvariable_dec x f); auto);
    try (rewrite predicate_dec_l; auto);
    try (rewrite IHalpha1; apply IHalpha2).
Qed.

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

Lemma same_struc_conjSO_ex : forall gamma alpha beta,
  same_struc gamma (conjSO alpha beta) = true ->
  existsT2 alpha' beta',
    gamma = conjSO alpha' beta'.
Proof.
  induction gamma; intros alpha beta H;
    try (simpl in *; discriminate).
    exists gamma1. exists gamma2. reflexivity.
Defined.

Lemma same_struc_comm : forall alpha beta,
  same_struc alpha beta = true ->
  same_struc beta alpha = true.
Proof.
  induction alpha; intros beta Hss; destruct beta;
    simpl in *; try discriminate; try reflexivity;
      try (    apply IHalpha; assumption);
      try (dest_pred_dec p p0; auto).

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