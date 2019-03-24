Require Export low_mods.
Require Import Rep_Pred_FOv Rel At instant_cons_empty.

Inductive att_allFO_var : SecOrder -> FOvariable -> Prop :=
| att_allFO_var_allFO_head beta y x : x = y -> att_allFO_var (allFO y beta) x
| att_allFO_var_allFO beta y x : att_allFO_var beta x -> att_allFO_var (allFO y beta) x
| att_allFO_var_exFO beta y x : att_allFO_var beta x -> att_allFO_var (exFO y beta) x
| att_allFO_var_negSO beta x : att_allFO_var beta x -> att_allFO_var (negSO beta) x
| att_allFO_var_conjSO_l b1 b2 x : att_allFO_var b1 x -> att_allFO_var (conjSO b1 b2) x
| att_allFO_var_conjSO_r b1 b2 x : att_allFO_var b2 x -> att_allFO_var (conjSO b1 b2) x
| att_allFO_var_disjSO_l b1 b2 x : att_allFO_var b1 x -> att_allFO_var (disjSO b1 b2) x
| att_allFO_var_disjSO_r b1 b2 x : att_allFO_var b2 x -> att_allFO_var (disjSO b1 b2) x
| att_allFO_var_implSO_l b1 b2 x : att_allFO_var b1 x -> att_allFO_var (implSO b1 b2) x
| att_allFO_var_implSO_r b1 b2 x : att_allFO_var b2 x -> att_allFO_var (implSO b1 b2) x
| att_allFO_var_allSO beta P x : att_allFO_var beta x -> att_allFO_var (allSO P beta) x
| att_allFO_var_exSO beta P x : att_allFO_var beta x -> att_allFO_var (exSO P beta) x.

Lemma att_allFO_var_dec : forall alpha x,
{att_allFO_var alpha x} + {~ att_allFO_var alpha x}.
Proof.
  induction alpha; intros x;
    try solve[(right; intros H; inversion H)].
  + destruct (FOvariable_dec f x). subst. left.
    constructor. auto.
    destruct (IHalpha x). left. constructor 2. auto.
    right. intros H. inversion H; subst; contradiction.
  + destruct (IHalpha x). left. constructor 3. auto.
    right. intros H. inversion H. subst. contradiction.
  + destruct (IHalpha x); 
      [left; constructor | right; intros H; inversion H; subst]; auto.
  + destruct (IHalpha1 x). left. constructor. auto.
    destruct (IHalpha2 x). left. constructor 6. auto. 
    right. intros H. inversion H; subst; contradiction. 
  + destruct (IHalpha1 x). left. constructor. auto.
    destruct (IHalpha2 x). left. constructor 8. auto. 
    right. intros H. inversion H; subst; contradiction. 
  + destruct (IHalpha1 x). left. constructor. auto.
    destruct (IHalpha2 x). left. constructor 10. auto. 
    right. intros H. inversion H; subst; contradiction. 
  + destruct (IHalpha x); [left | right].
    constructor. auto. intros H. inversion H; subst.
    contradiction.
  + destruct (IHalpha x); [left | right].
    constructor. auto. intros H. inversion H; subst.
    contradiction.
Qed.

Inductive ex_att_allFO_lvar : SecOrder -> list FOvariable -> Prop :=
| ex_att_allFO_lvar_head alpha y lv' :
    att_allFO_var alpha y -> ex_att_allFO_lvar alpha (y :: lv')
| ex_att_allFO_lvar_tail alpha y lv' : 
    ex_att_allFO_lvar alpha lv' -> ex_att_allFO_lvar alpha (y :: lv').

Inductive att_exFO_var : SecOrder -> FOvariable -> Prop :=
| att_exFO_var_exFO_head beta y x : x = y -> att_exFO_var (exFO y beta) x
| att_exFO_var_exFO beta y x : att_exFO_var beta x -> att_exFO_var (exFO y beta) x
| att_exFO_var_allFO beta y x : att_exFO_var beta x -> att_exFO_var (allFO y beta) x
| att_exFO_var_negSO beta x : att_exFO_var beta x -> att_exFO_var (negSO beta) x
| att_exFO_var_conjSO_l b1 b2 x : att_exFO_var b1 x -> att_exFO_var (conjSO b1 b2) x
| att_exFO_var_conjSO_r b1 b2 x : att_exFO_var b2 x -> att_exFO_var (conjSO b1 b2) x
| att_exFO_var_disjSO_l b1 b2 x : att_exFO_var b1 x -> att_exFO_var (disjSO b1 b2) x
| att_exFO_var_disjSO_r b1 b2 x : att_exFO_var b2 x -> att_exFO_var (disjSO b1 b2) x
| att_exFO_var_implSO_l b1 b2 x : att_exFO_var b1 x -> att_exFO_var (implSO b1 b2) x
| att_exFO_var_implSO_r b1 b2 x : att_exFO_var b2 x -> att_exFO_var (implSO b1 b2) x
| att_exFO_var_allSO beta P x : att_exFO_var beta x -> att_exFO_var (allSO P beta) x
| att_exFO_var_exSO beta P x : att_exFO_var beta x -> att_exFO_var (exSO P beta) x.

Inductive ex_att_exFO_lvar : SecOrder -> list FOvariable -> Prop :=
| ex_att_exFO_lvar_head alpha y lv' :
    att_exFO_var alpha y -> ex_att_exFO_lvar alpha (y :: lv')
| ex_att_exFO_lvar_tail alpha y lv' : 
    ex_att_exFO_lvar alpha lv' -> ex_att_exFO_lvar alpha (y :: lv').

Lemma ex_att_allFO_lvar_nil : forall alpha, ~ ex_att_allFO_lvar alpha nil.
Proof. destruct alpha; intros H; inversion H.  Qed. 

Lemma ex_att_allFO_lvar_cons: forall alpha x lv,
 ex_att_allFO_lvar alpha (x :: lv) ->
 ex_att_allFO_lvar alpha lv \/ att_allFO_var alpha x.
Proof. intros alpha x lv H1. inversion H1; subst; firstorder. Qed.

Lemma ex_att_allFO_lvar_allFO_In : forall lv alpha x,
In x lv ->
ex_att_allFO_lvar (allFO x alpha) lv.    
Proof.
  induction lv; intros alpha x H. inversion H.
  simpl in H. destruct H as [H1 | H1]. subst.
  apply ex_att_allFO_lvar_head. apply att_allFO_var_allFO_head. auto.
  apply ex_att_allFO_lvar_tail. apply IHlv. auto.
Qed.

Lemma ex_att_allFO_lvar_allFO : forall lv alpha x,
ex_att_allFO_lvar alpha lv ->
ex_att_allFO_lvar (allFO x alpha) lv.    
Proof.
  induction lv; intros alpha x H. inversion H.
  inversion H; subst. 
  apply ex_att_allFO_lvar_head. apply att_allFO_var_allFO. auto.
  apply ex_att_allFO_lvar_tail. apply IHlv. auto.
Qed.

Lemma ex_att_allFO_lvar_allFO_neg : forall lv alpha x,
  ~ ex_att_allFO_lvar (allFO x alpha) lv ->
    ~ ex_att_allFO_lvar alpha lv /\
    ~ In x lv.
Proof.
  intros lv alpha x H. apply conj; intros H2; apply H. 
  apply ex_att_allFO_lvar_allFO. auto.
  apply ex_att_allFO_lvar_allFO_In. auto.
Qed.

Lemma ex_att_exFO_lvar_allFO : forall lv alpha x,
    ex_att_exFO_lvar alpha lv ->
    ex_att_exFO_lvar (allFO x alpha) lv.
Proof.
  induction lv; intros alpha x H.  inversion H.
  inversion H; subst. constructor.
  constructor. auto.
  constructor 2. apply IHlv. auto.
Qed.

Lemma ex_att_exFO_lvar_exFO_In : forall lv alpha x,
In x lv ->
ex_att_exFO_lvar (exFO x alpha) lv.    
Proof.
  induction lv; intros alpha x H. inversion H.
  simpl in H. destruct H as [H1 | H1]. subst.
  apply ex_att_exFO_lvar_head. apply att_exFO_var_exFO_head. auto.
  apply ex_att_exFO_lvar_tail. apply IHlv. auto.
Qed.

Lemma ex_att_exFO_lvar_exFO : forall lv alpha x,
ex_att_exFO_lvar alpha lv ->
ex_att_exFO_lvar (exFO x alpha) lv.    
Proof.
  induction lv; intros alpha x H. inversion H.
  inversion H; subst. 
  apply ex_att_exFO_lvar_head. apply att_exFO_var_exFO. auto.
  apply ex_att_exFO_lvar_tail. apply IHlv. auto.
Qed.
  
Lemma ex_att_exFO_lvar_allFO_neg : forall lv alpha x,
  ~ ex_att_exFO_lvar (allFO x alpha) lv  ->
  ~ ex_att_exFO_lvar alpha lv.
Proof.
  intros lv alpha x H H2; apply H.
  apply ex_att_exFO_lvar_allFO. auto.
Qed. 

Lemma ex_att_exFO_lvar_exFO_neg : forall lv alpha x,
  ~ ex_att_exFO_lvar (exFO x alpha) lv ->
  ~   ex_att_exFO_lvar alpha lv /\
    ~ In x lv .
Proof.
  intros lv alpha x H; apply conj; intros H2; apply H.
  apply ex_att_exFO_lvar_exFO. auto.
  apply ex_att_exFO_lvar_exFO_In. auto.
Qed.

Lemma ex_att_allFO_lvar_exFO : forall lv alpha x,
  ex_att_allFO_lvar alpha lv ->
  ex_att_allFO_lvar (exFO x alpha) lv.
Proof.
  induction lv; intros alpha x H. inversion H.
  inversion H; subst. constructor.
  constructor. auto.
  constructor 2. apply IHlv. auto.
Qed.

Lemma ex_att_allFO_lvar_exFO_neg : forall lv alpha x,
  ~ ex_att_allFO_lvar (exFO x alpha) lv ->
   ~ ex_att_allFO_lvar alpha lv.
Proof.
  intros lv alpha x H1 H2. apply H1.
  apply ex_att_allFO_lvar_exFO. auto.
Qed.

Lemma ex_att_allFO_lvar_negSO : forall lv alpha,
  ex_att_allFO_lvar (negSO alpha) lv <-> ex_att_allFO_lvar alpha lv.
Proof.
  induction lv; intros alpha. split; intros H; contradiction (ex_att_allFO_lvar_nil _ H). 
  split; intros H. 
  apply ex_att_allFO_lvar_cons in H. destruct H.
  apply ex_att_allFO_lvar_tail; apply IHlv; auto. 
  apply ex_att_allFO_lvar_head. inversion H. subst. auto.
  
  apply ex_att_allFO_lvar_cons in H. destruct H.
  apply ex_att_allFO_lvar_tail; apply IHlv; auto. 
  apply ex_att_allFO_lvar_head.  apply att_allFO_var_negSO. auto.
Qed.

Lemma ex_att_exFO_lvar_negSO : forall lv alpha,
  ex_att_exFO_lvar (negSO alpha) lv <->  ex_att_exFO_lvar alpha lv.
Proof.
  induction lv; intros alpha;
    split; intros H; inversion H; subst.
  inversion H2; subst. constructor. auto.
  constructor 2. apply IHlv. auto.
  constructor. constructor. auto.
  constructor 2. apply IHlv. auto.
Qed.

Lemma ex_att_allFO_lvar_conjSO_l : forall lv alpha1 alpha2,
  ex_att_allFO_lvar alpha1 lv ->
  ex_att_allFO_lvar (conjSO alpha1 alpha2) lv .
Proof.
  induction lv; intros alpha1 alpha2 H. inversion H.
  inversion H; subst.
  + constructor. apply att_allFO_var_conjSO_l. auto.
  + constructor 2. apply IHlv. auto.
Qed.

Lemma ex_att_allFO_lvar_conjSO_r : forall lv alpha1 alpha2,
  ex_att_allFO_lvar alpha2 lv ->
  ex_att_allFO_lvar (conjSO alpha1 alpha2) lv .
Proof.
  induction lv; intros alpha1 alpha2 H. inversion H.
  inversion H; subst.
  + constructor. apply att_allFO_var_conjSO_r. auto.
  + constructor 2. apply IHlv. auto.
Qed.

Lemma ex_att_allFO_lvar_conjSO_f : forall lv alpha1 alpha2,
  ~ ex_att_allFO_lvar (conjSO alpha1 alpha2) lv ->
 (~ ex_att_allFO_lvar alpha1 lv) /\
 (~ ex_att_allFO_lvar alpha2 lv).
Proof.
  intros lv alpha1 alpha2 H.
  apply conj; intros H1.
  eapply ex_att_allFO_lvar_conjSO_l in H1. contradiction (H H1).
  eapply ex_att_allFO_lvar_conjSO_r in H1. contradiction (H H1).
Qed.

Lemma ex_att_exFO_lvar_conjSO_l : forall lv alpha1 alpha2,
  ex_att_exFO_lvar alpha1 lv ->
  ex_att_exFO_lvar (conjSO alpha1 alpha2) lv .
Proof.
  induction lv; intros alpha1 alpha2 H. inversion H.
  inversion H; subst.
  + constructor. apply att_exFO_var_conjSO_l. auto.
  + constructor 2. apply IHlv. auto.
Qed.

Lemma ex_att_exFO_lvar_conjSO_r : forall lv alpha1 alpha2,
  ex_att_exFO_lvar alpha2 lv ->
  ex_att_exFO_lvar (conjSO alpha1 alpha2) lv .
Proof.
  induction lv; intros alpha1 alpha2 H. inversion H.
  inversion H; subst.
  + constructor. apply att_exFO_var_conjSO_r. auto.
  + constructor 2. apply IHlv. auto.
Qed.

Lemma ex_att_exFO_lvar_conjSO_f : forall lv alpha1 alpha2,
  ~ ex_att_exFO_lvar (conjSO alpha1 alpha2) lv ->
 (~ ex_att_exFO_lvar alpha1 lv /\ ~ ex_att_exFO_lvar alpha2 lv).
Proof.
  intros lv alpha1 alpha2 H.
  apply conj; intros H1.
  eapply ex_att_exFO_lvar_conjSO_l in H1. contradiction (H H1).
  eapply ex_att_exFO_lvar_conjSO_r in H1. contradiction (H H1).
Qed.  

Lemma ex_att_allFO_lvar_disjSO_l : forall lv alpha1 alpha2,
  ex_att_allFO_lvar alpha1 lv ->
  ex_att_allFO_lvar (disjSO alpha1 alpha2) lv .
Proof.
  induction lv; intros alpha1 alpha2 H. inversion H.
  inversion H; subst.
  + constructor. apply att_allFO_var_disjSO_l. auto.
  + constructor 2. apply IHlv. auto.
Qed.

Lemma ex_att_allFO_lvar_disjSO_r : forall lv alpha1 alpha2,
  ex_att_allFO_lvar alpha2 lv ->
  ex_att_allFO_lvar (disjSO alpha1 alpha2) lv .
Proof.
  induction lv; intros alpha1 alpha2 H. inversion H.
  inversion H; subst.
  + constructor. apply att_allFO_var_disjSO_r. auto.
  + constructor 2. apply IHlv. auto.
Qed.

Lemma ex_att_allFO_lvar_disjSO_f : forall lv alpha1 alpha2,
  ~ ex_att_allFO_lvar (disjSO alpha1 alpha2) lv ->
 (~ ex_att_allFO_lvar alpha1 lv) /\
 (~ ex_att_allFO_lvar alpha2 lv).
Proof.
  intros lv alpha1 alpha2 H.
  apply conj; intros H1.
  eapply ex_att_allFO_lvar_disjSO_l in H1. contradiction (H H1).
  eapply ex_att_allFO_lvar_disjSO_r in H1. contradiction (H H1).
Qed.

Lemma ex_att_exFO_lvar_disjSO_l : forall lv alpha1 alpha2,
  ex_att_exFO_lvar alpha1 lv ->
  ex_att_exFO_lvar (disjSO alpha1 alpha2) lv .
Proof.
  induction lv; intros alpha1 alpha2 H. inversion H.
  inversion H; subst.
  + constructor. apply att_exFO_var_disjSO_l. auto.
  + constructor 2. apply IHlv. auto.
Qed.

Lemma ex_att_exFO_lvar_disjSO_r : forall lv alpha1 alpha2,
  ex_att_exFO_lvar alpha2 lv ->
  ex_att_exFO_lvar (disjSO alpha1 alpha2) lv .
Proof.
  induction lv; intros alpha1 alpha2 H. inversion H.
  inversion H; subst.
  + constructor. apply att_exFO_var_disjSO_r. auto.
  + constructor 2. apply IHlv. auto.
Qed.

Lemma ex_att_exFO_lvar_disjSO_f : forall lv alpha1 alpha2,
  ~ ex_att_exFO_lvar (disjSO alpha1 alpha2) lv ->
 (~ ex_att_exFO_lvar alpha1 lv /\ ~ ex_att_exFO_lvar alpha2 lv).
Proof.
  intros lv alpha1 alpha2 H.
  apply conj; intros H1.
  eapply ex_att_exFO_lvar_disjSO_l in H1. contradiction (H H1).
  eapply ex_att_exFO_lvar_disjSO_r in H1. contradiction (H H1).
Qed.

Lemma ex_att_allFO_lvar_implSO_l : forall lv alpha1 alpha2,
  ex_att_allFO_lvar alpha1 lv ->
  ex_att_allFO_lvar (implSO alpha1 alpha2) lv .
Proof.
  induction lv; intros alpha1 alpha2 H. inversion H.
  inversion H; subst.
  + constructor. apply att_allFO_var_implSO_l. auto.
  + constructor 2. apply IHlv. auto.
Qed.

Lemma ex_att_allFO_lvar_implSO_r : forall lv alpha1 alpha2,
  ex_att_allFO_lvar alpha2 lv ->
  ex_att_allFO_lvar (implSO alpha1 alpha2) lv .
Proof.
  induction lv; intros alpha1 alpha2 H. inversion H.
  inversion H; subst.
  + constructor. apply att_allFO_var_implSO_r. auto.
  + constructor 2. apply IHlv. auto.
Qed.

Lemma ex_att_allFO_lvar_implSO_f : forall lv alpha1 alpha2,
  ~ ex_att_allFO_lvar (implSO alpha1 alpha2) lv ->
 (~ ex_att_allFO_lvar alpha1 lv) /\
 (~ ex_att_allFO_lvar alpha2 lv).
Proof.
  intros lv alpha1 alpha2 H.
  apply conj; intros H1.
  eapply ex_att_allFO_lvar_implSO_l in H1. contradiction (H H1).
  eapply ex_att_allFO_lvar_implSO_r in H1. contradiction (H H1).
Qed.

Lemma ex_att_exFO_lvar_implSO_l : forall lv alpha1 alpha2,
  ex_att_exFO_lvar alpha1 lv ->
  ex_att_exFO_lvar (implSO alpha1 alpha2) lv .
Proof.
  induction lv; intros alpha1 alpha2 H. inversion H.
  inversion H; subst.
  + constructor. apply att_exFO_var_implSO_l. auto.
  + constructor 2. apply IHlv. auto.
Qed.

Lemma ex_att_exFO_lvar_implSO_r : forall lv alpha1 alpha2,
  ex_att_exFO_lvar alpha2 lv ->
  ex_att_exFO_lvar (implSO alpha1 alpha2) lv .
Proof.
  induction lv; intros alpha1 alpha2 H. inversion H.
  inversion H; subst.
  + constructor. apply att_exFO_var_implSO_r. auto.
  + constructor 2. apply IHlv. auto.
Qed.

Lemma ex_att_exFO_lvar_implSO_f : forall lv alpha1 alpha2,
 ~ ex_att_exFO_lvar (implSO alpha1 alpha2) lv ->
 ( ~ ex_att_exFO_lvar alpha1 lv /\ ~ ex_att_exFO_lvar alpha2 lv).
Proof.
  intros lv alpha1 alpha2 H.
  apply conj; intros H1.
  eapply ex_att_exFO_lvar_implSO_l in H1. contradiction (H H1).
  eapply ex_att_exFO_lvar_implSO_r in H1. contradiction (H H1).
Qed.

Lemma ex_att_allFO_lvar_allSO : forall lv alpha P,
  ex_att_allFO_lvar (allSO P alpha) lv <->
  ex_att_allFO_lvar alpha lv.
Proof.
  induction lv; intros alpha P.
    split; intros H; contradiction (ex_att_allFO_lvar_nil _ H).
    
  split; intros H; apply ex_att_allFO_lvar_cons in H; destruct H as [H| H].
    constructor 2. apply IHlv in H. auto.
    constructor 1. inversion H. auto.
    
    constructor 2. apply IHlv. auto.
    constructor 1. constructor. auto.
Qed.

Lemma ex_att_exFO_lvar_allSO : forall lv alpha P,
  ex_att_exFO_lvar (allSO P alpha) lv <->
  ex_att_exFO_lvar alpha lv.
Proof.
  induction lv; intros alpha P;
    split; intros H2; inversion H2; subst.
  constructor. inversion H1; auto.
  constructor 2. apply IHlv in H1. auto.
  constructor. constructor. auto.
  constructor 2. apply IHlv. auto.
Qed.

Lemma ex_att_allFO_lvar_exSO : forall lv alpha P,
  ex_att_allFO_lvar (exSO P alpha) lv <->
  ex_att_allFO_lvar alpha lv.
Proof.
  induction lv; intros alpha P.
    split; intros H; contradiction (ex_att_allFO_lvar_nil _ H).
    
  split; intros H; apply ex_att_allFO_lvar_cons in H; destruct H as [H| H].
    constructor 2. apply IHlv in H. auto.
    constructor 1. inversion H. auto.
    
    constructor 2. apply IHlv. auto.
    constructor 1. constructor. auto.
Qed.

Lemma ex_att_exFO_lvar_exSO : forall lv alpha P,
  ex_att_exFO_lvar (exSO P alpha) lv <->
  ex_att_exFO_lvar alpha lv.
Proof.
  induction lv; intros alpha P;
    split; intros H2; inversion H2; subst.
  constructor. inversion H1; auto.
  constructor 2. apply IHlv in H1. auto.
  constructor. constructor. auto.
  constructor 2. apply IHlv. auto.
Qed.

Inductive ex_att_allFO_llvar : SecOrder -> list (list FOvariable) -> Prop :=
| ex_att_allFO_llvar_head alpha lv llv :
    ex_att_allFO_lvar alpha lv -> ex_att_allFO_llvar alpha (lv :: llv)
| ex_att_allFO_llvar_tail alpha lv llv :
    ex_att_allFO_llvar alpha llv -> ex_att_allFO_llvar alpha (lv :: llv).

Inductive ex_att_exFO_llvar : SecOrder -> list (list FOvariable) -> Prop :=
| ex_att_exFO_llvar_head alpha lv llv :
    ex_att_exFO_lvar alpha lv -> ex_att_exFO_llvar alpha (lv :: llv)
| ex_att_exFO_llvar_tail alpha lv llv :
    ex_att_exFO_llvar alpha llv -> ex_att_exFO_llvar alpha (lv :: llv).

Lemma att_allFO_var_allFO_not : forall alpha x y,
~ att_allFO_var (allFO x alpha) y -> x <> y /\ ~ att_allFO_var alpha y.
Proof.
  intros alpha x y H1. apply conj; intros H2. 
  subst. pose proof (att_allFO_var_allFO_head alpha y y eq_refl).
  contradiction.
  eapply att_allFO_var_allFO in H2. contradiction (H1 H2).
Qed.

Lemma att_allFO_var_exFO_not : forall alpha x y,
~ att_allFO_var (exFO x alpha) y -> ~ att_allFO_var alpha y.
Proof.
  intros alpha x y H1 H2. pose proof (att_allFO_var_exFO alpha x y H2).
  contradiction.
Qed.

Lemma attached_allFO_x_rep_FOv : forall alpha x y z,
  ~ att_allFO_var alpha x ->
  ~ att_allFO_var alpha z ->
  ~ att_allFO_var (replace_FOv alpha x y) z.
Proof.
  induction alpha; intros x1 x2 ym H1 H2 H3.
    
    simpl in *. destruct (FOvariable_dec x1 f).
    subst. inversion H3. firstorder.

    simpl in *. destruct (FOvariable_dec x1 f).
    subst. destruct (FOvariable_dec f f0);
             inversion H3; firstorder.
    subst. destruct (FOvariable_dec x1 f0);
             inversion H3; firstorder.    

    simpl in *. destruct (FOvariable_dec x1 f).
    subst. destruct (FOvariable_dec f f0);
             inversion H3; firstorder.
    subst. destruct (FOvariable_dec x1 f0);
             inversion H3; firstorder.    

    apply att_allFO_var_allFO_not in H1. destruct H1 as [H1a H1b].
    apply att_allFO_var_allFO_not in H2. destruct H2 as [H2a H2b].
    simpl in *. rewrite FOvariable_dec_r in H3; auto.
    inversion H3. subst. contradiction.
    subst.  apply IHalpha in H2; auto.

    apply att_allFO_var_exFO_not in H1. 
    apply att_allFO_var_exFO_not in H2. 
    simpl in *. destruct (FOvariable_dec x1 f);
    inversion H3; subst; apply IHalpha in H5; auto.

    simpl in H3. inversion H3. subst.
    apply IHalpha in H0; auto. intros HH.
    pose proof (att_allFO_var_negSO alpha x1 HH). contradiction.
    intros HH.
    pose proof (att_allFO_var_negSO alpha _ HH). contradiction.

    simpl in H3. inversion H3; subst. 
    apply IHalpha1 in H5; auto; intros H6. 
    pose proof (att_allFO_var_conjSO_l alpha1 alpha2 x1 H6 ).
      contradiction.
    pose proof (att_allFO_var_conjSO_l alpha1 alpha2 ym H6).
      contradiction.    
    apply IHalpha2 in H5; auto; intros H6. 
    pose proof (att_allFO_var_conjSO_r alpha1 alpha2 x1 H6 ).
      contradiction.
    pose proof (att_allFO_var_conjSO_r alpha1 alpha2 ym H6).
      contradiction.    

    simpl in H3. inversion H3; subst. 
    apply IHalpha1 in H5; auto; intros H6. 
    pose proof (att_allFO_var_disjSO_l alpha1 alpha2 x1 H6 ).
      contradiction.
    pose proof (att_allFO_var_disjSO_l alpha1 alpha2 ym H6).
      contradiction.    
    apply IHalpha2 in H5; auto; intros H6. 
    pose proof (att_allFO_var_disjSO_r alpha1 alpha2 x1 H6 ).
      contradiction.
    pose proof (att_allFO_var_disjSO_r alpha1 alpha2 ym H6).
      contradiction.    

    simpl in H3. inversion H3; subst. 
    apply IHalpha1 in H5; auto; intros H6. 
    pose proof (att_allFO_var_implSO_l alpha1 alpha2 x1 H6 ).
      contradiction.
    pose proof (att_allFO_var_implSO_l alpha1 alpha2 ym H6).
      contradiction.    
    apply IHalpha2 in H5; auto; intros H6. 
    pose proof (att_allFO_var_implSO_r alpha1 alpha2 x1 H6 ).
      contradiction.
    pose proof (att_allFO_var_implSO_r alpha1 alpha2 ym H6).
      contradiction.    

    simpl in *. inversion H3. subst. apply IHalpha in H5. auto. 
    intros H6. eapply att_allFO_var_allSO in H6.
    contradiction (H1 H6).
    intros H6. eapply att_allFO_var_allSO in H6.
    contradiction (H2 H6).

    simpl in *. inversion H3. subst. apply IHalpha in H5. auto. 
    intros H6. eapply att_allFO_var_exSO in H6.
    contradiction (H1 H6).
    intros H6. eapply att_allFO_var_exSO in H6.
    contradiction (H2 H6).
Qed.

Lemma att_exFO_var_rep_FOv : forall alpha x y z,
  ~ att_exFO_var alpha x ->
  ~ att_exFO_var alpha z ->
  ~ att_exFO_var (replace_FOv alpha x y) z.
Proof.
  induction alpha; intros x1 x2 ym H1 H2 H; simpl in *;
  try solve [if_then_else_dest_blind; firstorder; inversion H].

  if_then_else_dest_blind; subst;
  inversion H; subst;
  (apply IHalpha in H5; auto;
    intros H6; [apply H1 | apply H2]; constructor; auto).

  destruct (FOvariable_dec x1 f); subst;
  inversion H; subst. apply H1. constructor. auto.
  apply IHalpha in H5; auto;
    intros H6; [apply H1 | apply H2]; constructor 2; auto.
  apply H2. constructor. auto.
  apply IHalpha in H5; auto;
    intros H6; [apply H1 | apply H2]; constructor 2; auto.

  inversion H; subst. apply IHalpha in H3; auto.
  intros HH. apply H1. constructor. auto.
  intros HH. apply H2. constructor. auto.

  inversion H; subst.
  apply IHalpha1 in H5; auto.
    intros HH. apply H1. constructor. auto.
    intros HH. apply H2. constructor. auto.
  apply IHalpha2 in H5; auto.
    intros HH. apply H1. constructor 6. auto.
    intros HH. apply H2. constructor 6. auto.

  inversion H; subst.
  apply IHalpha1 in H5; auto.
    intros HH. apply H1. constructor. auto.
    intros HH. apply H2. constructor. auto.
  apply IHalpha2 in H5; auto.
    intros HH. apply H1. constructor 8. auto.
    intros HH. apply H2. constructor 8. auto.

  inversion H; subst.
  apply IHalpha1 in H5; auto.
    intros HH. apply H1. constructor. auto.
    intros HH. apply H2. constructor. auto.
  apply IHalpha2 in H5; auto.
    intros HH. apply H1. constructor 10. auto.
    intros HH. apply H2. constructor 10. auto.

  inversion H; subst. apply IHalpha in H5; auto.
  intros Hh. apply H1. constructor. auto.
  intros Hh. apply H2. constructor. auto.

  inversion H; subst. apply IHalpha in H5; auto.
  intros Hh. apply H1. constructor. auto.
  intros Hh. apply H2. constructor. auto.
Qed.

Lemma FOQFree_att_allFO : forall alpha x,
  FOQFree alpha = true ->
  ~ att_allFO_var alpha x.
Proof.
  induction alpha; intros x H H2; try solve [inversion H2 | discriminate].

  simpl in *. inversion H2; subst. apply IHalpha in H1; auto.

  simpl in *. apply andb_prop in H. destruct H. 
  inversion H2; subst. apply IHalpha1 in H5; auto.
   apply IHalpha2 in H5; auto.

  simpl in *. apply andb_prop in H. destruct H. 
  inversion H2; subst. apply IHalpha1 in H5; auto.
   apply IHalpha2 in H5; auto.

  simpl in *. apply andb_prop in H. destruct H. 
  inversion H2; subst. apply IHalpha1 in H5; auto.
   apply IHalpha2 in H5; auto.

  simpl in *. inversion H2. subst. apply IHalpha in H4; auto.

  simpl in *. inversion H2. subst. apply IHalpha in H4; auto.
Qed.

Lemma FOQFree_att_exFO : forall alpha x,
  FOQFree alpha = true ->
  ~ att_exFO_var alpha x.
Proof.
  induction alpha; intros x H H2; try reflexivity;
    try solve [inversion H2]; try discriminate;
      simpl in *; inversion H2; subst;
        try solve [  if_then_else_dest_blind; firstorder].
Qed.

Lemma att_allFO_var_rep_pred : forall alpha cond y Q x,
  FOQFree cond = true ->
  ~ att_allFO_var alpha y  ->
  ~ att_allFO_var (replace_pred alpha Q x cond) y.
Proof.
  induction alpha; intros cond ym Q xn H1 H2 H3; try (simpl in *; contradiction).
    simpl in *. destruct (predicate_dec Q p).
    subst. apply attached_allFO_x_rep_FOv in H3; auto;
    intros H4; apply FOQFree_att_allFO in H4; auto.
    contradiction.

    simpl in *. inversion H3; subst. 
    apply att_allFO_var_allFO_not in H2. firstorder.
    apply IHalpha in H5; auto.
    apply att_allFO_var_allFO_not in H2. apply H2.

    simpl in *. inversion H3; subst. apply IHalpha in H5; auto.
    intros H6. contradiction (H2 (att_allFO_var_exFO  _ _ _ H6)).

    simpl in *. inversion H3; subst. apply IHalpha in H0; auto.
    intros H6. contradiction (H2 (att_allFO_var_negSO _ _ H6)).

    simpl in H3. inversion H3; subst. apply IHalpha1 in H5; auto.
    intros H6. contradiction (H2 (att_allFO_var_conjSO_l _ _ _ H6)).
    apply IHalpha2 in H5; auto.
    intros H6. contradiction (H2 (att_allFO_var_conjSO_r _ _ _ H6)).    

    simpl in H3. inversion H3; subst. apply IHalpha1 in H5; auto.
    intros H6. contradiction (H2 (att_allFO_var_disjSO_l _ _ _ H6)).
    apply IHalpha2 in H5; auto.
    intros H6. contradiction (H2 (att_allFO_var_disjSO_r _ _ _ H6)).    

    simpl in H3. inversion H3; subst. apply IHalpha1 in H5; auto.
    intros H6. contradiction (H2 (att_allFO_var_implSO_l _ _ _ H6)).
    apply IHalpha2 in H5; auto.
    intros H6. contradiction (H2 (att_allFO_var_implSO_r _ _ _ H6)).    

    simpl in *. destruct (predicate_dec Q p). apply IHalpha in H3;
    auto.  intros H6. contradiction (H2 (att_allFO_var_allSO _ _ _ H6)).
    inversion H3. subst.  apply IHalpha in H5;
    auto.  intros H6. contradiction (H2 (att_allFO_var_allSO _ _ _ H6)).

    simpl in *. destruct (predicate_dec Q p). apply IHalpha in H3;
    auto.  intros H6. contradiction (H2 (att_allFO_var_exSO _ _ _ H6)).
    inversion H3. subst.  apply IHalpha in H5;
    auto.  intros H6. contradiction (H2 (att_allFO_var_exSO _ _ _ H6)).
Qed.

Lemma att_exFO_var_rep_pred : forall alpha cond y Q x,
  FOQFree cond = true ->
  att_exFO_var (replace_pred alpha Q x cond) y ->
  att_exFO_var alpha y.
Proof.
  induction alpha; intros cond ym Q xn H1 H2; auto;
    try (simpl in *; apply IHalpha; auto); simpl in *.

    destruct (predicate_dec Q p). subst.
    apply att_exFO_var_rep_FOv in H2; auto; try contradiction;
    apply FOQFree_att_exFO; auto. auto.

    inversion H2; subst. constructor.
    apply IHalpha in H4; auto.

    inversion H2; subst. constructor. auto.
    constructor 2. apply IHalpha in H4; auto.

    inversion H2; subst; constructor; auto.
    apply IHalpha in H0; auto.

    inversion H2; subst;
      [constructor 5; apply IHalpha1 in H4 |
       constructor 6; apply IHalpha2 in H4]; auto.

    inversion H2; subst;
      [constructor 7; apply IHalpha1 in H4 |
       constructor 8; apply IHalpha2 in H4]; auto.

    inversion H2; subst;
      [constructor 9; apply IHalpha1 in H4 |
       constructor 10; apply IHalpha2 in H4]; auto.

    constructor. if_then_else_dest_blind;
                   [|inversion H2; subst].
    apply IHalpha in H2; auto.
    apply IHalpha in H4; auto.

    constructor. if_then_else_dest_blind;
                   [|inversion H2; subst].
    apply IHalpha in H2; auto.
    apply IHalpha in H4; auto.
Qed.

Lemma att_exFO_var_rep_pred_neg : forall alpha cond y Q x,
  FOQFree cond = true ->
  ~ att_exFO_var alpha y ->
  ~ att_exFO_var (replace_pred alpha Q x cond) y.
Proof.
  intros lpha cond y Q x H H1 H2.
  apply att_exFO_var_rep_pred in H2; auto.
Qed.

Lemma ex_att_allFO_lvar_rep_pred : forall lv alpha cond P x,
  FOQFree cond = true ->
 ~ ex_att_allFO_lvar alpha lv ->
 ~ ex_att_allFO_lvar (replace_pred alpha P x cond) lv.
Proof.
  induction lv; intros alpha cond P x H1 H2 H3. inversion H3.
  simpl in *. inversion H3; subst.
  apply att_allFO_var_rep_pred in H4; auto.
  intros H6. contradiction (H2 (ex_att_allFO_lvar_head _ _ _ H6)).
  apply IHlv in H4; auto. intros H6.
  contradiction (H2 (ex_att_allFO_lvar_tail _ _ _ H6)).
Qed.

Lemma ex_att_exFO_lvar_rep_pred : forall lv alpha cond P x,
  FOQFree cond = true ->
  ~ ex_att_exFO_lvar alpha lv ->
  ~ ex_att_exFO_lvar (replace_pred alpha P x cond) lv.
Proof.
  induction lv; intros alpha cond P x H1 H2 H3.
  inversion H3.
  inversion H3; subst. apply att_exFO_var_rep_pred in H4; auto.
  apply H2. constructor. auto.
  apply IHlv in H4; auto. intros H5. apply H2. constructor 2. auto.
Qed.

Lemma ex_attached_allFO_llv_rep_pred : forall llv alpha cond P x,
  FOQFree cond = true ->
  ~ ex_att_allFO_llvar alpha llv ->
  ~ ex_att_allFO_llvar (replace_pred alpha P x cond) llv.
Proof.
  induction llv; intros alpha cond P x Hat1 Hat2 Hat3. inversion Hat3.
  simpl in *. inversion Hat3; subst.
  apply ex_att_allFO_lvar_rep_pred in H1; auto. intros H6.
    contradiction (Hat2 (ex_att_allFO_llvar_head _ _ _ H6)).
  apply IHllv in H1; auto. intros H6.
    contradiction (Hat2 (ex_att_allFO_llvar_tail _ _ _ H6)).  
Qed. 

Lemma ex_att_exFO_llvar_rep_pred : forall llv alpha cond P x,
  FOQFree cond = true ->
  ~ ex_att_exFO_llvar alpha llv ->
  ~ ex_att_exFO_llvar (replace_pred alpha P x cond) llv.
Proof.
  induction llv; intros alpha cond P x Hat1 Hat2 H.
  inversion H.
  inversion H; subst. apply ex_att_exFO_lvar_rep_pred in H2; auto.
  intros HH. apply Hat2. constructor. auto.
  apply IHllv in H2; auto. intros HH.
  apply Hat2. constructor 2. auto.
Qed.

Lemma ex_att_allFO_lv_conjSO_f_rev : forall lv alpha1 alpha2,
 (~ ex_att_allFO_lvar alpha1 lv) ->
 (~ ex_att_allFO_lvar alpha2 lv) ->
  ~ ex_att_allFO_lvar (conjSO alpha1 alpha2) lv.
Proof.
  induction lv; intros alpha1 alpha2 Ha Hb Hc. inversion Hc.
  simpl in *. inversion Hc; subst.
  inversion H1; subst. 
  contradiction (Ha (ex_att_allFO_lvar_head _ _ _ H3)).
  contradiction (Hb (ex_att_allFO_lvar_head _ _ _ H3)).
  apply IHlv in H1; auto; intros H6.
  contradiction (Ha (ex_att_allFO_lvar_tail _ _ _ H6)).
  contradiction (Hb (ex_att_allFO_lvar_tail _ _ _ H6)).
Qed.  

Lemma  att_allFO_var_REL : forall rel x,
  REL rel = true ->
  ~ att_allFO_var rel x.
Proof.
  induction rel; intros [xn] H H2; try reflexivity;
    try (simpl in *; discriminate). inversion H2.

    simpl in *.
    case_eq (REL rel1); intros H1; rewrite H1 in H.
      2 : discriminate.
    inversion H2; subst. apply IHrel1 in H5; auto. 
    apply IHrel2 in H5; auto. 
Qed.

Lemma  att_allFO_var_AT : forall atm x,
  AT atm = true ->
  ~ att_allFO_var atm x.
Proof.
  induction atm; intros [xn] H H2; try  reflexivity;
    try (simpl in *; discriminate).

    inversion H2.
    simpl in *.
    case_eq (AT atm1); intros H1; rewrite H1 in H.
      2 : discriminate.
    inversion H2; subst. apply IHatm1 in H5; auto.
    apply IHatm2 in H5; auto.
Qed.

Lemma ex_att_allFO_lv_AT : forall lv atm,
  AT atm = true ->
  ~ ex_att_allFO_lvar atm lv.
Proof.
  induction lv; intros rel Hrel H. inversion H.
  simpl. inversion H; subst. apply att_allFO_var_AT in H2; auto.
  apply IHlv in H2; auto. 
Qed.

Lemma att_allFO_instant_cons_empty'_pre : forall beta P x y ,
  ~ att_allFO_var beta y ->
  ~ att_allFO_var (replace_pred beta P x (negSO (eqFO x x))) y.
Proof.
  induction beta; intros P y x Hat H;
    try (simpl in *; contradiction); simpl in *.
  +  FOv_dec_l_rep.
     destruct (predicate_dec P p). subst.
     inversion H. subst. inversion H1. contradiction.
  + inversion H. subst.
    contradiction (Hat (att_allFO_var_allFO_head _ _ _ eq_refl)).
    subst. apply IHbeta in H3. auto. intros H4. apply Hat.
    apply att_allFO_var_allFO. auto.
  + inversion H. subst.
    apply IHbeta in H3. auto. intros H4. apply Hat.
    constructor. auto.
  + inversion H. subst. apply IHbeta in H1. auto. intros H2.
    apply Hat. constructor. auto.
  + inversion H; subst.
    apply IHbeta1 in H3. auto.
    intros H4. apply Hat. constructor. auto.
    apply IHbeta2 in H3. auto.
    intros H4. apply Hat. constructor 6. auto.
  + inversion H; subst.
    apply IHbeta1 in H3. auto.
    intros H4. apply Hat. constructor. auto.
    apply IHbeta2 in H3. auto.
    intros H4. apply Hat. constructor 8. auto.
  + inversion H; subst.
    apply IHbeta1 in H3. auto.
    intros H4. apply Hat. constructor. auto.
    apply IHbeta2 in H3. auto.
    intros H4. apply Hat. constructor 10. auto.
  + destruct (predicate_dec P p). subst.
    apply Hat. apply IHbeta in H. contradiction.
    intros H2. apply Hat. constructor. auto.
    inversion H. subst. apply IHbeta in H3. auto.
    intros H2. apply Hat. constructor. auto.
  + destruct (predicate_dec P p). subst.
    apply Hat. apply IHbeta in H. contradiction.
    intros H2. apply Hat. constructor. auto.
    inversion H. subst. apply IHbeta in H3. auto.
    intros H2. apply Hat. constructor. auto.
Qed.

Lemma att_allFO_instant_cons_empty'_pre_l : forall l beta x,
  ~ att_allFO_var beta x ->
  ~ att_allFO_var (replace_pred_l beta l
     (nlist_list (length l) (nlist_var _ (Var 1)))
     (nlist_list (length l) (nlist_empty _))) x.
Proof.
  induction l; intros beta x H1.  auto. 
  simpl. apply att_allFO_instant_cons_empty'_pre.
  apply IHl. auto.
Qed.

Lemma att_allFO_instant_cons_empty' : forall beta alpha x,
  ~ att_allFO_var beta x ->
  ~ att_allFO_var (instant_cons_empty' alpha beta) x.
Proof.
  intros beta alpha x H.  unfold instant_cons_empty'.
  apply att_allFO_instant_cons_empty'_pre_l. auto.
Qed.

Lemma in_FOvar_att_allFO_x : forall alpha x,
  ~ In  x (FOvars_in alpha) -> ~ att_allFO_var alpha x.
Proof.
  induction alpha; intros x H H2; auto; 
    inversion H2; subst; try solve [firstorder]; simpl in *;
    try solve [apply IHalpha1 in H4; firstorder];
    try solve [apply IHalpha2 in H4; firstorder].
Qed.

Lemma rep_FOv_att_allFO: forall alpha x y z,
  ~ att_allFO_var alpha x ->
  ~z = x ->
  ~ att_allFO_var (replace_FOv alpha y z) x.
Proof.
  induction alpha; intros x y z Hat Hneq; simpl in *.
  + intros H. destruct (FOvariable_dec y f);
                            inversion H. 
  + dest_FOv_dec_blind; intros H; inversion H.
  + dest_FOv_dec_blind; intros H; inversion H.
  + intros H. destruct (FOvariable_dec y f);
    inversion H; subst. contradiction.
    apply IHalpha in H3. auto. intros H4.
    apply Hat. constructor 2. auto. auto.
    contradiction (Hat (att_allFO_var_allFO_head _ _ _ eq_refl)).
    apply IHalpha in H3. auto. intros H4.
    apply Hat. constructor 2. auto. auto.
  + intros H. destruct (FOvariable_dec y f);
    inversion H; subst; apply IHalpha in H3; auto; intros H4;
    apply Hat; constructor 3; auto. 
  + intros H. inversion H. subst. apply IHalpha in H1. auto.
    intros H2. apply Hat. constructor 4. auto. auto.
  + destruct (att_allFO_var_dec alpha1 x) as [H1 | H1].
      contradiction (Hat (att_allFO_var_conjSO_l _ _ _ H1)).
    destruct (att_allFO_var_dec alpha2 x) as [H2 | H2].
      contradiction (Hat (att_allFO_var_conjSO_r _ _ _ H2)).
    intros H. inversion H; subst. apply IHalpha1 in H5;
    auto. apply IHalpha2 in H5; auto.
  + destruct (att_allFO_var_dec alpha1 x) as [H1 | H1].
      contradiction (Hat (att_allFO_var_disjSO_l _ _ _ H1)).
    destruct (att_allFO_var_dec alpha2 x) as [H2 | H2].
      contradiction (Hat (att_allFO_var_disjSO_r _ _ _ H2)).
    intros H. inversion H; subst. apply IHalpha1 in H5;
    auto. apply IHalpha2 in H5; auto.
  + destruct (att_allFO_var_dec alpha1 x) as [H1 | H1].
      contradiction (Hat (att_allFO_var_implSO_l _ _ _ H1)).
    destruct (att_allFO_var_dec alpha2 x) as [H2 | H2].
      contradiction (Hat (att_allFO_var_implSO_r _ _ _ H2)).
    intros H. inversion H; subst. apply IHalpha1 in H5;
    auto. apply IHalpha2 in H5; auto.
  + intros H. inversion H. subst. apply IHalpha in H3.
    auto. intros H4. apply Hat. constructor. auto. auto.
  + intros H. inversion H. subst. apply IHalpha in H3.
    auto. intros H4. apply Hat. constructor. auto. auto.
Qed.

Lemma ex_att_allFO_llvar_cons_not : forall lv llv alpha,
  ~ ex_att_allFO_llvar alpha (lv :: llv) ->
  ~ ex_att_allFO_lvar alpha lv /\ ~ ex_att_allFO_llvar alpha llv.
Proof.
  intros lv llv alpha H. apply conj; intros H2.
  contradiction (H (ex_att_allFO_llvar_head _ _ _ H2)).
  contradiction (H (ex_att_allFO_llvar_tail _ _ _ H2)).
Qed.

Lemma ex_att_exFO_llvar_cons_not : forall lv llv alpha,
  ~ ex_att_exFO_llvar alpha (lv :: llv) ->
  ~ ex_att_exFO_lvar alpha lv /\ ~ ex_att_exFO_llvar alpha llv.
Proof.
  intros lv llv alpha H. apply conj; intros H2.
  contradiction (H (ex_att_exFO_llvar_head _ _ _ H2)).
  contradiction (H (ex_att_exFO_llvar_tail _ _ _ H2)).
Qed.

Lemma ex_att_allFO_lvar_cons_not: forall lv x (alpha : SecOrder),
  ~ ex_att_allFO_lvar alpha (x :: lv) ->
  ~ att_allFO_var alpha x /\ ~ ex_att_allFO_lvar alpha lv.
Proof.
  intros lv x alpha H1; split; intros H2.
  contradiction (H1 (ex_att_allFO_lvar_head _ _ _ H2)).
  contradiction (H1 (ex_att_allFO_lvar_tail _ _ _ H2)).
Qed.

Lemma ex_att_exFO_lvar_cons_not: forall lv x (alpha : SecOrder),
  ~ ex_att_exFO_lvar alpha (x :: lv) ->
  ~ att_exFO_var alpha x /\ ~ ex_att_exFO_lvar alpha lv.
Proof.
  intros lv x alpha H1; split; intros H2.
  contradiction (H1 (ex_att_exFO_lvar_head _ _ _ H2)).
  contradiction (H1 (ex_att_exFO_lvar_tail _ _ _ H2)).
Qed.

  Lemma ex_att_allFO_lvar_implSO : forall lv alpha beta,
  ~ ex_att_allFO_lvar alpha lv  ->
  ~ ex_att_allFO_lvar beta lv ->
  ~ ex_att_allFO_lvar (implSO alpha beta) lv.
Proof.
  induction lv; intros alpha beta H1 H2 H3. inversion H3.
  apply ex_att_allFO_lvar_cons_not in H1.
  apply ex_att_allFO_lvar_cons_not in H2.
  inversion H3; subst. inversion H4; subst; firstorder.
  eapply IHlv. apply H1. apply H2. inversion H3; subst; auto.
Qed.

  Lemma ex_att_allFO_lvar_conjSO : forall lv alpha beta,
  ~ ex_att_allFO_lvar alpha lv  ->
  ~ ex_att_allFO_lvar beta lv ->
  ~ ex_att_allFO_lvar (conjSO alpha beta) lv.
Proof.
  induction lv; intros alpha beta H1 H2 H3. inversion H3.
  apply ex_att_allFO_lvar_cons_not in H1.
  apply ex_att_allFO_lvar_cons_not in H2.
  inversion H3; subst. inversion H4; subst; firstorder.
  eapply IHlv. apply H1. apply H2. inversion H3; subst; auto.
Qed.

Lemma ex_att_exFO_lvar_implSO : forall lv alpha beta,
  ~ ex_att_exFO_lvar alpha lv ->
  ~ ex_att_exFO_lvar beta lv ->
  ~ ex_att_exFO_lvar (implSO alpha beta) lv.
Proof.
  induction lv; intros alpha beta H1 H2 H3. inversion H3.
  apply ex_att_exFO_lvar_cons_not in H1.
  apply ex_att_exFO_lvar_cons_not in H2.
  inversion H3; subst. inversion H4; subst; firstorder.
  eapply IHlv. apply H1. apply H2. inversion H3; subst; auto.
Qed.

Lemma ex_att_exFO_lv_conjSO_f_rev : forall lv alpha1 alpha2,
 (~ ex_att_exFO_lvar alpha1 lv) ->
 (~ ex_att_exFO_lvar alpha2 lv ) ->
  ~ ex_att_exFO_lvar (conjSO alpha1 alpha2) lv.
Proof.
  induction lv; intros alpha1 alpha2 Ha Hb H.
  inversion H.
  inversion H; subst. inversion H2; subst.
    contradiction (Ha (ex_att_exFO_lvar_head _ _ _ H4)).
    contradiction (Hb (ex_att_exFO_lvar_head _ _ _ H4)).
    apply IHlv in H2; auto.
    intros HH. apply Ha. constructor 2. auto.
    intros HH. apply Hb. constructor 2. auto.
Qed.

Lemma ex_att_exFO_llvar_implSO : forall llv alpha beta,
  ~ ex_att_exFO_llvar alpha llv ->
  ~ ex_att_exFO_llvar beta llv ->
  ~ ex_att_exFO_llvar (implSO alpha beta) llv.
Proof.
  induction llv; intros alpha beta H1 H2 H3. inversion H3.
  apply ex_att_exFO_llvar_cons_not in H1.
  apply ex_att_exFO_llvar_cons_not in H2.
  inversion H3; subst. apply ex_att_exFO_lvar_implSO in H4.
  auto. firstorder. firstorder. 
  apply (IHllv alpha beta); firstorder.
Qed.

Lemma ex_att_allFO_llvar_implSO : forall llv alpha beta,
  ~ ex_att_allFO_llvar alpha llv ->
  ~ ex_att_allFO_llvar beta llv ->
  ~ ex_att_allFO_llvar (implSO alpha beta) llv.
Proof.
  induction llv; intros alpha beta H1 H2 H3. inversion H3.
  apply ex_att_allFO_llvar_cons_not in H1.
  apply ex_att_allFO_llvar_cons_not in H2.
  inversion H3; subst. apply ex_att_allFO_lvar_implSO in H4.
  auto. firstorder. firstorder. 
  apply (IHllv alpha beta); firstorder.
Qed.

Lemma ex_att_allFO_llvar_conjSO : forall llv alpha beta,
  ~ ex_att_allFO_llvar alpha llv ->
  ~ ex_att_allFO_llvar beta llv ->
  ~ ex_att_allFO_llvar (conjSO alpha beta) llv.
Proof.
  induction llv; intros alpha beta H1 H2 H3. inversion H3.
  apply ex_att_allFO_llvar_cons_not in H1.
  apply ex_att_allFO_llvar_cons_not in H2.
  inversion H3; subst. apply ex_att_allFO_lvar_conjSO in H4.
  auto. firstorder. firstorder. 
  apply (IHllv alpha beta); firstorder.
Qed.

Lemma att_exFO_var__lv : forall l alpha,
  (forall x, ~ att_exFO_var alpha x) ->
  ~ ex_att_exFO_lvar alpha l.
Proof.
  induction l; intros alpha H1 H2;
    inversion H2; subst; firstorder.
Qed.
  
Lemma att_exFO_var__llv : forall l alpha,
  (forall x, ~ att_exFO_var alpha x) ->
  ~ ex_att_exFO_llvar alpha l.
Proof.
  induction l; intros alpha H H2; inversion H2;
    subst. eapply att_exFO_var__lv in H.
  contradiction (H H3). apply IHl in H3; auto.
Qed.

Lemma att_allFO_var__lv : forall l alpha,
  (forall x, ~ att_allFO_var alpha x) ->
  ~ ex_att_allFO_lvar alpha l.
Proof.
  induction l; intros alpha H1 H2. inversion H2.
  inversion H2; subst. firstorder.
  apply IHl in H3; auto.
Qed.

Lemma att_allFO_var__lv_gen : forall l alpha,
  (forall x, In x l -> ~ att_allFO_var alpha x) <->
  ~ ex_att_allFO_lvar alpha l.
Proof.
  induction l; intros alpha; split; intros H.
  - intros H2. inversion H2.
  - intros x Hx H2. inversion Hx.
  - intros H2. inversion H2; subst. firstorder.
    apply IHl in H3; auto. intros y Hy. apply H. firstorder.
  - intros x Hx H2. simpl in Hx.  destruct Hx.  subst. 
    contradiction (H (ex_att_allFO_lvar_head _ _ _ H2)).
    apply IHl in H2; auto. intros H3. apply H.
    constructor 2. auto. 
Qed. 

Lemma att_allFO_var__llv : forall l alpha,
  (forall x, ~ att_allFO_var alpha x) ->
  ~ ex_att_allFO_llvar alpha l.
Proof.
  induction l; intros alpha H H2. inversion H2.
  inversion H2; subst. apply att_allFO_var__lv in H3; auto.
  apply IHl in H3; auto.
Qed.

Lemma att_allFO_var__llv_gen : forall l alpha,
  (forall x, In x (flat_map (fun y => y) l) -> ~ att_allFO_var alpha x) <->
  ~ ex_att_allFO_llvar alpha l.
Proof.
  induction l; intros alpha; split; intros H. 
  - intros H2. inversion H2.
  - intros x Hx H2. inversion Hx.
  - intros H2. inversion H2; subst.
    apply att_allFO_var__lv_gen in H3; auto.
    intros y Hy. apply H. simpl. firstorder. 
    apply IHl in H3; auto. intros y Hy.
    apply H. simpl. firstorder.
  - intros x H2. simpl in H2. apply in_app_or in H2.
    apply ex_att_allFO_llvar_cons_not in H. 
    destruct H as [H H']. pose proof (att_allFO_var__lv_gen a alpha) as H3.
    destruct H2 as [H2 | H2]. destruct H3 as [H3 H3']. apply H3'; auto.
    apply IHl; auto. 
Qed.

Lemma att_exFO_instant_cons_empty'_pre_non_neg : forall beta P x y ,
att_exFO_var
  (replace_pred beta P x (negSO (eqFO x x))) y ->
att_exFO_var beta y.
Proof.
  induction beta; intros P y x Hat; simpl in *; auto;
    simpl in *.
  + FOv_dec_l_rep. destruct (predicate_dec P p); subst; auto.
     inversion Hat; subst. inversion H0.
  + inversion Hat; subst. constructor. apply IHbeta in H2.
    auto.
  + inversion Hat; subst. constructor. auto.
    constructor 2. apply IHbeta in H2. auto.
  + inversion Hat; subst; apply IHbeta in H0; constructor; auto.
  + inversion Hat; subst. apply IHbeta1 in H2. constructor. auto.
    apply IHbeta2 in H2. constructor 6. auto.
  + inversion Hat; subst. apply IHbeta1 in H2. constructor. auto.
    apply IHbeta2 in H2. constructor 8. auto.
  + inversion Hat; subst. apply IHbeta1 in H2. constructor. auto.
    apply IHbeta2 in H2. constructor 10. auto.
  + destruct (predicate_dec P p). apply IHbeta in Hat. constructor.
    auto. inversion Hat; subst. apply IHbeta in H2. constructor. auto.
  + destruct (predicate_dec P p). apply IHbeta in Hat. constructor.
    auto. inversion Hat; subst. apply IHbeta in H2. constructor. auto.
Qed.

Lemma att_exFO_instant_cons_empty'_pre : forall beta P x y ,
 ~ att_exFO_var beta y ->
~ att_exFO_var
  (replace_pred beta P x (negSO (eqFO x x))) y.
Proof.
  intros beta P x y H1 H2.
  apply att_exFO_instant_cons_empty'_pre_non_neg in H2; auto.
Qed.

Lemma att_exFO_instant_cons_empty'_pre_l : forall l beta x,
~  att_exFO_var beta x ->
~ att_exFO_var
  (replace_pred_l beta l
     (nlist_list (length l) (nlist_var _ (Var 1)))
     (nlist_list (length l) (nlist_empty _))) x.
Proof.
  induction l; intros beta x H.
    simpl. assumption.

    simpl. apply att_exFO_instant_cons_empty'_pre.
    apply IHl. assumption.
Qed.


Lemma att_exFO_instant_cons_empty' : forall beta alpha x,
~  att_exFO_var beta x ->
~  att_exFO_var (instant_cons_empty' alpha beta) x.
Proof.
  intros beta alpha x H.
  unfold instant_cons_empty'.
  apply att_exFO_instant_cons_empty'_pre_l.
  assumption.
Qed.

Lemma rep_FOv_att_exFO: forall alpha x y z,
~ att_exFO_var alpha x ->
  ~z = x ->
~ att_exFO_var (replace_FOv alpha y z) x.
Proof.
  induction alpha; intros x y z Hat Hneq; simpl in *;
  try solve [dest_FOv_dec_blind; intros HH; inversion HH].
  + dest_FOv_dec_blind; intros HH; subst;
    inversion HH; subst; apply IHalpha in H2; auto.
    intros HH2; apply Hat; constructor; auto.
    intros HH2; apply Hat; constructor; auto.
  + dest_FOv_dec_blind; intros HH; subst.
    inversion HH; subst. firstorder.
    apply IHalpha in H2; auto.
    intros HH2; apply Hat; constructor 2. auto.
    inversion HH; subst. apply Hat. constructor. auto.
    apply IHalpha in H2; auto.
    intros HH2. apply Hat. constructor 2. auto.
  + intros HH. inversion HH; subst. apply IHalpha in H0;
    auto. intros HH2. apply Hat. constructor.
    auto.
  + intros HH; inversion HH; subst.
    apply IHalpha1 in H2; auto. intros HH2. apply Hat.
    constructor. auto. apply IHalpha2 in H2; auto.
    intros H3. apply Hat. constructor 6. auto.
  + intros HH; inversion HH; subst.
    apply IHalpha1 in H2; auto. intros HH2. apply Hat.
    constructor. auto. apply IHalpha2 in H2; auto.
    intros H3. apply Hat. constructor 8. auto.
  + intros HH; inversion HH; subst.
    apply IHalpha1 in H2; auto. intros HH2. apply Hat.
    constructor. auto. apply IHalpha2 in H2; auto.
    intros H3. apply Hat. constructor 10. auto.
  + intros HH. inversion HH; subst. apply IHalpha in H2; auto.
    intros HH2. apply Hat. constructor. auto.
  + intros HH. inversion HH; subst. apply IHalpha in H2; auto.
    intros HH2. apply Hat. constructor. auto.
Qed.



Lemma is_in_FOvar_att_exFO_var : forall alpha x,
att_exFO_var alpha x -> In x (FOvars_in alpha).
Proof.
  induction alpha; intros x H; auto; simpl in *;
    inversion H; subst; firstorder.
Qed.

Lemma is_in_FOvar_att_exFO_var_neg : forall alpha x,
  ~ In x (FOvars_in alpha) ->
  ~ att_exFO_var alpha x.
Proof.
  intros alpha x H1 H2.
  apply is_in_FOvar_att_exFO_var in H2; auto.
Qed.


Lemma  att_exFO_var_REL : forall rel x,
  REL rel = true ->
  ~ att_exFO_var rel x.
Proof.
  induction rel; intros x H; auto;
    intros HH; inversion HH; subst;
      firstorder; simpl in *;
        if_then_else_dest_blind; auto; firstorder.
Qed. 

Lemma  att_exFO_var_AT : forall atm x,
  AT atm = true ->
  ~ att_exFO_var atm x.
Proof.
  induction atm; intros x H; auto;
    intros HH; inversion HH; subst;
      firstorder; simpl in *;
        if_then_else_dest_blind; auto; firstorder.
Qed.

Lemma ex_att_allFO_lvar_dec : forall alpha lv,
{ex_att_allFO_lvar alpha lv} + {~ ex_att_allFO_lvar alpha lv}.
Proof.
  induction lv. right. intros HH. inversion HH.
  destruct (att_allFO_var_dec alpha a). left.
  constructor. auto. 
  destruct IHlv. left. constructor 2. auto.
  right. intros HH. inversion HH; subst; contradiction.
Qed.

Lemma ex_att_allFO_llvar_dec : forall alpha llv,
{ex_att_allFO_llvar alpha llv} + {~ ex_att_allFO_llvar alpha llv}.
Proof.
  induction llv. right. intros HH. inversion HH.
  destruct (ex_att_allFO_lvar_dec alpha a). left.
  constructor. auto. 
  destruct IHllv. left. constructor 2. auto.
  right. intros HH. inversion HH; subst; contradiction.
Qed.  

Lemma ex_att_allFO_llvar_implSO_fwd: forall llv alpha beta,
  ex_att_allFO_llvar (implSO alpha beta) llv ->
  ex_att_allFO_llvar alpha llv \/ ex_att_allFO_llvar beta llv.
Proof.
  intros llv alpha beta H.
  destruct (ex_att_allFO_llvar_dec alpha llv). left. auto. 
  destruct (ex_att_allFO_llvar_dec beta llv) as [HH | HH]. right. auto.
  apply ex_att_allFO_llvar_implSO in H; auto; contradiction.
Qed.

Lemma ex_att_allFO_llvar_conjSO_fwd: forall llv alpha beta,
  ex_att_allFO_llvar (conjSO alpha beta) llv ->
  ex_att_allFO_llvar alpha llv \/ ex_att_allFO_llvar beta llv.
Proof.
  intros llv alpha beta H.
  destruct (ex_att_allFO_llvar_dec alpha llv). left. auto. 
  destruct (ex_att_allFO_llvar_dec beta llv) as [HH | HH]. right. auto.
  apply ex_att_allFO_llvar_conjSO in H; auto; contradiction.
Qed.

Lemma ex_att_allFO_lvar_REL : forall l rel,
  REL rel = true -> ~ ex_att_allFO_lvar rel l.
Proof.
  induction l; intros rel Hrel H. inversion H.
  inversion H; subst. apply att_allFO_var_REL in H2; auto.
  apply IHl in H2; auto.
Qed.

Lemma ex_att_allFO_llvar_REL : forall l rel,
  REL rel = true -> ~ ex_att_allFO_llvar rel l.
Proof.
  induction l; intros rel Hrel H. inversion H.
  inversion H; subst. apply ex_att_allFO_lvar_REL in H2; auto.
  apply IHl in H2; auto.
Qed.

Lemma ex_att_allFO_lvar_AT : forall l rel,
  AT rel = true -> ~ ex_att_allFO_lvar rel l.
Proof.
  induction l; intros rel Hrel H. inversion H.
  inversion H; subst. apply att_allFO_var_AT in H2; auto.
  apply IHl in H2; auto.
Qed.

Lemma ex_att_allFO_llvar_AT : forall l rel,
  AT rel = true -> ~ ex_att_allFO_llvar rel l.
Proof.
  induction l; intros rel Hrel H. inversion H.
  inversion H; subst. apply ex_att_allFO_lvar_AT in H2; auto.
  apply IHl in H2; auto.
Qed.

Lemma var_in_SO_att_allFO_x : forall alpha x,
 ~ var_in_SO alpha x ->
  ~ att_allFO_var alpha x.
Proof.
  induction alpha; intros x Hocc H;
    try solve [inversion H];
    try solve [inversion H; subst; firstorder].
  + inversion H; subst; unfold var_in_SO in *; simpl in *.
    apply IHalpha1 in H3; firstorder.
    apply IHalpha2 in H3; firstorder.
  + inversion H; subst; unfold var_in_SO in *; simpl in *.
    apply IHalpha1 in H3; firstorder.
    apply IHalpha2 in H3; firstorder.
  + inversion H; subst; unfold var_in_SO in *; simpl in *.
    apply IHalpha1 in H3; firstorder.
    apply IHalpha2 in H3; firstorder.
Qed.