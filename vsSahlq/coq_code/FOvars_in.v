Require Export base_mods SO_syntax.

Fixpoint FOvars_in alpha : list FOvariable :=
  match alpha with
    predSO P x => cons x nil
  | relatSO x y => cons x (cons y nil)
  | eqFO x y => cons x (cons y nil)
  | allFO x beta => cons x (FOvars_in beta)
  | exFO x beta => cons x (FOvars_in beta)
  | negSO beta => FOvars_in beta
  | conjSO beta1 beta2 => app (FOvars_in beta1) (FOvars_in beta2)
  | disjSO beta1 beta2 => app (FOvars_in beta1) (FOvars_in beta2)
  | implSO beta1 beta2 => app (FOvars_in beta1) (FOvars_in beta2)
  | allSO P beta => FOvars_in beta
  | exSO P beta => FOvars_in beta
  end.

Definition var_in_SO alpha x := In x (FOvars_in alpha).

Lemma var_in_SO_conjSO : forall alpha1 alpha2 x,
    var_in_SO (conjSO alpha1 alpha2) x <->
    var_in_SO alpha1 x \/ var_in_SO alpha2 x.
Proof.
  intros alpha1 alpha2 x. unfold var_in_SO. simpl.
  firstorder.
Qed.

Lemma var_in_SO_conjSO_f : forall alpha1 alpha2 x,
  ~ var_in_SO (conjSO alpha1 alpha2) x ->
  ~ var_in_SO alpha1 x /\ ~ var_in_SO alpha2 x.
Proof.
  intros alpha1 alpha2 x Hocc. unfold var_in_SO in *.
  simpl in *. firstorder.
Qed.

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

(*
Fixpoint predSO_vars_list alpha P : list FOvariable :=
  match alpha with
    predSO Q x => if predicate_dec P Q then cons x nil else nil
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
*)

(* creates a list of FOvariables that are attached to P *)
Fixpoint FOv_att_P alpha P : list FOvariable :=
  match alpha with
    predSO Q x => if predicate_dec P Q then cons x nil else nil
  | relatSO _ _ => nil
  | eqFO _ _ => nil
  | allFO _ beta => FOv_att_P beta P
  | exFO _ beta => FOv_att_P beta P
  | negSO beta => FOv_att_P beta P
  | conjSO beta1 beta2 => app (FOv_att_P beta1 P) (FOv_att_P beta2 P)
  | disjSO beta1 beta2 => app (FOv_att_P beta1 P) (FOv_att_P beta2 P)
  | implSO beta1 beta2 => app (FOv_att_P beta1 P) (FOv_att_P beta2 P)
  | allSO _ beta => FOv_att_P beta P
  | exSO _ beta => FOv_att_P beta P 
  end.

Fixpoint FOv_att_P_l alpha lP : list (list FOvariable) :=
  match lP with
  | nil => nil
  | cons P lP' => cons (FOv_att_P alpha P) (FOv_att_P_l alpha lP')
  end.

Definition rem_FOv x l := remove FOvariable_dec x l.

Lemma rem_FOv_cons : forall l x y,
    rem_FOv x (y :: l) = if FOvariable_dec x y then rem_FOv x l else y :: rem_FOv x l.
Proof. auto. Qed.

Lemma want13 : forall l x y,
  ~ x = y -> In y (rem_FOv x l) <-> In y l.
Proof.
  induction l; intros x y Hneq. auto.
  simpl in *. lia. simpl.
  destruct (FOvariable_dec x a); subst;
    firstorder.
Qed.

Lemma is_in_FOvar_rem_FOv_f : forall l x,
  ~ In x (rem_FOv x l).
Proof. intros l x. unfold rem_FOv. apply remove_In. Qed.

Lemma incl_FOv_att_P : forall alpha P,
incl (FOv_att_P alpha P) (FOvars_in alpha).
Proof.
  induction alpha; intros P; simpl; try solve [firstorder];
    try ( apply incl_app_gen; auto).
  + destruct (predicate_dec P p); firstorder.  
Qed.

Fixpoint FOvify ln : list FOvariable :=
  match ln with
  | nil => nil
  | x :: ln' => (Var x) :: (FOvify ln')
  end.

Lemma var_in_SO_dec : forall alpha x,
    {var_in_SO alpha x} + {~ var_in_SO alpha x}.
Proof.
  intros alpha x. unfold var_in_SO.
  apply in_dec. apply FOvariable_dec.
Qed.

Inductive var_in_SO_l : (list SecOrder) -> list FOvariable -> Prop :=
| var_in_SO_l_nil1 lcond : var_in_SO_l lcond nil
| var_in_SO_l_nil2 lx : var_in_SO_l nil lx
| var_in_SO_l_cons cond lcond x lx : var_in_SO cond x ->
                                     var_in_SO_l lcond lx ->
                                     var_in_SO_l (cond :: lcond) (x :: lx).

Inductive var_not_in_SO_l : (list SecOrder) -> list FOvariable -> Prop :=
| var_not_in_SO_l_nil1 lcond : var_not_in_SO_l lcond nil
| var_not_in_SO_l_nil2 lx : var_not_in_SO_l nil lx
| var_not_in_SO_l_cons cond lcond x lx :
    (forall y, ~ x = y -> ~ var_in_SO cond y) ->
    var_not_in_SO_l lcond lx -> var_not_in_SO_l (cond :: lcond) (x :: lx).

Lemma length_FOv_att_P_l : forall lP alpha,
  length lP = length (FOv_att_P_l alpha lP).
Proof.
  induction lP; intros alpha.
    reflexivity.

    simpl. rewrite <- IHlP. reflexivity.
Qed.

Inductive in_in_FOvar_ll : list (list FOvariable) -> list (list FOvariable) -> Prop :=
| in_in_FOvar_ll_nil : in_in_FOvar_ll nil nil
| in_in_FOvar_ll_cons x1 l1 x2 l2 : incl x1 x2 -> in_in_FOvar_ll l1 l2 ->
                                    in_in_FOvar_ll (x1 :: l1) (x2 :: l2).

Fixpoint ex_nil_in_llv (llv : list (list FOvariable)) : bool :=
  match llv with
  | nil => false
  | cons nil llv => true
  | cons (cons v lv) llv' => ex_nil_in_llv llv'
  end.

Lemma lem_try40 : forall lP beta gamma,
  ex_nil_in_llv (FOv_att_P_l gamma lP) = false ->
  ex_nil_in_llv (FOv_att_P_l (conjSO beta gamma) lP) = false.
Proof.
  induction lP; intros beta gamma Hex.
    simpl in *. reflexivity.

    simpl in *.
    case_eq (FOv_att_P gamma a). intros Hg. rewrite Hg in *.
      discriminate.

      intros x lx Hlx. rewrite <- Hlx.
      case_eq (app (FOv_att_P beta a) (FOv_att_P gamma a)).
        intros H. rewrite Hlx in H.
        destruct (FOv_att_P beta a); discriminate.

        intros y ly Hly.
        apply IHlP. rewrite Hlx in Hex. assumption.
Qed.

Fixpoint ex_FOvar_var_ll x llx :=
  match llx with
  | nil => false
  | cons lx llx' => if in_dec FOvariable_dec x lx then true else ex_FOvar_var_ll x llx'
  end.

Lemma ex_nil_in_llv_app_f : forall l1 l2,
  ex_nil_in_llv (app l1 l2) = false <->
  ex_nil_in_llv l1 = false /\
  ex_nil_in_llv l2 = false.
Proof.
  induction l1; intros l2.
    simpl. split; intros H.
      apply conj. reflexivity.
        assumption.
      apply H.

    simpl. destruct a. split; intros H.
      discriminate. destruct H. discriminate.

      apply IHl1.
Qed.
