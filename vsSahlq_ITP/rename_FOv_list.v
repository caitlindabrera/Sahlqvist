Require Import FOvars_in Rep_Pred_FOv.

Fixpoint rename_FOv_list (l : list FOvariable) x y : list FOvariable :=
  match l with
  | nil => nil
  | cons z l' => if FOvariable_dec x z then cons y (rename_FOv_list l' x y)
                 else cons z (rename_FOv_list l' x y)
  end.

Fixpoint rename_FOv_list_l l lv1 lv2 : list FOvariable :=
  match lv1, lv2 with 
  | nil, _ => l
  | _, nil => l
  | y :: lv1', z :: lv2' => (rename_FOv_list (rename_FOv_list_l l lv1' lv2') y z)
  end.

Lemma rename_FOv_list_cons : forall l a x y,
    rename_FOv_list (a :: l) x y =
    if FOvariable_dec x a then y :: (rename_FOv_list l x y)
    else a :: (rename_FOv_list l x y).
Proof. auto. Qed.
  
Lemma rename_FOv_list_app : forall l1 l2 x y,
  rename_FOv_list (app l1 l2) x y =
  app (rename_FOv_list l1 x y) (rename_FOv_list l2 x y).
Proof.
  induction l1; intros l2 [xn] [ym]; auto.
  simpl app at 1. do 2 rewrite rename_FOv_list_cons.
  destruct (FOvariable_dec (Var xn) a); simpl;
             rewrite IHl1; auto.
Qed.

Lemma rename_FOv_list_not_eq : forall l x y,
  ~ x = y ->
  ~ In x (rename_FOv_list l x y).
Proof.
  induction l; intros x y Hneq H. auto.
  simpl. destruct (FOvariable_dec x a); subst; simpl in *.
    rewrite FOvariable_dec_l in H. simpl in H. 
    destruct H. auto. apply IHl  in H; auto.
    auto.  rewrite FOvariable_dec_r in H; auto.
    simpl in H. destruct H. auto.
    apply IHl in H; auto.
Qed.

Lemma rename_FOv_list_refl : forall l x,
  rename_FOv_list l x x = l.
Proof.
  induction l; intros x. auto.
  simpl. rewrite IHl. destruct (FOvariable_dec x a).
  subst. auto. auto.
Qed.

Lemma rep__ren_list : forall alpha x y,
 (FOvars_in (replace_FOv alpha x y)) =
  rename_FOv_list (FOvars_in alpha) x y.
Proof.  
  induction alpha; intros x y; simpl in *;
    try apply IHalpha.
    destruct (FOvariable_dec x f); auto.
    destruct (FOvariable_dec x f); destruct (FOvariable_dec x f0); auto.
    destruct (FOvariable_dec x f); destruct (FOvariable_dec x f0); auto.
    destruct (FOvariable_dec x f); simpl; rewrite IHalpha; auto.
    destruct (FOvariable_dec x f); simpl; rewrite IHalpha; auto.
    rewrite IHalpha1. rewrite IHalpha2. rewrite rename_FOv_list_app. auto.
    rewrite IHalpha1. rewrite IHalpha2. rewrite rename_FOv_list_app. auto.
    rewrite IHalpha1. rewrite IHalpha2. rewrite rename_FOv_list_app. auto.
Qed.

Lemma rename_FOv_list_not_in : forall l x y,
    ~ In x l -> rename_FOv_list l x y = l.
Proof.
  induction l; intros [xn] [ym] H. auto.
  simpl in *. rewrite FOvariable_dec_r.
  rewrite IHl; auto. firstorder.
Qed.    


Lemma is_in_FOvar_rename_FOv_list : forall l x y z,
  ~ x = y ->
  ~ x = z ->
  ~ y = z ->
  In x (rename_FOv_list l y z) <-> In x l.
Proof.
  induction l; intros x y z H1 H2 H3. firstorder. 
  simpl. destruct (FOvariable_dec y a). subst. simpl.
  split; intros [H | H]; subst; firstorder.
  simpl. firstorder.
Qed.

Lemma in_rename_FOv_list_2 : forall l x y,
  In x l -> In y (rename_FOv_list l x y).
Proof.
  induction l; intros x y H. firstorder.
  simpl. simpl in H. destruct H.
  + rewrite FOvariable_dec_l. firstorder. auto.
  + destruct (FOvariable_dec x a). firstorder. auto.
    simpl. right. firstorder.
Qed.