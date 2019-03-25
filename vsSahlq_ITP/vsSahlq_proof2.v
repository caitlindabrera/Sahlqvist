Require Export high_mods SO_sem_mods.
Require Import vsSahlq_proof1 vsS_syn_sem SO_facts3 Monotonicity_lP_SO.
Require Import consistent FunctionalExtensionality.

Fixpoint change {A : Type} (l : list A) (n : nat) (a : A) :=
  match l, n with
  | nil, _ => nil
  | l, 0 => l
  | cons b l', 1 => cons a l'
  | cons b l', S m => cons b (change l' m a)
  end.

Fixpoint change_ln {A : Type} (l : list A) (ln : list nat) (a : A) :=
  match ln with
  | nil => l
  | cons n ln' => change (change_ln l ln' a) n a
  end.

Lemma change_ln_nil : forall W l pa,
  @change_ln W nil l pa = nil.
Proof.
  induction l; intros pa. reflexivity.
  simpl. rewrite IHl. reflexivity.
Qed.

Lemma change_ln_cons_n : forall  lP n P (W : Set) lpa (pa pa2 : W -> Prop),
   ~ lP = nil -> 
  change_ln (cons pa lpa) (indicies_l2_pre lP P (S n)) pa2 =
  cons pa (change_ln lpa (indicies_l2_pre lP P n) pa2).
Proof.
  induction lP; intros n P W lpa pa pa2 Hnil. contradiction.
  case_eq lP. intros HlP. subst. simpl in *. 
      destruct (predicate_dec P a); subst; auto.
  intros T lT HlT. rewrite <- HlT.
  assert (~ lP = nil) as Hnil2.
  rewrite HlT. discriminate. simpl.
  destruct (predicate_dec P a); simpl; rewrite IHlP; auto. 
Qed.

Lemma lem_a2 : forall lP P Q W Ip pa lpa',
~ P = Q ->
@alt_Ip_list W Ip (change_ln lpa' (indicies_l2 lP P) pa) lP Q
 = alt_Ip_list Ip lpa' lP Q.
Proof.
  induction lP; intros P Q W Ip pa lpa' Hneq. auto.
  unfold indicies_l2. simpl.
  destruct lpa'. 
  + simpl. rewrite change_ln_nil. auto.
  + rename P0 into pa2.  simpl.
    destruct (predicate_dec P a); subst; simpl in *.
    ++ rewrite alt_Ip_neq; auto.
       case_eq lP. intros HlP. simpl. 
       destruct lpa'; simpl; rewrite alt_Ip_neq; auto. 
       intros U lU HlU. rewrite <- HlU.
       assert (~ lP = nil) as Hnil2.
         rewrite HlU. discriminate.
       rewrite <- IHlP with (P := a) (pa := pa).
       rewrite change_ln_cons_n. simpl. 
       rewrite alt_Ip_neq. all : auto.
    ++ case_eq lP. intros HlP. auto.
       intros U lU HlU. rewrite <- HlU.
       rewrite change_ln_cons_n. simpl. 
       unfold indicies_l2 in IHlP.
       destruct (predicate_dec a Q). subst.
       do 2 rewrite alt_Ip_eq.  auto.
       do 2 (rewrite alt_Ip_neq; auto).
       rewrite HlU. discriminate.
Qed.

Lemma lem_a1 : forall lP P W Ip pa lpa',
@alt_Ip W (alt_Ip_list Ip lpa' lP) pa P =
alt_Ip (alt_Ip_list Ip (change_ln lpa' (indicies_l2 lP P) pa) lP)
  pa P.
Proof.
  intros. apply functional_extensionality. 
  intros Q. destruct (predicate_dec P Q). subst.
  do 2 rewrite alt_Ip_eq. auto.
  do 2 (rewrite alt_Ip_neq; auto).
  symmetry. apply lem_a2. auto.
Qed.

Lemma lem_a7 : forall (lP : list predicate) (W : Set) (lpa : list (W -> Prop)) (pa pa2 : W -> Prop)
  (P Q : predicate),
~ P = Q ->
@is_constant (W -> Prop)
  (@ind_gen (W -> Prop) pa2 (indicies_l2 (P :: lP) Q)
     (@change_ln (W -> Prop) (pa :: lpa) (indicies_l2 (P :: lP) P) pa)) <->
@is_constant (W -> Prop)
  (@ind_gen (W -> Prop) pa2 (indicies_l2 lP Q)
     (@change_ln (W -> Prop) lpa (indicies_l2 lP P) pa)).
Proof.
  unfold is_constant. unfold indicies_l2.
  intros lP W lpa pa pa2 P Q Hneq.
  split; intros H.
  + destruct H as [a [ n H]].
    simpl in H. destruct (predicate_dec Q P); subst.
    contradiction. pred_dec_l_rep. simpl in *.
    destruct lP. simpl in *. exists a, 0. auto.
    remember (p :: lP) as lP'.
    rewrite change_ln_cons_n in H.
    simpl in H. 
    rewrite ind_gen_pre_cons in H. 
    exists a. exists n. auto. subst. discriminate.
  + destruct H as [a [ n H]].
    simpl in *. destruct (predicate_dec Q P); subst.
    contradiction. pred_dec_l_rep. simpl in *.
    destruct lP. simpl in *. exists a, 0. auto.
    remember (p :: lP) as lP'.
    rewrite change_ln_cons_n. simpl.
    rewrite ind_gen_pre_cons. 
    exists a. exists n. auto. subst. discriminate.  
Qed.

Lemma length_indicies_l2_pre : forall lP n m P,
  length (indicies_l2_pre lP P n) = 
  length (indicies_l2_pre lP P m).
Proof.
  induction lP; intros n m P; auto. simpl. 
  destruct (predicate_dec P a); subst; simpl; auto.  
Qed. 

Lemma lem_a8_eq : forall (lP : list predicate) (W : Set) (lpa : list (W -> Prop)) (pa pa2 : W -> Prop)
  (P : predicate),
  length lP = length lpa ->
  (@ind_gen (W -> Prop) pa2 (indicies_l2 lP P)
     (@change_ln (W -> Prop) lpa (indicies_l2 lP P) pa)) = 
    repeat pa (length (indicies_l2 lP P)).
Proof.
  unfold indicies_l2. induction lP; 
  intros W lpa pa p2 P Hlength. auto.
  simpl. case_eq lP.
  + intros HlP. simpl. destruct (predicate_dec P a).
    simpl. destruct lpa. discriminate.
    simpl. all : try reflexivity.
  + intros PP lPP HlP.
    rewrite <- HlP.
    assert (~ lP = nil) as HH.
      rewrite HlP. discriminate.
    destruct (predicate_dec P a).
    ++ destruct lpa. discriminate.
       simpl. rewrite change_ln_cons_n. simpl.
       rewrite ind_gen_pre_cons. rewrite IHlP.
       rewrite length_indicies_l2_pre with (m := 1).
       all : auto.
    ++ destruct lpa. discriminate.
       simpl. rewrite change_ln_cons_n.
       rewrite ind_gen_pre_cons. rewrite IHlP. 
       rewrite length_indicies_l2_pre with (m := 1).
       all : auto.
Qed.

Lemma lem_a8 : forall (lP : list predicate) (W : Set) a n (lpa : list (W -> Prop)) (pa pa2 : W -> Prop)
  (P Q : predicate),
~ P = Q ->
 (@ind_gen (W -> Prop) pa2 (indicies_l2_pre lP Q 0) lpa) = repeat a n ->
  (@ind_gen (W -> Prop) pa2 (indicies_l2 lP Q)
     (@change_ln (W -> Prop) lpa (indicies_l2 lP P) pa)) = repeat a n.
Proof.
  induction lP; intros W b n lpa pa pa2 P Q Hneq Hn. auto.
  unfold indicies_l2 in *. simpl in *.
  case_eq lP. 
  + intros HlP; rewrite HlP in *. 
    simpl in *. destruct (predicate_dec Q a);
                destruct (predicate_dec P a); subst;
                  simpl in *; auto.
    contradiction. 
  + intros PP lPP HlP. rewrite <- HlP.
    assert (~ lP = nil) as HlPnil.
      rewrite HlP. discriminate.        
    destruct (predicate_dec Q a).
    ++ subst a.
       simpl in *. case_eq lpa. intros Hlpa. rewrite Hlpa in *.
       rewrite change_ln_nil. assumption.
       intros pa3 lpa3 Hlpa. rewrite <- Hlpa.
       destruct (predicate_dec P Q). subst Q.
       contradiction.
       simpl in *.
       rewrite Hlpa in *. simpl in Hn.
       rewrite change_ln_cons_n. simpl.
       rewrite ind_gen_pre_cons in Hn.
       rewrite ind_gen_pre_cons. destruct n. simpl in *. discriminate.
       rewrite IHlP with (a := b) (n := n). inversion Hn as [[H1 H2]].
       rewrite H2. all : auto.
       inversion Hn. reflexivity.
    ++ simpl in *. case_eq lpa. intros Hlpa. rewrite Hlpa in *.
       rewrite change_ln_nil. assumption.
       intros pa3 lpa3 Hlpa. rewrite <- Hlpa.
       destruct (predicate_dec P a). subst a. simpl. 
       * simpl. rewrite Hlpa in *. simpl in *.
         rewrite change_ln_cons_n in *. simpl.
         rewrite ind_gen_pre_cons in *.
         rewrite IHlP with (a := b) (n := n).
         reflexivity. all : try assumption.
       * rewrite Hlpa in *. rewrite change_ln_cons_n.
         rewrite ind_gen_pre_cons.
         rewrite ind_gen_pre_cons in Hn.
         apply IHlP. all : assumption.
Qed.

Lemma lem_a10 : forall (lP : list predicate) (W : Set) (lpa : list (W -> Prop)) (pa pa2 : W -> Prop)
  (P Q : predicate),
~ P = Q ->
@is_constant (W -> Prop) (@ind_gen (W -> Prop) pa2 (indicies_l2_pre lP Q 0) lpa) ->
@is_constant (W -> Prop)
  (@ind_gen (W -> Prop) pa2 (indicies_l2 lP Q)
     (@change_ln (W -> Prop) lpa (indicies_l2 lP P) pa)).
Proof.
  unfold is_constant. intros until 0. intros Hneq Hcon.
  destruct Hcon as [a [n H]].
  exists a. exists n. apply lem_a8; assumption.
Qed.

Lemma lem_a10_eq : forall (lP : list predicate) (W : Set) (lpa : list (W -> Prop)) (pa pa2 : W -> Prop)
  (P : predicate),
  length lP = length lpa ->
@is_constant (W -> Prop)
  (@ind_gen (W -> Prop) pa2 (indicies_l2 lP P)
     (@change_ln (W -> Prop) lpa (indicies_l2 lP P) pa)).
Proof.
  unfold is_constant. intros until 0. intros Hlength.
  exists pa. exists (length (indicies_l2 lP P)).
  unfold indicies_l2. apply lem_a8_eq.
  assumption.
Qed.

Lemma lem_a6 : forall (lP : list predicate) (W : Set) (lpa : list (W -> Prop)) (pa pa2 : W -> Prop)
  (P Q : predicate),
~ P = Q ->
@is_constant (W -> Prop) (@ind_gen (W -> Prop) pa2 (indicies_l2 lP Q) lpa) ->
@is_constant (W -> Prop)
  (@ind_gen (W -> Prop) pa2 (indicies_l2 (P :: lP) Q)
     (@change_ln (W -> Prop) (pa :: lpa) (indicies_l2 (P :: lP) P) pa)).
Proof.
  unfold indicies_l2.
  intros. apply lem_a7. assumption.
  apply lem_a10; assumption.
Qed.

Lemma lem_a5 : forall lP W lpa pa pa2 P Q,
length lP = length lpa ->
@consistent_lP_lpa_P W pa2 lP lpa Q ->
@consistent_lP_lpa_P W pa2 (P :: lP) 
  (@change_ln (W -> Prop) (cons pa lpa) (indicies_l2 (cons P lP) P) pa) Q.
Proof.
  unfold consistent_lP_lpa_P. intros until 0. intros Hlength Hcon.
  destruct (predicate_dec P Q). subst. apply lem_a10_eq. simpl. auto.
  apply lem_a6; auto.
Qed.

Lemma lem_a4 : forall lP W lpa pa pa2 P,
length lP = length lpa ->
@consistent_lP_lpa W pa2 lP lpa ->
@consistent_lP_lpa W pa2 (P :: lP)
  (@change_ln (W -> Prop) (cons pa lpa) (indicies_l2 (cons P lP) P) pa).
Proof.
  unfold consistent_lP_lpa.
  intros until 0. intros H1 H2 Q. apply lem_a5. assumption.
  apply H2.
Qed.

Lemma lem_a11 : forall lP P (W : Set) lpa pa pa2,
(@change_ln (W -> Prop) (cons pa lpa) (indicies_l2 (cons P lP) P) pa2) =
(cons pa2 (@change_ln (W -> Prop) lpa (indicies_l2 lP P) pa2)).
Proof.
  intros. unfold indicies_l2. simpl.
  pred_dec_l_rep. simpl.
  destruct lP. simpl. reflexivity.
  rewrite change_ln_cons_n. simpl. reflexivity.
  discriminate.
Qed.

Lemma length_change : forall (W : Set) l n pa,
  length (@change (W -> Prop) l n pa) = length l.
Proof.
 induction l; intros n pa. reflexivity.
  simpl. destruct n. reflexivity.
  destruct n. reflexivity.
  simpl. rewrite IHl. reflexivity.
Qed.

Lemma length_change_ln : forall (W : Set) ln lpa pa,
  length (@change_ln (W -> Prop) lpa ln pa) =
  length lpa.
Proof.
  induction ln; intros lpa pa. reflexivity.
  simpl. rewrite length_change. apply IHln.
Qed. 

Lemma alt_Ip_list_consistent_lP_lpa' : forall lP (W : Set) Ip lpa pa2,
  length lP = length lpa ->
  exists lpa',
    @consistent_lP_lpa W pa2 lP lpa' /\
    length lP = length lpa' /\
    alt_Ip_list Ip lpa lP =
    alt_Ip_list Ip lpa' lP.
Proof.
  induction lP; intros W Ip lpa pa2 Hlength.
    exists nil. simpl. apply conj.
      apply consistent_lP_lpa_nil_l.
      apply conj. reflexivity.

      apply alt_Ip_list_nil.

    destruct lpa. discriminate.
    simpl. destruct (IHlP W Ip lpa pa2) as [lpa' [Hcon [Hl Halt]]].
inversion Hlength. reflexivity.
    rewrite Halt.
    rename P into pa. rename a into P.
    exists (cons pa (change_ln lpa' (indicies_l2 lP P) pa)).
    simpl. apply conj.
      rewrite <- lem_a11 with (pa := pa).
      apply lem_a4. inversion Hlength. assumption.
      assumption.

      apply conj.
pose proof length_change_ln. 
        rewrite length_change_ln. rewrite Hl. reflexivity.

      apply lem_a1.
Qed.

Lemma lem_a15_pre_pre_pre_pre_pre_stronger : forall l P Q R W lpa2 pa pa0 pa1 pa2 n,
  @ind_gen (W -> Prop) pa2 (indicies_l2 (cons P (cons Q l)) R) (cons pa0 (cons pa1 lpa2)) = repeat pa n ->
  @ind_gen _ pa2 (indicies_l2 (cons Q (cons P l)) R) (cons pa1 (cons pa0 lpa2)) = repeat pa n.
Proof.
  unfold indicies_l2.
  intros l P Q R W lpa2 pa pa0 pa1 pa2 n  H.
    simpl in *. destruct (predicate_dec R Q);
    destruct (predicate_dec R P); subst; simpl in *;
        do 2 rewrite ind_gen_pre_cons;
        do 2 rewrite ind_gen_pre_cons in H;
        destruct n; try discriminate; auto.
    destruct n. discriminate.
    inversion H as [[H1 H2]]. rewrite H0. reflexivity.
Qed.

Lemma lem_a15_pre_pre_pre_pre_pre_stronger_rev : forall l P Q R W lpa2 pa pa0 pa1 pa2 n,
  @ind_gen _ pa2 (indicies_l2 (cons Q (cons P l)) R) (cons pa1 (cons pa0 lpa2)) = repeat pa n ->
  @ind_gen (W -> Prop) pa2 (indicies_l2 (cons P (cons Q l)) R) (cons pa0 (cons pa1 lpa2)) = repeat pa n.
Proof.
  unfold indicies_l2.
  intros l P Q R W lpa2 pa pa0 pa1 pa2 n  H.
    simpl in *. destruct (predicate_dec R Q);
      destruct (predicate_dec R P); subst; simpl in *;
        do 2 rewrite ind_gen_pre_cons;
        do 2 rewrite ind_gen_pre_cons in H;
        destruct n; try discriminate; auto.
    destruct n. discriminate.
    inversion H as [[H1 H2]]. rewrite H0. reflexivity.
Qed.

Lemma lem_a15_pre_pre_pre_pre_pre : forall l P Q R W lpa2 pa pa0 pa1 pa2 n,
  length l = length lpa2 ->
  @ind_gen (W -> Prop) pa2 (indicies_l2 (cons P (cons Q l)) R) (cons pa0 (cons pa1 lpa2)) = repeat pa n ->
  @ind_gen _ pa2 (indicies_l2 (cons Q (cons P l)) R) (cons pa1 (cons pa0 lpa2)) = repeat pa n.
Proof.
  unfold indicies_l2.
  intros l P Q R W lpa2 pa pa0 pa1 pa2 n Hlength H.
  simpl in *. destruct (predicate_dec R P);
      destruct (predicate_dec R Q); subst; simpl in *;
        do 2 rewrite ind_gen_pre_cons;
        do 2 rewrite ind_gen_pre_cons in H;
        destruct n; try discriminate; auto.
  destruct n. discriminate.
  inversion H as [[H1 H2]]. rewrite H0. reflexivity.
Qed.

Lemma consistent_lP_lpa_cons_cons_same : forall lP P W lpa pa1 pa2 pa3,
  @consistent_lP_lpa W pa3 (cons P (cons P lP)) (cons pa1 (cons pa2 lpa)) ->
  pa1 = pa2.
Proof.
  unfold consistent_lP_lpa.
  unfold consistent_lP_lpa_P.
  unfold is_constant. unfold indicies_l2.
  intros lP P W lpa pa1 pa2 pa3 H.
  specialize (H P). simpl in *. pred_dec_l_rep.
  destruct H as [pa4 [n H]].
  destruct n. discriminate. destruct n. discriminate.
  inversion H as [[H1 H2]]. reflexivity.
Qed.

Lemma alt_Ip_alt_list_alt_same : forall lP W Ip lpa pa pa2 P,
  @alt_Ip W (alt_Ip_list (alt_Ip Ip pa P) lpa lP) pa2 P =
  alt_Ip (alt_Ip_list Ip lpa lP) pa2 P.
Proof.
  induction lP; intros W Ip lpa pa pa2 P.
    do 2 rewrite alt_Ip_list_nil.
    rewrite alt_Ip_rem. auto.
  destruct lpa. simpl. rewrite alt_Ip_rem. auto.
  simpl. destruct (predicate_dec P a); subst.
  + rewrite IHlP. auto.
  + rewrite <- alt_Ip_switch; auto. rewrite IHlP.
    rewrite <- alt_Ip_switch; auto.
Qed.

Lemma consistent_lP_lpa_cons_cons_switch : forall lP P Q W lpa pa1 pa2 pa0,
  @consistent_lP_lpa W pa0 (cons P (cons Q lP)) (cons pa1 (cons pa2 lpa)) ->
  @consistent_lP_lpa W pa0 (cons Q (cons P lP)) (cons pa2 (cons pa1 lpa)).
Proof.
  unfold consistent_lP_lpa.
  unfold consistent_lP_lpa_P.
  unfold is_constant.
  intros lP P Q W lpa pa1 pa2 p0 H R.
  specialize (H R).
  destruct H as [pa3 [n H]].
  exists pa3. exists n.
  apply lem_a15_pre_pre_pre_pre_pre_stronger.
  assumption.
Qed.

Lemma alt_Ip__list_consistent_lP_lpa : forall lP P W Ip lpa pa pa2,
  @consistent_lP_lpa W pa2 (cons P lP) (cons pa lpa) ->
  alt_Ip (alt_Ip_list Ip lpa lP) pa P =
  alt_Ip_list (alt_Ip Ip pa P) lpa lP.
Proof.
  induction lP; intros P W Ip lpa pa pa2 Hcon .
    do 2 rewrite alt_Ip_list_nil. reflexivity.

    destruct lpa. simpl. reflexivity.
    simpl. destruct (predicate_dec P a); subst.
      apply consistent_lP_lpa_cons_cons_same in Hcon.
      subst. rewrite alt_Ip_rem.
      rewrite alt_Ip_alt_list_alt_same. auto. 

      specialize (IHlP P W Ip lpa pa pa2).
      rewrite <- IHlP. rewrite alt_Ip_switch; auto.

      apply consistent_lP_lpa_cons_cons_switch in Hcon.
      apply consistent_lP_lpa_cons_rem in Hcon. assumption.
Qed.

Lemma lem_a15_pre_pre_pre_pre : forall l2 Q P W lpa2 (pa pa1 pa2: W -> Prop) n,
  length l2 = length lpa2 ->
  @ind_gen _ pa2 (indicies_l2 (app l2 (cons Q nil)) P) (app lpa2 (cons pa1 nil)) = repeat pa n <->
  @ind_gen _ pa2 (indicies_l2 (cons Q l2) P) (cons pa1 lpa2) = repeat pa n.
Proof.
  induction l2; intros Q P W lpa2 pa pa1 pa2 n Hlength; simpl in *.
  destruct lpa2. simpl in *. apply iff_refl. discriminate.
  split; intros H.
  + destruct lpa2. discriminate. simpl in *.
    apply lem_a15_pre_pre_pre_pre_pre. inversion Hlength. reflexivity.
    unfold indicies_l2 in H. unfold indicies_l2.
    simpl in *.  destruct (predicate_dec P a). 
      simpl in *. rewrite ind_gen_pre_cons in H.
      unfold indicies_l2 in IHl2.
      destruct n. discriminate. inversion H as [[H1 H2]].
      apply  IHl2 in H2. simpl in H2.
      destruct (predicate_dec P Q).
        simpl in *. rewrite ind_gen_pre_cons. rewrite H2.
        reflexivity.

        rewrite ind_gen_pre_cons. rewrite H2. reflexivity.
          inversion Hlength. reflexivity.

      rewrite ind_gen_pre_cons in H. apply IHl2 in H.
      unfold indicies_l2 in H.
      simpl in H. destruct (predicate_dec P Q). simpl in *.
        rewrite ind_gen_pre_cons. assumption.

        rewrite ind_gen_pre_cons. assumption.
          inversion Hlength. reflexivity. 
  + simpl in *. destruct lpa2. discriminate. simpl in *.
    apply lem_a15_pre_pre_pre_pre_pre in H. 
      2 : (inversion Hlength; reflexivity).
    unfold indicies_l2 in H. unfold indicies_l2. simpl in *.
    destruct (predicate_dec P a). simpl in*.
    ++ simpl in *. rewrite ind_gen_pre_cons .
       unfold indicies_l2 in IHl2.
       destruct n. discriminate. inversion H as [[H1 H2]].
       destruct (predicate_dec P Q).
       simpl in *. rewrite ind_gen_pre_cons in H2.
       destruct n. discriminate. inversion H2 as [[H3 H4]].
       rewrite ind_gen_pre_cons in H4.
       specialize (IHl2 Q P W lpa2 pa pa1 pa2 (S n)).
       simpl in IHl2. subst. simpl in *.
       pred_dec_l_rep. simpl in *. apply IHl2 in H2.
       rewrite H2. auto. lia.

       rewrite ind_gen_pre_cons in H2.
       specialize (IHl2 Q P W lpa2 pa pa1 pa2 n).
       simpl in IHl2. subst. simpl in *.
       rewrite predicate_dec_r in IHl2; auto.
       apply IHl2 in H2.  rewrite H2.  auto. lia.

    ++ unfold indicies_l2. simpl. 
       destruct (predicate_dec P Q); subst.
       * simpl in *. rewrite ind_gen_pre_cons in H.
         destruct n. discriminate. inversion H as [[H1 H2]].
         simpl in *. subst.
         rewrite ind_gen_pre_cons. 
         rewrite ind_gen_pre_cons in H2.
         assert ( @ind_gen _ pa2 (indicies_l2 (l2 ++ Q :: nil) Q) (lpa2 ++ pa :: nil) = repeat pa (S n)) as Hass.
         apply IHl2. auto. simpl. unfold indicies_l2. simpl.
         pred_dec_l_rep. simpl in *. auto.
       * rewrite ind_gen_pre_cons. apply IHl2. auto.
         unfold indicies_l2. simpl. rewrite predicate_dec_r; auto.
         rewrite ind_gen_pre_cons in H. auto.
Qed.

Lemma lem_a15_pre_pre_pre : forall (lP1 lP2 : list predicate) a (W : Type) pa n
   (lpa1 lpa2 : list (W -> Prop))
  (pa2 pa1 : W -> Prop) (P : predicate),
length lP1 = length lpa1 ->
length lP2 = length lpa2 ->
@ind_gen _ pa2 (indicies_l2 ((a :: lP1) ++ lP2) P ) ((cons pa1 lpa1) ++ lpa2) = repeat pa n ->
@ind_gen _ pa2 (indicies_l2 (lP1 ++ a :: lP2) P ) (lpa1 ++ (cons pa1 lpa2)) = repeat pa n.
Proof.
   induction lP1; intros lP2 Q W pa n lpa1 lpa2 pa2 pa1 P Hl1 Hl2 H.
   + destruct lpa1. simpl in *. assumption. discriminate.
   + simpl in H. destruct lpa1. discriminate.
     apply (lem_a15_pre_pre_pre_pre_pre (app lP1 lP2)) in H.
     fold (app lpa1 lpa2) in H. simpl.
     unfold indicies_l2. unfold indicies_l2 in H.
     simpl in *.  destruct (predicate_dec P a).
     ++ simpl in *. destruct n. discriminate.
        inversion H as [[H1 H2]].
        simpl in *. destruct (predicate_dec P Q). 
        destruct n. discriminate. inversion H2.
        rewrite ind_gen_pre_cons in H4.
        rewrite ind_gen_pre_cons in H4.
        rewrite ind_gen_pre_cons. unfold indicies_l2 in IHlP1.
        rewrite IHlP1 with (pa := pa) (n := (S n)). reflexivity.
        all : try assumption. auto.
        simpl. subst. pred_dec_l_rep. simpl. rewrite ind_gen_pre_cons.
        rewrite H4. auto.
        
        unfold indicies_l2 in IHlP1.  rewrite ind_gen_pre_cons.
        rewrite IHlP1 with (pa := pa) (n := n). reflexivity.
        inversion Hl1. reflexivity.
        all : try assumption.

        do 2 rewrite ind_gen_pre_cons in H2.
        simpl. rewrite predicate_dec_r; auto.
        rewrite ind_gen_pre_cons. assumption.
     ++ destruct (predicate_dec P Q). simpl in *.
        rewrite ind_gen_pre_cons.
        do 2 rewrite ind_gen_pre_cons in H.
        apply IHlP1; try assumption.
        inversion Hl1. reflexivity.
        unfold indicies_l2.
        simpl in *. rewrite predicate_dec_l; auto. simpl.
        rewrite ind_gen_pre_cons. auto.
        
        do 2 rewrite ind_gen_pre_cons in H.
        rewrite ind_gen_pre_cons. apply IHlP1; auto.
        unfold indicies_l2. simpl. rewrite predicate_dec_r; auto.
        rewrite ind_gen_pre_cons. auto.
        
     ++ fold (app lpa1 lpa2). simpl in *.
      do 2 rewrite app_length. lia.
Qed.

Lemma lem_a15_pre_pre_pre_stronger : forall (lP1 lP2 : list predicate) a (W : Type) pa n
   (lpa1 lpa2 : list (W -> Prop))
  (pa2 pa1 : W -> Prop) (P : predicate),
length lP1 = length lpa1 ->
@ind_gen _ pa2 (indicies_l2 ((a :: lP1) ++ lP2) P ) ((cons pa1 lpa1) ++ lpa2) = repeat pa n ->
@ind_gen _ pa2 (indicies_l2 (lP1 ++ a :: lP2) P ) (lpa1 ++ (cons pa1 lpa2)) = repeat pa n.
Proof.
  induction lP1; intros lP2 Q W pa n lpa1 lpa2 pa2 pa1 P Hl1 H.
    destruct lpa1; auto. discriminate.
  simpl in H. destruct lpa1. discriminate.
  apply (lem_a15_pre_pre_pre_pre_pre_stronger (app lP1 lP2)) in H.
  fold (app lpa1 lpa2) in H.
  unfold indicies_l2. unfold indicies_l2 in H. simpl in *.
  destruct (predicate_dec P a); subst.
  + simpl in *. destruct n. discriminate.
    inversion H as [[H1 H2]].
    simpl in *.
    destruct (predicate_dec a Q); subst.
    ++ simpl in *.
       destruct n. discriminate. inversion H2.
       rewrite ind_gen_pre_cons in H3.
       rewrite ind_gen_pre_cons in H3.
       rewrite ind_gen_pre_cons. unfold indicies_l2 in IHlP1.
       rewrite IHlP1 with (pa := pa) (n := (S n)). reflexivity.
        all : try assumption.
        inversion Hl1. reflexivity.

        simpl. pred_dec_l_rep. simpl. rewrite ind_gen_pre_cons.
        rewrite H3. auto.
    ++ unfold indicies_l2 in IHlP1.  rewrite ind_gen_pre_cons.
       rewrite IHlP1 with (pa := pa) (n := n). reflexivity.
       inversion Hl1. reflexivity.
       
       do 2 rewrite ind_gen_pre_cons in H2.
       simpl. rewrite predicate_dec_r; auto.
       rewrite ind_gen_pre_cons. assumption.

  + rewrite ind_gen_pre_cons.
    apply IHlP1; try assumption.
    inversion Hl1. reflexivity.
    unfold indicies_l2. simpl.
    destruct (predicate_dec P Q); subst; simpl in *.
    ++ rewrite ind_gen_pre_cons.
       do 2 rewrite ind_gen_pre_cons in H.
       assumption.
    ++ rewrite ind_gen_pre_cons in H. assumption.
Qed.

Lemma lem_a15_pre_pre_pre' : forall (lP1 lP2 : list predicate) (W : Type) pa n
   (lpa1 lpa2 : list (W -> Prop))
  (pa2 : W -> Prop) (P : predicate),
length lP1 = length lpa1 ->
length lP2 = length lpa2 ->
   @ind_gen _ pa2 (indicies_l2_pre (lP1 ++ lP2) P 0) (lpa1 ++ lpa2) = repeat pa n ->
  @ind_gen _ pa2 (indicies_l2_pre (lP2 ++ lP1) P 0) (lpa2 ++ lpa1) = repeat pa n.
Proof.
  induction lP1; intros lP2 W pa n lpa1 lpa2 pa2 P Hl1 Hl2 H.
    simpl in *. rewrite List.app_nil_r. destruct lpa1. 2 : discriminate.
    rewrite List.app_nil_r. simpl in *. assumption.

    destruct lpa1. discriminate.
    apply lem_a15_pre_pre_pre. assumption. inversion Hl1. reflexivity.
    unfold indicies_l2.  simpl in *.
    destruct (predicate_dec P a).
      simpl in *. rewrite ind_gen_pre_cons in H. destruct n.
      discriminate. simpl in H.
      inversion H as [[H1 H2]].
      rewrite ind_gen_pre_cons.
      rewrite IHlP1 with (pa := pa) (n := n). reflexivity.  
        inversion Hl1. reflexivity. assumption.
      assumption.

      rewrite ind_gen_pre_cons.
      simpl in H.
      rewrite ind_gen_pre_cons in H.
      apply IHlP1; try assumption. 
      inversion Hl1. reflexivity.
Qed.


Lemma lem_a15_pre_pre : forall lP1 lP2 W lpa1 lpa2 (pa2 : W -> Prop) P,
length lP1 = length lpa1 ->
length lP2 = length lpa2 ->
is_constant (@ind_gen _ pa2 (indicies_l2 (app lP1 lP2) P) (app lpa1 lpa2)) ->
is_constant (@ind_gen _ pa2 (indicies_l2 (app lP2 lP1) P) (app lpa2  lpa1)).
Proof.
  unfold is_constant. unfold indicies_l2.
  intros until 0. intros H1 H2 H3.
  destruct H3 as [pa [n H3]].
  exists pa. exists n. apply lem_a15_pre_pre_pre';
  assumption.
Qed.

Lemma lem_a15_pre : forall lP1 lP2 W lpa1 lpa2 pa2 P,
  length lP1 = length lpa1 ->
  length lP2 = length lpa2 ->
  (@consistent_lP_lpa_P W pa2 (app lP1 lP2) (app lpa1 lpa2) P ->
  @consistent_lP_lpa_P _ pa2 (app lP2 lP1) (app lpa2 lpa1) P).
Proof.
  unfold consistent_lP_lpa_P.
  intros until 0. apply lem_a15_pre_pre.
Qed.

Lemma lem_a15 : forall lP1 lP2 W lpa1 lpa2 pa2,
  length lP1 = length lpa1 ->
  length lP2 = length lpa2 ->
  (@consistent_lP_lpa W pa2 (app lP1 lP2) (app lpa1 lpa2) ->
  @consistent_lP_lpa _ pa2 (app lP2 lP1) (app lpa2 lpa1)).
Proof.
  unfold consistent_lP_lpa.
  intros until 0. intros H1 H2 H P.
  apply lem_a15_pre; try assumption. apply H.
Qed.

Lemma lem_a16_pre_pre : forall lP1 lP2 (W : Set) lpa1 lpa2 (pa2 : W -> Prop) Q pa n,
  length lP1 = length lpa1 ->
   @ind_gen _ pa2 (indicies_l2 (lP1 ++ lP2) Q) (lpa1 ++ lpa2) = repeat pa n ->
exists m, @ind_gen _ pa2 (indicies_l2 lP1 Q) lpa1 = repeat pa m.
Proof.
  induction lP1; intros lP2 W lpa1 lpa2 pa2 Q pa n Hlength Hind.
    simpl in *. exists 0. reflexivity.

    unfold indicies_l2 in *. 
    destruct lpa1. discriminate. simpl in *.
    inversion Hlength as [Hl].
    destruct (predicate_dec Q a).
      simpl in *. rewrite ind_gen_pre_cons in *.
      destruct n. discriminate.
      simpl in Hind. inversion Hind as [[H1 H2]].
      destruct (IHlP1 lP2 W lpa1 lpa2 pa2 Q pa n Hl H2)
        as [m H].
      exists (S m). rewrite H. reflexivity.

      simpl in *. rewrite ind_gen_pre_cons in *.
      destruct (IHlP1 lP2 W lpa1 lpa2 pa2 (Q) pa n Hl Hind)
        as [m H].
      exists (m). rewrite H. reflexivity.
Qed.

Lemma lem_a16_pre : forall lP1 lP2 W lpa1 lpa2 pa2 Q,
  length lP1 = length lpa1 ->
  @consistent_lP_lpa_P W pa2 (app lP1 lP2) (app lpa1 lpa2) Q->
  @consistent_lP_lpa_P W pa2 lP1 lpa1 Q.
Proof.
  unfold consistent_lP_lpa_P.
  unfold is_constant.
  induction lP1; intros lP2 W lpa1 lpa2 pa2 Q Hlength H.
    simpl. apply is_constant_nil. apply pa2.

    destruct H as [pa [n H]]. unfold indicies_l2 in *.
    simpl in *. destruct (predicate_dec Q a).
      simpl in *. destruct lpa1. discriminate. simpl in *.
      rewrite ind_gen_pre_cons in *.
      destruct n.
      discriminate. simpl in H. inversion H as [[H1 H2]].
      inversion Hlength as [Hlength'].
      destruct (lem_a16_pre_pre lP1 lP2 W lpa1 lpa2 pa2 Q pa n Hlength' H2)
        as [m H3].
      exists pa. exists (S m). unfold indicies_l2 in H3. rewrite H3.
      reflexivity.

      destruct lpa1. discriminate. rewrite ind_gen_pre_cons.
      inversion Hlength.
      apply IHlP1 with (lP2 := lP2) (lpa2 := lpa2);
        try assumption.
      simpl in H. rewrite ind_gen_pre_cons in H.
      exists pa. exists n. assumption.
Qed.

Lemma lem_a16 : forall lP1 lP2 W lpa1 lpa2 pa2,
  length lP1 = length lpa1 ->
  @consistent_lP_lpa W pa2 (app lP1 lP2) (app lpa1 lpa2) ->
  @consistent_lP_lpa W pa2 lP1 lpa1.
Proof.
  unfold consistent_lP_lpa.
  intros until 0. intros H1 H2 P.
  specialize (H2 P). apply lem_a16_pre in H2;
  assumption.
Qed.

Lemma lem_a13 : forall lP W Ip pa lpa P,
  length lP = length lpa ->
  In P lP ->
  @alt_Ip_list W (alt_Ip Ip pa P) lpa lP =
  alt_Ip_list Ip lpa lP.
Proof.
  induction lP; intros W Ip pa lpa P Hlength Hin. contradiction.
  simpl in *.
  destruct lpa. discriminate.
  inversion Hlength as [Hl].
  destruct (predicate_dec a P).
  + subst.
    do 2 rewrite alt_Ip_list_cons. 
    destruct (in_dec predicate_dec P lP).
    ++ rewrite IHlP; auto.
    ++ rewrite alt_Ip__list_occ_f.
       rewrite alt_Ip_rem. auto. auto.
  + do 2 rewrite alt_Ip_list_cons. 
    rewrite IHlP; auto. firstorder.
Qed.

Lemma lem_a14_pre_pre_pre_pre : forall lP1 lP2 P W lpa1 lpa2 (pa0 pa2 : W -> Prop),
  length lP1 = length lpa1 ->
  ~@ind_gen _ pa0 (indicies_l2 (app lP1 (cons P lP2)) P) (app lpa1 (cons pa2 lpa2))
       = nil.
Proof.
  induction lP1; intros lP2 P W lpa1 lpa2 pa0 pa Hl H.
  + destruct lpa1. unfold indicies_l2 in *. simpl in *.
    pred_dec_l_rep. all : discriminate.
  + simpl in *. unfold indicies_l2 in *. simpl in *.
    destruct (predicate_dec P a);
    destruct lpa1; try discriminate.
    simpl in H. rewrite ind_gen_pre_cons in H.
    apply IHlP1 in H; auto.
Qed.

Lemma lem_a14_pre_pre_pre_rev: forall (lP1 lP2 : list predicate) n (P Q : predicate)
   (W : Set) (lpa1 lpa2 : list (W -> Prop)) (pa pa1 pa2 : W -> Prop),
length lP1 = length lpa1 ->
(@ind_gen _ pa2 (indicies_l2 (lP1 ++ P :: lP2) Q) (lpa1 ++ pa :: lpa2)) = repeat pa1 n ->
(@ind_gen _ pa2 (indicies_l2 (P :: (lP1 ++ lP2)%list) Q) 
    (pa :: (lpa1 ++ lpa2)%list)) = repeat pa1 n.
Proof.
   induction lP1; intros lP2 n P Q W lpa1 lpa2 pa pa1 pa2 Hl H.
     destruct lpa1. simpl in *. assumption. discriminate.
  simpl in H. destruct lpa1. discriminate. 
  apply (lem_a15_pre_pre_pre_pre_pre_stronger_rev (app lP1 lP2)).
  fold (app lpa1 lpa2).  simpl in *.
  unfold indicies_l2 in *. simpl in *.
  destruct (predicate_dec Q a).
  + simpl in *. destruct n. discriminate.
    destruct (predicate_dec Q P).
    ++ simpl in *. rewrite ind_gen_pre_cons in H.
       do 2 rewrite ind_gen_pre_cons.
       inversion H.  rewrite H2. apply IHlP1 in H2.
       subst. pred_dec_l_rep. simpl in *. destruct n. discriminate.
       simpl in H2. inversion H2. subst. rewrite ind_gen_pre_cons in H3.
       rewrite H3. auto. auto.
    ++ simpl in *. subst. rewrite ind_gen_pre_cons in H.
       inversion H. subst. rewrite H2. do 2 rewrite ind_gen_pre_cons.
       apply IHlP1 in H2. rewrite predicate_dec_r in H2; auto.
       rewrite ind_gen_pre_cons in H2. rewrite H2. auto. auto.
  + rewrite ind_gen_pre_cons in H. destruct (predicate_dec Q P).
    simpl in *. do 2 rewrite ind_gen_pre_cons. destruct n.
    ++ apply IHlP1 in H. subst. pred_dec_l_rep.
       simpl in *. discriminate. auto.
    ++ subst. apply IHlP1 in H. pred_dec_l_rep.
       simpl in *. rewrite ind_gen_pre_cons in H. auto.
       auto.
    ++ do 2 rewrite ind_gen_pre_cons.
       apply IHlP1 in H; auto. rewrite predicate_dec_r in H.
       rewrite ind_gen_pre_cons in H. auto. auto.
Qed.

Lemma lem_a14_pre_pre : forall (lP1 lP2 : list predicate) (P Q : predicate) (W : Set)
  (lpa1 lpa2 : list (W -> Prop)) (pa pa2 : W -> Prop),
length lP1 = length lpa1 ->
is_constant (@ind_gen _ pa2 (indicies_l2 (P :: (lP1 ++ lP2)%list) Q) (pa :: (lpa1 ++ lpa2)%list)) <->
is_constant (@ind_gen _ pa2 (indicies_l2 (lP1 ++ P :: lP2) Q) (lpa1 ++ pa :: lpa2)).
Proof.
  unfold is_constant. intros until 0. intros Hlength.
  split; intros [pa1 [n H]]; exists pa1; exists n.
    apply lem_a15_pre_pre_pre_stronger; assumption.

    apply lem_a14_pre_pre_pre_rev; assumption.
Qed.

Lemma lem_a14_pre: forall lP1 lP2 P Q W lpa1 lpa2 pa pa2,
  length lP1 = length lpa1 ->
  (@consistent_lP_lpa_P W pa2 (cons P (app lP1 lP2)) (cons pa (app lpa1 lpa2)) Q <->
  @consistent_lP_lpa_P _ pa2 (app lP1 (cons P lP2)) (app lpa1 (cons pa lpa2)) Q).
Proof.
  unfold consistent_lP_lpa_P.
  apply lem_a14_pre_pre.
Qed.

 Lemma lem_a14  : forall lP1 lP2 P W lpa1 lpa2 pa pa2,
  length lP1 = length lpa1 ->
  (@consistent_lP_lpa W pa2 (cons P (app lP1 lP2)) (cons pa (app lpa1 lpa2)) <->
  @consistent_lP_lpa _ pa2 (app lP1 (cons P lP2)) (app lpa1 (cons pa lpa2))).
Proof.
  unfold consistent_lP_lpa.
  intros. split; intros HH Q;
    (apply lem_a14_pre; [ assumption| apply HH]).
Qed.

Lemma lemma_try7_again : forall lP atm W Ip Iv Ir pa_l x pa2 lP0 pa_l0,
  AT atm = true ->
  incl lP (preds_in atm)->
  ex_FOvar_var_ll x (FOv_att_P_l atm lP) = false ->
  SOturnst W Iv (alt_Ip_list Ip pa_l0 lP0) Ir atm ->
  incl lP lP0 ->
  @consistent_lP_lpa _ pa2 (app lP lP0) (app pa_l pa_l0) ->
  length lP0 = length pa_l0 ->
  length lP = length pa_l ->
  @consistent_lP_lpa _ pa2 lP pa_l ->
Ip_extends_l W
  (alt_Ip_list Ip
     (vsS_pa_l Iv (FOv_att_P_l atm lP) (list_var (length lP) x)) lP)
  (alt_Ip_list Ip pa_l lP) lP.
Proof.
  induction lP; intros atm W Ip Iv Ir lpa x pa2 lP0 lpa0 Hat Hin Hex
                       SOt Hin4 Hcon4 Hlength4 Hlength Hcon.
    simpl in *. rewrite alt_Ip_list_nil. apply Ip_extends_l_refl.
  destruct lpa. discriminate. simpl in *.
  unfold Ip_extends_l. rename P into pa. rename a into P.
  if_then_else_hyp_dep.
  assert (@consistent_lP_lpa _ pa2 lP lpa) as Hcon2.
    apply consistent_lP_lpa_cons_rem in Hcon. assumption.
  intros Q. apply conj; intros Hpocc.
  ++ intros w Halt. simpl in Hpocc.
     destruct (predicate_dec P Q); subst.
     * rewrite alt_Ip_eq in *.
       apply lemma17' with (Ip := (alt_Ip_list Ip lpa0 lP0))
                           (Ir := Ir) (pa := pa) in Halt; auto.
       inversion Hlength.
       apply incl_hd in Hin. firstorder.
       rewrite alt_Ip__list_consistent_lP_lpa with (pa2 := pa2).
       rewrite lem_a13; auto. 
       apply lem_a14 in Hcon4.
       apply lem_a15 in Hcon4.
       apply lem_a16 in Hcon4. all : simpl; auto.
     * inversion Hlength as [Hlength'].
       pose proof (consistent_lP_lpa_cons_rem _ _ _ _ _ _ Hcon4) as Hcon5.
       pose proof (incl_hd _ _ _ _ Hin4) as Hin4'.
       apply incl_lcons in Hin4.
       pose proof (incl_hd _ _ _ _ Hin) as Hin'.
       apply incl_lcons in Hin.
       specialize (IHlP _ _ _ _ _ _ x pa2 lP0 lpa0 Hat Hin Hex SOt Hin4
                        Hcon5 Hlength4 Hlength' Hcon2 Q).
        destruct IHlP as [IH1 IH2]. destruct Hpocc as [?|Hpocc]. contradiction.
        specialize (IH1 Hpocc w). rewrite alt_Ip_neq in *.
        specialize (IH1 Halt); auto. auto. auto.
  ++ simpl in Hpocc. apply not_or_and in Hpocc. destruct Hpocc as [Hp1 Hp2].
     inversion Hlength as [Hlength'].
     pose proof (consistent_lP_lpa_cons_rem _ _ _ _ _ _ Hcon4) as Hcon5.
       pose proof (incl_hd _ _ _ _ Hin4) as Hin4'.
       apply incl_lcons in Hin4.
       pose proof (incl_hd _ _ _ _ Hin) as Hin'.
       apply incl_lcons in Hin.
     specialize (IHlP _ _ _ _ _ _ x pa2 lP0 lpa0 Hat Hin Hex SOt Hin4
                      Hcon5 Hlength4 Hlength' Hcon2 Q).
     destruct IHlP as [IH1 IH2]. do 2 (rewrite alt_Ip_neq; auto).
Qed.

Lemma is_repeatist_var : forall (lP : list predicate) (P : predicate) (x : FOvariable),
exists m, (ind_FOv (indicies_l2_pre lP P 0) (list_var (length lP) x)) = repeat x m.
Proof.
  induction lP; intros P x. exists 0. reflexivity.
  simpl. destruct (predicate_dec P a); try subst a; simpl;
  destruct (IHlP P x) as [m Hm]; [exists (S m) | exists m];
  simpl; rewrite ind_FOv_ind_l2_pre_cons; auto; rewrite Hm; auto.
Qed.

Lemma consistent_lP_lx_P_list_var : forall lP P x,
  consistent_lP_lx_P lP (list_var (length lP) x) P.
Proof.
  unfold consistent_lP_lx_P. unfold indicies_l2.
  unfold is_constant. intros lP P x.
  destruct (is_repeatist_var lP P x) as [m H].
  exists x. exists m. assumption.
Qed.

Lemma consistent_lP_lx_list_var : forall lP x,
  consistent_lP_lx lP (list_var (length lP) x).
Proof.
  unfold consistent_lP_lx.
  intros. apply consistent_lP_lx_P_list_var.
Qed.

Lemma AT_passing_predSO_ll : forall lP llx,
  ~ lP = nil ->
  ~ llx = nil ->
  ex_nil_in_llv llx = false ->
  AT (passing_conj (passing_predSO_ll lP llx)) = true.
Proof.
  induction lP; intros llx H1 H2 Hex.
    contradiction (H1 eq_refl).

    simpl. case_eq llx. intros Hllx. rewrite Hllx in *.
      contradiction (H2 eq_refl).
    intros lx llx' Hllx.
    simpl.
    case_eq (passing_predSO_ll lP llx').
      intros Hp. rewrite <- lem4. apply AT_passing_conj_atm.
      rewrite Hllx in Hex. destruct lx; discriminate.
    intros beta lbeta Hp. rewrite <- Hp.
    simpl. rewrite <- lem4. rewrite AT_passing_conj_atm.
    apply IHlP.
    destruct lP. discriminate. discriminate.
    destruct llx'. destruct lP; discriminate. discriminate.
    rewrite Hllx in Hex. destruct lx. discriminate. simpl in Hex.
    assumption.
    rewrite Hllx in Hex. destruct lx; discriminate.
Qed.

Lemma lP_is_pos_SO_uni : forall lP beta,
  uniform_pos_SO beta ->
  ~ lP = nil ->
  (forall P, In P lP -> (Pred_in_SO beta P )) ->
  lP_is_pos_SO beta lP.
Proof.
  induction lP; intros beta Hun Hnil Hpocc.
    simpl in *. contradiction (Hnil eq_refl).

    simpl. destruct lP. 
    apply Hun. apply Hpocc. firstorder.
    apply conj. apply Hun.
    apply Hpocc. firstorder. 

    apply IHlP; try assumption. discriminate.
    intros P Hin. apply Hpocc. simpl in *. 
    clear -Hin.  firstorder.
Qed.

Fixpoint cap_pred_lpa {W : Set} (lpa : list (W -> Prop)) l1 l2 :=
  match l1, lpa with
  | nil, _ => nil
  | _, nil => nil
  | cons P l1', cons pa lpa' => if in_predicate_dec P l2
                                then cons pa (cap_pred_lpa lpa' l1' l2)
          else cap_pred_lpa lpa' l1' l2
  end.

Lemma incl_cap_pred_refl : forall l1 l2,
  incl (cap_pred l1 l2) l1.
Proof.
  induction l1; intros l2. firstorder. 
  simpl. dest_in_pred_dec_blind.
  + apply incl_cons_cons. auto. 
  + apply incl_rcons. auto.
Qed.

Lemma ind_gen_nil : forall l W (pa0 : W -> Prop),
  @ind_gen _ pa0 l nil = repeat pa0 (length l).
Proof.
  induction l; intros W pa. reflexivity.
  simpl. rewrite IHl. simpl. destruct a. simpl.
  reflexivity. simpl. destruct a; reflexivity.
Qed.

Lemma length_cap_pred__lpa : forall lP l2 (W : Set) (lpa : list (W -> Prop)),
  length lP = length lpa ->
  length (cap_pred lP l2) = length (cap_pred_lpa lpa lP l2).
Proof.
  induction lP; intros l2 W lpa H. destruct lpa; auto.
  destruct lpa. discriminate. inversion H.
  simpl. dest_in_pred_dec_blind; simpl; auto. 
Qed.

Lemma ind_gen_ind_l2_cap_pred_app : forall l1 l2 P (W : Set) lpa ( pa pa0 : W -> Prop) n,
length l1 =  length lpa ->
@ind_gen _ pa0 (indicies_l2 l1 P) lpa = repeat pa n ->
exists (n' : nat),
@ind_gen _ pa0 (indicies_l2 (app (cap_pred l1 l2) l1) P) (app (cap_pred_lpa lpa l1 l2) lpa) =
  repeat pa n'.
Proof.
  induction l1; intros l2 P W lpa pa pa0 n Hl Hind. exists 0. auto.
  unfold indicies_l2 in *. 
  simpl in *. 
  dest_in_pred_dec_blind; simpl. 
  + destruct (predicate_dec P a); simpl in *; subst.
    ++ destruct lpa; simpl.
       * rewrite ind_gen_nil. simpl.
         exists (S(length (indicies_l2_pre
                           (cap_pred l1 l2 ++ a :: l1) a 1))).
         destruct n. discriminate. inversion Hind as [[H1 H2]].
         rewrite <- H1.  reflexivity.
       * simpl. rewrite in_predicate_dec_l; auto.
         simpl. rewrite ind_gen_pre_cons in *.
         destruct n. discriminate. unfold indicies_l2 in IHl1.
         inversion Hind as [[H1 H2]].
         inversion Hl as [Hl'].
         specialize (IHl1 l2 _ _ _ _ _ _ Hl' H2).
         destruct IHl1 as [n' IH].
         pose proof lem_a15_pre_pre_pre_stronger as Hlem.
         unfold indicies_l2 in Hlem.
         rewrite (Hlem (cap_pred l1 l2)
            l1 a W pa (S n')).
         exists (S (S n')). reflexivity.
         apply length_cap_pred__lpa. assumption.
         clear Hlem. simpl. pred_dec_l_rep. simpl. rewrite ind_gen_pre_cons.
         rewrite IH. auto.
    ++ destruct lpa. discriminate. simpl in *.
       rewrite ind_gen_pre_cons in Hind. 
       rewrite in_predicate_dec_l; auto. simpl. rewrite ind_gen_pre_cons. 
        inversion Hl as [Hl'].
        specialize (IHl1 l2 _ _ _ _ _ _ Hl' Hind).
        destruct IHl1 as [n' IH].
        pose proof lem_a15_pre_pre_pre_stronger as Hlem.
        unfold indicies_l2 in Hlem.
        rewrite (Hlem (cap_pred l1 l2)
            l1 a W pa (n')).
        exists ( n'). reflexivity.
        apply length_cap_pred__lpa. assumption.
        clear Hlem. simpl. rewrite predicate_dec_r; auto.
        rewrite ind_gen_pre_cons. rewrite IH. auto.
  + destruct lpa. discriminate. simpl in *.
    inversion Hl as [Hl']. destruct (predicate_dec P a).
    ++ rewrite in_predicate_dec_r; auto. simpl in *. destruct n. discriminate.
       inversion Hind as [[H1 H2]].
       rewrite ind_gen_pre_cons in H2.
       specialize (IHl1 l2 _ _ _ _ _ _ Hl' H2).
       destruct IHl1 as [n' IH].
       pose proof lem_a15_pre_pre_pre_stronger as Hlem.
       unfold indicies_l2 in Hlem.
       rewrite (Hlem (cap_pred l1 l2)
                     l1 a W pa (S n')).
       exists ((S n')). reflexivity.
       apply length_cap_pred__lpa. assumption.
       clear Hlem. simpl. rewrite predicate_dec_l; auto. simpl.
       rewrite ind_gen_pre_cons. rewrite IH. auto.
    ++ rewrite ind_gen_pre_cons in Hind.
       rewrite in_predicate_dec_r; auto.
       specialize (IHl1 l2 _ _ _ _ _ _ Hl' Hind).
       destruct IHl1 as [n' IH].
       pose proof lem_a15_pre_pre_pre_stronger as Hlem.
        unfold indicies_l2 in Hlem.
        rewrite (Hlem (cap_pred l1 l2)
            l1 a W pa (n')).
        exists ( n'). reflexivity.
        apply length_cap_pred__lpa. assumption.
        clear Hlem. simpl.
        rewrite predicate_dec_r; auto. 
        simpl. rewrite ind_gen_pre_cons.
        rewrite IH. reflexivity.
Qed.

Lemma is_constant_ind_gen_cap_pred_lpa_app : forall l1 l2 P (W : Set) (lpa : list (W -> Prop))
    (pa2 : W -> Prop),
length l1 = length lpa ->
is_constant (@ind_gen _ pa2 (indicies_l2 l1 P) lpa) ->
is_constant
  (@ind_gen _ pa2 (indicies_l2 (cap_pred l1 l2 ++ l1) P) (@cap_pred_lpa W lpa l1 l2 ++ lpa)).
Proof.
  unfold is_constant. intros until 0. intros Hl [pa [n H]].
  apply ind_gen_ind_l2_cap_pred_app with (l2 := l2) in H.
  destruct H as [n' H]. exists pa. exists n'. assumption.
  assumption.
Qed.

Lemma consistent_lP_lpa_P_cap_pred_lpa_app : forall l1 l2 P W lpa pa2,
  length l1 = length lpa ->
  @consistent_lP_lpa_P W pa2 l1 lpa P ->
  @consistent_lP_lpa_P W pa2 (app (cap_pred l1 l2) l1)
      (app (cap_pred_lpa lpa l1 l2) lpa) P.
Proof.
  unfold consistent_lP_lpa_P.
  intros until 0. intros Hl H.
  apply is_constant_ind_gen_cap_pred_lpa_app; assumption.
Qed.

Lemma consistent_lP_lpa_cap_pred_lpa_app : forall l1 l2 W lpa pa2,
  length l1 = length lpa ->
  @consistent_lP_lpa W pa2 l1 lpa ->
  @consistent_lP_lpa W pa2 (app (cap_pred l1 l2) l1)
      (app (cap_pred_lpa lpa l1 l2) lpa).
Proof.
  unfold consistent_lP_lpa.
  intros until 0. intros Hl H P. apply consistent_lP_lpa_P_cap_pred_lpa_app.
  assumption.
  apply H.
Qed.

Lemma ind_gen_indicies_l2_cap_pred : forall (lP : list predicate) n (P : predicate) (l2 : list predicate) 
  (W : Set) (lpa : list (W -> Prop)) (pa2 : W -> Prop) pa,
length lP = length lpa ->
(@ind_gen _ pa2 (indicies_l2 lP P) lpa) = repeat pa n ->
(exists (n' : nat),
@ind_gen _ pa2 (indicies_l2 (cap_pred lP l2) P) (cap_pred_lpa lpa lP l2) =
  repeat pa n').
Proof.
  induction lP; intros n P l2 W lpa pa2 pa Hl Hind. exists 0. auto.
  simpl in *. unfold indicies_l2 in *. simpl in *.
  destruct lpa. discriminate.
  destruct (in_predicate_dec a l2);
    destruct (predicate_dec P a); simpl in *; subst; 
      pred_dec_l_rep; simpl in *.
  + simpl.  rewrite in_predicate_dec_l; auto. 
    rewrite ind_gen_pre_cons.
    rewrite ind_gen_pre_cons in Hind.
    destruct n. discriminate.
    inversion Hind as [[H1 H2]].
    inversion Hl as [Hl'].
    specialize (IHlP _ _ l2 _ _ _ _  Hl' H2).
    destruct IHlP as [n' IH].  rewrite IH.
    exists (S n'). reflexivity.
  + rewrite predicate_dec_r; auto.
    rewrite in_predicate_dec_l; auto.
    rewrite ind_gen_pre_cons in *.
    apply IHlP with (n := n); auto.
  + simpl. rewrite in_predicate_dec_r; auto.
    destruct n. discriminate.
    inversion Hind as [[H1 H2]]. rewrite ind_gen_pre_cons in H2.
    apply (IHlP) with (n := n); auto.
  + rewrite in_predicate_dec_r; auto.
    rewrite ind_gen_pre_cons in Hind.
    apply IHlP with (n := n); auto.
Qed.

Lemma is_constant_ind_gen_cap_pred : forall (lP : list predicate) (P : predicate) (l2 : list predicate) 
  (W : Set) (lpa : list (W -> Prop)) (pa2 : W -> Prop),
length lP = length lpa ->
is_constant (@ind_gen _ pa2 (indicies_l2 lP P) lpa) ->
is_constant (@ind_gen _ pa2 (indicies_l2 (cap_pred lP l2) P) (cap_pred_lpa lpa lP l2)).
Proof.
  unfold is_constant.
  intros until 0. intros Hl [pa [n H]].
  apply ind_gen_indicies_l2_cap_pred with (l2 := l2) in H.
  destruct H as [n' H].
  exists pa. exists n'. assumption.
  assumption.
Qed.

Lemma consistent_lP_lpa_P_cap_pred : forall lP P l2 W lpa pa2,
length lP = length lpa ->
@consistent_lP_lpa_P W pa2 lP lpa P ->
@consistent_lP_lpa_P W pa2 (cap_pred lP l2) (cap_pred_lpa lpa lP l2) P.
Proof.
  unfold consistent_lP_lpa_P.
  intros until 0. apply is_constant_ind_gen_cap_pred.
Qed.

Lemma consistent_lP_lpa_cap_pred : forall lP l2 W lpa pa2,
length lP = length lpa ->
@consistent_lP_lpa W pa2 lP lpa ->
@consistent_lP_lpa W pa2 (cap_pred lP l2) (cap_pred_lpa lpa lP l2).
Proof.
  unfold consistent_lP_lpa. intros until 0.
  intros Hl H P. specialize (H P).
  apply consistent_lP_lpa_P_cap_pred; assumption.
Qed.

Lemma lem_a19 : forall lP W Iv Ip Ir pa_l beta pa2,
  length lP = length pa_l ->
  @consistent_lP_lpa W pa2 lP pa_l ->
  SOturnst W Iv (alt_Ip_list Ip pa_l lP) Ir beta <->
  SOturnst W Iv (alt_Ip_list Ip (cap_pred_lpa pa_l lP (preds_in beta)) 
     (cap_pred lP (preds_in beta))) Ir beta.
Proof.
  induction lP; intros W Iv Ip Ir pa_l beta pa2 Hl Hcon.
    simpl in *. do 2 rewrite alt_Ip_list_nil.
    apply iff_refl.
  destruct pa_l. simpl. apply iff_refl.
  inversion Hl as [Hl'].
  pose proof Hcon as Hcon'.
  apply consistent_lP_lpa_cons_rem in Hcon.
  simpl. destruct (in_predicate_dec a (preds_in beta)).
  + simpl. rewrite alt_Ip__list_consistent_lP_lpa with (pa2:=pa2).
    rewrite alt_Ip__list_consistent_lP_lpa with (pa2:=pa2).
    apply IHlP with (pa2 := pa2); auto.
    pose proof (consistent_lP_lpa_cap_pred (cons a lP) (preds_in beta)  W (cons P pa_l) pa2) as H.
    simpl in H. do 2 rewrite in_predicate_dec_l in H; auto. auto.
  + split; intros SOt.
    ++ apply P_not_occ_alt in SOt; auto.
       apply (IHlP W Iv Ip Ir pa_l beta pa2); auto.
    ++ apply P_not_occ_alt; auto.
       apply (IHlP W Iv Ip Ir pa_l beta pa2); auto.
Qed.

Lemma lem_a26 : forall (lP : list predicate) (Q : predicate) (atm : SecOrder) 
  (W : Set) (Iv : FOvariable -> W) (x : FOvariable) (pa2 : W -> Prop),
exists (n : nat),
  @ind_gen (W -> Prop) pa2 (indicies_l2_pre lP Q 0)
    (vsS_pa_l Iv (FOv_att_P_l atm lP) (list_var (length lP) x)) = 
  repeat (pa_l_disj_gen Iv (FOv_att_P atm Q) x) n.
Proof.
  induction lP; intros Q atm W Iv x pa2. exists 0. auto.
  simpl. destruct (IHlP Q atm W Iv x pa2) as [n H].
  destruct (predicate_dec Q a). subst.
  + exists (S n). simpl. rewrite ind_gen_pre_cons.
    rewrite H. auto.
  + exists n. rewrite ind_gen_pre_cons. auto.
Qed.

Lemma lem_a25 : forall lP Q atm W Iv x pa2,
  @consistent_lP_lpa_P W pa2 lP 
    (vsS_pa_l Iv (FOv_att_P_l atm lP) 
      (list_var (length lP) x)) Q.
Proof.
  unfold consistent_lP_lpa_P. unfold is_constant.
  unfold indicies_l2.
  intros lP Q atm W Iv x pa2. exists (pa_l_disj_gen Iv (FOv_att_P atm Q) x).
  apply lem_a26.
Qed.

Lemma lem_a27 : forall lP atm W Iv x pa2,
  @consistent_lP_lpa W pa2 lP 
    (vsS_pa_l Iv (FOv_att_P_l atm lP) 
      (list_var (length lP) x)).
Proof.
  unfold consistent_lP_lpa. intros.
  apply lem_a25.
Qed.

Lemma lem_a31 : forall lP l Q (W : Set) Iv atm x (pa2 : W -> Prop),
exists (n : nat),
   @ind_gen _ pa2 (indicies_l2_pre (cap_pred lP l) Q 0)
     (vsS_pa_l Iv (FOv_att_P_l atm (cap_pred lP l))
        (list_var (length (cap_pred lP l)) x)) = 
   repeat (pa_l_disj_gen Iv (FOv_att_P atm Q) x) n.
Proof.
  induction lP; intros l Q W Iv atm x pa2. exists 0. auto.
  simpl. destruct (IHlP l Q W Iv atm x pa2) as [n H].
  destruct (in_predicate_dec a l); simpl;
  destruct (predicate_dec Q a); subst; auto.
  + simpl. rewrite ind_gen_pre_cons.
    exists (S n). rewrite H. auto.
  + exists n. rewrite ind_gen_pre_cons. auto.
Qed.

Lemma lem_a30 : forall lP l Q (W : Set) Iv atm x (pa2 : W -> Prop),
is_constant (@ind_gen _ pa2 (indicies_l2 (cap_pred lP l) Q)
  (vsS_pa_l Iv (FOv_att_P_l atm (cap_pred lP l)) 
  (list_var (length (cap_pred lP l)) x))).
Proof.
  unfold is_constant.
  unfold indicies_l2.
  intros. exists (pa_l_disj_gen Iv (FOv_att_P atm Q) x).
  apply lem_a31.
Qed.

Lemma lem_a29 : forall lP Q l atm (W : Set) Iv pa2 x ,
@consistent_lP_lpa_P W pa2 (cap_pred lP l)
 (vsS_pa_l Iv (FOv_att_P_l atm (cap_pred lP l))
        (list_var (length (cap_pred lP l)) x)) Q.
Proof.
  unfold consistent_lP_lpa_P.
  intros.
  apply lem_a30.
Qed.

Lemma lem_a28 : forall lP l atm (W : Set) Iv pa2 x ,
@consistent_lP_lpa W pa2 (cap_pred lP l)
 (vsS_pa_l Iv (FOv_att_P_l atm (cap_pred lP l))
        (list_var (length (cap_pred lP l)) x)).
Proof.
  unfold consistent_lP_lpa.
  intros. apply lem_a29.
Qed.

Lemma lem_a21 : forall lP atm beta x W Iv Ip Ir,
AT atm = true ->
SOturnst W Iv (alt_Ip_list Ip
   (vsS_pa_l Iv (FOv_att_P_l atm lP) (list_var (length lP) x)) lP) Ir beta ->
SOturnst W Iv
  (alt_Ip_list Ip
     (vsS_pa_l Iv (FOv_att_P_l atm (cap_pred lP (preds_in beta)))
        (list_var (length (cap_pred lP (preds_in beta))) x))
     (cap_pred lP (preds_in beta))) Ir beta.
Proof.
  induction lP; intros atm beta x W Iv Ip Ir Hat SOt. auto.
  simpl in *. destruct (in_predicate_dec a (preds_in beta)).
  + simpl.
    rewrite alt_Ip__list_consistent_lP_lpa with (pa2 := pa_t).
    rewrite alt_Ip__list_consistent_lP_lpa with (pa2 := pa_t) in SOt.
    apply IHlP; try assumption. 
    pose proof (lem_a27 (cons a lP)) as H. simpl in H.
    apply H.
    pose proof (lem_a28 (cons a lP) (preds_in beta) atm W Iv pa_t x) as H. simpl in H.
    rewrite in_predicate_dec_l in H; auto.
  + apply P_not_occ_alt in SOt. apply IHlP; auto. auto.
Qed.

Lemma lem_a23 : forall lP l2 atm x,
  ex_FOvar_var_ll x (FOv_att_P_l atm lP) = false ->
  ex_FOvar_var_ll x (FOv_att_P_l atm (cap_pred lP l2)) = false.
Proof.
  induction lP; intros l2 atm x Hex. auto.
  simpl in *. if_then_else_hyp_dep.
  destruct (in_predicate_dec a l2). simpl. 
  dest_in_dec_blind. contradiction.
  apply IHlP; auto. apply IHlP; auto.
Qed.

Lemma alt_Ip_list_cap_pred_nil :  forall lP beta W Iv Ip Ir lpa,
  cap_pred lP (preds_in beta) = nil ->
  (SOturnst W Iv (alt_Ip_list Ip lpa lP) Ir beta <->
  SOturnst W Iv Ip Ir beta).
Proof.
  induction lP; intros beta W Iv Ip Ir lpa H.
  + rewrite alt_Ip_list_nil. apply iff_refl.
  + destruct lpa. simpl. apply iff_refl.
    simpl in H. destruct (in_predicate_dec a (preds_in beta)).
      discriminate.
    simpl. split; intros SOt.
    ++ apply P_not_occ_alt in SOt.
       apply IHlP in SOt. all : try assumption.
    ++ apply P_not_occ_alt. auto.
       apply IHlP; auto. 
Qed.

Lemma length_nlist_list_pa : forall n W pa_l,
length (nlist_list_pa W n pa_l) = n.
Proof.
  induction n; intros W pa_l.
    rewrite (nlist_nil W pa_l). reflexivity.

    destruct (nlist_cons W n pa_l) as [pa [pa_l2 H2]].
    rewrite H2. simpl. rewrite IHn. reflexivity.
Qed.

Lemma lem_is_in : forall l beta,
incl
  (preds_in
     (replace_pred_l beta (list_rel_compl (preds_in beta) l)
        (nlist_list (length (list_rel_compl (preds_in beta) l))
           (nlist_var (length (list_rel_compl (preds_in beta) l)) (Var 1)))
        (nlist_list (length (list_rel_compl (preds_in beta) l))
           (nlist_empty (length (list_rel_compl (preds_in beta) l)))))) l.
Proof.
  intros l beta. intros P H.
  destruct (in_dec predicate_dec P l). auto.
 apply jj7 in H; auto. contradiction.
Qed. 

Lemma is_in_pred_passing_predSO_l : forall l Q,
  ~ l = nil ->
  In Q (preds_in (passing_conj (passing_predSO_l Q l))).
Proof.
  destruct l; intros Q Hnil. contradiction.
  simpl in *. destruct (passing_predSO_l Q l); firstorder.
Qed.

Lemma in_pred_passing_predSO_l2:
  forall (l : list FOvariable) (P Q : predicate),
  l <> nil -> In P (preds_in (passing_conj (passing_predSO_l Q l))) -> P = Q.
Proof.
  induction l; intros P Q H1 H2. contradiction.
  simpl in *. destruct l; firstorder. 
Qed.

Lemma lem_is_in5 : forall lP llx P,
  length lP = length llx ->
  ex_nil_in_llv llx = false ->
  In P (preds_in (passing_conj (passing_predSO_ll lP llx))) <->
  In P lP.
Proof.
  induction lP; intros llx P Hnil Hex. reflexivity.
  simpl. destruct llx. discriminate.
  simpl in *. destruct l. discriminate.
  assert (f :: l <> nil) as Hass. discriminate.
  remember (f :: l) as l'.
  destruct (predicate_dec P a). subst a.
  * split; intros H. firstorder. simpl. 
    destruct (passing_predSO_ll lP llx); [|simpl; apply in_or_app;left]; 
    apply is_in_pred_passing_predSO_l; auto.
  * case_eq (passing_predSO_ll lP llx).
    + intros Hp. simpl. split ;intros H. right. 
      apply lem_try35 in H; auto. contradiction.
       destruct H. subst. firstorder. 
       eapply IHlP in H; auto. rewrite Hp in H. all : auto.
       contradiction. 
    + intros beta lbeta Hlbeta.
      rewrite <- Hlbeta. simpl. rewrite Hlbeta. rewrite <- Hlbeta.
      simpl. split; intros H. apply in_app_or in H. right.
      destruct H. apply in_pred_passing_predSO_l2 in H. firstorder. auto.
      apply IHlP in H; auto.
      apply in_or_app. right. apply IHlP; auto.
      simpl in Hex.  destruct H. symmetry in H. firstorder.
      auto.
Qed.

Lemma lem_is_in4 : forall l lP llx,
  length lP = length llx ->
  ex_nil_in_llv llx = false ->
  incl l (preds_in (passing_conj (passing_predSO_ll lP llx))) <->
  incl l lP.
Proof.
  induction l; intros lP llx Hnil Hex. firstorder.
  split; intros H; apply incl_cons.
  apply incl_hd in H. apply lem_is_in5 in H; auto.
  apply incl_lcons in H. apply IHl in H; auto.
  apply incl_hd in H. apply lem_is_in5; auto.
  apply incl_lcons in H. apply IHl; auto.
Qed.

Lemma list_rel_compl_passing_predSO_ll : forall l lP llx,
length lP = length llx ->
ex_nil_in_llv llx = false ->
(list_rel_compl l (preds_in (passing_conj (passing_predSO_ll lP llx)))) =
(list_rel_compl l lP).
Proof.
  induction l; intros lP llx Hl Hex. simpl. reflexivity.
  simpl. destruct (in_predicate_dec a lP). eapply lem_is_in5 in i.
  rewrite (in_predicate_dec_l); auto. apply i.
  all : auto.
  dest_in_pred_dec_blind. apply lem_is_in5 in i; auto. contradiction.
  rewrite IHl; auto.
Qed.

Lemma lem_a32 : forall lP rel atm,
REL rel = true ->
AT atm = true ->
~ ex_att_allFO_llvar (conjSO rel atm) (FOv_att_P_l (conjSO rel atm) lP) .
Proof.
  induction lP; intros rel atm Hrel Hat H. inversion H.
  apply ex_att_allFO_llvar_conjSO in H; auto; intros H2.
  eapply ex_att_allFO_llvar_REL in H2; auto.
  eapply ex_att_allFO_llvar_AT in H2; auto.
Qed.

Lemma ex_att_exFO_lvar_REL : forall lv rel,
  REL rel = true ->
  ~ ex_att_exFO_lvar rel lv.
Proof.
  induction lv; intros rel Hrel H;
    inversion H; subst.
  apply att_exFO_var_REL in H2; auto.
  apply IHlv in H2; auto.
Qed.

Lemma ex_att_exFO_lvar_AT : forall lv rel,
  AT rel = true ->
  ~ ex_att_exFO_lvar rel lv.
Proof.
  induction lv; intros rel Hrel H;
    inversion H; subst.
  apply att_exFO_var_AT in H2; auto.
  apply IHlv in H2; auto.
Qed. 

Lemma lem_a33 : forall lP rel atm,
REL rel = true ->
AT atm = true ->
~ ex_att_exFO_llvar (conjSO rel atm) (FOv_att_P_l (conjSO rel atm) lP).
Proof.
  induction lP; intros rel atm Hrel Hat HH; inversion HH;
    subst. apply ex_att_exFO_lv_conjSO_f_rev in H1; auto.
  apply ex_att_exFO_lvar_REL. assumption.
  apply ex_att_exFO_lvar_AT. assumption.
  apply IHlP in H1; auto.
Qed.