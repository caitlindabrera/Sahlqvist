Require Export nlist_syn.
Require Export SO_semantics.


Lemma alt_Ip_list_cons : forall (D:Set) (Ip: predicate -> D -> Prop) (l_pa : list (D -> Prop)) 
                      (l_pred : list (predicate)) (P : predicate) (pa : D -> Prop),
            alt_Ip_list Ip (cons pa l_pa) (cons P l_pred) 
               = alt_Ip (alt_Ip_list Ip l_pa l_pred) pa P.
Proof. firstorder. Qed.

Lemma alt_Ip_list_nil : forall (D:Set) (Ip: predicate -> D -> Prop) (l_pa : list (D -> Prop)) ,
  alt_Ip_list Ip l_pa nil = Ip.
Proof. intros. destruct l_pa; firstorder. Qed.

Lemma alt_Ip_list_tail : forall (W : Set) (Ip : predicate -> W -> Prop) (P : predicate)
                            (l : list predicate) (pa_l : nlist_pa W (length l)) 
                            (pa: W -> Prop),
         alt_Ip_list (alt_Ip Ip pa P) (nlist_list_pa W (length l) pa_l) l
            = alt_Ip_list Ip (app (nlist_list_pa W (length l) pa_l) (cons pa nil) ) (app l (cons P nil)).
Proof.
  intros.
  induction l.
    simpl.
    simpl length in pa_l.
    assert (pa_l = niln_pa W).
      apply nlist_nil.
    rewrite H.
    simpl.
    reflexivity.

    assert (exists (pa1 : W -> Prop) (pa_l1 : nlist_pa W (length l)), 
              (pa_l = consn_pa W (length l) pa1 pa_l1)).
      apply nlist_cons.
    destruct H as [pa1 [pa_l1 H]].
    rewrite H.
    simpl.
    rewrite IHl.
    reflexivity.
Qed.

Lemma alt_Ip_list_app : forall (W : Set) (Ip : predicate -> W -> Prop) (P : predicate)
                            (l : list predicate) (pa_l : nlist_pa W (length l)) 
                            (pa : W -> Prop),
       (alt_Ip_list Ip (app (nlist_list_pa W (length l) pa_l) (cons pa nil)) (l ++ P :: nil))
     = (alt_Ip_list (alt_Ip_list Ip (nlist_list_pa W 1 (consn_pa W 0 pa (niln_pa W)))
          (P :: nil)) (nlist_list_pa W (length l) pa_l) l).
Proof.
  intros.
  induction l.
    simpl in pa_l.
    assert (pa_l = (niln_pa W)).
      apply nlist_nil.
    rewrite H.
    simpl.
    reflexivity.

    simpl.
    assert (exists (pa1 : W -> Prop) (pa_l1 : nlist_pa W (length l)), 
              (pa_l = consn_pa W (length l) pa1 pa_l1)).
       apply nlist_cons.
    destruct H as [pa1 [pa_l1 H]]. 
    rewrite H.
    specialize (IHl pa_l1).
    simpl.
    rewrite IHl.
    simpl.
    reflexivity.
Qed.

(* ----------------------------------------------------------------------------- *)

Lemma alt_alt_list_1 : forall (W : Set) (l : list predicate) (pa_l_hat : nlist_pa W (length l)) 
                            (pa_hat : W -> Prop) (P : predicate) (Ip : predicate -> W -> Prop) ,
      exists (pa : W -> Prop) (pa_l : nlist_pa W (length l)),
          (alt_Ip (alt_Ip_list Ip (nlist_list_pa W (length l) pa_l_hat) l) pa_hat P) 
        = (alt_Ip_list (alt_Ip Ip pa P) (nlist_list_pa W (length l) pa_l) l).
Proof.
  intros W l.
  induction l.
    intros.
    simpl.
    simpl in pa_l_hat.
    assert (pa_l_hat = niln_pa W).
      apply nlist_nil.
    rewrite H.
    simpl.
    exists pa_hat.
    exists (niln_pa W).
    simpl.
    reflexivity.

    intros.
    simpl in pa_l_hat.
    assert (exists (pa : W -> Prop) (pa_l' : nlist_pa W (length l)), 
              (pa_l_hat = consn_pa W (length l) pa pa_l')).
       apply nlist_cons.
    destruct H as [pa1 [pa_l1 H]].
    destruct a as [Qm]; destruct P as [Pn].
    case_eq (EqNat.beq_nat Qm Pn).
      intros.
      pose proof ((EqNat.beq_nat_true Qm Pn) H0).
      rewrite <- H1.
      rewrite H.
      simpl nlist_list_pa.
      rewrite alt_Ip_list_cons.
      rewrite alt_Ip_rem.
      specialize (IHl pa_l1 pa_hat (Pred Qm) Ip).
      destruct IHl as [pa2 [pa_l2 IHl']].

      exists pa2.
      exists (consn_pa W (length l) pa_hat pa_l2).
      simpl nlist_list_pa.
      rewrite alt_Ip_list_cons.
      rewrite <- IHl'.
      rewrite alt_Ip_rem.
      reflexivity.

      intros.
      pose proof ((EqNat.beq_nat_false Qm Pn) H0).
      rewrite H.
      simpl nlist_list_pa.
      rewrite alt_Ip_list_cons.
      rewrite <- alt_Ip_switch.
      specialize (IHl pa_l1 pa_hat (Pred Pn) Ip).
      destruct IHl as [pa2 [pa_l2 IHl']].
      rewrite IHl'.
      assert (S (length l) = length (cons (Pred Pn) l)).
        simpl; reflexivity.
      rewrite <- alt_Ip_list_cons.
      exists pa2.
      exists (consn_pa W (length l) pa1 pa_l2).
      reflexivity.

      intros HH. inversion HH. subst. firstorder.
Qed.

Lemma alt_alt_list_2 : forall (W : Set) (Ip : predicate -> W -> Prop) (P : predicate)
                            (l : list predicate) (pa_l_hat : nlist_pa W (length l)) 
                            (pa_hat : W -> Prop),
   exists (pa : W -> Prop) (pa_l : nlist_pa W (length l)),
     (alt_Ip (alt_Ip_list Ip (nlist_list_pa W (length l) pa_l) l) pa P) = 
        (alt_Ip_list (alt_Ip Ip pa_hat P) (nlist_list_pa W (length l) pa_l_hat) l).
Proof.
  intros.
  rewrite alt_Ip_list_tail.
  induction l.
    simpl length in *.
    assert (pa_l_hat = niln_pa W).
      apply nlist_nil.
    rewrite H.
    simpl.
    exists pa_hat.
    exists (niln_pa W).
    simpl.
    reflexivity.

    assert (exists (pa1 : W -> Prop) (pa_l1 : nlist_pa W (length l)), 
              (pa_l_hat = consn_pa W (length l) pa1 pa_l1)).
      apply nlist_cons.
    destruct H as [pa1 [pa_l1 H']].
    rewrite H'.
    simpl.
    destruct a as [Qm].
    destruct P as [Pn].
    rewrite alt_Ip_list_app.
    specialize (IHl pa_l1).
    destruct IHl as [pa2 [pa_l2 IHl']].
    case_eq (EqNat.beq_nat Qm Pn).
      intros.
      pose proof ((EqNat.beq_nat_true Qm Pn) H).
      rewrite <- H0.
      assert (nlist_list_pa W (length (cons (Pred Pn) nil))
                    (consn_pa W (length (nil: list predicate)) pa_hat (niln_pa W))
               = cons pa_hat (nlist_list_pa W (length (nil:list predicate)) (niln_pa W)))
              as list_cons.
        apply nlist_list_cons.
      simpl length in list_cons.
      rewrite list_cons.
      rewrite alt_Ip_list_cons.
      rewrite alt_Ip_list_app in IHl'.
      rewrite list_cons in IHl'.
      rewrite alt_Ip_list_cons in IHl'.
      rewrite alt_Ip_list_nil.
      rewrite alt_Ip_list_nil in IHl'.
      rewrite H0.
      rewrite <- IHl'.
      exists pa1. 
      exists (consn_pa W (length l) pa2 pa_l2).
      assert ((nlist_list_pa W (length (cons (Pred Pn) l)) (consn_pa W (length l) pa2 pa_l2))
                 =  cons pa2 (nlist_list_pa W (length l) pa_l2) ) as list_cons2.
        apply nlist_list_cons.
      simpl length in list_cons2.
      rewrite list_cons2.
      rewrite alt_Ip_list_cons.
      reflexivity.

      intros.
      exists pa2.
      exists (consn_pa W (length l) pa1 pa_l2).
      assert ((nlist_list_pa W (length (cons (Pred Pn) l)) (consn_pa W (length l) pa1 pa_l2))
               = cons pa1 (nlist_list_pa W (length l) pa_l2)) as list_cons.
        apply nlist_list_cons.  
      simpl length in list_cons.
      rewrite list_cons.
      rewrite alt_Ip_list_app in IHl'.
      simpl nlist_list_pa in IHl'.
      rewrite alt_Ip_list_cons in IHl'.
      simpl alt_Ip_list in IHl' at 3.
      rewrite alt_Ip_list_cons.
      assert ((nlist_list_pa W (length (cons (Pred Pn) nil)) 
              (consn_pa W (length (nil: list predicate)) pa_hat (niln_pa W)))
                 = cons pa_hat (nlist_list_pa W (length (nil:list predicate)) (niln_pa W)))
              as list_cons2.
        apply nlist_list_cons.
      simpl length in list_cons2.
      rewrite list_cons2.
      rewrite alt_Ip_list_cons.
      unfold nlist_list_pa at 2.
      unfold alt_Ip_list at 3.
      rewrite <- IHl'.
      apply alt_Ip_switch.
      pose proof ((EqNat.beq_nat_false Qm Pn) H).
      unfold not; intros.
      symmetry in H1.
      inversion H1. subst. firstorder.
Qed.

Lemma alt_Ip_list_tail' : forall (W : Set) (Ip : predicate -> W -> Prop) (P : predicate)
                            (l : list predicate) (pa_l : nlist (length l)) 
                            (pa: W -> Prop),
         alt_Ip_list (alt_Ip Ip pa P) (nlist_list (length l) pa_l) l
            = alt_Ip_list Ip (app (nlist_list (length l) pa_l) (cons pa nil) ) (app l (cons P nil)).
Proof.
  induction l; intros pa_l pa; simpl. 
  + assert (pa_l = niln).  apply nlist_nil2. subst. auto.
  + assert (exists (pa1 : W -> Prop) (pa_l1 : nlist (length l)), 
              (pa_l = consn (length l) pa1 pa_l1)).
    apply nlist_cons2.
    destruct H as [pa1 [pa_l1 H]]. subst.
    simpl. rewrite IHl. auto.
Qed.

Lemma alt_Ip_list_app' : forall (W : Set) (Ip : predicate -> W -> Prop) (P : predicate)
                            (l : list predicate) (pa_l : nlist (length l)) 
                            (pa : W -> Prop),
       (alt_Ip_list Ip (app (nlist_list (length l) pa_l) (cons pa nil)) (l ++ P :: nil))
     = (alt_Ip_list (alt_Ip_list Ip (nlist_list 1 (consn 0 pa (niln)))
          (P :: nil)) (nlist_list (length l) pa_l) l).
Proof.
  induction l; intros pa_l pa. simpl. 
  + assert (pa_l = (niln)).  apply nlist_nil2. subst. auto.
  + simpl. assert (exists (pa1 : W -> Prop) (pa_l1 : nlist (length l)), 
              (pa_l = consn (length l) pa1 pa_l1)).
       apply nlist_cons2.
    destruct H as [pa1 [pa_l1 H]]. 
    rewrite H. simpl. rewrite IHl. auto.
Qed.

Lemma nlist_list_cons' : forall (W : Set) (pa : W -> Prop) (l : list predicate) 
                               (t : nlist (length l)),
      (nlist_list (S (length l) ) (consn (length l) pa t)) 
         = cons pa (nlist_list (length l) t).
Proof. auto. Qed.

Lemma alt_alt_list_1' : forall (W : Set) (l : list predicate) (pa_l_hat : nlist (length l)) 
                            (pa_hat : W -> Prop) (P : predicate) (Ip : predicate -> W -> Prop) ,
      exists (pa : W -> Prop) (pa_l : nlist (length l)),
          (alt_Ip (alt_Ip_list Ip (nlist_list (length l) pa_l_hat) l) pa_hat P) 
        = (alt_Ip_list (@alt_Ip W Ip pa P) (nlist_list (length l) pa_l) l).
Proof.
  induction l; intros; simpl in *.
  + assert (pa_l_hat = niln) as H.
      apply nlist_nil2.
    rewrite H. simpl. exists pa_hat, niln. auto.
  + assert (exists (pa : W -> Prop) (pa_l' : nlist (length l)), 
              (pa_l_hat = consn (length l) pa pa_l')).
       apply nlist_cons2.
    destruct H as [pa1 [pa_l1 H]].
    destruct (predicate_dec a P); subst.
    ++ simpl. rewrite alt_Ip_rem. 
       specialize (IHl pa_l1 pa_hat P Ip).
       destruct IHl as [pa2 [pa_l2 IHl']].
       exists pa2, (consn (length l) pa_hat pa_l2).
       simpl. rewrite <- IHl'. rewrite alt_Ip_rem. auto.       
    ++ intros. simpl. rewrite <- alt_Ip_switch.
       specialize (IHl pa_l1 pa_hat P Ip).
       destruct IHl as [pa2 [pa_l2 IHl']].
       rewrite IHl'.
       assert (S (length l) = length (cons P l)) by auto.
       exists pa2, (consn (length l) pa1 pa_l2). all: auto.
Qed.

Lemma alt_alt_list_2' : forall (W : Set) (Ip : predicate -> W -> Prop) (P : predicate)
                            (l : list predicate) (pa_l_hat : nlist (length l)) 
                            (pa_hat : W -> Prop),
   exists (pa : W -> Prop) (pa_l : nlist (length l)),
     (alt_Ip (alt_Ip_list Ip (nlist_list (length l) pa_l) l) pa P) = 
        (alt_Ip_list (alt_Ip Ip pa_hat P) (nlist_list (length l) pa_l_hat) l).
Proof.
  intros. rewrite alt_Ip_list_tail'.
  induction l; simpl in *.
  + exists pa_hat, niln. simpl.
    assert (pa_l_hat = niln). apply nlist_nil2.
    subst. auto.
  + assert (exists (pa1 : W -> Prop) (pa_l1 : nlist (length l)), 
              (pa_l_hat = consn (length l) pa1 pa_l1)) as H.
      apply nlist_cons2.
    destruct H as [pa1 [pa_l1 H']]. subst.
    simpl. rewrite alt_Ip_list_app'.
    destruct (IHl pa_l1) as [pa2 [pa_l2 IHl']].
    destruct (predicate_dec a P); subst.
    ++ simpl. exists pa1, (consn (length l) pa2 pa_l2).
       simpl. rewrite IHl'. rewrite alt_Ip_list_tail'. auto.
    ++ exists pa2, (consn (length l) pa1 pa_l2).
       simpl. rewrite alt_Ip_switch. rewrite IHl'.
       rewrite alt_Ip_list_tail'. auto. auto.
Qed.

(* Checks whether Ip and Ip' agree on given predicate values in list l. *)
Inductive same_Ip_list {W : Set} (Ip Ip' : predicate -> W -> Prop) : list predicate -> Prop :=
| same_Ip_list_nil : same_Ip_list Ip Ip' nil
| same_Ip_list_cons l' P : Ip P = Ip' P -> same_Ip_list Ip Ip' l' ->
                           same_Ip_list Ip Ip' (P :: l').

Lemma same_cons : forall (W : Set) (Ip Ip' : predicate -> W -> Prop) (l : list predicate)
                          (P : predicate),
     ( same_Ip_list Ip Ip' (cons P l)) <-> (Ip P = Ip' P /\ (same_Ip_list Ip Ip' l)).
Proof.
  intros. split; intros HH. inversion HH. subst. firstorder.
  constructor; firstorder.
Qed.

Lemma same_comm : forall  (W : Set) (Ip Ip' : predicate -> W -> Prop) (l : list predicate),
    same_Ip_list Ip Ip' l <-> same_Ip_list Ip' Ip l.
Proof.
  induction l. split; intros; constructor.
  split; intros H; inversion H; subst;
    constructor; firstorder.
Qed.

Lemma same_app2 : forall (W : Set) (Ip Ip' : predicate -> W -> Prop) 
                         (l1 l2 : list predicate),
        same_Ip_list Ip Ip' (app l1 l2) <-> 
          (same_Ip_list Ip Ip' l1 /\ same_Ip_list Ip Ip' l2).
Proof.
  induction l1; intros l2; simpl.
  split; intros HH. split. constructor. 1-2:firstorder.
  split; intros HH. inversion HH; subst.
  split. constructor; firstorder.  apply IHl1 in H2; firstorder.
  destruct HH as [H1 H2]. inversion H1. subst.
  constructor; firstorder.
Qed.

(* Removes nth predicate from list l if it is in it. *)
Fixpoint list_pred_rem (l : list predicate) (P : predicate) : list predicate :=
  match l with
  | nil => nil
  | cons Q l' => if predicate_dec P Q then list_pred_rem l' P 
                                       else cons Q (list_pred_rem l' P)
  end.

(* List l1 without the elements of list l2. *)
Fixpoint list_pred_without (l1 l2 : list predicate) : list predicate :=
  match l2 with
  | nil => l1
  | cons P l2' => list_pred_without (list_pred_rem l1 P) l2'
  end.

Lemma list_pred_rem_switch : forall (l : list predicate) (P Q : predicate),
       (list_pred_rem (list_pred_rem l P) Q)
     = (list_pred_rem (list_pred_rem l Q) P).
Proof.
  induction l; intros P Q. auto.
  simpl. destruct (predicate_dec P a) as [H1 | H1];
  destruct (predicate_dec Q a) as [H2 | H2].
  apply IHl. simpl. subst. rewrite predicate_dec_refl.
  apply IHl. simpl. subst. rewrite predicate_dec_refl.
  apply IHl. simpl. rewrite predicate_dec_r.
  rewrite predicate_dec_r. rewrite IHl. all : auto.
Qed. 

Lemma list_pred_without_rem : forall (l2 l1 : list predicate) P,
         (list_pred_without (list_pred_rem l1 P) l2)
       = (list_pred_rem (list_pred_without l1 l2) P).
Proof.
  induction l2. auto.
  intros. simpl.
  rewrite list_pred_rem_switch.  auto.
Qed.

Lemma list_pred_without_id : forall (l : list predicate),
        list_pred_without l l = nil.
Proof.
  induction l. auto.
  simpl. rewrite predicate_dec_refl.
  rewrite list_pred_without_rem.
  rewrite IHl. auto.
Qed.

(* --------------------------------------------------------------------------*)

Lemma same_rem : forall (W:Set) (l : list predicate) 
                        (Ip Ip': predicate -> W -> Prop) (n : predicate) ,
      same_Ip_list Ip Ip' l -> same_Ip_list Ip Ip' (list_pred_rem l n).
Proof.
  induction l; intros ? ? P H; auto.
  simpl in *. destruct (predicate_dec P a) as [H1 | H1].
  subst. apply IHl. inversion H; auto.
  inversion H. subst. constructor; auto.
Qed.

Lemma same_alt_rem : forall (W:Set) (l : list predicate)
                            (Ip Ip': predicate -> W -> Prop) 
                            P (pred_asgmt : W -> Prop) ,
  same_Ip_list Ip Ip' (list_pred_rem l P) <-> 
    same_Ip_list (alt_Ip Ip pred_asgmt P) 
                   (alt_Ip Ip' pred_asgmt P) l.
Proof.
  intros W l. induction l; intros Ip Ip' n pa.
  simpl. split; intros HH; constructor.
  rewrite same_cons. simpl.
  destruct (predicate_dec n a). subst.
  do 2 rewrite alt_Ip_eq.
  split; intros HH. apply conj. auto. apply IHl. auto.
  eapply IHl. apply HH.
  rewrite same_cons. do 2 (rewrite alt_Ip_neq; auto).
  split; intros [H1 H2]; apply conj; auto.
  apply IHl. auto. apply IHl in H2. auto.
Qed.


(* A specific choice of pa_l that doesn't alter Ip, as proved below in Lemmas ineffective_Ip
   and ineffective_Ip - used later in proof of correctness_ST *)
Fixpoint ineffective_pa_l (W : Set) (Ip : predicate -> W -> Prop) (n : nat) 
                     (l : nlist n) : nlist_pa W n :=
  match l with 
  | niln => niln_pa W
  | consn m P l' => consn_pa W m (Ip P) (ineffective_pa_l W Ip m l')
  end.

Lemma  ineffective_Ip2 : forall (W : Set) (l : list predicate) (Ip : predicate -> W -> Prop) ,  
   alt_Ip_list Ip (nlist_list_pa W (length l) 
       (ineffective_pa_l W Ip (length l) (list_nlist l))) l
   = Ip.
Proof.
  intros W l.
  induction l.
    intros.
    simpl.
    reflexivity.

    intros.
    simpl.
    rewrite (IHl Ip).
    rewrite unalt_fun.
    reflexivity.
Qed.

