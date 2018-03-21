 Set Asymmetric Patterns. 
(* Set Implicit Arguments. *)

(* Require Import Modal.
Require Import SecOrder.  *)
Require Export ST_setup.
Require Export Correctness_ST_world_model.
Require Import Coq.Arith.Peano_dec my_arith.

(* Definition of family of types of lists with n elements. *)
Inductive nlist_pa (W : Set) : nat -> Type :=
        | niln_pa : nlist_pa W 0
        | consn_pa : forall n:nat, (W -> Prop) -> nlist_pa W n -> nlist_pa W (S n).

Inductive nlist {A : Type} : nat -> Type :=
  | niln : nlist 0
  | consn : forall n:nat, A -> nlist n -> nlist (S n).

(*
Inductive nlist_pred : nat -> Type :=
        | niln_pred : nlist_pred 0
        | consn_pred : forall n:nat, predicate -> nlist_pred n -> nlist_pred (S n).
*)

(* Converts nlist_pa to list. *)
Fixpoint nlist_list_pa (W:Set) (n : nat) (ln : nlist_pa W n) : list (W -> Prop) :=
  match ln with
    | niln_pa  => nil
    | consn_pa  m pa ln' => cons pa (nlist_list_pa _ _ ln')
  end.

Fixpoint list_nlist {A : Type} (l : list A) : nlist (length l) :=
  match l in list _ return nlist (length l) with
  | nil => niln 
  | cons P l' => consn _ P (list_nlist l')
  end.

Fixpoint nlist_list {A : Type} (n : nat) (ln : nlist n) : list A :=
  match ln with
  | niln => nil
  | consn m P l' => cons P (nlist_list _ l') 
  end.

(*
Fixpoint list_nlist_pred (l : list predicate) : nlist_pred (length l) :=
  match l in list _ return nlist_pred (length l) with
  | nil => niln_pred
  | cons P l' => consn_pred P (list_nlist_pred l')
  end.
*)
(*
Fixpoint nlist_list_pred (n : nat) (ln : nlist_pred n) : list predicate :=
  match ln with
  | niln_pred => nil
  | consn_pred m P l' => cons P (nlist_list_pred l')
  end.
*)

(* --------------------------------------------------------------------------- *)

(* Similar to altered_Ip but with list. *)
Fixpoint altered_Ip_list {D:Set} (Ip: predicate -> D -> Prop) (l_pa : list (D -> Prop)) 
                      (l_pred : list (predicate)) : predicate -> D -> Prop:=
  match l_pa, l_pred with
    nil, _ => Ip
  | _, nil => Ip
  | cons pa l_pa', cons P l_pred' =>  altered_Ip (altered_Ip_list Ip l_pa' l_pred') pa P
  end.


(* --------------------------------------------------------------------------- *)

(* Destructs an nlist with n>0 intros consn_pa. *)
Lemma nlist_cons : forall (W : Set) (n : nat) (pa_l : nlist_pa W (S n)), 
           exists (pa : W -> Prop) (pa_l' : nlist_pa W n), 
              (pa_l = consn_pa W n pa pa_l').
Proof.
  intros.
  refine (match pa_l as pa_l0 in nlist_pa _ m
            return forall pf: (m = (S n)), 
                   eq_rect m (nlist_pa W) pa_l0 (S n) pf = pa_l -> 
                   exists (pa : W -> Prop) (pa_l' : nlist_pa W n), 
                   pa_l = consn_pa W n pa pa_l'
            with
          | niln_pa => _
          | consn_pa _ _ _ => _
          end eq_refl eq_refl).
    intros.
    inversion pf.

    intros.
    inversion pf.
    exists P.
    subst pa_l.
    subst n.
    exists n1.
    rewrite <- Eqdep_dec.eq_rect_eq_dec.
      reflexivity.

      apply eq_nat_dec.
Qed.


(* Destructs an nlist with n>0 into consn. *)
Lemma nlist_cons2 : forall {A : Type} (n : nat) (l : nlist (S n)), 
           exists (P : A) (l' : nlist n), 
              (l = consn n P l').
Proof.
  intros.
  refine (match l as l0 in nlist m
            return forall pf: (m = (S n)), 
                   eq_rect m (nlist) l0 (S n) pf = l -> 
                   exists (P : A) (l' : nlist n), 
                   l = consn n P l'
            with
          | niln => _
          | consn _ _ _ => _
          end eq_refl eq_refl).
    intros.
    inversion pf.

    intros.
    inversion pf.
    exists a.
    subst l.
    subst n.
    exists n1.
    rewrite <- Eqdep_dec.eq_rect_eq_dec.
      reflexivity.

      apply eq_nat_dec.
Qed.



(* Destructs an nlist with n=0 into niln_pa. *)
Lemma nlist_nil : forall (W : Set) (pa_l : nlist_pa W 0), 
           (pa_l = niln_pa W).
Proof.
  intros.
  refine (match pa_l as pa_l0 in nlist_pa _ m
            return forall pf: (m = 0), 
                   eq_rect m (nlist_pa W) pa_l0 0 pf = pa_l ->  
                     pa_l = niln_pa W
            with
          | niln_pa  => _
          | consn_pa  _ _ _ => _
          end eq_refl eq_refl).
    intros.
    subst pa_l.
    rewrite <- Eqdep_dec.eq_rect_eq_dec.
      reflexivity.

      apply eq_nat_dec.

    intros.
    inversion pf.
Qed.

(* Destructs an nlist with n=0 into niln_pa. *)
Lemma nlist_nil2 : forall {A : Type} (l : nlist 0), 
           (l = @niln A).
Proof.
  intros.
  refine (match l as l0 in nlist m
            return forall pf: (m = 0), 
                   eq_rect m (nlist) l0 0 pf = l ->  
                     l = niln
            with
          | niln  => _
          | consn  _ _ _ => _
          end eq_refl eq_refl).
    intros.
    subst l.
    rewrite <- Eqdep_dec.eq_rect_eq_dec.
      reflexivity.

      apply eq_nat_dec.

    intros.
    inversion pf.
Qed.




Lemma nlist_list_cons : forall (W : Set) (pa : W -> Prop) (l : list predicate) 
                               (t : nlist_pa W (length l)),
      (nlist_list_pa W (S (length l) ) (consn_pa W (length l) pa t)) 
         = cons pa (nlist_list_pa W (length l) t).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma nlist_list_nlist : forall {A : Type} l ln,
  nlist_list (length l) ln = l ->
  ln = @list_nlist A l.
Proof.
  intros A l. induction l; intros ln H.
    simpl in *.
    apply (nlist_nil2 ln).

    simpl in *.
    destruct (nlist_cons2 _ ln) as [a' [ln' H2]].
    rewrite H2 in *.
    simpl in *.
    inversion H.
    rewrite IHl with (ln := ln').
      reflexivity.
      assumption.
Qed.

Lemma length_nlist_list : forall {A : Type} n (nl : @nlist A n),
  length (nlist_list _ nl) = n.
Proof.
  intros A. induction n; intros nl.
    rewrite (nlist_nil2 nl).
    reflexivity.

    destruct (nlist_cons2 _ nl) as [a [nl' Heq]].   
    rewrite Heq.
    simpl.
    rewrite IHn.
    reflexivity.
Qed.

Lemma nlist_list_ex : forall {A : Type} n (l : list A),
  length l = n ->
  exists (ln : nlist n),
  nlist_list _ ln = l.
Proof.
  intros A n. induction n; intros l H.
    exists niln.
    simpl. apply List.length_zero_iff_nil in H.
    symmetry. assumption.

    case_eq l.
      intros Hnil; rewrite Hnil in H.
      simpl in *; discriminate.

      intros a l' Heq.
      rewrite Heq in H.
      simpl in H.
      inversion H as [H2].
      destruct (IHn l' H2) as [ln Heq2].
      rewrite H.
      exists (consn _ a ln).
      simpl.
      rewrite Heq2.
      reflexivity.
Qed.

(* ---------------------------------------------------------------------------- *)

Lemma altered_Ip_eq : forall (W : Set) (Ip : predicate -> W -> Prop) (pa1 pa2 : W -> Prop)
                                 (P : predicate),
     altered_Ip (altered_Ip Ip pa2 P) pa1 P 
                    = altered_Ip Ip pa1 P.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  apply functional_extensionality.
  intros.
  destruct x.
  destruct P.
  simpl.
  case_eq (EqNat.beq_nat n0 n).
    intros.
    reflexivity.

    intros.
    reflexivity.
Qed.

Lemma altered_Ip_switch : forall (W : Set) (Ip : predicate -> W -> Prop) (pa1 pa2 : W -> Prop)
                                 (n m : nat),
     ~(n = m) -> (altered_Ip (altered_Ip Ip pa2 (Pred m)) pa1 (Pred n) 
                    = altered_Ip (altered_Ip Ip pa1 (Pred n)) pa2 (Pred m) ).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  apply functional_extensionality.
  intros.
  destruct x.
  simpl.
  case_eq (EqNat.beq_nat n n0).
    case_eq (EqNat.beq_nat m n0).
      intros.
      pose proof ((EqNat.beq_nat_true m n0) H0).
      pose proof ((EqNat.beq_nat_true n n0) H1).
      rewrite <- H2 in H3.
      contradiction.

      intros.
      reflexivity.

    intros.
    case_eq (EqNat.beq_nat m n0).
      intros.
      reflexivity.

      intros.
      reflexivity.
Qed.

(* ------------------------------------------------------------------ *)

Lemma altered_Ip_list_cons : forall (D:Set) (Ip: predicate -> D -> Prop) (l_pa : list (D -> Prop)) 
                      (l_pred : list (predicate)) (P : predicate) (pa : D -> Prop),
            altered_Ip_list Ip (cons pa l_pa) (cons P l_pred) 
               = altered_Ip (altered_Ip_list Ip l_pa l_pred) pa P.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma altered_Ip_list_nil : forall (D:Set) (Ip: predicate -> D -> Prop) (l_pa : list (D -> Prop)) ,
  altered_Ip_list Ip l_pa nil = Ip.
Proof.
  intros.  
  case l_pa.
    simpl.
    reflexivity.

    simpl.
    reflexivity.
Qed.

Lemma altered_Ip_list_tail : forall (W : Set) (Ip : predicate -> W -> Prop) (P : predicate)
                            (l : list predicate) (pa_l : nlist_pa W (length l)) 
                            (pa: W -> Prop),
         altered_Ip_list (altered_Ip Ip pa P) (nlist_list_pa W (length l) pa_l) l
            = altered_Ip_list Ip (app (nlist_list_pa W (length l) pa_l) (cons pa nil) ) (app l (cons P nil)).
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

Lemma altered_Ip_list_app : forall (W : Set) (Ip : predicate -> W -> Prop) (P : predicate)
                            (l : list predicate) (pa_l : nlist_pa W (length l)) 
                            (pa : W -> Prop),
       (altered_Ip_list Ip (app (nlist_list_pa W (length l) pa_l) (cons pa nil)) (l ++ P :: nil))
     = (altered_Ip_list (altered_Ip_list Ip (nlist_list_pa W 1 (consn_pa W 0 pa (niln_pa W)))
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
          (altered_Ip (altered_Ip_list Ip (nlist_list_pa W (length l) pa_l_hat) l) pa_hat P) 
        = (altered_Ip_list (altered_Ip Ip pa P) (nlist_list_pa W (length l) pa_l) l).
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
      rewrite altered_Ip_list_cons.
      rewrite altered_Ip_eq.
      specialize (IHl pa_l1 pa_hat (Pred Qm) Ip).
      destruct IHl as [pa2 [pa_l2 IHl']].

      exists pa2.
      exists (consn_pa W (length l) pa_hat pa_l2).
      simpl nlist_list_pa.
      rewrite altered_Ip_list_cons.
      rewrite <- IHl'.
      rewrite altered_Ip_eq.
      reflexivity.

      intros.
      pose proof ((EqNat.beq_nat_false Qm Pn) H0).
      rewrite H.
      simpl nlist_list_pa.
      rewrite altered_Ip_list_cons.
      rewrite <- altered_Ip_switch.
      specialize (IHl pa_l1 pa_hat (Pred Pn) Ip).
      destruct IHl as [pa2 [pa_l2 IHl']].
      rewrite IHl'.
      assert (S (length l) = length (cons (Pred Pn) l)).
        simpl; reflexivity.
      rewrite <- altered_Ip_list_cons.
      exists pa2.
      exists (consn_pa W (length l) pa1 pa_l2).
      reflexivity.

        exact H1.
Qed.

Lemma alt_alt_list_2 : forall (W : Set) (Ip : predicate -> W -> Prop) (P : predicate)
                            (l : list predicate) (pa_l_hat : nlist_pa W (length l)) 
                            (pa_hat : W -> Prop),
   exists (pa : W -> Prop) (pa_l : nlist_pa W (length l)),
     (altered_Ip (altered_Ip_list Ip (nlist_list_pa W (length l) pa_l) l) pa P) = 
        (altered_Ip_list (altered_Ip Ip pa_hat P) (nlist_list_pa W (length l) pa_l_hat) l).
Proof.
  intros.
  rewrite altered_Ip_list_tail.
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
    rewrite altered_Ip_list_app.
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
      rewrite altered_Ip_list_cons.
      rewrite altered_Ip_list_app in IHl'.
      rewrite list_cons in IHl'.
      rewrite altered_Ip_list_cons in IHl'.
      rewrite altered_Ip_list_nil.
      rewrite altered_Ip_list_nil in IHl'.
      rewrite H0.
      rewrite <- IHl'.
      exists pa1. 
      exists (consn_pa W (length l) pa2 pa_l2).
      assert ((nlist_list_pa W (length (cons (Pred Pn) l)) (consn_pa W (length l) pa2 pa_l2))
                 =  cons pa2 (nlist_list_pa W (length l) pa_l2) ) as list_cons2.
        apply nlist_list_cons.
      simpl length in list_cons2.
      rewrite list_cons2.
      rewrite altered_Ip_list_cons.
      reflexivity.

      intros.
      exists pa2.
      exists (consn_pa W (length l) pa1 pa_l2).
      assert ((nlist_list_pa W (length (cons (Pred Pn) l)) (consn_pa W (length l) pa1 pa_l2))
               = cons pa1 (nlist_list_pa W (length l) pa_l2)) as list_cons.
        apply nlist_list_cons.  
      simpl length in list_cons.
      rewrite list_cons.
      rewrite altered_Ip_list_app in IHl'.
      simpl nlist_list_pa in IHl'.
      rewrite altered_Ip_list_cons in IHl'.
      simpl altered_Ip_list in IHl' at 3.
      rewrite altered_Ip_list_cons.
      assert ((nlist_list_pa W (length (cons (Pred Pn) nil)) 
              (consn_pa W (length (nil: list predicate)) pa_hat (niln_pa W)))
                 = cons pa_hat (nlist_list_pa W (length (nil:list predicate)) (niln_pa W)))
              as list_cons2.
        apply nlist_list_cons.
      simpl length in list_cons2.
      rewrite list_cons2.
      rewrite altered_Ip_list_cons.
      unfold nlist_list_pa at 2.
      unfold altered_Ip_list at 3.
      rewrite <- IHl'.
      apply altered_Ip_switch.
      pose proof ((EqNat.beq_nat_false Qm Pn) H).
      unfold not; intros.
      symmetry in H1.
      contradiction.
Qed.

Lemma nlist_list_closed_SO : forall (W : Set) (Iv : FOvariable -> W) 
                           (Ir: W -> W -> Prop) (alpha: SecOrder) (l : list predicate) 
                           (Ip: predicate -> W -> Prop),
     SOturnst W Iv Ip Ir (list_closed_SO alpha l) <->
   forall pa_l : (nlist_pa W (length l)),
      SOturnst W Iv (altered_Ip_list Ip (nlist_list_pa W (length l) pa_l) l) Ir alpha.
Proof.
  intros W Iv Ir alpha l.
  induction l.
    simpl.
    split.
      intros H pa_l.
      rewrite altered_Ip_list_nil.
      exact H.

      intros H.
      specialize (H (niln_pa W)).
      rewrite altered_Ip_list_nil in H.
      exact H.

    intros.
    split.
      intros.
      assert (exists (pa1 : W -> Prop) (pa_l1 : nlist_pa W (length l)), 
              (pa_l = consn_pa W (length l) pa1 pa_l1)).
         apply nlist_cons.
      destruct H0 as [pa1 [pa_l1 H0]].
      rewrite H0.
      simpl nlist_list_pa.
      simpl altered_Ip_list.
      assert (exists (pa : W -> Prop) (pa_l : nlist_pa W (length l)),
            (altered_Ip (altered_Ip_list Ip (nlist_list_pa W (length l) pa_l1) l) pa1 a) = 
            (altered_Ip_list (altered_Ip Ip pa a) (nlist_list_pa W (length l) pa_l) l)).
        apply alt_alt_list_1.
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
      assert (exists (pred_asgmt1 : W -> Prop) (pa_l1 : nlist_pa W (length l)),
           (altered_Ip (altered_Ip_list Ip (nlist_list_pa W (length l) pa_l1) l)
              pred_asgmt1 a) = 
           (altered_Ip_list (altered_Ip Ip pred_asgmt a) 
              (nlist_list_pa W (length l) pa_l) l)).
         apply alt_alt_list_2.
       destruct H0 as [pred_asgmt1 [pa_l1 H0]].
       rewrite <- H0.
       specialize (H (consn_pa W (length l) pred_asgmt1 pa_l1)).
       apply H.
Qed.
(* ----------------------------------------------------------------------------------------*)

(* Checks whether Ip and Ip' agree on given predicate values in list l. *)
Fixpoint same_Ip_list (W : Set) (Ip Ip' : predicate -> W -> Prop) (l : list predicate) : Prop :=
  match l with
  | nil => True
  | cons P l' => Ip P = (Ip' P) /\ (same_Ip_list W Ip Ip' l')
  end.


Lemma same_cons : forall (W : Set) (Ip Ip' : predicate -> W -> Prop) (l : list predicate)
                          (P : predicate),
     ( same_Ip_list W Ip Ip' (cons P l)) = (Ip P = Ip' P /\ (same_Ip_list W Ip Ip' l)).
Proof.
  intros;  simpl; reflexivity.
Qed.

Lemma same_comm : forall  (W : Set) (Ip Ip' : predicate -> W -> Prop) (l : list predicate),
    same_Ip_list W Ip Ip' l <-> same_Ip_list W Ip' Ip l.
Proof.
  intros.
  induction l.
    simpl.
    intuition.

    simpl in *.
    split.
      intros.
      destruct H as [H1 H2].
      symmetry in H1.
      apply conj.
        exact H1.

        apply IHl.
        exact H2.

      intros.
      destruct H as [H1 H2].
      symmetry in H1.
      apply conj.
        exact H1.

        apply IHl.
        exact H2.
Qed.

Lemma same_app2 : forall (W : Set) (Ip Ip' : predicate -> W -> Prop) 
                         (l1 l2 : list predicate),
        same_Ip_list W Ip Ip' (app l1 l2) <-> 
          (same_Ip_list W Ip Ip' l1 /\ same_Ip_list W Ip Ip' l2).
Proof.
  intros.
  induction l1.
    simpl.
    apply True_conj.
    apply iff_refl.

    simpl.
    split.
      intros.
      destruct H as [pf_eq pf_app].
      apply conj.
        apply conj.
          apply pf_eq.

          assert (same_Ip_list W Ip Ip' (l1 ++ l2) -> 
                  same_Ip_list W Ip Ip' l1 /\ same_Ip_list W Ip Ip' l2).
            apply IHl1.
          pose proof (H pf_app).
          apply H0.

        assert (same_Ip_list W Ip Ip' (l1 ++ l2) -> 
                same_Ip_list W Ip Ip' l1 /\ same_Ip_list W Ip Ip' l2).
        apply IHl1.
        pose proof (H pf_app).
        apply H0.

      intros.
      apply conj.
        apply H.

        apply IHl1.
        apply conj.
          apply H.

          apply H.
Qed. 

(* -----------------------------------------------------------------------*)

(* Removes nth predicate from list l if it is in it. *)
Fixpoint list_rem (l : list predicate) (n : nat) : list predicate :=
  match l with
  | nil => nil
  | cons (Pred m) l' => if EqNat.beq_nat n m then list_rem l' n 
                                       else cons (Pred m) (list_rem l' n)
  end.

(* List l1 without the elements of list l2. *)
Fixpoint list_without (l1 l2 : list predicate) : list predicate :=
  match l2 with
  | nil => l1
  | cons (Pred n) l2' => list_without (list_rem l1 n) l2'
  end.

Lemma list_rem_switch : forall (l : list predicate) (n n2 : nat),
       (list_rem (list_rem l n) n2)
     = (list_rem (list_rem l n2) n).
Proof.
  induction l.
    intros.
    simpl.
    reflexivity.

    intros.
    destruct a as [m].
    case_eq (EqNat.beq_nat n m).
      intros.
      simpl list_rem.
      rewrite H.
      case_eq (EqNat.beq_nat n2 m).
        intros.
        apply IHl.

        intros. 
        simpl list_rem.
        rewrite H.
        apply IHl.

      intros.
      case_eq (EqNat.beq_nat n2 m).
        intros.
        simpl list_rem.
        rewrite H.
        simpl list_rem.
        rewrite H0.
        apply IHl.

        intros.
        simpl list_rem.
        rewrite H.
        simpl list_rem.
        rewrite H0.
        simpl list_rem.
        rewrite H.
        rewrite (IHl n n2).
        reflexivity.
Qed.

Lemma list_without_rem : forall (l2 l1 : list predicate) (n : nat),
         (list_without (list_rem l1 n) l2)
       = (list_rem (list_without l1 l2) n).
Proof.
  intros l2.
  induction l2.
    intros.
    simpl.
    reflexivity.

    intros.
    destruct a.
    simpl.
    rewrite <- IHl2.
    rewrite list_rem_switch.
    reflexivity.
Qed.

Lemma list_without_id : forall (l : list predicate),
        list_without l l = nil.
Proof.
  intros.
  induction l.
    simpl ; reflexivity.

    destruct a.
    simpl.
    rewrite <- EqNat.beq_nat_refl.
    rewrite list_without_rem.
    rewrite IHl.
    simpl.
    reflexivity.
Qed.

(* --------------------------------------------------------------------------*)

Lemma same_rem : forall (W:Set) (l : list predicate) 
                        (Ip Ip': predicate -> W -> Prop) (n : nat) ,
      same_Ip_list W Ip Ip' l -> same_Ip_list W Ip Ip' (list_rem l n).
Proof.
  intros.
  induction l.
    simpl.
    exact I.

    destruct a.
    case_eq (EqNat.beq_nat n n0).
      intros.
      simpl.
      rewrite H0.
      apply IHl.
      simpl in H.
      apply H.

      intros.
      simpl.
      rewrite H0.
      simpl.
      simpl in H.
      apply conj.
        apply H.

        apply IHl.
        apply H.
Qed.

Lemma same_altered_rem : forall (W:Set) (l : list predicate)
                            (Ip Ip': predicate -> W -> Prop) 
                            (n : nat) (pred_asgmt : W -> Prop) ,
  same_Ip_list W Ip Ip' (list_rem l n) <-> 
    same_Ip_list W (altered_Ip Ip pred_asgmt (Pred n)) 
                   (altered_Ip Ip' pred_asgmt (Pred n)) l.
Proof.
  intros W l.
  induction l.
    intros.
    simpl.
    apply iff_refl.

    intros.
    rewrite same_cons.
    split.
      intros.
      apply conj.
      destruct a.
      case_eq (EqNat.beq_nat n n0).
        intros.
        pose proof (EqNat.beq_nat_true n n0 H0).
        rewrite H1 in *.
        simpl altered_Ip.
        rewrite <- EqNat.beq_nat_refl.
        reflexivity.

        intros.
        pose proof (EqNat.beq_nat_false n n0 H0).
        unfold altered_Ip.
        rewrite H0.
        simpl in H.
        rewrite H0 in H.
        rewrite same_cons in H.
        apply H.

      apply IHl.
      destruct a.
      simpl in H.
      case_eq (EqNat.beq_nat n n0).
        intros.
        rewrite H0 in H.
        exact H.

        intros.
        rewrite H0 in H.
        rewrite same_cons in H.
        apply H.

    intros.
    destruct H as [pf_eq pf_alt].
    destruct a.
    simpl list_rem.
    case_eq (EqNat.beq_nat n n0).
      intros.
      apply IHl with (pred_asgmt := pred_asgmt).
      exact pf_alt.

      intros.
      rewrite same_cons.
      apply conj.
        simpl in pf_eq.
        rewrite H in pf_eq.
        exact pf_eq.

        apply IHl with (pred_asgmt := pred_asgmt).
        exact pf_alt.
Qed.

Lemma same_preds_in : forall (W:Set)(alpha : SecOrder) (Ip Ip': predicate -> W -> Prop)
                             (Ir: W -> W -> Prop) (Iv : FOvariable -> W),
    same_Ip_list W Ip Ip' (preds_in alpha) ->
     (SOturnst W Iv Ip Ir alpha -> SOturnst W Iv Ip' Ir alpha).
Proof.
  intros W alpha.
  induction alpha.
    intros.
    destruct p; destruct f.
    simpl in *.
    destruct H.
    rewrite <- H.
    exact H0.

    intros.
    destruct f; destruct f0.
    simpl in *.
    exact H0.

    intros. 
    destruct f; destruct f0.
    simpl in *.
    exact H0.

    intros.
    destruct f.
    simpl preds_in in *.
    rewrite SOturnst_allFO in *.
    intros d.
    apply IHalpha with (Ip := Ip).
      exact H.

      apply H0.

    intros.
    destruct f.
    simpl preds_in in *.
    rewrite SOturnst_exFO in *.
    destruct H0 as [d H0].
    exists d.
    apply IHalpha with (Ip := Ip).
      exact H.

      apply H0.

    intros.
    simpl in *.
    unfold not in *; intros.
    apply H0.
    apply IHalpha with (Ip := Ip').
      apply same_comm.
      exact H.

      exact H1.

    intros.
    rewrite SOturnst_conjSO in *.
    simpl preds_in in H.
    apply conj.
      apply IHalpha1 with (Ip := Ip).
        apply same_app2 with (l2 := (preds_in alpha2)).
        apply H.

        apply H0.

      apply IHalpha2 with (Ip := Ip).
        apply same_app2 with (l1 := (preds_in alpha1)).
        apply H.

        apply H0.

    intros.
    rewrite SOturnst_disjSO in *.
    simpl preds_in in H.
    destruct H0.
      left.
      apply IHalpha1 with (Ip := Ip).
        apply same_app2 with (l2 := (preds_in alpha2)).
        apply H.

        exact H0.

      right.
      apply IHalpha2 with (Ip := Ip).
        apply same_app2 with (l1 := (preds_in alpha1)).
        apply H.

        exact H0.

    intros.
    simpl in *.
    intros.
      apply IHalpha2 with (Ip := Ip).
        apply same_app2 with (l1 := (preds_in alpha1)).
        apply H.

        apply H0.
        apply IHalpha1 with (Ip := Ip').
          apply same_comm.
          apply same_app2 with (l2 := (preds_in alpha2)).
          exact H.

          exact H1.
(*
    intros.
    simpl in *.
    destruct p. 
(*    split.
*)      intros.
      apply IHalpha2 with (Ip := Ip).
        apply same_app2 with (l1 := (preds_in alpha1)).
        apply H.

        apply H0.
        apply IHalpha1 with (Ip := Ip').
          apply same_comm.
          apply same_app2 with (l2 := (preds_in alpha2)).
          apply H.

          exact H1.

      intros.
      apply IHalpha1 with (Ip := Ip).
        apply same_app2 with (l2 := (preds_in alpha2)).
        apply H.

        apply H0.
        apply IHalpha2 with (Ip := Ip').
          apply same_comm.
          apply same_app2 with (l1 := (preds_in alpha1)).
          apply H.

          exact H1.
*)
    intros.
    destruct p.
    simpl preds_in in H.
    rewrite same_cons in *. 
    rewrite SOturnst_allSO in *.
    intros.
    apply IHalpha with (Ip := (altered_Ip Ip pred_asgmt (Pred n))).
      apply same_altered_rem.
      apply same_rem.
      apply H.

      apply H0.

    intros.
    destruct p.
    rewrite SOturnst_exSO in *.
    destruct H0 as [pred_asgmt H0].
    exists pred_asgmt.
    simpl preds_in in H.
    rewrite same_cons in H.
    apply IHalpha with (Ip := (altered_Ip Ip pred_asgmt (Pred n))).
    apply same_altered_rem.
      apply same_rem.
      apply H.

      exact H0.

(*    intros.
    destruct p; destruct p0.
    simpl in *.
    rewrite <- H0 in H.
    destruct H.
    rewrite <- H.
    destruct H1.
    rewrite H1.
    reflexivity. *)
Qed.

Lemma same_preds_in_without : forall (W:Set) (l : list predicate)
                              (alpha : SecOrder) (Ip Ip': predicate -> W -> Prop)
                              (Ir: W -> W -> Prop) (Iv : FOvariable -> W),
    same_Ip_list W Ip Ip' (list_without (preds_in alpha) l) ->
     (SOturnst W Iv Ip Ir (list_closed_SO alpha l) -> 
         SOturnst W Iv Ip' Ir (list_closed_SO alpha l)).
Proof.
  intros W l.
  induction l.
    intros.
    simpl in *.
    apply same_preds_in with (Ip := Ip).
      exact H.

      exact H0.

    intros.
    destruct a.
    simpl list_closed_SO in *.
    simpl list_without in H.
    rewrite SOturnst_allSO in *.
    intros.
    specialize (H0 pred_asgmt).
    apply IHl with (Ip := (altered_Ip Ip pred_asgmt (Pred n))).
      apply same_altered_rem.
      rewrite <- list_without_rem.
      exact H.

      exact H0.
Qed.

(* For universally closed formulas, Ip doesn't matter. *)
Lemma Ip_uni_closed : forall (W:Set) (alpha : SecOrder) (Iv: FOvariable -> W)
                             (Ip Ip': predicate -> W -> Prop)
                             (Ir: W -> W -> Prop)  , 
     SOturnst W Iv Ip Ir (uni_closed_SO alpha) -> SOturnst W Iv Ip' Ir (uni_closed_SO alpha).
Proof.
  intros.
  unfold uni_closed_SO in *.
  apply same_preds_in_without with (Ip := Ip).
    rewrite list_without_id.
    simpl; exact I.

    exact H.
Qed.
