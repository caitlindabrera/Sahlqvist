Require Import List Eqdep_dec PeanoNat Lia.
Require Import existsT.

Set Asymmetric Patterns. 

(* Definition of family of types of lists with n elements. *)
Inductive nlist_pa (W : Set) : nat -> Type :=
        | niln_pa : nlist_pa W 0
        | consn_pa : forall n:nat, (W -> Prop) -> nlist_pa W n -> nlist_pa W (S n).

Inductive nlist {A : Type} : nat -> Type :=
  | niln : nlist 0
  | consn : forall n:nat, A -> nlist n -> nlist (S n).


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
          end eq_refl eq_refl); intros pf; inversion pf.
  exists P. subst.
  exists n1. rewrite <- eq_rect_eq_dec. auto.
  apply Nat.eq_dec.
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
          end eq_refl eq_refl); intros; inversion pf.
  exists a. subst. exists n1.
  rewrite <- Eqdep_dec.eq_rect_eq_dec. auto.
  apply Nat.eq_dec.
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
          end eq_refl eq_refl); intros.
  subst pa_l.
  rewrite <- Eqdep_dec.eq_rect_eq_dec. auto.
  apply Nat.eq_dec. discriminate.
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
          end eq_refl eq_refl); intros.
  subst l. rewrite <- Eqdep_dec.eq_rect_eq_dec. auto.
  apply Nat.eq_dec.  inversion pf.
Qed.

Lemma nlist_list_cons : forall {A : Type} (W : Set) (pa : W -> Prop) (l : list A) 
                               (t : nlist_pa W (length l)),
      (nlist_list_pa W (S (length l) ) (consn_pa W (length l) pa t)) 
         = cons pa (nlist_list_pa W (length l) t).
Proof. auto. Qed.

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

(*
(* Checks whether Ip and Ip' agree on given predicate values in list l. *)
Fixpoint same_Ip_list (W : Set) (Ip Ip' : predicate -> W -> Prop) (l : list predicate) : Prop :=
  match l with
  | nil => True
  | cons P l' => Ip P = (Ip' P) /\ (same_Ip_list W Ip Ip' l')
  end.
*)


(* -----------------------------------------------------------------------*)


Lemma aa10' : forall {A B : Type}   (lx : list A) (ln : list B),
   (length lx) <= (length ln) ->
  exists ln1 ln2,
    length lx = length ln1 /\
    ln = app ln1 ln2.
Proof.
  intros A B; induction lx; intros ln Hleb.
  + simpl in *. exists nil. exists ln. firstorder.
  + simpl in *. destruct ln. simpl in *. lia. 
    simpl in *. apply le_S_n in Hleb.
    destruct (IHlx ln Hleb) as [ln1 [ln2 [H1 H2]]].
    exists (cons b ln1). exists ln2. simpl. subst.
    firstorder.
Qed.

Lemma aa11' : forall {A B : Type}  (ln : list B) (lx : list A),
  (exists ln1 ln2,
    length lx = length ln1 /\
    ln = app ln1 ln2) \/
  (exists lx1 lx2,
    length ln = length lx1 /\
    lx = app lx1 lx2).
Proof.
  intros A B ln lx. 
  destruct (Compare_dec.le_lt_dec (length lx) (length ln));
    [left | right]; apply aa10'; firstorder.
Qed.

Lemma in_ex_dec : forall {A : Type} 
(eq_dec : (forall x y : A, {x = y} + {x <> y})) (l : list A),
 (forall P, ~ In P l) + (existsT P, In P l).
Proof.
  destruct l. left. firstorder.
  right. exists a. firstorder.
Qed.

Lemma in_repeat_nocc  :forall {A : Type} n (P Q : A),
  ~ P = Q ->  ~ In Q (repeat P (S n)).
Proof. intros A n P Q H H1. apply repeat_spec in H1; auto. Qed.


