Require Import FunctionalExtensionality.
Require Import Arith.EqNat my_arith.

Fixpoint list_map {A : Type} (f : A -> A) (l : list A) : list A :=
  match l with
  | nil => nil
  | cons a l' => cons (f a) (list_map f l')
  end.

Lemma list_map_length : forall {A : Type} (f : A -> A) (l : list A),
  length (list_map f l) = length l.
Proof.
  intros.
  induction l; simpl; try rewrite IHl; reflexivity.
Qed.

Lemma list_map_app : forall {A : Type} (f : A -> A) (l1 l2 : list A),
  list_map f (app l1 l2) = app (list_map f l1) (list_map f l2).
Proof.
  intros.
  induction l1;
    simpl; try rewrite IHl1; reflexivity.
Qed.


Lemma list_map_comp : forall {A : Type} (f g : A -> A) (l : list A),
  list_map f (list_map g l) = list_map (fun n:A => f (g n)) l.
Proof.
  intros.
  induction l.
    simpl; reflexivity.

    simpl.
    rewrite IHl.
    reflexivity.
Qed.

Lemma fun_cancel : forall  (a b : nat),
  (fun n : nat => a + b + 1 - (b + n)) =
    (fun n : nat => a + 1 - n).
Proof.
  intros.
  apply functional_extensionality.
  intros n.
  rewrite arith_minus_exp.
  rewrite (PeanoNat.Nat.add_comm a).
  rewrite <- PeanoNat.Nat.add_assoc.
  rewrite (PeanoNat.Nat.add_comm b).
  rewrite PeanoNat.Nat.add_sub.
  reflexivity.
Qed.

Lemma list_map_nil : forall {A : Type} (f : A -> A) (l : list A),
  list_map f l = nil -> l = nil.
Proof.
  intros A f l H.
  induction l.
    reflexivity.

    simpl in *.
    discriminate.
Qed.
