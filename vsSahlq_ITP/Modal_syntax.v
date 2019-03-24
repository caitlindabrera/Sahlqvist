Require Import PeanoNat.

Inductive propvar : Type :=
  pv : nat -> propvar.

Lemma propvar_dec : forall (p q : propvar), {p = q} + {p <> q}.
Proof.
  intros [p] [q]. destruct (Nat.eq_dec p q).
  subst. auto. right. intros H.
  inversion H. subst. auto.
Qed.  
  
Inductive Modal : Type :=
    atom : propvar -> Modal  
  | mneg : Modal -> Modal
  | mconj : Modal -> Modal -> Modal
  | mdisj : Modal -> Modal -> Modal
  | mimpl : Modal -> Modal -> Modal
  | box : Modal -> Modal
  | diam : Modal -> Modal.

Notation "# p" := (atom p) (at level 1) : modal_scope.
Notation "m~ ϕ" := (mneg ϕ) (at level 2) : modal_scope.
Notation "ϕ1 m∧ ϕ2" := (mconj ϕ1 ϕ2) (at level 15, right associativity) : modal_scope.
Notation "ϕ1 m∨ ϕ2" := (mdisj ϕ1 ϕ2) (at level 15, right associativity) : modal_scope.
Notation "ϕ1 m→ ϕ2" := (mimpl ϕ1 ϕ2) (at level 16, right associativity) : modal_scope.
Notation "'[.]' ϕ" := (box ϕ) (at level 2) : modal_scope.
Notation "'<.>' ϕ" := (diam ϕ) (at level 2) : modal_scope.

(* Given a conditional, return the antecedent. Don't care about other inputs. *)
Definition calc_ante_modal ϕ :=
  match ϕ with
  | mimpl ψ1 ψ2 => ψ1
  | _ => ϕ
  end.

(* Given a conditional, return the consequent. Don't care about other inputs. *)
Definition calc_cons_modal ϕ :=
  match ϕ with
  | mimpl ψ1 ψ2 => ψ2
  | _ => ϕ
  end.
