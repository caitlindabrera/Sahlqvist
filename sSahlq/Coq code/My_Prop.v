(* Lemma bi_refl : forall A:Prop, A <-> A.
Proof.
  intros A.
  unfold iff; apply conj; intros H; exact H.
Qed.

Lemma bi_contrapos : forall A B: Prop, (A <-> B) -> (~A <-> ~B).
Proof.
  intros A B; intros A_B.
  unfold iff; apply conj.
    intros not_A; intros pf_B.
    apply not_A.
    apply A_B; exact pf_B.

    intros not_B; intros pf_A.
    apply not_B.
    apply A_B; exact pf_A.
Qed.  *)

Lemma bi_conj : forall A B C D: Prop, ((A <-> C) /\ (B <-> D)) -> ((A /\ B) <-> (C /\ D)).
Proof.
  firstorder.
Qed.

Lemma bi_impl : forall A B C D: Prop, ((A <-> C) /\ (B <-> D)) -> ((A -> B) <-> (C -> D)).
Proof.
  firstorder.
Qed.

Lemma prop_conj : forall {T: Type} (W:Set) (A B : Prop),
                     (forall (V : T -> W -> Prop) (w : W), A /\ B)
                  <-> ((forall (V : T -> W -> Prop) (w : W), A) /\
                        (forall (V : T -> W -> Prop) (w : W), B)).
Proof.
  firstorder.
Qed.

Lemma equiv_conj : forall (A B C D : Prop), (A <-> B) /\ (C <-> D) /\ (B /\ D) -> (A /\ C).
Proof.
  firstorder.
Qed.

Lemma True_conj : forall (A B : Prop), (A <-> (True /\ B)) <-> (A <-> B).
Proof.
  firstorder.
Qed.

Lemma contrapos : forall (A B : Prop),
  (A -> B) -> (~ B -> ~ A).
Proof.
  firstorder.
Qed.
