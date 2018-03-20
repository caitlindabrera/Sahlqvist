Lemma bi_refl : forall A:Prop, A <-> A.
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
Qed. 

Lemma bi_conj : forall A B C D: Prop, ((A <-> C) /\ (B <-> D)) -> ((A /\ B) <-> (C /\ D)).
Proof.
  intros A B C D.
  intros H.
  destruct H as [A_C B_D].
  unfold iff; apply conj.
    intros AandB.
    destruct AandB as [pf_A pf_B].
    apply conj.
      apply A_C; exact pf_A.

      apply B_D; exact pf_B.
    intros CandD.
    destruct CandD as [pf_C pf_D].
    apply conj.
      apply A_C; exact pf_C.

      apply B_D; exact pf_D.
Qed.

Lemma bi_impl : forall A B C D: Prop, ((A <-> C) /\ (B <-> D)) -> ((A -> B) <-> (C -> D)).
Proof.
  intros A B C D.
  intros H.
  destruct H as [A_C B_D].
  unfold iff; apply conj.
    intros A_B pf_C.
    apply B_D; apply A_B; apply A_C; exact pf_C.

    intros C_D pf_A.
    apply B_D; apply C_D; apply A_C; exact pf_A.
Qed.

Lemma prop_conj : forall {T: Type} (W:Set) (A B : Prop),
                     (forall (V : T -> W -> Prop) (w : W), A /\ B)
                  <-> ((forall (V : T -> W -> Prop) (w : W), A) /\
                        (forall (V : T -> W -> Prop) (w : W), B)).
Proof.
  intros T W A B.
  unfold iff; apply conj.
    intros pf_and.
    apply conj.
      intros V w.
      apply pf_and in V.
        destruct V as [pf_A pf_B].
        exact pf_A.

        exact w.
      intros V w.
      apply pf_and in V.
      destruct V as [pf_A pf_B].
        exact pf_B.

        exact w.

    intros pf_a_pf_b.
    destruct pf_a_pf_b as [pf_A pf_B].
    intros V w.
    apply conj.
      apply pf_A.
        exact V.

        exact w.
      apply pf_B. 
        exact V.

        exact w.
Qed.

Lemma equiv_conj : forall (A B C D : Prop), (A <-> B) /\ (C <-> D) /\ (B /\ D) -> (A /\ C).
Proof.
  intros A B C D.
  intros [pfAB [pfCD [pfB pfD]]].
  apply conj.
    apply pfAB; exact pfB.

    apply pfCD; exact pfD.
Qed.

Lemma True_conj : forall (A B : Prop), (A <-> (True /\ B)) <-> (A <-> B).
Proof.
  intros.
  split.
    intros.
    split.
      intros.
      destruct H as [H1 H2].
      pose proof (H1 H0).
      apply H.

      intros.
      apply H.
      apply conj.
        exact I.

        exact H0.

    intros.
    split.
      intros.
      apply conj.
        exact I.

        apply H; exact H0.

      intros.
      apply H; apply H0.
Qed.

Lemma True_True : True <-> True.
Proof.
  split.
    intros H; exact H.

    intros H; exact H.
Qed.

Lemma contrapos : forall (A B : Prop),
  (A -> B) -> (~ B -> ~ A).
Proof.
  intros A B H notB.
  unfold not in *; intros HA.
  apply notB; apply H; assumption.
Qed.