Require Export preds_in.
Require Import Coq.Arith.EqNat List.


Definition Pred_in_SO (alpha : SecOrder) (P : predicate) : Prop :=
  In P (preds_in alpha).

Lemma Pred_in_SO_allFO : forall (alpha : SecOrder) (x : FOvariable)
                                        (P : predicate),
  Pred_in_SO alpha P = Pred_in_SO (allFO x alpha) P.
Proof.
  intros alpha x P.
  unfold Pred_in_SO.
  reflexivity.
Qed.

Lemma Pred_in_SO_exFO : forall (alpha : SecOrder) (x : FOvariable)
                                        (P : predicate),
  Pred_in_SO alpha P = Pred_in_SO (exFO x alpha) P.
Proof.
  intros alpha x P; destruct x;
  unfold Pred_in_SO in *; reflexivity.
Qed.

Lemma Pred_in_SO_negSO : forall (alpha : SecOrder)
                                        (P : predicate),
  Pred_in_SO alpha P = Pred_in_SO (negSO alpha) P.
Proof.
  intros; unfold Pred_in_SO; reflexivity.
Qed.

Lemma Pred_in_SO_conjSO_comp : forall (alpha1 alpha2 : SecOrder)
                                        (P : predicate),
  (Pred_in_SO (conjSO alpha1 alpha2) P ->
    (Pred_in_SO alpha1 P ) + (Pred_in_SO alpha2 P)) *
  ((Pred_in_SO alpha1 P) + (Pred_in_SO alpha2 P) ->
    Pred_in_SO (conjSO alpha1 alpha2) P ).
Proof.
  intros until 0. apply pair; intros H;
                    unfold Pred_in_SO in *; simpl in *.
  apply in_app_or in H.
  destruct (in_dec (predicate_dec) P (preds_in alpha1)) as [H1 | H1].
  left. auto. right.
  destruct H.  contradiction. auto.
  apply in_or_app. firstorder.
Defined.

Lemma Pred_in_SO_conjSO : forall (alpha1 alpha2 : SecOrder)
                                        (P : predicate),
  (Pred_in_SO (conjSO alpha1 alpha2) P <->
    (Pred_in_SO alpha1 P) \/ (Pred_in_SO alpha2 P)).
Proof.
  intros until 0. split; intros H;
                    unfold Pred_in_SO in *; simpl in *.
    apply in_app_or. auto.
    apply in_or_app. auto.
Qed.

Lemma Pred_in_SO_disjSO_comp : forall (alpha1 alpha2 : SecOrder)
                                        (P : predicate),
  (Pred_in_SO (disjSO alpha1 alpha2) P ->
    (Pred_in_SO alpha1 P ) + (Pred_in_SO alpha2 P)) *
  ((Pred_in_SO alpha1 P) + (Pred_in_SO alpha2 P) ->
    Pred_in_SO (disjSO alpha1 alpha2) P ).
Proof.
  intros until 0. apply pair; intros H;
                    unfold Pred_in_SO in *; simpl in *.
  apply in_app_or in H.
  destruct (in_dec (predicate_dec) P (preds_in alpha1)) as [H1 | H1].
  left. auto. right.
  destruct H.  contradiction. auto.
  apply in_or_app. firstorder.
Defined.

Lemma Pred_in_SO_disjSO : forall (alpha1 alpha2 : SecOrder)
                                        (P : predicate),
  (Pred_in_SO (disjSO alpha1 alpha2) P <->
    (Pred_in_SO alpha1 P) \/ (Pred_in_SO alpha2 P)).
Proof.
  intros until 0. split; intros H;
                    unfold Pred_in_SO in *; simpl in *.
    apply in_app_or. auto.
    apply in_or_app. auto.
Qed.

Lemma Pred_in_SO_implSO_comp : forall (alpha1 alpha2 : SecOrder)
                                        (P : predicate),
  (Pred_in_SO (implSO alpha1 alpha2) P ->
    (Pred_in_SO alpha1 P ) + (Pred_in_SO alpha2 P)) *
  ((Pred_in_SO alpha1 P) + (Pred_in_SO alpha2 P) ->
    Pred_in_SO (implSO alpha1 alpha2) P ).
Proof.
  intros until 0. apply pair; intros H;
                    unfold Pred_in_SO in *; simpl in *.
  apply in_app_or in H.
  destruct (in_dec (predicate_dec) P (preds_in alpha1)) as [H1 | H1].
  left. auto. right.
  destruct H.  contradiction. auto.
  apply in_or_app. firstorder.
Defined.

Lemma Pred_in_SO_implSO : forall (alpha1 alpha2 : SecOrder)
                                        (P : predicate),
  (Pred_in_SO (implSO alpha1 alpha2) P <->
    (Pred_in_SO alpha1 P) \/ (Pred_in_SO alpha2 P)).
Proof.
  intros until 0. split; intros H;
                    unfold Pred_in_SO in *; simpl in *.
    apply in_app_or. auto.
    apply in_or_app. auto.
Qed.

Lemma Pred_in_SO_allSO : forall (alpha : SecOrder)
                                        (Q P: predicate),
  Pred_in_SO (allSO Q alpha) P <->
    P = Q   \/ Pred_in_SO alpha P.
Proof. firstorder. Qed.

Lemma Pred_in_SO_exSO : forall (alpha : SecOrder)
                                        (Q P: predicate),
  Pred_in_SO (exSO Q alpha) P <->
    P = Q   \/ Pred_in_SO alpha P.
Proof. firstorder. Qed.

Lemma  Pred_in_SO_allSO3 : forall alpha P Q,
  ~ Q = P ->
  Pred_in_SO alpha P <-> Pred_in_SO (allSO Q alpha) P.
Proof.
  intros alpha P Q Hneq. 
  unfold Pred_in_SO. simpl. firstorder.
Qed.

Lemma  Pred_in_SO_exSO2 : forall alpha P Q,
  ~ Q = P ->
  Pred_in_SO alpha P <-> Pred_in_SO (exSO Q alpha) P.
Proof.
  intros alpha P Q Hneq.
  unfold Pred_in_SO. simpl. firstorder.
Qed.

Lemma Pred_in_SO_conjSO_f : forall (alpha1 alpha2 : SecOrder)
                                        (P : predicate),
  ~ Pred_in_SO (conjSO alpha1 alpha2) P <->
  ~ Pred_in_SO alpha1 P /\ ~ Pred_in_SO alpha2 P.
Proof.
  split; intros H;
    unfold Pred_in_SO in *;
    simpl in *. split; intros H2.
  contradiction (H (in_or_app _ _ _ (or_introl  _ H2))).
  contradiction (H (in_or_app _ _ _ (or_intror  _ H2))).
  intros H2. apply in_app_or in H2. firstorder.
Qed.


(* ---------------------------------------------------------------- *)

Inductive lPred_in_SO (alpha : SecOrder) : list predicate -> Prop :=
| lPred_nil : lPred_in_SO alpha nil
| lPred_cons : forall P lP, Pred_in_SO alpha P -> lPred_in_SO alpha lP ->
                            lPred_in_SO alpha (P :: lP).