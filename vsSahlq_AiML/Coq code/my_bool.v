Lemma true_true : true = true.
Proof.
  reflexivity.
Qed.

Lemma false_false : false = false.
Proof.
  reflexivity.
Qed.

Lemma contrapos_bool_tt : forall (a b : bool),
  (a = true -> b = true) -> (b = false -> a = false).
Proof.
  intros.
  case_eq a; intros Ha; try reflexivity.
    rewrite H0 in H; symmetry; apply H; exact Ha.
Qed.

Lemma contrapos_bool_tf : forall (a b : bool),
  (a = true -> b = false) -> (b = true -> a = false).
Proof.
  intros a b H1 Hb.
  case_eq a; intros Ha; try reflexivity.
    rewrite Hb in *; specialize (H1 Ha); 
    rewrite H1 in *; discriminate.
Qed.

Lemma contrapos_bool_ft : forall (a b : bool),
  (a = false -> b = true) -> (b = false -> a = true).
Proof.
  intros a b H1 Hb.
  case_eq a; 
  [reflexivity | 
    intros Ha; specialize (H1 Ha); rewrite H1 in *; discriminate].
Qed.

Lemma contrapos_bool_ff : forall (a b : bool),
  (a = false -> b = false) -> (b = true -> a = true).
Proof.
  intros a b H1 Hb.
  case_eq a; intros Ha; [reflexivity | 
  specialize (H1 Ha); rewrite H1 in *; discriminate].
Qed.

Lemma contrapos_bool_or : forall (a b c : bool),
  (a = true <-> b = true \/ c = true) ->
    (a = false <-> b = false /\ c = false).
Proof.
  intros a b c H.
  destruct H as [f r].
  case_eq a; intros Ha; rewrite Ha in *.
    split; intros H1.
      discriminate.

      case_eq b; intros Hb; rewrite Hb in *;
        destruct H1 as [L R]; try discriminate.

        case_eq c; intros Hc; rewrite Hc in *.
          discriminate.

          symmetry.
          specialize (f true_true). 
          destruct f; discriminate.

          split; intros H1; try reflexivity.
            apply conj.
              case_eq b; intros Hb; rewrite Hb in *.
                symmetry; apply r; left; reflexivity.

                reflexivity.

              case_eq c; intros Hc; rewrite Hc in *.
                symmetry; apply r; right; reflexivity.

                reflexivity.
Qed. 

Lemma if_then_else_same : forall {A : Type} (a : bool) ( b : A),
  (if a then b else b) = b.
Proof.
  intros A a b.
  case a; reflexivity.
Qed.


Lemma if_then_else_false : forall a : bool,
  (if a then false else false )= false.
Proof.
  intros; case a; reflexivity.
Qed.

Lemma if_then_else_true : forall a : bool,
  (if a then true else true )= true.
Proof.
  intros; case a; reflexivity.
Qed.

Lemma if_then_else_true_false : forall a : bool,
(if a then true else false) = false -> a = false.
Proof.
  intros a H.
  case_eq a; intros Ha.
    rewrite Ha in *.
    discriminate.

    reflexivity.
Qed.