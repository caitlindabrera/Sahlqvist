Require Import base_mods SO_syntax.

Ltac FOv_dec_refl :=
  match goal with
  | [ |- context[FOvariable_dec ?x ?x] ] => destruct (FOvariable_dec x x) as [?H | ?H];
                                   [clear H|contradiction]
  end.

Ltac dest_pred_dec P Q :=
  destruct (predicate_dec P Q);
  [rewrite (predicate_dec_l Q P) in *; auto; subst Q
  | rewrite (predicate_dec_r Q P) in *; auto].


Ltac dest_FOv_blind :=
  repeat match goal with
           [ f : FOvariable |- _ ] => destruct f
         end.

Ltac dest_FOv_dec_blind :=
 repeat match goal with
    [ H5 : context[ FOvariable_dec ?x ?y] |- _ ] => destruct (FOvariable_dec x y)
  | [ |- context[ FOvariable_dec ?x ?y] ] => destruct (FOvariable_dec x y) end.


Ltac FOv_dec_l_rep :=
  repeat match goal with
         | [ H : context [(FOvariable_dec ?x ?x) ] |- _] =>
           rewrite (FOvariable_dec_l x x) in H; auto
         | [ |- context [(FOvariable_dec ?x ?x) ] ] =>
           rewrite (FOvariable_dec_l x x); auto
  end.

Ltac pred_dec_l_rep :=
  repeat match goal with
         | [ H : context [(predicate_dec ?x ?x) ] |- _] =>
           rewrite (predicate_dec_l x x) in H; auto
         | [ |- context [(predicate_dec ?x ?x) ] ] =>
           rewrite (predicate_dec_l x x); auto
  end.

Ltac dest_in_dec_blind :=
  repeat match goal with
           [ H5 : context[ in_dec ?eq_dec ?x ?y] |- _ ] => destruct (in_dec eq_dec x y)
         | [ |- context[ in_dec ?eq_dec ?x ?y] ] => destruct (in_dec eq_dec x y) end.

Ltac dest_in_pred_dec_blind :=
  repeat match goal with
           [ H5 : context[ in_predicate_dec ?x ?y] |- _ ] => destruct (in_predicate_dec x y)
         | [ |- context[ in_predicate_dec ?x ?y] ] => destruct (in_predicate_dec x y) end.