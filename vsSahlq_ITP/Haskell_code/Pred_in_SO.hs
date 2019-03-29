module Pred_in_SO where

import qualified Prelude
import qualified Datatypes
import qualified List
import qualified SO_syntax
import qualified Specif
import qualified Preds_in

__ :: any
__ = Prelude.error "Logical or arity value used"

coq_Pred_in_SO_dec :: SO_syntax.SecOrder -> SO_syntax.Coq_predicate ->
                      Specif.Coq_sumbool
coq_Pred_in_SO_dec alpha p =
  List.in_dec SO_syntax.predicate_dec p (Preds_in.preds_in alpha)

trying1 :: SO_syntax.SecOrder -> Datatypes.Coq_sum () SO_syntax.Coq_predicate
trying1 alpha =
  let {l = Preds_in.preds_in alpha} in
  case l of {
   Datatypes.Coq_nil -> Datatypes.Coq_inl __;
   Datatypes.Coq_cons p _ -> Datatypes.Coq_inr p}

coq_Pred_in_SO_conjSO_comp :: SO_syntax.SecOrder -> SO_syntax.SecOrder ->
                              SO_syntax.Coq_predicate -> Datatypes.Coq_prod
                              (() -> Datatypes.Coq_sum () ()) ()
coq_Pred_in_SO_conjSO_comp alpha1 _ p =
  Datatypes.Coq_pair (\_ ->
    let {
     s = List.in_dec SO_syntax.predicate_dec p (Preds_in.preds_in alpha1)}
    in
    case s of {
     Specif.Coq_left -> Datatypes.Coq_inl __;
     Specif.Coq_right -> Datatypes.Coq_inr __}) __

coq_Pred_in_SO_disjSO_comp :: SO_syntax.SecOrder -> SO_syntax.SecOrder ->
                              SO_syntax.Coq_predicate -> Datatypes.Coq_prod
                              (() -> Datatypes.Coq_sum () ()) ()
coq_Pred_in_SO_disjSO_comp alpha1 _ p =
  Datatypes.Coq_pair (\_ ->
    let {
     s = List.in_dec SO_syntax.predicate_dec p (Preds_in.preds_in alpha1)}
    in
    case s of {
     Specif.Coq_left -> Datatypes.Coq_inl __;
     Specif.Coq_right -> Datatypes.Coq_inr __}) __

coq_Pred_in_SO_implSO_comp :: SO_syntax.SecOrder -> SO_syntax.SecOrder ->
                              SO_syntax.Coq_predicate -> Datatypes.Coq_prod
                              (() -> Datatypes.Coq_sum () ()) ()
coq_Pred_in_SO_implSO_comp alpha1 _ p =
  Datatypes.Coq_pair (\_ ->
    let {
     s = List.in_dec SO_syntax.predicate_dec p (Preds_in.preds_in alpha1)}
    in
    case s of {
     Specif.Coq_left -> Datatypes.Coq_inl __;
     Specif.Coq_right -> Datatypes.Coq_inr __}) __

