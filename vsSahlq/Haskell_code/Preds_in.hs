module Preds_in where

import qualified Prelude
import qualified Datatypes
import qualified List
import qualified SO_syntax
import qualified Specif

preds_in :: SO_syntax.SecOrder -> Datatypes.Coq_list SO_syntax.Coq_predicate
preds_in _UU03b1_ =
  case _UU03b1_ of {
   SO_syntax.Coq_predSO p _ -> Datatypes.Coq_cons p Datatypes.Coq_nil;
   SO_syntax.Coq_allFO _ _UU03b2_ -> preds_in _UU03b2_;
   SO_syntax.Coq_exFO _ _UU03b2_ -> preds_in _UU03b2_;
   SO_syntax.Coq_negSO _UU03b2_ -> preds_in _UU03b2_;
   SO_syntax.Coq_conjSO _UU03b2_1 _UU03b2_2 ->
    Datatypes.app (preds_in _UU03b2_1) (preds_in _UU03b2_2);
   SO_syntax.Coq_disjSO _UU03b2_1 _UU03b2_2 ->
    Datatypes.app (preds_in _UU03b2_1) (preds_in _UU03b2_2);
   SO_syntax.Coq_implSO _UU03b2_1 _UU03b2_2 ->
    Datatypes.app (preds_in _UU03b2_1) (preds_in _UU03b2_2);
   SO_syntax.Coq_allSO p _UU03b2_ -> Datatypes.Coq_cons p (preds_in _UU03b2_);
   SO_syntax.Coq_exSO p _UU03b2_ -> Datatypes.Coq_cons p (preds_in _UU03b2_);
   _ -> Datatypes.Coq_nil}

list_closed_SO :: SO_syntax.SecOrder -> (Datatypes.Coq_list
                  SO_syntax.Coq_predicate) -> SO_syntax.SecOrder
list_closed_SO _UU03b1_ l =
  case l of {
   Datatypes.Coq_nil -> _UU03b1_;
   Datatypes.Coq_cons p ls -> SO_syntax.Coq_allSO p
    (list_closed_SO _UU03b1_ ls)}

uni_closed_SO :: SO_syntax.SecOrder -> SO_syntax.SecOrder
uni_closed_SO alpha =
  list_closed_SO alpha (preds_in alpha)

rem_pred :: (Datatypes.Coq_list SO_syntax.Coq_predicate) ->
            SO_syntax.Coq_predicate -> Datatypes.Coq_list
            SO_syntax.Coq_predicate
rem_pred l p =
  List.remove SO_syntax.predicate_dec p l

cap_pred_empty :: (Datatypes.Coq_list SO_syntax.Coq_predicate) ->
                  (Datatypes.Coq_list SO_syntax.Coq_predicate) ->
                  Datatypes.Coq_bool
cap_pred_empty l1 l2 =
  case l1 of {
   Datatypes.Coq_nil -> Datatypes.Coq_true;
   Datatypes.Coq_cons p l1' ->
    case SO_syntax.in_predicate_dec p l2 of {
     Specif.Coq_left -> Datatypes.Coq_false;
     Specif.Coq_right -> cap_pred_empty l1' l2}}

cap_pred :: (Datatypes.Coq_list SO_syntax.Coq_predicate) ->
            (Datatypes.Coq_list SO_syntax.Coq_predicate) ->
            Datatypes.Coq_list SO_syntax.Coq_predicate
cap_pred l1 l2 =
  case l1 of {
   Datatypes.Coq_nil -> Datatypes.Coq_nil;
   Datatypes.Coq_cons p l1' ->
    case SO_syntax.in_predicate_dec p l2 of {
     Specif.Coq_left -> Datatypes.Coq_cons p (cap_pred l1' l2);
     Specif.Coq_right -> cap_pred l1' l2}}

