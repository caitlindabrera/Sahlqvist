module P_occurs_in_alpha where

import qualified Prelude
import qualified Datatypes
import qualified PeanoNat
import qualified SecOrder

__ :: any
__ = Prelude.error "Logical or arity value used"

coq_P_occurs_in_l :: (Datatypes.Coq_list SecOrder.Coq_predicate) ->
                     SecOrder.Coq_predicate -> Datatypes.Coq_bool
coq_P_occurs_in_l l p =
  case l of {
   Datatypes.Coq_nil -> Datatypes.Coq_false;
   Datatypes.Coq_cons q l' ->
    case PeanoNat._Nat__eqb p q of {
     Datatypes.Coq_true -> Datatypes.Coq_true;
     Datatypes.Coq_false -> coq_P_occurs_in_l l' p}}

coq_P_occurs_in_l_app_comp :: (Datatypes.Coq_list SecOrder.Coq_predicate) ->
                              (Datatypes.Coq_list SecOrder.Coq_predicate) ->
                              SecOrder.Coq_predicate -> Datatypes.Coq_prod
                              (() -> Datatypes.Coq_sum () ()) ()
coq_P_occurs_in_l_app_comp l1 l2 p =
  Datatypes.list_rec
    (Datatypes.list_rec (Datatypes.Coq_pair (\_ -> Datatypes.Coq_inl __) __)
      (\a _ iHl2 ->
      case PeanoNat._Nat__eqb p a of {
       Datatypes.Coq_true -> Datatypes.Coq_pair (\_ -> Datatypes.Coq_inr __)
        __;
       Datatypes.Coq_false -> Datatypes.Coq_pair (\_ ->
        case iHl2 of {
         Datatypes.Coq_pair x _ -> x __}) __}) l2) (\a _ iHl1 ->
    case PeanoNat._Nat__eqb p a of {
     Datatypes.Coq_true -> Datatypes.Coq_pair (\_ -> Datatypes.Coq_inl __) __;
     Datatypes.Coq_false -> Datatypes.Coq_pair (\_ ->
      case iHl1 of {
       Datatypes.Coq_pair x _ -> x __}) __}) l1

coq_P_occurs_in_alpha :: SecOrder.SecOrder -> SecOrder.Coq_predicate ->
                         Datatypes.Coq_bool
coq_P_occurs_in_alpha alpha p =
  coq_P_occurs_in_l (SecOrder.preds_in alpha) p

coq_P_occurs_in_alpha_conjSO_comp :: SecOrder.SecOrder -> SecOrder.SecOrder
                                     -> SecOrder.Coq_predicate ->
                                     Datatypes.Coq_prod
                                     (() -> Datatypes.Coq_sum () ()) 
                                     ()
coq_P_occurs_in_alpha_conjSO_comp alpha1 alpha2 p =
  Datatypes.Coq_pair (\_ ->
    let {l1 = SecOrder.preds_in alpha1} in
    let {l2 = SecOrder.preds_in alpha2} in
    case coq_P_occurs_in_l_app_comp l1 l2 p of {
     Datatypes.Coq_pair x _ -> x __}) __

coq_P_occurs_in_alpha_disjSO_comp :: SecOrder.SecOrder -> SecOrder.SecOrder
                                     -> SecOrder.Coq_predicate ->
                                     Datatypes.Coq_prod
                                     (() -> Datatypes.Coq_sum () ()) 
                                     ()
coq_P_occurs_in_alpha_disjSO_comp alpha1 alpha2 p =
  Datatypes.Coq_pair (\_ ->
    let {l1 = SecOrder.preds_in alpha1} in
    let {l2 = SecOrder.preds_in alpha2} in
    case coq_P_occurs_in_l_app_comp l1 l2 p of {
     Datatypes.Coq_pair x _ -> x __}) __

coq_P_occurs_in_alpha_implSO_comp :: SecOrder.SecOrder -> SecOrder.SecOrder
                                     -> SecOrder.Coq_predicate ->
                                     Datatypes.Coq_prod
                                     (() -> Datatypes.Coq_sum () ()) 
                                     ()
coq_P_occurs_in_alpha_implSO_comp alpha1 alpha2 p =
  Datatypes.Coq_pair (\_ ->
    let {l1 = SecOrder.preds_in alpha1} in
    let {l2 = SecOrder.preds_in alpha2} in
    case coq_P_occurs_in_l_app_comp l1 l2 p of {
     Datatypes.Coq_pair x _ -> x __}) __

l_occurs_in_alpha :: SecOrder.SecOrder -> (Datatypes.Coq_list
                     SecOrder.Coq_predicate) -> Datatypes.Coq_bool
l_occurs_in_alpha alpha l =
  case l of {
   Datatypes.Coq_nil -> Datatypes.Coq_true;
   Datatypes.Coq_cons p l' ->
    case coq_P_occurs_in_alpha alpha p of {
     Datatypes.Coq_true -> l_occurs_in_alpha alpha l';
     Datatypes.Coq_false -> Datatypes.Coq_false}}

