module VsSahlq_instant9 where

import qualified Prelude
import qualified Datatypes
import qualified List_machinery_impl
import qualified Nat
import qualified PeanoNat
import qualified Rep_Pred_FOv
import qualified SecOrder
import qualified NList_egs
import qualified VsSahlq_preprocessing1
import qualified VsSahlq_preprocessing2

instant_cons_empty' :: SecOrder.SecOrder -> SecOrder.SecOrder ->
                       SecOrder.SecOrder
instant_cons_empty' alpha beta =
  Rep_Pred_FOv.replace_pred_l beta
    (VsSahlq_preprocessing2.list_pred_not_in (SecOrder.preds_in alpha)
      (SecOrder.preds_in beta))
    (List_machinery_impl.nlist_list
      (Datatypes.length
        (VsSahlq_preprocessing2.list_pred_not_in (SecOrder.preds_in alpha)
          (SecOrder.preds_in beta)))
      (NList_egs.nlist_Var1
        (Datatypes.length
          (VsSahlq_preprocessing2.list_pred_not_in (SecOrder.preds_in alpha)
            (SecOrder.preds_in beta)))))
    (List_machinery_impl.nlist_list
      (Datatypes.length
        (VsSahlq_preprocessing2.list_pred_not_in (SecOrder.preds_in alpha)
          (SecOrder.preds_in beta)))
      (NList_egs.nlist_empty
        (Datatypes.length
          (VsSahlq_preprocessing2.list_pred_not_in (SecOrder.preds_in alpha)
            (SecOrder.preds_in beta)))))

is_in_FOvar :: SecOrder.FOvariable -> (Datatypes.Coq_list
               SecOrder.FOvariable) -> Datatypes.Coq_bool
is_in_FOvar x l =
  case l of {
   Datatypes.Coq_nil -> Datatypes.Coq_false;
   Datatypes.Coq_cons y l0 ->
    case PeanoNat._Nat__eqb x y of {
     Datatypes.Coq_true -> Datatypes.Coq_true;
     Datatypes.Coq_false -> is_in_FOvar x l0}}

rename_FOv_list :: (Datatypes.Coq_list SecOrder.FOvariable) ->
                   SecOrder.FOvariable -> SecOrder.FOvariable ->
                   Datatypes.Coq_list SecOrder.FOvariable
rename_FOv_list l x y =
  case l of {
   Datatypes.Coq_nil -> Datatypes.Coq_nil;
   Datatypes.Coq_cons z l' ->
    case PeanoNat._Nat__eqb x z of {
     Datatypes.Coq_true -> Datatypes.Coq_cons y (rename_FOv_list l' x y);
     Datatypes.Coq_false -> Datatypes.Coq_cons z (rename_FOv_list l' x y)}}

coq_FOvars_in :: SecOrder.SecOrder -> Datatypes.Coq_list SecOrder.FOvariable
coq_FOvars_in alpha =
  case alpha of {
   SecOrder.Coq_predSO _ x -> Datatypes.Coq_cons x Datatypes.Coq_nil;
   SecOrder.Coq_relatSO x y -> Datatypes.Coq_cons x (Datatypes.Coq_cons y
    Datatypes.Coq_nil);
   SecOrder.Coq_eqFO x y -> Datatypes.Coq_cons x (Datatypes.Coq_cons y
    Datatypes.Coq_nil);
   SecOrder.Coq_allFO x beta -> Datatypes.Coq_cons x (coq_FOvars_in beta);
   SecOrder.Coq_exFO x beta -> Datatypes.Coq_cons x (coq_FOvars_in beta);
   SecOrder.Coq_negSO beta -> coq_FOvars_in beta;
   SecOrder.Coq_conjSO beta1 beta2 ->
    Datatypes.app (coq_FOvars_in beta1) (coq_FOvars_in beta2);
   SecOrder.Coq_disjSO beta1 beta2 ->
    Datatypes.app (coq_FOvars_in beta1) (coq_FOvars_in beta2);
   SecOrder.Coq_implSO beta1 beta2 ->
    Datatypes.app (coq_FOvars_in beta1) (coq_FOvars_in beta2);
   SecOrder.Coq_allSO _ beta -> coq_FOvars_in beta;
   SecOrder.Coq_exSO _ beta -> coq_FOvars_in beta}

rev_seq :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_list
           Datatypes.Coq_nat
rev_seq start length0 =
  case length0 of {
   Datatypes.O -> Datatypes.Coq_nil;
   Datatypes.S n -> Datatypes.Coq_cons (Nat.add start n) (rev_seq start n)}

newnew_pre :: SecOrder.SecOrder -> (Datatypes.Coq_list SecOrder.FOvariable)
              -> (Datatypes.Coq_list Datatypes.Coq_nat) -> SecOrder.SecOrder
newnew_pre alpha lv ln =
  case lv of {
   Datatypes.Coq_nil -> alpha;
   Datatypes.Coq_cons x lv' ->
    case ln of {
     Datatypes.Coq_nil -> alpha;
     Datatypes.Coq_cons n ln' ->
      VsSahlq_preprocessing1.rename_FOv (newnew_pre alpha lv' ln') x n}}

rem_FOv :: (Datatypes.Coq_list SecOrder.FOvariable) -> SecOrder.FOvariable ->
           Datatypes.Coq_list SecOrder.FOvariable
rem_FOv l x =
  case l of {
   Datatypes.Coq_nil -> Datatypes.Coq_nil;
   Datatypes.Coq_cons y l' ->
    case PeanoNat._Nat__eqb x y of {
     Datatypes.Coq_true -> rem_FOv l' x;
     Datatypes.Coq_false -> Datatypes.Coq_cons y (rem_FOv l' x)}}

is_in_FOvar_l :: (Datatypes.Coq_list SecOrder.FOvariable) ->
                 (Datatypes.Coq_list SecOrder.FOvariable) ->
                 Datatypes.Coq_bool
is_in_FOvar_l l1 l2 =
  case l1 of {
   Datatypes.Coq_nil -> Datatypes.Coq_true;
   Datatypes.Coq_cons x l1' ->
    case is_in_FOvar x l2 of {
     Datatypes.Coq_true -> is_in_FOvar_l l1' l2;
     Datatypes.Coq_false -> Datatypes.Coq_false}}

cap_pred_empty :: (Datatypes.Coq_list SecOrder.Coq_predicate) ->
                  (Datatypes.Coq_list SecOrder.Coq_predicate) ->
                  Datatypes.Coq_bool
cap_pred_empty l1 l2 =
  case l1 of {
   Datatypes.Coq_nil -> Datatypes.Coq_true;
   Datatypes.Coq_cons p l1' ->
    case VsSahlq_preprocessing2.is_in_pred p l2 of {
     Datatypes.Coq_true -> Datatypes.Coq_false;
     Datatypes.Coq_false -> cap_pred_empty l1' l2}}

rem_pred :: (Datatypes.Coq_list SecOrder.Coq_predicate) ->
            SecOrder.Coq_predicate -> Datatypes.Coq_list
            SecOrder.Coq_predicate
rem_pred l p =
  case l of {
   Datatypes.Coq_nil -> Datatypes.Coq_nil;
   Datatypes.Coq_cons q l' ->
    case PeanoNat._Nat__eqb p q of {
     Datatypes.Coq_true -> rem_pred l' p;
     Datatypes.Coq_false -> Datatypes.Coq_cons q (rem_pred l' p)}}

cap_pred :: (Datatypes.Coq_list SecOrder.Coq_predicate) ->
            (Datatypes.Coq_list SecOrder.Coq_predicate) -> Datatypes.Coq_list
            SecOrder.Coq_predicate
cap_pred l1 l2 =
  case l1 of {
   Datatypes.Coq_nil -> Datatypes.Coq_nil;
   Datatypes.Coq_cons p l1' ->
    case VsSahlq_preprocessing2.is_in_pred p l2 of {
     Datatypes.Coq_true -> Datatypes.Coq_cons p (cap_pred l1' l2);
     Datatypes.Coq_false -> cap_pred l1' l2}}

max_l :: (Datatypes.Coq_list Datatypes.Coq_nat) -> Datatypes.Coq_nat
max_l l =
  case l of {
   Datatypes.Coq_nil -> Datatypes.O;
   Datatypes.Coq_cons n l' -> Nat.max n (max_l l')}

min_l :: (Datatypes.Coq_list Datatypes.Coq_nat) -> Datatypes.Coq_nat
min_l l =
  case l of {
   Datatypes.Coq_nil -> Datatypes.O;
   Datatypes.Coq_cons n l' ->
    case l' of {
     Datatypes.Coq_nil -> n;
     Datatypes.Coq_cons _ _ -> Nat.min n (min_l l')}}

