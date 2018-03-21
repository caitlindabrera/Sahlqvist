module VsSahlq_preprocessing2 where

import qualified Prelude
import qualified Datatypes
import qualified List_machinery_impl
import qualified PeanoNat
import qualified Rep_Pred_FOv
import qualified SecOrder
import qualified NList_egs

vsSahlq_dest_SO_ante :: SecOrder.SecOrder -> SecOrder.SecOrder
vsSahlq_dest_SO_ante alpha =
  case alpha of {
   SecOrder.Coq_implSO beta1 _ -> beta1;
   _ -> alpha}

vsSahlq_dest_SO_cons :: SecOrder.SecOrder -> SecOrder.SecOrder
vsSahlq_dest_SO_cons alpha =
  case alpha of {
   SecOrder.Coq_implSO _ beta2 -> beta2;
   _ -> alpha}

predSO_vars_list :: SecOrder.SecOrder -> SecOrder.Coq_predicate ->
                    Datatypes.Coq_list SecOrder.FOvariable
predSO_vars_list alpha p =
  case alpha of {
   SecOrder.Coq_predSO q x ->
    case PeanoNat._Nat__eqb p q of {
     Datatypes.Coq_true -> Datatypes.Coq_cons x Datatypes.Coq_nil;
     Datatypes.Coq_false -> Datatypes.Coq_nil};
   SecOrder.Coq_allFO _ beta -> predSO_vars_list beta p;
   SecOrder.Coq_exFO _ beta -> predSO_vars_list beta p;
   SecOrder.Coq_negSO beta -> predSO_vars_list beta p;
   SecOrder.Coq_conjSO beta1 beta2 ->
    Datatypes.app (predSO_vars_list beta1 p) (predSO_vars_list beta2 p);
   SecOrder.Coq_disjSO beta1 beta2 ->
    Datatypes.app (predSO_vars_list beta1 p) (predSO_vars_list beta2 p);
   SecOrder.Coq_implSO beta1 beta2 ->
    Datatypes.app (predSO_vars_list beta1 p) (predSO_vars_list beta2 p);
   SecOrder.Coq_allSO _ beta -> predSO_vars_list beta p;
   SecOrder.Coq_exSO _ beta -> predSO_vars_list beta p;
   _ -> Datatypes.Coq_nil}

is_in :: Datatypes.Coq_nat -> (Datatypes.Coq_list Datatypes.Coq_nat) ->
         Datatypes.Coq_bool
is_in n l =
  case l of {
   Datatypes.Coq_nil -> Datatypes.Coq_false;
   Datatypes.Coq_cons m l' ->
    case PeanoNat._Nat__eqb n m of {
     Datatypes.Coq_true -> Datatypes.Coq_true;
     Datatypes.Coq_false -> is_in n l'}}

is_in_pred :: SecOrder.Coq_predicate -> (Datatypes.Coq_list
              SecOrder.Coq_predicate) -> Datatypes.Coq_bool
is_in_pred p l =
  case l of {
   Datatypes.Coq_nil -> Datatypes.Coq_false;
   Datatypes.Coq_cons p0 l' ->
    case PeanoNat._Nat__eqb p p0 of {
     Datatypes.Coq_true -> Datatypes.Coq_true;
     Datatypes.Coq_false -> is_in_pred p l'}}

list_pred_not_in :: (Datatypes.Coq_list SecOrder.Coq_predicate) ->
                    (Datatypes.Coq_list SecOrder.Coq_predicate) ->
                    Datatypes.Coq_list SecOrder.Coq_predicate
list_pred_not_in l1 l2 =
  case l2 of {
   Datatypes.Coq_nil -> Datatypes.Coq_nil;
   Datatypes.Coq_cons p l2' ->
    case is_in_pred p l1 of {
     Datatypes.Coq_true -> list_pred_not_in l1 l2';
     Datatypes.Coq_false -> Datatypes.Coq_cons p (list_pred_not_in l1 l2')}}

instant_cons_empty :: SecOrder.SecOrder -> SecOrder.SecOrder
instant_cons_empty alpha =
  Rep_Pred_FOv.replace_pred_l alpha
    (list_pred_not_in (SecOrder.preds_in (vsSahlq_dest_SO_ante alpha))
      (SecOrder.preds_in (vsSahlq_dest_SO_cons alpha)))
    (List_machinery_impl.nlist_list
      (Datatypes.length
        (list_pred_not_in (SecOrder.preds_in (vsSahlq_dest_SO_ante alpha))
          (SecOrder.preds_in (vsSahlq_dest_SO_cons alpha))))
      (NList_egs.nlist_Var1
        (Datatypes.length
          (list_pred_not_in (SecOrder.preds_in (vsSahlq_dest_SO_ante alpha))
            (SecOrder.preds_in (vsSahlq_dest_SO_cons alpha))))))
    (List_machinery_impl.nlist_list
      (Datatypes.length
        (list_pred_not_in (SecOrder.preds_in (vsSahlq_dest_SO_ante alpha))
          (SecOrder.preds_in (vsSahlq_dest_SO_cons alpha))))
      (NList_egs.nlist_empty
        (Datatypes.length
          (list_pred_not_in (SecOrder.preds_in (vsSahlq_dest_SO_ante alpha))
            (SecOrder.preds_in (vsSahlq_dest_SO_cons alpha))))))

is_in_pred_l :: (Datatypes.Coq_list SecOrder.Coq_predicate) ->
                (Datatypes.Coq_list SecOrder.Coq_predicate) ->
                Datatypes.Coq_bool
is_in_pred_l l1 l2 =
  case l1 of {
   Datatypes.Coq_nil -> Datatypes.Coq_true;
   Datatypes.Coq_cons p l1' ->
    case is_in_pred p l2 of {
     Datatypes.Coq_true -> is_in_pred_l l1' l2;
     Datatypes.Coq_false -> Datatypes.Coq_false}}

nlist_P :: Datatypes.Coq_nat -> SecOrder.Coq_predicate ->
           List_machinery_impl.Coq_nlist SecOrder.Coq_predicate
nlist_P n p =
  case n of {
   Datatypes.O -> List_machinery_impl.Coq_niln;
   Datatypes.S m -> List_machinery_impl.Coq_consn m p (nlist_P m p)}

free_SO :: SecOrder.SecOrder -> SecOrder.Coq_predicate -> Datatypes.Coq_bool
free_SO alpha p =
  case alpha of {
   SecOrder.Coq_predSO q _ -> PeanoNat._Nat__eqb p q;
   SecOrder.Coq_allFO _ beta -> free_SO beta p;
   SecOrder.Coq_exFO _ beta -> free_SO beta p;
   SecOrder.Coq_negSO beta -> free_SO beta p;
   SecOrder.Coq_conjSO beta1 beta2 ->
    case free_SO beta1 p of {
     Datatypes.Coq_true -> Datatypes.Coq_true;
     Datatypes.Coq_false -> free_SO beta2 p};
   SecOrder.Coq_disjSO beta1 beta2 ->
    case free_SO beta1 p of {
     Datatypes.Coq_true -> Datatypes.Coq_true;
     Datatypes.Coq_false -> free_SO beta2 p};
   SecOrder.Coq_implSO beta1 beta2 ->
    case free_SO beta1 p of {
     Datatypes.Coq_true -> Datatypes.Coq_true;
     Datatypes.Coq_false -> free_SO beta2 p};
   SecOrder.Coq_allSO q beta ->
    case PeanoNat._Nat__eqb p q of {
     Datatypes.Coq_true -> Datatypes.Coq_false;
     Datatypes.Coq_false -> free_SO beta p};
   SecOrder.Coq_exSO q beta ->
    case PeanoNat._Nat__eqb p q of {
     Datatypes.Coq_true -> Datatypes.Coq_false;
     Datatypes.Coq_false -> free_SO beta p};
   _ -> Datatypes.Coq_false}

no_free_SO_l :: SecOrder.SecOrder -> (Datatypes.Coq_list
                SecOrder.Coq_predicate) -> Datatypes.Coq_bool
no_free_SO_l alpha l =
  case l of {
   Datatypes.Coq_nil -> Datatypes.Coq_true;
   Datatypes.Coq_cons p l' ->
    case free_SO alpha p of {
     Datatypes.Coq_true -> Datatypes.Coq_false;
     Datatypes.Coq_false -> no_free_SO_l alpha l'}}

