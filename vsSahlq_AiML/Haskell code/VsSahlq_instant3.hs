module VsSahlq_instant3 where

import qualified Prelude
import qualified Datatypes
import qualified List_machinery_impl
import qualified PeanoNat
import qualified SecOrder

fun1 :: (Datatypes.Coq_list SecOrder.FOvariable) -> SecOrder.FOvariable ->
        SecOrder.SecOrder
fun1 lv x =
  case lv of {
   Datatypes.Coq_nil -> SecOrder.Coq_eqFO (Datatypes.S Datatypes.O)
    (Datatypes.S Datatypes.O);
   Datatypes.Coq_cons y lv' ->
    case lv' of {
     Datatypes.Coq_nil -> SecOrder.Coq_eqFO x y;
     Datatypes.Coq_cons _ _ -> SecOrder.Coq_disjSO (SecOrder.Coq_eqFO x y)
      (fun1 lv' x)}}

vsS_syn_l :: (Datatypes.Coq_list (Datatypes.Coq_list SecOrder.FOvariable)) ->
             SecOrder.FOvariable -> Datatypes.Coq_list SecOrder.SecOrder
vsS_syn_l llv x =
  case llv of {
   Datatypes.Coq_nil -> Datatypes.Coq_nil;
   Datatypes.Coq_cons lv llv' -> Datatypes.Coq_cons (fun1 lv x)
    (vsS_syn_l llv' x)}

fun2 :: SecOrder.SecOrder -> SecOrder.Coq_predicate -> Datatypes.Coq_list
        SecOrder.FOvariable
fun2 alpha p =
  case alpha of {
   SecOrder.Coq_predSO q x ->
    case PeanoNat._Nat__eqb p q of {
     Datatypes.Coq_true -> Datatypes.Coq_cons x Datatypes.Coq_nil;
     Datatypes.Coq_false -> Datatypes.Coq_nil};
   SecOrder.Coq_allFO _ beta -> fun2 beta p;
   SecOrder.Coq_exFO _ beta -> fun2 beta p;
   SecOrder.Coq_negSO beta -> fun2 beta p;
   SecOrder.Coq_conjSO beta1 beta2 ->
    Datatypes.app (fun2 beta1 p) (fun2 beta2 p);
   SecOrder.Coq_disjSO beta1 beta2 ->
    Datatypes.app (fun2 beta1 p) (fun2 beta2 p);
   SecOrder.Coq_implSO beta1 beta2 ->
    Datatypes.app (fun2 beta1 p) (fun2 beta2 p);
   SecOrder.Coq_allSO _ beta -> fun2 beta p;
   SecOrder.Coq_exSO _ beta -> fun2 beta p;
   _ -> Datatypes.Coq_nil}

coq_FOv_att_P_l :: SecOrder.SecOrder -> (Datatypes.Coq_list
                   SecOrder.Coq_predicate) -> Datatypes.Coq_list
                   (Datatypes.Coq_list SecOrder.FOvariable)
coq_FOv_att_P_l alpha lP =
  case lP of {
   Datatypes.Coq_nil -> Datatypes.Coq_nil;
   Datatypes.Coq_cons p lP' -> Datatypes.Coq_cons (fun2 alpha p)
    (coq_FOv_att_P_l alpha lP')}

nlist_Var :: Datatypes.Coq_nat -> SecOrder.FOvariable ->
             List_machinery_impl.Coq_nlist SecOrder.FOvariable
nlist_Var n x =
  case n of {
   Datatypes.O -> List_machinery_impl.Coq_niln;
   Datatypes.S m -> List_machinery_impl.Coq_consn m x (nlist_Var m x)}

list_Var :: Datatypes.Coq_nat -> SecOrder.FOvariable -> Datatypes.Coq_list
            SecOrder.FOvariable
list_Var n x =
  case n of {
   Datatypes.O -> Datatypes.Coq_nil;
   Datatypes.S m -> Datatypes.Coq_cons x (list_Var m x)}

coq_SOQFree_P :: SecOrder.SecOrder -> SecOrder.Coq_predicate ->
                 Datatypes.Coq_bool
coq_SOQFree_P alpha p =
  case alpha of {
   SecOrder.Coq_allFO _ beta -> coq_SOQFree_P beta p;
   SecOrder.Coq_exFO _ beta -> coq_SOQFree_P beta p;
   SecOrder.Coq_negSO beta -> coq_SOQFree_P beta p;
   SecOrder.Coq_conjSO beta1 beta2 ->
    case coq_SOQFree_P beta1 p of {
     Datatypes.Coq_true -> coq_SOQFree_P beta2 p;
     Datatypes.Coq_false -> Datatypes.Coq_false};
   SecOrder.Coq_disjSO beta1 beta2 ->
    case coq_SOQFree_P beta1 p of {
     Datatypes.Coq_true -> coq_SOQFree_P beta2 p;
     Datatypes.Coq_false -> Datatypes.Coq_false};
   SecOrder.Coq_implSO beta1 beta2 ->
    case coq_SOQFree_P beta1 p of {
     Datatypes.Coq_true -> coq_SOQFree_P beta2 p;
     Datatypes.Coq_false -> Datatypes.Coq_false};
   SecOrder.Coq_allSO p0 beta ->
    case PeanoNat._Nat__eqb p p0 of {
     Datatypes.Coq_true -> Datatypes.Coq_false;
     Datatypes.Coq_false -> coq_SOQFree_P beta p};
   SecOrder.Coq_exSO p0 beta ->
    case PeanoNat._Nat__eqb p p0 of {
     Datatypes.Coq_true -> Datatypes.Coq_false;
     Datatypes.Coq_false -> coq_SOQFree_P beta p};
   _ -> Datatypes.Coq_true}

no_FOquant :: SecOrder.SecOrder -> Datatypes.Coq_bool
no_FOquant alpha =
  case alpha of {
   SecOrder.Coq_allFO _ _ -> Datatypes.Coq_false;
   SecOrder.Coq_exFO _ _ -> Datatypes.Coq_false;
   SecOrder.Coq_negSO beta -> no_FOquant beta;
   SecOrder.Coq_conjSO beta1 beta2 ->
    case no_FOquant beta1 of {
     Datatypes.Coq_true -> no_FOquant beta2;
     Datatypes.Coq_false -> Datatypes.Coq_false};
   SecOrder.Coq_disjSO beta1 beta2 ->
    case no_FOquant beta1 of {
     Datatypes.Coq_true -> no_FOquant beta2;
     Datatypes.Coq_false -> Datatypes.Coq_false};
   SecOrder.Coq_implSO beta1 beta2 ->
    case no_FOquant beta1 of {
     Datatypes.Coq_true -> no_FOquant beta2;
     Datatypes.Coq_false -> Datatypes.Coq_false};
   SecOrder.Coq_allSO _ beta -> no_FOquant beta;
   SecOrder.Coq_exSO _ beta -> no_FOquant beta;
   _ -> Datatypes.Coq_true}

attached_allFO_x :: SecOrder.SecOrder -> SecOrder.FOvariable ->
                    Datatypes.Coq_bool
attached_allFO_x alpha x =
  case alpha of {
   SecOrder.Coq_allFO y beta ->
    case PeanoNat._Nat__eqb x y of {
     Datatypes.Coq_true -> Datatypes.Coq_true;
     Datatypes.Coq_false -> attached_allFO_x beta x};
   SecOrder.Coq_exFO _ beta -> attached_allFO_x beta x;
   SecOrder.Coq_negSO beta -> attached_allFO_x beta x;
   SecOrder.Coq_conjSO beta1 beta2 ->
    case attached_allFO_x beta1 x of {
     Datatypes.Coq_true -> Datatypes.Coq_true;
     Datatypes.Coq_false -> attached_allFO_x beta2 x};
   SecOrder.Coq_disjSO beta1 beta2 ->
    case attached_allFO_x beta1 x of {
     Datatypes.Coq_true -> Datatypes.Coq_true;
     Datatypes.Coq_false -> attached_allFO_x beta2 x};
   SecOrder.Coq_implSO beta1 beta2 ->
    case attached_allFO_x beta1 x of {
     Datatypes.Coq_true -> Datatypes.Coq_true;
     Datatypes.Coq_false -> attached_allFO_x beta2 x};
   SecOrder.Coq_allSO _ beta -> attached_allFO_x beta x;
   SecOrder.Coq_exSO _ beta -> attached_allFO_x beta x;
   _ -> Datatypes.Coq_false}

ex_attached_allFO_lv :: SecOrder.SecOrder -> (Datatypes.Coq_list
                        SecOrder.FOvariable) -> Datatypes.Coq_bool
ex_attached_allFO_lv alpha lv =
  case lv of {
   Datatypes.Coq_nil -> Datatypes.Coq_false;
   Datatypes.Coq_cons y lv' ->
    case attached_allFO_x alpha y of {
     Datatypes.Coq_true -> Datatypes.Coq_true;
     Datatypes.Coq_false -> ex_attached_allFO_lv alpha lv'}}

attached_exFO_x :: SecOrder.SecOrder -> SecOrder.FOvariable ->
                   Datatypes.Coq_bool
attached_exFO_x alpha x =
  case alpha of {
   SecOrder.Coq_allFO _ beta -> attached_exFO_x beta x;
   SecOrder.Coq_exFO y beta ->
    case PeanoNat._Nat__eqb x y of {
     Datatypes.Coq_true -> Datatypes.Coq_true;
     Datatypes.Coq_false -> attached_exFO_x beta x};
   SecOrder.Coq_negSO beta -> attached_exFO_x beta x;
   SecOrder.Coq_conjSO beta1 beta2 ->
    case attached_exFO_x beta1 x of {
     Datatypes.Coq_true -> Datatypes.Coq_true;
     Datatypes.Coq_false -> attached_exFO_x beta2 x};
   SecOrder.Coq_disjSO beta1 beta2 ->
    case attached_exFO_x beta1 x of {
     Datatypes.Coq_true -> Datatypes.Coq_true;
     Datatypes.Coq_false -> attached_exFO_x beta2 x};
   SecOrder.Coq_implSO beta1 beta2 ->
    case attached_exFO_x beta1 x of {
     Datatypes.Coq_true -> Datatypes.Coq_true;
     Datatypes.Coq_false -> attached_exFO_x beta2 x};
   SecOrder.Coq_allSO _ beta -> attached_exFO_x beta x;
   SecOrder.Coq_exSO _ beta -> attached_exFO_x beta x;
   _ -> Datatypes.Coq_false}

ex_attached_exFO_lv :: SecOrder.SecOrder -> (Datatypes.Coq_list
                       SecOrder.FOvariable) -> Datatypes.Coq_bool
ex_attached_exFO_lv alpha lv =
  case lv of {
   Datatypes.Coq_nil -> Datatypes.Coq_false;
   Datatypes.Coq_cons y lv' ->
    case attached_exFO_x alpha y of {
     Datatypes.Coq_true -> Datatypes.Coq_true;
     Datatypes.Coq_false -> ex_attached_exFO_lv alpha lv'}}

x_occ_in_alpha :: SecOrder.SecOrder -> SecOrder.FOvariable ->
                  Datatypes.Coq_bool
x_occ_in_alpha alpha x =
  case alpha of {
   SecOrder.Coq_predSO _ y -> PeanoNat._Nat__eqb x y;
   SecOrder.Coq_relatSO y1 y2 ->
    case PeanoNat._Nat__eqb x y1 of {
     Datatypes.Coq_true -> Datatypes.Coq_true;
     Datatypes.Coq_false -> PeanoNat._Nat__eqb x y2};
   SecOrder.Coq_eqFO y1 y2 ->
    case PeanoNat._Nat__eqb x y1 of {
     Datatypes.Coq_true -> Datatypes.Coq_true;
     Datatypes.Coq_false -> PeanoNat._Nat__eqb x y2};
   SecOrder.Coq_allFO y beta ->
    case PeanoNat._Nat__eqb x y of {
     Datatypes.Coq_true -> Datatypes.Coq_true;
     Datatypes.Coq_false -> x_occ_in_alpha beta x};
   SecOrder.Coq_exFO y beta ->
    case PeanoNat._Nat__eqb x y of {
     Datatypes.Coq_true -> Datatypes.Coq_true;
     Datatypes.Coq_false -> x_occ_in_alpha beta x};
   SecOrder.Coq_negSO beta -> x_occ_in_alpha beta x;
   SecOrder.Coq_conjSO beta1 beta2 ->
    case x_occ_in_alpha beta1 x of {
     Datatypes.Coq_true -> Datatypes.Coq_true;
     Datatypes.Coq_false -> x_occ_in_alpha beta2 x};
   SecOrder.Coq_disjSO beta1 beta2 ->
    case x_occ_in_alpha beta1 x of {
     Datatypes.Coq_true -> Datatypes.Coq_true;
     Datatypes.Coq_false -> x_occ_in_alpha beta2 x};
   SecOrder.Coq_implSO beta1 beta2 ->
    case x_occ_in_alpha beta1 x of {
     Datatypes.Coq_true -> Datatypes.Coq_true;
     Datatypes.Coq_false -> x_occ_in_alpha beta2 x};
   SecOrder.Coq_allSO _ beta -> x_occ_in_alpha beta x;
   SecOrder.Coq_exSO _ beta -> x_occ_in_alpha beta x}

is_in_var :: SecOrder.FOvariable -> (Datatypes.Coq_list SecOrder.FOvariable)
             -> Datatypes.Coq_bool
is_in_var x lv =
  case lv of {
   Datatypes.Coq_nil -> Datatypes.Coq_false;
   Datatypes.Coq_cons y lv' ->
    case PeanoNat._Nat__eqb x y of {
     Datatypes.Coq_true -> Datatypes.Coq_true;
     Datatypes.Coq_false -> is_in_var x lv'}}

ex_attached_allFO_llv :: SecOrder.SecOrder -> (Datatypes.Coq_list
                         (Datatypes.Coq_list SecOrder.FOvariable)) ->
                         Datatypes.Coq_bool
ex_attached_allFO_llv alpha llv =
  case llv of {
   Datatypes.Coq_nil -> Datatypes.Coq_false;
   Datatypes.Coq_cons lv llv' ->
    case ex_attached_allFO_lv alpha lv of {
     Datatypes.Coq_true -> Datatypes.Coq_true;
     Datatypes.Coq_false -> ex_attached_allFO_llv alpha llv'}}

ex_attached_exFO_llv :: SecOrder.SecOrder -> (Datatypes.Coq_list
                        (Datatypes.Coq_list SecOrder.FOvariable)) ->
                        Datatypes.Coq_bool
ex_attached_exFO_llv alpha llv =
  case llv of {
   Datatypes.Coq_nil -> Datatypes.Coq_false;
   Datatypes.Coq_cons lv llv' ->
    case ex_attached_exFO_lv alpha lv of {
     Datatypes.Coq_true -> Datatypes.Coq_true;
     Datatypes.Coq_false -> ex_attached_exFO_llv alpha llv'}}

