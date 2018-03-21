module Rep_Pred_FOv where

import qualified Prelude
import qualified Datatypes
import qualified PeanoNat
import qualified SecOrder

replace_FOv :: SecOrder.SecOrder -> SecOrder.FOvariable ->
               SecOrder.FOvariable -> SecOrder.SecOrder
replace_FOv alpha x y =
  case alpha of {
   SecOrder.Coq_predSO p f ->
    case PeanoNat._Nat__eqb x f of {
     Datatypes.Coq_true -> SecOrder.Coq_predSO p y;
     Datatypes.Coq_false -> alpha};
   SecOrder.Coq_relatSO f f0 ->
    case PeanoNat._Nat__eqb x f of {
     Datatypes.Coq_true ->
      case PeanoNat._Nat__eqb x f0 of {
       Datatypes.Coq_true -> SecOrder.Coq_relatSO y y;
       Datatypes.Coq_false -> SecOrder.Coq_relatSO y f0};
     Datatypes.Coq_false ->
      case PeanoNat._Nat__eqb x f0 of {
       Datatypes.Coq_true -> SecOrder.Coq_relatSO f y;
       Datatypes.Coq_false -> alpha}};
   SecOrder.Coq_eqFO f f0 ->
    case PeanoNat._Nat__eqb x f of {
     Datatypes.Coq_true ->
      case PeanoNat._Nat__eqb x f0 of {
       Datatypes.Coq_true -> SecOrder.Coq_eqFO y y;
       Datatypes.Coq_false -> SecOrder.Coq_eqFO y f0};
     Datatypes.Coq_false ->
      case PeanoNat._Nat__eqb x f0 of {
       Datatypes.Coq_true -> SecOrder.Coq_eqFO f y;
       Datatypes.Coq_false -> alpha}};
   SecOrder.Coq_allFO f beta ->
    case PeanoNat._Nat__eqb x f of {
     Datatypes.Coq_true -> SecOrder.Coq_allFO y (replace_FOv beta x y);
     Datatypes.Coq_false -> SecOrder.Coq_allFO f (replace_FOv beta x y)};
   SecOrder.Coq_exFO f beta ->
    case PeanoNat._Nat__eqb x f of {
     Datatypes.Coq_true -> SecOrder.Coq_exFO y (replace_FOv beta x y);
     Datatypes.Coq_false -> SecOrder.Coq_exFO f (replace_FOv beta x y)};
   SecOrder.Coq_negSO beta -> SecOrder.Coq_negSO (replace_FOv beta x y);
   SecOrder.Coq_conjSO beta1 beta2 -> SecOrder.Coq_conjSO
    (replace_FOv beta1 x y) (replace_FOv beta2 x y);
   SecOrder.Coq_disjSO beta1 beta2 -> SecOrder.Coq_disjSO
    (replace_FOv beta1 x y) (replace_FOv beta2 x y);
   SecOrder.Coq_implSO beta1 beta2 -> SecOrder.Coq_implSO
    (replace_FOv beta1 x y) (replace_FOv beta2 x y);
   SecOrder.Coq_allSO p beta -> SecOrder.Coq_allSO p (replace_FOv beta x y);
   SecOrder.Coq_exSO p beta -> SecOrder.Coq_exSO p (replace_FOv beta x y)}

replace_pred :: SecOrder.SecOrder -> SecOrder.Coq_predicate ->
                SecOrder.FOvariable -> SecOrder.SecOrder -> SecOrder.SecOrder
replace_pred alpha p x cond =
  case alpha of {
   SecOrder.Coq_predSO p0 f ->
    case PeanoNat._Nat__eqb p p0 of {
     Datatypes.Coq_true -> replace_FOv cond x f;
     Datatypes.Coq_false -> alpha};
   SecOrder.Coq_allFO f beta -> SecOrder.Coq_allFO f
    (replace_pred beta p x cond);
   SecOrder.Coq_exFO f beta -> SecOrder.Coq_exFO f
    (replace_pred beta p x cond);
   SecOrder.Coq_negSO beta -> SecOrder.Coq_negSO (replace_pred beta p x cond);
   SecOrder.Coq_conjSO beta1 beta2 -> SecOrder.Coq_conjSO
    (replace_pred beta1 p x cond) (replace_pred beta2 p x cond);
   SecOrder.Coq_disjSO beta1 beta2 -> SecOrder.Coq_disjSO
    (replace_pred beta1 p x cond) (replace_pred beta2 p x cond);
   SecOrder.Coq_implSO beta1 beta2 -> SecOrder.Coq_implSO
    (replace_pred beta1 p x cond) (replace_pred beta2 p x cond);
   SecOrder.Coq_allSO p0 beta ->
    case PeanoNat._Nat__eqb p p0 of {
     Datatypes.Coq_true -> replace_pred beta p x cond;
     Datatypes.Coq_false -> SecOrder.Coq_allSO p0
      (replace_pred beta p x cond)};
   SecOrder.Coq_exSO p0 beta ->
    case PeanoNat._Nat__eqb p p0 of {
     Datatypes.Coq_true -> replace_pred beta p x cond;
     Datatypes.Coq_false -> SecOrder.Coq_exSO p0 (replace_pred beta p x cond)};
   _ -> alpha}

replace_pred_l :: SecOrder.SecOrder -> (Datatypes.Coq_list
                  SecOrder.Coq_predicate) -> (Datatypes.Coq_list
                  SecOrder.FOvariable) -> (Datatypes.Coq_list
                  SecOrder.SecOrder) -> SecOrder.SecOrder
replace_pred_l alpha lP lx lcond =
  case lP of {
   Datatypes.Coq_nil -> alpha;
   Datatypes.Coq_cons p lP' ->
    case lx of {
     Datatypes.Coq_nil -> alpha;
     Datatypes.Coq_cons x lx' ->
      case lcond of {
       Datatypes.Coq_nil -> alpha;
       Datatypes.Coq_cons cond lcond' ->
        replace_pred (replace_pred_l alpha lP' lx' lcond') p x cond}}}

