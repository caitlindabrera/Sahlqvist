module Rep_Pred_FOv where

import qualified Prelude
import qualified Datatypes
import qualified SO_syntax
import qualified Specif

replace_FOv :: SO_syntax.SecOrder -> SO_syntax.FOvariable ->
               SO_syntax.FOvariable -> SO_syntax.SecOrder
replace_FOv alpha x y =
  case alpha of {
   SO_syntax.Coq_predSO p z ->
    case SO_syntax.coq_FOvariable_dec x z of {
     Specif.Coq_left -> SO_syntax.Coq_predSO p y;
     Specif.Coq_right -> alpha};
   SO_syntax.Coq_relatSO z1 z2 ->
    case SO_syntax.coq_FOvariable_dec x z1 of {
     Specif.Coq_left ->
      case SO_syntax.coq_FOvariable_dec x z2 of {
       Specif.Coq_left -> SO_syntax.Coq_relatSO y y;
       Specif.Coq_right -> SO_syntax.Coq_relatSO y z2};
     Specif.Coq_right ->
      case SO_syntax.coq_FOvariable_dec x z2 of {
       Specif.Coq_left -> SO_syntax.Coq_relatSO z1 y;
       Specif.Coq_right -> alpha}};
   SO_syntax.Coq_eqFO z1 z2 ->
    case SO_syntax.coq_FOvariable_dec x z1 of {
     Specif.Coq_left ->
      case SO_syntax.coq_FOvariable_dec x z2 of {
       Specif.Coq_left -> SO_syntax.Coq_eqFO y y;
       Specif.Coq_right -> SO_syntax.Coq_eqFO y z2};
     Specif.Coq_right ->
      case SO_syntax.coq_FOvariable_dec x z2 of {
       Specif.Coq_left -> SO_syntax.Coq_eqFO z1 y;
       Specif.Coq_right -> alpha}};
   SO_syntax.Coq_allFO z beta ->
    case SO_syntax.coq_FOvariable_dec x z of {
     Specif.Coq_left -> SO_syntax.Coq_allFO y (replace_FOv beta x y);
     Specif.Coq_right -> SO_syntax.Coq_allFO z (replace_FOv beta x y)};
   SO_syntax.Coq_exFO z beta ->
    case SO_syntax.coq_FOvariable_dec x z of {
     Specif.Coq_left -> SO_syntax.Coq_exFO y (replace_FOv beta x y);
     Specif.Coq_right -> SO_syntax.Coq_exFO z (replace_FOv beta x y)};
   SO_syntax.Coq_negSO beta -> SO_syntax.Coq_negSO (replace_FOv beta x y);
   SO_syntax.Coq_conjSO beta1 beta2 -> SO_syntax.Coq_conjSO
    (replace_FOv beta1 x y) (replace_FOv beta2 x y);
   SO_syntax.Coq_disjSO beta1 beta2 -> SO_syntax.Coq_disjSO
    (replace_FOv beta1 x y) (replace_FOv beta2 x y);
   SO_syntax.Coq_implSO beta1 beta2 -> SO_syntax.Coq_implSO
    (replace_FOv beta1 x y) (replace_FOv beta2 x y);
   SO_syntax.Coq_allSO p beta -> SO_syntax.Coq_allSO p (replace_FOv beta x y);
   SO_syntax.Coq_exSO p beta -> SO_syntax.Coq_exSO p (replace_FOv beta x y)}

replace_pred :: SO_syntax.SecOrder -> SO_syntax.Coq_predicate ->
                SO_syntax.FOvariable -> SO_syntax.SecOrder ->
                SO_syntax.SecOrder
replace_pred alpha p x cond =
  case alpha of {
   SO_syntax.Coq_predSO q z ->
    case SO_syntax.predicate_dec p q of {
     Specif.Coq_left -> replace_FOv cond x z;
     Specif.Coq_right -> alpha};
   SO_syntax.Coq_allFO z beta -> SO_syntax.Coq_allFO z
    (replace_pred beta p x cond);
   SO_syntax.Coq_exFO z beta -> SO_syntax.Coq_exFO z
    (replace_pred beta p x cond);
   SO_syntax.Coq_negSO beta -> SO_syntax.Coq_negSO
    (replace_pred beta p x cond);
   SO_syntax.Coq_conjSO beta1 beta2 -> SO_syntax.Coq_conjSO
    (replace_pred beta1 p x cond) (replace_pred beta2 p x cond);
   SO_syntax.Coq_disjSO beta1 beta2 -> SO_syntax.Coq_disjSO
    (replace_pred beta1 p x cond) (replace_pred beta2 p x cond);
   SO_syntax.Coq_implSO beta1 beta2 -> SO_syntax.Coq_implSO
    (replace_pred beta1 p x cond) (replace_pred beta2 p x cond);
   SO_syntax.Coq_allSO q beta ->
    case SO_syntax.predicate_dec p q of {
     Specif.Coq_left -> replace_pred beta p x cond;
     Specif.Coq_right -> SO_syntax.Coq_allSO q (replace_pred beta p x cond)};
   SO_syntax.Coq_exSO q beta ->
    case SO_syntax.predicate_dec p q of {
     Specif.Coq_left -> replace_pred beta p x cond;
     Specif.Coq_right -> SO_syntax.Coq_exSO q (replace_pred beta p x cond)};
   _ -> alpha}

replace_pred_l :: SO_syntax.SecOrder -> (Datatypes.Coq_list
                  SO_syntax.Coq_predicate) -> (Datatypes.Coq_list
                  SO_syntax.FOvariable) -> (Datatypes.Coq_list
                  SO_syntax.SecOrder) -> SO_syntax.SecOrder
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

