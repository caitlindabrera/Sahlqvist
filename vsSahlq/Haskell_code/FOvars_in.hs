module FOvars_in where

import qualified Prelude
import qualified Datatypes
import qualified List
import qualified SO_syntax
import qualified Specif

coq_FOvars_in :: SO_syntax.SecOrder -> Datatypes.Coq_list
                 SO_syntax.FOvariable
coq_FOvars_in alpha =
  case alpha of {
   SO_syntax.Coq_predSO _ x -> Datatypes.Coq_cons x Datatypes.Coq_nil;
   SO_syntax.Coq_relatSO x y -> Datatypes.Coq_cons x (Datatypes.Coq_cons y
    Datatypes.Coq_nil);
   SO_syntax.Coq_eqFO x y -> Datatypes.Coq_cons x (Datatypes.Coq_cons y
    Datatypes.Coq_nil);
   SO_syntax.Coq_allFO x beta -> Datatypes.Coq_cons x (coq_FOvars_in beta);
   SO_syntax.Coq_exFO x beta -> Datatypes.Coq_cons x (coq_FOvars_in beta);
   SO_syntax.Coq_negSO beta -> coq_FOvars_in beta;
   SO_syntax.Coq_conjSO beta1 beta2 ->
    Datatypes.app (coq_FOvars_in beta1) (coq_FOvars_in beta2);
   SO_syntax.Coq_disjSO beta1 beta2 ->
    Datatypes.app (coq_FOvars_in beta1) (coq_FOvars_in beta2);
   SO_syntax.Coq_implSO beta1 beta2 ->
    Datatypes.app (coq_FOvars_in beta1) (coq_FOvars_in beta2);
   SO_syntax.Coq_allSO _ beta -> coq_FOvars_in beta;
   SO_syntax.Coq_exSO _ beta -> coq_FOvars_in beta}

list_closed_exFO :: SO_syntax.SecOrder -> (Datatypes.Coq_list
                    SO_syntax.FOvariable) -> SO_syntax.SecOrder
list_closed_exFO alpha l =
  case l of {
   Datatypes.Coq_nil -> alpha;
   Datatypes.Coq_cons x ls -> SO_syntax.Coq_exFO x
    (list_closed_exFO alpha ls)}

list_closed_allFO :: SO_syntax.SecOrder -> (Datatypes.Coq_list
                     SO_syntax.FOvariable) -> SO_syntax.SecOrder
list_closed_allFO alpha l =
  case l of {
   Datatypes.Coq_nil -> alpha;
   Datatypes.Coq_cons x ls -> SO_syntax.Coq_allFO x
    (list_closed_allFO alpha ls)}

strip_exFO :: SO_syntax.SecOrder -> Datatypes.Coq_nat -> SO_syntax.SecOrder
strip_exFO alpha n =
  case n of {
   Datatypes.O -> alpha;
   Datatypes.S m ->
    case alpha of {
     SO_syntax.Coq_exFO _ beta -> strip_exFO beta m;
     _ -> alpha}}

strip_exFO_list :: SO_syntax.SecOrder -> Datatypes.Coq_nat ->
                   Datatypes.Coq_list SO_syntax.FOvariable
strip_exFO_list alpha n =
  case n of {
   Datatypes.O -> Datatypes.Coq_nil;
   Datatypes.S m ->
    case alpha of {
     SO_syntax.Coq_exFO x beta -> Datatypes.Coq_cons x
      (strip_exFO_list beta m);
     _ -> Datatypes.Coq_nil}}

coq_FOv_att_P :: SO_syntax.SecOrder -> SO_syntax.Coq_predicate ->
                 Datatypes.Coq_list SO_syntax.FOvariable
coq_FOv_att_P alpha p =
  case alpha of {
   SO_syntax.Coq_predSO q x ->
    case SO_syntax.predicate_dec p q of {
     Specif.Coq_left -> Datatypes.Coq_cons x Datatypes.Coq_nil;
     Specif.Coq_right -> Datatypes.Coq_nil};
   SO_syntax.Coq_allFO _ beta -> coq_FOv_att_P beta p;
   SO_syntax.Coq_exFO _ beta -> coq_FOv_att_P beta p;
   SO_syntax.Coq_negSO beta -> coq_FOv_att_P beta p;
   SO_syntax.Coq_conjSO beta1 beta2 ->
    Datatypes.app (coq_FOv_att_P beta1 p) (coq_FOv_att_P beta2 p);
   SO_syntax.Coq_disjSO beta1 beta2 ->
    Datatypes.app (coq_FOv_att_P beta1 p) (coq_FOv_att_P beta2 p);
   SO_syntax.Coq_implSO beta1 beta2 ->
    Datatypes.app (coq_FOv_att_P beta1 p) (coq_FOv_att_P beta2 p);
   SO_syntax.Coq_allSO _ beta -> coq_FOv_att_P beta p;
   SO_syntax.Coq_exSO _ beta -> coq_FOv_att_P beta p;
   _ -> Datatypes.Coq_nil}

coq_FOv_att_P_l :: SO_syntax.SecOrder -> (Datatypes.Coq_list
                   SO_syntax.Coq_predicate) -> Datatypes.Coq_list
                   (Datatypes.Coq_list SO_syntax.FOvariable)
coq_FOv_att_P_l alpha lP =
  case lP of {
   Datatypes.Coq_nil -> Datatypes.Coq_nil;
   Datatypes.Coq_cons p lP' -> Datatypes.Coq_cons (coq_FOv_att_P alpha p)
    (coq_FOv_att_P_l alpha lP')}

rem_FOv :: SO_syntax.FOvariable -> (Datatypes.Coq_list SO_syntax.FOvariable)
           -> Datatypes.Coq_list SO_syntax.FOvariable
rem_FOv x l =
  List.remove SO_syntax.coq_FOvariable_dec x l

coq_FOvify :: (Datatypes.Coq_list Datatypes.Coq_nat) -> Datatypes.Coq_list
              SO_syntax.FOvariable
coq_FOvify ln =
  case ln of {
   Datatypes.Coq_nil -> Datatypes.Coq_nil;
   Datatypes.Coq_cons x ln' -> Datatypes.Coq_cons x (coq_FOvify ln')}

var_in_SO_dec :: SO_syntax.SecOrder -> SO_syntax.FOvariable ->
                 Specif.Coq_sumbool
var_in_SO_dec alpha x =
  List.in_dec SO_syntax.coq_FOvariable_dec x (coq_FOvars_in alpha)

ex_nil_in_llv :: (Datatypes.Coq_list
                 (Datatypes.Coq_list SO_syntax.FOvariable)) ->
                 Datatypes.Coq_bool
ex_nil_in_llv llv =
  case llv of {
   Datatypes.Coq_nil -> Datatypes.Coq_false;
   Datatypes.Coq_cons l llv' ->
    case l of {
     Datatypes.Coq_nil -> Datatypes.Coq_true;
     Datatypes.Coq_cons _ _ -> ex_nil_in_llv llv'}}

ex_FOvar_var_ll :: SO_syntax.FOvariable -> (Datatypes.Coq_list
                   (Datatypes.Coq_list SO_syntax.FOvariable)) ->
                   Datatypes.Coq_bool
ex_FOvar_var_ll x llx =
  case llx of {
   Datatypes.Coq_nil -> Datatypes.Coq_false;
   Datatypes.Coq_cons lx llx' ->
    case List.in_dec SO_syntax.coq_FOvariable_dec x lx of {
     Specif.Coq_left -> Datatypes.Coq_true;
     Specif.Coq_right -> ex_FOvar_var_ll x llx'}}

