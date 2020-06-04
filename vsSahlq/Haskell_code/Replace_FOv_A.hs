module Replace_FOv_A where

import qualified Prelude
import qualified Datatypes
import qualified FOvars_in
import qualified SO_syntax
import qualified Replace_FOv_max_conj

replace_FOv_A_pre :: SO_syntax.SecOrder -> SO_syntax.SecOrder ->
                     (Datatypes.Coq_list SO_syntax.FOvariable) ->
                     Datatypes.Coq_nat -> SO_syntax.SecOrder
replace_FOv_A_pre alpha gamma lv n =
  case n of {
   Datatypes.O -> alpha;
   Datatypes.S m ->
    case lv of {
     Datatypes.Coq_nil -> alpha;
     Datatypes.Coq_cons x lv' ->
      replace_FOv_A_pre
        (FOvars_in.strip_exFO
          (Replace_FOv_max_conj.replace_FOv_max_conj
            (FOvars_in.list_closed_exFO alpha lv') gamma x)
          (Datatypes.length lv')) gamma
        (FOvars_in.strip_exFO_list
          (Replace_FOv_max_conj.replace_FOv_max_conj
            (FOvars_in.list_closed_exFO alpha lv') gamma x)
          (Datatypes.length lv')) m}}

replace_FOv_A :: SO_syntax.SecOrder -> SO_syntax.SecOrder ->
                 (Datatypes.Coq_list SO_syntax.FOvariable) ->
                 SO_syntax.SecOrder
replace_FOv_A alpha gamma lv =
  replace_FOv_A_pre alpha gamma lv (Datatypes.length lv)

replace_FOv_A_list_pre :: SO_syntax.SecOrder -> SO_syntax.SecOrder ->
                          (Datatypes.Coq_list SO_syntax.FOvariable) ->
                          Datatypes.Coq_nat -> Datatypes.Coq_list
                          SO_syntax.FOvariable
replace_FOv_A_list_pre alpha gamma lv n =
  case n of {
   Datatypes.O -> Datatypes.Coq_nil;
   Datatypes.S m ->
    case lv of {
     Datatypes.Coq_nil -> Datatypes.Coq_nil;
     Datatypes.Coq_cons x lv' -> Datatypes.Coq_cons
      (Replace_FOv_max_conj.replace_FOv_max_conj_var
        (FOvars_in.list_closed_exFO alpha lv') gamma x)
      (replace_FOv_A_list_pre
        (FOvars_in.strip_exFO
          (Replace_FOv_max_conj.replace_FOv_max_conj
            (FOvars_in.list_closed_exFO alpha lv') gamma x)
          (Datatypes.length lv')) gamma
        (FOvars_in.strip_exFO_list
          (Replace_FOv_max_conj.replace_FOv_max_conj
            (FOvars_in.list_closed_exFO alpha lv') gamma x)
          (Datatypes.length lv')) m)}}

replace_FOv_A_list :: SO_syntax.SecOrder -> SO_syntax.SecOrder ->
                      (Datatypes.Coq_list SO_syntax.FOvariable) ->
                      Datatypes.Coq_list SO_syntax.FOvariable
replace_FOv_A_list alpha gamma lv =
  replace_FOv_A_list_pre alpha gamma lv (Datatypes.length lv)

