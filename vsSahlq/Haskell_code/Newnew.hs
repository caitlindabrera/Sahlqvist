module Newnew where

import qualified Prelude
import qualified Datatypes
import qualified Rep_Pred_FOv
import qualified SO_syntax

newnew_pre :: SO_syntax.SecOrder -> (Datatypes.Coq_list SO_syntax.FOvariable)
              -> (Datatypes.Coq_list Datatypes.Coq_nat) -> SO_syntax.SecOrder
newnew_pre alpha lv ln =
  case lv of {
   Datatypes.Coq_nil -> alpha;
   Datatypes.Coq_cons x lv' ->
    case ln of {
     Datatypes.Coq_nil -> alpha;
     Datatypes.Coq_cons n ln' ->
      Rep_Pred_FOv.replace_FOv (newnew_pre alpha lv' ln') x n}}

