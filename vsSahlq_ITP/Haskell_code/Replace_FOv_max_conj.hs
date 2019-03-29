module Replace_FOv_max_conj where

import qualified Prelude
import qualified Datatypes
import qualified Rep_Pred_FOv
import qualified SO_syntax
import qualified Max_min

replace_FOv_max_conj :: SO_syntax.SecOrder -> SO_syntax.SecOrder ->
                        SO_syntax.FOvariable -> SO_syntax.SecOrder
replace_FOv_max_conj alpha gamma x =
  Rep_Pred_FOv.replace_FOv alpha x (Datatypes.S
    (Max_min.max_FOv (SO_syntax.Coq_conjSO gamma (SO_syntax.Coq_exFO x
      alpha))))

replace_FOv_max_conj_var :: SO_syntax.SecOrder -> SO_syntax.SecOrder ->
                            SO_syntax.FOvariable -> SO_syntax.FOvariable
replace_FOv_max_conj_var alpha gamma x =
  Datatypes.S
    (Max_min.max_FOv (SO_syntax.Coq_conjSO gamma (SO_syntax.Coq_exFO x
      alpha)))

