module ConjSO_exFO_relatSO where

import qualified Prelude
import qualified Datatypes
import qualified SO_syntax

conjSO_exFO_relatSO :: SO_syntax.SecOrder -> Datatypes.Coq_bool
conjSO_exFO_relatSO alpha =
  case alpha of {
   SO_syntax.Coq_predSO _ _ -> Datatypes.Coq_true;
   SO_syntax.Coq_relatSO _ _ -> Datatypes.Coq_true;
   SO_syntax.Coq_exFO _ beta -> conjSO_exFO_relatSO beta;
   SO_syntax.Coq_conjSO beta1 beta2 ->
    case conjSO_exFO_relatSO beta1 of {
     Datatypes.Coq_true -> conjSO_exFO_relatSO beta2;
     Datatypes.Coq_false -> Datatypes.Coq_false};
   _ -> Datatypes.Coq_false}

