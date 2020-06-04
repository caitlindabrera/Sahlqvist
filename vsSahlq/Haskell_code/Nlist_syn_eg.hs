module Nlist_syn_eg where

import qualified Prelude
import qualified Datatypes
import qualified SO_syntax
import qualified Nlist_syn

nlist_full :: Datatypes.Coq_nat -> Nlist_syn.Coq_nlist SO_syntax.SecOrder
nlist_full n =
  case n of {
   Datatypes.O -> Nlist_syn.Coq_niln;
   Datatypes.S m -> Nlist_syn.Coq_consn m (SO_syntax.Coq_eqFO (Datatypes.S
    Datatypes.O) (Datatypes.S Datatypes.O)) (nlist_full m)}

nlist_empty :: Datatypes.Coq_nat -> Nlist_syn.Coq_nlist SO_syntax.SecOrder
nlist_empty n =
  case n of {
   Datatypes.O -> Nlist_syn.Coq_niln;
   Datatypes.S m -> Nlist_syn.Coq_consn m (SO_syntax.Coq_negSO
    (SO_syntax.Coq_eqFO (Datatypes.S Datatypes.O) (Datatypes.S Datatypes.O)))
    (nlist_empty m)}

nlist_var :: Datatypes.Coq_nat -> SO_syntax.FOvariable -> Nlist_syn.Coq_nlist
             SO_syntax.FOvariable
nlist_var n x =
  case n of {
   Datatypes.O -> Nlist_syn.Coq_niln;
   Datatypes.S m -> Nlist_syn.Coq_consn m x (nlist_var m x)}

list_var :: Datatypes.Coq_nat -> SO_syntax.FOvariable -> Datatypes.Coq_list
            SO_syntax.FOvariable
list_var n x =
  case n of {
   Datatypes.O -> Datatypes.Coq_nil;
   Datatypes.S m -> Datatypes.Coq_cons x (list_var m x)}

nlist_P :: Datatypes.Coq_nat -> SO_syntax.Coq_predicate ->
           Nlist_syn.Coq_nlist SO_syntax.Coq_predicate
nlist_P n p =
  case n of {
   Datatypes.O -> Nlist_syn.Coq_niln;
   Datatypes.S m -> Nlist_syn.Coq_consn m p (nlist_P m p)}

