module NList_egs where

import qualified Prelude
import qualified Datatypes
import qualified List_machinery_impl
import qualified SecOrder

__ :: any
__ = Prelude.error "Logical or arity value used"

nlist_full :: Datatypes.Coq_nat -> List_machinery_impl.Coq_nlist
              SecOrder.SecOrder
nlist_full n =
  case n of {
   Datatypes.O -> List_machinery_impl.Coq_niln;
   Datatypes.S m -> List_machinery_impl.Coq_consn m (SecOrder.Coq_eqFO
    (Datatypes.S Datatypes.O) (Datatypes.S Datatypes.O)) (nlist_full m)}

nlist_empty :: Datatypes.Coq_nat -> List_machinery_impl.Coq_nlist
               SecOrder.SecOrder
nlist_empty n =
  case n of {
   Datatypes.O -> List_machinery_impl.Coq_niln;
   Datatypes.S m -> List_machinery_impl.Coq_consn m (SecOrder.Coq_negSO
    (SecOrder.Coq_eqFO (Datatypes.S Datatypes.O) (Datatypes.S Datatypes.O)))
    (nlist_empty m)}

nlist_Var1 :: Datatypes.Coq_nat -> List_machinery_impl.Coq_nlist
              SecOrder.FOvariable
nlist_Var1 n =
  case n of {
   Datatypes.O -> List_machinery_impl.Coq_niln;
   Datatypes.S m -> List_machinery_impl.Coq_consn m (Datatypes.S Datatypes.O)
    (nlist_Var1 m)}

nlist_pa_f :: Datatypes.Coq_nat -> List_machinery_impl.Coq_nlist ()
nlist_pa_f n =
  case n of {
   Datatypes.O -> List_machinery_impl.Coq_niln;
   Datatypes.S m -> List_machinery_impl.Coq_consn m __ (nlist_pa_f m)}

nlist_pa_t :: Datatypes.Coq_nat -> List_machinery_impl.Coq_nlist ()
nlist_pa_t n =
  case n of {
   Datatypes.O -> List_machinery_impl.Coq_niln;
   Datatypes.S m -> List_machinery_impl.Coq_consn m __ (nlist_pa_t m)}

