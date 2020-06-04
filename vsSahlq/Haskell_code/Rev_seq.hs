module Rev_seq where

import qualified Prelude
import qualified Datatypes
import qualified Nat

rev_seq :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_list
           Datatypes.Coq_nat
rev_seq start length =
  case length of {
   Datatypes.O -> Datatypes.Coq_nil;
   Datatypes.S n -> Datatypes.Coq_cons (Nat.add start n) (rev_seq start n)}

