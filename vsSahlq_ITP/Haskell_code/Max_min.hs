module Max_min where

import qualified Prelude
import qualified Datatypes
import qualified FOvars_in
import qualified Nat
import qualified SO_syntax

max_l :: (Datatypes.Coq_list Datatypes.Coq_nat) -> Datatypes.Coq_nat
max_l l =
  case l of {
   Datatypes.Coq_nil -> Datatypes.O;
   Datatypes.Coq_cons n l' -> Nat.max n (max_l l')}

min_l :: (Datatypes.Coq_list Datatypes.Coq_nat) -> Datatypes.Coq_nat
min_l l =
  case l of {
   Datatypes.Coq_nil -> Datatypes.O;
   Datatypes.Coq_cons n l' ->
    case l' of {
     Datatypes.Coq_nil -> n;
     Datatypes.Coq_cons _ _ -> Nat.min n (min_l l')}}

max_FOv_l :: (Datatypes.Coq_list SO_syntax.FOvariable) -> Datatypes.Coq_nat
max_FOv_l l =
  case l of {
   Datatypes.Coq_nil -> Datatypes.O;
   Datatypes.Coq_cons x l' -> Nat.max x (max_FOv_l l')}

max_FOv :: SO_syntax.SecOrder -> Datatypes.Coq_nat
max_FOv alpha =
  max_FOv_l (FOvars_in.coq_FOvars_in alpha)

deFOv :: SO_syntax.FOvariable -> Datatypes.Coq_nat
deFOv x =
  x

