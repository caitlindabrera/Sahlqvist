module List_machinery_impl where

import qualified Prelude
import qualified Datatypes
import qualified PeanoNat
import qualified SecOrder

__ :: any
__ = Prelude.error "Logical or arity value used"

data Coq_nlist_pa w =
   Coq_niln_pa
 | Coq_consn_pa Datatypes.Coq_nat (Coq_nlist_pa w)

nlist_pa_rect :: a2 -> (Datatypes.Coq_nat -> () -> (Coq_nlist_pa a1) -> a2 ->
                 a2) -> Datatypes.Coq_nat -> (Coq_nlist_pa a1) -> a2
nlist_pa_rect f f0 _ n =
  case n of {
   Coq_niln_pa -> f;
   Coq_consn_pa n0 n1 -> f0 n0 __ n1 (nlist_pa_rect f f0 n0 n1)}

nlist_pa_rec :: a2 -> (Datatypes.Coq_nat -> () -> (Coq_nlist_pa a1) -> a2 ->
                a2) -> Datatypes.Coq_nat -> (Coq_nlist_pa a1) -> a2
nlist_pa_rec =
  nlist_pa_rect

data Coq_nlist a =
   Coq_niln
 | Coq_consn Datatypes.Coq_nat a (Coq_nlist a)

nlist_rect :: a2 -> (Datatypes.Coq_nat -> a1 -> (Coq_nlist a1) -> a2 -> a2)
              -> Datatypes.Coq_nat -> (Coq_nlist a1) -> a2
nlist_rect f f0 _ n =
  case n of {
   Coq_niln -> f;
   Coq_consn n0 y n1 -> f0 n0 y n1 (nlist_rect f f0 n0 n1)}

nlist_rec :: a2 -> (Datatypes.Coq_nat -> a1 -> (Coq_nlist a1) -> a2 -> a2) ->
             Datatypes.Coq_nat -> (Coq_nlist a1) -> a2
nlist_rec =
  nlist_rect

nlist_list_pa :: Datatypes.Coq_nat -> (Coq_nlist_pa a1) -> Datatypes.Coq_list
                 ()
nlist_list_pa _ ln =
  case ln of {
   Coq_niln_pa -> Datatypes.Coq_nil;
   Coq_consn_pa m ln' -> Datatypes.Coq_cons __ (nlist_list_pa m ln')}

list_nlist :: (Datatypes.Coq_list a1) -> Coq_nlist a1
list_nlist l =
  case l of {
   Datatypes.Coq_nil -> Coq_niln;
   Datatypes.Coq_cons p l' -> Coq_consn (Datatypes.length l') p
    (list_nlist l')}

nlist_list :: Datatypes.Coq_nat -> (Coq_nlist a1) -> Datatypes.Coq_list a1
nlist_list _ ln =
  case ln of {
   Coq_niln -> Datatypes.Coq_nil;
   Coq_consn m p l' -> Datatypes.Coq_cons p (nlist_list m l')}

list_rem :: (Datatypes.Coq_list SecOrder.Coq_predicate) -> Datatypes.Coq_nat
            -> Datatypes.Coq_list SecOrder.Coq_predicate
list_rem l n =
  case l of {
   Datatypes.Coq_nil -> Datatypes.Coq_nil;
   Datatypes.Coq_cons p l' ->
    case PeanoNat._Nat__eqb n p of {
     Datatypes.Coq_true -> list_rem l' n;
     Datatypes.Coq_false -> Datatypes.Coq_cons p (list_rem l' n)}}

list_without :: (Datatypes.Coq_list SecOrder.Coq_predicate) ->
                (Datatypes.Coq_list SecOrder.Coq_predicate) ->
                Datatypes.Coq_list SecOrder.Coq_predicate
list_without l1 l2 =
  case l2 of {
   Datatypes.Coq_nil -> l1;
   Datatypes.Coq_cons p l2' -> list_without (list_rem l1 p) l2'}

