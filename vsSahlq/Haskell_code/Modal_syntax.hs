module Modal_syntax where

import qualified Prelude
import qualified Datatypes
import qualified Logic
import qualified PeanoNat
import qualified Specif

type Coq_propvar =
  Datatypes.Coq_nat
  -- singleton inductive, whose constructor was pv
  
propvar_rect :: (Datatypes.Coq_nat -> a1) -> Coq_propvar -> a1
propvar_rect f =
  f

propvar_rec :: (Datatypes.Coq_nat -> a1) -> Coq_propvar -> a1
propvar_rec =
  propvar_rect

propvar_dec :: Coq_propvar -> Coq_propvar -> Specif.Coq_sumbool
propvar_dec p0 q0 =
  let {s = PeanoNat._Nat__eq_dec p0 q0} in
  case s of {
   Specif.Coq_left -> Logic.eq_rec_r q0 Specif.Coq_left p0;
   Specif.Coq_right -> Specif.Coq_right}

data Modal =
   Coq_atom Coq_propvar
 | Coq_mneg Modal
 | Coq_mconj Modal Modal
 | Coq_mdisj Modal Modal
 | Coq_mimpl Modal Modal
 | Coq_box Modal
 | Coq_dia Modal

coq_Modal_rect :: (Coq_propvar -> a1) -> (Modal -> a1 -> a1) -> (Modal -> a1
                  -> Modal -> a1 -> a1) -> (Modal -> a1 -> Modal -> a1 -> a1)
                  -> (Modal -> a1 -> Modal -> a1 -> a1) -> (Modal -> a1 ->
                  a1) -> (Modal -> a1 -> a1) -> Modal -> a1
coq_Modal_rect f f0 f1 f2 f3 f4 f5 m =
  case m of {
   Coq_atom p -> f p;
   Coq_mneg m0 -> f0 m0 (coq_Modal_rect f f0 f1 f2 f3 f4 f5 m0);
   Coq_mconj m0 m1 ->
    f1 m0 (coq_Modal_rect f f0 f1 f2 f3 f4 f5 m0) m1
      (coq_Modal_rect f f0 f1 f2 f3 f4 f5 m1);
   Coq_mdisj m0 m1 ->
    f2 m0 (coq_Modal_rect f f0 f1 f2 f3 f4 f5 m0) m1
      (coq_Modal_rect f f0 f1 f2 f3 f4 f5 m1);
   Coq_mimpl m0 m1 ->
    f3 m0 (coq_Modal_rect f f0 f1 f2 f3 f4 f5 m0) m1
      (coq_Modal_rect f f0 f1 f2 f3 f4 f5 m1);
   Coq_box m0 -> f4 m0 (coq_Modal_rect f f0 f1 f2 f3 f4 f5 m0);
   Coq_dia m0 -> f5 m0 (coq_Modal_rect f f0 f1 f2 f3 f4 f5 m0)}

coq_Modal_rec :: (Coq_propvar -> a1) -> (Modal -> a1 -> a1) -> (Modal -> a1
                 -> Modal -> a1 -> a1) -> (Modal -> a1 -> Modal -> a1 -> a1)
                 -> (Modal -> a1 -> Modal -> a1 -> a1) -> (Modal -> a1 -> a1)
                 -> (Modal -> a1 -> a1) -> Modal -> a1
coq_Modal_rec =
  coq_Modal_rect

calc_ante_modal :: Modal -> Modal
calc_ante_modal _UU03d5_ =
  case _UU03d5_ of {
   Coq_mimpl _UU03c8_1 _ -> _UU03c8_1;
   _ -> _UU03d5_}

calc_cons_modal :: Modal -> Modal
calc_cons_modal _UU03d5_ =
  case _UU03d5_ of {
   Coq_mimpl _ _UU03c8_2 -> _UU03c8_2;
   _ -> _UU03d5_}

