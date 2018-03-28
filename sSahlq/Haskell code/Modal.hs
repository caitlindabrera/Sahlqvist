module Modal where

import qualified Prelude
import qualified Datatypes

type Coq_propvar =
  Datatypes.Coq_nat
  -- singleton inductive, whose constructor was pv
  
propvar_rect :: (Datatypes.Coq_nat -> a1) -> Coq_propvar -> a1
propvar_rect f p =
  f p

propvar_rec :: (Datatypes.Coq_nat -> a1) -> Coq_propvar -> a1
propvar_rec =
  propvar_rect

data Modal =
   Coq_atom Coq_propvar
 | Coq_mneg Modal
 | Coq_mconj Modal Modal
 | Coq_mdisj Modal Modal
 | Coq_mimpl Modal Modal
 | Coq_box Modal
 | Coq_diam Modal

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
   Coq_diam m0 -> f5 m0 (coq_Modal_rect f f0 f1 f2 f3 f4 f5 m0)}

coq_Modal_rec :: (Coq_propvar -> a1) -> (Modal -> a1 -> a1) -> (Modal -> a1
                 -> Modal -> a1 -> a1) -> (Modal -> a1 -> Modal -> a1 -> a1)
                 -> (Modal -> a1 -> Modal -> a1 -> a1) -> (Modal -> a1 -> a1)
                 -> (Modal -> a1 -> a1) -> Modal -> a1
coq_Modal_rec =
  coq_Modal_rect

pv_in :: Modal -> Datatypes.Coq_list Coq_propvar
pv_in phi =
  case phi of {
   Coq_atom p -> Datatypes.Coq_cons p Datatypes.Coq_nil;
   Coq_mneg psi -> pv_in psi;
   Coq_mconj psi1 psi2 -> Datatypes.app (pv_in psi1) (pv_in psi2);
   Coq_mdisj psi1 psi2 -> Datatypes.app (pv_in psi1) (pv_in psi2);
   Coq_mimpl psi1 psi2 -> Datatypes.app (pv_in psi1) (pv_in psi2);
   Coq_box psi -> pv_in psi;
   Coq_diam psi -> pv_in psi}

