module SecOrder where

import qualified Prelude
import qualified Datatypes
import qualified PeanoNat

type Coq_predicate =
  Datatypes.Coq_nat
  -- singleton inductive, whose constructor was Pred
  
predicate_rect :: (Datatypes.Coq_nat -> a1) -> Coq_predicate -> a1
predicate_rect f p =
  f p

predicate_rec :: (Datatypes.Coq_nat -> a1) -> Coq_predicate -> a1
predicate_rec =
  predicate_rect

type FOvariable =
  Datatypes.Coq_nat
  -- singleton inductive, whose constructor was Var
  
coq_FOvariable_rect :: (Datatypes.Coq_nat -> a1) -> FOvariable -> a1
coq_FOvariable_rect f f0 =
  f f0

coq_FOvariable_rec :: (Datatypes.Coq_nat -> a1) -> FOvariable -> a1
coq_FOvariable_rec =
  coq_FOvariable_rect

data SecOrder =
   Coq_predSO Coq_predicate FOvariable
 | Coq_relatSO FOvariable FOvariable
 | Coq_eqFO FOvariable FOvariable
 | Coq_allFO FOvariable SecOrder
 | Coq_exFO FOvariable SecOrder
 | Coq_negSO SecOrder
 | Coq_conjSO SecOrder SecOrder
 | Coq_disjSO SecOrder SecOrder
 | Coq_implSO SecOrder SecOrder
 | Coq_allSO Coq_predicate SecOrder
 | Coq_exSO Coq_predicate SecOrder

coq_SecOrder_rect :: (Coq_predicate -> FOvariable -> a1) -> (FOvariable ->
                     FOvariable -> a1) -> (FOvariable -> FOvariable -> a1) ->
                     (FOvariable -> SecOrder -> a1 -> a1) -> (FOvariable ->
                     SecOrder -> a1 -> a1) -> (SecOrder -> a1 -> a1) ->
                     (SecOrder -> a1 -> SecOrder -> a1 -> a1) -> (SecOrder ->
                     a1 -> SecOrder -> a1 -> a1) -> (SecOrder -> a1 ->
                     SecOrder -> a1 -> a1) -> (Coq_predicate -> SecOrder ->
                     a1 -> a1) -> (Coq_predicate -> SecOrder -> a1 -> a1) ->
                     SecOrder -> a1
coq_SecOrder_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 s =
  case s of {
   Coq_predSO p f10 -> f p f10;
   Coq_relatSO f10 f11 -> f0 f10 f11;
   Coq_eqFO f10 f11 -> f1 f10 f11;
   Coq_allFO f10 s0 ->
    f2 f10 s0 (coq_SecOrder_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 s0);
   Coq_exFO f10 s0 ->
    f3 f10 s0 (coq_SecOrder_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 s0);
   Coq_negSO s0 ->
    f4 s0 (coq_SecOrder_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 s0);
   Coq_conjSO s0 s1 ->
    f5 s0 (coq_SecOrder_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 s0) s1
      (coq_SecOrder_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 s1);
   Coq_disjSO s0 s1 ->
    f6 s0 (coq_SecOrder_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 s0) s1
      (coq_SecOrder_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 s1);
   Coq_implSO s0 s1 ->
    f7 s0 (coq_SecOrder_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 s0) s1
      (coq_SecOrder_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 s1);
   Coq_allSO p s0 ->
    f8 p s0 (coq_SecOrder_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 s0);
   Coq_exSO p s0 ->
    f9 p s0 (coq_SecOrder_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 s0)}

coq_SecOrder_rec :: (Coq_predicate -> FOvariable -> a1) -> (FOvariable ->
                    FOvariable -> a1) -> (FOvariable -> FOvariable -> a1) ->
                    (FOvariable -> SecOrder -> a1 -> a1) -> (FOvariable ->
                    SecOrder -> a1 -> a1) -> (SecOrder -> a1 -> a1) ->
                    (SecOrder -> a1 -> SecOrder -> a1 -> a1) -> (SecOrder ->
                    a1 -> SecOrder -> a1 -> a1) -> (SecOrder -> a1 ->
                    SecOrder -> a1 -> a1) -> (Coq_predicate -> SecOrder -> a1
                    -> a1) -> (Coq_predicate -> SecOrder -> a1 -> a1) ->
                    SecOrder -> a1
coq_SecOrder_rec =
  coq_SecOrder_rect

altered_Iv :: (FOvariable -> a1) -> a1 -> FOvariable -> FOvariable -> a1
altered_Iv iv d x y =
  case PeanoNat._Nat__eqb x y of {
   Datatypes.Coq_true -> d;
   Datatypes.Coq_false -> iv y}

preds_in :: SecOrder -> Datatypes.Coq_list Coq_predicate
preds_in alpha =
  case alpha of {
   Coq_predSO p _ -> Datatypes.Coq_cons p Datatypes.Coq_nil;
   Coq_allFO _ beta -> preds_in beta;
   Coq_exFO _ beta -> preds_in beta;
   Coq_negSO beta -> preds_in beta;
   Coq_conjSO beta1 beta2 -> Datatypes.app (preds_in beta1) (preds_in beta2);
   Coq_disjSO beta1 beta2 -> Datatypes.app (preds_in beta1) (preds_in beta2);
   Coq_implSO beta1 beta2 -> Datatypes.app (preds_in beta1) (preds_in beta2);
   Coq_allSO p beta -> Datatypes.Coq_cons p (preds_in beta);
   Coq_exSO p beta -> Datatypes.Coq_cons p (preds_in beta);
   _ -> Datatypes.Coq_nil}

list_closed_SO :: SecOrder -> (Datatypes.Coq_list Coq_predicate) -> SecOrder
list_closed_SO alpha l =
  case l of {
   Datatypes.Coq_nil -> alpha;
   Datatypes.Coq_cons p ls -> Coq_allSO p (list_closed_SO alpha ls)}

uni_closed_SO :: SecOrder -> SecOrder
uni_closed_SO alpha =
  list_closed_SO alpha (preds_in alpha)

