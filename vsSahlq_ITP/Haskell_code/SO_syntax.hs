module SO_syntax where

import qualified Prelude
import qualified Datatypes
import qualified List
import qualified Logic
import qualified PeanoNat
import qualified Specif

type Coq_predicate =
  Datatypes.Coq_nat
  -- singleton inductive, whose constructor was Pred
  
predicate_rect :: (Datatypes.Coq_nat -> a1) -> Coq_predicate -> a1
predicate_rect f =
  f

predicate_rec :: (Datatypes.Coq_nat -> a1) -> Coq_predicate -> a1
predicate_rec =
  predicate_rect

predicate_dec :: Coq_predicate -> Coq_predicate -> Specif.Coq_sumbool
predicate_dec p q =
  let {s = PeanoNat._Nat__eq_dec p q} in
  case s of {
   Specif.Coq_left -> Logic.eq_rec_r q Specif.Coq_left p;
   Specif.Coq_right -> Specif.Coq_right}

in_predicate_dec :: Coq_predicate -> (Datatypes.Coq_list Coq_predicate) ->
                    Specif.Coq_sumbool
in_predicate_dec a l =
  List.in_dec predicate_dec a l

type FOvariable =
  Datatypes.Coq_nat
  -- singleton inductive, whose constructor was Var
  
coq_FOvariable_rect :: (Datatypes.Coq_nat -> a1) -> FOvariable -> a1
coq_FOvariable_rect f =
  f

coq_FOvariable_rec :: (Datatypes.Coq_nat -> a1) -> FOvariable -> a1
coq_FOvariable_rec =
  coq_FOvariable_rect

coq_FOvariable_dec :: FOvariable -> FOvariable -> Specif.Coq_sumbool
coq_FOvariable_dec x y =
  let {s = PeanoNat._Nat__eq_dec x y} in
  case s of {
   Specif.Coq_left -> Logic.eq_rec_r y Specif.Coq_left x;
   Specif.Coq_right -> Specif.Coq_right}

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

calc_ante_SO :: SecOrder -> SecOrder
calc_ante_SO alpha =
  case alpha of {
   Coq_implSO beta1 _ -> beta1;
   _ -> alpha}

calc_cons_SO :: SecOrder -> SecOrder
calc_cons_SO alpha =
  case alpha of {
   Coq_implSO _ beta2 -> beta2;
   _ -> alpha}

