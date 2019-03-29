module Specif where

import qualified Prelude
import qualified Datatypes
import qualified Logic

__ :: any
__ = Prelude.error "Logical or arity value used"

type Coq_sig a = a
  -- singleton inductive, whose constructor was exist
  
sig_rect :: (a1 -> () -> a2) -> a1 -> a2
sig_rect f s =
  f s __

sig_rec :: (a1 -> () -> a2) -> a1 -> a2
sig_rec =
  sig_rect

type Coq_sig2 a = a
  -- singleton inductive, whose constructor was exist2
  
sig2_rect :: (a1 -> () -> () -> a2) -> (Coq_sig2 a1) -> a2
sig2_rect f s =
  f s __ __

sig2_rec :: (a1 -> () -> () -> a2) -> (Coq_sig2 a1) -> a2
sig2_rec =
  sig2_rect

data Coq_sigT a p =
   Coq_existT a p

sigT_rect :: (a1 -> a2 -> a3) -> (Coq_sigT a1 a2) -> a3
sigT_rect f s =
  case s of {
   Coq_existT x x0 -> f x x0}

sigT_rec :: (a1 -> a2 -> a3) -> (Coq_sigT a1 a2) -> a3
sigT_rec =
  sigT_rect

data Coq_sigT2 a p q =
   Coq_existT2 a p q

sigT2_rect :: (a1 -> a2 -> a3 -> a4) -> (Coq_sigT2 a1 a2 a3) -> a4
sigT2_rect f s =
  case s of {
   Coq_existT2 x x0 x1 -> f x x0 x1}

sigT2_rec :: (a1 -> a2 -> a3 -> a4) -> (Coq_sigT2 a1 a2 a3) -> a4
sigT2_rec =
  sigT2_rect

proj1_sig :: a1 -> a1
proj1_sig e =
  e

sig_of_sig2 :: (Coq_sig2 a1) -> a1
sig_of_sig2 x =
  x

projT1 :: (Coq_sigT a1 a2) -> a1
projT1 x =
  case x of {
   Coq_existT a _ -> a}

projT2 :: (Coq_sigT a1 a2) -> a2
projT2 x =
  case x of {
   Coq_existT _ h -> h}

sigT_of_sigT2 :: (Coq_sigT2 a1 a2 a3) -> Coq_sigT a1 a2
sigT_of_sigT2 x =
  Coq_existT (case x of {
               Coq_existT2 a _ _ -> a}) (case x of {
                                          Coq_existT2 _ p _ -> p})

projT3 :: (Coq_sigT2 a1 a2 a3) -> a3
projT3 e =
  case e of {
   Coq_existT2 _ _ c -> c}

sig_of_sigT :: (Coq_sigT a1 ()) -> a1
sig_of_sigT =
  projT1

sigT_of_sig :: a1 -> Coq_sigT a1 ()
sigT_of_sig x =
  Coq_existT (proj1_sig x) __

sig2_of_sigT2 :: (Coq_sigT2 a1 () ()) -> Coq_sig2 a1
sig2_of_sigT2 x =
  projT1 (sigT_of_sigT2 x)

sigT2_of_sig2 :: (Coq_sig2 a1) -> Coq_sigT2 a1 () ()
sigT2_of_sig2 x =
  Coq_existT2 (proj1_sig (sig_of_sig2 x)) __ __

eq_sigT_rect :: (Coq_sigT a1 a2) -> (Coq_sigT a1 a2) -> (() -> () -> a3) ->
                a3
eq_sigT_rect _ _ f =
  f __ __

eq_sigT_rec :: (Coq_sigT a1 a2) -> (Coq_sigT a1 a2) -> (() -> () -> a3) -> a3
eq_sigT_rec =
  eq_sigT_rect

eq_sig_rect :: a1 -> a1 -> (() -> () -> a2) -> a2
eq_sig_rect _ _ f =
  f __ __

eq_sig_rec :: a1 -> a1 -> (() -> () -> a2) -> a2
eq_sig_rec =
  eq_sig_rect

eq_sigT2_rect :: (Coq_sigT2 a1 a2 a3) -> (Coq_sigT2 a1 a2 a3) -> (() -> () ->
                 () -> a4) -> a4
eq_sigT2_rect _ _ f =
  f __ __ __

eq_sigT2_rec :: (Coq_sigT2 a1 a2 a3) -> (Coq_sigT2 a1 a2 a3) -> (() -> () ->
                () -> a4) -> a4
eq_sigT2_rec =
  eq_sigT2_rect

eq_sig2_rect :: (Coq_sig2 a1) -> (Coq_sig2 a1) -> (() -> () -> () -> a2) ->
                a2
eq_sig2_rect _ _ f =
  f __ __ __

eq_sig2_rec :: (Coq_sig2 a1) -> (Coq_sig2 a1) -> (() -> () -> () -> a2) -> a2
eq_sig2_rec =
  eq_sig2_rect

data Coq_sumbool =
   Coq_left
 | Coq_right

sumbool_rect :: (() -> a1) -> (() -> a1) -> Coq_sumbool -> a1
sumbool_rect f f0 s =
  case s of {
   Coq_left -> f __;
   Coq_right -> f0 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Coq_sumbool -> a1
sumbool_rec =
  sumbool_rect

data Coq_sumor a =
   Coq_inleft a
 | Coq_inright

sumor_rect :: (a1 -> a2) -> (() -> a2) -> (Coq_sumor a1) -> a2
sumor_rect f f0 s =
  case s of {
   Coq_inleft x -> f x;
   Coq_inright -> f0 __}

sumor_rec :: (a1 -> a2) -> (() -> a2) -> (Coq_sumor a1) -> a2
sumor_rec =
  sumor_rect

coq_Choice :: (a1 -> a2) -> (a1 -> a2)
coq_Choice h z =
  proj1_sig (h z)

coq_Choice2 :: (a1 -> Coq_sigT a2 a3) -> Coq_sigT (a1 -> a2) (a1 -> a3)
coq_Choice2 h =
  Coq_existT (\z -> projT1 (h z)) (\z ->
    let {s = h z} in case s of {
                      Coq_existT _ r -> r})

bool_choice :: (a1 -> Coq_sumbool) -> (a1 -> Datatypes.Coq_bool)
bool_choice h z =
  case h z of {
   Coq_left -> Datatypes.Coq_true;
   Coq_right -> Datatypes.Coq_false}

dependent_choice :: (a1 -> a1) -> a1 -> (Datatypes.Coq_nat -> a1)
dependent_choice h x0 n =
  case n of {
   Datatypes.O -> x0;
   Datatypes.S n' -> proj1_sig (h (dependent_choice h x0 n'))}

type Exc a = Datatypes.Coq_option a

value :: a1 -> Datatypes.Coq_option a1
value x =
  Datatypes.Some x

error :: Datatypes.Coq_option a1
error =
  Datatypes.None

except :: a1
except =
  Logic.coq_False_rec

absurd_set :: a1
absurd_set =
  Logic.coq_False_rec

