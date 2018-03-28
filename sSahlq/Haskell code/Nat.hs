module Nat where

import qualified Prelude
import qualified Datatypes

type Coq_t = Datatypes.Coq_nat

zero :: Datatypes.Coq_nat
zero =
  Datatypes.O

one :: Datatypes.Coq_nat
one =
  Datatypes.S Datatypes.O

two :: Datatypes.Coq_nat
two =
  Datatypes.S (Datatypes.S Datatypes.O)

succ :: Datatypes.Coq_nat -> Datatypes.Coq_nat
succ x =
  Datatypes.S x

pred :: Datatypes.Coq_nat -> Datatypes.Coq_nat
pred n =
  case n of {
   Datatypes.O -> n;
   Datatypes.S u -> u}

add :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
add n m =
  case n of {
   Datatypes.O -> m;
   Datatypes.S p -> Datatypes.S (add p m)}

double :: Datatypes.Coq_nat -> Datatypes.Coq_nat
double n =
  add n n

mul :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
mul n m =
  case n of {
   Datatypes.O -> Datatypes.O;
   Datatypes.S p -> add m (mul p m)}

sub :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
sub n m =
  case n of {
   Datatypes.O -> n;
   Datatypes.S k ->
    case m of {
     Datatypes.O -> n;
     Datatypes.S l -> sub k l}}

eqb :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_bool
eqb n m =
  case n of {
   Datatypes.O ->
    case m of {
     Datatypes.O -> Datatypes.Coq_true;
     Datatypes.S _ -> Datatypes.Coq_false};
   Datatypes.S n' ->
    case m of {
     Datatypes.O -> Datatypes.Coq_false;
     Datatypes.S m' -> eqb n' m'}}

leb :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_bool
leb n m =
  case n of {
   Datatypes.O -> Datatypes.Coq_true;
   Datatypes.S n' ->
    case m of {
     Datatypes.O -> Datatypes.Coq_false;
     Datatypes.S m' -> leb n' m'}}

ltb :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_bool
ltb n m =
  leb (Datatypes.S n) m

compare :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_comparison
compare n m =
  case n of {
   Datatypes.O ->
    case m of {
     Datatypes.O -> Datatypes.Eq;
     Datatypes.S _ -> Datatypes.Lt};
   Datatypes.S n' ->
    case m of {
     Datatypes.O -> Datatypes.Gt;
     Datatypes.S m' -> compare n' m'}}

max :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
max n m =
  case n of {
   Datatypes.O -> m;
   Datatypes.S n' ->
    case m of {
     Datatypes.O -> n;
     Datatypes.S m' -> Datatypes.S (max n' m')}}

min :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
min n m =
  case n of {
   Datatypes.O -> Datatypes.O;
   Datatypes.S n' ->
    case m of {
     Datatypes.O -> Datatypes.O;
     Datatypes.S m' -> Datatypes.S (min n' m')}}

even :: Datatypes.Coq_nat -> Datatypes.Coq_bool
even n =
  case n of {
   Datatypes.O -> Datatypes.Coq_true;
   Datatypes.S n0 ->
    case n0 of {
     Datatypes.O -> Datatypes.Coq_false;
     Datatypes.S n' -> even n'}}

odd :: Datatypes.Coq_nat -> Datatypes.Coq_bool
odd n =
  Datatypes.negb (even n)

pow :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
pow n m =
  case m of {
   Datatypes.O -> Datatypes.S Datatypes.O;
   Datatypes.S m0 -> mul n (pow n m0)}

divmod :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat ->
          Datatypes.Coq_nat -> Datatypes.Coq_prod Datatypes.Coq_nat
          Datatypes.Coq_nat
divmod x y q u =
  case x of {
   Datatypes.O -> Datatypes.Coq_pair q u;
   Datatypes.S x' ->
    case u of {
     Datatypes.O -> divmod x' y (Datatypes.S q) y;
     Datatypes.S u' -> divmod x' y q u'}}

div :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
div x y =
  case y of {
   Datatypes.O -> y;
   Datatypes.S y' -> Datatypes.fst (divmod x y' Datatypes.O y')}

modulo :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
modulo x y =
  case y of {
   Datatypes.O -> y;
   Datatypes.S y' -> sub y' (Datatypes.snd (divmod x y' Datatypes.O y'))}

gcd :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
gcd a b =
  case a of {
   Datatypes.O -> b;
   Datatypes.S a' -> gcd (modulo b (Datatypes.S a')) (Datatypes.S a')}

square :: Datatypes.Coq_nat -> Datatypes.Coq_nat
square n =
  mul n n

sqrt_iter :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat ->
             Datatypes.Coq_nat -> Datatypes.Coq_nat
sqrt_iter k p q r =
  case k of {
   Datatypes.O -> p;
   Datatypes.S k' ->
    case r of {
     Datatypes.O ->
      sqrt_iter k' (Datatypes.S p) (Datatypes.S (Datatypes.S q)) (Datatypes.S
        (Datatypes.S q));
     Datatypes.S r' -> sqrt_iter k' p q r'}}

sqrt :: Datatypes.Coq_nat -> Datatypes.Coq_nat
sqrt n =
  sqrt_iter n Datatypes.O Datatypes.O Datatypes.O

log2_iter :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat ->
             Datatypes.Coq_nat -> Datatypes.Coq_nat
log2_iter k p q r =
  case k of {
   Datatypes.O -> p;
   Datatypes.S k' ->
    case r of {
     Datatypes.O -> log2_iter k' (Datatypes.S p) (Datatypes.S q) q;
     Datatypes.S r' -> log2_iter k' p (Datatypes.S q) r'}}

log2 :: Datatypes.Coq_nat -> Datatypes.Coq_nat
log2 n =
  log2_iter (pred n) Datatypes.O (Datatypes.S Datatypes.O) Datatypes.O

iter :: Datatypes.Coq_nat -> (a1 -> a1) -> a1 -> a1
iter n f x =
  Datatypes.nat_rect x (\_ -> f) n

div2 :: Datatypes.Coq_nat -> Datatypes.Coq_nat
div2 n =
  case n of {
   Datatypes.O -> Datatypes.O;
   Datatypes.S n0 ->
    case n0 of {
     Datatypes.O -> Datatypes.O;
     Datatypes.S n' -> Datatypes.S (div2 n')}}

testbit :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_bool
testbit a n =
  case n of {
   Datatypes.O -> odd a;
   Datatypes.S n0 -> testbit (div2 a) n0}

shiftl :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
shiftl a =
  Datatypes.nat_rect a (\_ -> double)

shiftr :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
shiftr a =
  Datatypes.nat_rect a (\_ -> div2)

bitwise :: (Datatypes.Coq_bool -> Datatypes.Coq_bool -> Datatypes.Coq_bool)
           -> Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat ->
           Datatypes.Coq_nat
bitwise op n a b =
  case n of {
   Datatypes.O -> Datatypes.O;
   Datatypes.S n' ->
    add
      (case op (odd a) (odd b) of {
        Datatypes.Coq_true -> Datatypes.S Datatypes.O;
        Datatypes.Coq_false -> Datatypes.O})
      (mul (Datatypes.S (Datatypes.S Datatypes.O))
        (bitwise op n' (div2 a) (div2 b)))}

land :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
land a b =
  bitwise Datatypes.andb a a b

lor :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
lor a b =
  bitwise Datatypes.orb (max a b) a b

ldiff :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
ldiff a b =
  bitwise (\b0 b' -> Datatypes.andb b0 (Datatypes.negb b')) a a b

lxor :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
lxor a b =
  bitwise Datatypes.xorb (max a b) a b

