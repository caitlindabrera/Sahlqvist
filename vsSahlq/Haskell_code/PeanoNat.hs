module PeanoNat where

import qualified Prelude
import qualified Bool
import qualified Datatypes
import qualified Decimal
import qualified Logic
import qualified Specif

__ :: any
__ = Prelude.error "Logical or arity value used"

type Nat__Coq_t = Datatypes.Coq_nat

_Nat__zero :: Datatypes.Coq_nat
_Nat__zero =
  Datatypes.O

_Nat__one :: Datatypes.Coq_nat
_Nat__one =
  Datatypes.S Datatypes.O

_Nat__two :: Datatypes.Coq_nat
_Nat__two =
  Datatypes.S (Datatypes.S Datatypes.O)

_Nat__succ :: Datatypes.Coq_nat -> Datatypes.Coq_nat
_Nat__succ x =
  Datatypes.S x

_Nat__pred :: Datatypes.Coq_nat -> Datatypes.Coq_nat
_Nat__pred n =
  case n of {
   Datatypes.O -> n;
   Datatypes.S u -> u}

_Nat__add :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
_Nat__add n m =
  case n of {
   Datatypes.O -> m;
   Datatypes.S p -> Datatypes.S (_Nat__add p m)}

_Nat__double :: Datatypes.Coq_nat -> Datatypes.Coq_nat
_Nat__double n =
  _Nat__add n n

_Nat__mul :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
_Nat__mul n m =
  case n of {
   Datatypes.O -> Datatypes.O;
   Datatypes.S p -> _Nat__add m (_Nat__mul p m)}

_Nat__sub :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
_Nat__sub n m =
  case n of {
   Datatypes.O -> n;
   Datatypes.S k ->
    case m of {
     Datatypes.O -> n;
     Datatypes.S l -> _Nat__sub k l}}

_Nat__eqb :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_bool
_Nat__eqb n m =
  case n of {
   Datatypes.O ->
    case m of {
     Datatypes.O -> Datatypes.Coq_true;
     Datatypes.S _ -> Datatypes.Coq_false};
   Datatypes.S n' ->
    case m of {
     Datatypes.O -> Datatypes.Coq_false;
     Datatypes.S m' -> _Nat__eqb n' m'}}

_Nat__leb :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_bool
_Nat__leb n m =
  case n of {
   Datatypes.O -> Datatypes.Coq_true;
   Datatypes.S n' ->
    case m of {
     Datatypes.O -> Datatypes.Coq_false;
     Datatypes.S m' -> _Nat__leb n' m'}}

_Nat__ltb :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_bool
_Nat__ltb n m =
  _Nat__leb (Datatypes.S n) m

_Nat__compare :: Datatypes.Coq_nat -> Datatypes.Coq_nat ->
                 Datatypes.Coq_comparison
_Nat__compare n m =
  case n of {
   Datatypes.O ->
    case m of {
     Datatypes.O -> Datatypes.Eq;
     Datatypes.S _ -> Datatypes.Lt};
   Datatypes.S n' ->
    case m of {
     Datatypes.O -> Datatypes.Gt;
     Datatypes.S m' -> _Nat__compare n' m'}}

_Nat__max :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
_Nat__max n m =
  case n of {
   Datatypes.O -> m;
   Datatypes.S n' ->
    case m of {
     Datatypes.O -> n;
     Datatypes.S m' -> Datatypes.S (_Nat__max n' m')}}

_Nat__min :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
_Nat__min n m =
  case n of {
   Datatypes.O -> Datatypes.O;
   Datatypes.S n' ->
    case m of {
     Datatypes.O -> Datatypes.O;
     Datatypes.S m' -> Datatypes.S (_Nat__min n' m')}}

_Nat__even :: Datatypes.Coq_nat -> Datatypes.Coq_bool
_Nat__even n =
  case n of {
   Datatypes.O -> Datatypes.Coq_true;
   Datatypes.S n0 ->
    case n0 of {
     Datatypes.O -> Datatypes.Coq_false;
     Datatypes.S n' -> _Nat__even n'}}

_Nat__odd :: Datatypes.Coq_nat -> Datatypes.Coq_bool
_Nat__odd n =
  Datatypes.negb (_Nat__even n)

_Nat__pow :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
_Nat__pow n m =
  case m of {
   Datatypes.O -> Datatypes.S Datatypes.O;
   Datatypes.S m0 -> _Nat__mul n (_Nat__pow n m0)}

_Nat__tail_add :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
_Nat__tail_add n m =
  case n of {
   Datatypes.O -> m;
   Datatypes.S n0 -> _Nat__tail_add n0 (Datatypes.S m)}

_Nat__tail_addmul :: Datatypes.Coq_nat -> Datatypes.Coq_nat ->
                     Datatypes.Coq_nat -> Datatypes.Coq_nat
_Nat__tail_addmul r n m =
  case n of {
   Datatypes.O -> r;
   Datatypes.S n0 -> _Nat__tail_addmul (_Nat__tail_add m r) n0 m}

_Nat__tail_mul :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
_Nat__tail_mul n m =
  _Nat__tail_addmul Datatypes.O n m

_Nat__of_uint_acc :: Decimal.Coq_uint -> Datatypes.Coq_nat ->
                     Datatypes.Coq_nat
_Nat__of_uint_acc d acc =
  case d of {
   Decimal.Nil -> acc;
   Decimal.D0 d0 ->
    _Nat__of_uint_acc d0
      (_Nat__tail_mul (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
        (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
        (Datatypes.S Datatypes.O)))))))))) acc);
   Decimal.D1 d0 ->
    _Nat__of_uint_acc d0 (Datatypes.S
      (_Nat__tail_mul (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
        (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
        (Datatypes.S Datatypes.O)))))))))) acc));
   Decimal.D2 d0 ->
    _Nat__of_uint_acc d0 (Datatypes.S (Datatypes.S
      (_Nat__tail_mul (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
        (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
        (Datatypes.S Datatypes.O)))))))))) acc)));
   Decimal.D3 d0 ->
    _Nat__of_uint_acc d0 (Datatypes.S (Datatypes.S (Datatypes.S
      (_Nat__tail_mul (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
        (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
        (Datatypes.S Datatypes.O)))))))))) acc))));
   Decimal.D4 d0 ->
    _Nat__of_uint_acc d0 (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
      (_Nat__tail_mul (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
        (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
        (Datatypes.S Datatypes.O)))))))))) acc)))));
   Decimal.D5 d0 ->
    _Nat__of_uint_acc d0 (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
      (Datatypes.S
      (_Nat__tail_mul (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
        (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
        (Datatypes.S Datatypes.O)))))))))) acc))))));
   Decimal.D6 d0 ->
    _Nat__of_uint_acc d0 (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
      (Datatypes.S (Datatypes.S
      (_Nat__tail_mul (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
        (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
        (Datatypes.S Datatypes.O)))))))))) acc)))))));
   Decimal.D7 d0 ->
    _Nat__of_uint_acc d0 (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
      (Datatypes.S (Datatypes.S (Datatypes.S
      (_Nat__tail_mul (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
        (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
        (Datatypes.S Datatypes.O)))))))))) acc))))))));
   Decimal.D8 d0 ->
    _Nat__of_uint_acc d0 (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
      (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
      (_Nat__tail_mul (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
        (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
        (Datatypes.S Datatypes.O)))))))))) acc)))))))));
   Decimal.D9 d0 ->
    _Nat__of_uint_acc d0 (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
      (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
      (_Nat__tail_mul (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
        (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
        (Datatypes.S Datatypes.O)))))))))) acc))))))))))}

_Nat__of_uint :: Decimal.Coq_uint -> Datatypes.Coq_nat
_Nat__of_uint d =
  _Nat__of_uint_acc d Datatypes.O

_Nat__to_little_uint :: Datatypes.Coq_nat -> Decimal.Coq_uint ->
                        Decimal.Coq_uint
_Nat__to_little_uint n acc =
  case n of {
   Datatypes.O -> acc;
   Datatypes.S n0 -> _Nat__to_little_uint n0 (Decimal._Little__succ acc)}

_Nat__to_uint :: Datatypes.Coq_nat -> Decimal.Coq_uint
_Nat__to_uint n =
  Decimal.rev (_Nat__to_little_uint n (Decimal.D0 Decimal.Nil))

_Nat__of_int :: Decimal.Coq_int -> Datatypes.Coq_option Datatypes.Coq_nat
_Nat__of_int d =
  case Decimal.norm d of {
   Decimal.Pos u -> Datatypes.Some (_Nat__of_uint u);
   Decimal.Neg _ -> Datatypes.None}

_Nat__to_int :: Datatypes.Coq_nat -> Decimal.Coq_int
_Nat__to_int n =
  Decimal.Pos (_Nat__to_uint n)

_Nat__divmod :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
                -> Datatypes.Coq_nat -> Datatypes.Coq_prod Datatypes.Coq_nat
                Datatypes.Coq_nat
_Nat__divmod x y q u =
  case x of {
   Datatypes.O -> Datatypes.Coq_pair q u;
   Datatypes.S x' ->
    case u of {
     Datatypes.O -> _Nat__divmod x' y (Datatypes.S q) y;
     Datatypes.S u' -> _Nat__divmod x' y q u'}}

_Nat__div :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
_Nat__div x y =
  case y of {
   Datatypes.O -> y;
   Datatypes.S y' -> Datatypes.fst (_Nat__divmod x y' Datatypes.O y')}

_Nat__modulo :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
_Nat__modulo x y =
  case y of {
   Datatypes.O -> y;
   Datatypes.S y' ->
    _Nat__sub y' (Datatypes.snd (_Nat__divmod x y' Datatypes.O y'))}

_Nat__gcd :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
_Nat__gcd a b =
  case a of {
   Datatypes.O -> b;
   Datatypes.S a' ->
    _Nat__gcd (_Nat__modulo b (Datatypes.S a')) (Datatypes.S a')}

_Nat__square :: Datatypes.Coq_nat -> Datatypes.Coq_nat
_Nat__square n =
  _Nat__mul n n

_Nat__sqrt_iter :: Datatypes.Coq_nat -> Datatypes.Coq_nat ->
                   Datatypes.Coq_nat -> Datatypes.Coq_nat ->
                   Datatypes.Coq_nat
_Nat__sqrt_iter k p q r =
  case k of {
   Datatypes.O -> p;
   Datatypes.S k' ->
    case r of {
     Datatypes.O ->
      _Nat__sqrt_iter k' (Datatypes.S p) (Datatypes.S (Datatypes.S q))
        (Datatypes.S (Datatypes.S q));
     Datatypes.S r' -> _Nat__sqrt_iter k' p q r'}}

_Nat__sqrt :: Datatypes.Coq_nat -> Datatypes.Coq_nat
_Nat__sqrt n =
  _Nat__sqrt_iter n Datatypes.O Datatypes.O Datatypes.O

_Nat__log2_iter :: Datatypes.Coq_nat -> Datatypes.Coq_nat ->
                   Datatypes.Coq_nat -> Datatypes.Coq_nat ->
                   Datatypes.Coq_nat
_Nat__log2_iter k p q r =
  case k of {
   Datatypes.O -> p;
   Datatypes.S k' ->
    case r of {
     Datatypes.O -> _Nat__log2_iter k' (Datatypes.S p) (Datatypes.S q) q;
     Datatypes.S r' -> _Nat__log2_iter k' p (Datatypes.S q) r'}}

_Nat__log2 :: Datatypes.Coq_nat -> Datatypes.Coq_nat
_Nat__log2 n =
  _Nat__log2_iter (_Nat__pred n) Datatypes.O (Datatypes.S Datatypes.O)
    Datatypes.O

_Nat__iter :: Datatypes.Coq_nat -> (a1 -> a1) -> a1 -> a1
_Nat__iter n f x =
  Datatypes.nat_rect x (\_ -> f) n

_Nat__div2 :: Datatypes.Coq_nat -> Datatypes.Coq_nat
_Nat__div2 n =
  case n of {
   Datatypes.O -> Datatypes.O;
   Datatypes.S n0 ->
    case n0 of {
     Datatypes.O -> Datatypes.O;
     Datatypes.S n' -> Datatypes.S (_Nat__div2 n')}}

_Nat__testbit :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_bool
_Nat__testbit a n =
  case n of {
   Datatypes.O -> _Nat__odd a;
   Datatypes.S n0 -> _Nat__testbit (_Nat__div2 a) n0}

_Nat__shiftl :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
_Nat__shiftl a =
  Datatypes.nat_rect a (\_ -> _Nat__double)

_Nat__shiftr :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
_Nat__shiftr a =
  Datatypes.nat_rect a (\_ -> _Nat__div2)

_Nat__bitwise :: (Datatypes.Coq_bool -> Datatypes.Coq_bool ->
                 Datatypes.Coq_bool) -> Datatypes.Coq_nat ->
                 Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
_Nat__bitwise op n a b =
  case n of {
   Datatypes.O -> Datatypes.O;
   Datatypes.S n' ->
    _Nat__add
      (case op (_Nat__odd a) (_Nat__odd b) of {
        Datatypes.Coq_true -> Datatypes.S Datatypes.O;
        Datatypes.Coq_false -> Datatypes.O})
      (_Nat__mul (Datatypes.S (Datatypes.S Datatypes.O))
        (_Nat__bitwise op n' (_Nat__div2 a) (_Nat__div2 b)))}

_Nat__land :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
_Nat__land a b =
  _Nat__bitwise Datatypes.andb a a b

_Nat__lor :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
_Nat__lor a b =
  _Nat__bitwise Datatypes.orb (_Nat__max a b) a b

_Nat__ldiff :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
_Nat__ldiff a b =
  _Nat__bitwise (\b0 b' -> Datatypes.andb b0 (Datatypes.negb b')) a a b

_Nat__lxor :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
_Nat__lxor a b =
  _Nat__bitwise Datatypes.xorb (_Nat__max a b) a b

_Nat__recursion :: a1 -> (Datatypes.Coq_nat -> a1 -> a1) -> Datatypes.Coq_nat
                   -> a1
_Nat__recursion =
  Datatypes.nat_rect

_Nat__eq_dec :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Specif.Coq_sumbool
_Nat__eq_dec n =
  Datatypes.nat_rec (\m ->
    case m of {
     Datatypes.O -> Specif.Coq_left;
     Datatypes.S _ -> Specif.Coq_right}) (\_ iHn m ->
    case m of {
     Datatypes.O -> Specif.Coq_right;
     Datatypes.S m0 -> iHn m0}) n

_Nat__leb_spec0 :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Bool.Coq_reflect
_Nat__leb_spec0 x y =
  Bool.iff_reflect (_Nat__leb x y)

_Nat__ltb_spec0 :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Bool.Coq_reflect
_Nat__ltb_spec0 x y =
  Bool.iff_reflect (_Nat__ltb x y)

_Nat__Private_Dec__max_case_strong :: Datatypes.Coq_nat -> Datatypes.Coq_nat
                                      -> (Datatypes.Coq_nat ->
                                      Datatypes.Coq_nat -> () -> a1 -> a1) ->
                                      (() -> a1) -> (() -> a1) -> a1
_Nat__Private_Dec__max_case_strong n m compat hl hr =
  let {c = Datatypes.coq_CompSpec2Type n m (_Nat__compare n m)} in
  case c of {
   Datatypes.CompGtT -> compat n (_Nat__max n m) __ (hl __);
   _ -> compat m (_Nat__max n m) __ (hr __)}

_Nat__Private_Dec__max_case :: Datatypes.Coq_nat -> Datatypes.Coq_nat ->
                               (Datatypes.Coq_nat -> Datatypes.Coq_nat -> ()
                               -> a1 -> a1) -> a1 -> a1 -> a1
_Nat__Private_Dec__max_case n m x x0 x1 =
  _Nat__Private_Dec__max_case_strong n m x (\_ -> x0) (\_ -> x1)

_Nat__Private_Dec__max_dec :: Datatypes.Coq_nat -> Datatypes.Coq_nat ->
                              Specif.Coq_sumbool
_Nat__Private_Dec__max_dec n m =
  _Nat__Private_Dec__max_case n m (\_ _ _ h0 -> h0) Specif.Coq_left
    Specif.Coq_right

_Nat__Private_Dec__min_case_strong :: Datatypes.Coq_nat -> Datatypes.Coq_nat
                                      -> (Datatypes.Coq_nat ->
                                      Datatypes.Coq_nat -> () -> a1 -> a1) ->
                                      (() -> a1) -> (() -> a1) -> a1
_Nat__Private_Dec__min_case_strong n m compat hl hr =
  let {c = Datatypes.coq_CompSpec2Type n m (_Nat__compare n m)} in
  case c of {
   Datatypes.CompGtT -> compat m (_Nat__min n m) __ (hr __);
   _ -> compat n (_Nat__min n m) __ (hl __)}

_Nat__Private_Dec__min_case :: Datatypes.Coq_nat -> Datatypes.Coq_nat ->
                               (Datatypes.Coq_nat -> Datatypes.Coq_nat -> ()
                               -> a1 -> a1) -> a1 -> a1 -> a1
_Nat__Private_Dec__min_case n m x x0 x1 =
  _Nat__Private_Dec__min_case_strong n m x (\_ -> x0) (\_ -> x1)

_Nat__Private_Dec__min_dec :: Datatypes.Coq_nat -> Datatypes.Coq_nat ->
                              Specif.Coq_sumbool
_Nat__Private_Dec__min_dec n m =
  _Nat__Private_Dec__min_case n m (\_ _ _ h0 -> h0) Specif.Coq_left
    Specif.Coq_right

_Nat__max_case_strong :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> (() -> a1)
                         -> (() -> a1) -> a1
_Nat__max_case_strong n m x x0 =
  _Nat__Private_Dec__max_case_strong n m (\_ _ _ x1 ->
    Logic.eq_rect __ x1 __) x x0

_Nat__max_case :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> a1 -> a1 -> a1
_Nat__max_case n m x x0 =
  _Nat__max_case_strong n m (\_ -> x) (\_ -> x0)

_Nat__max_dec :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Specif.Coq_sumbool
_Nat__max_dec =
  _Nat__Private_Dec__max_dec

_Nat__min_case_strong :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> (() -> a1)
                         -> (() -> a1) -> a1
_Nat__min_case_strong n m x x0 =
  _Nat__Private_Dec__min_case_strong n m (\_ _ _ x1 ->
    Logic.eq_rect __ x1 __) x x0

_Nat__min_case :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> a1 -> a1 -> a1
_Nat__min_case n m x x0 =
  _Nat__min_case_strong n m (\_ -> x) (\_ -> x0)

_Nat__min_dec :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Specif.Coq_sumbool
_Nat__min_dec =
  _Nat__Private_Dec__min_dec

_Nat__sqrt_up :: Datatypes.Coq_nat -> Datatypes.Coq_nat
_Nat__sqrt_up a =
  case _Nat__compare Datatypes.O a of {
   Datatypes.Lt -> Datatypes.S (_Nat__sqrt (_Nat__pred a));
   _ -> Datatypes.O}

_Nat__log2_up :: Datatypes.Coq_nat -> Datatypes.Coq_nat
_Nat__log2_up a =
  case _Nat__compare (Datatypes.S Datatypes.O) a of {
   Datatypes.Lt -> Datatypes.S (_Nat__log2 (_Nat__pred a));
   _ -> Datatypes.O}

_Nat__lcm :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
_Nat__lcm a b =
  _Nat__mul a (_Nat__div b (_Nat__gcd a b))

_Nat__eqb_spec :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Bool.Coq_reflect
_Nat__eqb_spec x y =
  Bool.iff_reflect (_Nat__eqb x y)

_Nat__b2n :: Datatypes.Coq_bool -> Datatypes.Coq_nat
_Nat__b2n b =
  case b of {
   Datatypes.Coq_true -> Datatypes.S Datatypes.O;
   Datatypes.Coq_false -> Datatypes.O}

_Nat__setbit :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
_Nat__setbit a n =
  _Nat__lor a (_Nat__shiftl (Datatypes.S Datatypes.O) n)

_Nat__clearbit :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
_Nat__clearbit a n =
  _Nat__ldiff a (_Nat__shiftl (Datatypes.S Datatypes.O) n)

_Nat__ones :: Datatypes.Coq_nat -> Datatypes.Coq_nat
_Nat__ones n =
  _Nat__pred (_Nat__shiftl (Datatypes.S Datatypes.O) n)

_Nat__lnot :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
_Nat__lnot a n =
  _Nat__lxor a (_Nat__ones n)

