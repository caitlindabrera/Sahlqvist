module VsSahlq_instant13 where

import qualified Prelude
import qualified Datatypes
import qualified Logic
import qualified Modal
import qualified Nat
import qualified P_occurs_in_alpha
import qualified PeanoNat
import qualified ST_setup
import qualified SecOrder
import qualified Specif
import qualified VsSahlq_preprocessing1

__ :: any
__ = Prelude.error "Logical or arity value used"

vsS_pa_l :: (SecOrder.FOvariable -> a1) -> (Datatypes.Coq_list
            (Datatypes.Coq_list SecOrder.FOvariable)) -> (Datatypes.Coq_list
            SecOrder.FOvariable) -> Datatypes.Coq_list ()
vsS_pa_l iv llv lx =
  case llv of {
   Datatypes.Coq_nil -> Datatypes.Coq_nil;
   Datatypes.Coq_cons _ llv' ->
    case lx of {
     Datatypes.Coq_nil -> Datatypes.Coq_nil;
     Datatypes.Coq_cons _ lx' -> Datatypes.Coq_cons __ (vsS_pa_l iv llv' lx')}}

ind_pa :: (Datatypes.Coq_list Datatypes.Coq_nat) -> (Datatypes.Coq_list 
          ()) -> Datatypes.Coq_list ()
ind_pa l lx =
  case l of {
   Datatypes.Coq_nil -> Datatypes.Coq_nil;
   Datatypes.Coq_cons _ l' -> Datatypes.Coq_cons __ (ind_pa l' lx)}

indicies_l2_pre :: (Datatypes.Coq_list SecOrder.Coq_predicate) ->
                   SecOrder.Coq_predicate -> Datatypes.Coq_nat ->
                   Datatypes.Coq_list Datatypes.Coq_nat
indicies_l2_pre lP p count =
  case lP of {
   Datatypes.Coq_nil -> Datatypes.Coq_nil;
   Datatypes.Coq_cons q lP' ->
    case PeanoNat._Nat__eqb p q of {
     Datatypes.Coq_true -> Datatypes.Coq_cons
      (Nat.add (Datatypes.S Datatypes.O) count)
      (indicies_l2_pre lP' p (Datatypes.S count));
     Datatypes.Coq_false -> indicies_l2_pre lP' p (Datatypes.S count)}}

indicies_l2 :: (Datatypes.Coq_list SecOrder.Coq_predicate) ->
               SecOrder.Coq_predicate -> Datatypes.Coq_list Datatypes.Coq_nat
indicies_l2 lP p =
  indicies_l2_pre lP p Datatypes.O

constant_l :: a1 -> Datatypes.Coq_nat -> Datatypes.Coq_list a1
constant_l a n =
  case n of {
   Datatypes.O -> Datatypes.Coq_nil;
   Datatypes.S m -> Datatypes.Coq_cons a (constant_l a m)}

at_FOv :: Datatypes.Coq_nat -> (Datatypes.Coq_list SecOrder.FOvariable) ->
          SecOrder.FOvariable
at_FOv n l =
  case n of {
   Datatypes.O -> Datatypes.S Datatypes.O;
   Datatypes.S m ->
    case m of {
     Datatypes.O ->
      case l of {
       Datatypes.Coq_nil -> Datatypes.S Datatypes.O;
       Datatypes.Coq_cons x _ -> x};
     Datatypes.S _ ->
      case l of {
       Datatypes.Coq_nil -> Datatypes.S Datatypes.O;
       Datatypes.Coq_cons _ l0 -> at_FOv m l0}}}

ind_FOv :: (Datatypes.Coq_list Datatypes.Coq_nat) -> (Datatypes.Coq_list
           SecOrder.FOvariable) -> Datatypes.Coq_list SecOrder.FOvariable
ind_FOv l lx =
  case l of {
   Datatypes.Coq_nil -> Datatypes.Coq_nil;
   Datatypes.Coq_cons n l' -> Datatypes.Coq_cons (at_FOv n lx)
    (ind_FOv l' lx)}

at_cond :: Datatypes.Coq_nat -> (Datatypes.Coq_list SecOrder.SecOrder) ->
           SecOrder.SecOrder
at_cond n l =
  case n of {
   Datatypes.O -> SecOrder.Coq_eqFO (Datatypes.S Datatypes.O) (Datatypes.S
    Datatypes.O);
   Datatypes.S m ->
    case m of {
     Datatypes.O ->
      case l of {
       Datatypes.Coq_nil -> SecOrder.Coq_eqFO (Datatypes.S Datatypes.O)
        (Datatypes.S Datatypes.O);
       Datatypes.Coq_cons x _ -> x};
     Datatypes.S _ ->
      case l of {
       Datatypes.Coq_nil -> SecOrder.Coq_eqFO (Datatypes.S Datatypes.O)
        (Datatypes.S Datatypes.O);
       Datatypes.Coq_cons _ l' -> at_cond m l'}}}

ind_cond :: (Datatypes.Coq_list Datatypes.Coq_nat) -> (Datatypes.Coq_list
            SecOrder.SecOrder) -> Datatypes.Coq_list SecOrder.SecOrder
ind_cond l lx =
  case l of {
   Datatypes.Coq_nil -> Datatypes.Coq_nil;
   Datatypes.Coq_cons n l' -> Datatypes.Coq_cons (at_cond n lx)
    (ind_cond l' lx)}

at_llv :: Datatypes.Coq_nat -> (Datatypes.Coq_list
          (Datatypes.Coq_list SecOrder.FOvariable)) -> Datatypes.Coq_list
          SecOrder.FOvariable
at_llv n llv =
  case n of {
   Datatypes.O -> Datatypes.Coq_nil;
   Datatypes.S m ->
    case m of {
     Datatypes.O ->
      case llv of {
       Datatypes.Coq_nil -> Datatypes.Coq_nil;
       Datatypes.Coq_cons x _ -> x};
     Datatypes.S _ ->
      case llv of {
       Datatypes.Coq_nil -> Datatypes.Coq_nil;
       Datatypes.Coq_cons _ l -> at_llv m l}}}

ind_llv :: (Datatypes.Coq_list Datatypes.Coq_nat) -> (Datatypes.Coq_list
           (Datatypes.Coq_list SecOrder.FOvariable)) -> Datatypes.Coq_list
           (Datatypes.Coq_list SecOrder.FOvariable)
ind_llv l llv =
  case l of {
   Datatypes.Coq_nil -> Datatypes.Coq_nil;
   Datatypes.Coq_cons n l' -> Datatypes.Coq_cons (at_llv n llv)
    (ind_llv l' llv)}

ex_ind_exceed :: (Datatypes.Coq_list Datatypes.Coq_nat) -> Datatypes.Coq_nat
                 -> Datatypes.Coq_bool
ex_ind_exceed l n =
  case l of {
   Datatypes.Coq_nil -> Datatypes.Coq_false;
   Datatypes.Coq_cons m l' ->
    case Nat.leb m n of {
     Datatypes.Coq_true -> ex_ind_exceed l' n;
     Datatypes.Coq_false -> Datatypes.Coq_true}}

is_in_nat :: Datatypes.Coq_nat -> (Datatypes.Coq_list Datatypes.Coq_nat) ->
             Datatypes.Coq_bool
is_in_nat n l =
  case l of {
   Datatypes.Coq_nil -> Datatypes.Coq_false;
   Datatypes.Coq_cons m l' ->
    case PeanoNat._Nat__eqb n m of {
     Datatypes.Coq_true -> Datatypes.Coq_true;
     Datatypes.Coq_false -> is_in_nat n l'}}

at_gen :: a1 -> Datatypes.Coq_nat -> (Datatypes.Coq_list a1) -> a1
at_gen a n l =
  case n of {
   Datatypes.O -> a;
   Datatypes.S m ->
    case m of {
     Datatypes.O ->
      case l of {
       Datatypes.Coq_nil -> a;
       Datatypes.Coq_cons a0 _ -> a0};
     Datatypes.S _ ->
      case l of {
       Datatypes.Coq_nil -> a;
       Datatypes.Coq_cons _ l0 -> at_gen a m l0}}}

ind_gen :: a1 -> (Datatypes.Coq_list Datatypes.Coq_nat) ->
           (Datatypes.Coq_list a1) -> Datatypes.Coq_list a1
ind_gen a l lx =
  case l of {
   Datatypes.Coq_nil -> Datatypes.Coq_nil;
   Datatypes.Coq_cons n l' -> Datatypes.Coq_cons (at_gen a n lx)
    (ind_gen a l' lx)}

preprocess_vsSahlq_ante_predSO_againTRY :: SecOrder.Coq_predicate ->
                                           SecOrder.FOvariable ->
                                           Specif.Coq_sigT
                                           (Datatypes.Coq_list
                                           SecOrder.FOvariable)
                                           (Specif.Coq_sigT SecOrder.SecOrder
                                           (Datatypes.Coq_prod ()
                                           (Datatypes.Coq_sum
                                           SecOrder.SecOrder ())))
preprocess_vsSahlq_ante_predSO_againTRY p f =
  Specif.Coq_existT Datatypes.Coq_nil (Specif.Coq_existT (SecOrder.Coq_predSO
    p f) (Datatypes.Coq_pair __ (Datatypes.Coq_inr __)))

preprocess_vsSahlq_ante_exFO_againTRY :: SecOrder.SecOrder ->
                                         SecOrder.FOvariable ->
                                         SecOrder.Coq_predicate -> (() ->
                                         SecOrder.Coq_predicate ->
                                         Specif.Coq_sigT
                                         (Datatypes.Coq_list
                                         SecOrder.FOvariable)
                                         (Specif.Coq_sigT SecOrder.SecOrder
                                         (Datatypes.Coq_prod ()
                                         (Datatypes.Coq_sum SecOrder.SecOrder
                                         ())))) -> Specif.Coq_sigT
                                         (Datatypes.Coq_list
                                         SecOrder.FOvariable)
                                         (Specif.Coq_sigT SecOrder.SecOrder
                                         (Datatypes.Coq_prod ()
                                         (Datatypes.Coq_sum SecOrder.SecOrder
                                         ())))
preprocess_vsSahlq_ante_exFO_againTRY _ f hocc iHalpha =
  let {iHalpha0 = iHalpha __ hocc} in
  case iHalpha0 of {
   Specif.Coq_existT lv s ->
    case s of {
     Specif.Coq_existT atm p ->
      case p of {
       Datatypes.Coq_pair _ s0 ->
        case s0 of {
         Datatypes.Coq_inl s1 -> Specif.Coq_existT (Datatypes.Coq_cons f lv)
          (Specif.Coq_existT atm (Datatypes.Coq_pair __ (Datatypes.Coq_inl
          s1)));
         Datatypes.Coq_inr _ -> Specif.Coq_existT (Datatypes.Coq_cons f lv)
          (Specif.Coq_existT atm (Datatypes.Coq_pair __ (Datatypes.Coq_inr
          __)))}}}}

trying1 :: SecOrder.SecOrder -> Datatypes.Coq_sum () SecOrder.Coq_predicate
trying1 alpha =
  SecOrder.coq_SecOrder_rec (\p _ -> Datatypes.Coq_inr p) (\_ _ ->
    Datatypes.Coq_inl __) (\_ _ -> Datatypes.Coq_inl __) (\_ _ iHalpha ->
    case iHalpha of {
     Datatypes.Coq_inl _ -> Datatypes.Coq_inl __;
     Datatypes.Coq_inr iH2 -> Datatypes.Coq_inr iH2}) (\_ _ iHalpha ->
    case iHalpha of {
     Datatypes.Coq_inl _ -> Datatypes.Coq_inl __;
     Datatypes.Coq_inr iH2 -> Datatypes.Coq_inr iH2}) (\_ iHalpha ->
    case iHalpha of {
     Datatypes.Coq_inl _ -> Datatypes.Coq_inl __;
     Datatypes.Coq_inr iH2 -> Datatypes.Coq_inr iH2})
    (\_ iHalpha1 _ iHalpha2 ->
    case iHalpha1 of {
     Datatypes.Coq_inl _ ->
      case iHalpha2 of {
       Datatypes.Coq_inl _ -> Datatypes.Coq_inl __;
       Datatypes.Coq_inr iH2 -> Datatypes.Coq_inr iH2};
     Datatypes.Coq_inr iH1 -> Datatypes.Coq_inr iH1})
    (\_ iHalpha1 _ iHalpha2 ->
    case iHalpha1 of {
     Datatypes.Coq_inl _ ->
      case iHalpha2 of {
       Datatypes.Coq_inl _ -> Datatypes.Coq_inl __;
       Datatypes.Coq_inr iH2 -> Datatypes.Coq_inr iH2};
     Datatypes.Coq_inr iH1 -> Datatypes.Coq_inr iH1})
    (\_ iHalpha1 _ iHalpha2 ->
    case iHalpha1 of {
     Datatypes.Coq_inl _ ->
      case iHalpha2 of {
       Datatypes.Coq_inl _ -> Datatypes.Coq_inl __;
       Datatypes.Coq_inr iH2 -> Datatypes.Coq_inr iH2};
     Datatypes.Coq_inr iH1 -> Datatypes.Coq_inr iH1}) (\p _ _ ->
    Datatypes.Coq_inr p) (\p _ _ -> Datatypes.Coq_inr p) alpha

preprocess_vsSahlq_ante_5_againTRY :: SecOrder.SecOrder -> SecOrder.SecOrder
                                      -> (Datatypes.Coq_list
                                      SecOrder.FOvariable) ->
                                      SecOrder.SecOrder ->
                                      (Datatypes.Coq_list
                                      SecOrder.FOvariable) ->
                                      SecOrder.SecOrder -> Specif.Coq_sigT
                                      (Datatypes.Coq_list
                                      SecOrder.FOvariable) SecOrder.SecOrder
preprocess_vsSahlq_ante_5_againTRY _ _ lv1 rel1 lv2 rel2 =
  Specif.Coq_existT
    (Datatypes.app
      (VsSahlq_preprocessing1.rename_FOv_A_list rel2
        (VsSahlq_preprocessing1.list_closed_exFO rel1 lv1) lv2)
      (VsSahlq_preprocessing1.rename_FOv_A_list rel1
        (VsSahlq_preprocessing1.rename_FOv_A rel2
          (VsSahlq_preprocessing1.list_closed_exFO rel1 lv1) lv2) lv1))
    (SecOrder.Coq_conjSO
    (VsSahlq_preprocessing1.rename_FOv_A rel1
      (VsSahlq_preprocessing1.rename_FOv_A rel2
        (VsSahlq_preprocessing1.list_closed_exFO rel1 lv1) lv2) lv1)
    (VsSahlq_preprocessing1.rename_FOv_A rel2
      (VsSahlq_preprocessing1.list_closed_exFO rel1 lv1) lv2))

trying2 :: SecOrder.SecOrder -> Specif.Coq_sigT
           (Datatypes.Coq_list SecOrder.FOvariable)
           (Specif.Coq_sigT SecOrder.SecOrder ())
trying2 alpha =
  SecOrder.coq_SecOrder_rec (\_ _ _ _ -> Logic.coq_False_rec) (\f f0 _ _ ->
    Specif.Coq_existT Datatypes.Coq_nil (Specif.Coq_existT
    (SecOrder.Coq_relatSO f f0) __)) (\_ _ _ _ -> Logic.coq_False_rec)
    (\_ _ _ _ _ -> Logic.coq_False_rec) (\f _ iHalpha _ _ ->
    let {s = iHalpha __ __} in
    case s of {
     Specif.Coq_existT lv s0 ->
      case s0 of {
       Specif.Coq_existT rel _ -> Specif.Coq_existT (Datatypes.Coq_cons f lv)
        (Specif.Coq_existT rel __)}}) (\_ _ _ _ -> Logic.coq_False_rec)
    (\alpha1 iHalpha1 alpha2 iHalpha2 _ _ ->
    case VsSahlq_preprocessing1.conjSO_exFO_relatSO alpha1 of {
     Datatypes.Coq_true ->
      let {s = iHalpha1 __ __} in
      case s of {
       Specif.Coq_existT lv s0 ->
        case s0 of {
         Specif.Coq_existT rel _ ->
          let {s1 = iHalpha2 __ __} in
          case s1 of {
           Specif.Coq_existT lv2 s2 ->
            case s2 of {
             Specif.Coq_existT rel2 _ ->
              let {
               s3 = preprocess_vsSahlq_ante_5_againTRY alpha1 alpha2 lv rel
                      lv2 rel2}
              in
              case s3 of {
               Specif.Coq_existT lv' s4 -> Specif.Coq_existT lv'
                (Specif.Coq_existT s4 __)}}}}};
     Datatypes.Coq_false -> Logic.coq_False_rec}) (\_ _ _ _ _ _ ->
    Logic.coq_False_rec) (\_ _ _ _ _ _ -> Logic.coq_False_rec) (\_ _ _ _ _ ->
    Logic.coq_False_rec) (\_ _ _ _ _ -> Logic.coq_False_rec) alpha __ __

preprocess_vsSahlq_ante_notocc_againTRY :: SecOrder.SecOrder ->
                                           Specif.Coq_sigT
                                           (Datatypes.Coq_list
                                           SecOrder.FOvariable)
                                           (Specif.Coq_sigT SecOrder.SecOrder
                                           ())
preprocess_vsSahlq_ante_notocc_againTRY alpha =
  let {s = trying2 alpha} in
  case s of {
   Specif.Coq_existT lv s0 ->
    case s0 of {
     Specif.Coq_existT rel _ -> Specif.Coq_existT lv (Specif.Coq_existT rel
      __)}}

preprocess_vsSahlq_ante_4_againTRY :: SecOrder.SecOrder -> SecOrder.SecOrder
                                      -> (Datatypes.Coq_list
                                      SecOrder.FOvariable) ->
                                      SecOrder.SecOrder ->
                                      (Datatypes.Coq_list
                                      SecOrder.FOvariable) ->
                                      SecOrder.SecOrder -> SecOrder.SecOrder
                                      -> Specif.Coq_sigT
                                      (Datatypes.Coq_list
                                      SecOrder.FOvariable)
                                      (Specif.Coq_sigT SecOrder.SecOrder
                                      (Datatypes.Coq_prod ()
                                      SecOrder.SecOrder))
preprocess_vsSahlq_ante_4_againTRY _ _ lv1 rel1 lv2 rel2 atm2 =
  let {
   s = VsSahlq_preprocessing1.same_struc_conjSO_ex
         (VsSahlq_preprocessing1.rename_FOv_A (SecOrder.Coq_conjSO rel2 atm2)
           (VsSahlq_preprocessing1.list_closed_exFO rel1 lv1) lv2) rel2 atm2}
  in
  case s of {
   Specif.Coq_existT rel2' s0 ->
    case s0 of {
     Specif.Coq_existT atm2' _ -> Specif.Coq_existT
      (Datatypes.app
        (VsSahlq_preprocessing1.rename_FOv_A_list (SecOrder.Coq_conjSO rel2
          atm2) (VsSahlq_preprocessing1.list_closed_exFO rel1 lv1) lv2)
        (VsSahlq_preprocessing1.rename_FOv_A_list rel1
          (VsSahlq_preprocessing1.rename_FOv_A (SecOrder.Coq_conjSO rel2
            atm2) (VsSahlq_preprocessing1.list_closed_exFO rel1 lv1) lv2)
          lv1)) (Specif.Coq_existT atm2' (Datatypes.Coq_pair __
      (SecOrder.Coq_conjSO
      (VsSahlq_preprocessing1.rename_FOv_A rel1
        (VsSahlq_preprocessing1.rename_FOv_A (SecOrder.Coq_conjSO rel2 atm2)
          (VsSahlq_preprocessing1.list_closed_exFO rel1 lv1) lv2) lv1)
      rel2')))}}

preprocess_vsSahlq_ante_6_againTRY :: SecOrder.SecOrder -> SecOrder.SecOrder
                                      -> (Datatypes.Coq_list
                                      SecOrder.FOvariable) ->
                                      SecOrder.SecOrder ->
                                      (Datatypes.Coq_list
                                      SecOrder.FOvariable) ->
                                      SecOrder.SecOrder -> Specif.Coq_sigT
                                      (Datatypes.Coq_list
                                      SecOrder.FOvariable)
                                      (Specif.Coq_sigT SecOrder.SecOrder
                                      (Datatypes.Coq_prod ()
                                      SecOrder.SecOrder))
preprocess_vsSahlq_ante_6_againTRY _ _ lv1 rel1 lv2 atm2 =
  Specif.Coq_existT
    (Datatypes.app
      (VsSahlq_preprocessing1.rename_FOv_A_list atm2
        (VsSahlq_preprocessing1.list_closed_exFO rel1 lv1) lv2)
      (VsSahlq_preprocessing1.rename_FOv_A_list rel1
        (VsSahlq_preprocessing1.rename_FOv_A atm2
          (VsSahlq_preprocessing1.list_closed_exFO rel1 lv1) lv2) lv1))
    (Specif.Coq_existT
    (VsSahlq_preprocessing1.rename_FOv_A atm2
      (VsSahlq_preprocessing1.list_closed_exFO rel1 lv1) lv2)
    (Datatypes.Coq_pair __
    (VsSahlq_preprocessing1.rename_FOv_A rel1
      (VsSahlq_preprocessing1.rename_FOv_A atm2
        (VsSahlq_preprocessing1.list_closed_exFO rel1 lv1) lv2) lv1)))

preprocess_vsSahlq_ante_2_againTRY :: SecOrder.SecOrder -> SecOrder.SecOrder
                                      -> (Datatypes.Coq_list
                                      SecOrder.FOvariable) ->
                                      SecOrder.SecOrder -> SecOrder.SecOrder
                                      -> (Datatypes.Coq_list
                                      SecOrder.FOvariable) ->
                                      SecOrder.SecOrder -> Specif.Coq_sigT
                                      (Datatypes.Coq_list
                                      SecOrder.FOvariable)
                                      (Specif.Coq_sigT SecOrder.SecOrder
                                      (Datatypes.Coq_prod ()
                                      (Specif.Coq_sigT SecOrder.SecOrder ())))
preprocess_vsSahlq_ante_2_againTRY _ _ lv1 rel1 atm1 lv2 rel2 =
  let {
   s = VsSahlq_preprocessing1.same_struc_conjSO_ex
         (VsSahlq_preprocessing1.rename_FOv_A (SecOrder.Coq_conjSO rel1 atm1)
           (VsSahlq_preprocessing1.rename_FOv_A rel2
             (VsSahlq_preprocessing1.list_closed_exFO (SecOrder.Coq_conjSO
               rel1 atm1) lv1) lv2) lv1) rel1 atm1}
  in
  case s of {
   Specif.Coq_existT rel1' s0 ->
    case s0 of {
     Specif.Coq_existT atm1' _ -> Specif.Coq_existT
      (Datatypes.app
        (VsSahlq_preprocessing1.rename_FOv_A_list rel2
          (VsSahlq_preprocessing1.list_closed_exFO (SecOrder.Coq_conjSO rel1
            atm1) lv1) lv2)
        (VsSahlq_preprocessing1.rename_FOv_A_list (SecOrder.Coq_conjSO rel1
          atm1)
          (VsSahlq_preprocessing1.rename_FOv_A rel2
            (VsSahlq_preprocessing1.list_closed_exFO (SecOrder.Coq_conjSO
              rel1 atm1) lv1) lv2) lv1)) (Specif.Coq_existT atm1'
      (Datatypes.Coq_pair __ (Specif.Coq_existT (SecOrder.Coq_conjSO rel1'
      (VsSahlq_preprocessing1.rename_FOv_A rel2
        (VsSahlq_preprocessing1.list_closed_exFO (SecOrder.Coq_conjSO rel1
          atm1) lv1) lv2)) __)))}}

preprocess_vsSahlq_ante_8_againTRY :: SecOrder.SecOrder -> SecOrder.SecOrder
                                      -> (Datatypes.Coq_list
                                      SecOrder.FOvariable) ->
                                      SecOrder.SecOrder ->
                                      (Datatypes.Coq_list
                                      SecOrder.FOvariable) ->
                                      SecOrder.SecOrder -> Specif.Coq_sigT
                                      (Datatypes.Coq_list
                                      SecOrder.FOvariable)
                                      (Specif.Coq_sigT SecOrder.SecOrder
                                      (Datatypes.Coq_prod ()
                                      SecOrder.SecOrder))
preprocess_vsSahlq_ante_8_againTRY _ _ lv1 atm1 lv2 rel2 =
  Specif.Coq_existT
    (Datatypes.app
      (VsSahlq_preprocessing1.rename_FOv_A_list rel2
        (VsSahlq_preprocessing1.list_closed_exFO atm1 lv1) lv2)
      (VsSahlq_preprocessing1.rename_FOv_A_list atm1
        (VsSahlq_preprocessing1.rename_FOv_A rel2
          (VsSahlq_preprocessing1.list_closed_exFO atm1 lv1) lv2) lv1))
    (Specif.Coq_existT
    (VsSahlq_preprocessing1.rename_FOv_A atm1
      (VsSahlq_preprocessing1.rename_FOv_A rel2
        (VsSahlq_preprocessing1.list_closed_exFO atm1 lv1) lv2) lv1)
    (Datatypes.Coq_pair __
    (VsSahlq_preprocessing1.rename_FOv_A rel2
      (VsSahlq_preprocessing1.list_closed_exFO atm1 lv1) lv2)))

preprocess_vsSahlq_ante_1_againTRY :: SecOrder.SecOrder -> SecOrder.SecOrder
                                      -> (Datatypes.Coq_list
                                      SecOrder.FOvariable) ->
                                      SecOrder.SecOrder -> SecOrder.SecOrder
                                      -> (Datatypes.Coq_list
                                      SecOrder.FOvariable) ->
                                      SecOrder.SecOrder -> SecOrder.SecOrder
                                      -> Specif.Coq_sigT
                                      (Datatypes.Coq_list
                                      SecOrder.FOvariable)
                                      (Specif.Coq_sigT SecOrder.SecOrder
                                      (Datatypes.Coq_prod ()
                                      SecOrder.SecOrder))
preprocess_vsSahlq_ante_1_againTRY _ _ lv1 rel1 atm1 lv2 rel2 atm2 =
  let {
   s = VsSahlq_preprocessing1.same_struc_conjSO_ex
         (VsSahlq_preprocessing1.rename_FOv_A (SecOrder.Coq_conjSO rel1 atm1)
           (VsSahlq_preprocessing1.rename_FOv_A (SecOrder.Coq_conjSO rel2
             atm2)
             (VsSahlq_preprocessing1.list_closed_exFO (SecOrder.Coq_conjSO
               rel1 atm1) lv1) lv2) lv1) rel1 atm1}
  in
  case s of {
   Specif.Coq_existT rel1' s0 ->
    case s0 of {
     Specif.Coq_existT atm1' _ ->
      let {
       s1 = VsSahlq_preprocessing1.same_struc_conjSO_ex
              (VsSahlq_preprocessing1.rename_FOv_A (SecOrder.Coq_conjSO rel2
                atm2)
                (VsSahlq_preprocessing1.list_closed_exFO (SecOrder.Coq_conjSO
                  rel1 atm1) lv1) lv2) rel2 atm2}
      in
      case s1 of {
       Specif.Coq_existT rel2' s2 ->
        case s2 of {
         Specif.Coq_existT atm2' _ -> Specif.Coq_existT
          (Datatypes.app
            (VsSahlq_preprocessing1.rename_FOv_A_list (SecOrder.Coq_conjSO
              rel2 atm2)
              (VsSahlq_preprocessing1.list_closed_exFO (SecOrder.Coq_conjSO
                rel1 atm1) lv1) lv2)
            (VsSahlq_preprocessing1.rename_FOv_A_list (SecOrder.Coq_conjSO
              rel1 atm1)
              (VsSahlq_preprocessing1.rename_FOv_A (SecOrder.Coq_conjSO rel2
                atm2)
                (VsSahlq_preprocessing1.list_closed_exFO (SecOrder.Coq_conjSO
                  rel1 atm1) lv1) lv2) lv1)) (Specif.Coq_existT
          (SecOrder.Coq_conjSO atm1' atm2') (Datatypes.Coq_pair __
          (SecOrder.Coq_conjSO rel1' rel2')))}}}}

preprocess_vsSahlq_ante_3_againTRY :: SecOrder.SecOrder -> SecOrder.SecOrder
                                      -> (Datatypes.Coq_list
                                      SecOrder.FOvariable) ->
                                      SecOrder.SecOrder -> SecOrder.SecOrder
                                      -> (Datatypes.Coq_list
                                      SecOrder.FOvariable) ->
                                      SecOrder.SecOrder -> Specif.Coq_sigT
                                      (Datatypes.Coq_list
                                      SecOrder.FOvariable)
                                      (Specif.Coq_sigT SecOrder.SecOrder
                                      (Datatypes.Coq_prod ()
                                      SecOrder.SecOrder))
preprocess_vsSahlq_ante_3_againTRY _ _ lv1 rel1 atm1 lv2 atm2 =
  let {
   s = VsSahlq_preprocessing1.same_struc_conjSO_ex
         (VsSahlq_preprocessing1.rename_FOv_A (SecOrder.Coq_conjSO rel1 atm1)
           (VsSahlq_preprocessing1.rename_FOv_A atm2
             (VsSahlq_preprocessing1.list_closed_exFO (SecOrder.Coq_conjSO
               rel1 atm1) lv1) lv2) lv1) rel1 atm1}
  in
  case s of {
   Specif.Coq_existT rel1' s0 ->
    case s0 of {
     Specif.Coq_existT atm1' _ -> Specif.Coq_existT
      (Datatypes.app
        (VsSahlq_preprocessing1.rename_FOv_A_list atm2
          (VsSahlq_preprocessing1.list_closed_exFO (SecOrder.Coq_conjSO rel1
            atm1) lv1) lv2)
        (VsSahlq_preprocessing1.rename_FOv_A_list (SecOrder.Coq_conjSO rel1
          atm1)
          (VsSahlq_preprocessing1.rename_FOv_A atm2
            (VsSahlq_preprocessing1.list_closed_exFO (SecOrder.Coq_conjSO
              rel1 atm1) lv1) lv2) lv1)) (Specif.Coq_existT
      (SecOrder.Coq_conjSO atm1'
      (VsSahlq_preprocessing1.rename_FOv_A atm2
        (VsSahlq_preprocessing1.list_closed_exFO (SecOrder.Coq_conjSO rel1
          atm1) lv1) lv2)) (Datatypes.Coq_pair __ rel1'))}}

preprocess_vsSahlq_ante_7_againTRY :: SecOrder.SecOrder -> SecOrder.SecOrder
                                      -> (Datatypes.Coq_list
                                      SecOrder.FOvariable) ->
                                      SecOrder.SecOrder ->
                                      (Datatypes.Coq_list
                                      SecOrder.FOvariable) ->
                                      SecOrder.SecOrder -> SecOrder.SecOrder
                                      -> Specif.Coq_sigT
                                      (Datatypes.Coq_list
                                      SecOrder.FOvariable)
                                      (Specif.Coq_sigT SecOrder.SecOrder
                                      (Datatypes.Coq_prod ()
                                      SecOrder.SecOrder))
preprocess_vsSahlq_ante_7_againTRY _ _ lv1 atm1 lv2 rel2 atm2 =
  let {
   s = VsSahlq_preprocessing1.same_struc_conjSO_ex
         (VsSahlq_preprocessing1.rename_FOv_A (SecOrder.Coq_conjSO rel2 atm2)
           (VsSahlq_preprocessing1.list_closed_exFO atm1 lv1) lv2) rel2 atm2}
  in
  case s of {
   Specif.Coq_existT rel2' s0 ->
    case s0 of {
     Specif.Coq_existT atm2' _ -> Specif.Coq_existT
      (Datatypes.app
        (VsSahlq_preprocessing1.rename_FOv_A_list (SecOrder.Coq_conjSO rel2
          atm2) (VsSahlq_preprocessing1.list_closed_exFO atm1 lv1) lv2)
        (VsSahlq_preprocessing1.rename_FOv_A_list atm1
          (VsSahlq_preprocessing1.rename_FOv_A (SecOrder.Coq_conjSO rel2
            atm2) (VsSahlq_preprocessing1.list_closed_exFO atm1 lv1) lv2)
          lv1)) (Specif.Coq_existT (SecOrder.Coq_conjSO
      (VsSahlq_preprocessing1.rename_FOv_A atm1
        (VsSahlq_preprocessing1.rename_FOv_A (SecOrder.Coq_conjSO rel2 atm2)
          (VsSahlq_preprocessing1.list_closed_exFO atm1 lv1) lv2) lv1) atm2')
      (Datatypes.Coq_pair __ rel2'))}}

preprocess_vsSahlq_ante_9_againTRY :: SecOrder.SecOrder -> SecOrder.SecOrder
                                      -> (Datatypes.Coq_list
                                      SecOrder.FOvariable) ->
                                      SecOrder.SecOrder ->
                                      (Datatypes.Coq_list
                                      SecOrder.FOvariable) ->
                                      SecOrder.SecOrder -> Specif.Coq_sigT
                                      (Datatypes.Coq_list
                                      SecOrder.FOvariable)
                                      (Specif.Coq_sigT SecOrder.SecOrder ())
preprocess_vsSahlq_ante_9_againTRY _ _ lv1 atm1 lv2 atm2 =
  Specif.Coq_existT
    (Datatypes.app
      (VsSahlq_preprocessing1.rename_FOv_A_list atm2
        (VsSahlq_preprocessing1.list_closed_exFO atm1 lv1) lv2)
      (VsSahlq_preprocessing1.rename_FOv_A_list atm1
        (VsSahlq_preprocessing1.rename_FOv_A atm2
          (VsSahlq_preprocessing1.list_closed_exFO atm1 lv1) lv2) lv1))
    (Specif.Coq_existT (SecOrder.Coq_conjSO
    (VsSahlq_preprocessing1.rename_FOv_A atm1
      (VsSahlq_preprocessing1.rename_FOv_A atm2
        (VsSahlq_preprocessing1.list_closed_exFO atm1 lv1) lv2) lv1)
    (VsSahlq_preprocessing1.rename_FOv_A atm2
      (VsSahlq_preprocessing1.list_closed_exFO atm1 lv1) lv2)) __)

preprocess_vsSahlq_ante_againTRY :: SecOrder.SecOrder ->
                                    SecOrder.Coq_predicate -> Specif.Coq_sigT
                                    (Datatypes.Coq_list SecOrder.FOvariable)
                                    (Specif.Coq_sigT SecOrder.SecOrder
                                    (Datatypes.Coq_prod ()
                                    (Datatypes.Coq_sum SecOrder.SecOrder ())))
preprocess_vsSahlq_ante_againTRY alpha hocc =
  SecOrder.coq_SecOrder_rec (\p f _ _ ->
    preprocess_vsSahlq_ante_predSO_againTRY p f) (\_ _ _ _ ->
    Logic.coq_False_rec) (\_ _ _ _ -> Logic.coq_False_rec) (\_ _ _ _ _ ->
    Logic.coq_False_rec) (\f alpha0 iHalpha _ hocc0 ->
    preprocess_vsSahlq_ante_exFO_againTRY alpha0 f hocc0 iHalpha)
    (\_ _ _ _ -> Logic.coq_False_rec)
    (\alpha1 iHalpha1 alpha2 iHalpha2 _ hocc0 ->
    case VsSahlq_preprocessing1.conjSO_exFO_relatSO alpha1 of {
     Datatypes.Coq_true ->
      let {iHalpha3 = iHalpha1 __} in
      let {iHalpha4 = iHalpha2 __} in
      let {s = trying1 alpha1} in
      case s of {
       Datatypes.Coq_inl _ ->
        let {s0 = preprocess_vsSahlq_ante_notocc_againTRY alpha1} in
        case s0 of {
         Specif.Coq_existT lv1 s1 ->
          case s1 of {
           Specif.Coq_existT rel1 _ ->
            let {
             s2 = iHalpha4
                    (let {
                      h0 = \alpha3 alpha4 p ->
                       case P_occurs_in_alpha.coq_P_occurs_in_alpha_conjSO_comp
                              alpha3 alpha4 p of {
                        Datatypes.Coq_pair x _ -> x}}
                     in
                     let {hocc1 = h0 alpha1 alpha2 hocc0 __} in
                     let {
                      hocc2 = Logic.eq_rec
                                (P_occurs_in_alpha.coq_P_occurs_in_alpha
                                  alpha1 hocc0) hocc1 Datatypes.Coq_false}
                     in
                     case hocc2 of {
                      Datatypes.Coq_inl _ -> Logic.coq_False_rec;
                      Datatypes.Coq_inr _ -> hocc0})}
            in
            case s2 of {
             Specif.Coq_existT lv2 s3 ->
              case s3 of {
               Specif.Coq_existT atm2 p ->
                case p of {
                 Datatypes.Coq_pair _ s4 ->
                  case s4 of {
                   Datatypes.Coq_inl s5 ->
                    let {
                     s6 = preprocess_vsSahlq_ante_4_againTRY alpha1 alpha2
                            lv1 rel1 lv2 s5 atm2}
                    in
                    case s6 of {
                     Specif.Coq_existT lv' s7 ->
                      case s7 of {
                       Specif.Coq_existT atm' p0 ->
                        case p0 of {
                         Datatypes.Coq_pair _ s8 -> Specif.Coq_existT lv'
                          (Specif.Coq_existT atm' (Datatypes.Coq_pair __
                          (Datatypes.Coq_inl s8)))}}};
                   Datatypes.Coq_inr _ ->
                    let {
                     s5 = preprocess_vsSahlq_ante_6_againTRY alpha1 alpha2
                            lv1 rel1 lv2 atm2}
                    in
                    case s5 of {
                     Specif.Coq_existT lv' s6 ->
                      case s6 of {
                       Specif.Coq_existT atm' p0 ->
                        case p0 of {
                         Datatypes.Coq_pair _ s7 -> Specif.Coq_existT lv'
                          (Specif.Coq_existT atm' (Datatypes.Coq_pair __
                          (Datatypes.Coq_inl s7)))}}}}}}}}};
       Datatypes.Coq_inr hocc2 ->
        let {s0 = trying1 alpha2} in
        case s0 of {
         Datatypes.Coq_inl _ ->
          let {s1 = preprocess_vsSahlq_ante_notocc_againTRY alpha2} in
          case s1 of {
           Specif.Coq_existT lv2 s2 ->
            case s2 of {
             Specif.Coq_existT rel2 _ ->
              let {s3 = iHalpha3 hocc2} in
              case s3 of {
               Specif.Coq_existT lv1 s4 ->
                case s4 of {
                 Specif.Coq_existT atm1 p ->
                  case p of {
                   Datatypes.Coq_pair _ s5 ->
                    case s5 of {
                     Datatypes.Coq_inl s6 ->
                      let {
                       s7 = preprocess_vsSahlq_ante_2_againTRY alpha1 alpha2
                              lv1 s6 atm1 lv2 rel2}
                      in
                      case s7 of {
                       Specif.Coq_existT lv' s8 ->
                        case s8 of {
                         Specif.Coq_existT atm' p0 ->
                          case p0 of {
                           Datatypes.Coq_pair _ s9 ->
                            case s9 of {
                             Specif.Coq_existT rel' _ -> Specif.Coq_existT
                              lv' (Specif.Coq_existT atm' (Datatypes.Coq_pair
                              __ (Datatypes.Coq_inl rel')))}}}};
                     Datatypes.Coq_inr _ ->
                      let {
                       s6 = preprocess_vsSahlq_ante_8_againTRY alpha1 alpha2
                              lv1 atm1 lv2 rel2}
                      in
                      case s6 of {
                       Specif.Coq_existT lv' s7 ->
                        case s7 of {
                         Specif.Coq_existT atm' p0 ->
                          case p0 of {
                           Datatypes.Coq_pair _ s8 -> Specif.Coq_existT lv'
                            (Specif.Coq_existT atm' (Datatypes.Coq_pair __
                            (Datatypes.Coq_inl s8)))}}}}}}}}};
         Datatypes.Coq_inr hocc2b ->
          let {s1 = iHalpha3 hocc2} in
          case s1 of {
           Specif.Coq_existT lv1 s2 ->
            case s2 of {
             Specif.Coq_existT atm1 p ->
              case p of {
               Datatypes.Coq_pair _ s3 ->
                case s3 of {
                 Datatypes.Coq_inl s4 ->
                  let {s5 = iHalpha4 hocc2b} in
                  case s5 of {
                   Specif.Coq_existT lv2 s6 ->
                    case s6 of {
                     Specif.Coq_existT atm2 p0 ->
                      case p0 of {
                       Datatypes.Coq_pair _ s7 ->
                        case s7 of {
                         Datatypes.Coq_inl s8 ->
                          let {
                           s9 = preprocess_vsSahlq_ante_1_againTRY alpha1
                                  alpha2 lv1 s4 atm1 lv2 s8 atm2}
                          in
                          case s9 of {
                           Specif.Coq_existT lv' s10 ->
                            case s10 of {
                             Specif.Coq_existT atm' p1 ->
                              case p1 of {
                               Datatypes.Coq_pair _ s11 -> Specif.Coq_existT
                                lv' (Specif.Coq_existT atm'
                                (Datatypes.Coq_pair __ (Datatypes.Coq_inl
                                s11)))}}};
                         Datatypes.Coq_inr _ ->
                          let {
                           s8 = preprocess_vsSahlq_ante_3_againTRY alpha1
                                  alpha2 lv1 s4 atm1 lv2 atm2}
                          in
                          case s8 of {
                           Specif.Coq_existT lv' s9 ->
                            case s9 of {
                             Specif.Coq_existT atm' p1 ->
                              case p1 of {
                               Datatypes.Coq_pair _ s10 -> Specif.Coq_existT
                                lv' (Specif.Coq_existT atm'
                                (Datatypes.Coq_pair __ (Datatypes.Coq_inl
                                s10)))}}}}}}};
                 Datatypes.Coq_inr _ ->
                  let {s4 = iHalpha4 hocc2b} in
                  case s4 of {
                   Specif.Coq_existT lv2 s5 ->
                    case s5 of {
                     Specif.Coq_existT atm2 p0 ->
                      case p0 of {
                       Datatypes.Coq_pair _ s6 ->
                        case s6 of {
                         Datatypes.Coq_inl s7 ->
                          let {
                           s8 = preprocess_vsSahlq_ante_7_againTRY alpha1
                                  alpha2 lv1 atm1 lv2 s7 atm2}
                          in
                          case s8 of {
                           Specif.Coq_existT lv' s9 ->
                            case s9 of {
                             Specif.Coq_existT atm' p1 ->
                              case p1 of {
                               Datatypes.Coq_pair _ s10 -> Specif.Coq_existT
                                lv' (Specif.Coq_existT atm'
                                (Datatypes.Coq_pair __ (Datatypes.Coq_inl
                                s10)))}}};
                         Datatypes.Coq_inr _ ->
                          let {
                           s7 = preprocess_vsSahlq_ante_9_againTRY alpha1
                                  alpha2 lv1 atm1 lv2 atm2}
                          in
                          case s7 of {
                           Specif.Coq_existT lv' s8 ->
                            case s8 of {
                             Specif.Coq_existT atm' _ -> Specif.Coq_existT
                              lv' (Specif.Coq_existT atm' (Datatypes.Coq_pair
                              __ (Datatypes.Coq_inr __)))}}}}}}}}}}}};
     Datatypes.Coq_false -> Logic.coq_False_rec}) (\_ _ _ _ _ _ ->
    Logic.coq_False_rec) (\_ _ _ _ _ _ -> Logic.coq_False_rec) (\_ _ _ _ _ ->
    Logic.coq_False_rec) (\_ _ _ _ _ -> Logic.coq_False_rec) alpha __ hocc

ex_P_ST :: Modal.Modal -> SecOrder.FOvariable -> SecOrder.Coq_predicate
ex_P_ST phi =
  Modal.coq_Modal_rec (\p _ -> ST_setup.coq_ST_pv p) (\_ iHphi x -> iHphi x)
    (\_ iHphi1 _ _ x -> iHphi1 x) (\_ iHphi1 _ _ x -> iHphi1 x)
    (\_ iHphi1 _ _ x -> iHphi1 x) (\_ iHphi x ->
    iHphi (Nat.add x (Datatypes.S Datatypes.O))) (\_ iHphi x ->
    iHphi (Nat.add x (Datatypes.S Datatypes.O))) phi

