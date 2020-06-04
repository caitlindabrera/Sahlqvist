module VsSahlq_proof1 where

import qualified Prelude
import qualified Datatypes
import qualified FOvars_in
import qualified Logic
import qualified Pred_in_SO
import qualified SO_syntax
import qualified Specif
import qualified ConjSO_exFO_relatSO
import qualified Replace_FOv_A
import qualified Same_struc

__ :: any
__ = Prelude.error "Logical or arity value used"

preprocess_vsSahlq_ante_predSO_againTRY :: SO_syntax.Coq_predicate ->
                                           SO_syntax.FOvariable ->
                                           Specif.Coq_sigT
                                           (Datatypes.Coq_list
                                           SO_syntax.FOvariable)
                                           (Specif.Coq_sigT
                                           SO_syntax.SecOrder
                                           (Datatypes.Coq_prod ()
                                           (Datatypes.Coq_sum
                                           SO_syntax.SecOrder ())))
preprocess_vsSahlq_ante_predSO_againTRY p f =
  Specif.Coq_existT Datatypes.Coq_nil (Specif.Coq_existT
    (SO_syntax.Coq_predSO p f) (Datatypes.Coq_pair __ (Datatypes.Coq_inr
    __)))

preprocess_vsSahlq_ante_exFO_againTRY :: SO_syntax.SecOrder ->
                                         SO_syntax.FOvariable ->
                                         SO_syntax.Coq_predicate -> (() ->
                                         SO_syntax.Coq_predicate ->
                                         Specif.Coq_sigT
                                         (Datatypes.Coq_list
                                         SO_syntax.FOvariable)
                                         (Specif.Coq_sigT SO_syntax.SecOrder
                                         (Datatypes.Coq_prod ()
                                         (Datatypes.Coq_sum
                                         SO_syntax.SecOrder ())))) ->
                                         Specif.Coq_sigT
                                         (Datatypes.Coq_list
                                         SO_syntax.FOvariable)
                                         (Specif.Coq_sigT SO_syntax.SecOrder
                                         (Datatypes.Coq_prod ()
                                         (Datatypes.Coq_sum
                                         SO_syntax.SecOrder ())))
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

preprocess_vsSahlq_ante_5_againTRY :: SO_syntax.SecOrder ->
                                      SO_syntax.SecOrder ->
                                      (Datatypes.Coq_list
                                      SO_syntax.FOvariable) ->
                                      SO_syntax.SecOrder ->
                                      (Datatypes.Coq_list
                                      SO_syntax.FOvariable) ->
                                      SO_syntax.SecOrder -> Specif.Coq_sigT
                                      (Datatypes.Coq_list
                                      SO_syntax.FOvariable)
                                      SO_syntax.SecOrder
preprocess_vsSahlq_ante_5_againTRY _ _ lv1 rel1 lv2 rel2 =
  Specif.Coq_existT
    (Datatypes.app
      (Replace_FOv_A.replace_FOv_A_list rel2
        (FOvars_in.list_closed_exFO rel1 lv1) lv2)
      (Replace_FOv_A.replace_FOv_A_list rel1
        (Replace_FOv_A.replace_FOv_A rel2
          (FOvars_in.list_closed_exFO rel1 lv1) lv2) lv1))
    (SO_syntax.Coq_conjSO
    (Replace_FOv_A.replace_FOv_A rel1
      (Replace_FOv_A.replace_FOv_A rel2 (FOvars_in.list_closed_exFO rel1 lv1)
        lv2) lv1)
    (Replace_FOv_A.replace_FOv_A rel2 (FOvars_in.list_closed_exFO rel1 lv1)
      lv2))

trying2 :: SO_syntax.SecOrder -> Specif.Coq_sigT
           (Datatypes.Coq_list SO_syntax.FOvariable)
           (Specif.Coq_sigT SO_syntax.SecOrder ())
trying2 alpha =
  SO_syntax.coq_SecOrder_rec (\_ _ _ _ -> Logic.coq_False_rec) (\f f0 _ _ ->
    Specif.Coq_existT Datatypes.Coq_nil (Specif.Coq_existT
    (SO_syntax.Coq_relatSO f f0) __)) (\_ _ _ _ -> Logic.coq_False_rec)
    (\_ _ _ _ _ -> Logic.coq_False_rec) (\f _ iHalpha _ _ ->
    let {s = iHalpha __ __} in
    case s of {
     Specif.Coq_existT lv s0 ->
      case s0 of {
       Specif.Coq_existT rel _ -> Specif.Coq_existT (Datatypes.Coq_cons f lv)
        (Specif.Coq_existT rel __)}}) (\_ _ _ _ -> Logic.coq_False_rec)
    (\alpha1 iHalpha1 alpha2 iHalpha2 _ _ ->
    case ConjSO_exFO_relatSO.conjSO_exFO_relatSO alpha1 of {
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

preprocess_vsSahlq_ante_notocc_againTRY :: SO_syntax.SecOrder ->
                                           Specif.Coq_sigT
                                           (Datatypes.Coq_list
                                           SO_syntax.FOvariable)
                                           (Specif.Coq_sigT
                                           SO_syntax.SecOrder ())
preprocess_vsSahlq_ante_notocc_againTRY alpha =
  let {s = trying2 alpha} in
  case s of {
   Specif.Coq_existT lv s0 ->
    case s0 of {
     Specif.Coq_existT rel _ -> Specif.Coq_existT lv (Specif.Coq_existT rel
      __)}}

preprocess_vsSahlq_ante_4_againTRY :: SO_syntax.SecOrder ->
                                      SO_syntax.SecOrder ->
                                      (Datatypes.Coq_list
                                      SO_syntax.FOvariable) ->
                                      SO_syntax.SecOrder ->
                                      (Datatypes.Coq_list
                                      SO_syntax.FOvariable) ->
                                      SO_syntax.SecOrder ->
                                      SO_syntax.SecOrder -> Specif.Coq_sigT
                                      (Datatypes.Coq_list
                                      SO_syntax.FOvariable)
                                      (Specif.Coq_sigT SO_syntax.SecOrder
                                      (Datatypes.Coq_prod ()
                                      SO_syntax.SecOrder))
preprocess_vsSahlq_ante_4_againTRY _ _ lv1 rel1 lv2 rel2 atm2 =
  let {
   s = Same_struc.same_struc_conjSO_ex
         (Replace_FOv_A.replace_FOv_A (SO_syntax.Coq_conjSO rel2 atm2)
           (FOvars_in.list_closed_exFO rel1 lv1) lv2) rel2 atm2}
  in
  case s of {
   Specif.Coq_existT rel2' s0 ->
    case s0 of {
     Specif.Coq_existT atm2' _ -> Specif.Coq_existT
      (Datatypes.app
        (Replace_FOv_A.replace_FOv_A_list (SO_syntax.Coq_conjSO rel2 atm2)
          (FOvars_in.list_closed_exFO rel1 lv1) lv2)
        (Replace_FOv_A.replace_FOv_A_list rel1
          (Replace_FOv_A.replace_FOv_A (SO_syntax.Coq_conjSO rel2 atm2)
            (FOvars_in.list_closed_exFO rel1 lv1) lv2) lv1))
      (Specif.Coq_existT atm2' (Datatypes.Coq_pair __ (SO_syntax.Coq_conjSO
      (Replace_FOv_A.replace_FOv_A rel1
        (Replace_FOv_A.replace_FOv_A (SO_syntax.Coq_conjSO rel2 atm2)
          (FOvars_in.list_closed_exFO rel1 lv1) lv2) lv1) rel2')))}}

preprocess_vsSahlq_ante_6_againTRY :: SO_syntax.SecOrder ->
                                      SO_syntax.SecOrder ->
                                      (Datatypes.Coq_list
                                      SO_syntax.FOvariable) ->
                                      SO_syntax.SecOrder ->
                                      (Datatypes.Coq_list
                                      SO_syntax.FOvariable) ->
                                      SO_syntax.SecOrder -> Specif.Coq_sigT
                                      (Datatypes.Coq_list
                                      SO_syntax.FOvariable)
                                      (Specif.Coq_sigT SO_syntax.SecOrder
                                      (Datatypes.Coq_prod ()
                                      SO_syntax.SecOrder))
preprocess_vsSahlq_ante_6_againTRY _ _ lv1 rel1 lv2 atm2 =
  Specif.Coq_existT
    (Datatypes.app
      (Replace_FOv_A.replace_FOv_A_list atm2
        (FOvars_in.list_closed_exFO rel1 lv1) lv2)
      (Replace_FOv_A.replace_FOv_A_list rel1
        (Replace_FOv_A.replace_FOv_A atm2
          (FOvars_in.list_closed_exFO rel1 lv1) lv2) lv1)) (Specif.Coq_existT
    (Replace_FOv_A.replace_FOv_A atm2 (FOvars_in.list_closed_exFO rel1 lv1)
      lv2) (Datatypes.Coq_pair __
    (Replace_FOv_A.replace_FOv_A rel1
      (Replace_FOv_A.replace_FOv_A atm2 (FOvars_in.list_closed_exFO rel1 lv1)
        lv2) lv1)))

preprocess_vsSahlq_ante_2_againTRY :: SO_syntax.SecOrder ->
                                      SO_syntax.SecOrder ->
                                      (Datatypes.Coq_list
                                      SO_syntax.FOvariable) ->
                                      SO_syntax.SecOrder ->
                                      SO_syntax.SecOrder ->
                                      (Datatypes.Coq_list
                                      SO_syntax.FOvariable) ->
                                      SO_syntax.SecOrder -> Specif.Coq_sigT
                                      (Datatypes.Coq_list
                                      SO_syntax.FOvariable)
                                      (Specif.Coq_sigT SO_syntax.SecOrder
                                      (Datatypes.Coq_prod ()
                                      (Specif.Coq_sigT SO_syntax.SecOrder ())))
preprocess_vsSahlq_ante_2_againTRY _ _ lv1 rel1 atm1 lv2 rel2 =
  let {
   s = Same_struc.same_struc_conjSO_ex
         (Replace_FOv_A.replace_FOv_A (SO_syntax.Coq_conjSO rel1 atm1)
           (Replace_FOv_A.replace_FOv_A rel2
             (FOvars_in.list_closed_exFO (SO_syntax.Coq_conjSO rel1 atm1)
               lv1) lv2) lv1) rel1 atm1}
  in
  case s of {
   Specif.Coq_existT rel1' s0 ->
    case s0 of {
     Specif.Coq_existT atm1' _ -> Specif.Coq_existT
      (Datatypes.app
        (Replace_FOv_A.replace_FOv_A_list rel2
          (FOvars_in.list_closed_exFO (SO_syntax.Coq_conjSO rel1 atm1) lv1)
          lv2)
        (Replace_FOv_A.replace_FOv_A_list (SO_syntax.Coq_conjSO rel1 atm1)
          (Replace_FOv_A.replace_FOv_A rel2
            (FOvars_in.list_closed_exFO (SO_syntax.Coq_conjSO rel1 atm1) lv1)
            lv2) lv1)) (Specif.Coq_existT atm1' (Datatypes.Coq_pair __
      (Specif.Coq_existT (SO_syntax.Coq_conjSO rel1'
      (Replace_FOv_A.replace_FOv_A rel2
        (FOvars_in.list_closed_exFO (SO_syntax.Coq_conjSO rel1 atm1) lv1)
        lv2)) __)))}}

preprocess_vsSahlq_ante_8_againTRY :: SO_syntax.SecOrder ->
                                      SO_syntax.SecOrder ->
                                      (Datatypes.Coq_list
                                      SO_syntax.FOvariable) ->
                                      SO_syntax.SecOrder ->
                                      (Datatypes.Coq_list
                                      SO_syntax.FOvariable) ->
                                      SO_syntax.SecOrder -> Specif.Coq_sigT
                                      (Datatypes.Coq_list
                                      SO_syntax.FOvariable)
                                      (Specif.Coq_sigT SO_syntax.SecOrder
                                      (Datatypes.Coq_prod ()
                                      SO_syntax.SecOrder))
preprocess_vsSahlq_ante_8_againTRY _ _ lv1 atm1 lv2 rel2 =
  Specif.Coq_existT
    (Datatypes.app
      (Replace_FOv_A.replace_FOv_A_list rel2
        (FOvars_in.list_closed_exFO atm1 lv1) lv2)
      (Replace_FOv_A.replace_FOv_A_list atm1
        (Replace_FOv_A.replace_FOv_A rel2
          (FOvars_in.list_closed_exFO atm1 lv1) lv2) lv1)) (Specif.Coq_existT
    (Replace_FOv_A.replace_FOv_A atm1
      (Replace_FOv_A.replace_FOv_A rel2 (FOvars_in.list_closed_exFO atm1 lv1)
        lv2) lv1) (Datatypes.Coq_pair __
    (Replace_FOv_A.replace_FOv_A rel2 (FOvars_in.list_closed_exFO atm1 lv1)
      lv2)))

preprocess_vsSahlq_ante_1_againTRY :: SO_syntax.SecOrder ->
                                      SO_syntax.SecOrder ->
                                      (Datatypes.Coq_list
                                      SO_syntax.FOvariable) ->
                                      SO_syntax.SecOrder ->
                                      SO_syntax.SecOrder ->
                                      (Datatypes.Coq_list
                                      SO_syntax.FOvariable) ->
                                      SO_syntax.SecOrder ->
                                      SO_syntax.SecOrder -> Specif.Coq_sigT
                                      (Datatypes.Coq_list
                                      SO_syntax.FOvariable)
                                      (Specif.Coq_sigT SO_syntax.SecOrder
                                      (Datatypes.Coq_prod ()
                                      SO_syntax.SecOrder))
preprocess_vsSahlq_ante_1_againTRY _ _ lv1 rel1 atm1 lv2 rel2 atm2 =
  let {
   s = Same_struc.same_struc_conjSO_ex
         (Replace_FOv_A.replace_FOv_A (SO_syntax.Coq_conjSO rel1 atm1)
           (Replace_FOv_A.replace_FOv_A (SO_syntax.Coq_conjSO rel2 atm2)
             (FOvars_in.list_closed_exFO (SO_syntax.Coq_conjSO rel1 atm1)
               lv1) lv2) lv1) rel1 atm1}
  in
  case s of {
   Specif.Coq_existT rel1' s0 ->
    case s0 of {
     Specif.Coq_existT atm1' _ ->
      let {
       s1 = Same_struc.same_struc_conjSO_ex
              (Replace_FOv_A.replace_FOv_A (SO_syntax.Coq_conjSO rel2 atm2)
                (FOvars_in.list_closed_exFO (SO_syntax.Coq_conjSO rel1 atm1)
                  lv1) lv2) rel2 atm2}
      in
      case s1 of {
       Specif.Coq_existT rel2' s2 ->
        case s2 of {
         Specif.Coq_existT atm2' _ -> Specif.Coq_existT
          (Datatypes.app
            (Replace_FOv_A.replace_FOv_A_list (SO_syntax.Coq_conjSO rel2
              atm2)
              (FOvars_in.list_closed_exFO (SO_syntax.Coq_conjSO rel1 atm1)
                lv1) lv2)
            (Replace_FOv_A.replace_FOv_A_list (SO_syntax.Coq_conjSO rel1
              atm1)
              (Replace_FOv_A.replace_FOv_A (SO_syntax.Coq_conjSO rel2 atm2)
                (FOvars_in.list_closed_exFO (SO_syntax.Coq_conjSO rel1 atm1)
                  lv1) lv2) lv1)) (Specif.Coq_existT (SO_syntax.Coq_conjSO
          atm1' atm2') (Datatypes.Coq_pair __ (SO_syntax.Coq_conjSO rel1'
          rel2')))}}}}

preprocess_vsSahlq_ante_3_againTRY :: SO_syntax.SecOrder ->
                                      SO_syntax.SecOrder ->
                                      (Datatypes.Coq_list
                                      SO_syntax.FOvariable) ->
                                      SO_syntax.SecOrder ->
                                      SO_syntax.SecOrder ->
                                      (Datatypes.Coq_list
                                      SO_syntax.FOvariable) ->
                                      SO_syntax.SecOrder -> Specif.Coq_sigT
                                      (Datatypes.Coq_list
                                      SO_syntax.FOvariable)
                                      (Specif.Coq_sigT SO_syntax.SecOrder
                                      (Datatypes.Coq_prod ()
                                      SO_syntax.SecOrder))
preprocess_vsSahlq_ante_3_againTRY _ _ lv1 rel1 atm1 lv2 atm2 =
  let {
   s = Same_struc.same_struc_conjSO_ex
         (Replace_FOv_A.replace_FOv_A (SO_syntax.Coq_conjSO rel1 atm1)
           (Replace_FOv_A.replace_FOv_A atm2
             (FOvars_in.list_closed_exFO (SO_syntax.Coq_conjSO rel1 atm1)
               lv1) lv2) lv1) rel1 atm1}
  in
  case s of {
   Specif.Coq_existT rel1' s0 ->
    case s0 of {
     Specif.Coq_existT atm1' _ -> Specif.Coq_existT
      (Datatypes.app
        (Replace_FOv_A.replace_FOv_A_list atm2
          (FOvars_in.list_closed_exFO (SO_syntax.Coq_conjSO rel1 atm1) lv1)
          lv2)
        (Replace_FOv_A.replace_FOv_A_list (SO_syntax.Coq_conjSO rel1 atm1)
          (Replace_FOv_A.replace_FOv_A atm2
            (FOvars_in.list_closed_exFO (SO_syntax.Coq_conjSO rel1 atm1) lv1)
            lv2) lv1)) (Specif.Coq_existT (SO_syntax.Coq_conjSO atm1'
      (Replace_FOv_A.replace_FOv_A atm2
        (FOvars_in.list_closed_exFO (SO_syntax.Coq_conjSO rel1 atm1) lv1)
        lv2)) (Datatypes.Coq_pair __ rel1'))}}

preprocess_vsSahlq_ante_7_againTRY :: SO_syntax.SecOrder ->
                                      SO_syntax.SecOrder ->
                                      (Datatypes.Coq_list
                                      SO_syntax.FOvariable) ->
                                      SO_syntax.SecOrder ->
                                      (Datatypes.Coq_list
                                      SO_syntax.FOvariable) ->
                                      SO_syntax.SecOrder ->
                                      SO_syntax.SecOrder -> Specif.Coq_sigT
                                      (Datatypes.Coq_list
                                      SO_syntax.FOvariable)
                                      (Specif.Coq_sigT SO_syntax.SecOrder
                                      (Datatypes.Coq_prod ()
                                      SO_syntax.SecOrder))
preprocess_vsSahlq_ante_7_againTRY _ _ lv1 atm1 lv2 rel2 atm2 =
  let {
   s = Same_struc.same_struc_conjSO_ex
         (Replace_FOv_A.replace_FOv_A (SO_syntax.Coq_conjSO rel2 atm2)
           (FOvars_in.list_closed_exFO atm1 lv1) lv2) rel2 atm2}
  in
  case s of {
   Specif.Coq_existT rel2' s0 ->
    case s0 of {
     Specif.Coq_existT atm2' _ -> Specif.Coq_existT
      (Datatypes.app
        (Replace_FOv_A.replace_FOv_A_list (SO_syntax.Coq_conjSO rel2 atm2)
          (FOvars_in.list_closed_exFO atm1 lv1) lv2)
        (Replace_FOv_A.replace_FOv_A_list atm1
          (Replace_FOv_A.replace_FOv_A (SO_syntax.Coq_conjSO rel2 atm2)
            (FOvars_in.list_closed_exFO atm1 lv1) lv2) lv1))
      (Specif.Coq_existT (SO_syntax.Coq_conjSO
      (Replace_FOv_A.replace_FOv_A atm1
        (Replace_FOv_A.replace_FOv_A (SO_syntax.Coq_conjSO rel2 atm2)
          (FOvars_in.list_closed_exFO atm1 lv1) lv2) lv1) atm2')
      (Datatypes.Coq_pair __ rel2'))}}

preprocess_vsSahlq_ante_9_againTRY :: SO_syntax.SecOrder ->
                                      SO_syntax.SecOrder ->
                                      (Datatypes.Coq_list
                                      SO_syntax.FOvariable) ->
                                      SO_syntax.SecOrder ->
                                      (Datatypes.Coq_list
                                      SO_syntax.FOvariable) ->
                                      SO_syntax.SecOrder -> Specif.Coq_sigT
                                      (Datatypes.Coq_list
                                      SO_syntax.FOvariable)
                                      (Specif.Coq_sigT SO_syntax.SecOrder ())
preprocess_vsSahlq_ante_9_againTRY _ _ lv1 atm1 lv2 atm2 =
  Specif.Coq_existT
    (Datatypes.app
      (Replace_FOv_A.replace_FOv_A_list atm2
        (FOvars_in.list_closed_exFO atm1 lv1) lv2)
      (Replace_FOv_A.replace_FOv_A_list atm1
        (Replace_FOv_A.replace_FOv_A atm2
          (FOvars_in.list_closed_exFO atm1 lv1) lv2) lv1)) (Specif.Coq_existT
    (SO_syntax.Coq_conjSO
    (Replace_FOv_A.replace_FOv_A atm1
      (Replace_FOv_A.replace_FOv_A atm2 (FOvars_in.list_closed_exFO atm1 lv1)
        lv2) lv1)
    (Replace_FOv_A.replace_FOv_A atm2 (FOvars_in.list_closed_exFO atm1 lv1)
      lv2)) __)

preprocess_vsSahlq_ante_againTRY :: SO_syntax.SecOrder ->
                                    SO_syntax.Coq_predicate ->
                                    Specif.Coq_sigT
                                    (Datatypes.Coq_list SO_syntax.FOvariable)
                                    (Specif.Coq_sigT SO_syntax.SecOrder
                                    (Datatypes.Coq_prod ()
                                    (Datatypes.Coq_sum SO_syntax.SecOrder ())))
preprocess_vsSahlq_ante_againTRY alpha hocc =
  SO_syntax.coq_SecOrder_rec (\p f _ _ ->
    preprocess_vsSahlq_ante_predSO_againTRY p f) (\_ _ _ _ ->
    Logic.coq_False_rec) (\_ _ _ _ -> Logic.coq_False_rec) (\_ _ _ _ _ ->
    Logic.coq_False_rec) (\f alpha0 iHalpha _ hocc0 ->
    preprocess_vsSahlq_ante_exFO_againTRY alpha0 f hocc0 iHalpha)
    (\_ _ _ _ -> Logic.coq_False_rec)
    (\alpha1 iHalpha1 alpha2 iHalpha2 _ hocc0 ->
    case ConjSO_exFO_relatSO.conjSO_exFO_relatSO alpha1 of {
     Datatypes.Coq_true ->
      let {iHalpha3 = iHalpha1 __} in
      let {iHalpha4 = iHalpha2 __} in
      let {s = Pred_in_SO.trying1 alpha1} in
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
                       case Pred_in_SO.coq_Pred_in_SO_conjSO_comp alpha3
                              alpha4 p of {
                        Datatypes.Coq_pair x _ -> x}}
                     in
                     let {hocc1 = h0 alpha1 alpha2 hocc0 __} in
                     case hocc1 of {
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
        let {s0 = Pred_in_SO.trying1 alpha2} in
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

