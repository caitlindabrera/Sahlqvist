module VsSahlq_instant19 where

import qualified Prelude
import qualified Datatypes
import qualified Modal
import qualified PeanoNat
import qualified ST_setup
import qualified SecOrder
import qualified Specif
import qualified VsSahlq_instant13
import qualified VsSahlq_preprocessing1
import qualified VsSahlq_preprocessing2
import qualified VsSahlq_preprocessing3

__ :: any
__ = Prelude.error "Logical or arity value used"

first_occ_P_n :: (Datatypes.Coq_list SecOrder.Coq_predicate) ->
                 SecOrder.Coq_predicate -> Datatypes.Coq_nat ->
                 Datatypes.Coq_nat
first_occ_P_n lP p n =
  case lP of {
   Datatypes.Coq_nil -> Datatypes.O;
   Datatypes.Coq_cons q lP' ->
    case PeanoNat._Nat__eqb p q of {
     Datatypes.Coq_true -> n;
     Datatypes.Coq_false -> first_occ_P_n lP' p (Datatypes.S n)}}

first_occ_P :: (Datatypes.Coq_list SecOrder.Coq_predicate) ->
               SecOrder.Coq_predicate -> Datatypes.Coq_nat
first_occ_P lP p =
  first_occ_P_n lP p (Datatypes.S Datatypes.O)

cap_pred_lx :: (Datatypes.Coq_list SecOrder.Coq_predicate) ->
               (Datatypes.Coq_list SecOrder.Coq_predicate) ->
               (Datatypes.Coq_list SecOrder.FOvariable) -> Datatypes.Coq_list
               SecOrder.FOvariable
cap_pred_lx l1 l2 lx =
  case l1 of {
   Datatypes.Coq_nil -> Datatypes.Coq_nil;
   Datatypes.Coq_cons p l1' ->
    case lx of {
     Datatypes.Coq_nil -> Datatypes.Coq_nil;
     Datatypes.Coq_cons x lx' ->
      case VsSahlq_preprocessing2.is_in_pred p l2 of {
       Datatypes.Coq_true -> Datatypes.Coq_cons x (cap_pred_lx l1' l2 lx');
       Datatypes.Coq_false -> cap_pred_lx l1' l2 lx'}}}

new_FOv_pp_pre2 :: SecOrder.SecOrder -> Datatypes.Coq_nat
new_FOv_pp_pre2 alpha =
  Datatypes.S (VsSahlq_preprocessing1.max_FOv alpha)

vsS_preprocessing_Step1_1_againTRY'_withex'' :: Modal.Modal -> Modal.Modal ->
                                                SecOrder.SecOrder ->
                                                SecOrder.SecOrder ->
                                                SecOrder.FOvariable ->
                                                (Datatypes.Coq_list
                                                SecOrder.FOvariable) ->
                                                Specif.Coq_sigT
                                                (Datatypes.Coq_list
                                                SecOrder.FOvariable)
                                                (Specif.Coq_sigT
                                                SecOrder.SecOrder
                                                (Datatypes.Coq_prod ()
                                                (Datatypes.Coq_prod ()
                                                (Datatypes.Coq_sum
                                                SecOrder.SecOrder ()))))
vsS_preprocessing_Step1_1_againTRY'_withex'' _ phi2 rel atm x lv =
  let {
   s = VsSahlq_preprocessing3.rename_FOv_A_rel_atm lv rel atm
         (ST_setup.coq_ST phi2 x)}
  in
  case s of {
   Specif.Coq_existT rel' s0 ->
    case s0 of {
     Specif.Coq_existT atm' _ -> Specif.Coq_existT
      (VsSahlq_preprocessing1.rename_FOv_A_list (SecOrder.Coq_conjSO rel atm)
        (ST_setup.coq_ST phi2 x) lv) (Specif.Coq_existT atm'
      (Datatypes.Coq_pair __ (Datatypes.Coq_pair __ (Datatypes.Coq_inl
      rel'))))}}

vsS_preprocessing_Step1_3_againTRY'_withex' :: Modal.Modal -> Modal.Modal ->
                                               SecOrder.SecOrder ->
                                               SecOrder.FOvariable ->
                                               (Datatypes.Coq_list
                                               SecOrder.FOvariable) ->
                                               Specif.Coq_sigT
                                               (Datatypes.Coq_list
                                               SecOrder.FOvariable)
                                               (Specif.Coq_sigT
                                               SecOrder.SecOrder
                                               (Datatypes.Coq_prod ()
                                               (Datatypes.Coq_prod ()
                                               (Datatypes.Coq_sum
                                               SecOrder.SecOrder ()))))
vsS_preprocessing_Step1_3_againTRY'_withex' _ phi2 atm x lv =
  Specif.Coq_existT
    (VsSahlq_preprocessing1.rename_FOv_A_list atm (ST_setup.coq_ST phi2 x)
      lv) (Specif.Coq_existT
    (VsSahlq_preprocessing1.rename_FOv_A atm (ST_setup.coq_ST phi2 x) lv)
    (Datatypes.Coq_pair __ (Datatypes.Coq_pair __ (Datatypes.Coq_inr __))))

vsS_preprocessing_Step1_pre_againTRY'_withex' :: Modal.Modal -> Modal.Modal
                                                 -> SecOrder.FOvariable ->
                                                 Specif.Coq_sigT
                                                 (Datatypes.Coq_list
                                                 SecOrder.FOvariable)
                                                 (Specif.Coq_sigT
                                                 SecOrder.SecOrder
                                                 (Datatypes.Coq_prod 
                                                 ()
                                                 (Datatypes.Coq_prod 
                                                 ()
                                                 (Datatypes.Coq_sum
                                                 SecOrder.SecOrder ()))))
vsS_preprocessing_Step1_pre_againTRY'_withex' phi1 phi2 x =
  let {
   h1 = VsSahlq_instant13.preprocess_vsSahlq_ante_againTRY
          (ST_setup.coq_ST phi1 x) (VsSahlq_instant13.ex_P_ST phi1 x)}
  in
  case h1 of {
   Specif.Coq_existT lv s ->
    case s of {
     Specif.Coq_existT atm p ->
      case p of {
       Datatypes.Coq_pair _ s0 ->
        case s0 of {
         Datatypes.Coq_inl s1 ->
          vsS_preprocessing_Step1_1_againTRY'_withex'' phi1 phi2 s1 atm x lv;
         Datatypes.Coq_inr _ ->
          vsS_preprocessing_Step1_3_againTRY'_withex' phi1 phi2 atm x lv}}}}

