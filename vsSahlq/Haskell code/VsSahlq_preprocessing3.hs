module VsSahlq_preprocessing3 where

import qualified Prelude
import qualified Datatypes
import qualified Modal
import qualified SecOrder
import qualified Specif
import qualified VsSahlq_preprocessing1

__ :: any
__ = Prelude.error "Logical or arity value used"

rename_FOv_A_rel_atm :: (Datatypes.Coq_list SecOrder.FOvariable) ->
                        SecOrder.SecOrder -> SecOrder.SecOrder ->
                        SecOrder.SecOrder -> Specif.Coq_sigT
                        SecOrder.SecOrder
                        (Specif.Coq_sigT SecOrder.SecOrder ())
rename_FOv_A_rel_atm lv rel atm beta =
  Datatypes.list_rec (\rel0 atm0 _ _ _ -> Specif.Coq_existT rel0
    (Specif.Coq_existT atm0 __)) (\a lv0 _ rel0 atm0 beta0 _ _ ->
    let {
     s = VsSahlq_preprocessing1.same_struc_conjSO_ex
           (VsSahlq_preprocessing1.rename_FOv_A_pre
             (VsSahlq_preprocessing1.strip_exFO
               (VsSahlq_preprocessing1.rename_FOv_max_conj
                 (VsSahlq_preprocessing1.list_closed_exFO
                   (SecOrder.Coq_conjSO rel0 atm0) lv0) beta0 a)
               (Datatypes.length lv0)) beta0
             (VsSahlq_preprocessing1.strip_exFO_list
               (VsSahlq_preprocessing1.rename_FOv_max_conj
                 (VsSahlq_preprocessing1.list_closed_exFO
                   (SecOrder.Coq_conjSO rel0 atm0) lv0) beta0 a)
               (Datatypes.length lv0)) (Datatypes.length lv0)) rel0 atm0}
    in
    case s of {
     Specif.Coq_existT rel'' s0 ->
      case s0 of {
       Specif.Coq_existT atm'' _ -> Specif.Coq_existT rel''
        (Specif.Coq_existT atm'' __)}}) lv rel atm beta __ __

vsSahlq_dest_ante :: Modal.Modal -> Modal.Modal
vsSahlq_dest_ante phi =
  case phi of {
   Modal.Coq_mimpl psi1 _ -> psi1;
   _ -> phi}

vsSahlq_dest_cons :: Modal.Modal -> Modal.Modal
vsSahlq_dest_cons phi =
  case phi of {
   Modal.Coq_mimpl _ psi2 -> psi2;
   _ -> phi}

