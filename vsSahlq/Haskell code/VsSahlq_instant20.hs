module VsSahlq_instant20 where

import qualified Prelude
import qualified Datatypes
import qualified Logic
import qualified Modal
import qualified Nat
import qualified Rep_Pred_FOv
import qualified ST_setup
import qualified SecOrder
import qualified Specif
import qualified VsSahlq_instant13
import qualified VsSahlq_instant19
import qualified VsSahlq_instant3
import qualified VsSahlq_instant9
import qualified VsSahlq_preprocessing1
import qualified VsSahlq_preprocessing3

__ :: any
__ = Prelude.error "Logical or arity value used"

preprocess_vsSahlq_ante_againTRY_loc :: SecOrder.SecOrder ->
                                        SecOrder.FOvariable ->
                                        SecOrder.Coq_predicate ->
                                        Specif.Coq_sigT
                                        (Datatypes.Coq_list
                                        SecOrder.FOvariable)
                                        (Specif.Coq_sigT SecOrder.SecOrder
                                        (Datatypes.Coq_prod ()
                                        (Datatypes.Coq_sum SecOrder.SecOrder
                                        ())))
preprocess_vsSahlq_ante_againTRY_loc =
  Prelude.error "AXIOM TO BE REALIZED"

vsS_preprocessing_Step1_1_againTRY'_withex''_loc :: Modal.Modal ->
                                                    Modal.Modal ->
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
                                                    (Datatypes.Coq_prod 
                                                    ()
                                                    (Datatypes.Coq_prod 
                                                    ()
                                                    (Datatypes.Coq_sum
                                                    SecOrder.SecOrder 
                                                    ()))))
vsS_preprocessing_Step1_1_againTRY'_withex''_loc _ phi2 rel atm x lv =
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

vsS_preprocessing_Step1_3_againTRY'_withex'_loc :: Modal.Modal -> Modal.Modal
                                                   -> SecOrder.SecOrder ->
                                                   SecOrder.FOvariable ->
                                                   (Datatypes.Coq_list
                                                   SecOrder.FOvariable) ->
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
                                                   SecOrder.SecOrder 
                                                   ()))))
vsS_preprocessing_Step1_3_againTRY'_withex'_loc =
  Prelude.error "AXIOM TO BE REALIZED"

vsS_preprocessing_Step1_pre_againTRY'_withex'_loc :: Modal.Modal ->
                                                     Modal.Modal ->
                                                     SecOrder.FOvariable ->
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
                                                     SecOrder.SecOrder 
                                                     ()))))
vsS_preprocessing_Step1_pre_againTRY'_withex'_loc phi1 phi2 x =
  let {
   h1 = preprocess_vsSahlq_ante_againTRY_loc (ST_setup.coq_ST phi1 x) x
          (VsSahlq_instant13.ex_P_ST phi1 x)}
  in
  case h1 of {
   Specif.Coq_existT lv s ->
    case s of {
     Specif.Coq_existT atm p ->
      case p of {
       Datatypes.Coq_pair _ s0 ->
        case s0 of {
         Datatypes.Coq_inl s1 ->
          vsS_preprocessing_Step1_1_againTRY'_withex''_loc phi1 phi2 s1 atm x
            lv;
         Datatypes.Coq_inr _ ->
          vsS_preprocessing_Step1_3_againTRY'_withex'_loc phi1 phi2 atm x lv}}}}

hopeful4_REV'_withex'_FULL :: (Datatypes.Coq_list SecOrder.Coq_predicate) ->
                              Datatypes.Coq_nat -> Modal.Modal -> Modal.Modal
                              -> Specif.Coq_sigT
                              (Datatypes.Coq_list SecOrder.FOvariable)
                              (Specif.Coq_sigT SecOrder.SecOrder
                              (Datatypes.Coq_prod ()
                              (Datatypes.Coq_sum SecOrder.SecOrder ())))
hopeful4_REV'_withex'_FULL _ xn phi1 phi2 =
  let {
   s = VsSahlq_instant19.vsS_preprocessing_Step1_pre_againTRY'_withex' phi1
         phi2 xn}
  in
  case s of {
   Specif.Coq_existT lv s0 ->
    case s0 of {
     Specif.Coq_existT atm p ->
      case p of {
       Datatypes.Coq_pair _ p0 ->
        case p0 of {
         Datatypes.Coq_pair _ s1 ->
          case s1 of {
           Datatypes.Coq_inl s2 -> Specif.Coq_existT lv (Specif.Coq_existT
            atm (Datatypes.Coq_pair __ (Datatypes.Coq_inl s2)));
           Datatypes.Coq_inr _ -> Specif.Coq_existT lv (Specif.Coq_existT atm
            (Datatypes.Coq_pair __ (Datatypes.Coq_inr __)))}}}}}

hopeful4_REV'_withex'_FULL_loc :: (Datatypes.Coq_list SecOrder.Coq_predicate)
                                  -> Datatypes.Coq_nat -> Modal.Modal ->
                                  Modal.Modal -> Specif.Coq_sigT
                                  (Datatypes.Coq_list SecOrder.FOvariable)
                                  (Specif.Coq_sigT SecOrder.SecOrder
                                  (Datatypes.Coq_prod ()
                                  (Datatypes.Coq_sum SecOrder.SecOrder ())))
hopeful4_REV'_withex'_FULL_loc =
  Prelude.error "AXIOM TO BE REALIZED"

hopeful4_REV'_withex'_FULL_allFO :: (Datatypes.Coq_list
                                    SecOrder.Coq_predicate) ->
                                    Datatypes.Coq_nat -> Modal.Modal ->
                                    Modal.Modal -> Specif.Coq_sigT
                                    (Datatypes.Coq_list SecOrder.FOvariable)
                                    (Specif.Coq_sigT SecOrder.SecOrder
                                    (Datatypes.Coq_prod ()
                                    (Datatypes.Coq_sum SecOrder.SecOrder ())))
hopeful4_REV'_withex'_FULL_allFO lP xn phi1 phi2 =
  let {s = hopeful4_REV'_withex'_FULL lP xn phi1 phi2} in
  case s of {
   Specif.Coq_existT lx s0 ->
    case s0 of {
     Specif.Coq_existT atm p ->
      case p of {
       Datatypes.Coq_pair _ s1 ->
        case s1 of {
         Datatypes.Coq_inl s2 -> Specif.Coq_existT lx (Specif.Coq_existT atm
          (Datatypes.Coq_pair __ (Datatypes.Coq_inl s2)));
         Datatypes.Coq_inr _ -> Specif.Coq_existT lx (Specif.Coq_existT atm
          (Datatypes.Coq_pair __ (Datatypes.Coq_inr __)))}}}}

hopeful4_REV'_withex'_FULL_allFO_in :: (Datatypes.Coq_list
                                       SecOrder.Coq_predicate) ->
                                       Datatypes.Coq_nat -> Modal.Modal ->
                                       Modal.Modal -> Specif.Coq_sigT
                                       (Datatypes.Coq_list
                                       SecOrder.FOvariable)
                                       (Specif.Coq_sigT SecOrder.SecOrder
                                       (Datatypes.Coq_prod ()
                                       (Datatypes.Coq_sum SecOrder.SecOrder
                                       ())))
hopeful4_REV'_withex'_FULL_allFO_in lP xn phi1 phi2 =
  let {s = hopeful4_REV'_withex'_FULL_allFO lP xn phi1 phi2} in
  case s of {
   Specif.Coq_existT lx s0 ->
    case s0 of {
     Specif.Coq_existT atm p ->
      case p of {
       Datatypes.Coq_pair _ s1 ->
        case s1 of {
         Datatypes.Coq_inl s2 -> Specif.Coq_existT lx (Specif.Coq_existT atm
          (Datatypes.Coq_pair __ (Datatypes.Coq_inl s2)));
         Datatypes.Coq_inr _ -> Specif.Coq_existT lx (Specif.Coq_existT atm
          (Datatypes.Coq_pair __ (Datatypes.Coq_inr __)))}}}}

hopeful4_REV'_withex'_FULL_allFO_in_loc :: (Datatypes.Coq_list
                                           SecOrder.Coq_predicate) ->
                                           Datatypes.Coq_nat -> Modal.Modal
                                           -> Modal.Modal -> Specif.Coq_sigT
                                           (Datatypes.Coq_list
                                           SecOrder.FOvariable)
                                           (Specif.Coq_sigT SecOrder.SecOrder
                                           (Datatypes.Coq_prod ()
                                           (Datatypes.Coq_sum
                                           SecOrder.SecOrder ())))
hopeful4_REV'_withex'_FULL_allFO_in_loc lP xn phi1 phi2 =
  let {s = hopeful4_REV'_withex'_FULL_loc lP xn phi1 phi2} in
  case s of {
   Specif.Coq_existT lx s0 ->
    case s0 of {
     Specif.Coq_existT atm p ->
      case p of {
       Datatypes.Coq_pair _ s1 ->
        case s1 of {
         Datatypes.Coq_inl s2 -> Specif.Coq_existT lx (Specif.Coq_existT atm
          (Datatypes.Coq_pair __ (Datatypes.Coq_inl s2)));
         Datatypes.Coq_inr _ -> Specif.Coq_existT lx (Specif.Coq_existT atm
          (Datatypes.Coq_pair __ (Datatypes.Coq_inr __)))}}}}

vsSahlq_full_SO_pre :: Datatypes.Coq_nat -> Modal.Modal -> Modal.Modal ->
                       Specif.Coq_sigT
                       (Datatypes.Coq_list SecOrder.FOvariable)
                       (Specif.Coq_sigT SecOrder.SecOrder
                       (Datatypes.Coq_prod ()
                       (Datatypes.Coq_sum SecOrder.SecOrder ())))
vsSahlq_full_SO_pre xn phi1 phi2 =
  hopeful4_REV'_withex'_FULL_allFO_in
    (SecOrder.preds_in (SecOrder.Coq_allFO xn
      (ST_setup.coq_ST (Modal.Coq_mimpl phi1 phi2) xn))) xn phi1 phi2

vsSahlq_full_SO_pre_loc :: Datatypes.Coq_nat -> Modal.Modal -> Modal.Modal ->
                           Specif.Coq_sigT
                           (Datatypes.Coq_list SecOrder.FOvariable)
                           (Specif.Coq_sigT SecOrder.SecOrder
                           (Datatypes.Coq_prod ()
                           (Datatypes.Coq_sum SecOrder.SecOrder ())))
vsSahlq_full_SO_pre_loc xn phi1 phi2 =
  hopeful4_REV'_withex'_FULL_allFO_in_loc
    (SecOrder.preds_in (ST_setup.coq_ST (Modal.Coq_mimpl phi1 phi2) xn)) xn
    phi1 phi2

vsSahlq_full_SO :: Datatypes.Coq_nat -> Modal.Modal -> Modal.Modal ->
                   SecOrder.SecOrder
vsSahlq_full_SO xn phi1 phi2 =
  let {s = vsSahlq_full_SO_pre xn phi1 phi2} in
  case s of {
   Specif.Coq_existT lx s0 ->
    case s0 of {
     Specif.Coq_existT atm p ->
      case p of {
       Datatypes.Coq_pair _ s1 ->
        case s1 of {
         Datatypes.Coq_inl s2 -> SecOrder.Coq_allFO xn
          (Rep_Pred_FOv.replace_pred_l
            (VsSahlq_preprocessing1.list_closed_allFO (SecOrder.Coq_implSO
              (SecOrder.Coq_conjSO s2 atm)
              (VsSahlq_instant9.newnew_pre
                (VsSahlq_instant9.instant_cons_empty' (SecOrder.Coq_conjSO s2
                  atm) (ST_setup.coq_ST phi2 xn))
                (VsSahlq_instant9.rem_FOv
                  (VsSahlq_instant9.coq_FOvars_in
                    (VsSahlq_instant9.instant_cons_empty'
                      (SecOrder.Coq_conjSO s2 atm) (ST_setup.coq_ST phi2 xn)))
                  xn)
                (VsSahlq_instant9.rev_seq (Datatypes.S
                  (Nat.max
                    (VsSahlq_preprocessing1.max_FOv (SecOrder.Coq_implSO
                      (SecOrder.Coq_conjSO s2 atm)
                      (ST_setup.coq_ST phi2 xn))) xn))
                  (Datatypes.length
                    (VsSahlq_instant9.rem_FOv
                      (VsSahlq_instant9.coq_FOvars_in
                        (VsSahlq_instant9.instant_cons_empty'
                          (SecOrder.Coq_conjSO s2 atm)
                          (ST_setup.coq_ST phi2 xn))) xn))))) lx)
            (SecOrder.preds_in
              (ST_setup.coq_ST (Modal.Coq_mimpl phi1 phi2) xn))
            (VsSahlq_instant3.list_Var
              (Datatypes.length
                (SecOrder.preds_in
                  (ST_setup.coq_ST (Modal.Coq_mimpl phi1 phi2) xn)))
              (VsSahlq_instant19.new_FOv_pp_pre2 atm))
            (VsSahlq_instant3.vsS_syn_l
              (VsSahlq_instant3.coq_FOv_att_P_l (SecOrder.Coq_conjSO s2 atm)
                (SecOrder.preds_in
                  (ST_setup.coq_ST (Modal.Coq_mimpl phi1 phi2) xn)))
              (VsSahlq_instant19.new_FOv_pp_pre2 atm)));
         Datatypes.Coq_inr _ -> SecOrder.Coq_allFO xn
          (Rep_Pred_FOv.replace_pred_l
            (VsSahlq_preprocessing1.list_closed_allFO (SecOrder.Coq_implSO
              atm
              (VsSahlq_instant9.newnew_pre
                (VsSahlq_instant9.instant_cons_empty' atm
                  (ST_setup.coq_ST phi2 xn))
                (VsSahlq_instant9.rem_FOv
                  (VsSahlq_instant9.coq_FOvars_in
                    (VsSahlq_instant9.instant_cons_empty' atm
                      (ST_setup.coq_ST phi2 xn))) xn)
                (VsSahlq_instant9.rev_seq (Datatypes.S
                  (Nat.max
                    (VsSahlq_preprocessing1.max_FOv (SecOrder.Coq_implSO atm
                      (ST_setup.coq_ST phi2 xn))) xn))
                  (Datatypes.length
                    (VsSahlq_instant9.rem_FOv
                      (VsSahlq_instant9.coq_FOvars_in
                        (VsSahlq_instant9.instant_cons_empty' atm
                          (ST_setup.coq_ST phi2 xn))) xn))))) lx)
            (SecOrder.preds_in
              (ST_setup.coq_ST (Modal.Coq_mimpl phi1 phi2) xn))
            (VsSahlq_instant3.list_Var
              (Datatypes.length
                (SecOrder.preds_in
                  (ST_setup.coq_ST (Modal.Coq_mimpl phi1 phi2) xn)))
              (VsSahlq_instant19.new_FOv_pp_pre2 atm))
            (VsSahlq_instant3.vsS_syn_l
              (VsSahlq_instant3.coq_FOv_att_P_l atm
                (SecOrder.preds_in
                  (ST_setup.coq_ST (Modal.Coq_mimpl phi1 phi2) xn)))
              (VsSahlq_instant19.new_FOv_pp_pre2 atm)))}}}}

vsSahlq_full_SO_loc :: Datatypes.Coq_nat -> Modal.Modal -> Modal.Modal ->
                       SecOrder.SecOrder
vsSahlq_full_SO_loc xn phi1 phi2 =
  let {s = vsSahlq_full_SO_pre_loc xn phi1 phi2} in
  case s of {
   Specif.Coq_existT lx s0 ->
    case s0 of {
     Specif.Coq_existT atm p ->
      case p of {
       Datatypes.Coq_pair _ s1 ->
        case s1 of {
         Datatypes.Coq_inl s2 ->
          Rep_Pred_FOv.replace_pred_l
            (VsSahlq_preprocessing1.list_closed_allFO (SecOrder.Coq_implSO
              (SecOrder.Coq_conjSO s2 atm)
              (VsSahlq_instant9.newnew_pre
                (VsSahlq_instant9.instant_cons_empty' (SecOrder.Coq_conjSO s2
                  atm) (ST_setup.coq_ST phi2 xn))
                (VsSahlq_instant9.rem_FOv
                  (VsSahlq_instant9.coq_FOvars_in
                    (VsSahlq_instant9.instant_cons_empty'
                      (SecOrder.Coq_conjSO s2 atm) (ST_setup.coq_ST phi2 xn)))
                  xn)
                (VsSahlq_instant9.rev_seq (Datatypes.S
                  (Nat.max
                    (VsSahlq_preprocessing1.max_FOv (SecOrder.Coq_implSO
                      (SecOrder.Coq_conjSO s2 atm)
                      (ST_setup.coq_ST phi2 xn))) xn))
                  (Datatypes.length
                    (VsSahlq_instant9.rem_FOv
                      (VsSahlq_instant9.coq_FOvars_in
                        (VsSahlq_instant9.instant_cons_empty'
                          (SecOrder.Coq_conjSO s2 atm)
                          (ST_setup.coq_ST phi2 xn))) xn))))) lx)
            (SecOrder.preds_in
              (ST_setup.coq_ST (Modal.Coq_mimpl phi1 phi2) xn))
            (VsSahlq_instant3.list_Var
              (Datatypes.length
                (SecOrder.preds_in
                  (ST_setup.coq_ST (Modal.Coq_mimpl phi1 phi2) xn)))
              (VsSahlq_instant19.new_FOv_pp_pre2 atm))
            (VsSahlq_instant3.vsS_syn_l
              (VsSahlq_instant3.coq_FOv_att_P_l (SecOrder.Coq_conjSO s2 atm)
                (SecOrder.preds_in
                  (ST_setup.coq_ST (Modal.Coq_mimpl phi1 phi2) xn)))
              (VsSahlq_instant19.new_FOv_pp_pre2 atm));
         Datatypes.Coq_inr _ ->
          Rep_Pred_FOv.replace_pred_l
            (VsSahlq_preprocessing1.list_closed_allFO (SecOrder.Coq_implSO
              atm
              (VsSahlq_instant9.newnew_pre
                (VsSahlq_instant9.instant_cons_empty' atm
                  (ST_setup.coq_ST phi2 xn))
                (VsSahlq_instant9.rem_FOv
                  (VsSahlq_instant9.coq_FOvars_in
                    (VsSahlq_instant9.instant_cons_empty' atm
                      (ST_setup.coq_ST phi2 xn))) xn)
                (VsSahlq_instant9.rev_seq (Datatypes.S
                  (Nat.max
                    (VsSahlq_preprocessing1.max_FOv (SecOrder.Coq_implSO atm
                      (ST_setup.coq_ST phi2 xn))) xn))
                  (Datatypes.length
                    (VsSahlq_instant9.rem_FOv
                      (VsSahlq_instant9.coq_FOvars_in
                        (VsSahlq_instant9.instant_cons_empty' atm
                          (ST_setup.coq_ST phi2 xn))) xn))))) lx)
            (SecOrder.preds_in
              (ST_setup.coq_ST (Modal.Coq_mimpl phi1 phi2) xn))
            (VsSahlq_instant3.list_Var
              (Datatypes.length
                (SecOrder.preds_in
                  (ST_setup.coq_ST (Modal.Coq_mimpl phi1 phi2) xn)))
              (VsSahlq_instant19.new_FOv_pp_pre2 atm))
            (VsSahlq_instant3.vsS_syn_l
              (VsSahlq_instant3.coq_FOv_att_P_l atm
                (SecOrder.preds_in
                  (ST_setup.coq_ST (Modal.Coq_mimpl phi1 phi2) xn)))
              (VsSahlq_instant19.new_FOv_pp_pre2 atm))}}}}

vsSahlq_full_Modal_sep :: Modal.Modal -> Modal.Modal -> SecOrder.SecOrder
vsSahlq_full_Modal_sep phi1 phi2 =
  vsSahlq_full_SO Datatypes.O phi1 phi2

vsSahlq_full_Modal_sep_loc :: Modal.Modal -> Modal.Modal -> Specif.Coq_sigT
                              SecOrder.SecOrder ()
vsSahlq_full_Modal_sep_loc phi1 phi2 =
  let {s = vsSahlq_full_SO_loc Datatypes.O phi1 phi2} in
  Specif.Coq_existT s __

vsSahlq_full_Modal_loc :: Modal.Modal -> Specif.Coq_sigT SecOrder.SecOrder ()
vsSahlq_full_Modal_loc phi =
  case phi of {
   Modal.Coq_mimpl phi1 phi2 ->
    case VsSahlq_preprocessing1.vsSahlq_ante phi1 of {
     Datatypes.Coq_true -> vsSahlq_full_Modal_sep_loc phi1 phi2;
     Datatypes.Coq_false -> Logic.coq_False_rec};
   _ -> Logic.coq_False_rec}

vsSahlq_full_Modal :: Modal.Modal -> SecOrder.SecOrder
vsSahlq_full_Modal phi =
  case phi of {
   Modal.Coq_mimpl phi1 phi2 ->
    case VsSahlq_preprocessing1.vsSahlq_ante phi1 of {
     Datatypes.Coq_true -> vsSahlq_full_Modal_sep phi1 phi2;
     Datatypes.Coq_false -> Logic.coq_False_rec};
   _ -> Logic.coq_False_rec}

