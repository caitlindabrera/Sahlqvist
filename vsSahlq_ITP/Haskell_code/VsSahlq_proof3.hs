module VsSahlq_proof3 where

import qualified Prelude
import qualified Datatypes
import qualified FOvars_in
import qualified Modal_syntax
import qualified PeanoNat
import qualified Rep_Pred_FOv
import qualified SO_syntax
import qualified ST
import qualified Specif
import qualified Instant_cons_empty
import qualified Max_min
import qualified Newnew
import qualified Nlist_syn_eg
import qualified Preds_in
import qualified Replace_FOv_A
import qualified Replace_FOv_max_conj
import qualified Rev_seq
import qualified Same_struc
import qualified VsS_syn_sem
import qualified VsSahlq_proof1

__ :: any
__ = Prelude.error "Logical or arity value used"

first_occ_P_n :: (Datatypes.Coq_list SO_syntax.Coq_predicate) ->
                 SO_syntax.Coq_predicate -> Datatypes.Coq_nat ->
                 Datatypes.Coq_nat
first_occ_P_n lP p n =
  case lP of {
   Datatypes.Coq_nil -> Datatypes.O;
   Datatypes.Coq_cons q lP' ->
    case SO_syntax.predicate_dec p q of {
     Specif.Coq_left -> n;
     Specif.Coq_right -> first_occ_P_n lP' p (Datatypes.S n)}}

first_occ_P :: (Datatypes.Coq_list SO_syntax.Coq_predicate) ->
               SO_syntax.Coq_predicate -> Datatypes.Coq_nat
first_occ_P lP p =
  first_occ_P_n lP p (Datatypes.S Datatypes.O)

cap_pred_lx :: (Datatypes.Coq_list SO_syntax.Coq_predicate) ->
               (Datatypes.Coq_list SO_syntax.Coq_predicate) ->
               (Datatypes.Coq_list SO_syntax.FOvariable) ->
               Datatypes.Coq_list SO_syntax.FOvariable
cap_pred_lx l1 l2 lx =
  case l1 of {
   Datatypes.Coq_nil -> Datatypes.Coq_nil;
   Datatypes.Coq_cons p l1' ->
    case lx of {
     Datatypes.Coq_nil -> Datatypes.Coq_nil;
     Datatypes.Coq_cons x lx' ->
      case SO_syntax.in_predicate_dec p l2 of {
       Specif.Coq_left -> Datatypes.Coq_cons x (cap_pred_lx l1' l2 lx');
       Specif.Coq_right -> cap_pred_lx l1' l2 lx'}}}

new_FOv_pp_pre2 :: SO_syntax.SecOrder -> Datatypes.Coq_nat
new_FOv_pp_pre2 alpha =
  Datatypes.S (Max_min.max_FOv alpha)

replace_FOv_A_rel_atm :: (Datatypes.Coq_list SO_syntax.FOvariable) ->
                         SO_syntax.SecOrder -> SO_syntax.SecOrder ->
                         SO_syntax.SecOrder -> Specif.Coq_sigT
                         SO_syntax.SecOrder
                         (Specif.Coq_sigT SO_syntax.SecOrder ())
replace_FOv_A_rel_atm lv rel atm beta =
  Datatypes.list_rec (\rel0 atm0 _ _ _ -> Specif.Coq_existT rel0
    (Specif.Coq_existT atm0 __)) (\a lv0 _ rel0 atm0 beta0 _ _ ->
    let {
     s = Same_struc.same_struc_conjSO_ex
           (Replace_FOv_A.replace_FOv_A_pre
             (FOvars_in.strip_exFO
               (Replace_FOv_max_conj.replace_FOv_max_conj
                 (FOvars_in.list_closed_exFO (SO_syntax.Coq_conjSO rel0 atm0)
                   lv0) beta0 a) (Datatypes.length lv0)) beta0
             (FOvars_in.strip_exFO_list
               (Replace_FOv_max_conj.replace_FOv_max_conj
                 (FOvars_in.list_closed_exFO (SO_syntax.Coq_conjSO rel0 atm0)
                   lv0) beta0 a) (Datatypes.length lv0))
             (Datatypes.length lv0)) rel0 atm0}
    in
    case s of {
     Specif.Coq_existT rel'' s0 ->
      case s0 of {
       Specif.Coq_existT atm'' _ -> Specif.Coq_existT rel''
        (Specif.Coq_existT atm'' __)}}) lv rel atm beta __ __

vsS_preprocessing_Step1_1_againTRY'_withex'' :: Modal_syntax.Modal ->
                                                Modal_syntax.Modal ->
                                                SO_syntax.SecOrder ->
                                                SO_syntax.SecOrder ->
                                                SO_syntax.FOvariable ->
                                                (Datatypes.Coq_list
                                                SO_syntax.FOvariable) ->
                                                Specif.Coq_sigT
                                                (Datatypes.Coq_list
                                                SO_syntax.FOvariable)
                                                (Specif.Coq_sigT
                                                SO_syntax.SecOrder
                                                (Datatypes.Coq_prod ()
                                                (Datatypes.Coq_prod ()
                                                (Datatypes.Coq_sum
                                                SO_syntax.SecOrder ()))))
vsS_preprocessing_Step1_1_againTRY'_withex'' _ phi2 rel atm x lv =
  let {s = replace_FOv_A_rel_atm lv rel atm (ST.coq_ST phi2 x)} in
  case s of {
   Specif.Coq_existT rel' s0 ->
    case s0 of {
     Specif.Coq_existT atm' _ -> Specif.Coq_existT
      (Replace_FOv_A.replace_FOv_A_list (SO_syntax.Coq_conjSO rel atm)
        (ST.coq_ST phi2 x) lv) (Specif.Coq_existT atm' (Datatypes.Coq_pair __
      (Datatypes.Coq_pair __ (Datatypes.Coq_inl rel'))))}}

vsS_preprocessing_Step1_3_againTRY'_withex' :: Modal_syntax.Modal ->
                                               Modal_syntax.Modal ->
                                               SO_syntax.SecOrder ->
                                               SO_syntax.FOvariable ->
                                               (Datatypes.Coq_list
                                               SO_syntax.FOvariable) ->
                                               Specif.Coq_sigT
                                               (Datatypes.Coq_list
                                               SO_syntax.FOvariable)
                                               (Specif.Coq_sigT
                                               SO_syntax.SecOrder
                                               (Datatypes.Coq_prod ()
                                               (Datatypes.Coq_prod ()
                                               (Datatypes.Coq_sum
                                               SO_syntax.SecOrder ()))))
vsS_preprocessing_Step1_3_againTRY'_withex' _ phi2 atm x lv =
  Specif.Coq_existT
    (Replace_FOv_A.replace_FOv_A_list atm (ST.coq_ST phi2 x) lv)
    (Specif.Coq_existT
    (Replace_FOv_A.replace_FOv_A atm (ST.coq_ST phi2 x) lv)
    (Datatypes.Coq_pair __ (Datatypes.Coq_pair __ (Datatypes.Coq_inr __))))

vsS_preprocessing_Step1_pre_againTRY'_withex' :: Modal_syntax.Modal ->
                                                 Modal_syntax.Modal ->
                                                 SO_syntax.FOvariable ->
                                                 Specif.Coq_sigT
                                                 (Datatypes.Coq_list
                                                 SO_syntax.FOvariable)
                                                 (Specif.Coq_sigT
                                                 SO_syntax.SecOrder
                                                 (Datatypes.Coq_prod 
                                                 ()
                                                 (Datatypes.Coq_prod 
                                                 ()
                                                 (Datatypes.Coq_sum
                                                 SO_syntax.SecOrder ()))))
vsS_preprocessing_Step1_pre_againTRY'_withex' phi1 phi2 x =
  let {
   h1 = VsSahlq_proof1.preprocess_vsSahlq_ante_againTRY (ST.coq_ST phi1 x)
          (ST.ex_P_ST phi1 x)}
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

hopeful4_REV'_withex'_FULL :: (Datatypes.Coq_list SO_syntax.Coq_predicate) ->
                              Datatypes.Coq_nat -> Modal_syntax.Modal ->
                              Modal_syntax.Modal -> Specif.Coq_sigT
                              (Datatypes.Coq_list SO_syntax.FOvariable)
                              (Specif.Coq_sigT SO_syntax.SecOrder
                              (Datatypes.Coq_prod ()
                              (Datatypes.Coq_sum SO_syntax.SecOrder ())))
hopeful4_REV'_withex'_FULL _ xn phi1 phi2 =
  let {s = vsS_preprocessing_Step1_pre_againTRY'_withex' phi1 phi2 xn} in
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

hopeful4_REV'_withex'_FULL_allFO :: (Datatypes.Coq_list
                                    SO_syntax.Coq_predicate) ->
                                    Datatypes.Coq_nat -> Modal_syntax.Modal
                                    -> Modal_syntax.Modal -> Specif.Coq_sigT
                                    (Datatypes.Coq_list SO_syntax.FOvariable)
                                    (Specif.Coq_sigT SO_syntax.SecOrder
                                    (Datatypes.Coq_prod ()
                                    (Datatypes.Coq_sum SO_syntax.SecOrder ())))
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
                                       SO_syntax.Coq_predicate) ->
                                       Datatypes.Coq_nat ->
                                       Modal_syntax.Modal ->
                                       Modal_syntax.Modal -> Specif.Coq_sigT
                                       (Datatypes.Coq_list
                                       SO_syntax.FOvariable)
                                       (Specif.Coq_sigT SO_syntax.SecOrder
                                       (Datatypes.Coq_prod ()
                                       (Datatypes.Coq_sum SO_syntax.SecOrder
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

vsSahlq_full_SO_pre :: Datatypes.Coq_nat -> Modal_syntax.Modal ->
                       Modal_syntax.Modal -> Specif.Coq_sigT
                       (Datatypes.Coq_list SO_syntax.FOvariable)
                       (Specif.Coq_sigT SO_syntax.SecOrder
                       (Datatypes.Coq_prod ()
                       (Datatypes.Coq_sum SO_syntax.SecOrder ())))
vsSahlq_full_SO_pre xn phi1 phi2 =
  hopeful4_REV'_withex'_FULL_allFO_in
    (Preds_in.preds_in (SO_syntax.Coq_allFO xn
      (ST.coq_ST (Modal_syntax.Coq_mimpl phi1 phi2) xn))) xn phi1 phi2

vsSahlq_full_SO :: Datatypes.Coq_nat -> Modal_syntax.Modal ->
                   Modal_syntax.Modal -> SO_syntax.SecOrder
vsSahlq_full_SO xn phi1 phi2 =
  let {s = vsSahlq_full_SO_pre xn phi1 phi2} in
  case s of {
   Specif.Coq_existT lx s0 ->
    case s0 of {
     Specif.Coq_existT atm p ->
      case p of {
       Datatypes.Coq_pair _ s1 ->
        case s1 of {
         Datatypes.Coq_inl s2 -> SO_syntax.Coq_allFO xn
          (Rep_Pred_FOv.replace_pred_l
            (FOvars_in.list_closed_allFO (SO_syntax.Coq_implSO
              (SO_syntax.Coq_conjSO s2 atm)
              (Newnew.newnew_pre
                (Instant_cons_empty.instant_cons_empty' (SO_syntax.Coq_conjSO
                  s2 atm) (ST.coq_ST phi2 xn))
                (FOvars_in.rem_FOv xn
                  (FOvars_in.coq_FOvars_in
                    (Instant_cons_empty.instant_cons_empty'
                      (SO_syntax.Coq_conjSO s2 atm) (ST.coq_ST phi2 xn))))
                (Rev_seq.rev_seq (Datatypes.S
                  (PeanoNat._Nat__max
                    (Max_min.max_FOv (SO_syntax.Coq_implSO
                      (SO_syntax.Coq_conjSO s2 atm) (ST.coq_ST phi2 xn))) xn))
                  (Datatypes.length
                    (FOvars_in.rem_FOv xn
                      (FOvars_in.coq_FOvars_in
                        (Instant_cons_empty.instant_cons_empty'
                          (SO_syntax.Coq_conjSO s2 atm) (ST.coq_ST phi2 xn))))))))
              lx)
            (Preds_in.preds_in
              (ST.coq_ST (Modal_syntax.Coq_mimpl phi1 phi2) xn))
            (Nlist_syn_eg.list_var
              (Datatypes.length
                (Preds_in.preds_in
                  (ST.coq_ST (Modal_syntax.Coq_mimpl phi1 phi2) xn)))
              (new_FOv_pp_pre2 atm))
            (VsS_syn_sem.vsS_syn_l
              (FOvars_in.coq_FOv_att_P_l (SO_syntax.Coq_conjSO s2 atm)
                (Preds_in.preds_in
                  (ST.coq_ST (Modal_syntax.Coq_mimpl phi1 phi2) xn)))
              (new_FOv_pp_pre2 atm)));
         Datatypes.Coq_inr _ -> SO_syntax.Coq_allFO xn
          (Rep_Pred_FOv.replace_pred_l
            (FOvars_in.list_closed_allFO (SO_syntax.Coq_implSO atm
              (Newnew.newnew_pre
                (Instant_cons_empty.instant_cons_empty' atm
                  (ST.coq_ST phi2 xn))
                (FOvars_in.rem_FOv xn
                  (FOvars_in.coq_FOvars_in
                    (Instant_cons_empty.instant_cons_empty' atm
                      (ST.coq_ST phi2 xn))))
                (Rev_seq.rev_seq (Datatypes.S
                  (PeanoNat._Nat__max
                    (Max_min.max_FOv (SO_syntax.Coq_implSO atm
                      (ST.coq_ST phi2 xn))) xn))
                  (Datatypes.length
                    (FOvars_in.rem_FOv xn
                      (FOvars_in.coq_FOvars_in
                        (Instant_cons_empty.instant_cons_empty' atm
                          (ST.coq_ST phi2 xn)))))))) lx)
            (Preds_in.preds_in
              (ST.coq_ST (Modal_syntax.Coq_mimpl phi1 phi2) xn))
            (Nlist_syn_eg.list_var
              (Datatypes.length
                (Preds_in.preds_in
                  (ST.coq_ST (Modal_syntax.Coq_mimpl phi1 phi2) xn)))
              (new_FOv_pp_pre2 atm))
            (VsS_syn_sem.vsS_syn_l
              (FOvars_in.coq_FOv_att_P_l atm
                (Preds_in.preds_in
                  (ST.coq_ST (Modal_syntax.Coq_mimpl phi1 phi2) xn)))
              (new_FOv_pp_pre2 atm)))}}}}

