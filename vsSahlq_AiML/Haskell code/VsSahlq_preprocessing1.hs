module VsSahlq_preprocessing1 where

import qualified Prelude
import qualified Datatypes
import qualified Logic
import qualified Modal
import qualified Nat
import qualified PeanoNat
import qualified SecOrder
import qualified Specif

__ :: any
__ = Prelude.error "Logical or arity value used"

vsSahlq_ante :: Modal.Modal -> Datatypes.Coq_bool
vsSahlq_ante phi =
  case phi of {
   Modal.Coq_atom _ -> Datatypes.Coq_true;
   Modal.Coq_mconj psi1 psi2 ->
    case vsSahlq_ante psi1 of {
     Datatypes.Coq_true -> vsSahlq_ante psi2;
     Datatypes.Coq_false -> Datatypes.Coq_false};
   Modal.Coq_diam psi -> vsSahlq_ante psi;
   _ -> Datatypes.Coq_false}

free_FO :: SecOrder.SecOrder -> SecOrder.FOvariable -> Datatypes.Coq_bool
free_FO alpha x =
  case alpha of {
   SecOrder.Coq_predSO _ y -> PeanoNat._Nat__eqb x y;
   SecOrder.Coq_relatSO y1 y2 ->
    case PeanoNat._Nat__eqb x y1 of {
     Datatypes.Coq_true -> Datatypes.Coq_true;
     Datatypes.Coq_false -> PeanoNat._Nat__eqb x y2};
   SecOrder.Coq_eqFO y1 y2 ->
    case PeanoNat._Nat__eqb x y1 of {
     Datatypes.Coq_true -> Datatypes.Coq_true;
     Datatypes.Coq_false -> PeanoNat._Nat__eqb x y2};
   SecOrder.Coq_allFO y beta ->
    case PeanoNat._Nat__eqb x y of {
     Datatypes.Coq_true -> Datatypes.Coq_false;
     Datatypes.Coq_false -> free_FO beta x};
   SecOrder.Coq_exFO y beta ->
    case PeanoNat._Nat__eqb x y of {
     Datatypes.Coq_true -> Datatypes.Coq_false;
     Datatypes.Coq_false -> free_FO beta x};
   SecOrder.Coq_negSO beta -> free_FO beta x;
   SecOrder.Coq_conjSO beta1 beta2 ->
    case free_FO beta1 x of {
     Datatypes.Coq_true -> Datatypes.Coq_true;
     Datatypes.Coq_false -> free_FO beta2 x};
   SecOrder.Coq_disjSO beta1 beta2 ->
    case free_FO beta1 x of {
     Datatypes.Coq_true -> Datatypes.Coq_true;
     Datatypes.Coq_false -> free_FO beta2 x};
   SecOrder.Coq_implSO beta1 beta2 ->
    case free_FO beta1 x of {
     Datatypes.Coq_true -> Datatypes.Coq_true;
     Datatypes.Coq_false -> free_FO beta2 x};
   SecOrder.Coq_allSO _ beta -> free_FO beta x;
   SecOrder.Coq_exSO _ beta -> free_FO beta x}

no_free_FO_l :: SecOrder.SecOrder -> (Datatypes.Coq_list SecOrder.FOvariable)
                -> Datatypes.Coq_bool
no_free_FO_l alpha l =
  case l of {
   Datatypes.Coq_nil -> Datatypes.Coq_true;
   Datatypes.Coq_cons x l' ->
    case free_FO alpha x of {
     Datatypes.Coq_true -> Datatypes.Coq_false;
     Datatypes.Coq_false -> no_free_FO_l alpha l'}}

rename_FOv_n :: SecOrder.SecOrder -> Datatypes.Coq_nat -> Datatypes.Coq_nat
                -> SecOrder.SecOrder
rename_FOv_n alpha n1 n2 =
  case alpha of {
   SecOrder.Coq_predSO p f ->
    case PeanoNat._Nat__eqb n1 f of {
     Datatypes.Coq_true -> SecOrder.Coq_predSO p n2;
     Datatypes.Coq_false -> alpha};
   SecOrder.Coq_relatSO f f0 ->
    case PeanoNat._Nat__eqb n1 f of {
     Datatypes.Coq_true ->
      case PeanoNat._Nat__eqb n1 f0 of {
       Datatypes.Coq_true -> SecOrder.Coq_relatSO n2 n2;
       Datatypes.Coq_false -> SecOrder.Coq_relatSO n2 f0};
     Datatypes.Coq_false ->
      case PeanoNat._Nat__eqb n1 f0 of {
       Datatypes.Coq_true -> SecOrder.Coq_relatSO f n2;
       Datatypes.Coq_false -> alpha}};
   SecOrder.Coq_eqFO f f0 ->
    case PeanoNat._Nat__eqb n1 f of {
     Datatypes.Coq_true ->
      case PeanoNat._Nat__eqb n1 f0 of {
       Datatypes.Coq_true -> SecOrder.Coq_eqFO n2 n2;
       Datatypes.Coq_false -> SecOrder.Coq_eqFO n2 f0};
     Datatypes.Coq_false ->
      case PeanoNat._Nat__eqb n1 f0 of {
       Datatypes.Coq_true -> SecOrder.Coq_eqFO f n2;
       Datatypes.Coq_false -> alpha}};
   SecOrder.Coq_allFO f beta ->
    case PeanoNat._Nat__eqb f n1 of {
     Datatypes.Coq_true -> SecOrder.Coq_allFO n2 (rename_FOv_n beta n1 n2);
     Datatypes.Coq_false -> SecOrder.Coq_allFO f (rename_FOv_n beta n1 n2)};
   SecOrder.Coq_exFO f beta ->
    case PeanoNat._Nat__eqb f n1 of {
     Datatypes.Coq_true -> SecOrder.Coq_exFO n2 (rename_FOv_n beta n1 n2);
     Datatypes.Coq_false -> SecOrder.Coq_exFO f (rename_FOv_n beta n1 n2)};
   SecOrder.Coq_negSO beta -> SecOrder.Coq_negSO (rename_FOv_n beta n1 n2);
   SecOrder.Coq_conjSO beta1 beta2 -> SecOrder.Coq_conjSO
    (rename_FOv_n beta1 n1 n2) (rename_FOv_n beta2 n1 n2);
   SecOrder.Coq_disjSO beta1 beta2 -> SecOrder.Coq_disjSO
    (rename_FOv_n beta1 n1 n2) (rename_FOv_n beta2 n1 n2);
   SecOrder.Coq_implSO beta1 beta2 -> SecOrder.Coq_implSO
    (rename_FOv_n beta1 n1 n2) (rename_FOv_n beta2 n1 n2);
   SecOrder.Coq_allSO p beta -> SecOrder.Coq_allSO p
    (rename_FOv_n beta n1 n2);
   SecOrder.Coq_exSO p beta -> SecOrder.Coq_exSO p (rename_FOv_n beta n1 n2)}

rename_FOv :: SecOrder.SecOrder -> SecOrder.FOvariable -> SecOrder.FOvariable
              -> SecOrder.SecOrder
rename_FOv alpha x y =
  rename_FOv_n alpha x y

max_FOv :: SecOrder.SecOrder -> Datatypes.Coq_nat
max_FOv alpha =
  case alpha of {
   SecOrder.Coq_predSO _ f -> f;
   SecOrder.Coq_relatSO f f0 -> Nat.max f f0;
   SecOrder.Coq_eqFO f f0 -> Nat.max f f0;
   SecOrder.Coq_allFO f beta -> Nat.max f (max_FOv beta);
   SecOrder.Coq_exFO f beta -> Nat.max f (max_FOv beta);
   SecOrder.Coq_negSO beta -> max_FOv beta;
   SecOrder.Coq_conjSO beta1 beta2 -> Nat.max (max_FOv beta1) (max_FOv beta2);
   SecOrder.Coq_disjSO beta1 beta2 -> Nat.max (max_FOv beta1) (max_FOv beta2);
   SecOrder.Coq_implSO beta1 beta2 -> Nat.max (max_FOv beta1) (max_FOv beta2);
   SecOrder.Coq_allSO _ beta -> max_FOv beta;
   SecOrder.Coq_exSO _ beta -> max_FOv beta}

list_closed_exFO :: SecOrder.SecOrder -> (Datatypes.Coq_list
                    SecOrder.FOvariable) -> SecOrder.SecOrder
list_closed_exFO alpha l =
  case l of {
   Datatypes.Coq_nil -> alpha;
   Datatypes.Coq_cons x ls -> SecOrder.Coq_exFO x (list_closed_exFO alpha ls)}

list_closed_allFO :: SecOrder.SecOrder -> (Datatypes.Coq_list
                     SecOrder.FOvariable) -> SecOrder.SecOrder
list_closed_allFO alpha l =
  case l of {
   Datatypes.Coq_nil -> alpha;
   Datatypes.Coq_cons x ls -> SecOrder.Coq_allFO x
    (list_closed_allFO alpha ls)}

coq_REL :: SecOrder.SecOrder -> Datatypes.Coq_bool
coq_REL alpha =
  case alpha of {
   SecOrder.Coq_relatSO _ _ -> Datatypes.Coq_true;
   SecOrder.Coq_conjSO alpha1 alpha2 ->
    case coq_REL alpha1 of {
     Datatypes.Coq_true -> coq_REL alpha2;
     Datatypes.Coq_false -> Datatypes.Coq_false};
   _ -> Datatypes.Coq_false}

coq_AT :: SecOrder.SecOrder -> Datatypes.Coq_bool
coq_AT alpha =
  case alpha of {
   SecOrder.Coq_predSO _ _ -> Datatypes.Coq_true;
   SecOrder.Coq_conjSO alpha1 alpha2 ->
    case coq_AT alpha1 of {
     Datatypes.Coq_true -> coq_AT alpha2;
     Datatypes.Coq_false -> Datatypes.Coq_false};
   _ -> Datatypes.Coq_false}

no_exFO :: SecOrder.SecOrder -> Datatypes.Coq_bool
no_exFO alpha =
  case alpha of {
   SecOrder.Coq_allFO _ beta -> no_exFO beta;
   SecOrder.Coq_exFO _ _ -> Datatypes.Coq_false;
   SecOrder.Coq_negSO beta -> no_exFO beta;
   SecOrder.Coq_conjSO beta1 beta2 ->
    case no_exFO beta1 of {
     Datatypes.Coq_true -> no_exFO beta2;
     Datatypes.Coq_false -> Datatypes.Coq_false};
   SecOrder.Coq_disjSO beta1 beta2 ->
    case no_exFO beta1 of {
     Datatypes.Coq_true -> no_exFO beta2;
     Datatypes.Coq_false -> Datatypes.Coq_false};
   SecOrder.Coq_implSO beta1 beta2 ->
    case no_exFO beta1 of {
     Datatypes.Coq_true -> no_exFO beta2;
     Datatypes.Coq_false -> Datatypes.Coq_false};
   SecOrder.Coq_allSO _ beta -> no_exFO beta;
   SecOrder.Coq_exSO _ beta -> no_exFO beta;
   _ -> Datatypes.Coq_true}

exFO_front :: SecOrder.SecOrder -> Datatypes.Coq_bool
exFO_front alpha =
  case alpha of {
   SecOrder.Coq_predSO _ _ -> Datatypes.Coq_true;
   SecOrder.Coq_relatSO _ _ -> Datatypes.Coq_true;
   SecOrder.Coq_eqFO _ _ -> Datatypes.Coq_true;
   SecOrder.Coq_exFO _ alpha0 -> exFO_front alpha0;
   _ -> no_exFO alpha}

same_struc :: SecOrder.SecOrder -> SecOrder.SecOrder -> Datatypes.Coq_bool
same_struc alpha beta =
  case alpha of {
   SecOrder.Coq_predSO p _ ->
    case beta of {
     SecOrder.Coq_predSO q _ -> PeanoNat._Nat__eqb p q;
     _ -> Datatypes.Coq_false};
   SecOrder.Coq_relatSO _ _ ->
    case beta of {
     SecOrder.Coq_relatSO _ _ -> Datatypes.Coq_true;
     _ -> Datatypes.Coq_false};
   SecOrder.Coq_eqFO _ _ ->
    case beta of {
     SecOrder.Coq_eqFO _ _ -> Datatypes.Coq_true;
     _ -> Datatypes.Coq_false};
   SecOrder.Coq_allFO _ alpha' ->
    case beta of {
     SecOrder.Coq_allFO _ beta' -> same_struc alpha' beta';
     _ -> Datatypes.Coq_false};
   SecOrder.Coq_exFO _ alpha' ->
    case beta of {
     SecOrder.Coq_exFO _ beta' -> same_struc alpha' beta';
     _ -> Datatypes.Coq_false};
   SecOrder.Coq_negSO alpha' ->
    case beta of {
     SecOrder.Coq_negSO beta' -> same_struc alpha' beta';
     _ -> Datatypes.Coq_false};
   SecOrder.Coq_conjSO alpha1 alpha2 ->
    case beta of {
     SecOrder.Coq_conjSO beta1 beta2 ->
      case same_struc alpha1 beta1 of {
       Datatypes.Coq_true -> same_struc alpha2 beta2;
       Datatypes.Coq_false -> Datatypes.Coq_false};
     _ -> Datatypes.Coq_false};
   SecOrder.Coq_disjSO alpha1 alpha2 ->
    case beta of {
     SecOrder.Coq_disjSO beta1 beta2 ->
      case same_struc alpha1 beta1 of {
       Datatypes.Coq_true -> same_struc alpha2 beta2;
       Datatypes.Coq_false -> Datatypes.Coq_false};
     _ -> Datatypes.Coq_false};
   SecOrder.Coq_implSO alpha1 alpha2 ->
    case beta of {
     SecOrder.Coq_implSO beta1 beta2 ->
      case same_struc alpha1 beta1 of {
       Datatypes.Coq_true -> same_struc alpha2 beta2;
       Datatypes.Coq_false -> Datatypes.Coq_false};
     _ -> Datatypes.Coq_false};
   SecOrder.Coq_allSO p alpha' ->
    case beta of {
     SecOrder.Coq_allSO q beta' ->
      case PeanoNat._Nat__eqb p q of {
       Datatypes.Coq_true -> same_struc alpha' beta';
       Datatypes.Coq_false -> Datatypes.Coq_false};
     _ -> Datatypes.Coq_false};
   SecOrder.Coq_exSO p alpha' ->
    case beta of {
     SecOrder.Coq_exSO q beta' ->
      case PeanoNat._Nat__eqb p q of {
       Datatypes.Coq_true -> same_struc alpha' beta';
       Datatypes.Coq_false -> Datatypes.Coq_false};
     _ -> Datatypes.Coq_false}}

rename_FOv_max_conj :: SecOrder.SecOrder -> SecOrder.SecOrder ->
                       SecOrder.FOvariable -> SecOrder.SecOrder
rename_FOv_max_conj alpha gamma x =
  rename_FOv alpha x (Datatypes.S
    (max_FOv (SecOrder.Coq_conjSO gamma (SecOrder.Coq_exFO x alpha))))

rename_FOv_max_conj_var :: SecOrder.SecOrder -> SecOrder.SecOrder ->
                           SecOrder.FOvariable -> SecOrder.FOvariable
rename_FOv_max_conj_var alpha gamma x =
  Datatypes.S
    (max_FOv (SecOrder.Coq_conjSO gamma (SecOrder.Coq_exFO x alpha)))

strip_exFO :: SecOrder.SecOrder -> Datatypes.Coq_nat -> SecOrder.SecOrder
strip_exFO alpha n =
  case n of {
   Datatypes.O -> alpha;
   Datatypes.S m ->
    case alpha of {
     SecOrder.Coq_exFO _ beta -> strip_exFO beta m;
     _ -> alpha}}

strip_exFO_list :: SecOrder.SecOrder -> Datatypes.Coq_nat ->
                   Datatypes.Coq_list SecOrder.FOvariable
strip_exFO_list alpha n =
  case n of {
   Datatypes.O -> Datatypes.Coq_nil;
   Datatypes.S m ->
    case alpha of {
     SecOrder.Coq_exFO x beta -> Datatypes.Coq_cons x
      (strip_exFO_list beta m);
     _ -> Datatypes.Coq_nil}}

rename_FOv_A_pre :: SecOrder.SecOrder -> SecOrder.SecOrder ->
                    (Datatypes.Coq_list SecOrder.FOvariable) ->
                    Datatypes.Coq_nat -> SecOrder.SecOrder
rename_FOv_A_pre alpha gamma lv n =
  case n of {
   Datatypes.O -> alpha;
   Datatypes.S m ->
    case lv of {
     Datatypes.Coq_nil -> alpha;
     Datatypes.Coq_cons x lv' ->
      rename_FOv_A_pre
        (strip_exFO
          (rename_FOv_max_conj (list_closed_exFO alpha lv') gamma x)
          (Datatypes.length lv')) gamma
        (strip_exFO_list
          (rename_FOv_max_conj (list_closed_exFO alpha lv') gamma x)
          (Datatypes.length lv')) m}}

rename_FOv_A :: SecOrder.SecOrder -> SecOrder.SecOrder -> (Datatypes.Coq_list
                SecOrder.FOvariable) -> SecOrder.SecOrder
rename_FOv_A alpha gamma lv =
  rename_FOv_A_pre alpha gamma lv (Datatypes.length lv)

rename_FOv_A_list_pre :: SecOrder.SecOrder -> SecOrder.SecOrder ->
                         (Datatypes.Coq_list SecOrder.FOvariable) ->
                         Datatypes.Coq_nat -> Datatypes.Coq_list
                         SecOrder.FOvariable
rename_FOv_A_list_pre alpha gamma lv n =
  case n of {
   Datatypes.O -> Datatypes.Coq_nil;
   Datatypes.S m ->
    case lv of {
     Datatypes.Coq_nil -> Datatypes.Coq_nil;
     Datatypes.Coq_cons x lv' -> Datatypes.Coq_cons
      (rename_FOv_max_conj_var (list_closed_exFO alpha lv') gamma x)
      (rename_FOv_A_list_pre
        (strip_exFO
          (rename_FOv_max_conj (list_closed_exFO alpha lv') gamma x)
          (Datatypes.length lv')) gamma
        (strip_exFO_list
          (rename_FOv_max_conj (list_closed_exFO alpha lv') gamma x)
          (Datatypes.length lv')) m)}}

rename_FOv_A_list :: SecOrder.SecOrder -> SecOrder.SecOrder ->
                     (Datatypes.Coq_list SecOrder.FOvariable) ->
                     Datatypes.Coq_list SecOrder.FOvariable
rename_FOv_A_list alpha gamma lv =
  rename_FOv_A_list_pre alpha gamma lv (Datatypes.length lv)

conjSO_exFO :: SecOrder.SecOrder -> Datatypes.Coq_bool
conjSO_exFO alpha =
  case alpha of {
   SecOrder.Coq_predSO _ _ -> Datatypes.Coq_true;
   SecOrder.Coq_relatSO _ _ -> Datatypes.Coq_true;
   SecOrder.Coq_eqFO _ _ -> Datatypes.Coq_true;
   SecOrder.Coq_exFO _ beta -> conjSO_exFO beta;
   SecOrder.Coq_conjSO beta1 beta2 ->
    case conjSO_exFO beta1 of {
     Datatypes.Coq_true -> conjSO_exFO beta2;
     Datatypes.Coq_false -> Datatypes.Coq_false};
   _ -> Datatypes.Coq_false}

conjSO_exFO_relatSO :: SecOrder.SecOrder -> Datatypes.Coq_bool
conjSO_exFO_relatSO alpha =
  case alpha of {
   SecOrder.Coq_predSO _ _ -> Datatypes.Coq_true;
   SecOrder.Coq_relatSO _ _ -> Datatypes.Coq_true;
   SecOrder.Coq_exFO _ beta -> conjSO_exFO_relatSO beta;
   SecOrder.Coq_conjSO beta1 beta2 ->
    case conjSO_exFO_relatSO beta1 of {
     Datatypes.Coq_true -> conjSO_exFO_relatSO beta2;
     Datatypes.Coq_false -> Datatypes.Coq_false};
   _ -> Datatypes.Coq_false}

strip_exFO_gen :: SecOrder.SecOrder -> SecOrder.SecOrder
strip_exFO_gen alpha =
  case alpha of {
   SecOrder.Coq_exFO _ beta -> strip_exFO_gen beta;
   _ -> alpha}

size_SO :: SecOrder.SecOrder -> Datatypes.Coq_nat
size_SO alpha =
  case alpha of {
   SecOrder.Coq_exFO _ beta -> Datatypes.S (size_SO beta);
   SecOrder.Coq_negSO beta -> Datatypes.S (size_SO beta);
   SecOrder.Coq_conjSO beta1 beta2 -> Nat.add (size_SO beta1) (size_SO beta2);
   SecOrder.Coq_disjSO beta1 beta2 -> Nat.add (size_SO beta1) (size_SO beta2);
   SecOrder.Coq_implSO beta1 beta2 -> Nat.add (size_SO beta1) (size_SO beta2);
   SecOrder.Coq_allSO _ beta -> Datatypes.S (size_SO beta);
   SecOrder.Coq_exSO _ beta -> Datatypes.S (size_SO beta);
   _ -> Datatypes.S Datatypes.O}

strip_exFO_list_gen :: SecOrder.SecOrder -> Datatypes.Coq_list
                       SecOrder.FOvariable
strip_exFO_list_gen alpha =
  case alpha of {
   SecOrder.Coq_exFO x beta -> Datatypes.Coq_cons x
    (strip_exFO_list_gen beta);
   _ -> Datatypes.Coq_nil}

funC :: SecOrder.SecOrder -> SecOrder.SecOrder
funC alpha =
  case alpha of {
   SecOrder.Coq_exFO x beta -> SecOrder.Coq_exFO x (funC beta);
   SecOrder.Coq_conjSO beta1 beta2 ->
    list_closed_exFO
      (list_closed_exFO (SecOrder.Coq_conjSO
        (rename_FOv_A (strip_exFO_gen beta1)
          (rename_FOv_A (strip_exFO_gen beta2)
            (list_closed_exFO (strip_exFO_gen beta1)
              (strip_exFO_list_gen beta1)) (strip_exFO_list_gen beta2))
          (strip_exFO_list_gen beta1))
        (rename_FOv_A (strip_exFO_gen beta2)
          (list_closed_exFO (strip_exFO_gen beta1)
            (strip_exFO_list_gen beta1)) (strip_exFO_list_gen beta2)))
        (rename_FOv_A_list (strip_exFO_gen beta1)
          (rename_FOv_A (strip_exFO_gen beta2)
            (list_closed_exFO (strip_exFO_gen beta1)
              (strip_exFO_list_gen beta1)) (strip_exFO_list_gen beta2))
          (strip_exFO_list_gen beta1)))
      (rename_FOv_A_list (strip_exFO_gen beta2)
        (list_closed_exFO (strip_exFO_gen beta1) (strip_exFO_list_gen beta1))
        (strip_exFO_list_gen beta2));
   _ -> alpha}

same_struc_conjSO_ex :: SecOrder.SecOrder -> SecOrder.SecOrder ->
                        SecOrder.SecOrder -> Specif.Coq_sigT
                        SecOrder.SecOrder
                        (Specif.Coq_sigT SecOrder.SecOrder ())
same_struc_conjSO_ex gamma alpha beta =
  SecOrder.coq_SecOrder_rec (\_ _ _ _ _ -> Logic.coq_False_rec)
    (\_ _ _ _ _ -> Logic.coq_False_rec) (\_ _ _ _ _ -> Logic.coq_False_rec)
    (\_ _ _ _ _ _ -> Logic.coq_False_rec) (\_ _ _ _ _ _ ->
    Logic.coq_False_rec) (\_ _ _ _ _ -> Logic.coq_False_rec)
    (\gamma1 _ gamma2 _ _ _ _ -> Specif.Coq_existT gamma1 (Specif.Coq_existT
    gamma2 __)) (\_ _ _ _ _ _ _ -> Logic.coq_False_rec) (\_ _ _ _ _ _ _ ->
    Logic.coq_False_rec) (\_ _ _ _ _ _ -> Logic.coq_False_rec)
    (\_ _ _ _ _ _ -> Logic.coq_False_rec) gamma alpha beta __

fun_return_conj_l :: SecOrder.SecOrder -> SecOrder.SecOrder
fun_return_conj_l alpha =
  case alpha of {
   SecOrder.Coq_conjSO beta1 _ -> beta1;
   _ -> alpha}

fun_return_conj_r :: SecOrder.SecOrder -> SecOrder.SecOrder
fun_return_conj_r alpha =
  case alpha of {
   SecOrder.Coq_conjSO _ beta2 -> beta2;
   _ -> alpha}

