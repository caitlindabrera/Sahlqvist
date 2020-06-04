module Same_struc where

import qualified Prelude
import qualified Datatypes
import qualified Logic
import qualified SO_syntax
import qualified Specif

__ :: any
__ = Prelude.error "Logical or arity value used"

same_struc :: SO_syntax.SecOrder -> SO_syntax.SecOrder -> Datatypes.Coq_bool
same_struc alpha beta =
  case alpha of {
   SO_syntax.Coq_predSO p _ ->
    case beta of {
     SO_syntax.Coq_predSO q _ ->
      case SO_syntax.predicate_dec p q of {
       Specif.Coq_left -> Datatypes.Coq_true;
       Specif.Coq_right -> Datatypes.Coq_false};
     _ -> Datatypes.Coq_false};
   SO_syntax.Coq_relatSO _ _ ->
    case beta of {
     SO_syntax.Coq_relatSO _ _ -> Datatypes.Coq_true;
     _ -> Datatypes.Coq_false};
   SO_syntax.Coq_eqFO _ _ ->
    case beta of {
     SO_syntax.Coq_eqFO _ _ -> Datatypes.Coq_true;
     _ -> Datatypes.Coq_false};
   SO_syntax.Coq_allFO _ alpha' ->
    case beta of {
     SO_syntax.Coq_allFO _ beta' -> same_struc alpha' beta';
     _ -> Datatypes.Coq_false};
   SO_syntax.Coq_exFO _ alpha' ->
    case beta of {
     SO_syntax.Coq_exFO _ beta' -> same_struc alpha' beta';
     _ -> Datatypes.Coq_false};
   SO_syntax.Coq_negSO alpha' ->
    case beta of {
     SO_syntax.Coq_negSO beta' -> same_struc alpha' beta';
     _ -> Datatypes.Coq_false};
   SO_syntax.Coq_conjSO alpha1 alpha2 ->
    case beta of {
     SO_syntax.Coq_conjSO beta1 beta2 ->
      case same_struc alpha1 beta1 of {
       Datatypes.Coq_true -> same_struc alpha2 beta2;
       Datatypes.Coq_false -> Datatypes.Coq_false};
     _ -> Datatypes.Coq_false};
   SO_syntax.Coq_disjSO alpha1 alpha2 ->
    case beta of {
     SO_syntax.Coq_disjSO beta1 beta2 ->
      case same_struc alpha1 beta1 of {
       Datatypes.Coq_true -> same_struc alpha2 beta2;
       Datatypes.Coq_false -> Datatypes.Coq_false};
     _ -> Datatypes.Coq_false};
   SO_syntax.Coq_implSO alpha1 alpha2 ->
    case beta of {
     SO_syntax.Coq_implSO beta1 beta2 ->
      case same_struc alpha1 beta1 of {
       Datatypes.Coq_true -> same_struc alpha2 beta2;
       Datatypes.Coq_false -> Datatypes.Coq_false};
     _ -> Datatypes.Coq_false};
   SO_syntax.Coq_allSO p alpha' ->
    case beta of {
     SO_syntax.Coq_allSO q beta' ->
      case SO_syntax.predicate_dec p q of {
       Specif.Coq_left -> same_struc alpha' beta';
       Specif.Coq_right -> Datatypes.Coq_false};
     _ -> Datatypes.Coq_false};
   SO_syntax.Coq_exSO p alpha' ->
    case beta of {
     SO_syntax.Coq_exSO q beta' ->
      case SO_syntax.predicate_dec p q of {
       Specif.Coq_left -> same_struc alpha' beta';
       Specif.Coq_right -> Datatypes.Coq_false};
     _ -> Datatypes.Coq_false}}

same_struc_conjSO_ex :: SO_syntax.SecOrder -> SO_syntax.SecOrder ->
                        SO_syntax.SecOrder -> Specif.Coq_sigT
                        SO_syntax.SecOrder
                        (Specif.Coq_sigT SO_syntax.SecOrder ())
same_struc_conjSO_ex gamma alpha beta =
  SO_syntax.coq_SecOrder_rec (\_ _ _ _ _ -> Logic.coq_False_rec)
    (\_ _ _ _ _ -> Logic.coq_False_rec) (\_ _ _ _ _ -> Logic.coq_False_rec)
    (\_ _ _ _ _ _ -> Logic.coq_False_rec) (\_ _ _ _ _ _ ->
    Logic.coq_False_rec) (\_ _ _ _ _ -> Logic.coq_False_rec)
    (\gamma1 _ gamma2 _ _ _ _ -> Specif.Coq_existT gamma1 (Specif.Coq_existT
    gamma2 __)) (\_ _ _ _ _ _ _ -> Logic.coq_False_rec) (\_ _ _ _ _ _ _ ->
    Logic.coq_False_rec) (\_ _ _ _ _ _ -> Logic.coq_False_rec)
    (\_ _ _ _ _ _ -> Logic.coq_False_rec) gamma alpha beta __

