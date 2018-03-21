module ST_setup where

import qualified Prelude
import qualified Datatypes
import qualified Modal
import qualified Nat
import qualified SecOrder

coq_ST :: Modal.Modal -> SecOrder.FOvariable -> SecOrder.SecOrder
coq_ST phi x =
  case phi of {
   Modal.Coq_atom p -> SecOrder.Coq_predSO p x;
   Modal.Coq_mneg psi -> SecOrder.Coq_negSO (coq_ST psi x);
   Modal.Coq_mconj psi1 psi2 -> SecOrder.Coq_conjSO (coq_ST psi1 x)
    (coq_ST psi2 x);
   Modal.Coq_mdisj psi1 psi2 -> SecOrder.Coq_disjSO (coq_ST psi1 x)
    (coq_ST psi2 x);
   Modal.Coq_mimpl psi1 psi2 -> SecOrder.Coq_implSO (coq_ST psi1 x)
    (coq_ST psi2 x);
   Modal.Coq_box psi -> SecOrder.Coq_allFO
    (Nat.add x (Datatypes.S Datatypes.O)) (SecOrder.Coq_implSO
    (SecOrder.Coq_relatSO x (Nat.add x (Datatypes.S Datatypes.O)))
    (coq_ST psi (Nat.add x (Datatypes.S Datatypes.O))));
   Modal.Coq_diam psi -> SecOrder.Coq_exFO
    (Nat.add x (Datatypes.S Datatypes.O)) (SecOrder.Coq_conjSO
    (SecOrder.Coq_relatSO x (Nat.add x (Datatypes.S Datatypes.O)))
    (coq_ST psi (Nat.add x (Datatypes.S Datatypes.O))))}

coq_ST_pv :: Modal.Coq_propvar -> SecOrder.Coq_predicate
coq_ST_pv p =
  p

coq_ST_pred :: SecOrder.Coq_predicate -> Modal.Coq_propvar
coq_ST_pred p =
  p

