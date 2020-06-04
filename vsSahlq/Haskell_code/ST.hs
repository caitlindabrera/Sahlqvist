module ST where

import qualified Prelude
import qualified Datatypes
import qualified Modal_syntax
import qualified Nat
import qualified SO_syntax

next_FOv :: SO_syntax.FOvariable -> SO_syntax.FOvariable
next_FOv x =
  Nat.add x (Datatypes.S Datatypes.O)

coq_ST :: Modal_syntax.Modal -> SO_syntax.FOvariable -> SO_syntax.SecOrder
coq_ST _UU03d5_ x =
  case _UU03d5_ of {
   Modal_syntax.Coq_atom p -> SO_syntax.Coq_predSO p x;
   Modal_syntax.Coq_mneg _UU03c8_ -> SO_syntax.Coq_negSO (coq_ST _UU03c8_ x);
   Modal_syntax.Coq_mconj _UU03c8_1 _UU03c8_2 -> SO_syntax.Coq_conjSO
    (coq_ST _UU03c8_1 x) (coq_ST _UU03c8_2 x);
   Modal_syntax.Coq_mdisj _UU03c8_1 _UU03c8_2 -> SO_syntax.Coq_disjSO
    (coq_ST _UU03c8_1 x) (coq_ST _UU03c8_2 x);
   Modal_syntax.Coq_mimpl _UU03c8_1 _UU03c8_2 -> SO_syntax.Coq_implSO
    (coq_ST _UU03c8_1 x) (coq_ST _UU03c8_2 x);
   Modal_syntax.Coq_box _UU03c8_ -> SO_syntax.Coq_allFO (next_FOv x)
    (SO_syntax.Coq_implSO (SO_syntax.Coq_relatSO x (next_FOv x))
    (coq_ST _UU03c8_ (next_FOv x)));
   Modal_syntax.Coq_dia _UU03c8_ -> SO_syntax.Coq_exFO (next_FOv x)
    (SO_syntax.Coq_conjSO (SO_syntax.Coq_relatSO x (next_FOv x))
    (coq_ST _UU03c8_ (next_FOv x)))}

coq_ST_pv :: Modal_syntax.Coq_propvar -> SO_syntax.Coq_predicate
coq_ST_pv p =
  p

coq_ST_pred :: SO_syntax.Coq_predicate -> Modal_syntax.Coq_propvar
coq_ST_pred p =
  p

ex_P_ST :: Modal_syntax.Modal -> SO_syntax.FOvariable ->
           SO_syntax.Coq_predicate
ex_P_ST phi =
  Modal_syntax.coq_Modal_rec (\p _ -> coq_ST_pv p) (\_ iHphi -> iHphi)
    (\_ iHphi1 _ _ -> iHphi1) (\_ iHphi1 _ _ -> iHphi1) (\_ iHphi1 _ _ ->
    iHphi1) (\_ iHphi x -> iHphi (Nat.add x (Datatypes.S Datatypes.O)))
    (\_ iHphi x -> iHphi (Nat.add x (Datatypes.S Datatypes.O))) phi

