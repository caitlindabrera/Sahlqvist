module VsSahlq_setup where

import qualified Prelude
import qualified Logic
import qualified Modal_syntax
import qualified Specif

__ :: any
__ = Prelude.error "Logical or arity value used"

vsSahlq_ante_dec :: Modal_syntax.Modal -> Specif.Coq_sumbool
vsSahlq_ante_dec phi =
  Modal_syntax.coq_Modal_rec (\_ -> Specif.Coq_left) (\_ _ ->
    Specif.Coq_right) (\_ iHphi1 _ iHphi2 ->
    case iHphi1 of {
     Specif.Coq_left -> iHphi2;
     Specif.Coq_right -> Specif.Coq_right}) (\_ _ _ _ -> Specif.Coq_right)
    (\_ _ _ _ -> Specif.Coq_right) (\_ _ -> Specif.Coq_right) (\_ iHphi ->
    iHphi) phi

vsSahlq_dest_ex_comp :: Modal_syntax.Modal -> Specif.Coq_sigT
                        Modal_syntax.Modal
                        (Specif.Coq_sigT Modal_syntax.Modal ())
vsSahlq_dest_ex_comp phi =
  case phi of {
   Modal_syntax.Coq_mimpl phi1 phi2 -> Specif.Coq_existT phi1
    (Specif.Coq_existT phi2 __);
   _ -> Logic.coq_False_rec}

