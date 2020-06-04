module VsSahlq_proof4 where

import qualified Prelude
import qualified Datatypes
import qualified Logic
import qualified Modal_syntax
import qualified SO_syntax
import qualified Specif
import qualified VsSahlq_proof3
import qualified VsSahlq_setup

__ :: any
__ = Prelude.error "Logical or arity value used"

vsSahlq_full_Modal_sep :: Modal_syntax.Modal -> Modal_syntax.Modal ->
                          SO_syntax.SecOrder
vsSahlq_full_Modal_sep phi1 phi2 =
  VsSahlq_proof3.vsSahlq_full_SO Datatypes.O phi1 phi2

vsSahlq_full_Modal :: Modal_syntax.Modal -> SO_syntax.SecOrder
vsSahlq_full_Modal phi =
  let {s = VsSahlq_setup.vsSahlq_dest_ex_comp phi} in
  case s of {
   Specif.Coq_existT phi1 s0 ->
    case s0 of {
     Specif.Coq_existT phi2 _ ->
      Logic.eq_rec_r (Modal_syntax.Coq_mimpl phi1 phi2) (\_ ->
        vsSahlq_full_Modal_sep phi1 phi2) phi __}}

