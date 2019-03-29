module List_rel_compl where

import qualified Prelude
import qualified Datatypes
import qualified SO_syntax
import qualified Specif

list_rel_compl :: (Datatypes.Coq_list SO_syntax.Coq_predicate) ->
                  (Datatypes.Coq_list SO_syntax.Coq_predicate) ->
                  Datatypes.Coq_list SO_syntax.Coq_predicate
list_rel_compl l2 l1 =
  case l2 of {
   Datatypes.Coq_nil -> Datatypes.Coq_nil;
   Datatypes.Coq_cons p l2' ->
    case SO_syntax.in_predicate_dec p l1 of {
     Specif.Coq_left -> list_rel_compl l2' l1;
     Specif.Coq_right -> Datatypes.Coq_cons p (list_rel_compl l2' l1)}}

