module VsS_syn_sem where

import qualified Prelude
import qualified Datatypes
import qualified SO_syntax

__ :: any
__ = Prelude.error "Logical or arity value used"

disj_l :: (Datatypes.Coq_list SO_syntax.FOvariable) -> SO_syntax.FOvariable
          -> SO_syntax.SecOrder
disj_l lv x =
  case lv of {
   Datatypes.Coq_nil -> SO_syntax.Coq_eqFO (Datatypes.S Datatypes.O)
    (Datatypes.S Datatypes.O);
   Datatypes.Coq_cons y lv' ->
    case lv' of {
     Datatypes.Coq_nil -> SO_syntax.Coq_eqFO x y;
     Datatypes.Coq_cons _ _ -> SO_syntax.Coq_disjSO (SO_syntax.Coq_eqFO x y)
      (disj_l lv' x)}}

vsS_syn_l :: (Datatypes.Coq_list (Datatypes.Coq_list SO_syntax.FOvariable))
             -> SO_syntax.FOvariable -> Datatypes.Coq_list SO_syntax.SecOrder
vsS_syn_l llv x =
  case llv of {
   Datatypes.Coq_nil -> Datatypes.Coq_nil;
   Datatypes.Coq_cons lv llv' -> Datatypes.Coq_cons (disj_l lv x)
    (vsS_syn_l llv' x)}

vsS_pa_l :: (SO_syntax.FOvariable -> a1) -> (Datatypes.Coq_list
            (Datatypes.Coq_list SO_syntax.FOvariable)) -> (Datatypes.Coq_list
            SO_syntax.FOvariable) -> Datatypes.Coq_list ()
vsS_pa_l iv llv lx =
  case llv of {
   Datatypes.Coq_nil -> Datatypes.Coq_nil;
   Datatypes.Coq_cons _ llv' ->
    case lx of {
     Datatypes.Coq_nil -> Datatypes.Coq_nil;
     Datatypes.Coq_cons _ lx' -> Datatypes.Coq_cons __ (vsS_pa_l iv llv' lx')}}

passing_conj :: (Datatypes.Coq_list SO_syntax.SecOrder) -> SO_syntax.SecOrder
passing_conj lalpha =
  case lalpha of {
   Datatypes.Coq_nil -> SO_syntax.Coq_eqFO (Datatypes.S Datatypes.O)
    (Datatypes.S Datatypes.O);
   Datatypes.Coq_cons alpha lalpha' ->
    case lalpha' of {
     Datatypes.Coq_nil -> alpha;
     Datatypes.Coq_cons _ _ -> SO_syntax.Coq_conjSO alpha
      (passing_conj lalpha')}}

passing_conj_atm :: SO_syntax.Coq_predicate -> (Datatypes.Coq_list
                    SO_syntax.FOvariable) -> SO_syntax.SecOrder
passing_conj_atm p lx =
  case lx of {
   Datatypes.Coq_nil -> SO_syntax.Coq_eqFO (Datatypes.S Datatypes.O)
    (Datatypes.S Datatypes.O);
   Datatypes.Coq_cons x lx' ->
    case lx' of {
     Datatypes.Coq_nil -> SO_syntax.Coq_predSO p x;
     Datatypes.Coq_cons _ _ -> SO_syntax.Coq_conjSO (SO_syntax.Coq_predSO p
      x) (passing_conj_atm p lx')}}

passing_predSO_l :: SO_syntax.Coq_predicate -> (Datatypes.Coq_list
                    SO_syntax.FOvariable) -> Datatypes.Coq_list
                    SO_syntax.SecOrder
passing_predSO_l p lx =
  case lx of {
   Datatypes.Coq_nil -> Datatypes.Coq_nil;
   Datatypes.Coq_cons x lx' -> Datatypes.Coq_cons (SO_syntax.Coq_predSO p x)
    (passing_predSO_l p lx')}

passing_predSO_ll :: (Datatypes.Coq_list SO_syntax.Coq_predicate) ->
                     (Datatypes.Coq_list
                     (Datatypes.Coq_list SO_syntax.FOvariable)) ->
                     Datatypes.Coq_list SO_syntax.SecOrder
passing_predSO_ll lP llx =
  case lP of {
   Datatypes.Coq_nil -> Datatypes.Coq_nil;
   Datatypes.Coq_cons p lP' ->
    case llx of {
     Datatypes.Coq_nil -> Datatypes.Coq_nil;
     Datatypes.Coq_cons lx llx' -> Datatypes.Coq_cons
      (passing_conj (passing_predSO_l p lx)) (passing_predSO_ll lP' llx')}}

atm_passing_predSO_ll_lP :: SO_syntax.SecOrder -> Datatypes.Coq_list
                            SO_syntax.Coq_predicate
atm_passing_predSO_ll_lP atm =
  case atm of {
   SO_syntax.Coq_predSO p _ -> Datatypes.Coq_cons p Datatypes.Coq_nil;
   SO_syntax.Coq_conjSO beta1 beta2 ->
    Datatypes.app (atm_passing_predSO_ll_lP beta1)
      (atm_passing_predSO_ll_lP beta2);
   _ -> Datatypes.Coq_nil}

atm_passing_predSO_ll_llx :: SO_syntax.SecOrder -> Datatypes.Coq_list
                             (Datatypes.Coq_list SO_syntax.FOvariable)
atm_passing_predSO_ll_llx atm =
  case atm of {
   SO_syntax.Coq_predSO _ x -> Datatypes.Coq_cons (Datatypes.Coq_cons x
    Datatypes.Coq_nil) Datatypes.Coq_nil;
   SO_syntax.Coq_conjSO beta1 beta2 ->
    Datatypes.app (atm_passing_predSO_ll_llx beta1)
      (atm_passing_predSO_ll_llx beta2);
   _ -> Datatypes.Coq_nil}

