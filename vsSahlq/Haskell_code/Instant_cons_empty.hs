module Instant_cons_empty where

import qualified Prelude
import qualified Datatypes
import qualified Rep_Pred_FOv
import qualified SO_syntax
import qualified List_rel_compl
import qualified Nlist_syn
import qualified Nlist_syn_eg
import qualified Preds_in

instant_cons_empty :: SO_syntax.SecOrder -> SO_syntax.SecOrder
instant_cons_empty alpha =
  Rep_Pred_FOv.replace_pred_l alpha
    (List_rel_compl.list_rel_compl
      (Preds_in.preds_in (SO_syntax.calc_cons_SO alpha))
      (Preds_in.preds_in (SO_syntax.calc_ante_SO alpha)))
    (Nlist_syn.nlist_list
      (Datatypes.length
        (List_rel_compl.list_rel_compl
          (Preds_in.preds_in (SO_syntax.calc_cons_SO alpha))
          (Preds_in.preds_in (SO_syntax.calc_ante_SO alpha))))
      (Nlist_syn_eg.nlist_var
        (Datatypes.length
          (List_rel_compl.list_rel_compl
            (Preds_in.preds_in (SO_syntax.calc_cons_SO alpha))
            (Preds_in.preds_in (SO_syntax.calc_ante_SO alpha)))) (Datatypes.S
        Datatypes.O)))
    (Nlist_syn.nlist_list
      (Datatypes.length
        (List_rel_compl.list_rel_compl
          (Preds_in.preds_in (SO_syntax.calc_cons_SO alpha))
          (Preds_in.preds_in (SO_syntax.calc_ante_SO alpha))))
      (Nlist_syn_eg.nlist_empty
        (Datatypes.length
          (List_rel_compl.list_rel_compl
            (Preds_in.preds_in (SO_syntax.calc_cons_SO alpha))
            (Preds_in.preds_in (SO_syntax.calc_ante_SO alpha))))))

instant_cons_empty' :: SO_syntax.SecOrder -> SO_syntax.SecOrder ->
                       SO_syntax.SecOrder
instant_cons_empty' alpha beta =
  Rep_Pred_FOv.replace_pred_l beta
    (List_rel_compl.list_rel_compl (Preds_in.preds_in beta)
      (Preds_in.preds_in alpha))
    (Nlist_syn.nlist_list
      (Datatypes.length
        (List_rel_compl.list_rel_compl (Preds_in.preds_in beta)
          (Preds_in.preds_in alpha)))
      (Nlist_syn_eg.nlist_var
        (Datatypes.length
          (List_rel_compl.list_rel_compl (Preds_in.preds_in beta)
            (Preds_in.preds_in alpha))) (Datatypes.S Datatypes.O)))
    (Nlist_syn.nlist_list
      (Datatypes.length
        (List_rel_compl.list_rel_compl (Preds_in.preds_in beta)
          (Preds_in.preds_in alpha)))
      (Nlist_syn_eg.nlist_empty
        (Datatypes.length
          (List_rel_compl.list_rel_compl (Preds_in.preds_in beta)
            (Preds_in.preds_in alpha)))))

