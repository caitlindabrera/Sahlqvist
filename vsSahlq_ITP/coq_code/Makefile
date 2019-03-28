%.vo : %.v
	coqc $*.v

ltac_gen.vo : ltac_gen.v

existsT.vo : ltac_gen.vo existsT.v

incl_lemmas.vo : existsT.vo incl_lemmas.v

nlist_syn.vo : incl_lemmas.vo nlist_syn.v

base_mods.vo : nlist_syn.vo base_mods.v


Modal_syntax.vo : base_mods.vo Modal_syntax.v

Modal_semantics.vo : Modal_syntax.vo Modal_semantics.v

pv_in.vo : Modal_semantics.vo pv_in.v

occ_in_modal.vo : pv_in.vo occ_in_modal.v 

at_pv.vo : occ_in_modal.vo at_pv.v

pv_in_modal.vo : at_pv.vo pv_in_modal.v


SO_syntax.vo : pv_in_modal.vo SO_syntax.v

ltac_SO.vo : SO_syntax.vo ltac_SO.v

nlist_syn_eg.vo : ltac_SO.vo nlist_syn_eg.v

FOvars_in.vo : nlist_syn_eg.vo FOvars_in.v

preds_in.vo : FOvars_in.vo preds_in.v

Pred_in_SO.vo : preds_in.vo Pred_in_SO.v

lPred_in_SO.vo : Pred_in_SO.vo lPred_in_SO.v

FO_frame_condition.vo : lPred_in_SO.vo FO_frame_condition.v 

FO_frame_condition_l.vo : FO_frame_condition.vo FO_frame_condition_l.v

occ_in_SO.vo : FO_frame_condition_l.vo occ_in_SO.v

ltac_occ_in_SO.vo : occ_in_SO.vo ltac_occ_in_SO.v

at_pred.vo : ltac_occ_in_SO.vo at_pred.v

max_min.vo : at_pred.vo max_min.v

rev_seq.vo : max_min.vo rev_seq.v

low_mods.vo : rev_seq.vo low_mods.v


Rep_Pred_FOv.vo : low_mods.vo Rep_Pred_FOv.v  

free_FO.vo : Rep_Pred_FOv.vo free_FO.v

At.vo : free_FO.vo At.v

Rel.vo : At.vo Rel.v

ltac_rel.vo : Rel.vo ltac_rel.v

conjSO_exFO_relatSO.vo : ltac_rel.vo conjSO_exFO_relatSO.v

same_struc.vo : conjSO_exFO_relatSO.vo same_struc.v

rename_FOv_list.vo : same_struc.vo rename_FOv_list.v

replace_FOv_max_conj.vo : rename_FOv_list.vo replace_FOv_max_conj.v

replace_FOv_A.vo : replace_FOv_max_conj.vo replace_FOv_A.v

list_rel_compl.vo : replace_FOv_A.vo list_rel_compl.v

instant_cons_empty.vo : list_rel_compl.vo instant_cons_empty.v

att_allFO_exFO_var.vo : instant_cons_empty.vo att_allFO_exFO_var.v

Indicies.vo : att_allFO_exFO_var.vo Indicies.v

Num_Occ.vo : Indicies.vo Num_Occ.v

Num_occ_l.vo : Num_Occ.vo Num_occ_l.v

Identify.vo : Num_occ_l.vo Identify.v

Num_Occ_l2.vo : Identify.vo Num_Occ_l2.v

Pred_in_SO_rep_pred.vo : Num_Occ_l2.vo Pred_in_SO_rep_pred.v

med_mods.vo : Pred_in_SO_rep_pred.vo med_mods.v


SO_semantics.vo : med_mods.vo SO_semantics.v

nlist_sem.vo : SO_semantics.vo nlist_sem.v

nlist_sem_eg.vo : nlist_sem.vo nlist_sem_eg.v


ST.vo : nlist_sem_eg.vo ST.v

Correctness_ST.vo : ST.vo Correctness_ST.v


is_pos.vo : Correctness_ST.vo is_pos.v

is_neg.vo : is_pos.vo is_neg.v

is_pos_neg_lemmas.vo : is_neg.vo is_pos_neg_lemmas.v 

p_is_pos.vo : is_pos_neg_lemmas.vo p_is_pos.v

p_is_neg.vo : p_is_pos.vo p_is_neg.v

p_is_pos_neg_lemmas.vo : p_is_neg.vo p_is_pos_neg_lemmas.v

pos.vo : p_is_pos_neg_lemmas.vo pos.v

is_pos_SO.vo : pos.vo is_pos_SO.v

is_neg_SO.vo : is_pos_SO.vo is_neg_SO.v

is_pos_neg_SO_lemmas.vo : is_neg_SO.vo is_pos_neg_SO_lemmas.v

Pred_is_pos_SO.vo : is_pos_neg_SO_lemmas.vo Pred_is_pos_SO.v

Pred_is_neg_SO.vo : Pred_is_pos_SO.vo Pred_is_neg_SO.v

Pred_is_pos_neg_SO.vo : Pred_is_neg_SO.vo Pred_is_pos_neg_SO.v

pos_SO.vo : Pred_is_pos_neg_SO.vo pos_SO.v

Is_Pos_Rep_Pred.vo : pos_SO.vo Is_Pos_Rep_Pred.v

Monotonicity_SO.vo : Is_Pos_Rep_Pred.vo Monotonicity_SO.v

Rep_Pred_FOv_sem.vo : Monotonicity_SO.vo Rep_Pred_FOv_sem.v

high_mods.vo : Rep_Pred_FOv_sem.vo high_mods.v


vsSahlq_setup.vo : high_mods.vo vsSahlq_setup.v

SO_facts_syn.vo : vsSahlq_setup.vo SO_facts_syn.v

SO_sem_mods.vo : SO_facts_syn.vo SO_sem_mods.v

SO_facts1.vo : SO_sem_mods.vo SO_facts1.v

Monotonicity_lP_SO.vo : SO_facts1.vo Monotonicity_lP_SO.v

Sahlqvist_Pos.vo : Monotonicity_lP_SO.vo Sahlqvist_Pos.v 

SO_facts2.vo : Sahlqvist_Pos.vo SO_facts2.v

vsS_syn_sem.vo : SO_facts2.vo vsS_syn_sem.v

consistent.vo : vsS_syn_sem.vo consistent.v

SO_facts3.vo : consistent.vo SO_facts3.v

newnew.vo : SO_facts3.vo newnew.v

vsSahlq_proof1.vo : newnew.vo vsSahlq_proof1.v 

vsSahlq_proof2.vo : vsSahlq_proof1.vo vsSahlq_proof2.v 

vsSahlq_proof3.vo : vsSahlq_proof2.vo vsSahlq_proof3.v 

vsSahlq_proof4.vo : vsSahlq_proof3.vo vsSahlq_proof4.v

vsSahlq_extraction.vo : vsSahlq_proof4.vo vsSahlq_extraction.v  

clean : 
	find *.hs *.vo ! -name 'Main.hs' -type f -exec rm -f {} +

#	rm -rf  *.vo *.glob [^Main]*.hs Modal.hs *.aux


clean_win : 
	del /f *.vo *.glob  Bool.hs Datatypes.hs List_machinery_impl.hs Logic.hs Modal.hs Nat.hs NList_egs.hs P_occurs_in_alpha.hs PeanoNat.hs Rep_Pred_FOv.hs SecOrder.hs Specif.hs ST_setup.hs VsSahlq_instant3.hs VsSahlq_instant9.hs VsSahlq_instant13.hs VsSahlq_instant19.hs VsSahlq_instant20.hs VsSahlq_preprocessing1.hs VsSahlq_preprocessing2.hs VsSahlq_preprocessing3.hs

run_hs : 
	ghci Main.hs 

run : vsSahlq_extraction.vo Main.hs
	ghci Main.hs
