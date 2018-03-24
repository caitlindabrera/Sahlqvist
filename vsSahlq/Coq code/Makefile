%.vo : %.v
	coqc $*.v

Modal.vo : Modal.v

my_bool.vo : Modal.vo my_bool.v

My_Prop.vo : my_bool.vo My_Prop.v

SecOrder.vo : My_Prop.vo SecOrder.v 

p_occurs_in.vo : SecOrder.vo p_occurs_in.v 

P_occurs_in_alpha.vo : p_occurs_in.vo P_occurs_in_alpha.v 

my_arith.vo : P_occurs_in_alpha.vo my_arith.v 

my_arith__my_leb_nat.vo : my_arith.vo my_arith__my_leb_nat.v 

at_pv.vo : my_arith__my_leb_nat.vo at_pv.v 

at_pred.vo : at_pv.vo at_pred.v

ST_setup.vo : at_pred.vo ST_setup.v

occ_in_phi.vo : ST_setup.vo occ_in_phi.v 

is_pos_neg.vo : occ_in_phi.vo is_pos_neg.v 

is_pos_neg_lemmas.vo : is_pos_neg.vo is_pos_neg_lemmas.v 

p_is_pos.vo : is_pos_neg_lemmas.vo p_is_pos.v 

Correctness_ST_world_model.vo : p_is_pos.vo Correctness_ST_world_model.v

List_machinery_impl.vo : Correctness_ST_world_model.vo List_machinery_impl.v 

Correctness_ST.vo : List_machinery_impl.vo Correctness_ST.v 

My_List_Map.vo : Correctness_ST.vo My_List_Map.v 

Unary_Predless.vo : My_List_Map.vo Unary_Predless.v 

Occ_In_Alpha.vo : Unary_Predless.vo Occ_In_Alpha.v 

nList_egs.vo : Occ_In_Alpha.vo nList_egs.v 

Uniform_Defns.vo : nList_egs.vo Uniform_Defns.v 

pos_SO2.vo : Uniform_Defns.vo pos_SO2.v 

Rep_Pred_FOv.vo : pos_SO2.vo Rep_Pred_FOv.v  

Indicies.vo : Rep_Pred_FOv.vo Indicies.v 

Unary_Predless_l.vo : Indicies.vo Unary_Predless_l.v 

Num_Occ.vo : Unary_Predless_l.vo Num_Occ.v

Identify.vo : Num_Occ.vo Identify.v

P_occ_rep_pred.vo : Identify.vo P_occ_rep_pred.v

Is_Pos_Rep_Pred.vo : P_occ_rep_pred.vo Is_Pos_Rep_Pred.v

neg_SO2.vo : Is_Pos_Rep_Pred.vo neg_SO2.v

Monotonicity_SO.vo : neg_SO2.vo Monotonicity_SO.v 

Pre_Sahlqvist_Uniform_Pos.vo : Monotonicity_SO.vo Pre_Sahlqvist_Uniform_Pos.v

Num_Occ_l2.vo : Pre_Sahlqvist_Uniform_Pos.vo Num_Occ_l2.v 

Sahlqvist_Uniform_Pos.vo : Num_Occ_l2.vo Sahlqvist_Uniform_Pos.v 

vsSahlq_preprocessing1.vo : Sahlqvist_Uniform_Pos.vo vsSahlq_preprocessing1.v 

vsSahlq_preprocessing2.vo : vsSahlq_preprocessing1.vo vsSahlq_preprocessing2.v 

vsSahlq_preprocessing3.vo : vsSahlq_preprocessing2.vo vsSahlq_preprocessing3.v 

vsSahlq_instant3.vo : vsSahlq_preprocessing3.vo vsSahlq_instant3.v 

vsSahlq_instant_pre_to_be_sorted.vo : vsSahlq_instant3.vo vsSahlq_instant_pre_to_be_sorted.v 

vsSahlq_instant9.vo : vsSahlq_instant_pre_to_be_sorted.vo vsSahlq_instant9.v 

vsSahlq_instant10.vo : vsSahlq_instant9.vo vsSahlq_instant10.v 

vsSahlq_instant13.vo : vsSahlq_instant10.vo vsSahlq_instant13.v 

vsSahlq_instant15.vo : vsSahlq_instant13.vo vsSahlq_instant15.v 

vsSahlq_instant16.vo : vsSahlq_instant15.vo vsSahlq_instant16.v 

vsSahlq_instant17.vo : vsSahlq_instant16.vo vsSahlq_instant17.v 

vsSahlq_instant19.vo : vsSahlq_instant17.vo vsSahlq_instant19.v 

vsSahlq_instant20.vo : vsSahlq_instant19.vo vsSahlq_instant20.v

vsSahlq_extraction.vo : vsSahlq_instant20.vo vsSahlq_extraction.v  

clean : 
	rm -rf  *.vo *.glob [^Main]*.hs Modal.hs

clean_win : 
	del /f *.vo *.glob  Bool.hs Datatypes.hs List_machinery_impl.hs Logic.hs Modal.hs Nat.hs NList_egs.hs P_occurs_in_alpha.hs PeanoNat.hs Rep_Pred_FOv.hs SecOrder.hs Specif.hs ST_setup.hs VsSahlq_instant3.hs VsSahlq_instant9.hs VsSahlq_instant13.hs VsSahlq_instant19.hs VsSahlq_instant20.hs VsSahlq_preprocessing1.hs VsSahlq_preprocessing2.hs VsSahlq_preprocessing3.hs

run : 
	ghci Main.hs 
