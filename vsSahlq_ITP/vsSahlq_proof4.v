Require Export high_mods SO_sem_mods.
Require Import vsSahlq_instant19 vsSahlq_instant13 newnew.
Require Import Correctness_ST vsS_syn_sem uniform SO_facts2.

Open Scope type_scope.

Theorem vsSahlq_full_Modal_sep : forall phi1 phi2,
  vsSahlq_ante phi1 ->
  uniform_pos phi2  ->
  existsT (alpha : SecOrder),
FO_frame_condition alpha = true /\
forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir alpha <->
  mturnst_frame W Ir (mimpl phi1 phi2).
Proof.
  intros phi1 phi2 H1 H2.
  destruct (vsSahlq_full_SO 0 phi1 phi2 H1 H2) as [alpha [Hun SOt]].
  exists alpha. apply conj. assumption.
  intros. split; intros HH.
    apply (correctness_ST _ _ (Var 0) Iv Ip).
    apply SOt. assumption.

    apply SOt.
    apply (correctness_ST _ _ (Var 0) Iv Ip).
    assumption.
Defined.
 
Theorem vsSahlq_full_Modal : forall phi,
  vsSahlq phi -> existsT (alpha : SecOrder),
   FO_frame_condition alpha = true /\ corresponds phi alpha.
Proof.
  intros phi H. unfold corresponds.
  destruct (vsSahlq_dest_ex_comp phi H)
    as [phi1 [phi2 [[H1 H2] H3]]].
  subst. apply vsSahlq_full_Modal_sep; auto.
Defined.

(*
Theorem vsSahlq_full_Modal_withoutnot : forall phi,
  vsSahlq phi ->
  existsT (alpha : SecOrder),
FO_frame_condition alpha = true /\
forall W Iv Ip Ir,
  SOturnst W Iv Ip Ir alpha <->
  mturnst_frame W Ir phi.
Proof.
  intros phi H.
  destruct (vsSahlq_dest_ex_comp phi H)
    as [phi1 [phi2 [[H1 H2] H3]]].
  subst. apply vsSahlq_full_Modal_sep; auto.
Defined.
*)
Theorem vsSahlq_full_Modal_ex : forall phi,
  vsSahlq phi ->
  exists (alpha : SecOrder),
FO_frame_condition alpha = true /\ corresponds phi alpha.
Proof.
  intros phi H.
  destruct (vsSahlq_full_Modal phi H) as [alpha H2].
  exists alpha. auto.
Qed.
  
(* Print Assumptions vsSahlq_full_Modal. *)
(* Print All Dependencies vsSahlq_full_Modal. *)