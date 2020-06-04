Ltac if_then_else_dest_blind :=
repeat match goal with
| [ H : context[if ?x then _ else _] |- _ ] => destruct x
| [ |- context[if ?x then _ else _] ] => destruct x
       end.

(*
| [ H : context[andb ?x ?y = true] |- _ ] => apply (andb_prop x y) in H;
                                      let H2 := fresh "H" in
                                      let H3 := fresh "H" in
                                      destruct H as [H2 H3]
| [ H : context[andb ?x ?y = false] |- _ ] => apply (Bool.andb_false_iff x y) in H;
                                      let H2 := fresh "H" in
                                      let H3 := fresh "H" in
                                      destruct H as [H2 H3]
*)

Ltac if_then_else_reg :=
  match goal with
  | [ |- context[if ?b then ?x else ?y] ] => destruct b;
                                             solve [firstorder]
  end.

Ltac if_then_else_reg2 :=
  match goal with
  | [ |- context[if ?b then ?x else ?y] ] => destruct b;
  match goal with
  | [ |- context[if ?b2 then ?x2 else ?y2] ] => destruct b2;
                                             solve [firstorder]
  end end.

Ltac destruct_andb_t :=
  match goal with
  | [H2 : (if ?b then ?x else false) = true |- _] =>
    case_eq b; intros ?H1; rewrite H1 in H2
  end.

Ltac destruct_andb_t2 :=
  match goal with
  | [H2 : (if ?b then ?x else false) = true |- _] =>
    case_eq b; intros ?H1; rewrite H1 in H2; [| discriminate]
  end.

Ltac destruct_andb_t_name H1 H2 :=
  match goal with
  | [H : (if ?b then ?x else false) = true |- _] =>
    case_eq b; intros H2; rewrite H2 in H1; [| discriminate]
  end.

Ltac destruct_andb_t_simpl H1 H2 := simpl in H1; destruct_andb_t_name H1 H2.

Ltac case_if_then_else_rep :=
repeat match goal with
  | [ |- context[if ?a then ?b else ?c] ] => case_eq a; intros
end.

Ltac if_then_else_solve :=
  match goal with
    [ |- (if ?a then ?b else ?b) = ?b] => destruct a; auto end.

Ltac if_then_else_hyp_tzf :=
  repeat match goal with
    [ _ : (if ?a then true else ?b) = false |- _ ] =>
    case_eq a; let H := fresh "H" in intros H; rewrite H in *; try discriminate
         end.

Ltac if_then_else_hyp_fzt :=
  repeat match goal with
    [ _ : (if ?a then false else ?b) = true |- _ ] =>
    case_eq a; let H := fresh "H" in intros H; rewrite H in *; try discriminate
         end.

Ltac if_then_else_hyp_zft :=
  repeat   match goal with
    [ _ : (if ?a then ?b else false) = true |- _ ] =>
    case_eq a; let H := fresh "H" in intros H; rewrite H in *; try discriminate
         end.

Ltac if_then_else_hyp_ztf :=
  repeat   match goal with
    [ _ : (if ?a then ?b else true) = false |- _ ] =>
    case_eq a; let H := fresh "H" in intros H; rewrite H in *; try discriminate
         end.

Ltac if_then_else_hyp := if_then_else_hyp_tzf; if_then_else_hyp_tzf; 
                         if_then_else_hyp_zft; if_then_else_hyp_ztf.

Ltac if_then_else_hyp_dep_tzf :=
  repeat match goal with
    [ _ : (if ?a then true else ?b) = false |- _ ] =>
    let H := fresh "H" in destruct a as [H | H]; try discriminate
         end.

Ltac if_then_else_hyp_dep_fzt :=
  repeat match goal with
    [ _ : (if ?a then false else ?b) = true |- _ ] =>
    let H := fresh "H" in destruct a as [H | H]; try discriminate
         end.

Ltac if_then_else_hyp_dep_ztf :=
  repeat   match goal with
    [ _ : (if ?a then ?b else true) = false |- _ ] =>
    let H := fresh "H" in destruct a as [H | H]; try discriminate
         end.

Ltac if_then_else_hyp_dep_zft :=
  repeat   match goal with
    [ _ : (if ?a then ?b else false) = true |- _ ] =>
    let H := fresh "H" in destruct a as [H | H]; try discriminate
         end.

Ltac if_then_else_hyp_dep := if_then_else_hyp_dep_tzf; if_then_else_hyp_dep_fzt;
if_then_else_hyp_dep_zft; if_then_else_hyp_dep_ztf.

Ltac if_then_else_hyp_gen := if_then_else_hyp; if_then_else_hyp_dep. 