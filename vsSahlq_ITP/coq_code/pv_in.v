Require Export Modal_syntax.
Require Export List.
Import ListNotations.
Open Scope modal_scope.

(* Returns a list of propvars in phi. *)
Fixpoint pv_in (phi : Modal) : list propvar :=
  match phi with
    #p => [p]
  | m~ ψ => pv_in ψ
  | ψ1 m∧ ψ2 => (pv_in ψ1) ++ (pv_in ψ2)
  | ψ1 m∨ ψ2 => (pv_in ψ1) ++ (pv_in ψ2)
  | ψ1 m→ ψ2 => (pv_in ψ1) ++ (pv_in ψ2)
  | [.] ψ => pv_in ψ
  | <.> ψ => pv_in ψ
  end.