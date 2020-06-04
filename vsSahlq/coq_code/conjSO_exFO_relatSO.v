Require Export SO_syntax.

Fixpoint conjSO_exFO_relatSO alpha : bool :=
  match alpha with
    predSO _ _ => true 
  | relatSO _ _ => true
  | eqFO _ _ => false
  | allFO _ _ => false
  | exFO x beta => conjSO_exFO_relatSO beta
  | negSO _ => false 
  | conjSO beta1 beta2 => 
    if conjSO_exFO_relatSO beta1 then conjSO_exFO_relatSO beta2 else false
  | disjSO _ _ => false
  | implSO _ _ => false
  | allSO _ _ => false
  | exSO _ _ => false
  end.
