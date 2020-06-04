Require Export nlist_sem nlist_syn_eg.
Require Export SO_semantics.

Definition pa_f {W : Set} (w : W) : Prop := False.

Definition pa_t {W : Set} (w : W) : Prop := True.

Fixpoint nlist_pa_f (W : Set) (n : nat) : nlist n:=
  match n with
  | 0 => niln
  | S m => consn _ (@pa_f W) (nlist_pa_f W m)
  end.

Fixpoint nlist_pa_t (W : Set) (n : nat) : nlist n:=
  match n with
  | 0 => niln
  | S m => consn _ (@pa_t W) (nlist_pa_t W m)
  end.

Fixpoint alt_Ip_l {W : Set} (Ip : predicate -> W -> Prop) (l : list predicate)
                  (lpa : list (W -> Prop)) :=
  match l, lpa with
  | nil, _ => Ip
  | _, nil => Ip
  | cons P l', cons pa lpa' => alt_Ip_l (alt_Ip Ip pa P) l' lpa' 
  end.

Definition alt_Ip_pa_f {W : Set} (Ip : predicate -> W -> Prop) 
                       (l : list predicate) :=
  alt_Ip_l Ip l (nlist_list _ (nlist_pa_f W (length l))).

