Require Export Modal_syntax.
Require Export Classical.

Open Scope modal_scope.

(* Modal turnstile at world on model. *)
Reserved Notation "< W R V w > ⊩w ϕ"
         (at level 50, W at level 9, R at level 9, V at level 9, w at level 9,
          format "'<' W  R  V  w '>'  '⊩w'  ϕ").

Fixpoint mturnst (W:Set) (R: W -> W -> Prop) (V: propvar -> W -> Prop) (w:W) (ϕ: Modal)
  : Prop :=
  match ϕ with
    # p => (V p w)
  | m~ ψ => ~ <W R V w> ⊩w ψ
  | ψ1 m∧ ψ2 => <W R V w> ⊩w ψ1 /\ <W R V w> ⊩w ψ2
  | ψ1 m∨ ψ2 => <W R V w> ⊩w ψ1 \/ <W R V w> ⊩w ψ2
  | ψ1 m→ ψ2 => <W R V w> ⊩w ψ1 -> <W R V w> ⊩w ψ2
  | [.] ψ => forall u:W, (R w u) -> <W R V u> ⊩w ψ
  | <.> ψ => exists u:W, (R w u) /\ <W R V u> ⊩w ψ
  end
where  "< W R V w > ⊩w  ϕ" := (mturnst W R V w ϕ) : modal_scope.

(* Modal turnstile on model. *)
Definition mturnst_model (W:Set) (R: W -> W -> Prop) (V: propvar -> W -> Prop) (ϕ: Modal)
  : Prop := forall w:W, <W R V w> ⊩w ϕ.

Notation "< W R V > ⊩m ϕ" := (mturnst_model W R V ϕ)
                               (at level 50, W at level 9, R at level 9, V at level 9,
                                format  "'<' W  R  V '>'  '⊩m'  ϕ") : modal_scope.

(* Modal turnstile on frame. *)
Definition mturnst_frame (W:Set) (R: W -> W -> Prop) (ϕ: Modal) : Prop := 
  forall (V: propvar -> W -> Prop), <W R V> ⊩m ϕ.

Notation "< W R > ⊩ ϕ" := (mturnst_frame W R ϕ) (at level 50, W at level 9, R at level 9,
           format "'<' W  R '>'  '⊩'  ϕ"): modal_scope.

(* Modal validity w.r.t. all frames. *)
Definition mvalid (ϕ:Modal) : Prop :=
   forall (W:Set) (R: W -> W -> Prop), < W R > ⊩ ϕ.

(* Modal turnstile on frame locally. *)
Definition mturnst_frame_loc (W:Set) (R: W -> W -> Prop) (w : W) (ϕ: Modal) : Prop := 
  forall V: propvar -> W -> Prop, <W R V w> ⊩w ϕ.

Lemma mturnst_box : forall (W:Set) (R: W -> W -> Prop) (V: propvar -> W -> Prop)
                           (w:W) (ϕ:Modal),
<W R V w> ⊩w ([.]ϕ) = (forall d:W, (R w d) -> <W R V d> ⊩w ϕ).
Proof. auto. Qed.

Lemma mturnst_diam : forall (W:Set) (R: W -> W -> Prop) (V: propvar -> W -> Prop)
                            (w:W) (ϕ:Modal),
<W R V w> ⊩w (<.> ϕ) = (exists d:W, ((R w d) /\ <W R V d> ⊩w ϕ)).
Proof. auto. Qed.

(* ------------------------------------------------------------------------------------- *)

(* Proof of classicality *)

Lemma modal_LEM : forall ϕ W R V w,
    <W R V w> ⊩w (ϕ m∨ (m~ ϕ)).
Proof. intros. apply classic. Qed.

Lemma modal_LEM_model : forall ϕ W R V,
    <W R V> ⊩m (ϕ m∨ (m~ ϕ)).
Proof. intros. intros w. apply modal_LEM. Qed.

Lemma modal_LEM_frame : forall ϕ W R,
    <W R> ⊩ (ϕ m∨ (m~ ϕ)).
Proof.
  intros. intros V.
  apply modal_LEM_model.
Qed.