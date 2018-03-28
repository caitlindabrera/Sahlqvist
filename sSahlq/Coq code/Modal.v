Require Export Coq.Logic.Classical_Prop.

(* Definition of modal formulas. *)

Inductive propvar : Type :=
  pv : nat -> propvar.

Inductive Modal : Type :=
    atom : propvar -> Modal  
  | mneg : Modal -> Modal
  | mconj : Modal -> Modal -> Modal
  | mdisj : Modal -> Modal -> Modal
  | mimpl : Modal -> Modal -> Modal
  | box : Modal -> Modal
  | diam : Modal -> Modal.

(* Modal turnstile at world on model. *)
Fixpoint mturnst (W:Set) (R: W -> W -> Prop) (V: propvar -> W -> Prop) (w:W) (phi: Modal) : Prop :=
  match phi with
    atom p => (V p w)
  | mneg psi => ~(mturnst W R V w psi)
  | mconj psi1 psi2 => (mturnst W R V w psi1) /\ (mturnst W R V w psi2)
  | mdisj psi1 psi2 => (mturnst W R V w psi1) \/ (mturnst W R V w psi2)
  | mimpl psi1 psi2 => (mturnst W R V w psi1) -> (mturnst W R V w psi2)
  | box psi => forall u:W, (R w u) -> (mturnst W R V u psi)
  | diam psi => (exists u:W, (R w u) /\ (mturnst W R V u psi))
  end.

(* Modal turnstile on model. *)
Definition mturnst_model (W:Set) (R: W -> W -> Prop) (V: propvar -> W -> Prop) (phi: Modal) : Prop := 
  forall w:W, mturnst W R V w phi.

(* Modal turnstile on frame. *)
Definition mturnst_frame (W:Set) (R: W -> W -> Prop) (phi: Modal) : Prop := 
  forall V: propvar -> W -> Prop, mturnst_model W R V phi.

(* Modal validity w.r.t. all frames. *)
Definition mvalid (phi:Modal) : Prop :=
  forall (W:Set) (R: W -> W -> Prop), mturnst_frame W R phi.

Definition mturnst_frame_loc (W:Set) (R: W -> W -> Prop) (w : W) (phi: Modal) : Prop := 
  forall V: propvar -> W -> Prop, mturnst W R V w phi.

(* --------------------------------------------------------------------------------------- *)

Lemma mturnst_box : forall (W:Set) (R: W -> W -> Prop) (V: propvar -> W -> Prop) (w:W) (phi:Modal),
                       mturnst W R V w (box phi) = (forall d:W, (R w d) -> mturnst W R V d phi).
Proof.
  simpl; reflexivity.
Qed.

Lemma mturnst_diam : forall (W:Set) (R: W -> W -> Prop) (V: propvar -> W -> Prop) (w:W) (phi:Modal),
                       mturnst W R V w (diam phi) = (exists d:W, ((R w d) /\ mturnst W R V d phi)).
Proof.
  simpl; reflexivity.
Qed.


(* --------------------------------------------------------------------------------------- *)

(* Returns a list of propvars in phi. *)
Fixpoint pv_in (phi : Modal) : list propvar :=
  match phi with
    atom p => cons p nil
  | mneg psi => pv_in psi
  | mconj psi1 psi2 => app (pv_in psi1) (pv_in psi2)
  | mdisj psi1 psi2 => app (pv_in psi1) (pv_in psi2)
  | mimpl psi1 psi2 => app (pv_in psi1) (pv_in psi2)
  | box psi => pv_in psi
  | diam psi => pv_in psi
  end.

(* --------------------------------------------------------------------------------------- *)

(* Proof of classicality *)

Lemma modal_LEM : forall phi W R V w,
  mturnst W R V w (mdisj phi (mneg phi)).
Proof.
  intros phi W R V w. apply classic.
Qed.

Lemma modal_LEM_model : forall phi W R V,
  mturnst_model W R V (mdisj phi (mneg phi)).
Proof.
  intros phi W R V w. apply modal_LEM.
Qed.

Lemma modal_LEM_frame : forall phi W R,
  mturnst_frame W R (mdisj phi (mneg phi)).
Proof.
  intros phi W R V. apply modal_LEM_model.
Qed.