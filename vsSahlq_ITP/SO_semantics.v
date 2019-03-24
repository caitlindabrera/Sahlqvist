Require Export SO_syntax Classical_Prop base_mods.
Require Import FunctionalExtensionality.

Open Scope SO_scope.

(* Semantics requires ability to reassign variable target for interpretation. *)
Definition alt_Iv {D:Set} (Iv: FOvariable -> D) (d:D) (x:FOvariable) (y:FOvariable) : D :=
if FOvariable_dec x y then d else (Iv y).

(* Semantics requires ability to reassign predicate target for interpretation. *)
Definition alt_Ip {D:Set} (Ip: predicate -> D -> Prop) (pred_asgmt: D -> Prop) 
                      (P: predicate) (Q: predicate) : D -> Prop :=
  if predicate_dec P Q then pred_asgmt else Ip Q.

(* Alters Ip with list. *)
Fixpoint alt_Ip_list {D:Set} (Ip: predicate -> D -> Prop) (l_pa : list (D -> Prop)) 
                      (l_pred : list (predicate)) : predicate -> D -> Prop:=
  match l_pa, l_pred with
    nil, _ => Ip
  | _, nil => Ip
  | cons pa l_pa', cons P l_pred' =>  alt_Ip (alt_Ip_list Ip l_pa' l_pred') pa P
  end.


(* Iv = interpretation of FOvariables; 
   Ip = interpretation of predicates (here D -> Prop can be thought of as an indicator function);
   Ir = interpretation of binary relation. *)

Reserved Notation "< D Iv Ip Ir > '⊨' α"
         (at level 50, D at level 9, Iv at level 9, Ip at level 9, Ir at level 9,
          format "< D  Iv  Ip  Ir >  '⊨'  α").

Fixpoint SOturnst (D:Set) (Iv: FOvariable -> D) (Ip: predicate -> D -> Prop)
         (Ir: D -> D -> Prop) (α:SecOrder) : Prop :=
  match α with
    predSO P x => (Ip P (Iv x))
  | relatSO x y => (Ir (Iv x) (Iv y))
  | eqFO x y => (Iv x) = (Iv y)
  | allFO x β => forall d:D, <D (alt_Iv Iv d x) Ip Ir> ⊨ β
  | exFO x β => (exists d:D, <D (alt_Iv Iv d x) Ip Ir> ⊨ β)
  | negSO β => ~ <D Iv Ip Ir> ⊨ β
  | conjSO β1 β2 => (<D Iv Ip Ir> ⊨ β1) /\ (<D Iv Ip Ir> ⊨ β2)
  | disjSO β1 β2 => (<D Iv Ip Ir> ⊨ β1) \/ (<D Iv Ip Ir> ⊨ β2)
  | implSO β1 β2 => (<D Iv Ip Ir> ⊨ β1) -> (<D Iv Ip Ir> ⊨ β2)
  | allSO P β => forall (pred_asgmt: D -> Prop), 
                               <D Iv (alt_Ip Ip pred_asgmt P) Ir> ⊨ β
  | exSO P β => (exists (pred_asgmt: D -> Prop), 
                              <D Iv (alt_Ip Ip pred_asgmt P) Ir> ⊨ β)
  end
  where "< D Iv Ip Ir > '⊨' α" := (SOturnst D Iv Ip Ir α) : SO_scope.

(*----------------------------------------------------------------------------*)

(* "By definition" lemmas of SOturnst *)

Lemma SOturnst_allFO : forall (D:Set) (Iv: FOvariable -> D) (Ip: predicate -> D -> Prop)
                              (Ir: D -> D -> Prop) (x:FOvariable) (β:SecOrder),
    < D Iv Ip Ir > ⊨ (allFO x β) = (forall (d:D), <D (alt_Iv Iv d x) Ip Ir> ⊨ β).
Proof. reflexivity. Qed.

Lemma SOturnst_exFO : forall (D:Set) (Iv: FOvariable -> D) (Ip: predicate -> D -> Prop)
                             (Ir: D -> D -> Prop) (x:FOvariable) (β:SecOrder), 
    <D Iv Ip Ir> ⊨ (exFO x β) = (exists (d:D), <D (alt_Iv Iv d x) Ip Ir> ⊨ β).
Proof. reflexivity. Qed.

Lemma SOturnst_implSO : forall (D:Set) (Iv: FOvariable -> D) (Ip: predicate -> D -> Prop)
                             (Ir: D -> D -> Prop) (β1 β2:SecOrder), 
    <D Iv Ip Ir> ⊨ (β1 SO→ β2) = (<D Iv Ip Ir> ⊨ β1 -> <D Iv Ip Ir> ⊨ β2 ).
Proof. reflexivity.  Qed.

Lemma SOturnst_conjSO : forall (D:Set) (Iv: FOvariable -> D) (Ip: predicate -> D -> Prop)
                             (Ir: D -> D -> Prop) (β1 β2:SecOrder), 
    <D Iv Ip Ir> ⊨ (β1 SO∧ β2) = (<D Iv Ip Ir> ⊨ β1 /\ <D Iv Ip Ir> ⊨ β2 ).
Proof. reflexivity.  Qed.

Lemma SOturnst_disjSO : forall (D:Set) (Iv: FOvariable -> D) (Ip: predicate -> D -> Prop)
                             (Ir: D -> D -> Prop) (β1 β2:SecOrder), 
    <D Iv Ip Ir> ⊨ (β1 SO∨ β2) = (<D Iv Ip Ir> ⊨ β1 \/ <D Iv Ip Ir> ⊨ β2 ).
Proof. reflexivity.  Qed.

Lemma SOturnst_allSO : forall (D:Set) (Iv:FOvariable -> D) (Ip: predicate -> D -> Prop) 
                        (Ir: D -> D -> Prop) (P: predicate) (β : SecOrder), 
    <D Iv Ip Ir> ⊨ (allSO P β)
  = (forall (pred_asgmt: D -> Prop), <D Iv (alt_Ip Ip pred_asgmt P) Ir> ⊨ β).
Proof. reflexivity. Qed.

Lemma SOturnst_exSO : forall (D:Set) (Iv:FOvariable -> D) (Ip: predicate -> D -> Prop) 
                        (Ir: D -> D -> Prop) (P: predicate) (β : SecOrder), 
    <D Iv Ip Ir> ⊨ (exSO P β)
  = (exists (pred_asgmt: D -> Prop), <D Iv (alt_Ip Ip pred_asgmt P) Ir> ⊨ β).
Proof. reflexivity. Qed.

Lemma SOturnst_negSO : forall (D:Set) (Iv:FOvariable -> D) (Ip: predicate -> D -> Prop) 
                        (Ir: D -> D -> Prop) (β : SecOrder), 
    <D Iv Ip Ir> ⊨ (SO~ β) = ~ <D Iv Ip Ir> ⊨ β.
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------------- *)

(* alt_Iv and alt_Ip results. *)

Lemma alt_Iv_eq: forall (D : Set) Iv (d : D) x,
    alt_Iv Iv d x x = d.
Proof.
  intros D Iv d x. unfold alt_Iv.
  rewrite FOvariable_dec_refl. auto.
Qed.

Lemma alt_Iv_neq: forall (D : Set) Iv (d : D) x y,
    x <> y -> alt_Iv Iv d x y = (Iv y).
Proof.
  intros D Iv d x y Heq. unfold alt_Iv.
  rewrite FOvariable_dec_r; firstorder.
Qed.

Lemma alt_Ip_eq : forall (D : Set) (Ip : predicate -> D -> Prop) pred_asgmt P,
    alt_Ip Ip pred_asgmt P P = pred_asgmt.
Proof.
  intros D Ip pa P. unfold alt_Ip.
  rewrite predicate_dec_refl. firstorder.
Qed.

Lemma alt_Ip_neq : forall (D : Set) (Ip : predicate -> D -> Prop) pred_asgmt P Q,
    P <> Q ->
    alt_Ip Ip pred_asgmt P Q = Ip Q.
Proof.
  intros D Ip pa P Q Heq. unfold alt_Ip.
  rewrite predicate_dec_r; firstorder.
Qed.

Lemma unalt_fun : forall (D:Set) (Ip: predicate -> D -> Prop) (P: predicate),
                      (alt_Ip Ip (Ip P) P) = Ip.
Proof.
  intros D Ip P. apply functional_extensionality; intros Q.
  apply functional_extensionality; intros x.
  destruct (predicate_dec P Q).
  subst. rewrite alt_Ip_eq. reflexivity.
  rewrite alt_Ip_neq; auto.
Qed.

Lemma unalt_fun_Iv : forall (D:Set) (Iv: FOvariable -> D) (x : FOvariable),
                      (alt_Iv Iv (Iv x) x) = Iv.
Proof.
  intros D Iv x. apply functional_extensionality; intros y.
  destruct (FOvariable_dec x y). subst.
  rewrite alt_Iv_eq. reflexivity.
  rewrite alt_Iv_neq; auto.
Qed.

Lemma alt_Iv_rem : forall W Iv d d2 x,
  alt_Iv (@alt_Iv W Iv d x) d2 x =
  alt_Iv Iv d2 x.
Proof.
  intros W Iv d d2 x.
  apply functional_extensionality.
  intros y. destruct (FOvariable_dec x y) as [H | H].
  subst. do 2 rewrite alt_Iv_eq. reflexivity.
  rewrite alt_Iv_neq. rewrite alt_Iv_neq.
  rewrite alt_Iv_neq. all : auto.
Qed.

Lemma alt_Iv_switch : forall (W : Set) Iv dx dy x y,
  x <> y ->
  alt_Iv (@alt_Iv W Iv dx x) dy y =
  alt_Iv (alt_Iv Iv dy y) dx x.
Proof.
  intros W Iv dx dt x y H.
  apply functional_extensionality.
  intros z.
  destruct x as [xn]; destruct y as [yn];
  destruct z as [zn].
  simpl.
  case_eq (beq_nat yn zn); intros Hbeq.
    case_eq (beq_nat xn zn); intros Hbeq2.
      rewrite (beq_nat_true _ _ Hbeq) in H.
      rewrite (beq_nat_true _ _ Hbeq2) in H.
      contradiction (H eq_refl).

      unfold alt_Iv. rewrite (beq_nat_true _ _ Hbeq) in *.
      do 2 rewrite FOvariable_dec_refl.
      rewrite FOvariable_dec_r; auto.
      
      assert (Var yn <> Var zn) as Hass. intros H'; inversion H'.
        subst. rewrite <- beq_nat_refl in Hbeq. discriminate.
      unfold alt_Iv. rewrite (FOvariable_dec_r (Var yn) (Var zn)).
      rewrite (FOvariable_dec_r (Var yn) (Var zn)). all : auto.
Qed.

Lemma alt_Ip_rem : forall (W : Set) (Ip : predicate -> W -> Prop) (pa1 pa2 : W -> Prop)
                                 (P : predicate),
     alt_Ip (alt_Ip Ip pa2 P) pa1 P = alt_Ip Ip pa1 P.
Proof.
  intros. apply functional_extensionality.
  intros x. apply functional_extensionality. intros w.
  unfold alt_Ip. destruct (predicate_dec P x); auto.
Qed.

Lemma alt_Ip_switch : forall (W : Set) (Ip : predicate -> W -> Prop) (pa1 pa2 : W -> Prop)
                                 P Q,
     P<>Q -> (alt_Ip (alt_Ip Ip pa2 Q) pa1 P 
                    = alt_Ip (alt_Ip Ip pa1 P) pa2 Q ).
Proof.
  intros ? ? ? ? P Q H. apply functional_extensionality.
  intros R. apply functional_extensionality. intros w.
  unfold alt_Ip. destruct (predicate_dec P R). subst.
  rewrite predicate_dec_r. auto. firstorder.
  auto.
Qed.

Lemma alt_Ip__list_occ_f : forall l W pa_l pa P Ip,
  ~ In P l ->
  alt_Ip_list (@alt_Ip W Ip pa P) pa_l l =
  alt_Ip (alt_Ip_list Ip pa_l l) pa P.
Proof.
  induction l; intros W pa_l pa P Ip Hocc.
    destruct pa_l; reflexivity.

    destruct pa_l. reflexivity.
    simpl in *. apply not_or_and in Hocc. destruct Hocc as [H1 H2].
    rewrite IHl. rewrite alt_Ip_switch. all : auto.
Qed.

(* ------------------------------------------------------------------------------------- *)

(* Proof of classicality *)

Lemma SO_LEM : forall α D Iv Ip Ir,  <D Iv Ip Ir> ⊨ (α SO∨ (SO~ α)).
Proof. intros. apply classic. Qed.