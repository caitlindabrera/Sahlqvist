Require Import Modal_syntax uniform conjSO_exFO_relatSO ST.

Open Scope type_scope.

Inductive vsSahlq_ante : Modal -> Prop :=
| vsSahlq_ante_atom p : vsSahlq_ante (atom p)
| vsSahlq_ante_mconj ψ1 ψ2 :
    vsSahlq_ante ψ1 -> vsSahlq_ante ψ2 -> vsSahlq_ante (mconj ψ1 ψ2)
| vsSahlq_ante_dia ψ : vsSahlq_ante ψ -> vsSahlq_ante (dia ψ).

Inductive vsSahlq : Modal -> Prop :=
| vsSahlq_y ϕ1 ϕ2:
    vsSahlq_ante ϕ1 -> pos ϕ2 -> vsSahlq (mimpl ϕ1 ϕ2).

Definition corresponds (ϕ : Modal) (α: SecOrder) :=
  forall W Iv Ip Ir, <W Iv Ip Ir> ⊨ α <-> <W Ir> ⊩ ϕ.

Lemma vsSahlq_ante_dec : forall phi,
    {vsSahlq_ante phi} + {~ vsSahlq_ante phi}.
Proof.
  induction phi; simpl;
    try solve [left; constructor];
    try solve [right; intros H; inversion H].
  - destruct IHphi1 as [IH1 | IH1].
    destruct IHphi2 as [IH2 | IH2].
    left. constructor; auto.
    all : right; intros H; inversion H; subst; firstorder.
  - destruct IHphi as [IH | IH].
    left. constructor; auto.
    right; intros H; inversion H; subst; firstorder.
Qed.

Lemma vsSahlq_ex : forall phi,
  vsSahlq phi ->
  exists phi1 phi2, vsSahlq_ante phi1 /\ pos phi2.
Proof. intros phi H. inversion H. firstorder.  Qed.

Lemma vsSahlq_ante_mconj_rev : forall phi1 phi2,
  vsSahlq_ante (mconj phi1 phi2) ->
  (vsSahlq_ante phi1 /\ vsSahlq_ante phi2).
Proof. intros phi1 phi2 H. inversion H; auto. Qed.

Lemma vsSahlq_ante_conjSO_exFO_relatSO : forall phi x,
  vsSahlq_ante phi ->
  conjSO_exFO_relatSO (ST phi x) = true.
Proof.
  induction phi; intros [xn] Hvs;
    inversion Hvs; subst; simpl.
  destruct p; auto.
  rewrite IHphi1. all : auto. 
Qed.

Lemma vsSahlq_dest_ex : forall phi,
  vsSahlq phi ->
  exists phi1 phi2,
    phi = mimpl phi1 phi2 /\ 
    vsSahlq_ante phi1 /\ pos phi2.
Proof.
  destruct phi; intros Hvs;
  inversion Hvs; subst. firstorder.
Qed.

Lemma vsSahlq_dest_ex_comp : forall phi,
  vsSahlq phi ->
  existsT2 phi1 phi2,
    ((phi = mimpl phi1 phi2) * 
    vsSahlq_ante phi1 * pos phi2).
Proof.
  intros phi Hphi. destruct phi;
    try solve [assert False; [inversion Hphi|]; contradiction].
  exists phi1. exists phi2. inversion Hphi. subst.
  auto.
Qed.

Lemma vsSahlq_dest_implSO : forall phi x,
  vsSahlq phi ->
  (ST phi x) = implSO (calc_ante_SO (ST phi x)) 
                      (calc_cons_SO (ST phi x)).
Proof.
  intros phi x Hvs.
  destruct (vsSahlq_dest_ex phi Hvs) as [phi1 [phi2 [Heq [Hvsa Hun]]]].
  rewrite Heq.
  reflexivity.
Qed.

Lemma vsSahlq_ante_dest : forall phi,
  vsSahlq phi ->  vsSahlq_ante (calc_ante_modal phi).
Proof.
  intros phi Hvs. inversion Hvs; subst.
  simpl. auto.
Qed.

Lemma vsSahlq_cons_dest : forall phi,
  vsSahlq phi ->  pos (calc_cons_modal phi).
Proof.
  intros phi Hvs. inversion Hvs; subst.
  simpl. auto.
Qed.