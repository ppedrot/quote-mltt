From Coq Require Import ssreflect.
From smpl Require Import Smpl.
From LogRel Require Import Utils Syntax.All GenericTyping.

Set Primitive Projections.

Lemma wf_in_ctx : forall Γ n decl, in_ctx Γ n decl -> n < #|Γ|.
Proof.
induction 1; cbn; auto with arith.
Qed.

Definition scoped (k : nat) (t : term) := allfv_term (fun n => n < k) t.
Definition well_scoped (Γ : context) (t : term) := allfv_term (fun n => n < length Γ) t.

Lemma well_scoped_ren {Γ Δ} t (ρ : Δ ≤ Γ) : well_scoped Γ t -> well_scoped Δ t⟨ρ⟩.
Proof.
intros * H; apply allfvRenR_term.
eapply allfvImpl_term; [|apply H].
intros x Hx; unfold funcomp; cbn in *.
destruct ρ as [ρ Hρ]; cbn.
clear H; revert x Hx; induction Hρ; cbn in *; intros x Hx; unfold funcomp.
+ Lia.lia.
+ now enough (ρ x < #|Γ|) by Lia.lia.
+ destruct x as [|x]; cbn; unfold funcomp; [Lia.lia|].
  enough (ρ x < #|Γ|) by Lia.lia.
  apply IHHρ; Lia.lia.
Qed.

Lemma scoped_shift : forall k t, scoped k t -> scoped (S k) t⟨↑⟩.
Proof.
intros k t Ht.
pose (Γ := List.repeat U k).
rewrite <- wk1_ren_on with (Γ := Γ) (F := U).
replace k with (length Γ) in * by now apply List.repeat_length.
change (well_scoped (cons U Γ) t⟨@wk1 Γ U⟩).
now eapply well_scoped_ren.
Qed.

Lemma scoped_S_up : forall m t,
  allfv_term (fun n => n < S m) t ->
  allfv_term (upAllfv_term_term (fun n : nat => n < m)) t.
Proof.
intros * H.
eapply allfvImpl_term; [|exact H].
intros [|]; cbn; eauto with arith.
Qed.

Lemma scoped_SS_up : forall m t,
  allfv_term (fun n => n < S (S m)) t ->
  allfv_term (upAllfv_term_term (upAllfv_term_term (fun n : nat => n < m))) t.
Proof.
intros * H.
eapply allfvImpl_term; [|exact H].
intros [|[|]]; cbn; eauto with arith.
Qed.

Lemma scoped_up_S : forall m t,
  allfv_term (upAllfv_term_term (fun n : nat => n < m)) t ->
  allfv_term (fun n => n < S m) t.
Proof.
intros * H.
eapply allfvImpl_term; [|exact H].
intros [|]; cbn; eauto 3 with arith.
Qed.

Lemma scoped_up_SS : forall m t,
  allfv_term (upAllfv_term_term (upAllfv_term_term (fun n : nat => n < m))) t ->
  allfv_term (fun n => n < S (S m)) t.
Proof.
intros * H.
eapply allfvImpl_term; [|exact H].
intros [|[|]]; cbn; eauto 3 with arith.
Qed.

Lemma scoped_incl : forall m n t, m < n -> scoped m t -> scoped n t.
Proof.
intros * H Ht.
eapply allfvImpl_term; [|exact Ht].
cbn; Lia.lia.
Qed.

Lemma scoped_subs {γ δ} t σ : scoped γ t -> (forall n, n < γ -> scoped δ (σ n)) ->
  scoped δ t[σ].
Proof.
unfold scoped; revert σ γ δ.
induction t; intros σ γ δ Ht Hσ; cbn in *;
repeat match goal with [ H : _ /\ _ |- _ ] => destruct H end;
prod_splitter; eauto.
all: try (
  apply scoped_S_up;
  first [eapply IHt2|eapply IHt1]; eauto using scoped_up_S;
  intros [|]; cbn; [unfold var_zero; Lia.lia|];
  unfold funcomp; intros;
  apply scoped_shift, Hσ; Lia.lia
).
+ apply scoped_SS_up.
  eapply IHt3; eauto using scoped_up_SS.
  intros [|[|]]; cbn; try (compute; Lia.lia).
  unfold funcomp; intros.
  apply scoped_shift, scoped_shift, Hσ; Lia.lia.
Qed.

Lemma scoped_subst1 : forall k t u,
  scoped (S k) t -> scoped k u -> scoped k t[u..].
Proof.
intros * Ht Hu.
eapply scoped_subs; [apply Ht|].
intros [|]; cbn; eauto with arith.
Qed.

Lemma well_scoped_subst1 : forall Γ A t u,
  well_scoped (Γ,, A) t -> well_scoped Γ u -> well_scoped Γ t[u..].
Proof.
intros * Ht Hu.
eapply scoped_subs; [apply Ht|].
intros [|]; cbn; eauto with arith.
Qed.

Create HintDb rzbltyping.

Inductive WfContextRzbl : context -> Set :=
| wf_ctx_nil : WfContextRzbl nil
| wf_ctx_cons : forall Γ A, WfContextRzbl Γ -> well_scoped Γ A -> WfContextRzbl (Γ,, A).

Lemma wf_in_ctx_scoped : forall Γ n decl, WfContextRzbl Γ -> in_ctx Γ n decl -> well_scoped Γ decl.
Proof.
intros * HΓ; revert n decl.
induction HΓ; intros n decl H; inversion H; subst.
+ unfold well_scoped; cbn; now apply scoped_shift.
+ unfold well_scoped; cbn.
  now eapply scoped_shift, IHHΓ.
Qed.

Hint Constructors WfContextRzbl : rzbltyping.

Record WfTypeRzbl (Γ : context) (A : term) := {
  wfty_ctx_scoped : WfContextRzbl Γ;
  wfty_ty_scoped : well_scoped Γ A;
}.

Hint Resolve wfty_ctx_scoped wfty_ty_scoped : rzbltyping.

Record eqNf (t u : term) := {
  eqnf_lhs : term;
  eqnf_rhs : term;
  eqnf_lnf : isNf t eqnf_lhs;
  eqnf_rnf : isNf u eqnf_rhs;
  eqnf_eqn : eqnf eqnf_lhs eqnf_rhs;
}.

Instance PER_eqNf : CRelationClasses.PER eqNf.
Proof.
split.
+ intros t u []; econstructor; tea.
  now symmetry.
+ intros t u v [t₀ u₀] [w₀ v₀]; econstructor; tea.
  assert (u₀ = w₀); [|subst].
  { eapply dredalg_det; eauto using isnf_red, isnf_dnf. }
  etransitivity; tea.
Qed.

Lemma isNf_wk : forall {Γ Δ} t t₀ (ρ : Δ ≤ Γ), isNf t t₀ -> isNf t⟨ρ⟩ t₀⟨ρ⟩.
Proof.
intros * []; split.
+ eauto using gcredalg_wk, wk_inj.
+ now apply dnf_ren.
Qed.

Lemma eqNf_wk : forall {Γ Δ} t u (ρ : Δ ≤ Γ), eqNf t u -> eqNf t⟨ρ⟩ u⟨ρ⟩.
Proof.
intros * []; econstructor; try now apply isNf_wk.
apply eqnf_ren; eauto using wk_inj.
Qed.

Lemma isNf_exp : forall t t' t₀, [t ⤳* t'] -> isNf t' t₀ -> isNf t t₀.
Proof.
intros * H []; split; tea.
etransitivity; tea.
now apply dred_red.
Qed.

Lemma isNf_red : forall t t' t₀, [t ⤳* t'] -> isNf t t₀ -> isNf t' t₀.
Proof.
intros * H []; split; tea.
eapply dred_red_det; eauto using dred_red.
Qed.

Lemma isNf_U : isNf U U.
Proof.
constructor; eauto using dnf; reflexivity.
Qed.

Lemma eqNf_exp : forall t t' u u', [t ⤳* t'] -> [u ⤳* u'] -> eqNf t' u' -> eqNf t u.
Proof.
intros * Ht Hu []; econstructor; try (now eapply isNf_exp); tea.
Qed.

Lemma eqNf_red : forall t t' u u', [t ⤳* t'] -> [u ⤳* u'] -> eqNf t u -> eqNf t' u'.
Proof.
intros * Ht Hu []; econstructor; try (now eapply isNf_red); tea.
Qed.

Lemma dnf_isNf : forall t, dnf t -> isNf t t.
Proof.
intros; econstructor; tea; reflexivity.
Qed.

Lemma isNf_eqNf : forall t t₀, isNf t t₀ -> eqNf t t₀.
Proof.
intros * []; exists t₀ t₀; now econstructor.
Qed.

Lemma oredalg_well_scoped : forall deep Γ t u, @OneRedAlg deep t u -> well_scoped Γ t -> well_scoped Γ u.
Proof.
intros deep Γ t u Hr; revert Γ.
unfold well_scoped.
induction Hr; intros; cbn in *;
repeat match goal with [ H : _ /\ _ |- _ ] => destruct H end;
prod_splitter; eauto.
all: try (
  apply scoped_S_up;
  unshelve eapply (IHHr (cons _ Γ));
  cbn; eauto using scoped_up_S, term
).
+ apply scoped_subst1; cbn; tea.
  now apply scoped_up_S.
+ apply scoped_SS_up.
  unshelve eapply (IHHr (cons _ (cons _ Γ)));
  cbn; eauto using scoped_up_SS, term.
Qed.

Lemma redalg_well_scoped : forall deep Γ t u, @RedClosureAlg deep t u -> well_scoped Γ t -> well_scoped Γ u.
Proof.
intros deep Γ t u Hr; induction Hr; eauto using oredalg_well_scoped.
Qed.

Lemma isNf_well_scoped : forall Γ t t₀, isNf t t₀ -> well_scoped Γ t ->  well_scoped Γ t₀.
Proof.
intros * [] H; eauto using redalg_well_scoped.
Qed.

Lemma isNf_tProd : forall A A₀ B B₀, isNf A A₀ -> isNf B B₀ -> isNf (tProd A B) (tProd A₀ B₀).
Proof.
intros * [] []; split; eauto using dredalg_prod, dnf.
Qed.

Lemma isNf_tLambda : forall A t t₀, isNf t t₀ -> isNf (tLambda A t) (tLambda A t₀).
Proof.
intros * []; split; eauto using dredalg_lambda, dnf.
Qed.

Lemma isNf_tSig : forall A A₀ B B₀, isNf A A₀ -> isNf B B₀ -> isNf (tSig A B) (tSig A₀ B₀).
Proof.
intros * [] []; split; eauto using dredalg_sig, dnf.
Qed.

(* Lemma isNf_tPair : forall p p₀, isNf (tFst p) isNf (tPair p p₀. *)

Lemma isNf_tId : forall A A₀ t t₀ u u₀, isNf A A₀ -> isNf t t₀ -> isNf u u₀ -> isNf (tId A t u) (tId A₀ t₀ u₀).
Proof.
intros * [] [] []; split; eauto using dredalg_id, dnf.
Qed.

Lemma isNf_tRefl : forall A A₀ t t₀, isNf A A₀ -> isNf t t₀ -> isNf (tRefl A t) (tRefl A₀ t₀).
Proof.
intros * [] []; split; eauto using dredalg_refl, dnf.
Qed.

Lemma isNf_tSucc : forall t t₀, isNf t t₀ -> isNf (tSucc t) (tSucc t₀).
Proof.
intros * []; split; eauto using dredalg_succ, dnf.
Qed.

Lemma isNf_tApp : forall t t₀ u u₀, whne t -> isNf t t₀ -> isNf u u₀ -> isNf (tApp t u) (tApp t₀ u₀).
Proof.
intros * ? [] []; split; eauto using dredalg_app, dnf, dne, dne_dnf_whne, dredalg_whne.
Qed.

Lemma isNf_tFst : forall t t₀, whne t -> isNf t t₀ -> isNf (tFst t) (tFst t₀).
Proof.
intros * ? []; split; eauto using dredalg_fst, dnf, dne, dne_dnf_whne, dredalg_whne.
Qed.

Lemma isNf_tSnd : forall t t₀, whne t -> isNf t t₀ -> isNf (tSnd t) (tSnd t₀).
Proof.
intros * ? []; split; eauto using dredalg_snd, dnf, dne, dne_dnf_whne, dredalg_whne.
Qed.

Lemma isNf_tEmptyElim : forall P P₀ t t₀, whne t -> isNf P P₀ -> isNf t t₀ -> isNf (tEmptyElim P t) (tEmptyElim P₀ t₀).
Proof.
intros * ? [] []; split; eauto using dredalg_emptyElim, dnf, dne, dne_dnf_whne, dredalg_whne.
Qed.

Lemma isNf_tNatElim : forall P P₀ hz hz₀ hs hs₀ t t₀,
  whne t -> isNf P P₀ -> isNf hz hz₀ -> isNf hs hs₀ -> isNf t t₀ -> isNf (tNatElim P hs hz t) (tNatElim P₀ hs₀ hz₀ t₀).
Proof.
intros * ? [] [] [] []; split; eauto using dredalg_natElim, dnf, dne, dne_dnf_whne, dredalg_whne.
Qed.

Lemma isNf_tIdElim : forall A A₀ x x₀ P P₀ hr hr₀ y y₀ e e₀,
  whne e -> isNf A A₀ -> isNf x x₀ -> isNf P P₀ -> isNf hr hr₀ -> isNf y y₀ -> isNf e e₀ -> isNf (tIdElim A x P hr y e) (tIdElim A₀ x₀ P₀ hr₀ y₀ e₀).
Proof.
intros * ? [] [] [] [] [] []; split; eauto using dredalg_idElim, dnf, dne, dne_dnf_whne, dredalg_whne.
Qed.

Lemma isNf_tDecide : forall A A₀ t t₀ u u₀,
  dnf t -> dnf u -> (~ closed0 t) + (~ closed0 u) ->
  isNf A A₀ -> isNf t t₀ -> isNf u u₀ ->
  isNf (tDecide A t u) (tDecide A₀ t₀ u₀).
Proof.
intros * ??? [] [] [].
assert (t = t₀) by (eapply dredalg_det; eauto; reflexivity); subst t₀.
assert (u = u₀) by (eapply dredalg_det; eauto; reflexivity); subst u₀.
split; eauto using dredalg_decide, dnf, dne, dne_dnf_whne, dredalg_whne.
Qed.

Lemma isNf_tReflect : forall A A₀ t t₀ u u₀ e e₀,
  whne e ->
  isNf A A₀ -> isNf t t₀ -> isNf u u₀ -> isNf e e₀ ->
  isNf (tReflect A t u e) (tReflect A₀ t₀ u₀ e₀).
Proof.
intros * ? [] [] [] []; split; eauto using dredalg_reflect, dnf, dne, dne_dnf_whne, dredalg_whne.
Qed.

Lemma isNf_eta_tLambda : forall t t₀,
  isNf (eta_expand t) t₀ -> ∑ r₀, isNf t r₀ × ((∑ A, r₀ = tLambda A t₀) + (eta_expand r₀ = t₀)).
Proof.
intros t t₀ [? Hnf].
assert (Hr : [eta_expand t ⇊ t₀]) by eauto using dredalg_bigstep.
inversion Hr; subst; clear Hr;
repeat match goal with [ H : bigstep _ _ _ |- _ ] => apply bigstep_dredalg in H end.
+ let H := match goal with [H : [ _ ⤳* _ ] |- _] => H end in
  destruct (dredalg_ren_adj _ _ _ _ shift_inj H) as [u₀ Hu];
  destruct u₀; cbn in *; try congruence; injection Hu; intros; subst; clear Hu.
  match goal with [H : [t⟨↑⟩ ⤳* tLambda ?A⟨↑⟩ ?v⟨_⟩] |- _] => rename A into A₀, v into v₀ end.
  assert [t ⤳* tLambda A₀ v₀].
  { eapply redalg_ren_inv; [apply shift_inj|tea]. }
  assert (Hrw : v₀⟨upRen_term_term ↑⟩[(tRel 0)..] = v₀) by now bsimpl.
  assert [v₀ ⇶* t₀] by now rewrite <- Hrw.
  exists (tLambda A₀ t₀); split; [split|]; [|eauto using dnf|].
  - etransitivity; [now eapply dred_red|].
    now apply dredalg_lambda.
  - left; eexists; reflexivity.
+ let H := match goal with [H : [ _ ⤳* _ ] |- _] => H end in
  destruct (dredalg_ren_adj _ _ _ _ shift_inj H) as [v₀ Hv]; subst.
  assert [t ⤳* v₀].
  { eapply redalg_ren_inv; [apply shift_inj|tea]. }
  let H := match goal with [H : [ _⟨_⟩ ⇶* _ ] |- _] => H end in
  destruct (dredalg_ren_adj _ _ _ _ shift_inj H) as [w₀ Hw]; subst.
  assert [v₀ ⇶* w₀].
  { eapply redalg_ren_inv; [apply shift_inj|tea]. }
  match goal with [H : [ tRel 0 ⇶* ?v ] |- _] =>
    assert (tRel 0 = v) by eauto using dred_dnf, dne, dnf; subst v
  end.
  inversion Hnf; subst; inversion H5; subst.
  assert (dne w₀) by eauto using dne_ren_rev.
  exists w₀; split; [split|]; [|tea|right; reflexivity].
  - etransitivity; [|tea].
    now eapply dred_red.
  - eauto using dnf.
Qed.

Lemma isNf_eta_tPair : forall t p₀ q₀,
  isNf (tFst t) p₀ -> isNf (tSnd t) q₀ -> ∑ r₀, isNf t r₀ × ((∑ A B, r₀ = tPair A B p₀ q₀) + (p₀ = tFst r₀ × q₀ = tSnd r₀)).
Proof.
intros * [? Hnf] [].
assert (Hr : [tFst t ⇊ p₀]) by eauto using dredalg_bigstep.
inversion Hr; subst; clear Hr;
repeat match goal with [ H : bigstep _ _ _ |- _ ] => apply bigstep_dredalg in H end.
+ assert [b ⇶* q₀].
  { assert (Hr : [tSnd t ⇊ q₀]) by eauto using dredalg_bigstep.
    inversion Hr; subst; clear Hr;
    repeat match goal with [ H : bigstep _ _ _ |- _ ] => apply bigstep_dredalg in H end.
    + match goal with [ H : [t ⤳* ?p], H' : [t ⤳* ?q] |- _ ] => assert (Heq : p = q) end.
      { eapply whred_det; eauto using whnf. }
      injection Heq; intros; subst; tea.
    + assert (tPair A B a b = n); [|subst].
      { eapply whred_det; eauto using whnf, whne. }
      inversion H3. }
  exists (tPair A B p₀ q₀); split; [split|].
  - etransitivity; [now apply dred_red|].
    now eapply dredalg_pair.
  - eauto using dnf.
  - left; now eexists.
+ assert [t ⇶* t₀].
  { etransitivity; [now eapply dred_red|tea]. }
  exists t₀; split; [split|].
  - tea.
  - inversion Hnf; subst; inversion H3; subst.
    eauto using dnf.
  - right; split; [reflexivity|].
    assert (Hr : [tSnd t ⇊ q₀]) by eauto using dredalg_bigstep.
    inversion Hr; subst; clear Hr;
    repeat match goal with [ H : bigstep _ _ _ |- _ ] => apply bigstep_dredalg in H end.
    * assert (tPair A B a b = n); [|subst].
      { eapply whred_det; eauto using whnf, whne. }
      inversion H1.
    * eapply dredalg_det; eauto using dredalg_snd, gred_trans, redalg_snd, dred_red.
      inversion Hnf; subst; inversion H3; subst; eauto using dnf, dne.
Qed.

Lemma eqNf_U : eqNf U U.
Proof.
econstructor; try eapply isNf_U.
reflexivity.
Qed.

Lemma eqNf_tProd : forall A A' B B', eqNf A A' -> eqNf B B' -> eqNf (tProd A B) (tProd A' B').
Proof.
intros * [A₀ A₁] [B₀ B₁]; exists (tProd A₀ B₀) (tProd A₁ B₁);
eauto using isNf_tProd, eqnf_tProd.
Qed.

Lemma eqNf_tLambda : forall A A' t t', eqNf t t' -> eqNf (tLambda A t) (tLambda A' t').
Proof.
intros * [t₀ t₁]; exists (tLambda A t₀) (tLambda A' t₁);
eauto using isNf_tLambda, eqnf_tLambda.
Qed.

Lemma eqNf_eta_tLambda : forall t t',
  eqNf (tApp t⟨↑⟩ (tRel 0)) (tApp t'⟨↑⟩ (tRel 0)) -> eqNf t t'.
Proof.
intros * [t₀ t₁ H₀ H₁ Heq].
destruct (isNf_eta_tLambda _ _ H₀) as (v₀&?&Heq₀).
destruct (isNf_eta_tLambda _ _ H₁) as (v₁&?&Heq₁).
exists v₀ v₁; tea.
destruct Heq₀ as [[A₀ ?]|]; destruct Heq₁ as [[A₁ ?]|]; subst.
+ now apply eqnf_tLambda.
+ now apply eqnf_tLambda_whne.
+ now apply eqnf_whne_tLambda.
+ unfold eqnf in Heq; cbn in Heq.
  injection Heq; intros Heq'.
  eapply eqnf_ren_rev; eauto using shift_inj.
Qed.

Lemma eqNf_tSig : forall A A' B B', eqNf A A' -> eqNf B B' -> eqNf (tSig A B) (tSig A' B').
Proof.
intros * [A₀ A₁] [B₀ B₁]; exists (tSig A₀ B₀) (tSig A₁ B₁);
eauto using isNf_tSig, eqnf_tSig.
Qed.

Lemma eqNf_eta_tPair : forall t t', eqNf (tFst t) (tFst t') -> eqNf (tSnd t) (tSnd t') -> eqNf t t'.
Proof.
intros * [p₀ p₁ Hp₀ Hp₁ Heqp] [q₀ q₁ Hq₀ Hq₁ Heqq].
destruct (isNf_eta_tPair _ _ _ Hp₀ Hq₀) as (v₀&?&Heq₀).
destruct (isNf_eta_tPair _ _ _ Hp₁ Hq₁) as (v₁&?&Heq₁).
exists v₀ v₁; tea.
destruct Heq₀ as [(A₀&B₀&?)|[]]; destruct Heq₁ as [(A₁&B₁&?)|[]]; subst.
+ now apply eqnf_tPair.
+ now apply eqnf_tPair_whne.
+ now apply eqnf_whne_tPair.
+ unfold eqnf in Heqp; cbn in Heqp; congruence.
Qed.

Lemma eqNf_tId : forall A A' t t' u u', eqNf A A' -> eqNf t t' -> eqNf u u' -> eqNf (tId A t u) (tId A' t' u').
Proof.
intros * [A₀ A₁] [t₀ t₁] [u₀ u₁]; exists (tId A₀ t₀ u₀) (tId A₁ t₁ u₁);
eauto using isNf_tId, eqnf_tId.
Qed.

Lemma eqNf_tRefl : forall A A' t t', eqNf A A' -> eqNf t t' -> eqNf (tRefl A t) (tRefl A' t').
Proof.
intros * [A₀ A₁] [t₀ t₁]; exists (tRefl A₀ t₀) (tRefl A₁ t₁);
eauto using isNf_tRefl, eqnf_tRefl.
Qed.

Lemma eqNf_tSucc : forall t t', eqNf t t' -> eqNf (tSucc t) (tSucc t').
Proof.
intros * [t₀ t₁]; exists (tSucc t₀) (tSucc t₁);
eauto using isNf_tSucc, eqnf_tSucc.
Qed.

Lemma eqNf_tApp : forall t t' u u', whne t -> whne t' -> eqNf t t' -> eqNf u u' -> eqNf (tApp t u) (tApp t' u').
Proof.
intros * ?? [t₀ t₁] [u₀ u₁]; exists (tApp t₀ u₀) (tApp t₁ u₁);
eauto using isNf_tApp, eqnf_tApp.
Qed.

Lemma eqNf_tFst : forall t t', whne t -> whne t' -> eqNf t t' -> eqNf (tFst t) (tFst t').
Proof.
intros * ?? [t₀ t₁]; exists (tFst t₀) (tFst t₁);
eauto using isNf_tFst, eqnf_tFst.
Qed.

Lemma eqNf_tSnd : forall t t', whne t -> whne t' -> eqNf t t' -> eqNf (tSnd t) (tSnd t').
Proof.
intros * ?? [t₀ t₁]; exists (tSnd t₀) (tSnd t₁);
eauto using isNf_tSnd, eqnf_tSnd.
Qed.

Lemma eqNf_tEmptyElim : forall P P' t t', whne t -> whne t' -> eqNf P P' -> eqNf t t' -> eqNf (tEmptyElim P t) (tEmptyElim P' t').
Proof.
intros * ?? [P₀ P₁] [t₀ t₁]; exists (tEmptyElim P₀ t₀) (tEmptyElim P₁ t₁);
eauto using isNf_tEmptyElim, eqnf_tEmptyElim.
Qed.

Lemma eqNf_tNatElim : forall P P' hz hz' hs hs' t t', whne t -> whne t' ->
  eqNf P P' -> eqNf hz hz' -> eqNf hs hs' -> eqNf t t' -> eqNf (tNatElim P hz hs t) (tNatElim P' hz' hs' t').
Proof.
intros * ?? [P₀ P₁] [hz₀ hz₁] [hs₀ hs₁] [t₀ t₁]; exists (tNatElim P₀ hz₀ hs₀ t₀) (tNatElim P₁ hz₁ hs₁ t₁);
eauto using isNf_tNatElim, eqnf_tNatElim.
Qed.

Lemma eqNf_tIdElim : forall A A' x x' P P' hr hr' y y' e e',
  whne e -> whne e' ->
  eqNf A A' -> eqNf x x' -> eqNf P P' -> eqNf hr hr' -> eqNf y y' -> eqNf e e' -> eqNf (tIdElim A x P hr y e) (tIdElim A' x' P' hr' y' e').
Proof.
intros * ?? [A₀ A₁] [x₀ x₁] [P₀ P₁] [hr₀ hr₁] [y₀ y₁] [e₀ e₁]; exists (tIdElim A₀ x₀ P₀ hr₀ y₀ e₀) (tIdElim A₁ x₁ P₁ hr₁ y₁ e₁);
eauto using isNf_tIdElim, eqnf_tIdElim.
Qed.

Lemma eqNf_tDecide : forall A A' t t' u u',
  dnf t -> dnf t' -> dnf u -> dnf u' -> (~ closed0 t) + (~ closed0 u) -> (~ closed0 t') + (~ closed0 u') ->
  eqNf A A' -> eqNf t t' -> eqNf u u' ->
  eqNf (tDecide A t u) (tDecide A' t' u').
Proof.
intros * ?????? [A₀ A₁] [t₀ t₁] [u₀ u₁]; exists (tDecide A₀ t₀ u₀) (tDecide A₁ t₁ u₁);
eauto using isNf_tDecide, eqnf_tDecide.
Qed.

Lemma eqNf_tReflect : forall A A' t t' u u' e e',
  whne e -> whne e' ->
  eqNf A A' -> eqNf t t' -> eqNf u u' -> eqNf e e' -> eqNf (tReflect A t u e) (tReflect A' t' u' e').
Proof.
intros * ?? [A₀ A₁] [t₀ t₁] [u₀ u₁] [e₀ e₁]; exists (tReflect A₀ t₀ u₀ e₀) (tReflect A₁ t₁ u₁ e₁);
eauto using isNf_tReflect, eqnf_tReflect.
Qed.

Record TypingRzbl (Γ : context) (A t : term) := {
  typ_ctx_scoped : WfContextRzbl Γ;
  typ_ty_scoped : well_scoped Γ A;
  typ_tm_scoped : well_scoped Γ t;
}.

Hint Resolve typ_ctx_scoped typ_ty_scoped typ_tm_scoped : rzbltyping.

Record ConvTypeRzbl (Γ : context) (A B : term) := {
  cvty_ctx_scoped : WfContextRzbl Γ;
  cvty_lhs_scoped : well_scoped Γ A;
  cvty_rhs_scoped : well_scoped Γ B;
  cvty_eqn : eqNf A B;
}.

Hint Resolve cvty_ctx_scoped cvty_lhs_scoped cvty_rhs_scoped : rzbltyping.

Record ConvTermRzbl (Γ : context) (A t u : term) := {
  cvtm_ctx_scoped : WfContextRzbl Γ;
  cvtm_typ_scoped : well_scoped Γ A;
  cvtm_lhs_scoped : well_scoped Γ t;
  cvtm_rhs_scoped : well_scoped Γ u;
  cvtm_eqn : eqNf t u;
}.

Hint Resolve cvtm_ctx_scoped cvtm_typ_scoped cvtm_lhs_scoped cvtm_rhs_scoped : rzbltyping.

Record TypeRedClosure (Γ : context) (A B : term) := {
  tyred_ctx_scoped : WfContextRzbl Γ;
  tyred_lhs_scoped : well_scoped Γ A;
  tyred_rhs_scoped : well_scoped Γ B;
  tyred_red : [A ⤳* B];
}.

Record TermRedClosure (Γ : context) (A t u : term) := {
  tmred_ctx_scoped : WfContextRzbl Γ;
  tmred_typ_scoped : well_scoped Γ A;
  tmred_lhs_scoped : well_scoped Γ t;
  tmred_rhs_scoped : well_scoped Γ u;
  tmred_red : [t ⤳* u];
}.

Record RzblNeutralConversion (Γ : context) (A : term) (m n : term) := {
  cvne_ctx_scoped : WfContextRzbl Γ;
  cvne_typ_scoped : well_scoped Γ A;
  cvne_lhs_whne   : whne m;
  cvne_lhs_scoped : well_scoped Γ m;
  cvne_rhs_whne   : whne n;
  cvne_rhs_scoped : well_scoped Γ n;
  cvne_eqn : eqNf m n;
}.

Module RealizabilityTypingData.

  Definition rz : tag.
  Proof.
  constructor.
  Qed.

  #[export] Instance WfContext_Rzbl : WfContext rz := WfContextRzbl.
  #[export] Instance WfType_Rzbl : WfType rz := WfTypeRzbl.
  #[export] Instance Typing_Rzbl : Typing rz := TypingRzbl.
  #[export] Instance ConvType_Rzbl : ConvType rz := ConvTypeRzbl.
  #[export] Instance ConvTerm_Rzbl : ConvTerm rz := ConvTermRzbl.
  #[export] Instance RedType_Rzbl : RedType rz := TypeRedClosure.
  #[export] Instance RedTerm_Rzbl : RedTerm rz := TermRedClosure.
  #[export] Instance ConvNeuConv_Rzbl : ConvNeuConv rz := RzblNeutralConversion.

  Ltac fold_rzbl :=
    change WfContextRzbl with (wf_context (ta := rz)) in * ;
    change WfTypeRzbl with (wf_type (ta := rz)) in *;
    change TypingRzbl with (typing (ta := rz)) in * ;
    change ConvTypeRzbl with (conv_type (ta := rz)) in * ;
    change ConvTermRzbl with (conv_term (ta := rz)) in * ;
    change TypeRedClosure with (red_ty (ta := rz)) in *;
    change TermRedClosure with (red_tm (ta := rz)) in *;
    change RzblNeutralConversion with (conv_neu_ty (ta := rz)) in *.

  Ltac unfold_rzbl :=
    change (wf_context (ta := rz)) with WfContextRzbl in * ;
    change (wf_type (ta := rz)) with WfTypeRzbl in *;
    change (typing (ta := rz)) with TypingRzbl in * ;
    change (conv_type (ta := rz)) with ConvTypeRzbl in * ;
    change (conv_term (ta := rz)) with ConvTermRzbl in * ;
    change (red_ty (ta := rz)) with TypeRedClosure in *;
    change (red_tm (ta := rz)) with TermRedClosure in *;
    change (conv_neu_ty (ta := rz)) with RzblNeutralConversion in *.

  Smpl Add fold_rzbl : refold.

End RealizabilityTypingData.

Module RealizabilityTypingProperties.

Import RealizabilityTypingData.

Local Ltac case_rzbl := repeat match goal with
| [ H : wf_type (ta := rz) _ _ |- _ ] => destruct H
| [ H : typing (ta := rz) _ _ _ |- _ ] => destruct H
| [ H : conv_type (ta := rz) _ _ _ |- _ ] => destruct H
| [ H : conv_term (ta := rz) _ _ _ _ |- _ ] => destruct H
| [ H : red_ty (ta := rz) _ _ _ |- _ ] => destruct H
| [ H : red_tm (ta := rz) _ _ _ _ |- _ ] => destruct H
| [ H : conv_neu_ty (ta := rz) _ _ _ _ |- _ ] => destruct H
end.

#[export, refine] Instance WfContextRzblProperties : WfContextProperties (ta := rz) := {}.
Proof.
all: intros; case_rzbl; auto with rzbltyping.
+ constructor.
+ now constructor.
Qed.

#[export, refine] Instance WfTypeRzblProperties : WfTypeProperties (ta := rz) := {}.
Proof.
all: intros; case_rzbl; split; cbn; auto using well_scoped_ren, scoped_S_up.
Qed.

#[export, refine] Instance TypingRzblProperties : TypingProperties (ta := rz) := {}.
Proof.
all: intros; case_rzbl; split; cbn in *;
  prod_splitter; repeat match goal with [ H : _ /\ _ |- _ ] => destruct H end;
  try apply scoped_subst1; cbn;
  eauto using well_scoped_ren, scoped_S_up, scoped_up_S.
+ now eapply wf_in_ctx_scoped.
+ now eapply wf_in_ctx.
+ now apply scoped_up_S.
+ now apply scoped_up_S.
+ eapply scoped_subs; [eauto|]; cbn.
  intros [|[|]]; cbn; eauto with arith.
+ now apply scoped_SS_up.
Qed.

#[export, refine] Instance ConvTypeRzblProperties : ConvTypeProperties (ta := rz) := {}.
Proof.
all: intros; case_rzbl; split; cbn; auto using well_scoped_ren, scoped_S_up.
+ intros t u []; split; eauto.
  now symmetry.
+ intros t u v [] []; split; eauto.
  now etransitivity.
+ now apply eqNf_wk.
+ now eapply eqNf_exp.
+ eauto using isNf_eqNf, dnf_isNf, dnf, dne.
+ now eapply eqNf_tProd.
+ now eapply eqNf_tSig.
+ now eapply eqNf_tId.
Qed.

#[export, refine] Instance ConvTermRzblProperties : ConvTermProperties (ta := rz) := {}.
Proof.
all: intros; case_rzbl; split; cbn in *; prod_splitter;
auto using well_scoped_ren, scoped_S_up, isNf_eqNf, dnf_isNf, dnf, dne.
+ now split; case_rzbl.
+ split; case_rzbl; eauto; now etransitivity.
+ now apply eqNf_wk.
+ now eapply eqNf_exp.
+ now apply eqNf_tProd.
+ now apply eqNf_tSig.
+ now apply eqNf_tLambda.
+ now apply eqNf_eta_tLambda.
+ now apply eqNf_tSucc.
+ now apply eqNf_eta_tPair.
+ now apply eqNf_tId.
+ now apply eqNf_tRefl.
Qed.

#[export, refine] Instance ConvNeuRzblProperties : ConvNeuProperties (ta := rz) := {}.
Proof.
all: intros; case_rzbl; try constructor; cbn in *;
  prod_splitter; repeat match goal with [ H : _ /\ _ |- _ ] => destruct H end;
  try apply scoped_subst1; cbn;
  auto using well_scoped_ren, scoped_S_up, whne, whne_ren_wl.
+ now split; case_rzbl.
+ split; case_rzbl; eauto; now etransitivity.
+ now apply eqNf_wk.
+ eauto using isNf_eqNf, dnf_isNf, dnf, dne.
+ now apply scoped_up_S.
+ now apply eqNf_tApp.
+ now apply eqNf_tNatElim.
+ now apply eqNf_tEmptyElim.
+ now apply eqNf_tFst.
+ now apply scoped_up_S.
+ now apply eqNf_tSnd.
+ eapply scoped_subs; [eauto|].
  intros [|[|]]; cbn; eauto with arith.
+ now apply scoped_SS_up.
+ now apply scoped_SS_up.
+ now apply eqNf_tIdElim.
+ now apply eqNf_tDecide.
+ now apply eqNf_tReflect.
Qed.

#[export, refine] Instance RedTypeRzblProperties : RedTypeProperties (ta := rz) := {}.
Proof.
all: intros; case_rzbl; try split; case_rzbl; eauto using well_scoped_ren.
+ apply credalg_wk; eauto using wk_inj.
+ reflexivity.
+ now etransitivity.
Qed.

#[export, refine] Instance RedTermRzblProperties : RedTermProperties (ta := rz) := {}.
Proof.
all: intros; case_rzbl; try constructor; cbn in *;
  prod_splitter; repeat match goal with [ H : _ /\ _ |- _ ] => destruct H end;
  try apply scoped_subst1; cbn;
  eauto using well_scoped_ren, scoped_S_up, redalg_one_step, OneRedAlg.
+ apply credalg_wk; eauto using wk_inj.
+ now apply scoped_up_S.
+ now apply redalg_app.
+ now apply redalg_natElim.
+ now apply redalg_natEmpty.
+ now apply redalg_fst.
+ prod_splitter; eauto.
  now apply scoped_S_up.
+ now apply scoped_up_S.
+ now apply redalg_snd.
+ eapply scoped_subs; [eassumption|].
  cbn; intros [|[|]]; cbn; eauto 4 with arith.
+ now apply scoped_SS_up.
+ eapply scoped_subs; [eauto|].
  intros [|[|]]; cbn; eauto with arith.
+ now apply scoped_SS_up.
+ now apply scoped_SS_up.
+ now apply redalg_idElim.
+ now apply redalg_decide.
+ now apply redalg_reflect.
+ reflexivity.
+ now case_rzbl.
+ now case_rzbl.
+ now case_rzbl.
+ now case_rzbl.
+ case_rzbl; now etransitivity.
Qed.

#[export] Instance RealizabilityTypingProperties : GenericTypingProperties rz _ _ _ _ _ _ _ _ := {}.

#[export, refine] Instance RealizabilitySNTypingProperties : SNTypingProperties rz _ _ _ _ _ := {}.
Proof.
+ intros * [???? []].
  do 2 eexists; prod_splitter; eauto.
  - split; tea; [|now apply isNf_eqNf].
    now eapply isNf_well_scoped.
  - split; tea; [|now apply isNf_eqNf].
    now eapply isNf_well_scoped.
Qed.

#[export, refine] Instance RealizabilitySNCompleteTypingProperties : SNCompleteTypingProperties rz _ _ _ _ _ _ := {}.
Proof.
+ intros * [] [] **; split; tea.
  econstructor; tea.
+ intros * [] [] **; split; tea.
  econstructor; tea.
Qed.

End RealizabilityTypingProperties.
