From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.Syntax Require Import Confluence Standardisation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Universe Nat Sigma SimpleArr Id.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

(* More rewriting theory *)

Lemma sred_dnf_det_eqnf : forall t u v,
  [t →s u] -> [t →s v] -> dnf u -> dnf v -> eqannot u v.
Proof.
intros * Hu Hv Hnfu Hnfv.
destruct (sred_dredalg _ _ Hu) as (u₀&?&?); eauto.
destruct (sred_dredalg _ _ Hv) as (v₀&?&?); eauto.
assert (u₀ = v₀) by eauto using dredalg_det, dnf_eqannot; subst.
now etransitivity; eauto.
Qed.

Lemma pred_gred_dnf_pushout : forall t u p q t₀ u₀,
  [t ⇉* p] -> [u ⇉* q] -> [t ⇶* t₀] -> [u ⇶* u₀] -> eqnf p q -> dnf t₀ -> dnf u₀ ->
  eqnf t₀ u₀.
Proof.
intros * Hp Hq Ht Hu Heq Hnft Hnfu.
assert [t ⇉* t₀] by now apply dredalg_pred_clos.
assert [u ⇉* u₀] by now apply dredalg_pred_clos.
destruct (pred_confluent t p t₀) as (r₀&?&?); tea.
destruct (pred_confluent u q u₀) as (s₀&?&?); tea.
assert (eqannot t₀ r₀) by now apply dnf_pred_clos_id.
assert (eqannot u₀ s₀) by now apply dnf_pred_clos_id.
assert (dnf r₀) by now eapply dnf_eqannot.
assert (dnf s₀) by now eapply dnf_eqannot.
assert (eqnf t₀ r₀).
{ unfold eqnf; rewrite !erase_unannot_etared; congruence. }
assert (eqnf u₀ s₀).
{ unfold eqnf; rewrite !erase_unannot_etared; congruence. }
etransitivity; [tea|]; etransitivity; [|symmetry; tea].
assert [p →s r₀] by now apply pred_sred.
assert [q →s s₀] by now apply pred_sred.
destruct (sred_erased p (erase p) r₀) as (r₁&?&Hr₁); eauto using erase_erased.
destruct (sred_erased q (erase q) s₀) as (s₁&?&Hs₁); eauto using erase_erased.
rewrite <- Heq in Hs₁.
assert (eqannot r₁ s₁) by eauto using sred_dnf_det_eqnf, erased_dnf.
etransitivity; [now apply erased_eqnf|].
etransitivity; [|symmetry; now apply erased_eqnf].
now apply eqannot_eqnf.
Qed.

Section EquationalCompleteness.

Context `{GenericTypingProperties}.
Context {SN : SNTypingProperties ta _ _ _ _ _}.
Context {SNC : SNCompleteTypingProperties ta _ _ _ _ _ _}.

Lemma TermRedWf_dnf_det : forall Γ A t u,
  [Γ |- t :⤳*: u : A] -> dnf t -> t = u.
Proof.
intros.
eapply dred_dnf; tea.
now eapply dred_red, redtm_sound, tmr_wf_red.
Qed.

Definition hasNf_red {Γ l A A' t u} {rA : [Γ ||-<l> A ≅ A']} (p : [rA | Γ ||- t ≅ u : _ ≅ _]) :
  ∑ t₀ : term, isNf t t₀.
Proof.
apply escapeTm in p.
destruct p as (?&?&p).
apply SN.(snty_nf) in p.
destruct p as (?&?&?&?).
now eexists.
Qed.

Lemma isNf_TermRedWf_red : forall Γ A t u u₀,
  [Γ |- u :⤳*: t : A] -> isNf u u₀ -> isNf t u₀.
Proof.
intros.
eapply isNf_red; [|tea].
now eapply redtm_sound, tmr_wf_red; tea.
Qed.

Lemma eqnf_nfeval_app_compat : forall f f₀ g g₀ a a₀ b b₀ v₀ w₀,
  isNf f f₀ -> isNf g g₀ -> isNf a a₀ -> isNf b b₀ ->
  isNf (tApp f a) v₀ -> isNf (tApp g b) w₀ ->
  eqnf f₀ g₀ -> eqnf a₀ b₀ ->
  eqnf v₀ w₀.
Proof.
intros * [] [] [] [] [] [] Heq1 Heq2.
assert (eqnf (tApp f₀ a₀) (tApp g₀ b₀)) by now apply eqnf_tApp.
assert [f ⇉* f₀] by now apply dredalg_pred_clos.
assert [g ⇉* g₀] by now apply dredalg_pred_clos.
assert [a ⇉* a₀] by now apply dredalg_pred_clos.
assert [b ⇉* b₀] by now apply dredalg_pred_clos.
assert [tApp f a ⇉* tApp f₀ a] by now apply pred_clos_app.
assert [tApp g b ⇉* tApp g₀ b] by now apply pred_clos_app.
assert (Happ : forall t u u', [u ⇉* u'] -> [tApp t u ⇉* tApp t u']).
{ clear; intros t u u' Hr; revert t.
  induction Hr; intros f.
  + constructor.
  + econstructor; [|apply IHHr].
    constructor; [now apply pred_refl|tea]. }
assert [tApp f₀ a ⇉* tApp f₀ a₀] by now apply Happ.
assert [tApp g₀ b ⇉* tApp g₀ b₀] by now apply Happ.
assert [tApp f a ⇉* tApp f₀ a₀] by now eapply pred_trans.
assert [tApp g b ⇉* tApp g₀ b₀] by now eapply pred_trans.
assert [tApp f a ⇉* v₀] by now apply dredalg_pred_clos.
assert [tApp g b ⇉* w₀] by now apply dredalg_pred_clos.
eauto using pred_gred_dnf_pushout.
Qed.

#[local]
Lemma redtm_beta_ren : forall Γ Δ A B t a (ρ : Δ ≤ Γ),
  [|- Δ] ->
  [Γ |- A] ->
  [Δ |- a : A⟨ρ⟩] ->
  [Γ,, A |- t : B] ->
  [Δ |- tApp (tLambda A⟨ρ⟩ t⟨upRen_term_term ρ⟩) a ⤳* t[a .: ρ >> tRel] : B[a .: ρ >> tRel]].
Proof.
intros.
rewrite !(subst1_ren_wk_up (A := A)).
assert [Δ |- A⟨ρ⟩] by now eapply wft_wk.
apply redtm_beta; tea.
rewrite <- wk_up_ren_on with (F := A).
apply ty_wk; [gen_typing|tea].
Qed.

Lemma redalg_decide_zero_inv : forall A t t₀ u u₀,
  [tDecide A t u ⤳* tZero] ->
  isNf t t₀ -> isNf u u₀ -> eqnf t₀ u₀.
Proof.
intros A t t₀ u u₀ Hdec.
remember (tDecide A t u) as lhs eqn:Hl; remember tZero as rhs eqn:Hr.
revert A t t₀ u u₀ Hl Hr; induction Hdec as [|lhs mid rhs Hred].
+ intros; subst; inversion Hr.
+ intros; subst.
  assert (forall v, [v ⇶* v]) by reflexivity.
  inversion Hred; subst; try congruence.
  - assert (t = t₀) by (now apply isNf_dnf_det); subst.
    assert (u = u₀) by (now apply isNf_dnf_det); subst.
    now apply term_beq_eq.
  - enough (tSucc tZero = tZero) by congruence.
    apply red_whnf; eauto using whnf.
  - edestruct IHHdec; try reflexivity; eauto using dredalg_one_step, isNf_dred_exp.
  - edestruct IHHdec; try reflexivity; eauto using dredalg_one_step, isNf_dred_exp.
Qed.

Definition eqnf_complete {Γ l A A'} (rA : [Γ ||-<l> A ≅ A']) :=
  forall t t₀ u u₀
  (rt : [rA | Γ ||- t ≅ t : A ≅ _])
  (ru : [rA | Γ ||- u ≅ u : A ≅ _]),
  isNf t t₀ -> isNf u u₀ -> eqnf t₀ u₀ -> [rA | Γ ||- t ≅ u : _].

Lemma eqnf_complete_Ne : forall Γ l A A' (neA : [Γ ||-ne A ≅ A']), eqnf_complete (LRne_ l neA).
Proof.
intros * e e₀ e' e'₀ re re' ?? Heq.
cbn in *; destruct re as [v], re' as [w]; cbn in *.
exists v w; tea.
eapply sncmp_convneu; eauto using tmr_wf_r; try now eapply convneu_whne.
+ now eapply isNf_TermRedWf_red.
+ now eapply isNf_TermRedWf_red.
Qed.

Lemma eqnf_complete_Nat : forall Γ l A A' (NA : [Γ ||-Nat A ≅ A']), eqnf_complete (LRNat_ l NA).
Proof.
Admitted.

Lemma eqnf_complete_Empty : forall Γ l A A' (NA : [Γ ||-Empty A ≅ A']), eqnf_complete (LREmpty_ l NA).
Proof.
intros * t t₀ u u₀ rt ru ?? Heq.
destruct rt as [lhs ? [] [] []], ru as [rhs ? [] [] []].
enough [Γ ||-NeNf lhs ≅ rhs : tEmpty].
{ econstructor; [..|tea]; constructor; tea. }
constructor; tea.
eapply sncmp_convneu; eauto; try now eapply convneu_whne.
+ eapply isNf_red; [|tea].
  eapply redtm_sound; tea.
+ eapply isNf_red; [|tea].
  eapply redtm_sound; tea.
Qed.

Lemma eqnf_complete_Π : forall Γ l A A',
  forall ΠA : [Γ ||-Π<l> A ≅ A'],
  (forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]), eqnf_complete (PolyRed.shpRed ΠA ρ h)) ->
  (forall (Δ : context) (a b : term) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ])
    (ha : [PolyRed.shpRed ΠA ρ h | Δ ||- a ≅ b : (ParamRedTy.domL ΠA)⟨ρ⟩ ≅ (ParamRedTy.domR ΠA)⟨ρ⟩]),
  eqnf_complete (PolyRed.posRed ΠA ρ h ha)) ->
  eqnf_complete (LRPi' ΠA).
Proof.
intros * Hdom Hcod t t₀ u u₀ rt ru ?? Heq.
unshelve econstructor.
+ now eapply PiRedTmEq.redL.
+ now eapply PiRedTmEq.redL.
+ destruct rt as [[] []]; cbn in *.
  destruct ru as [[] []]; cbn in *.
  eapply SNC; [..|apply Heq]; eauto using isNf_TermRedWf_red, tmr_wf_r.
+ cbn; intros ? a b **.
  destruct rt as [[wft ? funt] [] ? redl]; cbn in *.
  destruct ru as [[wfu ? funu] [] ? redr]; cbn in *.
  assert [PolyRed.posRed ΠA ρ h hab | Δ ||- tApp wft⟨ρ⟩ a ≅ tApp wft⟨ρ⟩ a : (ParamRedTy.codL ΠA)[a .: ρ >> tRel] ≅ (ParamRedTy.codR ΠA)[b .: ρ >> tRel]].
  { now eapply lreflRedTm. }
  assert (hba : [PolyRed.shpRed ΠA ρ h | Δ ||- b ≅ a : (ParamRedTy.domL ΠA)⟨ρ⟩ ≅ (ParamRedTy.domR ΠA)⟨ρ⟩]) by now symmetry.
  assert (redr0 := redr _ _ _ _ _ hba).
  assert [PolyRed.posRed ΠA ρ h hab | Δ ||- tApp wfu⟨ρ⟩ b ≅ tApp wfu⟨ρ⟩ b : (ParamRedTy.codL ΠA)[a .: ρ >> tRel] ≅ (ParamRedTy.codR ΠA)[b .: ρ >> tRel]].
  { unshelve eapply irrLRConv; [..|eapply ureflRedTm; now symmetry].
    etransitivity; [apply (PolyRed.posRed ΠA ρ h hba)|].
    symmetry; now eapply (PolyRed.posRed ΠA), lreflRedTm. }
  assert (∑ v₀, isNf (tApp wft⟨ρ⟩ a) v₀) as [v₀ Hv] by now eapply hasNf_red.
  assert (∑ w₀, isNf (tApp wfu⟨ρ⟩ b) w₀) as [w₀ Hw] by now eapply hasNf_red.
  assert (∑ a₀, isNf a a₀) as [a₀ Ha] by now eapply hasNf_red.
  assert (∑ b₀, isNf b b₀) as [b₀ Hb] by now eapply hasNf_red.
  unshelve eapply Hcod; [..|tea|tea|]; tea.
  unshelve eapply (eqnf_nfeval_app_compat _ t₀⟨ρ⟩ _ u₀⟨ρ⟩ _ a₀ _ b₀ _ _ _ _ _ _ Hv Hw); eauto.
  - now eapply isNf_wk, isNf_TermRedWf_red.
  - now eapply isNf_wk, isNf_TermRedWf_red.
  - apply eqnf_ren; [apply wk_inj|tea].
  - assert (Htab : [Δ |- a ≅ b : (ParamRedTy.domL ΠA)⟨ρ⟩]) by now escape.
    apply snty_nf in Htab as (r₀&s₀&?&?&?&?&?).
    replace a₀ with r₀ by now eapply isNf_irr.
    replace b₀ with s₀ by now eapply isNf_irr.
    tea.
Qed.

Lemma eqnf_complete_Σ : forall Γ l A A',
  forall ΠA : [Γ ||-Σ< l > A ≅ A'],
  (forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]), eqnf_complete (PolyRed.shpRed ΠA ρ h)) ->
  (forall (Δ : context) (a b : term) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ])
     (ha : [PolyRed.shpRed ΠA ρ h | Δ ||- a ≅ b : (ParamRedTy.domL ΠA)⟨ρ⟩ ≅ (ParamRedTy.domR ΠA)⟨ρ⟩]),
   eqnf_complete (PolyRed.posRed ΠA ρ h ha)) ->
  eqnf_complete (LRSig' ΠA).
Proof.
Admitted.

Lemma red_eqnf_complete_zero : forall Γ A A' (rA : [Γ ||-<zero> A ≅ A']), eqnf_complete rA.
Proof.
intros *.
remember zero as l eqn:Hl; revert Hl.
indLR rA; cbn.
+ intros rA Hl.
  destruct rA; subst l.
  inversion lt.
+ intros; apply eqnf_complete_Ne.
+ intros; apply eqnf_complete_Π; eauto.
+ intros; apply eqnf_complete_Nat.
+ intros; apply eqnf_complete_Empty.
+ intros; apply eqnf_complete_Σ; auto.
+ admit.
Admitted.

Lemma redTy_eqn_complete_zero_ : forall Γ A A' A₀ B B₀
  (rA : [Γ ||-<zero> A ≅ A']) (rB : [Γ ||-<zero> B ≅ B]),
  isNf A A₀ -> isNf B B₀ ->
  eqnf A₀ B₀ -> [Γ ||-<zero> A ≅ B].
Proof.
intros Γ A A' A₀ B B₀ rA.
remember zero as l eqn:Hl; revert A₀ B B₀ Hl.
indLR rA; cbn in *.
+ intros [? Hlt] A₀ B B₀ Hl; subst l.
  inversion Hlt.
+ intros rA A₀ B B₀ Hl rB; subst l; destruct rA.
Admitted.

Lemma red_eqnf_complete_one : forall Γ A A' (rA : [Γ ||-<one> A ≅ A']), eqnf_complete rA.
Proof.
intros *.
remember one as l eqn:Hl; revert Hl.
indLR rA; cbn.
+ admit.
+ intros; apply eqnf_complete_Ne.
+ intros; apply eqnf_complete_Π; eauto.
+ intros; apply eqnf_complete_Nat.
+ intros; apply eqnf_complete_Empty.
+ admit.
+ admit.
Admitted.

Lemma red_eqnf_complete : forall Γ l A A' (rA : [Γ ||-<l> A ≅ A']), eqnf_complete rA.
Proof.
Admitted.

End EquationalCompleteness.
