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

Definition nfeval t {p : ∑ t₀, isNf t t₀} := projT1 p.

Definition isNf_red {Γ l A A' t u} {rA : [Γ ||-<l> A ≅ A']} (p : [rA | Γ ||- t ≅ u : _ ≅ _]) :
  ∑ t₀ : term, isNf t t₀.
Proof.
apply escapeTm in p.
destruct p as (?&?&p).
apply SN.(snty_nf) in p.
destruct p as (?&?&?&?).
now eexists.
Qed.

Lemma dnf_nfeval : forall t p, dnf (@nfeval t p).
Proof.
intros; unfold nfeval; destruct p as [?[]]; now cbn.
Qed.

Lemma dredalg_nfeval : forall t p, [t ⇶* @nfeval t p].
Proof.
intros; unfold nfeval; destruct p as [?[]]; now cbn.
Qed.

Lemma irr_nfeval : forall t p q, @nfeval t p = @nfeval t q.
Proof.
intros; eapply dredalg_det; eauto using dnf_nfeval, dredalg_nfeval.
Qed.

(* Notation deep_eval p := (@nfeval _ (isNf_red p)). *)

Definition deep_eval {Γ l A A' t u} {rA : [Γ ||-<l> A ≅ A']} (p : [rA | Γ ||- t ≅ u : _ ≅ _]) :=
  @nfeval _ (isNf_red p).

Lemma dnf_deep_eval : forall Γ l A A' t u
  (rA : [Γ ||-<l> A ≅ A'])
  (p : [rA | Γ ||- t ≅ u : _ ≅ _]),
  dnf (deep_eval p).
Proof.
intros; apply dnf_nfeval.
Qed.

Lemma dredalg_deep_eval : forall Γ l A A' t u
  (rA : [Γ ||-<l> A ≅ A'])
  (p : [rA | Γ ||- t ≅ u : _ ≅ _]),
  [t ⇶* deep_eval p].
Proof.
intros; apply dredalg_nfeval.
Qed.

Lemma irr_deep_eval : forall Γ l A A' B B' t u v
  (rA : [Γ ||-<l> A ≅ A'])
  (rB : [Γ ||-<l> B ≅ B'])
  (p : [rA | Γ ||- t ≅ u : _ ≅ _])
  (q : [rB | Γ ||- t ≅ v : _ ≅ _]),
  deep_eval p = deep_eval q.
Proof.
intros; apply irr_nfeval.
Qed.

Lemma isNf_dredalg : forall t u,
  [u ⇶* t] -> (∑ t₀, isNf t t₀) -> (∑ t₀, isNf u t₀).
Proof.
intros t u Hr [t₀ []]; exists t₀; split; tea.
now etransitivity.
Qed.

Lemma isNf_wk : forall {Γ Δ} t (ρ : Δ ≤ Γ), (∑ t₀, isNf t t₀) -> (∑ t₀, isNf t⟨ρ⟩ t₀).
Proof.
intros Γ Δ t ρ [t₀ []].
exists t₀⟨ρ⟩; split.
+ apply gcredalg_wk; [apply wk_inj|tea].
+ now apply dnf_ren.
Qed.

Lemma isNf_wk_rev : forall {Γ Δ} t (ρ : Δ ≤ Γ), (∑ t₀, isNf t⟨ρ⟩ t₀) -> (∑ t₀, isNf t t₀).
Proof.
intros Γ Δ t ρ [t₀ []].
assert (∑ u₀, t₀ = u₀⟨ρ⟩) as [u₀]; [|subst].
{ eapply dredalg_ren_adj; eauto using wk_inj. }
exists u₀; split.
+ eapply redalg_ren_inv; eauto using wk_inj.
+ now eapply dnf_ren_rev.
Qed.

Lemma nfeval_dredalg : forall {t u} {p : ∑ t₀, isNf t t₀} (r : [u ⇶* t]),
  @nfeval _ p = @nfeval _ (isNf_dredalg t u r p).
Proof.
intros t u [t₀ []] r; cbn.
unfold nfeval; destruct isNf_dredalg as [u₀ []]; cbn.
symmetry; eapply dredalg_det; tea.
transitivity t; tea.
Qed.

Lemma nfeval_dredalg_fwd : forall {t u} {p : ∑ t₀, isNf t t₀} (r : [t ⇶* u]),
  ∑ q, @nfeval _ p = @nfeval u q.
Proof.
intros.
destruct p as [t₀ []].
unshelve econstructor.
+ exists t₀; split; tea.
  now eapply dred_red_det.
+ reflexivity.
Qed.

Lemma eqnf_nfeval_app_compat : forall f g a b pf pg pa pb pl pr,
  eqnf (@nfeval f pf) (@nfeval g pg) ->
  eqnf (@nfeval a pa) (@nfeval b pb) ->
  eqnf (@nfeval (tApp f a) pl) (@nfeval (tApp g b) pr).
Proof.
intros f g a b [f₀ []] [g₀ []] [a₀ []] [b₀ []] [v₀ []] [w₀ []]; cbn.
intros Heq1 Heq2.
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

Lemma eqnf_nfeval_wk : forall {Γ Δ} t u (ρ : Δ ≤ Γ) pt pu,
  eqnf (@nfeval t (isNf_wk_rev _ ρ pt)) (@nfeval u (isNf_wk_rev _ ρ pu)) -> eqnf (@nfeval t⟨ρ⟩ pt) (@nfeval u⟨ρ⟩ pu).
Proof.
intros ????? [t₀ []] [u₀ []] Heq; cbn in *.
destruct (isNf_wk_rev t) as [r₀ [Hr]]; cbn in *.
destruct (isNf_wk_rev u) as [s₀ [Hs]]; cbn in *.
eapply (gcredalg_wk ρ) in Hr; eauto using wk_inj.
eapply (gcredalg_wk ρ) in Hs; eauto using wk_inj.
assert (t₀ = r₀⟨ρ⟩) by (now eapply dredalg_det; eauto using dnf_ren); subst.
assert (u₀ = s₀⟨ρ⟩) by (now eapply dredalg_det; eauto using dnf_ren); subst.
apply eqnf_ren; eauto using wk_inj.
Qed.

Lemma eqnf_nfeval_irr : forall t u p q r s,
  eqnf (@nfeval t p) (@nfeval u q) -> eqnf (@nfeval t r) (@nfeval u s).
Proof.
intros; now rewrite (irr_nfeval _ r p), (irr_nfeval _ s q).
Qed.

Lemma dredalg_deep_eval_factor : forall Γ l A A' t u v
  (rA : [Γ ||-<l> A ≅ A'])
  (p : [rA | Γ ||- t ≅ u : _ ≅ _]),
  [t ⇶* v] ->
  [v ⇶* deep_eval p].
Proof.
intros.
eapply dred_red_det; eauto using dredalg_deep_eval, dnf_deep_eval.
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

Lemma redalg_decide_zero_inv : forall A t u,
  [tDecide A t u ⤳* tZero] ->
  ∑ (p : ∑ t₀ : term, isNf t t₀) (q : ∑ t₀ : term, isNf u t₀), eqnf (@nfeval t p) (@nfeval u q).
Proof.
intros A t u Hdec.
remember (tDecide A t u) as lhs eqn:Hl; remember tZero as rhs eqn:Hr.
revert A t u Hl Hr; induction Hdec as [|lhs mid rhs Hred].
+ intros; subst; inversion Hr.
+ intros; subst.
  assert (forall v, [v ⇶* v]) by reflexivity.
  inversion Hred; subst; try congruence.
  - unshelve econstructor; [eauto using sigT, isNf|].
    unshelve econstructor; [eauto using sigT, isNf|].
    now cbn; apply term_beq_eq.
  - enough (tSucc tZero = tZero) by congruence.
    apply red_whnf; eauto using whnf.
  - edestruct IHHdec as (p&q&?); try reflexivity.
    assert [t ⇶* t'] by now eapply dredalg_one_step.
    assert (p' : ∑ t₀, isNf t t₀) by now eapply isNf_dredalg.
    unshelve econstructor; [tea|].
    unshelve econstructor; [tea|].
    transitivity (erase (@nfeval t' p)); [|tea].
    destruct p as [t₀ []], p' as [t'₀ []]; cbn.
    assert [t ⇶* t₀] by now transitivity t'.
    f_equal; eauto using dredalg_det.
  - edestruct IHHdec as (p&q&?); try reflexivity.
    assert [u ⇶* u'] by now eapply dredalg_one_step.
    assert (q' : ∑ t₀, isNf u t₀) by now eapply isNf_dredalg.
    unshelve econstructor; [tea|].
    unshelve econstructor; [tea|].
    transitivity (erase (@nfeval u' q)); [tea|].
    destruct q as [u₀ []], q' as [u'₀ []]; cbn.
    assert [u ⇶* u₀] by now transitivity u'.
    f_equal; eauto using dredalg_det.
Qed.

Definition eqnf_complete {Γ l A A'} (rA : [Γ ||-<l> A ≅ A']) :=
  forall t u
  (rt : [rA | Γ ||- t ≅ t : A ≅ _])
  (ru : [rA | Γ ||- u ≅ u : A ≅ _]),
  eqnf (deep_eval rt) (deep_eval ru) -> [rA | Γ ||- t ≅ u : _].

(*
Lemma convtm_exp_l : forall Γ A t u, [Γ |- A] -> [Γ |- A ≅ A] -> [Γ |- u ≅ u : A] -> [Γ |- t :⤳*: u : A] -> [Γ |- t ≅ u : A].
Proof.
intros * ? ? ? [].
eapply convtm_exp; tea.
now apply redtm_refl.
Qed.
*)

Lemma eqnf_complete_Ne : forall Γ l A A' (neA : [Γ ||-ne A ≅ A']), eqnf_complete (LRne_ l neA).
Proof.
intros * e e' re re' Heq.
unfold deep_eval in *.
cbn in *; destruct re as [v], re' as [w]; cbn in *.
exists v w; tea.
eapply sncmp_convneu; eauto using tmr_wf_r; try now eapply convneu_whne.
+ match goal with [ |- context [@nfeval _ ?p] ] => destruct p as [e₀ He] end; cbn.
  split; [|now destruct He].
Admitted.

Lemma eqnf_complete_Nat : forall Γ l A A' (NA : [Γ ||-Nat A ≅ A']), eqnf_complete (LRNat_ l NA).
Proof.
Admitted.

Lemma eqnf_complete_Empty : forall Γ l A A' (NA : [Γ ||-Empty A ≅ A']), eqnf_complete (LREmpty_ l NA).
Proof.
intros * t u rt ru Heq.
unfold deep_eval in *.
destruct rt as [lhs ? [] [] []], ru as [rhs ? [] [] []].
enough [Γ ||-NeNf lhs ≅ rhs : tEmpty].
{ econstructor; [..|tea]; constructor; tea. }
constructor; tea.
eapply sncmp_convneu; eauto; try now eapply convneu_whne.
Admitted.

Lemma eqnf_complete_Π : forall Γ l A A',
  forall ΠA : [Γ ||-Π<l> A ≅ A'],
  (forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]), eqnf_complete (PolyRed.shpRed ΠA ρ h)) ->
  (forall (Δ : context) (a b : term) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ])
    (ha : [PolyRed.shpRed ΠA ρ h | Δ ||- a ≅ b : (ParamRedTy.domL ΠA)⟨ρ⟩ ≅ (ParamRedTy.domR ΠA)⟨ρ⟩]),
  eqnf_complete (PolyRed.posRed ΠA ρ h ha)) ->
  eqnf_complete (LRPi' ΠA).
Proof.
intros * Hdom Hcod t u rt ru Heq.
unfold deep_eval in *.
unshelve econstructor.
+ now eapply PiRedTmEq.redL.
+ now eapply PiRedTmEq.redL.
+ destruct rt as [[] []]; cbn in *.
  destruct ru as [[] []]; cbn in *.
  eapply SNC; [..|apply Heq]; try apply Build_isNf; eauto using tmr_wf_r, dnf_deep_eval.
  - apply dredalg_deep_eval_factor.
    now eapply dred_red, redtm_sound, tmr_wf_red.
  - apply dredalg_deep_eval_factor.
    now eapply dred_red, redtm_sound, tmr_wf_red.
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
  unshelve eapply Hcod; tea.
  unfold deep_eval in *.
  assert (Hab : eqnf (deep_eval hab) (deep_eval hba)).
  { unfold deep_eval.
    assert (Htab : [Δ |- a ≅ b : (ParamRedTy.domL ΠA)⟨ρ⟩]) by now escape.
    apply snty_nf in Htab as (t₀&u₀&p&q&?&?&?).
    replace (nfeval a) with t₀; [replace (nfeval b) with u₀|]; tea.
    + change u₀ with (@nfeval b (existT _ _ q)).
      apply irr_nfeval.
    + change t₀ with (@nfeval a (existT _ _ p)).
      apply irr_nfeval. }
  unfold deep_eval in Hab.
  assert (Hrt : [t ⇶* wft]).
  { now eapply dred_red, redtm_sound, tmr_wf_red. }
  assert (Hru : [u ⇶* wfu]).
  { now eapply dred_red, redtm_sound, tmr_wf_red. }
  match type of Heq with eqnf (@nfeval _ ?p) (@nfeval _ ?q) =>
    assert (Hwft := @nfeval_dredalg_fwd _ _ p Hrt);
    assert (Hwfu := @nfeval_dredalg_fwd _ _ q Hru)
  end.
  destruct Hwft as [pft Hwft], Hwfu as [pfu Hwfu].
  rewrite Hwft, Hwfu in Heq.
  unshelve eapply eqnf_nfeval_app_compat; eauto using isNf_wk.
  eapply eqnf_nfeval_wk; tea.
  now eapply eqnf_nfeval_irr.
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

Lemma redTy_eqn_complete_zero_ : forall Γ A A' B
  (rA : [Γ ||-<zero> A ≅ A']) (rB : [Γ ||-<zero> B ≅ B]) pA pB,
  eqnf (@nfeval A pA) (@nfeval B pB) -> [Γ ||-<zero> A ≅ B].
Proof.
intros Γ A A' B rA.
remember zero as l eqn:Hl; revert B Hl.
indLR rA; cbn in *.
+ intros [? Hlt] B Hl; subst l.
  inversion Hlt.
+ intros rA B Hl rB; subst l; destruct rA.
Admitted.

Lemma red_eqnf_complete_one : forall Γ A A' (rA : [Γ ||-<one> A ≅ A']), eqnf_complete rA.
Proof.
intros *.
remember one as l eqn:Hl; revert Hl.
indLR rA; cbn.
+ intros rA Hl; subst l; intros X Y rX rY Heq; cbn in *; unfold deep_eval in *.
unfold nfeval in Heq.
  destruct rX, rY; cbn in *.
  unshelve econstructor; tea.
  - admit.
  - admit.
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
