From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.Syntax Require Import Confluence Standardisation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Universe Nat Sigma SimpleArr Id.
From LogRel.Validity Require Import Validity Irrelevance Properties.
From LogRel.Validity Require Import Universe Nat SimpleArr.

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
cbn in *; destruct re, re'; cbn in *.
econstructor; tea.
(* eapply sncmp_convneu. *)
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

Section Valid.

Context `{GenericTypingProperties}.
Context {SN : SNTypingProperties ta _ _ _ _ _}.

Lemma DecideRedEvalEq : forall Γ l A A' t u (rΓ : [|- Γ])
  (rNat : [Γ ||-<l> tNat])
  (rA : [Γ ||-<l> A ≅ A']),
  [rA | Γ ||- t ≅ t : A ≅ A'] ->
  [rA | Γ ||- u ≅ u : A ≅ A'] ->
  dnf t -> dnf u ->
  closed0 t -> closed0 u ->
  term_beq (erase t) (erase u) = true ->
  [rNat | Γ ||- tDecide A t u ≅ tZero : tNat].
Proof.
intros * rΓ rNat rA rt ru Ht Hu Hct Hcu Heq.
assert [Γ |- A] by now escape.
eapply redSubstLeftTmEq; tea.
+ unshelve eapply irrLR, zeroRed.
  3: apply natRedTy. all: tea.
+ apply redtm_decide_eval_eq; eauto; try now escape.
Qed.

(*
Lemma DecideRedEvalEq : forall Γ l A A' t u (rΓ : [|- Γ])
  (rNat : [Γ ||-<l> tNat])
  (rA : [Γ ||-<l> A ≅ A']),
  [rA | Γ ||- t ≅ u : A ≅ A'] ->
  closed0 t -> closed0 u ->
  [rNat | Γ ||- tDecide A t u ≅ tZero : tNat].
Proof.
intros * rΓ rNat rA req Hct Hcu.
assert [Γ |- A] by now escape.
assert (Hnf : [Γ |- t ≅ u : A]) by (now escape); apply snty_nf in Hnf.
destruct Hnf as (t₀&u₀&[]&[]&?&?&?).
assert [Γ |- A] by now escape.
assert [Γ |- A'] by now escape.
assert [Γ |- A ≅ A'] by now escape.
assert ([Γ |- tDecide A t u ⤳* tDecide A t₀ u₀ : tNat]) by now eapply redtm_decide.
eapply redSubstLeftTmEq; tea.
assert [Γ |- tDecide A t₀ u₀ ⤳* tZero : tNat].
{ apply redtm_decide_eval_eq; eauto using term_eq_beq, dredalg_closed0.
  + now eapply urefl.
  + now eapply urefl. }
eapply redSubstLeftTmEq; [|tea].
unshelve eapply irrLR, zeroRed.
3: apply natRedTy. all: tea.
Qed.
*)

Lemma DecideRedEvalNeq : forall Γ l A A' t u (rΓ : [|- Γ])
  (rNat : [Γ ||-<l> tNat])
  (rA : [Γ ||-<l> A ≅ A']),
  [rA | Γ ||- t ≅ t : A ≅ A'] ->
  [rA | Γ ||- u ≅ u : A ≅ A'] ->
  dnf t -> dnf u ->
  closed0 t -> closed0 u ->
  negb (term_beq (erase t) (erase u)) = true ->
  [rNat | Γ ||- tDecide A t u ≅ tSucc tZero : tNat].
Proof.
intros * rΓ rNat rA rt ru Ht Hu Hct Hcu Heq.
assert [Γ |- A] by now escape.
eapply redSubstLeftTmEq; tea.
+ unshelve eapply irrLR, succRed, zeroRed.
  3: apply natRedTy. all: tea.
+ apply redtm_decide_eval_neq; eauto; try now escape.
Qed.

Lemma DecideRedEq : forall {Γ l A A' t t' u u'} (rΓ : [|- Γ])
  {rNat : [Γ ||-<l> tNat]}
  {rA : [Γ ||-<l> A ≅ A']},
  [rA | Γ ||- t ≅ t' : A ≅ A'] ->
  [rA | Γ ||- u ≅ u' : A ≅ A'] ->
  [rNat | Γ ||- tDecide A t u ≅ tDecide A' t' u' : tNat].
Proof.
intros * rΓ rNat rA rt ru.
assert (Hnft : [Γ |- t ≅ t' : A]) by (now escape); apply snty_nf in Hnft.
assert (Hnfu : [Γ |- u ≅ u' : A]) by (now escape); apply snty_nf in Hnfu.
destruct Hnft as (t₀&t'₀&[]&[]&?&?&?).
destruct Hnfu as (u₀&u'₀&[]&[]&?&?&?).
assert [Γ |- A] by now escape.
assert [Γ |- A'] by now escape.
assert [Γ |- A ≅ A'] by now escape.
assert ([Γ |- tDecide A t u ⤳* tDecide A t₀ u₀ : tNat]) by now eapply redtm_decide.
assert ([Γ |- tDecide A' t' u' ⤳* tDecide A' t'₀ u'₀ : tNat]) by (eapply redtm_decide; gen_typing).
eapply redSubstTmEq; tea.
remember (is_closedn 0 t₀) as ct eqn:Hct; symmetry in Hct.
assert (Hct' : is_closedn 0 t'₀ = ct).
{ erewrite eqnf_is_closedn; [tea|now apply Symmetric_eqnf]. }
remember (is_closedn 0 u₀) as cu eqn:Hcu; symmetry in Hcu.
assert (Hcu' : is_closedn 0 u'₀ = cu).
{ erewrite eqnf_is_closedn; [tea|now apply Symmetric_eqnf]. }
remember (andb ct cu) as cb eqn:Hcb; symmetry in Hcb; destruct cb.
+ destruct ct; [|cbn in Hcb; congruence].
  destruct cu; [|cbn in Hcb; congruence].
  remember (term_beq (erase t₀) (erase u₀)) as eqb eqn:Heqb; symmetry in Heqb.
  assert ([Γ |- tDecide A t₀ u₀ ⤳* (if eqb then tZero else tSucc tZero) : tNat]).
  { destruct eqb.
    + apply redtm_decide_eval_eq; eauto; now eapply urefl.
    + apply redtm_decide_eval_neq; eauto using ssrbool.negbT; now eapply urefl. }
  assert ([Γ |- tDecide A' t'₀ u'₀ ⤳* (if eqb then tZero else tSucc tZero) : tNat]).
  { replace (erase t₀) with (erase t'₀) in Heqb by now eauto.
    replace (erase u₀) with (erase u'₀) in Heqb by now eauto.
    destruct eqb.
    + apply redtm_decide_eval_eq; eauto.
      - eapply convtm_conv; [|tea].
        now eapply urefl.
      - eapply convtm_conv; [|tea].
        now eapply urefl.
   + apply redtm_decide_eval_neq; eauto.
      - eapply convtm_conv; [|tea].
        now eapply urefl.
      - eapply convtm_conv; [|tea].
        now eapply urefl.
      - now apply ssrbool.negbT. }
  eapply redSubstTmEq; tea.
  destruct eqb.
  - unshelve eapply irrLR, zeroRed.
    3: apply natRedTy. all: tea.
  - unshelve eapply irrLR, succRed, zeroRed.
    3: apply natRedTy. all: tea.
+ eapply reflectLR.
  - apply ty_decide; tea; now eapply urefl.
  - apply ty_decide; tea.
    * eapply convtm_conv; tea; now eapply urefl.
    * eapply convtm_conv; tea; now eapply urefl.
  - apply convneu_decide; tea.
    * etransitivity; [|tea].
      etransitivity; [symmetry; tea|].
      now escape.
    * etransitivity; [|tea].
      etransitivity; [symmetry; tea|].
      now escape.
    * assert (forall b, b = false -> ~ (is_true b)).
      { intros []; congruence. }
      destruct ct, cu; cbn in *; eauto.
    * assert (forall b, b = false -> ~ (is_true b)).
      { intros []; congruence. }
      destruct ct, cu; cbn in *; eauto.
Qed.

Section DecideValid.

  Context {Γ Γ' l} {A A' t t' u u' : term}
    (vΓ : [||-v Γ ≅ Γ'])
    (vNat : [Γ ||-v<l> tNat ≅ tNat | vΓ])
    (vA : [Γ ||-v<l> A ≅ A' | vΓ])
    (vt : [Γ ||-v<l> t ≅ t' : A | vΓ | vA ])
    (vu : [Γ ||-v<l> u ≅ u' : A | vΓ | vA ])
  .

  Lemma DecideCongValid :
    [Γ ||-v<l> tDecide A t u ≅ tDecide A' t' u' : tNat | vΓ | vNat].
  Proof.
    econstructor; intros *; cbn.
    instValid Vσσ'.
    eapply DecideRedEq; tea.
  Qed.

End DecideValid.

Section DecideEvalEqValid.

  Context {Γ Γ' l} {A t u : term}
    (vΓ : [||-v Γ ≅ Γ'])
    (vNat : [Γ ||-v<l> tNat ≅ tNat | vΓ])
    (vA : [Γ ||-v<l> A | vΓ])
    (vt : [Γ ||-v<l> t : A | vΓ | vA ])
    (vu : [Γ ||-v<l> u : A | vΓ | vA ])
  .

  Lemma DecideEvalEqValid :
    dnf t -> dnf u -> closed0 t -> closed0 u ->
    term_beq (erase t) (erase u) = true ->
    [Γ ||-v<l> tDecide A t u ≅ tZero : tNat | vΓ | vNat].
  Proof.
    intros Hnft Hnfu Hct Hcu.
    econstructor; intros *; cbn.
    instValid Vσσ'.
    eapply DecideRedEvalEq; eauto using dnf_closed0_subst, closed0_subst.
    rewrite !erase_is_closed0_subst_id; tea.
  Qed.

  Lemma DecideEvalNeqValid :
    dnf t -> dnf u -> closed0 t -> closed0 u ->
    negb (term_beq (erase t) (erase u)) = true ->
    [Γ ||-v<l> tDecide A t u ≅ tSucc tZero : tNat | vΓ | vNat].
  Proof.
    intros Hnft Hnfu Hct Hcu.
    econstructor; intros *; cbn.
    instValid Vσσ'.
    eapply DecideRedEvalNeq; eauto using dnf_closed0_subst, closed0_subst.
    rewrite !erase_is_closed0_subst_id; tea.
  Qed.

End DecideEvalEqValid.

End Valid.

Section Reflect.

Context `{GenericTypingProperties}.
Context {SN : SNTypingProperties ta _ _ _ _ _}.
Context {SNC : SNCompleteTypingProperties ta _ _ _ _ _ _}.

Lemma DecideZeroRedComplete : forall Γ l A A' t u
  (rΓ : [|- Γ])
  (rNat := natRed (l := l) rΓ)
  (rA : [Γ ||-<l> A ≅ A']),
  [rA | Γ ||- t ≅ t : _] ->
  [rA | Γ ||- u ≅ u : _] ->
  [rNat | Γ ||- tDecide A t u ≅ tZero : tNat] ->
  [rA | Γ ||- t ≅ u : _].
Proof.
intros * rt ru rdec.
unshelve eapply red_eqnf_complete; tea.
unfold deep_eval.
assert (Hr : [tDecide A t u ⤳* tZero]).
{ remember (tDecide A t u) as lhs; remember tZero as rhs.
  cbn in rdec; destruct rdec as [? ? nfl nfr ? ? ? spec]; subst.
  assert (nfr = tZero); [|subst].
  { symmetry; apply red_whnf; [|constructor].
    now eapply redtm_sound, tmr_wf_red. }
  inversion spec; subst; [now eapply redtm_sound, tmr_wf_red|].
  enough (whne tZero) as Hne by inversion Hne.
  eapply convneu_whne; symmetry; now eapply NeNf.conv. }
enough (∑ p q, eqnf (@nfeval t p) (@nfeval u q)) as (p&q&?).
{ now eapply eqnf_nfeval_irr. }
now eapply redalg_decide_zero_inv.
Qed.

Lemma ReflectRedEq : forall Γ l A A' t t' u u' e e' (rΓ : [|- Γ])
  (rA : [Γ ||-<l> A ≅ A'])
  (rId : [Γ ||-<l> tId A t u ≅ tId A' t' u'])
  (rt : [rA | Γ ||- t ≅ t' : A ≅ A'])
  (ru : [rA | Γ ||- u ≅ u' : A ≅ A'])
  (rIdDec : [Γ ||-<l> tId tNat (tDecide A t u) tZero ≅ tId tNat (tDecide A' t' u') tZero] :=
    IdRed (natRed rΓ) (DecideRedEq rΓ rt ru) zeroRed),
  [rIdDec | Γ ||- e ≅ e' : _] ->
  [rId | Γ ||- tReflect A t u e ≅ tReflect A' t' u' e' : tId A t u ≅ tId A' t' u'].
Proof.
intros * re.
clearbody rIdDec.
pose (rIdDec0 := normRedId rIdDec).
assert (re0 : [LRId' rIdDec0 | Γ ||- e ≅ e' : _]) by now eapply irrLR.
cbn in re0; clear re; rename re0 into re.
destruct re as [lhs rhs ??? req]; cbn in *.
assert (rdec : [natRed (l := l) rΓ | Γ ||- tDecide A t u ≅ tDecide A' t' u' : tNat ≅ tNat]) by now eapply DecideRedEq.
assert [Γ |- tDecide A t u ≅ tDecide A' t' u' : tNat] by now escape.
assert [Γ |-[ ta ] t' : A'].
{ eapply ty_conv; now escape. }
assert [Γ |-[ ta ] u' : A'].
{ eapply ty_conv; now escape. }
assert ([Γ |- tReflect A t u e ⤳* tReflect A t u lhs : tId A t u]).
{ eapply redtm_reflect; try now escape.
  now apply tmr_wf_red. }
assert ([Γ |- tReflect A' t' u' e' ⤳* tReflect A' t' u' rhs : tId A' t' u']).
{ eapply redtm_reflect; try now escape.
  eapply redtm_conv; [now apply tmr_wf_red|].
  now escape. }
eapply redSubstTmEq; tea.
destruct req as [X X' x x'|]; cbn in *.
+ assert ([Γ |- tReflect A t u (tRefl X x) ⤳* tRefl A t : tId A t u]).
  { apply redtm_reflect_eval; now escape. }
  assert ([Γ |- tReflect A' t' u' (tRefl X' x') ⤳* tRefl A' t' : tId A' t' u']).
  { apply redtm_reflect_eval; escape; cbn in *; try now idtac.
    transitivity (tDecide A t u); [now symmetry|tea]. }
  eapply redSubstTmEq; tea.
  pose (rId0 := LRId' (normRedId rId)).
  unshelve eapply irrLR; [..|apply rId0|].
  assert [natRed (l := l) rΓ | Γ ||- tDecide A t u ≅ tZero : tNat].
  { etransitivity; eapply irrLR; [|symmetry]; tea. }
  assert [rA | Γ ||- t ≅ u : _].
  { eapply DecideZeroRedComplete; tea.
    + now eapply lreflRedTm.
    + now eapply lreflRedTm. }
  assert [Γ |- tId A t u ≅ tId A t t].
  { escape; apply convty_Id.
    + now eapply lrefl.
    + now eapply lrefl.
    + now symmetry. }
  cbn; econstructor.
  - apply redtmwf_refl; cbn.
    eapply ty_conv; [|now symmetry].
    eapply ty_refl; now escape.
  - apply redtmwf_refl; cbn.
    eapply ty_conv; [|now symmetry].
    eapply ty_conv; [eapply ty_refl; now escape|].
    assert [Γ |- t' ≅ t : A'].
    { eapply convtm_conv; [symmetry|]; now escape. }
    eapply convty_Id; [symmetry; now escape|..]; tea.
  - cbn.
    eapply convtm_conv; [|now symmetry].
    apply convtm_refl; now escape.
  - constructor; cbn; try now escape.
    * eapply lrefl; now escape.
    * eapply lreflRedTm, irrLR; tea.
    * eapply irrLR; tea.
    * symmetry; eapply irrLR; tea.
    * etransitivity; [symmetry|]; eapply irrLR; tea.
+ escape.
  eapply reflectLR.
  - apply ty_reflect; tea.
    now eapply tmr_wf_r.
  - eapply ty_conv; [|now symmetry].
    apply ty_reflect; tea.
    assert [Γ |- tId tNat (tDecide A t u) tZero ≅ tId tNat (tDecide A' t' u') tZero].
    { apply convty_Id; gen_typing. }
    eapply ty_conv; [|tea].
    now eapply tmr_wf_r.
  - apply convneu_reflect; tea.
    now eapply NeNf.conv.
Qed.

End Reflect.

(* Section Valid. *)

(*

Lemma embRedTy {Γ l l' A} (h : l << l') (rA : [Γ ||-< l > A]) : [Γ ||-< l' > A].
Proof.
destruct rA as [pack].
unshelve econstructor.
- exact pack.
- eapply Induction.LR_embedding; tea.
Defined.

Lemma embRedTyOne {Γ l A} (rA : [Γ ||-< l > A]) : [Γ ||-< one > A].
Proof.
destruct l; tea; now eapply (embRedTy Oi).
Defined.

Lemma ElURed {Γ A} (rU : [Γ ||-<one> U]) (rA : [rU | Γ ||- A : U]) : [Γ ||-<one> A].
Proof.
assert (rΓ : [|- Γ]) by now eapply wfc_wft, escape.
unshelve eapply irrLR in rA; [| |apply (LRU_ (redUOneCtx rΓ))|].
destruct rA.
apply (embRedTyOne relEq).
Qed.

Lemma simple_AppRedEq {Γ t t' u u' F G l} (RF : [Γ ||-< l > F]) (RG : [Γ ||-< l > G]) (RΠ := SimpleArr.ArrRedTy RF RG) :
  [RΠ | Γ ||- t ≅ t' : arr F G] -> [RF | Γ ||- u ≅ u' : F] -> [RG | Γ ||- tApp t u ≅ tApp t' u' : G].
Proof.
intros.
eapply SimpleArr.simple_appcongTerm; tea.
Qed.

Lemma dnf_closed_qNat_aux : forall Γ (rΓ : [|- Γ]),
  (forall t t', [Γ ||-Nat t ≅ t' :Nat] -> forall u, [t ⇶* u] -> dnf u -> closed0 u -> ∑ n, u = qNat n × [Γ ||-Nat t ≅ qNat n :Nat]) ×
  (forall t t', NatPropEq Γ t t' -> forall u, [t ⇶* u] -> dnf u -> closed0 u -> ∑ n, u = qNat n × [Γ ||-Nat t ≅ qNat n :Nat]).
Proof.
intros; apply NatRedEqInduction.
+ intros * [? Hr] Heq ? ? IH u Hr' Hnf Hc.
  unshelve epose (Hu := IH u _ _ _); tea.
  { eapply dred_red_det; tea.
    now eapply dred_red, redtm_sound. }
  destruct Hu as (n&Hu&Hn).
  exists n; split; tea.
  change [LRNat_ one (natRedTy rΓ) | Γ ||- t ≅ qNat n : tNat].
  etransitivity; [|tea].
  eapply redSubstTmEq; [|tea|now apply redtmwf_refl].
  eapply lrefl; eassumption.
+ intros * Hr Hnf Hc.
  apply dred_dnf in Hr; [subst|eauto using dnf].
  exists 0; split; [reflexivity|].
  unshelve eapply (zeroRed (l := zero) (NN := natRedTy rΓ)).
+ intros * Hn IH u Hr Hnf Hc.
  destruct (redalg_succ_adj _ _ Hr) as [m ->].
  apply redalg_succ_inv in Hr.
  inversion Hnf; subst; [|match goal with H : dne _ |- _ => inversion H end].
  destruct (IH _ Hr) as (v&Hv&Hm); tea; subst.
  exists (S v); split; [reflexivity|].
  change [LRNat_ one (natRedTy rΓ) | Γ ||- tSucc n ≅ qNat (S v) : tNat].
  change [LRNat_ one (natRedTy rΓ) | Γ ||- n ≅ qNat v : tNat] in Hm.
  cbn; eapply succRed; tea.
+ intros n n' [? ? Hne] * Hr Hnf Hc; exfalso.
  apply convneu_whne in Hne.
  eapply dredalg_whne in Hr; [|tea].
  now eapply closed0_whne.
Qed.

Lemma dnf_closed_qNat : forall Γ l t u (rNat : [Γ ||-<l> tNat]),
  [Γ ||-<l> t : tNat | rNat] -> [t ⇶* u] -> dnf u -> closed0 u -> ∑ n, (u = qNat n) × [rNat | Γ ||- t ≅ qNat n : tNat].
Proof.
intros * rt Hr Hnf **.
assert (rΓ : [|- Γ]) by now eapply wfc_wft, escape.
unshelve eapply irrLR in rt; [| |now apply (natRed (l := l))|].
eapply dnf_closed_qNat_aux in rt; tea.
destruct rt as (n&?&?).
exists n; split; tea.
unshelve eapply irrLR; [| |apply natRed|]; [..|tea]; tea.
Qed.

Lemma dnf_closed_qNatRedEq : forall Γ l t n (rNat : [Γ ||-<l> tNat]),
  [Γ ||-<l> t : tNat | rNat] -> [t ⇶* qNat n] -> [rNat | Γ ||- t ≅ qNat n : tNat].
Proof.
intros * rt Hred.
eapply dnf_closed_qNat in rt; [|tea|apply dnf_qNat|apply closedn_qNat].
destruct rt as (m&Hm&Hrt).
apply qNat_inj in Hm; now subst m.
Qed.

Lemma dred_qNatRedEq {Γ l t n} (rNat : [Γ ||-<l> tNat]) :
  [rNat | Γ ||- t ≅ qNat n : tNat] -> [t ⇶* qNat n].
Proof.
intros rEq.
assert (rΓ : [|- Γ]) by now eapply wfc_wft, escape.
unshelve eapply irrLR in rEq; [| |now apply (natRed (l := l))|].
enough (IH :
(forall (t u : term), NatRedTmEq Γ t u -> forall n, u = qNat n -> [t ⇶* qNat n])
× (forall (t u : term), NatPropEq Γ t u -> forall n, u = qNat n -> [t ⇶* qNat n])
).
{ destruct IH as [IH _]; eapply IH; [|reflexivity]; apply rEq. }
apply NatRedEqInduction.
+ intros ???????? IH **; subst.
  etransitivity.
  - now eapply dred_red, redtm_sound, tmr_wf_red.
  - apply IH; symmetry; apply red_whnf;
    eauto using dnf_whnf, dnf_qNat, tmr_wf_red, redtm_sound.
    now eapply redtm_sound, tmr_wf_red.
+ intros []; cbn; [reflexivity|congruence].
+ intros ??? IH []; cbn; try congruence.
  intros [=]; now apply dredalg_succ, IH.
+ intros ?? [] m' **; subst; exfalso.
  assert (Hne : whne (qNat m')) by now (eapply convneu_whne; symmetry).
  destruct m'; inversion Hne.
Qed.

Lemma red_qNat_inj {Γ l m n} (rNat : [Γ ||-<l> tNat]) :
  [rNat | Γ ||- qNat m ≅ qNat n : tNat] -> m = n.
Proof.
intros rEq.
apply qNat_inj, dred_dnf; [|apply dnf_qNat].
now apply dred_qNatRedEq in rEq.
Qed.

Lemma red_redtm_exp {Γ l A t t' u u'} (rA : [Γ ||-<l> A]) :
  [Γ |- t' ⤳* t : A] -> [Γ |- u' ⤳* u : A] ->
  [Γ ||-<l> t ≅ u : A | rA] -> [Γ ||-<l> t' ≅ u' : A | rA].
Proof.
intros.
now eapply redSubstTmEq.
Qed.

Lemma neuTermEqRed {Γ l A t t' n n'} (RA : [Γ ||-<l> A]) :
  [Γ |- t ⤳* n : A] ->
  [Γ |- t' ⤳* n' : A] ->
  [Γ |- n : A] -> [Γ |- n' : A] -> [Γ |- n ~ n' : A] -> [Γ ||-<l> t ≅ t' : A | RA].
Proof.
intros Ht Ht' Hn Hn' Hnn'.
eapply red_redtm_exp; tea.
apply neNfTermEq; now constructor.
Qed.

Lemma simple_betaRed {Γ l A B t a} (rΓ : [|- Γ])
  (rA : [Γ ||-<l> A]) (rB : [Γ ||-<l> B]) :
  [Γ,, A |- t : B⟨@wk1 Γ A⟩] ->
  [Γ |- a : A] ->
  [rB | Γ ||- t[a..] : B] ->
  [rB | Γ ||- tApp (tLambda A t) a ≅ t[a..] : B].
Proof.
intros rt ra rta.
eapply redSubstLeftTmEq; [tea|].
replace B with B⟨↑⟩[a..] by now bsimpl.
eapply redtm_beta.
+ now eapply escape.
+ now rewrite wk1_ren_on in rt.
+ tea.
Qed.

Lemma simple_lambdaRed {Γ l A A' B B' t t'}
  (rA : [Γ ||-<l> A ≅ A']) (rB : [Γ ||-<l> B ≅ B']) (rΠ : [Γ ||-<l> arr A B ≅ arr A' B'])
  (rte : forall Δ (ρ : Δ ≤ Γ) (rΔ : [|- Δ]) a b,
    [ (wkLR _ _ _ rA).(wkRed) ρ rΔ | Δ ||- a ≅ b : A⟨ρ⟩ ≅ A'⟨ρ⟩] -> [ (wkLR _ _ _ rB).(wkRed) ρ rΔ | Δ ||- t[a .: ρ >> tRel] ≅ t'[b .: ρ >> tRel] : B⟨ρ⟩ ≅ B'⟨ρ⟩]) :
  [rΠ | Γ ||- tLambda A t ≅ tLambda A' t' : arr A B ≅ arr A' B'].
Proof.
unshelve eapply irrLR; [..|eapply LRPi', normRedΠ, rΠ|].
escape.
assert [ |- Γ,, A] by gen_typing.
assert [ |- Γ,, A'] by gen_typing.
assert [Γ,, A |- t : B⟨↑⟩].
{ rewrite <- (@var0_wk1_id Γ A t).
  rewrite <- (@wk1_ren_on Γ A B).
  unshelve (eapply escapeTm; symmetry; apply rte, var0); tea.
  symmetry; apply wk1_ren_on. }
assert [Γ,, A' |- t' : B'⟨↑⟩].
{ rewrite <- (@var0_wk1_id Γ A' t').
  rewrite <- (@wk1_ren_on Γ A' B').
  unshelve eapply escapeTm; [..|eapply wkLR; [symmetry; eapply rB|]|]; [shelve|gen_typing|].
  cbn; unshelve eapply irrLRSym, rte, var0conv; tea.
  rewrite <- (wk1_ren_on Γ A' A').
  apply convty_wk; [|now symmetry]; tea. }
assert [Γ |- tLambda A t : arr A B].
{ now apply ty_lam. }
assert [Γ |- tLambda A' t' : arr A B].
{ eapply ty_conv; [eapply ty_lam|]; [..|symmetry; now eapply escapeEq]; tea. }
cbn; unshelve econstructor.
+ econstructor; cbn.
  - now eapply redtmwf_refl.
  - constructor; cbn; tea; [now eapply lrefl|].
    intros.
    unshelve (eapply irrLREq; [|etransitivity]; [|eapply rte|]).
    * tea.
    * shelve.
    * symmetry; apply shift_subst_scons.
    * eapply lreflRedTm, irrLR, ha.
    * unshelve eapply irrLRSym, symLR, rte; tea.
      unshelve eapply irrLRSym, symLR, ha.
+ econstructor; cbn.
  - now eapply redtmwf_refl.
  - constructor; cbn; tea.
    intros.
    unshelve (eapply irrLREq; [|etransitivity]; [|symmetry; eapply rte|]).
    * tea.
    * shelve.
    * symmetry; apply shift_subst_scons.
    * eapply lreflRedTm, irrLR, ha.
    * unshelve (eapply irrLRSym, symLR; symmetry; eapply rte); tea.
      unshelve eapply irrLR, ha.
+ cbn; eapply lambda_cong; tea.
  - rewrite <- (@wk1_ren_on Γ A B); apply wft_wk; gen_typing.
  - rewrite <- (@var0_wk1_id Γ A t').
    rewrite <- (@wk1_ren_on Γ A B).
    unshelve (eapply escapeTm; apply rte, var0); tea.
    symmetry; apply @wk1_ren_on.
  - rewrite <- !(@wk1_ren_on Γ A).
    apply convty_wk; gen_typing.
  - rewrite <- !(@wk1_ren_on Γ A').
    apply convty_wk; gen_typing.
  - rewrite <- (@wk1_ren_on Γ A).
    rewrite <- (@var0_wk1_id Γ A t'), <- (@var0_wk1_id Γ A t).
    unshelve eapply escapeTm, rte, var0; tea.
    symmetry; apply @wk1_ren_on.
+ cbn; intros.
  eapply irrLREq; [symmetry; apply shift_subst_scons|].
  eapply redSubstTmEq.
  - now unshelve eapply rte, irrLR, hab.
  - rewrite (subst1_ren_wk_up (A := A⟨ρ⟩)).
    rewrite wk_up_ren_on, <- (@shift_subst1 B⟨ρ⟩ a).
    eapply redtm_beta.
    * eapply wft_wk; tea.
    * unfold ren1 at 3; unfold Ren1_well_wk.
      rewrite shift_upRen.
      rewrite <- !(@wk_up_ren_on _ _ ρ A).
      eapply ty_wk; [eapply wfc_cons|]; tea.
      eapply wft_wk; tea.
    * now escape.
  - rewrite (subst1_ren_wk_up (A := A'⟨ρ⟩)).
    rewrite wk_up_ren_on, <- (@shift_subst1 B'⟨ρ⟩ b).
    eapply redtm_beta.
    * eapply wft_wk; tea.
    * unfold ren1 at 3; unfold Ren1_well_wk.
      rewrite shift_upRen.
      rewrite <- !(@wk_up_ren_on _ _ ρ A').
      eapply ty_wk; [eapply wfc_cons|]; tea.
      eapply wft_wk; tea.
    * unshelve apply symLR in hab; now escape.
Qed.

Lemma tAndURedEq {Γ l A A' B B'} (rΓ : [|- Γ])
  (rU : [Γ ||-<l> U])
  (rAA' : [Γ ||-<l> A ≅ A' : U | rU]) (rBB' : [Γ ||-<l> B ≅ B' : U | rU]) : [Γ ||-<l> tAnd A B ≅ tAnd A' B' : U | rU].
Proof.
unshelve eapply sigmaURed; [exact zero|tea|].
intros * hab.
replace B⟨↑⟩[a .: ρ >> tRel] with B⟨ρ⟩.
2:{ bsimpl; now apply rinst_inst_term. }
replace B'⟨↑⟩[b .: ρ >> tRel] with B'⟨ρ⟩.
2:{ bsimpl; now apply rinst_inst_term. }
now apply wkRedTm.
Qed.

Lemma simple_tPairRed {Γ l A A' B B' p p' q q'}
  (rA : [Γ ||-<l> A ≅ A']) (rB : [Γ ||-<l> B ≅ B'])
  (rΣ : [Γ ||-<l> tAnd A B ≅ tAnd A' B'])
  (rp : [rA | Γ ||- p ≅ p' : A ≅ A']) (rq : [rB | Γ ||- q ≅ q' : B ≅ B']) : [rΣ | Γ ||- tPair A B⟨↑⟩ p q ≅ tPair A' B'⟨↑⟩ p' q' : tAnd A B ≅ tAnd A' B'].
Proof.
unshelve (eapply irrLR, pairCongRed; [tea|]).
+ eapply rΣ.
+ now rewrite !shift_subst1.
+ eapply irrLREq.
  { symmetry; eapply shift_subst1. }
  eapply rq.
Qed.

Lemma tIsNilRedEq {Γ l t t'} (rΓ : [|- Γ])
  (rNat := natRed rΓ)
  (rU : [Γ ||-<one> U])
  (rt : [Γ ||-<l> t ≅ t' : tNat | rNat]) :
  [rU | Γ ||- tIsNil t ≅ tIsNil t' : U].
Proof.
unshelve eapply IdCongRedU.
+ now apply natRed.
+ now unshelve eapply irrLR, natTermRed.
+ eapply irrLR, rt.
+ now eapply zeroRed.
Qed.

Lemma tIsValRedEq {Γ l t t' v v'} (rΓ : [|- Γ])
  (rNat := natRed rΓ)
  (rU : [Γ ||-<one> U])
  (rt : [Γ ||-<l> t ≅ t' : tNat | rNat])
  (rv : [Γ ||-<l> v ≅ v' : tNat | rNat]) :
  [rU | Γ ||- tIsVal t v ≅ tIsVal t' v' : U].
Proof.
pose (rU' := LRU_ (redUOneCtx rΓ)).
unshelve eapply irrLR; [| |apply rU'|].
clear rU; rename rU' into rU.
assert [rU | Γ ||- tNat : U].
{ now unshelve eapply irrLR, natTermRed. }
assert (rS : [rNat | Γ ||- tSucc v ≅ tSucc v' : tNat]).
{ apply succRed.
  eapply rv. }
unshelve eapply IdCongRedU; tea.
+ now apply natRed.
+ eapply rt.
+ eapply rS.
Qed.

Lemma redtm_shift_app {Γ t u} :
  [Γ |- t : arr tNat tNat] ->
  [Γ |- u : tNat] ->
  [Γ |- tApp (tShift t) u ⤳* tApp t (tSucc u) : tNat].
Proof.
intros; unfold tShift.
assert [|- Γ] by gen_typing.
assert [|- Γ,, tNat] by gen_typing.
assert [Γ,, tNat |- tNat] by now apply wft_nat.
replace (tApp t (tSucc u)) with (tApp t⟨↑⟩ (tSucc (tRel 0)))[u..] by now bsimpl.
change tNat with tNat[u..].
eapply redtm_beta.
+ now apply wft_nat.
+ cbn; apply (ty_simple_app (A := tNat)); tea.
  - rewrite <- (@wk1_ren_on Γ tNat t).
    change (arr tNat tNat) with (arr tNat tNat)⟨@wk1 Γ tNat⟩.
    now apply ty_wk.
  - apply ty_succ, ty_var; tea.
    change tNat with tNat⟨↑⟩ at 2; constructor.
+ tea.
Qed.

Lemma tShift_ren : forall t ρ, (tShift t)⟨ρ⟩ = tShift (t⟨ρ⟩).
Proof.
intros; unfold tShift; cbn; do 2 f_equal.
now bsimpl.
Qed.

Lemma tShiftRedEq {Γ l t t'} (rPNat : [Γ ||-<l> tPNat])
  (rt : [rPNat | Γ ||- t ≅ t' : tPNat]) : [rPNat | Γ ||- tShift t ≅ tShift t' : tPNat].
Proof.
escape.
assert (rΓ : [|- Γ]) by gen_typing.
assert [Γ ||-< l > tNat].
{ now apply natRed. }
unshelve eapply simple_lambdaRed; tea.
intros * hab; cbn.
unshelve eapply simple_appcongTerm, succRed, irrLR, hab.
+ exact (tNat⟨ρ⟩).
+ rewrite wk_arr; eapply wkLR; tea.
+ now eapply natRedTy.
+ rewrite !shift_subst_scons.
  eapply irrLREq; [|eapply (wkLR _ _ _ _).(wkRedTm)]; [eapply arr_ren1|].
  Unshelve.
  - unshelve eapply irrLR, rt.
  - shelve.
  - apply rPNat.
  - tea.
Qed.

Lemma tEvalZeroRedEq {Γ l t v} (rΓ : [|- Γ])
  (rNat := natRed rΓ) (rNatNat := SimpleArr.ArrRedTy rNat rNat)
  (rU : [Γ ||-<one> U])
  (rt : [Γ ||-<l> t : tPNat | rNatNat])
  (rv : [Γ ||-<l> v : tNat | rNat]) :
  [Γ ||-<one> tEval t tZero v ≅ tIsVal (tApp t tZero) v : U | rU].
Proof.
eapply redSubstLeftTmEq.
+ eapply tIsValRedEq; [..|tea].
  eapply simple_appcongTerm.
  - tea.
  - unshelve eapply zeroRed; tea.
    now apply natRedTy.
+ apply redtm_evalBranchZero.
  - unshelve eapply escapeTerm, rt.
  - unshelve eapply escapeTerm, rv.
Qed.

Lemma tEvalSuccRedEq {Γ l t k v} (rΓ : [|- Γ])
  (rNat := natRed rΓ) (rNatNat := SimpleArr.ArrRedTy rNat rNat)
  (rU : [Γ ||-<one> U])
  (rt : [Γ ||-<l> t : tPNat | rNatNat])
  (rk : [Γ ||-<l> k : tNat | rNat])
  (rv : [Γ ||-<l> v : tNat | rNat])
  (rrec : [rU | Γ ||- tEval (tShift t) k v : U]) :
  [Γ ||-<one> tEval t (tSucc k) v ≅ tAnd (tIsNil (tApp t tZero)) (tEval (tShift t) k v) : U | rU].
Proof.
eapply redSubstLeftTmEq.
+ eapply tAndURedEq; tea.
  eapply tIsNilRedEq, simple_appcongTerm; [tea|].
  unshelve eapply zeroRed; now apply natRedTy.
  Unshelve. tea.
+ apply redtm_evalBranchSucc.
  - now eapply escapeTerm.
  - now eapply escapeTerm.
  - now eapply escapeTerm.
Qed.

Lemma tEvalNeuRedEq {Γ t t' k k' v v'} (rΓ : [|- Γ])
  (rU : [Γ ||-<one> U])
  (rt : [Γ |- t : tPNat])
  (rt' : [Γ |- t' : tPNat])
  (rtt' : [Γ |- t ≅ t' : tPNat])
  (rk : [Γ |- k : tNat])
  (rk' : [Γ |- k' : tNat])
  (rkk' : [Γ |- k ~ k' : tNat])
  (rv : [Γ |- v : tNat])
  (rv' : [Γ |- v' : tNat])
  (rvv' : [Γ |- v ≅ v' : tNat]) :
  [Γ ||-<one> tEval t k v ≅ tEval t' k' v' : U | rU].
Proof.
apply reflectLR.
+ apply ty_eval; tea.
+ apply ty_eval; tea.
+ apply tEval_cong; tea.
Qed.

Lemma tEvalURedEq {Γ l t t' k k' v v'} (rΓ : [|- Γ])
  (rNat : [Γ ||-<l> tNat]) (rPNat : [Γ ||-<l> tPNat])
  (rU : [Γ ||-<one> U])
  (rt : [Γ ||-<l> t ≅ t' : tPNat | rPNat])
  (rk : [Γ ||-<l> k ≅ k' : tNat | rNat])
  (rv : [Γ ||-<l> v ≅ v' : tNat | rNat]) :
  [Γ ||-<one> tEval t k v ≅ tEval t' k' v' : U | rU].
Proof.
assert (Rnat : [Γ ||-Nat tNat ≅ tNat]).
{ unshelve constructor; now apply redtywf_refl, wft_nat. }
pose (rNat' := LRNat_ l Rnat).
unshelve eapply irrLR in rk;  [..|exact rNat'| ].
unshelve eapply irrLR in rv;  [..|exact rNat'| ].
clear rNat; rename rNat' into rNat.
assert [rNat | Γ ||- v : tNat] by now eapply LRTmEqRed_l.
assert [rNat | Γ ||- v' : tNat] by now eapply LRTmEqRed_r.
revert t t' rt.
assert (Hk : [Γ |- k : tNat]) by now eapply escapeTerm, LRTmEqRed_l.
assert (Hk' : [Γ |- k' : tNat]) by now eapply escapeTerm, LRTmEqRed_r.
revert Hk Hk'.
pattern k, k'.
match goal with |- ?F _ _ => pose (P := F) end.
revert k k' rk.
cut ((forall k k', NatRedTmEq Γ k k' -> P k k') × (forall k k', NatPropEq Γ k k' -> P k k')).
{ intros [IH]; apply IH. }
apply NatRedEqInduction; unfold P.
+ intros k k' * [] [] ?? IH ?? t t' rt.
  eapply red_redtm_exp; [| |now apply IH]; apply redtm_evalArg; tea.
  - now eapply escapeTerm, LRTmEqRed_l.
  - now eapply escapeTerm.
  - now eapply escapeTerm, LRTmEqRed_r.
  - now eapply escapeTerm.
+ intros ?? t t' rt.
  assert [rPNat | Γ ||- t : tPNat] by now eapply LRTmEqRed_l.
  assert [rPNat | Γ ||- t' : tPNat] by now eapply LRTmEqRed_r.
  eapply red_redtm_exp.
  - eapply redtm_evalBranchZero; eapply escapeTerm; tea.
  - eapply redtm_evalBranchZero; eapply escapeTerm; tea.
  - eapply tIsValRedEq; tea.
    eapply SimpleArr.simple_appcongTerm; tea.
    now unshelve eapply zeroRed.
    Unshelve. tea.
+ intros k k' rk IH ?? t t' rt.
  assert [rPNat | Γ ||- t : tPNat] by now eapply LRTmEqRed_l.
  assert [rPNat | Γ ||- t' : tPNat] by now eapply LRTmEqRed_r.
  assert [Γ |- k : tNat].
  { destruct rk; now eapply redtm_ty_src, tmr_wf_red. }
  assert [Γ |- k' : tNat].
  { destruct rk; now eapply redtm_ty_src, tmr_wf_red. }
  eapply red_redtm_exp.
  - eapply redtm_evalBranchSucc; try now unshelve eapply escapeTerm.
    * tea.
    * now eapply escapeTerm.
  - eapply redtm_evalBranchSucc; try now unshelve eapply escapeTerm.
    * tea.
    * now eapply escapeTerm.
  - apply tAndURedEq; tea.
    * unshelve eapply tIsNilRedEq; [shelve|tea|].
      assert [rNat | Γ ||- tZero : tNat] by now apply zeroRed.
      eapply SimpleArr.simple_appcongTerm; tea.
    * apply IH; tea.
      now apply tShiftRedEq.
+ intros k k' rk ?? t t' rt.
  assert [rPNat | Γ ||- t : tPNat] by now eapply LRTmEqRed_l.
  assert [rPNat | Γ ||- t' : tPNat] by now eapply LRTmEqRed_r.
  apply tEvalNeuRedEq; first [assumption|now eapply escapeTerm|now eapply escapeEqTerm|idtac].
  apply rk.
Qed.

Lemma tEvalURed {Γ l t k v} (rΓ : [|- Γ])
  (rNat := natRed rΓ) (rNatNat := SimpleArr.ArrRedTy rNat rNat)
  (rU : [Γ ||-<one> U])
  (rt : [Γ ||-<l> t : tPNat | rNatNat])
  (rk : [Γ ||-<l> k : tNat | rNat])
  (rv : [Γ ||-<l> v : tNat | rNat]) :
  [Γ ||-<one> tEval t k v : U | rU].
Proof.
now eapply tEvalURedEq.
Qed.

Lemma tEvalRed {Γ l t k v} (rΓ : [|- Γ])
  (rNat := natRed rΓ) (rNatNat := SimpleArr.ArrRedTy rNat rNat)
  (rt : [Γ ||-<l> t : tPNat | rNatNat])
  (rk : [Γ ||-<l> k : tNat | rNat])
  (rv : [Γ ||-<l> v : tNat | rNat]) :
  [Γ ||-<one> tEval t k v].
Proof.
unshelve epose (rU := LRU_ (redUOneCtx _)); [|tea|].
enough (rEval : [rU | Γ ||- tEval t k v : U]).
{ destruct rEval; apply (embRedTyOne relEq). }
eapply tEvalURed; tea.
Qed.

Lemma qEvalTyURed {Γ} (rU : [Γ ||-< one > U]) k v: [rU | Γ ||- qEvalTy k v : U].
Proof.
assert (rΓ : [|- Γ]).
{ now eapply wfc_wft, escape. }
induction k; simpl.
+ unshelve eapply tIsValRedEq; [shelve|..].
  - tea.
  - unshelve eapply (succRed (l := one)), qNatRedEq.
  - eapply qNatRedEq.
+ eapply tAndURedEq; [tea| |].
  - now eapply tIsNilRedEq, zeroRed.
  - tea.
Unshelve. all: first [apply one|tea].
Qed.

Lemma qEvalTyRed {Γ} (rΓ : [|- Γ]) k v : [Γ ||-<one> qEvalTy k v].
Proof.
unshelve epose (rU := LRU_ (redUOneCtx _)); [|tea|].
enough (rEval : [rU | Γ ||- qEvalTy k v : U]).
{ destruct rEval; apply (embRedTyOne relEq). }
eapply qEvalTyURed; tea.
Qed.

Lemma qEvalTmRed {Γ k v} (rΓ : [|- Γ]) : [qEvalTyRed rΓ k v | Γ ||- qEvalTm k v : qEvalTy k v].
Proof.
induction k; cbn.
+ unshelve eapply Id.reflCongRed.
  - now eapply natRed.
  - apply succRed, qNatRedEq.
+ assert (Hrw : qEvalTy (S k) v = tAnd (tId tNat tZero tZero) (qEvalTy k v)) by reflexivity.
  assert [Γ ||-<one> tId tNat tZero tZero].
  { unshelve (eapply IdRed; eapply zeroRed); now eapply natRedTy. }
  assert [Γ ||-< one > tAnd (tId tNat tZero tZero) (qEvalTy k v)].
  { unshelve eapply sigmaRed; [tea|].
    intros. rewrite !qEvalTy_ren, !qEvalTy_subst.
    now eapply qEvalTyRed. }
  pose (rNat := natRed (l := one) rΓ).
  eapply irrLREq; [symmetry; apply Hrw|].
  rewrite <- (qEvalTy_ren k v ↑).
  eapply simple_tPairRed.
  - unshelve eapply reflCongRed, zeroRed; now eapply natRedTy.
  - eapply IHk.
Unshelve. all: tea.
Qed.

Lemma tShiftAppRedEq {Γ l t n} {rΓ : [|- Γ]}
  (rNat := natRed (l := l) rΓ) (rPNat := SimpleArr.ArrRedTy rNat rNat) :
  [rPNat | Γ ||- t : tPNat] -> [rNat | Γ ||- n : tNat] ->
  [rNat | Γ ||- tApp (tShift t) n ≅ tApp t (tSucc n) : tNat].
Proof.
intros rt rn.
eapply redSubstLeftTmEq; [|apply redtm_shift_app].
+ eapply simple_appcongTerm; [tea|].
  now eapply succRed.
  Unshelve. now apply natRedTy.
+ now eapply escapeTerm.
+ now eapply escapeTerm.
Qed.

Lemma qEvalTyRedEq {Γ t k v} (rΓ : [|- Γ]) (rU : [Γ ||-<one> U])
  (rNat := natRed (l := one) rΓ) (rPNat := SimpleArr.ArrRedTy rNat rNat) :
  [rPNat | Γ ||- t : tPNat] ->
  (forall k', k' < k -> [rNat | Γ ||- tApp t (qNat k') ≅ tZero : tNat]) ->
  [rNat | Γ ||- tApp t (qNat k) ≅ tSucc (qNat v) : tNat] ->
  [rU | _ ||- tEval t (qNat k) (qNat v) ≅ qEvalTy k v : U ].
Proof.
revert t.
induction k; cbn [qNat qEvalTy].
+ intros t Ht Hlt Hk.
  etransitivity; [eapply tEvalZeroRedEq|].
  - tea.
  - apply qNatRedEq.
  - eapply tIsValRedEq.
    * apply Hk.
    * apply qNatRedEq.
+ intros t Ht Hlt Hk.
  assert [rNat | Γ ||- qNat k : tNat] by apply qNatRedEq.
  assert [rNat | Γ ||- qNat v : tNat] by apply qNatRedEq.
  assert [rPNat | Γ ||- tShift t : tPNat] by now apply tShiftRedEq.
  assert [rU | Γ ||- tEval (tShift t) (qNat k) (qNat v) : U] by now eapply tEvalURed; tea.
  etransitivity; [eapply tEvalSuccRedEq|]; tea.
  apply tAndURedEq; tea.
  - unshelve eapply tIsNilRedEq; [exact one|tea|].
    apply (Hlt 0); Lia.lia.
  - apply IHk; tea.
    * intros k' Hk'.
      assert [rNat | Γ ||- qNat k' : tNat] by apply qNatRedEq.
      etransitivity; [eapply tShiftAppRedEq|]; tea.
      apply (Hlt (S k')); Lia.lia.
    * etransitivity; [eapply tShiftAppRedEq|]; tea. 
Qed.

End Utils.

Section StepRed.

Context `{GenericTypingProperties}.
Context {SN : SNTypingProperties ta _ _ _ _ _}.

Lemma StepClosed0RedEq : forall Γ l t u k v (rΓ : [|- Γ]) (rNat := natRed rΓ),
  [Γ ||-<l> run : arr tNat (arr tNat tPNat) | SimpleArr.ArrRedTy rNat (SimpleArr.ArrRedTy rNat (SimpleArr.ArrRedTy rNat rNat))] ->
  dnf t -> [Γ |- t ≅ t : arr tNat tNat] -> closed0 t -> EvalStep Γ t u k v ->
  [rNat | Γ ||- tStep t (qNat u) ≅ qNat k : tNat].
Proof.
intros.
eapply redSubstLeftTmEq.
+ eapply qNatRedEq.
+ eapply redtm_evalstep; tea.
  now eapply escapeTerm.
Qed.

Lemma erase_qNat : forall n, erase (qNat n) = qNat n.
Proof.
induction n; cbn; now f_equal.
Qed.

Lemma eqnf_qRun {t t' u k} : eqnf t t' -> qRun t u k = qRun t' u k.
Proof.
intros Heq; unfold qRun.
now rewrite Heq.
Qed.

Lemma unannot_qRun {t t' u k} : unannot t = unannot t' -> qRun t u k = qRun t' u k.
Proof.
intros Heq; unfold qRun.
now rewrite !erase_unannot_etared, Heq.
Qed.

Lemma qRun_subst {t u k σ} : closed0 t -> (qRun t u k)[σ] = qRun t[σ] u k.
Proof.
intros Ht.
rewrite (@unannot_qRun t[σ] t); [|now eapply unannot_closed0_subst].
unfold qRun; cbn; rewrite !qNat_subst.
now rewrite run_subst.
Qed.

Lemma eqnf_EvalStep {Γ t t' u k v} : eqnf t t' -> EvalStep Γ t u k v -> EvalStep Γ t' u k v.
Proof.
intros Heq [Hevl Hnil Hval]; split.
+ now rewrite <- Heq.
+ intros; erewrite <- eqnf_qRun; eauto.
+ erewrite <- eqnf_qRun; eauto.
Qed.

Lemma dredalg_eval_min {deep t r} : @RedClosureAlg deep t r -> dnf r ->
  ∑ k : nat, (forall k', k' < k -> eval deep t k' = None) × eval deep t k = Some r.
Proof.
intros Hred Hnf.
assert (Heval0 : ∑ k, eval deep t k = Some r).
{ destruct deep; [apply dredalg_eval|apply redalg_eval]; eauto using dnf_whnf. }
pose (f k := match eval deep t k with None => false | Some _ => true end).
destruct Heval0 as [k0 Hk0].
destruct (minimize f k0) as (k&Hk&Hlt); unfold f in *; clear f.
+ rewrite Hk0; reflexivity.
+ exists k; split.
  - intros k' Hk'; specialize (Hlt k' Hk').
    destruct (eval deep t k'); congruence.
  - remember (eval deep t k) as w eqn:Hw; symmetry in Hw.
    destruct w; [|congruence].
    destruct (PeanoNat.Nat.le_ge_cases k k0).
    * eapply eval_mon in Hw; [|tea]; congruence.
    * eapply eval_mon in Hk0; [|tea]; congruence.
Qed.

Axiom run_spec_None : forall t u k,
  eval true (tApp t (qNat u)) k = None ->
  [tApp (tApp (tApp run (qNat (quote t))) (qNat u)) (qNat k) ⇶* tZero].

Axiom run_spec_Some : forall t u k v,
  eval true (tApp t (qNat u)) k = Some (qNat v) ->
  [tApp (tApp (tApp run (qNat (quote t))) (qNat u)) (qNat k) ⇶* tSucc (qNat v)].

Lemma reify_EvalStep {Γ l t n v} (rNat : [Γ ||-<l> tNat]) :
  (forall k, [rNat | Γ ||- qRun t n k : tNat]) ->
  [tApp t (qNat n) ⇶* qNat v] ->
  ∑ k, EvalStep Γ t n k v.
Proof.
intros * Hrun Hred.
assert (Hred' : [tApp (erase t) (qNat n) ⇶* qNat v]).
{ apply dred_erase_qNat_compat in Hred; cbn in Hred.
  now rewrite erase_qNat in Hred. }

assert (Heval0 := Hred'); apply dredalg_eval in Heval0; [|apply dnf_qNat].
assert (Heval : ∑ k,
  (forall k', k' < k -> (eval true (tApp (erase t) (qNat n)) k' = None)) ×
  (eval true (tApp (erase t) (qNat n)) k = Some (qNat v))).
{ apply dredalg_eval_min; eauto using dnf_qNat. }
destruct Heval as (k&Hnil&Heval).
exists k; split.
+ exists (S k).
  now apply murec_intro.
+ intros k' Hk'.
  specialize (Hnil k' Hk').
  apply run_spec_None in Hnil.
  now eapply escapeEqTerm, dnf_closed_qNatRedEq with (n := 0).
+ apply run_spec_Some in Heval.
  now eapply escapeEqTerm, dnf_closed_qNatRedEq with (n := (S v)).
Qed.

Lemma StepRedEq : forall Γ l t t' u u' (rΓ : [|- Γ]) (rNat := natRed rΓ) (rNatNat := SimpleArr.ArrRedTy rNat rNat),
  [Γ ||-<l> t ≅ t' : arr tNat tNat | rNatNat ] ->
  [Γ ||-<l> u ≅ u' : tNat | rNat ] ->
  [Γ ||-<l> run : arr tNat (arr tNat tPNat) | SimpleArr.ArrRedTy rNat (SimpleArr.ArrRedTy rNat rNatNat)] ->
  [Γ ||-<l> tStep t u ≅ tStep t' u' : tNat | rNat ].
Proof.
intros * rtt' ruu' rrun.
assert (rt : [Γ ||-<l> t : arr tNat tNat | rNatNat ]) by now eapply LRTmEqRed_l.
assert (rt' : [Γ ||-<l> t' : arr tNat tNat | rNatNat ]) by now eapply LRTmEqRed_r.
assert (ru : [Γ ||-<l> u : tNat | rNat ]) by now eapply LRTmEqRed_l.
assert (ru' : [Γ ||-<l> u' : tNat | rNat ]) by now eapply LRTmEqRed_r.
assert [Γ |- run : arr tNat (arr tNat tPNat)] by now eapply escapeTerm.
assert (Hnft := rtt'); apply escapeEqTerm, snty_nf in Hnft.
assert (Hnfu := ruu'); apply escapeEqTerm, snty_nf in Hnfu.
destruct Hnft as (t₀&t'₀&[]&[]&?&?&?).
destruct Hnfu as (u₀&u'₀&[]&[]&?&?&?).
remember (is_closedn 0 t₀) as ct eqn:Hct; symmetry in Hct.
assert (Hct' : is_closedn 0 t'₀ = ct).
{ erewrite eqnf_is_closedn; [tea|now apply Symmetric_eqnf]. }
remember (is_closedn 0 u₀) as cu eqn:Hcu; symmetry in Hcu.
assert (Hcu' : is_closedn 0 u'₀ = cu).
{ erewrite eqnf_is_closedn; [tea|now apply Symmetric_eqnf]. }
remember (andb ct cu) as cb eqn:Hcb; symmetry in Hcb; destruct cb.
+ destruct ct; [|cbn in Hcb; congruence].
  destruct cu; [|cbn in Hcb; congruence].
  clear Hcb.

  assert (∑ n₀, u₀ = qNat n₀ ×  [rNat | Γ ||- u ≅ qNat n₀ : tNat]) as (n₀&?&?) by now eapply dnf_closed_qNat.
  assert (∑ n'₀, u'₀ = qNat n'₀ ×  [rNat | Γ ||- u' ≅ qNat n'₀ : tNat]) as (n'₀&?&?) by now eapply dnf_closed_qNat.
  subst.
  assert (n₀ = n'₀); [|subst n'₀].
  { eapply red_qNat_inj; etransitivity; [etransitivity|]; [now symmetry| |tea]; tea. }

  assert (rvv' : [rNat | Γ ||- tApp t (qNat n₀) ≅ tApp t' (qNat n₀) : tNat]).
  { unshelve eapply (simple_appcongTerm (F := tNat)), qNatRedEq; tea. }

  assert (Hnfv := rvv'); apply escapeEqTerm, snty_nf in Hnfv.
  destruct Hnfv as (v₀&v'₀&[]&[]&?&?&?).

  assert (rv : [rNat | Γ ||- tApp t (qNat n₀) : tNat]) by now eapply LRTmEqRed_l.
  assert (rv' : [rNat | Γ ||- tApp t' (qNat n₀) : tNat]) by now eapply LRTmEqRed_r.


  assert (∑ m₀, v₀ = qNat m₀ ×  [rNat | Γ ||- tApp t (qNat n₀) ≅ qNat m₀ : tNat]) as (m₀&?&?).
  { eapply dnf_closed_qNat; tea.
    eapply (dred_tApp_qNat_closed0 t t₀ n₀); eauto. }
  assert (∑ m₀, v'₀ = qNat m₀ ×  [rNat | Γ ||- tApp t' (qNat n₀) ≅ qNat m₀ : tNat]) as (m'₀&?&?).
  { eapply dnf_closed_qNat; tea.
    eapply (dred_tApp_qNat_closed0 t' t'₀ n₀); eauto. }
  subst.

  subst.
  let H := match goal with H : eqnf (qNat _) (qNat _) |- _ => H end in
  unfold eqnf in H; rewrite !erase_qNat in H; apply qNat_inj in H; subst m'₀.

  assert (forall k : nat, [rNat | Γ ||- qRun t₀ n₀ k : tNat]).
  { intros k; unfold qRun.
    unshelve eapply simple_appcongTerm, qNatRedEq; tea.
    assert (rT : [Γ ||-< l > arr tNat (arr tNat tNat)]) by now apply SimpleArr.ArrRedTy.
    unshelve eapply simple_appcongTerm, qNatRedEq; tea.
    unshelve eapply simple_appcongTerm, qNatRedEq; tea.
  }

  assert (∑ k, EvalStep Γ t₀ n₀ k m₀) as [k Hk].
  { eapply reify_EvalStep; [tea|].
    now eapply dred_tApp_qNat_compat. }

  eapply red_redtm_exp; try eapply redtm_step; tea.
  eapply red_redtm_exp; try eapply redtm_evalstep; tea.
  - now eapply urefl.
  - now eapply urefl.
  - eapply eqnf_EvalStep; tea.
  - apply qNatRedEq.
+ eapply neuTermEqRed.
  - now eapply redtm_step.
  - now eapply redtm_step.
  - apply ty_step; tea; now eapply urefl.
  - apply ty_step; tea; now eapply urefl.
  - eapply convneu_step; tea.
    * etransitivity; [now symmetry|].
      transitivity t'; [now eapply escapeEqTerm|tea].
    * etransitivity; [now symmetry|].
      transitivity u'; [now eapply escapeEqTerm|tea].
    * now symmetry.
    * now symmetry.
    * rewrite Hct, Hcu; destruct ct, cu; compute; now eauto.
    * rewrite Hct', Hcu'; destruct ct, cu; compute; now eauto.
Qed.

Lemma StepRed : forall Γ l t u (rΓ : [|- Γ]) (rNat := natRed rΓ) (rNatNat := SimpleArr.ArrRedTy rNat rNat),
  [Γ ||-<l> t : arr tNat tNat | rNatNat ] ->
  [Γ ||-<l> u : tNat | rNat ] ->
  [Γ ||-<l> run : arr tNat (arr tNat tPNat) | SimpleArr.ArrRedTy rNat (SimpleArr.ArrRedTy rNat rNatNat)] ->
  [Γ ||-<l> tStep t u : tNat | rNat ].
Proof.
intros.
now apply StepRedEq.
Qed.

Lemma reify_red_EvalStep {Γ l t u k v v'} (rNat : [Γ ||-<l> tNat]) :
  (forall k' : nat, k' < k -> [rNat | Γ ||- qRun t u k' ≅ tZero : tNat]) ->
  [rNat | Γ ||- qRun t u k ≅ tSucc (qNat v) : tNat] ->
  [tApp t (qNat u) ⇶* qNat v'] ->
  EvalStep Γ t u k v.
Proof.
intros rnil rval Hred.
split.
+ assert (Hered := Hred).
  apply dred_erase_qNat_compat in Hered; cbn in Hered.
  rewrite erase_qNat in Hered.
  assert (pnil : forall k', k' < k -> [qRun t u k' ⇶* tZero]).
  { intros; now eapply (dred_qNatRedEq (n := 0)). }
  assert (pval : [qRun t u k ⇶* tSucc (qNat v)]).
  { intros; now eapply (dred_qNatRedEq (n := (S v))). }
  clear rNat rnil rval.
  apply dredalg_eval_min in Hered as (k₀&Hnil&Hval); [|apply dnf_qNat].
  assert (Henil : forall k', k' < k₀ -> [qRun t u k' ⇶* tZero]).
  { intros; now apply run_spec_None, Hnil. }
  assert (Heval : [qRun t u k₀ ⇶* tSucc (qNat v')]) by now apply run_spec_Some.
  assert (k = k₀); [|subst k₀].
  { destruct (PeanoNat.Nat.lt_trichotomy k k₀) as [|[|]]; [|now tea|]; exfalso.
    + unshelve epose (Henil k _); tea.
      assert (tZero = tSucc (qNat v)); [|congruence].
      eapply dredalg_det; tea; eauto using dnf, dnf_qNat.
    + unshelve epose (pnil k₀ _); tea.
      assert (tZero = tSucc (qNat v')); [|congruence].
      eapply dredalg_det; eauto using dnf, dnf_qNat. }
  assert (tSucc (qNat v) = tSucc (qNat v')) by now eapply dredalg_det; eauto using dnf, dnf_qNat.
  assert (v = v'); [apply qNat_inj; congruence|subst v'].
  exists (S k); apply murec_intro; tea.
+ intros; now eapply escapeEqTerm.
+ now eapply escapeEqTerm.
Qed.

Lemma reify_Red_EvalStep {Γ l t t₀ u k v} (rNat : [Γ ||-<l> tNat]) :
  [t ⇶* t₀] -> dnf t₀ -> closed0 t₀ ->
  (forall k' : nat, k' < k -> [rNat | Γ ||- qRun t u k' ≅ tZero : tNat]) ->
  [rNat | Γ ||- qRun t u k ≅ tSucc (qNat v) : tNat] ->
  [SimpleArr.ArrRedTy rNat rNat | Γ ||- t : tPNat] ->
  EvalStep Γ t u k v.
Proof.
intros.
assert (rv : [rNat | Γ ||- tApp t (qNat u) : tNat]).
{ unshelve eapply simple_appcongTerm, qNatRedEq; tea. }
assert (Hnfv := rv); apply nf_eval in Hnfv.
destruct Hnfv as (v₀&Hred&?&?).
assert (∑ m₀, v₀ = qNat m₀ ×  [rNat | Γ ||- tApp t (qNat u) ≅ qNat m₀ : tNat]) as (m₀&?&?); [|subst v₀].
{ eapply dnf_closed_qNat; tea.
  eapply (dred_tApp_qNat_closed0 t t₀ u); eauto. }
now eapply reify_red_EvalStep.
Qed.

Lemma StepEvalRedEq : forall Γ l t t₀ u k v (rNat : [Γ ||-<l> tNat]) (rNatNat := SimpleArr.ArrRedTy rNat rNat),
  [Γ |- t ≅ t₀ : tPNat] -> [t ⇶* t₀] -> dnf t₀ -> closed0 t₀ -> eqnf t t₀ ->
  [Γ ||-<l> t : arr tNat tNat | rNatNat ] ->
  (forall k', k' < k -> [rNat | Γ ||- qRun t u k' ≅ tZero : tNat]) ->
  [rNat | Γ ||- qRun t u k ≅ tSucc (qNat v) : tNat] ->
  [Γ ||-<l> run : arr tNat (arr tNat tPNat) | SimpleArr.ArrRedTy rNat (SimpleArr.ArrRedTy rNat rNatNat)] ->
  [rNat | Γ ||- tStep t (qNat u) ≅ qNat k : tNat].
Proof.
intros * Ht Hr Hnf Hc Hannot rt rnil rval rrun.
assert (rΓ : [|- Γ]) by now eapply wfc_wft, escape.
eapply redSubstLeftTmEq; [eapply qNatRedEq|].
transitivity (tStep t₀ (qNat u)).
+ apply redtm_step; eauto using convtm_qNat, dnf_qNat.
  - unshelve eapply escapeEqTerm, qNatRedEq; tea.
  - unshelve eapply escapeTerm, rrun.
  - reflexivity.
+ assert (EvalStep Γ t u k v).
  { unshelve eapply reify_Red_EvalStep; tea. }
  assert (EvalStep Γ t₀ u k v) by now eapply eqnf_EvalStep.
  eapply redtm_evalstep; tea.
  - now eapply urefl.
  - now eapply escapeTerm.
Qed.

End StepRed.

Section ReflectRed.

Context `{GenericTypingProperties}.
Context {SN : SNTypingProperties ta _ _ _ _ _}.

Lemma TotalURedEq {Γ l t t' u u'} (rΓ : [|- Γ]) (rU : [Γ ||-<one> U]) (rNat := natRed rΓ) (rNatNat := SimpleArr.ArrRedTy rNat rNat) :
  [Γ ||-<l> t ≅ t' : arr tNat tNat | rNatNat ] ->
  [Γ ||-<l> u ≅ u' : tNat | rNat ] ->
  [Γ ||-<l> run : arr tNat (arr tNat tPNat) | SimpleArr.ArrRedTy rNat (SimpleArr.ArrRedTy rNat rNatNat)] ->
  [rU | Γ ||- tTotal t u ≅ tTotal t' u' : U].
Proof.
intros rt ru rrun.
unfold tTotal.
assert (rNN : [Γ ||-< l > arr tNat (arr tNat tNat)]) by now apply SimpleArr.ArrRedTy.
assert (rNNN : [Γ ||-< l > arr tNat (arr tNat (arr tNat tNat))]) by now apply SimpleArr.ArrRedTy.
assert [rNat | Γ ||- u : tNat] by now eapply LRTmEqRed_l.
assert [rNat | Γ ||- u' : tNat] by now eapply LRTmEqRed_r.
unshelve eapply tEvalURedEq; tea.
+ unshelve eapply simple_appcongTerm, ru; tea.
  unshelve (eapply simple_appcongTerm; tea); tea.
  apply QuoteRedEq.
  now eapply escapeEqTerm.
+ now eapply StepRedEq.
+ unshelve eapply simple_appcongTerm, ru; tea.
Qed.

Lemma TotalURed {Γ l t u} (rΓ : [|- Γ]) (rU : [Γ ||-<one> U]) (rNat := natRed rΓ) (rNatNat := SimpleArr.ArrRedTy rNat rNat) :
  [Γ ||-<l> t : arr tNat tNat | rNatNat ] ->
  [Γ ||-<l> u : tNat | rNat ] ->
  [Γ ||-<l> run : arr tNat (arr tNat tPNat) | SimpleArr.ArrRedTy rNat (SimpleArr.ArrRedTy rNat rNatNat)] ->
  [rU | Γ ||- tTotal t u : U].
Proof.
apply TotalURedEq.
Qed.

Lemma TotalRed {Γ l t u} (rΓ : [|- Γ]) (rNat := natRed rΓ) (rNatNat := SimpleArr.ArrRedTy rNat rNat) :
  [Γ ||-<l> t : arr tNat tNat | rNatNat ] ->
  [Γ ||-<l> u : tNat | rNat ] ->
  [Γ ||-<l> run : arr tNat (arr tNat tPNat) | SimpleArr.ArrRedTy rNat (SimpleArr.ArrRedTy rNat rNatNat)] ->
  [Γ ||-<one> tTotal t u].
Proof.
intros.
now eapply ElURed, TotalURed.
Unshelve.
now eapply LRU_, redUOne.
Qed.

Fixpoint nShift (n : nat) t := match n with
| 0 => t
| S n => tShift (nShift n t)
end.

Lemma nShiftRed {Γ l n t} (rNatNat : [Γ ||-<l> tPNat]) :
  [rNatNat | Γ ||- t : tPNat] ->
  [rNatNat | Γ ||- nShift n t : tPNat].
Proof.
revert t; induction n; intros t rt; cbn; tea.
now apply tShiftRedEq.
Qed.

Lemma nShiftAppRedEq {Γ l n m t} (rNat : [Γ ||-<l> tNat]) (rNatNat := SimpleArr.ArrRedTy rNat rNat) :
  [rNatNat | Γ ||- t : tPNat] ->
  [rNat | Γ ||- tApp (nShift n t) (qNat m) ≅ tApp t (qNat (n + m)) : tNat].
Proof.
intros rt.
assert (rΓ : [|- Γ]) by now eapply wfc_wft, escape.
unshelve eapply irrLR; [..|apply (natRed (l := l))|]; tea.
revert m t rt.
induction n; cbn [nShift plus]; intros.
+ unshelve eapply simple_appcongTerm, qNatRedEq; tea.
+ etransitivity; [eapply tShiftAppRedEq|].
  - eapply nShiftRed.
    unshelve eapply irrLR, rt.
  - now apply qNatRedEq.
  - cbn [qNat].
    assert (Hr := IHn (S m) t rt).
    now replace (n + S m) with (S (n + m)) in Hr by Lia.lia.
Qed.

Lemma qEvalTyEvalStepRedEq {Γ l t n k v} (rΓ : [|- Γ]) (rU : [Γ ||-<one> U]) (rNat := natRed rΓ) (rNatNat := SimpleArr.ArrRedTy rNat rNat)
  (f := (tApp (tApp run (qNat (quote (erase t)))) (qNat n))) :
  [Γ ||-<l> f : tPNat | rNatNat] ->
  EvalStep Γ t n k v ->
  [rU | Γ ||- tEval f (qNat k) (qNat v) ≅ qEvalTy k v : U].
Proof.
intros rrun.
change f with (nShift 0 f).
change (EvalStep Γ t n k v) with (EvalStep Γ t n (0 + k) v).
generalize 0 as acc.
induction k; intros acc Hstep.
+ etransitivity; [unshelve eapply (tEvalZeroRedEq (l := l))|]; tea.
  - now apply nShiftRed.
  - apply qNatRedEq.
  - unshelve eapply tIsValRedEq; eauto using qNatRedEq.
    etransitivity; [eapply (nShiftAppRedEq (m := 0))|]; tea.
    eapply dnf_closed_qNatRedEq with (n := S v); [now unshelve eauto using simple_appcongTerm, qNatRedEq|].
    destruct Hstep as [[k₀ Hk] _ _].
    apply murec_elim_Some in Hk.
    now apply run_spec_Some.
+ cbn [qNat].
  etransitivity; [unshelve eapply (tEvalSuccRedEq (l := l))|]; eauto using qNatRedEq.
  - now apply nShiftRed.
  - unshelve eapply tEvalURed; unshelve eauto using qNatRedEq.
    now unshelve apply tShiftRedEq, nShiftRed.
  - cbn [qEvalTy]; apply tAndURedEq; tea.
    { unshelve eapply tIsNilRedEq; tea.
      etransitivity; [eapply (nShiftAppRedEq (m := 0))|]; tea.
      eapply dnf_closed_qNatRedEq with (n := 0); [now unshelve eauto using simple_appcongTerm, qNatRedEq|].
      destruct Hstep as [[k₀ Hk] _ _].
      apply (murec_elim_None (k' := (acc + 0))) in Hk; [|Lia.lia].
      now apply run_spec_None.
    }
    { apply (IHk (S acc)).
      now replace (S acc + k) with (acc + S k) by Lia.lia. }
Qed.

Lemma ReflectRedEq : forall Γ l t t' u u' (rΓ : [|- Γ]) (rNat := natRed rΓ) (rNatNat := SimpleArr.ArrRedTy rNat rNat)
  (rTotal : [Γ ||-<l> tTotal t u]),
  [Γ ||-<l> t ≅ t' : arr tNat tNat | rNatNat ] ->
  [Γ ||-<l> u ≅ u' : tNat | rNat ] ->
  [Γ ||-<l> run : arr tNat (arr tNat tPNat) | SimpleArr.ArrRedTy rNat (SimpleArr.ArrRedTy rNat rNatNat)] ->
  [Γ ||-<l> tReflect t u ≅ tReflect t' u' : tTotal t u | rTotal ].
Proof.
intros * rtt' ruu' rrun.
assert (rt : [Γ ||-<l> t : arr tNat tNat | rNatNat ]) by now eapply LRTmEqRed_l.
assert (rt' : [Γ ||-<l> t' : arr tNat tNat | rNatNat ]) by now eapply LRTmEqRed_r.
assert (ru : [Γ ||-<l> u : tNat | rNat ]) by now eapply LRTmEqRed_l.
assert (ru' : [Γ ||-<l> u' : tNat | rNat ]) by now eapply LRTmEqRed_r.
assert (rU : [Γ ||-<one> U]) by now apply LRU_, redUOneCtx.
assert [Γ |- run : arr tNat (arr tNat (arr tNat tNat))] by now eapply escapeTerm.
assert [Γ |- tTotal t u ≅ tTotal t' u' : U].
{ now unshelve eapply escapeEqTerm, TotalURedEq. }
assert (Hnft := rtt'); apply escapeEqTerm, snty_nf in Hnft.
assert (Hnfu := ruu'); apply escapeEqTerm, snty_nf in Hnfu.
destruct Hnft as (t₀&t'₀&[]&[]&?&?&?).
destruct Hnfu as (u₀&u'₀&[]&[]&?&?&?).
remember (is_closedn 0 t₀) as ct eqn:Hct; symmetry in Hct.
assert (Hct' : is_closedn 0 t'₀ = ct).
{ erewrite eqnf_is_closedn; [tea|now apply Symmetric_eqnf]. }
remember (is_closedn 0 u₀) as cu eqn:Hcu; symmetry in Hcu.
assert (Hcu' : is_closedn 0 u'₀ = cu).
{ erewrite eqnf_is_closedn; [tea|now apply Symmetric_eqnf]. }
remember (andb ct cu) as cb eqn:Hcb; symmetry in Hcb; destruct cb.
+ destruct ct; [|cbn in Hcb; congruence].
  destruct cu; [|cbn in Hcb; congruence].
  clear Hcb.

  assert (∑ n₀, u₀ = qNat n₀ ×  [rNat | Γ ||- u ≅ qNat n₀ : tNat]) as (n₀&?&?) by now eapply dnf_closed_qNat.
  assert (∑ n'₀, u'₀ = qNat n'₀ ×  [rNat | Γ ||- u' ≅ qNat n'₀ : tNat]) as (n'₀&?&?) by now eapply dnf_closed_qNat.
  subst.
  assert (n₀ = n'₀); [|subst n'₀].
  { eapply red_qNat_inj, transLR, transLR; [now symmetry| |tea]; tea. }

  assert (rvv' : [rNat | Γ ||- tApp t (qNat n₀) ≅ tApp t' (qNat n₀) : tNat]).
  { unshelve eapply simple_appcongTerm, qNatRedEq; tea. }

  assert (Hnfv := rvv'); apply escapeEqTerm, snty_nf in Hnfv.
  destruct Hnfv as (v₀&v'₀&[]&[]&?&?&?).

  assert (rv : [rNat | Γ ||- tApp t (qNat n₀) : tNat]) by now eapply LRTmEqRed_l.
  assert (rv' : [rNat | Γ ||- tApp t' (qNat n₀) : tNat]) by now eapply LRTmEqRed_r.


  assert (∑ m₀, v₀ = qNat m₀ ×  [rNat | Γ ||- tApp t (qNat n₀) ≅ qNat m₀ : tNat]) as (m₀&?&?).
  { eapply dnf_closed_qNat; tea.
    eapply (dred_tApp_qNat_closed0 t t₀ n₀); eauto. }
  assert (∑ m₀, v'₀ = qNat m₀ ×  [rNat | Γ ||- tApp t' (qNat n₀) ≅ qNat m₀ : tNat]) as (m'₀&?&?).
  { eapply dnf_closed_qNat; tea.
    eapply (dred_tApp_qNat_closed0 t' t'₀ n₀); eauto. }
  subst.

  subst.
  let H := match goal with H : eqnf (qNat _) (qNat _) |- _ => H end in
  unfold eqnf in H; rewrite !erase_qNat in H; apply qNat_inj in H; subst m'₀.

  assert (forall k : nat, [rNat | Γ ||- qRun t₀ n₀ k : tNat]).
  { intros k; unfold qRun.
    unshelve eapply simple_appcongTerm, qNatRedEq; tea.
    assert (rT : [Γ ||-< l > arr tNat (arr tNat tNat)]) by now apply SimpleArr.ArrRedTy.
    unshelve eapply simple_appcongTerm, qNatRedEq; tea.
    unshelve eapply simple_appcongTerm, qNatRedEq; tea.
  }

  assert (∑ k, EvalStep Γ t₀ n₀ k m₀) as [k Hk].
  { eapply reify_EvalStep; [tea|].
    now eapply dred_tApp_qNat_compat. }

  assert [rNat | Γ ||- tQuote t ≅ qNat (quote (erase t₀)) : tNat].
  { eapply redSubstLeftTmEq; [now eapply qNatRedEq|].
    transitivity (tQuote t₀).
    - now eapply redtm_quote.
    - eapply redtm_evalquote; tea; now eapply urefl. }

  assert [rNat | Γ ||- tStep t u ≅ qNat k : tNat].
  { eapply redSubstLeftTmEq; [now eapply qNatRedEq|].
    transitivity (tStep t₀ (qNat n₀)).
    - now eapply redtm_step.
    - eapply redtm_evalstep; tea; now eapply urefl. }

  assert [rNat | Γ ||- tApp t u ≅ qNat m₀ : tNat].
  { transitivity (tApp t (qNat n₀)); tea.
    eapply simple_appcongTerm; tea. }

  assert [rNatNat | Γ ||- tApp (tApp run (tQuote t)) u ≅
    tApp (tApp run (qNat (quote (erase t₀)))) (qNat n₀) : tPNat].
  { eapply simple_appcongTerm; [|tea].
    eapply simple_appcongTerm; tea.
    Unshelve. now apply ArrRedTy. }

  assert [rU | Γ ||- tTotal t u ≅ qEvalTy k m₀ : U].
  { unfold tTotal; etransitivity.
    + eapply tEvalURedEq; tea.
    + eapply qEvalTyEvalStepRedEq; [|tea].
      now eapply LRTmEqRed_r. }

  assert [Γ |- tTotal t u ≅ tTotal t (qNat n₀)].
  { unshelve eapply convty_term, escapeEqTerm; [|exact rU|].
    eapply TotalURedEq; [tea|tea|tea]. }

  assert [Γ |- tTotal t' u' ≅ tTotal t' (qNat n₀)].
  { unshelve eapply convty_term, escapeEqTerm; [|exact rU|].
    eapply TotalURedEq; [tea|tea|tea]. }

  eapply (red_redtm_exp (t := qEvalTm k m₀) (u := qEvalTm k m₀)).
  - etransitivity; [now eapply redtm_reflect|].
    eapply redtm_conv; [|now symmetry].
    now eapply redtm_evalreflect.
  - eapply redtm_conv; [|symmetry; now apply convty_term].
    etransitivity; [now eapply redtm_reflect|].
    eapply redtm_conv; [|now symmetry].
    eapply redtm_evalreflect; tea.
    now eapply eqnf_EvalStep.
  - unshelve (eapply irrLRConv; [eapply UnivEq; symmetry; tea|]); [shelve|..].
    * eapply UnivEq; now symmetry.
    * now unshelve eapply irrLR, qEvalTmRed.
+ eapply neuTermEqRed.
  - eapply redtm_reflect; tea.
    all: now eapply escapeTerm.
  - eapply redtm_conv; [eapply redtm_reflect|]; tea.
    symmetry; now apply convty_term.
  - apply ty_reflect; first [now symmetry|now eapply escapeTerm].
  - apply ty_reflect; [..|now eapply escapeTerm].
    * symmetry; transitivity t'; [now eapply escapeEqTerm|tea].
    * symmetry; transitivity u'; [now eapply escapeEqTerm|tea].
  - eapply convneu_reflect; tea.
    * etransitivity; [now symmetry|].
      transitivity t'; [now eapply escapeEqTerm|tea].
    * etransitivity; [now symmetry|].
      transitivity u'; [now eapply escapeEqTerm|tea].
    * now symmetry.
    * now symmetry.
    * rewrite Hct, Hcu; destruct ct, cu; compute; now eauto.
    * rewrite Hct', Hcu'; destruct ct, cu; compute; now eauto.
Qed.

Lemma ReflectRed : forall Γ l t u (rΓ : [|- Γ])
  (rNat := natRed rΓ) (rNatNat := SimpleArr.ArrRedTy rNat rNat)
  (rTotal : [Γ ||-<l> tTotal t u]),
  [Γ ||-<l> t : arr tNat tNat | rNatNat] ->
  [Γ ||-<l> u : tNat | rNat] ->
  [Γ ||-<l> run : arr tNat (arr tNat tPNat) | SimpleArr.ArrRedTy rNat (SimpleArr.ArrRedTy rNat rNatNat)] ->
  [Γ ||-<l> tReflect t u : tTotal t u | rTotal].
Proof.
intros.
eapply LRTmEqRed_l, ReflectRedEq; tea.
Qed.

Lemma qTmEvalRed {Γ l t t₀ u k v} (rΓ : [|-Γ]) (rNat := natRed (l := l) rΓ) (rNatNat := SimpleArr.ArrRedTy rNat rNat)
  (rTotal : [Γ ||-<one> tTotal t (qNat u)]) :
  [Γ |- t ≅ t₀ : tPNat] -> [t ⇶* t₀] -> dnf t₀ -> closed0 t -> eqnf t t₀ ->
  [Γ ||-<l> run : arr tNat (arr tNat tPNat) | SimpleArr.ArrRedTy rNat (SimpleArr.ArrRedTy rNat rNatNat)] ->
  [rNatNat | Γ ||- t : tPNat] ->
  (forall k', k' < k -> [rNat | Γ ||- qRun t u k' ≅ tZero : tNat]) ->
  [rNat | Γ ||- qRun t u k ≅ tSucc (qNat v) : tNat] ->
  [rTotal | Γ ||- qEvalTm k v : tTotal t (qNat u)].
Proof.
intros ?? Hnf Hc Heq rrun rt rnil rval.
unshelve epose (rU := LRU_ (redUOneCtx _)); [|tea|].
assert (rapp : [rNat | Γ ||- tApp t (qNat u) : tNat]).
{ unshelve eapply simple_appcongTerm, qNatRedEq; tea. }
assert (Hred : ∑ v, [tApp t (qNat u) ⇶* qNat v]).
{ assert (rapp' := rapp).
  apply nf_eval in rapp'.
  destruct rapp' as (v'&?&?&?).
  assert (closed0 v').
  { eapply dredalg_closed0; [tea|unfold closed0; cbn].
    apply andb_true_intro; split; [tea|apply closedn_qNat]. }
  unshelve eapply dnf_closed_qNat in rapp; [| |tea| |]; tea.
  destruct rapp as (n&?&?); subst.
  now exists n. }
destruct Hred as [v' Hred].
assert (Hev : EvalStep Γ t u k v).
{ eapply reify_red_EvalStep.
  + intros; now unshelve apply rnil.
  + now unshelve eapply rval.
  + Unshelve. all: tea. }
assert (v' = v); [|subst v'].
{ destruct Hev as [[? Hev]].
  apply murec_elim_Some, eval_dredalg in Hev.
  apply dred_erase_qNat_compat in Hred; cbn in Hred.
  rewrite erase_qNat in Hred.
  eapply qNat_inj, dredalg_det; eauto using dnf_qNat. }
assert [rNat | Γ ||- tQuote t ≅ qNat (quote (erase t)) : tNat].
{ eapply QuoteEvalRedEq; tea.
  now eapply dredalg_closed0. }
assert (rEqLU : [rU | Γ ||- (tTotal t (qNat u)) ≅
  tEval (tApp (tApp run (qNat (quote (erase t)))) (qNat u)) (qNat k) (qNat v) : U]).
{ unshelve eapply tEvalURedEq; tea.
  + unshelve eapply simple_AppRedEq, qNatRedEq; eauto using SimpleArr.ArrRedTy; try apply qNatRed.
    unshelve eapply simple_AppRedEq; [..|tea].
    tea.
  + eapply StepEvalRedEq with (v := v); tea.
    now eapply dredalg_closed0.
  + eapply dnf_closed_qNatRedEq; tea.
}
assert (rEqRU : [rU | Γ ||- tEval (tApp (tApp run (qNat (quote (erase t)))) (qNat u)) (qNat k) (qNat v)
  ≅ qEvalTy k v : U]).
{ unshelve eapply qEvalTyEvalStepRedEq; tea.
  unshelve eapply simple_appcongTerm, qNatRedEq; eauto using SimpleArr.ArrRedTy.
  unshelve eapply simple_appcongTerm, qNatRedEq; eauto using SimpleArr.ArrRedTy. }
assert (rEqU : [rU | Γ ||- (tTotal t (qNat u)) ≅ qEvalTy k v : U]).
{ now etransitivity. }
assert (rEvalTy : [Γ ||-<one> qEvalTy k v]).
{ unshelve eapply ElURed, LRTmEqRed_r, rEqU. }
assert (rEq : [Γ ||-<one> qEvalTy k v ≅ (tTotal t (qNat u))]) .
{ eapply UnivEq; now symmetry. }
eapply irrLRConv; [apply rEq|].
now unshelve apply qEvalTmRed.
Qed.

Lemma ReflectEvalRedEq : forall Γ l t t₀ u k v (rΓ : [|- Γ])
  (rNat := natRed (l := l) rΓ) (rNatNat := SimpleArr.ArrRedTy rNat rNat)
  (rTotal : [Γ ||-<one> tTotal t (qNat u)]),
  [Γ |- t ≅ t₀ : tPNat] -> [t ⇶* t₀] -> dnf t₀ -> closed0 t -> eqnf t t₀ ->
  [Γ ||-<l> t : arr tNat tNat | rNatNat ] ->
  (forall k', k' < k -> [rNat | Γ ||- qRun t u k' ≅ tZero : tNat]) ->
  [rNat | Γ ||- qRun t u k ≅ tSucc (qNat v) : tNat] ->
  [Γ ||-<l> run : arr tNat (arr tNat tPNat) | SimpleArr.ArrRedTy rNat (SimpleArr.ArrRedTy rNat rNatNat)] ->
  [rTotal | Γ ||- tReflect t (qNat u) ≅ qEvalTm k v : tTotal t (qNat u)].
Proof.
intros * ????? rt rnil rval rrun.
eapply redSubstLeftTmEq.
+ eapply qTmEvalRed; tea.
+ assert [Γ |-[ ta ] run : arr tNat (arr tNat tPNat)] by now eapply escapeTerm.
  assert (closed0 t₀) by now eapply dredalg_closed0.
  transitivity (tReflect t₀ (qNat u)).
  - apply redtm_reflect; eauto using dnf_qNat, convtm_qNat, @RedClosureAlg.
    now eapply convtm_qNat.
  - apply redtm_evalreflect; tea.
    eapply eqnf_EvalStep; [tea|].
    eapply reify_Red_EvalStep; tea.
Qed.

End ReflectRed.

Section Valid.

Context `{GenericTypingProperties}.

(*
Lemma mkValid {Γ l A t} (vΓ : [||-v Γ]) (vA : [Γ ||-v< l > A | vΓ]) :
  (forall Δ σ σ' (wfΔ : [ |- Δ]) (Vσ : [vΓ | Δ ||-v σ : Γ | wfΔ]),
    [vΓ | Δ ||-v σ' : Γ | wfΔ] ->
    [vΓ | Δ ||-v σ ≅ σ' : Γ | wfΔ | Vσ] ->
    [validTy vA wfΔ Vσ | Δ ||- t[σ] ≅ t[σ'] : A[σ]]) ->
  [Γ ||-v< l > t : A | vΓ | vA].
Proof.
intros vt; split; [|tea].
intros; eapply LRTmEqRed_l.
apply vt; tea.
now apply reflSubst.
Qed.
*)

End Valid.

Section ReflectValid.

Context `{GenericTypingProperties}.
Context {SN : SNTypingProperties ta _ _ _ _ _}.

Definition evalValid {Γ l t k r} (vΓ : [||-v Γ])
  (vNat := natValid (l := l) vΓ)
  (vArr := simpleArrValid vΓ vNat vNat)
  (vt : [Γ ||-v< l > t : tPNat | vΓ | vArr ])
  (vk : [Γ ||-v< l > k : tNat | vΓ | vNat ])
  (vr : [Γ ||-v< l > r : tNat | vΓ | vNat ]) :
  [Γ ||-v< one > tEval t k r | vΓ].
Proof.
unshelve econstructor.
intros Δ tΔ σ σ' **.
unshelve epose (rU := LRU_ (redUOneCtx _)); [|tea|].
rewrite !tEval_subst.
eapply UnivEq, tEvalURedEq; tea.
- now unshelve apply vt.
- now unshelve apply vk.
- now unshelve apply vr.
Unshelve. apply rU.
Qed.

(*
Lemma TyCumValid@{u i j k l u' i' j' k' l'} {l Γ} {vΓ : VPack@{u} Γ} {A} :
typeValidity@{u i j k l} Γ vΓ l A -> typeValidity@{u' i' j' k' l'} Γ vΓ l A.
Proof.
intros [ty eq]; unshelve econstructor.
+ intros.
  now eapply LRCumulative, ty.
+ intros.
  now eapply LRTyEqIrrelevantCum, eq.
Qed.
*)

Context {Γ l t u} (vΓ : [||-v Γ])
  (vNat := natValid (l := l) vΓ)
  (vArr := simpleArrValid vΓ vNat vNat)
  (vRun := simpleArrValid vΓ vNat (simpleArrValid vΓ vNat vArr))
  (vrun : [ Γ ||-v< l > run : arr tNat (arr tNat tPNat) | vΓ | vRun ])
  (vt : [ Γ ||-v< l > t : arr tNat tNat | vΓ | vArr ])
  (vu : [ Γ ||-v< l > u : tNat | vΓ | vNat ])
.

Lemma StepValid : [ Γ ||-v< l > tStep t u : tNat | vΓ | vNat ].
Proof.
constructor.
intros Δ vΔ σ σ' vσσ'.
cbn - [vNat]; apply StepRedEq.
+ now unshelve eapply irrLR, vt.
+ now unshelve eapply irrLR, vu.
+ rewrite <- (run_subst σ).
  eapply lrefl; unshelve eapply irrLR, vrun; tea.
Qed.

Definition totalValid : [Γ ||-v< one > tTotal t u | vΓ].
Proof.
intros; unfold tTotal.
(* apply TyCumValid. *)
apply (evalValid (l := l)).
+ eapply (simple_appValid (F := tNat)); [eapply  (simple_appValid (F := tNat))|].
  - apply vrun.
  - apply QuoteCongValid; tea.
  - tea.
+ apply StepValid.
+ eapply (simple_appValid (F := tNat)); tea.
Unshelve. all: tea.
apply simpleArrValid; tea.
Qed.

End ReflectValid.

Section ReflectValid.

Context `{GenericTypingProperties}.
Context {SN : SNTypingProperties ta _ _ _ _ _}.

Context {Γ l t u} (vΓ : [||-v Γ])
  (vNat := natValid (l := l) vΓ)
  (vArr := simpleArrValid vΓ vNat vNat)
  (vRun := simpleArrValid vΓ vNat (simpleArrValid vΓ vNat vArr))
  (vrun : [ Γ ||-v< l > run : arr tNat (arr tNat tPNat) | vΓ | vRun ])
  (vt : [ Γ ||-v< l > t : arr tNat tNat | vΓ | vArr ])
  (vu : [ Γ ||-v< l > u : tNat | vΓ | vNat ])
.

Notation totalValid := ((totalValid vΓ vrun vt vu)).

Lemma ReflectValid : [ Γ ||-v< one > tReflect t u : tTotal t u | vΓ | totalValid ].
Proof.
constructor; intros; cbn.
pose (rNat := natRed (l := l) wfΔ).
assert (rrun : [SimpleArr.ArrRedTy (natRed wfΔ)
   (SimpleArr.ArrRedTy rNat (SimpleArr.ArrRedTy rNat rNat)) | Δ ||- run : arr tNat (arr tNat (arr tNat tNat))]).
{ - rewrite <- (run_subst σ).
  unshelve eapply irrLR, vrun; now try eapply lrefl. }
eapply irrLREq; [symmetry; apply tTotal_subst|].
unshelve eapply ReflectRedEq; tea.
+ now unshelve eapply irrLR, vt.
+ now unshelve eapply irrLR, vu.
+ rewrite <- (run_subst σ).
  unshelve eapply irrLR, vrun; now try eapply lrefl.
Unshelve.
eapply TotalRed.
- now unshelve (unshelve eapply irrLR, lrefl, vt; [..|tea]).
- now unshelve (unshelve eapply irrLR, lrefl, vu; [..|tea]).
- rewrite <- (run_subst σ).
  unshelve eapply irrLR, vrun; now try eapply lrefl.
Unshelve. all: tea.
Qed.

End ReflectValid.

Section StepEvalValid.

Context `{GenericTypingProperties}.
Context {SN : SNTypingProperties ta _ _ _ _ _}.

Context {Γ l t} {u k v : nat} (vΓ : [||-v Γ])
  (vNat := natValid (l := l) vΓ)
  (vArr := simpleArrValid vΓ vNat vNat)
  (vRun := simpleArrValid vΓ vNat (simpleArrValid vΓ vNat vArr))
  (vrun : [ Γ ||-v< l > run : arr tNat (arr tNat tPNat) | vΓ | vRun ])
  (vt : [ Γ ||-v< l > t : arr tNat tNat | vΓ | vArr ])
.

Lemma StepEvalValid :
  dnf t -> closed0 t ->
  (forall k', k' < k -> [Γ ||-v<l> qRun t u k' ≅ tZero : tNat | vΓ | vNat]) ->
  [Γ ||-v<l> qRun t u k ≅ tSucc (qNat v) : tNat | vΓ | vNat] ->
  [Γ ||-v<l> tStep t (qNat u) ≅ qNat k : tNat | vΓ | vNat].
Proof.
intros Hnf Hc Hnil Hval; constructor; intros.
cbn - [LRPack.eqTm validTyExt]; rewrite !qNat_subst.
pose (rNat := natRed (l := l) wfΔ).
assert (rPNat := SimpleArr.ArrRedTy rNat rNat).
assert (rt : [rPNat | Δ ||- t[σ] : tPNat]).
{ eapply lrefl; unshelve eapply irrLR, vt; tea. }
destruct (nf_eval rt) as (t₀&?&?&?).
eapply StepEvalRedEq with (v := v); tea.
- now eapply dredalg_closed0, closed0_subst.
- now eapply dnf_closed_subst_eqnf.
- eapply lrefl; unshelve eapply irrLR, vt; tea.
- intros k' Hk'.
  rewrite <- qRun_subst; tea.
  now apply Hnil.
- rewrite <- qRun_subst; tea.
  rewrite <- qNat_subst with (σ := σ').
  now apply Hval.
- rewrite <- (run_subst σ).
+ unshelve eapply irrLR, vrun; now try eapply lrefl. 
Qed.

Context {vTotal : [Γ ||-v< one > tTotal t (qNat u) | vΓ]}.

Lemma qTmEvalValid :
  dnf t -> closed0 t ->
  (forall k', k' < k -> [Γ ||-v<l> qRun t u k' ≅ tZero : tNat | vΓ | vNat]) ->
  [Γ ||-v<l> qRun t u k ≅ tSucc (qNat v) : tNat | vΓ | vNat] ->
  [Γ ||-v< one > qEvalTm k v : tTotal t (qNat u) | vΓ | vTotal].
Proof.
intros Hnf Hc Hnil Hval.
constructor.
intros; cbn - [LRPack.eqTm validTyExt]; rewrite !qEvalTm_subst.
pose (rNat := natRed (l := l) wfΔ).
pose (rNatNat := SimpleArr.ArrRedTy rNat rNat).
assert (rt : [rNatNat | Δ ||- t[σ] ≅ t[σ] : tPNat]).
{ eapply lrefl; unshelve eapply irrLR, vt; tea. }
assert (rrun : [SimpleArr.ArrRedTy rNat (SimpleArr.ArrRedTy rNat rNatNat) | Δ ||- run : arr tNat (arr tNat (arr tNat tNat))]).
{ rewrite <- (run_subst σ).
  eapply lrefl; unshelve eapply irrLR, vrun; tea. }
destruct (nf_eval rt) as (t₀&?&?&?).
assert (Hrw : tTotal t[σ] (qNat u) = (tTotal t (qNat u))[σ]).
{ now rewrite tTotal_subst, qNat_subst. }
unshelve (eapply irrLREq; [apply Hrw|eapply qTmEvalRed]; tea).
+ unshelve eapply TotalRed; tea.
  unshelve eapply qNatRedEq.
+ now apply closed0_subst.
+ now apply dnf_closed_subst_eqnf.
+ intros.
  rewrite <- qRun_subst; tea.
  unshelve eapply Hnil; tea.
+ rewrite <- qRun_subst; tea.
  rewrite <- (qNat_subst _ σ').
  unshelve eapply Hval; tea.
Qed.

Lemma ReflectEvalValid :
  dnf t -> closed0 t ->
  (forall k', k' < k -> [Γ ||-v<l> qRun t u k' ≅ tZero : tNat | vΓ | vNat]) ->
  [Γ ||-v<l> qRun t u k ≅ tSucc (qNat v) : tNat | vΓ | vNat] ->
  [Γ ||-v<one> tReflect t (qNat u) ≅ qEvalTm k v : tTotal t (qNat u) | vΓ | vTotal].
Proof.
intros Hnf Hc Hnil Hval; constructor; intros; cbn.
rewrite qEvalTm_subst, qNat_subst.
assert (Hrw : tTotal t[σ] (qNat u) = (tTotal t (qNat u))[σ]).
{ now rewrite tTotal_subst, qNat_subst. }
pose (rNat := natRed (l := l) wfΔ).
pose (rNatNat := SimpleArr.ArrRedTy rNat rNat).
assert (rt : [rNatNat | Δ ||- t[σ] : tPNat]).
{ eapply lrefl; unshelve eapply irrLR, vt; tea. }
destruct (nf_eval rt) as (t₀&?&?&?).
unshelve (eapply irrLREq; [exact Hrw|]; tea); [shelve|..].
+ unshelve eapply TotalRed; tea.
  - eapply qNatRedEq.
  - rewrite <- (run_subst σ).
    eapply lrefl; unshelve eapply irrLR, vrun; tea.
+ unshelve eapply ReflectEvalRedEq with (t₀ := t₀); tea.
  - now apply closed0_subst.
  - now eapply dnf_closed_subst_eqnf.
  - intros; rewrite <- qRun_subst; tea.
    unshelve eapply Hnil; tea.
  - rewrite <- qRun_subst; tea.
    rewrite <- (qNat_subst _ σ').
    now unshelve eapply Hval.
  - rewrite <- (run_subst σ).
    eapply lrefl; unshelve eapply irrLR, vrun; tea.
Qed.

End StepEvalValid.

Section ReflectCongValid.

Context `{GenericTypingProperties}.

Context {SN : SNTypingProperties ta _ _ _ _ _}.

Context {Γ l t t' u u'} (vΓ : [||-v Γ])
  (vNat := natValid (l := l) vΓ)
  (vArr := simpleArrValid vΓ vNat vNat)
  (vRun := simpleArrValid vΓ vNat (simpleArrValid vΓ vNat vArr))
  (vrun : [ Γ ||-v< l > run : arr tNat (arr tNat tPNat) | vΓ | vRun ])
  (vt : [ Γ ||-v< l > t : arr tNat tNat | vΓ | vArr ])
  (vt' : [ Γ ||-v< l > t' : arr tNat tNat | vΓ | vArr ])
  (vu : [ Γ ||-v< l > u : tNat | vΓ | vNat ])
  (vu' : [ Γ ||-v< l > u' : tNat | vΓ | vNat ])
.

Lemma StepCongValid :
  [Γ ||-v<l> t ≅ t' : arr tNat tNat | vΓ | vArr] ->
  [Γ ||-v<l> u ≅ u' : tNat | vΓ | vNat ] ->
  [Γ ||-v<l> tStep t u ≅ tStep t' u' : tNat | vΓ | vNat ].
Proof.
intros vtt' vuu'; constructor.
intros; cbn.
unshelve eapply StepRedEq with (l := l).
+ tea.
+ now unshelve eapply irrLR, vtt'.
+ now unshelve eapply irrLR, vuu'.
+ rewrite <- (run_subst σ).
  eapply lrefl.
  now unshelve eapply irrLR, vrun; tea.
Qed.

Notation totalValid := (totalValid vΓ vrun vt vu).

Lemma totalCongValid :
  [Γ ||-v<l> t ≅ t' : arr tNat tNat | vΓ | vArr] ->
  [Γ ||-v<l> u ≅ u' : tNat | vΓ | vNat ] ->
  [Γ ||-v<one> tTotal t u ≅ tTotal t' u' | vΓ ].
Proof.
intros vtt' vuu'; unfold tTotal; constructor; intros.
rewrite !tEval_subst.
assert (rU := redUOneCtx wfΔ).
unshelve eapply UnivEq with (rU := LRU_ rU), tEvalURedEq; tea.
+ now unshelve apply natRed.
+ eauto using SimpleArr.ArrRedTy, natRed.
+ cbn.
  eapply simple_appcongTerm; [|unshelve apply vuu'; tea].
  eapply simple_appcongTerm.
  - now unshelve apply vrun.
  - now unshelve eapply QuoteRedEq, escapeEqTerm, vtt'.
+ cbn - [natRed].
  eapply StepRedEq; tea.
  - now unshelve eapply irrLR, vtt'.
  - now unshelve eapply vuu'.
  - rewrite <- (run_subst σ).
    eapply lrefl; unshelve eapply irrLR, vrun; tea.
+ cbn - [natRed].
  eapply simple_appcongTerm; [|unshelve apply vuu'; tea].
  unshelve apply vtt'; tea.
Unshelve.
{ apply SimpleArr.ArrRedTy, SimpleArr.ArrRedTy; now apply natRed. }
{ now apply natRed. }
Qed.

Lemma ReflectCongValid :
  [Γ ||-v<l> t ≅ t' : arr tNat tNat | vΓ | vArr] ->
  [Γ ||-v<l> u ≅ u' : tNat | vΓ | vNat ] ->
  [Γ ||-v<one> tReflect t u ≅ tReflect t' u' : tTotal t u | vΓ | totalValid ].
Proof.
intros vtt' vuu'; constructor; intros.
pose (rNat := natRed (l := l) wfΔ).
pose (rPNat := SimpleArr.ArrRedTy rNat rNat).
assert (rtt' : [rPNat | Δ ||- t[σ] ≅ t'[σ'] : tPNat]).
{ unshelve eapply irrLR, vtt'; tea. }
assert (ruu' : [rNat | Δ ||- u[σ] ≅ u'[σ'] : tNat]).
{ unshelve eapply irrLR, vuu'; tea. }
cbn.
eapply irrLREq; [symmetry; apply tTotal_subst|].
unshelve eapply ReflectRedEq; tea.
+ unshelve eapply irrLR, rtt'.
+ rewrite <- (run_subst σ).
  eapply lrefl; unshelve eapply irrLR, vrun; tea.
Unshelve.
eapply TotalRed.
- unshelve eapply lrefl, rtt'.
- unshelve eapply lrefl, ruu'.
- rewrite <- (run_subst σ).
  eapply lrefl; unshelve eapply irrLR, vrun; tea.
Qed.

End ReflectCongValid.
*)