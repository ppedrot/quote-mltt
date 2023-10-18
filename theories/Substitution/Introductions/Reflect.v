From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Computation Notations Context Closed NormalForms NormalEq Weakening UntypedReduction
  DeclarativeTyping GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Escape Reflexivity Neutral Weakening Irrelevance Application Reduction Transitivity NormalRed.
From LogRel.Substitution Require Import Irrelevance Properties SingleSubst.
From LogRel.Substitution.Introductions Require Import Universe Var Nat SimpleArr Sigma Id Quote.

Set Universe Polymorphism.

Section Utils.

Context `{GenericTypingProperties}.

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

Lemma dnf_closed_qNat_aux : forall Γ (rNat : [Γ ||-Nat tNat]),
  (forall t, [Γ ||-Nat t : tNat | rNat] -> forall u, [t ⇶* u] -> dnf u -> closed0 u -> ∑ n, u = qNat n) ×
  (forall t, NatProp rNat t -> forall u, [t ⇶* u] -> dnf u -> closed0 u -> ∑ n, u = qNat n).
Proof.
intros; apply NatRedInduction.
+ intros * [? Hr] Heq ? IH u Hr' Hnf Hc.
  apply IH; tea.
  eapply dred_red_det; tea.
  now eapply dred_red, redtm_sound.
+ intros * Hr Hnf Hc.
  apply dred_dnf in Hr; [subst|eauto using dnf].
  exists 0; reflexivity.
+ intros * Hn IH u Hr Hnf Hc.
  destruct (redalg_succ_adj _ _ Hr) as [m ->].
  apply redalg_succ_inv in Hr.
  inversion Hnf; subst; [|match goal with H : dne _ |- _ => inversion H end].
  destruct (IH _ Hr) as [v Hv]; tea; subst.
  exists (S v); reflexivity.
+ intros n [? Hne] * Hr Hnf Hc; exfalso.
  apply convneu_whne in Hne.
  eapply dredalg_whne in Hr; [|tea].
  now eapply closed0_whne.
Qed.

Lemma dnf_closed_qNat : forall Γ l t u (rΓ : [|- Γ]) (rNat := natRed rΓ),
  [Γ ||-<l> t : tNat | rNat] -> [t ⇶* u] -> dnf u -> closed0 u -> ∑ n, u = qNat n.
Proof.
intros * Ht Hr Hnf.
edestruct dnf_closed_qNat_aux as [Haux ?]; eapply Haux; tea.
Qed.

Set Printing Primitive Projection Parameters.

Lemma NatPropEq_diag {Γ A} {rNat : [Γ ||-Nat A]} :
  (forall t u, [Γ ||-Nat t ≅ u : A | rNat] -> NatRedTm rNat t)
  × (forall t u, NatPropEq rNat t u -> [Γ |- t : tNat] -> NatProp rNat t).
Proof.
apply NatRedEqInduction.
+ intros; econstructor; tea.
  - now eapply lrefl.
  - destruct redL; eauto.
+ constructor.
+ intros; now constructor.
+ intros * []; constructor.
  constructor; tea; now eapply lrefl.
Qed.

Lemma LRTmEqRed_l : forall Γ l A t u (rA : [Γ ||-<l> A]),
  [rA | Γ ||- t ≅ u : A] -> [rA | Γ ||- t : A].
Proof.
intros Γ l A t u rA.
revert t u.
pattern l, Γ, A, rA.
eapply Induction.LR_rect_TyUr; clear l Γ A rA.
+ intros l Γ A rU t u [rl]; apply rl.
+ intros l Γ A rne t u [].
  unshelve econstructor; [|tea|].
  now eapply lrefl.
+ intros l Γ A rΠ IHdom IHcod t u []; tea.
+ intros l Γ A rNat t u [].
  cbn; econstructor; [tea| |].
  - now eapply lrefl.
  - destruct redL; now eapply NatPropEq_diag.
+ intros l Γ A rEmpty t u [].
  cbn; econstructor; [tea| |].
  - now eapply lrefl.
  - destruct prop; do 2 constructor.
    * apply redL.
    * destruct r; now eapply lrefl.
+ intros l Γ A rΣ IHdom IHcod t u []; tea.
+ intros l Γ A rId IHty IHty' t u [].
  cbn; econstructor; [tea| |].
  - now eapply lrefl.
  - destruct prop; [left|right]; tea.
    split; [apply redL|destruct r; now eapply lrefl].
Qed.

Lemma LRTmEqRed_r : forall Γ l A t u (rA : [Γ ||-<l> A]),
  [rA | Γ ||- t ≅ u : A] -> [rA | Γ ||- u : A].
Proof.
intros; now eapply LRTmEqRed_l, LRTmEqSym.
Qed.

Lemma red_redtm_exp {Γ l A t t' u u'} (rA : [Γ ||-<l> A]) :
  [Γ |- t' ⤳* t : A] -> [Γ |- u' ⤳* u : A] ->
  [Γ ||-<l> t ≅ u : A | rA] -> [Γ ||-<l> t' ≅ u' : A | rA].
Proof.
intros.
eapply transEqTerm; [|eapply transEqTerm; [|apply LRTmEqSym]].
- apply redSubstTerm; [|tea].
  now eapply LRTmEqRed_l.
- tea.
- apply redSubstTerm; [|tea].
  now eapply LRTmEqRed_r.
Qed.

Lemma simple_betaRed {Γ l A B t a} (rΓ : [|- Γ])
  (rA : [Γ ||-<l> A]) (rB : [Γ ||-<l> B]) :
  [Γ,, A |- t : B⟨@wk1 Γ A⟩] ->
  [Γ |- a : A] ->
  [rB | Γ ||- t[a..] : B] ->
  [rB | Γ ||- tApp (tLambda A t) a ≅ t[a..] : B].
Proof.
intros rt ra rta.
apply redSubstTerm; [tea|].
replace B with B⟨↑⟩[a..] by now bsimpl.
eapply redtm_beta.
+ now eapply escape.
+ now rewrite wk1_ren_on in rt.
+ tea.
Qed.

Lemma simple_lambdaRed {Γ l A B t} (rΓ : [|- Γ])
  (rA : [Γ ||-<l> A]) (rB : [Γ ||-<l> B]) (rΠ : [Γ ||-<l> arr A B])
  (rte : forall Δ a b (ρ : Δ ≤ Γ) (rΔ : [|- Δ]) (rA := wk ρ rΔ rA) (rB := wk ρ rΔ rB),
    [Δ ||-<l> a : A⟨ρ⟩ | rA] -> [Δ ||-<l> b : A⟨ρ⟩ | rA] -> [Δ ||-<l> a ≅ b : A⟨ρ⟩ | rA] -> [Δ ||-<l> t[a .: ρ >> tRel] ≅ t[b .: ρ >> tRel] : B⟨ρ⟩ | rB]) :
  [Γ ||-<l> tLambda A t : arr A B | rΠ].
Proof.
assert (rt : forall Δ a (ρ : Δ ≤ Γ) (rΔ : [|- Δ]) (rA := wk ρ rΔ rA) (rB := wk ρ rΔ rB), [Δ ||-<l> a : A⟨ρ⟩ | rA] -> [Δ ||-<l> t[a .: ρ >> tRel] : B⟨ρ⟩ | rB]).
{ intros; eapply LRTmEqRed_l, rte; tea.
  now apply reflLRTmEq. }
pose (rΠ0 := normRedΠ rΠ).
unshelve irrelevance0; [| |apply rΠ0|reflexivity|].
assert [Γ |- A] by now escape.
assert [Γ |- A ≅ A].
{ unshelve eapply escapeEq, reflLRTyEq; tea. }
assert [|- Γ,, A] by now apply wfc_cons.
assert [Γ,, A |- B⟨↑⟩].
{ rewrite <- (wk1_ren_on Γ A).
  now unshelve eapply escape, wk, rB. }
assert [Γ,, A |- B⟨↑⟩ ≅ B⟨↑⟩].
{ rewrite <- !(@wk1_ren_on Γ A).
  apply convty_wk; [|unshelve eapply escapeEq, reflLRTyEq; tea].
  now apply wfc_cons. }
assert [Γ,, A |- t : B⟨↑⟩].
{ replace t with t[(tRel 0) .: @wk1 Γ A >> tRel].
  2:{ bsimpl; apply idSubst_term; intros []; reflexivity. }
  rewrite <- (wk1_ren_on Γ A).
  unshelve eapply escapeTerm, rt; [tea|].
  apply var0; [now rewrite wk1_ren_on|tea]. }
assert [Γ,, A |- t ≅ t : B⟨↑⟩].
{ replace t with t[(tRel 0) .: @wk1 Γ A >> tRel].
  2:{ bsimpl; apply idSubst_term; intros []; reflexivity. }
  rewrite <- (wk1_ren_on Γ A).
  unshelve eapply escapeEqTerm, reflLRTmEq, rt; [tea|].
  apply var0; [now rewrite wk1_ren_on|tea]. }
assert [Γ |- tLambda A t : arr A B].
{ now apply ty_lam. }
assert (forall Δ (ρ : Δ ≤ Γ), [|- Δ] -> [Δ,, A⟨ρ⟩ |- t⟨upRen_term_term ρ⟩ : B⟨ρ⟩⟨↑⟩]).
{ intros.
  rewrite <- (@wk_up_ren_on _ _ ρ A), <- (@wk1_ren_on Δ A⟨ρ⟩), wk_up_wk1.
  apply ty_wk; [|now rewrite wk1_ren_on].
  apply wfc_cons; tea; now eapply escape, wk. }
eexists (tLambda A t).
+ apply redtmwf_refl, ty_lam; tea.
+ unshelve constructor; cbn.
  - intros; apply reflLRTyEq.
  - intros; irrelevance0; [|unshelve apply rt; tea].
    bsimpl; apply rinstInst'_term.
    irrelevance0; [reflexivity|tea].
+ cbn; apply convtm_eta; tea.
  - constructor; tea.
  - constructor; tea.
  - cbn.
    assert [Γ,, A |- tApp (tLambda A⟨↑⟩ t⟨upRen_term_term ↑⟩) (tRel 0) ⤳* t : B⟨↑⟩].
    { replace B⟨↑⟩ with B⟨↑ >> ↑⟩[(tRel 0)..].
      2:{ bsimpl; symmetry; now apply rinst_inst_term. }
      set (t' := t) at 2; replace t' with t⟨upRen_term_term ↑⟩[(tRel 0)..].
      2:{ bsimpl; apply idSubst_term; now intros []. }
      eapply redtm_beta.
      + rewrite <- (@wk1_ren_on Γ A); now apply wft_wk.
      + replace B⟨↑ >> ↑⟩ with (B⟨↑⟩⟨upRen_term_term ↑⟩) by now bsimpl.
        rewrite <- !(wk_up_wk1_ren_on Γ A A).
        rewrite <- (wk1_ren_on Γ A).
        apply ty_wk; [|tea]; apply wfc_cons; [tea|].
        apply wft_wk; tea.
      + now apply ty_var0.
    }
    eapply convtm_exp; tea.
+ cbn; intros.
  assert (Hrw : B⟨ρ⟩ = B⟨↑⟩[a .: ρ >> tRel]).
  { bsimpl; apply rinstInst'_term. }
  eapply (redSubstTerm (u := t[a .: ρ >> tRel])); tea.
  - irrelevance0; [|unshelve apply rt; tea].
    bsimpl; apply rinstInst'_term.
    irrelevance0; [reflexivity|tea].
  - replace t[a .: ρ >> tRel] with t⟨upRen_term_term ρ⟩[a..] by now bsimpl.
    rewrite <- Hrw.
    replace B⟨ρ⟩ with B⟨ρ⟩⟨↑⟩[a..].
    2:{ bsimpl; symmetry; apply rinstInst'_term. }
    apply redtm_beta; [now eapply escape, wk| |now eapply escapeTerm].
    now eauto.
+ cbn; intros.
  assert (Hrw : B⟨ρ⟩ = B⟨↑⟩[a .: ρ >> tRel]).
  { bsimpl; apply rinstInst'_term. }
  unshelve (irrelevance0; [tea|]); [shelve|now apply wk|].
  unshelve eapply (LREqTermHelper (G' := B⟨ρ⟩)). 1-2: shelve.
  - now apply wk.
  - unshelve eapply simple_betaRed; first [now apply wk|now eapply escapeTerm|tea].
    * rewrite wk1_ren_on; now eauto.
    * replace (t⟨upRen_term_term ρ⟩[a..]) with t[a .: ρ >> tRel] by now bsimpl.
      apply rt.
      irrelevance0; [reflexivity|apply ha].
  - unshelve eapply simple_betaRed; first [now apply wk|now eapply escapeTerm|tea].
    * rewrite wk1_ren_on; now eauto.
    * replace (t⟨upRen_term_term ρ⟩[b..]) with t[b .: ρ >> tRel] by now bsimpl.
      apply rt.
      irrelevance0; [reflexivity|apply hb].
  - apply reflLRTyEq.
  - replace (t⟨upRen_term_term ρ⟩[a..]) with t[a .: ρ >> tRel] by now bsimpl.
    replace (t⟨upRen_term_term ρ⟩[b..]) with t[b .: ρ >> tRel] by now bsimpl.
    apply rte; (irrelevance0; [reflexivity|]).
    { apply ha. }
    { apply hb. }
    { apply eq. }
Qed.

Lemma tAndRed {Γ l A B} (rΓ : [|- Γ])
  (rA : [Γ ||-<l> A]) (rB : [Γ ||-<l> B]) : [Γ ||-<l> tAnd A B].
Proof.
assert [Γ |- A] by now eapply escape.
assert [|- Γ,, A] by gen_typing.
assert [Γ |- B] by now eapply escape.
assert [Γ,, A |- B⟨↑⟩].
{ rewrite <- (@wk1_ren_on Γ A); apply wft_wk; tea. }
eapply LRSig'; econstructor.
+ now apply redtywf_refl, wft_sig.
+ unshelve eapply escapeEq, reflLRTyEq; tea.
+ apply convty_sig; tea.
  - unshelve eapply escapeEq, reflLRTyEq; tea.
  - rewrite <- (@wk1_ren_on Γ A); apply convty_wk; tea.
    unshelve eapply escapeEq, reflLRTyEq; tea.
+ unshelve econstructor; tea.
  - intros; now eapply wk.
  - intros ? a **.
    assert (Hrw : B⟨ρ⟩ = B⟨↑⟩[a .: ρ >> tRel]).
    { bsimpl; apply rinstInst'_term. }
    rewrite <- Hrw; now eapply wk.
  - intros.
    assert (Hrw : forall a, B⟨ρ⟩ = B⟨↑⟩[a .: ρ >> tRel]).
    { intros; bsimpl; apply rinstInst'_term. }
    irrelevance0; [apply Hrw|].
    rewrite <- Hrw; unshelve apply wkEq, reflLRTyEq; tea.
Qed.

Lemma tAndRedEq {Γ l A A' B B'} (rΓ : [|- Γ]) (rΣ : [Γ ||-<l> tAnd A B])
  (rA : [Γ ||-<l> A]) (tA' : [Γ |- A']) (rB : [Γ ||-<l> B]) (tB' : [Γ |- B']) (rAA' : [rA | Γ ||- A ≅ A']) (rBB' : [rB | Γ ||- B ≅ B'])
  : [rΣ | Γ ||- tAnd A B ≅ tAnd A' B'].
Proof.
pose (rΣ0 := normRedΣ rΣ).
unshelve (irrelevance0; [reflexivity|]); [|apply rΣ0|].
unshelve econstructor; [shelve|shelve|..].
+ apply redtywf_refl,  wft_sig; tea.
  rewrite <- !(@wk1_ren_on Γ A').
  apply wft_wk; tea.
  now eapply wfc_cons.
+ cbn; now eapply escapeEq.
+ cbn; eapply convty_sig.
  - now eapply escape.
  - now eapply escapeEq.
  - rewrite <- !(@wk1_ren_on Γ A).
    apply convty_wk; [|now eapply escapeEq].
    apply wfc_cons; tea; now eapply escape.
+ cbn; split.
  - intros.
    irrelevance0; [reflexivity|]; now unshelve eapply wkEq.
  - intros.
    assert (Hrw : forall B, B⟨ρ⟩ = B⟨↑⟩[a .: ρ >> tRel]).
    { intros; bsimpl; apply rinstInst'_term. }
    irrelevance0; [apply Hrw|].
    rewrite <- Hrw.
    now unshelve eapply wkEq.
Qed.

Lemma tAndURed {Γ l A B} (rΓ : [|- Γ])
  (rU : [Γ ||-<l> U]) (rA : [Γ ||-<l> A : U | rU]) (rB : [Γ ||-<l> B : U | rU]) :
  [Γ ||-<l> tAnd A B : U | rU].
Proof.
unshelve (irrelevance0; [reflexivity|]); [|apply (LRU_ (redUOne rΓ))|].
assert [Γ |- A : U] by now eapply escapeTerm.
assert [|- Γ,, A] by gen_typing.
assert [Γ |- B : U] by now eapply escapeTerm.
econstructor.
+ apply redtmwf_refl, ty_sig.
  - now unshelve eapply escapeTerm.
  - rewrite <- (@wk1_ren_on Γ A).
    change U with U⟨@wk1 Γ A⟩; eapply ty_wk; tea.
+ constructor.
+ apply convtm_sig; tea.
  - now eapply escapeEqTerm, reflLRTmEq.
  - rewrite <- (@wk1_ren_on Γ A).
    change U with U⟨@wk1 Γ A⟩; eapply convtm_wk; tea.
    now eapply escapeEqTerm, reflLRTmEq.
+ cbn.
  unshelve refine (LRCumulative (tAndRed _ _ _)); tea.
  - assert (rA' : [ LRU_ (redUOne rΓ) | Γ ||- A : U]) by now irrelevance0.
    destruct rA' as [? ? ? ? r]; apply r.
  - assert (rB' : [ LRU_ (redUOne rΓ) | Γ ||- B : U]) by now irrelevance0.
    destruct rB' as [? ? ? ? r]; apply r.
Qed.

Lemma tAndURedEq {Γ l A A' B B'} (rΓ : [|- Γ])
  (rU : [Γ ||-<l> U])
  (rAA' : [Γ ||-<l> A ≅ A' : U | rU]) (rBB' : [Γ ||-<l> B ≅ B' : U | rU]) : [Γ ||-<l> tAnd A B ≅ tAnd A' B' : U | rU].
Proof.
intros.
pose (rU' := LRU_ (redUOne rΓ)).
unshelve (irrelevance0; [reflexivity|]); [|apply rU'|].
unshelve eapply LRTmEqIrrelevant' in rAA'; [..|reflexivity]; [|apply rU'|].
unshelve eapply LRTmEqIrrelevant' in rBB'; [..|reflexivity]; [|apply rU'|].
assert (rA : [Γ ||-<one> A : U | rU']) by apply rAA'.
assert (rA' : [Γ ||-<one> A' : U | rU']) by apply rAA'.
assert (rB : [Γ ||-<one> B : U | rU']) by apply rBB'.
assert (rB' : [Γ ||-<one> B' : U | rU']) by apply rBB'.
unshelve econstructor.
+ refine (tAndURed rΓ rU' rA rB).
+ refine (tAndURed rΓ rU' rA' rB').
+ unshelve refine (tAndRed _ _ _); tea.
  - destruct rA as [? ? ? ? r]; apply r.
  - destruct rB as [? ? ? ? r]; apply r.
+ assert (Hrw : forall rec t A (R : [Γ ||-U< one > A]) (p : [rec | Γ ||-U t : A | R]), whnf t -> URedTm.te p = t).
  { intros; symmetry; eapply red_whnf; [|tea].
    now eapply redtm_sound, tmr_wf_red, URedTm.red. }
  rewrite !Hrw; try now constructor.
  apply convtm_and; first [now eapply escapeTerm|now eapply escapeEqTerm].
+ refine (tAndRed _ _ _); tea.
  - destruct rA' as [? ? ? ? r]; apply r.
  - destruct rB' as [? ? ? ? r]; apply r.
+ cbn.
  unshelve eapply tAndRedEq; tea.
  - apply rA.
  - apply rB.
  - now eapply wft_term, escapeTerm.
  - now eapply wft_term, escapeTerm.
  - destruct rAA'.
    destruct rA; cbn.
    unshelve (irrelevance0; [reflexivity|]).
    * shelve.
    * refine (embRedTyOne relL).
    * apply relEq.
  - destruct rBB'.
    destruct rB; cbn.
    unshelve (irrelevance0; [reflexivity|]).
    * shelve.
    * refine (embRedTyOne relL).
    * apply relEq.
Qed.

Lemma tIsNilRed {Γ l t} (rΓ : [|- Γ])
  (rNat := natRed rΓ)
  (rU : [Γ ||-<one> U])
  (rt : [Γ ||-<l> t : tNat | rNat]) :
  [rU | Γ ||- tIsNil t : U].
Proof.
unshelve eapply Id.IdRedU.
+ now apply natRed.
+ irrelevance0; [reflexivity|]; now unshelve apply natTermRed.
+ tea.
+ unshelve eapply zeroRed; tea.
Qed.

Lemma tIsNilRedEq {Γ l t t'} (rΓ : [|- Γ])
  (rNat := natRed rΓ)
  (rU : [Γ ||-<one> U])
  (rt : [Γ ||-<l> t ≅ t' : tNat | rNat]) :
  [rU | Γ ||- tIsNil t ≅ tIsNil t' : U].
Proof.
unshelve eapply Id.IdCongRedU.
+ now apply natRed.
+ now apply natRed.
+ irrelevance0; [reflexivity|]; now unshelve apply natTermRed.
+ irrelevance0; [reflexivity|]; now unshelve apply natTermRed.
+ eapply reflLRTmEq; irrelevance0; [reflexivity|]; now unshelve apply natTermRed.
+ eapply LRTmEqRed_l, rt.
+ eapply LRTmEqRed_r, rt.
+ eapply rt.
+ now eapply zeroRed.
+ now eapply zeroRed.
+ now eapply zeroRedEq.
Qed.

Lemma tIsValRed {Γ l t v} (rΓ : [|- Γ])
  (rNat := natRed rΓ)
  (rU : [Γ ||-<one> U])
  (rt : [Γ ||-<l> t : tNat | rNat])
  (rv : [Γ ||-<l> v : tNat | rNat]) :
  [rU | Γ ||- tIsVal t v : U].
Proof.
unshelve eapply Id.IdRedU.
+ now apply natRed.
+ irrelevance0; [reflexivity|]; now unshelve apply natTermRed.
+ tea.
+ unshelve eapply succRed, rv.
Qed.

Lemma tIsValRedEq {Γ l t t' v v'} (rΓ : [|- Γ])
  (rNat := natRed rΓ)
  (rU : [Γ ||-<one> U])
  (rt : [Γ ||-<l> t ≅ t' : tNat | rNat])
  (rv : [Γ ||-<l> v ≅ v' : tNat | rNat]) :
  [rU | Γ ||- tIsVal t v ≅ tIsVal t' v' : U].
Proof.
pose (rU' := LRU_ (redUOne rΓ)).
unshelve (irrelevance0; [reflexivity|]); [|exact rU'|].
clear rU; rename rU' into rU.
assert [rU | Γ ||- tNat : U].
{ irrelevance0; [reflexivity|].
  now unshelve apply natTermRed. }
assert [rU | Γ ||- tNat ≅ tNat : U] by now apply reflLRTmEq.
assert (rS : [rNat | Γ ||- tSucc v ≅ tSucc v' : tNat]).
{ apply succRedEq.
  - eapply LRTmEqRed_l, rv.
  - eapply LRTmEqRed_r, rv.
  - eapply rv. }
unshelve eapply Id.IdCongRedU; tea.
+ now apply natRed.
+ now apply natRed.
+ eapply LRTmEqRed_l, rt.
+ eapply LRTmEqRed_r, rt.
+ apply rt.
+ eapply LRTmEqRed_l, rS.
+ eapply LRTmEqRed_r, rS.
+ eapply rS.
Qed.

Lemma tShiftRed {Γ l t} (rPNat : [Γ ||-<l> tPNat])
  (rt : [rPNat | Γ ||- t : tPNat]) : [rPNat | Γ ||- tShift t : tPNat].
Proof.
assert (rΓ : [|- Γ]).
{ eapply wfc_wft; now eapply escape. }
pose (rNat := natRed (l := l) rΓ).
unshelve eapply simple_lambdaRed; tea; intros.
cbn - [rB]; unshelve eapply (SimpleArr.simple_appcongTerm (F := tNat)).
+ tea.
+ change (arr tNat tNat⟨ρ⟩) with (arr tNat tNat)⟨ρ⟩.
  now eapply (wk ρ).
+ assert (Hrw : forall a, t⟨ρ⟩ = t⟨↑⟩[a .: ρ >> tRel]).
  { intros; bsimpl; apply rinstInst'_term. }
  rewrite <- !Hrw.
  now apply reflLRTmEq, wkTerm.
+ eapply succRed; tea.
+ eapply succRed; tea.
+ eapply succRedEq; tea.
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
assert (rΓ : [|- Γ]).
{ eapply wfc_wft; now eapply escape. }
pose (rPNat0 := normRedΠ rPNat).
unshelve irrelevance0; [| |apply rPNat0|reflexivity|].
unshelve (eapply LRTmEqIrrelevant' in rt; [|reflexivity]); [|exact rPNat0|].
assert (Hrw : forall t R (p : [Γ ||-Π t : tPNat | R]), whnf t -> PiRedTm.nf p = t).
{ intros; symmetry; eapply red_whnf; tea.
    now eapply redtm_sound, tmr_wf_red, PiRedTm.red. }
unshelve econstructor.
+ eapply (tShiftRed rPNat0).
  irrelevance0; [reflexivity|]; now eapply LRTmEqRed_l.
+ eapply (tShiftRed rPNat0).
  irrelevance0; [reflexivity|]; now eapply LRTmEqRed_r.
+ rewrite !Hrw; cbn; try now constructor.
  assert [Γ |- tNat] by now apply wft_nat.
  assert [Γ |- tNat ≅ tNat] by now apply convty_term, convtm_nat.
  apply convtm_lam; tea.
  assert (rΓNat : [|- Γ,, tNat]) by gen_typing.
  assert [natRed (l := l) rΓNat | _ ||- tRel 0 : tNat].
  { apply var0; [reflexivity|]; gen_typing. }
  assert [natRed (l := l) rΓNat | _ ||- tSucc (tRel 0) : tNat].
  { now apply succRed. }
  assert [natRed (l := l) rΓNat | _ ||- tSucc (tRel 0) ≅ tSucc (tRel 0) : tNat].
  { apply succRedEq; tea; now apply reflLRTmEq. }
  rewrite <- (@wk1_ren_on Γ tNat t), <- (@wk1_ren_on Γ tNat t').
  unshelve eapply escapeEqTerm, (SimpleArr.simple_appcongTerm (F := tNat)); tea.
  - now apply natRed.
  - change (arr tNat tNat) with (arr tNat tNat)⟨@wk1 Γ tNat⟩.
    now apply wk.
  - apply wkTermEq, rt.
+ intros.
  rewrite !Hrw; try now constructor; cbn.
  unfold ren1, Ren1_well_wk.
  rewrite !(tShift_ren).
  eapply red_redtm_exp.
  - apply redtm_shift_app; [|now eapply escapeTerm].
    change (arr tNat tNat) with (arr tNat tNat)⟨ρ⟩.
    apply ty_wk; [tea|].
    now eapply escapeTerm, LRTmEqRed_l.
  - apply redtm_shift_app; [|now eapply escapeTerm].
    change (arr tNat tNat) with (arr tNat tNat)⟨ρ⟩.
    apply ty_wk; [tea|].
    now eapply escapeTerm, LRTmEqRed_r.
  - assert [natRed (l := l) h | Δ ||- a : tNat].
    { irrelevance0; [reflexivity|]; apply ha. }
    assert [natRed (l := l) h | Δ ||- tSucc a : tNat].
    { now apply succRed. }
    assert [natRed (l := l) h | Δ ||- tSucc a ≅ tSucc a : tNat].
    { apply succRedEq; tea; now apply reflLRTmEq. }
    unshelve eapply (SimpleArr.simple_appcongTerm (F := tNat)); tea.
    * cbn; change (tProd tNat tNat) with (tProd tNat tNat)⟨ρ⟩.
      apply wk; tea.
    * apply wkTermEq, rt.
Qed.

Lemma tEvalZeroRedEq {Γ l t v} (rΓ : [|- Γ])
  (rNat := natRed rΓ) (rNatNat := SimpleArr.ArrRedTy rNat rNat)
  (rU : [Γ ||-<one> U])
  (rt : [Γ ||-<l> t : tPNat | rNatNat])
  (rv : [Γ ||-<l> v : tNat | rNat]) :
  [Γ ||-<one> tEval t tZero v ≅ tIsVal (tApp t tZero) v : U | rU].
Proof.
intros; apply redSubstTerm.
+ unshelve eapply tIsValRed; [..|tea].
  unshelve eapply SimpleArr.simple_appTerm.
  - shelve.
  - now unshelve apply natRed.
  - apply SimpleArr.ArrRedTy; now apply natRed.
  - irrelevance0; [reflexivity|]; apply rt.
  - unshelve irrelevance0; [..|reflexivity|]; [|tea|]; unshelve eapply zeroRed; tea.
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
  [Γ ||-<one> tEval t (tSucc k) v ≅ tAnd (tIsNil (tApp t k)) (tEval (tShift t) k v) : U | rU].
Proof.
apply redSubstTerm.
+ apply tAndURed; tea.
  unshelve eapply tIsNilRed; [shelve|tea|].
  eapply SimpleArr.simple_appTerm; tea.
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
apply neuTermEq.
+ apply ty_eval; tea.
+ apply ty_eval; tea.
+ apply tEval_cong; tea.
Qed.

Lemma tEvalRedEq {Γ l t t' k k' v v'} (rΓ : [|- Γ])
  (rNat : [Γ ||-<l> tNat]) (rPNat : [Γ ||-<l> tPNat])
  (rU : [Γ ||-<one> U])
  (rt : [Γ ||-<l> t ≅ t' : tPNat | rPNat])
  (rk : [Γ ||-<l> k ≅ k' : tNat | rNat])
  (rv : [Γ ||-<l> v ≅ v' : tNat | rNat]) :
  [Γ ||-<one> tEval t k v ≅ tEval t' k' v' : U | rU].
Proof.
assert (Rnat : [Γ ||-Nat tNat]).
{ unshelve constructor; now apply redtywf_refl, wft_nat. }
pose (rNat' := LRNat_ l Rnat).
unshelve eapply LRTmEqIrrelevant' in rk; [..|exact rNat'| |reflexivity].
unshelve eapply LRTmEqIrrelevant' in rv; [..|exact rNat'| |reflexivity].
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
cut ((forall k k', NatRedTmEq Rnat k k' -> P k k') × (forall k k', NatPropEq Rnat k k' -> P k k')).
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
  - eapply redtm_evalBranchZero; now unshelve eapply escapeTerm.
  - eapply redtm_evalBranchZero; now unshelve eapply escapeTerm.
  - unshelve eapply tIsValRedEq; [tea|tea| |now (irrelevance0; [reflexivity|tea])].
    eapply SimpleArr.simple_appcongTerm; tea.
    * now unshelve eapply zeroRed.
    * now eapply zeroRed.
    * now eapply zeroRedEq.
+ intros k k' rk IH ?? t t' rt.
  assert [rPNat | Γ ||- t : tPNat] by now eapply LRTmEqRed_l.
  assert [rPNat | Γ ||- t' : tPNat] by now eapply LRTmEqRed_r.
  assert [Γ |- k : tNat].
  { destruct rk; now eapply redtm_ty_src, tmr_wf_red. }
  assert [Γ |- k' : tNat].
  { destruct rk; now eapply redtm_ty_src, tmr_wf_red. }
  eapply red_redtm_exp.
  - eapply redtm_evalBranchSucc; try now unshelve eapply escapeTerm.
    tea.
  - eapply redtm_evalBranchSucc; try now unshelve eapply escapeTerm.
    tea.
  - apply tAndURedEq; tea.
    * unshelve eapply tIsNilRedEq; [shelve|tea|].
      assert [rNat | Γ ||- k ≅ k' : tNat] by apply rk.
      unshelve eapply (SimpleArr.simple_appcongTerm (F := tNat)); tea.
      { now eapply LRTmEqRed_l. }
      { now eapply LRTmEqRed_r. }
    * apply IH; tea.
      now apply tShiftRedEq.
+ intros k k' rk ?? t t' rt.
  assert [rPNat | Γ ||- t : tPNat] by now eapply LRTmEqRed_l.
  assert [rPNat | Γ ||- t' : tPNat] by now eapply LRTmEqRed_r.
  apply tEvalNeuRedEq; first [assumption|now eapply escapeTerm|now eapply escapeEqTerm|idtac].
  apply rk.
Qed.

(*
Lemma tEvalZeroBranchRed {Γ v} (rΓ : [|- Γ])
  (rNat : [Γ ||-<one> tNat]) (rP : [Γ ||-<one> arr tPNat U])
  (rv : [rNat | Γ ||- v : tNat]) :
  [rP | Γ ||- tLambda tPNat (tIsVal (tApp (tRel 0) tZero) v⟨↑⟩) : arr tPNat U].
Proof.
unshelve eapply simple_lambdaRed; tea.
+ apply SimpleArr.ArrRedTy; now apply natRed.
+ now apply LRU_, redUOne.
+ intros.
  rewrite !tIsVal_subst; cbn - [rB].
  assert (Hrw : forall a, v⟨↑⟩[a .: ρ >> tRel] = v⟨ρ⟩).
  { intros x; bsimpl; symmetry; apply rinstInst'_term. }
  rewrite !Hrw.
Admitted.

Lemma tEvalSuccBranchRed {Γ} (rΓ : [|- Γ]) (rS : [Γ ||-<one> arr tNat (arr (arr tPNat U) (arr tPNat U))]) :
  [rS | Γ ||- tLambda tNat (tLambda (arr tPNat U) (tLambda tPNat
    (tAnd (tIsNil (tApp (tRel 0) (tRel 2))) (tApp (tRel 1) (tShift (tRel 0)))))) : arr tNat (arr (arr tPNat U) (arr tPNat U))].
Proof.
unshelve eapply simple_lambdaRed; tea.
+ now apply natRed.
+ do 2 apply SimpleArr.ArrRedTy; admit.
+ intros.
  cbn - [tAnd tIsNil].
  rewrite !tAnd_subst, !tIsNil_subst.
  cbn - [tAnd tIsNil].
  admit.
Admitted.
*)

Lemma tEvalRed {Γ l t k v} (rΓ : [|- Γ])
  (rNat := natRed rΓ) (rNatNat := SimpleArr.ArrRedTy rNat rNat)
  (rU : [Γ ||-<one> U])
  (rt : [Γ ||-<l> t : tPNat | rNatNat])
  (rk : [Γ ||-<l> k : tNat | rNat])
  (rv : [Γ ||-<l> v : tNat | rNat]) :
  [Γ ||-<one> tEval t k v : U | rU].
Proof.
eapply LRTmEqRed_l, tEvalRedEq.
+ tea.
+ now eapply reflLRTmEq.
+ now eapply reflLRTmEq.
+ now eapply reflLRTmEq.
Qed.

Definition evalValid {Γ l t k r} (vΓ : [||-v Γ])
  (vNat := natValid (l := l) vΓ)
  (vArr := simpleArrValid vΓ vNat vNat)
  (vt : [Γ ||-v< l > t : tPNat | vΓ | vArr ])
  (vk : [Γ ||-v< l > k : tNat | vΓ | vNat ])
  (vr : [Γ ||-v< l > r : tNat | vΓ | vNat ]) :
  [Γ ||-v< one > tEval t k r | vΓ].
Proof.
assert (vEval : forall Δ σ (vΔ : [|- Δ]) (vσ : [vΓ | Δ ||-v σ : Γ | vΔ]),
  [Δ ||-< one > tEval t[σ] k[σ] r[σ]]).
{ intros Δ σ vΔ **.
  unshelve epose (rU := LRU_ (redUOne _)); [|tea|].
  enough (rEval : [rU | Δ ||- tEval t[σ] k[σ] r[σ] : U]).
  { destruct rEval; apply (embRedTyOne rel). }
  unshelve eapply tEvalRed; tea.
  - destruct vt as [vt _].
    irrelevance0; [reflexivity|]; now unshelve apply vt.
  - destruct vk as [vk _].
    irrelevance0; [reflexivity|]; now unshelve apply vk.
  - destruct vr as [vr _].
    irrelevance0; [reflexivity|]; now unshelve apply vr.
}
unshelve econstructor.
+ intros Δ σ vΔ **.
  rewrite tEval_subst.
  now unshelve eapply vEval.
+ intros Δ σ σ' **.
  unshelve epose (rU := LRU_ (redUOne _)); [|tea|].
  unshelve (irrelevance0; [symmetry; apply tEval_subst|]); [|now eapply vEval|].
  rewrite tEval_subst with (σ := σ').
  enough (rEval : [rU | Δ ||- tEval t[σ] k[σ] r[σ] ≅ tEval t[σ'] k[σ'] r[σ'] : U]).
  { destruct rEval.
    unshelve (irrelevance0; [reflexivity|]).
    * shelve.
    * refine (embRedTyOne relL).
    * apply relEq. }
  unshelve eapply tEvalRedEq.
  - shelve.
  - now unshelve apply natRed.
  - now unshelve (apply SimpleArr.ArrRedTy; apply natRed).
  - tea.
  - destruct vt as [_ vt].
    irrelevance0; [reflexivity|]; now apply vt.
  - destruct vk as [_ vk].
    irrelevance0; [reflexivity|]; now apply vk.
  - destruct vr as [_ vr].
    irrelevance0; [reflexivity|]; now apply vr.
  Unshelve. all: tea.
Qed.

End Utils.

Section ReflectValid.

Context `{GenericTypingProperties}.
Context {SN : SNTypingProperties ta _ _ _ _ _}.

(*
Lemma ReflectRed : forall Γ l t u (rΓ : [|- Γ])
  (rNat := natRed rΓ) (rNatNat := SimpleArr.ArrRedTy rNat rNat)
  (rTotal : [Γ ||-<l> tTotal t u]),
  [Γ ||-<l> t : arr tNat tNat | rNatNat] ->
  [Γ ||-<l> u : tNat | rNat] ->
  [Γ ||-<l> run model : arr tNat (arr tNat tPNat) | SimpleArr.ArrRedTy rNat (SimpleArr.ArrRedTy rNat rNatNat)] ->
  [Γ ||-<l> tReflect t u : tTotal t u | rTotal].
Proof.
intros * rt ru rrun.
pose (rTotal' := normRedΣ0 (Induction.invLRΣ rTotal)); refold.
fold (tTotal t u) in rTotal'.
eapply LRTmRedIrrelevant' with (lrA := LRSig' rTotal'); [reflexivity|].
destruct (nf_eval rt) as [r [Hrnf [Hr Hrconv]]].
destruct (nf_eval ru) as [n [Hnnf [Hn Hnconv]]].
remember (is_closedn 0 r) as cr eqn:Hcr; symmetry in Hcr.
remember (is_closedn 0 n) as cn eqn:Hcn; symmetry in Hcn.
remember (andb cr cn) as cb eqn:Hcb; symmetry in Hcb; destruct cb.
+ destruct cr; [|cbn in Hcb; congruence].
  destruct cn; [|cbn in Hcb; congruence].
  assert (∑ n₀, n = qNat n₀) as [n₀]; [|subst].
  { eapply dnf_closed_qNat; [apply ru| | |]; tea. }
  clear Hcb Hn Hcn.
  assert (rapp : [rNat | _ ||- tApp t u : tNat]).
  { eapply SimpleArr.simple_appTerm; tea. }
  assert (Heval : ∑ m k, eval true (tApp (erase t) u) k = Some (qNat m)).
  { admit. }
  destruct Heval as (m&k&Heval).
(*   eapply (redSubstTerm (u := qTotal (model.(quote) (erase r)) n₀ k m)). *)
(*
  eapply LRTmRedConv.
(*   - cbn; unfold qTotal. *)
(*   unshelve eexists (qTotal (model.(quote) (erase r)) n₀ k m) _. *)
admit.
  - intros; unshelve irrelevance0; [exact l| |now apply natRed|reflexivity|].
    eexists (qNat k); [|now apply convtm_qNat|now apply qNatRed].
    split; [now apply ty_qNat|].
    unfold ren1, Ren1_well_wk; rewrite qTotal_ren.
    apply redtm_fst_beta.
    * gen_typing.
    * admit.
    * now apply ty_qNat.
    * rewrite tEval_subst; cbn; rewrite run_subst, quote_subst, !qNat_subst, erase_is_closed0_subst_id; tea.
      admit.
  - admit.
  - admit.
  - admit.
  - admit.
*)
admit.
+ assert ([Γ |-[ ta ] run model : arr tNat (arr tNat tPNat)]).
  { unshelve eapply escapeTerm; tea. }
(*
  assert [Γ |- tTotal r n ≅ tTotal t u].
  { eapply convty_term, tTotal_cong.
    + admit.
    + admit.
  }
*)
  eapply redSubstTerm; [|eapply redtm_reflect; tea]; try now eapply escapeTerm.
  apply neuTerm.
  - eapply ty_conv; [eapply ty_reflect; first [now eapply urefl|tea]|tea].
    eapply convty_term, tTotal_cong.
    admit.
    admit.
  - assert ((~ is_true (is_closedn 0 r)) + (~ is_true (is_closedn 0 n))).
    { destruct (is_closedn 0 r); [|left; congruence].
      destruct (is_closedn 0 n); [|right; congruence].
      subst; cbn in Hcb; congruence. }
    eapply convneu_reflect; first [now eapply urefl|now symmetry|tea].
Admitted.
*)

Lemma neuTermEqRed {Γ l A t t' n n'} (RA : [Γ ||-<l> A]) :
  [Γ |- t ⤳* n : A] ->
  [Γ |- t' ⤳* n' : A] ->
  [Γ |- n : A] -> [Γ |- n' : A] -> [Γ |- n ~ n' : A] -> [Γ ||-<l> t ≅ t' : A | RA].
Proof.
intros Ht Ht' Hn Hn' Hnn'.
eapply transEqTerm; [|eapply LRTmEqSym, transEqTerm]; [| |eapply LRTmEqSym, neuTermEq]; [..|tea]; tea.
- eapply redSubstTerm; [|tea]; try now eapply escapeTerm.
  eapply neuTerm; [tea|now eapply lrefl].
- eapply redSubstTerm; [|tea]; try now eapply escapeTerm.
  eapply neuTerm; [tea|now eapply urefl].
Qed.

Lemma ReflectRedEq : forall Γ l t t' u u' (rΓ : [|- Γ]) (rNat := natRed rΓ) (rNatNat := SimpleArr.ArrRedTy rNat rNat)
  (rTotal : [Γ ||-<l> tTotal t u]),
  [Γ ||-<l> t : arr tNat tNat | rNatNat ] ->
  [Γ ||-<l> t' : arr tNat tNat | rNatNat ] ->
  [Γ ||-<l> u : tNat | rNat ] ->
  [Γ ||-<l> u' : tNat | rNat ] ->
  [Γ ||-<l> t ≅ t' : arr tNat tNat | rNatNat ] ->
  [Γ ||-<l> u ≅ u' : tNat | rNat ] ->
  [Γ ||-<l> run model : arr tNat (arr tNat tPNat) | SimpleArr.ArrRedTy rNat (SimpleArr.ArrRedTy rNat rNatNat)] ->
  [Γ ||-<l> tReflect t u ≅ tReflect t' u' : tTotal t u | rTotal ].
Proof.
intros * rt rt' ru ru' rtt' ruu' rrun.
pose (rTotal' := normRedΣ0 (Induction.invLRΣ rTotal)); refold.
fold (tTotal t u) in rTotal'.
eapply LRTmEqIrrelevant' with (lrA := LRSig' rTotal'); [reflexivity|].
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
  assert (∑ n₀, u₀ = qNat n₀) as [n₀]; [|subst].
  { eapply dnf_closed_qNat; [apply ru| | |]; tea. }
  assert (∑ n'₀, u'₀ = qNat n'₀) as [n'₀]; [|subst].
  { eapply dnf_closed_qNat; [apply ru'| | |]; tea. }
  clear Hcu Hcu' Hcb.
  eapply red_redtm_exp.
  - admit.
  - admit.
  - admit.
+ eapply neuTermEqRed.
  - eapply redtm_reflect; tea.
    all: now eapply escapeTerm.
  - admit.
  - admit.
  - admit.
  - eapply convneu_reflect.
Admitted.

Lemma ReflectRed : forall Γ l t u (rΓ : [|- Γ])
  (rNat := natRed rΓ) (rNatNat := SimpleArr.ArrRedTy rNat rNat)
  (rTotal : [Γ ||-<l> tTotal t u]),
  [Γ ||-<l> t : arr tNat tNat | rNatNat] ->
  [Γ ||-<l> u : tNat | rNat] ->
  [Γ ||-<l> run model : arr tNat (arr tNat tPNat) | SimpleArr.ArrRedTy rNat (SimpleArr.ArrRedTy rNat rNatNat)] ->
  [Γ ||-<l> tReflect t u : tTotal t u | rTotal].
Proof.
intros.
eapply LRTmEqRed_l, ReflectRedEq; tea.
+ now eapply reflLRTmEq.
+ now eapply reflLRTmEq.
Qed.

End ReflectValid.

Section ReflectValid.

Context `{GenericTypingProperties}.
Context {SN : SNTypingProperties ta _ _ _ _ _}.

Lemma TyCumValid@{u i j k l u' i' j' k' l'} l Γ (vΓ : VPack@{u} Γ) A :
typeValidity@{u i j k l} Γ vΓ l A -> typeValidity@{u' i' j' k' l'} Γ vΓ l A.
Proof.
intros [ty eq]; unshelve econstructor.
+ intros.
  now eapply LRCumulative, ty.
+ intros.
  now eapply LRTyEqIrrelevantCum, eq.
Qed.

Context {Γ l t u} (vΓ : [||-v Γ])
  (vNat := natValid (l := l) vΓ)
  (vArr := simpleArrValid vΓ vNat vNat)
  (vRun := simpleArrValid vΓ vNat (simpleArrValid vΓ vNat vArr))
  (vrun : [ Γ ||-v< l > run model : arr tNat (arr tNat tPNat) | vΓ | vRun ])
  (vt : [ Γ ||-v< l > t : arr tNat tNat | vΓ | vArr ])
  (vu : [ Γ ||-v< l > u : tNat | vΓ | vNat ])
.

Definition totalValid : [Γ ||-v< one > tTotal t u | vΓ].
Proof.
intros; unfold tTotal.
unshelve eapply SigValid; [apply natValid|].
apply TyCumValid.
apply (evalValid (l := l)).
+ rewrite <- (run_ren _ ↑).
  change (tApp (tApp (run model)⟨↑⟩ (tQuote t⟨↑⟩)) u⟨↑⟩) with
    (tApp (tApp (run model) (tQuote t)) u)⟨↑⟩.
  change tPNat with tPNat⟨↑⟩.
  rewrite <- !(wk1_ren_on Γ tNat).
  eapply irrelevanceTm', wk1ValidTm; [eapply wk1_ren_on|].
  eapply (simple_appValid (F := tNat)); [eapply  (simple_appValid (F := tNat))|].
  - apply vrun.
  - apply QuoteValid; tea.
  - tea.
+ change tNat with (tNat⟨@wk1 Γ tNat⟩) at 2.
  unshelve eapply irrelevanceTm, var0Valid; tea.
+ rewrite <- (wk1_ren_on Γ tNat).
  change tNat with (tNat⟨@wk1 Γ tNat⟩) at 5.
  unshelve eapply irrelevanceTm, wk1ValidTm; tea.
  eapply (simple_appValid (F := tNat)); tea.
Unshelve. all: tea.
apply simpleArrValid; tea.
Qed.

Lemma ReflectValid : [ Γ ||-v< one > tReflect t u : tTotal t u | vΓ | totalValid ].
Proof.
split; cbn.
- intros Δ σ vΔ vσ; instValid vσ.
  assert (Rtotal : [Δ ||-< one > tTotal t[σ] u[σ]]).
  { rewrite <- tTotal_subst; eapply (validTy totalValid vΔ vσ). }
  unshelve irrelevance0; try exact Rtotal; [now rewrite tTotal_subst|].
  unshelve eapply ReflectRed; tea.
  + irrelevance0; [reflexivity|]; unshelve eapply vt; tea.
  + rewrite <- (run_subst σ); irrelevance0; [reflexivity|]; apply Rvrun.
- intros Δ σ σ' vΔ vσ vσ' vσσ'.
  assert (Rtotal : [Δ ||-< one > tTotal t[σ] u[σ]]).
  { rewrite <- tTotal_subst; eapply (validTy totalValid vΔ vσ). }
  unshelve irrelevance0; try exact Rtotal; [now rewrite tTotal_subst|].
  eapply ReflectRedEq.
  + irrelevance0; [reflexivity|]; unshelve eapply vt; tea.
  + irrelevance0; [reflexivity|]; unshelve eapply vt; tea.
  + irrelevance0; [reflexivity|]; unshelve eapply vu; tea.
  + irrelevance0; [reflexivity|]; unshelve eapply vu; tea.
  + irrelevance0; [reflexivity|]; unshelve eapply vt; tea.
  + irrelevance0; [reflexivity|]; unshelve eapply vu; tea.
  + rewrite <- (run_subst σ); irrelevance0; [reflexivity|]; apply vrun.
  Unshelve. all: tea.
Qed.

Lemma ReflectEvalValid :
  dnf t -> closed0 t -> dnf u -> closed0 u ->
  [ Γ ||-v< one > tReflect t u ≅ tZero : tTotal t u | vΓ | totalValid ].
Proof.
Admitted.

End ReflectValid.

Section ReflectCongValid.

Context `{GenericTypingProperties}.

Context {SN : SNTypingProperties ta _ _ _ _ _}.

Context {Γ l t t' u u'} (vΓ : [||-v Γ])
  (vNat := natValid (l := l) vΓ)
  (vArr := simpleArrValid vΓ vNat vNat)
  (vRun := simpleArrValid vΓ vNat (simpleArrValid vΓ vNat vArr))
  (vrun : [ Γ ||-v< l > run model : arr tNat (arr tNat tPNat) | vΓ | vRun ])
  (vt : [ Γ ||-v< l > t : arr tNat tNat | vΓ | vArr ])
  (vt' : [ Γ ||-v< l > t' : arr tNat tNat | vΓ | vArr ])
  (vu : [ Γ ||-v< l > u : tNat | vΓ | vNat ])
  (vu' : [ Γ ||-v< l > u' : tNat | vΓ | vNat ])
.

Lemma totalCongValid :
  [Γ ||-v<l> t ≅ t' : arr tNat tNat | vΓ | vArr] ->
  [Γ ||-v<l> u ≅ u' : tNat | vΓ | vNat ] ->
  [Γ ||-v<one> tTotal t u ≅ tTotal t' u' | vΓ | totalValid _ vrun vt vu ].
Proof.
intros; unfold tTotal.
eapply irrelevanceTyEq, SigCong; [|apply natconvValid|].
Admitted.

Lemma ReflectCongValid :
  [Γ ||-v<l> t ≅ t' : arr tNat tNat | vΓ | vArr] ->
  [Γ ||-v<l> u ≅ u' : tNat | vΓ | vNat ] ->
  [Γ ||-v<one> tReflect t u ≅ tReflect t' u' : tTotal t u | vΓ | totalValid _ vrun vt vu ].
Proof.
Admitted.

End ReflectCongValid.
