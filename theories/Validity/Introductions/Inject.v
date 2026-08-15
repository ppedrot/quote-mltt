From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Nat Id EqComplete.
From LogRel.Validity Require Import Validity Irrelevance Properties.
From LogRel.Validity Require Import Universe Nat SimpleArr Id Quote.

Section InjectRed.

Context `{GenericTypingProperties}.
Context {SN : SNTypingProperties ta _ _ _ _ _}.
Context {SNC : SNCompleteTypingProperties ta _ _ _ _ _ _}.

#[local]
Lemma not_whne_qNat : forall n, whne (qNat n) -> False.
Proof.
intros [] **; inv_whne.
Qed.

#[local]
Lemma NatPropEq_qNat_inj_aux : forall Γ,
  (forall n n', [Γ ||-Nat n ≅ n':Nat] -> forall k k', n = qNat k -> n' = qNat k' -> k = k') ×
  (forall n n' (Rnn' : NatPropEq Γ n n'), forall k k', n = qNat k -> n' = qNat k' -> k = k').
Proof.
intros; apply NatRedEqInduction.
+ intros * ???? IH **; subst.
  assert (forall n, whnf (qNat n)) by now destruct n; eauto using whnf.
  apply IH; symmetry; eapply redtmwf_whnf; eauto.
+ intros [] []; cbn in *; congruence.
+ intros * ? IH [] [] **; cbn in *; try congruence.
  f_equal; apply IH; congruence.
+ intros * ? **; subst.
  assert (whne (qNat k)) by now eapply NeNf_whne.
  now eelim not_whne_qNat.
Qed.

Lemma NatPropEq_qNat_inj : forall Γ n n', NatPropEq Γ (qNat n) (qNat n') -> n = n'.
Proof.
intros.
eapply (snd (NatPropEq_qNat_inj_aux Γ)); tea; reflexivity.
Qed.

#[local] Lemma NatPropEq_quote_inv : forall Γ A t v v',
  [Γ |- tQuote A t :⤳*: v : tNat] -> NatPropEq Γ v v' ->
  ∑ t₀, isNf t t₀ × ((v = qNat (quote (erase t₀))) + (v = tQuote A t₀ × ~ closed0 t₀ × [Γ ||-NeNf v ≅ v' : tNat])).
Proof.
intros * Hr Heq.
assert (whnf v) by eauto using NatPropEq_whnf.
assert (Hbs : [tQuote A t ↓ v]).
{ eapply redalg_bigstep; [|tea]; now eapply redtm_red, tmr_wf_red. }
inversion Hbs; subst; exists t₀; split.
+ split; eauto using bigstep_dnf, bigstep_dredalg.
+ left; eauto.
+ split; eauto using bigstep_dnf, bigstep_dredalg.
+ inversion Heq; subst.
  right; prod_splitter; eauto.
Qed.

Lemma QuoteRed_inj : forall l Γ A A' t t'
  (rNat : [Γ ||-<l> tNat])
  (rA : [Γ ||-<l> A ≅ A'])
  (rt : [rA | Γ ||- t ≅ t : A])
  (rt' : [rA | Γ ||- t' ≅ t' : A]),
  [rNat | Γ ||- tQuote A t ≅ tQuote A' t' : tNat] ->
  [rA | Γ ||- t ≅ t' : A].
Proof.
intros * rt rt' rq.
assert (rΓ : [|- Γ]) by now escape; gtyping.
assert (rq' : [natRed (l := l) rΓ | Γ ||- tQuote A t ≅ tQuote A' t' : tNat]).
{ unshelve eapply irrLREq, rq; trivial. }
clear rNat rq; rename rq' into rq; cbn in *.
inversion rq; subst.
match goal with [ H : NatPropEq _ _ _ |- _ ] => assert (Hrt := H); eapply NatPropEq_quote_inv in Hrt; [|tea] end.
match goal with [ H : NatPropEq _ _ _ |- _ ] => assert (Hrt' := H); eapply symNatRedTmEq, NatPropEq_quote_inv in Hrt'; [|tea] end.
destruct Hrt as (t₀&?&[|(?&?&?)]); destruct Hrt' as (t'₀&?&[|(?&?&?)]); subst.
+ apply NatPropEq_qNat_inj, quote_inj in prop.
  eapply red_eqnf_complete; tea.
+ eelim not_whne_qNat; now eapply NeNf_whne, symNeNf.
+ eelim not_whne_qNat; now eapply NeNf_whne, symNeNf.
+ destruct (hasNf_redty rA) as [A₀].
  assert (rA' : [Γ ||-<l> A' ≅ A]) by now symmetry.
  destruct (hasNf_redty rA') as [A'₀]; clear rA'.
  destruct (snty_nf _ _ _ _ eq) as (v₀&w₀&?&?&?&?&Heq).
  assert (isNf (tQuote A t₀) (tQuote A₀ t₀)).
  { apply isNf_tQuote; eauto using isnf_dnf, dnf_isNf. }
  assert (isNf (tQuote A' t'₀) (tQuote A'₀ t'₀)).
  { apply isNf_tQuote; eauto using isnf_dnf, dnf_isNf. }
  assert (v₀ = tQuote A₀ t₀) by (now eapply isNf_irr); subst.
  assert (w₀ = tQuote A'₀ t'₀) by (now eapply isNf_irr); subst.
  assert (eqnf t₀ t'₀).
  { unfold eqnf in Heq; cbn in Heq; now injection Heq. }
  eapply red_eqnf_complete; tea.
Qed.

Lemma InjectRed : forall l Γ A A' t t' u u' e e' (rNat : [Γ ||-<l> tNat])
  (rA : [Γ ||-<l> A ≅ A'])
  (rId : [Γ ||-<l> tId A t u ≅ tId A' t' u'])
  (rIdN : [Γ ||-<l> tId tNat (tQuote A t) (tQuote A u) ≅ tId tNat (tQuote A' t') (tQuote A' u')]),
  [rA | Γ ||- t ≅ t' : A ≅ A'] ->
  [rA | Γ ||- u ≅ u' : A ≅ A'] ->
  [rIdN | Γ ||- e ≅ e' : tId tNat (tQuote A t) (tQuote A u) ≅ tId tNat (tQuote A' t') (tQuote A' u')] ->
  [Γ ||-<l> tInject A t u e ≅ tInject A' t' u' e' : tId A t u | rId].
Proof.
intros * rNat rA rId rIdN rt ru re.
pose (rIdN' := normRedId rIdN).
pose (rId' := normRedId rId).
assert (re' : [LRId' rIdN' | Γ ||- e ≅ e' : tId tNat (tQuote A t) (tQuote A u) ≅ tId tNat (tQuote A' t') (tQuote A' u')]).
{ unshelve eapply irrLREq, re; trivial. }
clear re; rename re' into re; cbn in *.
destruct re as [nfe nfe' ??? rnf]; cbn in *.
assert [Γ |- t' : A'] by (escape; gtyping).
assert [Γ |- u' : A'] by (escape; gtyping).
assert [Γ |- t ≅ t' : A] by now escape.
assert [Γ |- u ≅ u' : A] by now escape.
assert (rqt : [rNat | Γ ||- tQuote A t ≅ tQuote A' t' : tNat]).
{ unshelve eapply QuoteRed, rt. }
assert (rqu : [rNat | Γ ||- tQuote A u ≅ tQuote A' u' : tNat]).
{ unshelve eapply QuoteRed, ru. }
assert [Γ |- tInject A t u e ⤳* tInject A t u nfe : tId A t u].
{ eapply redtm_inject; escape; eauto using tmr_wf_red. }
assert [Γ |- tInject A' t' u' e' ⤳* tInject A' t' u' nfe' : tId A' t' u'].
{ eapply redtm_inject; escape; eauto using tmr_wf_red. gtyping. }
eapply redSubstTmEq; tea.
induction rnf as [X X' x x'|n n' []]; cbn in *.
+ assert (rqtu : [rNat | Γ ||- tQuote A t ≅ tQuote A u : tNat]).
  { eapply irrLREq; [reflexivity|]; transitivity x; [tea|]; now symmetry. }
  assert (rAA : [Γ ||-<l> A ≅ A]) by now eapply lrefl.
  assert (rtu : [rAA | Γ ||- t ≅ u : A ≅ A]).
  { unshelve eapply irrLREq, QuoteRed_inj, rqtu; eauto.
    - eapply lrefl, irrLREq; [reflexivity|tea].
    - eapply lrefl, irrLREq; [reflexivity|tea]. }
  assert [rNat | Γ ||- tQuote A t ≅ tQuote A u : tNat].
  { transitivity x; [|symmetry]; eapply irrLREq; tea; reflexivity. }
  assert [Γ |- tInject A t u (tRefl X x) ⤳* tRefl A t : tId A t u].
  { apply redtm_inject_eval; escape; cbn in *; eauto; now symmetry. }
  assert [Γ |- tInject A' t' u' (tRefl X' x') ⤳* tRefl A' t' : tId A' t' u'].
  { apply redtm_inject_eval; escape; cbn in *; eauto; [now symmetry|..].
    - transitivity (tQuote A t); [now symmetry|tea].
    - transitivity (tQuote A u); [now symmetry|tea]. }
  eapply redSubstTmEq; tea.
  unshelve eapply irrLRConv, reflCongRed; tea.
  - eapply IdRed; tea.
  - eapply IdRed; tea.
    now eapply lrefl.
+ eapply reflectLR.
  - apply ty_inject; escape; tea.
  - eapply ty_conv; [apply ty_inject; escape; tea|].
    * eapply ty_conv; tea.
    * symmetry; apply convty_Id; escape; tea.
  - apply convneu_inject; escape; tea.
Qed.

Lemma InjectEvalRed : forall l Γ A A' X t t' u u' x (rNat : [Γ ||-<l> tNat])
  (rA : [Γ ||-<l> A ≅ A'])
  (rX : [Γ ||-<l> X ≅ tNat])
  (rId : [Γ ||-<l> tId A t u ≅ tId A' t' u']),
  [rA | Γ ||- t ≅ t' : A ≅ A'] ->
  [rA | Γ ||- u ≅ u' : A ≅ A'] ->
  [rNat | Γ ||- x ≅ tQuote A t : tNat] ->
  [rNat | Γ ||- x ≅ tQuote A u : tNat] ->
  [rId | Γ ||- tInject A t u (tRefl X x) ≅ tRefl A' t' : tId A t u ≅ tId A' t' u'].
Proof.
intros * rX rId rt ru rxl rxr.
eapply (redSubstLeftTmEq (u := tRefl A t)).
+ assert (rqtu : [rNat | Γ ||- tQuote A t ≅ tQuote A u : tNat]).
  { transitivity x; [|tea]; now symmetry. }
  assert (rAA : [Γ ||-<l> A ≅ A]) by now eapply lrefl.
  assert (rtu : [rAA | Γ ||- t ≅ u : A]).
  { eapply QuoteRed_inj; [..|tea].
    - unshelve (eapply irrLREq, lrefl; [reflexivity|tea]).
    - unshelve (eapply irrLREq, lrefl; [reflexivity|tea]). }
 unshelve (eapply irrLRConv, reflCongRed; [|tea]).
  - now unshelve eapply IdRed.
  - unshelve eapply IdRed; [now eapply lrefl|..].
    * now unshelve eapply irrLREq, lrefl, rt.
    * now unshelve eapply irrLREq, rtu.
+ eapply redtm_inject_eval; escape; tea.
  now eapply ty_conv.
Qed.

End InjectRed.

Section InjectValid.

Context `{GenericTypingProperties}.
Context {SN : SNTypingProperties ta _ _ _ _ _}.
Context {SNC : SNCompleteTypingProperties ta _ _ _ _ _ _}.

Section Cong.

Context {Γ Γ' l} {A A' t t' u u' e e' : term}
  (vΓ : [||-v Γ ≅ Γ'])
  (vNat : [Γ ||-v<l> tNat ≅ tNat | vΓ])
  (vId : [Γ ||-v<l> tId tNat (tQuote A t) (tQuote A u) ≅ tId tNat (tQuote A' t') (tQuote A' u') | vΓ])
  (vId0 : [Γ ||-v<l> tId A t u ≅ tId A t u | vΓ])
  (vA : [Γ ||-v<l> A ≅ A' | vΓ])
  (vt : [Γ ||-v<l> t ≅ t' : A | vΓ | vA ])
  (vu : [Γ ||-v<l> u ≅ u' : A | vΓ | vA ])
  (ve : [Γ ||-v<l> e ≅ e' : tId tNat (tQuote A t) (tQuote A u) | vΓ | vId ]).

Lemma InjectValid :
  [Γ ||-v< l > tInject A t u e ≅ tInject A' t' u' e' : tId A t u | vΓ | vId0].
Proof.
econstructor; intros *; cbn in *.
instValid Vσσ'.
unshelve eapply irrLR, InjectRed; [shelve|..]; tea.
cbn in *; eapply IdValid; tea.
Qed.

End Cong.

Section Eval.

Context {Γ Γ' l} {A X t u x : term}
  (vΓ : [||-v Γ ≅ Γ'])
  (vNat : [Γ ||-v<l> tNat ≅ tNat | vΓ])
  (vId0 : [Γ ||-v<l> tId A t u ≅ tId A t u | vΓ])
  (vA : [Γ ||-v<l> A ≅ A | vΓ])
  (vX : [Γ ||-v<l> X ≅ tNat | vΓ])
  (vt : [Γ ||-v<l> t : A | vΓ | vA ])
  (vu : [Γ ||-v<l> u : A | vΓ | vA ])
  (vxl : [Γ ||-v<l> x ≅ tQuote A t : tNat | vΓ | vNat])
  (vxr : [Γ ||-v<l> x ≅ tQuote A u : tNat | vΓ | vNat]).

Lemma InjectEvalValid :
  [Γ ||-v< l > tInject A t u (tRefl X x) ≅ tRefl A t : tId A t u | vΓ | vId0].
Proof.
econstructor; intros *; cbn in *.
instValid Vσσ'; cbn in *.
unshelve eapply (InjectEvalRed _ _ A[σ] A[σ'] X[σ] t[σ] t[σ'] u[σ] u[σ']); tea.
+ now eapply irrLREq; tea.
+ now eapply irrLREq; tea.
Qed.

End Eval.

End InjectValid.
