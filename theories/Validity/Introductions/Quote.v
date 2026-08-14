From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Nat.
From LogRel.Validity Require Import Validity Irrelevance Properties.
From LogRel.Validity Require Import Universe Nat SimpleArr.

Section QuoteRed.

Context `{GenericTypingProperties}.

Lemma qNatRedEq0 : forall {Γ} (n : nat), [|- Γ] -> NatPropEq Γ (qNat n) (qNat n).
Proof.
intros Γ n wfΓ.
induction n; cbn.
+ constructor.
+ constructor.
  assert ([Γ |-[ ta ] qNat n :⤳*: qNat n : tNat]).
  { constructor; [now apply ty_qNat|].
    now apply redtm_refl, ty_qNat. }
  eexists (qNat n) (qNat n); eauto.
  now apply convtm_qNat.
Qed.

Lemma qNatRedEq {Γ l} (n : nat) (rNat : [Γ ||-<l> tNat]) : [rNat | Γ ||- qNat n ≅ qNat n : tNat].
Proof.
assert [|- Γ] by now eapply wfc_wft, escape.
unshelve (eapply irrLREq; [reflexivity|]); [|now apply natRed|].
induction n.
+ unshelve eapply zeroRed.
+ cbn [qNat]; now eapply succRed.
Qed.

Context {SN : SNTypingProperties ta _ _ _ _ _}.

Lemma QuoteEvalRed : forall l Γ A t (rNat : [Γ ||-<l> tNat]) (rA : [Γ ||-<l> A]),
  [Γ ||-<l> t ≅ t : A | rA] -> dnf t -> closed0 t ->
  [Γ ||-<l> tQuote A t ≅ qNat (quote (erase t)) : tNat | rNat].
Proof.
intros.
eapply (redSubstTmEq (ur := qNat (quote (erase t)))).
+ eapply qNatRedEq.
+ apply redtm_evalquote; tea; now escape.
+ apply redtm_refl, ty_qNat; escape; gtyping.
Qed.

Lemma QuoteRed : forall l Γ A A' t t' (rNat : [Γ ||-<l> tNat])
  (rA : [Γ ||-<l> A ≅ A']),
  [rA | Γ ||- t ≅ t' : A ≅ A'] ->
  [Γ ||-<l> tQuote A t ≅ tQuote A' t' : tNat | rNat ].
Proof.
intros * rtt'.
assert (rΓ : [|- Γ]) by now eapply wfc_wft, escape.
unshelve (eapply irrLREq; [reflexivity|]); [|now apply natRed|].
assert [Γ |- A] by now escape.
assert [Γ |- A'] by now escape.
assert [Γ |- A ≅ A'] by now escape.
assert (re : [Γ |- t ≅ t' : A]) by now escape.
apply snty_nf in re.
destruct re as (l₀&r₀&[]&[]&?&?&?).
remember (is_closedn 0 l₀) as b eqn:Hc; symmetry in Hc.
assert (Hc' : is_closedn 0 r₀ = b).
{ erewrite eqnf_is_closedn; [tea|now apply Symmetric_eqnf]. }
destruct b.
- pose (q := qNat (quote (erase l₀))).
  exists q q.
  + constructor; [now apply ty_qNat|].
    transitivity (tQuote A l₀).
    * apply redtm_quote; tea.
    * apply redtm_evalquote; tea.
      now eapply urefl.
  + constructor; [now apply ty_qNat|].
    transitivity (tQuote A' r₀).
    * apply redtm_quote; tea.
      now eapply convtm_conv.
    * unfold q; rewrite e.
      apply redtm_evalquote; tea.
      eapply convtm_conv; [|tea].
      now eapply urefl.
  + now apply convtm_qNat.
  + now apply qNatRedEq0.
- assert [Γ |-[ ta ] tQuote A l₀ ~ tQuote A' r₀ : tNat].
  { apply convneu_quote; tea.
    + transitivity t; [now symmetry|].
      transitivity t'; tea; now escape.
    + unfold closed0; destruct is_closedn; cbn; congruence.
    + unfold closed0; destruct is_closedn; cbn; congruence. }
  exists (tQuote A l₀) (tQuote A' r₀).
  + constructor; [now eapply ty_quote, urefl|].
    apply redtm_quote; tea.
  + assert [Γ |-[ ta ] t' ≅ r₀ : A'].
    { eapply convtm_conv; tea. }
    constructor; [now eapply ty_quote, urefl|].
    apply redtm_quote; tea.
  + apply convtm_convneu; tea; constructor.
  + constructor; constructor; tea.
    * apply ty_quote; [tea|now eapply urefl].
    * apply ty_quote; [tea|].
      eapply convtm_conv; [|tea].
      now eapply urefl.
Qed.

End QuoteRed.

Section QuoteCongValid.

Context `{GenericTypingProperties}.
Context {SN : SNTypingProperties ta _ _ _ _ _}.

Context {Γ l} {A A' t t' : term}
  (vΓ : [||-v Γ])
  (vA : [Γ ||-v<l> A ≅ A' | vΓ])
  (vNat : [Γ ||-v<l> tNat | vΓ]).

Lemma QuoteCongValid :
  [Γ ||-v<l> t ≅ t' : A | vΓ | vA] ->
  [Γ ||-v<l> tQuote A t ≅ tQuote A' t' : tNat | vΓ | vNat].
Proof.
intros [vte]; constructor.
intros Δ tΔ σ σ' vσσ'; cbn.
now unshelve eapply QuoteRed, vte.
Qed.

End QuoteCongValid.

Section QuoteEvalValid.

Context `{GenericTypingProperties}.
Context {SN : SNTypingProperties ta _ _ _ _ _}.

Context {Γ l} {A t : term}
  (vΓ : [||-v Γ])
  (vA : [Γ ||-v<l> A | vΓ])
  (vNat : [Γ ||-v<l> tNat | vΓ]).

Lemma QuoteEvalValid :
  [Γ ||-v<l> t ≅ t : A | vΓ | vA] ->
  dnf t -> closed0 t ->
  [Γ ||-v<l> tQuote A t ≅ qNat (quote (erase t)) : tNat | vΓ | vNat].
Proof.
intros [vte]; constructor.
intros Δ tΔ σ σ' vσσ'; cbn.
instValid vσσ'.
rewrite quote_subst; [|tea].
assert (Hrw : erase t[σ'] = erase t[σ]); [|rewrite Hrw].
{ now rewrite !erase_is_closed0_subst_id. }
unshelve eapply QuoteEvalRed; eauto using dnf_closed0_subst, closed0_subst.
Qed.

End QuoteEvalValid.
