From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Nat.
From LogRel.Validity Require Import Validity Irrelevance Properties.
From LogRel.Validity Require Import Universe Nat SimpleArr.

(*
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Computation Notations Context Closed NormalForms NormalEq Weakening UntypedReduction
  GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Escape Reflexivity Neutral Weakening Irrelevance Application Reduction Transitivity NormalRed.
From LogRel.Substitution Require Import Irrelevance Properties SingleSubst.
From LogRel.Substitution.Introductions Require Import Universe Nat SimpleArr.
*)

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

Section Utils. (* TODO: move me somewhere sensible *)

Context `{GenericTypingProperties}.

Lemma LRTmEqRed_l : forall Γ l A t u (rA : [Γ ||-<l> A]),
  [rA | Γ ||- t ≅ u : A] -> [rA | Γ ||- t : A].
Proof.
intros; now eapply lreflRedTm.
Qed.

Lemma LRTmEqRed_r : forall Γ l A t u (rA : [Γ ||-<l> A]),
  [rA | Γ ||- t ≅ u : A] -> [rA | Γ ||- u : A].
Proof.
intros; now eapply ureflRedTm.
Qed.

End Utils.

Section QDnf.

Lemma dnf_closed_subst_eqnf : forall t t₀ σ,
  closed0 t -> dnf t -> [t[σ] ⇶* t₀] -> eqnf t[σ] t₀.
Proof.
intros; unfold eqnf.
rewrite !erase_unannot_etared; f_equal.
assert (Hrw : unannot t[σ] = unannot t) by now apply unannot_closed0_subst.
eapply gredalg_unannot_dnf_id; [|tea].
rewrite Hrw; now apply dnf_unannot.
Qed.

Lemma eqnf_closed0_subst : forall t σ, closed0 t -> eqnf t[σ] t.
Proof.
intros.
unfold eqnf.
rewrite !erase_unannot_etared; f_equal.
now apply unannot_closed0_subst.
Qed.

End QDnf.

Section QuoteValid.

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

Lemma nf_eval : forall {l Γ A t} {vA : [Γ ||-<l> A]}, [vA | Γ ||- t : A] ->
  ∑ r, [t ⇶* r] × dnf r × [Γ |- t ≅ r : A].
Proof.
intros l Γ A t vT vt.
destruct SN as [sn].
apply escapeEqTerm, sn in vt.
destruct vt as (t₀&u₀&[]&[]&?&?&?).
exists t₀; try now prod_splitter.
Qed.

  Lemma QuoteEvalRedEq : forall Γ l t t₀ (rNat : [Γ ||-<l> tNat]),
    [Γ |- t ≅ t₀ : tPNat] -> [t ⇶* t₀] -> dnf t₀ -> closed0 t₀ -> eqnf t t₀ ->
    [Γ ||-<l> tQuote t ≅ qNat (quote (erase t)) : tNat | rNat ].
  Proof.
  intros.
  eapply (redSubstTmEq (ur := qNat (quote (erase t)))).
  + eapply qNatRedEq.
  + transitivity (tQuote t₀).
    - now apply redtm_quote.
    - replace (erase t) with (erase t₀).
      apply redtm_evalquote; tea.
      now eapply urefl.
  + apply redtm_refl, ty_qNat; gen_typing.
  Qed.

  Lemma QuoteRedEq : forall Γ l t t' (rNat : [Γ ||-<l> tNat]),
    [Γ |- t ≅ t' : arr tNat tNat] ->
    [Γ ||-<l> tQuote t ≅ tQuote t' : tNat | rNat ].
  Proof.
  intros * rtt'.
  assert (rΓ : [|- Γ]) by now eapply wfc_wft, escape.
  unshelve (eapply irrLREq; [reflexivity|]); [|now apply natRed|].
  assert (re : [Γ |- t ≅ t' : arr tNat tNat]) by eauto.
  apply snty_nf in re.
  destruct re as (l₀&r₀&[]&[]&?&?&?).
  remember (is_closedn 0 l₀) as b eqn:Hc; symmetry in Hc.
  assert (Hc' : is_closedn 0 r₀ = b).
  { erewrite eqnf_is_closedn; [tea|now apply Symmetric_eqnf]. }
  destruct b.
  - pose (q := qNat (quote (erase l₀))).
    exists q q.
    + constructor; [now apply ty_qNat|].
      transitivity (tQuote l₀).
      * apply redtm_quote; tea.
      * apply redtm_evalquote; tea.
        now eapply urefl.
    + constructor; [now apply ty_qNat|].
      transitivity (tQuote r₀).
      * apply redtm_quote; tea.
      * unfold q; rewrite e.
        apply redtm_evalquote; tea.
        now eapply urefl.
    + now apply convtm_qNat.
    + now apply qNatRedEq0.
  - assert [Γ |-[ ta ] tQuote l₀ ~ tQuote r₀ : tNat].
    { apply convneu_quote; tea.
      + transitivity t; [now symmetry|].
        transitivity t'; tea.
      + unfold closed0; destruct is_closedn; cbn; congruence.
      + unfold closed0; destruct is_closedn; cbn; congruence. }
    exists (tQuote l₀) (tQuote r₀).
    + constructor; [now eapply ty_quote, urefl|].
      apply redtm_quote; tea.
    + constructor; [now eapply ty_quote, urefl|].
      apply redtm_quote; tea.
    + apply convtm_convneu; tea; constructor.
    + constructor; constructor; tea.
      * apply ty_quote; now eapply urefl.
      * apply ty_quote; now eapply urefl.
  Qed.

  Lemma QuoteRed : forall Γ l t (rNat : [Γ ||-<l> tNat]),
    [Γ |- t ≅ t : arr tNat tNat] ->
    [Γ ||-<l> tQuote t : tNat | rNat ].
  Proof.
    intros.
    now eapply LRTmEqRed_l, QuoteRedEq.
  Qed.


  Context {Γ l t} (vΓ : [||-v Γ])
    (vNat := natValid (l := l) vΓ)
    (vArr := simpleArrValid vΓ vNat vNat)
    (vt : [ Γ ||-v< l > t : arr tNat tNat | vΓ | vArr ])
  .

Lemma evalQuoteValid : dnf t -> closed0 t ->
  [Γ ||-v<l> tQuote t ≅ qNat (quote (erase t)) : tNat | vΓ | vNat].
Proof.
destruct SN as [sn].
econstructor.
intros Δ tΔ σ σ' vσσ'.
destruct vt as [vte].
unshelve eassert (vte0 := vte Δ tΔ σ σ' vσσ').
apply escapeEqTerm, sn in vte0 as (t₀&u₀&[]&[]&?&?&?); cbn in *.
assert [Δ |-[ ta ] t[σ] : tProd tNat tNat].
{ unshelve eapply escapeTerm, vte; tea. }
pose (q := qNat (quote (erase t₀))).
exists q q; cbn in *.
- constructor; [now apply ty_qNat|].
  transitivity (tQuote t₀).
  + apply redtm_quote; tea.
  + apply redtm_evalquote; tea.
    * now eapply urefl.
    * eapply dredalg_closed0; [tea|].
      now eapply closed0_subst.
- constructor; [now apply ty_qNat|].
  rewrite quote_subst; [|tea].
  replace (erase t[σ']) with (erase t₀); [now apply redtm_refl, ty_qNat|].
  replace (erase t₀) with (erase u₀) by now symmetry; apply e.
  symmetry; now apply dnf_closed_subst_eqnf.
- now apply convtm_qNat.
- now apply qNatRedEq0.
Qed.

End QuoteValid.

Section QuoteCongValid.

Context `{GenericTypingProperties}.
Context {SN : SNTypingProperties ta _ _ _ _ _}.

Context {Γ l} {t t' : term}
  (vΓ : [||-v Γ])
  (vNat := natValid (l := l) vΓ)
  (vArr := simpleArrValid vΓ vNat vNat).

Lemma QuoteCongValid :
  [Γ ||-v<l> t ≅ t' : arr tNat tNat | vΓ | vArr] ->
  [Γ ||-v<l> tQuote t ≅ tQuote t' : tNat | vΓ | vNat].
Proof.
intros [vte]; constructor.
intros Δ tΔ σ σ' vσσ'.
assert [Δ |- t[σ] : arr tNat tNat].
{ unshelve eapply escapeTerm, vte; tea. }
assert [Δ |- t'[σ'] : arr tNat tNat].
{ unshelve eapply escapeTerm, symRedTm', vte; tea.
  now eapply urefl. }
unshelve eapply QuoteRedEq, escapeEqTerm, vte; cbn; tea.
Qed.

End QuoteCongValid.
