From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.Syntax Require Import Confluence Standardisation.
From LogRel.LogicalRelation Require Import Properties.
From LogRel.LogicalRelation.Introductions Require Import Universe Nat Sigma SimpleArr Id.
From LogRel.LogicalRelation.Introductions Require Import EqComplete.
From LogRel.Validity Require Import Validity Irrelevance Properties.
From LogRel.Validity Require Import Universe Nat SimpleArr.

Set Universe Polymorphism.
Set Printing Primitive Projection Parameters.

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
assert (∑ t₀, isNf t t₀) as [t₀ Ht] by now eapply hasNf_red.
assert (∑ u₀, isNf u u₀) as [u₀ Hu] by now eapply hasNf_red.
unshelve eapply red_eqnf_complete; [..|tea|tea|]; tea.
assert (Hr : [tDecide A t u ⤳* tZero]).
{ remember (tDecide A t u) as lhs; remember tZero as rhs.
  cbn in rdec; destruct rdec as [? ? nfl nfr ? ? ? spec]; subst.
  assert (nfr = tZero); [|subst].
  { symmetry; apply red_whnf; [|constructor].
    now eapply redtm_sound, tmr_wf_red. }
  inversion spec; subst; [now eapply redtm_sound, tmr_wf_red|].
  enough (whne tZero) as Hne by inversion Hne.
  eapply convneu_whne; symmetry; now eapply NeNf.conv. }
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

Lemma ReflectEval : forall Γ l A A' X t t' u u' x (rΓ : [|- Γ])
  (rNat := natRed (l := l) rΓ)
  (rA : [Γ ||-<l> A ≅ A'])
  (rX : [Γ ||-<l> X ≅ tNat])
  (rId : [Γ ||-<l> tId A t u ≅ tId A' t' u'])
  (rt : [rA | Γ ||- t ≅ t' : A ≅ A'])
  (ru : [rA | Γ ||- u ≅ u' : A ≅ A'])
  (rx1 : [rNat | Γ ||- x ≅ tZero : tNat])
  (rx2 : [rNat | Γ ||- x ≅ tDecide A t u : tNat]),
  [rId | Γ ||- tReflect A t u (tRefl X x) ≅ tRefl A' t' : tId A t u ≅ tId A' t' u'].
Proof.
intros.
assert [Γ |- x : X].
{ apply (ty_conv (A' := tNat)); escape; tea; now symmetry. }
assert ([Γ |- tReflect A t u (tRefl X x) ⤳* tRefl A t : tId A t u]).
{ apply redtm_reflect_eval; escape; tea. }
assert [rA | Γ ||- t ≅ u : A ≅ A'].
{ unshelve eapply DecideZeroRedComplete; tea.
  + now eapply lrefl.
  + now eapply lrefl.
  + transitivity x; [|tea].
    now symmetry. }
assert [Γ |-[ ta ] t' : A'].
{ eapply ty_conv; now escape. }
assert [Γ |-[ ta ] u' : A'].
{ eapply ty_conv; now escape. }
assert [Γ ||-<l> tId A t t ≅ tId A' t' t'].
{ now eapply IdRed. }
assert [Γ ||-<l> tId A t t ≅ tId A t u].
{ unshelve eapply IdRed.
  + now eapply lrefl.
  + now eapply irrLREq, lrefl, rt.
  + eapply irrLREq; [|tea]; reflexivity. }
assert [Γ ||-<l> tId A' t' u' ≅ tId A' t' t'].
{ unshelve eapply IdRed.
  + now eapply urefl.
  + now eapply irrLRConv, urefl, rt.
  + transitivity t; [|now unshelve eapply irrLRConv, rt].
    symmetry; transitivity u; [|now unshelve eapply irrLRConv, ru].
    now eapply irrLRConv. }
enough [rId | Γ ||- tRefl A t ≅ tRefl A' t' : tId A t u ≅ tId A' t' u'].
{ eapply redSubstTmEq; tea; apply redtmwf_refl.
  apply (ty_conv (A' := tId A' t' t')); [|escape; now symmetry].
  apply ty_refl; escape; tea. }
unshelve eapply irrLRConv, reflCongRed; tea.
Qed.

Section ReflectCongValid.

  Context {Γ Γ' l} {A A' t t' u u' e e' : term}
    (vΓ : [||-v Γ ≅ Γ'])
    (vNat : [Γ ||-v<l> tNat ≅ tNat | vΓ])
    (vId : [Γ ||-v<l> tId tNat (tDecide A t u) tZero ≅ tId tNat (tDecide A' t' u') tZero | vΓ])
    (vId0 : [Γ ||-v<l> tId A t u ≅ tId A t u | vΓ])
    (vA : [Γ ||-v<l> A ≅ A' | vΓ])
    (vt : [Γ ||-v<l> t ≅ t' : A | vΓ | vA ])
    (vu : [Γ ||-v<l> u ≅ u' : A | vΓ | vA ])
    (ve : [Γ ||-v<l> e ≅ e' : tId tNat (tDecide A t u) tZero | vΓ | vId ])
  .

  Lemma ReflectCongValid :
    [Γ ||-v<l> tReflect A t u e ≅ tReflect A' t' u' e' : _ | vΓ | vId0].
  Proof.
    econstructor; intros *; cbn.
    instValid Vσσ'.
    unshelve eapply irrLR, ReflectRedEq; [shelve|..].
    + cbn; eapply IdRed; tea.
    + tea.
    + tea.
    + tea.
    + tea.
    + now eapply irrLR.
  Qed.

End ReflectCongValid.

Section ReflectEvalValid.

  Context {Γ Γ' l} {A X t u x : term}
    (vΓ : [||-v Γ ≅ Γ'])
    (vNat : [Γ ||-v<l> tNat | vΓ])
    (vId0 : [Γ ||-v<l> tId A t u | vΓ])
    (vA : [Γ ||-v<l> A | vΓ])
    (vX : [Γ ||-v<l> X ≅ tNat | vΓ])
    (vx1 : [Γ ||-v<l> x ≅ tDecide A t u : tNat | vΓ | vNat])
    (vx2 : [Γ ||-v<l> x ≅ tZero : tNat | vΓ | vNat])
    (vt : [Γ ||-v<l> t : A | vΓ | vA ])
    (vu : [Γ ||-v<l> u : A | vΓ | vA ])
  .

  Lemma ReflectEvalValid :
    [Γ ||-v<l> tReflect A t u (tRefl X x) ≅ tRefl A t : tId A t u | vΓ | vId0].
  Proof.
    econstructor; intros *; cbn.
    instValid Vσσ'; simpl in *.
    unshelve eapply irrLR, ReflectEval; tea.
    + now eapply irrLR.
    + now eapply irrLR.
  Qed.

End ReflectEvalValid.

End Reflect.
