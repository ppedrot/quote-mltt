From Coq Require Import CRelationClasses ssrbool.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Computation Notations Context Closed
  NormalForms NormalEq Weakening UntypedReduction Confluence.

(* Standardisation *)

Reserved Notation "[ t →s u ]" (at level 0, t, u at level 50).
Reserved Notation "[ t →w u ]" (at level 0, t, u at level 50).
Reserved Notation "[ t →w* u ]" (at level 0, t, u at level 50).

Inductive red_tag :=
| RedWh
| RedWhStar
| RedStd.

Inductive sred : red_tag -> term -> term -> Set :=
| sred_rel {w n} : [w →w* tRel n] -> [w →s tRel n]
| sred_sort {w s} : [w →w* tSort s] -> [w →s tSort s]
| sred_prod {w A A' B B'} : [w →w* tProd A B] -> [A →s A'] -> [B →s B'] -> [w →s tProd A' B']
| sred_lambda {w A A' t t'} : [w →w* tLambda A t] -> [t →s t'] -> [w →s tLambda A' t']
| sred_app {w t t' u u'} : [w →w* tApp t u] -> [t →s t'] -> [u →s u'] -> [w →s tApp t' u']
| sred_nat {w} : [w →w* tNat] -> [w →s tNat]
| sred_zero {w} : [w →w* tZero] -> [w →s tZero]
| sred_succ {w t t'} : [w →w* tSucc t] -> [t →s t'] -> [w →s tSucc t']
| sred_natelim {w P P' hz hz' hs hs' t t'} :
  [w →w* tNatElim P hz hs t] ->
  [P →s P'] -> [hz →s hz'] -> [hs →s hs'] -> [t →s t'] -> [w →s tNatElim P' hz' hs' t']
| sred_empty {w} : [w →w* tEmpty] -> [w →s tEmpty]
| sred_emptyelim {w P P' t t'} : [w →w* tEmptyElim P t] -> [P →s P'] -> [t →s t'] -> [w →s tEmptyElim P' t']
| sred_sig {w A A' B B'} : [w →w* tSig A B] -> [A →s A'] -> [B →s B'] -> [w →s tSig A' B']
| sred_pair {w A A' B B' a a' b b'} : [w →w* tPair A B a b] -> [a →s a'] -> [b →s b'] ->
  [w →s tPair A' B' a' b']
| sred_fst {w t t'} : [w →w* tFst t] -> [t →s t'] -> [w →s tFst t']
| sred_snd {w t t'} : [w →w* tSnd t] -> [t →s t'] -> [w →s tSnd t']
| sred_id {w A A' t t' u u'} : [w →w* tId A t u] -> [A →s A'] -> [t →s t'] -> [u →s u'] -> [w →s tId A' t' u']
| sred_idrefl {w A A' t t'} : [w →w* tRefl A t] -> [A →s A'] -> [t →s t'] -> [w →s tRefl A' t']
| sred_idelim {w A A' x x' P P' hr hr' y y' e e'} : [w →w* tIdElim A x P hr y e] ->
  [A →s A'] -> [x →s x'] -> [P →s P'] -> [hr →s hr'] -> [y →s y'] -> [e →s e'] ->
  [w →s tIdElim A' x' P' hr' y' e']
| sred_quote {w t t'} : [w →w* tQuote t] -> [t →s t'] -> [w →s tQuote t']
| sred_step {w t t' u u'} : [w →w* tStep t u] -> [t →s t'] -> [u →s u'] -> [w →s tStep t' u']
| sred_reflect {w t t' u u'} : [w →w* tReflect t u] -> [t →s t'] -> [u →s u'] -> [w →s tReflect t' u']

| wred_BRed {A a t} :
  [tApp (tLambda A t) a →w t[a..]]
| wred_appSubst {t u a} :
  [t →w u] ->
  [tApp t a →w tApp u a]
| wred_natElimSubst {P hz hs n n'} :
  [n →w n'] ->
  [tNatElim P hz hs n →w tNatElim P hz hs n']
| wred_natElimZero {P hz hs} :
  [tNatElim P hz hs tZero →w hz]
| wred_natElimSucc {P hz hs n} :
  [tNatElim P hz hs (tSucc n) →w tApp (tApp hs n) (tNatElim P hz hs n)]
| wred_emptyElimSubst {P e e'} :
  [e →w e'] ->
  [tEmptyElim P e →w tEmptyElim P e']
| wred_fstSubst {p p'} :
  [p →w p'] ->
  [tFst p →w tFst p']
| wred_fstPair {A B a b} :
  [tFst (tPair A B a b) →w a]
| wred_sndSubst {p p'} :
  [p →w p'] ->
  [tSnd p →w tSnd p']
| wred_sndPair {A B a b} :
  [tSnd (tPair A B a b) →w b]
| wred_idElimRefl {A x P hr y A' z} :
  [tIdElim A x P hr y (tRefl A' z) →w hr]
| wred_idElimSubst {A x P hr y e e'} :
  [e →w e'] ->
  [tIdElim A x P hr y e →w tIdElim A x P hr y e']
| wred_termEvalAlg {t t'} :
  [t →s t'] ->
  dnf t' ->
  closed0 t' ->
  [tQuote t →w qNat (model.(quote) (erase t'))]
| wred_termStepAlg {t t' u u' n k k'} :
  [t →s t'] ->
  [u →s qNat u'] ->
  dnf t' ->
  closed0 t' ->
  murec (fun k => eval true (tApp (erase t') (qNat u')) k) k = Some (k', qNat n) ->
  [tStep t u →w qNat k']
| wred_termReflectAlg {t t' u u' n k k'} :
  [t →s t'] ->
  [u →s qNat u'] ->
  dnf t' ->
  closed0 t' ->
  murec (fun k => eval true (tApp (erase t') (qNat u')) k) k = Some (k', qNat n) ->
  [tReflect t u →w qEvalTm k' n]

| wred_refl {t} : [t →w* t]
| wred_trans {t u r} :
  [t →w u] -> [u →w* r] -> [t →w* r]

where "[ t →s u ]" := (sred RedStd t u)
and "[ t →w u ]" := (sred RedWh t u)
and "[ t →w* u ]" := (sred RedWhStar t u)
.

#[local] Lemma redalg_refl : forall t, [t ⤳* t].
Proof.
reflexivity.
Qed.

Lemma sred_refl : forall t, [t →s t].
Proof.
induction t; eauto using sred.
Qed.

Lemma wsred_step : forall t u, [t →w u] -> [t →w* u].
Proof.
intros; eauto using sred.
Qed.

Lemma wsred_trans : forall t u r, [t →w* u] -> [u →w* r] -> [t →w* r].
Proof.
intros t u r Hl Hr.
remember RedWhStar as tag eqn:Htag in *.
revert r Hr; induction Hl; try discriminate Htag; eauto using sred.
Qed.

#[local] Instance PreOrder_wsred : CRelationClasses.PreOrder (sred RedWhStar).
Proof.
split.
+ intros ?; apply wred_refl.
+ intros ??? **; now eapply wsred_trans.
Qed.

Lemma redalg_sred_trans : forall t u r, [t →w* u] -> [u →s r] -> [t →s r].
Proof.
intros t u r Hr Hs.
remember RedStd as tag eqn:Htag in Hs.
revert t Hr.
induction Hs; try discriminate Htag.
all: try now (intros; econstructor; eauto using sred, wsred_trans).
Qed.

Lemma sred_ren : forall tag t t' ρ, sred tag t t' -> sred tag t⟨ρ⟩ t'⟨ρ⟩.
Proof.
intros tag t t' ρ Hr; revert ρ; induction Hr; intros ρ; cbn in *; eauto using sred.
+ replace t[a..]⟨ρ⟩ with t⟨upRen_term_term ρ⟩[a⟨ρ⟩..] by now bsimpl.
  constructor.
+ rewrite quote_ren; [|tea].
  constructor; eauto using dnf_ren, closed0_ren.
+ rewrite !qNat_ren.
  erewrite <- (erase_is_closed0_ren_id _ ρ) in e; tea.
  econstructor; [..|tea]; eauto using dnf_ren, closed0_ren.
  now rewrite <- (qNat_ren _ ρ).
+ rewrite qEvalTm_ren.
  erewrite <- (erase_is_closed0_ren_id _ ρ) in e; tea.
  econstructor; [..|tea]; eauto using dnf_ren, closed0_ren.
  now rewrite <- (qNat_ren _ ρ).
Qed.

Lemma sred_subst_gen : forall tag t t', sred tag t t' ->
  match tag with
  | RedWh => forall σ, [t[σ] →w t'[σ]]
  | RedWhStar => forall σ, [t[σ] →w* t'[σ]]
  | RedStd => forall σ σ' (Hσ : forall n, [σ n →s σ' n]), [t[σ] →s t'[σ']]
  end.
Proof.
assert (Hup : forall σ σ',
  (forall n : nat, [σ n →s σ' n]) -> forall n : nat, [up_term_term σ n →s up_term_term σ' n]).
{ intros σ σ' Hσ []; [apply sred_refl|].
  cbn; unfold funcomp; now apply sred_ren. }
induction 1; cbn in *; intros.
all: try eauto 10 using sred, wsred_step.
+ eapply redalg_sred_trans; [|apply Hσ]; eauto.
+ replace t[a..][σ] with t[up_term_term σ][a[σ]..] by now bsimpl.
  constructor.
+ rewrite quote_subst; [|tea].
  constructor; eauto using closed0_subst, dnf_closed0_subst, sred_refl.
+ rewrite !qNat_subst.
  erewrite <- (erase_is_closed0_subst_id _ ) in e; tea.
  econstructor; [..|tea]; eauto using closed0_subst, dnf_closed0_subst, sred_refl.
  rewrite <- (qNat_subst _ σ); eauto using sred_refl.
+ rewrite qEvalTm_subst.
  erewrite <- (erase_is_closed0_subst_id _ ) in e; tea.
  econstructor; [..|tea]; eauto using closed0_subst, dnf_closed0_subst, sred_refl.
  rewrite <- (qNat_subst _ σ); eauto using sred_refl.
Qed.

Lemma sred_subst : forall t t' σ σ', [t →s t'] -> (forall n, [σ n →s σ' n]) ->
  [t[σ] →s t'[σ']].
Proof.
intros; now apply (sred_subst_gen RedStd).
Qed.

Lemma sred_subst1 : forall t t' u u', [t →s t'] -> [u →s u'] -> [t[u..] →s t'[u'..]].
Proof.
intros; apply sred_subst; tea.
intros []; [tea|apply sred_refl].
Qed.

Lemma wsred_app : forall t t' u, [t →w* t'] -> [tApp t u →w* tApp t' u].
Proof.
intros * Hr.
remember RedWhStar as tag eqn:Htag in *.
induction Hr; try discriminate Htag.
+ reflexivity.
+ econstructor; [|eauto].
  now constructor.
Qed.

Lemma wsred_natElim : forall P hs hz t t', [t →w* t'] -> [tNatElim P hs hz t →w* tNatElim P hs hz t'].
Proof.
intros * Hr.
remember RedWhStar as tag eqn:Htag in *.
induction Hr; try discriminate Htag.
+ reflexivity.
+ econstructor; [|eauto].
  now constructor.
Qed.

Lemma wsred_fst : forall t t', [t →w* t'] -> [tFst t →w* tFst t'].
Proof.
intros * Hr.
remember RedWhStar as tag eqn:Htag in *.
induction Hr; try discriminate Htag.
+ reflexivity.
+ econstructor; [|eauto].
  now constructor.
Qed.

Lemma wsred_snd : forall t t', [t →w* t'] -> [tSnd t →w* tSnd t'].
Proof.
intros * Hr.
remember RedWhStar as tag eqn:Htag in *.
induction Hr; try discriminate Htag.
+ reflexivity.
+ econstructor; [|eauto].
  now constructor.
Qed.

Lemma wsred_idElim : forall A x P hr y t t', [t →w* t'] -> [tIdElim A x P hr y t →w* tIdElim A x P hr y t'].
Proof.
intros * Hr.
remember RedWhStar as tag eqn:Htag in *.
induction Hr; try discriminate Htag.
+ reflexivity.
+ econstructor; [|eauto].
  now constructor.
Qed.

#[local] Ltac inv_nf := repeat match goal with
| H : dnf _ |- _ => (inversion H; subst; try match goal with H : dne _ |- _ => now inversion H end); []; clear H
| H : dne _ |- _ => inversion H; subst; []; clear H
| H : whnf _ |- _ => (inversion H; subst; try match goal with H : whne _ |- _ => now inversion H end); []; clear H
| H : whne _ |- _ => inversion H; subst; []; clear H
end.

Lemma wred_tLambda_inv {A A' t t'} : [tLambda A t →w* tLambda A' t'] -> t = t'.
Proof.
remember RedWhStar as tag eqn:Htag.
remember (tLambda A t) as l eqn:Hl.
remember (tLambda A' t') as r eqn:Hr.
intros Hred; revert A A' t t' Hl Hr.
induction Hred; try discriminate Htag; intros; subst.
+ injection Hr; intros; subst; reflexivity.
+ inversion Hred1.
Qed.

Lemma sred_tLambda_inv {A A' t t'} : [tLambda A t →s tLambda A' t'] -> [t →s t'].
Proof.
inversion 1; subst.
apply wred_tLambda_inv in H2; now subst.
Qed.

Lemma wred_tSucc_inv {t t'} : [tSucc t →w* tSucc t'] -> t = t'.
Proof.
remember RedWhStar as tag eqn:Htag.
remember (tSucc t) as l eqn:Hl.
remember (tSucc t') as r eqn:Hr.
intros Hred; revert t t' Hl Hr.
induction Hred; try discriminate Htag; intros; subst.
+ injection Hr; intros; subst; reflexivity.
+ inversion Hred1.
Qed.

Lemma sred_tSucc_inv {t t'} : [tSucc t →s tSucc t'] -> [t →s t'].
Proof.
inversion 1; subst.
apply wred_tSucc_inv in H1; now subst.
Qed.

Lemma wred_tPair_inv_fst {A A' B B' a a' b b'} : [tPair A B a b →w* tPair A' B' a' b'] -> a = a'.
Proof.
remember RedWhStar as tag eqn:Htag.
remember (tPair A B a b) as l eqn:Hl.
remember (tPair A' B' a' b') as r eqn:Hr.
intros Hred; revert A A' B B' a a' b b' Hl Hr.
induction Hred; try discriminate Htag; intros; subst.
+ injection Hr; intros; subst; reflexivity.
+ inversion Hred1.
Qed.

Lemma sred_tPair_inv_fst {A A' B B' a a' b b'} : [tPair A B a b →s tPair A' B' a' b'] -> [a →s a'].
Proof.
inversion 1; subst.
apply wred_tPair_inv_fst in H5; now subst.
Qed.

Lemma wred_tPair_inv_snd {A A' B B' a a' b b'} : [tPair A B a b →w* tPair A' B' a' b'] -> b = b'.
Proof.
remember RedWhStar as tag eqn:Htag.
remember (tPair A B a b) as l eqn:Hl.
remember (tPair A' B' a' b') as r eqn:Hr.
intros Hred; revert A A' B B' a a' b b' Hl Hr.
induction Hred; try discriminate Htag; intros; subst.
+ injection Hr; intros; subst; reflexivity.
+ inversion Hred1.
Qed.

Lemma sred_tPair_inv_snd {A A' B B' a a' b b'} : [tPair A B a b →s tPair A' B' a' b'] -> [b →s b'].
Proof.
inversion 1; subst.
apply wred_tPair_inv_snd in H5; now subst.
Qed.

Lemma sred_pred_trans : forall t u u', [t →s u] -> [u ⇉ u'] -> [t →s u'].
Proof.
intros t u; revert t; induction u; intros t u' Hst Hred.
all: try now inversion Hred.
all: try now (inversion Hst; subst; inversion Hred; subst; eauto using sred).
+ inversion Hst; subst.
  inversion Hred; subst.
  - econstructor; eauto.
  - inversion H2; subst.
    eapply redalg_sred_trans; [tea|].
    eapply redalg_sred_trans; [now eapply wsred_app|].
    eapply redalg_sred_trans; [apply wsred_step, wred_BRed|].
    apply sred_subst1; eauto.
    eapply sred_tLambda_inv, IHu1; eauto using sred, pred.
+ inversion Hst; subst.
  inversion Hred; subst.
  - econstructor; eauto.
  - inversion H8; subst.
    eapply redalg_sred_trans; [tea|].
    eapply redalg_sred_trans; [now eapply wsred_natElim|].
    eapply redalg_sred_trans; [|apply IHu2; tea].
    apply wsred_step; eauto using sred.
  - inversion H8; subst.
    eapply redalg_sred_trans; [tea|].
    eapply redalg_sred_trans; [now eapply wsred_natElim|].
    eapply redalg_sred_trans; [apply wsred_step; eauto using sred|].
    assert [t2 →s t'].
    { apply sred_tSucc_inv, IHu4; eauto using sred, sred_refl, pred. }
    econstructor; [reflexivity|..]; [econstructor; [reflexivity|..]|]; eauto using sred.
+ inversion Hst; subst.
  inversion Hred; subst.
  - econstructor; eauto.
  - inversion H1; subst.
    eapply redalg_sred_trans; [tea|].
    eapply redalg_sred_trans; [now eapply wsred_fst|].
    eapply redalg_sred_trans; [apply wsred_step; eauto using sred|].
    eapply sred_tPair_inv_fst, IHu; [|eauto using pred, pred_refl].
    econstructor; [reflexivity|..]; eauto.
+ inversion Hst; subst.
  inversion Hred; subst.
  - econstructor; eauto.
  - inversion H1; subst.
    eapply redalg_sred_trans; [tea|].
    eapply redalg_sred_trans; [now eapply wsred_snd|].
    eapply redalg_sred_trans; [apply wsred_step; eauto using sred|].
    eapply sred_tPair_inv_snd, IHu; [|eauto using pred, pred_refl].
    econstructor; [reflexivity|..]; eauto.
+ inversion Hst; subst.
  inversion Hred; subst.
  - econstructor; eauto.
  - inversion H12; subst.
    eapply redalg_sred_trans; [tea|].
    eapply redalg_sred_trans; [now eapply wsred_idElim|].
    eapply redalg_sred_trans; [apply wsred_step; eauto using sred|]; eauto.
+ inversion Hst; subst.
  inversion Hred; subst.
  - econstructor; eauto.
  - eapply redalg_sred_trans; [tea|].
    eapply redalg_sred_trans; [eapply wsred_step, wred_termEvalAlg; eauto|apply sred_refl].
    now apply dnf_unannot_rev.
+ inversion Hst; subst.
  inversion Hred; subst.
  - econstructor; eauto.
  - eapply redalg_sred_trans; [tea|].
    eapply redalg_sred_trans; [eapply wsred_step, wred_termStepAlg; eauto|apply sred_refl].
    now apply dnf_unannot_rev.
+ inversion Hst; subst.
  inversion Hred; subst.
  - econstructor; eauto.
  - eapply redalg_sred_trans; [tea|].
    eapply redalg_sred_trans; [eapply wsred_step, wred_termReflectAlg; eauto|apply sred_refl].
Unshelve. all: exact U.
Qed.

Lemma pred_sred : forall t u, [t ⇉* u] -> [t →s u].
Proof.
intros.
enough (Hg : forall r, [r →s t] -> [r →s u]).
+ apply Hg, sred_refl.
+ induction H; eauto using sred_pred_trans.
Qed.

#[local] Ltac expandopt :=
  match goal with H : (bindopt ?x ?f) = Some ?y |- _ =>
    let Hrw := fresh "Hrw" in
    destruct (let_opt_some x y f H) as [? Hrw];
    rewrite Hrw in *; cbn [bindopt] in H
  end.

#[local] Ltac caseconstr f t :=
  let b := fresh "b" in
  let Hb := fresh "Hb" in
  remember (f t) as b eqn:Hb; destruct b;
  [destruct t; try discriminate Hb|idtac].

#[local] Ltac caseval := match goal with
| H : context [if isLambda ?t then _ else _] |- _ =>
  caseconstr isLambda t
| H : context [if isNatConstructor ?t then _ else _] |- _ =>
  caseconstr isNatConstructor t
| H : context [if isIdConstructor ?t then _ else _] |- _ =>
  caseconstr isIdConstructor t
| H : context [if isPairConstructor ?t then _ else _] |- _ =>
  caseconstr isPairConstructor t
end.

#[local] Ltac casenf :=
match goal with
| H : context [is_whne ?t] |- _ =>
  let b := fresh "b" in
  let Hb := fresh "Hb" in
  remember (is_whne t) as b eqn:Hb; symmetry in Hb; destruct b; [apply is_whne_whne in Hb|]
| H : context [is_dnf ?t] |- _ =>
  let b := fresh "b" in
  let Hb := fresh "Hb" in
  remember (is_dnf t) as b eqn:Hb; symmetry in Hb; destruct b; [apply is_dnf_dnf in Hb|]
| H : context [is_closedn 0 ?t] |- _ =>
  let b := fresh "b" in
  let Hb := fresh "Hb" in
  remember (is_closedn 0 t) as b eqn:Hb; symmetry in Hb; destruct b; [|apply UntypedReduction.is_false_not in Hb]
end.

Lemma dredalg_whne_inv : forall t n, [t ⇶* n] -> dne n -> ∑ t₀, [t ⤳* t₀] × whne t₀ × [t₀ ⇶* n].
Proof.
assert (Hnat : forall n, dne (qNat n) -> False).
{ intros []; inversion 1. }
assert (Hevaltm : forall n k, dne (qEvalTm n k) -> False).
{ intros [] ?; inversion 1. }
intros t n Hr Hn.
apply dredalg_eval in Hr; [|eauto using dne, dnf].
destruct Hr as [k Hr].
revert t n Hr Hn; induction (Wf_nat.lt_wf k) as [k _ IHk]; intros t n Hr Hn.
destruct t; rewrite UntypedReduction.eval_unfold in Hr.
all: try injection Hr; intros; subst.
all: try now inversion Hn.
all: try (destruct k; [discriminate Hr|]; []).
all: repeat expandopt; try caseval; try casenf; repeat expandopt.
all: try discriminate Hr.
all: try (injection Hr; intros; subst; try now inversion Hn).
+ eexists; split; [|split]; try reflexivity; eauto using whne.
+ apply IHk in Hr; try Lia.lia; eauto.
  destruct Hr as (r₀&?&?&?); exists r₀; split; [|split]; tea.
  etransitivity; [|tea].
  etransitivity; [eapply redalg_app, eval_dredalg; tea|].
  apply redalg_one_step; constructor.
+ inversion Hn; subst.
  eexists; split; [|split]; [|now eapply whne_tApp|].
  - now eapply redalg_app, eval_dredalg.
  - apply dredalg_app; eauto; now eapply eval_dredalg.
+ apply IHk in Hr; try Lia.lia; eauto.
  destruct Hr as (r₀&?&?&?); exists r₀; split; [|split]; tea.
  etransitivity; [|tea].
  etransitivity; [eapply redalg_natElim, eval_dredalg; tea|].
  apply redalg_one_step; constructor.
+ apply IHk in Hr; try Lia.lia; eauto.
  destruct Hr as (r₀&?&?&?); exists r₀; split; [|split]; tea.
  etransitivity; [|tea].
  etransitivity; [eapply redalg_natElim, eval_dredalg; tea|].
  apply redalg_one_step; constructor.
+ inversion Hn; subst.
  eexists; split; [|split]; [|now eapply whne_tNatElim|].
  - now eapply redalg_natElim, eval_dredalg.
  - apply dredalg_natElim; eauto; now eapply eval_dredalg.
+ inversion Hn; subst.
  eexists; split; [|split]; [|now eapply whne_tEmptyElim|].
  - now eapply redalg_natEmpty, eval_dredalg.
  - apply dredalg_emptyElim; eauto; now eapply eval_dredalg.
+ apply IHk in Hr; try Lia.lia; eauto.
  destruct Hr as (r₀&?&?&?); exists r₀; split; [|split]; tea.
  etransitivity; [|tea].
  etransitivity; [eapply redalg_fst, eval_dredalg; tea|].
  apply redalg_one_step; constructor.
+ inversion Hn; subst.
  eexists; split; [|split]; [|now eapply whne_tFst|].
  - now eapply redalg_fst, eval_dredalg.
  - apply dredalg_fst; eauto; now eapply eval_dredalg.
+ apply IHk in Hr; try Lia.lia; eauto.
  destruct Hr as (r₀&?&?&?); exists r₀; split; [|split]; tea.
  etransitivity; [|tea].
  etransitivity; [eapply redalg_snd, eval_dredalg; tea|].
  apply redalg_one_step; constructor.
+ inversion Hn; subst.
  eexists; split; [|split]; [|now eapply whne_tSnd|].
  - now eapply redalg_snd, eval_dredalg.
  - apply dredalg_snd; eauto; now eapply eval_dredalg.
+ apply IHk in Hr; try Lia.lia; eauto.
  destruct Hr as (r₀&?&?&?); exists r₀; split; [|split]; tea.
  etransitivity; [|tea].
  etransitivity; [eapply redalg_idElim, eval_dredalg; tea|].
  apply redalg_one_step; constructor.
+ inversion Hn; subst.
  eexists; split; [|split]; [|now eapply whne_tIdElim|].
  - now eapply redalg_idElim, eval_dredalg.
  - apply dredalg_idElim; eauto; now eapply eval_dredalg.
+ now eelim Hnat.
+ inversion Hn; subst.
  eexists; split; [|split]; [|now eapply whne_tQuote|].
  - now eapply redalg_quote, eval_dredalg.
  - reflexivity.
+ cbn in Hr; casenf; repeat expandopt.
  - destruct projT3; expandopt; injection Hr; intros; subst; clear Hr.
    now eelim Hnat.
  - injection Hr; intros; subst; clear Hr.
    inversion Hn; subst.
    eexists; split; [|split]; [..|reflexivity]; eauto using whnf, whne.
    apply redalg_step; eauto; now eapply eval_dredalg.
+ cbn in Hr; inversion Hn; subst.
  eexists; split; [|split]; [|now eapply whne_tStep|].
  - eapply redalg_step; tea; now eapply eval_dredalg.
  - reflexivity.
+ cbn in Hr; casenf; repeat expandopt.
  - destruct projT3; expandopt; injection Hr; intros; subst; clear Hr.
    now eelim Hevaltm.
  - injection Hr; intros; subst; clear Hr.
    inversion Hn; subst.
    eexists; split; [|split]; [..|reflexivity]; eauto using whnf, whne.
    apply redalg_reflect; eauto; now eapply eval_dredalg.
+ cbn in Hr; casenf; [congruence|].
  inversion Hn; subst.
  eexists; split; [|split]; [..|reflexivity]; eauto using whnf, whne.
  apply redalg_reflect; eauto; now eapply eval_dredalg.
Qed.

(* Quasi-reduction: reduction up to some annotations *)
Definition qred deep t u := ∑ u', eqannot u u' × @RedClosureAlg deep t u'.

Lemma qred_dqred : forall t u, qred false t u -> qred true t u.
Proof.
intros * [r []]; exists r; split; eauto using gred_red.
Qed.

Lemma red_qred : forall deep t u, @RedClosureAlg deep t u -> qred deep t u.
Proof.
intros; eexists; split; [reflexivity|tea].
Qed.

Lemma eqannot_red_qred : forall deep t t' u,
  eqannot t t' -> @OneRedAlg deep t u -> ∑ u', eqannot u u' × @OneRedAlg deep t' u'.
Proof.
assert (Hnf : forall t u, unannot t = unannot u -> dnf t -> dnf u).
{ intros; now eapply dnf_eqannot. }
assert (Hne : forall t u, unannot t = unannot u -> dne t -> dne u).
{ intros; now eapply dne_eqannot. }
assert (Hwhne : forall t u, unannot t = unannot u -> whne t -> whne u).
{ intros; now eapply whne_eqannot. }
unfold eqannot; intros deep t t' u Htt' Hr; revert t' Htt'; induction Hr; intros; cbn in *.
all: try match goal with H : is_true ?deep |- _ => destruct deep; [|discriminate H] end.
all: repeat match goal with H : _ = unannot ?t |- _ => destruct t; try discriminate H; []; try (injection H; intros; subst); clear H end.
all: repeat match goal with
  | H : forall (t' : term), (unannot ?t = unannot t') -> _, H' : unannot ?t = _ |- _ =>
    specialize (H _ H'); destruct H as (?&?&?)
  end.
all: try (eexists; split; [|now constructor; eauto]; []; cbn; congruence).
+ eexists; split; [|constructor].
  rewrite !unannot_subst1; congruence.
+ eexists; split; [reflexivity|].
  replace (erase t) with (erase t'); [eauto using @OneRedAlg, closed0_eqannot|].
  rewrite !erase_unannot_etared; now f_equal.
+ symmetry in H; apply eqannot_qNat_inv in H; subst.
  eexists; split; [reflexivity|].
  econstructor; eauto using closed0_eqannot.
  replace (erase t'1) with (erase t); [eauto using @OneRedAlg, closed0_eqannot|].
  rewrite !erase_unannot_etared; now f_equal.
+ symmetry in H; apply eqannot_qNat_inv in H; subst.
  eexists; split; [reflexivity|].
  econstructor; eauto using closed0_eqannot.
  replace (erase t'1) with (erase t); [eauto using @OneRedAlg, closed0_eqannot|].
  rewrite !erase_unannot_etared; now f_equal.
Qed.

Lemma eqannot_redalg_qred : forall deep t t' u,
  eqannot t t' -> @RedClosureAlg deep t u -> ∑ u', eqannot u u' × @RedClosureAlg deep t' u'.
Proof.
intros deep t t' u Heq Hr; revert t' Heq; induction Hr.
+ intros; eexists; split; [tea|reflexivity].
+ intros t'' Htt''.
  eapply eqannot_red_qred in o; [|tea].
  destruct o as (r&?&?).
  edestruct IHHr as (r'&?&?); [tea|].
  eexists; split; [tea|]; now econstructor.
Qed.

Lemma qred_refl : forall deep t, qred deep t t.
Proof.
intros; eexists; split; [reflexivity|reflexivity].
Qed.

Lemma qred_trans : forall deep t u r, qred deep t u -> qred deep u r -> qred deep t r.
Proof.
intros * [t' []] [u' [? Hr]].
eapply eqannot_redalg_qred in Hr; [|tea].
destruct Hr as (r'&?&?).
exists r'; split; [|now etransitivity].
etransitivity; tea.
Qed.

Lemma sred_dredalg_gen : forall tag t u, sred tag t u ->
  match tag with
  | RedWh => forall r, whnf r -> qred false u r -> qred false t r
  | RedWhStar => forall r, whnf r -> qred false u r -> qred false t r
  | RedStd => dnf u -> qred true t u
  end.
Proof.
induction 1; try (now constructor); eauto; intros; inv_nf.
all: try now (eapply qred_dqred, IHsred; eauto using whnf, whne; eapply qred_refl).
+ eapply qred_trans.
  - apply qred_dqred, IHsred1; [|apply qred_refl]; eauto using whnf, whne.
  - destruct IHsred2 as (A₀&?&?); tea.
    destruct IHsred3 as (B₀&?&?); tea.
    eexists; split; [now apply eqannot_tProd|].
    eapply dredalg_prod; eauto using dnf_eqannot.
+ eapply qred_trans.
  - eapply qred_dqred, IHsred1; [|apply qred_refl].
    eauto using whnf.
  - destruct IHsred2 as (t''&?&?); [tea|].
    eexists; split; [|now apply dredalg_lambda].
    now apply eqannot_tLambda.
+ destruct IHsred2 as (t₀&?&Ht); [eauto using dnf, dne|].
  apply dredalg_whne_inv in Ht; [|eapply dne_eqannot; tea].
  destruct Ht as (tn&?&?&?).
  assert (qred false (tApp t u) (tApp tn u)).
  { eexists; split; [reflexivity|]; now apply redalg_app. }
  eapply qred_trans; [eapply qred_dqred, IHsred1; tea|]; eauto using whnf, whne.
  destruct IHsred3 as (u₀&?&?); [tea|].
  eexists; split; [|eapply dredalg_app; tea]; [now apply eqannot_tApp|].
  now eapply dne_eqannot.
+ eapply qred_trans.
  - eapply qred_dqred, IHsred1; [|apply qred_refl].
    eauto using whnf.
  - destruct IHsred2 as (t₀&?&?); tea.
    eexists; split; [now apply eqannot_tSucc|].
    now apply dredalg_succ.
+ destruct IHsred5 as (t₀&?&Ht); eauto using dne, dnf.
  apply dredalg_whne_inv in Ht; [|eapply dne_eqannot; tea].
  destruct Ht as (tn&?&?&?).
  assert (qred false (tNatElim P hz hs t) (tNatElim P hz hs tn)).
  { eexists; split; [reflexivity|]; now apply redalg_natElim. }
  eapply qred_trans; [eapply qred_dqred, IHsred1; tea|]; eauto using whnf, whne.
  destruct IHsred2 as (P₀&?&?); tea.
  destruct IHsred3 as (hz₀&?&?); tea.
  destruct IHsred4 as (hs₀&?&?); tea.
  eexists; split; [now apply eqannot_tNatElim|].
  apply dredalg_natElim; eauto using dne_eqannot, dnf_eqannot.
+ destruct IHsred3 as (t₀&?&Ht); eauto using dne, dnf.
  apply dredalg_whne_inv in Ht; [|eapply dne_eqannot; tea].
  destruct Ht as (tn&?&?&?).
  assert (qred false (tEmptyElim P t) (tEmptyElim P tn)).
  { eexists; split; [reflexivity|]; now apply redalg_natEmpty. }
  eapply qred_trans; [eapply qred_dqred, IHsred1; tea|]; eauto using whnf, whne.
  destruct IHsred2 as (P₀&?&?); tea.
  eexists; split; [now apply eqannot_tEmptyElim|].
  apply dredalg_emptyElim; eauto using dne_eqannot, dnf_eqannot.
+ eapply qred_trans.
  - apply qred_dqred, IHsred1; [|apply qred_refl]; eauto using whnf, whne.
  - destruct IHsred2 as (A₀&?&?); tea.
    destruct IHsred3 as (B₀&?&?); tea.
    eexists; split; [now apply eqannot_tSig|].
    eapply dredalg_sig; eauto using dnf_eqannot.
+ eapply qred_trans.
  - apply qred_dqred, IHsred1; [|apply qred_refl]; eauto using whnf, whne.
  - destruct IHsred2 as (a₀&?&?); tea.
    destruct IHsred3 as (b₀&?&?); tea.
    eexists; split; [now apply eqannot_tPair|].
    now eapply dredalg_pair; eauto using dnf_eqannot.
+ destruct IHsred2 as (t₀&?&Ht); eauto using dnf, dne.
  apply dredalg_whne_inv in Ht; [|eapply dne_eqannot; tea].
  destruct Ht as (tn&?&?&?).
  assert (qred false (tFst t) (tFst tn)).
  { eexists; split; [reflexivity|]; now apply redalg_fst. }
  eapply qred_trans; [eapply qred_dqred, IHsred1; tea|]; eauto using whnf, whne.
  eexists; split; [now apply eqannot_tFst|].
  now apply dredalg_fst.
+ destruct IHsred2 as (t₀&?&Ht); eauto using dnf, dne.
  apply dredalg_whne_inv in Ht; [|eapply dne_eqannot; tea].
  destruct Ht as (tn&?&?&?).
  assert (qred false (tSnd t) (tSnd tn)).
  { eexists; split; [reflexivity|]; now apply redalg_snd. }
  eapply qred_trans; [eapply qred_dqred, IHsred1; tea|]; eauto using whnf, whne.
  eexists; split; [now apply eqannot_tSnd|].
  now apply dredalg_snd.
+ eapply qred_trans.
  - eapply qred_dqred, IHsred1; [|apply qred_refl].
    eauto using whnf.
  - destruct IHsred2 as (A₀&?&?); tea.
    destruct IHsred3 as (t₀&?&?); tea.
    destruct IHsred4 as (u₀&?&?); tea.
    eexists; split; [now apply eqannot_tId|].
    eapply dredalg_id; eauto using dnf_eqannot.
+ eapply qred_trans.
  - eapply qred_dqred, IHsred1; [|apply qred_refl]; eauto using whnf, whne.
  - destruct IHsred2 as (A₀&?&?); tea.
    destruct IHsred3 as (t₀&?&?); tea.
    eexists; split; [now apply eqannot_tRefl|].
    eapply dredalg_refl; eauto using dnf_eqannot.
+ destruct IHsred7 as (e₀&?&He); eauto using dnf, dne.
  apply dredalg_whne_inv in He; [|eapply dne_eqannot; tea].
  destruct He as (en&?&?&?).
  assert (qred false (tIdElim A x P hr y e) (tIdElim A x P hr y en)).
  { eexists; split; [reflexivity|]; now apply redalg_idElim. }
  eapply qred_trans; [eapply qred_dqred, IHsred1; tea|]; eauto using whnf, whne.
  destruct IHsred2 as (A₀&?&?); tea.
  destruct IHsred3 as (x₀&?&?); tea.
  destruct IHsred4 as (P₀&?&?); tea.
  destruct IHsred5 as (hr₀&?&?); tea.
  destruct IHsred6 as (y₀&?&?); tea.
  eexists; split; [now apply eqannot_tIdElim|].
  apply dredalg_idElim; eauto using dnf_eqannot, dne_eqannot.
+ eapply qred_dqred, IHsred1; eauto using whnf, whne.
  destruct IHsred2 as (t₀&?&?); tea.
  eexists; split; [|now eapply redalg_quote].
  unfold eqannot; cbn; now f_equal.
+ eapply qred_dqred, IHsred1; eauto using whnf, whne.
  destruct IHsred2 as (t₀&?&?); tea.
  destruct IHsred3 as (u₀&?&?); tea.
  eexists; split; [now apply eqannot_tStep|].
  apply redalg_step; eauto using dnf_eqannot.
+ eapply qred_dqred, IHsred1; eauto using whnf, whne.
  destruct IHsred2 as (t₀&?&?); tea.
  destruct IHsred3 as (u₀&?&?); tea.
  eexists; split; [now apply eqannot_tReflect|].
  apply redalg_reflect; eauto using dnf_eqannot.
+ destruct H0 as (r₀&?&?).
  eexists; split; [tea|].
  econstructor; [|tea]; constructor.
+ destruct H1 as (r₀&?&Hr).
  apply redalg_eval in Hr; [|now eapply whnf_eqannot].
  destruct Hr as [k Hr]; rewrite UntypedReduction.eval_unfold in Hr.
  destruct k; [discriminate Hr|].
  expandopt; caseval; try casenf.
  - apply eval_dredalg in Hrw, Hr.
    edestruct IHsred as (u₀&Hu₀&?); [|now apply red_qred|]; eauto using whnf, whne.
    destruct u₀; try discriminate Hu₀; unfold eqannot in Hu₀; cbn in Hu₀; injection Hu₀; intros.
    eapply eqannot_redalg_qred in Hr; [|eapply eqannot_subst1; tea; reflexivity].
    destruct Hr as (v&?&?).
    eexists; split; [etransitivity; tea|].
    etransitivity; [|tea].
    etransitivity; [now eapply redalg_app|].
    do 2 econstructor.
  - injection Hr; intros; subst; clear Hr; apply eval_dredalg in Hrw.
    edestruct IHsred as (u₀&Hu₀&?); [|now apply red_qred|]; eauto using whnf, whne.
    assert (Hred : [tApp t a ⤳* tApp u₀ a]) by now eapply redalg_app.
    eexists; split; [|tea].
    etransitivity; [tea|].
    apply eqannot_tApp; [tea|reflexivity].
  - discriminate.
+ destruct H1 as (r₀&?&Hr).
  apply redalg_eval in Hr; [|now eapply whnf_eqannot].
  destruct Hr as [k Hr]; rewrite UntypedReduction.eval_unfold in Hr.
  destruct k; [discriminate Hr|].
  expandopt; caseval; try casenf.
  - apply eval_dredalg in Hr, Hrw.
    edestruct IHsred as (n₀&Hn₀&?); [|now apply red_qred|]; eauto using whnf, whne.
    destruct n₀; try discriminate Hn₀.
    eexists; split; [tea|].
    etransitivity; [|tea].
    etransitivity; [now eapply redalg_natElim|].
    apply redalg_one_step; constructor.
  - apply eval_dredalg in Hr, Hrw.
    edestruct IHsred as (n₀&Hn₀&?); [|now apply red_qred|]; eauto using whnf, whne.
    destruct n₀; try discriminate Hn₀; unfold eqannot in Hn₀; cbn in Hn₀; injection Hn₀; intros.
    match type of Hr with [tApp (tApp hs ?r) (tNatElim P hz hs ?r) ⤳* _] =>
      assert (eqannot (tApp (tApp hs r) (tNatElim P hz hs r)) (tApp (tApp hs n₀) (tNatElim P hz hs n₀)))
    end.
    { repeat apply eqannot_tApp; try apply eqannot_tNatElim; tea; reflexivity. }
    eapply eqannot_redalg_qred in Hr; [|tea].
    destruct Hr as (r₁&?&?).
    eexists; split; [etransitivity; tea|].
    etransitivity; [|tea].
    etransitivity; [now eapply redalg_natElim|].
    apply redalg_one_step; constructor.
  - injection Hr; intros; subst; clear Hr.
    apply eval_dredalg in Hrw.
    edestruct IHsred as (n₀&Hn₀&?); [|now apply red_qred|]; eauto using whnf, whne.
    assert (Hred : [tNatElim P hz hs n ⤳* tNatElim P hz hs n₀]) by now eapply redalg_natElim.
    eexists; split; [|tea].
    etransitivity; [tea|]; apply eqannot_tNatElim; tea; reflexivity.
  - discriminate.
+ eapply qred_trans; [|tea].
  eexists; split; [reflexivity|].
  eauto using @OneRedAlg, @RedClosureAlg.
+ destruct H0 as (r₀&?&Hr).
  eexists; split; [tea|].
  econstructor; [|tea]; constructor.
+ destruct H1 as (r₀&?&Hr).
  apply redalg_eval in Hr; [|now eapply whnf_eqannot].
  destruct Hr as [k Hr]; rewrite UntypedReduction.eval_unfold in Hr.
  destruct k; [discriminate Hr|].
  expandopt; try casenf.
  - injection Hr; intros; subst; clear Hr.
    apply eval_dredalg in Hrw.
    edestruct IHsred as (e₀&He₀&?); [|now apply red_qred|]; eauto using whnf, whne.
    assert (Hred : [tEmptyElim P e ⤳* tEmptyElim P e₀]) by now eapply redalg_natEmpty.
    eexists; split; [|tea].
    etransitivity; [tea|]; apply eqannot_tEmptyElim; tea; reflexivity.
  - discriminate.
+ destruct H1 as (r₀&?&Hr).
  apply redalg_eval in Hr; [|now eapply whnf_eqannot].
  destruct Hr as [k Hr]; rewrite UntypedReduction.eval_unfold in Hr.
  destruct k; [discriminate Hr|].
  expandopt; caseval; try casenf.
  - apply eval_dredalg in Hr, Hrw.
    edestruct IHsred as (p₀&Hp₀&?); [|now apply red_qred|]; eauto using whnf, whne.
    destruct p₀; try discriminate Hp₀; unfold eqannot in Hp₀; cbn in Hp₀; injection Hp₀; intros.
    eapply eqannot_redalg_qred in Hr; [|tea].
    destruct Hr as (r₁&?&?).
    eexists; split; [etransitivity; tea|].
    etransitivity; [now eapply redalg_fst|].
    etransitivity; [|tea].
    apply redalg_one_step; constructor.
  - injection Hr; intros; subst; clear Hr.
    apply eval_dredalg in Hrw.
    edestruct IHsred as (p₀&Hp₀&?); [|now apply red_qred|]; eauto using whnf, whne.
    assert (Hred : [tFst p ⤳* tFst p₀]) by now eapply redalg_fst.
    eexists; split; [|tea].
    etransitivity; [tea|]; apply eqannot_tFst; tea.
  - discriminate.
+ destruct H0 as (r₀&?&Hr).
  eexists; split; [tea|].
  econstructor; [|tea]; constructor.
+ destruct H1 as (r₀&?&Hr).
  apply redalg_eval in Hr; [|now eapply whnf_eqannot].
  destruct Hr as [k Hr]; rewrite UntypedReduction.eval_unfold in Hr.
  destruct k; [discriminate Hr|].
  expandopt; caseval; try casenf.
  - apply eval_dredalg in Hr, Hrw.
    edestruct IHsred as (p₀&Hp₀&?); [|now apply red_qred|]; eauto using whnf, whne.
    destruct p₀; try discriminate Hp₀; unfold eqannot in Hp₀; cbn in Hp₀; injection Hp₀; intros.
    eapply eqannot_redalg_qred in Hr; [|tea].
    destruct Hr as (r₁&?&?).
    eexists; split; [etransitivity; tea|].
    etransitivity; [now eapply redalg_snd|].
    etransitivity; [|tea].
    apply redalg_one_step; constructor.
  - injection Hr; intros; subst; clear Hr.
    apply eval_dredalg in Hrw.
    edestruct IHsred as (p₀&Hp₀&?); [|now apply red_qred|]; eauto using whnf, whne.
    assert (Hred : [tSnd p ⤳* tSnd p₀]) by now eapply redalg_snd.
    eexists; split; [|tea].
    etransitivity; [tea|]; apply eqannot_tSnd; tea.
  - discriminate.
+ destruct H0 as (r₀&?&Hr).
  eexists; split; [tea|].
  econstructor; [|tea]; constructor.
+ destruct H0 as (r₀&?&Hr).
  eexists; split; [tea|].
  econstructor; [|tea]; constructor.
+ destruct H1 as (r₀&?&Hr).
  apply redalg_eval in Hr; [|now eapply whnf_eqannot].
  destruct Hr as [k Hr]; rewrite UntypedReduction.eval_unfold in Hr.
  destruct k; [discriminate Hr|].
  expandopt; caseval; try casenf.
  - apply eval_dredalg in Hr, Hrw.
    edestruct IHsred as (e₀&He₀&?); [|now apply red_qred|]; eauto using whnf, whne.
    destruct e₀; try discriminate He₀; unfold eqannot in He₀; cbn in He₀; injection He₀; intros.
    eexists; split; [tea|].
    etransitivity; [|tea].
    etransitivity; [now eapply redalg_idElim|].
    apply redalg_one_step; constructor.
  - injection Hr; intros; subst; clear Hr.
    apply eval_dredalg in Hrw.
    edestruct IHsred as (e₀&He₀&?); [|now apply red_qred|]; eauto using whnf, whne.
    assert (Hred : [tIdElim A x P hr y e ⤳* tIdElim A x P hr y e₀]) by now eapply redalg_idElim.
    eexists; split; [|tea].
    etransitivity; [tea|]; now apply eqannot_tIdElim.
  - discriminate.
+ eapply qred_trans with (tQuote t').
  - destruct IHsred as (t₀&?&?); [tea|].
    eexists; split; [now apply eqannot_tQuote|].
    now apply redalg_quote.
  - destruct H1 as (r₀&?&Hr).
    eexists; split; [tea|].
    econstructor; [|tea].
    now constructor.
+ eapply qred_trans with (tStep t' (qNat u')).
  - destruct IHsred1 as (t₀&?&?); [tea|].
    destruct IHsred2 as (u₀&?&?); [apply dnf_qNat|].
    eexists; split; [apply eqannot_tStep; tea; reflexivity|].
    eapply redalg_step; eauto using dnf_eqannot, @RedClosureAlg.
  - destruct H2 as (r₀&?&Hr).
    eexists; split; [tea|].
    econstructor; [|tea].
    now econstructor.
+ eapply qred_trans with (tReflect t' (qNat u')).
  - destruct IHsred1 as (t₀&?&?); [tea|].
    destruct IHsred2 as (u₀&?&?); [apply dnf_qNat|].
    eexists; split; [apply eqannot_tReflect; tea; reflexivity|].
    eapply redalg_reflect; eauto using dnf_eqannot, @RedClosureAlg.
  - destruct H2 as (r₀&?&Hr).
    eexists; split; [tea|].
    econstructor; [|tea].
    now econstructor.
Qed.

Lemma sred_dredalg : forall t u, [t →s u] -> dnf u -> ∑ u', eqannot u u' × [t ⇶* u'].
Proof.
intros t u Hr Hnf.
now eapply (sred_dredalg_gen RedStd).
Qed.

(* Ad-hoc stuff needed to prove the logical relation *)

Lemma dred_tApp_qNat_compat : forall t t₀ n m,
  [t ⇶* t₀] -> dnf t₀ ->
  [tApp t (qNat n) ⇶* qNat m] ->
  [tApp t₀ (qNat n) ⇶* qNat m].
Proof.
intros * Ht Hnf Happ.
apply dredalg_pred_clos in Ht.
apply dredalg_pred_clos in Happ.
eapply pred_clos_app with (u := (qNat n)) in Ht.
edestruct (pred_confluent) as (v&Hw&Hv); [apply Ht|apply Happ|].
eapply dnf_pred_clos_id in Hv; [|apply dnf_qNat].
symmetry in Hv; apply eqannot_qNat_inv in Hv; subst.
apply pred_sred, sred_dredalg in Hw; [|apply dnf_qNat].
destruct Hw as (u'&Hu'&?).
symmetry in Hu'; apply eqannot_qNat_inv in Hu'; now subst.
Qed.
