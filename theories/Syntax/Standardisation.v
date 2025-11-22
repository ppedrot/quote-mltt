From Coq Require Import CRelationClasses ssrbool.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils Notations.
From LogRel.Syntax Require Import BasicAst Computation Context Closed NormalForms NormalEq Weakening UntypedReduction Confluence.

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
  [tQuote t →w qNat (quote (erase t'))]
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

Lemma wsred_emptyElim : forall P t t', [t →w* t'] -> [tEmptyElim P t →w* tEmptyElim P t'].
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

(** Commutation with erasure *)

Inductive erased : term -> term -> Set :=
| erased_tRel {n} : erased (tRel n) (tRel n)
| erased_tSort {s} : erased (tSort s) (tSort s)
| erased_tProd {A A' B B'} : erased A A' -> erased B B' -> erased (tProd A B) (tProd A' B')
| erased_tLambda {A A' t t'} : erased t t' -> erased (tLambda A t) (tLambda A' t')
| erased_tApp {t t' u u'} : erased t t' -> erased u u' -> erased (tApp t u) (tApp t' u')
| erased_tNat : erased tNat tNat
| erased_tZero : erased tZero tZero
| erased_tSucc {t t'} : erased t t' -> erased (tSucc t) (tSucc t')
| erased_tNatElim {P P' hz hz' hs hs' t t'} :
  erased P P' -> erased hz hz' -> erased hs hs' -> erased t t' -> erased (tNatElim P hz hs t) (tNatElim P' hz' hs' t')
| erased_tEmpty : erased tEmpty tEmpty
| erased_tEmptyElim {P P' t t'} :
  erased P P' -> erased t t' -> erased (tEmptyElim P t) (tEmptyElim P' t')
| erased_tSig {A A' B B'} : erased A A' -> erased B B' -> erased (tSig A B) (tSig A' B')
| erased_tPair {A A' B B' a a' b b'} :
  erased a a' -> erased b b' -> erased (tPair A B a b) (tPair A' B' a' b')
| erased_tFst {t t'} : erased t t' -> erased (tFst t) (tFst t')
| erased_tSnd {t t'} : erased t t' -> erased (tSnd t) (tSnd t')
| erased_tId {A A' t t' u u'} : erased A A' -> erased t t' -> erased u u' -> erased (tId A t u) (tId A' t' u')
| erased_tRefl {A A' t t'} : erased A A' -> erased t t' -> erased (tRefl A t) (tRefl A' t')
| erased_tIdElim {A A' x x' P P' hr hr' y y' e e'} : 
  erased A A' -> erased x x' -> erased P P' -> erased hr hr' -> erased y y' -> erased e e' ->
  erased (tIdElim A x P hr y e) (tIdElim A' x' P' hr' y' e')
| erased_tQuote {t t'} : erased t t' -> erased (tQuote t) (tQuote t')
| erased_tStep {t t' u u'} : erased t t' -> erased u u' -> erased (tStep t u) (tStep t' u')
| erased_tReflect {t t' u u'} : erased t t' -> erased u u' -> erased (tReflect t u) (tReflect t' u')
(** Additional erasure primitives *)
| erased_tLambda_eta {A t r} : erased t (tApp r⟨↑⟩ (tRel 0)) -> erased (tLambda A t) r
| erased_tPair_eta {A B a b r} : erased a (tFst r) -> erased b (tSnd r) -> erased (tPair A B a b) r
.

Lemma erase_erased : forall t, erased t (erase t).
Proof.
induction t; cbn; try now (constructor; eauto).
+ remember (erase t2) as t2'.
  destruct (eta_fun_intro t2'); subst.
  - now apply erased_tLambda.
  - now apply erased_tLambda_eta.
+ remember (erase t3) as t3'.
  remember (erase t4) as t4'.
  destruct (eta_pair_intro t3' t4'); subst.
  - now apply erased_tPair.
  - now apply erased_tPair_eta.
Qed.

Lemma erased_eqnf : forall t t', erased t t' -> eqnf t t'.
Proof.
induction 1; eauto using
  eqnf_tRel, eqnf_tSort, eqnf_tProd, eqnf_tLambda, eqnf_tApp, eqnf_tNat, eqnf_tZero, eqnf_tSucc,
  eqnf_tNatElim, eqnf_tEmpty, eqnf_tEmptyElim, eqnf_tSig, eqnf_tPair, eqnf_tFst, eqnf_tSnd, eqnf_tId,
  eqnf_tRefl, eqnf_tIdElim, eqnf_tQuote, eqnf_tStep, eqnf_tReflect, eqnf_tLambda_whne, eqnf_tPair_whne.
Qed.

Lemma erased_is_closedn : forall t t' n, erased t t' -> is_closedn n t = is_closedn n t'.
Proof.
intros t t' n Herase; revert n; induction Herase; intros; cbn.
all: repeat match goal with |- _ && _ = _ && _ => f_equal end; eauto.
+ rewrite IHHerase; cbn; rewrite Bool.andb_true_r.
  apply NormalEq.closedn_shift.
+ rewrite IHHerase1, IHHerase2.
  apply Bool.andb_diag.
Qed.

Lemma erased_closed0 : forall t t', erased t t' -> closed0 t -> closed0 t'.
Proof.
intros; unfold closed0; now erewrite <- erased_is_closedn.
Qed.

Lemma erased_dnf_dne : forall t t', erased t t' -> (dnf t -> dnf t') × (dne t -> dne t').
Proof.
assert (Hc : forall t t', erased t t' -> ~ closed0 t -> ~ closed0 t').
{ intros; unfold closed0 in *; now erewrite <- erased_is_closedn. }
assert (Hc' : forall t t' u u', erased t t' -> erased u u' -> (~ is_closedn 0 t) + (~ is_closedn 0 u) -> (~ is_closedn 0 t') + (~ is_closedn 0 u')).
{ intros * ?? []; [left|right]; eauto. }
induction 1; repeat match goal with H : _ × _ |- _ => destruct H end; split; intros Hnf; inversion Hnf; subst; eauto 6 using dnf, dne.
all: try match goal with H : dne _ |- _ => now inversion H end.
all: try match goal with H : dne _ |- _ => now inversion H; subst; eauto 9 using dnf, dne end.
+ assert (Hr : dnf (tApp r⟨↑⟩ (tRel 0))) by eauto.
  inversion Hr; subst; inversion H0; subst.
  eapply dnf_ren_rev; now eauto using dne, dnf.
+ assert (Hr : dnf (tFst r)) by eauto.
  inversion Hr; subst; inversion H1; subst; now eauto using dnf, dne.
Qed.

Lemma erased_dnf : forall t t', erased t t' -> dnf t -> dnf t'.
Proof.
intros; now eapply erased_dnf_dne.
Qed.

Lemma erased_dne : forall t t', erased t t' -> dne t -> dne t'.
Proof.
intros; now eapply erased_dnf_dne.
Qed.

Lemma erased_whne : forall t t', erased t t' -> whne t -> whne t'.
Proof.
induction 1; intros Hne; inversion Hne; subst; eauto using whne.
+ constructor; eauto using erased_dnf.
  unfold closed0; erewrite <- erased_is_closedn; tea.
+ constructor; eauto using erased_dnf.
  destruct H3; [left|right]; unfold closed0; erewrite <- erased_is_closedn; tea.
+ constructor; eauto using erased_dnf.
  destruct H3; [left|right]; unfold closed0; erewrite <- erased_is_closedn; tea.
Qed.

Lemma erased_ren : forall t t' ρ, erased t t' -> erased t⟨ρ⟩ t'⟨ρ⟩.
Proof.
intros t t' ρ Ht; revert ρ; induction Ht; intros ρ; eauto using erased.
+ cbn; apply erased_tLambda_eta.
  replace r⟨ρ⟩⟨↑⟩ with r⟨↑⟩⟨upRen_term_term ρ⟩ by now bsimpl.
  apply IHHt.
Qed.

Lemma erased_refl : forall t, erased t t.
Proof.
induction t; eauto using erased.
Qed.

Lemma erased_trans : forall t u r, erased t u -> erased u r -> erased t r.
Proof.
intros t u r Hl; revert r; induction Hl; intros ? Hr.
all: try now (inversion Hr; subst; eauto 10 using erased, erased_ren).
Qed.

Lemma erased_subst : forall t t' σ σ', erased t t' -> (forall n, erased (σ n) (σ' n)) -> erased t[σ] t'[σ'].
Proof.
assert (Hup : forall σ σ', (forall n : nat, erased (σ n) (σ' n)) -> (forall n : nat, erased (up_term_term σ n) (up_term_term σ' n))).
{ intros σ σ' Hσ []; cbn; [constructor|].
  unfold funcomp; now apply erased_ren. }
intros t t' σ σ' Ht; revert σ σ'.
induction Ht; intros σ σ' Hσ; cbn; try eauto 10 using erased.
+ cbn; apply erased_tLambda_eta.
  replace r[σ']⟨↑⟩ with r⟨↑⟩[up_term_term σ'] by now bsimpl.
  eapply erased_trans; [now eapply IHHt|]; cbn.
  constructor; [now apply erased_refl|now constructor].
Qed.

Lemma erased_subst1 : forall t t' u u', erased t t' -> erased u u' -> erased t[u..] t'[u'..].
Proof.
intros.
apply erased_subst; tea.
intros []; cbn; [tea|constructor].
Qed.

Lemma erased_qNat : forall n t, erased (qNat n) t -> t = qNat n.
Proof.
induction n; intros t Ht; inversion Ht; subst; cbn; [reflexivity|].
f_equal; now apply IHn.
Qed.

Lemma eqannot_erased : forall t u, eqannot t u -> erased t u.
Proof.
unfold eqannot; induction t; intros u Heq.
all: destruct u; cbn in Heq; try discriminate Heq; try injection Heq; intros; subst.
all: eauto 10 using erased.
Qed.

Fixpoint is_shallow t := match t with
| tQuote _ | tReflect _ _ | tStep _ _ => false
| tApp t _ => is_shallow t
| tNatElim _ _ _ t => is_shallow t
| tIdElim _ _ _ _ _ t => is_shallow t
| tEmptyElim _ t => is_shallow t
| tFst t | tSnd t => is_shallow t
| _ => true
end.

Lemma bigstep_wsred : forall t v, [t ↓ v] -> is_shallow v -> [t →w* v].
Proof.
remember false as b eqn:Hb.
induction 1; try discriminate Hb; intros.
all: eauto using sred, wsred_app, wsred_natElim, wsred_idElim, wsred_emptyElim.
+ eauto 10 using wsred_trans, sred, wsred_app.
+ eauto 10 using wsred_trans, sred, wsred_natElim.
+ eauto 10 using wsred_trans, sred, wsred_natElim.
+ eauto 10 using wsred_trans, sred, wsred_fst.
+ eauto 10 using wsred_trans, sred, wsred_fst.
+ eauto 10 using wsred_trans, sred, wsred_snd.
+ eauto 10 using wsred_trans, sred, wsred_snd.
+ eauto 10 using wsred_trans, sred, wsred_idElim.
+ eauto 10 using bigstep_dredalg, dredalg_pred_clos, pred_sred, sred, bigstep_dnf.
+ discriminate H0.
+ eauto 10 using bigstep_dredalg, dredalg_pred_clos, pred_sred, sred, bigstep_dnf.
+ discriminate H1.
+ eauto 10 using bigstep_dredalg, dredalg_pred_clos, pred_sred, sred, bigstep_dnf.
+ discriminate H1.
Qed.

Lemma eqannot_sred : forall t r r', [t →s r] -> eqannot r r' -> [t →s r'].
Proof.
intros t r r' Hr.
remember RedStd as tag eqn:Htag in *.
revert r' Htag. induction Hr; intros r' Htag Heq; try discriminate Htag.
all: try (unfold eqannot in Heq; destruct r'; cbn in Heq; try discriminate Heq; []); try (injection Heq; intros; subst).
all: eauto 10 using sred.
Qed.

Lemma sred_eta_fun : forall t r,
  [tApp t⟨↑⟩ (tRel 0) →s r] -> dnf r ->
  (∑ t₀, [t →s t₀] × (eqannot r (tApp t₀⟨↑⟩ (tRel 0)))) + (∑ A₀ t₀, [t →w* tLambda A₀ t₀] × [t₀ →s r]).
Proof.
intros t r Happ Hr.
assert (Hst := Happ).
apply sred_dredalg in Happ; [|tea]; destruct Happ as (r₀&Hr₀&Hrr).
apply dredalg_bigstep in Hrr; [|eauto using dnf_eqannot].
inversion Hrr; subst.
+ assert (Hred := H1).
  apply bigstep_dredalg in Hred.
  eapply gred_red, dredalg_ren_adj in Hred; [|apply shift_inj].
  destruct Hred as [u' Hu']; destruct u'; cbn in Hu'; try discriminate Hu'.
  injection Hu'; intros; subst; clear Hu'.
  assert (Hrw : forall t, t⟨upRen_term_term ↑⟩[(tRel 0)..] = t).
  { intros; bsimpl; reflexivity. }
  rewrite Hrw in H2.
  apply bigstep_dredalg in H1.
  change (tLambda u'1⟨↑⟩ u'2⟨upRen_term_term ↑⟩) with ((tLambda u'1 u'2)⟨↑⟩) in H1.
  apply redalg_ren_inv in H1; [|apply shift_inj].
  apply redalg_bigstep in H1; [|constructor].
  apply bigstep_wsred in H1; [|constructor].
  right; do 2 eexists; split; [tea|].
  eapply eqannot_sred; [|symmetry; tea].
  now eapply pred_sred, dredalg_pred_clos, bigstep_dredalg.
+ assert (Hred := H1).
  apply bigstep_dredalg in Hred.
  eapply gred_red, dredalg_ren_adj in Hred; [|apply shift_inj].
  destruct Hred; subst.
  apply bigstep_dnf_det in H4; [subst|eauto using dnf, dne].
  apply bigstep_dredalg, redalg_ren_inv in H1; [|apply shift_inj].
  apply bigstep_dredalg in H3.
  assert (Hred := H3); apply dredalg_ren_adj in H3; [|apply shift_inj].
  destruct H3; subst.
  apply redalg_ren_inv in Hred; [|apply shift_inj].
  unfold eqannot in Hr₀; destruct r; cbn in Hr₀; try discriminate Hr₀; injection Hr₀; intros; subst.
  destruct r2; cbn in H; try discriminate H; injection H; intros; subst.
  left; eexists; split; [|now apply eqannot_tApp].
  eapply pred_sred, dredalg_pred_clos.
  etransitivity; [now apply gred_red|tea].
Unshelve. all: constructor.
Qed.


Lemma sred_eta_pair : forall t p q,
  [tFst t →s p] ->
  [tSnd t →s q] ->
  dnf p -> dnf q ->
  (∑ t₀, [t →s t₀] × (eqannot p (tFst t₀)) × (eqannot q (tSnd t₀))) + (∑ A₀ B₀ a₀ b₀, [t →w* tPair A₀ B₀ a₀ b₀] × [a₀ →s p] × [b₀ →s q]).
Proof.
intros t p q Hp Hq Hnfp Hnfq.
apply sred_dredalg in Hp; [|tea]; destruct Hp as (p₀&Hp&Hrp).
apply sred_dredalg in Hq; [|tea]; destruct Hq as (q₀&Hq&Hrq).
apply dredalg_bigstep in Hrp; [|eauto using dnf_eqannot].
apply dredalg_bigstep in Hrq; [|eauto using dnf_eqannot].
inversion Hrp; subst; inversion Hrq; subst.
all: match goal with Hl : [?t ↓ ?l], Hr : [?t ↓ ?r] |- _ => assert (l = r) by now eapply bigstep_det end; subst.
+ injection H; intros; subst; clear H.
  apply bigstep_wsred in H0; [|constructor].
  right; do 4 eexists; split; [|split]; [tea| |].
  - eapply eqannot_sred; [|symmetry; tea].
    apply pred_sred, dredalg_pred_clos; now apply bigstep_dredalg.
  - eapply eqannot_sred; [|symmetry; tea].
    apply pred_sred, dredalg_pred_clos; now apply bigstep_dredalg.
+ inv_whne.
+ inv_whne.
+ match goal with Hl : [?t ⇊ ?l], Hr : [?t ⇊ ?r] |- _ => assert (l = r) by now eapply bigstep_det end; subst.
  unfold eqannot in Hp; cbn in Hp; destruct p; try discriminate Hp; injection Hp; intros; subst.
  unfold eqannot in Hq; cbn in Hq; destruct q; try discriminate Hq; injection Hq; intros; subst.
  left; eexists; split; [|split]; tea.
  eapply pred_sred, dredalg_pred_clos.
  etransitivity; [apply gred_red|]; now apply bigstep_dredalg.
Qed.

Lemma sred_erased_gen : forall tag t u, sred tag t u ->
  match tag with
  | RedWh => forall t', erased t t' -> ∑ u', erased u u' × [t' →w* u']
  | RedWhStar => forall t', erased t t' -> ∑ u', erased u u' × [t' →w* u']
  | RedStd => forall t', erased t t' -> dnf u -> ∑ u', erased u u' × [t' →s u']
  end.
Proof.
induction 1; cbn; intros t₀ Ht₀.
all: try (intros Hnf; inv_nf).
all: try match goal with
| H : forall t', erased ?w t' -> _, He : erased ?w _ |- _ =>
  edestruct H as (w₀&Her&?); [exact He|]; inversion Her; []; subst; clear Her
end.
all: repeat match goal with
| H : forall t', erased ?w t' -> _, He : erased ?w _ |- _ =>
  let Her := fresh in 
  edestruct H as (?&Her&?); [exact He|]; clear H
end.
all: try now (eexists; split; [apply erased_refl|]; eauto using sred).
all: try now (eexists; split; [now constructor|]; eauto using sred).
all: repeat match goal with H : erased _ _ |- _ => inversion H; []; subst; clear H end.
all: repeat match goal with
| H : forall t', erased ?w t' -> dnf ?t -> _, He : erased ?w _ |- _ =>
  let Her := fresh in 
  edestruct H as (?&Her&?); [exact He|now eauto using dnf, dne, dnf_qNat|]; clear H
end.
all: repeat match goal with
| H : forall t', erased ?w t' -> _, He : erased ?w _ |- _ =>
  let Her := fresh in 
  edestruct H as (?&Her&?); [exact He|]; clear H
end.
all: try (eexists; split; [now eauto using erased|]).
all: eauto using sred, wsred_app, wsred_natElim, wsred_idElim, wsred_emptyElim, wsred_fst, wsred_snd.
+ inversion H1; subst; clear H1.
  - edestruct IHsred2 as (v₀&Hv&?); tea.
    eexists; split; [now constructor|]; eauto using sred.
  - edestruct IHsred2 as (v₀&Hv&Hr); tea.
    eapply sred_eta_fun in Hr; [|eauto using erased_dnf].
    destruct Hr as [(?&?&Heq)|(?&?&?&?)]; subst.
    * unfold eqannot in Heq; cbn in Heq; destruct v₀; try discriminate Heq.
      cbn in Heq; injection Heq; intros; subst.
      destruct v₀2; cbn in H1; try discriminate H1; injection H1; intros; subst.
      eexists; split; [apply erased_tLambda_eta|].
      { eapply erased_trans; [tea|]; constructor; [now apply eqannot_erased|constructor]. }
      now eapply redalg_sred_trans.
    * eexists; split; [now econstructor|].
      econstructor; [now etransitivity|tea].
+ inversion H2; subst; clear H2.
  - edestruct IHsred2 as (a₀&Ha&?); tea.
    edestruct IHsred3 as (b₀&Hb&?); tea.
    eexists; split; [now constructor|]; eauto using sred.
  - edestruct IHsred2 as (a₀&Ha&Hra); tea.
    edestruct IHsred3 as (b₀&Hb&Hrb); tea.
    edestruct sred_eta_pair as [(?&?&?&?)|(?&?&?&?&?&?&?)]; eauto using erased_dnf.
    * eexists; split; [apply erased_tPair_eta|eapply redalg_sred_trans; tea].
      { eapply erased_trans; [tea|]; now apply eqannot_erased. }
      { eapply erased_trans; [tea|]; now apply eqannot_erased. }
    * eexists; split; [now eapply erased_tPair|].
      eapply redalg_sred_trans; [tea|].
      eauto using sred.
+ inversion H1; subst.
  - eexists; split; [now apply erased_subst1|]; eauto using sred.
  - eexists; split; [|reflexivity].
    eapply erased_subst1 with (u := a) in H4; tea.
    cbn in H4; now replace (t'⟨↑⟩[u'..]) with t' in H4 by now bsimpl.
+ inversion H0; subst.
  - eexists; split; [tea|]; eauto using sred.
  - eexists; split; [tea|reflexivity].
+ inversion H0; subst.
  - eexists; split; [tea|]; eauto using sred.
  - eexists; split; [tea|reflexivity].
+ eexists; split; [apply erased_refl|].
  replace (erase t') with (erase projT1) by now symmetry; apply erased_eqnf.
  eauto using sred, erased_dnf, erased_closed0.
+ eexists; split; [apply erased_refl|].
  apply erased_qNat in H1; subst.
  replace (erase t') with (erase projT0) in e by now symmetry; apply erased_eqnf.
  eauto using sred, erased_dnf, erased_closed0.
+ eexists; split; [apply erased_refl|].
  apply erased_qNat in H1; subst.
  replace (erase t') with (erase projT0) in e by now symmetry; apply erased_eqnf.
  eauto using sred, erased_dnf, erased_closed0.
+ now etransitivity.
Unshelve. all: exact U.
Qed.

Lemma sred_erased : forall t t' u, [t →s u] -> erased t t' -> dnf u -> ∑ u', erased u u' × [t' →s u'].
Proof.
intros; now eapply (sred_erased_gen RedStd).
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

Lemma dred_erase_qNat_compat : forall t n,
  [t ⇶* qNat n] -> [erase t ⇶* qNat n].
Proof.
intros t n Hr.
apply dredalg_pred_clos, pred_sred in Hr.
eapply sred_erased in Hr; [|apply erase_erased|apply dnf_qNat].
destruct Hr as (m&Heq&Hr).
apply erased_qNat in Heq; subst.
apply sred_dredalg in Hr; [|apply dnf_qNat].
destruct Hr as (m&Heq&Hr).
symmetry in Heq; apply eqannot_qNat_inv in Heq; now subst.
Qed.
