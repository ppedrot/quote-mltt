From Coq Require Import CRelationClasses ssrbool.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Computation Notations Context Closed NormalForms NormalEq Weakening UntypedReduction.

Reserved Notation "[ t ⇉ u ]" (at level 0, t, u at level 50).

Inductive pred : term -> term -> Set :=
| pred_rel {n} : [tRel n ⇉ tRel n]
| pred_sort {s} : [tSort s ⇉ tSort s]
| pred_prod {A A' B B'} : [A ⇉ A'] -> [B ⇉ B'] -> [tProd A B ⇉ tProd A' B']
| pred_lambda {A A' t t'} : [t ⇉ t'] -> [tLambda A t ⇉ tLambda A' t']
| pred_app {t t' u u'} : [t ⇉ t'] -> [u ⇉ u'] -> [tApp t u ⇉ tApp t' u']
| pred_beta {A t t' u u'} : [t ⇉ t'] -> [u ⇉ u'] -> [tApp (tLambda A t) u ⇉ t'[u'..]]
| pred_nat : [tNat ⇉ tNat]
| pred_zero : [tZero ⇉ tZero]
| pred_succ {t t'} : [t ⇉ t'] -> [tSucc t ⇉ tSucc t']
| pred_natelim {P P' hz hz' hs hs' t t'} :
  [P ⇉ P'] -> [hz ⇉ hz'] -> [hs ⇉ hs'] -> [t ⇉ t'] -> [tNatElim P hz hs t ⇉ tNatElim P' hz' hs' t']
| pred_natelimzero {P hz hz' hs} : [hz ⇉ hz'] -> [tNatElim P hz hs tZero ⇉ hz']
| pred_natelimsucc {P P' hz hz' hs hs' t t'} : [P ⇉ P'] -> [hz ⇉ hz'] -> [hs ⇉ hs'] -> [t ⇉ t'] ->
  [tNatElim P hz hs (tSucc t) ⇉ tApp (tApp hs' t') (tNatElim P' hz' hs' t')]
| pred_empty : [tEmpty ⇉ tEmpty]
| pred_emptyelim {P P' t t'} : [P ⇉ P'] -> [t ⇉ t'] -> [tEmptyElim P t ⇉ tEmptyElim P' t']
| pred_sig {A A' B B'} : [A ⇉ A'] -> [B ⇉ B'] -> [tSig A B ⇉ tSig A' B']
| pred_pair {A A' B B' a a' b b'} : [a ⇉ a'] -> [b ⇉ b'] ->
  [tPair A B a b ⇉ tPair A' B' a' b']
| pred_fst {t t'} : [t ⇉ t'] -> [tFst t ⇉ tFst t']
| pred_fst_beta {A B a a' b} : [a ⇉ a'] -> [tFst (tPair A B a b) ⇉ a']
| pred_snd {t t'} : [t ⇉ t'] -> [tSnd t ⇉ tSnd t']
| pred_snd_beta {A B a b b'} : [b ⇉ b'] -> [tSnd (tPair A B a b) ⇉ b']
| pred_id {A A' t t' u u'} : [A ⇉ A'] -> [t ⇉ t'] -> [u ⇉ u'] -> [tId A t u ⇉ tId A' t' u']
| pred_idrefl {A A' t t'} : [A ⇉ A'] -> [t ⇉ t'] -> [tRefl A t ⇉ tRefl A' t']
| pred_idelim {A A' x x' P P' hr hr' y y' e e'} :
  [A ⇉ A'] -> [x ⇉ x'] -> [P ⇉ P'] -> [hr ⇉ hr'] -> [y ⇉ y'] -> [e ⇉ e'] ->
  [tIdElim A x P hr y e ⇉ tIdElim A' x' P' hr' y' e']
| pred_idelimrefl {A x P hr hr' y B z} : [hr ⇉ hr'] ->
  [tIdElim A x P hr y (tRefl B z) ⇉ hr']
| pred_quote {t t'} : [t ⇉ t'] -> [tQuote t ⇉ tQuote t']
| pred_quoteeval {t} : dnf (unannot t) -> closed0 t -> [tQuote t ⇉ qNat (quote (erase t))]
| pred_step {t t' u u'} : [t ⇉ t'] -> [u ⇉ u'] -> [tStep t u ⇉ tStep t' u']
| pred_stepeval {t u n k k'} :
  dnf (unannot t) -> closed0 t ->
  murec (fun k => eval true (tApp (erase t) (qNat u)) k) k = Some (k', qNat n) ->
  [tStep t (qNat u) ⇉ qNat k']
| pred_reflect {t t' u u'} : [t ⇉ t'] -> [u ⇉ u'] -> [tReflect t u ⇉ tReflect t' u']
| pred_reflecteval {t u n k k'} :
  dnf t -> closed0 t ->
  murec (fun k => eval true (tApp (erase t) (qNat u)) k) k = Some (k', qNat n) ->
  [tReflect t (qNat u) ⇉ qEvalTm k' n]

where "[ t ⇉ u ]" := (pred t u).

Lemma pred_refl : forall t, [t ⇉ t].
Proof.
induction t; try eauto using pred.
Qed.

Lemma red_pred : forall t u, [t ⇶ u] -> [t ⇉ u].
Proof.
induction 1; try eauto 10 using pred, pred_refl, dnf_unannot.
Qed.

Lemma closed0_qNat : forall n, closed0 (qNat n).
Proof.
unfold closed0; induction n; cbn; eauto.
Qed.

Lemma dnf_dne_pred_id : (forall t, dnf t -> forall u, [t ⇉ u] -> eqannot t u) × (forall t, dne t -> forall u, [t ⇉ u] -> eqannot t u).
Proof.
unfold eqannot.
apply dnf_dne_rect; intros.
all: match goal with H : [?t ⇉ ?u] |- _ => inversion H; subst end; cbn in *; eauto.
all: try match goal with H : dne _ |- _ => now inversion H end; cbn in *.
all: try now (f_equal; eauto).
all: try match goal with H : forall u, [?t ⇉ u] -> _, H' : [?t ⇉ ?u] |- _ => specialize (H _ H'); cbn in H; injection H; intros; subst end.
all: try now (f_equal; tea).
+ inversion d; subst; inversion H12.
+ contradiction.
+ assert (closed0 (qNat u1)) by apply closed0_qNat.
  destruct s; contradiction.
+ assert (closed0 (qNat u1)) by apply closed0_qNat.
  destruct s; contradiction.
Qed.

Lemma dnf_pred_id : forall t u, dnf t -> [t ⇉ u] -> eqannot t u.
Proof.
intros t u Hnf Hr; eapply dnf_dne_pred_id in Hnf; tea.
Qed.

Lemma pred_ren : forall t t' ρ, ren_inj ρ -> [t ⇉ t'] -> [t⟨ρ⟩ ⇉ t'⟨ρ⟩].
Proof.
intros t t' ρ Hρ Ht; revert ρ Hρ; induction Ht; cbn; eauto 10 using pred, upRen_term_term_inj.
+ intros ρ Hρ.
  replace t'[u'..]⟨ρ⟩ with t'⟨upRen_term_term ρ⟩[u'⟨ρ⟩..] by now bsimpl.
  eauto using pred, upRen_term_term_inj.
+ intros ρ Hρ.
  rewrite quote_ren; tea.
  constructor; [|now apply closed0_ren].
  rewrite <- unannot_ren; eauto using dnf_ren.
+ intros ρ Hρ.
  rewrite !qNat_ren.
  assert (dnf (unannot t⟨ρ⟩)).
  { rewrite <- unannot_ren; [|tea].
    now apply dnf_ren. }
  econstructor; eauto using closed0_ren.
  rewrite erase_is_closed0_ren_id; tea.
+ intros ρ Hρ.
  rewrite qNat_ren, qEvalTm_ren.
  assert (dnf t⟨ρ⟩) by now apply dnf_ren.
  econstructor; eauto using closed0_ren.
  rewrite erase_is_closed0_ren_id; tea.
Qed.

Lemma pred_subst : forall t t' σ σ', [t ⇉ t'] -> (forall n, [σ n ⇉ σ' n]) -> [t[σ] ⇉ t'[σ']].
Proof.
assert (Hup : forall σ σ', (forall n, [σ n ⇉ σ' n]) -> (forall n, [up_term_term σ n ⇉ up_term_term σ' n])).
{ intros σ σ' Hσ []; cbn; [now constructor|].
  apply pred_ren, Hσ. apply shift_inj. }
intros t t' σ σ' Ht; revert σ σ'; induction Ht; intros σ σ' Hσ; cbn; eauto 10 using pred.
+ replace t'[u'..][σ'] with t'[up_term_term σ'][u'[σ']..] by now bsimpl.
  eauto using pred.
+ rewrite qNat_subst, <- (qNat_subst _ σ).
  rewrite quote_subst; tea; constructor.
  - rewrite unannot_closed0_subst; tea.
  - now apply closed0_subst.
+ rewrite !qNat_subst.
  econstructor.
  - rewrite unannot_closed0_subst; tea.
  - now apply closed0_subst.
  - rewrite erase_is_closed0_subst_id; tea.
+ rewrite qNat_subst, qEvalTm_subst.
  econstructor.
  - now apply dnf_closed0_subst.
  - now apply closed0_subst.
  - rewrite erase_is_closed0_subst_id; tea.
Qed.

Lemma pred_subst1 : forall t t' u u', [t ⇉ t'] -> [u ⇉ u'] -> [t[u..] ⇉ t'[u'..]].
Proof.
intros; apply pred_subst; tea.
intros []; cbn; [tea|].
apply pred_refl.
Qed.

Lemma pred_closedn : forall t u n, [t ⇉ u] -> closedn n t -> closedn n u.
Proof.
unfold closedn.
intros t u n Hr; revert n; induction Hr; intros ? Hc; cbn in *.
all: repeat match goal with H : _ |- _ => apply andb_prop in H; destruct H end.
all: repeat (apply andb_true_intro; split).
all: try match goal with |- is_true true => constructor end.
all: try match goal with H : forall n : nat, _ |- _ => now apply H end.
+ tea.
+ apply closedn_beta; [apply IHHr1|apply IHHr2]; tea.
+ apply closedn_qNat.
+ apply closedn_qNat.
+ apply closedn_qEvalTm.
Qed.

Lemma closed0_unannot : forall t, closed0 t -> closed0 (unannot t).
Proof.
intros; unfold closed0; now rewrite closedn_unannot.
Qed.

Lemma pred_unannot_id : forall t t', dnf (unannot t) -> [t ⇉ t'] -> unannot t = unannot t'.
Proof.
induction t; cbn; intros t' Hnf Hr; inversion Hr; subst; cbn; inversion Hnf; subst.
all: try match goal with H : dne _ |- _ => now inversion H end.
all: try now eauto using pred.
all: try now (f_equal; eauto using pred).
all: try now match goal with H : dne _ |- _ => f_equal; inversion H; subst; eauto using pred, dne, dnf end.
all: try now do 2 match goal with H : dne _ |- _ => inversion H; subst end.
+ match goal with H : dne _ |- _ => inversion H; subst end.
  assert (closed0 (unannot t)) by now apply closed0_unannot.
  contradiction.
+ match goal with H : dne _ |- _ => inversion H; subst end.
  assert (closed0 (unannot t1)) by now apply closed0_unannot.
  assert (closed0 (unannot (qNat u))).
  { rewrite unannot_qNat; apply closed0_qNat. }
  destruct H5; contradiction.
+ match goal with H : dne _ |- _ => inversion H; subst end.
  assert (closed0 (unannot t1)) by now apply closed0_unannot.
  assert (closed0 (unannot (qNat u))).
  { rewrite unannot_qNat; apply closed0_qNat. }
  destruct H5; contradiction.
Qed.

Lemma pred_tLambda_inv : forall A A' t t', [tLambda A t ⇉ tLambda A' t'] -> [t ⇉ t'].
Proof.
inversion 1; subst; eauto.
Qed.

Lemma pred_tSucc_inv : forall t t', [tSucc t ⇉ tSucc t'] -> [t ⇉ t'].
Proof.
inversion 1; subst; eauto.
Qed.

Lemma pred_tPair_inv_fst : forall A A' B B' a a' b b', [tPair A B a b ⇉ tPair A' B' a' b'] -> [a ⇉ a'].
Proof.
inversion 1; subst; eauto.
Qed.

Lemma pred_tPair_inv_snd : forall A A' B B' a a' b b', [tPair A B a b ⇉ tPair A' B' a' b'] -> [b ⇉ b'].
Proof.
inversion 1; subst; eauto.
Qed.

Definition diamond t :=
  forall tl tr, [t ⇉ tl] -> [t ⇉ tr] -> ∑ v, [tl ⇉ v] × [tr ⇉ v].

Lemma diamond_tLambda_inv : forall A t, diamond (tLambda A t) -> diamond t.
Proof.
intros A t IH tl tr Hl Hr.
edestruct IH as (v&Hlv&Hrv).
+ eapply (pred_lambda (A' := A) (t' := tl)); eauto using pred_refl.
+ eapply (pred_lambda (A' := A) (t' := tr)); eauto using pred_refl.
+ inversion Hlv; subst; inversion Hrv; subst; eexists; split; tea.
Qed.

Lemma diamond_tSucc_inv : forall t, diamond (tSucc t) -> diamond t.
Proof.
intros t IH tl tr Hl Hr.
edestruct IH as (v&Hlv&Hrv).
+ now eapply (pred_succ (t' := tl)).
+ now eapply (pred_succ (t' := tr)).
+ inversion Hlv; subst; inversion Hrv; subst; eexists; split; tea.
Qed.

Lemma diamond_tPair_inv_fst : forall A B a b, diamond (tPair A B a b) -> diamond a.
Proof.
intros A B a b IH tl tr Hl Hr.
edestruct IH as (v&Hlv&Hrv).
+ eapply (pred_pair (A' := A) (B' := B) (a' := tl)); eauto using pred_refl.
+ eapply (pred_pair (A' := A) (B' := B) (a' := tr)); eauto using pred_refl.
+ inversion Hlv; subst; inversion Hrv; subst; eexists; split; tea.
Qed.

Lemma diamond_tPair_inv_snd : forall A B a b, diamond (tPair A B a b) -> diamond b.
Proof.
intros A B a b IH tl tr Hl Hr.
edestruct IH as (v&Hlv&Hrv).
+ eapply (pred_pair (A' := A) (B' := B) (b' := tl)); eauto using pred_refl.
+ eapply (pred_pair (A' := A) (B' := B) (b' := tr)); eauto using pred_refl.
+ inversion Hlv; subst; inversion Hrv; subst; eexists; split; tea.
Qed.

#[local] Ltac saturate_diamond :=
  repeat match goal with
  | H : diamond ?t, H' : [?t ⇉ _], H'' : [?t ⇉ _] |- _ =>
    specialize (H _ _ H' H''); destruct H as (?&?&?)
  end.

Lemma eqannot_qNat_inv : forall t n, eqannot t (qNat n) -> t = qNat n.
Proof.
intros t n; revert t; induction n; intros t Ht; cbn in *; destruct t; cbn in Ht; try discriminate Ht.
+ reflexivity.
+ f_equal; apply IHn; unfold eqannot in *; cbn in Ht; congruence.
Qed.

Lemma pred_diamond : forall t, diamond t.
Proof.
intros t; induction t; intros tl lr Hrl Hrr; inversion Hrl; subst; inversion Hrr; subst.
all: try now (eexists; eauto using pred).
all: try now saturate_diamond; eauto 10 using pred.
+ inversion H1; subst; clear H1.
  apply diamond_tLambda_inv in IHt1.
  saturate_diamond.
  eexists; split.
  - now constructor.
  - eapply pred_subst1; tea.
+ inversion H2; subst; clear H2.
  apply diamond_tLambda_inv in IHt1.
  saturate_diamond.
  eexists; split.
  - eapply pred_subst1; tea.
  - now constructor.
+ apply diamond_tLambda_inv in IHt1.
  saturate_diamond.
  eexists; split.
  - eapply pred_subst1; tea.
  - eapply pred_subst1; tea.
+ inversion H7; subst; clear H7.
  saturate_diamond.
  eexists projT1; split; eauto using pred.
+ inversion H7; subst; clear H7.
  apply diamond_tSucc_inv in IHt4.
  saturate_diamond.
  eexists; split; [eapply pred_natelimsucc|]; eauto using pred.
+ inversion H8; subst; clear H8.
  saturate_diamond.
  eexists; split; eauto using pred.
+ inversion H11; subst; clear H11.
  apply diamond_tSucc_inv in IHt4.
  saturate_diamond.
  eexists; split; [|eapply pred_natelimsucc]; eauto using pred.
+ apply diamond_tSucc_inv in IHt4.
  saturate_diamond.
  eexists; split; eauto using pred.
+ apply diamond_tPair_inv_fst in IHt.
  inversion H0; subst.
  saturate_diamond.
  eexists; split; eauto using pred.
+ apply diamond_tPair_inv_fst in IHt.
  inversion H1; subst.
  saturate_diamond.
  eexists; split; eauto using pred.
+ apply diamond_tPair_inv_fst in IHt.
  saturate_diamond.
  eexists; split; eauto.
+ apply diamond_tPair_inv_snd in IHt.
  inversion H0; subst.
  saturate_diamond.
  eexists; split; eauto using pred.
+ apply diamond_tPair_inv_snd in IHt.
  inversion H1; subst.
  saturate_diamond.
  eexists; split; eauto using pred.
+ apply diamond_tPair_inv_snd in IHt.
  saturate_diamond.
  eexists; split; eauto using pred.
+ inversion H11; subst.
  clear IHt6; saturate_diamond.
  eexists; split; eauto using pred.
+ inversion H12; subst.
  clear IHt6; saturate_diamond.
  eexists; split; eauto using pred.
+ eexists; split; [|eapply pred_refl].
  assert (Heq : unannot t = unannot t') by now apply pred_unannot_id.
  assert (Hrw : erase t = erase t').
  { rewrite !erase_unannot_etared; now f_equal. }
  rewrite Hrw; constructor.
  - now rewrite <- Heq.
  - unfold closed0; rewrite <- closedn_unannot, <- Heq, closedn_unannot; tea.
+ eexists; split; [eapply pred_refl|].
  assert (Heq : unannot t = unannot t') by now apply pred_unannot_id.
  assert (Hrw : erase t = erase t').
  { rewrite !erase_unannot_etared; now f_equal. }
  rewrite Hrw; constructor.
  - now rewrite <- Heq.
  - unfold closed0; rewrite <- closedn_unannot, <- Heq, closedn_unannot; tea.
+ eexists; split; eapply pred_refl.
+ eexists; split; [|eapply pred_refl].
  apply dnf_pred_id in H3; [|apply dnf_qNat].
  symmetry in H3; apply eqannot_qNat_inv in H3; subst.
  assert (Heq : unannot t1 = unannot t') by now apply pred_unannot_id.
  assert (Hrw : erase t1 = erase t').
  { rewrite !erase_unannot_etared; now f_equal. }
  econstructor.
  - now rewrite <- Heq.
  - unfold closed0; rewrite <- closedn_unannot, <- Heq, closedn_unannot; tea.
  - now rewrite <- Hrw.
+ eexists; split; [eapply pred_refl|].
  apply dnf_pred_id in H6; [|apply dnf_qNat].
  symmetry in H6; apply eqannot_qNat_inv in H6; subst.
  assert (Heq : unannot t1 = unannot t') by now apply pred_unannot_id.
  assert (Hrw : erase t1 = erase t').
  { rewrite !erase_unannot_etared; now f_equal. }
  econstructor.
  - now rewrite <- Heq.
  - unfold closed0; rewrite <- closedn_unannot, <- Heq, closedn_unannot; tea.
  - now rewrite <- Hrw.
+ apply qNat_inj in H0; subst.
  match goal with H : _ = Some ?r, H' : _ = Some ?r' |- _ =>
    assert (Hrw : r = r') by (now eapply murec_det)
  end.
  injection Hrw; intros; subst; clear Hrw.
  eexists; split; apply pred_refl.
+ eexists; split; [|eapply pred_refl].
  apply dnf_pred_id in H3; [|apply dnf_qNat].
  symmetry in H3; apply eqannot_qNat_inv in H3; subst.
  assert (Heq : unannot t1 = unannot t') by eauto using pred_unannot_id, dnf_unannot.
  assert (Hrw : erase t1 = erase t').
  { rewrite !erase_unannot_etared; now f_equal. }
  econstructor.
  - apply dnf_unannot_rev; rewrite <- Heq; now apply dnf_unannot.
  - unfold closed0; rewrite <- closedn_unannot, <- Heq, closedn_unannot; tea.
  - now rewrite <- Hrw.
+ eexists; split; [eapply pred_refl|].
  apply dnf_pred_id in H6; [|apply dnf_qNat].
  symmetry in H6; apply eqannot_qNat_inv in H6; subst.
  assert (Heq : unannot t1 = unannot t') by eauto using pred_unannot_id, dnf_unannot.
  assert (Hrw : erase t1 = erase t').
  { rewrite !erase_unannot_etared; now f_equal. }
  econstructor.
  - apply dnf_unannot_rev; rewrite <- Heq; now apply dnf_unannot.
  - unfold closed0; rewrite <- closedn_unannot, <- Heq, closedn_unannot; tea.
  - now rewrite <- Hrw.
+ apply qNat_inj in H0; subst.
  match goal with H : _ = Some ?r, H' : _ = Some ?r' |- _ =>
    assert (Hrw : r = r') by (now eapply murec_det)
  end.
  injection Hrw; intros; subst; clear Hrw.
  apply qNat_inj in H; subst.
  eexists; split; apply pred_refl.
Unshelve. all: exact U.
Qed.

Inductive pred_clos : term -> term -> Set :=
| pred_clos_refl : forall t, pred_clos t t
| pred_clos_step : forall t u r, pred t u -> pred_clos u r -> pred_clos t r.

Notation "[ t ⇉* u ]" := (pred_clos t u) (at level 0, t, u at level 50).

Lemma pred_trans : forall t u r, [t ⇉* u] -> [u ⇉* r] -> [t ⇉* r].
Proof.
intros t u r Hl; revert r; induction Hl; eauto using pred_clos.
Qed.

#[export] Instance PreOrder_pred_clos : CRelationClasses.PreOrder pred_clos.
Proof.
split.
+ intros ?; constructor.
+ intros ??? **; now eapply pred_trans.
Qed.

Lemma dnf_pred_clos_id : forall t u, dnf t -> [t ⇉* u] -> eqannot t u.
Proof.
induction 2; try reflexivity.
apply dnf_pred_id in p; [|tea].
etransitivity; [tea|].
now eapply IHpred_clos, dnf_eqannot.
Qed.

Lemma pred_confluent : forall t tl tr, [t ⇉* tl] -> [t ⇉* tr] -> ∑ v, [tl ⇉* v] × [tr ⇉* v].
Proof.
intros t tl tr Hl; revert tr; induction Hl; intros tl Hr.
+ exists tl; split; eauto using pred_clos.
+ enough (∑ v, [tl ⇉* v] × [u ⇉* v]) as (v&?&?).
  { apply IHHl in p1 as (w&?&?); exists w; split; tea.
    now eapply pred_trans. }
  clear - p Hr.
  revert u p; induction Hr; intros v Hv.
  - exists v; split; [eauto using pred_clos|constructor].
  - destruct (pred_diamond t u v) as (w&Hu&?); tea.
    destruct (IHHr _ Hu) as (z&?&?); exists z; split; tea.
    now econstructor.
Qed.

Lemma pred_clos_closedn : forall t u n, [t ⇉* u] -> closedn n t -> closedn n u.
Proof.
induction 1; intros; [tea|].
now eapply IHpred_clos, pred_closedn.
Qed.

Lemma dredalg_pred_clos : forall t u, [t ⇶* u] -> [t ⇉* u].
Proof.
induction 1; eauto using pred_clos, red_pred.
Qed.

Lemma pred_clos_app : forall t t' u, [t ⇉* t'] -> [tApp t u ⇉* tApp t' u].
Proof.
intros t t' u Hr; revert u; induction Hr; intros a.
+ constructor.
+ econstructor; [|apply IHHr].
  constructor; [tea|now apply pred_refl].
Qed.

Lemma pred_clos_lambda : forall A A' t t', [t ⇉* t'] -> [tLambda A t ⇉* tLambda A' t'].
Proof.
intros A A' t t' Hr; revert A A'; induction Hr; intros; eauto using pred, pred_clos, pred_refl.
Unshelve. all: exact U.
Qed.

Lemma pred_clos_quote : forall t t', [t ⇉* t'] -> [tQuote t ⇉* tQuote t'].
Proof.
induction 1; eauto using pred, pred_refl, pred_clos.
Qed.

(* Ad-hoc stuff needed to prove the logical relation *)

Lemma dred_tApp_qNat_closed0 : forall t t₀ n r₀,
  [t ⇶* t₀] -> [tApp t (qNat n) ⇶* r₀] -> dnf t₀ -> dnf r₀ ->
  closed0 t₀ -> closed0 r₀.
Proof.
intros * Ht Happ Htnf Hrnf Hc.
apply dredalg_pred_clos in Ht.
apply dredalg_pred_clos in Happ.
eapply pred_clos_app with (u := (qNat n)) in Ht.
edestruct (pred_confluent) as (v&Hw&Hv); [apply Ht|apply Happ|].
eapply dnf_pred_clos_id in Hv; [|tea].
eapply closed0_eqannot; [symmetry; tea|].
eapply pred_clos_closedn; [apply Hw|].
unfold closedn; cbn; apply andb_true_intro; split.
+ tea.
+ apply closed0_qNat.
Qed.
