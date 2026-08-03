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

Definition hasNf_red {Γ l A A' t u} {rA : [Γ ||-<l> A ≅ A']} (p : [rA | Γ ||- t ≅ u : _ ≅ _]) :
  ∑ t₀ : term, isNf t t₀.
Proof.
apply escapeTm in p.
destruct p as (?&?&p).
apply SN.(snty_nf) in p.
destruct p as (?&?&?&?).
now eexists.
Qed.

Lemma isNf_TypeRedWf_red : forall Γ A A₀ B,
  [Γ |- A :⤳*: B] -> isNf A A₀ -> isNf B A₀.
Proof.
intros.
eapply isNf_red; [|tea].
eapply redty_sound, tyr_wf_red; tea.
Qed.

Lemma isNf_TermRedWf_red : forall Γ A t u u₀,
  [Γ |- u :⤳*: t : A] -> isNf u u₀ -> isNf t u₀.
Proof.
intros.
eapply isNf_red; [|tea].
now eapply redtm_sound, tmr_wf_red; tea.
Qed.

Lemma isNf_TypeRedWf_exp : forall Γ A A₀ B,
  [Γ |- A :⤳*: B] -> isNf B A₀ -> isNf A A₀.
Proof.
intros.
eapply isNf_exp; [|tea].
eapply redty_sound, tyr_wf_red; tea.
Qed.

Lemma isNf_TermRedWf_exp : forall Γ A t u u₀,
  [Γ |- u :⤳*: t : A] -> isNf t u₀ -> isNf u u₀.
Proof.
intros.
eapply isNf_exp; [|tea].
now eapply redtm_sound, tmr_wf_red; tea.
Qed.

Definition hasNf_redty {Γ l A A'} (rA : [Γ ||-<l> A ≅ A']) : ∑ A₀ : term, isNf A A₀.
Proof.
indLR rA; cbn.
+ intros []; exists U; split; eauto using dnf.
  now eapply dred_red, redtywf_red.
+ intros [???? Heq].
  apply convtm_convneu in Heq; [|constructor].
  apply SN.(snty_nf) in Heq.
  destruct Heq as (t₀&?&?&?&?&?&?).
  exists t₀; now eapply isNf_TypeRedWf_exp.
+ intros [dom ? cod ? []]; cbn; intros IHdom IHcod.
  enough (∑ A₀, isNf (tProd dom cod) A₀) as [A₀].
  { exists A₀; now eapply isNf_TypeRedWf_exp. }
  assert (rΓ : [|- Γ]) by gtyping.
  specialize (IHdom Γ wk_id rΓ).
  rewrite wk_id_ren_on in IHdom.
  destruct IHdom as [dom₀ ?].
  assert (rΓd : [|- Γ,, dom]) by gtyping.
  specialize (IHcod _ (tRel 0) (tRel 0) (wk1 dom) rΓd).
  destruct IHcod as [cod₀ Hcod].
  - apply var0; tea; now bsimpl.
  - exists (tProd dom₀ cod₀); apply isNf_tProd; tea.
    now rewrite var0_wk1_id in Hcod.
+ intros []; exists tNat; split; eauto using dnf.
  now eapply dred_red, redtywf_red.
+ intros []; exists tEmpty; split; eauto using dnf.
  now eapply dred_red, redtywf_red.
+ intros [dom ? cod ? []]; cbn; intros IHdom IHcod.
  enough (∑ A₀, isNf (tSig dom cod) A₀) as [A₀].
  { exists A₀; now eapply isNf_TypeRedWf_exp. }
  assert (rΓ : [|- Γ]) by gtyping.
  specialize (IHdom Γ wk_id rΓ).
  rewrite wk_id_ren_on in IHdom.
  destruct IHdom as [dom₀ ?].
  assert (rΓd : [|- Γ,, dom]) by gtyping.
  specialize (IHcod _ (tRel 0) (tRel 0) (wk1 dom) rΓd).
  destruct IHcod as [cod₀ Hcod].
  - apply var0; tea; now bsimpl.
  - exists (tSig dom₀ cod₀); apply isNf_tSig; tea.
    now rewrite var0_wk1_id in Hcod.
+ intros [T ? lhs ? rhs ? ?? ?? rL rR]; cbn; intros [T₀].
  enough (∑ A₀, isNf (tId T lhs rhs) A₀) as [A₀].
  { exists A₀; now eapply isNf_TypeRedWf_exp. }
  apply hasNf_red in rL as [lhs₀].
  apply hasNf_red in rR as [rhs₀].
  exists (tId T₀ lhs₀ rhs₀); now apply isNf_tId.
Qed.

Lemma isNf_tSucc_inv : forall t t₀, isNf (tSucc t) (tSucc t₀) -> isNf t t₀.
Proof.
intros; constructor.
+ now eapply redalg_succ_inv, isnf_red.
+ enough (Hnf : dnf (tSucc t₀)).
  { apply dnf_is_dnf in Hnf; apply is_dnf_dnf; exact Hnf. }
  now eapply isnf_dnf.
Qed.

Lemma isNf_tProd_inv : forall A A₀ B B₀, isNf (tProd A B) (tProd A₀ B₀) -> isNf A A₀ × isNf B B₀.
Proof.
intros * [Hred Hnf].
assert (Hr : [tProd A B ⇊ tProd A₀ B₀]) by now apply dredalg_bigstep.
inversion Hr; subst.
split; split; eauto using bigstep_dredalg, bigstep_dnf.
Qed.

Lemma isNf_tSig_inv : forall A A₀ B B₀, isNf (tSig A B) (tSig A₀ B₀) -> isNf A A₀ × isNf B B₀.
Proof.
intros * [Hred Hnf].
assert (Hr : [tSig A B ⇊ tSig A₀ B₀]) by now apply dredalg_bigstep.
inversion Hr; subst.
split; split; eauto using bigstep_dredalg, bigstep_dnf.
Qed.

Lemma isNf_tPair_inv : forall A A₀ B B₀ a a₀ b b₀, isNf (tPair A B a b) (tPair A₀ B₀ a₀ b₀) -> isNf a a₀ × isNf b b₀.
Proof.
intros * [Hred Hnf].
assert (Hr : [tPair A B a b ⇊ tPair A₀ B₀ a₀ b₀]) by now apply dredalg_bigstep.
inversion Hr; subst.
prod_splitter; split; eauto using bigstep_dredalg, bigstep_dnf.
Qed.

Lemma isNf_tId_inv : forall A A₀ t t₀ u u₀, isNf (tId A t u) (tId A₀ t₀ u₀) -> isNf A A₀ × isNf t t₀ × isNf u u₀.
Proof.
intros * [Hred Hnf].
assert (Hr : [tId A t u ⇊ tId A₀ t₀ u₀]) by now apply dredalg_bigstep.
inversion Hr; subst.
split; [|split]; split; eauto using bigstep_dredalg, bigstep_dnf.
Qed.

Lemma eqnf_nfeval_app_compat : forall f f₀ g g₀ a a₀ b b₀ v₀ w₀,
  isNf f f₀ -> isNf g g₀ -> isNf a a₀ -> isNf b b₀ ->
  isNf (tApp f a) v₀ -> isNf (tApp g b) w₀ ->
  eqnf f₀ g₀ -> eqnf a₀ b₀ ->
  eqnf v₀ w₀.
Proof.
intros * [] [] [] [] [] [] Heq1 Heq2.
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

Lemma eqnf_nfeval_subst_compat : forall f f₀ g g₀ a a₀ b b₀ v₀ w₀,
  isNf f f₀ -> isNf g g₀ -> isNf a a₀ -> isNf b b₀ ->
  isNf (f[a..]) v₀ -> isNf (g[b..]) w₀ ->
  eqnf f₀ g₀ -> eqnf a₀ b₀ ->
  eqnf v₀ w₀.
Proof.
intros.
apply (eqnf_nfeval_app_compat (tLambda U f) (tLambda U f₀) (tLambda U g) (tLambda U g₀) a a₀ b b₀ v₀ w₀); eauto using isNf_tLambda, eqnf_tLambda.
+ eapply isNf_exp; [|tea].
  eapply redalg_one_step; constructor.
+ eapply isNf_exp; [|tea].
  eapply redalg_one_step; constructor.
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

Inductive same_head : term -> term -> Set :=
| same_head_Sort : forall s1 s2, same_head (tSort s1) (tSort s2)
| same_head_Prod : forall A1 A2 B1 B2, same_head (tProd A1 B1) (tProd A2 B2)
| same_head_Lambda : forall A1 A2 t1 t2, same_head (tLambda A1 t1) (tLambda A2 t2)
| same_head_Nat : same_head tNat tNat
| same_head_Zero : same_head tZero tZero
| same_head_Succ : forall t1 t2, same_head (tSucc t1) (tSucc t2)
| same_head_Empty : same_head tEmpty tEmpty
| same_head_Sig : forall A1 A2 B1 B2, same_head (tSig A1 B1) (tSig A2 B2)
| same_head_Pair : forall A1 A2 B1 B2 a1 a2 b1 b2, same_head (tPair A1 B1 a1 b1) (tPair A2 B2 a2 b2)
| same_head_Id : forall A1 A2 t1 t2 u1 u2, same_head (tId A1 t1 u1) (tId A2 t2 u2)
| same_head_Refl : forall A1 A2 t1 t2, same_head (tRefl A1 t1) (tRefl A2 t2)
| same_head_whne : forall w1 w2, whne w1 -> whne w2 -> same_head w1 w2.

Lemma whne_same_head_refl : forall t, whne t -> same_head t t.
Proof.
now constructor.
Qed.

Lemma whnf_same_head_refl : forall t, whnf t -> same_head t t.
Proof.
inversion 1; subst; now constructor.
Qed.

Lemma same_head_sym : forall t u, same_head t u -> same_head u t.
Proof.
induction 1; eauto using same_head.
Qed.

Lemma same_head_whnf : forall t u, same_head t u -> whnf t.
Proof.
induction 1; eauto using whnf.
Qed.

Lemma same_head_trans : forall t u r, same_head t u -> same_head u r -> same_head t r.
Proof.
intros t u r Hl Hr; revert r Hr; induction Hl; intros r Hr; inversion Hr; subst; eauto using same_head.
all: try match goal with [ H : whne _ |- _ ] => now inversion H end.
Qed.

#[local] Instance PER_same_head : CRelationClasses.PER same_head.
Proof.
split.
+ repeat intro; now apply same_head_sym.
+ repeat intro; now eapply same_head_trans.
Qed.

Lemma dred_whnf_same_head : forall t u,
  [t ⇶ u] -> whnf t -> same_head t u.
Proof.
intros t u Hr Ht; revert u Hr.
induction Ht; intros ? Hr; inversion Hr; subst; first [now constructor|idtac].
all: let H := match goal with [ H : whne _ |- _ ] => H end in
  try (apply whne_is_whne in H; cbn in H; first [discriminate H| apply is_whne_whne in H]).
all: try (constructor; eauto 2 using whne).
all: try now (exfalso; eapply whne_nored; eauto 2 using whne).
all: eauto 2 using whne, dred_whne.
Qed.

Lemma dredalg_whnf_same_head : forall t u,
  [t ⇶* u] -> whnf t -> same_head t u.
Proof.
intros t u Hr Ht; induction Hr.
+ now apply whnf_same_head_refl.
+ assert (same_head t t') by now apply dred_whnf_same_head.
  assert (whnf t') by eauto using same_head_sym, same_head_whnf.
  now eapply same_head_trans.
Qed.

Lemma isNf_whnf_same_head : forall t t₀, isNf t t₀ -> whnf t -> same_head t t₀.
Proof.
intros * Hnf Ht; apply dredalg_whnf_same_head, Ht; apply Hnf.
Qed.

Lemma whne_same_head_whne : forall t u, same_head t u -> whne t -> whne u.
Proof.
induction 1; intros; inv_whne; tea.
Qed.

(*
Lemma eqnf_nfeval_fst_compat : forall p p₀ q q₀ v₀ w₀,
  isNf p p₀ -> isNf q q₀ -> isNf (tFst p) v₀ -> isNf (tFst q) w₀ -> eqnf p₀ q₀ -> eqnf v₀ w₀.
Proof.
assert (Hinv : forall p v₀, isNf (tFst p) v₀ -> ∑ wf, ([p ⤳* wf] × whnf wf × ((∑ A, ∑ B, ∑ a, ∑ b, (wf = tPair A B a b) × [a ⇶* v₀]) + (whne wf)))).
{ intros * [].
  assert (Hr : [tFst p ⇊ v₀]) by now apply dredalg_bigstep.
  inversion Hr; subst; eexists; (split; [|split]); eauto 8 using whnf, bigstep_dredalg. }
intros * ?? Hnp Hnq Heq.
assert (Hrp := Hinv _ _ Hnp); assert (Hrq := Hinv _ _ Hnq).
destruct Hrp as (wp&?&?&Hrp), Hrq as (wq&?&?&Hrq).
assert (Hnfp : isNf wp p₀) by now eapply isNf_red.
assert (Hnfq : isNf wq q₀) by now eapply isNf_red.
assert (Hhp : same_head wp p₀) by eauto using isNf_whnf_same_head.
assert (Hhq : same_head wq q₀) by eauto using isNf_whnf_same_head.
destruct Hrp as [(A&B&a&b&?&?)|], Hrq as [(A'&B'&a'&b'&?&?)|]; subst.
+ inversion Hhp; subst; [|match goal with [ H : whne _ |- _ ] => now inversion H end].
  inversion Hhq; subst; [|match goal with [ H : whne _ |- _ ] => now inversion H end].
  assert (Hrp := isNf_tPair_inv _ _ _ _ _ _ _ _ Hnfp); destruct Hrp.
  assert (Hrq := isNf_tPair_inv _ _ _ _ _ _ _ _ Hnfq); destruct Hrq.
  match goal with [ H : isNf a ?r |- _ ] => assert (r = v₀); [|subst r] end.
  { eauto using dredalg_det, isnf_red, isnf_dnf. }
  match goal with [ H : isNf a' ?r |- _ ] => assert (r = w₀); [|subst r] end.
  { eauto using dredalg_det, isnf_red, isnf_dnf. }
  unfold eqnf in *; cbn in Heq; clear - Heq.
  destruct (eta_pair_intro (erase v₀) (erase b2)); destruct (eta_pair_intro (erase w₀) (erase b0)).
  - congruence.
  - destruct t0; try discriminate Heq.
    injection Heq; intros; subst.
    admit.
Abort. *)

Lemma NeNf_whne : forall Γ A t u, [Γ ||-NeNf t ≅ u : A] -> whne t.
Proof.
intros * []; now eapply convneu_whne.
Qed.

#[local]
Definition without_eta t := match t with
| tLambda _ _ | tPair _ _ _ _ => False
| _ => True
end.

Lemma whne_without_eta : forall t, whne t -> without_eta t.
Proof.
induction 1; constructor.
Qed.

Lemma isType_without_eta : forall t, isType t -> without_eta t.
Proof.
inversion 1; subst; try constructor.
now apply whne_without_eta.
Qed.

Lemma IdPropEq_without_eta : forall Γ A B (r : IdRedTyPack Γ A B) t u, IdRedTmEq.IdPropEq r t u -> without_eta t.
Proof.
intros * Heq.
inversion Heq; subst; eauto using whnf.
+ constructor.
+ now eapply whne_without_eta, NeNf_whne.
Qed.

Lemma eqnf_without_eta_same_head : forall t u,
  whnf t -> whnf u -> eqnf t u -> without_eta t -> without_eta u -> same_head t u.
Proof.
intros t u Ht Hu Heq Hwt Hwu.
induction Ht; try (now elim Hwt); induction Hu; try (now elim Hwu); try discriminate Heq; try now constructor.
all: try (match goal with [ H : whne _ |- _ ] => inversion H; subst end; discriminate Heq).
Qed.

Lemma isNf_without_eta : forall t t₀, isNf t t₀ -> whnf t -> without_eta t -> without_eta t₀.
Proof.
intros * ?? Hwt.
assert (Ht : same_head t t₀) by now apply isNf_whnf_same_head.
induction Ht; first [constructor|elim Hwt|idtac].
now apply whne_without_eta.
Qed.

Lemma isNf_eqnf_same_head : forall t t₀ u u₀,
  isNf t t₀ -> isNf u u₀ -> whnf t -> whnf u -> without_eta t -> without_eta u -> eqnf t₀ u₀ -> same_head t u.
Proof.
intros.
assert (whnf t₀) by now eapply dnf_whnf, isnf_dnf.
assert (whnf u₀) by now eapply dnf_whnf, isnf_dnf.
assert (without_eta t₀) by now eapply isNf_without_eta.
assert (without_eta u₀) by now eapply isNf_without_eta.
enough (same_head t₀ u₀).
+ transitivity t₀; [|transitivity u₀; [|symmetry]]; tea.
  - now apply isNf_whnf_same_head.
  - now apply isNf_whnf_same_head.
+ apply eqnf_without_eta_same_head; tea.
Qed.

Lemma redalg_decide_zero_inv : forall A t t₀ u u₀,
  [tDecide A t u ⤳* tZero] ->
  isNf t t₀ -> isNf u u₀ -> eqnf t₀ u₀.
Proof.
intros A t t₀ u u₀ Hdec.
remember (tDecide A t u) as lhs eqn:Hl; remember tZero as rhs eqn:Hr.
revert A t t₀ u u₀ Hl Hr; induction Hdec as [|lhs mid rhs Hred].
+ intros; subst; inversion Hr.
+ intros; subst.
  assert (forall v, [v ⇶* v]) by reflexivity.
  inversion Hred; subst; try congruence.
  - assert (t = t₀) by (now apply isNf_dnf_det); subst.
    assert (u = u₀) by (now apply isNf_dnf_det); subst.
    now apply term_beq_eq.
  - enough (tSucc tZero = tZero) by congruence.
    apply red_whnf; eauto using whnf.
  - edestruct IHHdec; try reflexivity; eauto using dredalg_one_step, isNf_dred_exp.
  - edestruct IHHdec; try reflexivity; eauto using dredalg_one_step, isNf_dred_exp.
Qed.

Definition eqnf_complete {Γ l A A'} (rA : [Γ ||-<l> A ≅ A']) :=
  forall t t₀ u u₀
  (rt : [rA | Γ ||- t ≅ t : A ≅ _])
  (ru : [rA | Γ ||- u ≅ u : A ≅ _]),
  isNf t t₀ -> isNf u u₀ -> eqnf t₀ u₀ -> [rA | Γ ||- t ≅ u : _].

Lemma eqnf_complete_Ne : forall Γ l A A' (neA : [Γ ||-ne A ≅ A']), eqnf_complete (LRne_ l neA).
Proof.
intros * e e₀ e' e'₀ re re' ?? Heq.
cbn in *; destruct re as [v], re' as [w]; cbn in *.
exists v w; tea.
eapply sncmp_convneu; eauto using tmr_wf_r; try now eapply convneu_whne.
+ now eapply isNf_TermRedWf_red.
+ now eapply isNf_TermRedWf_red.
Qed.

Lemma redtmwf_convtm_exp : forall Γ A t u,
  [Γ |- A] -> [Γ |- A ≅ A] -> [Γ |- u : A] -> [Γ |- u ≅ u : A] ->
  [Γ |- t :⤳*: u : A] -> [Γ |- t ≅ u : A].
Proof.
intros.
eapply convtm_wfexp; tea.
+ now apply redtywf_refl.
+ now apply redtmwf_refl.
Qed.

Lemma NatPropEq_whnf : forall Γ t u, NatPropEq Γ t u -> whnf t.
Proof.
intros * Heq.
inversion Heq; subst; eauto using whnf.
constructor; now eapply NeNf_whne.
Qed.

Lemma IdPropEq_whnf : forall Γ A B (r : IdRedTyPack Γ A B) t u, IdRedTmEq.IdPropEq r t u -> whnf t.
Proof.
intros * Heq.
inversion Heq; subst; eauto using whnf.
constructor; now eapply NeNf_whne.
Qed.

Lemma eqnf_complete_Nat_aux : forall Γ,
  (forall n n', [Γ ||-Nat n ≅ n':Nat] ->
    forall t₀ u u₀, [Γ ||-Nat u ≅ u:Nat] -> isNf n t₀ -> isNf u u₀ -> eqnf t₀ u₀ -> [Γ ||-Nat n ≅ u:Nat]) ×
  (forall n n' (Rnn' : NatPropEq Γ n n'),
    forall t₀ u u₀, [Γ ||-Nat u ≅ u:Nat] -> isNf n t₀ -> isNf u u₀ -> eqnf t₀ u₀ -> [Γ ||-Nat n ≅ u:Nat]).
Proof.
intros; apply NatRedEqInduction.
+ intros t t' nf nf' ??? Heq IH t₀ u u₀ **.
  assert (Hu : [Γ ||-Nat nf ≅ u:Nat]) by eauto using isNf_TermRedWf_red.
  inversion Hu; subst.
  assert (Hr : nf = nfL); [|subst nfL].
  { apply NatPropEq_isNat in Heq as [].
    eapply redtmwf_whnf; [tea|].
    now eapply isNat_whnf. }
  econstructor; tea.
+ intros t₀ u u₀ Hu ?? Heq.
  inversion Hu; subst.
  assert (rΓ : [ |- Γ ]) by gtyping.
  assert (Hru : [natRed (l := zero) rΓ | Γ ||- u ≅ u : tNat]) by apply Hu.
  assert [Γ |- u ≅ u : tNat] by now eapply escapeEqTerm.
  assert [Γ |- tZero : tNat] by gtyping.
  assert [Γ |- tZero ≅ tZero : tNat] by gtyping.
  assert [Γ |- tZero ≅ u : tNat] by now eapply sncmp_convtm.
  assert (isNf nfL u₀) by eauto using isNf_TermRedWf_red.
  assert (whnf nfL) by now eapply NatPropEq_whnf.
  assert (without_eta tZero) by constructor.
  assert (without_eta nfL).
  { inversion prop; subst; try constructor.
    eauto using whne_without_eta, NeNf_whne. }
  assert (Hh : same_head nfL tZero).
  { eapply isNf_eqnf_same_head; eauto using whnf, Symmetric_eqnf. }
  assert (nfL = tZero); [|subst nfL].
  { inversion Hh; subst; [reflexivity|inv_whne]. }
  exists tZero tZero; tea.
  - now apply redtmwf_refl.
  - constructor.
+ intros n n' Hn IH t₀ u u₀ Hu ?? Heq.
  inversion Hu; subst.
  assert (rΓ : [ |- Γ ]) by gtyping.
  assert (Hrn : [natRed (l := zero) rΓ | Γ ||- n ≅ n' : tNat]) by apply Hn.
  assert (Hru : [natRed (l := zero) rΓ | Γ ||- u ≅ u : tNat]) by apply Hu.
  assert [Γ |- n : tNat] by now eapply escapeTerm.
  assert [Γ |- tSucc n : tNat] by gtyping.
  assert (whnf nfL) by now eapply NatPropEq_whnf.
  assert (∑ n₀, t₀ = tSucc n₀) as [n₀ ?]; subst.
  { now eapply redalg_succ_adj, isnf_red. }
  assert (isNf n n₀) by now apply isNf_tSucc_inv.
  assert (isNf nfL u₀) by eauto using isNf_TermRedWf_red.
  assert (Hhu : same_head nfL u₀) by eauto using isNf_whnf_same_head, whnf.
  assert (Hm : ∑ m, nfL = tSucc m × [Γ ||-Nat m ≅ m:Nat]).
  { inversion prop; subst.
    - exfalso; inversion Hhu; subst; [|match goal with [ H : whne _ |- _ ] => now inversion H end].
      discriminate Heq.
    - eexists; split; [reflexivity|].
      eapply transNatRedTmEq; [tea|].
      now apply symNatRedTmEq.
    - assert (whne nfL) by now eapply NeNf_whne.
      assert (Hne : whne u₀) by now eapply whne_same_head_whne.
      inversion Hne; subst; discriminate Heq. }
  destruct Hm as (m&?&?); subst.
  assert (∑ m₀, u₀ = tSucc m₀) as [m₀ ?]; subst.
  { now eapply redalg_succ_adj, isnf_red. }
  assert (isNf m m₀) by now apply isNf_tSucc_inv.
  assert (eqnf n₀ m₀).
  { unfold eqnf in Heq; cbn in Heq; injection Heq; intros; assumption. }
  assert (Hnm : [Γ ||-Nat n ≅ m:Nat]) by now eapply IH.
  assert (Hrnm : [natRed (l := zero) rΓ | Γ ||- n ≅ m : tNat]) by apply Hnm.
  exists (tSucc n) (tSucc m); tea.
  - now apply redtmwf_refl.
  - apply convtm_succ.
    now eapply escapeEqTerm.
  - now constructor.
+ intros ??? t₀ u u₀ Hu ?? Heq.
  inversion Hu; subst.
  assert (rΓ : [ |- Γ ]) by gtyping.
  assert (Hru : [natRed (l := zero) rΓ | Γ ||- u ≅ u : tNat]) by apply Hu.
  assert [Γ |- u ≅ u : tNat] by now eapply escapeEqTerm.
  assert (whne ne) by now eapply NeNf_whne.
  destruct r.
  assert (isNf nfL u₀) by eauto using isNf_TermRedWf_red.
  assert (whnf nfL) by now eapply NatPropEq_whnf.
  assert (Hht : same_head ne t₀) by eauto using isNf_whnf_same_head, whnf.
  assert (Hhu : same_head nfL u₀) by eauto using isNf_whnf_same_head, whnf.
  assert (Hnf : [Γ ||-NeNf nfL ≅ nfR : tNat]).
  { assert (Hne : whne t₀) by now eapply whne_same_head_whne.
    inversion prop; subst; tea; exfalso.
    - inversion Hhu; subst; [|match goal with [ H : whne _ |- _ ] => now inversion H end].
      inversion Hne; subst; discriminate Heq.
    - inversion Hhu; subst; [|match goal with [ H : whne _ |- _ ] => now inversion H end].
      inversion Hne; subst; discriminate Heq. }
  assert (Hne : [Γ ||-NeNf ne ≅ nfL : tNat]).
  { constructor; tea; [apply redL|].
    eapply sncmp_convneu; tea; apply Hnf. }
  exists ne nfL.
  - now apply redtmwf_refl.
  - tea.
  - apply convtm_convneu; [constructor|].
    apply Hne.
  - now constructor.
Qed.

Lemma eqnf_complete_Nat : forall Γ l A A' (NA : [Γ ||-Nat A ≅ A']), eqnf_complete (LRNat_ l NA).
Proof.
intros * t t₀ u u₀ rt ru ?? Heq; cbn in *; clear NA.
now eapply (fst (eqnf_complete_Nat_aux Γ)).
Qed.

Lemma eqnf_complete_Empty : forall Γ l A A' (NA : [Γ ||-Empty A ≅ A']), eqnf_complete (LREmpty_ l NA).
Proof.
intros * t t₀ u u₀ rt ru ?? Heq.
destruct rt as [lhs ? [] [] []], ru as [rhs ? [] [] []].
enough [Γ ||-NeNf lhs ≅ rhs : tEmpty].
{ econstructor; [..|tea]; constructor; tea. }
constructor; tea.
eapply sncmp_convneu; eauto; try now eapply convneu_whne.
+ eapply isNf_red; [|tea].
  eapply redtm_sound; tea.
+ eapply isNf_red; [|tea].
  eapply redtm_sound; tea.
Qed.

Lemma eqnf_complete_Π : forall Γ l A A',
  forall ΠA : [Γ ||-Π<l> A ≅ A'],
  (forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]), eqnf_complete (PolyRed.shpRed ΠA ρ h)) ->
  (forall (Δ : context) (a b : term) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ])
    (ha : [PolyRed.shpRed ΠA ρ h | Δ ||- a ≅ b : (ParamRedTy.domL ΠA)⟨ρ⟩ ≅ (ParamRedTy.domR ΠA)⟨ρ⟩]),
  eqnf_complete (PolyRed.posRed ΠA ρ h ha)) ->
  eqnf_complete (LRPi' ΠA).
Proof.
intros * Hdom Hcod t t₀ u u₀ rt ru ?? Heq.
unshelve econstructor.
+ now eapply PiRedTmEq.redL.
+ now eapply PiRedTmEq.redL.
+ destruct rt as [[] []]; cbn in *.
  destruct ru as [[] []]; cbn in *.
  eapply SNC; [..|apply Heq]; eauto using isNf_TermRedWf_red, tmr_wf_r.
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
  assert (∑ v₀, isNf (tApp wft⟨ρ⟩ a) v₀) as [v₀ Hv] by now eapply hasNf_red.
  assert (∑ w₀, isNf (tApp wfu⟨ρ⟩ b) w₀) as [w₀ Hw] by now eapply hasNf_red.
  assert (∑ a₀, isNf a a₀) as [a₀ Ha] by now eapply hasNf_red.
  assert (∑ b₀, isNf b b₀) as [b₀ Hb] by now eapply hasNf_red.
  unshelve eapply Hcod; [..|tea|tea|]; tea.
  unshelve eapply (eqnf_nfeval_app_compat _ t₀⟨ρ⟩ _ u₀⟨ρ⟩ _ a₀ _ b₀ _ _ _ _ _ _ Hv Hw); eauto.
  - now eapply isNf_wk, isNf_TermRedWf_red.
  - now eapply isNf_wk, isNf_TermRedWf_red.
  - apply eqnf_ren; [apply wk_inj|tea].
  - assert (Htab : [Δ |- a ≅ b : (ParamRedTy.domL ΠA)⟨ρ⟩]) by now escape.
    apply snty_nf in Htab as (r₀&s₀&?&?&?&?&?).
    replace a₀ with r₀ by now eapply isNf_irr.
    replace b₀ with s₀ by now eapply isNf_irr.
    tea.
Qed.

Lemma eqnf_complete_Σ : forall Γ l A A',
  forall ΣA : [Γ ||-Σ< l > A ≅ A'],
  (forall (Δ : context) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ]), eqnf_complete (PolyRed.shpRed ΣA ρ h)) ->
  (forall (Δ : context) (a b : term) (ρ : Δ ≤ Γ) (h : [ |-[ ta ] Δ])
     (ha : [PolyRed.shpRed ΣA ρ h | Δ ||- a ≅ b : (ParamRedTy.domL ΣA)⟨ρ⟩ ≅ (ParamRedTy.domR ΣA)⟨ρ⟩]),
   eqnf_complete (PolyRed.posRed ΣA ρ h ha)) ->
  eqnf_complete (LRSig' ΣA).
Proof.
intros * Hdom Hcod t t₀ u u₀ rt ru ?? Heq; cbn in *.
destruct rt as [[p] pr ? rpfst rpsnd]; cbn in *.
destruct ru as [[q] qr ? rqfst rqsnd]; cbn in *.
assert [|- Γ] by gtyping.
assert (isNf p t₀) by now eapply isNf_TermRedWf_red.
assert (isNf q u₀) by now eapply isNf_TermRedWf_red.
assert (∑ p1₀, isNf (tFst p) p1₀) as [p1₀].
{ replace p with p⟨@wk_id Γ⟩ by now bsimpl.
  now unshelve eapply hasNf_red, rpfst. }
assert (∑ q1₀, isNf (tFst q) q1₀) as [q1₀].
{ replace q with q⟨@wk_id Γ⟩ by now bsimpl.
  now unshelve eapply hasNf_red, rqfst. }
assert (∑ p2₀, isNf (tSnd p) p2₀) as [p2₀].
{ replace p with p⟨@wk_id Γ⟩ by now bsimpl.
  now unshelve eapply hasNf_red, rpsnd. }
assert (∑ q2₀, isNf (tSnd q) q2₀) as [q2₀].
{ replace q with q⟨@wk_id Γ⟩ by now bsimpl.
  now unshelve eapply hasNf_red, rqsnd. }
unshelve econstructor.
+ now exists p.
+ now exists q.
+ intros; cbn in *.
  eapply Hdom.
  - eapply lrefl, rpfst.
  - eapply lrefl, rqfst.
  - now eapply (isNf_wk (tFst p)).
  - now eapply (isNf_wk (tFst q)).
  - eapply eqnf_ren; [eapply wk_inj|].
    admit.
+ cbn in *.
  admit.
+ cbn in *.
  admit.
Admitted.

Lemma eqnf_complete_Id : forall Γ l A A',
  forall IA : [Γ ||-Id< l > A ≅ A'],
  eqnf_complete (IdRedTy.tyRed IA) -> eqnf_complete (LRId' IA).
Proof.
intros * HA t t₀ u u₀ rt ru ?? Heq; cbn in *.
destruct rt as [nft nft' ??? Hrt], ru as [nfu nfu' ??? Hru]; cbn in *.
assert (isNf nft t₀) by eauto using isNf_TermRedWf_red.
assert (isNf nfu u₀) by eauto using isNf_TermRedWf_red.
assert (whnf nft) by eauto using IdPropEq_whnf.
assert (whnf nfu) by eauto using IdPropEq_whnf.
assert (without_eta nft) by now eapply IdPropEq_without_eta.
assert (without_eta nfu) by now eapply IdPropEq_without_eta.
assert (Hh : same_head nft nfu) by now eapply isNf_eqnf_same_head.
assert [Γ |- nft ≅ nfu : tId (IdRedTy.tyL IA) (IdRedTy.lhsL IA) (IdRedTy.rhsL IA)].
{ now eapply sncmp_convtm. }
exists nft nfu; tea; cbn in *.
induction Hrt as [A_ ? t_ ?|ne]; cbn in *.
+ assert (Hinv : ∑ B_, ∑ u_, nfu = tRefl B_ u_).
  { inversion Hh; subst; [|match goal with [ H : whne _ |- _ ] => now inversion H end].
    do 2 eexists; reflexivity. }
  destruct Hinv as (B_&u_&?); subst.
  inversion Hru; subst.
  * constructor; tea.
  * assert (Hne : whne (tRefl B_ u_)) by eauto using NeNf_whne.
    inversion Hne.
+ assert (whne ne) by now eapply NeNf_whne.
  assert (Hne : whne nfu) by now eapply whne_same_head_whne.
  assert [Γ ||-NeNf nfu ≅ nfu' : IdRedTyPack.outTy (IdRedTy.toPack IA)].
  { inversion Hru; subst; [inversion Hne|tea]. }
  do 2 constructor; cbn in *.
  - eauto using NeNf.tyL.
  - eauto using NeNf.tyL.
  - eapply sncmp_convneu; eauto using NeNf.conv.
Qed.

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
+ intros; apply eqnf_complete_Id; auto.
Qed.

Lemma redTy_param_eqn_complete : forall T, ((T = tProd) + (T = tSig)) ->
  forall Γ A A' (l := zero) (PA : ParamRedTy T Γ l A A'),
  (forall (Δ : context) (ρ : Δ ≤ Γ),
   [ |- Δ] ->
   forall A₀ B B₀ : term,
   [Δ ||-< l > B] ->
   isNf (ParamRedTy.domL PA)⟨ρ⟩ A₀ -> isNf B B₀ -> eqnf A₀ B₀ -> [Δ ||-< l > (ParamRedTy.domL PA)⟨ρ⟩ ≅ B]) ->
  (forall (Δ : context) (a b : term) (ρ : Δ ≤ Γ) (h : [ |- Δ]),
   [PolyRed.shpRed PA ρ h | Δ ||- a ≅ b : (ParamRedTy.domL PA)⟨ρ⟩ ≅ (ParamRedTy.domR PA)⟨ρ⟩] ->
   forall A₀ B B₀ : term,
   [Δ ||-< l > B] ->
   isNf (ParamRedTy.codL PA)[a .: ρ >> tRel] A₀ ->
   isNf B B₀ -> eqnf A₀ B₀ -> [Δ ||-< l > (ParamRedTy.codL PA)[a .: ρ >> tRel] ≅ B]) ->
  forall A₀ B B₀ : term,
  [Γ ||-< l > B] -> isNf A A₀ -> isNf B B₀ -> eqnf A₀ B₀ -> [Γ ||-< l > A ≅ B].
Proof.
intros T HT Γ A A' l ΠA Hdom Hcod A₀ B B₀ rB ?? Heq.
destruct ΠA as [domL domR codL codR]; cbn in *.
assert [Γ |- A :⤳*: T domL codL] by now destruct redL.
eapply redwfSubst; [|tea].
destruct (redFwd' rB) as [rB' _]; symmetry in rB'.
etransitivity; [|eapply rB'].
destruct (whredtyL rB) as [B' HB]; cbn [tyred_whnf] in *.
assert [|- Γ] by gtyping.
assert (isNf (T domL codL) A₀) by eauto using isNf_TypeRedWf_red.
assert (isNf B' B₀) by eauto using isNf_TypeRedWf_red.
assert (whnf B') by now apply isType_whnf.
assert (without_eta B') by now apply isType_without_eta.
assert (Hh : same_head (T domL codL) B').
{ eapply isNf_eqnf_same_head; destruct HT; subst; eauto using whnf; constructor. }
assert (Hinv : ∑ domB, ∑ codB, B' = T domB codB); [|clear Hh].
{ destruct HT; subst; (inversion Hh; subst; [|match goal with [ H : whne _ |- _ ] => now inversion H end]).
  all: do 2 eexists; reflexivity. }
destruct Hinv as (domB&codB&?); subst B'.
assert (rT : ParamRedTy T Γ l (T domB codB) B).
{ destruct HT; subst.
  + apply invLRΠ in rB'; apply rB'.
  + apply invLRΣ in rB'; apply rB'. }
enough (HP : PolyRed Γ l domL domB codL codB).
{ destruct HT; subst.
  + now apply Pi.LRPiPoly.
  + apply LRSig', Poly.mkParamRedTy; tea.
    - intros; gtyping.
    - intros; gtyping. }
clear rB rB'; destruct rT as [dom' ? cod' ? [] ??? rPi]; cbn in *.
assert (He : T domB codB = T dom' cod').
{ eapply redtywf_whnf; eauto using whnf. }
assert (domB = dom' × codB = cod') as [].
{ destruct HT; subst; now injection He. }
subst cod' dom'; clear He.
assert (whnf (T domL codL)).
{ destruct HT; subst; eauto using whnf. }
assert (Hnf : ∑ domL₀, ∑ codL₀, A₀ = T domL₀ codL₀).
{ assert (Hh : same_head (T domL codL) A₀) by eauto using isNf_whnf_same_head, whnf.
  destruct HT; subst; (inversion Hh; subst; [|match goal with [ H : whne _ |- _ ] => now inversion H end]).
  all: do 2 eexists; reflexivity. }
destruct Hnf as (domL₀&?codL₀&?); subst.
assert (Hnf : ∑ domB₀, ∑ codB₀, B₀ = T domB₀ codB₀).
{ assert (Hh : same_head (T domB codB) B₀) by eauto using isNf_whnf_same_head, whnf.
  destruct HT; subst; (inversion Hh; subst; [|match goal with [ H : whne _ |- _ ] => now inversion H end]).
  all: do 2 eexists; reflexivity. }
destruct Hnf as (domB₀&?codB₀&?); subst.
assert (isNf domL domL₀ × isNf codL codL₀) as [].
{ destruct HT; subst.
  + now apply isNf_tProd_inv.
  + now apply isNf_tSig_inv. }
assert (isNf domB domB₀ × isNf codB codB₀) as [].
{ destruct HT; subst.
  + now apply isNf_tProd_inv.
  + now apply isNf_tSig_inv. }
assert (rdom : forall (Δ : context) (ρ : Δ ≤ Γ), [ |-[ ta ] Δ] -> [Δ ||-< l > domL⟨ρ⟩ ≅ domB⟨ρ⟩]).
{ intros; eapply Hdom; trivial.
  - now eapply lrefl, rPi.
  - now apply isNf_wk.
  - now apply isNf_wk.
  - apply eqnf_ren; [apply wk0_inj|].
    unfold eqnf in Heq; simpl in Heq; destruct HT; subst; now injection Heq. }
unshelve econstructor.
+ exact rdom.
+ intros ? a b ?? rab.
  destruct rPi as [rdomB rcodB].
  assert (rba : [rdom _ _ _ | Δ ||- b ≅ a : (domL)⟨ρ⟩ ≅ (domB)⟨ρ⟩]) by now symmetry.
  assert (rB : [Δ ||-< l > codB[b .: ρ >> tRel]]).
  { eapply symLR in rab.
    unshelve eapply lrefl, rcodB, irrLREq, rab; trivial. }
  assert (∑ v₀, isNf codL[a .: ρ >> tRel] v₀) as [v₀ Hnfv].
  { destruct polyRed as [rdomL rcodL].
    unshelve eapply hasNf_redty, rcodL, irrLREq, rab; trivial. }

  assert (∑ w₀, isNf codB[b .: ρ >> tRel] w₀) as [w₀ Hnfw].
  { eapply hasNf_redty, rB. }

  assert (∑ a₀, isNf a a₀) as [a₀ Ha] by now eapply hasNf_red.
  assert (∑ b₀, isNf b b₀) as [b₀ Hb] by now eapply hasNf_red.
  assert (Heqcod : eqnf codL₀ codB₀).
  { unfold eqnf in Heq; cbn in Heq; destruct HT; subst; now injection Heq. }

  assert (Heqarg : eqnf a₀ b₀).
  { assert (Htab : [Δ |- a ≅ b : domL⟨ρ⟩]) by now escape.
    apply snty_nf in Htab as (r₀&s₀&?&?&?&?&?).
    replace a₀ with r₀ by now eapply isNf_irr.
    replace b₀ with s₀ by now eapply isNf_irr.
    tea. }
  eapply Hcod.
  - eapply irrLREq; [|tea]; reflexivity.
  - eapply rB.
  - tea.
  - tea.
  - pose (ρ' := wk_up domL ρ).
    eapply (eqnf_nfeval_subst_compat codL⟨ρ'⟩ codL₀⟨ρ'⟩ codB⟨ρ'⟩ codB₀⟨ρ'⟩ a a₀ b b₀); eauto using isNf_wk, eqnf_ren, wk0_inj.
    * unfold ρ'; rewrite <- (subst1_ren_wk_up (A := domL)) with ρ; tea.
    * unfold ρ'; rewrite <- (subst1_ren_wk_up (A := domL)) with ρ; tea.
Unshelve.
all: tea.
Qed.

Lemma redTy_prod_eqn_complete : forall Γ A A' (l := zero) (ΠA : [Γ ||-Π< l > A ≅ A']),
  (forall (Δ : context) (ρ : Δ ≤ Γ),
   [ |- Δ] ->
   forall A₀ B B₀ : term,
   [Δ ||-< l > B] ->
   isNf (ParamRedTy.domL ΠA)⟨ρ⟩ A₀ -> isNf B B₀ -> eqnf A₀ B₀ -> [Δ ||-< l > (ParamRedTy.domL ΠA)⟨ρ⟩ ≅ B]) ->
  (forall (Δ : context) (a b : term) (ρ : Δ ≤ Γ) (h : [ |- Δ]),
   [PolyRed.shpRed ΠA ρ h | Δ ||- a ≅ b : (ParamRedTy.domL ΠA)⟨ρ⟩ ≅ (ParamRedTy.domR ΠA)⟨ρ⟩] ->
   forall A₀ B B₀ : term,
   [Δ ||-< l > B] ->
   isNf (ParamRedTy.codL ΠA)[a .: ρ >> tRel] A₀ ->
   isNf B B₀ -> eqnf A₀ B₀ -> [Δ ||-< l > (ParamRedTy.codL ΠA)[a .: ρ >> tRel] ≅ B]) ->
  forall A₀ B B₀ : term,
  [Γ ||-< l > B] -> isNf A A₀ -> isNf B B₀ -> eqnf A₀ B₀ -> [Γ ||-< l > A ≅ B].
Proof.
apply redTy_param_eqn_complete; eauto.
Qed.

Lemma redTy_sig_eqn_complete : forall Γ A A' (l := zero) (ΠA : [Γ ||-Σ< l > A ≅ A']),
  (forall (Δ : context) (ρ : Δ ≤ Γ),
   [ |- Δ] ->
   forall A₀ B B₀ : term,
   [Δ ||-< l > B] ->
   isNf (ParamRedTy.domL ΠA)⟨ρ⟩ A₀ -> isNf B B₀ -> eqnf A₀ B₀ -> [Δ ||-< l > (ParamRedTy.domL ΠA)⟨ρ⟩ ≅ B]) ->
  (forall (Δ : context) (a b : term) (ρ : Δ ≤ Γ) (h : [ |- Δ]),
   [PolyRed.shpRed ΠA ρ h | Δ ||- a ≅ b : (ParamRedTy.domL ΠA)⟨ρ⟩ ≅ (ParamRedTy.domR ΠA)⟨ρ⟩] ->
   forall A₀ B B₀ : term,
   [Δ ||-< l > B] ->
   isNf (ParamRedTy.codL ΠA)[a .: ρ >> tRel] A₀ ->
   isNf B B₀ -> eqnf A₀ B₀ -> [Δ ||-< l > (ParamRedTy.codL ΠA)[a .: ρ >> tRel] ≅ B]) ->
  forall A₀ B B₀ : term,
  [Γ ||-< l > B] -> isNf A A₀ -> isNf B B₀ -> eqnf A₀ B₀ -> [Γ ||-< l > A ≅ B].
Proof.
apply redTy_param_eqn_complete; eauto.
Qed.

Lemma redTy_eqn_complete_zero : forall Γ A A' A₀ B B₀
  (rA : [Γ ||-<zero> A ≅ A']) (rB : [Γ ||-<zero> B ≅ B]),
  isNf A A₀ -> isNf B B₀ ->
  eqnf A₀ B₀ -> [Γ ||-<zero> A ≅ B].
Proof.
intros Γ A A' A₀ B B₀ rA.
remember zero as l eqn:Hl; revert A₀ B B₀ Hl.
indLR rA; cbn in *.
+ intros [? Hlt] A₀ B B₀ Hl; subst l.
  inversion Hlt.
+ intros rA A₀ B B₀ Hl rB ?? Heq; destruct rA as [whA].
  apply LRne_.
  assert (Hr := whredty_conv rB).
  destruct (whredtyL rB) as [B' HB Hty]; cbn [tyred_whnf] in *.
  exists whA B'; tea.
  assert (isNf whA A₀) by eauto using isNf_TypeRedWf_red.
  assert (isNf B' B₀) by eauto using isNf_TypeRedWf_red.
  assert (whne whA) by now eapply convneu_whne.
  assert (whnf B') by now apply isType_whnf.
  assert (without_eta B') by now apply isType_without_eta.
  assert (same_head whA B').
  { eapply isNf_eqnf_same_head; eauto using whnf, whne_without_eta. }
  assert (Hne : whne B') by now eapply whne_same_head_whne.
  assert (Hinv : invLRTyEqL rB (@NeType _ Hne)) by now eapply invLREqL, redtywf_red.
  cbn in Hinv; destruct Hinv as (rne&?&?); subst.
  eapply sncmp_convneu; try now eapply tyr_wf_r.
  - eassumption.
  - apply neRedTy.eq.
  - tea.
  - tea.
  - exact Heq.
+ intros ΠA Hdom Hcod A₀ B B₀ Hl rB ?? Heq; subst l.
  eapply redTy_prod_eqn_complete; tea.
  - intros; eapply Hdom; tea; reflexivity.
  - intros; eapply Hcod; tea; reflexivity.
+ intros [] **.
  destruct (redFwd' rB) as [rB' _]; symmetry in rB'.
  destruct (whredtyL rB) as [B' HB]; cbn [tyred_whnf] in *.
  symmetry; eapply redwfSubst; [|tea].
  apply LRNat_; constructor; tea.
  assert (isNf tNat A₀) by eauto using isNf_TypeRedWf_red.
  assert (isNf B' B₀) by eauto using isNf_TypeRedWf_red.
  assert (whnf B') by now apply isType_whnf.
  assert (without_eta B') by now apply isType_without_eta.
  assert (Hh : same_head tNat B').
  { eapply isNf_eqnf_same_head; eauto using whnf; constructor. }
  assert (B' = tNat); [|subst].
  { inversion Hh; subst; [|match goal with [ H : whne _ |- _ ] => now inversion H end]; reflexivity. }
  apply redtywf_refl; gtyping.
+ intros [] **.
  destruct (redFwd' rB) as [rB' _]; symmetry in rB'.
  destruct (whredtyL rB) as [B' HB]; cbn [tyred_whnf] in *.
  symmetry; eapply redwfSubst; [|tea].
  apply LREmpty_; constructor; tea.
  assert (isNf tEmpty A₀) by eauto using isNf_TypeRedWf_red.
  assert (isNf B' B₀) by eauto using isNf_TypeRedWf_red.
  assert (whnf B') by now apply isType_whnf.
  assert (without_eta B') by now apply isType_without_eta.
  assert (Hh : same_head tEmpty B').
  { eapply isNf_eqnf_same_head; eauto using whnf; constructor. }
  assert (B' = tEmpty); [|subst].
  { inversion Hh; subst; [|match goal with [ H : whne _ |- _ ] => now inversion H end]; reflexivity. }
  apply redtywf_refl; gtyping.
+ intros ΣA Hdom Hcod A₀ B B₀ Hl rB ?? Heq; subst l.
  eapply redTy_sig_eqn_complete; tea.
  - intros; eapply Hdom; tea; reflexivity.
  - intros; eapply Hcod; tea; reflexivity.
+ intros [tyL ? lhsL ? rhsL ?]; cbn; intros IHA ???? rB ?? Heq; subst l.
  destruct (redFwd' rB) as [rB' _]; symmetry in rB'.
  destruct (whredtyL rB) as [B' HB]; cbn [tyred_whnf] in *.
  assert (isNf (tId tyL lhsL rhsL) A₀) by eauto using isNf_TypeRedWf_red.
  assert (isNf B' B₀) by eauto using isNf_TypeRedWf_red.
  assert (whnf B') by now apply isType_whnf.
  assert (without_eta B') by now apply isType_without_eta.
  assert (Hh : same_head (tId tyL lhsL rhsL) B').
  { eapply isNf_eqnf_same_head; eauto using whnf, whne_without_eta; constructor. }
  assert (∑ tyB, ∑ lhsB, ∑ rhsB, B' = tId tyB lhsB rhsB) as (tyB&lhsB&rhsB&?); [|subst].
  { inversion Hh; subst; [|match goal with [ H : whne _ |- _ ] => now inversion H end].
    do 3 eexists; reflexivity. }
  eapply redSubst, tyr_wf_red; [|tea].
  symmetry; eapply redSubst, tyr_wf_red; [|tea]; symmetry.
  apply invLRId in rB'; destruct rB' as [tyB' ? lhsB' ? rhsB' ?].
  assert (Hinv : tId tyB lhsB rhsB = tId tyB' lhsB' rhsB').
  { eapply redtywf_whnf; eauto using whnf. }
  injection Hinv; intros; subst tyB' lhsB' rhsB'; clear Hinv.

  assert (Hnf : ∑ tyL₀, ∑ lhsL₀, ∑ rhsL₀, A₀ = tId tyL₀ lhsL₀ rhsL₀).
  { assert (Hh' : same_head (tId tyL lhsL rhsL) A₀) by eauto using isNf_whnf_same_head, whnf.
    inversion Hh'; subst; [|match goal with [ H : whne _ |- _ ] => now inversion H end].
    all: do 3 eexists; reflexivity. }
  destruct Hnf as (tyL₀&lhsL₀&rhsL₀&?); subst.

  assert (Hnf : ∑ tyB₀, ∑ lhsB₀, ∑ rhsB₀, B₀ = tId tyB₀ lhsB₀ rhsB₀).
  { assert (Hh' : same_head (tId tyB lhsB rhsB) B₀) by eauto using isNf_whnf_same_head, whnf.
    inversion Hh'; subst; [|match goal with [ H : whne _ |- _ ] => now inversion H end].
    all: do 3 eexists; reflexivity. }
  destruct Hnf as (tyB₀&lhsB₀&rhsB₀&?); subst.

  repeat match goal with [ H : isNf _ _ |- _ ] => apply isNf_tId_inv in H; destruct H as (?&?&?) end.

  assert (rtyB : [Γ ||-<zero> tyL ≅ tyB]).
  { eapply IHA; tea; try reflexivity.
    - now eapply lrefl.
    - unfold eqnf in Heq; cbn in Heq; now injection Heq. }
  unshelve eapply IdRed.
  - exact rtyB.
  - eapply red_eqnf_complete_zero; tea.
    * eapply lrefl, irrLREq; [|tea]; reflexivity.
    * eapply symLR, lrefl, irrLREq; [|tea]; reflexivity.
    * unfold eqnf in Heq; cbn in Heq; now injection Heq.
  - eapply red_eqnf_complete_zero; tea.
    * eapply lrefl, irrLREq; [|tea]; reflexivity.
    * eapply symLR, lrefl, irrLREq; [|tea]; reflexivity.
    * unfold eqnf in Heq; cbn in Heq; now injection Heq.
Qed.

Lemma red_eqnf_complete_one : forall Γ A A' (rA : [Γ ||-<one> A ≅ A']), eqnf_complete rA.
Proof.
intros *.
remember one as l eqn:Hl; revert Hl.
indLR rA; cbn.
+ intros * ? X X₀ Y Y₀ HX HY ?? Heq; subst l.
  destruct HX as [HX], HY as [HY]; cbn in *.
  exists HX HY.
  - destruct HX as [], HY as []; cbn in *.
    eapply sncmp_convtm; eauto using isNf_TermRedWf_red, tmr_wf_r.
  - destruct h as [l Hlt]; cbn in *; inversion Hlt; subst.
    eapply redTy_eqn_complete_zero; tea.
+ intros; apply eqnf_complete_Ne.
+ intros; apply eqnf_complete_Π; eauto.
+ intros; apply eqnf_complete_Nat.
+ intros; apply eqnf_complete_Empty.
+ intros; apply eqnf_complete_Σ; auto.
+ intros; apply eqnf_complete_Id; auto.
Qed.

Lemma red_eqnf_complete : forall Γ l A A' (rA : [Γ ||-<l> A ≅ A']), eqnf_complete rA.
Proof.
intros; destruct l.
+ apply red_eqnf_complete_zero.
+ apply red_eqnf_complete_one.
Qed.

End EquationalCompleteness.
