(** * LogRel.DeclarativeInstance: proof that declarative typing is an instance of generic typing. *)
From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Computation Notations Context Closed NormalForms UntypedReduction Weakening NormalEq GenericTyping DeclarativeTyping DeclarativeInstance.

Import DeclarativeTypingData.

Record NfTypeDecl Γ (A A₀ : term) := {
  nftydecl_red : [A ⇶* A₀];
  nftydecl_nf : dnf A₀;
  nftydecl_conv : [Γ |- A ≅ A₀];
}.

Record NfTermDecl Γ (A t t₀ : term) := {
  nftmdecl_red : [t ⇶* t₀];
  nftmdecl_nf : dnf t₀;
  nftmdecl_conv : [Γ |- t ≅ t₀ : A];
}.

Record NeTermDecl Γ (A t t₀ : term) := {
  netmdecl_whne : whne t;
  netmdecl_nf : NfTermDecl Γ A t t₀;
}.

Record ConvTypeNfDecl Γ A B := {
  nfconvty_lhs : term;
  nfconvty_rhs : term;
  nfconvty_conv : [Γ |- A ≅ B];
  nfconvty_nfl : NfTypeDecl Γ A nfconvty_lhs;
  nfconvty_nfr : NfTypeDecl Γ B nfconvty_rhs;
  nfconvty_eqv : eqnf nfconvty_lhs nfconvty_rhs;
}.

Record ConvTermNfDecl Γ A t u := {
  nfconvtm_lhs : term;
  nfconvtm_rhs : term;
  nfconvtm_conv : [Γ |- t ≅ u : A];
  nfconvtm_nfl : NfTermDecl Γ A t nfconvtm_lhs;
  nfconvtm_nfr : NfTermDecl Γ A u nfconvtm_rhs;
  nfconvtm_eqv : eqnf nfconvtm_lhs nfconvtm_rhs;
}.

Record ConvTermNeDecl Γ A t u := {
  neconvtm_lhs : term;
  neconvtm_rhs : term;
  neconvtm_conv : [Γ |- t ~ u : A];
  neconvtm_nfl : NeTermDecl Γ A t neconvtm_lhs;
  neconvtm_nfr : NeTermDecl Γ A u neconvtm_rhs;
  neconvtm_eqv : eqnf neconvtm_lhs neconvtm_rhs;
}.

Section Nf.

Import DeclarativeTypingProperties.

Lemma NfTypeDecl_unique : forall Γ Γ' A A₀ A₀',
  NfTypeDecl Γ A A₀ -> NfTypeDecl Γ' A A₀' -> A₀ = A₀'.
Proof.
intros * [] []; apply dred_dnf; tea.
now eapply dred_red_det.
Qed.

Lemma NfTermDecl_unique : forall Γ Γ' A A' t t₀ t₀',
  NfTermDecl Γ A t t₀ -> NfTermDecl Γ' A' t t₀' -> t₀ = t₀'.
Proof.
intros * [] []; apply dred_dnf; tea.
now eapply dred_red_det.
Qed.

Lemma NeTermDecl_unique : forall Γ Γ' A A' t t₀ t₀',
  NeTermDecl Γ A t t₀ -> NeTermDecl Γ' A' t t₀' -> t₀ = t₀'.
Proof.
intros * [? []] [? []]; apply dred_dnf; tea.
now eapply dred_red_det.
Qed.

#[local]
Lemma ConvTypeNf_PER : forall Γ, PER (ConvTypeNfDecl Γ).
Proof.
intros Γ; split.
- intros t u []; esplit; tea.
  + now apply TypeSym.
  + now apply Symmetric_eqnf.
- intros t u r [t₀ u₀] [u₀' r₀]; esplit; tea.
  + now eapply TypeTrans.
  + replace u₀' with u₀ in * by now eapply NfTypeDecl_unique.
    now eapply Transitive_eqnf.
Qed.

#[local]
Lemma ConvTermNf_PER : forall Γ A, PER (ConvTermNfDecl Γ A).
Proof.
intros Γ A; split.
- intros t u []; esplit; tea.
  + now apply TermSym.
  + now apply Symmetric_eqnf.
- intros t u r [t₀ u₀] [u₀' r₀]; esplit; tea.
  + now eapply TermTrans.
  + replace u₀' with u₀ in * by now eapply NfTermDecl_unique.
    now eapply Transitive_eqnf.
Qed.

#[local]
Lemma ConvTermNe_PER : forall Γ A, PER (ConvTermNeDecl Γ A).
Proof.
intros Γ A; split.
- intros t u []; esplit; tea.
  + now symmetry.
  + now apply Symmetric_eqnf.
- intros t u r [t₀ u₀] [u₀' r₀]; esplit; tea.
  + now etransitivity.
  + replace u₀' with u₀ in * by now eapply NeTermDecl_unique.
    now eapply Transitive_eqnf.
Qed.

Lemma NfTermConv : forall Γ A B t t₀, [Γ |-[de] A ≅ B] -> NfTermDecl Γ A t t₀ -> NfTermDecl Γ B t t₀.
Proof.
intros * H []; split; tea.
now eapply TermConv.
Qed.

Lemma NeTermConv : forall Γ A B t t₀, [Γ |-[de] A ≅ B] -> NeTermDecl Γ A t t₀ -> NeTermDecl Γ B t t₀.
Proof.
intros * ? [Hne Hnf]; split; [tea|].
now eapply NfTermConv.
Qed.

Lemma NeTerm_whne : forall Γ A t t₀, NeTermDecl Γ A t t₀ -> whne t₀.
Proof.
eauto using dredalg_whne, netmdecl_whne, netmdecl_nf, nftmdecl_red.
Qed.

Lemma NeTerm_dne : forall Γ A t t₀, NeTermDecl Γ A t t₀ -> dne t₀.
Proof.
intros; apply dne_dnf_whne.
+ now eapply netmdecl_nf.
+ now eapply NeTerm_whne.
Qed.

Lemma NfTypeDecl_tSort : forall Γ, [|-[de] Γ] -> NfTypeDecl Γ U U.
Proof.
intros; split.
+ reflexivity.
+ constructor.
+ now do 2 constructor.
Qed.

Lemma NfTypeDecl_tProd : forall Γ A A' A₀ B B₀,
  [Γ |-[de] A] ->
  [Γ |-[de] A ≅ A'] ->
  [Γ,, A |-[de] B ≅ B] ->
  NfTypeDecl Γ A' A₀ -> NfTypeDecl (Γ,, A) B B₀ -> NfTypeDecl Γ (tProd A' B) (tProd A₀ B₀).
Proof.
intros Γ A A' A₀ B B₀ HA HAA' HBB [HRA HAnf] [HRB HBnf].
split.
+ now apply dredalg_prod.
+ now constructor.
+ assert [ Γ |-[de] tProd A B ≅ tProd A' B ].
  { constructor; tea. }
  eapply TypeTrans; [now eapply TypeSym|].
  constructor; [tea|now eapply TypeTrans|tea].
Qed.

Lemma NfTermDecl_tProd : forall Γ A A' A₀ B B₀,
  [Γ |-[de] A : U] ->
  [Γ |-[de] A ≅ A' : U] ->
  [Γ,, A |-[de] B ≅ B : U] ->
  NfTermDecl Γ U A' A₀ -> NfTermDecl (Γ,, A) U B B₀ -> NfTermDecl Γ U (tProd A' B) (tProd A₀ B₀).
Proof.
intros Γ A A' A₀ B B₀ HA HAA' HBB [HRA HAnf] [HRB HBnf].
split.
+ now apply dredalg_prod.
+ now constructor.
+ assert [ Γ |-[de] tProd A B ≅ tProd A' B : U ].
  { constructor; tea. }
  eapply TermTrans; [now eapply TermSym|].
  constructor; [tea|now eapply TermTrans|tea].
Qed.

Lemma NfTermDecl_tLambda : forall Γ A A' A₀ B t t₀,
  [Γ |-[ de ] A] ->
  [Γ |-[ de ] A'] ->
  [Γ,, A |-[ de ] B] ->
  [Γ |-[ de ] A ≅ A'] ->
  [Γ |-[ de ] tLambda A' t : tProd A B] ->
  [Γ,, A |-[ de ] t : B] ->
  [Γ,, A' |-[ de ] t : B] ->
  NfTypeDecl Γ A' A₀ ->
  NfTermDecl (Γ,, A) B (tApp (tLambda A' t)⟨↑⟩ (tRel 0)) t₀ ->
  NfTermDecl Γ (tProd A B) (tLambda A' t) (tLambda A₀ t₀).
Proof.
intros * ? ? ? ? ? ? Ht [] [].
assert (eq0 : forall t, t⟨upRen_term_term ↑⟩[(tRel 0)..] = t).
{ bsimpl; apply idSubst_term; intros [|]; reflexivity. }
split.
+ apply dredalg_lambda; tea.
  assert (Hr : [tApp (tLambda A' t)⟨↑⟩ (tRel 0) ⇶ t]).
  { cbn. set (t' := t) at 2; rewrite <- (eq0 t'); constructor. }
  eapply dred_red_det; tea.
  econstructor; [tea|reflexivity].
+ now constructor.
+ assert [|- Γ] by boundary.
  assert [|- Γ,, A] by now constructor.
  apply TermLambdaCong; tea.
  - eapply TypeTrans; tea.
  - eapply TermTrans; [|tea].
    rewrite <- (eq0 B).
    eapply TermSym; cbn; eapply TermTrans; [eapply TermBRed|].
    * rewrite <- (wk1_ren_on Γ A); eapply typing_wk; tea.
    * repeat rewrite <- (wk1_ren_on Γ A).
      do 2 rewrite <- (wk_up_wk1_ren_on Γ A' A).
      eapply typing_wk; tea.
      constructor; tea.
      now eapply typing_wk.
    * eapply wfTermConv; [now apply ty_var0|].
      repeat rewrite <- (wk1_ren_on Γ A).
      eapply typing_wk; tea.
    * do 2 rewrite eq0; apply TermRefl; tea.
Qed.

Lemma NfTermDecl_tLambda0 : forall Γ A A₀ B t t₀,
  [Γ |-[ de ] A] ->
  NfTypeDecl Γ A A₀ ->
  NfTermDecl (Γ,, A) B t t₀ ->
  NfTermDecl Γ (tProd A B) (tLambda A t) (tLambda A₀ t₀).
Proof.
intros * ? [] [].
split.
+ apply dredalg_lambda; tea.
+ now constructor.
+ constructor; tea.
  now apply TypeRefl.
Qed.

Lemma NfTypeDecl_tSig : forall Γ A A' A₀ B B₀,
  [Γ |-[de] A] ->
  [Γ |-[de] A ≅ A'] ->
  [Γ,, A |-[de] B ≅ B] ->
  NfTypeDecl Γ A' A₀ -> NfTypeDecl (Γ,, A) B B₀ -> NfTypeDecl Γ (tSig A' B) (tSig A₀ B₀).
Proof.
intros Γ A A' A₀ B B₀ HA HAA' HBB [HRA HAnf] [HRB HBnf].
split.
+ now apply dredalg_sig.
+ now constructor.
+ assert [ Γ |-[de] tSig A B ≅ tSig A' B ].
  { constructor; tea. }
  eapply TypeTrans; [now eapply TypeSym|].
  constructor; [tea|now eapply TypeTrans|tea].
Qed.

Lemma NfTermDecl_tSig : forall Γ A A' A₀ B B₀,
  [Γ |-[de] A : U] ->
  [Γ |-[de] A ≅ A' : U] ->
  [Γ,, A |-[de] B ≅ B : U] ->
  NfTermDecl Γ U A' A₀ -> NfTermDecl (Γ,, A) U B B₀ -> NfTermDecl Γ U (tSig A' B) (tSig A₀ B₀).
Proof.
intros Γ A A' A₀ B B₀ HA HAA' HBB [HRA HAnf] [HRB HBnf].
split.
+ now apply dredalg_sig.
+ now constructor.
+ assert [ Γ |-[de] tSig A B ≅ tSig A' B : U ].
  { constructor; tea. }
  eapply TermTrans; [now eapply TermSym|].
  constructor; [tea|now eapply TermTrans|tea].
Qed.

Lemma NfTypeDecl_tId : forall Γ A A₀ t t₀ u u₀,
  NfTypeDecl Γ A A₀ -> NfTermDecl Γ A t t₀ -> NfTermDecl Γ A u u₀ -> NfTypeDecl Γ (tId A t u) (tId A₀ t₀ u₀).
Proof.
intros Γ A A₀ t t₀ u u₀ [HRA HAnf] [] [].
split.
+ now apply dredalg_id.
+ now constructor.
+ constructor; tea.
Qed.

Lemma NfTermDecl_tId : forall Γ A A₀ t t₀ u u₀,
  NfTermDecl Γ U A A₀ -> NfTermDecl Γ A t t₀ -> NfTermDecl Γ A u u₀ -> NfTermDecl Γ U (tId A t u) (tId A₀ t₀ u₀).
Proof.
intros Γ A A₀ t t₀ u u₀ [HRA HAnf] [] [].
split.
+ now apply dredalg_id.
+ now constructor.
+ constructor; tea.
Qed.

Lemma NfTermDecl_Refl : forall Γ A A₀ x x₀,
  NfTypeDecl Γ A A₀ -> NfTermDecl Γ A x x₀ -> NfTermDecl Γ (tId A x x) (tRefl A x) (tRefl A₀ x₀).
Proof.
intros * [] [].
split.
+ now apply dredalg_refl.
+ now constructor.
+ constructor; tea.
Qed.

Lemma NfTypeDecl_wk : forall Γ Δ A A₀ (ρ : Δ ≤ Γ), [|- Δ] -> NfTypeDecl Γ A A₀ -> NfTypeDecl Δ A⟨ρ⟩ A₀⟨ρ⟩.
Proof.
intros * tΔ []; split.
+ apply gcredalg_wk; now eauto using wk_inj.
+ now apply dnf_ren.
+ now apply typing_wk.
Qed.

Lemma NfTermDecl_wk : forall Γ Δ A t t₀ (ρ : Δ ≤ Γ), [|- Δ] -> NfTermDecl Γ A t t₀ -> NfTermDecl Δ A⟨ρ⟩ t⟨ρ⟩ t₀⟨ρ⟩.
Proof.
intros * tΔ []; split.
+ apply gcredalg_wk; now eauto using wk_inj.
+ now apply dnf_ren.
+ now apply typing_wk.
Qed.

Lemma NeTermDecl_wk : forall Γ Δ A t t₀ (ρ : Δ ≤ Γ), [|- Δ] -> NeTermDecl Γ A t t₀ -> NeTermDecl Δ A⟨ρ⟩ t⟨ρ⟩ t₀⟨ρ⟩.
Proof.
intros * tΔ [Hne Hnf]; split.
+ now eapply whne_ren.
+ now eapply NfTermDecl_wk.
Qed.

Lemma NfTypeDecl_tNat : forall Γ, [|-[de] Γ] -> NfTypeDecl Γ tNat tNat.
Proof.
intros; split.
+ reflexivity.
+ constructor.
+ now repeat econstructor.
Qed.

Lemma NfTermDecl_tNat : forall Γ, [|-[de] Γ] -> NfTermDecl Γ U tNat tNat.
Proof.
intros; split.
+ reflexivity.
+ constructor.
+ now repeat econstructor.
Qed.

Lemma NfTermDecl_tZero : forall Γ, [|-[de] Γ] -> NfTermDecl Γ tNat tZero tZero.
Proof.
intros; split.
+ reflexivity.
+ constructor.
+ now do 2 constructor.
Qed.

Lemma NfTermDecl_tSucc : forall Γ n n₀, NfTermDecl Γ tNat n n₀ -> NfTermDecl Γ tNat (tSucc n) (tSucc n₀).
Proof.
intros * []; split.
+ now apply dredalg_succ.
+ now constructor.
+ now do 2 constructor.
Qed.

Lemma NfTypeDecl_tEmpty : forall Γ, [|-[de] Γ] -> NfTypeDecl Γ tEmpty tEmpty.
Proof.
intros; split.
+ reflexivity.
+ constructor.
+ now repeat econstructor.
Qed.

Lemma NfTermDecl_tEmpty : forall Γ, [|-[de] Γ] -> NfTermDecl Γ U tEmpty tEmpty.
Proof.
intros; split.
+ reflexivity.
+ constructor.
+ now repeat econstructor.
Qed.

Lemma NfTermDecl_tPair : forall Γ A A' A₀ B B' B₀ a a' a₀ b' b₀,
  [Γ |-[ de ] A] ->
  [Γ,, A |-[ de ] B] ->
  [Γ |-[ de ] tPair A' B' a' b' : tSig A B] ->
  [Γ |-[ de ] A ≅ A'] ->
  [Γ,, A |-[ de ] B ≅ B'] ->
  [Γ |-[ de ] B[a..] ≅ B[a'..]] ->
  [Γ |-[ de ] a ≅ a' : A] ->
  NfTypeDecl Γ A' A₀ ->
  NfTypeDecl (Γ,, A) B' B₀ ->
  NfTermDecl Γ A a' a₀ ->
  NfTermDecl Γ B[a..] b' b₀ ->
  NfTermDecl Γ (tSig A B) (tPair A' B' a' b') (tPair A₀ B₀ a₀ b₀).
Proof.
intros * ? ? ? ? ? ? ? [] [] [] [].
split.
+ apply dredalg_pair; tea.
+ now constructor.
+ apply TermPairCong; tea.
  - now eapply TypeTrans.
  - now eapply TypeTrans.
  - eapply convtm_conv; tea.
Qed.

Lemma NeTermDecl_NfTermDecl : forall Γ A n n₀,
  NeTermDecl Γ A n n₀ -> NfTermDecl Γ A n n₀.
Proof.
intros * []; tea.
Qed.

Lemma NeTermDecl_dne : forall Γ A n,
  [Γ |-[de] n : A] -> dne n -> NeTermDecl Γ A n n.
Proof.
intros; split.
+ now apply dnf_dne_whnf_whne.
+ split.
  - reflexivity.
  - now constructor.
  - now apply TermRefl.
Qed.

Lemma NfTermDecl_exp : forall Γ A t t' t₀,
  [Γ |-[de] t ⤳* t' : A] ->
  [Γ |-[de] A] ->
  [Γ |-[de] A ≅ A] ->
  [Γ |- t' : A] ->
  NfTermDecl Γ A t' t₀ -> NfTermDecl Γ A t t₀.
Proof.
intros * ? ? ? ? [].
split; tea.
+ etransitivity; [|tea].
  now eapply dred_red, redtm_sound.
+ transitivity t'; [|tea].
  eapply convtm_exp; tea.
  * now eapply redtm_refl.
  * now eapply TermRefl.
Qed.

Lemma NeTermDecl_tApp : forall Γ A B t t' t₀ u u' u₀,
  [Γ |-[de] t ≅ t' : tProd A B] ->
  [Γ |-[de] u ≅ u' : A] ->
  NeTermDecl Γ (tProd A B) t' t₀ ->
  NfTermDecl Γ A u' u₀ ->
  NeTermDecl Γ B[u..] (tApp t' u') (tApp t₀ u₀).
Proof.
intros * ? ? [? []] []; split; [now constructor|].
split.
+ apply dredalg_app; tea.
  apply dne_dnf_whne; [tea|].
  now eapply dredalg_whne.
+ do 2 constructor; [|tea].
  apply dne_dnf_whne; [tea|].
  now eapply dredalg_whne.
+ transitivity (tApp t u).
  - symmetry; econstructor; tea.
  - econstructor.
    * eapply TermTrans; tea.
    * transitivity u'; tea.
Qed.

Lemma NeTermDecl_tFst : forall Γ A B p p₀,
  NeTermDecl Γ (tSig A B) p p₀ ->
  NeTermDecl Γ A (tFst p) (tFst p₀).
Proof.
intros * [? []]; split; [now constructor|].
split.
+ now apply dredalg_fst.
+ do 2 constructor.
  apply dne_dnf_whne; [tea|].
  now eapply dredalg_whne.
+ now eapply TermFstCong.
Qed.

Lemma NeTermDecl_tSnd : forall Γ A B p p' p₀,
  [Γ |-[de] p ≅ p' : tSig A B] ->
  NeTermDecl Γ (tSig A B) p' p₀ ->
  NeTermDecl Γ B[(tFst p)..] (tSnd p') (tSnd p₀).
Proof.
intros * ? [? []]; split; [now constructor|].
split.
+ now apply dredalg_snd.
+ do 2 constructor.
  apply dne_dnf_whne; [tea|].
  now eapply dredalg_whne.
+ transitivity (tSnd p); [symmetry|]; eapply TermSndCong; tea.
  eapply TermTrans; tea.
Qed.

Lemma NeTermDecl_tNatElim : forall Γ P P' P₀ hz hz' hz₀ hs hs' hs₀ t t' t₀,
  [Γ,, tNat |-[de] P ≅ P'] ->
  [Γ |-[de] hz ≅ hz' : P[tZero..]] ->
  [Γ |-[de] hs ≅ hs' : elimSuccHypTy P] ->
  [Γ |-[de] t ≅ t' : tNat] ->
  NfTypeDecl (Γ,, tNat) P' P₀ ->
  NfTermDecl Γ P[tZero..] hz' hz₀ ->
  NfTermDecl Γ (elimSuccHypTy P) hs' hs₀ ->
  NeTermDecl Γ tNat t' t₀ ->
  NeTermDecl Γ P[t..] (tNatElim P' hz' hs' t') (tNatElim P₀ hz₀ hs₀ t₀).
Proof.
intros * ? ? ? ? [] [] [] [? []]; split; [now constructor|].
split.
+ eapply dredalg_natElim; tea.
  apply dne_dnf_whne; [tea|].
  now eapply dredalg_whne.
+ do 2 constructor; tea.
  apply dne_dnf_whne; [tea|].
  now eapply dredalg_whne.
+ transitivity (tNatElim P hz hs t); [symmetry|].
  - constructor; tea.
  - constructor; etransitivity; tea.
Qed.

Lemma NeTermDecl_tEmptyElim : forall Γ P P' P₀ t t' t₀,
  [Γ,, tEmpty |-[de] P ≅ P'] ->
  [Γ |-[de] t ≅ t' : tEmpty] ->
  NfTypeDecl (Γ,, tEmpty) P' P₀ ->
  NeTermDecl Γ tEmpty t' t₀ ->
  NeTermDecl Γ P[t..] (tEmptyElim P' t') (tEmptyElim P₀ t₀).
Proof.
intros * ? ? [] [? []]; split; [now constructor|].
split.
+ eapply dredalg_emptyElim; tea.
  apply dne_dnf_whne; [tea|].
  now eapply dredalg_whne.
+ do 2 constructor; tea.
  apply dne_dnf_whne; [tea|].
  now eapply dredalg_whne.
+ transitivity (tEmptyElim P t); [symmetry|].
  - constructor; tea.
  - constructor; etransitivity; tea.
Qed.

Lemma NeTermDecl_tIdElim : forall Γ A A' A₀ x x' x₀ P P' P₀ hr hr' hr₀ y y' y₀ t t' t₀,
  [Γ |-[de] A] ->
  [Γ |-[de] A ≅ A'] ->
  [Γ |-[de] x : A] ->
  [Γ |-[de] x ≅ x' : A] ->
  [Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |-[de] P ≅ P'] ->
  [Γ |-[de] hr ≅ hr' : P[tRefl A x .: x..]] ->
  [Γ |-[de] y ≅ y' : A] ->
  [Γ |-[de] t ≅ t' : tId A x y] ->
  NfTypeDecl Γ A' A₀ ->
  NfTermDecl Γ A x' x₀ ->
  NfTypeDecl (Γ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)) P' P₀ ->
  NfTermDecl Γ  P[tRefl A x .: x..] hr' hr₀ ->
  NfTermDecl Γ A y' y₀ ->
  NeTermDecl Γ (tId A x y) t' t₀ ->
  NeTermDecl Γ P[t .: y..] (tIdElim A' x' P' hr' y' t') (tIdElim A₀ x₀ P₀ hr₀ y₀ t₀).
Proof.
intros * ? ? ? ? ? ? ? ? [] [] [] [] [] [? []]; split; [now constructor|].
split.
+ eapply dredalg_idElim; tea.
  apply dne_dnf_whne; [tea|].
  now eapply dredalg_whne.
+ do 2 constructor; tea.
  apply dne_dnf_whne; [tea|].
  now eapply dredalg_whne.
+ transitivity (tIdElim A x P hr y t); [symmetry|].
  - constructor; tea.
  - constructor; tea; etransitivity; tea.
Qed.

Lemma NeTermDecl_tQuote : forall Γ n n₀, ~ closed0 n -> dnf n ->
  NfTermDecl Γ (arr tNat tNat) n n₀ ->
  NeTermDecl Γ tNat (tQuote n) (tQuote n₀).
Proof.
intros * Hc Hnf [].
split; [now constructor|].
split.
+ now apply dred_red, redalg_quote.
+ do 2 constructor; [|tea].
  replace n₀ with n by now eapply dred_dnf.
  assumption.
+ now constructor.
Qed.

Lemma NeTermDecl_tStep : forall Γ (t t' t₀ u u' u₀ : term),
  [Γ |-[ de ] t ≅ t' : arr tNat tNat] ->
  [Γ |-[ de ] u ≅ u' : tNat] ->
  [Γ |-[ de ] model.(run) : arr tNat (arr tNat tPNat) ] ->
  (~ closed0 t') + (~ closed0 u') -> dnf t' -> dnf u' ->
  NfTermDecl Γ (arr tNat tNat) t' t₀ ->
  NfTermDecl Γ tNat u' u₀ ->
  NeTermDecl Γ tNat (tStep t' u') (tStep t₀ u₀).
Proof.
intros * Ht Hu ? ? ? ? [] [].
assert (t' = t₀) by now eapply dred_dnf.
assert (u' = u₀) by now eapply dred_dnf.
subst.
split; [now constructor|]; split.
+ apply gred_red, redalg_step; tea.
+ do 2 constructor; tea.
+ eapply TermStepCong; tea.
Qed.

Lemma NeTermDecl_tReflect : forall Γ (t t' t₀ u u' u₀ : term),
  [Γ |-[ de ] t ≅ t' : arr tNat tNat] ->
  [Γ |-[ de ] u ≅ u' : tNat] ->
  [Γ |-[ de ] model.(run) : arr tNat (arr tNat tPNat) ] ->
  (~ closed0 t') + (~ closed0 u') -> dnf t' -> dnf u' ->
  NfTermDecl Γ (arr tNat tNat) t' t₀ ->
  NfTermDecl Γ tNat u' u₀ ->
  NeTermDecl Γ (tTotal t u) (tReflect t' u') (tReflect t₀ u₀).
Proof.
intros * Ht Hu ? ? ? ? [] [].
assert (t' = t₀) by now eapply dred_dnf.
assert (u' = u₀) by now eapply dred_dnf.
subst.
split; [now constructor|]; split.
+ apply gred_red, redalg_reflect; tea.
+ do 2 constructor; tea.
+ eapply TermConv; [apply TermReflectCong; tea|].
  apply convty_term, tTotal_decl_cong; tea; now symmetry.
Qed.

End Nf.

Module DeepTypingData.

  Definition nf : tag.
  Proof.
  constructor.
  Qed.

  #[export] Instance WfContext_Decl : WfContext nf := WfContextDecl.
  #[export] Instance WfType_Decl : WfType nf := WfTypeDecl.
  #[export] Instance Typing_Decl : Typing nf := TypingDecl.
  #[export] Instance ConvType_Decl : ConvType nf := ConvTypeNfDecl.
  #[export] Instance ConvTerm_Decl : ConvTerm nf := ConvTermNfDecl.
  #[export] Instance ConvNeuConv_Decl : ConvNeuConv nf := ConvTermNeDecl.
  #[export] Instance RedType_Decl : RedType nf := TypeRedClosure.
  #[export] Instance RedTerm_Decl : RedTerm nf := TermRedClosure.

End DeepTypingData.

Module DeepTypingProperties.

  Import DeclarativeTypingProperties DeepTypingData.

  Local Ltac invnf := repeat match goal with
  | H : [_ |-[nf] _ ≅ _] |- _ => destruct H
  | H : [_ |-[nf] _ ≅ _ : _] |- _ => destruct H
  | H : [_ |-[nf] _ ~ _ : _] |- _ => destruct H
  end.

  Lemma EvalStep_compat : forall Γ t u k v,
    EvalStep (ta := nf) Γ t u k v -> EvalStep (ta := de) Γ t u k v.
  Proof.
  intros * []; split; invnf; tea.
  intros k' Hk **; invnf.
  specialize (evstep_nil k' Hk); now invnf.
  Qed.

  #[export, refine] Instance WfCtxDeclProperties : WfContextProperties (ta := nf) := {}.
  Proof.
    1-2: now constructor.
    all: intro Γ; try change [|-[nf] Γ] with [|-[de] Γ].
    intros; now eapply wfc_wft.
    intros; now eapply wfc_ty.
    intros * []; now eapply wfc_convty.
    intros * []; now eapply wfc_convtm.
    intros; now eapply wfc_redty.
    intros; now eapply wfc_redtm.
  Qed.

  #[export, refine] Instance WfTypeDeclProperties : WfTypeProperties (ta := nf) := {}.
  Proof.
  all: try apply DeclarativeTypingProperties.WfTypeDeclProperties.
  Qed.

  #[export, refine] Instance ConvTypeDeclProperties : ConvTypeProperties (ta := nf) := {}.
  Proof.
  - intros * [A₀ B₀]; exists A₀ B₀.
    + now econstructor.
    + destruct nfconvtm_nfl0; split; tea; try now econstructor.
    + destruct nfconvtm_nfr0; split; tea; try now econstructor.
    + tea.
  - intros; apply ConvTypeNf_PER.
  - intros; invnf; eexists.
    + now apply typing_wk.
    + now apply NfTypeDecl_wk.
    + now apply NfTypeDecl_wk.
    + now eauto using eqnf_ren, wk_inj.
  - intros; invnf; eexists.
    + eapply TypeTrans ; [eapply TypeTrans | ..].
      2: eassumption.
      2: eapply TypeSym.
      all: now eapply RedConvTyC.
    + destruct nfconvty_nfl0; split; tea.
      * etransitivity; [|eassumption].
        apply dred_red, H.
      * eapply TypeTrans; [apply H|tea].
    + destruct nfconvty_nfr0; split; tea.
      * etransitivity; [|eassumption].
        apply dred_red, H0.
      * eapply TypeTrans; [apply H0|tea].
    + tea.
  - intros; invnf; eexists.
    + now do 2 constructor.
    + now apply NfTypeDecl_tSort.
    + now apply NfTypeDecl_tSort.
    + now constructor.
  - intros; invnf; eexists.
    + constructor; tea.
    + eapply NfTypeDecl_tProd; tea.
      * now eapply lrefl.
      * now eapply lrefl.
    + eapply NfTypeDecl_tProd; tea.
      now eapply urefl.
    + now apply eqnf_tProd.
  - intros; invnf; eexists.
    + constructor; match goal with H : _ |- _ => now apply H end.
    + eapply NfTypeDecl_tSig; tea.
      * now eapply lrefl.
      * now eapply lrefl.
    + eapply NfTypeDecl_tSig; tea.
      now eapply urefl.
    + now eapply eqnf_tSig.
  - intros; invnf; eexists.
    + constructor; now assumption.
    + apply NfTypeDecl_tId; tea.
    + apply NfTypeDecl_tId; tea.
      * now eapply NfTermConv.
      * now eapply NfTermConv.
    + now eapply eqnf_tId.
  Qed.

  Inductive isNfFun Γ A B : term -> Set :=
  | LamNfFun : forall A' A₀ t t₀,
    [Γ |-[ de ] A'] ->
    [Γ |-[ de ] A ≅ A'] ->
    [Γ,, A |-[ de ] t : B] ->
    [Γ,, A' |-[ de ] t : B] ->
    NfTypeDecl Γ A' A₀ -> NfTermDecl (Γ,, A) B (tApp (tLambda A' t)⟨↑⟩ (tRel 0)) t₀ ->
    isWfFun (ta := de) Γ A B (tLambda A' t) -> isNfFun Γ A B (tLambda A' t)
  | NeNfFun : forall n n₀, [Γ |-[de] n ~ n : tProd A B] ->
    NeTermDecl Γ (tProd A B) n n₀ -> isNfFun Γ A B n.
  Arguments LamNfFun {_ _ _}.
  Arguments NeNfFun {_ _ _}.

  Inductive isNfPair Γ A B : term -> Set :=
  | PairNfPair : forall A' A₀ B' B₀ a a₀ b b₀,
    [Γ |-[ de ] A'] ->
    [Γ |-[ de ] A ≅ A'] ->
    [Γ,, A |-[ de ] B ≅ B'] ->
    [Γ |-[ de ] B[a..] ≅ B'[a..]] ->
    [Γ |-[ de ] a ≅ a : A] ->
    NfTypeDecl Γ A' A₀ ->
    NfTypeDecl (Γ,, A) B' B₀ ->
    NfTermDecl Γ A a a₀ ->
    NfTermDecl Γ B[a..] b b₀ ->
    isWfPair (ta := de) Γ A B (tPair A' B' a b) -> isNfPair Γ A B (tPair A' B' a b)
  | NeNfPair : forall n n₀, [Γ |-[de] n ~ n : tSig A B] ->
    NeTermDecl Γ (tSig A B) n n₀ -> isNfPair Γ A B n.
  Arguments PairNfPair {_ _ _}.
  Arguments NeNfPair {_ _ _}.

  Lemma isWfFun_isNfFun : forall Γ A B t t₀,
    NfTermDecl (Γ,, A) B (tApp t⟨↑⟩ (tRel 0)) t₀ -> isWfFun Γ A B t -> isNfFun Γ A B t.
  Proof.
  intros * H Hwf; revert H; destruct Hwf; intros; invnf.
  + econstructor; tea.
    constructor; tea.
  + econstructor; tea.
  Qed.

  Lemma isWfPair_isNfPair : forall Γ A B t (* p₀ q₀ *),
    isWfPair Γ A B t -> isNfPair Γ A B t.
  Proof.
  intros * Hwf; destruct Hwf; intros; invnf.
  + econstructor; tea.
    constructor; tea.
  + econstructor; tea.
  Qed.

  Definition exp_fun {Γ A B f} (w : isNfFun Γ A B f) : term := match w with
  | LamNfFun _ A₀ _ t₀ _ _ _ _ _ _ _ => tLambda A₀ t₀
  | NeNfFun _ n₀ _ _ => n₀
  end.

  Definition exp_pair {Γ A B p} (w : isNfPair Γ A B p) : term := match w with
  | PairNfPair _ A₀ _ B₀ _ a₀ _ b₀ _ _ _ _ _ _ _ _ _ _ => tPair A₀ B₀ a₀ b₀
  | NeNfPair _ n₀ _ _ => n₀
  end.

  Lemma NfTerm_eta_fun : forall Γ A B n n₀ t₀,
    NeTermDecl Γ (tProd A B) n n₀ ->
    NfTermDecl (Γ,, A) B (tApp n⟨↑⟩ (tRel 0)) t₀ ->
    t₀ = tApp n₀⟨↑⟩ (tRel 0).
  Proof.
  intros.
  assert (dne n₀⟨↑⟩).
  { now eapply dne_ren, NeTerm_dne. }
  eapply dredalg_det; [now eapply nftmdecl_nf| |now eapply nftmdecl_red|].
  - do 2 constructor; [|repeat constructor]; tea.
  - apply dredalg_app; [| |tea|reflexivity].
    * now eapply whne_ren, netmdecl_whne.
    * eapply gcredalg_wk, netmdecl_nf; now eauto using shift_inj.
  Qed.

  Lemma eqnf_exp_fun : forall Γ A B f f₀ g g₀ (nf : isNfFun Γ A B f) (ng : isNfFun Γ A B g),
    NfTermDecl (Γ,, A) B (tApp f⟨↑⟩ (tRel 0)) f₀ ->
    NfTermDecl (Γ,, A) B (tApp g⟨↑⟩ (tRel 0)) g₀ ->
    eqnf f₀ g₀ ->
    eqnf (exp_fun nf) (exp_fun ng).
  Proof.
  intros Γ A B f f₀ g g₀ [] [] ? ? ?; cbn.
  + apply eqnf_tLambda; eauto using nftydecl_nf.
    repeat match goal with H : NfTermDecl _ _ _ ?t, H' : NfTermDecl _ _ _ ?u |- _ =>
      (assert (t = u) by now eapply NfTermDecl_unique); subst; clear H
    end.
    tea.
  + repeat match goal with H : NfTermDecl _ _ _ ?t, H' : NfTermDecl _ _ _ ?u |- _ =>
      (assert (t = u) by now eapply NfTermDecl_unique); subst; clear H
    end.
    apply eqnf_tLambda_whne; eauto using NeTerm_whne, nftydecl_nf.
    etransitivity; [tea|].
    replace (tApp n₀⟨↑⟩ (tRel 0)) with g₀; [now eapply urefl|].
    now eapply NfTerm_eta_fun.
  + repeat match goal with H : NfTermDecl _ _ _ ?t, H' : NfTermDecl _ _ _ ?u |- _ =>
      (assert (t = u) by now eapply NfTermDecl_unique); subst; clear H
    end.
    apply eqnf_whne_tLambda; eauto using NeTerm_whne, nftydecl_nf.
    etransitivity; [|tea].
    replace (tApp n₀⟨↑⟩ (tRel 0)) with f₀; [now eapply lrefl|].
    now eapply NfTerm_eta_fun.
  + rename n₀0 into m₀.
    assert (f₀ = tApp n₀⟨↑⟩ (tRel 0)) by now eapply NfTerm_eta_fun.
    assert (g₀ = tApp m₀⟨↑⟩ (tRel 0)) by now eapply NfTerm_eta_fun.
    subst.
    assert (Hn₀ : whne n₀⟨↑⟩) by now eapply whne_ren, NeTerm_whne.
    assert (Hm₀ : whne m₀⟨↑⟩) by now eapply whne_ren, NeTerm_whne.
    inversion H1; subst.
    eapply eqnf_ren_rev; [apply shift_inj|tea].
  Qed.

  Lemma NfTerm_eta_pair_fst : forall Γ A B n n₀ p₀,
    NeTermDecl Γ (tSig A B) n n₀ ->
    NfTermDecl Γ A (tFst n) p₀ ->
    p₀ = tFst n₀.
  Proof.
  intros * [? []] [].
  eapply dredalg_det; eauto using dnf, dne, dne_dnf_whne, dredalg_whne.
  now eapply dredalg_fst.
  Qed.

  Lemma NfTerm_eta_pair_snd : forall Γ P A B n n₀ p₀,
    NeTermDecl Γ (tSig A B) n n₀ ->
    NfTermDecl Γ P (tSnd n) p₀ ->
    p₀ = tSnd n₀.
  Proof.
  intros * [? []] [].
  eapply dredalg_det; eauto using dnf, dne, dne_dnf_whne, dredalg_whne.
  now eapply dredalg_snd.
  Qed.

  Lemma NfTerm_fst_red : forall Γ P Q A B a b p₀ q₀,
    NfTermDecl Γ Q a p₀ ->
    NfTermDecl Γ P (tFst (tPair A B a b)) q₀ -> p₀ = q₀.
  Proof.
  intros * [] []; eapply dredalg_det; tea.
  eapply dred_red_det; tea.
  econstructor; [constructor|reflexivity].
  Qed.

  Lemma NfTerm_snd_red : forall Γ P Q A B a b p₀ q₀,
    NfTermDecl Γ Q b p₀ ->
    NfTermDecl Γ P (tSnd (tPair A B a b)) q₀ -> p₀ = q₀.
  Proof.
  intros * [] []; eapply dredalg_det; tea.
  eapply dred_red_det; tea.
  econstructor; [constructor|reflexivity].
  Qed.

  Lemma eqnf_exp_pair : forall Γ A B p pl₀ pr₀ q ql₀ qr₀ (np : isNfPair Γ A B p) (nq : isNfPair Γ A B q),
    NfTermDecl Γ A (tFst p) pl₀ ->
    NfTermDecl Γ A (tFst q) ql₀ ->
    eqnf pl₀ ql₀ ->
    NfTermDecl Γ B[(tFst p)..] (tSnd p) pr₀ ->
    NfTermDecl Γ B[(tFst p)..] (tSnd q) qr₀ ->
    eqnf pr₀ qr₀ ->
    eqnf (exp_pair np) (exp_pair nq).
  Proof.
  intros Γ A B p pl₀ pr₀ q ql₀ qr₀ [] [] **; cbn.
  + apply eqnf_tPair.
    - match goal with |- eqnf ?l ?r =>
        replace l with pl₀ by (now symmetry; eapply NfTerm_fst_red);
        replace r with ql₀ by (now symmetry; eapply NfTerm_fst_red)
      end; tea.
    - match goal with |- eqnf ?l ?r =>
        replace l with pr₀ by (now symmetry; eapply NfTerm_snd_red);
        replace r with qr₀ by (now symmetry; eapply NfTerm_snd_red)
      end; tea.
  + apply eqnf_tPair_whne.
    - match goal with |- eqnf ?l ?r =>
        replace l with pl₀ by (now symmetry; eapply NfTerm_fst_red);
        replace r with ql₀ by (now eapply NfTerm_eta_pair_fst)
      end; tea.
    - match goal with |- eqnf ?l ?r =>
        replace l with pr₀ by (now symmetry; eapply NfTerm_snd_red);
        replace r with qr₀ by (now eapply NfTerm_eta_pair_snd)
      end; tea.
  + apply eqnf_whne_tPair.
    - match goal with |- eqnf ?l ?r =>
        replace l with pl₀ by (now eapply NfTerm_eta_pair_fst);
        replace r with ql₀ by (now symmetry; eapply NfTerm_fst_red)
      end; tea.
    - match goal with |- eqnf ?l ?r =>
        replace l with pr₀ by (now eapply NfTerm_eta_pair_snd);
        replace r with qr₀ by (now symmetry; eapply NfTerm_snd_red)
      end; tea.
  + match goal with |- eqnf ?l ?r =>
      assert (pl₀ = tFst l) by (now eapply NfTerm_eta_pair_fst);
      assert (ql₀ = tFst r) by (now eapply NfTerm_eta_pair_fst)
    end.
    subst; inversion H1; tea.
  Qed.

  #[export, refine] Instance ConvTermDeclProperties : ConvTermProperties (ta := nf) := {}.
  Proof.
  + apply ConvTermNf_PER.
  + intros; invnf; eexists.
    - now eapply TermConv.
    - now eapply NfTermConv.
    - now eapply NfTermConv.
    - tea.
  + intros; invnf; eexists.
    - now apply typing_wk.
    - now apply NfTermDecl_wk.
    - now apply NfTermDecl_wk.
    - now eauto using eqnf_ren, wk_inj.
  + intros; invnf; eexists.
    - now eapply convtm_exp.
    - eapply NfTermDecl_exp with (t' := t'); tea.
    - eapply NfTermDecl_exp with (t' := u'); tea.
    - tea.
  + intros; invnf; eexists.
    - now apply convtm_convneu.
    - now apply NeTermDecl_NfTermDecl.
    - now apply NeTermDecl_NfTermDecl.
    - tea.
  + intros; invnf; eexists.
    - now apply convtm_prod.
    - eapply NfTermDecl_tProd; tea.
      * now eapply lrefl.
      * now eapply lrefl.
    - eapply NfTermDecl_tProd; tea.
      now eapply urefl.
    - now apply eqnf_tProd.
  + intros; invnf; eexists.
    - constructor; tea.
    - eapply NfTermDecl_tSig; tea.
      * now eapply lrefl.
      * now eapply lrefl.
    - eapply NfTermDecl_tSig; tea.
      * now eapply urefl.
    - now apply eqnf_tSig.
  + intros; invnf; eexists.
    - constructor; tea; now eapply TypeRefl.
    - apply NfTermDecl_tLambda0; tea.
    - apply NfTermDecl_tLambda0; tea.
    - now apply eqnf_tLambda.
  + intros * ? ? ? Hf ? Hg [].
    eapply isWfFun_isNfFun in Hf; [|tea].
    eapply isWfFun_isNfFun in Hg; [|tea].
    eexists (exp_fun Hf) (exp_fun Hg).
    - apply convtm_eta; tea.
      * destruct Hf; constructor; tea.
      * destruct Hg; constructor; tea.
    - destruct Hf; cbn.
      * apply NfTermDecl_tLambda; tea.
      * now apply netmdecl_nf.
    - destruct Hg; cbn.
      * apply NfTermDecl_tLambda; tea.
      * now apply netmdecl_nf.
    - now eapply eqnf_exp_fun.
  + intros; eexists; tea.
    - do 2 constructor; tea.
    - now apply NfTermDecl_tNat.
    - now apply NfTermDecl_tNat.
    - now apply eqnf_tNat.
  + intros; eexists.
    - now do 2 constructor.
    - now apply NfTermDecl_tZero.
    - now apply NfTermDecl_tZero.
    - now apply eqnf_tZero.
  + intros; invnf; eexists.
    - constructor; tea.
    - now apply NfTermDecl_tSucc.
    - now apply NfTermDecl_tSucc.
    - now apply eqnf_tSucc.
  + intros * ? ? ? Hp ? Hp' [] [].
    eapply isWfPair_isNfPair in Hp; tea.
    eapply isWfPair_isNfPair in Hp'; tea.
    eexists (exp_pair Hp) (exp_pair Hp').
    - etransitivity; [|now eapply TermPairEta].
      etransitivity; [now symmetry; eapply TermPairEta|].
      constructor; tea; now apply TypeRefl.
    - destruct Hp.
      * invnf.
        eapply NfTermDecl_tPair; [..|tea]; tea.
        now eapply lrefl.
      * now eapply netmdecl_nf.
    - destruct Hp'.
      * invnf.
        eapply NfTermDecl_tPair; tea.
        now eapply lrefl.
      * now eapply netmdecl_nf.
    - now eapply eqnf_exp_pair.
  + intros; invnf; eexists.
    - now do 2 constructor.
    - now apply NfTermDecl_tEmpty.
    - now apply NfTermDecl_tEmpty.
    - now apply eqnf_tEmpty.
  + intros; invnf; eexists.
    - now constructor.
    - now apply NfTermDecl_tId.
    - apply NfTermDecl_tId; tea.
      all: eapply NfTermConv; tea; now constructor.
    - now apply eqnf_tId.
  + intros; invnf; eexists.
    - now constructor.
    - now apply NfTermDecl_Refl.
    - eapply NfTermConv; [symmetry; now constructor|apply NfTermDecl_Refl; tea].
      eapply NfTermConv; tea.
    - now apply eqnf_tRefl.
  Qed.

  #[export, refine] Instance TypingDeclProperties : TypingProperties (ta := nf) := {}.
  Proof.
  all: try apply DeclarativeTypingProperties.TypingDeclProperties.
  + intros * []; now constructor.
  + intros * [] []; now econstructor.
  + intros * [] [] ?.
    now eapply DeclarativeTypingProperties.TypingDeclProperties.
  + intros * ? []; now econstructor.
  Qed.

  #[export, refine] Instance ConvNeuDeclProperties : ConvNeuProperties (ta := nf) := {}.
  Proof.
  + apply ConvTermNe_PER.
  + intros; invnf; eexists.
    - now eapply convneu_conv.
    - now eapply NeTermConv.
    - now eapply NeTermConv.
    - tea.
  + intros; invnf; eexists.
    - now eapply convneu_wk.
    - now eapply NeTermDecl_wk.
    - now eapply NeTermDecl_wk.
    - eauto using eqnf_ren, wk_inj.
  + intros; invnf; now eapply convneu_whne.
  + intros; invnf; eexists.
    - now apply convneu_var.
    - apply NeTermDecl_dne; tea; now constructor.
    - apply NeTermDecl_dne; tea; now constructor.
    - now apply eqnf_tRel.
  + intros * [f₀ g₀ Hfg] []; eexists.
    - now eapply convneu_app.
    - eapply NeTermDecl_tApp; tea.
      * eapply lrefl, Hfg.
      * eapply lrefl; tea.
    - eapply NeTermDecl_tApp; tea.
      apply Hfg.
    - now apply eqnf_tApp.
  + intros; invnf; eexists.
    - now eapply convneu_natElim.
    - eapply NeTermDecl_tNatElim; tea; try now symmetry.
      * now eapply lrefl.
      * now eapply lrefl, convtm_convneu.
    - eapply NeTermDecl_tNatElim; tea.
      now eapply convtm_convneu.
    - now apply eqnf_tNatElim.
  + intros; invnf; eexists.
    - now eapply convneu_emptyElim.
    - eapply NeTermDecl_tEmptyElim; tea.
      * now eapply lrefl.
      * now eapply lrefl, convtm_convneu.
    - eapply NeTermDecl_tEmptyElim; tea.
      now eapply convtm_convneu.
    - now apply eqnf_tEmptyElim.
  + intros; invnf; eexists.
    - now eapply convneu_fst.
    - now eapply NeTermDecl_tFst.
    - now eapply NeTermDecl_tFst.
    - now apply eqnf_tFst.
  + intros; invnf; eexists.
    - now eapply convneu_snd.
    - eapply NeTermDecl_tSnd; tea.
      eapply lrefl; tea; apply neconvtm_conv0.
    - eapply NeTermDecl_tSnd; tea.
      now apply neconvtm_conv0.
    - now apply eqnf_tSnd.
  + intros; invnf; eexists.
    - now eapply convneu_IdElim.
    - eapply NeTermDecl_tIdElim; tea.
      all: try now eapply lrefl.
      now eapply lrefl, convtm_convneu.
    - eapply NeTermDecl_tIdElim; tea.
      now eapply convtm_convneu.
    - now apply eqnf_tIdElim.
  + intros ? n n' **; invnf; eexists.
    - now eapply convneu_quote.
    - now apply NeTermDecl_tQuote.
    - now apply NeTermDecl_tQuote.
    - match goal with |- eqnf (tQuote ?t) (tQuote ?u) =>
        replace t with n in * by eauto using dred_dnf, nftmdecl_red, nftmdecl_nf;
        replace u with n' in * by eauto using dred_dnf, nftmdecl_red, nftmdecl_nf
      end.
      now apply eqnf_tQuote.
  + intros; invnf; eexists.
    - now eapply convneu_step.
    - eapply NeTermDecl_tStep; tea; try now eapply lrefl.
      all: try now symmetry.
    - eapply NeTermDecl_tStep; tea.
      all: etransitivity; [now symmetry|tea].
    - match goal with |- eqnf (tStep ?f ?n) (tStep ?g ?m) =>
        replace f with t in * by eauto using dred_dnf, nftmdecl_red, nftmdecl_nf;
        replace g with t' in * by eauto using dred_dnf, nftmdecl_red, nftmdecl_nf;
        replace n with u in * by eauto using dred_dnf, nftmdecl_red, nftmdecl_nf;
        replace m with u' in * by eauto using dred_dnf, nftmdecl_red, nftmdecl_nf
      end.
      match goal with H : NfTermDecl _ _  t ?r |- _ =>
        tryif unify t r then fail else assert (r = t) by (now eapply NfTermDecl_unique); subst
      end.
      match goal with H : NfTermDecl _ _  u ?r |- _ =>
        tryif unify u r then fail else assert (r = u) by (now eapply NfTermDecl_unique); subst
      end.
      now apply eqnf_tStep.
  + intros; invnf; eexists.
    - now eapply convneu_reflect.
    - apply NeTermDecl_tReflect; tea; try now eapply lrefl.
      all: try now symmetry.
    - apply NeTermDecl_tReflect; tea.
      all: etransitivity; [now symmetry|tea].
    - match goal with |- eqnf (tReflect ?f ?n) (tReflect ?g ?m) =>
        replace f with t in * by eauto using dred_dnf, nftmdecl_red, nftmdecl_nf;
        replace g with t' in * by eauto using dred_dnf, nftmdecl_red, nftmdecl_nf;
        replace n with u in * by eauto using dred_dnf, nftmdecl_red, nftmdecl_nf;
        replace m with u' in * by eauto using dred_dnf, nftmdecl_red, nftmdecl_nf
      end.
      match goal with H : NfTermDecl _ _  t ?r |- _ =>
        tryif unify t r then fail else assert (r = t) by (now eapply NfTermDecl_unique); subst
      end.
      match goal with H : NfTermDecl _ _  u ?r |- _ =>
        tryif unify u r then fail else assert (r = u) by (now eapply NfTermDecl_unique); subst
      end.
      now apply eqnf_tReflect.
  Qed.

  #[export, refine] Instance RedTypeDeclProperties : RedTypeProperties (ta := nf) := {}.
  Proof.
  all: try apply DeclarativeTypingProperties.RedTypeDeclProperties.
  Qed.

  #[export, refine] Instance RedTermDeclProperties : RedTermProperties (ta := nf) := {}.
  Proof.
  all: try apply DeclarativeTypingProperties.RedTermDeclProperties.
  + intros; invnf; now apply DeclarativeTypingProperties.RedTermDeclProperties.
  + intros; invnf; now apply DeclarativeTypingProperties.RedTermDeclProperties.
  + intros; invnf; now apply DeclarativeTypingProperties.RedTermDeclProperties.
  + intros; invnf.
    match goal with H : EvalStep _ _ _ _ _ |- _ => apply EvalStep_compat in H end.
    now eapply DeclarativeTypingProperties.RedTermDeclProperties.
  + intros; invnf; now eapply DeclarativeTypingProperties.RedTermDeclProperties.
  + intros; invnf.
    match goal with H : EvalStep _ _ _ _ _ |- _ => apply EvalStep_compat in H end.
    now eapply DeclarativeTypingProperties.RedTermDeclProperties.
  + intros; invnf; now apply DeclarativeTypingProperties.RedTermDeclProperties.
  + intros; invnf; now eapply DeclarativeTypingProperties.RedTermDeclProperties.
  Qed.

  #[export] Instance DeclarativeTypingProperties : GenericTypingProperties nf _ _ _ _ _ _ _ _ _ _ := {}.

  #[local]
  Lemma NfConvBuild : forall Γ A t t₀, [Γ |-[ de ] t ≅ t₀ : A] -> [t ⇶* t₀] -> eqnf t₀ t₀ -> dnf t₀ -> [Γ |-[ nf ] t ≅ t₀ : A].
  Proof.
  intros; exists t₀ t₀; tea; try now split.
  + split; tea.
    - reflexivity.
    - now eapply urefl.
  Qed.

  #[export] Instance DeclarativeSNProperties : SNTypingProperties nf _ _ _ _ _.
  Proof.
  assert (Hper : forall t u, eqnf t u -> eqnf t t).
  { intros; eapply Transitive_eqnf; [tea|now eapply Symmetric_eqnf]. }
  split.
  + intros * [t₀ u₀ ? [] []].
    assert (eqnf t₀ t₀) by eauto.
    assert (eqnf u₀ u₀) by eauto using Symmetric_eqnf.
    exists t₀, u₀; prod_splitter; tea.
    - now split.
    - now split.
    - now apply NfConvBuild.
    - now apply NfConvBuild.
  Qed.

End DeepTypingProperties.
