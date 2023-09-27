(** * LogRel.DeclarativeInstance: proof that declarative typing is an instance of generic typing. *)
From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms UntypedReduction Weakening GenericTyping DeclarativeTyping DeclarativeInstance.

Import DeclarativeTypingData.

Record NfTypeDecl Γ (A : term) := {
  nftydecl_val : term;
  nftydecl_red : [A ⇶* nftydecl_val];
  nftydecl_nf : dnf nftydecl_val;
  nftydecl_conv : [Γ |- A ≅ nftydecl_val];
}.

Record NfTermDecl Γ (A t : term) := {
  nftmdecl_val : term;
  nftmdecl_red : [t ⇶* nftmdecl_val];
  nftmdecl_nf : dnf nftmdecl_val;
  nftmdecl_conv : [Γ |- t ≅ nftmdecl_val : A];
}.

Record NeTermDecl Γ (A t : term) := {
  netmdecl_whne : whne t;
  netmdecl_nf : NfTermDecl Γ A t;
}.

Record ConvTypeNfDecl Γ A B := {
  nfconvty_conv : [Γ |- A ≅ B];
  nfconvty_nfl : NfTypeDecl Γ A;
  nfconvty_nfr : NfTypeDecl Γ B;
}.

Record ConvTermNfDecl Γ A t u := {
  nfconvtm_conv : [Γ |- t ≅ u : A];
  nfconvtm_nfl : NfTermDecl Γ A t;
  nfconvtm_nfr : NfTermDecl Γ A u;
}.

Record ConvTermNeDecl Γ A t u := {
  neconvtm_conv : [Γ |- t ~ u : A];
  neconvtm_nfl : NeTermDecl Γ A t;
  neconvtm_nfr : NeTermDecl Γ A u;
}.

Section Nf.

Import DeclarativeTypingProperties.

#[local]
Lemma ConvTypeNf_PER : forall Γ, PER (ConvTypeNfDecl Γ).
Proof.
intros Γ; split.
- intros t u []; split; tea.
  now apply TypeSym.
- intros t u r [] []; split; tea.
  now eapply TypeTrans.
Qed.

Lemma NfTermConv : forall Γ A B t, [Γ |-[de] A ≅ B] -> NfTermDecl Γ A t -> NfTermDecl Γ B t.
Proof.
intros * H [r]; exists r; tea.
now eapply TermConv.
Qed.

Lemma NeTermConv : forall Γ A B t, [Γ |-[de] A ≅ B] -> NeTermDecl Γ A t -> NeTermDecl Γ B t.
Proof.
intros * ? [Hne Hnf]; split; [tea|].
now eapply NfTermConv.
Qed.

Lemma NfTypeDecl_tSort : forall Γ, [|-[de] Γ] -> NfTypeDecl Γ U.
Proof.
intros; exists U.
+ reflexivity.
+ constructor.
+ now do 2 constructor.
Qed.

Lemma NfTypeDecl_tProd : forall Γ A A' B,
  [Γ |-[de] A] ->
  [Γ |-[de] A ≅ A'] ->
  [Γ,, A |-[de] B ≅ B] ->
  NfTypeDecl Γ A' -> NfTypeDecl (Γ,, A) B -> NfTypeDecl Γ (tProd A' B).
Proof.
intros Γ A A' B HA HAA' HBB [A₀ HRA HAnf] [B₀ HRB HBnf].
exists (tProd A₀ B₀).
+ now apply dredalg_prod.
+ now constructor.
+ assert [ Γ |-[de] tProd A B ≅ tProd A' B ].
  { constructor; tea. }
  eapply TypeTrans; [now eapply TypeSym|].
  constructor; [tea|now eapply TypeTrans|tea].
Qed.

Lemma NfTermDecl_tProd : forall Γ A A' B,
  [Γ |-[de] A : U] ->
  [Γ |-[de] A ≅ A' : U] ->
  [Γ,, A |-[de] B ≅ B : U] ->
  NfTermDecl Γ U A' -> NfTermDecl (Γ,, A) U B -> NfTermDecl Γ U (tProd A' B).
Proof.
intros Γ A A' B HA HAA' HBB [A₀ HRA HAnf] [B₀ HRB HBnf].
exists (tProd A₀ B₀).
+ now apply dredalg_prod.
+ now constructor.
+ assert [ Γ |-[de] tProd A B ≅ tProd A' B : U ].
  { constructor; tea. }
  eapply TermTrans; [now eapply TermSym|].
  constructor; [tea|now eapply TermTrans|tea].
Qed.

Lemma NfTermDecl_tLambda : forall Γ A A' B t,
  [Γ |-[ de ] A] ->
  [Γ |-[ de ] A'] ->
  [Γ,, A |-[ de ] B] ->
  [Γ |-[ de ] A ≅ A'] ->
  [Γ |-[ de ] tLambda A' t : tProd A B] ->
  [Γ,, A |-[ de ] t : B] ->
  [Γ,, A' |-[ de ] t : B] ->
  NfTypeDecl Γ A' ->
  NfTermDecl (Γ,, A) B (tApp (tLambda A' t)⟨↑⟩ (tRel 0)) ->
  NfTermDecl Γ (tProd A B) (tLambda A' t).
Proof.
intros * ? ? ? ? ? ? Ht [A₀] [t₀].
assert (eq0 : forall t, t⟨upRen_term_term ↑⟩[(tRel 0)..] = t).
{ bsimpl; apply idSubst_term; intros [|]; reflexivity. }
exists (tLambda A₀ t₀).
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

Lemma NfTypeDecl_tSig : forall Γ A A' B,
  [Γ |-[de] A] ->
  [Γ |-[de] A ≅ A'] ->
  [Γ,, A |-[de] B ≅ B] ->
  NfTypeDecl Γ A' -> NfTypeDecl (Γ,, A) B -> NfTypeDecl Γ (tSig A' B).
Proof.
intros Γ A A' B HA HAA' HBB [A₀ HRA HAnf] [B₀ HRB HBnf].
exists (tSig A₀ B₀).
+ now apply dredalg_sig.
+ now constructor.
+ assert [ Γ |-[de] tSig A B ≅ tSig A' B ].
  { constructor; tea. }
  eapply TypeTrans; [now eapply TypeSym|].
  constructor; [tea|now eapply TypeTrans|tea].
Qed.

Lemma NfTermDecl_tSig : forall Γ A A' B,
  [Γ |-[de] A : U] ->
  [Γ |-[de] A ≅ A' : U] ->
  [Γ,, A |-[de] B ≅ B : U] ->
  NfTermDecl Γ U A' -> NfTermDecl (Γ,, A) U B -> NfTermDecl Γ U (tSig A' B).
Proof.
intros Γ A A' B HA HAA' HBB [A₀ HRA HAnf] [B₀ HRB HBnf].
exists (tSig A₀ B₀).
+ now apply dredalg_sig.
+ now constructor.
+ assert [ Γ |-[de] tSig A B ≅ tSig A' B : U ].
  { constructor; tea. }
  eapply TermTrans; [now eapply TermSym|].
  constructor; [tea|now eapply TermTrans|tea].
Qed.

Lemma NfTypeDecl_tId : forall Γ A t u, NfTypeDecl Γ A -> NfTermDecl Γ A t -> NfTermDecl Γ A u -> NfTypeDecl Γ (tId A t u).
Proof.
intros Γ A t u [A₀ HRA HAnf] [t₀] [u₀].
exists (tId A₀ t₀ u₀).
+ now apply dredalg_id.
+ now constructor.
+ constructor; tea.
Qed.

Lemma NfTermDecl_tId : forall Γ A t u, NfTermDecl Γ U A -> NfTermDecl Γ A t -> NfTermDecl Γ A u -> NfTermDecl Γ U (tId A t u).
Proof.
intros Γ A t u [A₀ HRA HAnf] [t₀] [u₀].
exists (tId A₀ t₀ u₀).
+ now apply dredalg_id.
+ now constructor.
+ constructor; tea.
Qed.

Lemma NfTermDecl_Refl : forall Γ A x,
  NfTypeDecl Γ A -> NfTermDecl Γ A x -> NfTermDecl Γ (tId A x x) (tRefl A x).
Proof.
intros * [A₀] [x₀].
exists (tRefl A₀ x₀).
+ now apply dredalg_refl.
+ now constructor.
+ constructor; tea.
Qed.

Lemma NfTypeDecl_wk : forall Γ Δ A (ρ : Δ ≤ Γ), [|- Δ] -> NfTypeDecl Γ A -> NfTypeDecl Δ A⟨ρ⟩.
Proof.
intros * tΔ [R]; exists R⟨ρ⟩.
+ now apply gcredalg_wk.
+ now apply dnf_ren.
+ now apply typing_wk.
Qed.

Lemma NfTermDecl_wk : forall Γ Δ A t (ρ : Δ ≤ Γ), [|- Δ] -> NfTermDecl Γ A t -> NfTermDecl Δ A⟨ρ⟩ t⟨ρ⟩.
Proof.
intros * tΔ [r]; exists r⟨ρ⟩.
+ now apply gcredalg_wk.
+ now apply dnf_ren.
+ now apply typing_wk.
Qed.

Lemma NeTermDecl_wk : forall Γ Δ A t (ρ : Δ ≤ Γ), [|- Δ] -> NeTermDecl Γ A t -> NeTermDecl Δ A⟨ρ⟩ t⟨ρ⟩.
Proof.
intros * tΔ [Hne Hnf]; split.
+ now eapply whne_ren.
+ now eapply NfTermDecl_wk.
Qed.

Lemma NfTypeDecl_tNat : forall Γ, [|-[de] Γ] -> NfTypeDecl Γ tNat.
Proof.
intros; exists tNat.
+ reflexivity.
+ constructor.
+ now repeat econstructor.
Qed.

Lemma NfTermDecl_tNat : forall Γ, [|-[de] Γ] -> NfTermDecl Γ U tNat.
Proof.
intros; exists tNat.
+ reflexivity.
+ constructor.
+ now repeat econstructor.
Qed.

Lemma NfTermDecl_tZero : forall Γ, [|-[de] Γ] -> NfTermDecl Γ tNat tZero.
Proof.
intros; exists tZero.
+ reflexivity.
+ constructor.
+ now do 2 constructor.
Qed.

Lemma NfTermDecl_tSucc : forall Γ n, NfTermDecl Γ tNat n -> NfTermDecl Γ tNat (tSucc n).
Proof.
intros * [n₀]; exists (tSucc n₀).
+ now apply dredalg_succ.
+ now constructor.
+ now do 2 constructor.
Qed.

Lemma NfTypeDecl_tEmpty : forall Γ, [|-[de] Γ] -> NfTypeDecl Γ tEmpty.
Proof.
intros; exists tEmpty.
+ reflexivity.
+ constructor.
+ now repeat econstructor.
Qed.

Lemma NfTermDecl_tEmpty : forall Γ, [|-[de] Γ] -> NfTermDecl Γ U tEmpty.
Proof.
intros; exists tEmpty.
+ reflexivity.
+ constructor.
+ now repeat econstructor.
Qed.

Lemma NfTermDecl_tPair : forall Γ A A' B B' a a' b',
  [Γ |-[ de ] A] ->
  [Γ,, A |-[ de ] B] ->
  [Γ |-[ de ] tPair A' B' a' b' : tSig A B] ->
  [Γ |-[ de ] A ≅ A'] ->
  [Γ,, A |-[ de ] B ≅ B'] ->
  [Γ |-[ de ] B[a..] ≅ B[a'..]] ->
  [Γ |-[ de ] a ≅ a' : A] ->
  NfTypeDecl Γ A' ->
  NfTypeDecl (Γ,, A) B' ->
  NfTermDecl Γ A a' ->
  NfTermDecl Γ B[a..] b' ->
  NfTermDecl Γ (tSig A B) (tPair A' B' a' b').
Proof.
intros * ? ? ? ? ? ? ? [A₀] [B₀] [a₀] [b₀].
exists (tPair A₀ B₀ a₀ b₀).
+ apply dredalg_pair; tea.
+ now constructor.
+ apply TermPairCong; tea.
  - now eapply TypeTrans.
  - now eapply TypeTrans.
  - eapply convtm_conv; tea.
Qed.

Lemma NeTermDecl_NfTermDecl : forall Γ A n,
  NeTermDecl Γ A n -> NfTermDecl Γ A n.
Proof.
intros * []; tea.
Qed.

Lemma NeTermDecl_dne : forall Γ A n,
  [Γ |-[de] n : A] -> dne n -> NeTermDecl Γ A n.
Proof.
intros; split.
+ now apply dnf_dne_whnf_whne.
+ exists n.
  - reflexivity.
  - now constructor.
  - now apply TermRefl.
Qed.

Lemma NfTermDecl_exp : forall Γ A t t',
  [Γ |-[de] t ⤳* t' : A] ->
  [Γ |-[de] A] ->
  [Γ |-[de] A ≅ A] ->
  [Γ |- t' : A] ->
  NfTermDecl Γ A t' -> NfTermDecl Γ A t.
Proof.
intros * ? ? ? ? [t₀].
exists t₀; tea.
+ etransitivity; [|tea].
  now eapply dred_red, redtm_sound.
+ transitivity t'; [|tea].
  eapply convtm_exp; tea.
  * now eapply redtm_refl.
  * now eapply TermRefl.
Qed.

Lemma NeTermDecl_tApp : forall Γ A B t t' u u',
  [Γ |-[de] t ≅ t' : tProd A B] ->
  [Γ |-[de] u ≅ u' : A] ->
  NeTermDecl Γ (tProd A B) t' ->
  NfTermDecl Γ A u' ->
  NeTermDecl Γ B[u..] (tApp t' u').
Proof.
intros * ? ? [? [t₀]] [u₀]; split; [now constructor|].
exists (tApp t₀ u₀).
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

Lemma NeTermDecl_tFst : forall Γ A B p,
  NeTermDecl Γ (tSig A B) p ->
  NeTermDecl Γ A (tFst p).
Proof.
intros * [? [p₀]]; split; [now constructor|].
exists (tFst p₀).
+ now apply dredalg_fst.
+ do 2 constructor.
  apply dne_dnf_whne; [tea|].
  now eapply dredalg_whne.
+ now eapply TermFstCong.
Qed.

Lemma NeTermDecl_tSnd : forall Γ A B p p',
  [Γ |-[de] p ≅ p' : tSig A B] ->
  NeTermDecl Γ (tSig A B) p' ->
  NeTermDecl Γ B[(tFst p)..] (tSnd p').
Proof.
intros * ? [? [p₀]]; split; [now constructor|].
exists (tSnd p₀).
+ now apply dredalg_snd.
+ do 2 constructor.
  apply dne_dnf_whne; [tea|].
  now eapply dredalg_whne.
+ transitivity (tSnd p); [symmetry|]; eapply TermSndCong; tea.
  eapply TermTrans; tea.
Qed.

Lemma NeTermDecl_tNatElim : forall Γ P P' hz hz' hs hs' t t',
  [Γ,, tNat |-[de] P ≅ P'] ->
  [Γ |-[de] hz ≅ hz' : P[tZero..]] ->
  [Γ |-[de] hs ≅ hs' : elimSuccHypTy P] ->
  [Γ |-[de] t ≅ t' : tNat] ->
  NfTypeDecl (Γ,, tNat) P' ->
  NfTermDecl Γ P[tZero..] hz' ->
  NfTermDecl Γ (elimSuccHypTy P) hs' ->
  NeTermDecl Γ tNat t' ->
  NeTermDecl Γ P[t..] (tNatElim P' hz' hs' t').
Proof.
intros * ? ? ? ? [P₀] [hz₀] [hs₀] [? [t₀]]; split; [now constructor|].
exists (tNatElim P₀ hz₀ hs₀ t₀).
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

Lemma NeTermDecl_tEmptyElim : forall Γ P P' t t',
  [Γ,, tEmpty |-[de] P ≅ P'] ->
  [Γ |-[de] t ≅ t' : tEmpty] ->
  NfTypeDecl (Γ,, tEmpty) P' ->
  NeTermDecl Γ tEmpty t' ->
  NeTermDecl Γ P[t..] (tEmptyElim P' t').
Proof.
intros * ? ? [P₀] [? [t₀]]; split; [now constructor|].
exists (tEmptyElim P₀ t₀).
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

Lemma NeTermDecl_tIdElim : forall Γ A A' x x' P P' hr hr' y y' t t',
  [Γ |-[de] A] ->
  [Γ |-[de] A ≅ A'] ->
  [Γ |-[de] x : A] ->
  [Γ |-[de] x ≅ x' : A] ->
  [Γ ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0) |-[de] P ≅ P'] ->
  [Γ |-[de] hr ≅ hr' : P[tRefl A x .: x..]] ->
  [Γ |-[de] y ≅ y' : A] ->
  [Γ |-[de] t ≅ t' : tId A x y] ->
  NfTypeDecl Γ A' ->
  NfTermDecl Γ A x' ->
  NfTypeDecl (Γ,, A ,, tId A⟨@wk1 Γ A⟩ x⟨@wk1 Γ A⟩ (tRel 0)) P' ->
  NfTermDecl Γ  P[tRefl A x .: x..] hr' ->
  NfTermDecl Γ A y' ->
  NeTermDecl Γ (tId A x y) t' ->
  NeTermDecl Γ P[t .: y..] (tIdElim A' x' P' hr' y' t').
Proof.
intros * ? ? ? ? ? ? ? ? [A₀] [x₀] [P₀] [hr₀] [y₀] [? [t₀]]; split; [now constructor|].
exists (tIdElim A₀ x₀ P₀ hr₀ y₀ t₀).
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
  - intros * []; split.
    + now econstructor.
    + destruct nfconvtm_nfl0 as [r]; exists r; tea; try now econstructor.
    + destruct nfconvtm_nfr0 as [r]; exists r; tea; try now econstructor.
  - intros; apply ConvTypeNf_PER.
  - intros; invnf; split.
    + now apply typing_wk.
    + now apply NfTypeDecl_wk.
    + now apply NfTypeDecl_wk.
  - intros; invnf; split.
    + eapply TypeTrans ; [eapply TypeTrans | ..].
      2: eassumption.
      2: eapply TypeSym.
      all: now eapply RedConvTyC.
    + destruct nfconvty_nfl0 as [r]; exists r; tea.
      * etransitivity; [|eassumption].
        apply dred_red, H.
      * eapply TypeTrans; [apply H|tea].
    + destruct nfconvty_nfr0 as [r]; exists r; tea.
      * etransitivity; [|eassumption].
        apply dred_red, H0.
      * eapply TypeTrans; [apply H0|tea].
  - intros; invnf; split.
    + now do 2 constructor.
    + now apply NfTypeDecl_tSort.
    + now apply NfTypeDecl_tSort.
  - intros; invnf; split.
    + constructor; tea.
    + eapply NfTypeDecl_tProd; tea.
      * now eapply lrefl.
      * now eapply lrefl.
    + eapply NfTypeDecl_tProd; tea.
      now eapply urefl.
  - intros; invnf; split.
    + constructor; match goal with H : _ |- _ => now apply H end.
    + eapply NfTypeDecl_tSig; tea.
      * now eapply lrefl.
      * now eapply lrefl.
    + eapply NfTypeDecl_tSig; tea.
      now eapply urefl.
  - intros; invnf; split.
    + constructor; now assumption.
    + apply NfTypeDecl_tId; tea.
    + apply NfTypeDecl_tId; tea.
      * now eapply NfTermConv.
      * now eapply NfTermConv.
  Qed.

  #[export, refine] Instance ConvTermDeclProperties : ConvTermProperties (ta := nf) := {}.
  Proof.
  + intros; split.
    - intros ? ? []; split; tea.
      now symmetry.
    - intros ? ? ? [] []; split; tea.
      now etransitivity.
  + intros; invnf; split.
    - now eapply TermConv.
    - now eapply NfTermConv.
    - now eapply NfTermConv.
  + intros; invnf; split.
    - now apply typing_wk.
    - now apply NfTermDecl_wk.
    - now apply NfTermDecl_wk.
  + intros; invnf; split.
    - now eapply convtm_exp.
    - eapply NfTermDecl_exp with (t' := t'); tea.
    - eapply NfTermDecl_exp with (t' := u'); tea.
  + intros; invnf; split.
    - now apply convtm_convneu.
    - now apply NeTermDecl_NfTermDecl.
    - now apply NeTermDecl_NfTermDecl.
  + intros; invnf; split.
    - now apply convtm_prod.
    - eapply NfTermDecl_tProd; tea.
      * now eapply lrefl.
      * now eapply lrefl.
    - eapply NfTermDecl_tProd; tea.
      now eapply urefl.
  + intros; invnf; split.
    - constructor; tea.
    - eapply NfTermDecl_tSig; tea.
      * now eapply lrefl.
      * now eapply lrefl.
    - eapply NfTermDecl_tSig; tea.
      * now eapply urefl.
  + intros * ? ? ? Hf ? Hg []; split.
    - apply convtm_eta; tea.
      * destruct Hf as [? ? ? []|? []]; now constructor.
      * destruct Hg as [? ? ? []|? []]; now constructor.
    - destruct Hf as [A₀ f₀ ? []|? Hf₀].
      * apply NfTermDecl_tLambda; tea.
      * apply Hf₀.
    - destruct Hg as [A₀ g₀ ? []|? Hg₀].
      * apply NfTermDecl_tLambda; tea.
      * apply Hg₀.
  + intros; split; tea.
    - do 2 constructor; tea.
    - now apply NfTermDecl_tNat.
    - now apply NfTermDecl_tNat.
  + intros; split.
    - now do 2 constructor.
    - now apply NfTermDecl_tZero.
    - now apply NfTermDecl_tZero.
  + intros; invnf; split.
    - constructor; tea.
    - now apply NfTermDecl_tSucc.
    - now apply NfTermDecl_tSucc.
  + intros * ? ? ? Hp ? Hp' [] []; split.
    - etransitivity; [|now eapply TermPairEta].
      etransitivity; [now symmetry; eapply TermPairEta|].
      constructor; tea; now apply TypeRefl.
    - destruct Hp as [A₀ B₀ a b|? Hp₀].
      * invnf.
        eapply NfTermDecl_tPair; tea.
        now eapply lrefl.
      * apply Hp₀.
    - destruct Hp' as [A₀ B₀ a b|? Hp₀].
      * invnf.
        eapply NfTermDecl_tPair; tea.
        now eapply lrefl.
      * apply Hp₀.
  + intros; invnf; split.
    - now do 2 constructor.
    - now apply NfTermDecl_tEmpty.
    - now apply NfTermDecl_tEmpty.
  + intros; invnf; split.
    - now constructor.
    - now apply NfTermDecl_tId.
    - apply NfTermDecl_tId; tea.
      all: eapply NfTermConv; tea; now constructor.
  + intros; invnf; split.
    - now constructor.
    - now apply NfTermDecl_Refl.
    - eapply NfTermConv; [symmetry; now constructor|apply NfTermDecl_Refl; tea].
      eapply NfTermConv; tea.
  Qed.

  #[export, refine] Instance TypingDeclProperties : TypingProperties (ta := nf) := {}.
  Proof.
  all: try apply DeclarativeTypingProperties.TypingDeclProperties.
  + intros * ? []; now econstructor.
  Qed.

  #[export, refine] Instance ConvNeuDeclProperties : ConvNeuProperties (ta := nf) := {}.
  Proof.
  + intros; split.
    - intros ? ? []; split; tea.
      now symmetry.
    - intros ? ? ? [] []; split; tea.
      now etransitivity.
  + intros; invnf; split.
    - now eapply convneu_conv.
    - now eapply NeTermConv.
    - now eapply NeTermConv.
  + intros; invnf; split.
    - now eapply convneu_wk.
    - now eapply NeTermDecl_wk.
    - now eapply NeTermDecl_wk.
  + intros; invnf; now eapply convneu_whne.
  + intros; invnf; split.
    - now apply convneu_var.
    - apply NeTermDecl_dne; tea; now constructor.
    - apply NeTermDecl_dne; tea; now constructor.
  + intros * [Hfg] []; split; tea.
    - now eapply convneu_app.
    - eapply NeTermDecl_tApp; tea.
      * eapply lrefl, Hfg.
      * eapply lrefl; tea.
    - eapply NeTermDecl_tApp; tea.
      apply Hfg.
  + intros; invnf; split.
    - now eapply convneu_natElim.
    - eapply NeTermDecl_tNatElim; tea; try now symmetry.
      * now eapply lrefl.
      * now eapply lrefl, convtm_convneu.
    - eapply NeTermDecl_tNatElim; tea.
      now eapply convtm_convneu.
  + intros; invnf; split.
    - now eapply convneu_emptyElim.
    - eapply NeTermDecl_tEmptyElim; tea.
      * now eapply lrefl.
      * now eapply lrefl, convtm_convneu.
    - eapply NeTermDecl_tEmptyElim; tea.
      now eapply convtm_convneu.
  + intros; invnf; split.
    - now eapply convneu_fst.
    - now eapply NeTermDecl_tFst.
    - now eapply NeTermDecl_tFst.
  + intros; invnf; split.
    - now eapply convneu_snd.
    - eapply NeTermDecl_tSnd; tea.
      eapply lrefl; tea; apply neconvtm_conv0.
    - eapply NeTermDecl_tSnd; tea.
      now apply neconvtm_conv0.
  + intros; invnf; split.
    - now eapply convneu_IdElim.
    - eapply NeTermDecl_tIdElim; tea.
      all: try now eapply lrefl.
      now eapply lrefl, convtm_convneu.
    - eapply NeTermDecl_tIdElim; tea.
      now eapply convtm_convneu.
  Qed.

  #[export, refine] Instance RedTypeDeclProperties : RedTypeProperties (ta := nf) := {}.
  Proof.
  all: try apply DeclarativeTypingProperties.RedTypeDeclProperties.
  Qed.

  #[export, refine] Instance RedTermDeclProperties : RedTermProperties (ta := nf) := {}.
  Proof.
  all: try apply DeclarativeTypingProperties.RedTermDeclProperties.
  + intros; invnf; now apply DeclarativeTypingProperties.RedTermDeclProperties.
  + intros; invnf; change (@red_tm nf) with (@red_tm de).
    now eapply redtm_conv.
  Qed.

  #[export] Instance DeclarativeTypingProperties : GenericTypingProperties nf _ _ _ _ _ _ _ _ _ _ := {}.

End DeepTypingProperties.
