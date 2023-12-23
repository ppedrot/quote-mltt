(** * LogRel.DeclarativeInstance: proof that declarative typing is an instance of generic typing. *)
From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Computation Notations Context Closed NormalForms NormalEq UntypedReduction Weakening GenericTyping DeclarativeTyping.

Import DeclarativeTypingData.

(** ** Stability by weakening *)

Lemma shift_up_ren {Γ Δ t} (ρ : Δ ≤ Γ) : t⟨ρ⟩⟨↑⟩ = t⟨↑ >> up_ren ρ⟩.
Proof. now asimpl. Qed.

Section TypingWk.
  
  Let PCon (Γ : context) := True.
  Let PTy (Γ : context) (A : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] -> [Δ |- A⟨ρ⟩].
  Let PTm (Γ : context) (A t : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] ->
    [Δ |- t⟨ρ⟩ : A⟨ρ⟩].
  Let PTyEq (Γ : context) (A B : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] ->
    [Δ |- A⟨ρ⟩ ≅ B⟨ρ⟩].
  Let PTmEq (Γ : context) (A t u : term) := forall Δ (ρ : Δ ≤ Γ), [|- Δ ] ->
    [Δ |- t⟨ρ⟩ ≅ u⟨ρ⟩ : A⟨ρ⟩].



  Theorem typing_wk : WfDeclInductionConcl PCon PTy PTm PTyEq PTmEq.
  Proof.
    subst PCon PTy PTm PTyEq PTmEq.
    apply WfDeclInduction.
    - trivial.
    - trivial.
    - intros ? ? IH.
      now econstructor.
    - intros Γ A B HA IHA HB IHB Δ ρ HΔ.
      econstructor ; fold ren_term.
      1: now eapply IHA.
      eapply IHB with (ρ := wk_up _ ρ).
      now constructor.
    - intros; now constructor.
    - intros; now constructor.
    - intros ?????? ih ** ; rewrite <- wk_sig.
      constructor; eauto.
      eapply ih; constructor; eauto.
    - intros * _ IHA _ IHx _ IHy **; rewrite <- wk_Id.
      constructor; eauto.
    - intros * _ IHA ? * ?.
      econstructor.
      now eapply IHA.
    - intros * _ IHΓ Hnth ? * ?.
      eapply typing_meta_conv.
      1: econstructor ; tea.
      1: eapply in_ctx_wk ; tea.
      reflexivity.
    - intros * _ IHA _ IHB ? ρ ?.
      cbn.
      econstructor.
      1: now eapply IHA.
      eapply IHB with (ρ := wk_up _ ρ).
      econstructor ; tea.
      econstructor.
      now eapply IHA.
    - intros * _ IHA _ IHt ? ρ ?.
      econstructor.
      1: now eapply IHA.
      eapply IHt with (ρ := wk_up _ ρ).
      econstructor ; tea.
      now eapply IHA.
    - intros * _ IHf _ IHu ? ρ ?.
      cbn.
      red in IHf.
      cbn in IHf.
      eapply typing_meta_conv.
      1: econstructor.
      1: now eapply IHf.
      1: now eapply IHu.
      now asimpl.
    - intros; now constructor.
    - intros; now constructor.
    - intros; cbn; econstructor; eauto.
    - intros * ? ihP ? ihhz ? ihhs ? ihn **; cbn.
      erewrite subst_ren_wk_up; eapply wfTermNatElim.
      * eapply ihP; econstructor; tea; now econstructor.
      * eapply typing_meta_conv.
        1: now eapply ihhz.
        now erewrite subst_ren_wk_up.
      * rewrite wk_elimSuccHypTy.
        now eapply ihhs.
      * now eapply ihn.
    - intros; now constructor.
    - intros * ? ihP ? ihe **; cbn.
      erewrite subst_ren_wk_up; eapply wfTermEmptyElim.
      * eapply ihP; econstructor; tea; now econstructor.
      * now eapply ihe.
    - intros ???? ih1 ? ih2 ** ; rewrite <- wk_sig; cbn.
      constructor.
      1: now eapply ih1.
      eapply ih2 ; constructor; eauto.
      now constructor.
    - intros ?????? ihA ? ihB ? iha ? ihb **.
      rewrite <- wk_sig; rewrite <- wk_pair.
      constructor; eauto.
      1: eapply ihB; constructor; eauto.
      rewrite <- subst_ren_wk_up. 
      now eapply ihb.
    - intros; cbn; econstructor; eauto.
    - intros ????? ih **.
      unshelve erewrite subst_ren_wk_up; tea.
      econstructor; now eapply ih.
    - intros * _ IHA _ IHx _ IHy **; rewrite <- wk_Id.
      constructor; eauto.
    - intros * _ IHA _ IHx **; rewrite <- wk_Id, <- wk_refl.
      constructor; eauto.
    - intros * _ IHA _ IHx _ IHP _ IHhr _ IHy _ IHe **.
      rewrite <- wk_idElim.
      erewrite subst_ren_wk_up2.
      assert [|- Δ ,, A⟨ρ⟩] by (constructor; tea; eauto).
      constructor; eauto.
      + rewrite 2!(wk_up_wk1 ρ).
        eapply IHP; constructor; tea.
        rewrite <- wk_Id; constructor.
        * rewrite <- wk_up_wk1, wk_step_wk1; eauto.
        * rewrite <- 2!wk_up_wk1, 2!wk_step_wk1; eauto.
        * rewrite <- wk_up_wk1, wk1_ren_on; cbn; constructor; tea; constructor.
      + rewrite wk_refl, <- subst_ren_wk_up2; eauto.
    - intros * _ IH **; cbn.
      econstructor.
      now apply IH.
    - intros; cbn; constructor; eauto.
      + now change (arr tNat tNat) with (arr tNat tNat)⟨ρ⟩.
      + rewrite <- run_ren with (ρ := ρ); now apply H4.
    - intros * **.
      unfold ren1, Ren1_well_wk; rewrite tTotal_ren.
      cbn in *; constructor; eauto.
      rewrite <- run_ren with (ρ := ρ); eauto.
    - intros * _ IHt _ IHAB ? ρ ?.
      econstructor.
      1: now eapply IHt.
      now eapply IHAB.
    - intros Γ A A' B B' _ IHA _ IHAA' _ IHBB' ? ρ ?.
      cbn.
      econstructor.
      + now eapply IHA.
      + now eapply IHAA'.
      + eapply IHBB' with (ρ := wk_up _ ρ).
        econstructor ; tea.
        now eapply IHA.
    - intros ?????????? ih **.
      do 2 rewrite <- wk_sig; constructor; eauto.
      eapply ih; constructor; eauto.
    - intros * _ IHA _ IHx _ IHy **.
      rewrite <- 2!wk_Id; constructor; eauto.
    - intros * _ IHA ? ρ ?.
      eapply TypeRefl.
      now eapply IHA.
    - intros * _ IH ? ρ ?.
      econstructor.
      now eapply IH.
    - intros * _ IH ? ρ ?.
      now econstructor ; eapply IH.
    - intros * _ IHA _ IHB ? ρ ?.
      eapply TypeTrans.
      + now eapply IHA.
      + now eapply IHB.
    - intros Γ u t A B _ IHA _ IHt _ IHu ? ρ ?.
      cbn.
      eapply convtm_meta_conv.
      1: econstructor.
      + now eapply IHA.
      + eapply IHt with (ρ := wk_up _ ρ).
        econstructor ; tea.
        now eapply IHA.
      + now eapply IHu.
      + now asimpl.
      + now asimpl. 
    - intros * H IH **; cbn.
      unfold ren1, Ren1_well_wk.
      rewrite quote_ren; eauto using wk_inj.
      constructor; [now apply IH|now apply dnf_ren|now apply closed0_ren].
    - intros * * He IHe **; cbn.
      constructor.
      now apply IHe.
    - intros * ? IHt ? IHrun ?? ? IHnil ? IHval **.
      cbn; unfold ren1, Ren1_well_wk.
      rewrite !qNat_ren.
      eapply TermStepRed.
      + now apply IHt.
      + now rewrite <- run_ren with (ρ := ρ); apply IHrun.
      + now apply dnf_ren.
      + now apply closed0_ren.
      + intros k' Hk.
        unshelve eassert (Hnil := IHnil k' Hk Δ ρ _); [tea|].
        rewrite <- qRun_ren; [|tea].
        apply Hnil.
      + cbn - [qRun] in IHval.
        unshelve eassert (Hval := IHval Δ ρ _); [tea|].
        rewrite <- qRun_ren; [|tea].
        rewrite !qNat_ren in Hval.
        apply Hval.
    - intros; cbn.
      constructor; eauto using dnf_ren, closed0_ren.
      + change (arr tNat tNat) with (arr tNat tNat)⟨ρ⟩; now eauto.
      + rewrite <- run_ren with (ρ := ρ); now apply H4.
    - intros * ? IHt ? IHrun ?? ? IHnil ? IHval **.
      cbn - [tTotal].
      unfold ren1, Ren1_well_wk.
      rewrite tTotal_ren, qEvalTm_ren, !qNat_ren.
      apply TermReflectRed.
      + now apply IHt.
      + now rewrite <- run_ren with (ρ := ρ); apply IHrun.
      + now apply dnf_ren.
      + now apply closed0_ren.
      + intros k' Hk.
        unshelve eassert (Hnil := IHnil k' Hk Δ ρ _); [tea|].
        rewrite <- qRun_ren; [|tea].
        apply Hnil.
      + cbn - [qRun] in IHval.
        unshelve eassert (Hval := IHval Δ ρ _); [tea|].
        rewrite <- qRun_ren; [|tea].
        rewrite !qNat_ren in Hval.
        apply Hval.
    - intros.
      unfold ren1, Ren1_well_wk.
      rewrite tTotal_ren; cbn in *; constructor; eauto using dnf_ren, closed0_ren.
      rewrite <- run_ren with (ρ := ρ); eauto.
    - intros Γ A A' B B' _ IHA _ IHAA' _ IHBB' ? ρ ?.
      cbn.
      econstructor.
      + now eapply IHA.
      + now eapply IHAA'.
      + eapply IHBB' with (ρ := wk_up _ ρ).
        pose (IHA _ ρ H).
        econstructor; tea; now econstructor.
    - intros Γ u u' f f' A B _ IHf _ IHu ? ρ ?.
      cbn.
      red in IHf.
      cbn in IHf.
      eapply convtm_meta_conv.
      1: econstructor.
      + now eapply IHf.
      + now eapply IHu.
      + now asimpl.
      + now asimpl.
    - intros * _ IHA _ IHA' _ IHA'' _ IHe ? ρ ?.
      cbn; econstructor; try easy.
      apply (IHe _ (wk_up _ ρ)).
      now constructor.
    - intros * _ IHf ? ρ ?.
      cbn.
      rewrite <- shift_upRen.
      now apply TermFunEta, IHf.
    - intros * ? ih **; cbn; constructor; now apply ih.
    - intros * ? ihP ? ihhz ? ihhs ? ihn **; cbn.
      erewrite subst_ren_wk_up.
      eapply TermNatElimCong.
      * eapply ihP; constructor; tea; now constructor.
      * eapply convtm_meta_conv.
        1: now eapply ihhz.
        2: reflexivity.
        now erewrite subst_ren_wk_up.
      * rewrite wk_elimSuccHypTy. 
        now eapply ihhs.
      * now eapply ihn.
    - intros * ? ihP ? ihhz ? ihhs **.
      erewrite subst_ren_wk_up.
      eapply TermNatElimZero; fold ren_term.
      * eapply ihP; constructor; tea; now constructor.
      * eapply typing_meta_conv.
        1: now eapply ihhz.
        now erewrite subst_ren_wk_up.
      * rewrite wk_elimSuccHypTy.
        now eapply ihhs.
    - intros * ? ihP ? ihhz ? ihhs ? ihn **.
      erewrite subst_ren_wk_up.
      eapply TermNatElimSucc; fold ren_term.
      * eapply ihP; constructor; tea; now constructor.
      * eapply typing_meta_conv.
        1: now eapply ihhz.
        now erewrite subst_ren_wk_up.
      * rewrite wk_elimSuccHypTy.
        now eapply ihhs.
      * now eapply ihn.
    - intros * ? ihP ? ihe **; cbn.
      erewrite subst_ren_wk_up.
      eapply TermEmptyElimCong.
      * eapply ihP; constructor; tea; now constructor.
      * now eapply ihe.
    - intros * ????? ih ** ; do 2 rewrite <- wk_sig.
      constructor; eauto.
      eapply ih; constructor; tea; constructor; eauto.
    - intros * ? ihA₀ ? ihA ? ihA' ? ihB ? ihB' ? iha ? ihb Δ ρ **.
      rewrite <- wk_sig, <- !wk_pair.
      assert [|-[de] Δ,, A⟨ρ⟩] by now constructor.
      constructor; eauto.
      rewrite <- subst_ren_wk_up; now apply ihb.
    - intros * ? ihp Δ ρ **.
      rewrite <- wk_sig, <- wk_pair.
      constructor; rewrite wk_sig; eauto.
    - intros * ? ih **. econstructor; now eapply ih.
    - intros * ??? ihB ** ; rewrite <- wk_fst; rewrite <- wk_pair; constructor; eauto.
      1: eapply ihB; constructor; eauto.
      rewrite <- subst_ren_wk_up; eauto.
    - intros * ? ih **.
      unshelve erewrite subst_ren_wk_up; tea; cbn.
      econstructor; now eapply ih.
    - intros * ??? ihB **. 
      rewrite <- wk_snd; rewrite <- wk_pair.
      unshelve erewrite subst_ren_wk_up.
      2:constructor; eauto.
      1: eapply ihB; constructor; eauto.
      rewrite <- subst_ren_wk_up; eauto.
    - intros * _ IHA _ IHx _ IHy **.
      rewrite <- 2! wk_Id; constructor; eauto.
    - intros * _ IHA _ IHx **.
      rewrite <- 2!wk_refl, <- wk_Id; constructor; eauto.
    - intros * _ IHA0 _ IHx0 _ IHA _ IHx _ IHP _ IHhr _ IHy _ IHe **.
      rewrite <- 2!wk_idElim; erewrite subst_ren_wk_up2.
      assert [|- Δ ,, A⟨ρ⟩] by (constructor; tea; eauto).
      constructor; eauto.
      + rewrite 2!(wk_up_wk1 ρ).
        eapply IHP; constructor; tea.
        rewrite <- wk_Id; constructor.
        * rewrite <- wk_up_wk1, wk_step_wk1; eauto.
        * rewrite <- 2!wk_up_wk1, 2!wk_step_wk1; eauto.
        * rewrite <- wk_up_wk1, wk1_ren_on; cbn; constructor; tea; constructor.
      + rewrite wk_refl, <- subst_ren_wk_up2; eauto.
    - intros * _ IHA _ IHx _ IHP _ IHhr _ IHy _ IHA' _ IHz _ IHAA' _ IHxy _ IHxz **.
      rewrite <- wk_idElim; erewrite subst_ren_wk_up2.
      assert [|- Δ ,, A⟨ρ⟩] by (constructor; tea; eauto).
      constructor; eauto.
      + rewrite 2!(wk_up_wk1 ρ).
        eapply IHP; constructor; tea.
        rewrite <- wk_Id; constructor.
        * rewrite <- wk_up_wk1, wk_step_wk1; eauto.
        * rewrite <- 2!wk_up_wk1, 2!wk_step_wk1; eauto.
        * rewrite <- wk_up_wk1, wk1_ren_on; cbn; constructor; tea; constructor.
      + rewrite wk_refl, <- subst_ren_wk_up2; eauto.
    - intros * _ IHt ? ρ ?.
      now econstructor.
    - intros * _ IHt _ IHA ? ρ ?.
      now econstructor.
    - intros * _ IHt ? ρ ?.
      now econstructor.
    - intros * _ IHt _ IHt' ? ρ ?.
      now econstructor.
  Qed.

End TypingWk.

(** ** A first set of boundary conditions *)

(** These lemmas assert that various boundary conditions, ie that if a certain typing-like relation
holds, some of its components are themselves well-formed. For instance, if [Γ |- t ⤳* u : A] then
[Γ |- t : A ]. The tactic boundary automates usage of these lemmas. *)

(** We cannot prove yet that all boundaries are well-typed: this needs stability of typing
by substitution and injectivity of type constructors, which we get from the logical relation.*)

Section Boundaries.
  Import DeclarativeTypingData.

  Section TypingBoundaries.

    Let PCon (Γ : context) := True.
    Let PTy (Γ : context) (A : term) := [|- Γ].
    Let PTm (Γ : context) (A t : term) := [|- Γ].
    Let PTyEq (Γ : context) (A B : term) := [|- Γ].
    Let PTmEq (Γ : context) (A t u : term) := [|- Γ].

    Theorem typing_boundary : WfDeclInductionConcl PCon PTy PTm PTyEq PTmEq.
    Proof.
      subst PCon PTy PTm PTyEq PTmEq.
      apply WfDeclInduction; eauto.
    Qed.

  End TypingBoundaries.

  Definition boundary_ctx_ctx {Γ A} : [|- Γ,, A] -> [|- Γ].
  Proof.
    now inversion 1.
  Qed.

  Definition boundary_ctx_tip {Γ A} : [|- Γ,, A] -> [Γ |- A].
  Proof.
    now inversion 1.
  Qed.

  Definition boundary_tm_ctx {Γ} {t A} :
      [ Γ |- t : A ] -> 
      [ |- Γ ].
  Proof.
    apply typing_boundary.
  Qed.

  Definition boundary_ty_ctx {Γ} {A} :
      [ Γ |- A ] -> 
      [ |- Γ ].
  Proof.
    induction 1; now eauto using boundary_tm_ctx.
  Qed.

  Definition boundary_tm_conv_ctx {Γ} {t u A} :
      [ Γ |- t ≅ u : A ] -> 
      [ |- Γ ].
  Proof.
      induction 1 ; now eauto using boundary_tm_ctx, boundary_ty_ctx.
  Qed.

  Definition boundary_ty_conv_ctx {Γ} {A B} :
      [ Γ |- A ≅ B ] -> 
      [ |- Γ ].
  Proof.
    induction 1 ; now eauto using boundary_ty_ctx, boundary_tm_conv_ctx.
  Qed.


  Definition boundary_red_l {Γ t u K} : 
    [ Γ |- t ⤳* u ∈ K] ->
    match K with istype => [ Γ |- t ] | isterm A => [ Γ |- t : A ] end.
  Proof.
    destruct 1; assumption.
  Qed.

  Definition boundary_red_tm_l {Γ t u A} : 
    [ Γ |- t ⤳* u : A] ->
    [ Γ |- t : A ].
  Proof.
    apply @boundary_red_l with (K := isterm A).
  Qed.

  Definition boundary_red_ty_l {Γ A B} : 
    [ Γ |- A ⤳* B ] ->
    [ Γ |- A ].
  Proof.
    apply @boundary_red_l with (K := istype).
  Qed.

End Boundaries.

#[export] Hint Resolve
  boundary_ctx_ctx boundary_ctx_tip boundary_tm_ctx
  boundary_ty_ctx boundary_tm_conv_ctx boundary_ty_conv_ctx
  boundary_red_tm_l
  boundary_red_ty_l : boundary.

(** ** Inclusion of the various reductions in conversion *)

Definition RedConvC {Γ} {t u : term} {K} :
    [Γ |- t ⤳* u ∈ K] -> 
    match K with istype => [Γ |- t ≅ u] | isterm A => [Γ |- t ≅ u : A] end.
Proof.
apply reddecl_conv.
Qed.

Definition RedConvTeC {Γ} {t u A : term} :
    [Γ |- t ⤳* u : A] -> 
    [Γ |- t ≅ u : A].
Proof.
apply @RedConvC with (K := isterm A).
Qed.

Definition RedConvTyC {Γ} {A B : term} :
    [Γ |- A ⤳* B] -> 
    [Γ |- A ≅ B].
Proof.
apply @RedConvC with (K := istype).
Qed.

(** Some derived rules *)

Lemma simple_TermApp : forall Γ A B t u,
  [Γ |- t : arr A B] -> [Γ |- u : A] -> [Γ |- tApp t u : B].
Proof.
intros.
replace B with B⟨↑⟩[u..] by now bsimpl.
eapply wfTermApp; tea.
Qed.

Lemma simple_TermAppCong : forall Γ A B t t' u u',
  [Γ |- t ≅ t' : arr A B] -> [Γ |- u ≅ u' : A] -> [Γ |- tApp t u ≅ tApp t' u' : B].
Proof.
intros.
replace B with B⟨↑⟩[u..] by now bsimpl.
eapply TermAppCong; tea.
Qed.

Lemma simple_TermLambdaCong : forall Γ A B t t',
  [Γ |- A] ->
  [Γ,, A |- t ≅ t' : B⟨↑⟩] -> [Γ |- tLambda A t ≅ tLambda A t' : arr A B].
Proof.
intros; eapply TermLambdaCong; tea; now apply TypeRefl.
Qed.

Lemma wfTermAnd : forall Γ A B,
  [Γ |- A : U] -> [Γ |- B : U] -> [Γ |- tAnd A B : U].
Proof.
intros.
apply wfTermSig; [tea|].
rewrite <- (@wk1_ren_on Γ A).
change U with U⟨@wk1 Γ A⟩.
apply typing_wk; [tea|].
constructor; [|now constructor].
now eapply boundary_tm_ctx.
Qed.

#[local] Ltac auto_type :=
  try match goal with
  | |- [|-[de] _] => do 2 red
  | |- [_ |-[de] _] => do 2 red
  | |- [_ |-[de] _ : _] => do 2 red
  end; eauto using WfContextDecl, TypingDecl, WfTypeDecl.

Lemma tEval_decl_cong : forall Γ t t' k k' v v',
  [Γ |- t ≅ t' : arr tNat tNat] ->
  [Γ |- k ≅ k' : tNat] ->
  [Γ |- v ≅ v' : tNat] ->
  [Γ |- tEval t k v ≅ tEval t' k' v' : U].
Proof.
intros.
assert [|- Γ] by now eapply boundary_tm_conv_ctx.
assert [|- Γ,, tNat] by (constructor; [tea|now constructor]).
assert [Γ,, tNat |- tNat] by now constructor.
assert [Γ |- arr tNat tNat].
{ apply wfTypeProd; tea. now constructor. }
eapply simple_TermAppCong; tea.
change (arr (arr tNat tNat) U) with (arr (arr tNat tNat) U)[k..].
eapply TermNatElimCong.
+ eapply TypeRefl.
  apply wfTypeProd; [apply wfTypeProd|]; tea.
  - do 2 constructor; [tea|now constructor].
  - do 2 constructor; [tea|apply wfTypeProd]; cbn; auto_type.
+ change (arr (arr tNat tNat) U)[tZero..] with (arr (arr tNat tNat) U).
  apply simple_TermLambdaCong; tea.
  apply TermIdCong.
  - apply TermRefl; auto_type.
  - apply TermRefl.
    change tNat with tNat[tZero..].
    eapply wfTermApp; [|auto_type].
    apply wfVar; [|constructor].
    auto_type.
  - apply TermSuccCong.
    repeat rewrite <- (@wk1_ren_on Γ tPNat).
    change tNat with tNat⟨@wk1 Γ tPNat⟩.
    eapply typing_wk; [tea|].
    auto_type.
+ apply TermRefl.
  change (elimSuccHypTy (arr (arr tNat tNat) U)) with (arr tNat (arr (arr (arr tNat tNat) U) (arr (arr tNat tNat) U))).
  apply wfTermLam; [auto_type|cbn].
  apply wfTermLam; [eauto 10 using WfContextDecl, TypingDecl, WfTypeDecl|].
  apply wfTermLam; [repeat constructor; tea|].
  match goal with |- TypingDecl ?Γ _ _ => assert [|- Γ] end.
  { repeat constructor; tea. }
  apply wfTermAnd.
  - apply wfTermId; auto_type.
    eapply simple_TermApp with tNat; first [apply wfVar|apply wfTermZero]; tea.
    constructor.
  - change U with U[(tShift (tRel 0))..]; eapply (wfTermApp (A := tPNat)).
    * apply wfVar; [auto_type|].
      change (tProd tPNat U) with (tProd tPNat U)⟨↑⟩⟨↑⟩ at 1.
      do 2 constructor.
    * apply wfTermLam; [auto_type|].
      match goal with |- TypingDecl ?Γ _ _ => assert [|- Γ] by auto_type end.
      apply simple_TermApp with tNat; [|constructor]; apply wfVar; tea.
      { change (arr tNat tNat⟨↑⟩) with (arr tNat tNat)⟨↑⟩⟨↑⟩; do 2 constructor. }
      { change tNat with tNat⟨↑⟩ at 7; constructor. }
+ tea.
Qed.

Lemma tTotal_decl_cong : forall Γ t t' u u',
  [Γ |- run : arr tNat (arr tNat (arr tNat tNat))] ->
  [Γ |- t ≅ t' : arr tNat tNat] ->
  [Γ |- u ≅ u' : tNat] ->
  [Γ |- tTotal t u ≅ tTotal t' u' : U].
Proof.
intros.
assert [|- Γ] by now eapply boundary_tm_conv_ctx.
assert [|- Γ,, tNat] by (constructor; [tea|now constructor]).
apply tEval_decl_cong.
- eapply simple_TermAppCong with tNat; tea.
  eapply simple_TermAppCong with tNat.
  * now apply TermRefl.
  * now apply TermQuoteCong.
- apply TermStepCong; tea.
- cbn; now eapply simple_TermAppCong with tNat.
Qed.

(** ** Weakenings of reduction *)

Lemma redtmdecl_wk {Γ Δ t u A} (ρ : Δ ≤ Γ) :
  [|- Δ ] -> [Γ |- t ⤳* u : A] -> [Δ |- t⟨ρ⟩ ⤳* u⟨ρ⟩ : A⟨ρ⟩].
Proof.
  intros * ? []; split.
  - now apply typing_wk.
  - apply credalg_wk; now eauto using wk_inj.
  - now apply typing_wk.
Qed.

Lemma redtydecl_wk {Γ Δ A B} (ρ : Δ ≤ Γ) :
  [|- Δ ] -> [Γ |- A ⤳* B] -> [Δ |- A⟨ρ⟩ ⤳* B⟨ρ⟩].
Proof.
  intros * ? []; split.
  - now apply typing_wk.
  - apply credalg_wk; now eauto using wk_inj.
  - now apply typing_wk.
Qed.

(** ** Derived rules for multi-step reduction *)

Lemma redtmdecl_app Γ A B f f' t :
  [ Γ |- f ⤳* f' : tProd A B ] ->
  [ Γ |- t : A ] ->
  [ Γ |- tApp f t ⤳* tApp f' t : B[t..] ].
Proof.
  intros [] ?; split.
  + now econstructor.
  + now apply redalg_app.
  + econstructor; [tea|now apply TermRefl].
Qed.

Lemma redtmdecl_conv Γ t u A A' : 
  [Γ |- t ⤳* u : A] ->
  [Γ |- A ≅ A'] ->
  [Γ |- t ⤳* u : A'].
Proof.
  intros [] ?; split.
  + now econstructor.
  + assumption.
  + now econstructor.
Qed.

Lemma redtydecl_term Γ A B :
  [ Γ |- A ⤳* B : U] -> [Γ |- A ⤳* B ].
Proof.
  intros []; split.
  + now constructor.
  + assumption.
  + now constructor.
Qed.

#[export] Instance RedTermTrans Γ A : Transitive (red_tm Γ A).
Proof.
  intros t u r [] []; split.
  + assumption.
  + now etransitivity.
  + now eapply TermTrans.
Qed.

#[export] Instance RedTypeTrans Γ : Transitive (red_ty Γ).
Proof.
  intros t u r [] []; split.
  + assumption.
  + now etransitivity.
  + now eapply TypeTrans.
Qed.

(** ** Bundling the properties together in an instance *)

Module DeclarativeTypingProperties.
  Export DeclarativeTypingData.

  #[export, refine] Instance WfCtxDeclProperties : WfContextProperties (ta := de) := {}.
  Proof.
    1-2: now constructor.
    all: boundary. 
  Qed.

  #[export, refine] Instance WfTypeDeclProperties : WfTypeProperties (ta := de) := {}.
  Proof.
    all: try now econstructor.
    - intros.
      now eapply typing_wk.
  Qed.

  #[export, refine] Instance TypingDeclProperties : TypingProperties (ta := de) := {}.
  Proof.
    all: try (intros; now econstructor).
    - intros.
      now eapply typing_wk.
    - intros.
      eapply wfTermConv; [constructor; tea|].
      + eapply TermTrans; [|eapply TermSym]; tea.
      + eapply TermTrans; [|eapply TermSym]; tea.
      + now apply convUniv, tTotal_decl_cong.
    - intros.
      econstructor ; tea.
      now apply TypeSym, RedConvTyC.
  Qed.

  #[export, refine] Instance ConvTypeDeclProperties : ConvTypeProperties (ta := de) := {}.
  Proof.
  - now econstructor.
  - intros.
    constructor ; red ; intros.
    all: now econstructor.
  - intros.
    now apply typing_wk.
  - intros.
    eapply TypeTrans ; [eapply TypeTrans | ..].
    2: eassumption.
    2: eapply TypeSym.
    all: now eapply RedConvTyC.
  - econstructor.
    now econstructor.
  - now econstructor.
  - now econstructor.
  - now econstructor.
  Qed.

  #[export, refine] Instance ConvTermDeclProperties : ConvTermProperties (ta := de) := {}.
  Proof.
  - intros.
    constructor ; red ; intros.
    all: now econstructor.
  - intros.
    now econstructor.
  - intros.
    now eapply typing_wk.
  - intros.
    econstructor; [|tea].
    eapply TermTrans ; [eapply TermTrans |..].
    2: eassumption.
    2: eapply TermSym.
    all: now eapply RedConvTeC.
  - intros ???? H; apply H.
  - intros.
    now econstructor.
  - intros.
    now econstructor.
  - intros.
    constructor; tea; now eapply TypeRefl.
  - intros.
    eapply TermTrans; [|now eapply TermFunEta].
    eapply TermTrans; [now eapply TermSym, TermFunEta|].
    constructor; tea.
    all: now econstructor.
  - now do 2 econstructor.
  - now do 2 econstructor.
  - now econstructor.
  - intros.
    eapply TermTrans; [|now constructor].
    eapply TermTrans; [eapply TermSym; now constructor|].
    constructor; tea; now apply TypeRefl.
  - now do 2 econstructor.
  - now econstructor.
  - now econstructor.
  Qed.

  #[export, refine] Instance ConvNeuDeclProperties : ConvNeuProperties (ta := de) := {}.
  Proof.
  - split; red.
    + intros ?? []; split; tea; now econstructor.
    + intros ??? [] []; split; tea; now econstructor.
  - intros ????? [] ?; split; tea; now econstructor.
  - intros ??????? []; split.
    + now eapply whne_ren.
    + now eapply whne_ren.
    + now eapply typing_wk.
  - now intros ???? [].
  - intros ???; split; now econstructor.
  - intros ??????? [] ?; split; now econstructor.
  - intros ???????????? []; split; now econstructor.
  - intros ?????? []; split; now econstructor.
  - intros ????? []; split; now econstructor.
  - intros ????? []; split; now econstructor.
  - intros * ??????? []; split; now econstructor.
  - intros; econstructor; now econstructor.
  - intros; econstructor; eauto using whne.
    eapply TermConv; [now constructor|].
    assert [|- Γ] by gen_typing.
    now eapply convUniv, convtm_nat.
  - intros; econstructor; eauto using whne.
    eapply TermConv; [now constructor|].
    assert [|- Γ] by gen_typing.
    eapply convUniv, tTotal_decl_cong; [tea|tea|now symmetry].
  Qed.

  #[export, refine] Instance RedTermDeclProperties : RedTermProperties (ta := de) := {}.
  Proof.
  - intros.
    now eapply redtmdecl_wk.
  - intros; now eapply redtmdecl_red.
  - intros. now eapply boundary_red_tm_l.
  - intros; split.
    + repeat (econstructor; tea).
    + eapply redalg_one_step; constructor.
    + now constructor.
  - intros; split.
    + repeat (econstructor; tea).
      now eapply boundary_tm_ctx.
    + eapply redalg_one_step; constructor.
    + now constructor.
  - intros; split.
    + repeat (econstructor; tea).
    + eapply redalg_one_step; constructor.
    + now constructor.
  - intros; now eapply redtmdecl_app.
  - intros * ??? []; split.
    + repeat (constructor; tea).
    + now eapply redalg_natElim.
    + constructor; first [eassumption|now apply TermRefl|now apply TypeRefl].
  - intros * ? []; split.
    + repeat (constructor; tea).
    + now eapply redalg_natEmpty.
    + constructor; first [eassumption|now apply TermRefl|now apply TypeRefl].
  - intros; split; refold.
    + econstructor; now constructor.
    + eapply redalg_one_step; constructor.
    + now constructor.
  - intros * [? r ?]; split; refold.
    + now econstructor.
    + now apply redalg_fst.
    + now econstructor.
  - intros; split; refold.
    + econstructor; now constructor.
    + eapply redalg_one_step; constructor.
    + now constructor.
  - intros * [? r ?]; split; refold.
    + now econstructor.
    + now apply redalg_snd.
    + now econstructor.
  - intros **; split; refold.
    + econstructor; tea.
      econstructor. 
      1: econstructor; tea; now econstructor.
      econstructor.
      1: now econstructor.
      1,2: econstructor; tea.
      1: now econstructor.
      eapply TermTrans; tea; now econstructor.
    + eapply redalg_one_step; constructor.
    + now econstructor.
  - intros * ????? []; split; refold.
    + now econstructor.
    + now eapply redalg_idElim.
    + econstructor; tea; now (eapply TypeRefl + eapply TermRefl).
  - intros; split.
    + now constructor.
    + econstructor; [|reflexivity].
      now constructor.
    + now constructor.
  - intros; split.
    + econstructor; now eapply lrefl.
    + now apply redalg_quote.
    + now constructor.
  - intros.
    assert [|- Γ] by gen_typing.
    split.
    + constructor; eauto using convtm_qNat.
    + apply redalg_one_step.
      match goal with H : EvalStep _ _ _ _ _ |- _ => destruct H as [[]] end.
      econstructor; tea.
    + match goal with H : EvalStep _ _ _ _ _ |- _ => destruct H end.
      eapply TermStepRed; tea.
  - intros; split.
    + constructor; [now eapply lrefl|now eapply lrefl|tea].
    + apply redalg_step; tea.
    + constructor; tea.
  - intros.
    assert [|- Γ] by gen_typing.
    assert [Γ |- tTotal t (qNat u) ≅ tTotal t₀ (qNat u)].
    { eapply convUniv, tTotal_decl_cong; tea.
      now apply convtm_qNat. }
    split. 
    + eapply wfTermConv; [apply wfTermReflect|now eapply TypeSym]; eauto.
      * eapply TermTrans; [eapply TermSym|]; tea.
      * now apply convtm_qNat.
    + apply redalg_one_step.
      match goal with H : EvalStep _ _ _ _ _ |- _ => destruct H as [[]] end.
      econstructor; tea.
    + match goal with H : EvalStep _ _ _ _ _ |- _ => destruct H end.
      eapply TermConv; [eapply TermReflectRed; tea|].
      * eapply TermTrans; [eapply TermSym|]; tea.
      * now apply TypeSym.
  - intros; split.
    + constructor; [now eapply lrefl|now eapply lrefl|tea].
    + apply redalg_reflect; tea.
    + constructor; tea.
  - intros; now eapply redtmdecl_conv.
  - intros; split.
    + assumption.
    + reflexivity.
    + now econstructor.
  Qed.

  #[export, refine] Instance RedTypeDeclProperties : RedTypeProperties (ta := de) := {}.
  Proof.
  - intros.
    now eapply redtydecl_wk.
  - intros; now eapply redtydecl_red.
  - intros. now eapply boundary_red_ty_l.
  - intros.
    now eapply redtydecl_term.
  - intros; split.
    + assumption.
    + reflexivity.
    + now constructor.
  Qed.

  #[export] Instance DeclarativeTypingProperties : GenericTypingProperties de _ _ _ _ _ _ _ _ _ _ := {}.

End DeclarativeTypingProperties.
