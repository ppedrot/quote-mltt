(** * LogRel.AlgorithmicTypingProperties: properties of algorithmic typing. *)
From LogRel Require Import Syntax.All GenericTyping DeclarativeTyping AlgorithmicJudgments.
From LogRel.TypingProperties Require Import PropertiesDefinition DeclarativeProperties SubstConsequences TypeInjectivityConsequences NeutralConvProperties.
From LogRel.Algorithmic Require Import Bundled TypedConvProperties TypedConvInstances.

From LogRel Require Import Utils.

Section TypingWk.

  Context `{ta : tag} `{! ConvType ta}.
  Hypothesis conv_wk :
    forall Γ A B, [Γ |-[ta] A ≅ B] ->
    forall Δ (ρ : Δ ≤ Γ), [Δ |- A⟨ρ⟩ ≅ B⟨ρ⟩].

  Import AlgorithmicTypingData.

  Let PTy (Γ : context) (A : term) := forall Δ (ρ : Δ ≤ Γ), [Δ |-[ta] A⟨ρ⟩].
  Let PInf (Γ : context) (A t : term) := forall Δ (ρ : Δ ≤ Γ),
    [Δ |-[ta] t⟨ρ⟩ ▹ A⟨ρ⟩].
  Let PInfRed (Γ : context) (A t : term) := forall Δ (ρ : Δ ≤ Γ),
    [Δ |-[ta] t⟨ρ⟩ ▹h A⟨ρ⟩].
  Let PCheck (Γ : context) (A t : term) := forall Δ (ρ : Δ ≤ Γ),
  [Δ |-[ta] t⟨ρ⟩ ◃ A⟨ρ⟩].

  Theorem algo_typing_wk :
    AlgoTypingInductionConcl PTy PInf PInfRed PCheck.
  Proof.
    subst PTy PInf PInfRed PCheck.
    apply AlgoTypingInduction.
    - constructor.
    - intros * ? ? ? IHB **.
      cbn.
      econstructor.
      + now eauto.
      + now eapply IHB with(ρ := wk_up _ ρ).
    - intros.
      now econstructor.
    - now constructor.
    - intros * ? ? ? IHB **.
      rewrite <-wk_sig.
      econstructor.
      + now eauto.
      + now eapply IHB.
    - intros; rewrite <- wk_Id; econstructor; eauto.
    - constructor.
      + now intros ?%isCanonical_ren.
      + eauto. 
    - intros.
      eapply typing_meta_conv.
      + now econstructor ; eapply in_ctx_wk.
      + reflexivity.
    - intros * ? ? ? IHB.
      cbn.
      econstructor.
      + eauto.
      + now eapply IHB with(ρ := wk_up _ ρ).
    - intros * ? ? ? IHt ? ?.
      cbn.
      econstructor.
      + now eauto.
      + now eapply IHt with(ρ := wk_up _ ρ).
    - intros.
      cbn in *.
      eapply typing_meta_conv.
      + now econstructor.
      + now asimpl.
    - now econstructor.
    - now econstructor.
    - now econstructor.
    - intros * ? IHn ? IHP ? IHz ? IHs *.
      cbn in *.
      eapply typing_meta_conv.
      1: econstructor.
      + eauto.
      + eapply IHP with (ρ := wk_up _ ρ).
      + eapply typing_meta_conv.
        1: eapply IHz.
        now bsimpl.
      + eapply typing_meta_conv.
        1: eapply IHs.
        unfold elimSuccHypTy.
        now bsimpl.
      + now bsimpl.
    - intros.
      now econstructor.
    - intros * ? IHe ? IHP *.
      cbn in *.
      eapply typing_meta_conv.
      1: econstructor.
      + eauto.
      + eapply IHP with (ρ := wk_up _ ρ).
      + now bsimpl. 
    - intros * ??? IHB *.
      rewrite <- wk_sig.
      econstructor; eauto.
    - intros * ???????? *.
      rewrite <- wk_pair, <-wk_sig.
      econstructor.
      1-3: now eauto.
      rewrite <- subst_ren_wk_up; eauto.
    - intros * ?? *.
      rewrite <- wk_fst; now econstructor.
    - intros ? A ?? ? IH *.
      rewrite <- wk_snd, (subst_ren_wk_up (A:=A)).
      econstructor.
      now eapply IH.
    - intros; rewrite <- wk_Id; econstructor; eauto.
    - intros; rewrite <- wk_refl; econstructor; eauto.
    - intros; erewrite <- wk_idElim, subst_ren_wk_up2; econstructor; eauto.
      + rewrite 2!(wk_up_wk1 ρ); eauto.
      + rewrite wk_refl, <- subst_ren_wk_up2; eauto.
    - intros.
      econstructor.
      + eauto.
      + eauto using credalg_wk.
      + now eapply whnf_ren. 
    - intros.
      econstructor.
      + eauto.
      + now eapply conv_wk.
  Qed.

  Corollary algo_typing_shift : AlgoTypingInductionConcl
  (fun (Γ : context) (A : term) => forall T, [Γ,, T |-[ta] A⟨↑⟩])
  (fun (Γ : context) (A t : term) => forall T, [Γ,, T |-[ta] t⟨↑⟩ ▹ A⟨↑⟩])
  (fun (Γ : context) (A t : term) => forall T, [Γ,, T |-[ta] t⟨↑⟩ ▹h A⟨↑⟩])
  (fun (Γ : context) (A t : term) => forall T, [Γ,, T |-[ta] t⟨↑⟩ ◃ A⟨↑⟩]).
  Proof.
  red.
  repeat match goal with |- _ × _ => split end.
  all: intros Γ * Hty T.
  all: eapply algo_typing_wk in Hty.
  all: specialize (Hty _ (@wk1 Γ T)).
  all: repeat rewrite <- (extRen_term _ _ (@wk1_ren Γ T)) ; refold.
  all: now eapply Hty.
  Qed.

End TypingWk.


Section AlgoTypingDet.

Context `{ta : tag} `{! ConvType ta}.

Import AlgorithmicTypingData.

Theorem algo_typing_det :
  AlgoTypingInductionConcl
    (fun _ _ => True)
    (fun Γ A t => forall A', [Γ |-[ta] t ▹ A'] -> A' = A)
    (fun Γ A t => forall A', [Γ |-[ta] t ▹h A'] -> A' = A)
    (fun _ _ _ => True).
Proof.
  apply AlgoTypingInduction.
  all: try easy.
  - intros * ? ? Hinf.
    inversion Hinf ; subst ; clear Hinf.
    now eapply in_ctx_inj.
  - intros * ? IHA ? IHB ? Hconv.
    now inversion Hconv.
  - intros * ?? ? IHt ? Hconv.
    inversion Hconv ; subst ; clear Hconv ; refold.
    eapply IHt in H7 ; subst.
    now reflexivity.
  - intros * ? IHf ?? ? Hconv.
    inversion Hconv ; subst ; clear Hconv ; refold.
    eapply IHf in H6.
    congruence.
  - intros * Hconv.
    now inversion Hconv.
  - intros * Hconv.
    now inversion Hconv.
  - intros * ?? ? Hconv.
    now inversion Hconv.
  - intros * ? IH ?????? ? Hconv.
    now inversion Hconv.
  - intros * Hconv.
    now inversion Hconv.
  - intros * ? IH ?? ? Hconv.
    now inversion Hconv.
  - intros * ? IH ??? Hconv.
    now inversion Hconv.
  - intros * ????????? Hconv.
    now inversion Hconv.
  - intros * ? IH ? Hconv.
    inversion Hconv; subst; refold.
    apply IH in H3; try constructor.
    now inversion H3.
  - intros * ? IH ? Hconv.
    inversion Hconv; subst; refold.
    apply IH in H3; try constructor.
    now inversion H3.
  - intros * ?????? * Hconv; inversion Hconv; now subst.
  - intros * ???? * Hconv; now inversion Hconv.
  - intros * ???????????? * Hconv; now inversion Hconv.
  - intros * ? IH ?? ? Hconv.
    inversion Hconv ; subst ; clear Hconv ; refold.
    eapply IH in H2 ; subst.
    eapply whred_det ; tea.
Qed.

End AlgoTypingDet.


(** ** Small types are large types *)

(** In the generic instance we allow to turn any small type into a type,
while in the definition of algorithmic typing we only allow it when A is a non-canonical
type (in which case it has to be small).
So we need to show admissibility of the more general rule. *)

Section SmallLarge.
  Import DeclarativeTypingProperties AlgorithmicTypingData AlgorithmicTypedConvData BundledTypingData.
  Context `{!TypingSubst de} `{!TypeReductionComplete de} `{!TypeConstructorsInj de}.

  Lemma algo_typing_small_large Γ A :
    [Γ |-[bn] A : U] ->
    [Γ |-[bn] A].
  Proof.
    enough (BundledTypingInductionConcl
      (fun _ _ => True)
      (fun Γ A t => [Γ |-[de] A ≅ U] -> [Γ |-[al] t])
      (fun Γ A t => A = U -> [Γ |-[al] t])
      (fun _ _ _ => True)) as (?&?&H&?).
    {
      intros [].
      split ; tea.
      eapply H.
      2: reflexivity.
      do 2 (econstructor ; tea).
      now eapply redty_red, red_compl_univ_r.
      constructor.
    }
    eapply BundledTypingInduction.
    all: try solve [
      econstructor |
      intros; econstructor; [intros Hcan; inversion Hcan| econstructor;[now econstructor|now eapply redty_red, red_compl_univ_r|constructor]]|
      intros; match goal with H : [_ |- _ ≅ _] |- _ => unshelve eapply ty_conv_inj in H; try now econstructor; now cbn in H end ].

      intros * ? [IH []] **; subst.
      eapply IH.
      eapply subject_reduction_type ; tea.
      boundary.
  Qed.

End SmallLarge.

(** The shape of the inferred type is the same as that of any type *)

Section InferShape.
  Import DeclarativeTypingProperties AlgorithmicTypingData.
  Context `{ta : tag} `{! ConvType ta}.
  Context `{!TypingSubst de} `{!TypeConstructorsInj de}.

  Hypothesis conv_sound :
    forall Γ A A', [Γ |-[de] A] -> [Γ |-[de] A'] -> [Γ |-[ta] A ≅ A'] -> [Γ |-[de] A ≅ A'].

  Lemma infer_U Γ A T : [Γ |-[de] A : U] -> [Γ |-[ta] A ▹h T] -> T = U.
  Proof.
    intros Hde [Hal Hal']%dup.
    eapply algo_infer_unique in Hal ; tea.
    2: boundary.
    assert (isType T).
    {
      eapply type_isType.
      1: boundary.
      now inversion Hal'.
    }
    unshelve eapply ty_conv_inj in Hal ; tea.
    1: constructor.
    destruct H ; cbn in * ; try easy.
    now destruct s.
  Qed.

  Lemma infer_nat Γ A T : [Γ |-[de] A : tNat] -> [Γ |-[ta] A ▹h T] -> T = tNat.
  Proof.
    intros Hde [Hal Hal']%dup.
    eapply algo_infer_unique in Hal ; tea.
    2: boundary.
    assert (isType T).
    {
      eapply type_isType.
      1: boundary.
      now inversion Hal'.
    }
    unshelve eapply ty_conv_inj in Hal ; tea.
    1: constructor.
    now destruct H ; cbn in *.
  Qed.

  Lemma infer_empty Γ A T : [Γ |-[de] A : tEmpty] -> [Γ |-[ta] A ▹h T] -> T = tEmpty.
  Proof.
    intros Hde [Hal Hal']%dup.
    eapply algo_infer_unique in Hal ; tea.
    2: boundary.
    assert (isType T).
    {
      eapply type_isType.
      1: boundary.
      now inversion Hal'.
    }
    unshelve eapply ty_conv_inj in Hal ; tea.
    1: constructor.
    now destruct H ; cbn in *.
  Qed.

  Lemma infer_prod Γ A B f T : [Γ |-[de] f : tProd A B] -> [Γ |-[ta] f ▹h T] ->
    ∑ A' B', T = tProd A' B'.
  Proof.
    intros Hde [Hal Hal']%dup.
    eapply algo_infer_unique in Hal ; tea.
    2: boundary.
    assert (isType T).
    {
      eapply type_isType.
      1: boundary.
      now inversion Hal'.
    }
    unshelve eapply ty_conv_inj in Hal ; tea.
    1: constructor.
    destruct H ; cbn in * ; easy.
  Qed.

  Lemma infer_sig Γ A B f T : [Γ |-[de] f : tSig A B] -> [Γ |-[ta] f ▹h T] ->
    ∑ A' B', T = tSig A' B'.
  Proof.
    intros Hde [Hal Hal']%dup.
    eapply algo_infer_unique in Hal ; tea.
    2: boundary.
    assert (isType T).
    {
      eapply type_isType.
      1: boundary.
      now inversion Hal'.
    }
    unshelve eapply ty_conv_inj in Hal ; tea.
    1: constructor.
    destruct H ; cbn in * ; easy.
  Qed.

  Lemma infer_U_ty Γ A T : [Γ |-[de] A] -> [Γ |-[ta] A ▹h T] -> T = U.
  Proof.
    intros Hde Hal.
    inversion Hde ; subst ; refold.
    1-6: inversion Hal as [???? Hal'] ; subst ; refold.
    1-6: inversion Hal' ; subst ; refold.
    1-5: symmetry ; eapply red_whnf ; tea ; constructor.
    now eapply infer_U.
  Qed.

End InferShape.

Import BundledIntermediateData IntermediateTypingProperties.

(** ** Instance *)
(** Equipped with the equivalence of declarative and algorithmic conversion,
we easily derive our third instance. *)

Module AlgorithmicTypingProperties.
  Import AlgorithmicTypedConvData DeclarativeTypingProperties.
  Export BundledTypingData AlgorithmicConvProperties.

  #[local] Ltac intros_bn :=
    intros ;
    repeat match goal with | H : context [bn] |- _ => destruct H end ;
    econstructor ; try assumption.

  #[export, refine] Instance WfCtxAlgProperties
    `{!TypingSubst de} `{!TypeReductionComplete de} `{!TypeConstructorsInj de} :
    WfContextProperties (ta := bn) := {}.
  Proof.
    1-8: intros_bn.
    - now do 2 constructor.
    - constructor ; tea.
      now apply algo_typing_sound.
  Qed.

  #[export, refine] Instance WfTypeAlgProperties
    `{!TypingSubst de} `{!TypeReductionComplete de} `{!TypeConstructorsInj de} `{!ConvImplies de al}:
    WfTypeProperties (ta := bn) := {}.
  Proof.
    all: cycle -1.
    1: intros; now eapply algo_typing_small_large.
    1: intros_bn; eapply algo_typing_wk ; tea ; intros ; now eapply algo_conv_wk.
    1-3: intros_bn; now econstructor.
    intros_bn; econstructor; tea; econstructor ; tea; now eapply ty_conv_compl.
  Qed.

  #[export, refine] Instance TypingAlgProperties
    `{!TypingSubst de} `{!TypeReductionComplete de} `{!TypeConstructorsInj de} `{!ConvImplies de al}:
    TypingProperties (ta := bn) := {}.
  Proof.
    - intros_bn.
      + now eapply algo_typing_wk; tea ; intros ; now eapply algo_conv_wk.
      + gen_typing.
    - intros_bn.
      + now econstructor.
      + constructor.
        now eapply in_ctx_wf.
    - intros_bn.
      + do 2 econstructor ; tea.
        all: try constructor.
        all: now eapply (redty_red (ta := de)), red_compl_univ_r.
      + now do 2 econstructor.
    - intros_bn.
      + now econstructor.
      + econstructor ; tea.
        2: econstructor.
        all: boundary.
    - intros * [? ? ? (?&?&[])%red_compl_prod_r] [].
      esplit ; tea.
      + do 2 econstructor ; tea.
        1: now eapply (redty_red (ta := de)).
        1: constructor.
        eapply ty_conv_compl.
        now etransitivity.
      + eapply typing_subst1 ; tea.
        econstructor.
        now eapply inf_conv_decl.
    - intros_bn.
      1: now econstructor.
      now do 2 econstructor.
    - intros_bn.
      1: now econstructor.
      now do 2 econstructor.
    - intros_bn.
      + do 2 econstructor ; tea.
        2: now constructor.
        now eapply (redty_red (ta := de)), red_compl_nat_r.
      + now do 2 econstructor.
    - intros_bn.
      1: econstructor ; tea.
      + econstructor ; tea.
        2: now constructor.
        now eapply (redty_red (ta := de)), red_compl_nat_r.
      + econstructor ; tea.
        now eapply ty_conv_compl.
      + econstructor ; tea.
        now eapply ty_conv_compl.
      + econstructor.
        eapply typing_subst1.
        1: eauto using inf_conv_decl.
        now eapply algo_typing_sound.
    - intros_bn.
      1: econstructor.
      gen_typing.
    - intros_bn.
      1: econstructor ; tea.
      + econstructor ; tea.
        2: now constructor.
        now eapply (redty_red (ta := de)), red_compl_empty_r.
      + econstructor.
        eapply typing_subst1.
        1: eauto using inf_conv_decl.
        now eapply algo_typing_sound.
    - intros_bn.
      1: do 2 econstructor; tea ; try constructor.
      1,2: now eapply (redty_red (ta:=de)), red_compl_univ_r.
      gen_typing.
    - intros_bn.
      1: do 2 (econstructor; tea); now eapply ty_conv_compl.
      econstructor.
      2,3: eapply TypeRefl; refold.
      1,2: boundary.
      now eapply algo_typing_sound.
    - intros * [].
      pose proof bun_inf_conv_conv as [?[?[]]]%red_compl_sig_r .
      econstructor; tea.
      do 2 econstructor; tea.
      2: constructor.
      now eapply (redty_red (ta:=de)).
    - intros * [].
      pose proof bun_inf_conv_conv as [?[?[]]]%red_compl_sig_r .
      econstructor; tea.
      1: do 2 econstructor; tea; [now eapply (redty_red (ta:=de))|constructor].
      eapply typing_subst1; tea.
      eapply TermConv; refold ; [|now symmetry].
      econstructor. eapply TermRefl.
      now eapply inf_conv_decl.
    - intros_bn.
      + econstructor; tea.
        2,3: econstructor ; tea; now eapply ty_conv_compl.
        econstructor; tea; [now eapply red_compl_univ_r|constructor].
      + now do 2 econstructor.
    - intros * tyA tyx.
      pose proof tyA as ?%bn_alg_typing_sound.
      pose proof tyx as ?%bn_typing_sound.
      destruct tyA, tyx.
      do 3 (econstructor; tea); now eapply ty_conv_compl.
    - intros * tyA tyx tyP tyhr tyy tye.
      pose proof tyA as ?%bn_alg_typing_sound.
      pose proof tyx as ?%bn_typing_sound.
      pose proof tyP as ?%bn_alg_typing_sound.
      pose proof tyhr as ?%bn_typing_sound.
      pose proof tyy as ?%bn_typing_sound.
      pose proof tye as ?%bn_typing_sound.
      destruct tyA, tyx, tyP, tyhr, tyy, tye.
      econstructor; tea.
      + econstructor; tea; econstructor; tea.
        all: now eapply ty_conv_compl.
      + econstructor; eapply typing_subst2; tea.
        cbn; now rewrite 2!wk1_ren_on, 2!shift_one_eq.
    - intros_bn.
      1: eassumption.
      etransitivity ; tea.
      symmetry.
      eapply RedConvTyC, subject_reduction_type ; tea.
      now eapply algo_typing_sound.
    - intros_bn.
      1: eassumption.
      etransitivity ; tea.
      now eapply algo_conv_sound in bun_conv_ty.
  Qed.

  #[export, refine] Instance RedTermAlgProperties
    `{!TypingSubst de} `{!TypeReductionComplete de} `{!TypeConstructorsInj de} `{!ConvImplies de al}:
    RedTermProperties (ta := bn) := {}.
  Proof.
    - intros_bn.
      2: now apply credalg_wk.
      econstructor ; tea.
      1: now eapply algo_typing_wk; tea ; intros ; now eapply algo_conv_wk.
      now eapply typing_wk.
    - intros * [? []]; assumption.
    - now intros * [].
    - intros_bn.
      2: apply redalg_one_step; now constructor.
      econstructor ; tea.
      + econstructor.
        1: now do 2 econstructor.
        econstructor ; tea.
        now eapply ty_conv_compl.
      + eapply typing_subst1 ; tea.
        econstructor.
        now eapply inf_conv_decl.
    - intros * HP Hz Hs.
      assert [|-[de] Γ] by (destruct Hz ; boundary).
      split ; tea.
      + eapply ty_natElim ; tea.
        econstructor ; tea.
        1: econstructor.
        now do 2 econstructor.
      + apply redalg_one_step ; now constructor.
    - intros * HP Hz Hs [].
      assert [|-[de] Γ] by (destruct Hz ; boundary).
      split ; tea.
      + eapply ty_natElim ; tea.
        econstructor.
        * eassumption.
        * do 2 econstructor ; tea.
          2: now constructor.
          now eapply (redty_red (ta := de)), red_compl_nat_r.
        * now do 2 econstructor.
      + apply redalg_one_step; now constructor.
    - intros_bn.
      + eapply red_compl_prod_r in bun_inf_conv_conv0 as (?&?&[]).
        econstructor ; tea.
        1: econstructor.
        * econstructor ; tea.
          2: now constructor.
          now eapply (redty_red (ta := de)).
        * econstructor ; tea.
          eapply ty_conv_compl ; now etransitivity.
        * eapply typing_subst1 ; tea.
          econstructor.
          now eapply inf_conv_decl.
      + now apply redalg_app.
    - intros * [] [] [] [? []].
      assert [Γ |-[al] n ▹h tNat].
      {
        econstructor ; tea.
        2: now constructor.
        now eapply (redty_red (ta := de)), red_compl_nat_r.
      }
      split ; tea.
      1: econstructor ; tea.
      1: econstructor ; tea.
      + econstructor ; tea.
        now eapply ty_conv_compl.
      + econstructor ; tea.
        now eapply ty_conv_compl.
      + econstructor.
        eapply typing_subst1.
        all: eapply algo_typing_sound ; tea.
        2: now econstructor.
        econstructor ; tea.
        now eapply ty_conv_compl.
      + now apply redalg_natElim.
    - intros * [] [?[]].
      assert [Γ |-[al] n ▹h tEmpty].
      {
        econstructor ; tea.
        2: now constructor.
        now eapply (redty_red (ta := de)), red_compl_empty_r.
      }
      split ; tea.
      1: econstructor ; tea.
      1: econstructor ; tea.
      + econstructor.
        eapply typing_subst1.
        all: eapply algo_typing_sound ; tea.
        2: now econstructor.
        econstructor ; tea.
        now eapply ty_conv_compl.
      + now apply redalg_natEmpty.
    - intros_bn.
      2: econstructor; [|reflexivity]; now constructor.
      econstructor.
      1: tea.
      2: eapply TypeRefl; refold; now boundary.
      do 2 econstructor.
      1: do 2 (econstructor; tea); now eapply ty_conv_compl.
      2: now constructor.
      reflexivity.
    - intros * [? []].
      pose proof bun_inf_conv_conv as [?[?[]]]%red_compl_sig_r.
      econstructor; tea.
      2: now apply redalg_fst.
      econstructor; tea.
      do 2 econstructor; tea; [now eapply (redty_red (ta:=de))|now constructor].
    - intros_bn.
      2: econstructor; [|reflexivity]; now constructor.
      econstructor.
      1: tea.
      + do 2 econstructor.
        2: reflexivity.
        2: now constructor.
        do 2 (econstructor; tea); now eapply ty_conv_compl.
      + eapply TypeRefl; eapply typing_subst1.
        2: now eapply algo_typing_sound.
        do 2 econstructor.
        * boundary.
        * now eapply algo_typing_sound.
        * now eapply inf_conv_decl.
        * now eapply inf_conv_decl.
    - intros * [? []].
      pose proof bun_inf_conv_conv as [?[?[]]]%red_compl_sig_r.
      econstructor; tea.
      2: now apply redalg_snd.
      econstructor; tea.
      1: do 2 econstructor; tea; [now eapply (redty_red (ta:=de))|now constructor].
      eapply typing_subst1 ; tea.
      eapply TermRefl; eapply wfTermConv; refold; [|now symmetry].
      econstructor; now eapply inf_conv_decl.
    - intros * tyA tyx tyP tyhr tyy tyA' tyz convA convxy convxz.
      pose proof tyA as ?%bn_alg_typing_sound.
      pose proof tyx as ?%bn_typing_sound.
      pose proof tyP as ?%bn_alg_typing_sound.
      pose proof tyhr as ?%bn_typing_sound.
      pose proof tyy as ?%bn_typing_sound.
      pose proof convA as ?%bn_conv_sound.
      pose proof convxy as ?%bn_conv_sound.
      pose proof convxz as ?%bn_conv_sound.
      destruct tyA, tyx, tyP, tyhr, tyy, tyA', tyz, convA, convxy, convxz.
      econstructor; tea.
      2: eapply redalg_one_step; constructor.
      assert [Γ |-[ de ] tId A' z z ≅ tId A x y].
      1:{
        econstructor; symmetry; tea.
        1,2: econstructor; tea.
        etransitivity; tea; now symmetry.
      }
      econstructor; tea.
      + econstructor; tea; econstructor; tea.
        4: econstructor; tea; econstructor; tea.
        all: eapply ty_conv_compl; tea.
        now etransitivity.
      + econstructor; eapply typing_subst2; tea.
        cbn; rewrite 2!wk1_ren_on, 2!shift_one_eq.
        econstructor; [econstructor; tea|tea].
        now econstructor.
    - intros * tyA tyx tyP tyhr tyy [? tye].
      pose proof tyP as ?%bn_alg_typing_sound.
      pose proof tyy as ?%bn_typing_sound.
      pose proof tye as ?%bn_typing_sound.
      revert tyA tyx tyP tyhr tyy tye; intros_bn.
      2: now eapply redalg_idElim.
      econstructor; tea.
      + econstructor; tea; econstructor; tea.
        all: now eapply ty_conv_compl.
      + econstructor; eapply typing_subst2; tea.
        cbn; now rewrite 2!wk1_ren_on, 2!shift_one_eq.
    - intros_bn.
      eapply algo_conv_sound in bun_conv_ty ; tea.
      econstructor ; tea.
      now etransitivity.
    - intros_bn.
      all: now econstructor.
    - red. intros_bn.
      2: now etransitivity.
      now econstructor.
  Qed.

  #[export, refine] Instance RedTypeAlgProperties
    `{!TypingSubst de} `{!TypeReductionComplete de} `{!TypeConstructorsInj de} :
    RedTypeProperties (ta := bn) := {}.
  Proof.
    - intros_bn.
      1: now apply algo_typing_wk; tea ; intros ; now eapply algo_conv_wk.
      now apply credalg_wk.
    - intros * []; assumption.
    - now intros_bn.
    - intros * [?[]%algo_typing_small_large].
      now econstructor.
    - intros_bn.
      now econstructor.
    - red. intros_bn.
      now etransitivity.
  Qed.

  #[export] Instance AlgorithmicTypingProperties
    `{!TypingSubst de} `{!TypeReductionComplete de} `{!TypeConstructorsInj de} `{!ConvImplies de al}:
    GenericTypingProperties bn _ _ _ _ _ _ _ _ := {}.

End AlgorithmicTypingProperties.

(** ** Consequences *)

Import AlgorithmicTypingData AlgorithmicTypingProperties DeclarativeTypingProperties.

(** *** Uniqueness of types *)

Lemma type_uniqueness `{! TypingImplies de bn} Γ A A' t :
  [Γ |-[de] t : A] ->
  [Γ |-[de] t : A'] ->
  [Γ |-[de] A ≅ A'].
Proof.
  intros [?? Hinf]%tm_compl [?? Hinf']%tm_compl.
  eapply algo_typing_det in Hinf.
  2: eassumption.
  subst.
  etransitivity ; tea.
  now symmetry.
Qed.