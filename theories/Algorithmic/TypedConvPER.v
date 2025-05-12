(** * LogRel.TypedConvPER: algorithmic conversion is symmetric and transitive. *)
From LogRel Require Import Utils Sections Syntax.All GenericTyping DeclarativeTyping AlgorithmicJudgments.
From LogRel.TypingProperties Require Import DeclarativeProperties PropertiesDefinition SubstConsequences TypeInjectivityConsequences NeutralConvProperties NormalisationDefinition.
From LogRel.Algorithmic Require Import Bundled TypedConvProperties.

Import DeclarativeTypingProperties AlgorithmicTypedConvData BundledTypingData.

(** ** Symmetry *)

Section Symmetry.
  Context `{!TypingSubst de} `{!TypeReductionComplete de} `{!TypeConstructorsInj de}.

  Let PTyEq (Γ : context) (A B : term) := forall Δ,
    [|-[de] Γ ≅ Δ] ->
    [Δ |-[al] B ≅ A].
  Let PTyRedEq (Γ : context) (A B : term) := forall Δ,
    [|-[de] Γ ≅ Δ] ->
    [Δ |-[al] B ≅h A].
  Let PNeEq (Γ : context) (A t u : term) := forall Δ,
    [|-[de] Γ ≅ Δ] ->
    ∑ A', [Δ |-[al] u ~ t ▹ A'] × [Δ |-[de] A ≅ A'].
  Let PNeRedEq (Γ : context) (A t u : term) := forall Δ,
    [|-[de] Γ ≅ Δ] ->
    ∑ A', [Δ |-[al] u ~h t ▹ A'] × [Δ |-[de] A ≅ A'].
  Let PTmEq (Γ : context) (A t u : term) := forall Δ,
    [|-[de] Γ ≅ Δ] ->
    [Δ |-[al] u ≅ t : A].
  Let PTmRedEq (Γ : context) (A t u : term) := forall Δ,
    [|-[de] Γ ≅ Δ] ->
    [Δ |-[al] u ≅h t : A].

  Theorem algo_conv_sym :
  BundledConvInductionConcl PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
  Proof.
    subst PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
    apply BundledConvInduction.
    - intros.
      econstructor.
      all: intuition eauto.
    - intros * ? IHA ? IHB  **.
      econstructor.
      1: now intuition eauto.
      eapply IHB.
      econstructor ; tea.
      eapply IHA.
    - now econstructor.
    - intros.
      now econstructor.
    - intros.
      now econstructor.
    - intros * ? ihA ? ihB **.
      econstructor.
      1: now eapply ihA.
      eapply ihB.
      econstructor; tea.
      now eapply ihA.
    - intros * ? ihA ? [ihx] ? [ihy] [[]%id_ty_inv []%id_ty_inv] * ?.
      econstructor.
      + now eapply ihA.
      + eapply algo_conv_conv.
        * eapply ihx; tea.
        * now eapply conv_ctx_refl_r.
        * pose proof H as ?%algo_conv_sound;try boundary.
          now eapply stability.
        * eapply stability; [| now symmetry].
          eapply wfTermConv; refold; tea.
          now symmetry.
        * now eapply stability.
      + eapply algo_conv_conv.
        * eapply ihy; tea.
        * now eapply conv_ctx_refl_r.
        * pose proof H as ?%algo_conv_sound;try boundary.
          now eapply stability.
        * eapply stability; [| now symmetry].
          eapply wfTermConv; refold; tea.
          now symmetry.
        * now eapply stability.
    - intros * ?? ? IHM  **.
      edestruct IHM as [[U' [IHM' HconvM]] ?] ; tea.
      now econstructor.
    - intros * HΓ **.
      eapply in_ctx_conv_l in HΓ as [? []] ; tea.
      eexists ; split.
      1: now econstructor.
      now eapply stability.
    - intros * ? IHm ? [IHt Hwft]  **.
      edestruct IHm as [[? [IHm' (?&?&[->])%conv_prod_l]] ?] ; tea ; clear IHm.
      2:{
        eapply type_isType.
        1: boundary.
        now eapply algo_conv_wh in IHm' as [].
      }
      eexists ; split.
      + econstructor.
        1: eassumption.
        eapply algo_conv_conv.
        * now eapply IHt.
        * now eapply conv_ctx_refl_r.
        * now symmetry.
        * eapply stability.
          2: now symmetry.
          boundary.
        * eapply stability.
          2: now symmetry.
          boundary.
      + eapply typing_subst1 ; tea.
        econstructor.
        2: now symmetry.
        eapply stability ; tea.
        now symmetry.
    - intros * ? IHn ? IHP ? IHz ? IHs **.
      edestruct IHn as [[? [IHn' ->%conv_nat_l]] ?] ; tea ; clear IHn.
      2:{
        eapply type_isType.
        1: boundary.
        now eapply algo_conv_wh in IHn' as [].
      }
      eexists ; split.
      1: econstructor ; tea.
      + eapply IHP.
        econstructor ; tea.
        econstructor.
        boundary.
      + eapply algo_conv_conv.
        * now eapply IHz.
        * now eapply conv_ctx_refl_r.
        * eapply stability.
          2: now symmetry.
          eapply typing_subst1.
          2: eapply IHP.
          do 2 econstructor.
          boundary.
        * eapply stability.
          2: now symmetry.
          destruct IHz.
          now boundary.
        * eapply stability.
          2: now symmetry.
          destruct IHz.
          now boundary.
      + eapply algo_conv_conv.
        * now eapply IHs.
        * now eapply conv_ctx_refl_r.
        * eapply stability.
          2: now symmetry.
          destruct IHP.
          eapply elimSuccHypTy_conv ; tea.
          all: now boundary.
        * eapply stability.
          2: now symmetry.
          destruct IHs.
          boundary.
        * eapply stability.
          2: now symmetry.
          destruct IHs.
          boundary.
      + eapply (typing_subst1 _).
        * eapply stability.
          1: now apply conv_neu_sound.
          now symmetry.
        * eapply stability.
          1: now eapply IHP.
          symmetry.
          econstructor ; tea.
          do 2 econstructor.
          boundary.
    - intros * ? IHe ? IHP **.
      edestruct IHe as [[? [IHe' ->%conv_empty_l]] ?] ; tea ; clear IHe.
      2:{
        eapply type_isType.
        1: boundary.
        now eapply algo_conv_wh in IHe' as [].
      }
      eexists ; split.
      1: econstructor ; tea.
      + eapply IHP.
        econstructor ; tea.
        do 2 econstructor.
        boundary.
      + eapply (typing_subst1 _).
        * eapply stability.
          1: now apply conv_neu_sound.
          now symmetry.
        * eapply stability.
          1: now eapply IHP.
          symmetry.
          econstructor ; tea.
          do 2 econstructor.
          boundary.
    - intros * ? [ih ?] **.
      edestruct ih as [? [hconv (?&?&[])%conv_sig_l]]; tea; subst.
      2:{
        eapply type_isType.
        1: boundary.
        now eapply algo_conv_wh in hconv as [].
      }
      eexists; split.
      1: now econstructor.
      now symmetry.
    - intros * ? [ih ?] **.
      edestruct ih as [? [hconv (?&?&[])%conv_sig_l]]; tea; subst.
      2:{
        eapply type_isType.
        1: boundary.
        now eapply algo_conv_wh in hconv as [].
      }
      eexists; split.
      1: now econstructor.
      eapply typing_subst1; tea.
      econstructor.
      eapply stability.
      1: now apply conv_neu_sound.
      now symmetry.
    - intros * ? [ihe ?] ? [ihP] ? [ihhr] [hm hn] * ?.
      edestruct ihe as [? [[hconv hconv']%dup]] ; tea; subst.
      destruct hm as [? [? [? [[->] ]]%termGen']%dup].
      destruct hn as [? [? [? [[->] ]]%termGen']%dup].
      eapply algo_conv_sound in hconv' as []%conv_neu_typing_unique.
      2-3: now eexists ; eapply stability.
      epose proof (idElimConv (e := e) (e' := e')) as (?&?&?&[]) ; tea.
      1-2: eexists ; eapply stability ; tea ; now symmetry.
      1: now symmetry.
      now eapply algo_conv_wh in hconv as [].
      subst.
      eassert [(Δ,, A'),, tId A'⟨wk1 A'⟩ x'⟨wk1 A'⟩ (tRel 0) |-[ al ] P' ≅ P].
      {
        eapply ihP.
        eapply idElimMotiveCtxConv; tea.
        * now symmetry.
        * now symmetry.
        * symmetry ; now econstructor.
      }
      eexists; split.
      1: econstructor; tea.
      + eapply algo_conv_conv.
        * now eapply ihhr.
        * now eapply conv_ctx_refl_r.
        * eapply typing_subst2; tea.
          1: boundary.
          all: cycle -1.
          -- eapply stability ; tea.
             eapply idElimMotiveCtxConv ; tea.
             all: econstructor.
             all: boundary.
          -- eapply convtm_meta_conv.
             1: econstructor.
             4: reflexivity.
             1-2: eassumption.
             cbn; rewrite 2!wk1_ren_on, 2!shift_one_eq; now econstructor.
        * eapply stability; [| now symmetry]; now boundary.
        * eapply stability; [| now symmetry]; now boundary.
      + eapply stability; tea;[| now symmetry].
        eapply typing_subst2; tea.
        1: boundary.
        1: now eapply stability.
        cbn; rewrite 2!wk1_ren_on, 2!shift_one_eq; tea.
        econstructor; tea.
        1: now apply conv_neu_sound.
        symmetry.
        eapply stability ; tea.
        now econstructor.
    - intros * ? IHm  **.
      edestruct IHm as [[A'' [IHm' Hconv]] ?] ; tea ; clear IHm.
      assert [Δ |-[de] A' ≅ A''] as Hconv'.
      {
        etransitivity ; tea.
        symmetry.
        eapply RedConvTyC, subject_reduction_type ; tea.
        eapply stability.
        2: now symmetry.
        boundary.
      }
      pose proof Hconv' as [? []]%red_ty_complete_l.
      2: now eapply type_isType ; boundary.
      eexists ; split.
      + econstructor.
        * eassumption.
        * now eapply redty_red.
        * gen_typing.
      + etransitivity ; tea.
        now eapply RedConvTyC.
    - intros.
      econstructor.
      all: intuition eauto.
    - intros * ? IHA ? IHB **.
      econstructor.
      1: now eapply IHA.
      eapply IHB.
      econstructor ; tea.
      now econstructor ; intuition eauto.
    - now econstructor.
    - now econstructor.
    - intros * ? IH **.
      econstructor.
      now eapply IH.
    - now econstructor.
    - intros * ? ? ? IH [Hf] **.
      econstructor.
      1-2: assumption.
      eapply IH.
      econstructor ; tea.
      eapply boundary, prod_ty_inv in Hf as [].
      now econstructor.
    - intros * ? ihA ? ihB ? ihSig **.
      econstructor.
      1: now eapply ihA.
      eapply ihB; econstructor; tea.
      econstructor; now eapply ihA.
    - intros * ??? [ihFst] ? [ihSnd] [ihp ihq] **.
      econstructor; tea.
      1: now eapply ihFst.
      assert [Δ |-[ de ] B[(tFst p)..] ≅ B[(tFst q)..]]. 1:{
        eapply stability; [|now symmetry].
        eapply typing_subst1; tea.
        eapply boundary, sig_ty_inv in ihp as [].
        now econstructor.
      }
      eapply algo_conv_conv.
      * eapply ihSnd; tea.
      * eapply ctx_refl; now boundary.
      * tea.
      * eapply wfTermConv; refold.
        1: eapply stability.
        2,3: now symmetry.
        now econstructor.
      * eapply stability; [now econstructor| now symmetry].
    - intros * ? [ihA] ? [ihx] ? [ihy] [[? [[->]]]%termGen' [? [[->]]]%termGen'] * ?.
      econstructor.
      + now eapply ihA.
      + eapply algo_conv_conv.
        * eapply ihx; tea.
        * now eapply conv_ctx_refl_r.
        * constructor.
          pose proof H as ?%algo_conv_sound;try boundary.
          now eapply stability.
        * eapply stability; [| now symmetry].
          eapply wfTermConv; refold; tea.
          symmetry; now econstructor.
        * now eapply stability.
      + eapply algo_conv_conv.
        * eapply ihy; tea.
        * now eapply conv_ctx_refl_r.
        * pose proof H as ?%algo_conv_sound;try boundary.
          econstructor; now eapply stability.
        * eapply stability; [| now symmetry].
          eapply wfTermConv; refold; tea.
          econstructor; now symmetry.
        * now eapply stability.
    - econstructor.
    - intros * ? IH  **.
      edestruct IH as [[? []] ?] ; tea.
      now econstructor.
  Qed.

End Symmetry.

(** ** Transitivity *)

Section Transitivity.
  Context `{!TypingSubst de} `{!TypeReductionComplete de} `{!TypeConstructorsInj de}.

  Let PTyEq (Γ : context) (A B : term) := forall Δ C,
    [|-[de] Γ ≅ Δ] ->
    [Δ |-[al] B ≅ C] ->
    [Γ |-[al] A ≅ C].
  Let PTyRedEq (Γ : context) (A B : term) := forall Δ C,
    [|-[de] Γ ≅ Δ] ->
    [Δ |-[al] B ≅h C] ->
    [Γ |-[al] A ≅h C].
  Let PNeEq (Γ : context) (A t u : term) := forall Δ v A',
    [|-[de] Γ ≅ Δ] ->
    [Δ |-[al] u ~ v ▹ A'] ->
    [Γ |-[al] t ~ v ▹ A] × [Γ |-[de] A ≅ A'].
  Let PNeRedEq (Γ : context) (A t u : term) := forall Δ A' v,
    [|-[de] Γ ≅ Δ] ->
    [Δ |-[al] u ~h v ▹ A'] ->
    [Γ |-[al] t ~h v ▹ A] × [Γ |-[de] A ≅ A'].
  Let PTmEq (Γ : context) (A t u : term) := forall Δ A' v,
    [|-[de] Γ ≅ Δ] ->
    [Γ |-[de] A' ≅ A] ->
    [Δ |-[al] u ≅ v : A'] ->
    [Γ |-[al] t ≅ v : A].
  Let PTmRedEq (Γ : context) (A t u : term) := forall Δ A' v,
    [|-[de] Γ ≅ Δ] ->
    [Γ |-[de] A' ≅ A] ->
    [Δ |-[al] u ≅h v : A'] ->
    [Γ |-[al] t ≅h v : A].

  Theorem algo_conv_trans :
  BundledConvInductionConcl PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
  Proof.
    subst PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
    apply BundledConvInduction.
    - intros ? ? ? ? B' ? ? Hconv IH ? ? ? * ? Hconv'.
      inversion Hconv' ; subst ; clear Hconv'.
      assert (A'0 = B') as ->.
      {
        eapply whred_det ; tea.
        - eapply algo_conv_wh in H5 as [] ; gen_typing.
        - eapply algo_conv_wh in Hconv as [] ; gen_typing.
      }
      econstructor ; tea.
      eapply IH ; tea.
    - intros * ? [IHA ] ? IHB ? ? ? * ? Hconv.
      inversion Hconv ; subst ; clear Hconv.
      2:{
        apply algo_conv_wh in H5 as [e _].
        now inversion e.
        }
        econstructor.
        + eapply IHA ; tea.
        + eapply IHB ; tea.
          now econstructor.
    - intros * [_] * ? Hconv.
      inversion Hconv ; subst ; clear Hconv.
      2:{ apply algo_conv_wh in H2 as [e _]. now inversion e. }
      now constructor.
    - intros * [_] * ? Hconv.
      inversion Hconv ; subst ; refold.
      1: now constructor.
      eapply algo_conv_wh in H2 as [e _].
      now inversion e.
    - intros * [_] * ? Hconv.
      inversion Hconv ; subst ; clear Hconv.
      2:{ apply algo_conv_wh in H2 as [e _]. now inversion e. }
      now constructor.
    - intros * ? [IHA ] ? IHB ? ? ? * ? Hconv.
      inversion Hconv ; subst ; clear Hconv.
      2:{
        apply algo_conv_wh in H5 as [e _].
        now inversion e.
        }
        econstructor.
        + eapply IHA ; tea.
        + eapply IHB ; tea.
          now econstructor.
    - intros * ? [ihA] ? [ihx] ? [ihy] ??? * ? hconv.
      inversion hconv; subst; clear hconv; refold.
      2: apply algo_conv_wh in H6 as [e _]; now inversion e.
      econstructor.
      + now eapply ihA.
      + eapply ihx; tea; now symmetry.
      + eapply ihy; tea; now symmetry.
    - intros * ?? ? IH ? ? ? * ? Hconv.
      inversion Hconv ; subst ; clear Hconv ; refold; cycle -1.
      1: econstructor ; tea ; now eapply IH.
      all: apply algo_conv_wh in H1 as [_ e] ; now inversion e.
    - intros * Hin [_] * ? Hconv.
      inversion Hconv ; subst ; clear Hconv ; refold.
      split.
      + now econstructor.
      + eapply in_ctx_conv_l in Hin as [? [Hin ]]; tea.
        eapply in_ctx_inj in Hin.
        2: clear Hin ; tea.
        now subst.
    - intros * ? IHm ? IHt ? ? ? * ? Hconv.
      inversion Hconv ; subst ; clear Hconv ; refold.
      eapply IHm in H7 as [? []%prod_ty_inj] ; tea.
      split.
      + econstructor ; tea.
        now eapply IHt.
      + eapply typing_subst1 ; tea.
        econstructor.
        1: now eapply IHt.
        now symmetry.
    - intros * ? IHn ? IHP ? IHz ? IHs ? ? ? * ? Hconv.
      inversion Hconv ; subst ; clear Hconv ; refold.
      eapply IHn in H11 as [? _] ; tea.
      split.
      + econstructor ; tea.
        * eapply IHP ; tea.
          econstructor ; tea.
          do 2 econstructor.
          boundary.
        * eapply IHz ; tea.
          symmetry.
          eapply typing_subst1.
          2: eapply IHP.
          do 2 econstructor.
          boundary.
        * eapply IHs ; tea.
          symmetry.
          destruct IHP.
          eapply elimSuccHypTy_conv ; tea.
          all: now boundary.
      + eapply typing_subst1 ; tea.
        1: now eapply conv_neu_sound.
        eapply IHP.
    - intros * ? IHe ? IHP ? ? ? ? * ? Hconv.
      inversion Hconv ; subst ; clear Hconv ; refold.
      eapply IHe in H7 as [? _] ; tea.
      split.
      + econstructor ; tea.
        eapply IHP ; tea.
        econstructor ; tea.
        do 2 econstructor.
        boundary.
      + eapply typing_subst1 ; tea.
        1: now eapply conv_neu_sound.
        eapply IHP.
    - intros * ? [ih ?] [] * ? hconv.
      inversion hconv; subst; clear hconv; refold.
      edestruct ih as [? []%sig_ty_inj]; tea.
      split; [now econstructor|now symmetry].
    - intros * ? [ih ?] [] * ? hconv.
      inversion hconv; subst; clear hconv; refold.
      edestruct ih as [? []%sig_ty_inj]; tea.
      split; [now econstructor|].
      eapply typing_subst1; tea.
      econstructor.
      now eapply conv_neu_sound.
    - intros * hconve [ihe ?] ? [ihP] ? [ihhr] [hm hn] * ? hconv.
      inversion hconv; subst; clear hconv; refold.
      edestruct ihe as [? []%id_ty_inj]; tea.
      eapply algo_conv_sound in hconve as []%conv_neu_typing_unique.
      2: edestruct hm as [? [? [[-> ]]]%termGen'] ; now eexists.
      2: edestruct hn as [? [? [[-> ]]]%termGen'] ; now eexists.
      epose proof (idElimConv hm hn) as (?&?&?&[]) ; tea.
      1: eapply TypeRefl ; refold ; boundary.
      now econstructor.
      split.
      + econstructor; tea; eauto.
        * eapply ihP; tea; symmetry.
          eapply idElimMotiveCtxConv ; tea ; eapply idElimMotiveCtx.
        * eapply ihhr; tea; symmetry.
          eapply typing_subst2; tea.
          1: boundary.
          cbn; rewrite 2!wk1_ren_on, 2!shift_one_eq.
          now econstructor.
      + eapply typing_subst2; tea.
        1: boundary.
        cbn; rewrite 2!wk1_ren_on, 2!shift_one_eq.
        econstructor; tea.
        symmetry.
        now econstructor.
    - intros * ? IH ? ? ? ? ? * ? Hconv.
      inversion Hconv ; subst ; clear Hconv ; refold.
      edestruct IH as [[? HconvA] ?] ; tea.
      split.
      1: now econstructor.
      etransitivity ; [|etransitivity].
      1: symmetry.
      1,3: eapply RedConvTyC, subject_reduction_type ; tea ; boundary.
      eassumption.
    - intros * ? ? Hu Ht' IHt ? ? ? * ? HconvA Hconv.
      inversion Hconv ; subst ; clear Hconv ; refold.
      eapply whred_det in Hu ; tea.
      2,3: now eapply algo_conv_wh in H6 as [], Ht' as [].
      subst.
      econstructor ; tea.
      eapply IHt ; tea.
      etransitivity ; [|etransitivity].
      1: symmetry.
      1,3: eapply RedConvTyC, subject_reduction_type ; tea ; boundary.
      eassumption.
    - intros * ? [IHA HpostA] ? IHB [] ? A'' ? HΓ Hconvty Hconv.
      replace A'' with U in *.
      2:{
        eapply algo_conv_wh in Hconv as [].
        symmetry.
        eapply red_whnf.
        2: gen_typing.
        now eapply red_compl_univ_r, redty_red in Hconvty.
      }
      inversion Hconv ; subst ; clear Hconv ; refold.
      2: now inversion H1.
      econstructor.
      1: now eapply IHA.
      eapply IHB.
      3: eassumption.
      + econstructor ; tea. now econstructor.
      + do 3 econstructor.
        * now symmetry in HΓ ; boundary.
        * econstructor.
          boundary.
    - intros * [_] ? A' ? ? Hconvty Hconv.
      replace A' with U in *.
        2:{
          eapply algo_conv_wh in Hconv as [].
          symmetry.
          eapply red_whnf.
          2: gen_typing.
          now eapply red_compl_univ_r, redty_red in Hconvty.
        }
      inversion Hconv ; subst ; clear Hconv ; refold.
      + now econstructor.
      + inversion H0.
    - intros * [_] ? A' ? ? Hconvty Hconv.
      replace A' with tNat in *.
        2:{
          eapply algo_conv_wh in Hconv as [].
          symmetry.
          eapply red_whnf.
          2: gen_typing.
          now eapply red_compl_nat_r, redty_red in Hconvty.
        }
      inversion Hconv ; subst ; clear Hconv ; refold.
      2: now inversion H0.
      now econstructor.
    - intros * ? IHt [] ? A' ? ? Hconvty Hconv.
      replace A' with tNat in *.
      2:{
        eapply algo_conv_wh in Hconv as [].
        symmetry.
        eapply red_whnf.
        2: gen_typing.
        now eapply red_compl_nat_r, redty_red in Hconvty.
      }
      inversion Hconv ; subst ; clear Hconv ; refold.
      2: now inversion H1.
      now econstructor.
    - intros * [] ? A' ? ? Hconvty Hconv.
      replace A' with U in *.
      2:{
        eapply algo_conv_wh in Hconv as [].
        symmetry.
        eapply red_whnf.
        2: gen_typing.
        now eapply red_compl_univ_r, redty_red in Hconvty.
      }
      inversion Hconv ; subst ; clear Hconv ; refold.
      2: now inversion H0.
      now econstructor.
    - intros * ? ? ? IH [] * ? h Hconv.
      inversion Hconv ; subst ; clear Hconv ; refold.
      all: try match goal with H : isPosType _ |- _ => destruct H end.
      all: try solve [now unshelve eapply ty_conv_inj in h ; [econstructor | econstructor | cbn in *]].
      eapply prod_ty_inj in h as [].
      econstructor ; tea.
      eapply IH ; tea.
      now econstructor.
    - intros * ? [IHA HpostA] ? IHB [] ? A'' ? HΓ Hconvty Hconv.
      replace A'' with U in *.
      2:{
        eapply algo_conv_wh in Hconv as [].
        symmetry.
        eapply red_whnf.
        2: gen_typing.
        now eapply red_compl_univ_r, redty_red in Hconvty.
      }
      inversion Hconv ; subst ; clear Hconv ; refold.
      2: inversion H1.
      econstructor.
      1: now eapply IHA.
      eapply IHB.
      3: eassumption.
      + econstructor ; tea. now econstructor.
      + do 3 econstructor.
        * now symmetry in HΓ ; boundary.
        * econstructor.
          boundary.
    - intros * ? ? ? [ihFst] ? ihSnd [] * ? h Hconv.
      inversion Hconv ; subst ; clear Hconv ; refold.
      all: try match goal with H : isPosType _ |- _ => destruct H end.
      all: try solve [now unshelve eapply ty_conv_inj in h ; [econstructor | econstructor | cbn in *]].
      eapply sig_ty_inj in h as [].
      econstructor ; tea.
      1: eapply ihFst ; tea; now econstructor.
      eapply ihSnd; tea.
      eapply typing_subst1; tea.
      symmetry.
      now econstructor.
    - intros * ? [ihA] ? [ihx] ? [ihy] ??? * ? r%red_compl_univ_r hconv.
      inversion hconv; subst; clear hconv.
      1,2: unshelve epose proof (redty_whnf r _); try constructor; congruence.
      2: refold; apply algo_conv_wh in H4 as [? _]; inv_whne.
      econstructor; tea.
      * eapply ihA; tea; do 2 econstructor; boundary.
      * eapply ihx; tea; econstructor; now symmetry.
      * eapply ihy; tea; econstructor; now symmetry.
    - intros * ??? * ? [? [? [? [r]]]]%red_compl_id_r hconv.
      inversion hconv; subst; clear hconv; refold.
      1,2: unshelve epose proof (redty_whnf r _); try constructor; congruence.
      2: refold; apply algo_conv_wh in H1 as [? _]; inv_whne.
      econstructor.
    - intros * Hnconv IH ? ? ? ? * ? h Hconv.
      inversion Hconv ; subst ; clear Hconv ; refold.
      1-5,7,9,10: now inversion Hnconv.
      1,2: destruct H ;
          now unshelve eapply ty_conv_inj in h ; [now econstructor | now econstructor | cbn in *].
      econstructor ; tea.
      now eapply IH.
Qed.

End Transitivity.