(** * LogRel.AlgorithmicConvInstances: algorithmic conversion is an instance of generic typing. *)
From LogRel Require Import Utils Sections Syntax.All GenericTyping DeclarativeTyping AlgorithmicJudgments.
From LogRel.TypingProperties Require Import DeclarativeProperties PropertiesDefinition SubstConsequences TypeInjectivityConsequences NeutralConvProperties NormalisationDefinition.
From LogRel.Algorithmic Require Import Bundled AlgorithmicConvProperties AlgorithmicConvPER.

Import DeclarativeTypingProperties AlgorithmicTypedConvData BundledTypingData.


(** ** Instances *)

Module AlgorithmicConvProperties.
  Export AlgorithmicTypingData.

  #[local] Ltac intros_bn :=
    intros ;
    repeat match goal with | H : context [bn] |- _ => destruct H end ;
    econstructor ; try assumption.

  #[export, refine] Instance ConvTypeAlgProperties
    `{!TypingSubst de} `{!TypeReductionComplete de} `{!TypeConstructorsInj de} :
    ConvTypeProperties (ta := bn) := {}.
  Proof.
    2: split.
    - intros_bn.
      1-2: now constructor.
      now eapply algo_conv_tm_ty.
    - red ; intros_bn.
      eapply algo_conv_sym.
      + now econstructor.
      + now eapply ctx_refl.
    - red ; intros * Hconv [? ? ? Hconv'].
      econstructor ; tea.
      1: now apply Hconv.
      eapply algo_conv_trans ; tea.
      now eapply ctx_refl.
    - intros_bn.
      1-2: now apply typing_wk.
      now apply algo_conv_wk.
    - intros_bn.
      1-2: now eapply algo_typing_sound.
      now eapply algo_conv_ty_expand.
    - intros_bn.
      1-2: now econstructor.
      do 2 econstructor.
    - intros_bn.
      + now econstructor.
      + econstructor ; tea.
        eapply stability ; tea.
        econstructor.
        * now eapply ctx_refl.
        * symmetry.
          now eapply algo_conv_sound in bun_conv_ty0.
      + now do 2 econstructor.
    - intros_bn.
      + now econstructor.
      + econstructor ; tea.
        eapply stability ; tea.
        econstructor.
        * now eapply ctx_refl.
        * symmetry.
          now eapply algo_conv_sound in bun_conv_ty0.
      + now do 2 econstructor.
    - intros * convA.
      pose proof convA as ?%bn_conv_sound.
      revert convA; intros_bn.
      + now econstructor.
      + econstructor; tea; econstructor; tea.
      + econstructor.
        1,2: now reflexivity.
        now econstructor.
Qed.

  #[export, refine] Instance ConvTermAlgProperties
    `{!TypingSubst de} `{!TypeReductionComplete de} `{!TypeConstructorsInj de} :
    ConvTermProperties (ta := bn) := {}.
  Proof.
    1: split.
    - red ; intros_bn.
      eapply algo_conv_sym.
      + now econstructor.
      + now eapply ctx_refl.
    - red. intros * Hconv [? ? ? Hconv'].
      split ; tea.
      1: apply Hconv.
      eapply algo_conv_trans ; tea.
      + now apply ctx_refl.
      + now constructor.
    - intros_bn.
      all: eapply algo_conv_sound in bun_conv_ty ; tea.
      1-2: now econstructor.
      eapply algo_conv_conv ; tea.
      now apply ctx_refl.
    - intros_bn.
      1-3: now apply typing_wk.
      now apply algo_conv_wk.
    - intros_bn.
      1-2: now eapply inf_conv_decl.
      eapply algo_conv_tm_expand ; tea.
      reflexivity.
    - intros_bn.
      + boundary.
      + eapply algo_conv_sound in bun_conv_ne_conv ; tea.
        econstructor ; tea.
        boundary.
      + eapply algo_conv_sound in bun_conv_ne_conv ; tea.
        econstructor ; tea.
        boundary.
      + econstructor.
        1-3: reflexivity.
        now econstructor.
    - intros_bn.
      + now constructor.
      + constructor ; tea.
        eapply stability ; tea.
        econstructor.
        1: now apply ctx_refl.
        eapply algo_conv_sound in bun_conv_tm0 ; tea.
        symmetry.
        now constructor.
      + now do 2 econstructor.
    - intros_bn.
      + now constructor.
      + constructor ; tea.
        eapply stability ; tea.
        econstructor.
        1: now apply ctx_refl.
        eapply algo_conv_sound in bun_conv_tm0 ; tea.
        symmetry.
        now constructor.
      + now do 2 econstructor.
    - intros * [] [] [] ? [] ? []; constructor; tea.
      + boundary.
      + eauto using inf_conv_decl.
      + eauto using inf_conv_decl.
      + econstructor.
        1-3: reflexivity.
        econstructor.
        1-2: eapply isFun_whnf ;
          match goal with H : isWfFun _ _ _ ?f |- isFun ?f => destruct H end; constructor;
          match goal with H : [_ |-[bn] ?f ~ ?f : _] |- whne ?f =>
            now destruct H as [?????%algo_conv_wh] end.
        eassumption.
    - intros_bn.
      1-3: gen_typing.
      now do 2 econstructor.
    - intros_bn.
      1-3: gen_typing.
      now do 2 econstructor.
    - intros_bn.
      1-2: gen_typing.
      now do 2 econstructor.
   - intros * [] [] [] ? [] ? [] []; constructor; tea.
      + boundary.
      + eauto using inf_conv_decl.
      + eauto using inf_conv_decl.
      + econstructor.
        1-3: reflexivity.
        econstructor; tea.
        1-2: eapply isPair_whnf;
          match goal with H : isWfPair _ _ _ ?f |- isPair ?f => destruct H end; constructor;
          match goal with H : [_ |-[bn] ?f ~ ?f : _] |- whne ?f =>
            now destruct H as [?????%algo_conv_wh] end.
    - intros_bn.
      1-3: gen_typing.
      now do 2 econstructor.
    - intros * convA.
      assert [Γ |-[de] A ≅ A'] by (econstructor; now pose proof convA as ?%bn_conv_sound).
      revert convA; intros_bn.
      + now econstructor.
      + econstructor; tea; now econstructor.
      + econstructor; try reflexivity.
        now econstructor.
    - intros * convA convx.
      pose proof convA as ?%bn_conv_sound.
      pose proof convx as ?%bn_conv_sound.
      revert convA convx; intros_bn.
      + now econstructor.
      + now econstructor.
      + econstructor.
        1: econstructor; tea; now econstructor.
        symmetry; econstructor; tea.
      + econstructor; try reflexivity.
        now econstructor.
  Qed.

  #[export, refine] Instance ConvNeuAlgProperties
    `{!TypingSubst de} `{!TypeReductionComplete de} `{!TypeConstructorsInj de} :
    ConvNeuProperties (ta := bn) := {}.
  Proof.
    1: split.
    - intros ? ? [].
      assert ([Γ |-[bn] x ~ y ▹ bun_conv_ne_conv_ty]) as Hconv.
      {
        now econstructor.
      }
      eapply algo_conv_sym in Hconv as [? []].
      2: now eapply ctx_refl.
      econstructor ; tea.
      etransitivity ; tea.
      now symmetry.
    - red. intros_bn.
      + eapply algo_conv_trans ; tea.
        * now constructor.
        * now apply ctx_refl.
      + eassumption.
    - intros_bn.
      1: eassumption.
      etransitivity ; tea.
      now eapply algo_conv_sound in bun_conv_ty.
    - intros_bn.
      + destruct bun_conv_ne_conv_l.
        eexists.
        gen_typing.
      + destruct bun_conv_ne_conv_r.
        eexists.
        gen_typing.
      + now apply algo_conv_wk.
      + now apply typing_wk.
    - now intros * [?????%algo_conv_wh].
    - intros * [? ? Hty].
      inversion Hty ; subst ; clear Hty.
      econstructor.
      + assumption.
      + eexists. now econstructor.
      + eexists. now econstructor.
      + now econstructor.
      + eassumption.
  - intros *
    [? ? ? ? Hf (?&?&[])%red_compl_prod_r]
    [? ? ? ? Ht].
    econstructor ; tea.
    + eapply algo_conv_sound,conv_neu_sound in Hf ; tea.
      eapply boundary in Hf as [_ Hf _].
      eexists ; econstructor.
      * econstructor ; tea.
        now eapply RedConvTyC.
      * now econstructor.
    + eapply algo_conv_sound,conv_neu_sound in Hf as Hg ; tea.
      eapply boundary in Hg as [_ _ Hg].
      eexists ; econstructor.
      * econstructor ; tea.
        now eapply RedConvTyC.
      * now econstructor.
    + econstructor.
      * econstructor ; tea.
        2: econstructor.
        now eapply redty_red.
      * eapply algo_conv_conv ; tea.
        now eapply ctx_refl.
    + eapply typing_subst1 ; tea.
      econstructor.
      eassumption.
  - intros_bn.
    + eexists.
      econstructor ; tea.
      eapply algo_conv_sound, conv_neu_sound in bun_conv_ne_conv as Hconv ; tea.
      eapply boundary in Hconv as [].
      now econstructor.
    + eexists.
      econstructor ; tea.
      * econstructor ; tea.
        eapply typing_subst1 ; tea.
        2: now eapply algo_conv_sound in bun_conv_ty.
        now do 2 econstructor.
      * econstructor ; tea.
        eapply elimSuccHypTy_conv ; tea.
        now eapply algo_conv_sound in bun_conv_ty.
      * eapply algo_conv_sound, conv_neu_sound in bun_conv_ne_conv as Hconv ; tea.
        eapply boundary in Hconv as [].
        now econstructor.
    + econstructor ; tea.
      econstructor ; tea.
      2: now econstructor.
      now eapply redty_red, red_compl_nat_r.
    + econstructor.
      eapply typing_subst1 ; tea.
      eapply algo_conv_sound, conv_neu_sound in bun_conv_ne_conv as Hconv ; tea.
      eapply boundary in Hconv as [].
      now econstructor.
  - intros_bn.
    + eexists.
      econstructor ; tea.
      eapply algo_conv_sound, conv_neu_sound in bun_conv_ne_conv as Hconv ; tea.
      eapply boundary in Hconv as [].
      now econstructor.
    + eexists.
      econstructor ; tea.
      eapply algo_conv_sound, conv_neu_sound in bun_conv_ne_conv as Hconv ; tea.
      eapply boundary in Hconv as [].
      now econstructor.
    + econstructor ; tea.
      econstructor ; tea.
      2: now econstructor.
      now eapply redty_red, red_compl_empty_r.
    + econstructor.
      eapply typing_subst1 ; tea.
      eapply algo_conv_sound, conv_neu_sound in bun_conv_ne_conv as Hconv ; tea.
      eapply boundary in Hconv as [].
      now econstructor.
  - intros * [].
    pose proof bun_conv_ne_conv_conv as [?[?[]]]%red_compl_sig_r.
    econstructor; tea.
    + eexists.
      econstructor; tea.
      eapply algo_conv_sound, conv_neu_sound in bun_conv_ne_conv as Hconv ; tea.
      eapply boundary in Hconv as [].
      now econstructor.
    + eexists.
      econstructor; tea.
      eapply algo_conv_sound, conv_neu_sound in bun_conv_ne_conv as Hconv ; tea.
      eapply boundary in Hconv as [].
      now econstructor.
    + do 2 econstructor; tea.
      2: constructor.
      now eapply redty_red.
  - intros * [].
    pose proof bun_conv_ne_conv_conv as [?[?[]]]%red_compl_sig_r.
    econstructor; tea.
    + eexists.
      econstructor; tea.
      eapply algo_conv_sound, conv_neu_sound in bun_conv_ne_conv as Hconv ; tea.
      eapply boundary in Hconv as [].
      now econstructor.
    + eexists.
      econstructor; tea.
      eapply algo_conv_sound, conv_neu_sound in bun_conv_ne_conv as Hconv ; tea.
      eapply boundary in Hconv as [].
      now econstructor.
    + do 2 econstructor; tea.
      2: constructor.
      now eapply redty_red.
    + eapply typing_subst1 ; tea.
      eapply algo_conv_sound, conv_neu_sound in bun_conv_ne_conv as Hconv ; tea.
      econstructor; eapply lrefl.
      eapply TermConv; tea; refold.
      etransitivity; tea.
      symmetry; econstructor; tea.
      boundary.
  - intros * tyA tyx convA convx convP convhr convy [???? conve conv].
    pose proof convA as ?%bn_conv_sound.
    pose proof convx as ?%bn_conv_sound.
    pose proof convP as ?%bn_conv_sound.
    pose proof convhr as ?%bn_conv_sound.
    pose proof convy as ?%bn_conv_sound.
    econstructor; tea.
    + eexists; econstructor; try boundary.
      apply algo_conv_sound, conv_neu_sound in conve; tea.
      econstructor; [boundary|]; tea.
    + eexists; econstructor; try boundary.
      * econstructor; tea; boundary.
      * eapply stability; [boundary|].
        eapply idElimMotiveCtxConv; tea.
        1: now eapply ctx_refl.
      * econstructor; [now boundary|].
        eapply typing_subst2; tea.
        cbn ; rewrite 2!wk1_ren_on, 2! shift_one_eq.
        now econstructor.
      * econstructor; tea; boundary.
      * apply algo_conv_sound, conv_neu_sound in conve ; tea.
        econstructor; [boundary|]; tea.
        etransitivity; tea.
        econstructor; tea.
    + destruct convA, convx, convP, convhr, convy.
      pose proof conv as [?[?[?[[]]]]]%red_compl_id_r.
      econstructor; tea.
      econstructor; constructor + tea.
    + eapply TypeRefl; refold; eapply typing_subst2; tea.
      all: try boundary.
      cbn; rewrite 2!wk1_ren_on, 2!shift_one_eq.
      apply algo_conv_sound, conv_neu_sound in conve ; tea.
      econstructor; [boundary|]; tea.
  Qed.

End AlgorithmicConvProperties.

Module IntermediateTypingProperties.
  Export BundledIntermediateData.
  Import AlgorithmicConvProperties.

  #[export, refine] Instance WfCtxIntProperties : WfContextProperties (ta := bni) := {}.
  Proof.
    all: unfold_bni.
    1-2: now econstructor.
    1-2: gen_typing.
    1-4: intros * [] ; gen_typing.
  Qed.

  #[export, refine] Instance WfTypeIntProperties : WfTypeProperties (ta := bni) := {}.
  Proof.
    all: unfold_bni ; gen_typing.
  Qed.

  #[export, refine] Instance TypingIntProperties
    `{!TypingSubst de} `{!TypeReductionComplete de} `{!TypeConstructorsInj de} :
    TypingProperties (ta := bni) := {}.
  Proof.
    all: unfold_bni.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - intros * ? [].
      econstructor ; tea.
      symmetry.
      eapply RedConvTyC, subject_reduction_type ; tea.
    - intros * ? [].
      econstructor ; tea.
      now eapply algo_conv_sound in bun_conv_ty.
  Qed.

  #[export, refine] Instance ConvTypeIntProperties
    `{!TypingSubst de} `{!TypeReductionComplete de} `{!TypeConstructorsInj de} :
    ConvTypeProperties (ta := bni) := {}.
  Proof.
    all: unfold_bni.
    - gen_typing.
    - gen_typing.
    - intros * ? ?.
      apply convty_wk ; tea.
      now split.
    - intros * [] [] [] ; econstructor.
      1-3: eassumption.
      now eapply algo_conv_ty_expand.
    - intros ? ?.
      split.
      2-3: econstructor.
      1-3: assumption.
      do 2 econstructor.
    - intros * ?  [] [].
      split ; tea.
      + now econstructor.
      + econstructor ; tea.
        eapply stability ; tea.
        econstructor.
        1: now eapply ctx_refl.
        symmetry.
        now eapply algo_conv_sound in bun_conv_ty.
      + now do 2 econstructor.
    - intros * ?  [] [].
      split ; tea.
      + now econstructor.
      + econstructor ; tea.
        eapply stability ; tea.
        econstructor.
        1: now eapply ctx_refl.
        symmetry.
        now eapply algo_conv_sound in bun_conv_ty.
      + now do 2 econstructor.
    - intros. gen_typing.
  Qed.

  #[export, refine] Instance ConvTermIntProperties
    `{!TypingSubst de} `{!TypeReductionComplete de} `{!TypeConstructorsInj de} :
    ConvTermProperties (ta := bni) := {}.
  Proof.
    all: unfold_bni.
    - gen_typing.
    - gen_typing.
    - intros.
      apply (convtm_wk (ta := bn)) ; tea.
      now econstructor.
    - intros * [] [] _ _ _ _ [].
      econstructor ; tea.
      eapply algo_conv_tm_expand ; tea.
      reflexivity.
    - gen_typing.
    - intros * ? [] [].
      split ; tea.
      + now econstructor.
      + econstructor ; tea.
        eapply stability ; tea.
        econstructor.
        1: now eapply ctx_refl.
        symmetry.
        econstructor.
        now eapply algo_conv_sound in bun_conv_tm.
      + now do 2 econstructor.
    - intros * ? [] [].
      split ; tea.
      + now econstructor.
      + econstructor ; tea.
        eapply stability ; tea.
        econstructor.
        1: now eapply ctx_refl.
        symmetry.
        econstructor.
        now eapply algo_conv_sound in bun_conv_tm.
      + now do 2 econstructor.
    - intros * ? ? ? ? ? ? [].
      split ; tea.
      + gen_typing.
      + boundary.
      + do 2 econstructor ; [| |gen_typing].
        all: eapply isFun_whnf;
          match goal with H : isWfFun _ _ _ ?f |- isFun ?f => destruct H end; constructor;
          match goal with H : [_ |-[bni] ?f ~ ?f : _] |- whne ?f =>
            now destruct H as [?????%algo_conv_wh] end.
    - intros.
      eapply (convtm_nat (ta := bn)).
      now econstructor.
    - intros.
      eapply (convtm_zero (ta := bn)).
      now econstructor.
    - intros.
      now eapply (convtm_succ (ta := bn)).
    - intros * ? ? ? ? ? ? [] [].
      split ; tea.
      + gen_typing.
      + econstructor.
        1-3: reflexivity.
        econstructor; [| |gen_typing|gen_typing].
        all: eapply isPair_whnf;
          match goal with H : isWfPair _ _ _ ?f |- isPair ?f => destruct H end; constructor;
          match goal with H : [_ |-[bni] ?f ~ ?f : _] |- whne ?f =>
            now destruct H as [?????%algo_conv_wh] end.
    - intros ? HΓ.
      eapply (convtm_empty (ta := bn)).
      now econstructor.
    - intros; gen_typing.
    - intros. gen_typing.
  Qed.

  #[export, refine] Instance ConvNeuIntProperties
    `{!TypingSubst de} `{!TypeReductionComplete de} `{!TypeConstructorsInj de} :
    ConvNeuProperties (ta := bni) := {}.
  Proof.
    all: unfold_bni.
    - gen_typing.
    - gen_typing.
    - intros.
      apply convneu_wk ; tea.
      now split.
    - now intros * [?????%algo_conv_wh].
    - intros * [? [[? [-> ]]]]%termGen'.
      econstructor.
      + gen_typing.
      + now eexists ; gen_typing.
      + now eexists ; gen_typing.
      + now econstructor.
      + eassumption.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - gen_typing.
    - (* Copy-paste of the proof above in ConvNeuAlgProperties but gen_typing fails (why ?) *)
      intros * tyA tyx convA convx convP convhr convy [???? conve conv].
      pose proof convA as ?%bn_conv_sound.
      pose proof convx as ?%bn_conv_sound.
      pose proof convP as ?%bn_conv_sound.
      pose proof convhr as ?%bn_conv_sound.
      pose proof convy as ?%bn_conv_sound.
      econstructor; tea.
      + eexists; econstructor; try boundary.
        apply algo_conv_sound,conv_neu_sound in conve ; tea.
        econstructor; [boundary|]; tea.
      + eexists; econstructor; try boundary.
        * econstructor; tea; boundary.
        * eapply stability; [boundary|].
          eapply idElimMotiveCtxConv; tea.
          1: now eapply ctx_refl.
        * econstructor; [now boundary|].
          eapply typing_subst2; tea.
          cbn ; rewrite 2!wk1_ren_on, 2! shift_one_eq.
          now econstructor.
        * econstructor; tea; boundary.
        * apply algo_conv_sound,conv_neu_sound in conve ; tea.
          econstructor; [boundary|]; tea.
          etransitivity; tea.
          econstructor; tea.
      + destruct convA, convx, convP, convhr, convy.
        pose proof conv as [?[?[?[[]]]]]%red_compl_id_r.
        econstructor; tea.
        econstructor; constructor + tea.
      + eapply TypeRefl; refold; eapply typing_subst2; tea.
        all: try boundary.
        cbn; rewrite 2!wk1_ren_on, 2!shift_one_eq.
        apply algo_conv_sound,conv_neu_sound in conve ; tea.
        econstructor; [boundary|]; tea.
  Qed.

  #[export, refine] Instance RedTermIntProperties
    `{!TypingSubst de} `{!TypeReductionComplete de} `{!TypeConstructorsInj de} :
    RedTermProperties (ta := bni) := {}.
  Proof.
    all: unfold_bni.
    - intros * ? [].
      econstructor ; tea.
      + now eapply typing_wk.
      + now eapply credalg_wk.
    - intros * []; assumption.
    - now intros * [].
    - intros; constructor.
      + boundary.
      + econstructor ; tea.
        now econstructor.
      + do 2 econstructor.
    - constructor; unfold_bni.
      + boundary.
      + econstructor ; tea.
        econstructor.
        now boundary.
      + econstructor ; [| reflexivity]; econstructor.
    - constructor; unfold_bni.
      + boundary.
      + econstructor ; tea.
        econstructor.
        now boundary.
      + econstructor ; [| reflexivity]; econstructor.
    - intros * [] ?.
      split.
      + boundary.
      + now econstructor.
      + clear -buni_red_tm.
        induction buni_red_tm.
        1: econstructor.
        econstructor.
        1: now econstructor.
        eassumption.
    - intros ? ? ? ? ? ? ? ? ? [? ? Hr]; econstructor.
      + now eapply boundary_tm_ctx.
      + now constructor.
      + clear - Hr; induction Hr; try constructor.
        econstructor; [|eassumption].
        now constructor.
    - intros ? ? ? ? ? [? ? Hr]; econstructor.
      + now eapply boundary_tm_ctx.
      + now constructor.
      + clear - Hr; induction Hr; try constructor.
        econstructor; [|eassumption].
        now constructor.
    - intros; econstructor; tea.
      1: boundary.
      1: gen_typing.
      econstructor.
      2: reflexivity.
      constructor.
    - intros * [].
      econstructor; tea.
      1: gen_typing.
      clear -buni_red_tm; induction buni_red_tm.
      1: reflexivity.
      econstructor; eauto.
      now constructor.
    - intros; econstructor; tea.
      1: boundary.
      1: gen_typing.
      econstructor.
      2: reflexivity.
      constructor.
    - intros * [].
      econstructor; tea.
      1: gen_typing.
      clear -buni_red_tm; induction buni_red_tm.
      1: reflexivity.
      econstructor; eauto.
      now constructor.
    - intros * ??????? convA convxy convxz.
      pose proof convA as ?%bn_conv_sound.
      pose proof convxy as ?%bn_conv_sound.
      pose proof convxz as ?%bn_conv_sound.
      destruct convA, convxy, convxz.
      econstructor; tea.
      2: eapply redalg_one_step; constructor.
      econstructor; tea.
      econstructor.
      1: econstructor; tea; now econstructor.
      symmetry; econstructor; tea.
      etransitivity; tea; now symmetry.
    - intros * ????? [].
      econstructor; tea.
      2: now eapply redalg_idElim.
      now econstructor.
    - intros * [] [].
      econstructor ; tea.
      econstructor ; tea.
      now eapply algo_conv_sound in bun_conv_ty.
    - intros.
      split.
      + boundary.
      + assumption.
      + reflexivity.
    - red ; intros * [] [].
      econstructor ; tea.
      now etransitivity.
    Qed.

  #[export, refine] Instance RedTypeIntProperties
    `{!TypingSubst de} `{!TypeReductionComplete de} `{!TypeConstructorsInj de} :
    RedTypeProperties (ta := bni) := {}.
  Proof.
    all: unfold_bni.
    - intros * ? [].
      econstructor ; tea.
      + now eapply typing_wk.
      + now eapply credalg_wk.
    - intros * []; assumption.
    - now intros * [].
    - intros * [].
      split.
      + boundary.
      + now econstructor.
      + eassumption.
    - intros.
      split.
      + boundary.
      + eassumption.
      + reflexivity.
    - red. intros * [] [].
      econstructor ; tea.
      now etransitivity.
  Qed.

  #[export] Instance IntermediateTypingProperties
    `{!TypingSubst de} `{!TypeReductionComplete de} `{!TypeConstructorsInj de} :
    GenericTypingProperties bni _ _ _ _ _ _ _ _ := {}.

End IntermediateTypingProperties.