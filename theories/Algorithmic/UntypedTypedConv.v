(** * LogRel.Algorithmic.UntypedTypedConv: implications between typed and untyped conversion. *)

From LogRel Require Import Utils Syntax.All GenericTyping DeclarativeTyping AlgorithmicJudgments.
From LogRel.TypingProperties Require Import PropertiesDefinition DeclarativeProperties SubstConsequences TypeInjectivityConsequences NeutralConvProperties.
From LogRel.Algorithmic Require Import Bundled TypedConvProperties  UntypedConvSoundness Strengthening.

Import DeclarativeTypingProperties AlgorithmicTypedConvData AlgorithmicTypingData.

(** ** Typed algorithmic conversion implies untyped algorithmic conversion *)

Section TypedToUntyped.
  Context
    `{!TypingSubst de}
    `{!TypeConstructorsInj de}.

  Lemma whne_app_inv f g :
  [tApp f⟨↑⟩ (tRel 0) ~ tApp g⟨↑⟩ (tRel 0)] ->
  [f ~ g].
  Proof.
    inversion 1 ; subst.
    unshelve eapply algo_uconv_str.
    6: eassumption.
    3: unshelve eapply wk1 ; tea ; exact ε.
    all: now bsimpl.
  Qed.

  Let PTyEq (Γ : context) (A B : term) := 
    [A ≅ B] × (whne A -> whne B -> [A ~ B]).
  Let PTyRedEq (Γ : context) (A B : term) :=
    [A ≅h B] × (whne A -> whne B -> [A ~ B]).
  Let PNeEq (Γ : context) (A t u : term) := [t ~ u].
  Let PNeRedEq (Γ : context) (A t u : term) := [t ~ u].
  Let PTmEq (Γ : context) (A t u : term) :=
    [t ≅ u] × (whne t -> whne u -> [t ~ u]).
  Let PTmRedEq (Γ : context) (A t u : term) :=
    [t ≅h u] × (whne t -> whne u -> [t ~ u]).

  Theorem bundled_conv_uconv :
    BundledConvInductionConcl PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
  Proof.
    all: subst PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
    apply BundledConvInduction ; cbn in *.
    all: try solve [
      intros ; prod_hyp_splitter ; 
      now econstructor |
      intros ; prod_hyp_splitter ; 
      split ; [now econstructor|..] ;
      intros ;
      repeat match goal with
        | H : [_ ⤳* _] |- _ => eapply red_whne in H ; [..|eassumption] end ;
      now subst |
      intros ; prod_hyp_splitter ; 
      split ; [now econstructor|..] ;
      intros Hne ; now inversion Hne].
    - intros ; now prod_hyp_splitter.

    (** Comparison of two functions *)
    - intros * whf whg ? [[IHconv IHne]] [Hf Hg].
      eapply fun_isFun in Hf ; tea.
      eapply fun_isFun in Hg ; tea.
      destruct Hf, Hg.
      + split.
        2: intros Hne ; inversion Hne.
        econstructor.
        inversion IHconv ; subst.
        econstructor ; tea.
        all: eapply eta_expand_beta_inv ; tea.
        all: now eapply algo_uconv_wh in H2 as [].
      + split.
        2: intros Hne ; inversion Hne.
        econstructor ; tea.
        inversion IHconv ; subst.
        econstructor ; tea.
        eapply eta_expand_beta_inv ; tea.
        now eapply algo_uconv_wh in H2 as [].
      + split.
        2: intros ? Hne ; inversion Hne.
        econstructor ; tea.
        inversion IHconv ; subst.
        econstructor ; tea.
        eapply eta_expand_beta_inv ; tea.
        now eapply algo_uconv_wh in H2 as [].
      + split.
        1: econstructor.
        2: intros _ _.
        all: eapply whne_app_inv, IHne ; econstructor ; now eapply whne_ren.

    (** Comparison of two pairs *)
    - intros * whp whq ? [[IHconv IHne]] ? [[IHconv' IHne']] [Hp Hq].
      eapply sig_isPair in Hp ; tea.
      eapply sig_isPair in Hq ; tea.
      destruct Hp, Hq.
      + split.
        2: intros Hne ; inversion Hne.
        econstructor.
        * inversion IHconv ; subst.
          econstructor ; tea.
          all: eapply eta_expand_fst_inv ; tea.
          all: now eapply algo_uconv_wh in H3 as [].
        * inversion IHconv' ; subst.
          econstructor ; tea.
          all: eapply eta_expand_snd_inv ; tea.
          all: now eapply algo_uconv_wh in H3 as [].
      + split.
        2: intros Hne ; inversion Hne.
        econstructor ; tea.
        * inversion IHconv ; subst.
          econstructor ; tea.
          eapply eta_expand_fst_inv ; tea.
          now eapply algo_uconv_wh in H3 as [].
        * inversion IHconv' ; subst.
          econstructor ; tea.
          all: eapply eta_expand_snd_inv ; tea.
          all: now eapply algo_uconv_wh in H3 as [].
      + split.
        2: intros ? Hne ; inversion Hne.
        econstructor ; tea.
        * inversion IHconv ; subst.
          econstructor ; tea.
          eapply eta_expand_fst_inv ; tea.
          now eapply algo_uconv_wh in H3 as [].
        * inversion IHconv' ; subst.
          econstructor ; tea.
          all: eapply eta_expand_snd_inv ; tea.
          all: now eapply algo_uconv_wh in H3 as [].
      + split.
        1: econstructor.
        2: intros _ _.
        all: unshelve (epose proof (IHne _ _) as IHne_ ; inversion IHne_ ; subst ; tea).
        all: now econstructor. 
  Qed.
  
End TypedToUntyped.

(** ** Algorithmic typed neutral comparison *)
(** We prove that algorithmic neutral comparison implies algorithmic conversion, *at all types*.
  The quick proof goes through completeness of algorithmic conversion and soundness. Otherwise, we'd
  need deep normalisation of the type… In any case, of form of normalisation is unavoidable:
  at a non-normalising type, a variable is related to itself as a neutral but not as a normal form. *)

Section NeutralConversion.
  Context `{!TypingSubst de} `{!TypeConstructorsInj de}
    `{!TypeReductionComplete de} `{!ConvImplies de al}.

  Import AlgorithmicTypingData.
  
  Lemma ne_conv_conv (Γ : context) (A A' m n : term) :
    [Γ |-[de] A] ->
    isType A ->
    well_typed Γ m ->
    well_typed Γ n ->
    [Γ |-[al] m ~ n ▹ A'] ->
    [Γ |-[de] A' ≅ A] ->
    [Γ |-[al] m ≅h n : A].
  Proof.
    intros * ???? [[]%algo_conv_wh Hconv]%dup ? ; tea.
    eapply algo_conv_sound in Hconv as [Hconv%conv_neu_sound]%dup ; tea.
    eapply tm_conv_compl, algo_conv_conv in Hconv ; cycle 1.
    - eapply ctx_refl ; boundary.
    - eassumption.
    - boundary.
    - boundary.
    - destruct Hconv as [??????? hA hm hn] ; subst ; refold.
      eapply red_whnf in hA as -> ; [| gen_typing].
      eapply red_whnf in hm as -> ; [| gen_typing].
      eapply red_whnf in hn as -> ; [| gen_typing].
      assumption.
  Qed.

  Lemma conv_wh_conv_red (Γ : context) (A A' m n : term) :
    [A ⤳* A'] ->
    whnf A' ->
    whnf m ->
    whnf n ->
    [Γ |-[al] m ≅ n : A] ->
    [Γ |-[al] m ≅h n : A'].
  Proof.
    intros hred hA hm hn hconv.
    destruct hconv as [??????? redA ?? hconv] ; refold.
    eapply red_whnf in hm, hn ; tea ; subst.
    eapply whred_det in redA ; tea ; subst.
    2: now eapply algo_conv_wh in hconv as [] ; gen_typing.
    eassumption.
  Qed.

End NeutralConversion.

(** Untyped algorithmic conversion implies typed algorithmic conversion *)

Section UntypedToTyped.
  Context
    `{!TypingSubst de}
    `{!TypeConstructorsInj de}
    `{!TypeReductionComplete de}
    `{!ConvImplies de al}
    `{!Normalisation de}.

  Let PEq (t u : term) :=
    (forall Γ, [Γ |-[de] t] × [Γ |-[de] u] -> [Γ |-[al] t ≅ u]) ×
    (forall Γ A, [Γ |-[de] t : A] × [Γ |-[de] u : A] -> [Γ |-[al] t ≅ u : A]).

  Let PRedEq (t u : term) :=
    (forall Γ, [Γ |-[de] t] × [Γ |-[de] u] -> [Γ |-[al] t ≅h u]) ×
    (forall Γ A, isType A -> [Γ |-[de] t : A] × [Γ |-[de] u : A] -> [Γ |-[al] t ≅h u : A]).

  Let PNeEq (t u : term) :=
    forall Γ, well_typed Γ t × well_typed Γ u ->
    ∑ A'', [Γ |-[al] t ~ u ▹ A''].

  Lemma uconv_tconv :
    UAlgoConvInductionConcl PEq PRedEq PNeEq.
  Proof.
    subst PEq PRedEq PNeEq.
    unfold UAlgoConvInductionConcl.
    apply UAlgoConvInduction.
    
    - intros * Ht Hu Ht' [Hty Htm].
      split.
      + intros * Hconcl.
        eapply typeConvRed_prem2 in Hconcl.
        2-3: eassumption.
        now econstructor.
      + intros * [Hconcl []]%dup.
        assert [Γ |-[de] A] as [[? ? wh]%ty_norm]%dup by boundary.
        eapply termConvRed_prem3 in Hconcl ; tea.
        econstructor ; eauto.
        eapply Htm ; eauto.
        eapply type_isType ; tea.
        now eapply  subject_reduction_raw_ty.

    - split.
      + now econstructor.
      + intros * ? [[? [[] ]]%termGen' _].

    - intros * HA [IHA_ty IHA_tm] HB [IHB_ty IHB_tm].
      split.
      + intros ? [Hconcl]%dup.
        eapply typePiCongAlg_prem0 in Hconcl as [Hpre0 []]%dup.
        eapply IHA_ty, algo_conv_sound, typePiCongAlg_prem1 in Hpre0 ; tea.
        now econstructor.

      + intros ? T ? [Hconcl [[Hty]%dup]]%dup.

        eapply termGen' in Hty as (?&[->]&->%conv_univ_l) ; tea.
        eapply termPiCongAlg_prem0 in Hconcl as [Hpre0 []]%dup.
        eapply IHA_tm, algo_conv_sound, termPiCongAlg_prem1 in Hpre0 ; eauto.
        now econstructor.
        
    - split.
      1: now econstructor.
      intros ? T ? [Hty].

      assert (T = U) as -> by
        now eapply termGen' in Hty as (?&->&?%conv_univ_l).
      constructor.

    - split.
      
      + intros * [Hz%type_isType _].
        2: constructor.
        inversion Hz ; inv_whne.

      + intros ? T ? [Hty].
        assert (T = tNat) as ->.
        {
          eapply termGen' in Hty as (?&->&?%red_compl_nat_l%redty_sound%red_whnf) ; tea.
          gen_typing.
        }
        constructor.

    - split.
    
      + intros * [Hz%type_isType _].
        2: constructor.
        inversion Hz ; inv_whne.

      + intros ? T ? [Hconcl [Hty]]%dup.
        assert (T = tNat) as ->.
        {
          eapply termGen' in Hty as (?&[->]&?%red_compl_nat_l%redty_sound%red_whnf) ; tea.
          gen_typing.
        }

        eapply termSuccCongAlg_prem0 in Hconcl.
        now constructor.

    - split.
      1: now econstructor.
      intros ? T ? [Hty].
      assert (T = U) as ->.
      {
        eapply termGen' in Hty as (?&->&?%red_compl_univ_l%redty_sound%red_whnf) ; tea.
        gen_typing.
      }
      constructor.

    - intros * ? [].
      split.
    
      + intros * [Hz%type_isType _].
        2: constructor.
        inversion Hz ; inv_whne.

      + intros ? T ? [Hconv]%dup.
        eapply LamCongUAlg_prem0_red in Hconv as (?&?&[Hred]); tea.
        eapply red_whnf in Hred as ->.
        2: gen_typing.
        
        econstructor.
        1-2: now constructor.
        eapply algo_conv_tm_expand ; eauto.
        1: reflexivity.
        1-2: eapply redalg_one_step, eta_expand_beta.

    - intros * ?? [].
      split.
    
      + intros * [Hz%type_isType _].
        2: constructor.
        inversion Hz ; inv_whne.

      + intros ? T ? [Hconv]%dup.
        eapply LamNeUAlg_prem0_red in Hconv as (?&?&[Hred]); tea.
        eapply red_whnf in Hred as ->.
        2: gen_typing.
        
        econstructor.
        1-2: now constructor.
        eapply algo_conv_tm_expand ; eauto.
        1,3: reflexivity.
        eapply redalg_one_step, eta_expand_beta.


    - intros * ?? [].
      split.
    
      + intros * [_ Hz%type_isType].
        2: constructor.
        inversion Hz ; inv_whne.

      + intros ? T ? [Hconv]%dup.
        eapply NeLamUAlg_prem0_red in Hconv as (?&?&[Hred]); tea.
        eapply red_whnf in Hred as ->.
        2: gen_typing.
        
        econstructor.
        1-2: now constructor.
        eapply algo_conv_tm_expand ; eauto.
        1,2: reflexivity.
        eapply redalg_one_step, eta_expand_beta.

    - intros * HA [IHA_ty IHA_tm] HB [IHB_ty IHB_tm].
      split.
      + intros ? [Hconcl]%dup.
        eapply typeSigCongAlg_prem0 in Hconcl as [Hpre0 []]%dup.
        eapply IHA_ty, algo_conv_sound, typeSigCongAlg_prem1 in Hpre0 ; tea.
        now econstructor.

      + intros ? T ? [Hconcl [[Hty]%dup]]%dup.

        eapply termGen' in Hty as (?&[->]&->%red_compl_univ_l%redty_sound%red_whnf) ; tea.
        2: gen_typing.

        eapply termSigCongAlg_prem0 in Hconcl as [Hpre0 []]%dup.

        eapply IHA_tm, algo_conv_sound, termSigCongAlg_prem1 in Hpre0 ; eauto.
        now econstructor.

    - intros * Hp [_ IHp] Hq [_ IHq].
      split.

      + intros * [Hz%type_isType _].
        2: constructor.
        inversion Hz ; inv_whne.

      + intros * ? [Hconcl [[Hty]%dup]]%dup.

        eapply PairCongUAlg_prem0_red in Hconcl as (?&?&[Hred [Hpre0 []]%dup]) ; tea.
        eapply red_whnf in Hred as ->.
        2: gen_typing.

        eapply IHp, algo_conv_sound, PairCongUAlg_prem1_red in Hpre0 ; eauto.
        2: reflexivity.
        econstructor.
        1-2: now constructor.

        all: eapply algo_conv_tm_expand.
        all: solve [eapply redalg_one_step ; now constructor | reflexivity | eauto].

      - intros * ? Hp [_ IHp] Hq [_ IHq].
        split.
  
        + intros * [Hz%type_isType _].
          2: constructor.
          inversion Hz ; inv_whne.
  
        + intros * ? [Hconcl [[Hty]%dup]]%dup.
  
          eapply PairNeUAlg_prem0_red in Hconcl as (?&?&[Hred [Hpre0 []]%dup]) ; tea.
          eapply red_whnf in Hred as ->.
          2: gen_typing.
  
          eapply IHp, algo_conv_sound, PairNeUAlg_prem1_red in Hpre0 ; eauto.
          econstructor.
          1-2: now constructor.
          3: reflexivity.
  
          all: eapply algo_conv_tm_expand.
          all: solve [eapply redalg_one_step ; now constructor | reflexivity | eauto].

    - intros * ? Hp [_ IHp] Hq [_ IHq].
      split.

      + intros * [_ Hz%type_isType].
        2: constructor.
        inversion Hz ; inv_whne.

      + intros * ? [Hconcl [[Hty]%dup]]%dup.

        eapply NePairUAlg_prem0_red in Hconcl as (?&?&[Hred [Hpre0 []]%dup]) ; tea.
        eapply red_whnf in Hred as ->.
        2: gen_typing.

        eapply IHp, algo_conv_sound, NePairUAlg_prem1_red in Hpre0 ; eauto.
        econstructor.
        1-2: now constructor.
        3: reflexivity.

        all: eapply algo_conv_tm_expand.
        all: solve [eapply redalg_one_step ; now constructor | reflexivity | eauto].
        
    - intros * HA [IHA_ty IHA_tm] Hx [_ IHx_tm] Hy [_ IHy_tm].
      split.

      + intros ? [Hconcl]%dup.
        eapply typeIdCongAlg_prem0 in Hconcl as [Hpre0 []]%dup.
        eapply IHA_ty, algo_conv_sound in Hpre0 as [Hpost0]%dup; eauto.
        eapply typeIdCongAlg_prem1 in Hpost0 as [Hpre1 []]%dup ; eauto. 
        eapply IHx_tm, algo_conv_sound, typeIdCongAlg_prem2 in Hpre1 as [Hpre2]%dup; eauto.
        now econstructor.

      + intros ? T ? [Hconcl [[Hty]%dup]]%dup.

        eapply termGen' in Hty as (?&[->]&->%red_compl_univ_l%redty_sound%red_whnf) ; tea.
        2: gen_typing.

        eapply termIdCongAlg_prem0 in Hconcl as [Hpre0 []]%dup.
        eapply IHA_tm, algo_conv_sound in Hpre0 as [Hpost0]%dup; eauto.
        eapply termIdCongAlg_prem1 in Hpost0 as [Hpre1 []]%dup ; eauto. 
        eapply IHx_tm, algo_conv_sound, termIdCongAlg_prem2 in Hpre1 as [Hpre2]%dup; eauto.
        now econstructor.

    - split.
  
      + intros * [Hz%type_isType _].
        2: constructor.
        inversion Hz ; inv_whne.

      + intros ? T ? [[? [[->] Hconv]]%termGen' _].
        eapply red_compl_id_l in Hconv as (?&?&?&[Hred]).
        eapply redty_sound, red_whnf in Hred as ->.
        2: gen_typing.
        econstructor.
      
    - intros * Hconv IH.
      split.
      
      + intros * [Hconcl]%dup.
        eapply algo_uconv_wh in Hconv as [].
        eapply typeNeuConvAlg_prem2 in Hconcl ; tea.
        edestruct IH ; tea.
        now econstructor.

      + intros * ? [Hconcl []]%dup.
        pose proof Hconv as []%algo_uconv_wh.
        eapply termNeuConvAlg_prem0 in Hconcl as [] ; tea.
        edestruct IH as [? IHconv] ; eauto.
        epose proof IHconv as ?%algo_conv_sound ; tea.
        eapply ne_conv_conv in IHconv ; eauto.
        1: boundary.
        now eapply conv_neu_typing.

    - intros * [[? [? [[decl [-> ? Hdecl]] ]]%termGen'] _].
      eexists.
      now econstructor.

    - intros * ? IH ? [_] ? [Hconcl]%dup.

      eapply neuAppCongAlg_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
      eapply IH in Hpre0 as [? [Hpost0]%dup].
      eapply algo_conv_sound, AppCongUAlg_bridge in Hpost0 as (?&?&[Hconv Hpre1]); eauto.
      eapply red_compl_prod_r in Hconv as (?&?&[]).
      eapply convneu_conv in Hpre1 ; refold.
      2: econstructor ; tea ; [boundary|now symmetry].
      eapply neuAppCongAlg_prem1 in Hpre1 ; eauto.
      eexists ; econstructor ; eauto.
      econstructor ; tea.
      1: now eapply redty_sound.
      constructor.

    - intros * ? IH ? [IHP] ? [_ IHz] ? [_ IHs] ? [Hconcl]%dup.

      eapply neuNatElimCong_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
      eapply IH in Hpre0 as [? [Hpost0]%dup].
      eapply algo_conv_sound, NatElimCongUAlg_bridge in Hpost0 as [? [Hpost0]%dup]; eauto.
      eapply neuNatElimCong_prem1 in Hpost0 as [Hpre1 []]%dup ; eauto.
      eapply IHP in Hpre1 as [Hpos1]%dup ; eauto.
      eapply algo_conv_sound in Hpos1 as [Hpos1]%dup ; eauto.
      eapply neuNatElimCong_prem2 in Hpos1 as [Hpre2 []]%dup ; eauto.
      eapply IHz in Hpre2 as [Hpos2]%dup ; eauto.
      eapply algo_conv_sound in Hpos2 as [Hpos2]%dup ; eauto.
      eapply neuNatElimCong_prem3 in Hpos2 as [Hpre3 []]%dup ; eauto.
      eapply IHs in Hpre3 as Hpos3 ; eauto.
      eexists ; econstructor ; tea.
      econstructor ; eauto.
      1:now eapply red_compl_nat_r.
      now constructor.

    - intros * ? IH ? [IHP] ? [Hconcl]%dup.

      eapply neuEmptyElimCong_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
      eapply IH in Hpre0 as [? [Hpost0]%dup].
      eapply algo_conv_sound, EmptyElimCongUAlg_bridge in Hpost0 as [? [Hpost0]%dup]; eauto.
      eapply neuEmptyElimCong_prem1 in Hpost0 as [Hpre1 []]%dup ; eauto.
      eapply IHP in Hpre1 as [Hpos1]%dup ; eauto.
      eexists.
      do 2 (econstructor ; eauto).
      1: now eapply red_compl_empty_r.
      now constructor.

    - intros * ? IH ? [Hconcl]%dup.

      eapply neuFstCongAlg_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
      eapply IH in Hpre0 as [? [Hpost0]%dup].
      eapply algo_conv_sound, FstCongUAlg_bridge in Hpost0 as (?&?&[Hconv [Hpre1 ]%dup]); eauto.
      eapply red_compl_sig_r in Hconv as (?&?&[]).
      eapply convneu_conv in Hpre1 ; refold.
      2: symmetry ; econstructor ; tea ; boundary.
      eexists ; econstructor ; eauto.
      econstructor ; tea.
      1: now eapply redty_sound.
      constructor.
      
    - intros * ? IH ? [Hconcl]%dup.

      eapply neuSndCongAlg_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
      eapply IH in Hpre0 as [? [Hpost0]%dup].
      eapply algo_conv_sound, SndCongUAlg_bridge in Hpost0 as (?&?&[Hconv [Hpre1 ?]%dup]); eauto.
      eapply red_compl_sig_r in Hconv as (?&?&[]).
      eapply convneu_conv in Hpre1 ; refold.
      2: symmetry ; econstructor ; tea ; boundary.
      eexists ; econstructor ; eauto.
      econstructor ; tea.
      1: now eapply redty_sound.
      constructor.

    - intros * ? IH ? [IHP] ? [_ IHr]  ? [Hconcl]%dup.

      eapply neuIdElimCong_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
      eapply IH in Hpre0 as [? [Hpost0]%dup].
      eapply algo_conv_sound, IdElimCongUAlg_bridge in Hpost0 as [? (?&?&Hconv&[Hpost0]%dup)]; eauto.
      eapply red_compl_id_r in Hconv as (?&?&?&[]).
      eapply neuIdElimCong_prem1 in Hpost0 as [Hpre1 []]%dup ; eauto.
      eapply IHP in Hpre1 as [Hpos1]%dup ; eauto.
      eapply algo_conv_sound in Hpos1 as [Hpos1]%dup ; eauto.
      eapply neuIdElimCong_prem2 in Hpos1 as [Hpre2 []]%dup ; eauto.
      eapply IHr in Hpre2 as [Hpos2]%dup ; eauto.
      eexists ; econstructor ; tea.
      econstructor ; tea.
      1: now eapply redty_sound.
      now econstructor.
  Qed.

End UntypedToTyped.


(** ** Completeness of neutral conversion at all types *)
(** The main ideas for this completeness are already part of the proof that untyped and typed
  conversion are equivalent, so we reap the fruits here. Maybe one day we'll attempt a direct
  proof, but it is quite subtle. *)

  Section ConvPos.
  Context `{!TypingSubst de} `{!ConvImplies de al} `{!TypeConstructorsInj de}.

  Lemma neuIdElimCong_concl (Γ : context) (A A' A'' x x' x'' P P' hr hr' y y' y'' e e' : term) :
    [Γ |-[ de ] e ~ e' : tId A'' x'' y''] ->
    [(Γ,, A),, tId A⟨wk1 (Γ := Γ) A⟩ x⟨wk1 (Γ := Γ) A⟩ (tRel 0) |-[ de ] P ≅ P'] ->
    [Γ |-[ de ] hr ≅ hr' : P[tRefl A x .: x..]] ->
    well_typed (ta := de) Γ (tIdElim A x P hr y e) ×
      well_typed (ta := de) Γ (tIdElim A' x' P' hr' y' e') ->
    [Γ |-[ de ] tIdElim A x P hr y e ~ tIdElim A' x' P' hr' y' e' : P[e .: y..]].
  Proof.
    intros * He HP Hr [[Hwn Hwn'] [[? (?&[->]&?)%termGen'] [? (?&[->]&?)%termGen']]]%dup.
    epose proof (idElimConv Hwn Hwn') as (?&?&?&[He']) ; tea.
    1-2: now eapply conv_neu_typing_unique in He as [].
    1: eapply TypeRefl ; refold ; boundary.
    1: constructor.
    + econstructor ; tea.
      econstructor ; tea.
      symmetry.
      now econstructor.
  Qed.

  Lemma uconv_sound_ne :
    UAlgoConvInductionConcl
      (fun t u => True)
      (fun t u => True)

      (fun m n =>
        forall Γ, well_typed Γ m × well_typed Γ n ->
        ∑ A, [Γ |-[de] m ~ n : A]).
  Proof.
    apply UAlgoConvInduction ; try easy.
    
    - intros * [[[ ? (?&[? []]&?)%termGen']]]%dup ; subst.
      now intros ; econstructor ; [econstructor|..].

    - intros * Hconv IHm Ht _ * [Hconcl]%dup.

      eapply neuAppCongAlg_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
      eapply IHm in Hpre0 as [? [Hpost0]%dup].
      eapply AppCongUAlg_bridge in Hpost0 as (?&?&[? [Hpre1]%dup]); tea.
      eapply neuAppCongAlg_prem1 in Hpre1 ; eauto.
      eapply uconv_sound_decl in Ht as [_ ?]; tea.
      eexists.
      now econstructor.

    - intros * ? IH HP _ Hz _ Hs _ ? [Hconcl]%dup.

      eapply neuNatElimCong_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
      eapply IH in Hpre0 as [? [Hpost0]%dup].
      eapply NatElimCongUAlg_bridge in Hpost0 as [? [Hpost0]%dup]; eauto.
      eapply neuNatElimCong_prem1 in Hpost0 as [Hpre1 []]%dup ; eauto.
      eapply uconv_sound_decl in HP as [? _]; eauto.
      eexists.
      econstructor ; eauto.
      + eapply uconv_sound_decl in Hz as [_ Hz].
        eapply Hz, neuNatElimCong_prem2 ; eauto.
      + eapply uconv_sound_decl in Hs as [_ Hs].
        eapply Hs, neuNatElimCong_prem3 ; eauto.
        eapply uconv_sound_decl in Hz as [_ Hz].
        eapply Hz, neuNatElimCong_prem2 ; eauto.

    - intros * ? IH HP _ ? [Hconcl]%dup.

      eapply neuEmptyElimCong_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
      eapply IH in Hpre0 as [? [Hpost0]%dup].
      eapply EmptyElimCongUAlg_bridge in Hpost0 as [? [Hpost0]%dup]; eauto.
      eapply neuEmptyElimCong_prem1 in Hpost0 as [Hpre1 []]%dup ; eauto.
      eapply uconv_sound_decl in HP as [? _]; eauto.
      eexists.
      econstructor ; eauto.

    - intros * ? IH ? [Hconcl]%dup.

      eapply neuFstCongAlg_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
      eapply IH in Hpre0 as [? [Hpost0]%dup].
      eapply FstCongUAlg_bridge in Hpost0 as (?&?&[]); eauto.
      eexists.
      econstructor ; eauto.

    - intros * ? IH ? [Hconcl]%dup.

      eapply neuSndCongAlg_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
      eapply IH in Hpre0 as [? [Hpost0]%dup].
      eapply SndCongUAlg_bridge in Hpost0 as (?&?&[]); eauto.
      eexists.
      econstructor ; eauto.

    - intros * ? IH HP _ Hr _  ? [Hconcl]%dup.

      eapply neuIdElimCong_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
      eapply IH in Hpre0 as [? [Hpost0]%dup].
      eapply IdElimCongUAlg_bridge in Hpost0 as [? (?&?&?&[Hpost0]%dup)]; eauto.
      eapply neuIdElimCong_prem1 in Hpost0 as [Hpre1 []]%dup ; eauto.
      eapply uconv_sound_decl in HP as [? _]; eauto.
      eexists.
      eapply neuIdElimCong_concl ; eauto.
      eapply uconv_sound_decl in Hr as [_ Hr].
      now eapply Hr, neuIdElimCong_prem2.
  Qed.

  Lemma conv_pos_all : ConvNeutralConv de.
  Proof.
    constructor.
    intros Γ T n n' w w' [Hconv]%dup.
    eapply tm_conv_compl, Build_ConvTermBun, bundled_conv_uconv in Hconv as [_ Hconv].
    2-5: boundary.
    specialize (Hconv w w').
    eapply uconv_sound_ne in Hconv as [? Hconv].
    2: split ; now eexists ; boundary.
    econstructor ; tea.
    eapply conv_neu_typing ; tea.
    boundary.
  Qed.

End ConvPos.