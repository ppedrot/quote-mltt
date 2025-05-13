(** * LogRel.TypedConvProperties: properties of typed algorithmic conversion. *)
From LogRel Require Import Utils Syntax.All GenericTyping DeclarativeTyping AlgorithmicJudgments.
From LogRel.TypingProperties Require Import DeclarativeProperties PropertiesDefinition SubstConsequences TypeInjectivityConsequences NeutralConvProperties NormalisationDefinition.
From LogRel.Algorithmic Require Import Bundled.

Import DeclarativeTypingProperties AlgorithmicTypedConvData BundledTypingData.

(** ** Stability by weakening *)

Section ConvWk.
  Import AlgorithmicTypedConvData.
  
  Let PTyEq (Γ : context) (A B : term) := forall Δ (ρ : Δ ≤ Γ),
    [Δ |-[al] A⟨ρ⟩ ≅ B⟨ρ⟩].
  Let PTyRedEq (Γ : context) (A B : term) := forall Δ (ρ : Δ ≤ Γ),
      [Δ |-[al] A⟨ρ⟩ ≅h B⟨ρ⟩].
  Let PNeEq (Γ : context) (A t u : term) := forall Δ (ρ : Δ ≤ Γ),
    [Δ |-[al] t⟨ρ⟩ ~ u⟨ρ⟩ ▹ A⟨ρ⟩].
  Let PNeRedEq (Γ : context) (A t u : term) := forall Δ (ρ : Δ ≤ Γ),
    [Δ |-[al] t⟨ρ⟩ ~h u⟨ρ⟩ ▹ A⟨ρ⟩].
  Let PTmEq (Γ : context) (A t u : term) := forall Δ (ρ : Δ ≤ Γ),
    [Δ |-[al] t⟨ρ⟩ ≅ u⟨ρ⟩ : A⟨ρ⟩].
  Let PTmRedEq (Γ : context) (A t u : term) := forall Δ (ρ : Δ ≤ Γ),
      [Δ |-[al] t⟨ρ⟩ ≅h u⟨ρ⟩ : A⟨ρ⟩].

  Theorem algo_conv_wk :
    AlgoConvInductionConcl PTyEq PTyRedEq
      PNeEq PNeRedEq PTmEq PTmRedEq.
  Proof.
    subst PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
    apply AlgoConvInduction.
    - intros.
      econstructor.
      all: eauto using credalg_wk.
    - intros * ? ? ? IHB ? *.
      cbn.
      econstructor.
      1: now eauto.
      now eapply IHB with(ρ := wk_up _ ρ).
    - econstructor.
    - intros.
      now econstructor.
    - intros.
      now econstructor.
    - intros * ??? IHB ? *; do 2 rewrite <- wk_sig.
      econstructor.
      1: eauto.
      now eapply IHB.
    - intros; now econstructor.
    - intros.
      econstructor.
      3: easy.
      all: now apply whne_ren.
    - intros * ? ? ?.
      eapply convne_meta_conv.
      1: econstructor ; eauto using in_ctx_wk.
      all: reflexivity.
    - intros * ? IHm ? IHt ? ?.
      cbn in *.
      eapply convne_meta_conv ; [econstructor|..] ; refold.
      + eauto.
      + eauto.
      + now asimpl.
      + reflexivity.
    - intros * ? IHn ? IHP ? IHz ? IHs *.
      cbn.
      eapply convne_meta_conv ; [econstructor|..] ; refold.
      + eauto.
      + now eapply (IHP _ (wk_up tNat ρ)).
      + eapply convtm_meta_conv.
        * eapply IHz.
        * now bsimpl.
        * reflexivity.
      + eapply convtm_meta_conv.
        * eapply IHs.
        * unfold elimSuccHypTy.
          now bsimpl.
        * reflexivity.
      + now bsimpl.
      + now bsimpl.
    - intros * ? IHe ? IHP *.
      cbn.
      eapply convne_meta_conv ; [econstructor|..] ; refold.
      + eauto.
      + now eapply (IHP _ (wk_up tEmpty ρ)).
      + now bsimpl.
      + now bsimpl.
    - intros * ? IH *; cbn.
      econstructor; now eapply IH.
    - intros ??? A? ? IH *; cbn.
      rewrite (subst_ren_wk_up (A:=A)).
      econstructor; now eapply IH.
    - intros * ? IHe ? IHp **; erewrite <-2!wk_idElim, subst_ren_wk_up2.
      econstructor; eauto.
      + rewrite 2!(wk_up_wk1 ρ).
        eapply IHp; constructor; tea.
      + rewrite wk_refl, <- subst_ren_wk_up2; eauto.
    - intros.
      econstructor.
      + eauto.
      + eauto using credalg_wk.
      + gen_typing. 
    - intros.
      econstructor.
      1-3: eauto using credalg_wk.
      now eauto.
    - intros * ? ? ? IHB ? ?.
      cbn.
      econstructor.
      1: now eauto.
      now eapply IHB with(ρ := wk_up _ ρ).
    - now econstructor.
    - now econstructor.
    - now econstructor.
    - now econstructor.
    - intros * ? ? ? IH ? ?.
      cbn.
      econstructor.
      1-2: gen_typing.
      specialize IH with(ρ := wk_up _ ρ).
      cbn in *.
      assert (eq: forall t, t⟨ρ⟩⟨↑⟩ = t⟨↑⟩⟨up_ren ρ⟩) by now asimpl.
      do 2 rewrite eq.
      apply IH.
    - intros * ??? IHB *. 
      do 2 rewrite <- wk_sig.
      econstructor.
      1: now eauto.
      now eapply IHB.
    - intros * ??? IHfst ? IHsnd *.
      rewrite <- wk_sig.
      econstructor.
      1,2: gen_typing.
      1: eauto.
      rewrite wk_fst, <- subst_ren_wk_up; eauto.
    - intros; econstructor; eauto.
    - intros; econstructor; eauto.
    - intros.
      econstructor.
      + eauto.
      + now eapply isPosType_ren.
  Qed.

  Corollary algo_conv_shift : AlgoConvInductionConcl
      (fun (Γ : context) (A B : term) => forall T, [Γ,, T |-[al] A⟨↑⟩ ≅ B⟨↑⟩])
      (fun (Γ : context) (A B : term) => forall T, [Γ,, T |-[al] A⟨↑⟩ ≅h B⟨↑⟩])
      (fun (Γ : context) (A m n : term) => forall T, [Γ,, T |-[al] m⟨↑⟩ ~ n⟨↑⟩ ▹ A⟨↑⟩])
      (fun (Γ : context) (A m n : term) => forall T, [Γ,, T |-[al] m⟨↑⟩ ~h n⟨↑⟩ ▹ A⟨↑⟩])
      (fun (Γ : context) (A t u : term) => forall T, [Γ,, T |-[al] t⟨↑⟩ ≅ u⟨↑⟩ : A⟨↑⟩])
      (fun (Γ : context) (A t u : term) => forall T, [Γ,, T |-[al] t⟨↑⟩ ≅h u⟨↑⟩ : A⟨↑⟩]).
  Proof.
    red.
    repeat match goal with |- _ × _ => split end.
    all: intros Γ * Hty T.
    all: eapply algo_conv_wk in Hty.
    all: specialize (Hty _ (@wk1 Γ T)).
    all: repeat rewrite <- (extRen_term _ _ (@wk1_ren Γ T)) ; refold.
    all: now eapply Hty.
  Qed.

End ConvWk.


(** ** Relation to weak-head normal forms *)

(** We show that the predicates that should apply only to weak-head normal forms/neutrals
indeed imply that the relevant arguments are such weak-head normal forms/neutrals. *)
Section AlgoConvWh.

  Let PTyEq (Γ : context) (A B : term) := True.
  Let PTyRedEq (Γ : context) (A B : term) := 
    isType A × isType B.
  Let PNeEq (Γ : context) (A t u : term) := 
    whne t × whne u.
  Let PNeRedEq (Γ : context) (A t u : term) :=
    [× whne t, whne u & whnf A].
  Let PTmEq (Γ : context) (A t u : term) := True.
  Let PTmRedEq (Γ : context) (A t u : term) := 
    [× whnf t, whnf u & isType A].

  Theorem algo_conv_wh :
    AlgoConvInductionConcl PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
  Proof.
    subst PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq; cbn.
    apply AlgoConvInduction.
    all: intros ; prod_splitter ; prod_hyp_splitter.
    all: try solve [now constructor].
    all: gen_typing.
  Qed.
End AlgoConvWh.

(** ** Determinism: there is at most one inferred type *)

Section AlgoConvDet.

Import AlgorithmicTypedConvData.

Let PTyEq (Γ : context) (A B : term) := True.
Let PTyRedEq (Γ : context) (A B : term) := True.
Let PNeEq (Γ : context) (A t u : term) := 
  forall A' u', [Γ |-[al] t ~ u' ▹ A'] -> A' = A.
Let PNeRedEq (Γ : context) (A t u : term) :=
  forall A' u', [Γ |-[al] t ~h u' ▹ A'] -> A' = A.
Let PTmEq (Γ : context) (A t u : term) := True.
Let PTmRedEq (Γ : context) (A t u : term) := True.

Theorem algo_conv_det :
  AlgoConvInductionConcl PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
Proof.
  subst PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq; cbn.
  apply AlgoConvInduction.
  all: try easy.
  - intros * ? * Hconv.
    inversion Hconv ; subst ; clear Hconv.
    now eapply in_ctx_inj.
  - intros * ? IH ? ? ?? Hconv.
    inversion Hconv ; subst ; clear Hconv ; refold.
    apply IH in H6.
    now inversion H6.
  - intros * ? IH ?????? ?? Hconv.
    inversion Hconv ; subst ; clear Hconv ; refold.
    now reflexivity.
  - intros * ? IH ?? ?? Hconv.
    inversion Hconv ; subst ; clear Hconv ; refold.
    now reflexivity.
  - intros * ? IH ?? Hconv.
    inversion Hconv; subst; clear Hconv; refold.
    apply IH in H3.
    now inversion H3.
  - intros * ? IH ?? Hconv.
    inversion Hconv; subst; clear Hconv; refold.
    apply IH in H3.
    now inversion H3.
  - intros * _ * _ * _ * ? ? ? _ ? _ * Hconv.
    inversion Hconv; now subst.
  - intros * ? IH ???? Hconv.
    inversion Hconv ; subst ; clear Hconv ; refold.
    eapply IH in H2 as ->.
    now eapply whred_det.
Qed.

End AlgoConvDet.

(** ** Stability of algorithmic conversion by type/term expansion *)

  Lemma algo_conv_ty_expand Γ A A' B B':
    [A ⤳* A'] -> [B ⤳* B'] -> [Γ |-[al] A' ≅ B'] -> [Γ |-[al] A ≅ B].
  Proof.
    intros ?? Hconv.
    inversion Hconv ; subst ; clear Hconv ; refold.
    econstructor ; [..|eassumption].
    all: now etransitivity.
  Qed.

  Lemma algo_conv_tm_expand Γ A A' t t' u u':
    [A ⤳* A'] -> [t ⤳* t'] -> [u ⤳* u'] -> [Γ |-[al] t' ≅ u' : A'] -> [Γ |-[al] t ≅ u : A].
  Proof.
    intros ??? Hconv.
    inversion Hconv ; subst ; clear Hconv ; refold.
    econstructor ; [..|eassumption].
    all: now etransitivity.
  Qed.

(** Algorithmic conversion implies normalisation *)
Section AlgoConvNorm.
  
  Let PTyEq (Γ : context) (A B : term) := dnorm_ty Γ A.
  Let PTyRedEq (Γ : context) (A B : term) := dnf_ty Γ A.
  Let PNeEq (Γ : context) (A t u : term) := dneu Γ A t.
  Let PNeRedEq (Γ : context) (A t u : term) := dneu_red Γ A t.
  Let PTmEq (Γ : context) (A t u : term) := dnorm_tm Γ A t.
  Let PTmRedEq (Γ : context) (A t u : term) := dnf_tm Γ A t.

  Lemma algo_conv_dnorm :
    AlgoConvInductionConcl PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
  Proof.
    subst PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
    apply AlgoConvInduction ; cbn.
    all: intros ; now econstructor.
  Qed.

End AlgoConvNorm.

(** From this, we deduce that completeness of algorithmic typing wrt. declarative typing
  implies normalisation, through reflexivity of declarative typing. We can combine this later
  with the consequence of the logical relation to obtain deep normalisation. *)

Section CompleteNormalisation.
  Import BundledIntermediateData.

  #[refine]Instance CompleteAlgoNormalisation
    `{! ConvImplies de al} :
    DeepNormalisation de := {}.
  Proof.
    - intros * Hty.
      eapply algo_conv_dnorm.
      now eapply TermRefl, tm_conv_compl in Hty.
    - intros * Hty.
      eapply algo_conv_dnorm.
      now eapply TypeRefl, ty_conv_compl in Hty.
  Qed.

End CompleteNormalisation.

(** ** Stability of algorithmic conversion by context and type change *)

(** If the input context and input type (when there is one) are changed to convertible
ones, algorithmic conversion still holds, possibly with a different output type
(when there is one). *)

Section AlgoConvConv.
  Context `{!TypingSubst de} `{!TypeReductionComplete de} `{!TypeConstructorsInj de}.

  Let PTyEq' (Γ : context) (A B : term) := forall Γ',
    [|-[de] Γ' ≅ Γ] ->
    [Γ' |-[al] A ≅ B].
  Let PTyRedEq' (Γ : context) (A B : term) := forall Γ',
    [|-[de] Γ' ≅ Γ] ->
    [Γ' |-[al] A ≅h B].
  Let PNeEq' (Γ : context) (A t u : term) := forall Γ',
    [|-[de] Γ' ≅ Γ] ->
    ∑ A', [Γ' |-[al] t ~ u ▹ A'] × [Γ' |-[de] A' ≅ A].
  Let PNeRedEq' (Γ : context) (A t u : term) := forall Γ',
    [|-[de] Γ' ≅ Γ] ->
    ∑ A', [× [Γ' |-[al] t ~h u ▹ A'], isType A' & [Γ' |-[de] A' ≅ A]].
  Let PTmEq' (Γ : context) (A t u : term) := forall Γ' A',
    [|-[de] Γ' ≅ Γ] -> [Γ' |-[de] A ≅ A'] ->
    [Γ' |-[al] t ≅ u : A'].
  Let PTmRedEq' (Γ : context) (A t u : term) := forall Γ' A',
    [|-[de] Γ' ≅ Γ] ->  isType A' -> [Γ' |-[de] A ≅ A'] ->
    [Γ' |-[al] t ≅h u : A'].

  Theorem bundled_conv_conv :
    BundledConvInductionConcl PTyEq' PTyRedEq' PNeEq' PNeRedEq' PTmEq' PTmRedEq'.
  Proof.
    subst PTyEq' PTyRedEq' PNeEq' PNeRedEq' PTmEq' PTmRedEq'.
    apply BundledConvInduction ; cbn in *.
    - intros * ??? IH **.
      econstructor ; tea.
      now eapply IH.
    - intros * ? IHA ? IHB ? H **.
      econstructor.
      1: now eapply IHA.
      eapply IHB.
      econstructor ; tea.
      econstructor.
      eapply stability ; tea.
      destruct IHA.
      now boundary.
    - now econstructor.
    - now econstructor.
    - now econstructor.
    - intros * ? ihA ? ihB ? h **.
      econstructor.
      1: now eapply ihA.
      eapply ihB.
      econstructor ; tea.
      econstructor.
      eapply stability ; tea.
      destruct ihA.
      now boundary.
    - intros * ? ihA ? ihx ? ihy ? h **.
      econstructor; [now eapply ihA| eapply ihx | eapply ihy]; tea.
      1,2: eapply stability; tea; now eapply lrefl.
    - intros * ?? ? IHM **.
      edestruct IHM as [[? []]] ; tea.
      now econstructor.
    - intros * HΓ **.
      eapply in_ctx_conv_r in HΓ as [? []] ; tea.
      eexists ; split.
      1: now econstructor.
      eassumption.
    - intros * ? IHm Ht [IHt []%boundary] **.
      edestruct IHm as [[? [?? (?&?&[->])%conv_prod_r]] ?] ; tea.
      eexists ; split.
      + econstructor ; tea.
        now eapply IHt.
      + eapply typing_subst1 ; tea.
        econstructor.
        now eapply stability.
    - intros * ? IHn ? IHP ? IHz ? IHs **.
      edestruct IHn as [[? [?? ->%conv_nat_r]]?] ; tea.
      eexists ; split.
      1: econstructor.
      + eauto.
      + eapply IHP.
        econstructor ; tea ; do 2 econstructor ; boundary.
      + eapply IHz ; tea.
        econstructor.
        eapply stability ; tea.
        destruct IHz.
        boundary.
      + eapply IHs ; tea.
        eapply TypeRefl ; refold.
        eapply stability ; tea.
        destruct IHs.
        boundary.
      + econstructor.
        destruct IHP.
        eapply stability ; tea.
        eapply typing_subst1.
        all: now boundary.
    - intros * ? IHe ? IHP **.
      edestruct IHe as [[? [?? ->%conv_empty_r]]?] ; tea.
      eexists ; split.
      1: econstructor.
      + eauto.
      + eapply IHP.
        econstructor ; tea ; do 2 econstructor ; boundary.
      + econstructor.
        destruct IHP.
        eapply stability ; tea.
        eapply typing_subst1.
        all: now boundary.
    - intros * ? [ih ?] [hm hn] ??.
      edestruct ih as [?[?? [?[? [->] ]]%conv_sig_r]]; tea.
      eexists; split; tea; now econstructor.
    - intros * ? [ih ?] **.
      edestruct ih as [?[?? [?[? [->] ]]%conv_sig_r]]; tea.
      eexists; split.
      1: now econstructor.
      eapply typing_subst1 ; tea.
      do 3 econstructor.
      1: eapply stability ; boundary.
      symmetry.
      econstructor ; tea.
      boundary.
    - intros * ? [ih ?] ? [ihP] ? [ihhr] [hm hn] **.
      assert (well_typed (ta := de) Γ' (tIdElim A x P hr y e)) as hm'
        by (edestruct hm ; eexists ; now eapply stability).
      assert (well_typed (ta := de) Γ' (tIdElim A' x' P' hr' y' e')) as hn'
        by (edestruct hn ; eexists ; now eapply stability).
      edestruct ih as (?&[[? ihe]%dup]) ; tea.
      pose proof hm' as [? [? [[] ]]%termGen'].
      pose proof hn' as [? [? [[] ]]%termGen'].
      eapply algo_conv_sound in ihe.
      2-3: now eexists.
      epose proof (conv_neu_typing_unique _ _ _ _ ihe) as [].
      epose proof (idElimConv hm' hn') as (?&?&?&[]) ; tea ; subst.
      1: gen_typing.
      eexists; split.
      1: econstructor; tea; eauto.
      + eapply ihP.
        symmetry.
        eapply idElimMotiveCtxConv ; tea.
        * econstructor. boundary.
        * now econstructor.
      + eapply ihhr ; tea.
        econstructor.
        eapply typing_subst2 ; tea.
        1: boundary.
        eapply typing_meta_conv.
        1: econstructor ; boundary.
        cbn.
        now bsimpl.
      + eapply TypeRefl; refold; now boundary.
    - intros * ? IHm **.
      edestruct IHm as [[A'' []] ?]; tea.
      assert [Γ' |-[de] A' ≅ A''] as HconvA'.
      {
        eapply conv_red_l ; tea.
        now symmetry.
      }
      pose proof HconvA' as [? []]%red_ty_complete_l.
      2:{
        eapply type_isType ; tea.
        now boundary.
      }
      eexists ; split.
      + econstructor.
        1: eauto.
        1: now eapply redty_red.
        gen_typing.
      + eassumption.
      + symmetry ; etransitivity ; tea.
        now eapply RedConvTyC.
    - intros * ? ? ? []%algo_conv_wh IH [] ? A'' **.
      assert [Γ' |-[de] A' ≅ A''] as HconvA'
        by now eapply conv_red_l.
      pose proof HconvA' as [? []]%red_ty_complete_l ; tea.
      econstructor ; tea.
      1: now eapply redty_red.
      eapply IH ; tea.
      etransitivity ; tea.
      now eapply RedConvTyC.
    - intros * ? [IHA HconvA] ? IHB ? ? ? * ? ? ->%conv_univ_l ; tea.
      econstructor.
      + eapply IHA ; tea.
        do 2 econstructor.
        boundary.
      + assert [Γ' |-[de] A].
        {
          eapply stability ; tea.
          econstructor.
          now boundary.
        }
        eapply IHB ; tea.
        all: econstructor ; tea.
        all: econstructor ; tea.
        econstructor.
        all: gen_typing.
    - intros * ??? * ?? ->%conv_univ_l ; tea.
      now econstructor.
    - intros * ??? * ?? ->%conv_nat_l ; tea.
      now econstructor.
    - intros * ? IH [] * ?? ->%conv_nat_l ; tea.
      econstructor.
      eapply IH ; tea.
      do 2 econstructor ; boundary.
    - intros * ??? * ?? ->%conv_univ_l ; tea.
      now econstructor.
    - intros * ? ? ? IHf ? ? ? * ? ? (?&?&[->])%conv_prod_l ; tea.
      econstructor ; tea.
      eapply IHf ; tea.
      now econstructor.
    - intros * ? [ihA] ? [ihB] [] * ?? ->%conv_univ_l ; tea.
      econstructor.
      + eapply ihA ; tea.
        do 2 econstructor ; boundary.
      + assert [ |-[ de ] Γ',, A ≅ Γ,, A].
        {
          econstructor; tea; eapply stability; tea.
          eapply lrefl; now econstructor.
        }
      eapply ihB; tea.
      do 2 constructor; boundary.
    - intros * ??? [ihA] ? [ihB] [] * ?? [?[?[->]]]%conv_sig_l ; tea.
      econstructor; tea.
      1: eapply ihA; tea; now symmetry.
      eapply ihB; tea.
      eapply typing_subst1; tea.
      do 2 econstructor.
      now eapply stability.
    - intros * ? [ihA] ? [ihx] ? [ihy] ? * ? ? ->%conv_univ_l ; tea.
      assert [Γ' |-[de] A ≅ A] by (eapply stability; tea; eapply lrefl; now econstructor).
      econstructor; tea.
      + eapply ihA; tea; constructor; eapply stability; tea; now boundary.
      + eapply ihx; tea.
      + eapply ihy; tea.
    - intros * ??? * ? ? [?[?[? [->]]]]%conv_id_l ; tea.
      now econstructor.
    - intros * ? IHm HtyP ? ? ? * ? HtyA' HconvN.
      edestruct IHm as [[? []] ?] ; tea.
      unshelve eapply ty_conv_inj in HconvN.
      1: now gen_typing.
      1: assumption.
      econstructor ; tea.
      destruct HtyP, HtyA'.
      all: cbn in HconvN ; try now exfalso.
      all: now constructor.
  Qed.

  Let PTyEq (Γ : context) (A B : term) := True.
  Let PTyRedEq (Γ : context) (A B : term) := True.
  Let PNeEq (Γ : context) (A t u : term) := forall Γ',
    [|-[de] Γ' ≅ Γ] ->
    (well_typed (ta := de) Γ t) ->
    (well_typed (ta := de) Γ u) ->
    ∑ A', [Γ' |-[al] t ~ u ▹ A'] × [Γ' |-[de] A' ≅ A].
  Let PNeRedEq (Γ : context) (A t u : term) := forall Γ',
    [|-[de] Γ' ≅ Γ] ->
    (well_typed (ta := de) Γ t) ->
    (well_typed (ta := de) Γ u) ->
    ∑ A', [× [Γ' |-[al] t ~h u ▹ A'], isType A' & [Γ' |-[de] A' ≅ A]].
  Let PTmEq (Γ : context) (A t u : term) := forall Γ' A',
    [|-[de] Γ' ≅ Γ] -> [Γ' |-[de] A ≅ A'] ->
    [Γ |-[de] t : A] -> [Γ |-[de] u : A ] ->
    [Γ' |-[al] t ≅ u : A'].
  Let PTmRedEq (Γ : context) (A t u : term) := forall Γ' A',
    [|-[de] Γ' ≅ Γ] -> isType A' -> [Γ' |-[de] A ≅ A'] ->
    [Γ |-[de] t : A] -> [Γ |-[de] u : A ] ->
    [Γ' |-[al] t ≅h u : A'].

  Corollary algo_conv_conv : AlgoConvInductionConcl PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
  Proof.
    subst PTyEq PTyRedEq PNeEq PNeRedEq PTmEq PTmRedEq.
    pose proof bundled_conv_conv as Hind.
    subst PTyEq' PTyRedEq' PNeEq' PNeRedEq' PTmEq' PTmRedEq'.
    unfold BundledConvInductionConcl, AlgoConvInductionConcl in *.
    unshelve (repeat (split ; [destruct Hind as [Hind _] ; shelve | destruct Hind as [_ Hind]])).
    1-2: now constructor.
    all: intros * Hconv ; intros ; eapply Hind ; tea.
    all: match goal with H : ConvCtx _ _ |- _ => symmetry in H ; apply boundary_ctx_conv_l in H end.
    all: split ; tea.
    all: try solve [now apply algo_conv_wh in Hconv as []].
    all: now boundary.
  Qed.

End AlgoConvConv.

(** ** Lifting of algorithmic conversion from terms at the universe to types *)

Section TermTypeConv.
  Context `{!TypingSubst de} `{!TypeReductionComplete de} `{!TypeConstructorsInj de}.

  Let PTyEq (Γ : context) (A B : term) := True.
  Let PNeEq (Γ : context) (A t u : term) := True.
  Let PTmEq (Γ : context) (A t u : term) :=
      [A ⤳* U] ->
      [Γ |-[al] t ≅ u].
  Let PTmRedEq (Γ : context) (A t u : term) :=
    A = U ->
    [Γ |-[al] t ≅h u].

  Theorem algo_conv_tm_ty :
  AlgoConvInductionConcl PTyEq PTyEq PNeEq PNeEq PTmEq PTmRedEq.
  Proof.
    subst PTyEq PNeEq PTmEq PTmRedEq.
    apply AlgoConvInduction.
    all: try solve [now constructor].
    - intros * ? ? ? Hconv IH ?.
      econstructor ; tea.
      eapply IH, whred_det ; tea.
      2: gen_typing.
      eapply algo_conv_wh in Hconv as [].
      now gen_typing.
    - intros.
      congruence.
    - intros.
      congruence.
    - intros.
      congruence.
    - intros; congruence.
    - intros; congruence.
    - intros * H.
      econstructor ; tea.
      all: now apply algo_conv_wh in H.
  Qed.

End TermTypeConv.