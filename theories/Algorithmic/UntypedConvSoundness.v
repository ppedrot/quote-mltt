(** * LogRel.Algorithmic.UntypedConvSoundness: untyped conversion implies declarative typing. *)

From LogRel Require Import Utils Syntax.All GenericTyping DeclarativeTyping AlgorithmicJudgments.
From LogRel Require Import Sections.
From LogRel.TypingProperties Require Import PropertiesDefinition DeclarativeProperties SubstConsequences TypeInjectivityConsequences NeutralConvProperties.
From LogRel.Algorithmic Require Import Bundled TypedConvProperties.

Import DeclarativeTypingProperties AlgorithmicTypedConvData AlgorithmicTypingData.

(** ** Relation to weak-head normal forms *)

Section UAlgoConvWh.

  Let PEq (A B : term) := True.
  Let PNeEq (m n : term) := 
    whne m × whne n.
  Let PRedEq (t u : term) := 
    whnf t × whnf u.

  Theorem algo_uconv_wh :
    UAlgoConvInductionConcl PEq PRedEq PNeEq.
  Proof.
    subst PEq PRedEq PNeEq ; cbn.
    apply UAlgoConvInduction.
    all: intros ; prod_splitter ; prod_hyp_splitter.
    all: now constructor.
  Qed.

End UAlgoConvWh.

Notation "[ A ≅ B ]" := (UConvAlg A B).
Notation "[ A ≅h B ]" := (UConvRedAlg A B).
Notation "[ m ~ n ]" := (UConvNeuAlg m n).

(** ** Extra preservation lemmas for untyped conversion *)

Section PremisePreserve.
  Context `{!TypingSubst de} `{!TypeConstructorsInj de} `{!TypeReductionComplete de}.

  Lemma LamCongUAlg_prem0_red Γ T A t A' t' :
    [Γ |-[ de ] tLambda A t : T] × [Γ |-[ de ] tLambda A' t' : T] ->
    ∑ A'' B, [× [T ⤳* tProd A'' B], [Γ ,, A'' |-[de] t : B] & [Γ ,, A'' |-[de] t' : B]].
  Proof.
    intros [[? [[B [->]] Hconv]]%termGen' [? [[B' [->]] Hconv']]%termGen'].
    eapply red_compl_prod_l in Hconv as (A''&B''&[Hred]).
    edestruct prod_ty_inj.
    {
     etransitivity ; tea.
     now eapply RedConvTyC.
    }

    do 2 eexists ; split.
    - now eapply redty_sound.
    - now econstructor ; [eapply stability1|..] ; cycle 1.
    - now econstructor ; [eapply stability1|..].
  Qed.

  Lemma LamCongUAlg_prem0 Γ T A t A' t' :
    [Γ |-[ de ] tLambda A t : T] × [Γ |-[ de ] tLambda A' t' : T] ->
    ∑ B, [× [Γ ,, A |-[de] t : B], [Γ ,, A |- t' : B] & [Γ |-[de] tProd A B ≅ T]].
  Proof.
    intros [[? [[B [->]] Hconv]]%termGen' [? [[B' [->]] Hconv']]%termGen'].
    edestruct prod_ty_inj.
    {
     etransitivity ; [..|symmetry] ; [eapply Hconv'|eapply Hconv].
    }

    eexists ; split ; tea.
    econstructor ; tea.
    now eapply stability1.
  Qed.

  Lemma LamCongUAlg_concl Γ T A t A' t' B :
    [Γ |-[ de ] tLambda A t : T] × [Γ |-[ de ] tLambda A' t' : T] ->
    [Γ ,, A |-[de] t ≅ t' : B] ->
    [Γ |-[de] tProd A B ≅ T] ->
    [Γ |-[de] tLambda A t ≅ tLambda A' t' : T].
  Proof.
    intros [[? []]%LamCongUAlg_prem0 [_ Ht']]%dup ??.
    econstructor ; tea.
    econstructor ; tea.
    2: constructor.
    1-2: eapply prod_ty_inv ; boundary.
    eapply termGen' in Ht' as (?&[? [->]]&?).
    eapply prod_ty_inj.
    etransitivity ; tea.
    now symmetry.
  Qed.

  Lemma LamNeUAlg_prem0_red Γ T A t n' :
    [Γ |-[ de ] tLambda A t : T] × [Γ |-[ de ] n' : T] ->
    ∑ A'' B, [× [T ⤳* tProd A'' B], [Γ ,, A'' |- t : B] & [Γ ,, A'' |- eta_expand n' : B]].
  Proof.
    intros [[? [[B [->]] Hconv]]%termGen' Hn].
    eapply red_compl_prod_l in Hconv as (A''&B''&[Hred]).
    do 2 eexists ; split.

    - now eapply redty_sound.
    - now econstructor ; [eapply stability1 |..].
    - eapply typing_eta' ; econstructor ; tea.
      now eapply RedConvTyC.
  Qed.

  Lemma LamNeUAlg_prem0 Γ T A t n' :
    [Γ |-[ de ] tLambda A t : T] × [Γ |-[ de ] n' : T] ->
    ∑ B, [× [Γ ,, A |-[de] t : B], [Γ ,, A |- eta_expand n' : B] & [Γ |-[de] tProd A B ≅ T]].
  Proof.
    intros [[? [[B [->]] Hconv]]%termGen' ?].

    eexists ; split ; tea.
    eapply typing_eta'.
    now econstructor.
  Qed.

  Lemma LamNeUAlg_concl Γ T A t n' B :
    [Γ |-[ de ] tLambda A t : T] × [Γ |-[ de ] n' : T] ->
    [Γ ,, A |-[de] t ≅ eta_expand n' : B] ->
    [Γ |-[de] tProd A B ≅ T] ->
    [Γ |-[de] tLambda A t ≅ n' : T].
  Proof.
    intros [[? []]%LamNeUAlg_prem0 [_ Ht']]%dup ??.
    econstructor ; tea.
    etransitivity.
    2: eapply TermFunEta ; refold ; now econstructor.
    econstructor ; tea.
    2-3: constructor.
    all: eapply prod_ty_inv ; boundary.
  Qed.

  Lemma NeLamUAlg_prem0_red Γ T n A' t' :
    [Γ |-[ de ] n : T] × [Γ |-[ de ] tLambda A' t' : T] ->
    ∑ A'' B, [× [T ⤳* tProd A'' B], [Γ ,, A'' |- eta_expand n : B] & [Γ ,, A'' |- t' : B]].
  Proof.
    intros [Hn [? [[B [->]] Hconv]]%termGen'].
    eapply red_compl_prod_l in Hconv as (A''&B''&[Hred]).
    do 2 eexists ; split.

    - now eapply redty_sound.
    - eapply typing_eta' ; econstructor ; tea.
      now eapply RedConvTyC.
    - now econstructor ; [eapply stability1 | ..].
  Qed.

  Lemma NeLamUAlg_prem0 Γ T n A' t' :
    [Γ |-[ de ] n : T] × [Γ |-[ de ] tLambda A' t' : T] ->
    ∑ B, [× [Γ ,, A' |-[de] eta_expand n : B], [Γ ,, A' |- t' : B] & [Γ |-[de] tProd A' B ≅ T]].
  Proof.
    intros [? [? [[B [->]] Hconv]]%termGen'].

    eexists ; split ; tea.
    eapply typing_eta'.
    now econstructor.
  Qed.

  Lemma NeLamUAlg_concl Γ T n A' t' B :
    [Γ |-[ de ] n : T] × [Γ |-[ de ] tLambda A' t' : T] ->
    [Γ ,, A' |-[de] eta_expand n ≅ t' : B] ->
    [Γ |-[de] tProd A' B ≅ T] ->
    [Γ |-[de] n ≅ tLambda A' t' : T].
  Proof.
    intros [[? []]%NeLamUAlg_prem0 [Ht _]]%dup ??.
    econstructor ; tea.
    etransitivity.
    1: symmetry ; eapply TermFunEta ; refold ; now econstructor.
    econstructor ; tea.
    2-3: constructor.
    all: eapply prod_ty_inv ; boundary.
  Qed.

  Lemma PairCongUAlg_prem0_red Γ T A B p q A' B' p' q' :
    [Γ |-[ de ] tPair A B p q : T] × [Γ |-[ de ] tPair A' B' p' q' : T] ->
    ∑ A'' B'', [T ⤳* tSig A'' B''] × ([Γ |- p : A''] × [Γ |- p' : A'']).
  Proof.
    intros [[? [[->] Hconv]]%termGen' [? [[->] Hconv']]%termGen'].
    eapply red_compl_sig_l in Hconv as (A''&B''&[Hred]).

    edestruct sig_ty_inj.
    {
      etransitivity ; tea.
      now eapply RedConvTyC.
    }
    do 2 eexists ; split ; [..|split].
    - now eapply redty_sound.
    - now econstructor.
    - now econstructor.
  Qed.

  Lemma PairCongUAlg_prem1_red Γ A B p q A' B' p' q' A'' B'' T :
    [Γ |-[ de ] tPair A B p q : T] × [Γ |-[ de ] tPair A' B' p' q' : T] ->
    [T ⤳* tSig A'' B''] ->
    [Γ |-[de] p ≅ p' : A''] ->
    [Γ |- q : B''[(tFst (tPair A B p q))..]] × [Γ |- q' : B''[(tFst (tPair A B p q))..]].
  Proof.
    intros * [[? [[->] Hconv]]%termGen' [? [[->] Hconv']]%termGen'] ? ?.
    eapply (TypeTrans (B := T)), sig_ty_inj in Hconv as [].
    2: eapply RedConvTyC, subject_reduction_type ; boundary.
    eapply (TypeTrans (B := T)), sig_ty_inj in Hconv' as [].
    2: eapply RedConvTyC, subject_reduction_type ; boundary.
    
    assert [Γ |-[de] p' : A]
      by (econstructor ; tea ; etransitivity ; tea ; now symmetry).
    assert [Γ |-[ de ] p ≅ tFst (tPair A B p q) : A] by
      (econstructor ; symmetry ; now econstructor).

    split.
    all: econstructor ; tea.
    all: eapply typing_subst1 ; tea.
    etransitivity.
    all: eapply TermConv ; refold ; tea.
    3: etransitivity ; tea.
    all: now symmetry.
  Qed.

  Lemma PairCongUAlg_prem0 Γ T A B p q A' B' p' q' :
    [Γ |-[ de ] tPair A B p q : T] × [Γ |-[ de ] tPair A' B' p' q' : T] ->
    [Γ |- p : A] × [Γ |- p' : A].
  Proof.
    intros * [[? [[->] Hconv]]%termGen' [? [[->] Hconv']]%termGen'].
    split ; tea.
    econstructor ; tea.
    eapply sig_ty_inj.
    etransitivity ; tea.
    now symmetry.
  Qed.

  Lemma PairCongUAlg_prem1 Γ T A B p q A' B' p' q' :
    [Γ |-[ de ] tPair A B p q : T] × [Γ |-[ de ] tPair A' B' p' q' : T] ->
    [Γ |-[de] p ≅ p' : A] ->
    [Γ |- q : B[p..]] × [Γ |- q' : B[p..]].
  Proof.
    intros * [[? [[->] Hconv]]%termGen' [? [[->] Hconv']]%termGen'].
    split ; tea.
    econstructor ; tea.
    symmetry.
    eapply typing_subst1 ; tea.
    eapply sig_ty_inj.
    etransitivity ; tea.
    now symmetry.
  Qed.

  Lemma PairCongUAlg_concl Γ T A B p q A' B' p' q' :
    [Γ |-[ de ] tPair A B p q : T] × [Γ |-[ de ] tPair A' B' p' q' : T] ->
    [Γ |-[de] p ≅ p' : A] ->
    [Γ |-[de] q ≅ q' : B[p..]] ->
    [Γ |-[de] tPair A B p q ≅ tPair A' B' p' q' : T].
  Proof.
    intros * [[? [[->] Hconv]]%termGen' [? [[->] Hconv']]%termGen'] ??.
    econstructor.
    2: apply Hconv.
    econstructor ; tea.
    1: constructor ; boundary.
    all: eapply sig_ty_inj.
    all: etransitivity ; tea.
    all: now symmetry.
  Qed.

  Lemma PairNeUAlg_prem0_red Γ T A B p q n' :
    [Γ |-[ de ] tPair A B p q : T] × [Γ |-[ de ] n' : T] ->
    ∑ A'' B'', [T ⤳* tSig A'' B''] × ([Γ |- p : A''] × [Γ |- tFst n' : A'']).
  Proof.
    intros [[? [[->] [Hconv Hconv']%dup]]%termGen' ?].
    eapply red_compl_sig_l in Hconv as (?&?&[Hred]).
    
    do 2 eexists ; split ; [..|split].
    - now eapply redty_sound.
    - now econstructor.
    - do 2 econstructor ; tea.
      now eapply RedConvTyC.
  Qed.

  Lemma PairNeUAlg_prem1_red Γ A B p q n' A'' B'' T :
    [Γ |-[ de ] tPair A B p q : T] × [Γ |-[ de ] n' : T] ->
    [T ⤳* tSig A'' B''] ->
    [Γ |-[de] p ≅ tFst n' : A''] ->
    [Γ |- q : B''[(tFst (tPair A B p q))..]] × [Γ |- tSnd n' : B''[(tFst (tPair A B p q))..]].
  Proof.
    intros * [[? [[->] Hconv]]%termGen'?] ? ?.

    assert [Γ |-[de] T ≅ tSig A'' B''] by
      (eapply RedConvTyC, subject_reduction_type ; boundary).
    eapply (TypeTrans (B := T)), sig_ty_inj in Hconv as [] ; tea.
    
    assert [Γ |-[ de ] p ≅ tFst (tPair A B p q) : A] by
      (econstructor ; symmetry ; now econstructor).

    split.
    - econstructor ; tea.
      now eapply typing_subst1.
    - econstructor.
      1: now do 2 econstructor.
      eapply typing_subst1.
      2: constructor ; boundary.
      etransitivity ; tea.
      econstructor.
      all: now symmetry.
  Qed.

  Lemma PairNeUAlg_prem0 Γ T A B p q n' :
    [Γ |-[ de ] tPair A B p q : T] × [Γ |-[ de ] n' : T] ->
    [Γ |- p : A] × [Γ |- tFst n' : A].
  Proof.
    intros * [[? [[->] Hconv]]%termGen' ?].
    split ; tea.
    do 2 (econstructor ; tea).
    now symmetry.
  Qed.

  Lemma PairNeUAlg_prem1 Γ T A B p q n' :
    [Γ |-[ de ] tPair A B p q : T] × [Γ |-[ de ] n' : T] ->
    [Γ |-[de] p ≅ tFst n' : A] ->
    [Γ |- q : B[p..]] × [Γ |- tSnd n' : B[p..]].
  Proof.
    intros * [[? [[->] Hconv]]%termGen' ?].
    split ; tea.
    econstructor ; tea.
    1: do 2 (econstructor ; tea).
    1: now symmetry.
    symmetry.
    eapply typing_subst1 ; tea.
    constructor.
    eapply sig_ty_inv.
    boundary.
  Qed.

  Lemma PairNeUAlg_concl Γ T A B p q n' :
    [Γ |-[ de ] tPair A B p q : T] × [Γ |-[ de ] n' : T] ->
    [Γ |-[de] p ≅ tFst n' : A] ->
    [Γ |-[de] q ≅ tSnd n' : B[p..]] ->
    [Γ |-[de] tPair A B p q ≅ n' : T].
  Proof.
    intros * [[? [[->] Hconv]]%termGen' ?] ??.
    econstructor ; tea.
    etransitivity.
    2: do 2 (econstructor ; tea) ; now symmetry.
    econstructor ; eauto.
    all: eapply sig_ty_inj.
    all: etransitivity ; tea.
    all: now symmetry.
  Qed.

  Lemma NePairUAlg_prem0_red Γ T n A' B' p' q' :
    [Γ |-[ de ] n : T] × [Γ |-[ de ] tPair A' B' p' q' : T] ->
    ∑ A'' B'', [T ⤳* tSig A'' B''] × ([Γ |- tFst n : A''] × [Γ |- p' : A'']).
  Proof.
    intros [? [? [[->] [Hconv Hconv']%dup]]%termGen'].
    eapply red_compl_sig_l in Hconv as (?&?&[Hred]).
    do 2 eexists ; split ; [..|split].
    - now eapply redty_sound.
    - do 2 econstructor ; tea.
      now eapply RedConvTyC.
    - now econstructor.
  Qed.

  Lemma NePairUAlg_prem1_red Γ n A' B' p' q' A'' B'' T :
    [Γ |-[ de ] n : T] × [Γ |-[ de ] tPair A' B' p' q' : T] ->
    [T ⤳* tSig A'' B''] ->
    [Γ |-[de] tFst n ≅ p' : A''] ->
    [Γ |- tSnd n : B''[(tFst n)..]] × [Γ |- q' : B''[(tFst n)..]].
  Proof.
    intros * [? [? [[->] Hconv]]%termGen'] ? ?.

    assert [Γ |-[de] T ≅ tSig A'' B''] by
      (eapply RedConvTyC, subject_reduction_type ; boundary).
    eapply (TypeTrans (B := T)), sig_ty_inj in Hconv as [] ; tea.

    split.
    - now do 2 econstructor.
    - econstructor ; tea.
      eapply typing_subst1 ; tea.
      econstructor.
      all: now symmetry.
  Qed.

  Lemma NePairUAlg_prem0 Γ T n A' B' p' q' :
    [Γ |-[ de ] n : T] × [Γ |-[ de ] tPair A' B' p' q' : T] ->
    [Γ |- tFst n : A'] × [Γ |- p' : A'].
  Proof.
    intros * [? [? [[->] Hconv]]%termGen'].
    split ; tea.
    do 2 (econstructor ; tea).
    now symmetry.
  Qed.

  Lemma NePairUAlg_prem1 Γ T n A' B' p' q' :
    [Γ |-[ de ] n : T] × [Γ |-[ de ] tPair A' B' p' q' : T] ->
    [Γ |-[de] tFst n ≅ p' : A'] ->
    [Γ |- tSnd n : B'[p'..]] × [Γ |- q' : B'[p'..]].
  Proof.
    intros * [? [? [[->] Hconv]]%termGen'].
    split ; tea.
    econstructor ; tea.
    1: do 2 (econstructor ; tea).
    1: now symmetry.
    eapply typing_subst1 ; tea.
    constructor.
    eapply sig_ty_inv.
    boundary.
  Qed.

  Lemma NePairUAlg_concl Γ T n A' B' p' q' :
    [Γ |-[ de ] n : T] × [Γ |-[ de ] tPair A' B' p' q' : T] ->
    [Γ |-[de] tFst n ≅ p' : A'] ->
    [Γ |-[de] tSnd n ≅ q' : B'[p'..]] ->
    [Γ |-[de] n ≅ tPair A' B' p' q' : T].
  Proof.
    intros * [? [? [[->] Hconv]]%termGen'] ??.
    econstructor ; tea.
    symmetry.
    etransitivity.
    2: do 2 (econstructor ; tea) ; now symmetry.
    econstructor ; eauto.
    5-6: now symmetry. 
    all: eapply sig_ty_inj.
    all: etransitivity ; tea.
    all: now symmetry.
  Qed.

  Lemma AppCongUAlg_bridge Γ T m n t u :
    [Γ |-[de] m ~ n : T] ->
    well_typed Γ (tApp m t) × well_typed Γ (tApp n u) ->
    ∑ A B,
      [Γ |-[de] T ≅ tProd A B] ×
      [Γ |-[ de ] m ~ n : tProd A B].
  Proof.
    intros Hal [[? [? [(A&B&[-> Hm])]]%termGen'] [? [? [(A'&B'&[->])]]%termGen']].
    unshelve epose proof (conv_neu_typing _ _ _ _ _ _ _) ; cycle -3 ; tea.
    do 2 eexists ; split ; tea.
    now econstructor.
  Qed.

  Lemma NatElimCongUAlg_bridge Γ T P hz hs n P' hz' hs' n' :
    [Γ |-[de] n ~ n' : T] ->
    well_typed Γ (tNatElim P hz hs n) × well_typed Γ (tNatElim P' hz' hs' n') ->
    [Γ |-[de] T ≅ tNat] × [Γ |-[ de ] n ~ n' : tNat].
  Proof.
    intros ? [[? [? [[-> ??? Hn]]]%termGen'] [? [? [[->]]]%termGen']].
    unshelve epose proof (conv_neu_typing _ _ _ _ _ _ _) ; cycle -3 ; tea.
    split ; tea.
    now econstructor.
  Qed.

  Lemma EmptyElimCongUAlg_bridge Γ T P n P' n' :
    [Γ |-[de] n ~ n' : T] ->
    well_typed Γ (tEmptyElim P n) × well_typed Γ (tEmptyElim P' n') ->
    [Γ |-[de] T ≅ tEmpty] × [Γ |-[ de ] n ~ n' : tEmpty].
  Proof.
    intros ? [[? [? [[-> ? Hn]]]%termGen'] [? [? [[->]]]%termGen']].
    unshelve epose proof (conv_neu_typing _ _ _ _ _ _ _) ; cycle -3 ; tea.
    split ; tea.
    now econstructor.
  Qed.

  Lemma FstCongUAlg_bridge Γ T m n :
    [Γ |-[de] m ~ n : T] ->
    well_typed Γ (tFst m) × well_typed Γ (tFst n) ->
    ∑ A B, [Γ |-[de] T ≅ tSig A B] × [Γ |-[ de ] m ~ n : tSig A B].
  Proof.
    intros Hal [[? [? [(A&B&[-> Hm])]]%termGen'] [? [? [(A'&B'&[->])]]%termGen']].
    unshelve epose proof (conv_neu_typing _ _ _ _ _ _ _) ; cycle -3 ; tea.
    do 2 eexists ; split ; tea.
    now econstructor.
  Qed.

  Lemma SndCongUAlg_bridge Γ T m n :
    [Γ |-[de] m ~ n : T] ->
    well_typed Γ (tSnd m) × well_typed Γ (tSnd n) ->
    ∑ A B, [Γ |-[de] T ≅ tSig A B] × [Γ |-[ de ] m ~ n : tSig A B].
  Proof.
    intros Hal [[? [? [(A&B&[-> Hm])]]%termGen'] [? [? [(A'&B'&[->])]]%termGen']].
    unshelve epose proof (conv_neu_typing _ _ _ _ _ _ _) ; cycle -3 ; tea.
    do 2 eexists ; split ; tea.
    now econstructor.
  Qed.

  Lemma IdElimCongUAlg_bridge Γ T A x P hr y e A' x' P' hr' y' e' :
    [Γ |-[de] e ~ e' : T] ->
    well_typed Γ (tIdElim A x P hr y e) × well_typed Γ (tIdElim A' x' P' hr' y' e') ->
    ∑ A'' x'' y'', [Γ |-[de] T ≅ tId A'' x'' y''] × [Γ |-[ de ] e ~ e' : tId A'' x'' y''].
  Proof.
    intros Hal [[? [? [[-> ????? He]]]%termGen'] [? [? [[->]]]%termGen']].
    unshelve epose proof (conv_neu_typing _ _ _ _ _ _ _) ; cycle -3 ; tea.
    do 3 eexists ; split ; tea.
    now econstructor.
  Qed.

End PremisePreserve.

(** ** Untyped algorithmic conversion implies declarative conversion *)

Section UConvSound.
  Context `{!TypingSubst de} `{!TypeConstructorsInj de}.

  Lemma uconv_sound_decl :
    UAlgoConvInductionConcl
      (fun t u => 
        (forall Γ, [Γ |-[de] t] × [Γ |-[de] u] -> [Γ |-[de] t ≅ u]) ×
        (forall Γ A, [Γ |-[de] t : A] × [Γ |-[de] u : A] -> [Γ |-[de] t ≅ u : A]))

      (fun t u =>
        (forall Γ, [Γ |-[de] t] × [Γ |-[de] u] -> [Γ |-[de] t ≅ u]) ×
        (forall Γ A, [Γ |-[de] t : A] × [Γ |-[de] u : A] -> [Γ |-[de] t ≅ u : A]))

      (fun m n =>
        forall Γ, well_typed Γ m × well_typed Γ n ->
        ∑ A, [Γ |-[de] m ~ n : A]).
  
  Proof.
    apply UAlgoConvInduction.

    - intros * Ht Hu Ht' [Hty Htm].
      split.
      + intros * [Hconcl]%dup.
        eapply typeConvRed_prem2 in Hconcl ; tea.
        now eapply typeConvRed_concl ; eauto.

      + intros * [Hconcl]%dup.
        eapply termConvRed_prem3 in Hconcl ; tea.
        2: reflexivity.
        eapply termConvRed_concl ; eauto.
        reflexivity.

    - split.
      + now econstructor.
      + intros * [[? [[] ]]%termGen' _].

    - intros * HA [IHA_ty IHA_tm] HB [IHB_ty IHB_tm].
      split.
      + intros ? [Hconcl]%dup.
        eapply typePiCongAlg_prem0 in Hconcl as [Hpre0 []]%dup.
        eapply IHA_ty, typePiCongAlg_prem1 in Hpre0 ; tea.
        now econstructor.

      + intros * [Hconcl [[Hty]%dup]]%dup.

        eapply termGen' in Hty as (?&[->]&Hconv) ; tea.
        econstructor ; tea.
        eapply termPiCongAlg_concl.
        2: eapply IHB_tm, termPiCongAlg_prem1.
        1-2: eapply IHA_tm, termPiCongAlg_prem0.
        all: split ; now eapply ty_conv.
        
    - split.
      1: now constructor.
      intros * [].
      now constructor.

    - split.
      
      + intros * [Hz%type_isType _].
        2: constructor.
        inversion Hz ; inv_whne.

      + intros * [].
        now constructor.

    - intros * ? [? IH].
      split.
    
      + intros * [Hz%type_isType _].
        2: constructor.
        inversion Hz ; inv_whne.

      + intros * [Hconcl [Hty]]%dup.
        
        eapply termGen' in Hty as (?&[->]&?) ; tea.
        econstructor ; tea.
        eapply termSuccCongAlg_concl.
        1: eapply IH, termSuccCongAlg_prem0.
        all: split ; now eapply ty_conv.

    - split.
      1: now econstructor.
      intros * [].
      now constructor.

    - intros * ? [].
      split.
    
      + intros * [Hz%type_isType _].
        2: constructor.
        inversion Hz ; inv_whne.

      + intros * [Hconv]%dup.
        eapply LamCongUAlg_prem0 in Hconv as (?&[]).
        eapply LamCongUAlg_concl ; eauto.

    - intros * ?? [].
      split.
    
      + intros * [Hz%type_isType _].
        2: constructor.
        inversion Hz ; inv_whne.

      + intros * [Hconv]%dup.
        eapply LamNeUAlg_prem0 in Hconv as (?&[]).
        eapply LamNeUAlg_concl ; eauto.

    - intros * ?? [].
      split.
    
      + intros * [_ Hz%type_isType].
        2: constructor.
        inversion Hz ; inv_whne.

      + intros * [Hconv]%dup.
        eapply NeLamUAlg_prem0 in Hconv as (?&[]).
        eapply NeLamUAlg_concl ; eauto.

    - intros * HA [IHA_ty IHA_tm] HB [IHB_ty IHB_tm].
      split.
      + intros ? [Hconcl]%dup.
        eapply typeSigCongAlg_prem0 in Hconcl as [Hpre0 []]%dup.
        eapply IHA_ty, typeSigCongAlg_prem1 in Hpre0 ; tea.
        now econstructor.

      + intros * [Hconcl [[Hty]%dup]]%dup.

        eapply termGen' in Hty as (?&[->]&Hconv) ; tea.
        econstructor ; tea.
        eapply termSigCongAlg_concl.
        2: eapply IHB_tm, termSigCongAlg_prem1.
        1-2: eapply IHA_tm, termSigCongAlg_prem0.
        all: split ; now eapply ty_conv.

    - intros * Hp [_ IHp] Hq [_ IHq].
      split.

      + intros * [Hz%type_isType _].
        2: constructor.
        inversion Hz ; inv_whne.

      + intros * [Hconcl ?]%dup.
        eapply PairCongUAlg_concl ; tea.
        2:eapply IHq, PairCongUAlg_prem1 ; tea.
        all: now eapply IHp, PairCongUAlg_prem0.

    - intros * ? Hp [_ IHp] Hq [_ IHq].
      split.

      + intros * [Hz%type_isType _].
        2: constructor.
        inversion Hz ; inv_whne.

      + intros * [Hconcl ?]%dup.
        eapply PairNeUAlg_concl ; tea.
        2:eapply IHq, PairNeUAlg_prem1 ; tea.
        all: now eapply IHp, PairNeUAlg_prem0.

    - intros * ? Hp [_ IHp] Hq [_ IHq].
      split.

      + intros * [_ Hz%type_isType].
        2: constructor.
        inversion Hz ; inv_whne.

      + intros * [Hconcl ?]%dup.
        eapply NePairUAlg_concl ; tea.
        2:eapply IHq, NePairUAlg_prem1 ; tea.
        all: now eapply IHp, NePairUAlg_prem0.
        
    - intros * HA [IHA_ty IHA_tm] Hx [_ IHx_tm] Hy [_ IHy_tm].
      split.

      + intros ? [Hconcl]%dup.
        eapply typeIdCongAlg_prem0 in Hconcl as [Hpre0 []]%dup.
        eapply IHA_ty in Hpre0 as [Hpost0]%dup; eauto.
        eapply typeIdCongAlg_prem1 in Hpost0 as [Hpre1 []]%dup ; eauto. 
        eapply IHx_tm, typeIdCongAlg_prem2 in Hpre1 as [Hpre2]%dup; eauto.
        now econstructor.

      + intros * [Hconcl [[Hty]%dup]]%dup.

        eapply termGen' in Hty as (?&[->]&?) ; tea.
        econstructor ; tea.
        eapply termIdCongAlg_concl.
        3: eapply IHy_tm, termIdCongAlg_prem2.
        2,4: eapply IHx_tm, termIdCongAlg_prem1.
        1,2,4,6: eapply IHA_tm, termIdCongAlg_prem0.
        all: split ; now eapply ty_conv.

    - split.
  
      + intros * [Hz%type_isType _].
        2: constructor.
        inversion Hz ; inv_whne.

      + intros * [[[? [[->] Hconv]]%termGen'] ?]%dup.
        econstructor ; tea.
        eapply termIdReflCong_concl.
        split ; now eapply ty_conv.

    - intros * Hconv IH.
      split.
      
      + intros * [Hconcl]%dup.
        eapply algo_uconv_wh in Hconv as [].
        eapply typeNeuConvAlg_prem2 in Hconcl; tea.
        edestruct IH ; tea.
        now eapply typeNeuConvAlg_concl.

      + intros * [Hconcl []]%dup.
        edestruct IH.
        1: split ; now eexists.
        econstructor.
        1: now eapply conv_neu_sound.
        now eapply conv_neu_typing.

    - intros * [[[? (?&[? []]&?)%termGen']]]%dup.
      eexists.
      now eapply neuVarConvAlg_concl.

    - intros * Hconv IHm ? [_ IHt] * [Hconcl]%dup.

      eapply neuAppCongAlg_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
      eapply IHm in Hpre0 as [? [Hpost0]%dup].
      eapply AppCongUAlg_bridge in Hpost0 as (?&?&[? [Hpre1]%dup]); tea.
      eapply neuAppCongAlg_prem1, IHt in Hpre1 ; eauto.
      eexists.
      now eapply neuAppCongAlg_concl.

    - intros * ? IH ? [IHP] ? [_ IHz] ? [_ IHs] ? [Hconcl]%dup.

      eapply neuNatElimCong_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
      eapply IH in Hpre0 as [? [Hpost0]%dup].
      eapply NatElimCongUAlg_bridge in Hpost0 as [? [Hpost0]%dup]; eauto.
      eapply neuNatElimCong_prem1 in Hpost0 as [Hpre1 []]%dup ; eauto.
      eapply IHP in Hpre1 as [Hpos1]%dup ; eauto.
      eapply neuNatElimCong_prem2 in Hpos1 as [Hpre2 []]%dup ; eauto.
      eapply IHz in Hpre2 as [Hpos2]%dup ; eauto.
      eapply neuNatElimCong_prem3 in Hpos2 as [Hpre3 []]%dup ; eauto.
      eapply IHs in Hpre3 as Hpos3 ; eauto.
      eexists.
      now eapply neuNatElimCong_concl.

    - intros * ? IH ? [IHP] ? [Hconcl]%dup.

      eapply neuEmptyElimCong_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
      eapply IH in Hpre0 as [? [Hpost0]%dup].
      eapply EmptyElimCongUAlg_bridge in Hpost0 as [? [Hpost0]%dup]; eauto.
      eapply neuEmptyElimCong_prem1 in Hpost0 as [Hpre1 []]%dup ; eauto.
      eapply IHP in Hpre1 as [Hpos1]%dup ; eauto.
      eexists.
      now eapply neuEmptyElimCong_concl.

    - intros * ? IH ? [Hconcl]%dup.

      eapply neuFstCongAlg_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
      eapply IH in Hpre0 as [? [Hpost0]%dup].
      eapply FstCongUAlg_bridge in Hpost0 as (?&?&[? Hpre1]); eauto.
      eexists.
      now eapply neuFstCongAlg_concl.

    - intros * ? IH ? [Hconcl]%dup.

      eapply neuSndCongAlg_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
      eapply IH in Hpre0 as [? [Hpost0]%dup].
      eapply SndCongUAlg_bridge in Hpost0 as (?&?&[? Hpre1]); eauto.
      eexists.
      now eapply neuSndCongAlg_concl.

    - intros * ? IH ? [IHP] ? [_ IHr]  ? [Hconcl]%dup.

      eapply neuIdElimCong_prem0 in Hconcl as [Hpre0 []]%dup ; eauto.
      eapply IH in Hpre0 as [? [Hpost0]%dup].
      eapply IdElimCongUAlg_bridge in Hpost0 as [? (?&?&?&[Hpost0]%dup)]; eauto.
      eapply neuIdElimCong_prem1 in Hpost0 as [Hpre1 []]%dup ; eauto.
      eapply IHP in Hpre1 as [Hpos1]%dup ; eauto.
      eapply neuIdElimCong_prem2 in Hpos1 as [Hpre2 []]%dup ; eauto.
      eapply IHr in Hpre2 as [Hpos2]%dup ; eauto.
      eexists.
      now eapply neuIdElimCong_concl.
  Qed.

End UConvSound.