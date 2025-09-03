(** * LogRel.Checkers.ReductionCorrectness: properties of the reduction function. *)
From Stdlib Require Import Nat Lia Arith.
From Equations Require Import Equations.
From LogRel Require Import Syntax.All DeclarativeTyping GenericTyping AlgorithmicJudgments.
From LogRel.TypingProperties Require Import NormalisationDefinition DeclarativeProperties PropertiesDefinition SubstConsequences TypeInjectivityConsequences NeutralConvProperties.
From LogRel Require Import Utils.

From LogRel.Checkers Require Import Functions Views.
From PartialFun Require Import Monad PartialFun MonadExn.

Set Universe Polymorphism.
#[global] Unset Asymmetric Patterns.

Import DeclarativeTypingProperties.


Lemma zip_ored t t' π : [t ⤳ t'] -> [zip t π ⤳ zip t' π].
Proof.
  intros Hred.
  induction π as [|[]] in t, t', Hred |- * ; cbn in *.
  1: eassumption.
  all: apply IHπ ; now econstructor.
Qed.

Lemma zip_red t t' π : [t ⤳* t'] -> [zip t π ⤳* zip t' π].
Proof.
  induction 1.
  1: reflexivity.
  econstructor ; tea.
  now eapply zip_ored.
Qed.

(** ** Soundness of reduction *)
(** If the reduction function called on a term t returns a term t', then
t reduces to t' and t' is a weak-head normal form. *)

Section RedImplemSound.

Lemma red_stack_sound :
  funrec wh_red_stack (fun _ => True) (fun '(t,π) t' => [zip t π ⤳* t']).
Proof.
  intros ? _.
  funelim (wh_red_stack _).
  all: cbn ; econstructor ; try eauto.
  all: intros v ?.
  all: etransitivity ; [..|eassumption].
  all: eapply zip_red.
  all: econstructor ; [..|reflexivity].
  all: now econstructor.
Qed.

Lemma stack_ne n π :
  whne n -> whne (zip n π).
Proof.
  intros Hne.
  induction π as [|[]] in n, Hne |- * ; cbn.
  1: eassumption.
  all: eapply IHπ ; now econstructor.
Qed.

Lemma red_stack_whnf :
funrec wh_red_stack (fun _ => True) (fun '(t,π) t' => whnf t').
Proof.
  intros ? _.
  funelim (wh_red_stack _).
  all: cbn ; try solve [constructor ; eauto]. 
  - now eapply isType_whnf, isType_tm_view1.
  - econstructor. eapply stack_ne.
    now econstructor.
  - now eapply whnf_tm_view1_nat.
Qed.

Corollary _red_sound :
  funrec wh_red (fun _ => True) (fun t t' => [t ⤳* t'] × whnf t').
Proof.
  intros ? _.
  cbn; intros ? H; split.
  - eapply funrec_graph in H.
    2: apply red_stack_sound.
    all: easy.
  - eapply funrec_graph in H.
    2: exact red_stack_whnf.
    all: easy.
Qed.

#[universes(polymorphic)]Corollary red_sound t t' :
  graph wh_red t t' ->
  [t ⤳* t'] × whnf t'.
Proof.
  intros H.
  pattern t, t'.
  eapply funrec_graph.
  1: apply _red_sound.
  all: easy.
Qed.

End RedImplemSound.

(** ** Completeness of reduction *)
(** Given any well-formed input, which reduces to a weak-head normal form, the reduction function finds
  that weak-head normal form. This does not rely on normalisation, since we assume a reduction relation. *)

Section RedImplemComplete.
  Context `{!TypingSubst de} `{!TypeConstructorsInj de}.

  #[local]Definition R_aux := lexprod term term cored term_subterm.

  #[local]Definition R (t u : term × stack) :=
    R_aux (Datatypes.pair (zip (fst t) (snd t)) (fst t)) (Datatypes.pair (zip (fst u) (snd u)) (fst u)).

  Lemma R_acc t π :
    Acc cored (zip t π) ->
    Acc R (t, π).
  Proof.
  intros h.
  eapply acc_A_B_lexprod with (leA := cored) (leB := term_subterm) (y := t) in h.
  - remember (Datatypes.pair (zip t π) t) as z eqn:e.
    induction h as [z h ih] in t, π, e |- *. subst.
    constructor. intros [v ρ] hr.
    unfold R, R_aux in hr ; cbn in *.
    eapply ih. 2: reflexivity.
    assumption.
  - eapply well_founded_term_subterm.
  - eapply well_founded_term_subterm.
  Qed.

  Lemma normalising_acc t π t' :
    [(zip t π) ⤳* t'] ->
    whnf t' ->
    Acc R (t,π).
  Proof.
    intros Hred Hnf.
    eapply R_acc.
    set (t'' := (zip t π)) in *.
    clearbody t''.
    clear -Hred Hnf.
    induction Hred.
    - constructor.
      intros ? [].
      now edestruct whnf_nored.
    - constructor.
      now eintros ? [<-%ored_det].
  Qed.

  Lemma well_typed_zip Γ t π :
    well_typed (ta := de) Γ (zip t π) ->
    ∑ T', [Γ |-[de] t : T'] × (forall u, [Γ |-[de] t ≅ u : T'] -> well_typed (ta := de) Γ (zip u π)).
  Proof.
    intros H.
    induction π as [|[]] in t, H |- * ; cbn.
    - destruct H as [T Hty].
      exists T ; split.
      1: eassumption.
      intros *.
      eexists.
      boundary.
    - cbn in H.
      eapply IHπ in H as (T&(?&[]&?)%termGen'&Hsubst) ; subst.
      eexists ; split ; tea.
      intros u Htyu.
      eapply Hsubst.
      econstructor.
      1: eapply TermEmptyElimCong ; tea ; refold.
      2: eassumption.
      now econstructor.
    - cbn in H.
      eapply IHπ in H as (T&(?&[]&?)%termGen'&Hsubst) ; subst.
      eexists ; split ; tea.
      intros u Htyu.
      eapply Hsubst.
      econstructor.
      1: eapply TermNatElimCong ; tea ; refold.
      + now econstructor.
      + now econstructor.
      + now eapply TermRefl.
      + eassumption.
    - cbn in H.
      eapply IHπ in H as (T&(?&(?&?&[])&?)%termGen'&Hsubst) ; subst.
      eexists ; split ; tea.
      intros u' Htyu.
      eapply Hsubst.
      econstructor.
      1: econstructor ; tea.
      2: eassumption.
      now econstructor.
    - cbn in H.
      eapply IHπ in H as [T [[?[[?[?[->]]]]]%termGen' Hsubst]].
      eexists; split; tea.
      intros; eapply Hsubst.
      eapply TermConv; refold; tea.
      now econstructor.
    - cbn in H.
      eapply IHπ in H as [T [[?[[?[?[->]]]]]%termGen' Hsubst]].
      eexists; split; tea.
      intros; eapply Hsubst.
      eapply TermConv; refold; tea.
      now econstructor.
  - cbn in H.
    eapply IHπ in H as [T [[? [[->]]]%termGen' Hsubst]].
      eexists; split; tea.
      intros; eapply Hsubst.
      eapply TermConv; refold; tea.
      econstructor; tea; eapply TypeRefl + eapply TermRefl; refold; tea.
  Qed.

  Lemma zip1_notType Γ T t π :
    isType t ->
    ~ whne t ->
    ~ [Γ |-[de] zip1 t π : T].
  Proof.
    intros Ht Ht' Hty.
    destruct π ; cbn in * ;
      eapply termGen' in Hty as (?&[]&?) ; subst ; prod_hyp_splitter ;
      match goal with H : [_ |-[de] t : _] |- _ => (unshelve eapply isType_ty, ty_conv_inj in H) end ; tea.
    all: try solve
      [now econstructor| now eapply not_whne_can ; tea ; eapply isType_whnf | now cbn in *].
  Qed.

  Ltac termInvContradiction Hty := 
    eapply termGen' in Hty; cbn in Hty; prod_hyp_splitter; subst;
    now match goal with 
    | [H : [_ |-[de] _ : _] |- _] =>
      eapply termGen' in H; cbn in H; prod_hyp_splitter; subst;
      now match goal with
      | [H : [_ |-[de] _ ≅ _] |- _] => unshelve eapply ty_conv_inj in H; first [constructor | easy]
      end
    end.

  Lemma wh_red_stack_complete Γ t π t' :
    well_typed Γ (zip t π) ->
    [(zip t π) ⤳* t'] ->
    whnf t' ->
    domain wh_red_stack (t,π).
  Proof.
    intros Hty Hred Hnf.
    pose proof (Hacc := normalising_acc _ _ _ Hred Hnf).
    change (zip t π) with (zip (fst (t,π)) (snd (t,π))) in *.
    set (z := (t, π)) in *. clearbody z.
    clear Hnf Hred.
    induction Hacc as [z H IH] in Hty |- *.
    apply compute_domain. funelim (wh_red_stack z).
    all: simpl.
    all: try easy.
    all: try solve [ cbn in * ; eapply well_typed_zip in Hty as [? [Hty _]] ; cbn in *; termInvContradiction Hty].
    - cbn in * ; eapply well_typed_zip in Hty as [? [? _]] ; cbn in *.
      eapply zip1_notType ; tea.
      all: now eapply isType_tm_view1.
    - split ; [|easy].
      eapply IH.
      + red. red. cbn.
        left.
        constructor.
        eapply zip_ored.
        now econstructor.
      + cbn in *.
        eapply well_typed_zip in Hty as (?&[??Hu]).
        eapply Hu, RedConvTeC, subject_reduction ; tea.
        now do 2 econstructor.
  - split ; [|easy].
    eapply IH.
    + red. red. cbn.
      left.
      constructor.
      eapply zip_ored.
      now econstructor.
    + cbn in *.
      eapply well_typed_zip in Hty as (?&[??Hu]).
      eapply Hu, RedConvTeC, subject_reduction ; tea.
      now do 2 econstructor.
  - cbn in *.
    split ; [|easy].
    eapply IH ; cbn in *.
    + red. red. cbn.
      left.
      constructor.
      eapply zip_ored.
      now econstructor.
    + cbn in *.
      eapply well_typed_zip in Hty as (?&[??Hu]).
      eapply Hu, RedConvTeC, subject_reduction ; tea.
      now do 2 econstructor.
  - cbn in *; split; [|easy].
    eapply IH.
    + do 2 red; cbn.
      left; constructor; eapply zip_ored; constructor.
    + cbn. 
      eapply well_typed_zip in Hty as (?&[??Hu]).
      eapply Hu, RedConvTeC, subject_reduction ; tea.
      now do 2 econstructor.
  - cbn in *; split; [|easy].
    eapply IH.
    + do 2 red; cbn.
      left; constructor; eapply zip_ored; constructor.
    + cbn. 
      eapply well_typed_zip in Hty as (?&[??Hu]).
      eapply Hu, RedConvTeC, subject_reduction ; tea.
      now do 2 econstructor.
  - cbn in *; split;[|easy].
    eapply IH.
    + do 2 red; cbn.
      left; constructor; eapply zip_ored; constructor.
    + cbn.
      eapply well_typed_zip in Hty as [? [? Hu]] .
      eapply Hu, RedConvTeC, subject_reduction; tea.
      eapply redalg_one_step; constructor.
  - cbn in *.
    split ; [|easy].
    eapply IH ; cbn in *.
    2: eassumption.
    red. red. cbn.
    right.
    econstructor.
    destruct s ; cbn ; now constructor.
  Qed.

  Corollary wh_red_complete Γ t :
    well_formed Γ t ->
    normalising t ->
    domain wh_red t.
  Proof.
    intros [|w]%well_formed_well_typed [].
    all: eapply compute_domain; cbn.
    all: split ; [|easy].
    - eapply wh_red_stack_complete ; tea.
    - inversion w ; subst ; clear w; cycle -1.
      1: eapply wh_red_stack_complete ; tea ; now econstructor.
      all: econstructor ; cbn ; red.
      all: simp wh_red_stack ; cbn.
      all: now econstructor.
  Qed.

  Corollary wh_red_complete_whnf_class Γ K t t' :
  [Γ |- t ⤳* t' ∈ K] ->
  whnf t' ->
  graph wh_red t t'.
  Proof.
    intros [] ? ; refold.
    assert (domain wh_red t) as h.
    {
      eapply (wh_red_complete Γ).
      2: now econstructor.
      destruct K as [|A] ; unshelve econstructor ; [left|right|..] ; cbn.
      2-3: eassumption.
    }
    replace t' with (def wh_red t h).
    1: eapply def_graph_sound.
    eapply whred_det ; tea.
    all: now eapply red_sound, def_graph_sound.
  Qed.
  
  Corollary wh_red_complete_whnf_ty Γ A A' :
  [Γ |-[de] A] ->
  [A ⤳* A'] ->
  whnf A' ->
  graph wh_red A A'.
  Proof.
    intros ? Hred ?.
    eapply subject_reduction_type in Hred ; tea.
    now eapply wh_red_complete_whnf_class.
  Qed.
  
  Corollary wh_red_complete_whnf_tm Γ A t t' :
  [Γ |-[de] t : A] ->
  [t ⤳* t'] ->
  whnf t' ->
  graph wh_red t t'.
  Proof.
    intros ? Hred ?.
    eapply subject_reduction in Hred ; tea.
    now eapply wh_red_complete_whnf_class.
  Qed.

End RedImplemComplete.