(** * LogRel.Consequences: important meta-theoretic consequences of normalization: canonicity of natural numbers and consistency. *)
From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Computation Notations Context NormalForms Weakening UntypedReduction
  LogicalRelation Fundamental Validity LogicalRelation.Induction Substitution.Escape LogicalRelation.Irrelevance
  GenericTyping DeclarativeTyping DeclarativeInstance TypeConstructorsInj.

Import DeclarativeTypingData DeclarativeTypingProperties SNDeclarativeTypingProperties.

Section TypingFv.

  Fixpoint mem_ctx (Γ : list term) n {struct n} : Prop := match Γ with
  | nil => False
  | cons _ Γ =>
    match n with
    | 0 => True
    | S n => mem_ctx Γ n
    end
  end.

  Lemma in_ctx_mem_ctx : forall Γ n decl, in_ctx Γ n decl -> mem_ctx Γ n.
  Proof.
  induction 1; cbn; eauto.
  Qed.

  Lemma allfv_memctx {Γ A t} : allfv_term (mem_ctx (Γ,, A)) t -> allfv_term (upAllfv_term_term (mem_ctx Γ)) t.
  Proof.
  intros.
  eapply allfvImpl_term; [|tea].
  intros []; cbn; eauto.
  Qed.

  Lemma allfvSubsR_term :
    forall (p_term : nat -> Prop) (xi_term : nat -> term) (s : term),
    allfv_term (fun n => allfv_term p_term (xi_term n)) s -> allfv_term p_term (subst_term xi_term s).
  Proof.
  intros p_term xi_term s; revert p_term xi_term; induction s; intros p_term xi_term **; cbn in *; prod_splitter; eauto.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end; eauto.
  + eapply IHs2; eapply allfvImpl_term; [|tea].
    intros []; cbn in *; [eauto|]; intros.
    eapply allfvRenR_term, allfvImpl_term; [|tea].
    intros; tea.
  + eapply IHs2; eapply allfvImpl_term; [|tea].
    intros []; cbn in *; [eauto|]; intros.
    eapply allfvRenR_term, allfvImpl_term; [|tea].
    intros; tea.
  + eapply IHs1; eapply allfvImpl_term; [|tea].
    intros []; cbn in *; [eauto|]; intros.
    eapply allfvRenR_term, allfvImpl_term; [|tea].
    intros; tea.
  + eapply IHs1; eapply allfvImpl_term; [|tea].
    intros []; cbn in *; [eauto|]; intros.
    eapply allfvRenR_term, allfvImpl_term; [|tea].
    intros; tea.
  + eapply IHs2; eapply allfvImpl_term; [|tea].
    intros []; cbn in *; [eauto|]; intros.
    eapply allfvRenR_term, allfvImpl_term; [|tea].
    intros; tea.
  + eapply IHs2; eapply allfvImpl_term; [|tea].
    intros []; cbn in *; [eauto|]; intros.
    eapply allfvRenR_term, allfvImpl_term; [|tea].
    intros; tea.
  + eapply IHs3; eapply allfvImpl_term; [|tea].
    intros [|[|]]; cbn in *; eauto; intros.
    eapply allfvRenR_term, allfvImpl_term; [|tea].
    - intros; tea.
    - eapply allfvRenR_term, allfvImpl_term; [|tea].
      intros; tea.
  Qed.

  Lemma allfv_qNat : forall P n, allfv_term P (qNat n).
  Proof.
  intros P n; revert P; induction n; cbn; eauto.
  Qed.

  Lemma allfv_qEvalTy : forall P n v, allfv_term P (qEvalTy n v).
  Proof.
  intros P n; revert P; induction n; cbn; intros; prod_splitter; eauto using allfv_qNat.
  apply allfvRenR_term; eauto.
  Qed.

  Lemma allfv_qEvalTm : forall P n v, allfv_term P (qEvalTm n v).
  Proof.
  intros P n; revert P; induction n; cbn; intros; prod_splitter; eauto using allfv_qNat, allfv_qEvalTy.
  Qed.

  Lemma allfv_subst1_term : forall Γ t u,
    allfv_term (upAllfv_term_term (mem_ctx Γ)) t ->
    allfv_term (mem_ctx Γ) u ->
    allfv_term (mem_ctx Γ) t[u..].
  Proof.
  intros * Ht Hu.
  eapply allfvSubsR_term.
  eapply allfvImpl_term; [|tea].
  intros []; cbn; eauto.
  Qed.

  Let PCon (Γ : context) := (forall n decl, in_ctx Γ n decl -> allfv_term (mem_ctx Γ) decl).
  Let PTy (Γ : context) (A : term) := allfv_term (mem_ctx Γ) A.
  Let PTm (Γ : context) (A t : term) := allfv_term (mem_ctx Γ) A × allfv_term (mem_ctx Γ) t.
  Let PTyEq (Γ : context) (A B : term) :=  allfv_term (mem_ctx Γ) A × allfv_term (mem_ctx Γ) B.
  Let PTmEq (Γ : context) (A t u : term) :=  allfv_term (mem_ctx Γ) A × allfv_term (mem_ctx Γ) t × allfv_term (mem_ctx Γ) u.

  Theorem typing_fv : WfDeclInductionConcl PCon PTy PTm PTyEq PTmEq.
  Proof.
    subst PCon PTy PTm PTyEq PTmEq.
    apply WfDeclInduction; intros; cbn in *; prod_splitter;
    repeat match goal with H : _ × _ |- _ => destruct H end;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    eauto using allfv_memctx, allfvRenR_term, allfv_qNat, allfv_qEvalTm, in_ctx_mem_ctx, allfv_subst1_term.
    all: try now (eapply allfvImpl_term; [|tea]; cbn; intros [|[]]; eauto).
    all: try now (apply allfv_subst1_term; eauto; cbn; eauto).
    + inversion H.
    + inversion H3; subst; eauto; apply allfvRenR_term; eauto.
    + eapply allfvSubsR_term.
      eapply allfvImpl_term; [|tea].
      intros [|[|]]; cbn; eauto.
    + apply allfv_subst1_term; eauto; cbn; eauto.
      - eapply allfvImpl_term; [|tea]; cbn; intros [|[]]; eauto.
      - repeat constructor; eauto; eapply allfvImpl_term; [|tea]; cbn; intros [|[]]; eauto.
    + eapply allfvSubsR_term.
      eapply allfvImpl_term; [|tea].
      intros [|[|]]; cbn; eauto.
    + eapply allfvSubsR_term.
      eapply allfvImpl_term; [|tea].
      intros [|[|]]; cbn; eauto.
  Qed.

End TypingFv.

Lemma allfv_closed : forall Γ t,
  allfv_term (mem_ctx Γ) t -> Closed.is_closedn (length Γ) t = true.
Proof.
intros Γ t; revert Γ; induction t; intros; cbn in *;
repeat match goal with H : _ /\ _ |- _ => destruct H end;
repeat (apply andb_true_intro; split); eauto.
+ change (PeanoNat.Nat.ltb n (length Γ) = true).
  apply <- PeanoNat.Nat.ltb_lt; revert Γ H.
  induction n; intros [] H; cbn in *; try contradiction; try Lia.lia.
  enough (n < #|l|) by Lia.lia; eauto.
+ eapply (IHt2 (cons U Γ)), allfvImpl_term; [|tea].
  intros [|]; cbn; eauto.
+ eapply (IHt2 (cons U Γ)), allfvImpl_term; [|tea].
  intros [|]; cbn; eauto.
+ eapply (IHt1 (cons U Γ)), allfvImpl_term; [|tea].
  intros [|]; cbn; eauto.
+ eapply (IHt1 (cons U Γ)), allfvImpl_term; [|tea].
  intros [|]; cbn; eauto.
+ eapply (IHt2 (cons U Γ)), allfvImpl_term; [|tea].
  intros [|]; cbn; eauto.
+ eapply (IHt3 (cons U (cons U Γ))), allfvImpl_term; [|tea].
  intros [|[|]]; cbn; eauto.
Qed.

Lemma no_neutral_empty_ctx {A t} : whne t -> [ε |-[de] t : A] -> False.
Proof.
  intros Hne Ht.
  apply typing_fv in Ht as [_ Ht].
  clear A; induction Hne; cbn in Ht;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  eauto; tea.
  - destruct v; tea.
  - elim n; now eapply (allfv_closed nil).
  - destruct s as [n|n]; elim n; now eapply (allfv_closed nil).
  - destruct s as [n|n]; elim n; now eapply (allfv_closed nil).
Qed.

(** *** Consistency: there are no closed proofs of false, i.e. no closed inhabitants of the empty type. *)

#[local] Lemma red_empty_empty : [ε ||-Empty tEmpty].
Proof.
  repeat econstructor.
Qed.

Lemma consistency {t} : [ε |- t : tEmpty] -> False.
Proof.
  intros H.
  assert (Ht : [LREmpty_ one red_empty_empty | ε ||- t : tEmpty]).
  {
    apply Fundamental in H as [?? Vt%reducibleTm].
    irrelevance.
  }
  destruct Ht, prop, r.
  eapply no_neutral_empty_ctx; tea.
  now eapply convneu_whne.
Qed.

(** Strong normalization *)

Section SN.

Import DeepTyping.DeepTypingData.
Import DeepTyping.DeepTypingProperties.

Lemma strong_normalization : forall Γ A t, [Γ |-[de] t : A] -> ∑ v, [t ⇊ v].
Proof.
intros * H.
apply TermRefl in H.
apply Fundamental in H as [].
eapply escapeTmEq in Vtu.
apply snty_nf in Vtu as (t₀&?&[]&?&?&?&?).
exists t₀.
now eapply dredalg_bigstep.
Qed.

End SN.

(** *** Canonicity: every closed natural number is a numeral, i.e. an iteration of [tSucc] on [tZero]. *)

Section NatCanonicityInduction.

  Let red_nat_empty : [ε ||-Nat tNat].
  Proof.
    repeat econstructor.
  Defined.

  Lemma nat_red_empty_ind :
    (forall t, [ε ||-Nat t : tNat | red_nat_empty] ->
    ∑ n : nat, [ε |- t ≅ qNat n : tNat]) ×
    (forall t, NatProp red_nat_empty t -> ∑ n : nat, [ε |- t ≅ qNat n : tNat]).
  Proof.
    apply NatRedInduction.
    - intros * [? []] ? _ [n] ; refold.
      exists n.
      now etransitivity.
    - exists 0 ; cbn.
      now repeat constructor.
    - intros ? _ [n].
      exists (S n) ; simpl.
      now econstructor.
    - intros ? [? [? _ _]].
      exfalso.
      now eapply no_neutral_empty_ctx.
  Qed.

  Lemma _nat_canonicity {t} : [ε |- t : tNat] ->
  ∑ n : nat, [ε |- t ≅ qNat n : tNat].
  Proof.
    intros Ht.
    assert [LRNat_ one red_nat_empty | ε ||- t : tNat] as ?%nat_red_empty_ind.
    {
      apply Fundamental in Ht as [?? Vt%reducibleTm].
      irrelevance.
    }
    now assumption.
  Qed.

End NatCanonicityInduction.

Section NatCanonicityDeepRed.

Import DeepTyping.DeepTypingData.
Import DeepTyping.DeepTypingProperties.

Let red_nat_empty : [ε ||-Nat tNat].
Proof.
repeat econstructor.
Defined.

Lemma _nat_canonicity_dred {t} : [ε |-[de] t : tNat] -> ∑ n : nat, [t ⇊ qNat n].
Proof.
  intros Ht.
  assert (rt : [LRNat_ one red_nat_empty | ε ||- t : tNat]).
  { apply Fundamental in Ht as [?? Vt%reducibleTm]; irrelevance. }
  assert (Htt : [ε |-[nf] t ≅ t : tNat]).
  { now eapply LogicalRelation.Escape.escapeEqTerm, Reflexivity.reflLRTmEq. }
  destruct Htt as [t₀ ?? [Hr Hnf Ht₀]].
  assert (Hn : ∑ n, t₀ = qNat n).
  { eapply Reflect.dnf_closed_qNat in Hr; tea.
    + destruct Hr as (n&?&?); subst; now exists n.
    + apply (allfv_closed ε).
      now apply typing_fv in Ht₀ as (?&?&?). }
  destruct Hn as [n]; subst; exists n; now eapply dredalg_bigstep.
Qed.

End NatCanonicityDeepRed.

Lemma nat_canonicity {t} : [ε |- t : tNat] ->
  ∑ n : nat, [ε |- t ≅ qNat n : tNat].
Proof.
  now apply _nat_canonicity.
Qed.

Lemma nat_canonicity_dred {t} : [ε |-[de] t : tNat] -> ∑ n : nat, [t ⇊ qNat n].
Proof.
  now apply _nat_canonicity_dred.
Qed.
