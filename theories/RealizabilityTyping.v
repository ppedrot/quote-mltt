From Coq Require Import ssreflect.
From smpl Require Import Smpl.
From LogRel Require Import Utils Syntax.All GenericTyping.

Set Primitive Projections.

Lemma wf_in_ctx : forall Γ n decl, in_ctx Γ n decl -> n < #|Γ|.
Proof.
induction 1; cbn; auto with arith.
Qed.

Definition scoped (k : nat) (t : term) := allfv_term (fun n => n < k) t.
Definition well_scoped (Γ : context) (t : term) := allfv_term (fun n => n < length Γ) t.

Lemma well_scoped_ren {Γ Δ} t (ρ : Δ ≤ Γ) : well_scoped Γ t -> well_scoped Δ t⟨ρ⟩.
Proof.
intros * H; apply allfvRenR_term.
eapply allfvImpl_term; [|apply H].
intros x Hx; unfold funcomp; cbn in *.
destruct ρ as [ρ Hρ]; cbn.
clear H; revert x Hx; induction Hρ; cbn in *; intros x Hx; unfold funcomp.
+ Lia.lia.
+ now enough (ρ x < #|Γ|) by Lia.lia.
+ destruct x as [|x]; cbn; unfold funcomp; [Lia.lia|].
  enough (ρ x < #|Γ|) by Lia.lia.
  apply IHHρ; Lia.lia.
Qed.

Lemma scoped_shift : forall k t, scoped k t -> scoped (S k) t⟨↑⟩.
Proof.
intros k t Ht.
pose (Γ := List.repeat U k).
rewrite <- wk1_ren_on with (Γ := Γ) (F := U).
replace k with (length Γ) in * by now apply List.repeat_length.
change (well_scoped (cons U Γ) t⟨@wk1 Γ U⟩).
now eapply well_scoped_ren.
Qed.

Lemma scoped_S_up : forall m t,
  allfv_term (fun n => n < S m) t ->
  allfv_term (upAllfv_term_term (fun n : nat => n < m)) t.
Proof.
intros * H.
eapply allfvImpl_term; [|exact H].
intros [|]; cbn; eauto with arith.
Qed.

Lemma scoped_SS_up : forall m t,
  allfv_term (fun n => n < S (S m)) t ->
  allfv_term (upAllfv_term_term (upAllfv_term_term (fun n : nat => n < m))) t.
Proof.
intros * H.
eapply allfvImpl_term; [|exact H].
intros [|[|]]; cbn; eauto with arith.
Qed.

Lemma scoped_up_S : forall m t,
  allfv_term (upAllfv_term_term (fun n : nat => n < m)) t ->
  allfv_term (fun n => n < S m) t.
Proof.
intros * H.
eapply allfvImpl_term; [|exact H].
intros [|]; cbn; eauto 3 with arith.
Qed.

Lemma scoped_up_SS : forall m t,
  allfv_term (upAllfv_term_term (upAllfv_term_term (fun n : nat => n < m))) t ->
  allfv_term (fun n => n < S (S m)) t.
Proof.
intros * H.
eapply allfvImpl_term; [|exact H].
intros [|[|]]; cbn; eauto 3 with arith.
Qed.

Lemma scoped_incl : forall m n t, m < n -> scoped m t -> scoped n t.
Proof.
intros * H Ht.
eapply allfvImpl_term; [|exact Ht].
cbn; Lia.lia.
Qed.

Lemma scoped_subs {γ δ} t σ : scoped γ t -> (forall n, n < γ -> scoped δ (σ n)) ->
  scoped δ t[σ].
Proof.
unfold scoped; revert σ γ δ.
induction t; intros σ γ δ Ht Hσ; cbn in *;
repeat match goal with [ H : _ /\ _ |- _ ] => destruct H end;
prod_splitter; eauto.
all: try (
  apply scoped_S_up;
  first [eapply IHt2|eapply IHt1]; eauto using scoped_up_S;
  intros [|]; cbn; [unfold var_zero; Lia.lia|];
  unfold funcomp; intros;
  apply scoped_shift, Hσ; Lia.lia
).
+ apply scoped_SS_up.
  eapply IHt3; eauto using scoped_up_SS.
  intros [|[|]]; cbn; try (compute; Lia.lia).
  unfold funcomp; intros.
  apply scoped_shift, scoped_shift, Hσ; Lia.lia.
Qed.

Lemma scoped_subst1 : forall k t u,
  scoped (S k) t -> scoped k u -> scoped k t[u..].
Proof.
intros * Ht Hu.
eapply scoped_subs; [apply Ht|].
intros [|]; cbn; eauto with arith.
Qed.

Lemma well_scoped_subst1 : forall Γ A t u,
  well_scoped (Γ,, A) t -> well_scoped Γ u -> well_scoped Γ t[u..].
Proof.
intros * Ht Hu.
eapply scoped_subs; [apply Ht|].
intros [|]; cbn; eauto with arith.
Qed.

Create HintDb rzbltyping.

Inductive WfContextRzbl : context -> Set :=
| wf_ctx_nil : WfContextRzbl nil
| wf_ctx_cons : forall Γ A, WfContextRzbl Γ -> well_scoped Γ A -> WfContextRzbl (Γ,, A).

Lemma wf_in_ctx_scoped : forall Γ n decl, WfContextRzbl Γ -> in_ctx Γ n decl -> well_scoped Γ decl.
Proof.
intros * HΓ; revert n decl.
induction HΓ; intros n decl H; inversion H; subst.
+ unfold well_scoped; cbn; now apply scoped_shift.
+ unfold well_scoped; cbn.
  now eapply scoped_shift, IHHΓ.
Qed.

Hint Constructors WfContextRzbl : rzbltyping.

Record WfTypeRzbl (Γ : context) (A : term) := {
  wfty_ctx_scoped : WfContextRzbl Γ;
  wfty_ty_scoped : well_scoped Γ A;
}.

Hint Resolve wfty_ctx_scoped wfty_ty_scoped : rzbltyping.

Record TypingRzbl (Γ : context) (A t : term) := {
  typ_ctx_scoped : WfContextRzbl Γ;
  typ_ty_scoped : well_scoped Γ A;
  typ_tm_scoped : well_scoped Γ t;
}.

Hint Resolve typ_ctx_scoped typ_ty_scoped typ_tm_scoped : rzbltyping.

Record ConvTypeRzbl (Γ : context) (A B : term) := {
  cvty_ctx_scoped : WfContextRzbl Γ;
  cvty_lhs_scoped : well_scoped Γ A;
  cvty_rhs_scoped : well_scoped Γ B;
}.

Hint Resolve cvty_ctx_scoped cvty_lhs_scoped cvty_rhs_scoped : rzbltyping.

Record ConvTermRzbl (Γ : context) (A t u : term) := {
  cvtm_ctx_scoped : WfContextRzbl Γ;
  cvtm_typ_scoped : well_scoped Γ A;
  cvtm_lhs_scoped : well_scoped Γ t;
  cvtm_rhs_scoped : well_scoped Γ u;
}.

Hint Resolve cvtm_ctx_scoped cvtm_typ_scoped cvtm_lhs_scoped cvtm_rhs_scoped : rzbltyping.

Record TypeRedClosure (Γ : context) (A B : term) := {
  tyred_ctx_scoped : WfContextRzbl Γ;
  tyred_lhs_scoped : well_scoped Γ A;
  tyred_rhs_scoped : well_scoped Γ B;
  tyred_red : [A ⤳* B];
}.

Record TermRedClosure (Γ : context) (A t u : term) := {
  tmred_ctx_scoped : WfContextRzbl Γ;
  tmred_typ_scoped : well_scoped Γ A;
  tmred_lhs_scoped : well_scoped Γ t;
  tmred_rhs_scoped : well_scoped Γ u;
  tmred_red : [t ⤳* u];
}.

Record RzblNeutralConversion (Γ : context) (A : term) (m n : term) := {
  cvne_ctx_scoped : WfContextRzbl Γ;
  cvne_typ_scoped : well_scoped Γ A;
  cvne_lhs_whne   : whne m;
  cvne_lhs_scoped : well_scoped Γ m;
  cvne_rhs_whne   : whne n;
  cvne_rhs_scoped : well_scoped Γ n;
}.

Module RealizabilityTypingData.

  Definition rz : tag.
  Proof.
  constructor.
  Qed.

  #[export] Instance WfContext_Rzbl : WfContext rz := WfContextRzbl.
  #[export] Instance WfType_Rzbl : WfType rz := WfTypeRzbl.
  #[export] Instance Typing_Rzbl : Typing rz := TypingRzbl.
  #[export] Instance ConvType_Rzbl : ConvType rz := ConvTypeRzbl.
  #[export] Instance ConvTerm_Rzbl : ConvTerm rz := ConvTermRzbl.
  #[export] Instance RedType_Rzbl : RedType rz := TypeRedClosure.
  #[export] Instance RedTerm_Rzbl : RedTerm rz := TermRedClosure.
  #[export] Instance ConvNeuConv_Rzbl : ConvNeuConv rz := RzblNeutralConversion.

  Ltac fold_rzbl :=
    change WfContextRzbl with (wf_context (ta := rz)) in * ;
    change WfTypeRzbl with (wf_type (ta := rz)) in *;
    change TypingRzbl with (typing (ta := rz)) in * ;
    change ConvTypeRzbl with (conv_type (ta := rz)) in * ;
    change ConvTermRzbl with (conv_term (ta := rz)) in * ;
    change TypeRedClosure with (red_ty (ta := rz)) in *;
    change TermRedClosure with (red_tm (ta := rz)) in *;
    change RzblNeutralConversion with (conv_neu_ty (ta := rz)) in *.

  Ltac unfold_rzbl :=
    change (wf_context (ta := rz)) with WfContextRzbl in * ;
    change (wf_type (ta := rz)) with WfTypeRzbl in *;
    change (typing (ta := rz)) with TypingRzbl in * ;
    change (conv_type (ta := rz)) with ConvTypeRzbl in * ;
    change (conv_term (ta := rz)) with ConvTermRzbl in * ;
    change (red_ty (ta := rz)) with TypeRedClosure in *;
    change (red_tm (ta := rz)) with TermRedClosure in *;
    change (conv_neu_ty (ta := rz)) with RzblNeutralConversion in *.

  Smpl Add fold_rzbl : refold.

End RealizabilityTypingData.

Module RealizabilityTypingProperties.

Import RealizabilityTypingData.

Local Ltac case_rzbl := repeat match goal with
| [ H : wf_type (ta := rz) _ _ |- _ ] => destruct H
| [ H : typing (ta := rz) _ _ _ |- _ ] => destruct H
| [ H : conv_type (ta := rz) _ _ _ |- _ ] => destruct H
| [ H : conv_term (ta := rz) _ _ _ _ |- _ ] => destruct H
| [ H : red_ty (ta := rz) _ _ _ |- _ ] => destruct H
| [ H : red_tm (ta := rz) _ _ _ _ |- _ ] => destruct H
| [ H : conv_neu_ty (ta := rz) _ _ _ _ |- _ ] => destruct H
end.

#[export, refine] Instance WfContextRzblProperties : WfContextProperties (ta := rz) := {}.
Proof.
all: intros; case_rzbl; auto with rzbltyping.
+ constructor.
+ now constructor.
Qed.

#[export, refine] Instance WfTypeRzblProperties : WfTypeProperties (ta := rz) := {}.
Proof.
all: intros; case_rzbl; split; cbn; auto using well_scoped_ren, scoped_S_up.
Qed.

#[export, refine] Instance TypingRzblProperties : TypingProperties (ta := rz) := {}.
Proof.
all: intros; case_rzbl; split; cbn in *;
  prod_splitter; repeat match goal with [ H : _ /\ _ |- _ ] => destruct H end;
  try apply scoped_subst1; cbn;
  eauto using well_scoped_ren, scoped_S_up, scoped_up_S.
+ now eapply wf_in_ctx_scoped.
+ now eapply wf_in_ctx.
+ now apply scoped_up_S.
+ now apply scoped_up_S.
+ eapply scoped_subs; [eauto|]; cbn.
  intros [|[|]]; cbn; eauto with arith.
+ now apply scoped_SS_up.
Qed.

#[export, refine] Instance ConvTypeRzblProperties : ConvTypeProperties (ta := rz) := {}.
Proof.
all: intros; case_rzbl; split; cbn; auto using well_scoped_ren, scoped_S_up.
+ now split; case_rzbl.
+ now split; case_rzbl.
Qed.

#[export, refine] Instance ConvTermRzblProperties : ConvTermProperties (ta := rz) := {}.
Proof.
all: intros; case_rzbl; split; cbn in *; prod_splitter; auto using well_scoped_ren, scoped_S_up.
+ now split; case_rzbl.
+ now split; case_rzbl.
Qed.

#[export, refine] Instance ConvNeuRzblProperties : ConvNeuProperties (ta := rz) := {}.
Proof.
all: intros; case_rzbl; try constructor; cbn in *;
  prod_splitter; repeat match goal with [ H : _ /\ _ |- _ ] => destruct H end;
  try apply scoped_subst1; cbn;
  auto using well_scoped_ren, scoped_S_up, whne, whne_ren_wl.
+ now split; case_rzbl.
+ now split; case_rzbl.
+ now apply scoped_up_S.
+ now apply scoped_up_S.
+ eapply scoped_subs; [eauto|].
  intros [|[|]]; cbn; eauto with arith.
+ now apply scoped_SS_up.
+ now apply scoped_SS_up.
Qed.

#[export, refine] Instance RedTypeRzblProperties : RedTypeProperties (ta := rz) := {}.
Proof.
all: intros; case_rzbl; try split; case_rzbl; eauto using well_scoped_ren.
+ apply credalg_wk; eauto using wk_inj.
+ reflexivity.
+ now etransitivity.
Qed.

#[export, refine] Instance RedTermRzblProperties : RedTermProperties (ta := rz) := {}.
Proof.
all: intros; case_rzbl; try constructor; cbn in *;
  prod_splitter; repeat match goal with [ H : _ /\ _ |- _ ] => destruct H end;
  try apply scoped_subst1; cbn;
  eauto using well_scoped_ren, scoped_S_up, redalg_one_step, OneRedAlg.
+ apply credalg_wk; eauto using wk_inj.
+ now apply scoped_up_S.
+ now apply redalg_app.
+ now apply redalg_natElim.
+ now apply redalg_natEmpty.
+ now apply redalg_fst.
+ prod_splitter; eauto.
  now apply scoped_S_up.
+ now apply scoped_up_S.
+ now apply redalg_snd.
+ eapply scoped_subs; [eassumption|].
  cbn; intros [|[|]]; cbn; eauto 4 with arith.
+ now apply scoped_SS_up.
+ eapply scoped_subs; [eauto|].
  intros [|[|]]; cbn; eauto with arith.
+ now apply scoped_SS_up.
+ now apply scoped_SS_up.
+ now apply redalg_idElim.
+ now apply redalg_decide.
+ now apply redalg_reflect.
+ reflexivity.
+ now case_rzbl.
+ now case_rzbl.
+ now case_rzbl.
+ now case_rzbl.
+ case_rzbl; now etransitivity.
Qed.

#[export] Instance RealizabilityTypingProperties : GenericTypingProperties rz _ _ _ _ _ _ _ _ := {}.

End RealizabilityTypingProperties.
