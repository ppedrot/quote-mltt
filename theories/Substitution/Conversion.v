From Coq Require Import CRelationClasses.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context NormalForms Weakening GenericTyping LogicalRelation Validity.
From LogRel.LogicalRelation Require Import Irrelevance Escape Reflexivity Weakening Neutral.
From LogRel.Substitution Require Import  Irrelevance Properties.

Set Universe Polymorphism.

Section Conversion.
Context `{GenericTypingProperties}.

Set Printing Primitive Projection Parameters.


Lemma conv {Γ t A B l} (VΓ : [||-v Γ])
  (VA : [Γ ||-v<l> A | VΓ])
  (VB : [Γ ||-v<l> B | VΓ])
  (VeqAB : [Γ ||-v<l> A ≅ B | VΓ | VA])
  (Vt : [Γ ||-v<l> t : A | VΓ | VA]) :
  [Γ ||-v<l> t : B | VΓ | VB].
Proof.
  constructor; intros; eapply LRTmEqConv.
  2: now unshelve now eapply validTmExt.
  now eapply validTyEqLeft.
Qed.

Lemma convsym {Γ t A B l} (VΓ : [||-v Γ])
  (VA : [Γ ||-v<l> A | VΓ])
  (VB : [Γ ||-v<l> B | VΓ])
  (VeqAB : [Γ ||-v<l> A ≅ B | VΓ | VA])
  (Vt : [Γ ||-v<l> t : B | VΓ | VB]) :
  [Γ ||-v<l> t : A | VΓ | VA].
Proof.
  eapply conv; tea; now eapply symValidTyEq.
Qed.

Lemma convEq {Γ t u A B l} (VΓ : [||-v Γ])
  (VA : [Γ ||-v<l> A | VΓ])
  (VB : [Γ ||-v<l> B | VΓ])
  (VeqAB : [Γ ||-v<l> A ≅ B | VΓ | VA])
  (Vt : [Γ ||-v<l> t ≅ u : A | VΓ | VA]) :
  [Γ ||-v<l> t ≅ u : B | VΓ | VB].
Proof.
  constructor; intros; eapply LRTmEqConv.
  1: (unshelve now eapply validTyEqLeft); cycle 2; tea.
  now eapply validTmEq.
Qed.


Lemma convSubstEqCtx1 {Γ Δ A B l σ σ'}
  (VΓ : [||-v Γ])
  (wfΔ : [|- Δ])
  (VΓA : [||-v Γ ,, A])
  (VΓB : [||-v Γ ,, B])
  (VA : [_ ||-v<l> A | VΓ])
  (VB : [_ ||-v<l> B | VΓ])
  (VAB : [_ ||-v<l> A ≅ B | VΓ | VA])
  (Vσσ': [_ ||-v σ ≅ σ' : _ | VΓA | wfΔ]) :
  [_ ||-v σ ≅ σ' : _ | VΓB | wfΔ].
Proof.
  pose proof (invValiditySnoc VΓA) as [? [? [?]]]; subst.
  pose proof (invValiditySnoc VΓB) as [? [? [?]]]; subst.
  eapply irrelevanceSubstEqExt.
  1: rewrite <- scons_eta'; reflexivity.
  1: rewrite <- scons_eta'; reflexivity.
  unshelve eapply consSubstEq.
  1: epose (eqTail Vσσ'); irrValid.
  eapply LRTmEqConv.
  2: irrelevanceRefl; eapply eqHead.
  eapply validTyEqLeft; [exact VB| exact VAB].
  Unshelve. 6: tea.
    3: eapply irrelevanceSubstEq; now eapply eqTail.
    tea.
Qed.

Lemma convCtx1 {Γ A B P l}
  (VΓ : [||-v Γ])
  (VΓA : [||-v Γ ,, A])
  (VΓB : [||-v Γ ,, B])
  (VA : [_ ||-v<l> A | VΓ])
  (VB : [_ ||-v<l> B | VΓ])
  (VAB : [_ ||-v<l> A ≅ B | VΓ | VA])
  (VP : [_ ||-v<l> P | VΓA]) :
  [_ ||-v<l> P | VΓB].
Proof.
  opector; intros.
  - eapply validTy; tea; eapply convSubstEqCtx1; tea; now eapply symValidTyEq.
  - irrelevanceRefl; unshelve eapply validTyExt.
    3,4: tea.
    eapply convSubstEqCtx1; tea; now eapply symValidTyEq.
    Unshelve. all: tea.
Qed.

Lemma convEqCtx1 {Γ A B P Q l}
  (VΓ : [||-v Γ])
  (VΓA : [||-v Γ ,, A])
  (VΓB : [||-v Γ ,, B])
  (VA : [_ ||-v<l> A | VΓ])
  (VB : [_ ||-v<l> B | VΓ])
  (VAB : [_ ||-v<l> A ≅ B | VΓ | VA])
  (VP : [_ ||-v<l> P | VΓA])
  (VPB : [_ ||-v<l> P | VΓB])
  (VPQ : [_ ||-v<l> P ≅ Q | VΓA | VP]) :
  [_ ||-v<l> P ≅ Q | VΓB | VPB].
Proof.
  constructor; intros; irrelevanceRefl.
  eapply validTyEq; tea.
  Unshelve. 1: tea.
  unshelve eapply convSubstEqCtx1; cycle 5; tea; now eapply symValidTyEq.
Qed.

Lemma convTmEqCtx1 {Γ A B C t u l}
  (VΓ : [||-v Γ])
  (VΓA : [||-v Γ ,, A])
  (VΓB : [||-v Γ ,, B])
  (VA : [_ ||-v<l> A | VΓ])
  (VB : [_ ||-v<l> B | VΓ])
  (VC : [_ ||-v<l> C | VΓA])
  (VC' : [_ ||-v<l> C | VΓB])
  (VAB : [_ ||-v<l> A ≅ B | VΓ | VA])
  (VPtu : [_ ||-v<l> t ≅ u : _ | VΓA | VC]) :
  [_ ||-v<l> t ≅ u : _ | VΓB | VC'].
Proof.
  constructor; intros; irrelevanceRefl.
  (unshelve now eapply validTmEq); tea.
  now unshelve (eapply convSubstEqCtx1; tea; now eapply symValidTyEq).
Qed.


Lemma convSubstEqCtx2 {Γ Δ A1 B1 A2 B2 l σ σ'}
  (VΓ : [||-v Γ])
  (wfΔ : [|- Δ])
  (VA1 : [_ ||-v<l> A1 | VΓ])
  (VB1 : [_ ||-v<l> B1 | VΓ])
  (VAB1 : [_ ||-v<l> A1 ≅ B1 | VΓ | VA1])
  (VΓA1 := validSnoc VΓ VA1)
  (VΓB1 := validSnoc VΓ VB1)
  (VA2 : [_ ||-v<l> A2 | VΓA1])
  (VB2 : [_ ||-v<l> B2 | VΓA1])
  (VAB : [_ ||-v<l> A2 ≅ B2 | VΓA1 | VA2])
  (VB2' := convCtx1 VΓ VΓA1 VΓB1 VA1 VB1 VAB1 VB2)
  (VΓA12 := validSnoc VΓA1 VA2)
  (VΓB12 := validSnoc VΓB1 VB2')
  (Vσσ' : [_ ||-v σ ≅ σ' : _ | VΓA12 | wfΔ]) :
  [_ ||-v σ ≅ σ' : _ | VΓB12 | wfΔ].
Proof.
  eapply irrelevanceSubstEqExt.
  1,2: rewrite <- scons_eta'; reflexivity.
  unshelve eapply consSubstEq.
  + unshelve (eapply convSubstEqCtx1; tea); tea.
    now eapply eqTail.
  + unshelve eapply LRTmEqConv; cycle 3.
    2: now eapply eqHead.
    1: eapply validTyEqLeft; [|tea]; tea.
  Unshelve. all: tea.
Qed.

Lemma convSubstEqCtx2' {Γ Δ A1 B1 A2 B2 l σ σ'}
  (VΓ : [||-v Γ])
  (wfΔ : [|- Δ])
  (VΓA1 : [||-v Γ ,, A1])
  (VΓA12 : [||-v Γ ,, A1 ,, A2])
  (VΓB12 : [||-v Γ ,, B1 ,, B2])
  (VA1 : [_ ||-v<l> A1 | VΓ])
  (VB1 : [_ ||-v<l> B1 | VΓ])
  (VAB1 : [_ ||-v<l> A1 ≅ B1 | VΓ | VA1])
  (VA2 : [_ ||-v<l> A2 | VΓA1])
  (VB2 : [_ ||-v<l> B2 | VΓA1])
  (VAB : [_ ||-v<l> A2 ≅ B2 | VΓA1 | VA2])
  (Vσσ' : [_ ||-v σ ≅ σ' : _ | VΓA12 | wfΔ]) :
  [_ ||-v σ ≅ σ' : _ | VΓB12 | wfΔ].
Proof.
  eapply irrelevanceSubstEq.
  eapply convSubstEqCtx2; irrValid.
  Unshelve. all: tea; irrValid.
Qed.

Lemma convCtx2 {Γ A1 B1 A2 B2 P l}
  (VΓ : [||-v Γ])
  (VA1 : [_ ||-v<l> A1 | VΓ])
  (VB1 : [_ ||-v<l> B1 | VΓ])
  (VAB1 : [_ ||-v<l> A1 ≅ B1 | VΓ | VA1])
  (VΓA1 := validSnoc VΓ VA1)
  (VΓB1 := validSnoc VΓ VB1)
  (VA2 : [_ ||-v<l> A2 | VΓA1])
  (VB2 : [_ ||-v<l> B2 | VΓA1])
  (VAB : [_ ||-v<l> A2 ≅ B2 | VΓA1 | VA2])
  (VB2' := convCtx1 VΓ VΓA1 VΓB1 VA1 VB1 VAB1 VB2)
  (VΓA12 := validSnoc VΓA1 VA2)
  (VΓB12 := validSnoc VΓB1 VB2')
  (VP : [_ ||-v<l> P | VΓA12]) :
  [_ ||-v<l> P | VΓB12].
Proof.
  assert [_ ||-v<l> A2 | VΓB1] by now eapply convCtx1.
  assert [_ ||-v<l> B1 ≅ A1 | _ | VB1] by now eapply symValidTyEq.
  assert [_ ||-v<l> B2 ≅ A2 | _ | VB2'] by (eapply convEqCtx1; tea; now eapply symValidTyEq).
  opector; intros.
  - eapply validTy; tea; now eapply convSubstEqCtx2'.
  - irrelevanceRefl; unshelve eapply validTyExt.
    3,4: tea.
    eapply convSubstEqCtx2'; tea.
    Unshelve. tea.
Qed.

Lemma convCtx2' {Γ A1 A2 B1 B2 P l}
  (VΓ : [||-v Γ])
  (VA1 : [_ ||-v<l> A1 | VΓ])
  (VB1 : [_ ||-v<l> B1 | VΓ])
  (VAB1 : [_ ||-v<l> A1 ≅ B1 | VΓ | VA1])
  (VΓA1 : [||-v Γ ,, A1])
  (VΓB1 : [||-v Γ ,, B1])
  (VA2 : [_ ||-v<l> A2 | VΓA1])
  (VB2 : [_ ||-v<l> B2 | VΓA1])
  (VAB : [_ ||-v<l> A2 ≅ B2 | VΓA1 | VA2])
  (VB2' : [_ ||-v<l> B2 | VΓB1])
  (VΓA12 : [||-v Γ ,, A1 ,, A2])
  (VΓB12 : [||-v Γ ,, B1,, B2])
  (VP : [_ ||-v<l> P | VΓA12]) :
  [_ ||-v<l> P | VΓB12].
Proof.
  eapply irrelevanceTy; eapply convCtx2; irrValid.
  Unshelve. all: tea; irrValid.
Qed.


End Conversion.
