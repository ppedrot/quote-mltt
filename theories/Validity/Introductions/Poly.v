From Coq Require Import ssrbool.
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Escape Reflexivity Neutral Weakening Irrelevance Transitivity EqRedRight InstKripke.
From LogRel.LogicalRelation.Introductions Require Import Poly.
From LogRel.Validity Require Import Validity Irrelevance Properties Reflexivity Universe.

Set Universe Polymorphism.

Lemma eq_subst_1 F G Δ σ : G[up_term_term σ] = G[tRel 0 .: σ⟨ @wk1 Δ F[σ] ⟩].
Proof.
  now bsimpl.
Qed.

Lemma eq_subst_2 G a ρ σ : G[up_term_term σ][a .: ρ >> tRel] = G[a .: σ⟨ρ⟩].
Proof.
  bsimpl ; now substify.
Qed.

Set Printing Primitive Projection Parameters.

Section PolyValidity.

  Context `{GenericTypingProperties}.

  Context {l Γ F G} (VΓ : [||-v Γ])
    (VF : [Γ ||-v< l > F | VΓ ])
    (VG : [Γ ,, F ||-v< l > G | validSnoc VΓ VF]).

  Context {Δ σ σ'} (tΔ : [ |-[ ta ] Δ]) (Vσσ' : [VΓ | Δ ||-v σ ≅ σ' : _ | tΔ]).

  Lemma substPolyRed : PolyRed Δ l F[σ] G[up_term_term σ].
  Proof.
    pose proof (Vuσ := liftSubstEq' VF Vσσ').
    instValid Vσσ'; instValid Vuσ; escape.
    unshelve econstructor; tea.
    - intros; now eapply wk.
    - cbn; intros ??? ρ wfΔ' hab.
      rewrite eq_subst_2.
      pose proof (Vawkσ := consWkSubstEq VF Vσσ' ρ wfΔ' hab).
      now instValid Vawkσ.
    - cbn; intros ??? ρ wfΔ' hab.
      epose proof (Vabwkσ := consWkSubstEq VF (lrefl Vσσ') ρ wfΔ' hab).
      instValid Vabwkσ.
      rewrite !eq_subst_2; irrelevance.
  Qed.

  Lemma substEqPolyRedEq {F' G'} (VF' : [Γ ||-v< l > F' | VΓ ])
    (VG' : [Γ ,, F' ||-v< l > G' | validSnoc VΓ VF'])
    (VFF' : [Γ ||-v< l > F ≅ F' | VΓ | VF])
    (VGG' : [Γ ,, F ||-v< l > G ≅ G' | validSnoc VΓ VF | VG])
    (PFGσ : PolyRed Δ l F[σ] G[up_term_term σ])
    : PolyRedEq PFGσ F'[σ'] G'[up_term_term σ'].
  Proof.
     instValid Vσσ'.
    unshelve econstructor.
    - intros; irrelevanceRefl; now unshelve now eapply wkEq.
    - intros ??? ρ wfΔ' hab; rewrite eq_subst_2.
      unshelve epose proof (Vabwkσ := consWkSubstEq VF Vσσ' ρ wfΔ' (lrefl hab)).
      instValid Vabwkσ; irrelevance0; [|tea].
      now rewrite eq_subst_2.
  Qed.

  Lemma substPolyRedEq (PFGσ : PolyRed Δ l F[σ] G[up_term_term σ])
    : PolyRedEq PFGσ F[σ'] G[up_term_term σ'].
  Proof.
    eapply substEqPolyRedEq; tea.
    all: eapply reflValidTy.
  Qed.

End PolyValidity.


