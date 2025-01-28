From Coq Require Import ssrbool.
From LogRel Require Import Utils Syntax.All GenericTyping LogicalRelation.
From LogRel.LogicalRelation Require Import Escape Reflexivity Neutral Weakening Irrelevance Induction NormalRed EqRedRight.
From LogRel.LogicalRelation.Introductions Require Import Poly.

Set Universe Polymorphism.

Section PolyRedPi.
  Context `{GenericTypingProperties}.

  Lemma LRPiPoly0 {Γ l A B} (PAB : PolyRed Γ l A B) : [Γ ||-Π<l> tProd A B].
  Proof.
    econstructor; tea; pose proof (polyRedId PAB) as []; escape.
    + eapply redtywf_refl; gen_typing.
    + unshelve eapply escapeEq; tea; eapply reflLRTyEq.
    + eapply convty_prod; tea; unshelve eapply escapeEq; tea; eapply reflLRTyEq.
  Defined.

  Definition LRPiPoly {Γ l A B} (PAB : PolyRed Γ l A B) : [Γ ||-<l> tProd A B] := LRPi' (LRPiPoly0 PAB).

  Lemma LRPiPolyEq0 {Γ l A A' B B'} (PAB : PolyRed Γ l A B) (Peq : PolyRedEq PAB A' B') :
    [Γ |- A'] -> [Γ ,, A' |- B'] ->
    [Γ ||-Π tProd A B ≅ tProd A' B' | LRPiPoly0 PAB].
  Proof.
    econstructor; cbn; tea.
    + eapply redtywf_refl; gen_typing.
    + pose proof (polyRedEqId PAB Peq) as []; now escape.
    + pose proof (polyRedEqId PAB Peq) as []; escape.
      eapply convty_prod; tea.
      eapply escape; now apply (polyRedId PAB).
  Qed.

  Lemma LRPiPolyEq {Γ l A A' B B'} (PAB : PolyRed Γ l A B) (Peq : PolyRedEq PAB A' B') :
    [Γ |- A'] -> [Γ ,, A' |- B'] ->
    [Γ ||-<l> tProd A B ≅ tProd A' B' | LRPiPoly PAB].
  Proof.
    now eapply LRPiPolyEq0.
  Qed.

  Lemma LRPiPolyEq' {Γ l A A' B B'} (PAB : PolyRed Γ l A B) (Peq : PolyRedEq PAB A' B') (RAB : [Γ ||-<l> tProd A B]):
    [Γ |- A'] -> [Γ ,, A' |- B'] ->
    [Γ ||-<l> tProd A B ≅ tProd A' B' | RAB].
  Proof.
    intros; irrelevanceRefl; now eapply LRPiPolyEq.
  Qed.

End PolyRedPi.
