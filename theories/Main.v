(** * Derive the main properties of typing. *)
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Computation Notations Context NormalForms NormalEq Weakening
  DeclarativeTyping GenericTyping DeclarativeInstance UntypedReduction.

From LogRel Require Import Fundamental TypeConstructorsInj.
From LogRel Require Import Consequences.

Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Set Printing Primitive Projection Parameters.

Import DeclarativeTypingData.

Lemma consistency : forall t, [nil |-[de] t : tEmpty] -> False.
Proof.
intros t Ht.
now eapply consistency.
Qed.

Print Assumptions consistency.

(*
Axioms:
run : term
quote : term -> nat
run_subst : forall σ : nat -> term, run[[σ]] = run
run_spec_Some
  : forall (t : term) (u k v : nat),
    eval true (tApp t (qNat u)) k = Some (qNat v) ->
    [[tApp (tApp (tApp run (qNat (quote t))) (qNat u)) (qNat k) ⇶* tSucc (qNat v)]]
run_spec_None
  : forall (t : term) (u k : nat),
    eval true (tApp t (qNat u)) k = None ->
    [[tApp (tApp (tApp run (qNat (quote t))) (qNat u)) (qNat k) ⇶* tZero]]
*)

Lemma strong_normalization : forall Γ A t, [Γ |-[de] t : A] -> ∑ v, [t ⇊ v].
Proof.
intros; now eapply strong_normalization.
Qed.

Print Assumptions strong_normalization.

Lemma nat_canonicity_dred {t} : [ε |-[de] t : tNat] -> ∑ n : nat, [t ⇊ qNat n].
Proof.
intros; now eapply nat_canonicity_dred.
Qed.

Print Assumptions nat_canonicity_dred.


