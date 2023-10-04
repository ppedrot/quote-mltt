(** * LogRel.Computation: internal definitions related to the computation model. *)
From Coq Require Import ssrbool.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst.

(** A bunch of helpers and notations *)

Definition tAnd A B := tSig A B⟨↑⟩.

(* We represent code as natural numbers for simplicity *)
Definition tCode := tNat.

(* Partial natural numbers as step-indexed nats.
   For α : tPNat, the evaluation of f is the potential
   number v such that there is n with f n = S v and f m = 0 for all
   m < n. *)
Definition tPNat := arr tNat tNat.

(* tIsVal m n ~ m = S n *)
Definition tIsVal m n := tId tNat m (tSucc n).

(* tIsNil m ~ m = 0 *)
Definition tIsNil m := tId tNat m tZero.

(* tShift α := fun k : nat => α (S k) *)
Definition tShift (α : term) := tLambda tNat (tApp α⟨↑⟩ (tSucc (tRel 0))).

(* tEval n k v ~ n evaluates to v in k steps *)
Definition tEval (n k v : term) :=
  tNatElim (arr tPNat U)
    (tLambda tPNat (tIsVal (tApp (tRel 0) tZero) v⟨↑⟩))
    (tLambda tNat (tLambda (arr tPNat U) (tLambda tPNat
      (tAnd
        (tIsNil (tApp (tRel 0) (tSucc (tRel 2))))
        (tApp (tRel 1) (tShift (tRel 0)))))))
    k.

(*
Fixpoint eval (k : nat) (v : nat) : (nat -> nat) -> Set :=
| 0 => fun n => n 0 = S v
| S k => fun n => n (S k) = 0 /\ eval k v (fun c => n (S c))
end
*)

Fixpoint qNat (n : nat) := match n with
| 0 => tZero
| S n => tSucc (qNat n)
end.

Lemma qNat_ren : forall n ρ, (qNat n)⟨ρ⟩ = qNat n.
Proof.
intros n ρ; induction n; cbn in *; try f_equal; eauto.
Qed.

Lemma qNat_subst : forall n σ, (qNat n)[σ] = qNat n.
Proof.
intros n ρ; induction n; cbn in *; try f_equal; eauto.
Qed.

(** Axiomatic definition of a computation model internal to MLTT *)

Record Model := {
  quote : term -> nat;
}.

Axiom model : Model.
