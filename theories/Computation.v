(** * LogRel.Computation: internal definitions related to the computation model. *)
From Coq Require Import ssrbool.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Closed.

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

Fixpoint uNat (n : term) := match n with
| tZero => Some 0
| tSucc n =>
  match uNat n with
  | None => None
  | Some n => Some (S n)
  end
| _ => None
end.

(* Builds the type [0 = 0 × ... × 0 = 0 × tSucc v = tSucc v] *)
Fixpoint qEvalTy (n : nat) (v : nat) := match n with
| 0 => tId tNat (tSucc (qNat v)) (tSucc (qNat v))
| S n => tAnd (tId tNat tZero tZero) (qEvalTy n v)
end.

(* Builds a canonical proof of [0 = 0 × ... × 0 = 0 × tSucc v = tSucc v] *)
Fixpoint qEvalTm (n : nat) (v : nat) := match n with
| 0 => tRefl tNat (tSucc (qNat v))
| S n => tPair (tId tNat tZero tZero) (qEvalTy n v) (tRefl tNat tZero) (qEvalTm n v)
end.

Lemma uNat_qNat : forall n, uNat (qNat n) = Some n.
Proof.
induction n; cbn; try congruence.
rewrite IHn; eauto.
Qed.

Lemma qNat_uNat : forall t n, uNat t = Some n -> t = qNat n.
Proof.
intros t n; revert t; induction n; intros; destruct t; cbn in *; try discriminate.
+ reflexivity.
+ destruct (uNat t); cbn in *; discriminate.
+ remember (uNat t) as m eqn:Hm; symmetry in Hm; destruct m; cbn in *.
  - f_equal; apply IHn; congruence.
  - discriminate.
Qed.

Lemma qNat_inj : forall m n, qNat m = qNat n -> m = n.
Proof.
induction m; intros []; cbn; intros; try congruence.
f_equal; apply IHm; congruence.
Qed.

Lemma qNat_ren : forall n ρ, (qNat n)⟨ρ⟩ = qNat n.
Proof.
intros n ρ; induction n; cbn in *; try f_equal; eauto.
Qed.

Lemma qNat_subst : forall n σ, (qNat n)[σ] = qNat n.
Proof.
intros n ρ; induction n; cbn in *; try f_equal; eauto.
Qed.

Lemma closedn_qNat : forall n k, closedn k (qNat n).
Proof.
unfold closedn; induction n; intros; cbn in *; eauto.
Qed.

Lemma qEvalTy_ren : forall n v ρ, (qEvalTy n v)⟨ρ⟩ = qEvalTy n v.
Proof.
intros n; induction n; intros v ρ; cbn in *.
+ now rewrite qNat_ren.
+ unfold tAnd; f_equal.
  rewrite !IHn; reflexivity.
Qed.

Lemma qEvalTy_subst : forall n v σ, (qEvalTy n v)[σ] = qEvalTy n v.
Proof.
intros n; induction n; intros v σ; cbn in *.
+ now rewrite qNat_subst.
+ unfold tAnd; f_equal.
  rewrite qEvalTy_ren, !IHn; reflexivity.
Qed.

Lemma closedn_qEvalTy : forall n v k, closedn k (qEvalTy n v).
Proof.
unfold closedn; induction n; intros; cbn in *.
- apply andb_true_intro; split; apply closedn_qNat.
- apply closedn_shift, IHn.
Qed.

Lemma qEvalTm_ren : forall n v ρ, (qEvalTm n v)⟨ρ⟩ = qEvalTm n v.
Proof.
intros n; induction n; intros v ρ; cbn in *.
+ now rewrite qNat_ren.
+ rewrite !IHn, qEvalTy_ren; reflexivity.
Qed.

Lemma qEvalTm_subst : forall n v σ, (qEvalTm n v)[σ] = qEvalTm n v.
Proof.
intros n; induction n; intros v σ; cbn in *.
+ now rewrite qNat_subst.
+ rewrite !IHn, qEvalTy_subst; reflexivity.
Qed.

Lemma closedn_qEvalTm : forall n v k, closedn k (qEvalTm n v).
Proof.
unfold closedn; induction n; intros; cbn in *.
- apply closedn_qNat.
- apply IHn.
Qed.

(** Axiomatic definition of a computation model internal to MLTT *)

Record Model := {
  quote : term -> nat;
}.

Axiom model : Model.
