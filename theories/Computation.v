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
  tApp (tNatElim (arr tPNat U)
    (tLambda tPNat (tIsVal (tApp (tRel 0) tZero) v⟨↑⟩))
    (tLambda tNat (tLambda (arr tPNat U) (tLambda tPNat
      (tAnd
        (tIsNil (tApp (tRel 0) (tRel 2)))
        (tApp (tRel 1) (tShift (tRel 0)))))))
    k) n.

(*
Fixpoint eval (k : nat) (v : nat) : (nat -> nat) -> Set :=
| 0 => fun n => n 0 = S v
| S k => fun n => n k = 0 /\ eval k v (fun c => n (S c))
end
*)

Lemma tAnd_subst : forall A B σ, (tAnd A B)[σ] = tAnd A[σ] B[σ].
Proof.
intros; cbn; unfold tAnd.
f_equal; now asimpl.
Qed.

Lemma tIsNil_subst : forall t σ, (tIsNil t)[σ] = tIsNil t[σ].
Proof.
reflexivity.
Qed.

Lemma tIsVal_subst : forall t v σ, (tIsVal t v)[σ] = tIsVal t[σ] v[σ].
Proof.
reflexivity.
Qed.

Lemma tShift_subst : forall t σ, (tShift t)[σ] = tShift t[σ].
Proof.
intros; unfold tShift; cbn.
do 2 f_equal; now asimpl.
Qed.

Lemma tEval_ren : forall n k v ρ,
  (tEval n k v)⟨ρ⟩ = tEval n⟨ρ⟩ k⟨ρ⟩ v⟨ρ⟩.
Proof.
intros; unfold tEval; cbn; repeat f_equal.
unfold tIsVal; do 2 f_equal.
now asimpl.
Qed.

Lemma tEval_subst : forall n k v σ,
  (tEval n k v)[σ] = tEval n[σ] k[σ] v[σ].
Proof.
intros; unfold tEval; cbn; repeat f_equal.
unfold tIsVal; do 2 f_equal.
now asimpl.
Qed.

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

Axiom quote : term -> nat.
Axiom run : term.

(** Slightly contrived way to state that [run] is closed. *)
Axiom run_subst : forall (σ : nat -> term), run[σ] = run.

Lemma run_ren : forall ρ, run⟨ρ⟩ = run.
Proof.
intros; rewrite rinstInst'_term; apply run_subst.
Qed.

(** Derived notions from the model *)

Definition tTotal t u :=
  tEval (tApp (tApp run (tQuote t)) u) (tStep t u) (tApp t u).
(** eval (run (quote t) u) (step t u) (t u) *)

Lemma tTotal_ren : forall t u ρ,
  (tTotal t u)⟨ρ⟩ = tTotal t⟨ρ⟩ u⟨ρ⟩.
Proof.
intros; unfold tTotal; cbn - [tEval].
f_equal; rewrite tEval_ren; cbn; do 2 f_equal; try now asimpl.
now rewrite run_ren.
Qed.

Lemma tTotal_subst : forall t u σ,
  (tTotal t u)[σ] = tTotal t[σ] u[σ].
Proof.
intros; unfold tTotal; cbn - [tEval].
f_equal; rewrite tEval_subst; cbn; do 2 f_equal; try now asimpl.
f_equal; apply run_subst.
Qed.

(*
Definition qTotal (t u k v : nat) :=
  tPair tNat (tEval (tApp (tApp model.(run) (qNat t)) (qNat u)) (tRel 0) (qNat v))
    (qNat k) (qEvalTm k v).

Lemma qTotal_ren : forall (t u k v : nat) (ρ : nat -> nat), (qTotal t u k v)⟨ρ⟩ = qTotal t u k v.
Proof.
intros; unfold qTotal; cbn - [tEval]; f_equal.
+ rewrite tEval_ren; f_equal; [|apply qNat_ren].
  cbn; f_equal; [|apply qNat_ren].
  cbn; f_equal; [|apply qNat_ren].
  apply run_ren.
+ apply qNat_ren.
+ apply qEvalTm_ren.
Qed.

Lemma closedn_qTotal : forall t u k v n, closedn n (qTotal t u k v).
Proof.
intros; unfold closedn, qTotal; cbn - [qEvalTm].
apply andb_true_intro; split; [apply closedn_qNat|].
apply closedn_qEvalTm.
Qed.
*)

(* Compute the smallest n s.t. a function returns Some *)

Section Murec.

Context {A : Type}.
Variable f : nat -> option A.

Fixpoint murec0 (n : nat) :=
match n with
| 0 => None
| S n =>
  match murec0 n with
  | None =>
    match f n with
    | Some v => Some v
    | None => murec0 n
    end
  | Some v => Some v
  end
end.

End Murec.

Definition murec {A} f n :=
  @murec0 (nat × A) (fun n => match f n with None => None | Some v => Some (n, v) end) n.

Lemma murec0_S : forall A f k r, @murec0 A f k = Some r -> @murec0 A f (S k) = Some r.
Proof.
intros; cbn; now rewrite H.
Qed.

Lemma murec_S : forall A f k r, @murec A f k = Some r -> @murec A f (S k) = Some r.
Proof.
intros; now apply murec0_S.
Qed.

Lemma murec_mon : forall A f k k' r, k <= k' -> @murec A f k = Some r -> murec f k' = Some r.
Proof.
induction 1; eauto using murec_S.
Qed.

Lemma murec_det : forall A f k k' r r', @murec A f k = Some r -> murec f k' = Some r' -> r = r'.
Proof.
intros A f k k' r r' Hk Hk'.
assert (murec f (max k k') = Some r).
{ apply (murec_mon _ _ k); [Lia.lia|eauto]. }
assert (murec f (max k k') = Some r').
{ apply (murec_mon _ _ k'); [Lia.lia|eauto]. }
now congruence.
Qed.

Lemma minimize (f : nat -> bool) (n : nat) :
  is_true (f n) -> ∑ m, is_true (f m) × (forall m', m' < m -> ~ is_true (f m')).
Proof.
revert f; induction n; intros f Hn.
+ exists 0; split; [tea|Lia.lia].
+ destruct (IHn (fun n => f (S n)) Hn) as (m&Hm&Hlt).
  remember (f 0) as b eqn:Hb; symmetry in Hb; destruct b.
  - exists 0; split; [tea|Lia.lia].
  - exists (S m); split; [tea|].
    intros []; [congruence|].
    intros; apply Hlt; Lia.lia.
Qed.

Lemma murec0_None : forall {A} {f k}, (forall k', k' < k -> f k' = None) -> @murec0 A f k = None.
Proof.
intros A f k Hk.
induction k; cbn.
+ reflexivity.
+ rewrite IHk; [rewrite Hk; eauto|].
  intros; now apply Hk.
Qed.

Lemma murec_None : forall {A} {f k}, (forall k', k' < k -> f k' = None) -> @murec A f k = None.
Proof.
intros A f k Hk; apply murec0_None.
intros; now rewrite Hk.
Qed.

Lemma murec0_None_rev : forall {A} {f k k'}, k' < k -> @murec0 A f k = None -> f k' = None.
Proof.
intros A f k k' Hlt Hk; revert k' Hlt; induction k; cbn in *.
+ intros; Lia.lia.
+ destruct (murec0 f k); [discriminate|].
  intros; destruct (PeanoNat.Nat.eq_dec k k').
  - subst; destruct (f k'); congruence.
  - apply IHk; eauto; Lia.lia.
Qed.

Lemma murec_None_rev : forall {A} {f k k'}, k' < k -> @murec A f k = None -> f k' = None.
Proof.
intros A f k k' Hlt Heq; unfold murec.
eapply murec0_None_rev in Heq; tea.
cbn in Heq; destruct (f k'); congruence.
Qed.

Lemma murec_Some_lt : forall {A} {f k k' v}, @murec A f k = Some (k', v) -> k' < k.
Proof.
induction k; intros k' v Heq; cbn in *.
+ discriminate.
+ fold (murec f k) in Heq.
  remember (murec f k) as w eqn:Hw in *; destruct w as [[]|].
  - injection Heq; intros; subst.
    enough (k' < k) by Lia.lia.
    eauto.
  - destruct (f k); [|congruence].
    injection Heq; intros; subst; Lia.lia.
Qed.

Lemma murec_intro {A} {f k v} :
  (forall k', k' < k -> f k' = None) -> f k = Some v ->
  @murec A f (S k) = Some (k, v).
Proof.
intros Hlt Hk; cbn.
rewrite murec0_None, Hk; eauto.
intros; rewrite Hlt; eauto.
Qed.

Lemma murec_elim_Some {A f k k₀ v} : @murec A f k₀ = Some (k, v) -> f k = Some v.
Proof.
intros Heq.
assert (Hlt : k < k₀) by now eapply murec_Some_lt.
revert k v Hlt Heq; induction k₀; intros k v Hlt Heq; cbn in *.
+ discriminate.
+ fold (murec f k₀) in Heq.
  remember (murec f k₀) as w eqn:Hw in *; destruct w as [[]|].
  - injection Heq; intros; subst.
    symmetry in Hw; apply murec_Some_lt in Hw.
    now apply IHk₀.
  - remember (f k₀) as z eqn:Hz in *; destruct z; [|discriminate].
    injection Heq; intros; now subst.
Qed.

Lemma murec_elim_None {A f k k₀ k' v} : k' < k -> @murec A f k₀ = Some (k, v) -> f k' = None.
Proof.
intros Hlt Heq.
remember (f k') as w eqn:Hf; symmetry in Hf; destruct w; [|reflexivity].
exfalso.
assert (Hlt₀ : k < k₀) by now eapply murec_Some_lt.
revert v a k k' Hlt Hlt₀ Heq Hf.
induction k₀.
+ intros; cbn; Lia.lia.
+ intros; cbn in *.
  fold (murec f k₀) in Heq.
  remember (murec f k₀) as w eqn:Hw in *; destruct w as [[]|].
  - injection Heq; intros; subst.
    symmetry in Hw; apply murec_Some_lt in Hw.
    now eapply (IHk₀ v a k k').
  - remember (f k₀) as z eqn:Hz in *; destruct z; [|discriminate].
    injection Heq; intros; subst.
    symmetry in Hw; eapply (murec_None_rev (k' := k')) in Hw; [|tea].
    congruence.
Qed.
