From Coq Require Import ssrbool Lia.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Context.

(** Essentially closed terms. We ignore type annotations on λ-abstractions and pairs for closedness. *)

Fixpoint is_closedn (n : nat) (t : term) {struct t} :=
match t with
| tRel m => PeanoNat.Nat.ltb m n
| tSort _ => true
| tProd A B => andb (is_closedn n A) (is_closedn (S n) B)
| tLambda A t => is_closedn (S n) t (* Ignore annotation *)
| tApp t u => andb (is_closedn n t) (is_closedn n u)
| tNat => true
| tZero => true
| tSucc t => is_closedn n t
| tNatElim P hz hs t =>
  andb (is_closedn (S n) P)
    (andb (is_closedn n hz) (andb (is_closedn n hs) (is_closedn n t)))
| tEmpty => true
| tEmptyElim P t =>
  andb (is_closedn (S n) P) (is_closedn n t)
| tSig A B =>
  andb (is_closedn n A) (is_closedn (S n) B)
| tPair A B a b =>
  andb (is_closedn n a) (is_closedn n b)
| tFst t => is_closedn n t
| tSnd t => is_closedn n t
| tId A t u => andb (is_closedn n A) (andb (is_closedn n t) (is_closedn n u))
| tRefl A t => andb (is_closedn n A) (is_closedn n t)
| tIdElim A x P hr y e =>
  andb (is_closedn n A)
  (andb (is_closedn n x)
  (andb (is_closedn (S (S n)) P)
    (andb (is_closedn n hr) (andb (is_closedn n y) (is_closedn n e)))))
| tQuote t => is_closedn n t
end.

Definition closedn n (t : term) := is_true (is_closedn n t).
Definition closed0 (t : term) := is_true (is_closedn 0 t).

Lemma closedn_ren ρ n n' (t : term) : (forall m, m < n -> ρ m < n') -> closedn n t -> closedn n' t⟨ρ⟩.
Proof.
unfold closedn, is_true; revert ρ n n'; induction t; intros ρ k k' Hρ Ht; simpl in *; eauto.
all: repeat match goal with H : _ |- _ => apply andb_prop in H; destruct H end.
all: repeat (apply andb_true_intro; split); f_equal; try now intuition.
+ now apply PeanoNat.Nat.ltb_lt, Hρ, PeanoNat.Nat.ltb_lt.
+ eapply IHt2; [|tea].
  intros [] ?; compute; intuition.
+ eapply IHt2; [|tea].
  intros [] ?; compute; intuition.
+ eapply IHt1; [|tea].
  intros [] ?; compute; intuition.
+ eapply IHt1; [|tea].
  intros [] ?; compute; intuition.
+ eapply IHt2; [|tea].
  intros [] ?; compute; intuition.
+ eapply IHt3; [|eassumption].
  intros [|[]] ?; compute; intuition.
  do 2 apply Arith_prebase.lt_n_S_stt.
  apply Hρ; now do 2 apply Arith_prebase.lt_S_n.
Qed.

Lemma closedn_ren_rev ρ n n' (t : term) : (forall m, ρ m < n' -> m < n) -> closedn n' t⟨ρ⟩ -> closedn n t.
Proof.
unfold closedn, is_true; revert ρ n n'; induction t; intros ρ k k' Hρ Ht; simpl in *; eauto.
all: repeat match goal with H : _ |- _ => apply andb_prop in H; destruct H end.
all: repeat (apply andb_true_intro; split); f_equal; try now intuition.
+ now apply PeanoNat.Nat.ltb_lt, Hρ, PeanoNat.Nat.ltb_lt.
+ eapply IHt2; [|tea].
  intros [] ?; compute; intuition.
+ eapply IHt2; [|tea].
  intros [] ?; compute; intuition.
+ eapply IHt1; [|tea].
  intros [] ?; compute; intuition.
+ eapply IHt1; [|tea].
  intros [] ?; compute; intuition.
+ eapply IHt2; [|tea].
  intros [] ?; compute; intuition.
+ eapply IHt3; [|eassumption].
  intros [|[]] ?; compute; intuition.
  do 2 apply Arith_prebase.lt_n_S_stt; apply Hρ.
  do 2 apply Arith_prebase.lt_S_n; tea.
Qed.

Lemma closed0_ren ρ (t : term) : closed0 t -> closed0 t⟨ρ⟩.
Proof.
intros; eapply closedn_ren; [|eassumption].
intros; exfalso; now eapply PeanoNat.Nat.nlt_0_r.
Qed.

Lemma closed0_ren_rev ρ (t : term) : closed0 t⟨ρ⟩ -> closed0 t.
Proof.
intros; eapply closedn_ren_rev; [|eassumption].
intros; exfalso; now eapply PeanoNat.Nat.nlt_0_r.
Qed.

Lemma closedn_shift : forall n t, closedn n t -> closedn (S n) t⟨↑⟩.
Proof.
intros; eapply closedn_ren; [|tea].
intros [] ?; compute; lia.
Qed.

Lemma closedn_subst σ n n' (t : term) : (forall m, m < n -> closedn n' (σ m)) -> closedn n t -> closedn n' t[σ].
Proof.
unfold closedn, is_true; revert σ n n'; induction t; intros σ k k' Hσ Ht; simpl in *; eauto.
all: repeat match goal with H : _ |- _ => apply andb_prop in H; destruct H end.
all: repeat (apply andb_true_intro; split); f_equal; try now intuition.
+ now apply Hσ, PeanoNat.Nat.ltb_lt.
+ eapply IHt2; [|tea].
  intros [] ?; cbn; [reflexivity|]; unfold funcomp; now apply closedn_shift, Hσ, Arith_prebase.lt_S_n.
+ eapply IHt2; [|tea].
  intros [] ?; cbn; [reflexivity|]; unfold funcomp; now apply closedn_shift, Hσ, Arith_prebase.lt_S_n.
+ eapply IHt1; [|tea].
  intros [] ?; cbn; [reflexivity|]; unfold funcomp; now apply closedn_shift, Hσ, Arith_prebase.lt_S_n.
+ eapply IHt1; [|tea].
  intros [] ?; cbn; [reflexivity|]; unfold funcomp; now apply closedn_shift, Hσ, Arith_prebase.lt_S_n.
+ eapply IHt2; [|tea].
  intros [] ?; cbn; [reflexivity|]; unfold funcomp; now apply closedn_shift, Hσ, Arith_prebase.lt_S_n.
+ eapply IHt3; [|eassumption].
  intros [|[]] ?; cbn; try reflexivity.
  unfold funcomp.
  now apply closedn_shift, closedn_shift, Hσ, Arith_prebase.lt_S_n, Arith_prebase.lt_S_n.
Qed.

Lemma closedn_beta : forall t u n, closedn (S n) t -> closedn n u -> closedn n t[u..].
Proof.
intros; eapply closedn_subst; [|tea].
intros [|m] ?; cbn; tea.
assert (Hlt : m < n) by lia; clear - Hlt.
revert n Hlt; induction m; intros.
+ destruct n; cbn; [lia|reflexivity].
+ destruct n as [|[]]; try lia.
  apply (IHm (S n)); lia.
Qed.

Lemma closed0_subst σ (t : term) : closed0 t -> closed0 t[σ].
Proof.
apply closedn_subst.
intros; exfalso; now eapply PeanoNat.Nat.nlt_0_r.
Qed.
