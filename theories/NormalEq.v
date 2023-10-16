From Coq Require Import ssrbool.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Computation Context Closed NormalForms.

(** Lossy equality on normal forms *)

Scheme Equality for term.

Lemma term_beq_spec : forall t u, reflect (t = u) (term_beq t u).
Proof.
intros; remember (term_beq t u) as b eqn:Hb; symmetry in Hb; destruct b; constructor.
+ now apply internal_term_dec_bl.
+ intros ?%internal_term_dec_lb; congruence.
Qed.

Lemma term_beq_eq : forall t u, term_beq t u -> t = u.
Proof.
intros; destruct (term_beq_spec t u); tea; discriminate.
Qed.

Lemma term_eq_beq : forall t u, t = u -> term_beq t u.
Proof.
intros; destruct (term_beq_spec t u); tea; congruence.
Qed.

Fixpoint noccurn (n : nat) (t : term) : bool :=
match t with
| tRel m => negb (Nat.eqb m n)
| tSort _ | tNat | tZero | tEmpty => true
| tProd A B => (noccurn n A) && (noccurn (S n) B)
| tLambda A t => (noccurn n A) && (noccurn (S n) t)
| tApp t u => noccurn n t && noccurn n u
| tSucc t => noccurn n t
| tNatElim P hz hs t => noccurn (S n) P && noccurn n hz && noccurn n hs && noccurn n t
| tEmptyElim P t => noccurn (S n) P && noccurn n t
| tSig A B => (noccurn n A) && (noccurn (S n) B)
| tPair A B a b => noccurn n A && noccurn (S n) B && noccurn n a && noccurn n b
| tFst t => noccurn n t
| tSnd t => noccurn n t
| tId A t u => noccurn n A && noccurn n t && noccurn n u
| tRefl A t => noccurn n A && noccurn n t
| tIdElim A x P hr y t => noccurn n A && noccurn n x && noccurn (S (S n)) P && noccurn n hr && noccurn n y && noccurn n t
| tQuote t => noccurn n t
| tReflect t u => noccurn n t && noccurn n u
end.

Lemma noccurn_ren_id : forall n t ρ, (forall m, m <> n -> ρ m = m) -> noccurn n t -> t⟨ρ⟩ = t.
Proof.
assert (Hup : forall n ρ, (forall m, m <> n -> ρ m = m) -> (forall m : nat, m <> S n -> upRen_term_term ρ m = m)).
{ intros n ρ Hρ m Hm.
  destruct m as [|m]; compute; [reflexivity|f_equal; apply Hρ; Lia.lia]. }
intros n t; revert n; induction t; cbn in *; intros.
all: repeat match goal with H : _ |- _ => apply andb_prop in H; destruct H end.
all: repeat match goal with H : _ |- _ => erewrite H end; eauto.
intros ?%PeanoNat.Nat.eqb_eq; rewrite H1 in H0; cbn in *; eauto.
Qed.

Lemma noccurn_subst_id : forall n t σ, (forall m, m <> n -> σ m = tRel m) -> noccurn n t -> t[σ] = t.
Proof.
assert (Hup : forall n σ, (forall m, m <> n -> σ m = tRel m) -> (forall m : nat, m <> S n -> up_term_term σ m = tRel m)).
{ intros n σ Hσ m Hm.
  destruct m as [|m]; [reflexivity|].
  cbn; unfold funcomp; rewrite Hσ by Lia.lia.
  reflexivity. }
intros n t; revert n; induction t; cbn in *; intros.
all: repeat match goal with H : _ |- _ => apply andb_prop in H; destruct H end.
all: repeat match goal with H : _ |- _ => erewrite H end; eauto.
intros ?%PeanoNat.Nat.eqb_eq; rewrite H1 in H0; cbn in *; eauto.
Qed.

Lemma noccur_ren : forall n t ρ, ren_inj ρ -> noccurn n t = noccurn (ρ n) t⟨ρ⟩.
Proof.
intros n t; revert n; induction t; cbn in *; intros k ρ Hρ.
all: repeat match goal with |- _ && _ = _ && _ => f_equal end.
all: try replace (S (S (ρ k))) with (upRen_term_term (upRen_term_term ρ) (S (S k))) by reflexivity.
all: try replace (S (ρ k)) with (upRen_term_term ρ (S k)) by reflexivity.
all: eauto using upRen_term_term_inj.
+ f_equal; apply Bool.eq_true_iff_eq; split.
  - intros ?%PeanoNat.Nat.eqb_eq; subst; apply PeanoNat.Nat.eqb_eq; eauto.
  - intros ?%PeanoNat.Nat.eqb_eq%Hρ%PeanoNat.Nat.eqb_eq; eauto.
Qed.

Lemma noccurn_ren_rev : forall n t ρ, ρ n = n -> noccurn (ρ n) t⟨ρ⟩ -> noccurn n t.
Proof.
intros n t; revert n; induction t; cbn in *; intros k ρ Hρ Ht.
all: repeat match goal with H : _ |- _ => apply andb_prop in H; destruct H end.
all: repeat (apply andb_true_intro; split); unfold is_true in *.
all: try match goal with
| |- true = true => reflexivity
| H : forall (n : nat) (ρ : nat -> nat), _ |- noccurn (S (S ?k)) _ = true => eapply (H (S (S k)) (upRen_term_term (upRen_term_term ρ))); [|tea]; compute; congruence
| H : forall (n : nat) (ρ : nat -> nat), _ |- noccurn (S ?k) _ = true => eapply (H (S k) (upRen_term_term ρ)); [|tea]; compute; congruence
| H : forall (n : nat) (ρ : nat -> nat), _ |- noccurn ?k _ = true => eapply (H k ρ); [|tea]; compute; congruence
end.
+ eapply contraNN; [|tea].
  intros ?%PeanoNat.Nat.eqb_eq; subst; now apply PeanoNat.Nat.eqb_eq.
Qed.

Lemma noccurn_ren_ignore : forall n t ρ,
  (forall m, ρ m <> n) -> noccurn n t⟨ρ⟩ = true.
Proof.
assert (Hup : forall n ρ, (forall m, ρ m <> n) -> (forall m : nat, upRen_term_term ρ m <> S n)).
{ intros n ρ Hρ []; compute; [Lia.lia|].
  intros [=]; now eelim Hρ. }
intros n t; revert n; induction t; cbn in *; intros k ρ Hρ.
all: repeat match goal with H : _ |- _ => apply andb_prop in H; destruct H end.
all: repeat (apply andb_true_intro; split); f_equal; eauto.
apply negbT; apply PeanoNat.Nat.eqb_neq, Hρ.
Qed.

Lemma noccurn_shift_ignore : forall t, noccurn 0 t⟨↑⟩ = true.
Proof.
intros; apply noccurn_ren_ignore.
intros; compute; Lia.lia.
Qed.

Definition get_eta_fun t := match t with
| tApp t (tRel 0) =>
  if noccurn 0 t then Some t[U..] else None
| _ => None
end.

Definition get_eta_pair a b := match a with
| tFst a =>
  match b with
  | tSnd b => if term_beq a b then Some a else None
  | _ => None
  end
| _ => None
end.

Fixpoint erase (t : term) := match t with
| tRel _ | tSort _ | tNat | tZero | tEmpty => t
| tProd A B => tProd (erase A) (erase B)
| tSig A B => tSig (erase A) (erase B)
| tLambda A t =>
  let t := erase t in
  match get_eta_fun t with
  | None => tLambda U t
  | Some n => n
  end
| tApp t u => tApp (erase t) (erase u)
| tSucc t => tSucc (erase t)
| tNatElim P hz hs t => tNatElim (erase P) (erase hz) (erase hs) (erase t)
| tEmptyElim P t => tEmptyElim (erase P) (erase t)
| tPair A B a b =>
  let a := erase a in
  let b := erase b in
  match get_eta_pair a b with
  | None => tPair U U a b
  | Some n => n
  end
| tFst t => tFst (erase t)
| tSnd t => tSnd (erase t)
| tId A t u => tId (erase A) (erase t) (erase u)
| tRefl A t => tRefl (erase A) (erase t)
| tIdElim A x P hr y t => tIdElim (erase A) (erase x) (erase P) (erase hr) (erase y) (erase t)
| tQuote t => tQuote (erase t)
| tReflect t u => tReflect (erase t) (erase u)
end.

Definition eqnf t u := erase t = erase u.

Inductive eta_fun_spec : term -> option term -> Set :=
| eta_fun_none : forall t, get_eta_fun t = None -> eta_fun_spec t None
| eta_fun_some : forall t, eta_fun_spec (tApp t⟨↑⟩ (tRel 0)) (Some t).

Inductive eta_pair_spec : term -> term -> option term -> Set :=
| eta_pair_none : forall t u, get_eta_pair t u = None -> eta_pair_spec t u None
| eta_pair_some : forall t, eta_pair_spec (tFst t) (tSnd t) (Some t).

Lemma eta_fun_intro : forall t, eta_fun_spec t (get_eta_fun t).
Proof.
intros t.
remember (get_eta_fun t) as o eqn:Ho; symmetry in Ho; rewrite <- Ho.
destruct t; cbn; try now apply eta_fun_none.
destruct t2; cbn; try now apply eta_fun_none.
destruct n; cbn; try now apply eta_fun_none.
remember (noccurn 0 t1) as b eqn:Hb; destruct b.
+ assert (Hrw : t1 = (t1[U..])⟨↑⟩).
  { asimpl; symmetry; eapply noccurn_subst_id; [|now symmetry].
    intros [|] ?; [Lia.lia|reflexivity]. }
  set (t' := t1[U..]); rewrite Hrw; constructor.
+ apply eta_fun_none; cbn.
  now rewrite <- Hb.
Qed.

Lemma eta_pair_intro : forall t u, eta_pair_spec t u (get_eta_pair t u).
Proof.
intros t u.
remember (get_eta_pair t u) as o eqn:Ho; symmetry in Ho; rewrite <- Ho.
destruct t; cbn; try now apply eta_pair_none.
destruct u; cbn; try now apply eta_pair_none.
edestruct (term_beq_spec t u).
+ subst; now constructor.
+ constructor; cbn in *.
  edestruct (term_beq_spec t u); congruence.
Qed.

#[local]
Lemma closedn_shift : forall m t, is_closedn (S m) t⟨↑⟩ = is_closedn m t.
Proof.
intros; remember (is_closedn m t) as b eqn:Ht; symmetry in Ht; destruct b.
+ eapply closedn_ren; [|tea].
  intros []; compute; Lia.lia.
+ eapply contraFF; [|tea]; clear.
  intros H; eapply closedn_ren_rev; [|tea].
  intros []; compute; Lia.lia.
Qed.

Lemma get_eta_fun_ren_None : forall t ρ,
   get_eta_fun t = None -> get_eta_fun t⟨upRen_term_term ρ⟩ = None.
Proof.
intros [] ρ **; cbn in *; try reflexivity.
destruct t0; cbn in *; try reflexivity.
destruct n; cbn; [|reflexivity].
remember (noccurn 0 t) as b eqn:Hb; symmetry in Hb; destruct b.
+ exfalso; congruence.
+ change 0 with (upRen_term_term ρ 0).
  replace (noccurn (upRen_term_term ρ 0) t⟨upRen_term_term ρ⟩) with false; [trivial|].
  symmetry; eapply contraFF; [|tea].
  apply noccurn_ren_rev; reflexivity.
Qed.

Lemma get_eta_pair_ren_None : forall t u ρ, ren_inj ρ ->
   get_eta_pair t u = None -> get_eta_pair t⟨ρ⟩ u⟨ρ⟩ = None.
Proof.
intros [] [] ρ **; cbn in *; try reflexivity.
remember (term_beq t t0) as b eqn:Hb; symmetry in Hb; destruct b.
+ exfalso; congruence.
+ enough (Hrw : term_beq t⟨ρ⟩ t0⟨ρ⟩ = false) by now rewrite Hrw.
  revert Hb; apply contraFF.
  intros ?%term_beq_eq%ren_inj_inv; tea.
  now apply term_eq_beq.
Qed.

Lemma erase_ren : forall t ρ, ren_inj ρ -> (erase t)⟨ρ⟩ = erase t⟨ρ⟩.
Proof.
induction t; intros ρ Hρ; cbn.
all: repeat match goal with H : forall (ρ : nat -> nat), _ |- _ => rewrite H end; eauto using  upRen_term_term_inj.
+ remember (erase t2) as u.
  destruct (eta_fun_intro u); cbn.
  - eapply get_eta_fun_ren_None in e.
    rewrite <- IHt2; [|now apply upRen_term_term_inj].
    now rewrite e.
  - rewrite <- IHt2; [|now apply upRen_term_term_inj]; cbn.
    replace t⟨↑⟩⟨upRen_term_term ρ⟩ with t⟨ρ⟩⟨↑⟩ by now asimpl.
    rewrite noccurn_shift_ignore.
    asimpl; now apply rinstInst'_term.
+ remember (erase t3) as u; remember (erase t4) as v.
  destruct (eta_pair_intro u v); cbn.
  - eapply get_eta_pair_ren_None in e; [|tea].
    rewrite <- IHt3, <- IHt4, e; now tea.
  - rewrite <- IHt3, <- IHt4; tea; cbn.
    now rewrite term_eq_beq.
Qed.

Lemma erase_idempotent : forall t, erase (erase t) = erase t.
Proof.
induction t; cbn in *; f_equal; eauto.
+ remember (erase t2) as t₀; destruct (eta_fun_intro t₀).
  - cbn; rewrite IHt2, e; reflexivity.
  - cbn in *; injection IHt2; intros Hrw.
    rewrite <- erase_ren in Hrw; [|apply shift_inj].
    eapply ren_inj_inv; [apply shift_inj|tea].
+ remember (erase t3) as a₀; remember (erase t4) as b₀.
  destruct (eta_pair_intro a₀ b₀).
  - cbn; rewrite IHt3, IHt4, e; reflexivity.
  - cbn in *; injection IHt3; auto.
Qed.

Lemma erase_subst : forall t σ, erase (t[σ]) = erase ((erase t)[fun n => erase (σ n)]).
Proof.
assert (Hup : forall σ (n : nat), erase (up_term_term σ n) = up_term_term (fun n : nat => erase (σ n)) n).
{ intros σ []; cbn; eauto.
  symmetry; apply erase_ren, shift_inj. }
induction t; intros; cbn in *; try now (f_equal; eauto).
+ destruct n; cbn; now rewrite erase_idempotent.
+ f_equal; eauto.
  etransitivity; [eauto|].
  f_equal; now apply ext_term.
+ remember (erase t2) as t₀.
  destruct (eta_fun_intro t₀).
  - cbn; rewrite IHt2.
    replace (t[fun n : nat => erase (up_term_term σ n)]) with (t[up_term_term (fun n : nat => erase (σ n))]); [reflexivity|].
    apply ext_term.
    intros []; eauto.
  - cbn in *; rewrite IHt2; cbn.
    assert (Hrw : t⟨↑⟩[fun n : nat => erase (up_term_term σ n)] = t[fun n : nat => erase (σ n)]⟨↑⟩).
    { asimpl; apply ext_term.
      intros []; cbn; unfold funcomp.
      - rewrite erase_ren; [eauto|apply shift_inj].
      - rewrite erase_ren; [eauto|apply shift_inj]. }
    rewrite Hrw, <- erase_ren, noccurn_shift_ignore; [|apply shift_inj].
    now asimpl.
+ f_equal; eauto.
  etransitivity; [eapply IHt1|].
  f_equal; now apply ext_term.
+ f_equal; eauto.
  etransitivity; [eapply IHt1|].
  f_equal; now apply ext_term.
+ f_equal; eauto.
  etransitivity; [eapply IHt2|].
  f_equal; now apply ext_term.
+ remember (erase t3) as a₀.
  remember (erase t4) as b₀.
  destruct (eta_pair_intro a₀ b₀); cbn.
  - rewrite IHt3, IHt4; reflexivity.
  - rewrite IHt3, IHt4; cbn; rewrite term_eq_beq; reflexivity.
+ f_equal; eauto.
  etransitivity; [eapply IHt3|].
  f_equal; apply ext_term.
  intros [|[]]; cbn; eauto.
  rewrite erase_ren, erase_ren; eauto using shift_inj.
Qed.

Lemma erase_is_closedn : forall n t, is_closedn n (erase t) = is_closedn n t.
Proof.
intros n t; revert n; unfold eqnf; induction t; intros k; cbn in *.
all: repeat match goal with |- _ && _ = _ && _ => f_equal end.
all: try now eauto.
+ destruct (eta_fun_intro (erase t2)).
  - cbn; eauto.
  - specialize (IHt2 (S k)); cbn in *.
    rewrite Bool.andb_true_r in IHt2.
    now rewrite <- IHt2, closedn_shift.
+ rewrite <- IHt3, <- IHt4.
  destruct (eta_pair_intro (erase t3) (erase t4)); cbn.
  - f_equal; eauto.
  - symmetry; apply Bool.andb_diag.
Qed.

Lemma erase_is_closedn_ren_id : forall n t ρ, (forall m, m < n -> ρ m = m) -> is_closedn n t -> erase t⟨ρ⟩ = erase t.
Proof.
assert (Hup : forall n ρ, (forall m, m < n -> ρ m = m) -> (forall m, m < S n -> upRen_term_term ρ m = m)).
{ intros n ρ Hρ [] ?; [reflexivity|].
  compute; f_equal; apply Hρ; Lia.lia. }
intros n t; revert n; induction t; intros k ρ Hρ Ht; cbn in *.
all: repeat match goal with H : _ |- _ => apply andb_prop in H; destruct H end.
all: f_equal; eauto.
+ destruct k; [discriminate|].
  apply Hρ; apply PeanoNat.Nat.leb_le in Ht; Lia.lia.
+ remember (erase t2) as u eqn:Hu.
  destruct (eta_fun_intro u); cbn.
  - erewrite IHt2, e; eauto.
  - erewrite IHt2; eauto.
    cbn; rewrite noccurn_shift_ignore.
    now asimpl.
+ destruct (eta_pair_intro (erase t3) (erase t4)).
  - erewrite IHt3, IHt4, e; eauto.
  - erewrite IHt3, IHt4; tea.
    cbn; destruct (term_beq_spec t t); congruence.
Qed.

Lemma erase_is_closedn_subst_id : forall n t σ, (forall m, m < n -> σ m = tRel m) -> is_closedn n t -> erase t[σ] = erase t.
Proof.
assert (Hup : forall n σ, (forall m, m < n -> σ m = tRel m) -> (forall m, m < S n -> up_term_term σ m = tRel m)).
{ intros n ρ Hρ [] ?; [reflexivity|].
  cbn; unfold funcomp; rewrite Hρ; [reflexivity|Lia.lia]. }
intros n t; revert n; induction t; intros k σ Hσ Ht; cbn in *.
all: repeat match goal with H : _ |- _ => apply andb_prop in H; destruct H end.
all: f_equal; eauto.
+ destruct k; [discriminate|].
  rewrite Hσ; [reflexivity|]; apply PeanoNat.Nat.leb_le in Ht; Lia.lia.
+ remember (erase t2) as u eqn:Hu.
  destruct (eta_fun_intro u); cbn.
  - erewrite IHt2, e; eauto.
  - erewrite IHt2; eauto.
    cbn; rewrite noccurn_shift_ignore.
    now asimpl.
+ destruct (eta_pair_intro (erase t3) (erase t4)).
  - erewrite IHt3, IHt4, e; eauto.
  - erewrite IHt3, IHt4; tea.
    cbn; destruct (term_beq_spec t t); congruence.
Qed.

Lemma erase_is_closed0_ren_id : forall t ρ, closed0 t -> erase t⟨ρ⟩ = erase t.
Proof.
intros; apply (erase_is_closedn_ren_id 0); tea.
intros; Lia.lia.
Qed.

Lemma erase_is_closed0_subst_id : forall t σ, closed0 t -> erase t[σ] = erase t.
Proof.
intros; apply (erase_is_closedn_subst_id 0); tea.
intros; Lia.lia.
Qed.

Lemma dnf_dne_erase : (forall t, dnf t -> dnf (erase t)) × (forall t, dne t -> dne (erase t)).
Proof.
apply dnf_dne_rect; intros; cbn in *.
all: try now (constructor; eauto).
+ destruct (eta_fun_intro (erase t)).
  - constructor; tea; constructor.
  - inversion H0; subst; inversion H1; subst.
    constructor; now eapply dne_ren_rev.
+ destruct (eta_pair_intro (erase a) (erase b)).
  - constructor; tea; constructor.
  - inversion H1; subst; inversion H3; subst.
    now constructor.
+ constructor; tea.
  unfold closed0; now rewrite erase_is_closedn.
+ constructor; tea.
  unfold closed0; now rewrite !erase_is_closedn.
Qed.

Lemma dnf_erase : forall t, dnf t -> dnf (erase t).
Proof.
apply dnf_dne_erase.
Qed.

Lemma dne_erase : forall t, dne t -> dne (erase t).
Proof.
apply dnf_dne_erase.
Qed.

Lemma quote_ren : forall t (ρ : nat -> nat), closed0 t ->
  (qNat (quote model (erase t)))⟨ρ⟩ = qNat (quote model (erase t⟨ρ⟩)).
Proof.
intros.
rewrite qNat_ren; do 2 f_equal.
now rewrite erase_is_closed0_ren_id.
Qed.

Lemma quote_subst : forall t (σ : nat -> term), closed0 t ->
  (qNat (quote model (erase t)))[σ] = qNat (quote model (erase t[σ])).
Proof.
intros.
rewrite qNat_subst; do 2 f_equal.
now rewrite erase_is_closed0_subst_id.
Qed.

(** Alternative characterizations of erasure *)

Fixpoint unannot (t : term) := match t with
| tRel _ | tSort _ | tNat | tZero | tEmpty => t
| tProd A B => tProd (unannot A) (unannot B)
| tSig A B => tSig (unannot A) (unannot B)
| tLambda A t => tLambda U (unannot t)
| tApp t u => tApp (unannot t) (unannot u)
| tSucc t => tSucc (unannot t)
| tNatElim P hz hs t => tNatElim (unannot P) (unannot hz) (unannot hs) (unannot t)
| tEmptyElim P t => tEmptyElim (unannot P) (unannot t)
| tPair A B a b => tPair U U (unannot a) (unannot b)
| tFst t => tFst (unannot t)
| tSnd t => tSnd (unannot t)
| tId A t u => tId (unannot A) (unannot t) (unannot u)
| tRefl A t => tRefl (unannot A) (unannot t)
| tIdElim A x P hr y t => tIdElim (unannot A) (unannot x) (unannot P) (unannot hr) (unannot y) (unannot t)
| tQuote t => tQuote (unannot t)
| tReflect t u => tReflect (unannot t) (unannot u)
end.

Fixpoint etared (t : term) := match t with
| tRel _ | tSort _ | tNat | tZero | tEmpty => t
| tProd A B => tProd (etared A) (etared B)
| tSig A B => tSig (etared A) (etared B)
| tLambda A t =>
  let t := etared t in
  match get_eta_fun t with
  | None => tLambda (etared A) t
  | Some n => n
  end
| tApp t u => tApp (etared t) (etared u)
| tSucc t => tSucc (etared t)
| tNatElim P hz hs t => tNatElim (etared P) (etared hz) (etared hs) (etared t)
| tEmptyElim P t => tEmptyElim (etared P) (etared t)
| tPair A B a b =>
  let a := etared a in
  let b := etared b in
  match get_eta_pair a b with
  | None => tPair (etared A) (etared B) a b
  | Some n => n
  end
| tFst t => tFst (etared t)
| tSnd t => tSnd (etared t)
| tId A t u => tId (etared A) (etared t) (etared u)
| tRefl A t => tRefl (etared A) (etared t)
| tIdElim A x P hr y t => tIdElim (etared A) (etared x) (etared P) (etared hr) (etared y) (etared t)
| tQuote t => tQuote (etared t)
| tReflect t u => tReflect (etared t) (etared u)
end.

Lemma erase_unannot_etared : forall t, erase t = etared (unannot t).
Proof.
induction t; cbn in *; try now f_equal.
+ rewrite IHt2; reflexivity.
+ rewrite IHt3, IHt4; reflexivity.
Qed.

Lemma closedn_etared : forall n t, is_closedn n (etared t) = is_closedn n t.
Proof.
intros n t; revert n; induction t; cbn in *; intros.
all: repeat match goal with H : _ |- _ => apply andb_prop in H; destruct H end.
all: repeat match goal with |- _ && _ = _ && _ => f_equal end; eauto.
- remember (etared t2) as t2'.
  destruct (eta_fun_intro t2'); cbn; eauto.
  specialize (IHt2 (S n)); cbn in *.
  now rewrite Bool.andb_true_r, NormalEq.closedn_shift in IHt2.
- remember (etared t3) as t3'.
  remember (etared t4) as t4'.
  destruct (eta_pair_intro t3' t4'); cbn.
  + f_equal; eauto.
  + rewrite <- IHt3, <- IHt4; cbn.
    now rewrite Bool.andb_diag.
Qed.

Lemma dnf_dne_etared :
  (forall t, dnf t -> dnf (etared t)) ×
  (forall t, dne t -> dne (etared t)).
Proof.
apply dnf_dne_rect; cbn in *; intros.
all: try eauto using dnf, dne.
+ remember (etared t) as t₀.
  destruct (eta_fun_intro t₀).
  - constructor; eauto.
  - inversion H0; subst; inversion H1; subst.
    eauto using dnf_ren_rev, dne, dnf.
+ remember (etared a) as a₀.
  remember (etared b) as b₀.
  destruct (eta_pair_intro a₀ b₀).
  - constructor; eauto.
  - inversion H2; subst; inversion H3; eauto using dne, dnf.
+ constructor; eauto using dne, dnf.
  intro Hc; unfold closed0 in Hc; rewrite closedn_etared in Hc; contradiction.
+ constructor; eauto using dne, dnf.
  destruct s; [left|right];
  intro Hc; unfold closed0 in Hc; rewrite closedn_etared in Hc; contradiction.
Qed.

Lemma dnf_etared : forall t, dnf t -> dnf (etared t).
Proof.
apply dnf_dne_etared.
Qed.

Lemma closedn_unannot : forall n t, is_closedn n (unannot t) = is_closedn n t.
Proof.
intros n t; revert n; induction t; cbn in *; intros.
all: repeat match goal with H : _ |- _ => apply andb_prop in H; destruct H end.
all: repeat match goal with |- _ && _ = _ && _ => f_equal end; eauto.
Qed.

Lemma dnf_dne_unannot :
  (forall t, dnf t -> dnf (unannot t)) ×
  (forall t, dne t -> dne (unannot t)).
Proof.
apply dnf_dne_rect; cbn in *; intros.
all: try eauto using dnf, dne.
+ constructor; eauto.
  unfold closed0; rewrite closedn_unannot; tea.
+ constructor; eauto.
  destruct s; [left|right];
  unfold closed0; rewrite closedn_unannot; tea.
Qed.

Lemma dnf_unannot : forall t, dnf t -> dnf (unannot t).
Proof.
apply dnf_dne_unannot.
Qed.

Lemma dne_unannot : forall t, dne t -> dne (unannot t).
Proof.
apply dnf_dne_unannot.
Qed.

Lemma whne_unannot : forall t, whne t -> whne (unannot t).
Proof.
induction 1; cbn; eauto using whne.
+ constructor; [|now apply dnf_unannot].
  unfold closed0; rewrite closedn_unannot; tea.
+ constructor; try now apply dnf_unannot.
  destruct s; [left|right];
  unfold closed0; rewrite closedn_unannot; tea.
Qed.

Lemma unannot_closedn_subst : forall n t σ,
  (forall m, m < n -> σ m = tRel m) -> is_closedn n t ->
  unannot t[σ] = unannot t.
Proof.
assert (Hup : forall k σ, (forall m : nat, m < k -> σ m = tRel m) -> (forall m : nat, m < S k -> up_term_term σ m = tRel m)).
{ intros k σ Hσ [] ?; cbn; [reflexivity|].
  unfold funcomp; rewrite Hσ; [reflexivity|Lia.lia]. }
intros n t; revert n; induction t; intros k σ Hσ Ht; cbn in *.
all: repeat match goal with H : _ |- _ => apply andb_prop in H; destruct H end.
all: f_equal; eauto.
+ rewrite Hσ; [reflexivity|now apply PeanoNat.Nat.leb_le].
Qed.

Lemma unannot_closed0_subst : forall t σ, closed0 t -> unannot t[σ] = unannot t.
Proof.
unfold closed0; intros; eapply unannot_closedn_subst; tea.
intros m ?; Lia.lia.
Qed.

Lemma unannot_ren : forall t ρ, ren_inj ρ -> (unannot t)⟨ρ⟩ = unannot t⟨ρ⟩.
Proof.
induction t; intros ρ Hρ; cbn in *.
all: try f_equal; eauto using upRen_term_term_inj.
Qed.

Lemma unannot_subst : forall t σ, unannot (t[σ]) = (unannot t)[fun n => unannot (σ n)].
Proof.
assert (Hup : forall t σ,  t[fun n : nat => unannot (up_term_term σ n)] = t[up_term_term (fun n : nat => unannot (σ n))]).
{ intros; apply ext_term; intros []; cbn; [reflexivity|].
  unfold funcomp; rewrite unannot_ren; [reflexivity|apply shift_inj]. }
induction t; intros σ; cbn in *.
all: try f_equal; eauto.
all: etransitivity; eauto.
+ apply ext_term; intros [|[]]; cbn; try reflexivity.
  unfold funcomp; rewrite unannot_ren; [|apply shift_inj].
  rewrite unannot_ren; [|apply shift_inj].
  now asimpl.
Qed.

Lemma unannot_qNat : forall n, unannot (qNat n) = qNat n.
Proof.
induction n; cbn in *; f_equal; eauto.
Qed.

Lemma unannot_idempotent : forall t, unannot (unannot t) = unannot t.
Proof.
induction t; cbn in *; f_equal; eauto.
Qed.

(** Equality of normal forms *)

Lemma eqnf_is_closedn : forall t u n,
  eqnf t u -> is_closedn n t = is_closedn n u.
Proof.
intros * He.
rewrite <- (erase_is_closedn _ t), <- (erase_is_closedn _ u).
now rewrite He.
Qed.

Lemma eqnf_ren : forall t u ρ, ren_inj ρ -> eqnf t u -> eqnf t⟨ρ⟩ u⟨ρ⟩.
Proof.
intros t u ρ **; unfold eqnf in *.
repeat rewrite <- erase_ren; intros; tea; congruence.
Qed.

Lemma eqnf_ren_rev : forall t u ρ, ren_inj ρ -> eqnf t⟨ρ⟩ u⟨ρ⟩ -> eqnf t u.
Proof.
intros t u ρ H He; unfold eqnf in *.
eapply ren_inj_inv; [tea|].
repeat rewrite erase_ren; tea.
Qed.

Lemma eqnf_tSort {s} : eqnf (tSort s) (tSort s).
Proof.
reflexivity.
Qed.

Lemma eqnf_tProd {A A' B B'} : eqnf A A' -> eqnf B B' -> eqnf (tProd A B) (tProd A' B').
Proof.
unfold eqnf; cbn; now intros -> ->.
Qed.

Lemma eqnf_tLambda {A A' t t'} : eqnf t t' -> eqnf (tLambda A t) (tLambda A' t').
Proof.
unfold eqnf; cbn; now intros ->.
Qed.

Lemma eqnf_tLambda_whne {A t n} :
  eqnf t (tApp n⟨↑⟩ (tRel 0)) -> eqnf (tLambda A t) n.
Proof.
unfold eqnf; cbn; intros ->; cbn.
rewrite <- erase_ren; [|apply shift_inj].
change 0 with (upRen_term_term ↑ 0).
rewrite noccurn_ren_ignore.
+ now asimpl.
+ compute; intros; Lia.lia.
Qed.

Lemma eqnf_whne_tLambda {A t n} :
  eqnf (tApp n⟨↑⟩ (tRel 0)) t -> eqnf n (tLambda A t).
Proof.
intros; symmetry; apply eqnf_tLambda_whne; now symmetry.
Qed.

Lemma eqnf_tNat : eqnf tNat tNat.
Proof.
reflexivity.
Qed.

Lemma eqnf_tZero : eqnf tZero tZero.
Proof.
reflexivity.
Qed.

Lemma eqnf_tSucc {t u} : eqnf t u -> eqnf (tSucc t) (tSucc u).
Proof.
unfold eqnf; cbn; now intros ->.
Qed.

Lemma eqnf_tEmpty : eqnf tEmpty tEmpty.
Proof.
reflexivity.
Qed.

Lemma eqnf_tSig {A A' B B'} : eqnf A A' -> eqnf B B' -> eqnf (tSig A B) (tSig A' B').
Proof.
unfold eqnf; cbn; now intros -> ->.
Qed.

Lemma eqnf_tPair {A A' B B' a a' b b'} :
  eqnf a a' -> eqnf b b' -> eqnf (tPair A B a b) (tPair A' B' a' b').
Proof.
unfold eqnf; cbn; now intros -> ->.
Qed.

Lemma eqnf_tPair_whne {A B a b n} :
 eqnf a (tFst n) -> eqnf b (tSnd n) -> eqnf (tPair A B a b) n.
Proof.
unfold eqnf; cbn; intros -> ->; cbn.
now rewrite term_eq_beq.
Qed.

Lemma eqnf_whne_tPair {A B a b n} :
 eqnf (tFst n) a -> eqnf (tSnd n) b -> eqnf n (tPair A B a b).
Proof.
unfold eqnf; cbn; intros <- <-; cbn.
now rewrite term_eq_beq.
Qed.

Lemma eqnf_tId {A A' x x' y y'} : eqnf A A' -> eqnf x x' -> eqnf y y' -> eqnf (tId A x y) (tId A' x' y').
Proof.
unfold eqnf; cbn; now intros -> -> ->.
Qed.

Lemma eqnf_tRefl {A A' x x'} : eqnf A A' -> eqnf x x' -> eqnf (tRefl A x) (tRefl A' x').
Proof.
unfold eqnf; cbn; now intros -> ->.
Qed.

Lemma eqnf_tRel {v} : eqnf (tRel v) (tRel v).
Proof.
reflexivity.
Qed.

Lemma eqnf_tApp {n n' t t'} : eqnf n n' -> eqnf t t' -> eqnf (tApp n t) (tApp n' t').
Proof.
unfold eqnf; cbn; now intros -> ->.
Qed.

Lemma eqnf_tNatElim {P P' hz hz' hs hs' n n'} :
  eqnf P P' -> eqnf hz hz' -> eqnf hs hs' -> eqnf n n' -> eqnf (tNatElim P hz hs n) (tNatElim P' hz' hs' n').
Proof.
unfold eqnf; cbn; now intros -> -> -> ->.
Qed.

Lemma eqnf_tEmptyElim {P P' n n'} :
  eqnf P P' -> eqnf n n' -> eqnf (tEmptyElim P n) (tEmptyElim P' n').
Proof.
unfold eqnf; cbn; now intros -> ->.
Qed.

Lemma eqnf_tFst {n n'} :
  eqnf n n' -> eqnf (tFst n) (tFst n').
Proof.
unfold eqnf; cbn; now intros ->.
Qed.

Lemma eqnf_tSnd {n n'} :
  eqnf n n' -> eqnf (tSnd n) (tSnd n').
Proof.
unfold eqnf; cbn; now intros ->.
Qed.

Lemma eqnf_tIdElim {A A' x x' P P' hr hr' y y' n n'} :
  eqnf A A' -> eqnf x x' -> eqnf P P' -> eqnf hr hr' -> eqnf y y' -> eqnf n n' ->
  eqnf (tIdElim A x P hr y n) (tIdElim A' x' P' hr' y' n').
Proof.
unfold eqnf; cbn; now intros -> -> -> -> -> ->.
Qed.

Lemma eqnf_tQuote {t t'} :
  eqnf t t' -> eqnf (tQuote t) (tQuote t').
Proof.
unfold eqnf; cbn; now intros ->.
Qed.

(*
Ltac unren t := lazymatch t with
| ?t⟨?ρ⟩ => open_constr:(_ : term)
| tRel ?n => constr:(tRel n)
| tSort ?s => constr:(tSort s)
| tProd ?t ?u =>
  let t := unren t in
  let u := unren u in
  constr:(tProd t u)
| tLambda ?t ?u =>
  let t := unren t in
  let u := unren u in
  constr:(tLambda t u)
| tApp ?t ?u =>
  let t := unren t in
  let u := unren u in
  constr:(tApp t u)
| tNat => constr:(tNat)
| tZero => constr:(tZero)
| tSucc ?t =>
  let t := unren t in
  constr:(tSucc t)
| tNatElim ?P ?hz ?hs ?t =>
  let P := unren P in
  let hz := unren hz in
  let hs := unren hs in
  let t := unren t in
  constr:(tNatElim P hz hs t)
| tEmpty => constr:(tEmpty)
| tEmptyElim ?P ?t =>
  let P := unren P in
  let t := unren t in
  constr:(tEmptyElim P t)
| tSig ?t ?u =>
  let t := unren t in
  let u := unren u in
  constr:(tSig t u)
| tPair ?A ?B ?a ?b =>
  let A := unren A in
  let B := unren B in
  let a := unren a in
  let b := unren b in
  constr:(tPair A B a b)
| tFst ?t =>
  let t := unren t in
  constr:(tFst t)
| tSnd ?t =>
  let t := unren t in
  constr:(tSnd t)
| tId ?A ?x ?y =>
  let A := unren A in
  let x := unren x in
  let y := unren y in
  constr:(tId A x y)
| tRefl ?t ?u =>
  let t := unren t in
  let u := unren u in
  constr:(tRefl t u)
| tIdElim ?A ?x ?P ?hr ?y ?t =>
  let A := unren A in
  let x := unren x in
  let P := unren P in
  let hr := unren hr in
  let y := unren y in
  let t := unren t in
  constr:(tIdElim A x P hr y t)
| t => open_constr:(_ : term)
end.
*)

Lemma Symmetric_eqnf : forall t u, eqnf t u -> eqnf u t.
Proof.
intros; now symmetry.
Qed.

Lemma Transitive_eqnf : forall t u r, eqnf t u -> eqnf u r -> eqnf t r.
Proof.
intros; now transitivity (erase u).
Qed.

#[export] Instance PER_eqnf : CRelationClasses.PER eqnf.
Proof.
split.
+ repeat intro; now apply Symmetric_eqnf.
+ repeat intro; now eapply Transitive_eqnf.
Qed.
