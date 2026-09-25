(** * LogRel.Eval: specification of the Gödel numbering and of the internal evaluator.

  The Gödel numbering [quote] and the System T term [tRun] are defined in
  [LogRel.Syntax.Quote]. We prove here that [quote] is injective and that
  [tRun (quote t) k] computes [eval true t k], i.e. returns [0] when the
  evaluation runs out of fuel and [S (quote v)] when it returns [v].

  The internal evaluator is proved correct w.r.t. a call-by-name logical
  relation [RNat t n] stating that [t] weak-head reduces hereditarily to the
  numeral [n]. All internal functions are written as closed combinators of the
  form [λ x₁ … xₙ. body] where [body] contains no binders (except for closed
  motives), which makes their correctness proofs a matter of substitution
  computation followed by the application of the specifications of the
  sub-combinators. *)

From Stdlib Require Import Lia Arith List Cantor.
From LogRel Require Import Utils Syntax.All.
From LogRel Require Import GenericTyping.
From LogRel.Syntax Require Import Quote.

#[local] Notation "⟪ ⟫" := nil (format "⟪ ⟫").
(* The autosubst notation [t ..] prevents the use of recursive notations. *)
#[local] Notation "⟪ a ⟫" := (cons a nil).
#[local] Notation "⟪ a ; b ⟫" := (cons a (cons b nil)).
#[local] Notation "⟪ a ; b ; c ⟫" := (cons a (cons b (cons c nil))).
#[local] Notation "⟪ a ; b ; c ; d ⟫" := (cons a (cons b (cons c (cons d nil)))).
#[local] Notation "⟪ a ; b ; c ; d ; e ⟫" := (cons a (cons b (cons c (cons d (cons e nil))))).
#[local] Notation "⟪ a ; b ; c ; d ; e ; f ⟫" := (cons a (cons b (cons c (cons d (cons e (cons f nil)))))).

Set Default Goal Selector "!".
#[local] Open Scope bool_scope.

(** ** Pairing functions *)

Definition nfst (n : nat) : nat := Datatypes.fst (Cantor.of_nat n).
Definition nsnd (n : nat) : nat := Datatypes.snd (Cantor.of_nat n).

Lemma npair_to_nat : forall x y, npair x y = Cantor.to_nat (Datatypes.pair x y).
Proof.
intros x y; unfold npair; reflexivity.
Qed.

Lemma nfst_npair : forall x y, nfst (npair x y) = x.
Proof.
intros; unfold nfst; now rewrite npair_to_nat, Cantor.cancel_of_to.
Qed.

Lemma nsnd_npair : forall x y, nsnd (npair x y) = y.
Proof.
intros; unfold nsnd; now rewrite npair_to_nat, Cantor.cancel_of_to.
Qed.

Lemma npair_inj : forall x y x' y', npair x y = npair x' y' -> x = x' /\ y = y'.
Proof.
intros * H; split.
+ rewrite <- (nfst_npair x y), <- (nfst_npair x' y'); now f_equal.
+ rewrite <- (nsnd_npair x y), <- (nsnd_npair x' y'); now f_equal.
Qed.

Lemma tri_ge : forall n, n <= tri n.
Proof.
induction n; cbn; lia.
Qed.

Lemma npair_ge_l : forall x y, x <= npair x y.
Proof.
intros; unfold npair; pose proof (tri_ge (y + x)); lia.
Qed.

Lemma npair_ge_r : forall x y, y <= npair x y.
Proof.
intros; unfold npair; lia.
Qed.

(** ** Gödel numbering of terms *)

Lemma lcode_inj : forall l l', lcode l = lcode l' -> l = l'.
Proof.
induction l as [|x l IHl]; intros [|x' l'] H; cbn in *; try discriminate; [reflexivity|].
injection H; intros [-> ?]%npair_inj; f_equal; eauto.
Qed.

Lemma lcode_In : forall l x, In x l -> x < lcode l.
Proof.
induction l as [|y l IHl]; intros x Hx; cbn in *; [now elim Hx|].
destruct Hx as [->|Hx].
+ pose proof (npair_ge_l x (lcode l)); lia.
+ pose proof (npair_ge_r y (lcode l)); specialize (IHl x Hx); lia.
Qed.

Lemma quote_rel : forall n, quote (tRel n) = node 0 n.
Proof.
reflexivity.
Qed.

Lemma quote_node : forall t, tag_of t <> 0 ->
  quote t = node (tag_of t) (lcode (map quote (fields t))).
Proof.
intros []; cbn; try reflexivity; now intros [].
Qed.

Lemma node_inj : forall g g' p p', node g p = node g' p' -> g = g' /\ p = p'.
Proof.
intros * H; unfold node in H; injection H; apply npair_inj.
Qed.

Lemma quote_inj : forall t u, quote t = quote u -> t = u.
Proof.
induction t; intros []; cbn [quote]; intros H.
all: apply node_inj in H; destruct H as [Hg H]; try discriminate Hg.
all: try (apply lcode_inj in H; injection H; clear H; intros).
all: f_equal; eauto.
destruct s, s0; reflexivity.
Qed.

Lemma quote_fields_lt : forall t u, In u (fields t) -> quote u < quote t.
Proof.
intros t u Hu.
assert (Hg : tag_of t <> 0) by (destruct t; cbn in *; first [now destruct Hu | discriminate]).
rewrite (quote_node t Hg).
assert (quote u < lcode (map quote (fields t))).
{ apply lcode_In, in_map, Hu. }
unfold node; pose proof (npair_ge_r (tag_of t) (lcode (map quote (fields t)))); lia.
Qed.

(** ** A call-by-name logical relation for System T *)

Lemma ety_subst : forall T σ, (ety T)[σ] = ety T.
Proof.
induction T; intros σ; cbn; [reflexivity|].
rewrite IHT1; f_equal; asimpl; unfold funcomp.
now rewrite IHT2, rinstInst'_term, IHT2.
Qed.

Lemma ety_ren : forall T ρ, (ety T)⟨ρ⟩ = ety T.
Proof.
intros; rewrite rinstInst'_term; apply ety_subst.
Qed.

#[export] Hint Rewrite ety_ren ety_subst : closed.

Fixpoint interp (T : ty) : Type := match T with
| N => nat
| Arr A B => interp A -> interp B
end.

(** [RNat t n] : [t] hereditarily weak-head reduces to the numeral [n]. *)
Fixpoint RNat (t : term) (n : nat) : Type := match n with
| 0 => [t ⤳* tZero]
| S n => ∑ t₀, [t ⤳* tSucc t₀] × RNat t₀ n
end.

Fixpoint R (T : ty) : term -> interp T -> Type := match T with
| N => RNat
| Arr A B => fun t f => forall u x, R A u x -> R B (tApp t u) (f x)
end.

Lemma RNat_exp : forall t t' n, [t ⤳* t'] -> RNat t' n -> RNat t n.
Proof.
intros t t' [|n] Hr H; cbn in *.
+ eapply gred_trans; tea.
+ destruct H as (t₀&?&?); exists t₀; split; tea.
  eapply gred_trans; tea.
Qed.

Lemma R_exp : forall T t t' x, [t ⤳* t'] -> R T t' x -> R T t x.
Proof.
induction T; intros t t' x Hr H; cbn in *.
+ eapply RNat_exp; tea.
+ intros u y Hu; eapply IHT2; [apply (redalg_app Hr)|].
  now apply H.
Qed.

Lemma RNat_zero : RNat tZero 0.
Proof.
apply redIdAlg.
Qed.

Lemma RNat_succ : forall t n, RNat t n -> RNat (tSucc t) (S n).
Proof.
intros; exists t; split; [apply redIdAlg|tea].
Qed.

Lemma RNat_qNat : forall n, RNat (qNat n) n.
Proof.
induction n; cbn; [apply RNat_zero|now apply RNat_succ].
Qed.

Lemma RNat_dred : forall t n, RNat t n -> [t ⇶* qNat n].
Proof.
intros t n; revert t; induction n; intros t Ht; cbn in *.
+ now apply dred_red.
+ destruct Ht as (t₀&Hr&Ht).
  eapply gred_trans; [now apply dred_red|].
  now apply dredalg_succ.
Qed.

(** From now on, we reason abstractly about [RNat]. *)
Arguments RNat : simpl never.

(** Iterated abstractions and applications *)

Fixpoint srev (us : list term) (σ : nat -> term) : nat -> term := match us with
| nil => σ
| cons u us => srev us (u .: σ)
end.

Lemma redalg_apps : forall t t' us, [t ⤳* t'] -> [apps t us ⤳* apps t' us].
Proof.
intros t t' us; revert t t'; induction us; intros t t' Hr; cbn; [tea|].
apply IHus, redalg_app, Hr.
Qed.

Lemma redalg_beta : forall A b u, [tApp (tLambda A b) u ⤳* b[u..]].
Proof.
intros; eapply redSuccAlg; [apply BRed|apply redIdAlg].
Qed.

Lemma redalg_lams_gen : forall As b us σ, length As = length us ->
  [apps (lams As b)[σ] us ⤳* b[srev us σ]].
Proof.
induction As as [|A As IHAs]; intros b [|u us] σ Hlen; cbn in *; try discriminate.
+ apply redIdAlg.
+ eapply gred_trans; [apply redalg_apps, redalg_beta|].
  rewrite up_single_subst.
  apply IHAs; now injection Hlen.
Qed.

Lemma redalg_lams : forall As b us, length As = length us ->
  [apps (lams As b) us ⤳* b[srev us tRel]].
Proof.
intros As b us Hlen.
rewrite <- (subst_rel (lams As b)).
now apply redalg_lams_gen.
Qed.

Lemma R_lams : forall T As b us x, length As = length us ->
  R T b[srev us tRel] x -> R T (apps (lams As b) us) x.
Proof.
intros; eapply R_exp; [now apply redalg_lams|tea].
Qed.

Lemma apps_app : forall t us vs, apps t (us ++ vs) = apps (apps t us) vs.
Proof.
intros t us; revert t; induction us; intros; cbn; eauto.
Qed.

Lemma R_lams_gen : forall T As b us x, length As <= length us ->
  R T (apps b[srev (firstn (length As) us) tRel] (skipn (length As) us)) x ->
  R T (apps (lams As b) us) x.
Proof.
intros * Hlen H.
rewrite <- (firstn_skipn (length As) us), apps_app.
eapply R_exp; [|exact H].
apply redalg_apps, redalg_lams.
rewrite firstn_length_le; lia.
Qed.

Lemma R_conv : forall T t x y, R T t x -> x = y -> R T t y.
Proof.
intros; now subst.
Qed.

Lemma RNat_conv : forall t x y, RNat t x -> x = y -> RNat t y.
Proof.
intros; now subst.
Qed.

Lemma R_app : forall A B f g u x, R (Arr A B) f g -> R A u x -> R B (tApp f u) (g x).
Proof.
intros * Hf Hu; now apply Hf.
Qed.

(** Recursion on natural numbers *)

Lemma natElim_ind (Q : nat -> term -> Type) P hz hs :
  (forall m t t', [t ⤳* t'] -> Q m t' -> Q m t) ->
  Q 0 hz ->
  (forall m n r, RNat n m -> Q m r -> Q (S m) (tApp (tApp hs n) r)) ->
  forall n m, RNat n m -> Q m (tNatElim P hz hs n).
Proof.
intros Hexp Hz Hs n m; revert n; induction m as [|m IHm]; intros n Hn; cbn in Hn.
+ eapply Hexp; [|exact Hz].
  eapply gred_trans; [apply (redalg_natElim Hn)|].
  eapply redSuccAlg; [apply natElimZero|apply redIdAlg].
+ destruct Hn as (n₀&Hr&Hn₀).
  eapply Hexp; [|apply Hs; [exact Hn₀|apply IHm, Hn₀]].
  eapply gred_trans; [apply (redalg_natElim Hr)|].
  eapply redSuccAlg; [apply natElimSucc|apply redIdAlg].
Qed.

Fixpoint natrec {X : Type} (z : X) (s : nat -> X -> X) (n : nat) : X := match n with
| 0 => z
| S n => s n (natrec z s n)
end.

Lemma natrec_add : forall a b, natrec b (fun _ r => S r) a = a + b.
Proof.
induction a; intros; cbn; congruence.
Qed.

Lemma natrec_sub : forall a b, natrec a (fun _ r => pred r) b = a - b.
Proof.
intros a b; induction b; cbn; lia.
Qed.

Lemma natrec_tri : forall a, natrec 0 (fun i m => S i + m) a = tri a.
Proof.
induction a; [reflexivity|]; cbn [natrec tri]; now rewrite IHa.
Qed.

Lemma R_natElim : forall T P hz hs n z s m,
  R T hz z -> R (Arr N (Arr T T)) hs s -> RNat n m ->
  R T (tNatElim P hz hs n) (natrec z s m).
Proof.
intros * Hz Hs Hn.
refine (natElim_ind (fun m t => R T t (natrec z s m)) P hz hs _ _ _ n m Hn); cbn.
+ intros; eapply R_exp; tea.
+ tea.
+ intros; now apply Hs.
Qed.

(** ** Closed combinators *)

(** Variants of the above lemmas matching the output of [cbn]. *)
Lemma ety_subst_term : forall T σ, subst_term σ (ety T) = ety T.
Proof.
exact ety_subst.
Qed.

Lemma ety_ren_term : forall T ρ, ren_term ρ (ety T) = ety T.
Proof.
exact ety_ren.
Qed.

#[export] Hint Rewrite ety_subst_term ety_ren_term : closed.

Tactic Notation "closed_tac" reference(c) :=
  intros; unfold c; cbn; autorewrite with closed; reflexivity.

(** Computes the body of a fully applied combinator [c]. *)
Ltac get_apps t acc := match t with
| tApp ?f ?u => get_apps f (cons u acc)
| apps ?h ?l => let acc' := eval cbn [List.app] in (List.app l acc) in get_apps h acc'
| _ => constr:(apps t acc)
end.

Ltac to_apps := match goal with
| |- R ?T ?t ?x => let t' := get_apps t (@nil term) in change (R T t' x)
| |- RNat ?t ?x => let t' := get_apps t (@nil term) in change (R N t' x)
end.

Ltac cbn_term :=
  match goal with |- R ?T ?t ?x => let t' := eval cbn in t in change (R T t' x) end;
  autorewrite with closed.

Tactic Notation "beta_tac" reference(c) :=
  to_apps; unfold c; apply R_lams_gen; [cbn; lia|]; cbn_term.

(** Boolean values are represented as 0 and 1 *)
Definition b2n (b : bool) : nat := if b then 1 else 0.

Definition ifz {X} (n : nat) (x y : X) : X := match n with 0 => x | S _ => y end.

Lemma cConstS_closed : forall T σ, subst_term σ (cConstS T) = cConstS T.
Proof. closed_tac cConstS. Qed.
#[export] Hint Rewrite cConstS_closed : closed.

Lemma cConstS_spec : forall T t x, R T t x -> R (Arr N (Arr T T)) (apps (cConstS T) ⟪t⟫) (fun _ _ => x).
Proof.
intros; cbn [R]; intros.
beta_tac cConstS; tea.
Qed.

Lemma cIfz_closed : forall T σ, subst_term σ (cIfz T) = cIfz T.
Proof. closed_tac cIfz. Qed.
#[export] Hint Rewrite cIfz_closed : closed.

Lemma cIfz_spec : forall T n m a x b y, RNat n m -> R T a x -> R T b y ->
  R T (apps (cIfz T) ⟪n; a; b⟫) (ifz m x y).
Proof.
intros; beta_tac cIfz.
replace (ifz m x y) with (natrec x (fun _ _ => y) m) by now destruct m.
apply R_natElim; [tea|now apply cConstS_spec|tea].
Qed.

Lemma cSuccS_closed : forall σ, subst_term σ cSuccS = cSuccS.
Proof. closed_tac cSuccS. Qed.
#[export] Hint Rewrite cSuccS_closed : closed.

Lemma cSuccS_spec : R (Arr N (Arr N N)) cSuccS (fun _ r => S r).
Proof.
cbn [R]; intros; beta_tac cSuccS; now apply RNat_succ.
Qed.

Lemma cProjS_closed : forall σ, subst_term σ cProjS = cProjS.
Proof. closed_tac cProjS. Qed.
#[export] Hint Rewrite cProjS_closed : closed.

Lemma cProjS_spec : R (Arr N (Arr N N)) cProjS (fun i _ => i).
Proof.
cbn [R]; intros; beta_tac cProjS; tea.
Qed.

Lemma cAdd_closed : forall σ, subst_term σ cAdd = cAdd.
Proof. closed_tac cAdd. Qed.
#[export] Hint Rewrite cAdd_closed : closed.

Lemma cAdd_spec : forall u a v b, RNat u a -> RNat v b -> RNat (apps cAdd ⟪u; v⟫) (a + b).
Proof.
intros; beta_tac cAdd.
rewrite <- natrec_add.
apply R_natElim; [tea|apply cSuccS_spec|tea].
Qed.

Lemma cPred_closed : forall σ, subst_term σ cPred = cPred.
Proof. closed_tac cPred. Qed.
#[export] Hint Rewrite cPred_closed : closed.

Lemma cPred_spec : forall u a, RNat u a -> RNat (apps cPred ⟪u⟫) (pred a).
Proof.
intros; beta_tac cPred.
replace (pred a) with (natrec 0 (fun i _ => i) a) by now destruct a.
apply R_natElim; [apply RNat_zero|apply cProjS_spec|tea].
Qed.

Lemma cPredS_closed : forall σ, subst_term σ cPredS = cPredS.
Proof. closed_tac cPredS. Qed.
#[export] Hint Rewrite cPredS_closed : closed.

Lemma cPredS_spec : R (Arr N (Arr N N)) cPredS (fun _ r => pred r).
Proof.
cbn [R]; intros; beta_tac cPredS; now apply cPred_spec.
Qed.

Lemma cSub_closed : forall σ, subst_term σ cSub = cSub.
Proof. closed_tac cSub. Qed.
#[export] Hint Rewrite cSub_closed : closed.

Lemma cSub_spec : forall u a v b, RNat u a -> RNat v b -> RNat (apps cSub ⟪u; v⟫) (a - b).
Proof.
intros; beta_tac cSub.
rewrite <- natrec_sub.
apply R_natElim; [tea|apply cPredS_spec|tea].
Qed.

Lemma cEqb_closed : forall σ, subst_term σ cEqb = cEqb.
Proof. closed_tac cEqb. Qed.
#[export] Hint Rewrite cEqb_closed : closed.

Lemma cEqb_spec : forall u a v b, RNat u a -> RNat v b -> RNat (apps cEqb ⟪u; v⟫) (b2n (Nat.eqb a b)).
Proof.
intros; beta_tac cEqb.
eapply R_conv; [apply cIfz_spec; [apply cAdd_spec; apply cSub_spec; tea|apply RNat_succ, RNat_zero|apply RNat_zero]|].
destruct (Nat.eqb_spec a b).
+ subst; now rewrite Nat.sub_diag.
+ remember (a - b + (b - a)) as k; destruct k; [lia|reflexivity].
Qed.

Lemma cLtb_closed : forall σ, subst_term σ cLtb = cLtb.
Proof. closed_tac cLtb. Qed.
#[export] Hint Rewrite cLtb_closed : closed.

Lemma cLtb_spec : forall u a v b, RNat u a -> RNat v b -> RNat (apps cLtb ⟪u; v⟫) (b2n (Nat.ltb a b)).
Proof.
intros; beta_tac cLtb.
eapply R_conv; [apply cIfz_spec; [apply cSub_spec; [apply RNat_succ|]; tea|apply RNat_succ, RNat_zero|apply RNat_zero]|].
destruct (Nat.ltb_spec a b).
+ replace (S a - b) with 0 by lia; reflexivity.
+ replace (S a - b) with (S (a - b)) by lia; reflexivity.
Qed.

Lemma cAndb_closed : forall σ, subst_term σ cAndb = cAndb.
Proof. closed_tac cAndb. Qed.
#[export] Hint Rewrite cAndb_closed : closed.

Lemma cAndb_spec : forall u a v b, RNat u (b2n a) -> RNat v (b2n b) ->
  RNat (apps cAndb ⟪u; v⟫) (b2n (andb a b)).
Proof.
intros; beta_tac cAndb.
eapply R_conv; [apply cIfz_spec; [tea|apply RNat_zero|tea]|].
now destruct a.
Qed.

Lemma cOrb_closed : forall σ, subst_term σ cOrb = cOrb.
Proof. closed_tac cOrb. Qed.
#[export] Hint Rewrite cOrb_closed : closed.

Lemma cOrb_spec : forall u a v b, RNat u (b2n a) -> RNat v (b2n b) ->
  RNat (apps cOrb ⟪u; v⟫) (b2n (orb a b)).
Proof.
intros; beta_tac cOrb.
eapply R_conv; [apply cIfz_spec; [tea|tea|apply RNat_succ, RNat_zero]|].
now destruct a.
Qed.

Lemma cNegb_closed : forall σ, subst_term σ cNegb = cNegb.
Proof. closed_tac cNegb. Qed.
#[export] Hint Rewrite cNegb_closed : closed.

Lemma cNegb_spec : forall u a, RNat u (b2n a) -> RNat (apps cNegb ⟪u⟫) (b2n (negb a)).
Proof.
intros; beta_tac cNegb.
eapply R_conv; [apply cIfz_spec; [tea|apply RNat_succ, RNat_zero|apply RNat_zero]|].
now destruct a.
Qed.

(** Cantor pairing *)

Lemma cTriS_closed : forall σ, subst_term σ cTriS = cTriS.
Proof. closed_tac cTriS. Qed.
#[export] Hint Rewrite cTriS_closed : closed.

Lemma cTriS_spec : R (Arr N (Arr N N)) cTriS (fun i m => S i + m).
Proof.
cbn [R]; intros; beta_tac cTriS; apply cAdd_spec; [apply RNat_succ|]; tea.
Qed.

Lemma cTri_closed : forall σ, subst_term σ cTri = cTri.
Proof. closed_tac cTri. Qed.
#[export] Hint Rewrite cTri_closed : closed.

Lemma cTri_spec : forall u a, RNat u a -> RNat (apps cTri ⟪u⟫) (tri a).
Proof.
intros; beta_tac cTri.
rewrite <- natrec_tri.
apply R_natElim; [apply RNat_zero|apply cTriS_spec|tea].
Qed.

Lemma cPair_closed : forall σ, subst_term σ cPair = cPair.
Proof. closed_tac cPair. Qed.
#[export] Hint Rewrite cPair_closed : closed.

Lemma cPair_spec : forall u a v b, RNat u a -> RNat v b -> RNat (apps cPair ⟪u; v⟫) (npair a b).
Proof.
intros; beta_tac cPair.
unfold npair; apply cAdd_spec; [tea|apply cTri_spec, cAdd_spec; tea].
Qed.

Lemma cMkp_closed : forall σ, subst_term σ cMkp = cMkp.
Proof. closed_tac cMkp. Qed.
#[export] Hint Rewrite cMkp_closed : closed.

Lemma cMkp_spec : forall u a v b, RNat u a -> RNat v b ->
  R (Arr N N) (apps cMkp ⟪u; v⟫) (fun i => ifz i a b).
Proof.
intros; cbn [R]; intros; beta_tac cMkp.
apply cIfz_spec; tea.
Qed.

Lemma cUnpS_closed : forall σ, subst_term σ cUnpS = cUnpS.
Proof. closed_tac cUnpS. Qed.
#[export] Hint Rewrite cUnpS_closed : closed.

Lemma cUnpair_closed : forall σ, subst_term σ cUnpair = cUnpair.
Proof. closed_tac cUnpair. Qed.
#[export] Hint Rewrite cUnpair_closed : closed.

Lemma nfst_S : forall m, nfst (S m) = ifz (nfst m) (S (nsnd m)) (pred (nfst m)).
Proof.
intros; unfold nfst, nsnd; cbn; fold (Cantor.of_nat m).
destruct (Cantor.of_nat m) as [[|x] y]; reflexivity.
Qed.

Lemma nsnd_S : forall m, nsnd (S m) = ifz (nfst m) 0 (S (nsnd m)).
Proof.
intros; unfold nfst, nsnd; cbn; fold (Cantor.of_nat m).
destruct (Cantor.of_nat m) as [[|x] y]; reflexivity.
Qed.

Lemma cUnpair_state : forall P u a, RNat u a ->
  RNat (tApp (tNatElim P (apps cMkp ⟪tZero; tZero⟫) cUnpS u) tZero) (nfst a) ×
  RNat (tApp (tNatElim P (apps cMkp ⟪tZero; tZero⟫) cUnpS u) (tSucc tZero)) (nsnd a).
Proof.
intros P.
refine (natElim_ind (fun m s => RNat (tApp s tZero) (nfst m) × RNat (tApp s (tSucc tZero)) (nsnd m)) _ _ _ _ _ _).
+ intros m t t' Hr [H1 H2]; split; eapply RNat_exp; tea; now apply redalg_app.
+ split; [apply (cMkp_spec _ 0 _ 0 RNat_zero RNat_zero _ 0 RNat_zero)|].
  apply (cMkp_spec _ 0 _ 0 RNat_zero RNat_zero _ 1 (RNat_succ _ _ RNat_zero)).
+ intros m n r Hn [Hr0 Hr1]; split.
  all: beta_tac cUnpS.
  all: eapply R_conv; [eapply (R_app N N); [apply (cIfz_spec (Arr N N)); [exact Hr0|apply cMkp_spec; [apply RNat_succ, Hr1|apply RNat_zero]|apply cMkp_spec; [apply cPred_spec, Hr0|apply RNat_succ, Hr1]]|]|].
  all: try (apply RNat_zero + apply RNat_succ, RNat_zero).
  all: rewrite ?nfst_S, ?nsnd_S; now destruct (nfst m).
Qed.

Lemma cUnpair_spec : forall u a, RNat u a ->
  RNat (apps cUnpair ⟪u; tZero⟫) (nfst a) × RNat (apps cUnpair ⟪u; tSucc tZero⟫) (nsnd a).
Proof.
intros u a Hu; split; beta_tac cUnpair; now apply cUnpair_state.
Qed.

Lemma cFst_closed : forall σ, subst_term σ cFst = cFst.
Proof. closed_tac cFst. Qed.
#[export] Hint Rewrite cFst_closed : closed.

Lemma cFst_spec : forall u a, RNat u a -> RNat (apps cFst ⟪u⟫) (nfst a).
Proof.
intros; beta_tac cFst; now apply cUnpair_spec.
Qed.

Lemma cSnd_closed : forall σ, subst_term σ cSnd = cSnd.
Proof. closed_tac cSnd. Qed.
#[export] Hint Rewrite cSnd_closed : closed.

Lemma cSnd_spec : forall u a, RNat u a -> RNat (apps cSnd ⟪u⟫) (nsnd a).
Proof.
intros; beta_tac cSnd; now apply cUnpair_spec.
Qed.

Lemma cIfz_zero : forall T n a x b, RNat n 0 -> R T a x -> R T (apps (cIfz T) ⟪n; a; b⟫) x.
Proof.
intros * Hn Ha; beta_tac cIfz.
eapply R_exp; [|tea].
eapply gred_trans; [apply (redalg_natElim Hn)|].
eapply redSuccAlg; [apply natElimZero|apply redIdAlg].
Qed.

Lemma cIfz_succ : forall T n m a b y, RNat n (S m) -> R T b y -> R T (apps (cIfz T) ⟪n; a; b⟫) y.
Proof.
intros * Hn Hb; beta_tac cIfz.
destruct Hn as (n₀&Hr&Hn₀).
eapply R_exp; [eapply gred_trans; [apply (redalg_natElim Hr)|eapply redSuccAlg; [apply natElimSucc|apply redIdAlg]]|].
beta_tac cConstS; tea.
Qed.

Lemma cIte_closed : forall T σ, subst_term σ (cIte T) = cIte T.
Proof. closed_tac cIte. Qed.
#[export] Hint Rewrite cIte_closed : closed.

Lemma cIte_true : forall T n a x c, RNat n 1 -> R T a x -> R T (apps (cIte T) ⟪n; a; c⟫) x.
Proof.
intros; beta_tac cIte; now eapply cIfz_succ.
Qed.

Lemma cIte_false : forall T n a c y, RNat n 0 -> R T c y -> R T (apps (cIte T) ⟪n; a; c⟫) y.
Proof.
intros; beta_tac cIte; now eapply cIfz_zero.
Qed.

Lemma cIte_spec : forall T n b a x c y, RNat n (b2n b) -> R T a x -> R T c y ->
  R T (apps (cIte T) ⟪n; a; c⟫) (if b then x else y).
Proof.
intros; destruct b; [now apply cIte_true|now apply cIte_false].
Qed.

Lemma switch_spec : forall T bs d n m x, RNat n m -> R T (nth m bs d) x -> R T (switch T n bs d) x.
Proof.
intros T bs d; induction bs as [|b bs IHbs]; intros n m x Hn Hx; cbn [switch].
+ destruct m; cbn in Hx; tea.
+ destruct m as [|m]; cbn in Hx.
  - now apply cIfz_zero.
  - eapply cIfz_succ; [tea|].
    eapply IHbs; [|tea].
    apply (cPred_spec _ (S m)); tea.
Qed.

(** ** Course-of-value recursion *)

Lemma dflt_closed : forall T σ, subst_term σ (dflt T) = dflt T.
Proof.
induction T; intros; cbn; [reflexivity|].
now rewrite ety_subst_term, IHT2.
Qed.
#[export] Hint Rewrite dflt_closed : closed.

Lemma cIgn1_closed : forall T σ, subst_term σ (cIgn1 T) = cIgn1 T.
Proof. closed_tac cIgn1. Qed.
#[export] Hint Rewrite cIgn1_closed : closed.

Lemma cRec_closed : forall T σ, subst_term σ (cRec T) = cRec T.
Proof. closed_tac cRec. Qed.
#[export] Hint Rewrite cRec_closed : closed.

Section cRec.

Context (T : ty) {X : Type} (code : X -> nat) (Pre : X -> Type) (f : X -> interp T) (alg : term).

Definition RecSpec (x : X) (rec : term) :=
  forall y, code y < code x -> Pre y -> forall u, RNat u (code y) -> R T (tApp rec u) (f y).

Definition AlgSpec := forall x rec, Pre x -> RecSpec x rec ->
  forall u, RNat u (code x) -> R T (apps alg ⟪rec; u⟫) (f x).

Lemma cRec_spec : AlgSpec ->
  forall x u, Pre x -> RNat u (code x) -> R T (apps (cRec T) ⟪alg; u⟫) (f x).
Proof.
intros Halg x u Hx Hu; unfold AlgSpec, RecSpec in *.
beta_tac cRec.
pose (Q (m : nat) (F : term) := forall y v, code y < m -> Pre y -> RNat v (code y) -> R T (tApp F v) (f y)).
enough (HQ : Q (S (code x)) (tNatElim (tProd tNat (ety T)) (dflt (Arr N T)) (tApp (cIgn1 T) alg) (tSucc u))).
{ apply HQ; tea; lia. }
refine (natElim_ind Q _ _ _ _ _ _ _ _ _).
+ intros m t t' Hr HQ y v Hlt Hy Hv; eapply R_exp; [apply (redalg_app Hr)|]; now apply HQ.
+ intros y v Hlt; lia.
+ intros m n r Hn HQ y v Hlt Hy Hv.
  beta_tac cIgn1.
  refine (Halg y r Hy _ v Hv).
  intros z Hz Hpz w Hw; unfold Q in HQ; apply HQ; tea; lia.
+ now apply RNat_succ.
Qed.

End cRec.

(** ** Lists *)

Lemma cCons_closed : forall σ, subst_term σ cCons = cCons.
Proof. closed_tac cCons. Qed.
#[export] Hint Rewrite cCons_closed : closed.

Lemma cCons_spec : forall u a v b, RNat u a -> RNat v b -> RNat (apps cCons ⟪u; v⟫) (S (npair a b)).
Proof.
intros; beta_tac cCons; apply RNat_succ, cPair_spec; tea.
Qed.

Lemma cCons_lcode : forall u a v l, RNat u a -> RNat v (lcode l) -> RNat (apps cCons ⟪u; v⟫) (lcode (cons a l)).
Proof.
intros; now apply cCons_spec.
Qed.

Lemma cCons_node : forall u a v b, RNat u a -> RNat v b -> RNat (apps cCons ⟪u; v⟫) (node a b).
Proof.
intros; now apply cCons_spec.
Qed.

Definition hd_code (n : nat) := nfst (pred n).
Definition tl_code (n : nat) := nsnd (pred n).

Lemma hd_code_lcode : forall l, hd_code (lcode l) = nth 0 l 0.
Proof.
intros [|x l]; unfold hd_code; cbn; [reflexivity|].
apply nfst_npair.
Qed.

Lemma tl_code_lcode : forall l, tl_code (lcode l) = lcode (tl l).
Proof.
intros [|x l]; unfold tl_code; cbn; [reflexivity|].
apply nsnd_npair.
Qed.

Lemma hd_code_node : forall g p, hd_code (node g p) = g.
Proof.
intros; apply nfst_npair.
Qed.

Lemma tl_code_node : forall g p, tl_code (node g p) = p.
Proof.
intros; apply nsnd_npair.
Qed.

Lemma cHd_closed : forall σ, subst_term σ cHd = cHd.
Proof. closed_tac cHd. Qed.
#[export] Hint Rewrite cHd_closed : closed.

Lemma cHd_spec : forall u a, RNat u a -> RNat (apps cHd ⟪u⟫) (hd_code a).
Proof.
intros; beta_tac cHd; now apply cFst_spec, cPred_spec.
Qed.

Lemma cTl_closed : forall σ, subst_term σ cTl = cTl.
Proof. closed_tac cTl. Qed.
#[export] Hint Rewrite cTl_closed : closed.

Lemma cTl_spec : forall u a, RNat u a -> RNat (apps cTl ⟪u⟫) (tl_code a).
Proof.
intros; beta_tac cTl; now apply cSnd_spec, cPred_spec.
Qed.

Lemma cNthS_closed : forall σ, subst_term σ cNthS = cNthS.
Proof. closed_tac cNthS. Qed.
#[export] Hint Rewrite cNthS_closed : closed.

Lemma cNth_closed : forall σ, subst_term σ cNth = cNth.
Proof. closed_tac cNth. Qed.
#[export] Hint Rewrite cNth_closed : closed.

Lemma cNth_spec : forall u i v l, RNat u i -> RNat v (lcode l) -> RNat (apps cNth ⟪u; v⟫) (nth i l 0).
Proof.
intros u i v l Hu Hv; beta_tac cNth.
revert l v Hv; pattern i.
match goal with |- ?P i => change (P i) with ((fun i F => forall l v, RNat v (lcode l) -> R N (tApp F v) (nth i l 0)) i (tNatElim (tProd tNat tNat) cHd cNthS u)) end.
revert u i Hu; refine (natElim_ind _ _ _ _ _ _ _).
+ intros m t t' Hr HQ l v Hv; eapply R_exp; [apply (redalg_app Hr)|]; now apply HQ.
+ intros l v Hv; eapply RNat_conv; [now apply cHd_spec|].
  apply hd_code_lcode.
+ intros m n r Hn HQ l v Hv.
  beta_tac cNthS.
  eapply RNat_conv; [apply (HQ (tl l)); rewrite <- tl_code_lcode; now apply cTl_spec|].
  destruct l; cbn; [now destruct m|reflexivity].
Qed.

(** Indexed map on lists *)

Fixpoint mapi {A B : Type} (f : nat -> A -> B) (i : nat) (l : list A) : list B := match l with
| nil => nil
| cons x l => cons (f i x) (mapi f (S i) l)
end.

Lemma cMapiAlg_closed : forall σ, subst_term σ cMapiAlg = cMapiAlg.
Proof. closed_tac cMapiAlg. Qed.
#[export] Hint Rewrite cMapiAlg_closed : closed.

Lemma cMapi_closed : forall σ, subst_term σ cMapi = cMapi.
Proof. closed_tac cMapi. Qed.
#[export] Hint Rewrite cMapi_closed : closed.

Lemma cMapi_spec {X Y : Type} (cx : X -> nat) (cy : Y -> nat) (gm : nat -> X -> Y) (g : term) :
  forall l,
  (forall j y u v, In y l -> RNat u j -> RNat v (cx y) -> RNat (apps g ⟪u; v⟫) (cy (gm j y))) ->
  forall w i z, RNat w i -> RNat z (lcode (map cx l)) ->
  RNat (apps cMapi ⟪g; w; z⟫) (lcode (map cy (mapi gm i l))).
Proof.
intros l Hg w i z Hw Hz.
beta_tac cMapi.
pose (Pre l' := forall j y u v, In y l' -> RNat u j -> RNat v (cx y) -> RNat (apps g ⟪u; v⟫) (cy (gm j y))).
refine (R_app N N _ (fun i => lcode (map cy (mapi gm i l))) _ _ _ Hw).
refine (cRec_spec (Arr N N) (fun l => lcode (map cx l)) Pre (fun l i => lcode (map cy (mapi gm i l))) _ _ l z Hg Hz).
clear - Hg; intros l' rec Hl' Hrec u Hu w i Hw.
beta_tac cMapiAlg.
destruct l' as [|y l']; cbn [lcode List.map] in Hu.
+ now apply cIfz_zero, RNat_zero.
+ eapply cIfz_succ; [exact Hu|].
  apply cCons_lcode.
  - apply Hl'; [now left|tea|].
    eapply RNat_conv; [now apply cHd_spec|].
    apply hd_code_node.
  - refine (R_app N N _ (fun i => lcode (map cy (mapi gm i l'))) _ (S i) _ (RNat_succ _ _ Hw)).
    apply Hrec; cbn.
    * pose proof (npair_ge_r (cx y) (lcode (map cx l'))); lia.
    * intros ? ? ? ? ?; apply Hl'; now right.
    * eapply RNat_conv; [now apply cTl_spec|].
      apply tl_code_node.
Qed.

(** Conjunction of a list of booleans *)

Fixpoint lall (l : list nat) : nat := match l with
| nil => 1
| cons x l => ifz x 0 (lall l)
end.

Lemma lall_b2n : forall l, lall (map b2n l) = b2n (forallb (fun b => b) l).
Proof.
induction l as [|[] l IHl]; cbn; eauto.
Qed.

Lemma cLAllAlg_closed : forall σ, subst_term σ cLAllAlg = cLAllAlg.
Proof. closed_tac cLAllAlg. Qed.
#[export] Hint Rewrite cLAllAlg_closed : closed.

Lemma cLAll_closed : forall σ, subst_term σ cLAll = cLAll.
Proof. closed_tac cLAll. Qed.
#[export] Hint Rewrite cLAll_closed : closed.

Lemma cLAll_spec : forall z l, RNat z (lcode l) -> RNat (apps cLAll ⟪z⟫) (lall l).
Proof.
intros z l Hz; beta_tac cLAll.
refine (cRec_spec N lcode (fun _ => unit) lall _ _ l z tt Hz).
intros l' rec _ Hrec u Hu.
beta_tac cLAllAlg.
destruct l' as [|x l']; cbn [lcode] in Hu.
+ now apply cIfz_zero, RNat_succ, RNat_zero.
+ eapply cIfz_succ; [exact Hu|].
  assert (Hx : RNat (apps cHd ⟪u⟫) x).
  { eapply RNat_conv; [now apply cHd_spec|apply hd_code_node]. }
  destruct x as [|x]; cbn [lall ifz].
  - now apply cIfz_zero, RNat_zero.
  - eapply cIfz_succ; [exact Hx|].
    apply Hrec; [|constructor|].
    * pose proof (npair_ge_r (S x) (lcode l')); cbn; lia.
    * eapply RNat_conv; [now apply cTl_spec|apply tl_code_node].
Qed.

(** ** Constant tables indexed by tags *)

Lemma switch_subst : forall T n bs d σ,
  subst_term σ (switch T n bs d) = switch T (subst_term σ n) (map (subst_term σ) bs) (subst_term σ d).
Proof.
intros T n bs; revert n; induction bs; intros; cbn; [reflexivity|].
rewrite IHbs; cbn; now autorewrite with closed.
Qed.

Lemma map_qNat_subst : forall l σ, map (subst_term σ) (map qNat l) = map qNat l.
Proof.
induction l; intros; cbn; [reflexivity|].
now rewrite qNat_subst, IHl.
Qed.

Lemma cTable_closed : forall tab σ, subst_term σ (cTable tab) = cTable tab.
Proof.
intros; unfold cTable; cbn [lams subst_term].
now rewrite switch_subst, map_qNat_subst.
Qed.
#[export] Hint Rewrite cTable_closed : closed.

Lemma cTable_spec : forall tab u g, RNat u g -> RNat (apps (cTable tab) ⟪u⟫) (nth g tab 0).
Proof.
intros tab u g Hu.
change (R N (apps (lams ⟪tNat⟫ (switch N (tRel 0) (map qNat tab) tZero)) ⟪u⟫) (nth g tab 0)).
apply R_lams; [reflexivity|].
change (R N (subst_term (srev ⟪u⟫ tRel) (switch N (tRel 0) (map qNat tab) tZero)) (nth g tab 0)).
rewrite switch_subst, map_qNat_subst.
eapply switch_spec; [exact Hu|].
cbn [subst_term srev scons]; clear Hu.
revert g; induction tab as [|x tab IHtab]; intros [|g]; cbn.
+ apply RNat_zero.
+ apply RNat_zero.
+ apply RNat_qNat.
+ apply IHtab.
Qed.

(** Number of binders of the field [i] of a node tagged [g]. *)
Definition bnd (g i : nat) : nat := if Nat.eqb i (nth g bpos_tab 0) then nth g bcnt_tab 0 else 0.
(** Is the field [i] of a node tagged [g] an ignored annotation? *)
Definition ignb (g i : nat) : bool := Nat.ltb i (nth g ignn_tab 0).
Definition scr (g : nat) : nat := nth g scr_tab 0.
Definition kind (g : nat) : nat := nth g kind_tab 0.

Lemma cBnd_closed : forall σ, subst_term σ cBnd = cBnd.
Proof. closed_tac cBnd. Qed.
#[export] Hint Rewrite cBnd_closed : closed.

Lemma cBnd_spec : forall u g v i, RNat u g -> RNat v i -> RNat (apps cBnd ⟪u; v⟫) (bnd g i).
Proof.
intros; beta_tac cBnd; unfold bnd.
apply cIte_spec; [apply cEqb_spec; [tea|now apply cTable_spec]|now apply cTable_spec|apply RNat_zero].
Qed.

Lemma cIgn_closed : forall σ, subst_term σ cIgn = cIgn.
Proof. closed_tac cIgn. Qed.
#[export] Hint Rewrite cIgn_closed : closed.

Lemma cIgn_spec : forall u g v i, RNat u g -> RNat v i -> RNat (apps cIgn ⟪u; v⟫) (b2n (ignb g i)).
Proof.
intros; beta_tac cIgn; unfold ignb.
apply cLtb_spec; [tea|now apply cTable_spec].
Qed.

(** ** Views on codes of terms *)

Definition payload (t : term) : nat := match t with
| tRel n => n
| _ => lcode (map quote (fields t))
end.

Lemma quote_view : forall t, quote t = node (tag_of t) (payload t).
Proof.
intros []; reflexivity.
Qed.

Lemma RNat_tag : forall u t, RNat u (quote t) -> RNat (apps cHd ⟪u⟫) (tag_of t).
Proof.
intros u t Hu; eapply RNat_conv; [now apply cHd_spec|].
now rewrite quote_view, hd_code_node.
Qed.

Lemma RNat_payload : forall u t, RNat u (quote t) -> RNat (apps cTl ⟪u⟫) (payload t).
Proof.
intros u t Hu; eapply RNat_conv; [now apply cTl_spec|].
now rewrite quote_view, tl_code_node.
Qed.

Lemma RNat_fields : forall u t, tag_of t <> 0 -> RNat u (quote t) ->
  RNat (apps cTl ⟪u⟫) (lcode (map quote (fields t))).
Proof.
intros u t Ht Hu; eapply RNat_conv; [now apply RNat_payload|].
destruct t; cbn in *; now try contradiction.
Qed.

Lemma cIfz_tag : forall T u t A B x, RNat u (quote t) ->
  (forall n, t = tRel n -> R T A x) -> (tag_of t <> 0 -> R T B x) ->
  R T (apps (cIfz T) ⟪apps cHd ⟪u⟫; A; B⟫) x.
Proof.
intros * Hu HA HB.
remember (tag_of t) as g eqn:Hg; destruct g as [|g].
+ apply cIfz_zero; [rewrite Hg; now apply RNat_tag|].
  destruct t; try discriminate; now eapply HA.
+ eapply cIfz_succ; [rewrite Hg; now apply RNat_tag|].
  apply HB; congruence.
Qed.

Lemma RNat_nth_field : forall u t i v, tag_of t <> 0 -> RNat u (quote t) -> RNat v i ->
  RNat (apps cNth ⟪v; apps cTl ⟪u⟫⟫) (nth i (map quote (fields t)) 0).
Proof.
intros * Ht Hu Hv.
apply cNth_spec; [tea|now apply RNat_fields].
Qed.

(** ** Renaming *)

Definition shift_at (c : nat) (t : term) : term := t⟨Nat.iter c upRen_term_term ↑⟩.

Lemma iter_upRen_shift : forall c n, Nat.iter c upRen_term_term ↑ n = if Nat.ltb n c then n else S n.
Proof.
induction c; intros n; [reflexivity|].
destruct n as [|n]; [reflexivity|].
change (Nat.iter (S c) upRen_term_term ↑ (S n)) with (S (Nat.iter c upRen_term_term ↑ n)).
change (Nat.ltb (S n) (S c)) with (Nat.ltb n c).
rewrite IHc; now destruct (Nat.ltb n c).
Qed.

Lemma quote_shift_at_rel : forall c n,
  quote (shift_at c (tRel n)) = node 0 (if Nat.ltb n c then n else S n).
Proof.
intros; unfold shift_at; cbn.
now rewrite iter_upRen_shift.
Qed.

Lemma quote_shift_at_node : forall c t, tag_of t <> 0 ->
  quote (shift_at c t) = node (tag_of t) (lcode (map quote (mapi (fun i f => shift_at (bnd (tag_of t) i + c) f) 0 (fields t)))).
Proof.
intros c []; intros Ht; try (now elim Ht); reflexivity.
Qed.

Lemma cBindF_closed : forall σ, subst_term σ cBindF = cBindF.
Proof. closed_tac cBindF. Qed.
#[export] Hint Rewrite cBindF_closed : closed.

(** Generic specification of a map over the fields of a node with binders *)
Lemma cMapi_bind {X : Type} (fm : term -> nat -> X) (cx : X -> nat) : forall rec t u w p,
  tag_of t <> 0 ->
  RecSpec (Arr N N) quote (fun _ => unit) (fun t p => cx (fm t p)) t rec ->
  RNat u (quote t) -> RNat w p ->
  RNat (apps cMapi ⟪apps cBindF ⟪rec; u; w⟫; tZero; apps cTl ⟪u⟫⟫)
    (lcode (map cx (mapi (fun i f => fm f (bnd (tag_of t) i + p)) 0 (fields t)))).
Proof.
intros * Ht Hrec Hu Hw.
apply (cMapi_spec quote cx (fun i f => fm f (bnd (tag_of t) i + p))); [|apply RNat_zero|now apply RNat_fields].
intros j y u' v' Hy Hu' Hv'.
beta_tac cBindF.
refine (Hrec y _ tt _ _ _ _ _); [now apply quote_fields_lt|tea|].
apply cAdd_spec; [|tea].
apply cBnd_spec; [now apply RNat_tag|tea].
Qed.

Lemma cShiftAlg_closed : forall σ, subst_term σ cShiftAlg = cShiftAlg.
Proof. closed_tac cShiftAlg. Qed.
#[export] Hint Rewrite cShiftAlg_closed : closed.

Lemma cShift_closed : forall σ, subst_term σ cShift = cShift.
Proof. closed_tac cShift. Qed.
#[export] Hint Rewrite cShift_closed : closed.

Lemma cShift_spec : forall u t v c, RNat u (quote t) -> RNat v c ->
  RNat (apps cShift ⟪u; v⟫) (quote (shift_at c t)).
Proof.
intros u t v c Hu Hv; beta_tac cShift.
refine (R_app N N _ (fun c => quote (shift_at c t)) _ _ _ Hv).
refine (cRec_spec (Arr N N) quote (fun _ => unit) (fun t c => quote (shift_at c t)) _ _ t u tt Hu).
clear; intros t rec _ Hrec u Hu v c Hv.
beta_tac cShiftAlg.
apply (cIfz_tag N u t); [tea| |].
+ intros n ->; rewrite quote_shift_at_rel.
  apply cCons_node; [apply RNat_zero|].
  apply (cIte_spec N); [apply cLtb_spec; [now apply (RNat_payload _ (tRel n))|tea]| |apply RNat_succ]; now apply (RNat_payload _ (tRel n)).
+ intros Ht; rewrite quote_shift_at_node; [|tea].
  apply cCons_node; [now apply RNat_tag|].
  now apply (cMapi_bind (fun t c => shift_at c t) quote).
Qed.

(** ** Substitution *)

Definition subst_at (k : nat) (u t : term) : term := t[Nat.iter k up_term_term (u..)].

Lemma iter_up_subst : forall k u n, Nat.iter k up_term_term (u..) n =
  if Nat.ltb n k then tRel n else if Nat.eqb n k then Nat.iter k (shift_at 0) u else tRel (pred n).
Proof.
induction k; intros u n; [now destruct n|].
destruct n as [|n]; [reflexivity|].
change (Nat.iter (S k) up_term_term (u..) (S n)) with (ren_term ↑ (Nat.iter k up_term_term (u..) n)).
change (Nat.ltb (S n) (S k)) with (Nat.ltb n k).
change (Nat.eqb (S n) (S k)) with (Nat.eqb n k).
rewrite IHk.
destruct (Nat.ltb_spec n k); [reflexivity|].
destruct (Nat.eqb_spec n k); [reflexivity|].
destruct n; [lia|reflexivity].
Qed.

Lemma quote_subst_at_rel : forall k u n, quote (subst_at k u (tRel n)) =
  if Nat.ltb n k then node 0 n else if Nat.eqb n k then quote (Nat.iter k (shift_at 0) u) else node 0 (pred n).
Proof.
intros; transitivity (quote (Nat.iter k up_term_term (u..) n)); [reflexivity|].
rewrite iter_up_subst.
destruct Nat.ltb; [reflexivity|].
destruct Nat.eqb; reflexivity.
Qed.

Lemma quote_subst_at_node : forall k u t, tag_of t <> 0 ->
  quote (subst_at k u t) = node (tag_of t) (lcode (map quote (mapi (fun i f => subst_at (bnd (tag_of t) i + k) u f) 0 (fields t)))).
Proof.
intros k u []; intros Ht; try (now elim Ht); reflexivity.
Qed.

Lemma cShiftNS_closed : forall σ, subst_term σ cShiftNS = cShiftNS.
Proof. closed_tac cShiftNS. Qed.
#[export] Hint Rewrite cShiftNS_closed : closed.

Lemma cShiftN_closed : forall σ, subst_term σ cShiftN = cShiftN.
Proof. closed_tac cShiftN. Qed.
#[export] Hint Rewrite cShiftN_closed : closed.

Lemma cShiftN_spec : forall w k z u, RNat w k -> RNat z (quote u) ->
  RNat (apps cShiftN ⟪w; z⟫) (quote (Nat.iter k (shift_at 0) u)).
Proof.
intros w k z u Hw Hz; beta_tac cShiftN.
revert w k Hw.
refine (natElim_ind (fun k t => R N t (quote (Nat.iter k (shift_at 0) u))) _ _ _ _ _ _).
+ intros; eapply R_exp; tea.
+ tea.
+ intros m n r Hn Hr; beta_tac cShiftNS.
  now apply cShift_spec, RNat_zero.
Qed.

Lemma cSubstAlg_closed : forall σ, subst_term σ cSubstAlg = cSubstAlg.
Proof. closed_tac cSubstAlg. Qed.
#[export] Hint Rewrite cSubstAlg_closed : closed.

Lemma cSubst_closed : forall σ, subst_term σ cSubst = cSubst.
Proof. closed_tac cSubst. Qed.
#[export] Hint Rewrite cSubst_closed : closed.

Lemma cSubst_spec : forall w k z u v t, RNat w k -> RNat z (quote u) -> RNat v (quote t) ->
  RNat (apps cSubst ⟪w; z; v⟫) (quote (subst_at k u t)).
Proof.
intros w k z u v t Hw Hz Hv; beta_tac cSubst.
refine (R_app N N _ (fun k => quote (subst_at k u t)) _ _ _ Hw).
refine (cRec_spec (Arr N N) quote (fun _ => unit) (fun t k => quote (subst_at k u t)) _ _ t v tt Hv).
clear - Hz; intros t rec _ Hrec v Hv w k Hw.
beta_tac cSubstAlg.
apply (cIfz_tag N v t); [tea| |].
+ intros n ->; rewrite quote_subst_at_rel.
  assert (Hn := RNat_payload _ _ Hv); cbn [payload] in Hn.
  apply (cIte_spec N); [now apply cLtb_spec|apply cCons_node; [apply RNat_zero|tea]|].
  apply (cIte_spec N); [now apply cEqb_spec|now apply cShiftN_spec|].
  apply cCons_node; [apply RNat_zero|now apply cPred_spec].
+ intros Ht; rewrite quote_subst_at_node; [|tea].
  apply cCons_node; [now apply RNat_tag|].
  now apply (cMapi_bind (fun t k => subst_at k u t) quote).
Qed.

(** ** Boolean traversals *)

Lemma mapi_const {A B} : forall (f : A -> B) i l, mapi (fun _ x => f x) i l = map f l.
Proof.
intros f i l; revert i; induction l; intros; cbn; f_equal; eauto.
Qed.

Lemma mapi_ext {A B} : forall (f g : nat -> A -> B) i l, (forall j x, f j x = g j x) -> mapi f i l = mapi g i l.
Proof.
intros f g i l Hfg; revert i; induction l; intros; cbn; f_equal; eauto.
Qed.

Lemma if_app {A B} : forall (f : A -> B) (b : bool) x y, f (if b then x else y) = if b then f x else f y.
Proof.
now intros ? [].
Qed.

Lemma b2n_if : forall (b c d : bool), b2n (if b then c else d) = if b then b2n c else b2n d.
Proof.
now intros [].
Qed.

Lemma b2n_eqb_1 : forall b, Nat.eqb (b2n b) 1 = b.
Proof.
now intros [].
Qed.

Ltac bool_brute f :=
  repeat match goal with |- context [f ?m ?u] => destruct (f m u) end; reflexivity.

(** *** Occurrence check *)

Lemma noccurn_view : forall n t, tag_of t <> 0 ->
  noccurn n t = forallb (fun b => b) (mapi (fun i f => noccurn (bnd (tag_of t) i + n) f) 0 (fields t)).
Proof.
intros n []; intros Ht; try (now elim Ht); cbn; bool_brute noccurn.
Qed.

Lemma cNoccAlg_closed : forall σ, subst_term σ cNoccAlg = cNoccAlg.
Proof. closed_tac cNoccAlg. Qed.
#[export] Hint Rewrite cNoccAlg_closed : closed.

Lemma cNocc_closed : forall σ, subst_term σ cNocc = cNocc.
Proof. closed_tac cNocc. Qed.
#[export] Hint Rewrite cNocc_closed : closed.

Lemma cNocc_spec : forall u t v n, RNat u (quote t) -> RNat v n ->
  RNat (apps cNocc ⟪u; v⟫) (b2n (noccurn n t)).
Proof.
intros u t v n Hu Hv; beta_tac cNocc.
refine (R_app N N _ (fun n => b2n (noccurn n t)) _ _ _ Hv).
refine (cRec_spec (Arr N N) quote (fun _ => unit) (fun t n => b2n (noccurn n t)) _ _ t u tt Hu).
clear; intros t rec _ Hrec u Hu v n Hv.
beta_tac cNoccAlg.
apply (cIfz_tag N u t); [tea| |].
+ intros m ->; cbn [noccurn].
  apply cNegb_spec, cEqb_spec; [now apply (RNat_payload _ (tRel m))|tea].
+ intros Ht; rewrite noccurn_view, <- lall_b2n; [|tea].
  apply cLAll_spec.
  now apply (cMapi_bind (fun t n => noccurn n t) b2n).
Qed.

(** *** Closedness check *)

Lemma is_closedn_view : forall n t, tag_of t <> 0 ->
  is_closedn n t = forallb (fun b => b) (mapi (fun i f => ignb (tag_of t) i || is_closedn (bnd (tag_of t) i + n) f) 0 (fields t)).
Proof.
intros n []; intros Ht; try (now elim Ht); cbn; bool_brute is_closedn.
Qed.

Lemma cClosF_closed : forall σ, subst_term σ cClosF = cClosF.
Proof. closed_tac cClosF. Qed.
#[export] Hint Rewrite cClosF_closed : closed.

Lemma cClosAlg_closed : forall σ, subst_term σ cClosAlg = cClosAlg.
Proof. closed_tac cClosAlg. Qed.
#[export] Hint Rewrite cClosAlg_closed : closed.

Lemma cClosed_closed : forall σ, subst_term σ cClosed = cClosed.
Proof. closed_tac cClosed. Qed.
#[export] Hint Rewrite cClosed_closed : closed.

Lemma cClosed_spec : forall u t v n, RNat u (quote t) -> RNat v n ->
  RNat (apps cClosed ⟪u; v⟫) (b2n (is_closedn n t)).
Proof.
intros u t v n Hu Hv; beta_tac cClosed.
refine (R_app N N _ (fun n => b2n (is_closedn n t)) _ _ _ Hv).
refine (cRec_spec (Arr N N) quote (fun _ => unit) (fun t n => b2n (is_closedn n t)) _ _ t u tt Hu).
clear; intros t rec _ Hrec u Hu v n Hv.
beta_tac cClosAlg.
apply (cIfz_tag N u t); [tea| |].
+ intros m ->; cbn [is_closedn].
  apply cLtb_spec; [now apply (RNat_payload _ (tRel m))|tea].
+ intros Ht; rewrite is_closedn_view, <- lall_b2n; [|tea].
  apply cLAll_spec.
  apply (cMapi_spec quote b2n (fun i f => ignb (tag_of t) i || is_closedn (bnd (tag_of t) i + n) f)); [|apply RNat_zero|now apply RNat_fields].
  intros j y u' v' Hy Hu' Hv'.
  beta_tac cClosF.
  apply cOrb_spec; [apply cIgn_spec; [now apply RNat_tag|tea]|].
  refine (Hrec y _ tt _ _ _ _ _); [now apply quote_fields_lt|tea|].
  apply cAdd_spec; [|tea].
  apply cBnd_spec; [now apply RNat_tag|tea].
Qed.

Lemma cClos0F_closed : forall σ, subst_term σ cClos0F = cClos0F.
Proof. closed_tac cClos0F. Qed.
#[export] Hint Rewrite cClos0F_closed : closed.

Lemma cMapi_closed0 : forall t u, tag_of t <> 0 -> RNat u (quote t) ->
  RNat (apps cLAll ⟪apps cMapi ⟪cClos0F; tZero; apps cTl ⟪u⟫⟫⟫)
    (b2n (forallb (fun b => b) (map (is_closedn 0) (fields t)))).
Proof.
intros t u Ht Hu.
rewrite <- lall_b2n; apply cLAll_spec.
rewrite <- (mapi_const (is_closedn 0) 0).
apply (cMapi_spec quote b2n (fun _ f => is_closedn 0 f)); [|apply RNat_zero|now apply RNat_fields].
intros j y u' v' Hy Hu' Hv'.
beta_tac cClos0F.
now apply cClosed_spec, RNat_zero.
Qed.

(** *** Normal form check *)

Lemma is_nf_view : forall ne t, tag_of t <> 0 ->
  is_nf ne t =
    (negb (Nat.eqb (kind (tag_of t)) 1) || negb ne) &&
    forallb (fun b => b) (mapi (fun i f => ignb (tag_of t) i || is_nf (Nat.eqb i (scr (tag_of t))) f) 0 (fields t)) &&
    (negb (Nat.eqb (kind (tag_of t)) 3) || negb (forallb (fun b => b) (map (is_closedn 0) (fields t)))).
Proof.
intros ne []; intros Ht; try (now elim Ht); destruct ne; cbn.
all: repeat match goal with |- context [is_nf ?m ?u] => destruct (is_nf m u) end.
all: bool_brute is_closedn.
Qed.

Lemma cNfF_closed : forall σ, subst_term σ cNfF = cNfF.
Proof. closed_tac cNfF. Qed.
#[export] Hint Rewrite cNfF_closed : closed.

Lemma cNfAlg_closed : forall σ, subst_term σ cNfAlg = cNfAlg.
Proof. closed_tac cNfAlg. Qed.
#[export] Hint Rewrite cNfAlg_closed : closed.

Lemma cNf_closed : forall σ, subst_term σ cNf = cNf.
Proof. closed_tac cNf. Qed.
#[export] Hint Rewrite cNf_closed : closed.

Lemma cNf_spec : forall u t v ne, RNat u (quote t) -> RNat v (b2n ne) ->
  RNat (apps cNf ⟪u; v⟫) (b2n (is_nf ne t)).
Proof.
intros u t v ne Hu Hv; beta_tac cNf.
eapply RNat_conv; [refine (R_app N N _ (fun p => b2n (is_nf (Nat.eqb p 1) t)) _ _ _ Hv)|now rewrite b2n_eqb_1].
refine (cRec_spec (Arr N N) quote (fun _ => unit) (fun t p => b2n (is_nf (Nat.eqb p 1) t)) _ _ t u tt Hu).
clear; intros t rec _ Hrec u Hu v p Hv.
beta_tac cNfAlg.
apply (cIfz_tag N u t); [tea| |].
+ intros m ->; cbn [is_nf]; now apply RNat_succ, RNat_zero.
+ intros Ht; rewrite is_nf_view; [|tea].
  apply cAndb_spec; [apply cAndb_spec|].
  - apply cOrb_spec; apply cNegb_spec, cEqb_spec; tea.
    * now apply cTable_spec, RNat_tag.
    * now apply RNat_succ, RNat_zero.
    * now apply RNat_succ, RNat_zero.
  - rewrite <- lall_b2n; apply cLAll_spec.
    apply (cMapi_spec quote b2n (fun i f => ignb (tag_of t) i || is_nf (Nat.eqb i (scr (tag_of t))) f)); [|apply RNat_zero|now apply RNat_fields].
    intros j y u' v' Hy Hu' Hv'.
    beta_tac cNfF.
    apply cOrb_spec; [apply cIgn_spec; [now apply RNat_tag|tea]|].
    eapply RNat_conv; [refine (Hrec y _ tt _ _ _ _ _); [now apply quote_fields_lt|tea|]|now rewrite b2n_eqb_1].
    apply cEqb_spec; [tea|now apply cTable_spec, RNat_tag].
  - apply cOrb_spec; apply cNegb_spec.
    * apply cEqb_spec; [now apply cTable_spec, RNat_tag|exact (RNat_qNat 3)].
    * now apply cMapi_closed0.
Qed.

Lemma cDnfF_closed : forall σ, subst_term σ cDnfF = cDnfF.
Proof. closed_tac cDnfF. Qed.
#[export] Hint Rewrite cDnfF_closed : closed.

Lemma cMapi_dnf : forall t u, tag_of t <> 0 -> RNat u (quote t) ->
  RNat (apps cLAll ⟪apps cMapi ⟪cDnfF; tZero; apps cTl ⟪u⟫⟫⟫)
    (b2n (forallb (fun b => b) (map is_dnf (fields t)))).
Proof.
intros t u Ht Hu.
rewrite <- lall_b2n; apply cLAll_spec.
rewrite <- (mapi_const is_dnf 0).
apply (cMapi_spec quote b2n (fun _ f => is_dnf f)); [|apply RNat_zero|now apply RNat_fields].
intros j y u' v' Hy Hu' Hv'.
beta_tac cDnfF.
now apply (cNf_spec _ _ _ false), RNat_zero.
Qed.

Ltac rnum := repeat (apply RNat_succ); apply RNat_zero.

(** Lazy variants of the boolean combinators *)

Lemma cAndb_false : forall u v, RNat u 0 -> RNat (apps cAndb ⟪u; v⟫) 0.
Proof.
intros; beta_tac cAndb; apply cIfz_zero; [tea|apply RNat_zero].
Qed.

Lemma cAndb_true : forall u v x, RNat u 1 -> RNat v x -> RNat (apps cAndb ⟪u; v⟫) x.
Proof.
intros; beta_tac cAndb; eapply cIfz_succ; tea.
Qed.

(** *** Weak-head neutral check *)

Lemma is_whne_view : forall t, tag_of t <> 0 ->
  is_whne t =
    if Nat.eqb (kind (tag_of t)) 1 then false
    else if Nat.eqb (kind (tag_of t)) 2 then is_whne (nth (scr (tag_of t)) (fields t) (tRel 0))
    else forallb (fun b => b) (map is_dnf (fields t)) && negb (forallb (fun b => b) (map (is_closedn 0) (fields t))).
Proof.
intros []; intros Ht; try (now elim Ht); try reflexivity; cbn.
all: unfold is_dnf; repeat match goal with |- context [is_nf ?m ?u] => destruct (is_nf m u) end.
all: bool_brute is_closedn.
Qed.

Lemma scr_lt : forall t, Nat.eqb (kind (tag_of t)) 2 = true -> scr (tag_of t) < length (fields t).
Proof.
intros []; cbn; intros; try discriminate; lia.
Qed.

Lemma nth_map_quote : forall i l, i < length l -> nth i (map quote l) 0 = quote (nth i l (tRel 0)).
Proof.
intros i l Hi.
rewrite (nth_indep _ 0 (quote (tRel 0))); [|now rewrite length_map].
apply map_nth.
Qed.

Lemma RNat_nth_quote : forall u t i v, tag_of t <> 0 -> RNat u (quote t) -> RNat v i -> i < length (fields t) ->
  RNat (apps cNth ⟪v; apps cTl ⟪u⟫⟫) (quote (nth i (fields t) (tRel 0))).
Proof.
intros; eapply RNat_conv; [now apply RNat_nth_field|].
now apply nth_map_quote.
Qed.

Lemma cWhneAlg_closed : forall σ, subst_term σ cWhneAlg = cWhneAlg.
Proof. closed_tac cWhneAlg. Qed.
#[export] Hint Rewrite cWhneAlg_closed : closed.

Lemma cWhne_closed : forall σ, subst_term σ cWhne = cWhne.
Proof. closed_tac cWhne. Qed.
#[export] Hint Rewrite cWhne_closed : closed.

Lemma cWhne_spec : forall u t, RNat u (quote t) -> RNat (apps cWhne ⟪u⟫) (b2n (is_whne t)).
Proof.
intros u t Hu; beta_tac cWhne.
refine (cRec_spec N quote (fun _ => unit) (fun t => b2n (is_whne t)) _ _ t u tt Hu).
clear; intros t rec _ Hrec u Hu.
beta_tac cWhneAlg.
apply (cIfz_tag N u t); [tea| |].
+ intros m ->; now apply RNat_succ, RNat_zero.
+ intros Ht; rewrite is_whne_view, !b2n_if; [|tea].
  assert (Hk : RNat (apps (cTable kind_tab) ⟪apps cHd ⟪u⟫⟫) (kind (tag_of t))).
  { now apply cTable_spec, RNat_tag. }
  apply (cIte_spec N); [apply cEqb_spec; [tea|rnum]|apply RNat_zero|].
  remember (Nat.eqb (kind (tag_of t)) 2) as b eqn:Hb; symmetry in Hb; destruct b.
  - apply cIte_true; [eapply RNat_conv; [apply cEqb_spec; [tea|rnum]|now rewrite Hb]|].
    refine (Hrec _ _ tt _ _); [apply quote_fields_lt, nth_In; now apply scr_lt|].
    apply RNat_nth_quote; tea; [|now apply scr_lt].
    now apply cTable_spec, RNat_tag.
  - apply cIte_false; [eapply RNat_conv; [apply cEqb_spec; [tea|rnum]|now rewrite Hb]|].
    apply cAndb_spec; [now apply cMapi_dnf|].
    now apply cNegb_spec, cMapi_closed0.
Qed.

(** ** Erasure *)

Lemma code_rel0_spec : RNat code_rel0 (quote (tRel 0)).
Proof.
apply cCons_node; apply RNat_zero.
Qed.

Lemma code_U_spec : RNat code_U (quote U).
Proof.
apply cCons_node; [rnum|apply RNat_zero].
Qed.

Fixpoint RNats (ts : list term) (xs : list nat) : Type := match ts, xs with
| nil, nil => unit
| cons t ts, cons x xs => RNat t x × RNats ts xs
| _, _ => False
end.

Lemma clist_spec : forall ts xs, RNats ts xs -> RNat (clist ts) (lcode xs).
Proof.
induction ts as [|t ts IHts]; intros [|x xs] H; cbn in H; try (now elim H).
+ apply RNat_zero.
+ destruct H; now apply cCons_lcode.
Qed.

Lemma cnode_spec : forall g ts xs, RNats ts xs -> RNat (cnode g ts) (node g (lcode xs)).
Proof.
intros; apply cCons_node; [apply RNat_qNat|now apply clist_spec].
Qed.

Ltac rnats := cbn [RNats]; repeat split.

Definition eraseLam (t : term) := match get_eta_fun t with None => tLambda U t | Some n => n end.
Definition erasePair (a b : term) := match get_eta_pair a b with None => tPair U U a b | Some n => n end.

Lemma eraseLam_eta : forall f, noccurn 0 f = true -> eraseLam (tApp f (tRel 0)) = subst_at 0 U f.
Proof.
intros f Hf; unfold eraseLam; cbn; now rewrite Hf.
Qed.

Lemma eraseLam_noeta : forall f, noccurn 0 f = false -> eraseLam (tApp f (tRel 0)) = tLambda U (tApp f (tRel 0)).
Proof.
intros f Hf; unfold eraseLam; cbn; now rewrite Hf.
Qed.

Lemma eraseLam_other : forall t, (forall f, t <> tApp f (tRel 0)) -> eraseLam t = tLambda U t.
Proof.
intros t Ht; destruct t; try reflexivity.
destruct t2 as [[|]| | | | | | | | | | | | | | | | | | | |]; try reflexivity.
now elim (Ht t1).
Qed.

Lemma erasePair_eta : forall a, erasePair (tFst a) (tSnd a) = a.
Proof.
intros a; unfold erasePair; cbn.
destruct (term_beq_spec a a); congruence.
Qed.

Lemma erasePair_other : forall a b, (forall x, a = tFst x -> b = tSnd x -> False) -> erasePair a b = tPair U U a b.
Proof.
intros a b Hab; destruct a; try reflexivity; destruct b; try reflexivity.
unfold erasePair; cbn.
destruct (term_beq_spec a b); [subst; now elim (Hab b)|reflexivity].
Qed.

Lemma cEraseLam_closed : forall σ, subst_term σ cEraseLam = cEraseLam.
Proof. closed_tac cEraseLam. Qed.
#[export] Hint Rewrite cEraseLam_closed : closed.

Lemma cEraseLam_spec : forall u t, RNat u (quote t) -> RNat (apps cEraseLam ⟪u⟫) (quote (eraseLam t)).
Proof.
intros u t Hu; beta_tac cEraseLam.
assert (Hfb : RNat (cnode 3 ⟪code_U; u⟫) (quote (tLambda U t))).
{ apply cnode_spec; rnats; [apply code_U_spec|tea]. }
assert (Htag : RNat (apps cEqb ⟪apps cHd ⟪u⟫; qNat 4⟫) (b2n (Nat.eqb (tag_of t) 4))).
{ apply cEqb_spec; [now apply RNat_tag|apply RNat_qNat]. }
destruct t; try (rewrite eraseLam_other; [|discriminate]; apply cIte_false; [exact Htag|exact Hfb]).
apply cIte_true; [exact Htag|].
assert (Hrel : RNat (apps cEqb ⟪apps cNth ⟪tSucc tZero; apps cTl ⟪u⟫⟫; code_rel0⟫) (b2n (Nat.eqb (quote t2) (quote (tRel 0))))).
{ apply cEqb_spec; [|apply code_rel0_spec].
  apply (RNat_nth_quote _ (tApp t1 t2) 1); tea; [discriminate|rnum|cbn; lia]. }
destruct (Nat.eqb_spec (quote t2) (quote (tRel 0))) as [He|Hne].
+ apply quote_inj in He; subst t2.
  apply cIte_true; [exact Hrel|].
  assert (Hf : RNat (apps cNth ⟪tZero; apps cTl ⟪u⟫⟫) (quote t1)).
  { apply (RNat_nth_quote _ (tApp t1 (tRel 0)) 0); tea; [discriminate|rnum|cbn; lia]. }
  assert (Hn : RNat (apps cNocc ⟪apps cNth ⟪tZero; apps cTl ⟪u⟫⟫; tZero⟫) (b2n (noccurn 0 t1))).
  { now apply cNocc_spec, RNat_zero. }
  remember (noccurn 0 t1) as b eqn:Hb; symmetry in Hb; destruct b.
  - rewrite eraseLam_eta; [|tea].
    apply cIte_true; [exact Hn|].
    apply cSubst_spec; [apply RNat_zero|apply code_U_spec|tea].
  - rewrite eraseLam_noeta; [|tea].
    apply cIte_false; [exact Hn|exact Hfb].
+ rewrite eraseLam_other; [|intros f [= _ ->]; now elim Hne].
  apply cIte_false; [exact Hrel|exact Hfb].
Qed.

Lemma cErasePair_closed : forall σ, subst_term σ cErasePair = cErasePair.
Proof. closed_tac cErasePair. Qed.
#[export] Hint Rewrite cErasePair_closed : closed.

Lemma cErasePair_spec : forall u a v b, RNat u (quote a) -> RNat v (quote b) ->
  RNat (apps cErasePair ⟪u; v⟫) (quote (erasePair a b)).
Proof.
intros u a v b Hu Hv; beta_tac cErasePair.
assert (Hfb : RNat (cnode 12 ⟪code_U; code_U; u; v⟫) (quote (tPair U U a b))).
{ apply cnode_spec; rnats; first [apply code_U_spec|tea]. }
assert (Htag : RNat (apps cEqb ⟪apps cHd ⟪u⟫; qNat 13⟫) (b2n (Nat.eqb (tag_of a) 13))).
{ apply cEqb_spec; [now apply RNat_tag|apply RNat_qNat]. }
destruct a; try (rewrite erasePair_other; [|intros ? [=]]; apply cIte_false; [exact Htag|exact Hfb]).
apply cIte_true; [exact Htag|].
assert (Htag' : RNat (apps cEqb ⟪apps cHd ⟪v⟫; qNat 14⟫) (b2n (Nat.eqb (tag_of b) 14))).
{ apply cEqb_spec; [now apply RNat_tag|apply RNat_qNat]. }
destruct b; try (rewrite erasePair_other; [|intros ? _ [=]]; apply cIte_false; [exact Htag'|exact Hfb]).
apply cIte_true; [exact Htag'|].
assert (Ha : RNat (apps cNth ⟪tZero; apps cTl ⟪u⟫⟫) (quote a)).
{ apply (RNat_nth_quote _ (tFst a) 0); tea; [discriminate|rnum|cbn; lia]. }
assert (Hb : RNat (apps cNth ⟪tZero; apps cTl ⟪v⟫⟫) (quote b)).
{ apply (RNat_nth_quote _ (tSnd b) 0); tea; [discriminate|rnum|cbn; lia]. }
destruct (Nat.eqb_spec (quote a) (quote b)) as [He|Hne].
+ apply quote_inj in He; subst b.
  rewrite erasePair_eta.
  apply cIte_true; [eapply RNat_conv; [now apply cEqb_spec|now rewrite Nat.eqb_refl]|tea].
+ rewrite erasePair_other; [|intros ? [= ->] [= ->]; now elim Hne].
  apply cIte_false; [eapply RNat_conv; [now apply cEqb_spec|now apply Nat.eqb_neq in Hne; rewrite Hne]|exact Hfb].
Qed.

Lemma cRecF_closed : forall σ, subst_term σ cRecF = cRecF.
Proof. closed_tac cRecF. Qed.
#[export] Hint Rewrite cRecF_closed : closed.

Lemma cEraseAlg_closed : forall σ, subst_term σ cEraseAlg = cEraseAlg.
Proof. closed_tac cEraseAlg. Qed.
#[export] Hint Rewrite cEraseAlg_closed : closed.

Lemma cErase_closed : forall σ, subst_term σ cErase = cErase.
Proof. closed_tac cErase. Qed.
#[export] Hint Rewrite cErase_closed : closed.

Lemma quote_erase_view : forall t, tag_of t <> 0 -> tag_of t <> 3 -> tag_of t <> 12 ->
  quote (erase t) = node (tag_of t) (lcode (map quote (mapi (fun _ f => erase f) 0 (fields t)))).
Proof.
intros []; intros; try (now elim H); try (now elim H0); try (now elim H1); reflexivity.
Qed.

Lemma cErase_spec : forall u t, RNat u (quote t) -> RNat (apps cErase ⟪u⟫) (quote (erase t)).
Proof.
intros u t Hu; beta_tac cErase.
refine (cRec_spec N quote (fun _ => unit) (fun t => quote (erase t)) _ _ t u tt Hu).
clear; intros t rec _ Hrec u Hu.
beta_tac cEraseAlg.
apply (cIfz_tag N u t); [tea| |].
+ intros m ->; tea.
+ intros Ht.
  assert (Htag : forall g, RNat (apps cEqb ⟪apps cHd ⟪u⟫; qNat g⟫) (b2n (Nat.eqb (tag_of t) g))).
  { intros; apply cEqb_spec; [now apply RNat_tag|apply RNat_qNat]. }
  assert (Hfield : forall i, i < length (fields t) -> RNat (apps rec ⟪apps cNth ⟪qNat i; apps cTl ⟪u⟫⟫⟫) (quote (erase (nth i (fields t) (tRel 0))))).
  { intros i Hi; refine (Hrec _ _ tt _ _); [now apply quote_fields_lt, nth_In|].
    apply RNat_nth_quote; tea; apply RNat_qNat. }
  destruct (Nat.eqb_spec (tag_of t) 3) as [H3|H3].
  { apply cIte_true; [eapply RNat_conv; [apply (Htag 3)|now rewrite H3]|].
    destruct t; try discriminate.
    now apply cEraseLam_spec, (Hfield 1); cbn; lia. }
  apply cIte_false; [eapply RNat_conv; [apply (Htag 3)|now apply Nat.eqb_neq in H3; rewrite H3]|].
  destruct (Nat.eqb_spec (tag_of t) 12) as [H12|H12].
  { apply cIte_true; [eapply RNat_conv; [apply (Htag 12)|now rewrite H12]|].
    destruct t; try discriminate.
    apply cErasePair_spec; [apply (Hfield 2)|apply (Hfield 3)]; cbn; lia. }
  apply cIte_false; [eapply RNat_conv; [apply (Htag 12)|now apply Nat.eqb_neq in H12; rewrite H12]|].
  rewrite quote_erase_view; tea.
  apply cCons_node; [now apply RNat_tag|].
  apply (cMapi_spec quote quote (fun _ f => erase f)); [|apply RNat_zero|now apply RNat_fields].
  intros j y u' v' Hy Hu' Hv'.
  beta_tac cRecF.
  refine (Hrec _ _ tt _ Hv'); now apply quote_fields_lt.
Qed.

(** ** Numerals *)

Definition encN (o : option nat) : nat := match o with None => 0 | Some n => S n end.

Lemma cUNatAlg_closed : forall σ, subst_term σ cUNatAlg = cUNatAlg.
Proof. closed_tac cUNatAlg. Qed.
#[export] Hint Rewrite cUNatAlg_closed : closed.

Lemma cUNat_closed : forall σ, subst_term σ cUNat = cUNat.
Proof. closed_tac cUNat. Qed.
#[export] Hint Rewrite cUNat_closed : closed.

Lemma cUNat_spec : forall u t, RNat u (quote t) -> RNat (apps cUNat ⟪u⟫) (encN (uNat t)).
Proof.
intros u t Hu; beta_tac cUNat.
refine (cRec_spec N quote (fun _ => unit) (fun t => encN (uNat t)) _ _ t u tt Hu).
clear; intros t rec _ Hrec u Hu.
beta_tac cUNatAlg.
assert (Htag : forall g, RNat (apps cEqb ⟪apps cHd ⟪u⟫; qNat g⟫) (b2n (Nat.eqb (tag_of t) g))).
{ intros; apply cEqb_spec; [now apply RNat_tag|apply RNat_qNat]. }
destruct (Nat.eqb_spec (tag_of t) 6) as [H6|H6].
{ apply cIte_true; [eapply RNat_conv; [apply (Htag 6)|now rewrite H6]|].
  destruct t; try discriminate; rnum. }
apply cIte_false; [eapply RNat_conv; [apply (Htag 6)|now apply Nat.eqb_neq in H6; rewrite H6]|].
destruct (Nat.eqb_spec (tag_of t) 7) as [H7|H7].
+ apply cIte_true; [eapply RNat_conv; [apply (Htag 7)|now rewrite H7]|].
  destruct t; try discriminate; cbn [uNat].
  assert (Hn : RNat (apps rec ⟪apps cNth ⟪tZero; apps cTl ⟪u⟫⟫⟫) (encN (uNat t))).
  { refine (Hrec _ _ tt _ _); [apply (quote_fields_lt (tSucc t)); now left|].
    apply (RNat_nth_quote _ (tSucc t) 0); tea; [discriminate|rnum|cbn; lia]. }
  destruct (uNat t); cbn [encN] in Hn |- *.
  - eapply (cIfz_succ N); [exact Hn|now apply RNat_succ].
  - apply (cIfz_zero N); [exact Hn|apply RNat_zero].
+ apply cIte_false; [eapply RNat_conv; [apply (Htag 7)|now apply Nat.eqb_neq in H7; rewrite H7]|].
  destruct t; try (apply RNat_zero); now elim H6 + elim H7.
Qed.

Lemma cQNatS_closed : forall σ, subst_term σ cQNatS = cQNatS.
Proof. closed_tac cQNatS. Qed.
#[export] Hint Rewrite cQNatS_closed : closed.

Lemma cQNat_closed : forall σ, subst_term σ cQNat = cQNat.
Proof. closed_tac cQNat. Qed.
#[export] Hint Rewrite cQNat_closed : closed.

Lemma cQNat_spec : forall u n, RNat u n -> RNat (apps cQNat ⟪u⟫) (quote (qNat n)).
Proof.
intros u n Hu; beta_tac cQNat.
revert u n Hu.
refine (natElim_ind (fun n t => R N t (quote (qNat n))) _ _ _ _ _ _).
+ intros; eapply R_exp; tea.
+ apply (cnode_spec 6 nil nil); constructor.
+ intros m n r Hn Hr; beta_tac cQNatS.
  apply (cnode_spec 7 ⟪r⟫ ⟪_⟫); rnats; tea.
Qed.

Lemma code_IdZZ_spec : RNat code_IdZZ (quote (tId tNat tZero tZero)).
Proof.
apply (cnode_spec 15 ⟪_; _; _⟫ ⟪_; _; _⟫); rnats; apply (cnode_spec _ nil nil); constructor.
Qed.

Lemma code_ReflZ_spec : RNat code_ReflZ (quote (tRefl tNat tZero)).
Proof.
apply (cnode_spec 16 ⟪_; _⟫ ⟪_; _⟫); rnats; apply (cnode_spec _ nil nil); constructor.
Qed.

Lemma cQEvalTyS_closed : forall σ, subst_term σ cQEvalTyS = cQEvalTyS.
Proof. closed_tac cQEvalTyS. Qed.
#[export] Hint Rewrite cQEvalTyS_closed : closed.

Lemma cQEvalTy_closed : forall σ, subst_term σ cQEvalTy = cQEvalTy.
Proof. closed_tac cQEvalTy. Qed.
#[export] Hint Rewrite cQEvalTy_closed : closed.

Lemma quote_qEvalTy_S : forall n v,
  quote (qEvalTy (S n) v) = node 11 (lcode ⟪quote (tId tNat tZero tZero); quote (qEvalTy n v)⟫).
Proof.
intros; cbn [qEvalTy]; unfold tAnd.
now rewrite qEvalTy_ren.
Qed.

Lemma cQEvalTy_spec : forall w n z v, RNat w n -> RNat z v ->
  RNat (apps cQEvalTy ⟪w; z⟫) (quote (qEvalTy n v)).
Proof.
intros w n z v Hw Hz; beta_tac cQEvalTy.
revert w n Hw.
refine (natElim_ind (fun n t => R N t (quote (qEvalTy n v))) _ _ _ _ _ _).
+ intros; eapply R_exp; tea.
+ apply (cnode_spec 15 ⟪_; _; _⟫ ⟪_; _; _⟫); rnats.
  - apply (cnode_spec 5 nil nil); constructor.
  - apply (cnode_spec 7 ⟪_⟫ ⟪_⟫); rnats; now apply cQNat_spec.
  - apply (cnode_spec 7 ⟪_⟫ ⟪_⟫); rnats; now apply cQNat_spec.
+ intros m n r Hn Hr; beta_tac cQEvalTyS.
  rewrite quote_qEvalTy_S.
  apply (cnode_spec 11 ⟪_; _⟫ ⟪_; _⟫); rnats; [apply code_IdZZ_spec|tea].
Qed.

Lemma cQEvalTmS_closed : forall σ, subst_term σ cQEvalTmS = cQEvalTmS.
Proof. closed_tac cQEvalTmS. Qed.
#[export] Hint Rewrite cQEvalTmS_closed : closed.

Lemma cQEvalTm_closed : forall σ, subst_term σ cQEvalTm = cQEvalTm.
Proof. closed_tac cQEvalTm. Qed.
#[export] Hint Rewrite cQEvalTm_closed : closed.

Lemma cQEvalTm_spec : forall w n z v, RNat w n -> RNat z v ->
  RNat (apps cQEvalTm ⟪w; z⟫) (quote (qEvalTm n v)).
Proof.
intros w n z v Hw Hz; beta_tac cQEvalTm.
revert w n Hw.
refine (natElim_ind (fun n t => R N t (quote (qEvalTm n v))) _ _ _ _ _ _).
+ intros; eapply R_exp; tea.
+ apply (cnode_spec 16 ⟪_; _⟫ ⟪_; _⟫); rnats.
  - apply (cnode_spec 5 nil nil); constructor.
  - apply (cnode_spec 7 ⟪_⟫ ⟪_⟫); rnats; now apply cQNat_spec.
+ intros m n r Hn Hr; beta_tac cQEvalTmS.
  apply (cnode_spec 12 ⟪_; _; _; _⟫ ⟪_; _; _; _⟫); rnats; [apply code_IdZZ_spec|now apply cQEvalTy_spec|apply code_ReflZ_spec|tea].
Qed.

(** ** The evaluator *)

(** Encodings of optional results *)
Definition encO (o : option term) : nat := match o with None => 0 | Some t => S (quote t) end.
Definition encM (o : option (nat × term)) : nat := match o with None => 0 | Some (n, t) => S (npair n (quote t)) end.
Definition encH (o : option (option term)) : nat := match o with None => 0 | Some o => S (encO o) end.

Definition EvSpec (E : term) (ev : bool -> term -> option term) :=
  forall d b x t, RNat d (b2n b) -> RNat x (quote t) -> RNat (apps E ⟪d; x⟫) (encO (ev b t)).

Definition MuSpec (M : term) (mu : term -> option (nat × term)) :=
  forall x t, RNat x (quote t) -> RNat (apps M ⟪x⟫) (encM (mu t)).

Lemma RNat_pred_encO : forall u t, RNat u (S (quote t)) -> RNat (apps cPred ⟪u⟫) (quote t).
Proof.
intros; now apply (cPred_spec _ (S (quote t))).
Qed.

(** *** Sequencing of optional results *)

Fixpoint osequence (l : list (option term)) : option (list term) := match l with
| nil => Some nil
| cons None _ => None
| cons (Some t) l => match osequence l with None => None | Some ts => Some (cons t ts) end
end.

Fixpoint seqo (l : list nat) : nat := match l with
| nil => 1
| cons x l => ifz x 0 (ifz (seqo l) 0 (S (S (npair (pred x) (pred (seqo l))))))
end.

Lemma seqo_encO : forall l,
  seqo (map encO l) = match osequence l with None => 0 | Some ts => S (lcode (map quote ts)) end.
Proof.
induction l as [|[t|] l IHl]; cbn [seqo osequence map encO]; [reflexivity| |reflexivity].
rewrite IHl; destruct (osequence l); reflexivity.
Qed.

Lemma cSeqAlg_closed : forall σ, subst_term σ cSeqAlg = cSeqAlg.
Proof. closed_tac cSeqAlg. Qed.
#[export] Hint Rewrite cSeqAlg_closed : closed.

Lemma cSeq_closed : forall σ, subst_term σ cSeq = cSeq.
Proof. closed_tac cSeq. Qed.
#[export] Hint Rewrite cSeq_closed : closed.

Lemma cSeq_spec : forall z l, RNat z (lcode l) -> RNat (apps cSeq ⟪z⟫) (seqo l).
Proof.
intros z l Hz; beta_tac cSeq.
refine (cRec_spec N lcode (fun _ => unit) seqo _ _ l z tt Hz).
intros l' rec _ Hrec u Hu.
beta_tac cSeqAlg.
destruct l' as [|x l']; cbn [lcode] in Hu.
+ apply (cIfz_zero N); [tea|rnum].
+ eapply (cIfz_succ N); [exact Hu|].
  assert (Hx : RNat (apps cHd ⟪u⟫) x).
  { eapply RNat_conv; [now apply cHd_spec|apply hd_code_node]. }
  assert (Hr : RNat (apps rec ⟪apps cTl ⟪u⟫⟫) (seqo l')).
  { apply Hrec; [|constructor|].
    * pose proof (npair_ge_r x (lcode l')); cbn; lia.
    * eapply RNat_conv; [now apply cTl_spec|apply tl_code_node]. }
  cbn [seqo]; destruct x as [|x]; cbn [ifz].
  - apply (cIfz_zero N); [tea|apply RNat_zero].
  - eapply (cIfz_succ N); [exact Hx|].
    remember (seqo l') as r eqn:Heq; destruct r as [|r].
    * apply (cIfz_zero N); [tea|apply RNat_zero].
    * eapply (cIfz_succ N); [exact Hr|].
      apply RNat_succ, cCons_spec; now apply (cPred_spec _ (S _)).
Qed.

(** *** Deep evaluation of the fields of a node *)

Definition deepall_code (ev : bool -> term -> option term) (g : nat) (fs : list term) : nat :=
  match osequence (mapi (fun i f => if ignb g i then Some f else ev true f) 0 fs) with
  | None => 0
  | Some fs' => S (node g (lcode (map quote fs')))
  end.

Lemma cDeepF_closed : forall σ, subst_term σ cDeepF = cDeepF.
Proof. closed_tac cDeepF. Qed.
#[export] Hint Rewrite cDeepF_closed : closed.

Lemma cDeep_closed : forall σ, subst_term σ cDeep = cDeep.
Proof. closed_tac cDeep. Qed.
#[export] Hint Rewrite cDeep_closed : closed.

Lemma cDeep_spec : forall E ev x g fs, EvSpec E ev -> RNat x (node g (lcode (map quote fs))) ->
  RNat (apps cDeep ⟪E; x⟫) (deepall_code ev g fs).
Proof.
intros E ev x g fs HE Hx; beta_tac cDeep.
assert (Hg : RNat (apps cHd ⟪x⟫) g).
{ eapply RNat_conv; [now apply cHd_spec|apply hd_code_node]. }
assert (HS : RNat (apps cSeq ⟪apps cMapi ⟪apps cDeepF ⟪E; x⟫; tZero; apps cTl ⟪x⟫⟫⟫)
  (seqo (map encO (mapi (fun i f => if ignb g i then Some f else ev true f) 0 fs)))).
{ apply cSeq_spec.
  apply (cMapi_spec quote encO (fun i f => if ignb g i then Some f else ev true f)); [|apply RNat_zero|].
  + intros j y u v _ Hu Hv; beta_tac cDeepF.
    remember (ignb g j) as b eqn:Hb; destruct b.
    - apply cIte_true; [eapply RNat_conv; [now apply cIgn_spec|now rewrite <- Hb]|now apply RNat_succ].
    - apply cIte_false; [eapply RNat_conv; [now apply cIgn_spec|now rewrite <- Hb]|].
      apply HE; [rnum|tea].
  + eapply RNat_conv; [now apply cTl_spec|apply tl_code_node]. }
rewrite seqo_encO in HS; unfold deepall_code.
destruct osequence as [fs'|].
+ eapply (cIfz_succ N); [exact HS|].
  apply RNat_succ, cCons_node; [tea|].
  now apply (cPred_spec _ (S _)).
+ apply (cIfz_zero N); [tea|apply RNat_zero].
Qed.

(** *** Canonical forms *)

Lemma cCanon_closed : forall σ, subst_term σ cCanon = cCanon.
Proof. closed_tac cCanon. Qed.
#[export] Hint Rewrite cCanon_closed : closed.

Lemma cCanon_spec : forall E ev d b x t, EvSpec E ev -> RNat d (b2n b) -> RNat x (quote t) -> tag_of t <> 0 ->
  RNat (apps cCanon ⟪E; d; x⟫) (if b then deepall_code ev (tag_of t) (fields t) else S (quote t)).
Proof.
intros; beta_tac cCanon.
apply (cIte_spec N); [tea| |now apply RNat_succ].
apply cDeep_spec; [tea|].
now rewrite <- quote_node.
Qed.

(** *** Eliminators *)

Definition repl (s : nat) (r : term) (fs : list term) := mapi (fun i f => if Nat.eqb i s then r else f) 0 fs.

Definition elim_code (ev : bool -> term -> option term) (b : bool) (g s : nat) (fs : list term)
  (hm : term -> option (option term)) : nat :=
  match ev false (nth s fs (tRel 0)) with
  | None => 0
  | Some r =>
    match hm r with
    | Some o => encO o
    | None =>
      if is_whne r then
        if b then deepall_code ev g (repl s r fs)
        else S (node g (lcode (map quote (repl s r fs))))
      else 0
    end
  end.

Lemma cReplF_closed : forall σ, subst_term σ cReplF = cReplF.
Proof. closed_tac cReplF. Qed.
#[export] Hint Rewrite cReplF_closed : closed.

Lemma cRepl_spec : forall w s z r l fs, RNat w s -> RNat z (quote r) -> RNat l (lcode (map quote fs)) ->
  RNat (apps cMapi ⟪apps cReplF ⟪w; z⟫; tZero; l⟫) (lcode (map quote (repl s r fs))).
Proof.
intros; apply (cMapi_spec quote quote (fun i f => if Nat.eqb i s then r else f)); [|apply RNat_zero|tea].
intros j y u v _ Hu Hv; beta_tac cReplF.
rewrite (if_app quote).
apply (cIte_spec N); [now apply cEqb_spec|tea|tea].
Qed.

Lemma cElim_closed : forall σ, subst_term σ cElim = cElim.
Proof. closed_tac cElim. Qed.
#[export] Hint Rewrite cElim_closed : closed.

Lemma cElim_spec : forall E ev d b x t w s h hm,
  EvSpec E ev -> RNat d (b2n b) -> RNat x (quote t) -> tag_of t <> 0 -> RNat w s -> s < length (fields t) ->
  (forall r v, RNat v (quote r) -> RNat (apps h ⟪v⟫) (encH (hm r))) ->
  RNat (apps cElim ⟪E; d; x; w; h⟫) (elim_code ev b (tag_of t) s (fields t) hm).
Proof.
intros * HE Hd Hx Ht Hw Hs Hh; beta_tac cElim.
assert (Hr0 : RNat (apps E ⟪tZero; apps cNth ⟪w; apps cTl ⟪x⟫⟫⟫) (encO (ev false (nth s (fields t) (tRel 0))))).
{ apply HE; [apply RNat_zero|now apply RNat_nth_quote]. }
unfold elim_code; destruct (ev false (nth s (fields t) (tRel 0))) as [r|]; cbn [encO] in Hr0.
2:{ apply (cIfz_zero N); [tea|apply RNat_zero]. }
eapply (cIfz_succ N); [exact Hr0|].
apply RNat_pred_encO in Hr0.
assert (Hhr := Hh _ _ Hr0).
destruct (hm r) as [o|]; cbn [encH] in Hhr.
+ eapply (cIfz_succ N); [exact Hhr|].
  now apply (cPred_spec _ (S _)).
+ apply (cIfz_zero N); [tea|].
  assert (Hx' : RNat (apps cCons ⟪apps cHd ⟪x⟫; apps cMapi ⟪apps cReplF ⟪w; apps cPred ⟪apps E ⟪tZero; apps cNth ⟪w; apps cTl ⟪x⟫⟫⟫⟫⟫; tZero; apps cTl ⟪x⟫⟫⟫)
    (node (tag_of t) (lcode (map quote (repl s r (fields t)))))).
  { apply cCons_node; [now apply RNat_tag|].
    apply cRepl_spec; tea; now apply RNat_fields. }
  apply (cIte_spec N); [now apply cWhne_spec| |apply RNat_zero].
  apply (cIte_spec N); [tea|now apply cDeep_spec|now apply RNat_succ].
Qed.

(** Redex handlers *)

Lemma RNat_F : forall i x t, tag_of t <> 0 -> RNat x (quote t) -> i < length (fields t) ->
  RNat (F i x) (quote (nth i (fields t) (tRel 0))).
Proof.
intros; apply RNat_nth_quote; tea; apply RNat_qNat.
Qed.

Definition hm_app (ev : bool -> term -> option term) (b : bool) (u r : term) : option (option term) :=
  match r with tLambda _ body => Some (ev b (subst_at 0 u body)) | _ => None end.

Lemma cHApp_closed : forall σ, subst_term σ cHApp = cHApp.
Proof. closed_tac cHApp. Qed.
#[export] Hint Rewrite cHApp_closed : closed.

Lemma cHApp_spec : forall E ev d b x t u r v, EvSpec E ev -> RNat d (b2n b) -> RNat x (quote (tApp t u)) ->
  RNat v (quote r) -> RNat (apps cHApp ⟪E; d; x; v⟫) (encH (hm_app ev b u r)).
Proof.
intros * HE Hd Hx Hv; beta_tac cHApp.
assert (Htag : RNat (apps cEqb ⟪apps cHd ⟪v⟫; qNat 3⟫) (b2n (Nat.eqb (tag_of r) 3))).
{ apply cEqb_spec; [now apply RNat_tag|apply RNat_qNat]. }
destruct r; try (apply cIte_false; [exact Htag|apply RNat_zero]).
apply cIte_true; [exact Htag|].
apply RNat_succ, HE; [tea|].
apply cSubst_spec; [apply RNat_zero| |].
+ apply (RNat_F 1 x (tApp t u)); tea; [discriminate|cbn; lia].
+ apply (RNat_F 1 v (tLambda r1 r2)); tea; [discriminate|cbn; lia].
Qed.

Definition hm_nat (ev : bool -> term -> option term) (b : bool) (P hz hs r : term) : option (option term) :=
  match r with
  | tZero => Some (ev b hz)
  | tSucc n => Some (ev b (tApp (tApp hs n) (tNatElim P hz hs n)))
  | _ => None
  end.

Lemma cHNat_closed : forall σ, subst_term σ cHNat = cHNat.
Proof. closed_tac cHNat. Qed.
#[export] Hint Rewrite cHNat_closed : closed.

Lemma cHNat_spec : forall E ev d b x P hz hs n r v, EvSpec E ev -> RNat d (b2n b) ->
  RNat x (quote (tNatElim P hz hs n)) ->
  RNat v (quote r) -> RNat (apps cHNat ⟪E; d; x; v⟫) (encH (hm_nat ev b P hz hs r)).
Proof.
intros * HE Hd Hx Hv; beta_tac cHNat.
assert (Htag : forall g, RNat (apps cEqb ⟪apps cHd ⟪v⟫; qNat g⟫) (b2n (Nat.eqb (tag_of r) g))).
{ intros; apply cEqb_spec; [now apply RNat_tag|apply RNat_qNat]. }
assert (HF : forall i, i < 4 -> RNat (F i x) (quote (nth i ⟪P; hz; hs; n⟫ (tRel 0)))).
{ intros; apply (RNat_F i x (tNatElim P hz hs n)); tea; [discriminate]. }
destruct r; try (apply cIte_false; [apply (Htag 6)|apply cIte_false; [apply (Htag 7)|apply RNat_zero]]).
+ apply cIte_true; [apply (Htag 6)|].
  apply RNat_succ, HE; [tea|apply (HF 1); lia].
+ apply cIte_false; [apply (Htag 6)|].
  apply cIte_true; [apply (Htag 7)|].
  assert (Hr : RNat (F 0 v) (quote r)).
  { apply (RNat_F 0 v (tSucc r)); tea; [discriminate|cbn; lia]. }
  apply RNat_succ, HE; [tea|].
  apply (cnode_spec 4 ⟪_; _⟫ ⟪_; _⟫); rnats.
  - apply (cnode_spec 4 ⟪_; _⟫ ⟪_; _⟫); rnats; [apply (HF 2); lia|tea].
  - apply (cnode_spec 8 ⟪_; _; _; _⟫ ⟪_; _; _; _⟫); rnats; try tea; [apply (HF 0)|apply (HF 1)|apply (HF 2)]; lia.
Qed.

Lemma cHNone_closed : forall σ, subst_term σ cHNone = cHNone.
Proof. closed_tac cHNone. Qed.
#[export] Hint Rewrite cHNone_closed : closed.

Lemma cHNone_spec : forall r v, RNat v (quote r) -> RNat (apps cHNone ⟪v⟫) (encH None).
Proof.
intros; beta_tac cHNone; apply RNat_zero.
Qed.

Definition hm_fst (ev : bool -> term -> option term) (b : bool) (r : term) : option (option term) :=
  match r with tPair _ _ a _ => Some (ev b a) | _ => None end.

Definition hm_snd (ev : bool -> term -> option term) (b : bool) (r : term) : option (option term) :=
  match r with tPair _ _ _ b' => Some (ev b b') | _ => None end.

Lemma cHProj_closed : forall σ, subst_term σ cHProj = cHProj.
Proof. closed_tac cHProj. Qed.
#[export] Hint Rewrite cHProj_closed : closed.

Lemma cHProj_spec : forall E ev d b r v, EvSpec E ev -> RNat d (b2n b) -> RNat v (quote r) ->
  RNat (apps cHProj ⟪E; d; qNat 2; v⟫) (encH (hm_fst ev b r)) ×
  RNat (apps cHProj ⟪E; d; qNat 3; v⟫) (encH (hm_snd ev b r)).
Proof.
intros * HE Hd Hv; split; beta_tac cHProj.
all: assert (Htag : RNat (apps cEqb ⟪apps cHd ⟪v⟫; qNat 12⟫) (b2n (Nat.eqb (tag_of r) 12))) by
  (apply cEqb_spec; [now apply RNat_tag|apply RNat_qNat]).
all: destruct r; try (apply cIte_false; [exact Htag|apply RNat_zero]).
all: apply cIte_true; [exact Htag|].
all: apply RNat_succ, HE; [tea|].
+ apply (RNat_F 2 v (tPair r1 r2 r3 r4)); tea; [discriminate|cbn; lia].
+ apply (RNat_F 3 v (tPair r1 r2 r3 r4)); tea; [discriminate|cbn; lia].
Qed.

Definition hm_id (ev : bool -> term -> option term) (b : bool) (hr r : term) : option (option term) :=
  match r with tRefl _ _ => Some (ev b hr) | _ => None end.

Lemma cHId_closed : forall σ, subst_term σ cHId = cHId.
Proof. closed_tac cHId. Qed.
#[export] Hint Rewrite cHId_closed : closed.

Lemma cHId_spec : forall E ev d b x A a P hr y e r v, EvSpec E ev -> RNat d (b2n b) ->
  RNat x (quote (tIdElim A a P hr y e)) ->
  RNat v (quote r) -> RNat (apps cHId ⟪E; d; x; v⟫) (encH (hm_id ev b hr r)).
Proof.
intros * HE Hd Hx Hv; beta_tac cHId.
assert (Htag : RNat (apps cEqb ⟪apps cHd ⟪v⟫; qNat 16⟫) (b2n (Nat.eqb (tag_of r) 16))).
{ apply cEqb_spec; [now apply RNat_tag|apply RNat_qNat]. }
destruct r; try (apply cIte_false; [exact Htag|apply RNat_zero]).
apply cIte_true; [exact Htag|].
apply RNat_succ, HE; [tea|].
apply (RNat_F 3 x (tIdElim A a P hr y e)); tea; [discriminate|cbn; lia].
Qed.

(** *** Quote *)

Definition quote_code (ev : bool -> term -> option term) (t : term) : nat :=
  match ev true t with
  | None => 0
  | Some t' => if is_closedn 0 t' then S (quote (qNat (quote (erase t')))) else S (quote (tQuote t'))
  end.

Lemma cQuoteB_closed : forall σ, subst_term σ cQuoteB = cQuoteB.
Proof. closed_tac cQuoteB. Qed.
#[export] Hint Rewrite cQuoteB_closed : closed.

Lemma cQuoteB_spec : forall E ev x t, EvSpec E ev -> RNat x (quote (tQuote t)) ->
  RNat (apps cQuoteB ⟪E; x⟫) (quote_code ev t).
Proof.
intros * HE Hx; beta_tac cQuoteB.
assert (Hr : RNat (apps E ⟪tSucc tZero; F 0 x⟫) (encO (ev true t))).
{ apply HE; [rnum|apply (RNat_F 0 x (tQuote t)); tea; [discriminate|cbn; lia]]. }
unfold quote_code; destruct (ev true t) as [t'|]; cbn [encO] in Hr.
+ eapply (cIfz_succ N); [exact Hr|].
  apply RNat_pred_encO in Hr.
  apply (cIte_spec N); [now apply cClosed_spec, RNat_zero| |].
  - now apply RNat_succ, cQNat_spec, cErase_spec.
  - apply RNat_succ, (cnode_spec 18 ⟪_⟫ ⟪_⟫); rnats; tea.
+ apply (cIfz_zero N); [tea|apply RNat_zero].
Qed.

(** *** Step and reflect *)

Definition step_core (mu : term -> option (nat × term)) (fin : nat -> nat -> option term) (t' u' : term) : option term :=
  match uNat u' with
  | None => None
  | Some n =>
    match mu (tApp (erase t') (qNat n)) with
    | None => None
    | Some (st, v) => match uNat v with None => None | Some v' => fin st v' end
    end
  end.

Definition step_code (ev : bool -> term -> option term) (mu : term -> option (nat × term)) (g : nat)
  (fin : nat -> nat -> option term) (t u : term) : nat :=
  match ev true t with
  | None => 0
  | Some t' =>
    match ev true u with
    | None => 0
    | Some u' =>
      if is_closedn 0 t' && is_closedn 0 u' then encO (step_core mu fin t' u')
      else S (node g (lcode ⟪quote t'; quote u'⟫))
    end
  end.

Lemma cStepCore_closed : forall σ, subst_term σ cStepCore = cStepCore.
Proof. closed_tac cStepCore. Qed.
#[export] Hint Rewrite cStepCore_closed : closed.

Definition FinSpec (fin : term) (finm : nat -> nat -> option term) :=
  forall a st c v, RNat a st -> RNat c v -> RNat (apps fin ⟪a; c⟫) (encO (finm st v)).

Lemma cStepCore_spec : forall M mu t t' u u' fin finm, MuSpec M mu -> FinSpec fin finm ->
  RNat t (quote t') -> RNat u (quote u') ->
  RNat (apps cStepCore ⟪M; t; u; fin⟫) (encO (step_core mu finm t' u')).
Proof.
intros * HM Hfin Ht Hu; beta_tac cStepCore.
assert (Hn := cUNat_spec _ _ Hu).
unfold step_core; destruct (uNat u') as [n|]; cbn [encN] in Hn.
2:{ apply (cIfz_zero N); [tea|apply RNat_zero]. }
eapply (cIfz_succ N); [exact Hn|].
assert (Hans : RNat (apps M ⟪cnode 4 ⟪apps cErase ⟪t⟫; apps cQNat ⟪apps cPred ⟪apps cUNat ⟪u⟫⟫⟫⟫⟫)
  (encM (mu (tApp (erase t') (qNat n))))).
{ apply HM, (cnode_spec 4 ⟪_; _⟫ ⟪_; _⟫); rnats; [now apply cErase_spec|].
  now apply cQNat_spec, (cPred_spec _ (S n)). }
destruct (mu (tApp (erase t') (qNat n))) as [[st v]|]; cbn [encM] in Hans.
2:{ apply (cIfz_zero N); [tea|apply RNat_zero]. }
eapply (cIfz_succ N); [exact Hans|].
apply (cPred_spec _ (S _)) in Hans.
assert (Hv : RNat (apps cUNat ⟪apps cSnd ⟪apps cPred ⟪apps M ⟪cnode 4 ⟪apps cErase ⟪t⟫; apps cQNat ⟪apps cPred ⟪apps cUNat ⟪u⟫⟫⟫⟫⟫⟫⟫⟫) (encN (uNat v))).
{ apply cUNat_spec; eapply RNat_conv; [now apply cSnd_spec|apply nsnd_npair]. }
destruct (uNat v) as [v'|]; cbn [encN] in Hv.
2:{ apply (cIfz_zero N); [tea|apply RNat_zero]. }
eapply (cIfz_succ N); [exact Hv|].
apply Hfin.
+ eapply RNat_conv; [now apply cFst_spec|apply nfst_npair].
+ now apply (cPred_spec _ (S _)).
Qed.

Lemma cStepB_closed : forall σ, subst_term σ cStepB = cStepB.
Proof. closed_tac cStepB. Qed.
#[export] Hint Rewrite cStepB_closed : closed.

Lemma cStepB_spec : forall E ev M mu x t0 t u w g fin finm,
  EvSpec E ev -> MuSpec M mu -> FinSpec fin finm ->
  RNat x (quote t0) -> tag_of t0 <> 0 -> fields t0 = ⟪t; u⟫ -> RNat w g ->
  RNat (apps cStepB ⟪E; M; x; w; fin⟫) (step_code ev mu g finm t u).
Proof.
intros * HE HM Hfin Hx Ht Hf Hw; beta_tac cStepB.
assert (Ht' : RNat (apps E ⟪tSucc tZero; F 0 x⟫) (encO (ev true t))).
{ apply HE; [rnum|]; replace t with (nth 0 (fields t0) (tRel 0)) by now rewrite Hf.
  apply RNat_F; tea; rewrite Hf; cbn; lia. }
assert (Hu' : RNat (apps E ⟪tSucc tZero; F 1 x⟫) (encO (ev true u))).
{ apply HE; [rnum|]; replace u with (nth 1 (fields t0) (tRel 0)) by now rewrite Hf.
  apply RNat_F; tea; rewrite Hf; cbn; lia. }
unfold step_code; destruct (ev true t) as [t'|]; cbn [encO] in Ht'.
2:{ apply (cIfz_zero N); [tea|apply RNat_zero]. }
eapply (cIfz_succ N); [exact Ht'|].
destruct (ev true u) as [u'|]; cbn [encO] in Hu'.
2:{ apply (cIfz_zero N); [tea|apply RNat_zero]. }
eapply (cIfz_succ N); [exact Hu'|].
apply RNat_pred_encO in Ht', Hu'.
apply (cIte_spec N).
+ apply cAndb_spec; now apply cClosed_spec, RNat_zero.
+ now apply cStepCore_spec.
+ apply RNat_succ, cCons_node; [tea|].
  apply (clist_spec ⟪_; _⟫ ⟪_; _⟫); rnats; tea.
Qed.

Lemma cFinStep_closed : forall σ, subst_term σ cFinStep = cFinStep.
Proof. closed_tac cFinStep. Qed.
#[export] Hint Rewrite cFinStep_closed : closed.

Lemma cFinStep_spec : FinSpec cFinStep (fun st _ => Some (qNat st)).
Proof.
intros a st c v Ha Hc; beta_tac cFinStep.
now apply RNat_succ, cQNat_spec.
Qed.

Lemma cFinRefl_closed : forall σ, subst_term σ cFinRefl = cFinRefl.
Proof. closed_tac cFinRefl. Qed.
#[export] Hint Rewrite cFinRefl_closed : closed.

Lemma cFinRefl_spec : FinSpec cFinRefl (fun st v => Some (qEvalTm st v)).
Proof.
intros a st c v Ha Hc; beta_tac cFinRefl.
now apply RNat_succ, cQEvalTm_spec.
Qed.

(** *** The body of the evaluator *)

Arguments quote : simpl never.

(** Branches of the evaluator, indexed by the tag of the evaluated term.
    Variables: [E] = 3, [M] = 2, [d] = 1, [x] = 0. *)

Lemma cBody_closed : forall σ, subst_term σ cBody = cBody.
Proof. closed_tac cBody. Qed.
#[export] Hint Rewrite cBody_closed : closed.

Ltac meta_destruct ev :=
  repeat match goal with
  | |- context [ev ?b ?t] => destruct (ev b t)
  | |- context [if ?c then _ else _] => destruct c
  end.

Ltac meta_destruct_mu ev mu :=
  repeat (cbn [bindopt]; match goal with
  | |- context [ev ?b ?t] => destruct (ev b t)
  | |- context [mu ?t] => destruct (mu t) as [[? ?]|]
  | |- context [uNat ?t] => destruct (uNat t)
  | |- context [if ?c then _ else _] => destruct c
  end).

Lemma cBody_spec : forall E ev M mu d b x t k, EvSpec E ev -> MuSpec M mu ->
  RNat d (b2n b) -> RNat x (quote t) ->
  RNat (apps cBody ⟪E; M; d; x⟫) (encO (eval_body ev mu b t k)).
Proof.
intros * HE HM Hd Hx.
to_apps; unfold cBody; apply R_lams; [reflexivity|].
change (R N (subst_term (srev ⟪E; M; d; x⟫ tRel) (switch N (apps cHd ⟪tRel 0⟫) body_branches tZero)) (encO (eval_body ev mu b t k))).
rewrite switch_subst.
eapply switch_spec; [cbn; apply RNat_tag, Hx|].
destruct t; cbn [tag_of body_branches List.app nth map]; cbn_term.
(** Atoms *)
all: try match goal with |- R N (tSucc _) _ => apply RNat_succ, Hx end.
(** Canonical forms *)
all: try match goal with |- R N (tApp (tApp (tApp cCanon _) _) _) _ =>
  eapply RNat_conv; [apply cCanon_spec; tea; discriminate|];
  destruct b; [|reflexivity]; unfold deepall_code; cbn; meta_destruct ev; reflexivity end.
(** Eliminators *)
+ eapply RNat_conv; [apply (cElim_spec E ev d b x (tApp t1 t2) tZero 0 _ (hm_app ev b t2)); tea; try (discriminate + rnum + (cbn; lia))|].
  - intros; now eapply cHApp_spec.
  - unfold elim_code; cbn.
    destruct (ev false t1) as [r|]; [|reflexivity].
    destruct r; cbn; first [reflexivity|unfold deepall_code; cbn; meta_destruct ev; reflexivity].
+ eapply RNat_conv; [apply (cElim_spec E ev d b x (tNatElim t1 t2 t3 t4) (qNat 3) 3 _ (hm_nat ev b t1 t2 t3)); tea; try (discriminate + rnum + (cbn; lia))|].
  - intros; now eapply cHNat_spec.
  - unfold elim_code; cbn.
    destruct (ev false t4) as [r|]; [|reflexivity].
    destruct r; cbn; first [reflexivity|unfold deepall_code; cbn; meta_destruct ev; reflexivity].
+ eapply RNat_conv; [apply (cElim_spec E ev d b x (tEmptyElim t1 t2) (qNat 1) 1 _ (fun _ => None)); tea; try (discriminate + rnum + (cbn; lia))|].
  - intros r v Hv; exact (cHNone_spec r v Hv).
  - unfold elim_code; cbn.
    destruct (ev false t2) as [r|]; [|reflexivity].
    unfold deepall_code; cbn; meta_destruct ev; reflexivity.
+ eapply RNat_conv; [apply (cElim_spec E ev d b x (tFst t) tZero 0 _ (hm_fst ev b)); tea; try (discriminate + rnum + (cbn; lia))|].
  - intros r v Hv; destruct (cHProj_spec E ev d b r v HE Hd Hv) as [H _]; exact H.
  - unfold elim_code; cbn.
    destruct (ev false t) as [r|]; [|reflexivity].
    destruct r; cbn; first [reflexivity|unfold deepall_code; cbn; meta_destruct ev; reflexivity].
+ eapply RNat_conv; [apply (cElim_spec E ev d b x (tSnd t) tZero 0 _ (hm_snd ev b)); tea; try (discriminate + rnum + (cbn; lia))|].
  - intros r v Hv; destruct (cHProj_spec E ev d b r v HE Hd Hv) as [_ H]; exact H.
  - unfold elim_code; cbn.
    destruct (ev false t) as [r|]; [|reflexivity].
    destruct r; cbn; first [reflexivity|unfold deepall_code; cbn; meta_destruct ev; reflexivity].
+ eapply RNat_conv; [apply (cElim_spec E ev d b x (tIdElim t1 t2 t3 t4 t5 t6) (qNat 5) 5 _ (hm_id ev b t4)); tea; try (discriminate + rnum + (cbn; lia))|].
  - intros; now eapply cHId_spec.
  - unfold elim_code; cbn.
    destruct (ev false t6) as [r|]; [|reflexivity].
    destruct r; cbn; first [reflexivity|unfold deepall_code; cbn; meta_destruct ev; reflexivity].
(** Quote *)
+ eapply RNat_conv; [now apply cQuoteB_spec|].
  unfold quote_code; cbn.
  destruct (ev true t) as [t'|]; [|reflexivity]; cbn.
  remember (is_closedn 0 t') as c eqn:Hc; symmetry in Hc; destruct c; [|reflexivity].
  reflexivity.
(** Step and reflect *)
+ eapply RNat_conv; [apply (cStepB_spec E ev M mu x (tStep t1 t2) t1 t2 (qNat 19) 19 cFinStep); tea; try (discriminate + rnum + reflexivity); apply cFinStep_spec|].
  unfold step_code, step_core; cbn.
  meta_destruct_mu ev mu; reflexivity.
+ eapply RNat_conv; [apply (cStepB_spec E ev M mu x (tReflect t1 t2) t1 t2 (qNat 20) 20 cFinRefl); tea; try (discriminate + rnum + reflexivity); apply cFinRefl_spec|].
  unfold step_code, step_core; cbn.
  meta_destruct_mu ev mu; reflexivity.
Qed.

(** ** Iterating the body *)

(** The state after [k] iterations packs the evaluator [eval · · (k - 1)] and the
    minimization up to [k] into a single function [λ sel d x. …] where [sel = 0]
    selects the evaluator and [sel = 1] the minimization. *)

Definition evprev (k : nat) (b : bool) (t : term) : option term :=
  match k with 0 => None | S k => eval b t k end.

Definition mu_k (k : nat) (t : term) : option (nat × term) := murec (fun j => eval true t j) k.

Lemma eval_body_unfold : forall b t k, eval b t k = eval_body (evprev k) (mu_k k) b t k.
Proof.
intros b t []; reflexivity.
Qed.

Lemma mu_k_0 : forall t, mu_k 0 t = None.
Proof.
reflexivity.
Qed.

Lemma mu_k_S : forall k t, mu_k (S k) t =
  match mu_k k t with
  | None => match eval true t k with None => None | Some v => Some (k, v) end
  | Some r => Some r
  end.
Proof.
intros; unfold mu_k, murec; cbn [murec0].
destruct murec0; [reflexivity|].
now destruct eval.
Qed.

Definition StateSpec (k : nat) (F : term) :=
  EvSpec (apps F ⟪tZero⟫) (evprev k) × MuSpec (apps F ⟪tSucc tZero; tZero⟫) (mu_k k).

Lemma StateSpec_exp : forall k F F', [F ⤳* F'] -> StateSpec k F' -> StateSpec k F.
Proof.
intros k F F' Hr [HE HM]; split.
+ intros d b x t Hd Hx; eapply RNat_exp; [|now apply HE].
  apply (redalg_apps _ _ ⟪_; _; _⟫ Hr).
+ intros x t Hx; eapply RNat_exp; [|now apply HM].
  apply (redalg_apps _ _ ⟪_; _; _⟫ Hr).
Qed.

Lemma cStateS_closed : forall σ, subst_term σ cStateS = cStateS.
Proof. closed_tac cStateS. Qed.
#[export] Hint Rewrite cStateS_closed : closed.

Lemma cState_closed : forall σ, subst_term σ cState = cState.
Proof. closed_tac cState. Qed.
#[export] Hint Rewrite cState_closed : closed.

Lemma cStateS_spec : forall m n F, RNat n m -> StateSpec m F -> StateSpec (S m) (apps cStateS ⟪n; F⟫).
Proof.
intros m n F Hn [HE HM]; split.
+ intros d b x t Hd Hx; beta_tac cStateS.
  apply (cIfz_zero N); [apply RNat_zero|].
  cbn [evprev]; rewrite eval_body_unfold.
  apply cBody_spec; tea.
+ intros x t Hx; beta_tac cStateS.
  eapply (cIfz_succ N); [rnum|].
  assert (Hm := HM x t Hx).
  rewrite mu_k_S; destruct (mu_k m t) as [[st v]|]; cbn [encM] in Hm |- *.
  - eapply (cIfz_succ N); [exact Hm|tea].
  - apply (cIfz_zero N); [tea|].
    assert (Hb : RNat (apps cBody ⟪apps F ⟪tZero⟫; apps F ⟪tSucc tZero; tZero⟫; tSucc tZero; x⟫) (encO (eval true t m))).
    { rewrite eval_body_unfold; apply cBody_spec; tea; rnum. }
    destruct (eval true t m) as [v|]; cbn [encO] in Hb |- *.
    * eapply (cIfz_succ N); [exact Hb|].
      apply cCons_spec; [tea|].
      now apply (cPred_spec _ (S _)).
    * apply (cIfz_zero N); [tea|apply RNat_zero].
Qed.

Lemma cState_spec : forall w k, RNat w k -> StateSpec k (apps cState ⟪w⟫).
Proof.
intros w k Hw.
eapply StateSpec_exp; [unfold cState; apply (redalg_lams ⟪_⟫ _ ⟪_⟫); reflexivity|].
cbn; autorewrite with closed.
revert w k Hw; refine (natElim_ind StateSpec _ _ _ _ _ _).
+ intros; eapply StateSpec_exp; tea.
+ split.
  - intros d b x t Hd Hx.
    change (R N (apps (lams ⟪tNat; tNat; tNat⟫ tZero) ⟪tZero; d; x⟫) 0).
    apply R_lams; [reflexivity|apply RNat_zero].
  - intros x t Hx.
    change (R N (apps (lams ⟪tNat; tNat; tNat⟫ tZero) ⟪tSucc tZero; tZero; x⟫) 0).
    apply R_lams; [reflexivity|apply RNat_zero].
+ intros m n F Hn HF; now apply (cStateS_spec m n F).
Qed.

(** ** The internal evaluator *)

Lemma tRun_spec : forall x t w k, RNat x (quote t) -> RNat w k ->
  RNat (apps tRun ⟪x; w⟫) (encO (eval true t k)).
Proof.
intros x t w k Hx Hw; beta_tac tRun.
destruct (cState_spec w k Hw) as [HE HM].
rewrite eval_body_unfold.
apply cBody_spec; tea; rnum.
Qed.

Lemma tRun_None : forall t k,
  eval true t k = None ->
  [tApp (tApp tRun (qNat (quote t))) (qNat k) ⇶* tZero].
Proof.
intros t k Heval.
assert (H := tRun_spec _ t _ k (RNat_qNat _) (RNat_qNat _)).
rewrite Heval in H.
exact (RNat_dred _ _ H).
Qed.

Lemma tRun_Some : forall t v k,
  eval true t k = Some v ->
  [tApp (tApp tRun (qNat (quote t))) (qNat k) ⇶* tSucc (qNat (quote v))].
Proof.
intros t v k Heval.
assert (H := tRun_spec _ t _ k (RNat_qNat _) (RNat_qNat _)).
rewrite Heval in H.
exact (RNat_dred _ _ H).
Qed.

(** ** The [run] primitive of the computation model *)

Lemma tRun_closed : forall σ, subst_term σ tRun = tRun.
Proof. closed_tac tRun. Qed.
#[export] Hint Rewrite tRun_closed : closed.

Lemma tRunNat_closed : forall σ, subst_term σ tRunNat = tRunNat.
Proof. closed_tac tRunNat. Qed.
#[export] Hint Rewrite tRunNat_closed : closed.

Lemma tRunNat_spec : forall c t w u z k, RNat c (quote t) -> RNat w u -> RNat z k ->
  RNat (apps tRunNat ⟪c; w; z⟫)
    (match eval true (tApp t (qNat u)) k with None => 0 | Some v => encN (uNat v) end).
Proof.
intros * Hc Hw Hz; beta_tac tRunNat.
assert (Hr : RNat (apps tRun ⟪cnode 4 ⟪c; apps cQNat ⟪w⟫⟫; z⟫) (encO (eval true (tApp t (qNat u)) k))).
{ apply tRun_spec; [|tea].
  apply (cnode_spec 4 ⟪_; _⟫ ⟪_; _⟫); rnats; [tea|now apply cQNat_spec]. }
destruct eval as [v|]; cbn [encO] in Hr.
+ eapply (cIfz_succ N); [exact Hr|].
  now apply cUNat_spec, RNat_pred_encO.
+ apply (cIfz_zero N); [tea|apply RNat_zero].
Qed.

Lemma run_spec_None : forall t u k,
  eval true (tApp t (qNat u)) k = None ->
  [tApp (tApp (tApp run (qNat (Computation.quote t))) (qNat u)) (qNat k) ⇶* tZero].
Proof.
intros t u k Heval.
assert (H := tRunNat_spec _ t _ u _ k (RNat_qNat _) (RNat_qNat _) (RNat_qNat _)).
rewrite Heval in H.
exact (RNat_dred _ _ H).
Qed.

Lemma run_spec_Some : forall t u k v,
  eval true (tApp t (qNat u)) k = Some (qNat v) ->
  [tApp (tApp (tApp run (qNat (Computation.quote t))) (qNat u)) (qNat k) ⇶* tSucc (qNat v)].
Proof.
intros t u k v Heval.
assert (H := tRunNat_spec _ t _ u _ k (RNat_qNat _) (RNat_qNat _) (RNat_qNat _)).
rewrite Heval, uNat_qNat in H.
exact (RNat_dred _ _ H).
Qed.

(** ** Typing *)

Section Wf.

Context `{GenericTypingProperties}.

Lemma ety_arr : forall A B, ety (Arr A B) = tProd (ety A) (ety B).
Proof.
intros; cbn [ety]; now rewrite ety_ren.
Qed.

Lemma wft_nat {Γ} : [|- Γ] -> [Γ |- tNat].
Proof.
intros; now apply wft_term, ty_nat.
Qed.

Lemma wft_ety {Γ} T : [|- Γ] -> [Γ |- ety T].
Proof.
induction T; intros; cbn [ety]; [now apply wft_nat|].
apply wft_simple_arr; eauto.
Qed.

Lemma wfc_ety {Γ} T : [|- Γ] -> [|- Γ ,, ety T].
Proof.
intros; apply wfc_cons; [tea|now apply wft_ety].
Qed.

Lemma wfc_nat {Γ} : [|- Γ] -> [|- Γ ,, tNat].
Proof.
intros; apply wfc_cons; [tea|now apply wft_nat].
Qed.

Lemma in_ctx_ety0 {Γ} A : in_ctx (Γ ,, ety A) 0 (ety A).
Proof.
rewrite <- (ety_ren A ↑) at 2; constructor.
Qed.

Lemma in_ctx_nat0 {Γ} : in_ctx (Γ ,, tNat) 0 (ety N).
Proof.
exact (@in_ctx_ety0 Γ N).
Qed.

Lemma in_ctx_etyS {Γ} n d T : in_ctx Γ n (ety T) -> in_ctx (Γ ,, d) (S n) (ety T).
Proof.
intros Hin; rewrite <- (ety_ren T ↑); now constructor.
Qed.

Lemma ty_varS {Γ} n T : [|- Γ] -> in_ctx Γ n (ety T) -> [Γ |- tRel n : ety T].
Proof.
intros; now apply ty_var.
Qed.

Lemma ty_lamS {Γ} A B b : [|- Γ] -> [Γ ,, ety A |- b : ety B] -> [Γ |- tLambda (ety A) b : ety (Arr A B)].
Proof.
intros; cbn [ety]; rewrite ety_ren.
apply ty_lam; [now apply wft_ety|tea].
Qed.

Lemma ty_lamN {Γ} B b : [|- Γ] -> [Γ ,, tNat |- b : ety B] -> [Γ |- tLambda tNat b : ety (Arr N B)].
Proof.
exact (@ty_lamS Γ N B b).
Qed.

Lemma ty_appS {Γ} A B f a : [|- Γ] -> [Γ |- f : ety (Arr A B)] -> [Γ |- a : ety A] -> [Γ |- tApp f a : ety B].
Proof.
intros; eapply ty_simple_app; tea; now apply wft_ety.
Qed.

Lemma ty_zeroS {Γ} : [|- Γ] -> [Γ |- tZero : ety N].
Proof.
intros; now apply ty_zero.
Qed.

Lemma ty_succS {Γ} n : [Γ |- n : ety N] -> [Γ |- tSucc n : ety N].
Proof.
intros; now apply ty_succ.
Qed.

Lemma ty_natElimS {Γ} T hz hs n : [|- Γ] ->
  [Γ |- hz : ety T] -> [Γ |- hs : ety (Arr N (Arr T T))] -> [Γ |- n : ety N] ->
  [Γ |- tNatElim (ety T)⟨↑⟩ hz hs n : ety T].
Proof.
intros HΓ Hz Hs Hn.
enough (Hty : [Γ |- tNatElim (ety T)⟨↑⟩ hz hs n : ((ety T)⟨↑⟩)[n..]]) by now rewrite shift_one_eq in Hty.
apply ty_natElim.
+ rewrite ety_ren; apply wft_ety, wfc_nat, HΓ.
+ now rewrite shift_one_eq.
+ unfold elimSuccHypTy; rewrite ety_ren, ety_subst, ety_ren.
  now rewrite !ety_arr in Hs.
+ tea.
Qed.

Lemma ty_natElimN {Γ} hz hs n : [|- Γ] ->
  [Γ |- hz : ety N] -> [Γ |- hs : ety (Arr N (Arr N N))] -> [Γ |- n : ety N] ->
  [Γ |- tNatElim tNat hz hs n : ety N].
Proof.
exact (@ty_natElimS Γ N hz hs n).
Qed.

Lemma ty_dflt {Γ} T : [|- Γ] -> [Γ |- dflt T : ety T].
Proof.
revert Γ; induction T; intros Γ HΓ; cbn [dflt].
+ now apply ty_zeroS.
+ apply ty_lamS; [tea|].
  apply IHT2, wfc_ety, HΓ.
Qed.

Lemma ty_qNat {Γ} n : [|- Γ] -> [Γ |- qNat n : ety N].
Proof.
intros; induction n; cbn [qNat]; [now apply ty_zeroS|now apply ty_succS].
Qed.

Create HintDb tyc.
#[local] Hint Resolve wfc_ety wfc_nat in_ctx_ety0 in_ctx_nat0 in_ctx_etyS ty_dflt ty_qNat : tyc.

Ltac tyc_step :=
  match goal with
  | |- [|- _] => eauto 20 with tyc
  | |- in_ctx _ _ _ => eauto 20 with tyc
  | |- [_ |- tLambda tNat _ : _] => apply ty_lamN
  | |- [_ |- tLambda _ _ : _] => apply ty_lamS
  | |- [_ |- tApp _ _ : _] => eapply ty_appS
  | |- [_ |- tRel _ : _] => eapply ty_varS
  | |- [_ |- tZero : _] => apply ty_zeroS
  | |- [_ |- tSucc _ : _] => apply ty_succS
  | |- [_ |- tNatElim tNat _ _ _ : _] => apply ty_natElimN
  | |- [_ |- tNatElim _ _ _ _ : _] => apply ty_natElimS
  | |- [_ |- _ : _] => eauto 20 with tyc
  end.

Ltac tyc := repeat tyc_step.

Ltac ty_comb c :=
  intros; unfold c; cbn [lams apps clist cnode F qNat]; tyc.

Lemma cConstS_ty {Γ} T : [|- Γ] -> [Γ |- cConstS T : ety (Arr T (Arr N (Arr T T)))].
Proof. ty_comb cConstS. Qed.
#[local] Hint Resolve cConstS_ty : tyc.

Lemma cIfz_ty {Γ} T : [|- Γ] -> [Γ |- cIfz T : ety (Arr N (Arr T (Arr T T)))].
Proof. ty_comb cIfz. Qed.
#[local] Hint Resolve cIfz_ty : tyc.

Lemma cSuccS_ty {Γ} : [|- Γ] -> [Γ |- cSuccS : ety (Arr N (Arr N N))].
Proof. ty_comb cSuccS. Qed.
#[local] Hint Resolve cSuccS_ty : tyc.

Lemma cProjS_ty {Γ} : [|- Γ] -> [Γ |- cProjS : ety (Arr N (Arr N N))].
Proof. ty_comb cProjS. Qed.
#[local] Hint Resolve cProjS_ty : tyc.

Lemma cAdd_ty {Γ} : [|- Γ] -> [Γ |- cAdd : ety (Arr N (Arr N N))].
Proof. ty_comb cAdd. Qed.
#[local] Hint Resolve cAdd_ty : tyc.

Lemma cPred_ty {Γ} : [|- Γ] -> [Γ |- cPred : ety (Arr N N)].
Proof. ty_comb cPred. Qed.
#[local] Hint Resolve cPred_ty : tyc.

Lemma cPredS_ty {Γ} : [|- Γ] -> [Γ |- cPredS : ety (Arr N (Arr N N))].
Proof. ty_comb cPredS. Qed.
#[local] Hint Resolve cPredS_ty : tyc.

Lemma cSub_ty {Γ} : [|- Γ] -> [Γ |- cSub : ety (Arr N (Arr N N))].
Proof. ty_comb cSub. Qed.
#[local] Hint Resolve cSub_ty : tyc.

Lemma cEqb_ty {Γ} : [|- Γ] -> [Γ |- cEqb : ety (Arr N (Arr N N))].
Proof. ty_comb cEqb. Qed.
#[local] Hint Resolve cEqb_ty : tyc.

Lemma cLtb_ty {Γ} : [|- Γ] -> [Γ |- cLtb : ety (Arr N (Arr N N))].
Proof. ty_comb cLtb. Qed.
#[local] Hint Resolve cLtb_ty : tyc.

Lemma cAndb_ty {Γ} : [|- Γ] -> [Γ |- cAndb : ety (Arr N (Arr N N))].
Proof. ty_comb cAndb. Qed.
#[local] Hint Resolve cAndb_ty : tyc.

Lemma cOrb_ty {Γ} : [|- Γ] -> [Γ |- cOrb : ety (Arr N (Arr N N))].
Proof. ty_comb cOrb. Qed.
#[local] Hint Resolve cOrb_ty : tyc.

Lemma cNegb_ty {Γ} : [|- Γ] -> [Γ |- cNegb : ety (Arr N N)].
Proof. ty_comb cNegb. Qed.
#[local] Hint Resolve cNegb_ty : tyc.

Lemma cTriS_ty {Γ} : [|- Γ] -> [Γ |- cTriS : ety (Arr N (Arr N N))].
Proof. ty_comb cTriS. Qed.
#[local] Hint Resolve cTriS_ty : tyc.

Lemma cTri_ty {Γ} : [|- Γ] -> [Γ |- cTri : ety (Arr N N)].
Proof. ty_comb cTri. Qed.
#[local] Hint Resolve cTri_ty : tyc.

Lemma cPair_ty {Γ} : [|- Γ] -> [Γ |- cPair : ety (Arr N (Arr N N))].
Proof. ty_comb cPair. Qed.
#[local] Hint Resolve cPair_ty : tyc.

Lemma cMkp_ty {Γ} : [|- Γ] -> [Γ |- cMkp : ety (Arr N (Arr N (Arr N N)))].
Proof. ty_comb cMkp. Qed.
#[local] Hint Resolve cMkp_ty : tyc.

Lemma cUnpS_ty {Γ} : [|- Γ] -> [Γ |- cUnpS : ety (Arr N (Arr (Arr N N) (Arr N N)))].
Proof. ty_comb cUnpS. Qed.
#[local] Hint Resolve cUnpS_ty : tyc.

Lemma cUnpair_ty {Γ} : [|- Γ] -> [Γ |- cUnpair : ety (Arr N (Arr N N))].
Proof. ty_comb cUnpair. Qed.
#[local] Hint Resolve cUnpair_ty : tyc.

Lemma cFst_ty {Γ} : [|- Γ] -> [Γ |- cFst : ety (Arr N N)].
Proof. ty_comb cFst. Qed.
#[local] Hint Resolve cFst_ty : tyc.

Lemma cSnd_ty {Γ} : [|- Γ] -> [Γ |- cSnd : ety (Arr N N)].
Proof. ty_comb cSnd. Qed.
#[local] Hint Resolve cSnd_ty : tyc.

Lemma cIte_ty {Γ} T : [|- Γ] -> [Γ |- cIte T : ety (Arr N (Arr T (Arr T T)))].
Proof. ty_comb cIte. Qed.
#[local] Hint Resolve cIte_ty : tyc.

Fixpoint AllT (P : term -> Type) (l : list term) : Type := match l with
| nil => unit
| cons b l => P b × AllT P l
end.

Lemma ty_switch {Γ} T n bs d : [|- Γ] -> [Γ |- n : ety N] ->
  AllT (fun b => [Γ |- b : ety T]) bs -> [Γ |- d : ety T] -> [Γ |- switch T n bs d : ety T].
Proof.
intros HΓ Hn; revert n Hn; induction bs as [|b bs IHbs]; intros n Hn Hbs Hd; cbn [switch]; [tea|].
destruct Hbs as [Hb Hbs].
cbn [apps]; eapply ty_appS; [tea| |].
+ eapply ty_appS; [tea| |tea].
  eapply ty_appS; [tea|now apply cIfz_ty|tea].
+ apply IHbs; tea.
  eapply ty_appS; [tea|now apply cPred_ty|tea].
Qed.

Lemma cIgn1_ty {Γ} T : [|- Γ] -> [Γ |- cIgn1 T : ety (Arr (Arr (Arr N T) (Arr N T)) (Arr N (Arr (Arr N T) (Arr N T))))].
Proof. ty_comb cIgn1. Qed.
#[local] Hint Resolve cIgn1_ty : tyc.

Lemma cRec_ty {Γ} T : [|- Γ] -> [Γ |- cRec T : ety (Arr (Arr (Arr N T) (Arr N T)) (Arr N T))].
Proof. ty_comb cRec. Qed.
#[local] Hint Resolve cRec_ty : tyc.

Lemma cCons_ty {Γ} : [|- Γ] -> [Γ |- cCons : ety (Arr N (Arr N N))].
Proof. ty_comb cCons. Qed.
#[local] Hint Resolve cCons_ty : tyc.

Lemma cHd_ty {Γ} : [|- Γ] -> [Γ |- cHd : ety (Arr N N)].
Proof. ty_comb cHd. Qed.
#[local] Hint Resolve cHd_ty : tyc.

Lemma cTl_ty {Γ} : [|- Γ] -> [Γ |- cTl : ety (Arr N N)].
Proof. ty_comb cTl. Qed.
#[local] Hint Resolve cTl_ty : tyc.

Lemma cNthS_ty {Γ} : [|- Γ] -> [Γ |- cNthS : ety (Arr N (Arr (Arr N N) (Arr N N)))].
Proof. ty_comb cNthS. Qed.
#[local] Hint Resolve cNthS_ty : tyc.

Lemma cNth_ty {Γ} : [|- Γ] -> [Γ |- cNth : ety (Arr N (Arr N N))].
Proof. ty_comb cNth. Qed.
#[local] Hint Resolve cNth_ty : tyc.

Lemma cMapiAlg_ty {Γ} : [|- Γ] -> [Γ |- cMapiAlg : ety (Arr (Arr N (Arr N N)) (Arr (Arr N (Arr N N)) (Arr N (Arr N N))))].
Proof. ty_comb cMapiAlg. Qed.
#[local] Hint Resolve cMapiAlg_ty : tyc.

Lemma cMapi_ty {Γ} : [|- Γ] -> [Γ |- cMapi : ety (Arr (Arr N (Arr N N)) (Arr N (Arr N N)))].
Proof. ty_comb cMapi. Qed.
#[local] Hint Resolve cMapi_ty : tyc.

Lemma cLAllAlg_ty {Γ} : [|- Γ] -> [Γ |- cLAllAlg : ety (Arr (Arr N N) (Arr N N))].
Proof. ty_comb cLAllAlg. Qed.
#[local] Hint Resolve cLAllAlg_ty : tyc.

Lemma cLAll_ty {Γ} : [|- Γ] -> [Γ |- cLAll : ety (Arr N N)].
Proof. ty_comb cLAll. Qed.
#[local] Hint Resolve cLAll_ty : tyc.

Lemma cTable_ty {Γ} tab : [|- Γ] -> [Γ |- cTable tab : ety (Arr N N)].
Proof.
intros HΓ; unfold cTable; cbn [lams].
apply ty_lamN; [tea|].
apply ty_switch; [now apply wfc_nat|now apply ty_varS; eauto with tyc| |now apply ty_zeroS, wfc_nat].
induction tab; cbn; [constructor|split; [now apply ty_qNat, wfc_nat|tea]].
Qed.
#[local] Hint Resolve cTable_ty : tyc.

Lemma cBnd_ty {Γ} : [|- Γ] -> [Γ |- cBnd : ety (Arr N (Arr N N))].
Proof. ty_comb cBnd. Qed.
#[local] Hint Resolve cBnd_ty : tyc.

Lemma cIgn_ty {Γ} : [|- Γ] -> [Γ |- cIgn : ety (Arr N (Arr N N))].
Proof. ty_comb cIgn. Qed.
#[local] Hint Resolve cIgn_ty : tyc.

Lemma cBindF_ty {Γ} : [|- Γ] -> [Γ |- cBindF : ety (Arr (Arr N (Arr N N)) (Arr N (Arr N (Arr N (Arr N N)))))].
Proof. ty_comb cBindF. Qed.
#[local] Hint Resolve cBindF_ty : tyc.

Lemma cShiftAlg_ty {Γ} : [|- Γ] -> [Γ |- cShiftAlg : ety (Arr (Arr N (Arr N N)) (Arr N (Arr N N)))].
Proof. ty_comb cShiftAlg. Qed.
#[local] Hint Resolve cShiftAlg_ty : tyc.

Lemma cShift_ty {Γ} : [|- Γ] -> [Γ |- cShift : ety (Arr N (Arr N N))].
Proof. ty_comb cShift. Qed.
#[local] Hint Resolve cShift_ty : tyc.

Lemma cShiftNS_ty {Γ} : [|- Γ] -> [Γ |- cShiftNS : ety (Arr N (Arr N N))].
Proof. ty_comb cShiftNS. Qed.
#[local] Hint Resolve cShiftNS_ty : tyc.

Lemma cShiftN_ty {Γ} : [|- Γ] -> [Γ |- cShiftN : ety (Arr N (Arr N N))].
Proof. ty_comb cShiftN. Qed.
#[local] Hint Resolve cShiftN_ty : tyc.

Lemma cSubstAlg_ty {Γ} : [|- Γ] -> [Γ |- cSubstAlg : ety (Arr N (Arr (Arr N (Arr N N)) (Arr N (Arr N N))))].
Proof. ty_comb cSubstAlg. Qed.
#[local] Hint Resolve cSubstAlg_ty : tyc.

Lemma cSubst_ty {Γ} : [|- Γ] -> [Γ |- cSubst : ety (Arr N (Arr N (Arr N N)))].
Proof. ty_comb cSubst. Qed.
#[local] Hint Resolve cSubst_ty : tyc.

Lemma cNoccAlg_ty {Γ} : [|- Γ] -> [Γ |- cNoccAlg : ety (Arr (Arr N (Arr N N)) (Arr N (Arr N N)))].
Proof. ty_comb cNoccAlg. Qed.
#[local] Hint Resolve cNoccAlg_ty : tyc.

Lemma cNocc_ty {Γ} : [|- Γ] -> [Γ |- cNocc : ety (Arr N (Arr N N))].
Proof. ty_comb cNocc. Qed.
#[local] Hint Resolve cNocc_ty : tyc.

Lemma cClosF_ty {Γ} : [|- Γ] -> [Γ |- cClosF : ety (Arr (Arr N (Arr N N)) (Arr N (Arr N (Arr N (Arr N N)))))].
Proof. ty_comb cClosF. Qed.
#[local] Hint Resolve cClosF_ty : tyc.

Lemma cClosAlg_ty {Γ} : [|- Γ] -> [Γ |- cClosAlg : ety (Arr (Arr N (Arr N N)) (Arr N (Arr N N)))].
Proof. ty_comb cClosAlg. Qed.
#[local] Hint Resolve cClosAlg_ty : tyc.

Lemma cClosed_ty {Γ} : [|- Γ] -> [Γ |- cClosed : ety (Arr N (Arr N N))].
Proof. ty_comb cClosed. Qed.
#[local] Hint Resolve cClosed_ty : tyc.

Lemma cClos0F_ty {Γ} : [|- Γ] -> [Γ |- cClos0F : ety (Arr N (Arr N N))].
Proof. ty_comb cClos0F. Qed.
#[local] Hint Resolve cClos0F_ty : tyc.

Lemma cNfF_ty {Γ} : [|- Γ] -> [Γ |- cNfF : ety (Arr (Arr N (Arr N N)) (Arr N (Arr N (Arr N N))))].
Proof. ty_comb cNfF. Qed.
#[local] Hint Resolve cNfF_ty : tyc.

Lemma cNfAlg_ty {Γ} : [|- Γ] -> [Γ |- cNfAlg : ety (Arr (Arr N (Arr N N)) (Arr N (Arr N N)))].
Proof. ty_comb cNfAlg. Qed.
#[local] Hint Resolve cNfAlg_ty : tyc.

Lemma cNf_ty {Γ} : [|- Γ] -> [Γ |- cNf : ety (Arr N (Arr N N))].
Proof. ty_comb cNf. Qed.
#[local] Hint Resolve cNf_ty : tyc.

Lemma cDnfF_ty {Γ} : [|- Γ] -> [Γ |- cDnfF : ety (Arr N (Arr N N))].
Proof. ty_comb cDnfF. Qed.
#[local] Hint Resolve cDnfF_ty : tyc.

Lemma cWhneAlg_ty {Γ} : [|- Γ] -> [Γ |- cWhneAlg : ety (Arr (Arr N N) (Arr N N))].
Proof. ty_comb cWhneAlg. Qed.
#[local] Hint Resolve cWhneAlg_ty : tyc.

Lemma cWhne_ty {Γ} : [|- Γ] -> [Γ |- cWhne : ety (Arr N N)].
Proof. ty_comb cWhne. Qed.
#[local] Hint Resolve cWhne_ty : tyc.

Lemma code_rel0_ty {Γ} : [|- Γ] -> [Γ |- code_rel0 : ety N].
Proof. ty_comb code_rel0. Qed.
#[local] Hint Resolve code_rel0_ty : tyc.

Lemma code_U_ty {Γ} : [|- Γ] -> [Γ |- code_U : ety N].
Proof. ty_comb code_U. Qed.
#[local] Hint Resolve code_U_ty : tyc.

Lemma cEraseLam_ty {Γ} : [|- Γ] -> [Γ |- cEraseLam : ety (Arr N N)].
Proof. ty_comb cEraseLam. Qed.
#[local] Hint Resolve cEraseLam_ty : tyc.

Lemma cErasePair_ty {Γ} : [|- Γ] -> [Γ |- cErasePair : ety (Arr N (Arr N N))].
Proof. ty_comb cErasePair. Qed.
#[local] Hint Resolve cErasePair_ty : tyc.

Lemma cRecF_ty {Γ} : [|- Γ] -> [Γ |- cRecF : ety (Arr (Arr N N) (Arr N (Arr N N)))].
Proof. ty_comb cRecF. Qed.
#[local] Hint Resolve cRecF_ty : tyc.

Lemma cEraseAlg_ty {Γ} : [|- Γ] -> [Γ |- cEraseAlg : ety (Arr (Arr N N) (Arr N N))].
Proof. ty_comb cEraseAlg. Qed.
#[local] Hint Resolve cEraseAlg_ty : tyc.

Lemma cErase_ty {Γ} : [|- Γ] -> [Γ |- cErase : ety (Arr N N)].
Proof. ty_comb cErase. Qed.
#[local] Hint Resolve cErase_ty : tyc.

Lemma cUNatAlg_ty {Γ} : [|- Γ] -> [Γ |- cUNatAlg : ety (Arr (Arr N N) (Arr N N))].
Proof. ty_comb cUNatAlg. Qed.
#[local] Hint Resolve cUNatAlg_ty : tyc.

Lemma cUNat_ty {Γ} : [|- Γ] -> [Γ |- cUNat : ety (Arr N N)].
Proof. ty_comb cUNat. Qed.
#[local] Hint Resolve cUNat_ty : tyc.

Lemma cQNatS_ty {Γ} : [|- Γ] -> [Γ |- cQNatS : ety (Arr N (Arr N N))].
Proof. ty_comb cQNatS. Qed.
#[local] Hint Resolve cQNatS_ty : tyc.

Lemma cQNat_ty {Γ} : [|- Γ] -> [Γ |- cQNat : ety (Arr N N)].
Proof. ty_comb cQNat. Qed.
#[local] Hint Resolve cQNat_ty : tyc.

Lemma code_nat_ty {Γ} : [|- Γ] -> [Γ |- code_nat : ety N].
Proof. ty_comb code_nat. Qed.
#[local] Hint Resolve code_nat_ty : tyc.

Lemma code_zero_ty {Γ} : [|- Γ] -> [Γ |- code_zero : ety N].
Proof. ty_comb code_zero. Qed.
#[local] Hint Resolve code_zero_ty : tyc.

Lemma code_IdZZ_ty {Γ} : [|- Γ] -> [Γ |- code_IdZZ : ety N].
Proof. ty_comb code_IdZZ. Qed.
#[local] Hint Resolve code_IdZZ_ty : tyc.

Lemma code_ReflZ_ty {Γ} : [|- Γ] -> [Γ |- code_ReflZ : ety N].
Proof. ty_comb code_ReflZ. Qed.
#[local] Hint Resolve code_ReflZ_ty : tyc.

Lemma cQEvalTyS_ty {Γ} : [|- Γ] -> [Γ |- cQEvalTyS : ety (Arr N (Arr N N))].
Proof. ty_comb cQEvalTyS. Qed.
#[local] Hint Resolve cQEvalTyS_ty : tyc.

Lemma cQEvalTy_ty {Γ} : [|- Γ] -> [Γ |- cQEvalTy : ety (Arr N (Arr N N))].
Proof. ty_comb cQEvalTy. Qed.
#[local] Hint Resolve cQEvalTy_ty : tyc.

Lemma cQEvalTmS_ty {Γ} : [|- Γ] -> [Γ |- cQEvalTmS : ety (Arr N (Arr N (Arr N N)))].
Proof. ty_comb cQEvalTmS. Qed.
#[local] Hint Resolve cQEvalTmS_ty : tyc.

Lemma cQEvalTm_ty {Γ} : [|- Γ] -> [Γ |- cQEvalTm : ety (Arr N (Arr N N))].
Proof. ty_comb cQEvalTm. Qed.
#[local] Hint Resolve cQEvalTm_ty : tyc.

Lemma cSeqAlg_ty {Γ} : [|- Γ] -> [Γ |- cSeqAlg : ety (Arr (Arr N N) (Arr N N))].
Proof. ty_comb cSeqAlg. Qed.
#[local] Hint Resolve cSeqAlg_ty : tyc.

Lemma cSeq_ty {Γ} : [|- Γ] -> [Γ |- cSeq : ety (Arr N N)].
Proof. ty_comb cSeq. Qed.
#[local] Hint Resolve cSeq_ty : tyc.

Lemma cDeepF_ty {Γ} : [|- Γ] -> [Γ |- cDeepF : ety (Arr EvTy (Arr N (Arr N (Arr N N))))].
Proof. ty_comb cDeepF. Qed.
#[local] Hint Resolve cDeepF_ty : tyc.

Lemma cDeep_ty {Γ} : [|- Γ] -> [Γ |- cDeep : ety (Arr EvTy (Arr N N))].
Proof. ty_comb cDeep. Qed.
#[local] Hint Resolve cDeep_ty : tyc.

Lemma cCanon_ty {Γ} : [|- Γ] -> [Γ |- cCanon : ety (Arr EvTy (Arr N (Arr N N)))].
Proof. ty_comb cCanon. Qed.
#[local] Hint Resolve cCanon_ty : tyc.

Lemma cReplF_ty {Γ} : [|- Γ] -> [Γ |- cReplF : ety (Arr N (Arr N (Arr N (Arr N N))))].
Proof. ty_comb cReplF. Qed.
#[local] Hint Resolve cReplF_ty : tyc.

Lemma cElim_ty {Γ} : [|- Γ] -> [Γ |- cElim : ety (Arr EvTy (Arr N (Arr N (Arr N (Arr (Arr N N) N)))))].
Proof. ty_comb cElim. Qed.
#[local] Hint Resolve cElim_ty : tyc.

Lemma cHApp_ty {Γ} : [|- Γ] -> [Γ |- cHApp : ety (Arr EvTy (Arr N (Arr N (Arr N N))))].
Proof. ty_comb cHApp. Qed.
#[local] Hint Resolve cHApp_ty : tyc.

Lemma cHNat_ty {Γ} : [|- Γ] -> [Γ |- cHNat : ety (Arr EvTy (Arr N (Arr N (Arr N N))))].
Proof. ty_comb cHNat. Qed.
#[local] Hint Resolve cHNat_ty : tyc.

Lemma cHNone_ty {Γ} : [|- Γ] -> [Γ |- cHNone : ety (Arr N N)].
Proof. ty_comb cHNone. Qed.
#[local] Hint Resolve cHNone_ty : tyc.

Lemma cHProj_ty {Γ} : [|- Γ] -> [Γ |- cHProj : ety (Arr EvTy (Arr N (Arr N (Arr N N))))].
Proof. ty_comb cHProj. Qed.
#[local] Hint Resolve cHProj_ty : tyc.

Lemma cHId_ty {Γ} : [|- Γ] -> [Γ |- cHId : ety (Arr EvTy (Arr N (Arr N (Arr N N))))].
Proof. ty_comb cHId. Qed.
#[local] Hint Resolve cHId_ty : tyc.

Lemma cQuoteB_ty {Γ} : [|- Γ] -> [Γ |- cQuoteB : ety (Arr EvTy (Arr N N))].
Proof. ty_comb cQuoteB. Qed.
#[local] Hint Resolve cQuoteB_ty : tyc.

Lemma cStepCore_ty {Γ} : [|- Γ] -> [Γ |- cStepCore : ety (Arr (Arr N N) (Arr N (Arr N (Arr EvTy N))))].
Proof. ty_comb cStepCore. Qed.
#[local] Hint Resolve cStepCore_ty : tyc.

Lemma cStepB_ty {Γ} : [|- Γ] -> [Γ |- cStepB : ety (Arr EvTy (Arr (Arr N N) (Arr N (Arr N (Arr EvTy N)))))].
Proof. ty_comb cStepB. Qed.
#[local] Hint Resolve cStepB_ty : tyc.

Lemma cFinStep_ty {Γ} : [|- Γ] -> [Γ |- cFinStep : ety (Arr N (Arr N N))].
Proof. ty_comb cFinStep. Qed.
#[local] Hint Resolve cFinStep_ty : tyc.

Lemma cFinRefl_ty {Γ} : [|- Γ] -> [Γ |- cFinRefl : ety (Arr N (Arr N N))].
Proof. ty_comb cFinRefl. Qed.
#[local] Hint Resolve cFinRefl_ty : tyc.

Lemma cBody_ty {Γ} : [|- Γ] -> [Γ |- cBody : ety (Arr EvTy (Arr (Arr N N) (Arr N (Arr N N))))].
Proof.
intros; unfold cBody, body_branches, br_atom, br_canon, br_elim; cbn [lams apps clist cnode F qNat switch List.app]; tyc.
Qed.
#[local] Hint Resolve cBody_ty : tyc.

Lemma cStateS_ty {Γ} : [|- Γ] -> [Γ |- cStateS : ety (Arr N (Arr ST ST))].
Proof. ty_comb cStateS. Qed.
#[local] Hint Resolve cStateS_ty : tyc.

Lemma cState_ty {Γ} : [|- Γ] -> [Γ |- cState : ety (Arr N ST)].
Proof. ty_comb cState. Qed.
#[local] Hint Resolve cState_ty : tyc.

Lemma tRun_ty {Γ} : [|- Γ] -> [Γ |- tRun : ety (Arr N (Arr N N))].
Proof. ty_comb tRun. Qed.
#[local] Hint Resolve tRun_ty : tyc.

Lemma tRunNat_ty {Γ} : [|- Γ] -> [Γ |- tRunNat : ety (Arr N (Arr N (Arr N N)))].
Proof. ty_comb tRunNat. Qed.

Lemma ty_run_model {Γ} : [|- Γ] -> [Γ |- run : arr tNat (arr tNat tPNat)].
Proof.
intros; exact (tRunNat_ty H8).
Qed.

Lemma ty_run : [ nil |- tRun : tProd tNat (tProd tNat tNat) ].
Proof.
exact (tRun_ty wfc_nil).
Qed.

End Wf.
