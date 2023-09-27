(** * LogRel.UntypedReduction: untyped reduction, used to define algorithmic typing.*)
From Coq Require Import CRelationClasses ssrbool.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Notations Context Closed NormalForms Weakening.

(** ** Reductions *)

(** *** One-step reduction. *)

Inductive OneRedAlg {deep : bool} : term -> term -> Type :=
| BRed {A a t} :
    [ tApp (tLambda A t) a ⤳ t[a..] ]
| appSubst {t u a} :
    negb (isLambda t) ->
    [ t ⤳ u ] ->
    [ tApp t a ⤳ tApp u a ]
| natElimSubst {P hz hs n n'} :
    negb (isNatConstructor n) ->
    [ n ⤳ n' ] ->
    [ tNatElim P hz hs n ⤳ tNatElim P hz hs n' ]
| natElimZero {P hz hs} :
    [ tNatElim P hz hs tZero ⤳ hz ]
| natElimSucc {P hz hs n} :
    [ tNatElim P hz hs (tSucc n) ⤳ tApp (tApp hs n) (tNatElim P hz hs n) ]
| emptyElimSubst {P e e'} :
    negb (isEmptyConstructor e) ->
    [e ⤳ e'] ->
    [tEmptyElim P e ⤳ tEmptyElim P e']        
| fstSubst {p p'} :
    negb (isPairConstructor p) ->
    [ p ⤳ p'] ->
    [ tFst p ⤳ tFst p']
| fstPair {A B a b} :
    [ tFst (tPair A B a b) ⤳ a ]
| sndSubst {p p'} :
    negb (isPairConstructor p) ->
    [ p ⤳ p'] ->
    [ tSnd p ⤳ tSnd p']
| sndPair {A B a b} :
    [ tSnd (tPair A B a b) ⤳ b ]
| idElimRefl {A x P hr y A' z} :
  [ tIdElim A x P hr y (tRefl A' z) ⤳ hr ]
| idElimSubst {A x P hr y e e'} :
  negb (isIdConstructor e) ->
  [e ⤳ e'] ->
  [ tIdElim A x P hr y e ⤳ tIdElim A x P hr y e' ]
| termEvalAlg {t} :
  dnf t ->
  closed0 t ->
  [ tQuote t ⤳ tZero ]

(* Hereditary normal forms *)

| prodDom {A A' B} : deep ->
  [ A ⤳ A' ] -> [ tProd A B ⤳ tProd A' B ]
| prodCod {A B B'} : deep ->
  dnf A -> [ B ⤳ B' ] -> [ tProd A B ⤳ tProd A B' ]
| lamDom {A A' t} : deep ->
  [ A ⤳ A' ] -> [ tLambda A t ⤳ tLambda A' t ]
| lamBody {A t t'} : deep ->
  dnf A -> [ t ⤳ t' ] -> [ tLambda A t ⤳ tLambda A t' ]
| appSubstNe {t u u'} : deep ->
  dne t -> [ u ⤳ u' ] -> [ tApp t u ⤳ tApp t u' ]
| succArg {t t'} : deep ->
  [ t ⤳ t' ] -> [ tSucc t ⤳ tSucc t' ]
| natElimPred {P P' hz hs n} : deep ->
  dne n -> [ P ⤳ P' ] -> [ tNatElim P hz hs n ⤳ tNatElim P' hz hs n ]
| natElimBranchZero {P hz hz' hs n} : deep ->
  dne n -> dnf P -> [ hz ⤳ hz' ] -> [ tNatElim P hz hs n ⤳ tNatElim P hz' hs n ]
| natElimBranchSucc {P hz hs hs' n} : deep ->
  dne n -> dnf P -> dnf hz -> [ hs ⤳ hs' ] -> [ tNatElim P hz hs n ⤳ tNatElim P hz hs' n ]
| emptyElimPred {P P' n} : deep ->
  dne n -> [ P ⤳ P' ] -> [ tEmptyElim P n ⤳ tEmptyElim P' n ]
| sigDom {A A' B} : deep ->
  [ A ⤳ A' ] -> [ tSig A B ⤳ tSig A' B ]
| sigCod {A B B'} : deep ->
  dnf A ->
  [ B ⤳ B' ] -> [ tSig A B ⤳ tSig A B' ]
| pairDom {A A' B a b} : deep ->
  [ A ⤳ A' ] -> [ tPair A B a b ⤳ tPair A' B a b ]
| pairCod {A B B' a b} : deep ->
  dnf A ->
  [ B ⤳ B' ] -> [ tPair A B a b ⤳ tPair A B' a b ]
| pairFst {A B a a' b} : deep ->
  dnf A -> dnf B ->
  [ a ⤳ a' ] -> [ tPair A B a b ⤳ tPair A B a' b ]
| pairSnd {A B a b b'} : deep ->
  dnf A -> dnf B -> dnf a ->
  [ b ⤳ b' ] -> [ tPair A B a b ⤳ tPair A B a b' ]
| idDom {A A' t u} : deep ->
  [ A ⤳ A' ] -> [ tId A t u ⤳ tId A' t u ]
| idLHS {A t t' u} : deep ->
  dnf A -> [ t ⤳ t' ] -> [ tId A t u ⤳ tId A t' u ]
| idRHS {A t u u'} : deep ->
  dnf A -> dnf t -> [ u ⤳ u' ] -> [ tId A t u ⤳ tId A t u' ]
| reflDom {A A' t} : deep ->
  [ A ⤳ A' ] -> [ tRefl A t ⤳ tRefl A' t ]
| reflArg {A t t'} : deep ->
  dnf A -> [ t ⤳ t' ] -> [ tRefl A t ⤳ tRefl A t' ]
| idElimDom {A A' x P hr y e} : deep ->
  dne e ->
  [ A ⤳ A' ] -> [ tIdElim A x P hr y e ⤳ tIdElim A' x P hr y e ]
| idElimLHS {A x x' P hr y e} : deep ->
  dne e -> dnf A ->
  [ x ⤳ x' ] -> [ tIdElim A x P hr y e ⤳ tIdElim A x' P hr y e ]
| idElimPred {A x P P' hr y e} : deep ->
  dne e -> dnf A -> dnf x ->
  [ P ⤳ P' ] -> [ tIdElim A x P hr y e ⤳ tIdElim A x P' hr y e ]
| idElimBranchRefl {A x P hr hr' y e} : deep ->
  dne e -> dnf A -> dnf x -> dnf P ->
  [ hr ⤳ hr' ] -> [ tIdElim A x P hr y e ⤳ tIdElim A x P hr' y e ]
| idElimRHS {A x P hr y y' e} : deep ->
  dne e -> dnf A -> dnf x -> dnf P -> dnf hr ->
  [ y ⤳ y' ] -> [ tIdElim A x P hr y e ⤳ tIdElim A x P hr y' e ]
| quoteSubst {t t'} :
  @OneRedAlg true t t' ->
  [ tQuote t ⤳ tQuote t' ]

where "[ t ⤳ t' ]" := (OneRedAlg t t') : typing_scope.

Notation "[ t ⤳ t' ]" := (OneRedAlg (deep := false) t t') : typing_scope.
Notation "[ t ⇶ t' ]" := (OneRedAlg (deep := true) t t') : typing_scope.

(* Keep in sync with OneRedTermDecl! *)

(** *** Multi-step reduction *)

Inductive RedClosureAlg {deep : bool} : term -> term -> Type :=
  | redIdAlg {t} :
    [ t ⤳* t ]
  | redSuccAlg {t t' u} :
    @OneRedAlg deep t t' ->
    [ t' ⤳* u ] ->
    [ t ⤳* u ]
  where "[ t ⤳* t' ]" := (RedClosureAlg t t') : typing_scope.

Notation "[ t ⤳* t' ]" := (RedClosureAlg (deep := false) t t') : typing_scope.
Notation "[ t ⇶* t' ]" := (RedClosureAlg (deep := true) t t') : typing_scope.

#[export] Instance RedAlgTrans {deep} : PreOrder (@RedClosureAlg deep).
  Proof.
    split.
    - now econstructor.
    - intros * ; induction 1.
      1: easy.
      intros.
      now econstructor.
  Qed.

(** ** Properties *)

(** Inclusions *)

Lemma dred_ored : forall t t', [ t ⤳ t' ] -> [ t ⇶ t' ].
Proof.
intros t t'; induction 1; now econstructor.
Qed.

Lemma dred_red : forall t t', [ t ⤳* t' ] -> [ t ⇶* t' ].
Proof.
induction 1; econstructor; tea.
now apply dred_ored.
Qed.

(** *** Weak-head normal forms do not reduce *)

Lemma dnf_dne_nogred :
  (forall t, dnf t -> forall deep u, OneRedAlg (deep := deep) t u -> False) × (forall n, dne n -> forall deep u, OneRedAlg (deep := deep) n u -> False).
Proof.
apply dnf_dne_rect; intros.
all: match goal with
| H : OneRedAlg _ _ |- _ => inversion H; subst
end; try now intuition.
all: match goal with H : dne _ |- _ => solve [inversion H] end.
Qed.

Lemma dnf_dne_nored :
  (forall t, dnf t -> forall u, [t ⇶ u] -> False) × (forall n, dne n -> forall u, [n ⇶ u] -> False).
Proof.
apply dnf_dne_rect; intros.
all: match goal with
| H : [_ ⇶ _] |- _ => inversion H; subst
end; try now intuition.
all: match goal with H : dne _ |- _ => solve [inversion H] end.
Qed.

Lemma dnf_nored : forall t u, dnf t -> [t ⇶ u] -> False.
Proof.
intros t u H Hr.
destruct dnf_dne_nored as [f _]; now eapply f.
Qed.

Lemma dne_nored : forall t u, dne t -> [t ⇶ u] -> False.
Proof.
intros t u H Hr.
destruct dnf_dne_nored as [_ f]; now eapply f.
Qed.

Ltac inv_whne :=
  match goal with [ H : whne _ |- _ ] => inversion H end.

Lemma whne_nored n u :
  whne n -> [n ⤳ u] -> False.
Proof.
  remember false as deep eqn: Hd.
  intros ne red.
  revert Hd; induction red; intros Hd.
  all: inversion ne ; subst ; clear ne; auto.
  all: try inv_whne.
  - now eelim dnf_nored.
Qed.

Lemma whnf_nored n u :
  whnf n -> [n ⤳ u] -> False.
Proof.
  remember false as deep eqn: Hd.
  intros nf red.
  revert Hd; induction red; intros Hd.
  all: inversion nf; subst; auto.
  - inversion H ; subst.
    now eapply neLambda.
  - inversion H ; subst.
    eapply IHred; [|trivial].
    now constructor.
  - inversion H ; subst.
    eapply IHred; [|trivial].
    now constructor.
  - inversion H ; subst.
    inv_whne.
  - inversion H ; subst.
    inv_whne.
  - inversion H; subst.
    eapply IHred; [|trivial].
    now constructor.
  - inversion H; subst.
    eapply IHred; [|trivial].
    now constructor.
  - inversion H; subst.
    inversion H1; subst.
  - inversion H; subst.
    eapply IHred; [|trivial].
    now constructor.
  - inversion H; subst.
    inversion H1; subst.
  - inversion H; subst.
    inversion H1.
  - inversion H; subst.
    eapply IHred; [|trivial].
    now constructor.
  - inversion H ; subst.
    contradiction.
  - inversion H; subst.
    now eelim dnf_nored.
Qed.

(** *** Determinism of reduction *)

Lemma gred_det {deep t u v} :
  OneRedAlg (deep := deep) t u ->
  OneRedAlg (deep := deep) t v ->
  u = v.
Proof.
intros Hu Hv; revert v Hv; induction Hu; intros v Hv; inversion Hv; subst; simpl in *.
all: match goal with
| _ => reflexivity
| H : is_true false |- _ => elim notF; exact H
| H : dne _ |- _ => now inversion H
| H : dne _ |- _ => now eapply dnf_dne_nogred in H
| H : dnf _ |- _ => now eapply dnf_dne_nogred in H
| H : [ ?t ⇶ ?u ] |- _ => now inversion H
| _ => now f_equal
| _ => idtac
end.
Qed.

Lemma dred_det {t u v} :
  [t ⇶ u] -> [t ⇶ v] ->
  u = v.
Proof.
apply gred_det.
Qed.

Lemma ored_det {t u v} :
  [t ⤳ u] -> [t ⤳ v] ->
  u = v.
Proof.
intros; eapply dred_det; now eapply dred_ored.
Qed.

Lemma red_whne t u : [t ⤳* u] -> whne t -> t = u.
Proof.
  intros [] ?.
  1: reflexivity.
  exfalso.
  eauto using whne_nored.
Qed.

Lemma dred_whne : forall t u, [t ⇶ u] -> whne t -> whne u.
Proof.
intros t u Hr Ht; revert u Hr.
induction Ht; intros u Hr; inversion Hr; subst; first [constructor; now eauto|now inv_whne|idtac].
+ contradiction.
+ now eelim dnf_nored.
Qed.

Lemma dredalg_whne : forall t u, [t ⇶* u] -> whne t -> whne u.
Proof.
intros * H Hne.
induction H; [tea|].
now eauto using dred_whne.
Qed.

Lemma red_whnf t u : [t ⤳* u] -> whnf t -> t = u.
Proof.
  intros [] ?.
  1: reflexivity.
  exfalso.
  eauto using whnf_nored.
Qed.

Lemma dred_dnf t u : [t ⇶* u] -> dnf t -> t = u.
Proof.
  intros [] ?.
  1: reflexivity.
  exfalso.
  eauto using dnf_nored.
Qed.

Lemma whred_red_det t u u' :
  whnf u ->
  [t ⤳* u] -> [t ⤳* u'] ->
  [u' ⤳* u].
Proof.
  intros whnf red red'.
  induction red in whnf, u', red' |- *.
  - eapply red_whnf in red' as -> ; tea.
    now econstructor.
  - destruct red' as [? | ? ? ? o'].
    + now econstructor.
    + unshelve epose proof (ored_det o o') as <-.
      now eapply IHred.
Qed.

Lemma dred_red_det t u u' :
  dnf u ->
  [t ⇶* u] -> [t ⇶* u'] ->
  [u' ⇶* u].
Proof.
  intros whnf red red'.
  induction red in whnf, u', red' |- *.
  - inversion red'; subst; [reflexivity|].
    now eelim dnf_nored.
  - destruct red' as [|? ? ? o'].
    + now econstructor.
    + eapply IHred; [tea|].
      now unshelve epose proof (dred_det o o') as <-.
Qed.

Corollary whred_det t u u' :
  whnf u -> whnf u' ->
  [t ⤳* u] -> [t ⤳* u'] ->
  u = u'.
Proof.
  intros.
  eapply red_whnf ; tea.
  now eapply whred_red_det.
Qed.

Corollary dredalg_det t u u' :
  dnf u -> dnf u' ->
  [t ⇶* u] -> [t ⇶* u'] ->
  u = u'.
Proof.
  intros.
  eapply dred_dnf ; tea.
  now eapply dred_red_det.
Qed.

(** Helpers *)

Lemma oredalg_appSubst t t' u :
  [ t ⤳ t' ] -> [ tApp t u ⤳ tApp t' u ].
Proof.
intros; constructor; [|eassumption].
assert (Hw : ~ whnf t) by (intro; now eelim whnf_nored).
destruct t; first [now (elim Hw; constructor)|constructor].
Qed.

Lemma oredalg_natElimSubst {P hz hs n n'} :
  [ n ⤳ n' ] ->
  [ tNatElim P hz hs n ⤳ tNatElim P hz hs n' ].
Proof.
intros; constructor; [|eassumption].
assert (Hw : ~ whnf n) by (intro; now eelim whnf_nored).
destruct n; first [now (elim Hw; constructor)|constructor].
Qed.

(** *** Stability by weakening *)

Lemma gredalg_wk {deep} (ρ : nat -> nat) (t u : term) : OneRedAlg (deep := deep) t u ->  OneRedAlg (deep := deep)  t⟨ρ⟩ u⟨ρ⟩.
Proof.
intros Hred; induction Hred in ρ |- *; cbn.
all: try now (econstructor; intuition).
all: try now (econstructor; try apply dnf_ren; try apply dne_ren; intuition).
+ replace (t[a..]⟨ρ⟩) with (t⟨upRen_term_term ρ⟩)[a⟨ρ⟩..] by now bsimpl.
  now constructor.
+ constructor; [|now intuition].
  destruct t; first [constructor|now elim notF].
+ constructor; [|now intuition].
  destruct n; first [constructor|now elim notF].
+ constructor; [|now intuition].
  destruct p; first [constructor|now elim notF].
+ constructor; [|now intuition].
  destruct p; first [constructor|now elim notF].
+ constructor; [|now intuition].
  destruct e; first [constructor|now elim notF].
+ constructor; [now apply dnf_ren|now apply closed0_ren].
Qed.

Lemma oredalg_wk (ρ : nat -> nat) (t u : term) :
[t ⤳ u] ->
[t⟨ρ⟩ ⤳ u⟨ρ⟩].
Proof.
apply gredalg_wk.
Qed.

Lemma gcredalg_wk {deep} (ρ : nat -> nat) (t u : term) : RedClosureAlg (deep := deep) t u -> RedClosureAlg (deep := deep)  t⟨ρ⟩ u⟨ρ⟩.
Proof.
induction 1; econstructor; eauto using gredalg_wk.
Qed.

Lemma credalg_wk (ρ : nat -> nat) (t u : term) :
[t ⤳* u] ->
[t⟨ρ⟩ ⤳* u⟨ρ⟩].
Proof.
apply gcredalg_wk.
Qed.

(** Invertibility *)

Lemma redalg_app_inv : forall n n' t t', whne n -> [tApp n t ⇶* tApp n' t'] -> [n ⇶* n'].
Proof.
intros n n' t t' Hn Hr.
remember (tApp n t) as a eqn:Ha.
remember (tApp n' t') as a' eqn:Ha'.
revert n n' t t' Ha Ha' Hn.
induction Hr; intros; subst.
+ injection Ha'; intros; subst; reflexivity.
+ inversion o; subst; [inversion Hn| |].
  - econstructor; [tea|eapply IHHr]; try reflexivity.
    eapply dredalg_whne; tea.
    econstructor; [tea|reflexivity].
  - eapply IHHr; tea; reflexivity.
Qed.

Lemma redalg_fst_inv : forall n n', whne n -> [tFst n ⇶* tFst n'] -> [n ⇶* n'].
Proof.
intros n n' Hn Hr.
remember (tFst n) as a eqn:Ha.
remember (tFst n') as a' eqn:Ha'.
revert n n' Ha Ha' Hn.
induction Hr; intros; subst.
+ injection Ha'; intros; subst; reflexivity.
+ inversion o; subst.
  - econstructor; [tea|eapply IHHr]; try reflexivity.
    eapply dredalg_whne; tea.
    econstructor; [tea|reflexivity].
  - inv_whne.
Qed.

Lemma dred_ren_inv : forall t u ρ, ren_inj ρ -> [t⟨ρ⟩ ⇶ u⟨ρ⟩] -> [t ⇶ u].
Proof.
intros t u ρ Hρ Hr.
remember t⟨ρ⟩ as t' eqn:Ht.
remember u⟨ρ⟩ as u' eqn:Hu.
revert t u ρ Ht Hu Hρ; induction Hr; intros t₀ u₀ ρ Ht Hu Hρ.
all: repeat match goal with H : _ = ?t⟨?ρ⟩ |- _ =>
  destruct t; cbn in *; try discriminate; [idtac];
  try injection H; intros; subst
end.
all: repeat (match goal with H : ?t⟨?ρ⟩ = ?u⟨?ρ⟩ |- _ =>
  apply ren_inj_inv in H; [|eauto using upRen_term_term_inj]; []; subst; clear H
end).
all: try now (constructor; eauto using dne_ren_rev, dnf_ren_rev, upRen_term_term_inj).
+ assert (Hrw : forall t u, t⟨upRen_term_term ρ⟩[(u⟨ρ⟩)..] = (t[u..])⟨ρ⟩) by now asimpl.
  rewrite Hrw in Hu; apply ren_inj_inv in Hu; tea.
  subst; constructor.
+ assert (forall t, isLambda t -> isLambda t⟨ρ⟩) by now intros [].
  constructor; eauto using contraNN.
+ assert (forall t, isNatConstructor t -> isNatConstructor t⟨ρ⟩) by now intros [].
  constructor; eauto using contraNN.
+ assert (forall t, isPairConstructor t -> isPairConstructor t⟨ρ⟩) by now intros [].
  constructor; eauto using contraNN.
+ assert (forall t, isPairConstructor t -> isPairConstructor t⟨ρ⟩) by now intros [].
  constructor; eauto using contraNN.
+ assert (forall t, isIdConstructor t -> isIdConstructor t⟨ρ⟩).
  { intros []; cbn in *; eauto. }
  constructor; eauto using contraNN.
+ constructor; [now eapply dnf_ren_rev|].
  now eapply closed0_ren_rev.
Qed.

Ltac unren t := lazymatch t with
| ?t⟨?ρ⟩ => open_constr:(_ : term)
| tProd ?t ?u =>
  let t := unren t in
  let u := unren u in
  constr:(tProd t u)
| tSig ?t ?u =>
  let t := unren t in
  let u := unren u in
  constr:(tSig t u)
| tApp ?t ?u =>
  let t := unren t in
  let u := unren u in
  constr:(tApp t u)
| tLambda ?t ?u =>
  let t := unren t in
  let u := unren u in
  constr:(tLambda t u)
| tFst ?t =>
  let t := unren t in
  constr:(tFst t)
| tSnd ?t =>
  let t := unren t in
  constr:(tSnd t)
| tSucc ?t =>
  let t := unren t in
  constr:(tSucc t)
| tNatElim ?P ?hz ?hs ?t =>
  let P := unren P in
  let hz := unren hz in
  let hs := unren hs in
  let t := unren t in
  constr:(tNatElim P hz hs t)
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
| tEmptyElim ?P ?t =>
  let P := unren P in
  let t := unren t in
  constr:(tEmptyElim P t)
| tPair ?A ?B ?a ?b =>
  let A := unren A in
  let B := unren B in
  let a := unren a in
  let b := unren b in
  constr:(tPair A B a b)
| _ => t
end.

Lemma dred_ren_adj : forall t u ρ, [t⟨ρ⟩ ⇶ u] -> ∑ u', u = u'⟨ρ⟩.
Proof.
intros t u ρ Hr.
remember t⟨ρ⟩ as t' eqn:Ht.
revert t ρ Ht; induction Hr; intros t₀ ρ Ht.
all: repeat match goal with H : _ = ?t⟨?ρ⟩ |- _ =>
  destruct t; cbn in *; try discriminate; [idtac];
  try injection H; intros; subst
end.
all: repeat match goal with H : forall (t : term) (ρ : nat -> nat), _ |- _ =>
  specialize (H _ _ eq_refl); destruct H; subst
end.
all: let t := lazymatch goal with |- ∑ n, ?t = _ => t end in
     try (let t := unren t in now eexists t).
+ assert (Hrw : forall t u, t⟨upRen_term_term ρ⟩[(u⟨ρ⟩)..] = (t[u..])⟨ρ⟩) by now asimpl.
  rewrite Hrw; now eexists.
+ eexists (tQuote _); reflexivity.
Qed.

Lemma redalg_ren_inv : forall t u ρ, ren_inj ρ -> [t⟨ρ⟩ ⇶* u⟨ρ⟩] -> [t ⇶* u].
Proof.
intros t u ρ Hρ Hr.
remember t⟨ρ⟩ as t' eqn:Ht.
remember u⟨ρ⟩ as u' eqn:Hu.
revert t u ρ Ht Hu Hρ; induction Hr; intros; subst.
+ intros; subst.
  apply ren_inj_inv in Hu; now subst.
+ unshelve eassert (H := dred_ren_adj _ _ _ _); [..|tea|].
  destruct H; subst.
  econstructor; [|eapply IHHr]; eauto.
  now eapply dred_ren_inv.
Qed.

(** Derived rules *)

Lemma redalg_app {t t' u} : [t ⤳* t'] -> [tApp t u ⤳* tApp t' u].
Proof.
induction 1.
+ reflexivity.
+ econstructor; [|eassumption].
  econstructor; [|eassumption].
  destruct t; try constructor.
  all: eelim whnf_nored; [eapply whnf_tLambda|eassumption].
Qed.

Lemma redalg_natElim {P hs hz t t'} : [t ⤳* t'] -> [tNatElim P hs hz t ⤳* tNatElim P hs hz t'].
Proof.
induction 1.
+ reflexivity.
+ econstructor; [|eassumption].
  econstructor; [|eassumption].
  destruct t; try constructor.
  - eelim whnf_nored; [eapply whnf_tZero|eassumption].
  - eelim whnf_nored; [eapply whnf_tSucc|eassumption].
Qed.

Lemma redalg_natEmpty {P t t'} : [t ⤳* t'] -> [tEmptyElim P t ⤳* tEmptyElim P t'].
Proof.
induction 1.
+ reflexivity.
+ econstructor; [|eassumption].
  now econstructor.
Qed.

Lemma redalg_fst {t t'} : [t ⤳* t'] -> [tFst t ⤳* tFst t'].
Proof.
  induction 1; [reflexivity|].
  econstructor; tea.
  constructor; tea.
  destruct t; try constructor.
  eelim whnf_nored; [eapply whnf_tPair|eassumption].
Qed.

Lemma redalg_snd {t t'} : [t ⤳* t'] -> [tSnd t ⤳* tSnd t'].
Proof.
  induction 1; [reflexivity|].
  econstructor; tea.
  constructor; tea.
  destruct t; try constructor.
  eelim whnf_nored; [eapply whnf_tPair|eassumption].
Qed.

Lemma redalg_idElim {A x P hr y t t'} : [t ⤳* t'] -> [tIdElim A x P hr y t ⤳* tIdElim A x P hr y t'].
Proof.
  induction 1; [reflexivity|].
  econstructor; tea; constructor; [|tea].
  destruct t; try constructor.
  eelim whnf_nored; [eapply whnf_tRefl|eassumption].
Qed.

Lemma redalg_quote {t t'} : [t ⇶* t'] -> [tQuote t ⤳* tQuote t'].
Proof.
induction 1; [reflexivity|].
econstructor; [|tea].
now constructor.
Qed.

Lemma redalg_one_step {t t'} : [t ⤳ t'] -> [t ⤳* t'].
Proof. intros; econstructor;[tea|reflexivity]. Qed.

Lemma dredalg_prod : forall A A₀ B B₀,
  [A ⇶* A₀] -> dnf A₀ ->
  [B ⇶* B₀] -> [tProd A B ⇶* tProd A₀ B₀].
Proof.
intros A A₀ B B₀ HRA HAnf HRB.
transitivity (tProd A₀ B).
- clear - HRA HAnf; induction HRA.
  * constructor.
  * econstructor; [|now eauto].
    now constructor.
- clear - HAnf HRB; induction HRB.
  * constructor.
  * econstructor; [|now eauto].
    now constructor.
Qed.

Lemma dredalg_lambda : forall A A₀ t t₀,
  [A ⇶* A₀] -> dnf A₀ ->
  [t ⇶* t₀] -> [tLambda A t ⇶* tLambda A₀ t₀].
Proof.
intros A A₀ t t₀ HRA HAnf HRt.
transitivity (tLambda A₀ t).
- clear - HRA HAnf; induction HRA.
  * constructor.
  * econstructor; [|now eauto].
    now constructor.
- clear - HAnf HRt; induction HRt.
  * constructor.
  * econstructor; [|now eauto].
    now constructor.
Qed.

Lemma dredalg_app : forall t t₀ u u₀,
  whne t ->
  [t ⇶* t₀] -> dne t₀ -> [u ⇶* u₀] -> [tApp t u ⇶* tApp t₀ u₀].
Proof.
intros t t₀ u u₀ Ht HRt Htnf Hru.
transitivity (tApp t₀ u).
- clear - HRt Ht Htnf; induction HRt.
  + constructor.
  + assert (whne t') by now eapply dred_whne.
    etransitivity; [|now apply IHHRt].
    econstructor; [|reflexivity].
    constructor; [|tea].
    inversion Ht; subst; eauto.
- clear - Htnf Hru; induction Hru.
  + constructor.
  + econstructor; [|tea].
    constructor; eauto.
Qed.

Lemma dredalg_sig : forall A A₀ B B₀,
  [A ⇶* A₀] -> dnf A₀ ->
  [B ⇶* B₀] -> [tSig A B ⇶* tSig A₀ B₀].
Proof.
intros A A₀ B B₀ HRA HAnf HRB.
transitivity (tSig A₀ B).
- clear - HRA HAnf; induction HRA.
  * constructor.
  * econstructor; [|now eauto].
    now constructor.
- clear - HAnf HRB; induction HRB.
  * constructor.
  * econstructor; [|now eauto].
    now constructor.
Qed.

Lemma dredalg_pair : forall A A₀ B B₀ a a₀ b b₀,
  [A ⇶* A₀] -> dnf A₀ -> [B ⇶* B₀] -> dnf B₀ ->
  [a ⇶* a₀] -> dnf a₀ -> [b ⇶* b₀] -> dnf b₀ ->
  [tPair A B a b ⇶* tPair A₀ B₀ a₀ b₀].
Proof.
intros A A₀ B B₀ a a₀ b b₀ HRA HA HRB HB HRa Ha HRb Hb.
transitivity (tPair A₀ B a b);
  [|transitivity (tPair A₀ B₀ a b);
    [|transitivity (tPair A₀ B₀ a₀ b)]].
- clear - HRA HA; induction HRA.
  * constructor.
  * econstructor; [|now eauto].
    now constructor.
- clear - HA HRB; induction HRB.
  * constructor.
  * econstructor; [|now eauto].
    now constructor.
- clear - HA HB HRa; induction HRa.
  * constructor.
  * econstructor; [|now eauto].
    now constructor.
- clear - HA HB Ha HRb; induction HRb.
  * constructor.
  * econstructor; [|now eauto].
    now constructor.
Qed.

Lemma dredalg_fst : forall t t₀,
  whne t ->
  [t ⇶* t₀] -> [tFst t ⇶* tFst t₀].
Proof.
intros t t₀ Ht HRt.
induction HRt.
- constructor.
- assert (whne t') by now eapply dred_whne.
  econstructor; [|now eauto].
  constructor; [|tea].
  inversion Ht; subst; eauto.
Qed.

Lemma dredalg_snd : forall t t₀,
  whne t ->
  [t ⇶* t₀] -> [tSnd t ⇶* tSnd t₀].
Proof.
intros t t₀ Ht HRt.
induction HRt.
- constructor.
- assert (whne t') by now eapply dred_whne.
  econstructor; [|now eauto].
  constructor; [|tea].
  inversion Ht; subst; eauto.
Qed.

Lemma dredalg_succ : forall n n₀, [n ⇶* n₀] -> [tSucc n ⇶* tSucc n₀].
Proof.
intros n n₀ HRn; induction HRn.
- reflexivity.
- econstructor; [|tea].
  now constructor.
Qed.

Lemma dredalg_natElim : forall P P₀ hz hz₀ hs hs₀ t t₀,
  whne t -> [t ⇶* t₀] -> dne t₀ ->
  [P ⇶* P₀] -> dnf P₀ -> [hz ⇶* hz₀] -> dnf hz₀ -> [hs ⇶* hs₀] -> dnf hs₀ ->
  [tNatElim P hz hs t ⇶* tNatElim P₀ hz₀ hs₀ t₀].
Proof.
intros P P₀ hz hz₀ hs hs₀ t t₀ Ht HRt Hne HRP HP HRhz Hhz HRhs Hhs.
transitivity (tNatElim P hz hs t₀);
  [|transitivity (tNatElim P₀ hz hs t₀);
    [|transitivity (tNatElim P₀ hz₀ hs t₀)]].
- clear - HRt Ht Hne; induction HRt.
  + constructor.
  + assert (whne t') by now eapply dred_whne.
    econstructor; [|now eauto].
    constructor; [|tea].
    inversion Ht; subst; eauto.
- clear - HRP HP Hne; induction HRP.
  + constructor.
  + econstructor; [|now eauto].
    constructor; eauto.
- clear - HRhz Hne HP; induction HRhz.
  + constructor.
  + econstructor; [|now eauto].
    constructor; eauto.
- clear - HRhs Hne HP Hhz; induction HRhs.
  + constructor.
  + econstructor; [|now eauto].
    constructor; eauto.
Qed.

Lemma dredalg_emptyElim : forall P P₀ t t₀,
  whne t -> [t ⇶* t₀] -> dne t₀ ->
  [P ⇶* P₀] -> dnf P₀ ->
  [tEmptyElim P t ⇶* tEmptyElim P₀ t₀].
Proof.
intros P P₀ t t₀ Ht HRt Hne HRP HP.
transitivity (tEmptyElim P t₀).
- clear - HRt Ht Hne; induction HRt.
  + constructor.
  + assert (whne t') by now eapply dred_whne.
    econstructor; [|now eauto].
    constructor; [|tea].
    inversion Ht; subst; eauto.
- clear - HRP HP Hne; induction HRP.
  + constructor.
  + econstructor; [|now eauto].
    constructor; eauto.
Qed.

Lemma dredalg_id : forall A A₀ t t₀ u u₀,
  [A ⇶* A₀] -> dnf A₀ -> [t ⇶* t₀] -> dnf t₀ -> [u ⇶* u₀] -> dnf u₀ ->
  [tId A t u ⇶* tId A₀ t₀ u₀].
Proof.
intros A A₀ t t₀ u u₀ HRA HAnf HRt Htnf HRu Hunf.
transitivity (tId A₀ t u); [|transitivity (tId A₀ t₀ u)]; [| |].
- clear - HRA HAnf; induction HRA.
  * constructor.
  * econstructor; [|now eauto].
    now constructor.
- induction HRt.
  * constructor.
  * econstructor; [|now eauto].
    now constructor.
- induction HRu.
  * constructor.
  * econstructor; [|now eauto].
    now constructor.
Qed.

Lemma dredalg_refl : forall A A₀ x x₀,
  [A ⇶* A₀] -> dnf A₀ -> [x ⇶* x₀] ->
  [tRefl A x ⇶* tRefl A₀ x₀].
Proof.
intros A A₀ x x₀ HRA HAnf HRx.
transitivity (tRefl A₀ x).
- clear - HRA HAnf; induction HRA.
  * constructor.
  * econstructor; [|now eauto].
    now constructor.
- clear - HAnf HRx; induction HRx.
  * constructor.
  * econstructor; [|now eauto].
    now constructor.
Qed.

Lemma dredalg_idElim : forall A A₀ x x₀ P P₀ hr hr₀ y y₀ t t₀,
  whne t -> [t ⇶* t₀] -> dne t₀ ->
  [A ⇶* A₀] -> dnf A₀ -> [x ⇶* x₀] -> dnf x₀ ->
  [P ⇶* P₀] -> dnf P₀ -> [hr ⇶* hr₀] -> dnf hr₀ -> [y ⇶* y₀] -> dnf y₀ ->
  [tIdElim A x P hr y t ⇶* tIdElim A₀ x₀ P₀ hr₀ y₀ t₀].
Proof.
intros A A₀ x x₀ P P₀ hr hr₀ y y₀ t t₀ Ht HRt Hne HRA HA HRx Hx HRP HP HRhr Hhr HRy Hy.
transitivity (tIdElim A x P hr y t₀);
  [|transitivity (tIdElim A₀ x P hr y t₀);
    [|transitivity (tIdElim A₀ x₀ P hr y t₀);
      [|transitivity (tIdElim A₀ x₀ P₀ hr y t₀);
        [|transitivity (tIdElim A₀ x₀ P₀ hr₀ y t₀)]]]].
- clear - HRt Ht Hne; induction HRt.
  + constructor.
  + assert (whne t') by now eapply dred_whne.
    econstructor; [|now eauto].
    constructor; [|tea].
    inversion Ht; subst; eauto.
- clear - HRA HA Hne; induction HRA.
  + constructor.
  + econstructor; [|now eauto].
    constructor; eauto.
- clear - HRx Hne HA; induction HRx.
  + constructor.
  + econstructor; [|now eauto].
    constructor; eauto.
- clear - HRP Hne HA Hx; induction HRP.
  + constructor.
  + econstructor; [|now eauto].
    constructor; eauto.
- clear - HRhr Hne HA Hx HP; induction HRhr.
  + constructor.
  + econstructor; [|now eauto].
    constructor; eauto.
- clear - HRy Hne HA Hx HP Hhr; induction HRy.
  + constructor.
  + econstructor; [|now eauto].
    constructor; eauto.
Qed.

(** Stability of closedness by deep reduction *)

Lemma dred_closedn : forall t u n, [t ⇶ u] -> closedn n t -> closedn n u.
Proof.
unfold closedn.
intros t u n Hr; revert n; induction Hr; intros k Hc; cbn in *.
all: repeat match goal with H : _ |- _ => apply andb_prop in H; destruct H end.
all: repeat (apply andb_true_intro; split); f_equal; try now intuition.
all: try now apply IHHr.
now apply closedn_beta.
Qed.

Lemma dredalg_closedn : forall t u n, [t ⇶* u] -> closedn n t -> closedn n u.
Proof.
intros t u n Hr Hc; induction Hr; eauto using dred_closedn.
Qed.

Lemma dredalg_closed0 : forall t u, [t ⇶* u] -> closed0 t -> closed0 u.
Proof.
intros; now eapply dredalg_closedn.
Qed.
