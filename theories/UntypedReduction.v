(** * LogRel.UntypedReduction: untyped reduction, used to define algorithmic typing.*)
From Coq Require Import CRelationClasses ssrbool.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Computation Notations Context Closed NormalForms NormalEq Weakening.

(** ** Reductions *)

(** Step-indexed normalization function *)

Section StepIndex.

Definition bindopt {A B} (x : option A) (f : A -> option B) :=
match x with
| None => None
| Some x => f x
end.

#[local]
Notation "'let*' x ':=' t 'in' u" := (bindopt t (fun x => u)) (at level 50, x binder).

Definition eval_body (eval : bool -> term -> option term) (deep : bool) (t : term) (k : nat) : option term :=
  match t with
  | tRel _ | tSort _ | tNat | tEmpty | tZero => Some t
  | tApp t u =>
    let* t := eval false t in
    if isLambda t then match t with
    | tLambda _ t => eval deep t[u..]
    | _ => None
    end
    else if is_whne t then
      if deep then
        let* t := eval true t in
        let* u := eval true u in
        Some (tApp t u)
      else Some (tApp t u)
    else None
  | tNatElim P hz hs t =>
    let* t := eval false t in
    if isNatConstructor t then match t with
    | tZero => eval deep hz
    | tSucc n => eval deep (tApp (tApp hs n) (tNatElim P hz hs n))
    | _ => None
    end else if is_whne t then
      if deep then
        let* t := eval true t in
        let* P := eval true P in
        let* hz := eval true hz in
        let* hs := eval true hs in
        Some (tNatElim P hz hs t)
      else Some (tNatElim P hz hs t)
    else None
  | tEmptyElim P t =>
    let* t := eval false t in
    if is_whne t then
      if deep then
        let* t := eval true t in
        let* P := eval true P in
        Some (tEmptyElim P t)
      else Some (tEmptyElim P t)
    else None
  | tIdElim A x P hr y t =>
    let* t := eval false t in
    if isIdConstructor t then match t with
    | tRefl _ t => eval deep hr
    | _ => None
    end else if is_whne t then
      if deep then
        let* t := eval true t in
        let* A := eval true A in
        let* x := eval true x in
        let* P := eval true P in
        let* hr := eval true hr in
        let* y := eval true y in
        Some (tIdElim A x P hr y t)
      else Some (tIdElim A x P hr y t)
    else None
  | tFst t =>
    let* t := eval false t in
    if isPairConstructor t then match t with
    | tPair _ _ a _ => eval deep a
    | _ => None
    end else if is_whne t then
      if deep then
        let* t := eval true t in
        Some (tFst t)
      else Some (tFst t)
    else None
  | tSnd t =>
    let* t := eval false t in
    if isPairConstructor t then match t with
    | tPair _ _ _ b => eval deep b
    | _ => None
    end else if is_whne t then
      if deep then
        let* t := eval true t in
        Some (tSnd t)
      else Some (tSnd t)
    else None
  | tProd A B =>
    if deep then
      let* A := eval true A in
      let* B := eval true B in
      Some (tProd A B)
    else Some (tProd A B)
  | tLambda A t =>
    if deep then
      let* A := eval true A in
      let* t := eval true t in
      Some (tLambda A t)
    else Some (tLambda A t)
  | tSucc t =>
    if deep then
      let* t := eval true t in
      Some (tSucc t)
    else Some (tSucc t)
  | tSig A B =>
    if deep then
      let* A := eval true A in
      let* B := eval true B in
      Some (tSig A B)
    else Some (tSig A B)
  | tPair A B a b =>
    if deep then
      let* A := eval true A in
      let* B := eval true B in
      let* a := eval true a in
      let* b := eval true b in
      Some (tPair A B a b)
    else Some (tPair A B a b)
  | tId A t u =>
    if deep then
      let* A := eval true A in
      let* t := eval true t in
      let* u := eval true u in
      Some (tId A t u)
    else Some (tId A t u)
  | tRefl A t =>
    if deep then
      let* A := eval true A in
      let* t := eval true t in
      Some (tRefl A t)
    else Some (tRefl A t)
  | tQuote t =>
    let* t := eval true t in
    if is_closedn 0 t then
      Some (qNat (model.(quote) (erase t)))
    else Some (tQuote t)
  | tReflect t u =>
    None
  end.

Fixpoint eval (deep : bool) (t : term) (k : nat) {struct k} : option term :=
  let eval deep t := match k with 0 => None | S k => eval deep t k end in
  eval_body eval deep t k.

#[local]
Lemma eval_unfold : forall deep t k,
  eval deep t k = ltac:(
    let T := constr:(
      let eval deep t := match k with 0 => None | S k => eval deep t k end in
      eval_body eval deep t k
    ) in
    let T := eval unfold eval_body in T in
    exact T
  ).
Proof.
intros; destruct k; reflexivity.
Qed.

Lemma let_opt_some : forall {A B} (x : option A) (y : B) (f : A -> option B),
  let* x := x in f x = Some y -> ∑ x₀, x = Some x₀.
Proof.
intros ? ? [] **; eauto; cbn in *; congruence.
Qed.

#[local] Ltac expandopt :=
  match goal with H : (bindopt ?x ?f) = Some ?y |- _ =>
    let Hrw := fresh "Hrw" in
    destruct (let_opt_some x y f H) as [? Hrw];
    rewrite Hrw in *; cbn in H
  end.

#[local] Ltac caseconstr f t :=
  let b := fresh "b" in
  let Hb := fresh "Hb" in
  remember (f t) as b eqn:Hb; destruct b;
  [destruct t; try discriminate Hb|idtac].

#[local] Ltac caseval := match goal with
| H : context [isLambda ?t] |- _ =>
  caseconstr isLambda t
| H : context [isNatConstructor ?t] |- _ =>
  caseconstr isNatConstructor t
| H : context [isIdConstructor ?t] |- _ =>
  caseconstr isIdConstructor t
| H : context [isPairConstructor ?t] |- _ =>
  caseconstr isPairConstructor t
| |- context [isLambda ?t] =>
  caseconstr isLambda t
| |- context [isNatConstructor ?t] =>
  caseconstr isNatConstructor t
| |- context [isIdConstructor ?t] =>
  caseconstr isIdConstructor t
| |- context [isPairConstructor ?t] =>
  caseconstr isPairConstructor t
end.

#[local] Lemma is_false_not : forall b, b = false -> ~ b.
Proof.
destruct b; congruence.
Qed.

#[local] Ltac casenf :=
match goal with
| H : (if is_whne ?t then _ else _) = _ |- _ =>
  let b := fresh "b" in
  let Hb := fresh "Hb" in
  remember (is_whne t) as b eqn:Hb; symmetry in Hb; destruct b; [apply is_whne_whne in Hb|]
| H : (if is_dnf ?t then _ else _) = _ |- _ =>
  let b := fresh "b" in
  let Hb := fresh "Hb" in
  remember (is_dnf t) as b eqn:Hb; symmetry in Hb; destruct b; [apply is_dnf_dnf in Hb|]
| H : (if is_closedn 0 ?t then _ else _) = _ |- _ =>
  let b := fresh "b" in
  let Hb := fresh "Hb" in
  remember (is_closedn 0 t) as b eqn:Hb; symmetry in Hb; destruct b; [|apply is_false_not in Hb]
end.

Lemma eval_S : forall k t r deep, eval deep t k = Some r -> eval deep t (S k) = Some r.
Proof.
intros k; induction (Wf_nat.lt_wf k) as [k Hk IHk].
intros t r deep Heq.
rewrite eval_unfold in Heq.
destruct t; cbn; eauto.
all: try match goal with |- (if ?t then _ else _) = Some _ => destruct t; [|now eauto] end.
all: destruct k; [discriminate|].
all: try now (
  repeat expandopt;
  repeat (erewrite IHk; [|Lia.lia|tea]); cbn; congruence
).
+ repeat expandopt.
  erewrite IHk; [|Lia.lia|tea]; cbn [bindopt].
  caseval.
  - now eauto.
  - casenf; [|discriminate].
    destruct deep; [|congruence].
    repeat expandopt.
    repeat (erewrite IHk; [|Lia.lia|tea]); cbn; congruence.
+ repeat expandopt.
  erewrite IHk; [|Lia.lia|tea]; cbn [bindopt].
  caseval.
  - now eauto.
  - now eauto.
  - casenf; [|discriminate].
    destruct deep; [|congruence].
    repeat expandopt.
    repeat (erewrite IHk; [|Lia.lia|tea]); cbn; congruence.
+ repeat expandopt.
  erewrite IHk; [|Lia.lia|tea]; cbn [bindopt].
  casenf; [|discriminate].
  destruct deep; [|congruence].
  repeat expandopt.
  repeat (erewrite IHk; [|Lia.lia|tea]); cbn; congruence.
+ repeat expandopt.
  erewrite IHk; [|Lia.lia|tea]; cbn [bindopt].
  caseval.
  - now eauto.
  - casenf; [|discriminate].
    destruct deep; [|congruence].
    repeat expandopt.
    repeat (erewrite IHk; [|Lia.lia|tea]); cbn; congruence.
+ repeat expandopt.
  erewrite IHk; [|Lia.lia|tea]; cbn [bindopt].
  caseval.
  - now eauto.
  - casenf; [|discriminate].
    destruct deep; [|congruence].
    repeat expandopt.
    repeat (erewrite IHk; [|Lia.lia|tea]); cbn; congruence.
+ repeat expandopt.
  erewrite IHk; [|Lia.lia|tea]; cbn [bindopt].
  caseval.
  - now eauto.
  - casenf; [|discriminate].
    destruct deep; [|congruence].
    repeat expandopt.
    repeat (erewrite IHk; [|Lia.lia|tea]); cbn; congruence.
Qed.

Lemma eval_mon : forall k k' t r deep, k <= k' -> eval deep t k = Some r -> eval deep t k' = Some r.
Proof.
induction 1.
+ eauto.
+ intros; now eapply eval_S.
Qed.

#[local] Ltac rweval := match goal with
| H : _ = isLambda ?t |- (if isLambda ?t then _ else _) = Some _ => rewrite <- H
| H : _ = isNatConstructor ?t |- (if isNatConstructor ?t then _ else _) = Some _ => rewrite <- H
| H : eval ?d ?t ?k = Some ?r |- context [bindopt (eval _ ?t ?k')] =>
  let Hrw := fresh "Hrw" in
  assert (Hrw : eval d t k' = Some r) by (apply (eval_mon k); [Lia.lia|exact H]);
  rewrite Hrw; cbn [bindopt]
| H : whne ?t |- (if is_whne ?t then _ else _) = Some _ => rewrite whne_is_whne; [|exact H]
end.

Lemma dnf_qNat : forall n, dnf (qNat n).
Proof.
induction n; constructor; eauto.
Qed.

Lemma dnf_dne_eval : (forall t, dnf t -> forall deep, ∑ k, eval deep t k = Some t) × (forall t, dne t -> forall deep, ∑ k, eval deep t k = Some t).
Proof.
apply dnf_dne_rect; cbn; intros.
all: try (intros; exists 0; reflexivity).
all: let rec dest accu := match goal with
| H : forall deep, (∑ k : nat, _) |- _ =>
  let k := fresh "k" in
  destruct (H true) as [k];
  clear H; dest constr:(max k accu)
| _ => exists (S accu)
end in
try now (dest 0; rewrite eval_unfold; destruct deep; repeat rweval; congruence).
all: let rec dest accu := match goal with
| H : forall deep, (∑ k : nat, eval deep ?n _ = _), H' : dne ?n |- _ =>
  let k := fresh "k" in
  let k' := fresh "k" in
  destruct (H true) as [k];
  destruct (H false) as [k'];
  clear H; dest constr:(max k (max k' accu))
| H : forall deep, (∑ k : nat, _) |- _ =>
  let k := fresh "k" in
  destruct (H true) as [k];
  clear H; dest constr:(max k accu)
| _ => exists (S accu)
end in
try now (
  dest 0; rewrite eval_unfold; destruct deep; repeat rweval; try caseval; try casenf;
  try match goal with H : dne _ |- _ => now inversion H end;
  rewrite whne_is_whne; eauto using dne_whne
).
+ eauto.
+ destruct (H true) as [k].
  exists (S k); rewrite eval_unfold; rweval.
  apply Bool.not_true_is_false in n; now rewrite n.
Qed.

Lemma dnf_eval : forall t deep, dnf t -> ∑ k, eval deep t k = Some t.
Proof.
destruct dnf_dne_eval as [H _].
intros; now eapply H.
Qed.

Lemma whne_eval : forall t, whne t -> ∑ k, eval false t k = Some t.
Proof.
induction 1; cbn; intros.
all: try match goal with
| H : (∑ k : nat, _) |- _ =>
  let k := fresh "k" in
  let Hk := fresh "Hk" in
  destruct H as [k Hk]; exists (S k); cbn; rewrite Hk; cbn; try caseval;
  inv_whne; rewrite whne_is_whne; eauto
  end.
+ exists 0; reflexivity.
+ edestruct dnf_eval with (deep := true) as [k Hk]; [tea|].
  exists (S k); cbn; rewrite Hk; cbn.
  unfold closed0 in *; destruct is_closedn; congruence.
Qed.

Lemma whnf_eval : forall t, whnf t -> ∑ k, eval false t k = Some t.
Proof.
induction 1; cbn; intros.
all: try now (exists 0; reflexivity).
now eapply whne_eval.
Qed.

Lemma eval_det : forall t u1 u2 k1 k2 deep,
  eval deep t k1 = Some u1 -> eval deep t k2 = Some u2 -> u1 = u2.
Proof.
intros.
assert (eval deep t (max k1 k2) = Some u1).
{ eapply eval_mon; [|tea]; Lia.lia. }
assert (eval deep t (max k1 k2) = Some u2).
{ eapply eval_mon; [|tea]; Lia.lia. }
congruence.
Qed.

Lemma eval_dnf_det : forall t r k deep,
  dnf t -> eval deep t k = Some r -> t = r.
Proof.
intros * Ht Hr.
eapply dnf_eval with (deep := deep) in Ht; destruct Ht.
now eapply eval_det.
Qed.

Lemma eval_whnf_det : forall t r k,
  whnf t -> eval false t k = Some r -> t = r.
Proof.
intros * Ht Hr.
eapply whnf_eval in Ht; destruct Ht.
now eapply eval_det.
Qed.

Lemma eval_nf : forall k t r,
  (eval true t k = Some r -> dnf r) ×
  (eval false t k = Some r -> whnf r) ×
  (forall deep, eval deep t k = Some r -> whne t -> whne r).
Proof.
intros k.
induction (Wf_nat.lt_wf k) as [k Hk IHk].
intros t r.
assert (IHkd : match k return Set with 0 => True | S k =>
  forall t r, eval true t k = Some r -> dnf r end).
{ destruct k; [constructor|]; intros; eapply IHk; eauto. }
assert (IHkw : match k return Set with 0 => True | S k =>
  forall t r, eval false t k = Some r -> whnf r end).
{ destruct k; [constructor|]; intros; eapply IHk; eauto. }
assert (IHkn : match k return Set with 0 => True | S k =>
  forall t r deep, eval deep t k = Some r -> whne t -> whne r end).
{ destruct k; [constructor|]; intros; eapply IHk; eauto. }
clear Hk IHk.
split; [|split; [|intro deep]]; intros Heq; rewrite !eval_unfold in Heq; destruct t; cbn; eauto.
all: try now (injection Heq; intros; subst; eauto using dne, dnf, whne, whnf).
all: try (destruct k; [discriminate|]).
all: try match goal with |- whne ?t -> whne ?u => let H := fresh H in intro H; now inversion H end.
all: try now (
  repeat expandopt;
  injection Heq; intros; subst; eauto 6 using dne, dnf, whne, whnf
).
all: try now (
  repeat expandopt; try caseval; eauto; [];
  casenf; [|discriminate];
  repeat expandopt;
  injection Heq; intros; subst;
  eauto 12 using whne, whnf, dnf, dne, dne_dnf_whne
).
all: try now (
  inversion 1; subst;
  repeat expandopt; caseval;
  [ apply IHkn in Hrw; [inv_whne|tea] |
    casenf; [|discriminate]; destruct deep;
    repeat expandopt; injection Heq; intros; subst; eauto using whne ]
).
+ repeat expandopt; casenf; cbn in *; try discriminate.
  - injection Heq; intros; subst; apply dnf_qNat.
  - injection Heq; intros; subst.
    do 2 constructor; eauto using whne, whnf, dnf, dne, dne_dnf_whne.
+ discriminate.
+ expandopt; casenf; cbn in *; try discriminate.
  - injection Heq; intros; subst; apply dnf_whnf, dnf_qNat.
  - injection Heq; intros; subst.
    do 2 constructor; eauto using whne, whnf, dnf, dne, dne_dnf_whne.
+ discriminate.
+ inversion 1; subst.
  repeat expandopt; caseval.
  - apply IHkn in Hrw; [inv_whne|tea].
  - rewrite eval_unfold in Heq; destruct k; [discriminate|].
    repeat expandopt; caseval.
    * apply IHkn in Hrw; [inv_whne|tea].
    * casenf; [|discriminate]; destruct deep;
      (apply IHkn in Hrw; [inv_whne|tea]).
  - casenf; [|discriminate].
    destruct deep; repeat expandopt; injection Heq; intros; subst; eauto using whne.
+ inversion 1; subst.
  repeat expandopt; casenf; [|discriminate].
  destruct deep; repeat expandopt; injection Heq; intros; subst; eauto using whne.
+ inversion 1; subst.
  repeat expandopt.
  match goal with H : dnf ?t, H' : eval true ?t _ = Some ?r |- _ =>
    let H'' := fresh "H" in
    assert (H'' := dnf_eval _ true H); destruct H'' as [k'];
    assert (t = r) by (now eapply eval_det); subst
  end.
  casenf.
  - exfalso; congruence.
  - injection Heq; intros; subst; eauto using whne.
Qed.

Lemma eval_dnf : forall k t r, eval true t k = Some r -> dnf r.
Proof.
intros; eapply eval_nf; tea.
Qed.

Lemma eval_whne_dne : forall k t r, eval true t k = Some r -> whne t -> dne r.
Proof.
intros; apply dne_dnf_whne.
+ now eapply eval_dnf.
+ now eapply eval_nf.
Qed.

Lemma eval_whnf : forall k t r, eval false t k = Some r -> whnf r.
Proof.
intros; eapply eval_nf; tea.
Qed.

End StepIndex.

(** *** One-step reduction. *)

Inductive OneRedAlg {deep : bool} : term -> term -> Type :=
| BRed {A a t} :
    [ tApp (tLambda A t) a ⤳ t[a..] ]
| appSubst {t u a} :
    OneRedAlg (deep := false) t u ->
    [ tApp t a ⤳ tApp u a ]
| natElimSubst {P hz hs n n'} :
    OneRedAlg (deep := false) n n' ->
    [ tNatElim P hz hs n ⤳ tNatElim P hz hs n' ]
| natElimZero {P hz hs} :
    [ tNatElim P hz hs tZero ⤳ hz ]
| natElimSucc {P hz hs n} :
    [ tNatElim P hz hs (tSucc n) ⤳ tApp (tApp hs n) (tNatElim P hz hs n) ]
| emptyElimSubst {P e e'} :
    OneRedAlg (deep := false) e e' ->
    [tEmptyElim P e ⤳ tEmptyElim P e']        
| fstSubst {p p'} :
    OneRedAlg (deep := false) p p' ->
    [ tFst p ⤳ tFst p']
| fstPair {A B a b} :
    [ tFst (tPair A B a b) ⤳ a ]
| sndSubst {p p'} :
    OneRedAlg (deep := false) p p' ->
    [ tSnd p ⤳ tSnd p']
| sndPair {A B a b} :
    [ tSnd (tPair A B a b) ⤳ b ]
| idElimRefl {A x P hr y A' z} :
  [ tIdElim A x P hr y (tRefl A' z) ⤳ hr ]
| idElimSubst {A x P hr y e e'} :
  OneRedAlg (deep := false) e e' ->
  [ tIdElim A x P hr y e ⤳ tIdElim A x P hr y e' ]
| termEvalAlg {t} :
  dnf t ->
  closed0 t ->
  [ tQuote t ⤳ qNat (model.(quote) (erase t)) ]

(* Hereditary normal forms *)

| prodDom {A A' B} : deep ->
  [ A ⤳ A' ] -> [ tProd A B ⤳ tProd A' B ]
| prodCod {A B B'} : deep ->
  dnf A -> [ B ⤳ B' ] -> [ tProd A B ⤳ tProd A B' ]
| lamDom {A A' t} : deep ->
  [ A ⤳ A' ] -> [ tLambda A t ⤳ tLambda A' t ]
| lamBody {A t t'} : deep ->
  dnf A -> [ t ⤳ t' ] -> [ tLambda A t ⤳ tLambda A t' ]
| appHead {t t' u} : deep ->
  whne t -> [ t ⤳ t' ] -> [ tApp t u ⤳ tApp t' u ]
| appSubstNe {t u u'} : deep ->
  dne t -> [ u ⤳ u' ] -> [ tApp t u ⤳ tApp t u' ]
| succArg {t t'} : deep ->
  [ t ⤳ t' ] -> [ tSucc t ⤳ tSucc t' ]
| natElimHead {P hz hs n n'} : deep ->
  whne n -> [ n ⤳ n' ] -> [ tNatElim P hz hs n ⤳ tNatElim P hz hs n' ]
| natElimPred {P P' hz hs n} : deep ->
  dne n -> [ P ⤳ P' ] -> [ tNatElim P hz hs n ⤳ tNatElim P' hz hs n ]
| natElimBranchZero {P hz hz' hs n} : deep ->
  dne n -> dnf P -> [ hz ⤳ hz' ] -> [ tNatElim P hz hs n ⤳ tNatElim P hz' hs n ]
| natElimBranchSucc {P hz hs hs' n} : deep ->
  dne n -> dnf P -> dnf hz -> [ hs ⤳ hs' ] -> [ tNatElim P hz hs n ⤳ tNatElim P hz hs' n ]
| emptyElimHead {P n n'} : deep ->
  whne n -> [ n ⤳ n' ] -> [ tEmptyElim P n ⤳ tEmptyElim P n' ]
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
| fstHead {n n'} : deep ->
  whne n -> [ n ⤳ n' ] -> [ tFst n ⤳ tFst n' ]
| sndHead {n n'} : deep ->
  whne n -> [ n ⤳ n' ] -> [ tSnd n ⤳ tSnd n' ]
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
| idElimHead {A x P hr y e e'} : deep ->
  whne e -> [ e ⤳ e' ] ->
  [ tIdElim A x P hr y e ⤳ tIdElim A x P hr y e' ]
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

Lemma gred_ored : forall deep t t', [ t ⤳ t' ] -> @OneRedAlg deep t t'.
Proof.
destruct deep; intros; tea.
now apply dred_ored.
Qed.

Lemma dred_red : forall t t', [ t ⤳* t' ] -> [ t ⇶* t' ].
Proof.
induction 1; econstructor; tea.
now apply dred_ored.
Qed.

Lemma gred_red : forall deep t t', [ t ⤳* t' ] -> @RedClosureAlg deep t t'.
Proof.
destruct deep; intros; tea.
now apply dred_red.
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
end; try now eauto using dred_ored.
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
    eauto using whne, whnf.
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
| H : whne _ |- _ => now inversion H
| H : dne _ |- _ => now eapply dnf_dne_nogred in H
| H : dnf _ |- _ => now eapply dnf_dne_nogred in H
| H : whne _ |- _ => now eapply whne_nored in H
| H : [ ?t ⇶ ?u ] |- _ => now inversion H
| H : [ ?t ⤳ ?u ] |- _ => inversion H; discriminate
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
induction Ht; intros u Hr; inversion Hr; subst; first [constructor; now eauto using dred_ored|now inv_whne|idtac].
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
intros; now constructor.
Qed.

Lemma oredalg_natElimSubst {P hz hs n n'} :
  [ n ⤳ n' ] ->
  [ tNatElim P hz hs n ⤳ tNatElim P hz hs n' ].
Proof.
intros; now constructor.
Qed.

(** *** Stability by weakening *)

Lemma gredalg_wk {deep} (ρ : nat -> nat) (t u : term) : ren_inj ρ -> OneRedAlg (deep := deep) t u ->  OneRedAlg (deep := deep)  t⟨ρ⟩ u⟨ρ⟩.
Proof.
intros Hρ Hred; induction Hred in ρ, Hρ |- *; cbn.
all: try now (econstructor; intuition).
all: try now (econstructor; try apply dnf_ren; try apply dne_ren; intuition eauto using upRen_term_term_inj).
+ replace (t[a..]⟨ρ⟩) with (t⟨upRen_term_term ρ⟩)[a⟨ρ⟩..] by now bsimpl.
  now constructor.
+ rewrite quote_ren; tea.
  constructor; [now apply dnf_ren|now apply closed0_ren].
Qed.

Lemma oredalg_wk (ρ : nat -> nat) (t u : term) :
ren_inj ρ ->
[t ⤳ u] ->
[t⟨ρ⟩ ⤳ u⟨ρ⟩].
Proof.
apply gredalg_wk.
Qed.

Lemma gcredalg_wk {deep} (ρ : nat -> nat) (t u : term) : ren_inj ρ -> RedClosureAlg (deep := deep) t u -> RedClosureAlg (deep := deep)  t⟨ρ⟩ u⟨ρ⟩.
Proof.
induction 2; econstructor; eauto using gredalg_wk.
Qed.

Lemma credalg_wk (ρ : nat -> nat) (t u : term) :
ren_inj ρ ->
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
+ inversion o; subst; [inversion Hn| | |].
  - now eelim whne_nored.
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
  - now eelim whne_nored.
  - inv_whne.
  - econstructor; [tea|eapply IHHr]; try reflexivity.
    eapply dredalg_whne; tea.
    econstructor; [tea|reflexivity].
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
all: try now (constructor; eauto using @OneRedAlg, whne_ren_rev, dne_ren_rev, dnf_ren_rev, upRen_term_term_inj).
+ assert (Hrw : forall t u, t⟨upRen_term_term ρ⟩[(u⟨ρ⟩)..] = (t[u..])⟨ρ⟩) by now asimpl.
  rewrite Hrw in Hu; apply ren_inj_inv in Hu; tea.
  subst; constructor.
+ assert (closed0 t₀) by now eapply closed0_ren_rev.
  rewrite <- quote_ren in Hu; tea.
  apply ren_inj_inv in Hu; tea.
  rewrite <- Hu.
  constructor; [now eapply dnf_ren_rev|tea].
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

Lemma dred_ren_adj : forall t u ρ, ren_inj ρ -> [t⟨ρ⟩ ⇶ u] -> ∑ u', u = u'⟨ρ⟩.
Proof.
intros t u ρ Hρ Hr.
remember t⟨ρ⟩ as t' eqn:Ht.
revert t ρ Hρ Ht; induction Hr; intros t₀ ρ Hρ Ht.
all: repeat match goal with H : _ = ?t⟨?ρ⟩ |- _ =>
  destruct t; cbn in *; try discriminate; [idtac];
  try injection H; intros; subst
end.
all: repeat match goal with H : forall (t : term) (ρ : nat -> nat), _ |- _ =>
  let H' := fresh in
  unshelve eassert (H' := H _ _ _ eq_refl); [eauto using upRen_term_term_inj|];
  clear H; destruct H'; subst
end.
all: let t := lazymatch goal with |- ∑ n, ?t = _ => t end in
     try (let t := unren t in now eexists t).
+ assert (Hrw : forall t u, t⟨upRen_term_term ρ⟩[(u⟨ρ⟩)..] = (t[u..])⟨ρ⟩) by now asimpl.
  rewrite Hrw; now eexists.
+ rewrite <- quote_ren; eauto using closed0_ren_rev.
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
+ unshelve eassert (H := dred_ren_adj _ _ _ _ _); [..|tea|tea|].
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
  now econstructor.
Qed.

Lemma redalg_natElim {P hs hz t t'} : [t ⤳* t'] -> [tNatElim P hs hz t ⤳* tNatElim P hs hz t'].
Proof.
induction 1.
+ reflexivity.
+ econstructor; [|eassumption].
  now econstructor.
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
Qed.

Lemma redalg_snd {t t'} : [t ⤳* t'] -> [tSnd t ⤳* tSnd t'].
Proof.
  induction 1; [reflexivity|].
  econstructor; tea.
  constructor; tea.
Qed.

Lemma redalg_idElim {A x P hr y t t'} : [t ⤳* t'] -> [tIdElim A x P hr y t ⤳* tIdElim A x P hr y t'].
Proof.
  induction 1; [reflexivity|].
  econstructor; tea; now constructor.
Qed.

Lemma redalg_quote {t t'} : [t ⇶* t'] -> [tQuote t ⤳* tQuote t'].
Proof.
induction 1; [reflexivity|].
econstructor; [|tea].
now constructor.
Qed.

Lemma redalg_one_step {t t'} : [t ⤳ t'] -> [t ⤳* t'].
Proof. intros; econstructor;[tea|reflexivity]. Qed.

Lemma dredalg_one_step {t t'} : [t ⇶ t'] -> [t ⇶* t'].
Proof. intros; econstructor;[tea|reflexivity]. Qed.

Lemma gredalg_one_step {deep t t'} : @OneRedAlg deep t t' -> @RedClosureAlg deep t t'.
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
    now constructor.
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
  now constructor.
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
  now constructor.
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
    now constructor.
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
    now constructor.
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
    now constructor.
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
+ now apply closedn_beta.
+ apply closedn_qNat.
Qed.

Lemma dredalg_closedn : forall t u n, [t ⇶* u] -> closedn n t -> closedn n u.
Proof.
intros t u n Hr Hc; induction Hr; eauto using dred_closedn.
Qed.

Lemma dredalg_closed0 : forall t u, [t ⇶* u] -> closed0 t -> closed0 u.
Proof.
intros; now eapply dredalg_closedn.
Qed.

(** Step-indexed normalization coincides with reduction *)

#[local] Ltac expandopt :=
  match goal with H : (bindopt ?x ?f) = Some ?y |- _ =>
    let Hrw := fresh "Hrw" in
    destruct (let_opt_some x y f H) as [? Hrw];
    rewrite Hrw in *; cbn in H
  end.

#[local] Ltac caseconstr f t :=
  let b := fresh "b" in
  let Hb := fresh "Hb" in
  remember (f t) as b eqn:Hb; destruct b;
  [destruct t; try discriminate Hb|idtac].

#[local] Ltac caseval := match goal with
| H : context [if isLambda ?t then _ else _] |- _ =>
  caseconstr isLambda t
| H : context [if isNatConstructor ?t then _ else _] |- _ =>
  caseconstr isNatConstructor t
| H : context [if isIdConstructor ?t then _ else _] |- _ =>
  caseconstr isIdConstructor t
| H : context [if isPairConstructor ?t then _ else _] |- _ =>
  caseconstr isPairConstructor t
| |- context [if isLambda ?t then _ else _] =>
  caseconstr isLambda t
| |- context [if isNatConstructor ?t then _ else _] =>
  caseconstr isNatConstructor t
| |- context [if isIdConstructor ?t then _ else _] =>
  caseconstr isIdConstructor t
| |- context [if isPairConstructor ?t then _ else _] =>
  caseconstr isPairConstructor t
end.

#[local] Ltac casenf :=
match goal with
| H : context [is_whne ?t] |- _ =>
  let b := fresh "b" in
  let Hb := fresh "Hb" in
  remember (is_whne t) as b eqn:Hb; symmetry in Hb; destruct b; [apply is_whne_whne in Hb|]
| H : context [is_dnf ?t] |- _ =>
  let b := fresh "b" in
  let Hb := fresh "Hb" in
  remember (is_dnf t) as b eqn:Hb; symmetry in Hb; destruct b; [apply is_dnf_dnf in Hb|]
| H : context [is_closedn 0 ?t] |- _ =>
  let b := fresh "b" in
  let Hb := fresh "Hb" in
  remember (is_closedn 0 t) as b eqn:Hb; symmetry in Hb; destruct b; [|apply is_false_not in Hb]
end.

#[local] Ltac rweval := match goal with
| H : _ = isLambda ?t |- (if isLambda ?t then _ else _) = Some _ => rewrite <- H
| H : _ = isNatConstructor ?t |- (if isNatConstructor ?t then _ else _) = Some _ => rewrite <- H
| H : eval ?d ?t ?k = Some ?r |- context [bindopt (eval _ ?t ?k')] =>
  let Hrw := fresh "Hrw" in
  assert (Hrw : eval d t k' = Some r) by (apply (eval_mon k); [Lia.lia|exact H]);
  rewrite Hrw; cbn [bindopt]
| H : whne ?t |- (if is_whne ?t then _ else _) = Some _ => rewrite whne_is_whne; [|exact H]
end.

#[local] Ltac evalinv := match goal with
| H : whne ?t, H' : eval false ?t _ = Some ?r |- _ =>
  assert (t = r) by (now (eapply eval_whnf_det; eauto using whnf_whne)); subst
end.

Lemma dred_eval : forall deep t u r k, OneRedAlg (deep := deep) t u ->
  eval deep u k = Some r -> ∑ k', k <= k' × eval deep t k' = Some r.
Proof.
intros deep t u r k Hr; revert r k.
induction Hr; intros r k Heval; cbn.
all: try now (
  rewrite eval_unfold in Heval;
  destruct k; [discriminate|];
  expandopt; edestruct IHHr as (k'&?&Hk'); [tea|];
  exists (S k'); split; [Lia.lia|];
  cbn; repeat rweval; [..|destruct deep]; try caseval; repeat expandopt; repeat rweval; try casenf; try congruence;
  now eapply eval_mon
).
all: try now (
  rewrite eval_unfold in Heval;
  destruct deep; [|discriminate];
  destruct k; [discriminate|];
  repeat expandopt;
  edestruct IHHr as (k'&?&Hk'); [tea|];
  exists (S k'); split; [Lia.lia|];
  cbn; repeat rweval; try caseval; repeat expandopt; repeat rweval; try casenf; try congruence;
  now eapply eval_mon
).
all: try now (
  exists (S k); split; [Lia.lia|];
  do 2 rewrite eval_unfold; tea
).
all: try now (
  rewrite eval_unfold in Heval;
  destruct k; [discriminate|];
  repeat expandopt; try caseval; try casenf;
  (let T := type of Heval in try match T with (if ?d then _ else _) = _ => destruct d; repeat expandopt end);
  (edestruct IHHr as (k'&?&Hk'); [tea|]);
  (exists (S k'); split; [Lia.lia|]);
  cbn; repeat rweval; try caseval; try (rewrite whne_is_whne; [|now tea]); first [now congruence|now eapply eval_mon|idtac]
).
+ destruct (dnf_eval _ true d) as [k'].
  exists (S (max k k')); split; [Lia.lia|].
  rewrite eval_unfold; cbn [bindopt]; rweval.
  rewrite c; cbn.
  assert (Hq : dnf (qNat (quote model (erase t)))) by apply dnf_qNat.
  apply (dnf_eval _ deep) in Hq; destruct Hq as [k''].
  f_equal; eapply eval_det; [|tea]; tea.
+ rewrite eval_unfold in Heval.
  destruct k; [discriminate|].
  destruct deep; [|discriminate].
  repeat expandopt; caseval.
  - apply eval_nf in Hrw; [inv_whne|now eapply dred_whne].
  - assert (whne t') by (now eapply dred_whne); evalinv.
    casenf; [|discriminate]; repeat expandopt.
    edestruct IHHr as (k'&?&Hk'); [tea|].
    destruct (whne_eval t) as [k'']; [tea|].
    exists (S (max k' k'')); split; [Lia.lia|].
    cbn; repeat rweval; caseval; [now inversion w|].
    rewrite whne_is_whne; tea.
+ rewrite eval_unfold in Heval.
  destruct k; [discriminate|].
  destruct deep; [|discriminate].
  repeat expandopt; caseval.
  - apply eval_nf in Hrw; [inv_whne|now eapply dne_whne].
  - casenf; [|discriminate]; repeat expandopt.
    edestruct IHHr as (k'&?&Hk'); [tea|].
    exists (S k'); split; [Lia.lia|].
    cbn; repeat rweval; congruence.
+ rewrite eval_unfold in Heval.
  destruct k; [discriminate|].
  destruct deep; [|discriminate].
  repeat expandopt; caseval.
  - apply eval_nf in Hrw; [inv_whne|now eapply dred_whne].
  - apply eval_nf in Hrw; [inv_whne|now eapply dred_whne].
  - casenf; [|discriminate]; repeat expandopt.
    assert (whne n') by (now eapply dred_whne); evalinv.
    edestruct IHHr as (k'&?&Hk'); [tea|].
    destruct (whne_eval n) as [k'']; [tea|].
    exists (S (max k' k'')); split; [Lia.lia|].
    cbn; repeat rweval; caseval; try now inversion w.
    rewrite whne_is_whne; tea.
+ rewrite eval_unfold in Heval.
  destruct k; [discriminate|].
  destruct deep; [|discriminate].
  repeat expandopt; caseval.
  - assert (Hw : whne n) by now apply dne_whne.
    eapply eval_nf in Hw; [|tea]; inv_whne.
  - assert (Hw : whne n) by now apply dne_whne.
    eapply eval_nf in Hw; [|tea]; inv_whne.
  - casenf; [|discriminate].
    repeat expandopt.
    edestruct IHHr as (k'&?&Hk'); [tea|].
    exists (S k'); split; [Lia.lia|].
    cbn; repeat rweval; congruence.
+ rewrite eval_unfold in Heval.
  destruct k; [discriminate|].
  destruct deep; [|discriminate].
  repeat expandopt; caseval.
  - assert (Hw : whne n) by now apply dne_whne.
    eapply eval_nf in Hw; [|tea]; inv_whne.
  - assert (Hw : whne n) by now apply dne_whne.
    eapply eval_nf in Hw; [|tea]; inv_whne.
  - casenf; [|discriminate].
    repeat expandopt.
    edestruct IHHr as (k'&?&Hk'); [tea|].
    exists (S k'); split; [Lia.lia|].
    cbn; repeat rweval; congruence.
+ rewrite eval_unfold in Heval.
  destruct k; [discriminate|].
  destruct deep; [|discriminate].
  repeat expandopt; caseval.
  - assert (Hw : whne n) by now apply dne_whne.
    eapply eval_nf in Hw; [|tea]; inv_whne.
  - assert (Hw : whne n) by now apply dne_whne.
    eapply eval_nf in Hw; [|tea]; inv_whne.
  - casenf; [|discriminate].
    repeat expandopt.
    edestruct IHHr as (k'&?&Hk'); [tea|].
    exists (S k'); split; [Lia.lia|].
    cbn; repeat rweval; congruence.
+ rewrite eval_unfold in Heval.
  destruct k; [discriminate|].
  destruct deep; [|discriminate].
  repeat expandopt.
  casenf; [|discriminate]; repeat expandopt.
  assert (whne n') by (now eapply dred_whne); evalinv.
  edestruct IHHr as (k'&?&Hk'); [tea|].
  destruct (whne_eval n) as [k'']; [tea|].
  exists (S (max k' k'')); split; [Lia.lia|].
  cbn; repeat rweval; congruence.
+ rewrite eval_unfold in Heval.
  destruct k; [discriminate|].
  destruct deep; [|discriminate].
  repeat expandopt.
  casenf; [|discriminate]; repeat expandopt.
  edestruct IHHr as (k'&?&Hk'); [tea|].
  exists (S k'); split; [Lia.lia|].
  cbn; repeat rweval; congruence.
+ rewrite eval_unfold in Heval.
  destruct k; [discriminate|].
  destruct deep; [|discriminate].
  repeat expandopt; caseval.
  - apply eval_nf in Hrw; [inv_whne|now eapply dred_whne].
  - casenf; [|discriminate]; repeat expandopt.
    assert (whne n') by (now eapply dred_whne); evalinv.
    edestruct IHHr as (k'&?&Hk'); [tea|].
    destruct (whne_eval n) as [k'']; [tea|].
    exists (S (max k' k'')); split; [Lia.lia|].
    cbn; repeat rweval; caseval; try now inversion w.
    rewrite whne_is_whne; tea.
+ rewrite eval_unfold in Heval.
  destruct k; [discriminate|].
  destruct deep; [|discriminate].
  repeat expandopt; caseval.
  - apply eval_nf in Hrw; [inv_whne|now eapply dred_whne].
  - casenf; [|discriminate]; repeat expandopt.
    assert (whne n') by (now eapply dred_whne); evalinv.
    edestruct IHHr as (k'&?&Hk'); [tea|].
    destruct (whne_eval n) as [k'']; [tea|].
    exists (S (max k' k'')); split; [Lia.lia|].
    cbn; repeat rweval; caseval; try now inversion w.
    rewrite whne_is_whne; tea.
+ rewrite eval_unfold in Heval.
  destruct k; [discriminate|].
  destruct deep; [|discriminate].
  repeat expandopt; caseval.
  - apply eval_nf in Hrw; [inv_whne|now eapply dred_whne].
  - casenf; [|discriminate]; repeat expandopt.
    assert (whne e') by (now eapply dred_whne); evalinv.
    edestruct IHHr as (k'&?&Hk'); [tea|].
    destruct (whne_eval e) as [k'']; [tea|].
    exists (S (max k' k'')); split; [Lia.lia|].
    cbn; repeat rweval; caseval; try now inversion w.
    rewrite whne_is_whne; tea.
+ rewrite eval_unfold in Heval.
  destruct k; [discriminate|].
  destruct deep; [|discriminate].
  repeat expandopt; caseval.
  - apply eval_nf in Hrw; [inv_whne|now eapply dne_whne].
  - casenf; [|discriminate]; repeat expandopt.
    edestruct IHHr as (k'&?&Hk'); [tea|].
    exists (S k'); split; [Lia.lia|].
    cbn; repeat rweval; caseval; [congruence|].
    rewrite whne_is_whne; tea.
+ rewrite eval_unfold in Heval.
  destruct k; [discriminate|].
  destruct deep; [|discriminate].
  repeat expandopt; caseval.
  - apply eval_nf in Hrw; [inv_whne|now eapply dne_whne].
  - casenf; [|discriminate]; repeat expandopt.
    edestruct IHHr as (k'&?&Hk'); [tea|].
    exists (S k'); split; [Lia.lia|].
    cbn; repeat rweval; caseval; [congruence|].
    rewrite whne_is_whne; tea.
+ rewrite eval_unfold in Heval.
  destruct k; [discriminate|].
  destruct deep; [|discriminate].
  repeat expandopt; caseval.
  - apply eval_nf in Hrw; [inv_whne|now eapply dne_whne].
  - casenf; [|discriminate]; repeat expandopt.
    edestruct IHHr as (k'&?&Hk'); [tea|].
    exists (S k'); split; [Lia.lia|].
    cbn; repeat rweval; caseval; [congruence|].
    rewrite whne_is_whne; tea.
+ rewrite eval_unfold in Heval.
  destruct k; [discriminate|].
  destruct deep; [|discriminate].
  repeat expandopt; caseval.
  - apply eval_nf in Hrw; [inv_whne|now eapply dne_whne].
  - casenf; [|discriminate]; repeat expandopt.
    edestruct IHHr as (k'&?&Hk'); [tea|].
    exists (S k'); split; [Lia.lia|].
    cbn; repeat rweval; caseval; [congruence|].
    rewrite whne_is_whne; tea.
+ rewrite eval_unfold in Heval.
  destruct k; [discriminate|].
  destruct deep; [|discriminate].
  repeat expandopt; caseval.
  - apply eval_nf in Hrw; [inv_whne|now eapply dne_whne].
  - casenf; [|discriminate]; repeat expandopt.
    edestruct IHHr as (k'&?&Hk'); [tea|].
    exists (S k'); split; [Lia.lia|].
    cbn; repeat rweval; caseval; [congruence|].
    rewrite whne_is_whne; tea.
Qed.

Lemma dredalg_eval : forall deep t r, RedClosureAlg (deep := deep) t r -> dnf r ->
  ∑ k, eval deep t k = Some r.
Proof.
induction 1; intros.
+ now apply dnf_eval.
+ destruct IHRedClosureAlg as [k Hk]; [tea|].
  destruct (dred_eval _ _ _ _ _ o Hk) as (k'&?&?).
  eauto.
Qed.

Lemma eval_dredalg : forall k deep t r, eval deep t k = Some r -> RedClosureAlg (deep := deep) t r.
Proof.
intros k; induction (Wf_nat.lt_wf k) as [k Hk IHk].
intros deep t r Heq; rewrite eval_unfold in Heq.
destruct t.
all: try now (injection Heq; intros; subst; reflexivity).
all: try now (
  destruct deep; [
    destruct k; [discriminate|];
    repeat expandopt;
    injection Heq; intros; subst;
    eauto 14 using eval_dnf,
      dredalg_lambda, dredalg_sig, dredalg_prod, dredalg_id,
      dredalg_succ, dredalg_pair, dredalg_refl
  | injection Heq; intros; subst; reflexivity]
).
all: destruct k; [discriminate|].
+ repeat expandopt; caseval; [..|casenf; [|discriminate]; destruct deep; repeat expandopt].
  - etransitivity; [|eapply IHk; now eauto].
    apply gred_red.
    etransitivity; [eapply redalg_app, IHk; eauto|].
    apply redalg_one_step; now constructor.
  - injection Heq; intros; subst.
    etransitivity.
    * eapply gred_red, redalg_app, IHk; eauto.
    * apply dredalg_app; eauto using eval_whne_dne, eval_dnf.
  - injection Heq; intros; subst.
    eapply redalg_app, IHk; eauto.
+ repeat expandopt; caseval; [..|casenf; [|discriminate]; destruct deep; repeat expandopt].
  - etransitivity; [|eapply IHk; eauto].
    etransitivity; [eapply gred_red, redalg_natElim; eauto|].
    eapply gredalg_one_step; constructor.
  - etransitivity; [|eapply IHk; eauto].
    etransitivity; [eapply gred_red, redalg_natElim; eauto|].
    eapply gredalg_one_step; constructor.
  - injection Heq; intros; subst.
    etransitivity.
    * eapply gred_red, redalg_natElim, IHk; eauto.
    * apply dredalg_natElim; eauto using eval_whne_dne, eval_dnf.
  - injection Heq; intros; subst.
    eapply gred_red, redalg_natElim, IHk; eauto.
+ repeat expandopt; [..|casenf; [|discriminate]; destruct deep; repeat expandopt].
  - injection Heq; intros; subst.
    etransitivity; [eapply gred_red, redalg_natEmpty; eauto|].
    apply dredalg_emptyElim; eauto using eval_whne_dne, eval_dnf.
  - injection Heq; intros; subst.
    apply redalg_natEmpty; eauto using eval_whne_dne, eval_dnf.
+ repeat expandopt; caseval; [..|casenf; [|discriminate]; destruct deep; repeat expandopt].
  - etransitivity; [|eapply IHk; eauto].
    etransitivity; [eapply gred_red, redalg_fst; eauto|].
    eapply gredalg_one_step; constructor.
  - injection Heq; intros; subst.
    etransitivity.
    * eapply gred_red, redalg_fst, IHk; eauto.
    * apply dredalg_fst; eauto using eval_whne_dne, eval_dnf.
  - injection Heq; intros; subst.
    apply redalg_fst; eauto using eval_whne_dne, eval_dnf.
+ repeat expandopt; caseval; [..|casenf; [|discriminate]; destruct deep; repeat expandopt].
  - etransitivity; [|eapply IHk; eauto].
    etransitivity; [eapply gred_red, redalg_snd; eauto|].
    eapply gredalg_one_step; constructor.
  - injection Heq; intros; subst.
    etransitivity.
    * eapply gred_red, redalg_snd, IHk; eauto.
    * apply dredalg_snd; eauto using eval_whne_dne, eval_dnf.
  - injection Heq; intros; subst.
    apply redalg_snd; eauto using eval_whne_dne, eval_dnf.
+ repeat expandopt; caseval; [..|casenf; [|discriminate]; destruct deep; repeat expandopt].
  - etransitivity; [|eapply IHk; eauto].
    etransitivity; [eapply gred_red, redalg_idElim; eauto|].
    eapply gredalg_one_step; constructor.
  - injection Heq; intros; subst.
    etransitivity; [eapply gred_red, redalg_idElim; eauto|].
    apply dredalg_idElim; eauto using eval_whne_dne, eval_dnf.
  - injection Heq; intros; subst.
    apply redalg_idElim; eauto using eval_whne_dne, eval_dnf.
+ repeat expandopt; casenf; injection Heq; intros; subst.
  - etransitivity; [|apply gredalg_one_step, termEvalAlg; eauto using eval_dnf].
    apply gred_red, redalg_quote; now eauto.
  - apply gred_red, redalg_quote; now eauto.
+ discriminate.
Qed.

(** Stability of erasure *)

Lemma gred_unannot : forall deep t u, @OneRedAlg deep t u -> (unannot t = unannot u) + @OneRedAlg deep (unannot t) (unannot u).
Proof.
induction 1; cbn in *.
all: eauto.
all: try match goal with H : sum _ _ |- _ => let He := fresh in destruct H as [He|]; [left; now rewrite He|] end.
all: try now (right; eauto 7 using @OneRedAlg, whne_unannot, dne_unannot, dnf_unannot, dnf).
+ right; rewrite unannot_subst.
  match goal with |- OneRedAlg _ ?u => replace u with (unannot t)[(unannot a)..] end.
  - constructor.
  - apply ext_term; intros []; reflexivity.
+ right; rewrite unannot_qNat.
  replace (erase t) with (erase (unannot t)).
  - constructor; [now apply dnf_unannot|].
    unfold closed0; now rewrite closedn_unannot.
  - repeat rewrite erase_unannot_etared.
    now rewrite unannot_idempotent.
Qed.

Lemma dred_unannot : forall t u, [t ⇶ u] -> (unannot t = unannot u) + [unannot t ⇶ unannot u].
Proof.
intros; now apply gred_unannot.
Qed.

Lemma dredalg_unannot : forall t u, [t ⇶* u] -> [unannot t ⇶* unannot u].
Proof.
induction 1.
+ reflexivity.
+ destruct (dred_unannot _ _ o) as [He|].
  - now rewrite He.
  - etransitivity; eauto using dredalg_one_step.
Qed.
