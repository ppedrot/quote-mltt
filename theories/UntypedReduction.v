(** * LogRel.UntypedReduction: untyped reduction, used to define algorithmic typing.*)
From Coq Require Import CRelationClasses ssrbool.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Computation Notations Context Closed NormalForms NormalEq Weakening.

(** ** Reductions *)

(** Step-indexed normalization function *)

Arguments murec : simpl never.

Section StepIndex.

Definition bindopt {A B} (x : option A) (f : A -> option B) :=
match x with
| None => None
| Some x => f x
end.

#[local]
Notation "'let*' x ':=' t 'in' u" := (bindopt t (fun x => u)) (at level 50, x binder).

Definition eval_body (eval : bool -> term -> option term) (murec : term -> option (nat × term))
  (deep : bool) (t : term) (k : nat) : option term :=
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
  | tStep t u =>
    let* t := eval true t in
    let* u := eval true u in
    if is_closedn 0 t && is_closedn 0 u then
      let* u := uNat u in
      let* ans := murec (tApp (erase t) (qNat u)) in
      let (step, v) := ans in
      let* v := uNat v in
      Some (qNat step)
    else Some (tStep t u)
  | tReflect t u =>
    let* t := eval true t in
    let* u := eval true u in
    if is_closedn 0 t && is_closedn 0 u then
      let* u := uNat u in
      let* ans := murec (tApp (erase t) (qNat u)) in
      let (step, v) := ans in
      let* v := uNat v in
      Some (qEvalTm step v)
    else Some (tReflect t u)
  end.

Fixpoint eval (deep : bool) (t : term) (k : nat) {struct k} : option term :=
  let murec t := murec (fun k => eval true t k) k in
  let eval deep t := match k with 0 => None | S k => eval deep t k end in
  eval_body eval murec deep t k.

(** Big step reduction: essentially the same as above with hidden steps *)

Reserved Notation "[ t ↓ u ]" (at level 0, t, u at level 50).
Reserved Notation "[ t ⇊ u ]" (at level 0, t, u at level 50).

Inductive bigstep : bool -> term -> term -> Set :=
| bs_rel : forall n, [tRel n ↓ tRel n]
| bs_sort : forall s, [tSort s ↓ tSort s]
| bs_prod : forall A B, [tProd A B ↓ tProd A B]
| bs_lambda : forall A t, [tLambda A t ↓ tLambda A t]
| bs_app_lambda : forall A t t₀ u r, [t ↓ tLambda A t₀] -> [t₀[u..] ↓ r] -> [tApp t u ↓ r]
| bs_app_ne : forall t t₀ u, [t ↓ t₀] -> whne t₀ -> [tApp t u ↓ tApp t₀ u]
| bs_nat : [tNat ↓ tNat]
| bs_zero : [tZero ↓ tZero]
| bs_succ : forall t, [tSucc t ↓ tSucc t]
| bs_natElim_zero : forall P hz hs t r, [t ↓ tZero] -> [hz ↓ r] -> [tNatElim P hz hs t ↓ r]
| bs_natElim_succ : forall P hz hs t t₀ r,
  [t ↓ tSucc t₀] -> [tApp (tApp hs t₀) (tNatElim P hz hs t₀) ↓ r] -> [tNatElim P hz hs t ↓ r]
| bs_natElim_ne : forall P hz hs t t₀, [t ↓ t₀] -> whne t₀ -> [tNatElim P hz hs t ↓ tNatElim P hz hs t₀]
| bs_empty : [tEmpty ↓ tEmpty]
| bs_emptyElim_ne : forall P t t₀, [t ↓ t₀] -> whne t₀ -> [tEmptyElim P t ↓ tEmptyElim P t₀]
| bs_sig : forall A B, [tSig A B ↓ tSig A B]
| bs_pair : forall A B a b, [tPair A B a b ↓ tPair A B a b]
| bs_fst_pair : forall t A B a b r, [t ↓ tPair A B a b] -> [a ↓ r] -> [tFst t ↓ r]
| bs_fst_ne : forall t t₀, [t ↓ t₀] -> whne t₀ -> [tFst t ↓ tFst t₀]
| bs_snd_pair : forall t A B a b r, [t ↓ tPair A B a b] -> [b ↓ r] -> [tSnd t ↓ r]
| bs_snd_ne : forall t t₀, [t ↓ t₀] -> whne t₀ -> [tSnd t ↓ tSnd t₀]
| bs_id : forall A t u, [tId A t u ↓ tId A t u]
| bs_refl : forall A t, [tRefl A t ↓ tRefl A t]
| bs_idElim_refl : forall A A₀ x x₀ P hr y e r, [e ↓ tRefl A₀ x₀] -> [hr ↓ r] -> [tIdElim A x P hr y e ↓ r]
| bs_idElim_ne : forall A x P hr y e e₀, [e ↓ e₀] -> whne e₀ -> [tIdElim A x P hr y e ↓ tIdElim A x P hr y e₀]
| bs_quote_eval : forall t t₀, [t ⇊ t₀] -> closed0 t₀ -> [tQuote t ↓ qNat (model.(quote) (erase t₀))]
| bs_quote_ne : forall t t₀, [t ⇊ t₀] -> ~ closed0 t₀ -> [tQuote t ↓ tQuote t₀]
| bs_step_eval : forall t t₀ u u₀ n k k',
  [t ⇊ t₀] -> [u ⇊ qNat u₀] -> closed0 t₀ ->
  murec (fun k => eval true (tApp (erase t₀) (qNat u₀)) k) k = Some (k', qNat n) ->
  [tStep t u ↓ qNat k']
| bs_step_ne : forall t t₀ u u₀,
  [t ⇊ t₀] -> [u ⇊ u₀] -> (~ closed0 t₀) + (~ closed0 u₀) ->
  [tStep t u ↓ tStep t₀ u₀]
| bs_reflect_eval : forall t t₀ u u₀ n k k',
  [t ⇊ t₀] -> [u ⇊ qNat u₀] -> closed0 t₀ ->
  murec (fun k => eval true (tApp (erase t₀) (qNat u₀)) k) k = Some (k', qNat n) ->
  [tReflect t u ↓ qEvalTm k' n]
| bs_reflect_ne : forall t t₀ u u₀,
  [t ⇊ t₀] -> [u ⇊ u₀] -> (~ closed0 t₀) + (~ closed0 u₀) ->
  [tReflect t u ↓ tReflect t₀ u₀]

| dbs_rel : forall n, [tRel n ⇊ tRel n]
| dbs_sort : forall s, [tSort s ⇊ tSort s]
| dbs_prod : forall A A₀ B B₀, [A ⇊ A₀] -> [B ⇊ B₀] -> [tProd A B ⇊ tProd A₀ B₀]
| dbs_lambda : forall A t t₀, [t ⇊ t₀] -> [tLambda A t ⇊ tLambda A t₀]
| dbs_app_lambda : forall A t t₀ u r, [t ↓ tLambda A t₀] -> [t₀[u..] ⇊ r] -> [tApp t u ⇊ r]
| dbs_app_ne : forall t n t₀ u u₀, [t ↓ n] -> whne n -> [n ⇊ t₀] -> [u ⇊ u₀] -> [tApp t u ⇊ tApp t₀ u₀]
| dbs_nat : [tNat ⇊ tNat]
| dbs_zero : [tZero ⇊ tZero]
| dbs_succ : forall t t₀, [t ⇊ t₀] -> [tSucc t ⇊ tSucc t₀]
| dbs_natElim_zero : forall P hz hs t r, [t ↓ tZero] -> [hz ⇊ r] -> [tNatElim P hz hs t ⇊ r]
| dbs_natElim_succ : forall P hz hs t t₀ r,
  [t ↓ tSucc t₀] -> [tApp (tApp hs t₀) (tNatElim P hz hs t₀) ⇊ r] -> [tNatElim P hz hs t ⇊ r]
| dbs_natElim_ne : forall P P₀ hz hz₀ hs hs₀ t n t₀,
  [t ↓ n] -> whne n -> [P ⇊ P₀] -> [hz ⇊ hz₀] -> [hs ⇊ hs₀] -> [n ⇊ t₀] ->
  [tNatElim P hz hs t ⇊ tNatElim P₀ hz₀ hs₀ t₀]
| dbs_empty : [tEmpty ⇊ tEmpty]
| dbs_emptyElim_ne : forall P P₀ t n t₀, [t ↓ n] -> whne n -> [P ⇊ P₀] -> [n ⇊ t₀] -> [tEmptyElim P t ⇊ tEmptyElim P₀ t₀]
| dbs_sig : forall A A₀ B B₀, [A ⇊ A₀] -> [B ⇊ B₀] -> [tSig A B ⇊ tSig A₀ B₀]
| dbs_pair : forall A B a a₀ b b₀, [a ⇊ a₀] -> [b ⇊ b₀] -> [tPair A B a b ⇊ tPair A B a₀ b₀]
| dbs_fst_pair : forall t A B a b r, [t ↓ tPair A B a b] -> [a ⇊ r] -> [tFst t ⇊ r]
| dbs_fst_ne : forall t n t₀, [t ↓ n] -> whne n -> [n ⇊ t₀] -> [tFst t ⇊ tFst t₀]
| dbs_snd_pair : forall t A B a b r, [t ↓ tPair A B a b] -> [b ⇊ r] -> [tSnd t ⇊ r]
| dbs_snd_ne : forall t n t₀, [t ↓ n] -> whne n -> [n ⇊ t₀] -> [tSnd t ⇊ tSnd t₀]
| dbs_id : forall A A₀ t t₀ u u₀, [A ⇊ A₀] -> [t ⇊ t₀] -> [u ⇊ u₀] -> [tId A t u ⇊ tId A₀ t₀ u₀]
| dbs_refl : forall A A₀ t t₀, [A ⇊ A₀] -> [t ⇊ t₀] -> [tRefl A t ⇊ tRefl A₀ t₀]
| dbs_idElim_refl : forall A A₀ x x₀ P hr y e r, [e ↓ tRefl A₀ x₀] -> [hr ⇊ r] -> [tIdElim A x P hr y e ⇊ r]
| dbs_idElim_ne : forall A A₀ x x₀ P P₀ hr hr₀ y y₀ e n e₀, [e ↓ n] -> whne n ->
  [A ⇊ A₀] -> [x ⇊ x₀] -> [P ⇊ P₀] -> [hr ⇊ hr₀] -> [y ⇊ y₀] -> [n ⇊ e₀] -> [tIdElim A x P hr y e ⇊ tIdElim A₀ x₀ P₀ hr₀ y₀ e₀]
| dbs_quote_eval : forall t t₀, [t ⇊ t₀] -> closed0 t₀ -> [tQuote t ⇊ qNat (model.(quote) (erase t₀))]
| dbs_quote_ne : forall t t₀, [t ⇊ t₀] -> ~ closed0 t₀ -> [tQuote t ⇊ tQuote t₀]
| dbs_step_eval : forall t t₀ u u₀ n k k',
  [t ⇊ t₀] -> [u ⇊ qNat u₀] -> closed0 t₀ ->
  murec (fun k => eval true (tApp (erase t₀) (qNat u₀)) k) k = Some (k', qNat n) ->
  [tStep t u ⇊ qNat k']
| dbs_step_ne : forall t t₀ u u₀,
  [t ⇊ t₀] -> [u ⇊ u₀] -> (~ closed0 t₀) + (~ closed0 u₀) ->
  [tStep t u ⇊ tStep t₀ u₀]
| dbs_reflect_eval : forall t t₀ u u₀ n k k',
  [t ⇊ t₀] -> [u ⇊ qNat u₀] -> closed0 t₀ ->
  murec (fun k => eval true (tApp (erase t₀) (qNat u₀)) k) k = Some (k', qNat n) ->
  [tReflect t u ⇊ qEvalTm k' n]
| dbs_reflect_ne : forall t t₀ u u₀,
  [t ⇊ t₀] -> [u ⇊ u₀] -> (~ closed0 t₀) + (~ closed0 u₀) ->
  [tReflect t u ⇊ tReflect t₀ u₀]

where "[ t ↓ u ]" := (bigstep false t u)
and "[ t ⇊ u ]" := (bigstep true t u)
.

#[local]
Lemma eval_unfold : forall deep t k,
  eval deep t k = ltac:(
    let T := constr:(
      let murec t := murec (fun k => eval true t k) k in
      let eval deep t := match k with 0 => None | S k => eval deep t k end in
      eval_body eval murec deep t k
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
| H : (if is_closedn 0 ?t && _ then _ else _) = _ |- _ =>
  let b := fresh "b" in
  let Hb := fresh "Hb" in
  remember (is_closedn 0 t) as b eqn:Hb; symmetry in Hb; destruct b; [|apply is_false_not in Hb]; cbn in H
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
+ repeat expandopt.
  erewrite IHk; [|Lia.lia|tea]; cbn [bindopt].
  erewrite IHk; [|Lia.lia|tea]; cbn [bindopt].
  destruct is_closedn; cbn in *; destruct is_closedn; cbn in *; try congruence.
  repeat expandopt; cbn.
  erewrite murec_mon; [..|tea]; [tea|Lia.lia].
+ repeat expandopt.
  erewrite IHk; [|Lia.lia|tea]; cbn [bindopt].
  erewrite IHk; [|Lia.lia|tea]; cbn [bindopt].
  destruct is_closedn; cbn in *; destruct is_closedn; cbn in *; try congruence.
  repeat expandopt; cbn.
  erewrite murec_mon; [..|tea]; [tea|Lia.lia].
Qed.

Lemma eval_mon : forall k k' t r deep, k <= k' -> eval deep t k = Some r -> eval deep t k' = Some r.
Proof.
induction 1.
+ eauto.
+ intros; now eapply eval_S.
Qed.

Lemma bigstep_eval : forall deep t r, bigstep deep t r -> ∑ k, eval deep t k = Some r.
Proof.
assert (Hnc : forall t, ~ closed0 t -> is_closedn 0 t = false).
{ intros; unfold closed0 in *; destruct is_closedn; congruence. }
assert (Hncc : forall t u , (~ closed0 t) + (~ closed0 u) -> is_closedn 0 t && is_closedn 0 u = false).
{ intros ?? []; [now rewrite Hnc|].
  rewrite (Hnc u); [|tea]; destruct is_closedn; reflexivity. }
induction 1.
all: let rec dest accu := match goal with
| H : (∑ k : nat, _) |- _ =>
  let k := fresh "k" in
  destruct H as [k];
  clear H; dest constr:(max k accu)
| H : murec _ ?k = Some _ |- _ => exists (S (max k accu))
| _ => exists (S accu)
end in
try dest 0; rewrite eval_unfold; try reflexivity.
all: repeat (erewrite eval_mon; [..|tea]; [|Lia.lia]; cbn); try reflexivity.
all: try (caseval; inv_whne).
all: try (rewrite whne_is_whne; [|assumption]).
all: repeat (erewrite eval_mon; [..|tea]; [|Lia.lia]; cbn).
all: repeat match goal with H : closed0 _ |- _ => rewrite H; cbn end.
all: repeat rewrite closedn_qNat, !uNat_qNat; cbn.
all: repeat (rewrite Hnc; [|assumption]).
all: repeat (rewrite Hncc; [|assumption]).
all: try (erewrite murec_mon; [..|tea]; [|Lia.lia]; cbn).
all: repeat rewrite !uNat_qNat; cbn.
all: try reflexivity.
Qed.

Lemma eval_bigstep : forall k deep t r, eval deep t k = Some r -> bigstep deep t r.
Proof.
intros k; induction (Wf_nat.lt_wf k) as [k _ IHk].
assert (IH : match k with 0 => unit | S k => forall deep t r, eval deep t k = Some r -> bigstep deep t r end).
{ destruct k; [constructor|]; apply IHk; Lia.lia. }
clear IHk.
intros * Heq; rewrite eval_unfold in Heq; destruct t, deep.
all: try (destruct k; [discriminate Heq|]).
all: repeat expandopt; try caseval; try casenf.
all: repeat expandopt.
all: try (discriminate Heq).
all: repeat casenf.
all: try (injection Heq; intros; subst).
all: try now eauto 10 using bigstep.
all:
  match goal with H : context[uNat ?t] |- _ => remember (uNat t) as n; destruct n; [|discriminate Heq]; cbn in * end;
  match goal with H : context[murec ?f ?k] |- _ => remember (murec f k) as v; destruct v as [[]|]; [|discriminate Heq]; cbn in * end;
  match goal with H : context[uNat ?t] |- _ => remember (uNat t) as m; destruct m; [|discriminate Heq]; cbn in * end;
  symmetry in Heqm, Heqn; apply qNat_uNat in Heqm, Heqn; subst;
  injection Heq; intros; subst;
  eauto using bigstep.
Qed.

Lemma dnf_qNat : forall n, dnf (qNat n).
Proof.
induction n; constructor; eauto.
Qed.

Lemma dnf_qEvalTy : forall n v, dnf (qEvalTy n v).
Proof.
induction n; intros; cbn in *; unfold tAnd; eauto using dnf, dnf_qNat, dnf_ren.
Qed.

Lemma dnf_qEvalTm : forall n v, dnf (qEvalTm n v).
Proof.
induction n; intros; cbn in *; eauto using dnf, dnf_qNat, dnf_qEvalTy.
Qed.

Lemma dnf_dne_bigstep : (forall t, dnf t -> forall deep, bigstep deep t t) × (forall t, dne t -> forall deep, bigstep deep t t).
Proof.
apply dnf_dne_rect; cbn; intros.
all: destruct deep; eauto 10 using bigstep, dne_whne.
Qed.

Lemma dnf_bigstep : forall t deep, dnf t -> bigstep deep t t.
Proof.
intros; destruct dnf_dne_bigstep as [p _]; now eapply p.
Qed.

Lemma dne_bigstep : forall t deep, dne t -> bigstep deep t t.
Proof.
intros; destruct dnf_dne_bigstep as [_ p]; now eapply p.
Qed.

Lemma dnf_eval : forall t deep, dnf t -> ∑ k, eval deep t k = Some t.
Proof.
intros; now apply bigstep_eval, dnf_bigstep.
Qed.

Lemma whne_bigstep : forall t, whne t -> bigstep false t t.
Proof.
induction 1; cbn; intros; eauto using bigstep, dnf_bigstep.
Qed.

Lemma whne_eval : forall t, whne t -> ∑ k, eval false t k = Some t.
Proof.
intros; now apply bigstep_eval, whne_bigstep.
Qed.

Lemma whnf_bigstep : forall t, whnf t -> bigstep false t t.
Proof.
induction 1; eauto using bigstep, whne_bigstep.
Qed.

Lemma whnf_eval : forall t, whnf t -> ∑ k, eval false t k = Some t.
Proof.
intros; now apply bigstep_eval, whnf_bigstep.
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

Lemma bigstep_det : forall deep t u1 u2, bigstep deep t u1 -> bigstep deep t u2 -> u1 = u2.
Proof.
intros * Hl Hr.
apply bigstep_eval in Hl, Hr.
destruct Hl, Hr; now eapply eval_det.
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

Lemma bigstep_dnf_det : forall t r deep, dnf t -> bigstep deep t r -> t = r.
Proof.
intros * Ht Hr.
eapply bigstep_det; tea.
now apply dnf_bigstep.
Qed.

Lemma bigstep_whnf_det : forall t r, whnf t -> bigstep false t r -> t = r.
Proof.
intros * Ht Hr.
eapply bigstep_det; tea.
now apply whnf_bigstep.
Qed.

Lemma bigstep_nf : forall deep t r, bigstep deep t r ->
  (whne t -> whne r) × (if deep then dnf r else whnf r).
Proof.
induction 1; repeat match goal with H : _ × _ |- _ => destruct H end; split.
all: eauto 6 using dne, dnf, whne, whnf, dnf_qNat, dnf_qEvalTm, dnf_whnf.
all: eauto 12 using whne, whnf, dnf, dne, dne_dnf_whne.
all: try now (intros; inv_whne).
all: inversion 1; subst; eauto.
all: try now match goal with H : (?T -> whne _) |- _ =>
      let H' := fresh in unshelve epose (H' := H _); [now eauto|inversion H']
     end.
all: exfalso; repeat match goal with H : [?t ⇊ ?r] |- _ => assert (t = r) by (eauto using bigstep_dnf_det, dnf_qNat); subst; clear H end.
all: try contradiction.
all: match goal with H : _ + _ |- _ => destruct H as [H|H]; [now eauto|]; elim H; apply closedn_qNat end.
Qed.

Lemma bigstep_dnf : forall t r, bigstep true t r -> dnf r.
Proof.
now apply bigstep_nf.
Qed.

Lemma bigstep_whnf : forall t r, bigstep false t r -> whnf r.
Proof.
now apply bigstep_nf.
Qed.

Lemma bigstep_whne_dne : forall t r, bigstep true t r -> whne t -> dne r.
Proof.
intros; apply dne_dnf_whne.
+ now eapply bigstep_dnf.
+ now eapply bigstep_nf.
Qed.

Lemma eval_dnf : forall k t r, eval true t k = Some r -> dnf r.
Proof.
intros; now eapply bigstep_dnf, eval_bigstep.
Qed.

Lemma eval_whne_dne : forall k t r, eval true t k = Some r -> whne t -> dne r.
Proof.
intros; eauto using bigstep_whne_dne, eval_bigstep.
Qed.

Lemma eval_whnf : forall k t r, eval false t k = Some r -> whnf r.
Proof.
intros; now eapply bigstep_whnf, eval_bigstep.
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
| termStepAlg {t u n k k'} :
  dnf t ->
  closed0 t ->
  murec (fun k => eval true (tApp (erase t) (qNat u)) k) k = Some (k', qNat n) ->
  [ tStep t (qNat u) ⤳ qNat k' ]
| termReflectAlg {t u n k k'} :
  dnf t ->
  closed0 t ->
  murec (fun k => eval true (tApp (erase t) (qNat u)) k) k = Some (k', qNat n) ->
  [ tReflect t (qNat u) ⤳ qEvalTm k' n ]

(* Hereditary normal forms *)

| prodDom {A A' B} : deep ->
  [ A ⤳ A' ] -> [ tProd A B ⤳ tProd A' B ]
| prodCod {A B B'} : deep ->
  dnf A -> [ B ⤳ B' ] -> [ tProd A B ⤳ tProd A B' ]
| lamBody {A t t'} : deep ->
  [ t ⤳ t' ] -> [ tLambda A t ⤳ tLambda A t' ]
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
| pairFst {A B a a' b} : deep ->
  [ a ⤳ a' ] -> [ tPair A B a b ⤳ tPair A B a' b ]
| pairSnd {A B a b b'} : deep ->
  dnf a ->
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
| stepHead {t t' u} :
  @OneRedAlg true t t' ->
  [ tStep t u ⤳ tStep t' u ]
| stepFun {t u u'} :
  dnf t ->
  @OneRedAlg true u u' ->
  [ tStep t u ⤳ tStep t u' ]
| reflectHead {t t' u} :
  @OneRedAlg true t t' ->
  [ tReflect t u ⤳ tReflect t' u ]
| reflectFun {t u u'} :
  dnf t ->
  @OneRedAlg true u u' ->
  [ tReflect t u ⤳ tReflect t u' ]

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

Lemma gred_trans : forall deep t u r, @RedClosureAlg deep t u -> @RedClosureAlg deep u r -> @RedClosureAlg deep t r.
Proof.
intros deep t u r Hl; revert r.
induction Hl; intros; eauto using @RedClosureAlg.
Qed.

#[export] Instance RedAlgTrans {deep} : PreOrder (@RedClosureAlg deep).
  Proof.
    split.
    - now econstructor.
    - intros ??? **; now eapply gred_trans.
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
all: try match goal with H : dne _ |- _ => solve [inversion H] end.
+ destruct s as [|s]; [congruence|elim s; apply closedn_qNat].
+ destruct s as [|s]; [congruence|elim s; apply closedn_qNat].
Qed.

Lemma dnf_dne_nored :
  (forall t, dnf t -> forall u, [t ⇶ u] -> False) × (forall n, dne n -> forall u, [n ⇶ u] -> False).
Proof.
apply dnf_dne_rect; intros.
all: match goal with
| H : [_ ⇶ _] |- _ => inversion H; subst
end; try now eauto using dred_ored.
all: try match goal with H : dne _ |- _ => solve [inversion H] end.
+ destruct s as [|s]; [congruence|elim s; apply closedn_qNat].
+ destruct s as [|s]; [congruence|elim s; apply closedn_qNat].
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
  - destruct H1 as [|s]; [contradiction|elim s; apply closedn_qNat].
  - destruct H1 as [|s]; [contradiction|elim s; apply closedn_qNat].
  - now eelim dnf_nored.
  - eelim dnf_nored; [|tea]; tea.
  - eelim dnf_nored; [|tea]; tea.
  - eelim dnf_nored; [|tea]; tea.
  - eelim dnf_nored; [|tea]; tea.
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
    destruct H2 as [|s]; [contradiction|elim s; apply closedn_qNat].
  - inversion H; subst.
    destruct H2 as [|s]; [contradiction|elim s; apply closedn_qNat].
  - inversion H; subst.
    now eelim dnf_nored.
  - inversion H; subst.
    eelim dnf_nored; [|tea]; tea.
  - inversion H; subst.
    eelim dnf_nored; [|tea]; tea.
  - inversion H; subst.
    eelim dnf_nored; [|tea]; tea.
  - inversion H; subst.
    eelim dnf_nored; [|tea]; tea.
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
+ match goal with
  | H : qNat ?t = qNat ?u |- _ =>
    assert (t = u) by (now eapply qNat_inj); subst
  end.
  match goal with
  | H : (murec _ _ = Some ?r), H' : (murec _ _ = Some ?r') |- _ =>
    assert (r = r') by (now eapply murec_det); f_equal; congruence
  end.
+ eelim dnf_nored; [apply dnf_qNat|tea].
+ match goal with
  | H : qNat ?t = qNat ?u |- _ =>
    assert (t = u) by (now eapply qNat_inj); subst
  end.
  match goal with
  | H : (murec _ _ = Some ?r), H' : (murec _ _ = Some ?r') |- _ =>
    assert (r = r') by (now eapply murec_det); f_equal; [congruence|apply qNat_inj; congruence]
  end.
+ eelim dnf_nored; [apply dnf_qNat|tea].
+ eelim dnf_nored; [apply dnf_qNat|tea].
+ eelim dnf_nored; [apply dnf_qNat|tea].
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
induction Ht; intros ? Hr; inversion Hr; subst; first [constructor; now eauto using dred_ored|now inv_whne|idtac].
+ contradiction.
+ now eelim dnf_nored.
+ destruct s as [|s]; [contradiction|elim s; apply closedn_qNat].
+ eelim dnf_nored; [|tea]; tea.
+ eelim dnf_nored; [|tea]; tea.
+ destruct s as [|s]; [contradiction|elim s; apply closedn_qNat].
+ eelim dnf_nored; [|tea]; tea.
+ eelim dnf_nored; [|tea]; tea.
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
+ rewrite qNat_ren, qNat_ren.
  econstructor; eauto using dnf_ren, closed0_ren.
  rewrite erase_is_closed0_ren_id; tea.
+ rewrite qEvalTm_ren, qNat_ren.
  econstructor; eauto using dnf_ren, closed0_ren.
  rewrite erase_is_closed0_ren_id; tea.
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

Lemma redalg_succ_inv : forall t u, [tSucc t ⇶* tSucc u] -> [t ⇶* u].
Proof.
intros t u Hr.
remember (tSucc t) as t₀ eqn:Ht;
remember (tSucc u) as u₀ eqn:Hu;
revert t u Ht Hu; induction Hr.
+ intros; subst; injection Hu; intros; subst; reflexivity.
+ intros; subst; inversion o; subst.
  econstructor; [tea|eauto].
Qed.

Lemma dred_ren_inv : forall t u ρ, ren_inj ρ -> [t⟨ρ⟩ ⇶ u⟨ρ⟩] -> [t ⇶ u].
Proof.
intros t u ρ Hρ Hr.
remember t⟨ρ⟩ as t' eqn:Ht.
remember u⟨ρ⟩ as u' eqn:Hu.
revert t u ρ Ht Hu Hρ; induction Hr; intros t₀ u₀ ρ Ht Hu Hρ.
all: repeat match goal with H : ?l = ?t⟨?ρ⟩ |- _ =>
(*   lazymatch l with qTotal _ _ _ _ => fail | _ => idtac end; *)
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
+ rewrite <- (qNat_ren _ ρ) in Hu; apply ren_inj_inv in Hu; tea.
  rewrite <- (qNat_ren _ ρ) in H; apply ren_inj_inv in H; tea.
  rewrite <- Hu, <- H.
  eapply termStepAlg; eauto using dnf_ren_rev, closed0_ren_rev.
  rewrite <- (erase_is_closed0_ren_id _ ρ); eauto using closed0_ren_rev.
+ rewrite <- (qEvalTm_ren _ _ ρ) in Hu; apply ren_inj_inv in Hu; tea.
  rewrite <- (qNat_ren _ ρ) in H; apply ren_inj_inv in H; tea.
  rewrite <- Hu, <- H.
  eapply termReflectAlg; eauto using dnf_ren_rev, closed0_ren_rev.
  rewrite <- (erase_is_closed0_ren_id _ ρ); eauto using closed0_ren_rev.
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
+ eexists (qNat _); symmetry; eapply qNat_ren.
+ eexists (qEvalTm _ _); symmetry; apply qEvalTm_ren.
+ eexists (tQuote _); reflexivity.
+ eexists (tStep _ _); reflexivity.
+ eexists (tStep _ _); reflexivity.
+ eexists (tReflect _ _); reflexivity.
+ eexists (tReflect _ _); reflexivity.
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

Lemma redalg_succ_adj : forall t u, [tSucc t ⇶* u] -> ∑ u₀, u = tSucc u₀.
Proof.
intros t u Hr.
remember (tSucc t) as t₀ eqn:Ht; revert t Ht; induction Hr.
+ intros; subst; now eexists.
+ intros; subst; inversion o; subst.
  eapply IHHr; reflexivity.
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

Lemma redalg_step {t t' u u'} : [t ⇶* t'] -> dnf t' -> [u ⇶* u'] -> [tStep t u ⤳* tStep t' u'].
Proof.
intros; transitivity (tStep t' u).
+ induction H; [reflexivity|].
  econstructor; [|eauto].
  now constructor.
+ clear - H0 H1.
 induction H1; [reflexivity|].
  econstructor; [|tea].
  now constructor.
Qed.

Lemma redalg_reflect {t t' u u'} : [t ⇶* t'] -> dnf t' -> [u ⇶* u'] -> [tReflect t u ⤳* tReflect t' u'].
Proof.
intros; transitivity (tReflect t' u).
+ induction H; [reflexivity|].
  econstructor; [|eauto].
  now constructor.
+ clear - H0 H1.
 induction H1; [reflexivity|].
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

Lemma dredalg_lambda : forall A t t₀,
  [t ⇶* t₀] -> [tLambda A t ⇶* tLambda A t₀].
Proof.
intros A t t₀ HRt.
induction HRt.
- constructor.
- econstructor; [|now eauto].
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

Lemma dredalg_pair : forall A B a a₀ b b₀,
  [a ⇶* a₀] -> dnf a₀ -> [b ⇶* b₀] -> dnf b₀ ->
  [tPair A B a b ⇶* tPair A B a₀ b₀].
Proof.
intros A B a a₀ b b₀ HRa Ha HRb Hb.
transitivity (tPair A B a₀ b).
- clear - HRa; induction HRa.
  * constructor.
  * econstructor; [|now eauto].
    now constructor.
- clear - Ha HRb; induction HRb.
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
intros t u n Hr; revert n; induction Hr; intros ? Hc; cbn in *.
all: repeat match goal with H : _ |- _ => apply andb_prop in H; destruct H end.
all: repeat (apply andb_true_intro; split); tea.
all: try match goal with H : forall n : nat, _ |- _ => now apply H end.
+ now apply closedn_beta.
+ apply closedn_qNat.
+ apply closedn_qNat.
+ apply closedn_qEvalTm.
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

Lemma dred_bigstep : forall deep t u r, OneRedAlg (deep := deep) t u ->
  bigstep deep u r -> bigstep deep t r.
Proof.
intros deep t u r Hr; revert r.
induction Hr; try intros r Heval; cbn.
all: try (destruct deep; [|discriminate]).
all: try now (inversion Heval; subst; eauto using bigstep, whnf, whne).
+ apply bigstep_dnf_det in Heval; [subst|apply dnf_qNat]; destruct deep; eauto using bigstep, dnf_bigstep.
+ apply bigstep_dnf_det in Heval; [subst|apply dnf_qNat]; destruct deep; eauto using bigstep, dnf_bigstep, dnf_qNat.
+ apply bigstep_dnf_det in Heval; [subst|apply dnf_qEvalTm]; destruct deep; eauto using bigstep, dnf_bigstep, dnf_qNat.
+ assert (Ht' : whne t') by now eapply dred_whne.
  inversion Heval; subst.
  - eapply bigstep_nf in Ht'; [|tea]; now inv_whne.
  - assert (t' = n) by eauto using bigstep_whnf_det, whne, whnf; subst.
    eauto using bigstep, whnf_bigstep, whnf, whne.
+ inversion Heval; subst.
  - apply bigstep_whnf_det in H1; [subst; inversion d|eauto using dnf, dne, dnf_whnf].
  - eauto using bigstep.
+ assert (Hn' : whne n') by now eapply dred_whne.
  inversion Heval; subst.
  - eapply bigstep_nf in Hn'; [|tea]; now inv_whne.
  - eapply bigstep_nf in Hn'; [|tea]; now inv_whne.
  - assert (n' = n0) by eauto using bigstep_whnf_det, whne, whnf; subst.
    eauto using bigstep, whnf_bigstep, whnf, whne.
+ inversion Heval; subst.
  - apply bigstep_whnf_det in H4; [subst; inversion d|eauto using dnf, dne, dnf_whnf].
  - apply bigstep_whnf_det in H4; [subst; inversion d|eauto using dnf, dne, dnf_whnf].
  - eauto using bigstep.
+ inversion Heval; subst.
  - apply bigstep_whnf_det in H4; [subst; inversion d|eauto using dnf, dne, dnf_whnf].
  - apply bigstep_whnf_det in H4; [subst; inversion d|eauto using dnf, dne, dnf_whnf].
  - eauto using bigstep.
+ inversion Heval; subst.
  - apply bigstep_whnf_det in H4; [subst; inversion d|eauto using dnf, dne, dnf_whnf].
  - apply bigstep_whnf_det in H4; [subst; inversion d|eauto using dnf, dne, dnf_whnf].
  - eauto using bigstep.
+ assert (Hn' : whne n') by now eapply dred_whne.
  inversion Heval; subst.
  assert (n' = n0) by eauto using bigstep_whnf_det, whne, whnf; subst.
  eauto using bigstep, whnf_bigstep, whnf, whne.
+ assert (Hn' : whne n') by now eapply dred_whne.
  inversion Heval; subst.
  - eapply bigstep_nf in Hn'; [|tea]; now inv_whne.
  - assert (n' = n0) by eauto using bigstep_whnf_det, whne, whnf; subst.
    eauto using bigstep, whnf_bigstep, whnf, whne.
+ assert (Hn' : whne n') by now eapply dred_whne.
  inversion Heval; subst.
  - eapply bigstep_nf in Hn'; [|tea]; now inv_whne.
  - assert (n' = n0) by eauto using bigstep_whnf_det, whne, whnf; subst.
    eauto using bigstep, whnf_bigstep, whnf, whne.
+ assert (He' : whne e') by now eapply dred_whne.
  inversion Heval; subst.
  - eapply bigstep_nf in He'; [|tea]; now inv_whne.
  - assert (e' = n) by eauto using bigstep_whnf_det, whne, whnf; subst.
    eauto using bigstep, whnf_bigstep, whnf, whne.
Qed.

Lemma dredalg_bigstep : forall t r, [t ⇶* r] -> dnf r -> bigstep true t r.
Proof.
induction 1; intros.
+ now apply dnf_bigstep.
+ now eapply dred_bigstep.
Qed.

Lemma redalg_bigstep : forall t r, [t ⤳* r] -> whnf r ->  bigstep false t r.
Proof.
induction 1; intros.
+ now apply whnf_bigstep.
+ now eapply dred_bigstep.
Qed.

Lemma dredalg_eval : forall t r, [t ⇶* r] -> dnf r ->
  ∑ k, eval true t k = Some r.
Proof.
intros; now apply bigstep_eval, dredalg_bigstep.
Qed.

Lemma redalg_eval : forall t r, [t ⤳* r] -> whnf r ->
  ∑ k, eval false t k = Some r.
Proof.
intros; now apply bigstep_eval, redalg_bigstep.
Qed.

Lemma bigstep_dredalg : forall deep t r, bigstep deep t r -> RedClosureAlg (deep := deep) t r.
Proof.
induction 1; eauto using @RedClosureAlg, @OneRedAlg, gred_trans, gred_red,
  redalg_app, redalg_natElim, redalg_natEmpty, redalg_fst, redalg_snd, redalg_idElim,
  redalg_quote, redalg_step, redalg_reflect,
  dredalg_prod, dredalg_lambda, dredalg_app, dredalg_succ,
  dredalg_sig, dredalg_pair, dredalg_fst, dredalg_snd, dredalg_id, dredalg_refl,
  bigstep_dnf, bigstep_whne_dne.
+ eauto 7 using gred_trans, @OneRedAlg, redalg_quote, bigstep_dnf, redalg_one_step.
+ eauto 7 using gred_trans, @OneRedAlg, redalg_step, bigstep_dnf, redalg_one_step.
+ eauto 7 using gred_trans, @OneRedAlg, redalg_reflect, bigstep_dnf, redalg_one_step.
+ etransitivity; [|apply dredalg_app; eauto using bigstep_dnf, bigstep_whne_dne].
  eauto using gred_red, bigstep_dnf, bigstep_whne_dne, redalg_app.
+ etransitivity; [|apply dredalg_natElim; eauto using bigstep_dnf, bigstep_whne_dne].
  eauto using gred_red, bigstep_dnf, bigstep_whne_dne, redalg_natElim.
+ etransitivity; [|apply dredalg_emptyElim; eauto using bigstep_dnf, bigstep_whne_dne].
  eauto using gred_red, bigstep_dnf, bigstep_whne_dne, redalg_natEmpty.
+ etransitivity; [|apply dredalg_idElim; eauto using bigstep_dnf, bigstep_whne_dne].
  eauto using gred_red, bigstep_dnf, bigstep_whne_dne, redalg_idElim.
+ eauto 7 using gred_red, gred_trans, @OneRedAlg, redalg_quote, bigstep_dnf, redalg_one_step.
+ eauto 8 using gred_red, gred_trans, @OneRedAlg, redalg_step, bigstep_dnf, redalg_one_step.
+ eauto 8 using gred_red, gred_trans, @OneRedAlg, redalg_reflect, bigstep_dnf, redalg_one_step.
Qed.

Lemma eval_dredalg : forall k deep t r, eval deep t k = Some r -> RedClosureAlg (deep := deep) t r.
Proof.
intros; now eapply bigstep_dredalg, eval_bigstep.
Qed.

(** Stability of erasure *)

Lemma gred_unannot_dnf_id : forall deep t u,
  dnf (unannot t) -> @OneRedAlg deep t u -> unannot t = unannot u.
Proof.
intros deep t u Ht Hr; induction Hr; cbn in *.
all: try (inversion Ht; []; subst).
all: try (inversion Ht; [|match goal with H : dne _ |- _ => now inversion H end]; subst).
all: try match goal with H : dne _ |- _ => inversion H; subst end.
all: try rewrite IHHr; eauto using dnf.
all: try match goal with H : dne _ |- _ => now inversion H end.
+ elim H1; unfold closed0; rewrite closedn_unannot; tea.
+ destruct H2 as [H2|H2].
  - elim H2; rewrite closedn_unannot; tea.
  - elim H2; rewrite unannot_qNat; apply closedn_qNat.
+ destruct H2 as [H2|H2].
  - elim H2; rewrite closedn_unannot; tea.
  - elim H2; rewrite unannot_qNat; apply closedn_qNat.
Qed.

Lemma gredalg_unannot_dnf_id : forall deep t u,
  dnf (unannot t) -> @RedClosureAlg deep t u -> unannot t = unannot u.
Proof.
induction 2.
+ reflexivity.
+ apply gred_unannot_dnf_id in o; [|tea].
  etransitivity; [tea|apply IHRedClosureAlg; congruence].
Qed.
