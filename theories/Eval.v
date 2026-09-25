From LogRel Require Import Utils Syntax.All.
From LogRel Require Import GenericTyping.

Axiom quote : term -> nat.
Axiom quote_inj : forall t u, quote t = quote u -> t = u.

Axiom tRun : term.

Axiom tRun_None : forall t k,
  eval true t k = None ->
  [tApp (tApp tRun (qNat (quote t))) (qNat k) ⇶* tZero].

Axiom tRun_Some : forall t v k,
  eval true t k = Some v ->
  [tApp (tApp tRun (qNat (quote t))) (qNat k) ⇶* tSucc (qNat (quote v))].

Section Wf.

Context `{GenericTypingProperties}.

Axiom ty_run : [ nil |- tRun : tProd tNat (tProd tNat tNat) ].

End Wf.
