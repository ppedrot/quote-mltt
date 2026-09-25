(** * LogRel.Syntax.Quote: a Gödel numbering of terms and an internal evaluator.

  This file only contains definitions: the Gödel numbering [quote] of terms,
  and the System T term [tRun] such that [tRun (quote t) k] computes
  [eval true t k]. The specification and the correctness proofs are in
  [LogRel.Eval]. *)
From Stdlib Require Import List.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst.

(* The autosubst notation [t ..] prevents the use of recursive notations. *)
#[local] Notation "⟪ ⟫" := nil (format "⟪ ⟫").
#[local] Notation "⟪ a ⟫" := (cons a nil).
#[local] Notation "⟪ a ; b ⟫" := (cons a (cons b nil)).
#[local] Notation "⟪ a ; b ; c ⟫" := (cons a (cons b (cons c nil))).
#[local] Notation "⟪ a ; b ; c ; d ⟫" := (cons a (cons b (cons c (cons d nil)))).
#[local] Notation "⟪ a ; b ; c ; d ; e ⟫" := (cons a (cons b (cons c (cons d (cons e nil))))).
#[local] Notation "⟪ a ; b ; c ; d ; e ; f ⟫" := (cons a (cons b (cons c (cons d (cons e (cons f nil)))))).

(** Numerals, duplicated from [qNat] to avoid depending on [Computation].
    Both definitions are convertible. *)
Fixpoint tnum (n : nat) : term := match n with
| 0 => tZero
| S n => tSucc (tnum n)
end.

Fixpoint tri (n : nat) : nat := match n with
| 0 => 0
| S i => S i + tri i
end.

(** Cantor pairing *)
Definition npair (x y : nat) : nat := y + tri (y + x).
Arguments npair : simpl never.

(** Lists of numbers *)
Fixpoint lcode (l : list nat) : nat := match l with
| nil => 0
| x :: l => S (npair x (lcode l))
end.

(** A node of the syntax tree is coded by its tag and its payload. *)
Definition node (tag : nat) (payload : nat) := S (npair tag payload).
Arguments node : simpl never.

Definition tag_of (t : term) : nat := match t with
| tRel _ => 0
| tSort _ => 1
| tProd _ _ => 2
| tLambda _ _ => 3
| tApp _ _ => 4
| tNat => 5
| tZero => 6
| tSucc _ => 7
| tNatElim _ _ _ _ => 8
| tEmpty => 9
| tEmptyElim _ _ => 10
| tSig _ _ => 11
| tPair _ _ _ _ => 12
| tFst _ => 13
| tSnd _ => 14
| tId _ _ _ => 15
| tRefl _ _ => 16
| tIdElim _ _ _ _ _ _ => 17
| tQuote _ => 18
| tStep _ _ => 19
| tReflect _ _ => 20
end.

(** The direct subterms of a term, from left to right. *)
Definition fields (t : term) : list term := match t with
| tRel _ | tSort _ | tNat | tZero | tEmpty => nil
| tProd A B => ⟪A; B⟫
| tLambda A t => ⟪A; t⟫
| tApp t u => ⟪t; u⟫
| tSucc t => ⟪t⟫
| tNatElim P hz hs n => ⟪P; hz; hs; n⟫
| tEmptyElim P e => ⟪P; e⟫
| tSig A B => ⟪A; B⟫
| tPair A B a b => ⟪A; B; a; b⟫
| tFst p => ⟪p⟫
| tSnd p => ⟪p⟫
| tId A x y => ⟪A; x; y⟫
| tRefl A x => ⟪A; x⟫
| tIdElim A x P hr y e => ⟪A; x; P; hr; y; e⟫
| tQuote t => ⟪t⟫
| tStep t u => ⟪t; u⟫
| tReflect t u => ⟪t; u⟫
end.

Fixpoint quote (t : term) : nat := match t with
| tRel n => node 0 n
| tSort _ => node 1 (lcode nil)
| tProd A B => node 2 (lcode ⟪quote A; quote B⟫)
| tLambda A t => node 3 (lcode ⟪quote A; quote t⟫)
| tApp t u => node 4 (lcode ⟪quote t; quote u⟫)
| tNat => node 5 (lcode nil)
| tZero => node 6 (lcode nil)
| tSucc t => node 7 (lcode ⟪quote t⟫)
| tNatElim P hz hs n => node 8 (lcode ⟪quote P; quote hz; quote hs; quote n⟫)
| tEmpty => node 9 (lcode nil)
| tEmptyElim P e => node 10 (lcode ⟪quote P; quote e⟫)
| tSig A B => node 11 (lcode ⟪quote A; quote B⟫)
| tPair A B a b => node 12 (lcode ⟪quote A; quote B; quote a; quote b⟫)
| tFst p => node 13 (lcode ⟪quote p⟫)
| tSnd p => node 14 (lcode ⟪quote p⟫)
| tId A x y => node 15 (lcode ⟪quote A; quote x; quote y⟫)
| tRefl A x => node 16 (lcode ⟪quote A; quote x⟫)
| tIdElim A x P hr y e =>
  node 17 (lcode ⟪quote A; quote x; quote P; quote hr; quote y; quote e⟫)
| tQuote t => node 18 (lcode ⟪quote t⟫)
| tStep t u => node 19 (lcode ⟪quote t; quote u⟫)
| tReflect t u => node 20 (lcode ⟪quote t; quote u⟫)
end.

(** Simple types *)
Inductive ty := N | Arr (A B : ty).

Fixpoint ety (T : ty) : term := match T with
| N => tNat
| Arr A B => arr (ety A) (ety B)
end.

Fixpoint lams (As : list term) (b : term) : term := match As with
| nil => b
| cons A As => tLambda A (lams As b)
end.

Fixpoint apps (t : term) (us : list term) : term := match us with
| nil => t
| cons u us => apps (tApp t u) us
end.

(** [λ x _ _. x] *)
Definition cConstS (T : ty) := lams ⟪ety T; tNat; ety T⟫ (tRel 2).
Arguments cConstS : simpl never.

(** [if n = 0 then a else b] *)
Definition cIfz (T : ty) :=
  lams ⟪tNat; ety T; ety T⟫ (tNatElim (ety T)⟨↑⟩ (tRel 1) (apps (cConstS T) ⟪tRel 0⟫) (tRel 2)).
Arguments cIfz : simpl never.

(** [λ _ r. S r] *)
Definition cSuccS := lams ⟪tNat; tNat⟫ (tSucc (tRel 0)).
Arguments cSuccS : simpl never.

(** [λ i _. i] *)
Definition cProjS := lams ⟪tNat; tNat⟫ (tRel 1).
Arguments cProjS : simpl never.

Definition cAdd := lams ⟪tNat; tNat⟫ (tNatElim tNat (tRel 0) cSuccS (tRel 1)).
Arguments cAdd : simpl never.

Definition cPred := lams ⟪tNat⟫ (tNatElim tNat tZero cProjS (tRel 0)).
Arguments cPred : simpl never.

(** [λ _ r. pred r] *)
Definition cPredS := lams ⟪tNat; tNat⟫ (apps cPred ⟪tRel 0⟫).
Arguments cPredS : simpl never.

Definition cSub := lams ⟪tNat; tNat⟫ (tNatElim tNat (tRel 1) cPredS (tRel 0)).
Arguments cSub : simpl never.

Definition cEqb := lams ⟪tNat; tNat⟫
  (apps (cIfz N) ⟪apps cAdd ⟪apps cSub ⟪tRel 1; tRel 0⟫; apps cSub ⟪tRel 0; tRel 1⟫⟫; tSucc tZero; tZero⟫).
Arguments cEqb : simpl never.

Definition cLtb := lams ⟪tNat; tNat⟫
  (apps (cIfz N) ⟪apps cSub ⟪tSucc (tRel 1); tRel 0⟫; tSucc tZero; tZero⟫).
Arguments cLtb : simpl never.

Definition cAndb := lams ⟪tNat; tNat⟫ (apps (cIfz N) ⟪tRel 1; tZero; tRel 0⟫).
Arguments cAndb : simpl never.

Definition cOrb := lams ⟪tNat; tNat⟫ (apps (cIfz N) ⟪tRel 1; tRel 0; tSucc tZero⟫).
Arguments cOrb : simpl never.

Definition cNegb := lams ⟪tNat⟫ (apps (cIfz N) ⟪tRel 0; tSucc tZero; tZero⟫).
Arguments cNegb : simpl never.

(** [λ i m. S i + m] *)
Definition cTriS := lams ⟪tNat; tNat⟫ (apps cAdd ⟪tSucc (tRel 1); tRel 0⟫).
Arguments cTriS : simpl never.

Definition cTri := lams ⟪tNat⟫ (tNatElim tNat tZero cTriS (tRel 0)).
Arguments cTri : simpl never.

Definition cPair := lams ⟪tNat; tNat⟫
  (apps cAdd ⟪tRel 0; apps cTri ⟪apps cAdd ⟪tRel 0; tRel 1⟫⟫⟫).
Arguments cPair : simpl never.

(** Pairs of numbers represented as functions [0 ↦ x; S _ ↦ y]. *)
Definition cMkp := lams ⟪tNat; tNat; tNat⟫ (apps (cIfz N) ⟪tRel 0; tRel 2; tRel 1⟫).
Arguments cMkp : simpl never.

Definition cUnpS := lams ⟪tNat; ety (Arr N N)⟫
  (apps (cIfz (Arr N N)) ⟪apps (tRel 0) ⟪tZero⟫;
    apps cMkp ⟪tSucc (apps (tRel 0) ⟪tSucc tZero⟫); tZero⟫;
    apps cMkp ⟪apps cPred ⟪apps (tRel 0) ⟪tZero⟫⟫; tSucc (apps (tRel 0) ⟪tSucc tZero⟫)⟫⟫).
Arguments cUnpS : simpl never.

Definition cUnpair := lams ⟪tNat⟫
  (tNatElim (ety (Arr N N))⟨↑⟩ (apps cMkp ⟪tZero; tZero⟫) cUnpS (tRel 0)).
Arguments cUnpair : simpl never.

Definition cFst := lams ⟪tNat⟫ (apps cUnpair ⟪tRel 0; tZero⟫).
Arguments cFst : simpl never.

Definition cSnd := lams ⟪tNat⟫ (apps cUnpair ⟪tRel 0; tSucc tZero⟫).
Arguments cSnd : simpl never.

(** [if b then a else c] *)
Definition cIte (T : ty) := lams ⟪tNat; ety T; ety T⟫ (apps (cIfz T) ⟪tRel 2; tRel 0; tRel 1⟫).
Arguments cIte : simpl never.

(** Case analysis on a small number *)
Fixpoint switch (T : ty) (n : term) (bs : list term) (d : term) : term := match bs with
| nil => d
| cons b bs => apps (cIfz T) ⟪n; b; switch T (apps cPred ⟪n⟫) bs d⟫
end.

(** A default inhabitant of each type *)
Fixpoint dflt (T : ty) : term := match T with
| N => tZero
| Arr A B => tLambda (ety A) (dflt B)
end.

(** [λ alg _ F. alg F] *)
Definition cIgn1 (T : ty) :=
  lams ⟪ety (Arr (Arr N T) (Arr N T)); tNat; ety (Arr N T)⟫ (apps (tRel 2) ⟪tRel 0⟫).
Arguments cIgn1 : simpl never.

(** [cRec alg x] iterates [alg] [S x] times on a dummy function and applies it to [x]. *)
Definition cRec (T : ty) :=
  lams ⟪ety (Arr (Arr N T) (Arr N T)); tNat⟫
    (apps (tNatElim (ety (Arr N T))⟨↑⟩ (dflt (Arr N T)) (apps (cIgn1 T) ⟪tRel 1⟫) (tSucc (tRel 0))) ⟪tRel 0⟫).
Arguments cRec : simpl never.

Definition cCons := lams ⟪tNat; tNat⟫ (tSucc (apps cPair ⟪tRel 1; tRel 0⟫)).
Arguments cCons : simpl never.

Definition cHd := lams ⟪tNat⟫ (apps cFst ⟪apps cPred ⟪tRel 0⟫⟫).
Arguments cHd : simpl never.

Definition cTl := lams ⟪tNat⟫ (apps cSnd ⟪apps cPred ⟪tRel 0⟫⟫).
Arguments cTl : simpl never.

(** [λ _ F l. F (tl l)] *)
Definition cNthS := lams ⟪tNat; ety (Arr N N); tNat⟫ (apps (tRel 1) ⟪apps cTl ⟪tRel 0⟫⟫).
Arguments cNthS : simpl never.

Definition cNth := lams ⟪tNat; tNat⟫
  (apps (tNatElim (ety (Arr N N))⟨↑⟩ cHd cNthS (tRel 1)) ⟪tRel 0⟫).
Arguments cNth : simpl never.

(** [λ g rec l i. if l = 0 then 0 else cons (g i (hd l)) (rec (tl l) (S i))] *)
Definition cMapiAlg := lams ⟪ety (Arr N (Arr N N)); ety (Arr N (Arr N N)); tNat; tNat⟫
  (apps (cIfz N) ⟪tRel 1; tZero;
    apps cCons ⟪apps (tRel 3) ⟪tRel 0; apps cHd ⟪tRel 1⟫⟫; apps (tRel 2) ⟪apps cTl ⟪tRel 1⟫; tSucc (tRel 0)⟫⟫⟫).
Arguments cMapiAlg : simpl never.

Definition cMapi := lams ⟪ety (Arr N (Arr N N)); tNat; tNat⟫
  (apps (cRec (Arr N N)) ⟪apps cMapiAlg ⟪tRel 2⟫; tRel 0; tRel 1⟫).
Arguments cMapi : simpl never.

(** [λ rec l. if l = 0 then 1 else if hd l = 0 then 0 else rec (tl l)] *)
Definition cLAllAlg := lams ⟪ety (Arr N N); tNat⟫
  (apps (cIfz N) ⟪tRel 0; tSucc tZero;
    apps (cIfz N) ⟪apps cHd ⟪tRel 0⟫; tZero; apps (tRel 1) ⟪apps cTl ⟪tRel 0⟫⟫⟫⟫).
Arguments cLAllAlg : simpl never.

Definition cLAll := lams ⟪tNat⟫ (apps (cRec N) ⟪cLAllAlg; tRel 0⟫).
Arguments cLAll : simpl never.

Definition cTable (tab : list nat) := lams ⟪tNat⟫ (switch N (tRel 0) (map tnum tab) tZero).
Arguments cTable : simpl never.

(** Position of the field with binders, if any (6 otherwise). *)
Definition bpos_tab := ⟪6; 6; 1; 1; 6; 6⟫ ++ ⟪6; 6; 0; 6; 0; 1⟫ ++ ⟪1; 6; 6; 6; 6; 2⟫ ++ ⟪6; 6; 6⟫.

(** Number of binders of that field. *)
Definition bcnt_tab := ⟪0; 0; 1; 1; 0; 0⟫ ++ ⟪0; 0; 1; 0; 1; 1⟫ ++ ⟪1; 0; 0; 0; 0; 2⟫ ++ ⟪0; 0; 0⟫.

(** Number of leading fields that are ignored annotations. *)
Definition ignn_tab := ⟪0; 0; 0; 1; 0; 0⟫ ++ ⟪0; 0; 0; 0; 0; 0⟫ ++ ⟪2; 0; 0; 0; 0; 0⟫ ++ ⟪0; 0; 0⟫.

(** Position of the scrutinee of eliminators (6 otherwise). *)
Definition scr_tab := ⟪6; 6; 6; 6; 0; 6⟫ ++ ⟪6; 6; 3; 6; 1; 6⟫ ++ ⟪6; 0; 0; 6; 6; 5⟫ ++ ⟪6; 6; 6⟫.

(** Kind of node: 0 = variable, 1 = canonical form, 2 = eliminator, 3 = quote-like primitive. *)
Definition kind_tab := ⟪0; 1; 1; 1; 2; 1⟫ ++ ⟪1; 1; 2; 1; 2; 1⟫ ++ ⟪1; 2; 2; 1; 1; 2⟫ ++ ⟪3; 3; 3⟫.

Definition cBnd := lams ⟪tNat; tNat⟫
  (apps (cIte N) ⟪apps cEqb ⟪tRel 0; apps (cTable bpos_tab) ⟪tRel 1⟫⟫; apps (cTable bcnt_tab) ⟪tRel 1⟫; tZero⟫).
Arguments cBnd : simpl never.

Definition cIgn := lams ⟪tNat; tNat⟫ (apps cLtb ⟪tRel 0; apps (cTable ignn_tab) ⟪tRel 1⟫⟫).
Arguments cIgn : simpl never.

(** [λ rec x p i y. rec y (bnd (tag x) i + p)] *)
Definition cBindF := lams ⟪ety (Arr N (Arr N N)); tNat; tNat; tNat; tNat⟫
  (apps (tRel 4) ⟪tRel 0; apps cAdd ⟪apps cBnd ⟪apps cHd ⟪tRel 3⟫; tRel 1⟫; tRel 2⟫⟫).
Arguments cBindF : simpl never.

(** [λ rec x c. if tag x = 0 then var (if n < c then n else S n) else node (tag x) (mapi (λ i y. rec y (bnd i + c)) (fields x))] *)
Definition cShiftAlg := lams ⟪ety (Arr N (Arr N N)); tNat; tNat⟫
  (apps (cIfz N) ⟪apps cHd ⟪tRel 1⟫;
    apps cCons ⟪tZero; apps (cIte N) ⟪apps cLtb ⟪apps cTl ⟪tRel 1⟫; tRel 0⟫; apps cTl ⟪tRel 1⟫; tSucc (apps cTl ⟪tRel 1⟫)⟫⟫;
    apps cCons ⟪apps cHd ⟪tRel 1⟫; apps cMapi ⟪apps cBindF ⟪tRel 2; tRel 1; tRel 0⟫; tZero; apps cTl ⟪tRel 1⟫⟫⟫⟫).
Arguments cShiftAlg : simpl never.

Definition cShift := lams ⟪tNat; tNat⟫ (apps (cRec (Arr N N)) ⟪cShiftAlg; tRel 1; tRel 0⟫).
Arguments cShift : simpl never.

(** [λ _ r. shift r 0] *)
Definition cShiftNS := lams ⟪tNat; tNat⟫ (apps cShift ⟪tRel 0; tZero⟫).
Arguments cShiftNS : simpl never.

(** [λ k u. shiftᵏ u] *)
Definition cShiftN := lams ⟪tNat; tNat⟫ (tNatElim tNat (tRel 0) cShiftNS (tRel 1)).
Arguments cShiftN : simpl never.

(** [λ u rec x k. if tag x = 0 then (subst var) else node (tag x) (mapi (λ i y. rec y (bnd i + k)) (fields x))] *)
Definition cSubstAlg := lams ⟪tNat; ety (Arr N (Arr N N)); tNat; tNat⟫
  (apps (cIfz N) ⟪apps cHd ⟪tRel 1⟫;
    apps (cIte N) ⟪apps cLtb ⟪apps cTl ⟪tRel 1⟫; tRel 0⟫; apps cCons ⟪tZero; apps cTl ⟪tRel 1⟫⟫;
      apps (cIte N) ⟪apps cEqb ⟪apps cTl ⟪tRel 1⟫; tRel 0⟫; apps cShiftN ⟪tRel 0; tRel 3⟫;
        apps cCons ⟪tZero; apps cPred ⟪apps cTl ⟪tRel 1⟫⟫⟫⟫⟫;
    apps cCons ⟪apps cHd ⟪tRel 1⟫; apps cMapi ⟪apps cBindF ⟪tRel 2; tRel 1; tRel 0⟫; tZero; apps cTl ⟪tRel 1⟫⟫⟫⟫).
Arguments cSubstAlg : simpl never.

(** [λ k u t. t[⇑ᵏ u..]] *)
Definition cSubst := lams ⟪tNat; tNat; tNat⟫
  (apps (cRec (Arr N N)) ⟪apps cSubstAlg ⟪tRel 1⟫; tRel 0; tRel 2⟫).
Arguments cSubst : simpl never.

(** [λ rec x n. if tag x = 0 then ¬ (var x = n) else all (mapi (λ i y. rec y (bnd i + n)) (fields x))] *)
Definition cNoccAlg := lams ⟪ety (Arr N (Arr N N)); tNat; tNat⟫
  (apps (cIfz N) ⟪apps cHd ⟪tRel 1⟫;
    apps cNegb ⟪apps cEqb ⟪apps cTl ⟪tRel 1⟫; tRel 0⟫⟫;
    apps cLAll ⟪apps cMapi ⟪apps cBindF ⟪tRel 2; tRel 1; tRel 0⟫; tZero; apps cTl ⟪tRel 1⟫⟫⟫⟫).
Arguments cNoccAlg : simpl never.

Definition cNocc := lams ⟪tNat; tNat⟫ (apps (cRec (Arr N N)) ⟪cNoccAlg; tRel 1; tRel 0⟫).
Arguments cNocc : simpl never.

(** [λ rec x p i y. ign (tag x) i || rec y (bnd (tag x) i + p)] *)
Definition cClosF := lams ⟪ety (Arr N (Arr N N)); tNat; tNat; tNat; tNat⟫
  (apps cOrb ⟪apps cIgn ⟪apps cHd ⟪tRel 3⟫; tRel 1⟫;
    apps (tRel 4) ⟪tRel 0; apps cAdd ⟪apps cBnd ⟪apps cHd ⟪tRel 3⟫; tRel 1⟫; tRel 2⟫⟫⟫).
Arguments cClosF : simpl never.

(** [λ rec x n. if tag x = 0 then var x < n else all (mapi (λ i y. ign i || rec y (bnd i + n)) (fields x))] *)
Definition cClosAlg := lams ⟪ety (Arr N (Arr N N)); tNat; tNat⟫
  (apps (cIfz N) ⟪apps cHd ⟪tRel 1⟫;
    apps cLtb ⟪apps cTl ⟪tRel 1⟫; tRel 0⟫;
    apps cLAll ⟪apps cMapi ⟪apps cClosF ⟪tRel 2; tRel 1; tRel 0⟫; tZero; apps cTl ⟪tRel 1⟫⟫⟫⟫).
Arguments cClosAlg : simpl never.

Definition cClosed := lams ⟪tNat; tNat⟫ (apps (cRec (Arr N N)) ⟪cClosAlg; tRel 1; tRel 0⟫).
Arguments cClosed : simpl never.

(** [λ _ y. closed₀ y] *)
Definition cClos0F := lams ⟪tNat; tNat⟫ (apps cClosed ⟪tRel 0; tZero⟫).
Arguments cClos0F : simpl never.

(** [λ rec x i y. ign (tag x) i || rec y (i = scr (tag x))] *)
Definition cNfF := lams ⟪ety (Arr N (Arr N N)); tNat; tNat; tNat⟫
  (apps cOrb ⟪apps cIgn ⟪apps cHd ⟪tRel 2⟫; tRel 1⟫;
    apps (tRel 3) ⟪tRel 0; apps cEqb ⟪tRel 1; apps (cTable scr_tab) ⟪apps cHd ⟪tRel 2⟫⟫⟫⟫⟫).
Arguments cNfF : simpl never.

Definition cNfAlg := lams ⟪ety (Arr N (Arr N N)); tNat; tNat⟫
  (apps (cIfz N) ⟪apps cHd ⟪tRel 1⟫; tSucc tZero;
    apps cAndb ⟪apps cAndb ⟪
      apps cOrb ⟪apps cNegb ⟪apps cEqb ⟪apps (cTable kind_tab) ⟪apps cHd ⟪tRel 1⟫⟫; tSucc tZero⟫⟫;
                 apps cNegb ⟪apps cEqb ⟪tRel 0; tSucc tZero⟫⟫⟫;
      apps cLAll ⟪apps cMapi ⟪apps cNfF ⟪tRel 2; tRel 1⟫; tZero; apps cTl ⟪tRel 1⟫⟫⟫⟫;
      apps cOrb ⟪apps cNegb ⟪apps cEqb ⟪apps (cTable kind_tab) ⟪apps cHd ⟪tRel 1⟫⟫; tnum 3⟫⟫;
                 apps cNegb ⟪apps cLAll ⟪apps cMapi ⟪cClos0F; tZero; apps cTl ⟪tRel 1⟫⟫⟫⟫⟫⟫⟫).
Arguments cNfAlg : simpl never.

(** [cNf t p] decides [is_nf (p = 1) t] *)
Definition cNf := lams ⟪tNat; tNat⟫ (apps (cRec (Arr N N)) ⟪cNfAlg; tRel 1; tRel 0⟫).
Arguments cNf : simpl never.

(** [λ _ y. dnf y] *)
Definition cDnfF := lams ⟪tNat; tNat⟫ (apps cNf ⟪tRel 0; tZero⟫).
Arguments cDnfF : simpl never.

Definition cWhneAlg := lams ⟪ety (Arr N N); tNat⟫
  (apps (cIfz N) ⟪apps cHd ⟪tRel 0⟫; tSucc tZero;
    apps (cIte N) ⟪apps cEqb ⟪apps (cTable kind_tab) ⟪apps cHd ⟪tRel 0⟫⟫; tSucc tZero⟫; tZero;
      apps (cIte N) ⟪apps cEqb ⟪apps (cTable kind_tab) ⟪apps cHd ⟪tRel 0⟫⟫; tnum 2⟫;
        apps (tRel 1) ⟪apps cNth ⟪apps (cTable scr_tab) ⟪apps cHd ⟪tRel 0⟫⟫; apps cTl ⟪tRel 0⟫⟫⟫;
        apps cAndb ⟪apps cLAll ⟪apps cMapi ⟪cDnfF; tZero; apps cTl ⟪tRel 0⟫⟫⟫;
          apps cNegb ⟪apps cLAll ⟪apps cMapi ⟪cClos0F; tZero; apps cTl ⟪tRel 0⟫⟫⟫⟫⟫⟫⟫⟫).
Arguments cWhneAlg : simpl never.

Definition cWhne := lams ⟪tNat⟫ (apps (cRec N) ⟪cWhneAlg; tRel 0⟫).
Arguments cWhne : simpl never.

(** Some constant codes *)
Definition code_rel0 := apps cCons ⟪tZero; tZero⟫.

Definition code_U := apps cCons ⟪tSucc tZero; tZero⟫.

(** Building nodes *)
Fixpoint clist (ts : list term) : term := match ts with
| nil => tZero
| cons t ts => apps cCons ⟪t; clist ts⟫
end.

Definition cnode (g : nat) (ts : list term) := apps cCons ⟪tnum g; clist ts⟫.

Definition cEraseLam := lams ⟪tNat⟫
  (apps (cIte N) ⟪apps cEqb ⟪apps cHd ⟪tRel 0⟫; tnum 4⟫;
    apps (cIte N) ⟪apps cEqb ⟪apps cNth ⟪tSucc tZero; apps cTl ⟪tRel 0⟫⟫; code_rel0⟫;
      apps (cIte N) ⟪apps cNocc ⟪apps cNth ⟪tZero; apps cTl ⟪tRel 0⟫⟫; tZero⟫;
        apps cSubst ⟪tZero; code_U; apps cNth ⟪tZero; apps cTl ⟪tRel 0⟫⟫⟫;
        cnode 3 ⟪code_U; tRel 0⟫⟫;
      cnode 3 ⟪code_U; tRel 0⟫⟫;
    cnode 3 ⟪code_U; tRel 0⟫⟫).
Arguments cEraseLam : simpl never.

Definition cErasePair := lams ⟪tNat; tNat⟫
  (apps (cIte N) ⟪apps cEqb ⟪apps cHd ⟪tRel 1⟫; tnum 13⟫;
    apps (cIte N) ⟪apps cEqb ⟪apps cHd ⟪tRel 0⟫; tnum 14⟫;
      apps (cIte N) ⟪apps cEqb ⟪apps cNth ⟪tZero; apps cTl ⟪tRel 1⟫⟫; apps cNth ⟪tZero; apps cTl ⟪tRel 0⟫⟫⟫;
        apps cNth ⟪tZero; apps cTl ⟪tRel 1⟫⟫;
        cnode 12 ⟪code_U; code_U; tRel 1; tRel 0⟫⟫;
      cnode 12 ⟪code_U; code_U; tRel 1; tRel 0⟫⟫;
    cnode 12 ⟪code_U; code_U; tRel 1; tRel 0⟫⟫).
Arguments cErasePair : simpl never.

(** [λ rec _ y. rec y] *)
Definition cRecF := lams ⟪ety (Arr N N); tNat; tNat⟫ (apps (tRel 2) ⟪tRel 0⟫).
Arguments cRecF : simpl never.

Definition cEraseAlg := lams ⟪ety (Arr N N); tNat⟫
  (apps (cIfz N) ⟪apps cHd ⟪tRel 0⟫; tRel 0;
    apps (cIte N) ⟪apps cEqb ⟪apps cHd ⟪tRel 0⟫; tnum 3⟫;
      apps cEraseLam ⟪apps (tRel 1) ⟪apps cNth ⟪tSucc tZero; apps cTl ⟪tRel 0⟫⟫⟫⟫;
      apps (cIte N) ⟪apps cEqb ⟪apps cHd ⟪tRel 0⟫; tnum 12⟫;
        apps cErasePair ⟪apps (tRel 1) ⟪apps cNth ⟪tnum 2; apps cTl ⟪tRel 0⟫⟫⟫;
          apps (tRel 1) ⟪apps cNth ⟪tnum 3; apps cTl ⟪tRel 0⟫⟫⟫⟫;
        apps cCons ⟪apps cHd ⟪tRel 0⟫; apps cMapi ⟪apps cRecF ⟪tRel 1⟫; tZero; apps cTl ⟪tRel 0⟫⟫⟫⟫⟫⟫).
Arguments cEraseAlg : simpl never.

Definition cErase := lams ⟪tNat⟫ (apps (cRec N) ⟪cEraseAlg; tRel 0⟫).
Arguments cErase : simpl never.

Definition cUNatAlg := lams ⟪ety (Arr N N); tNat⟫
  (apps (cIte N) ⟪apps cEqb ⟪apps cHd ⟪tRel 0⟫; tnum 6⟫; tSucc tZero;
    apps (cIte N) ⟪apps cEqb ⟪apps cHd ⟪tRel 0⟫; tnum 7⟫;
      apps (cIfz N) ⟪apps (tRel 1) ⟪apps cNth ⟪tZero; apps cTl ⟪tRel 0⟫⟫⟫; tZero;
        tSucc (apps (tRel 1) ⟪apps cNth ⟪tZero; apps cTl ⟪tRel 0⟫⟫⟫)⟫;
      tZero⟫⟫).
Arguments cUNatAlg : simpl never.

Definition cUNat := lams ⟪tNat⟫ (apps (cRec N) ⟪cUNatAlg; tRel 0⟫).
Arguments cUNat : simpl never.

(** [λ _ r. code (tSucc r)] *)
Definition cQNatS := lams ⟪tNat; tNat⟫ (cnode 7 ⟪tRel 0⟫).
Arguments cQNatS : simpl never.

Definition cQNat := lams ⟪tNat⟫ (tNatElim tNat (cnode 6 nil) cQNatS (tRel 0)).
Arguments cQNat : simpl never.

Definition code_nat := cnode 5 nil.

Definition code_zero := cnode 6 nil.

Definition code_IdZZ := cnode 15 ⟪code_nat; code_zero; code_zero⟫.

Definition code_ReflZ := cnode 16 ⟪code_nat; code_zero⟫.

(** [λ _ r. code (tAnd (tId tNat tZero tZero) r)] *)
Definition cQEvalTyS := lams ⟪tNat; tNat⟫ (cnode 11 ⟪code_IdZZ; tRel 0⟫).
Arguments cQEvalTyS : simpl never.

Definition cQEvalTy := lams ⟪tNat; tNat⟫
  (tNatElim tNat (cnode 15 ⟪code_nat; cnode 7 ⟪apps cQNat ⟪tRel 0⟫⟫; cnode 7 ⟪apps cQNat ⟪tRel 0⟫⟫⟫) cQEvalTyS (tRel 1)).
Arguments cQEvalTy : simpl never.

(** [λ v n r. code (tPair (tId tNat tZero tZero) (qEvalTy n v) (tRefl tNat tZero) r)] *)
Definition cQEvalTmS := lams ⟪tNat; tNat; tNat⟫
  (cnode 12 ⟪code_IdZZ; apps cQEvalTy ⟪tRel 1; tRel 2⟫; code_ReflZ; tRel 0⟫).
Arguments cQEvalTmS : simpl never.

Definition cQEvalTm := lams ⟪tNat; tNat⟫
  (tNatElim tNat (cnode 16 ⟪code_nat; cnode 7 ⟪apps cQNat ⟪tRel 0⟫⟫⟫) (apps cQEvalTmS ⟪tRel 0⟫) (tRel 1)).
Arguments cQEvalTm : simpl never.

(** Type of the internal evaluator [E d x] of the previous step *)
Definition EvTy := Arr N (Arr N N).

(** [λ rec l. if l = 0 then 1 else if hd l = 0 then 0 else if rec (tl l) = 0 then 0 else S (cons (pred (hd l)) (pred (rec (tl l))))] *)
Definition cSeqAlg := lams ⟪ety (Arr N N); tNat⟫
  (apps (cIfz N) ⟪tRel 0; tSucc tZero;
    apps (cIfz N) ⟪apps cHd ⟪tRel 0⟫; tZero;
      apps (cIfz N) ⟪apps (tRel 1) ⟪apps cTl ⟪tRel 0⟫⟫; tZero;
        tSucc (apps cCons ⟪apps cPred ⟪apps cHd ⟪tRel 0⟫⟫; apps cPred ⟪apps (tRel 1) ⟪apps cTl ⟪tRel 0⟫⟫⟫⟫)⟫⟫⟫).
Arguments cSeqAlg : simpl never.

Definition cSeq := lams ⟪tNat⟫ (apps (cRec N) ⟪cSeqAlg; tRel 0⟫).
Arguments cSeq : simpl never.

(** [λ E x i y. if ign (tag x) i then S y else E true y] *)
Definition cDeepF := lams ⟪ety EvTy; tNat; tNat; tNat⟫
  (apps (cIte N) ⟪apps cIgn ⟪apps cHd ⟪tRel 2⟫; tRel 1⟫; tSucc (tRel 0); apps (tRel 3) ⟪tSucc tZero; tRel 0⟫⟫).
Arguments cDeepF : simpl never.

Definition cDeep := lams ⟪ety EvTy; tNat⟫
  (apps (cIfz N) ⟪apps cSeq ⟪apps cMapi ⟪apps cDeepF ⟪tRel 1; tRel 0⟫; tZero; apps cTl ⟪tRel 0⟫⟫⟫; tZero;
    tSucc (apps cCons ⟪apps cHd ⟪tRel 0⟫; apps cPred ⟪apps cSeq ⟪apps cMapi ⟪apps cDeepF ⟪tRel 1; tRel 0⟫; tZero; apps cTl ⟪tRel 0⟫⟫⟫⟫⟫)⟫).
Arguments cDeep : simpl never.

Definition cCanon := lams ⟪ety EvTy; tNat; tNat⟫
  (apps (cIte N) ⟪tRel 1; apps cDeep ⟪tRel 2; tRel 0⟫; tSucc (tRel 0)⟫).
Arguments cCanon : simpl never.

(** [λ s r i y. if i = s then r else y] *)
Definition cReplF := lams ⟪tNat; tNat; tNat; tNat⟫
  (apps (cIte N) ⟪apps cEqb ⟪tRel 1; tRel 3⟫; tRel 2; tRel 0⟫).
Arguments cReplF : simpl never.

Definition cElim := lams ⟪ety EvTy; tNat; tNat; tNat; ety (Arr N N)⟫
  (apps (cIfz N) ⟪apps (tRel 4) ⟪tZero; apps cNth ⟪tRel 1; apps cTl ⟪tRel 2⟫⟫⟫; tZero;
    apps (cIfz N) ⟪apps (tRel 0) ⟪apps cPred ⟪apps (tRel 4) ⟪tZero; apps cNth ⟪tRel 1; apps cTl ⟪tRel 2⟫⟫⟫⟫⟫;
      apps (cIte N) ⟪apps cWhne ⟪apps cPred ⟪apps (tRel 4) ⟪tZero; apps cNth ⟪tRel 1; apps cTl ⟪tRel 2⟫⟫⟫⟫⟫;
        apps (cIte N) ⟪tRel 3;
          apps cDeep ⟪tRel 4; apps cCons ⟪apps cHd ⟪tRel 2⟫;
            apps cMapi ⟪apps cReplF ⟪tRel 1; apps cPred ⟪apps (tRel 4) ⟪tZero; apps cNth ⟪tRel 1; apps cTl ⟪tRel 2⟫⟫⟫⟫⟫; tZero; apps cTl ⟪tRel 2⟫⟫⟫⟫;
          tSucc (apps cCons ⟪apps cHd ⟪tRel 2⟫;
            apps cMapi ⟪apps cReplF ⟪tRel 1; apps cPred ⟪apps (tRel 4) ⟪tZero; apps cNth ⟪tRel 1; apps cTl ⟪tRel 2⟫⟫⟫⟫⟫; tZero; apps cTl ⟪tRel 2⟫⟫⟫)⟫;
        tZero⟫;
      apps cPred ⟪apps (tRel 0) ⟪apps cPred ⟪apps (tRel 4) ⟪tZero; apps cNth ⟪tRel 1; apps cTl ⟪tRel 2⟫⟫⟫⟫⟫⟫⟫⟫).
Arguments cElim : simpl never.

Definition F (i : nat) (x : term) := apps cNth ⟪tnum i; apps cTl ⟪x⟫⟫.

Definition cHApp := lams ⟪ety EvTy; tNat; tNat; tNat⟫
  (apps (cIte N) ⟪apps cEqb ⟪apps cHd ⟪tRel 0⟫; tnum 3⟫;
    tSucc (apps (tRel 3) ⟪tRel 2; apps cSubst ⟪tZero; F 1 (tRel 1); F 1 (tRel 0)⟫⟫); tZero⟫).
Arguments cHApp : simpl never.

Definition cHNat := lams ⟪ety EvTy; tNat; tNat; tNat⟫
  (apps (cIte N) ⟪apps cEqb ⟪apps cHd ⟪tRel 0⟫; tnum 6⟫; tSucc (apps (tRel 3) ⟪tRel 2; F 1 (tRel 1)⟫);
    apps (cIte N) ⟪apps cEqb ⟪apps cHd ⟪tRel 0⟫; tnum 7⟫;
      tSucc (apps (tRel 3) ⟪tRel 2; cnode 4 ⟪cnode 4 ⟪F 2 (tRel 1); F 0 (tRel 0)⟫;
        cnode 8 ⟪F 0 (tRel 1); F 1 (tRel 1); F 2 (tRel 1); F 0 (tRel 0)⟫⟫⟫);
      tZero⟫⟫).
Arguments cHNat : simpl never.

Definition cHNone := lams ⟪tNat⟫ tZero.
Arguments cHNone : simpl never.

(** [λ E d i r. if tag r = 12 then S (E d (field i r)) else 0] *)
Definition cHProj := lams ⟪ety EvTy; tNat; tNat; tNat⟫
  (apps (cIte N) ⟪apps cEqb ⟪apps cHd ⟪tRel 0⟫; tnum 12⟫;
    tSucc (apps (tRel 3) ⟪tRel 2; apps cNth ⟪tRel 1; apps cTl ⟪tRel 0⟫⟫⟫); tZero⟫).
Arguments cHProj : simpl never.

Definition cHId := lams ⟪ety EvTy; tNat; tNat; tNat⟫
  (apps (cIte N) ⟪apps cEqb ⟪apps cHd ⟪tRel 0⟫; tnum 16⟫; tSucc (apps (tRel 3) ⟪tRel 2; F 3 (tRel 1)⟫); tZero⟫).
Arguments cHId : simpl never.

Definition cQuoteB := lams ⟪ety EvTy; tNat⟫
  (apps (cIfz N) ⟪apps (tRel 1) ⟪tSucc tZero; F 0 (tRel 0)⟫; tZero;
    apps (cIte N) ⟪apps cClosed ⟪apps cPred ⟪apps (tRel 1) ⟪tSucc tZero; F 0 (tRel 0)⟫⟫; tZero⟫;
      tSucc (apps cQNat ⟪apps cErase ⟪apps cPred ⟪apps (tRel 1) ⟪tSucc tZero; F 0 (tRel 0)⟫⟫⟫⟫);
      tSucc (cnode 18 ⟪apps cPred ⟪apps (tRel 1) ⟪tSucc tZero; F 0 (tRel 0)⟫⟫⟫)⟫⟫).
Arguments cQuoteB : simpl never.

Definition cStepCore := lams ⟪ety (Arr N N); tNat; tNat; ety EvTy⟫
  (apps (cIfz N) ⟪apps cUNat ⟪tRel 1⟫; tZero;
    apps (cIfz N) ⟪apps (tRel 3) ⟪cnode 4 ⟪apps cErase ⟪tRel 2⟫; apps cQNat ⟪apps cPred ⟪apps cUNat ⟪tRel 1⟫⟫⟫⟫⟫; tZero;
      apps (cIfz N) ⟪apps cUNat ⟪apps cSnd ⟪apps cPred ⟪apps (tRel 3) ⟪cnode 4 ⟪apps cErase ⟪tRel 2⟫; apps cQNat ⟪apps cPred ⟪apps cUNat ⟪tRel 1⟫⟫⟫⟫⟫⟫⟫⟫; tZero;
        apps (tRel 0) ⟪apps cFst ⟪apps cPred ⟪apps (tRel 3) ⟪cnode 4 ⟪apps cErase ⟪tRel 2⟫; apps cQNat ⟪apps cPred ⟪apps cUNat ⟪tRel 1⟫⟫⟫⟫⟫⟫⟫;
          apps cPred ⟪apps cUNat ⟪apps cSnd ⟪apps cPred ⟪apps (tRel 3) ⟪cnode 4 ⟪apps cErase ⟪tRel 2⟫; apps cQNat ⟪apps cPred ⟪apps cUNat ⟪tRel 1⟫⟫⟫⟫⟫⟫⟫⟫⟫⟫⟫⟫⟫).
Arguments cStepCore : simpl never.

Definition cStepB := lams ⟪ety EvTy; ety (Arr N N); tNat; tNat; ety EvTy⟫
  (apps (cIfz N) ⟪apps (tRel 4) ⟪tSucc tZero; F 0 (tRel 2)⟫; tZero;
    apps (cIfz N) ⟪apps (tRel 4) ⟪tSucc tZero; F 1 (tRel 2)⟫; tZero;
      apps (cIte N) ⟪apps cAndb ⟪apps cClosed ⟪apps cPred ⟪apps (tRel 4) ⟪tSucc tZero; F 0 (tRel 2)⟫⟫; tZero⟫;
                                 apps cClosed ⟪apps cPred ⟪apps (tRel 4) ⟪tSucc tZero; F 1 (tRel 2)⟫⟫; tZero⟫⟫;
        apps cStepCore ⟪tRel 3; apps cPred ⟪apps (tRel 4) ⟪tSucc tZero; F 0 (tRel 2)⟫⟫;
          apps cPred ⟪apps (tRel 4) ⟪tSucc tZero; F 1 (tRel 2)⟫⟫; tRel 0⟫;
        tSucc (apps cCons ⟪tRel 1; clist ⟪apps cPred ⟪apps (tRel 4) ⟪tSucc tZero; F 0 (tRel 2)⟫⟫;
          apps cPred ⟪apps (tRel 4) ⟪tSucc tZero; F 1 (tRel 2)⟫⟫⟫⟫)⟫⟫⟫).
Arguments cStepB : simpl never.

Definition cFinStep := lams ⟪tNat; tNat⟫ (tSucc (apps cQNat ⟪tRel 1⟫)).
Arguments cFinStep : simpl never.

Definition cFinRefl := lams ⟪tNat; tNat⟫ (tSucc (apps cQEvalTm ⟪tRel 1; tRel 0⟫)).
Arguments cFinRefl : simpl never.

Definition br_atom := tSucc (tRel 0).

Definition br_canon := apps cCanon ⟪tRel 3; tRel 1; tRel 0⟫.

Definition br_elim (s : nat) (h : term) := apps cElim ⟪tRel 3; tRel 1; tRel 0; tnum s; h⟫.

Definition body_branches : list term :=
  ⟪br_atom; br_atom; br_canon; br_canon; br_elim 0 (apps cHApp ⟪tRel 3; tRel 1; tRel 0⟫); br_atom⟫ ++
  ⟪br_atom; br_canon; br_elim 3 (apps cHNat ⟪tRel 3; tRel 1; tRel 0⟫); br_atom; br_elim 1 cHNone; br_canon⟫ ++
  ⟪br_canon; br_elim 0 (apps cHProj ⟪tRel 3; tRel 1; tnum 2⟫); br_elim 0 (apps cHProj ⟪tRel 3; tRel 1; tnum 3⟫);
    br_canon; br_canon; br_elim 5 (apps cHId ⟪tRel 3; tRel 1; tRel 0⟫)⟫ ++
  ⟪apps cQuoteB ⟪tRel 3; tRel 0⟫;
   apps cStepB ⟪tRel 3; tRel 2; tRel 0; tnum 19; cFinStep⟫;
   apps cStepB ⟪tRel 3; tRel 2; tRel 0; tnum 20; cFinRefl⟫⟫.

Definition cBody := lams ⟪ety EvTy; ety (Arr N N); tNat; tNat⟫
  (switch N (apps cHd ⟪tRel 0⟫) body_branches tZero).
Arguments cBody : simpl never.

Definition ST := Arr N (Arr N (Arr N N)).

(** [λ m F sel d x. if sel = 0 then body (F 0) (F 1 0) d x else (update of the minimization)] *)
Definition cStateS := lams ⟪tNat; ety ST; tNat; tNat; tNat⟫
  (apps (cIfz N) ⟪tRel 2;
    apps cBody ⟪apps (tRel 3) ⟪tZero⟫; apps (tRel 3) ⟪tSucc tZero; tZero⟫; tRel 1; tRel 0⟫;
    apps (cIfz N) ⟪apps (tRel 3) ⟪tSucc tZero; tZero; tRel 0⟫;
      apps (cIfz N) ⟪apps cBody ⟪apps (tRel 3) ⟪tZero⟫; apps (tRel 3) ⟪tSucc tZero; tZero⟫; tSucc tZero; tRel 0⟫; tZero;
        apps cCons ⟪tRel 4; apps cPred ⟪apps cBody ⟪apps (tRel 3) ⟪tZero⟫; apps (tRel 3) ⟪tSucc tZero; tZero⟫; tSucc tZero; tRel 0⟫⟫⟫⟫;
      apps (tRel 3) ⟪tSucc tZero; tZero; tRel 0⟫⟫⟫).
Arguments cStateS : simpl never.

Definition cState := lams ⟪tNat⟫ (tNatElim (ety ST)⟨↑⟩ (dflt ST) cStateS (tRel 0)).
Arguments cState : simpl never.

Definition tRun := lams ⟪tNat; tNat⟫
  (apps cBody ⟪apps cState ⟪tRel 0; tZero⟫; apps cState ⟪tRel 0; tSucc tZero; tZero⟫; tSucc tZero; tRel 1⟫).
