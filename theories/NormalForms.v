(** * LogRel.NormalForms: definition of normal and neutral forms, and properties. *)
From Coq Require Import ssrbool.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Context Closed Computation.

(** Deep normal forms *)

Definition isLambda (t : term) := match t with
| tLambda _ _ => true
| _ => false
end.

Definition isNatConstructor (t : term) := match t with
| tZero | tSucc _ => true
| _ => false
end.

Definition isPairConstructor (t : term) := match t with
| tPair _ _ _ _ => true
| _ => false
end.

Definition isEmptyConstructor (t : term) := false.

Definition isIdConstructor (t : term) := match t with
| tRefl _ _ => true
| _ => false
end.

Unset Elimination Schemes.

Inductive dnf : term -> Set :=
  | dnf_tSort {s} : dnf (tSort s)
  | dnf_tProd {A B} : dnf A -> dnf B -> dnf (tProd A B)
  | dnf_tLambda {A t} : dnf A -> dnf t -> dnf (tLambda A t)
  | dnf_tNat : dnf tNat
  | dnf_tZero : dnf tZero
  | dnf_tSucc {n} : dnf n -> dnf (tSucc n)
  | dnf_tEmpty : dnf tEmpty
  | dnf_tSig {A B} : dnf A -> dnf B -> dnf (tSig A B)
  | dnf_tPair {A B a b} : dnf A -> dnf B -> dnf a -> dnf b -> dnf (tPair A B a b)
  | dnf_tId {A x y} : dnf A -> dnf x -> dnf y -> dnf (tId A x y)
  | dnf_tRefl {A x} : dnf A -> dnf x -> dnf (tRefl A x)
  | dnf_dne {n} : dne n -> dnf n
with dne : term -> Set :=
  | dne_tRel {v} : dne (tRel v)
  | dne_tApp {n t} : dne n -> dnf t -> dne (tApp n t)
  | dne_tNatElim {P hz hs n} : dnf P -> dnf hz -> dnf hs -> dne n -> dne (tNatElim P hz hs n)
  | dne_tEmptyElim {P n} : dnf P -> dne n -> dne (tEmptyElim P n)
  | dne_tFst {n} : dne n -> dne (tFst n)
  | dne_tSnd {n} : dne n -> dne (tSnd n)
  | dne_tIdElim {A x P hr y e} : dnf A -> dnf x -> dnf P -> dnf hr -> dnf y -> dne e -> dne (tIdElim A x P hr y e)
  | dne_tQuote {t} : ~ closed0 t -> dnf t -> dne (tQuote t)
  | dne_tReflect {t u} : (~ is_closedn 0 t) + (~ is_closedn 0 u) -> dnf t -> dnf u -> dne (tReflect t u)
.

Set Elimination Schemes.

Scheme
  Induction for dnf Sort Type with
  Induction for dne Sort Type.

Definition dnf_dne_rect P Q p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 :=
  pair
    (dnf_rect P Q p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21)
    (dne_rect P Q p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21).

(** ** Weak-head normal forms and neutrals. *)

Inductive whnf : term -> Type :=
  | whnf_tSort {s} : whnf (tSort s)
  | whnf_tProd {A B} : whnf (tProd A B)
  | whnf_tLambda {A t} : whnf (tLambda A t)
  | whnf_tNat : whnf tNat
  | whnf_tZero : whnf tZero
  | whnf_tSucc {n} : whnf (tSucc n)
  | whnf_tEmpty : whnf tEmpty
  | whnf_tSig {A B} : whnf (tSig A B)
  | whnf_tPair {A B a b} : whnf (tPair A B a b)
  | whnf_tId {A x y} : whnf (tId A x y)
  | whnf_tRefl {A x} : whnf (tRefl A x)
  | whnf_whne {n} : whne n -> whnf n
with whne : term -> Type :=
  | whne_tRel {v} : whne (tRel v)
  | whne_tApp {n t} : whne n -> whne (tApp n t)
  | whne_tNatElim {P hz hs n} : whne n -> whne (tNatElim P hz hs n)
  | whne_tEmptyElim {P e} : whne e -> whne (tEmptyElim P e)
  | whne_tFst {p} : whne p -> whne (tFst p)
  | whne_tSnd {p} : whne p -> whne (tSnd p)
  | whne_tIdElim {A x P hr y e} : whne e -> whne (tIdElim A x P hr y e)
  | whne_tQuote {t} :  ~ closed0 t -> dnf t -> whne (tQuote t)
  | whne_tReflect {t u} : (~ is_closedn 0 t) + (~ is_closedn 0 u) -> dnf t -> dnf u -> whne (tReflect t u)
.


#[global] Hint Constructors whne whnf : gen_typing.

Ltac inv_whne :=
  repeat lazymatch goal with
    | H : whne _ |- _ =>
    try solve [inversion H] ; block H
  end; unblock.

Lemma dnf_dne_whnf_whne : (forall v, dnf v -> whnf v) × (forall n, dne n -> whne n).
Proof.
apply dnf_dne_rect; intros; now constructor.
Qed.

Lemma dnf_whnf : forall v, dnf v -> whnf v.
Proof.
intros; now apply dnf_dne_whnf_whne.
Qed.

Lemma dne_whne : forall v, dne v -> whne v.
Proof.
intros; now apply dnf_dne_whnf_whne.
Qed.

Lemma dne_dnf_whne : forall v, dnf v -> whne v -> dne v.
Proof.
intros v [] H; inversion H; subst; tea.
Qed.

Lemma neSort s : whne (tSort s) -> False.
Proof.
  inversion 1.
Qed.

Lemma nePi A B : whne (tProd A B) -> False.
Proof.
  inversion 1.
Qed.

Lemma neLambda A t : whne (tLambda A t) -> False.
Proof.
  inversion 1.
Qed.

Section RenDnf.

Lemma dnf_dne_ren : (forall t, dnf t -> forall ρ, dnf t⟨ρ⟩) × (forall t, dne t -> forall ρ, dne t⟨ρ⟩).
Proof.
apply dnf_dne_rect; cbn; intros; try now econstructor.
+ constructor; [|now eauto].
  intros Hc; now apply closed0_ren_rev in Hc.
+ constructor; [|now eauto|now eauto].
  destruct s; [left|right];
  intros Hc; now apply closed0_ren_rev in Hc.
Qed.

Local Ltac inv_dne := try match goal with H : dne _ |- _ => inversion H; subst end.

Lemma dnf_dne_ren_rev : forall t ρ, (dnf t⟨ρ⟩ -> dnf t) × (whne t⟨ρ⟩ -> whne t).
Proof.
induction t; intros ρ; split; cbn in *; intros; inv_whne.
all: repeat match goal with H : forall ρ, (_ × _) |- _ =>
  pose proof (fun ρ => fst (H ρ));
  pose proof (fun ρ => snd (H ρ));
  clear H
end.
all: repeat match goal with H : dnf ?t |- _ => is_var t; inversion H; subst; clear H end.
all: try now (constructor; match goal with H : whne _ |- _ => inversion H end; subst).
all: try now (match goal with H : dnf ?t |- _ => inversion H; subst; clear H end; inv_dne; constructor).
all: try now (
  match goal with H : dnf ?t |- _ => inversion H; subst; clear H end;
  match goal with H : dne ?t |- _ => inversion H; subst; clear H end;
  do 2 constructor; eauto; apply dne_dnf_whne; eauto using dnf_dne, dne_whne).
+ inversion H; subst; inversion H2; subst.
  do 2 constructor; [now eintros ?%closed0_ren|eauto].
+ inversion H; subst.
  constructor; [now eintros ?%closed0_ren|eauto].
+ inversion H; subst; inversion H4; subst.
  do 2 constructor; eauto.
  destruct H7; [left|right]; now eintros ?%closed0_ren.
+ inversion H; subst.
  constructor; eauto.
  destruct H6; [left|right]; now eintros ?%closed0_ren.
Qed.

Lemma dnf_ren_rev : forall t ρ, dnf t⟨ρ⟩ -> dnf t.
Proof.
intros; now eapply dnf_dne_ren_rev.
Qed.

Lemma dne_ren_rev : forall t ρ, dne t⟨ρ⟩ -> dne t.
Proof.
intros.
eapply dne_dnf_whne.
+ eapply dnf_dne_ren_rev; now constructor.
+ apply dnf_dne_whnf_whne in H.
  now apply dnf_dne_ren_rev in H.
Qed.

Lemma whne_ren_rev : forall t ρ, whne t⟨ρ⟩ -> whne t.
Proof.
intros; now eapply dnf_dne_ren_rev.
Qed.

Lemma dne_ren ρ (t : term) : dne t -> dne t⟨ρ⟩.
Proof.
intros; now apply dnf_dne_ren.
Qed.

Lemma dnf_ren ρ (t : term) : dnf t -> dnf t⟨ρ⟩.
Proof.
intros; now apply dnf_dne_ren.
Qed.

End RenDnf.

#[global] Hint Resolve neSort nePi neLambda : gen_typing.

(** ** Restricted classes of normal forms *)

Inductive is_eta_expanded : term -> Type :=
| is_eta_expanded_intro :
  forall f, is_eta_expanded (tApp f⟨↑⟩ (tRel 0)).

Inductive isType : term -> Type :=
  | UnivType {s} : isType (tSort s)
  | ProdType { A B} : isType (tProd A B)
  | NatType : isType tNat
  | EmptyType : isType tEmpty
  | SigType {A B} : isType (tSig A B)
  | IdType {A x y} : isType (tId A x y)
  | NeType {A}  : whne A -> isType A.

Inductive isPosType : term -> Type :=
  | UnivPos {s} : isPosType (tSort s)
  | NatPos : isPosType tNat
  | EmptyPos : isPosType tEmpty
  | IdPos {A x y} : isPosType (tId A x y)
  | NePos {A}  : whne A -> isPosType A.

Inductive isFun : term -> Type :=
  | LamFun {A t} : isFun (tLambda A t)
  | NeFun  {f} : whne f -> isFun f.

Inductive isNat : term -> Type :=
  | ZeroNat : isNat tZero
  | SuccNat {t} : isNat (tSucc t)
  | NeNat {n} : whne n -> isNat n.

Inductive isPair : term -> Type :=
  | PairPair {A B a b} : isPair (tPair A B a b)
  | NePair {p} : whne p -> isPair p.

Definition isPosType_isType t (i : isPosType t) : isType t.
Proof. destruct i; now constructor. Defined.

Coercion isPosType_isType : isPosType >-> isType.

Definition isType_whnf t (i : isType t) : whnf t.
Proof. destruct i; now constructor. Defined.

Coercion isType_whnf : isType >-> whnf.

Definition isFun_whnf t (i : isFun t) : whnf t.
Proof. destruct i; now constructor. Defined.

Coercion isFun_whnf : isFun >-> whnf.

Definition isPair_whnf t (i : isPair t) : whnf t.
Proof. destruct i; now constructor. Defined.

Coercion isPair_whnf : isPair >-> whnf.

Definition isNat_whnf t (i : isNat t) : whnf t :=
  match i with
  | ZeroNat => whnf_tZero
  | SuccNat => whnf_tSucc
  | NeNat n => whnf_whne n
  end.

#[global] Hint Resolve isPosType_isType isType_whnf isFun_whnf isNat_whnf isPair_whnf : gen_typing.
#[global] Hint Constructors isPosType isType isFun isNat : gen_typing.

(** ** Canonical forms *)

Inductive isCanonical : term -> Type :=
  | can_tSort {s} : isCanonical (tSort s)
  | can_tProd {A B} : isCanonical (tProd A B)
  | can_tLambda {A t} : isCanonical (tLambda A t)
  | can_tNat : isCanonical tNat
  | can_tZero : isCanonical tZero
  | can_tSucc {n} : isCanonical (tSucc n)
  | can_tEmpty : isCanonical tEmpty
  | can_tSig {A B} : isCanonical (tSig A B)
  | can_tPair {A B a b}: isCanonical (tPair A B a b)
  | can_tId {A x y}: isCanonical (tId A x y)
  | can_tRefl {A x}: isCanonical (tRefl A x).

#[global] Hint Constructors isCanonical : gen_typing.

(** ** Normal and neutral forms are stable by renaming *)

Section RenWhnf.

  Variable (ρ : nat -> nat).

  Lemma whne_ren t : whne t -> whne (t⟨ρ⟩).
  Proof.
    induction 1 ; cbn; try now econstructor.
    + econstructor; [|now eapply dnf_ren].
      intros Hc; now apply closed0_ren_rev in Hc.
    + econstructor; try now eapply dnf_ren.
      destruct s; [left|right]; intros Hc; now apply closed0_ren_rev in Hc.
  Qed.

  Lemma whnf_ren t : whnf t -> whnf (t⟨ρ⟩).
  Proof.
    induction 1 ; cbn.
    all: econstructor.
    now eapply whne_ren.
  Qed.

  Lemma isType_ren A : isType A -> isType (A⟨ρ⟩).
  Proof.
    induction 1 ; cbn.
    all: econstructor.
    now eapply whne_ren.
  Qed.

  Lemma isPosType_ren A : isPosType A -> isPosType (A⟨ρ⟩).
  Proof.
    destruct 1 ; cbn.
    all: econstructor.
    now eapply whne_ren.
  Qed.

  Lemma isFun_ren f : isFun f -> isFun (f⟨ρ⟩).
  Proof.
    induction 1 ; cbn.
    all: econstructor.
    now eapply whne_ren.
  Qed.

  Lemma isPair_ren f : isPair f -> isPair (f⟨ρ⟩).
  Proof.
    induction 1 ; cbn.
    all: econstructor.
    now eapply whne_ren.
  Qed.

  Lemma isCanonical_ren t : isCanonical t <~> isCanonical (t⟨ρ⟩).
  Proof.
    split.
    all: destruct t ; cbn ; inversion 1.
    all: now econstructor.
  Qed.

End RenWhnf.

#[global] Hint Resolve whne_ren whnf_ren isType_ren isPosType_ren isFun_ren isCanonical_ren : gen_typing.

(** Computational variant of the above *)

Fixpoint is_nf ne t {struct t} := match t with
| tSort _ | tNat | tZero | tEmpty => negb ne
| tProd A B => negb ne && is_nf false A && is_nf false B
| tLambda A t => negb ne && is_nf false A && is_nf false t
| tSucc t => negb ne && is_nf false t
| tSig A B => negb ne && is_nf false A && is_nf false B
| tPair A B a b => negb ne && is_nf false A && is_nf false B && is_nf false a && is_nf false b
| tId A t u => negb ne && is_nf false A && is_nf false t && is_nf false u
| tRefl A t => negb ne && is_nf false A && is_nf false t
| tRel _ => true
| tApp t u => is_nf true t && is_nf false u
| tNatElim P hz hs n => is_nf false P && is_nf false hz && is_nf false hs && is_nf true n
| tEmptyElim P e => is_nf false P && is_nf true e
| tFst t => is_nf true t
| tSnd t => is_nf true t
| tIdElim A x P hr y e =>
  is_nf false A && is_nf false x && is_nf false P && is_nf false hr && is_nf false y && is_nf true e
| tQuote t => is_nf false t && negb (is_closedn 0 t)
| tReflect t u => is_nf false t && is_nf false u && (negb (is_closedn 0 t) || negb (is_closedn 0 u))
end.

Definition is_dnf t := is_nf false t.
Definition is_dne t := is_nf true t.

Fixpoint is_wnf ne t {struct t} := match t with
| tSort _ | tNat | tZero | tEmpty => negb ne
| tProd A B => negb ne
| tLambda A t => negb ne
| tSucc t => negb ne
| tSig A B => negb ne
| tPair A B a b => negb ne
| tId A t u => negb ne
| tRefl A t => negb ne
| tRel _ => true
| tApp t u => is_wnf true t
| tNatElim P hz hs n => is_wnf true n
| tEmptyElim P e => is_wnf true e
| tFst t => is_wnf true t
| tSnd t => is_wnf true t
| tIdElim A x P hr y e => is_wnf true e
| tQuote t => is_dnf t && negb (is_closedn 0 t)
| tReflect t u => is_dnf t && is_dnf u && (negb (is_closedn 0 t) || negb (is_closedn 0 u))
end.

Definition is_whnf t := is_wnf false t.
Definition is_whne t := is_wnf true t.

Lemma is_nf_incl : forall t, is_dne t -> is_dnf t.
Proof.
induction t; cbn; intros.
all: repeat match goal with H : _ |- _ => apply andb_prop in H; destruct H end.
all: repeat (apply andb_true_intro; split); eauto.
Qed.

Lemma dnf_dne_is_nf :
  (forall t, dnf t -> is_dnf t = true) × (forall t, dne t -> is_dne t = true).
Proof.
apply dnf_dne_rect; cbn; intros.
all: repeat (apply andb_true_intro; split); eauto.
+ now apply is_nf_incl.
+ now apply Bool.eq_true_not_negb.
+ apply Bool.orb_true_intro; destruct s; [left|right]; now apply Bool.eq_true_not_negb.
Qed.

Lemma is_nf_dnf_dne :
  forall t, (is_dnf t = true -> dnf t) × (is_dne t = true -> dne t).
Proof.
induction t; split; intros; cbn in *.
all: repeat match goal with H : _ × _ |- _ => destruct H end.
all: repeat match goal with H : _ |- _ => apply andb_prop in H; destruct H end.
all: try discriminate.
all: try match goal with |- dnf _ => constructor end.
all: try match goal with |- dne _ => constructor end.
all: eauto using dnf, dne.
+ now eapply contraNnot.
+ now eapply contraNnot.
+ apply Bool.orb_true_elim in H0; destruct H0; [left|right]; now eapply contraNnot.
+ apply Bool.orb_true_elim in H0; destruct H0; [left|right]; now eapply contraNnot.
Qed.

Lemma is_dnf_dnf : forall t, is_dnf t = true -> dnf t.
Proof.
intros; now eapply is_nf_dnf_dne.
Qed.

Lemma dnf_is_dnf : forall t, dnf t -> is_dnf t = true.
Proof.
intros; now eapply dnf_dne_is_nf.
Qed.

Lemma is_dne_dne : forall t, is_dne t = true -> dne t.
Proof.
intros; now eapply is_nf_dnf_dne.
Qed.

Lemma dne_is_dne : forall t, dne t -> is_dne t = true.
Proof.
intros; now eapply dnf_dne_is_nf.
Qed.

Lemma whne_is_whne : forall t, whne t -> is_whne t = true.
Proof.
induction 1; cbn.
all: repeat (apply andb_true_intro; split); eauto using whne, whnf.
+ now eapply dnf_dne_is_nf.
+ apply Bool.eq_true_not_negb; tea.
+ now eapply dnf_dne_is_nf.
+ now eapply dnf_dne_is_nf.
+ apply Bool.orb_true_intro; destruct s; [left|right]; now apply Bool.eq_true_not_negb.
Qed.

Lemma is_whne_whne : forall t, is_whne t = true -> whne t.
Proof.
induction t; cbn; intros; try discriminate.
all: repeat match goal with H : _ |- _ => apply andb_prop in H; destruct H end.
all: eauto using whne, whnf.
+ constructor.
  - unfold closed0; destruct is_closedn; cbn in *; congruence.
  - now apply is_nf_dnf_dne.
+ constructor; try now apply is_nf_dnf_dne.
  apply Bool.orb_true_elim in H0; destruct H0; [left|right]; now eapply contraNnot.
Qed.
