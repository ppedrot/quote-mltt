(** * LogRel.NormalForms: definition of normal and neutral forms, and properties. *)
From Coq Require Import ssrbool.
From LogRel.AutoSubst Require Import core unscoped Ast Extra.
From LogRel Require Import Utils BasicAst Context Closed.

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
.

Set Elimination Schemes.

Scheme
  Induction for dnf Sort Type with
  Induction for dne Sort Type.

Definition dnf_dne_rect P Q p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 :=
  pair
    (dnf_rect P Q p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20)
    (dne_rect P Q p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20).

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
constructor; [|now eauto].
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
    econstructor; [|now eapply dnf_ren].
    intros Hc; now apply closed0_ren_rev in Hc.
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
