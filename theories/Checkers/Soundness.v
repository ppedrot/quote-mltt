(** * LogRel.Checkers.Soundness: the implementations imply the inductive predicates. *)
From Coq Require Import Nat Lia Arith.
From Equations Require Import Equations.
From LogRel Require Import Utils Syntax.All GenericTyping AlgorithmicJudgments.

From LogRel.Checkers Require Import Functions Views CtxAccessCorrectness ReductionCorrectness.
From PartialFun Require Import Monad PartialFun MonadExn.

Set Universe Polymorphism.

(** ** Correctness of context access *)
(** The function is equivalent to the in_ctx predicate. *)

Section CtxAccessCorrect.

  Lemma ctx_access_sound Γ n d :
    ctx_access Γ n = success d ->
    in_ctx Γ n d.
  Proof.
    funelim (ctx_access Γ n).
    all: simp ctx_access ; cbn.
    - inversion 1.
    - inversion 1.
      now constructor.
    - destruct (ctx_access Γ n') ; cbn.
      all: inversion 1 ; subst.
      constructor.
      now apply H.
  Qed.

  Lemma ctx_access_complete Γ n d :
    in_ctx Γ n d ->
    ctx_access Γ n = success d.
  Proof.
    induction 1.
    all: simp ctx_access ; cbn.
    - reflexivity.
    - now rewrite IHin_ctx. 
  Qed.

  Corollary ctx_access_correct Γ n d :
    in_ctx Γ n d <~> (ctx_access Γ n = success d).
  Proof.
    split.
    - eapply ctx_access_complete.
    - eapply ctx_access_sound.
  Qed.

End CtxAccessCorrect.


(** ** Soundness of typed conversion *)
(** If the function returns positively, the algorithmic judgment holds. *)


Ltac funelim_conv :=
  funelim (_conv _); 
    [ funelim (conv_ty _) | funelim (conv_ty_red _) | 
      funelim (conv_tm _) | funelim (conv_tm_red _) | 
      funelim (conv_ne _) | funelim (conv_ne_red _) ].

Section ConversionSound.
  Import AlgorithmicTypedConvData.

  #[universes(polymorphic)]Definition tconv_sound_type
    (x : conv_full_dom)
    (r : conv_full_cod x) : Type :=
  match x, r with
  | _, (exception _) => True
  | (ty_state;Γ;_;T;V), (success _) =>  [Γ |-[al] T ≅ V]
  | (ty_red_state;Γ;_;T;V), (success _) => whnf T -> whnf V -> [Γ |-[al] T ≅h V]
  | (tm_state;Γ;A;t;u), (success _) => [Γ |-[al] t ≅ u : A]
  | (tm_red_state;Γ;A;t;u), (success _) =>
      whnf A -> whnf t -> whnf u -> [Γ |-[al] t ≅h u : A]
  | (ne_state;Γ;_;m;n), (success T) => whne m -> whne n -> [Γ |-[al] m ~ n ▹ T]
  | (ne_red_state;Γ;_;m;n), (success T) => whne m -> whne n -> [Γ |-[al] m ~h n ▹ T] × whnf T
  end.

  Lemma _implem_tconv_sound :
    funrec _conv (fun _ => True) tconv_sound_type.
  Proof.
    intros x _.
    funelim_conv ; cbn.
    all: intros ; simp tconv_sound_type ; try easy ; cbn.
    all: repeat (
      match goal with
      | |- True * _ => split ; [easy|..]
      | |- forall x : exception _ _, _ => intros [|] ; [..|easy] ; cbn
      | |- _ -> _ => simp conv_sound_type ; intros ?
      | |- context [match ?t with | _ => _ end] => destruct t ; cbn ; try easy
      | s : sort |- _ => destruct s
      | H : graph wh_red _ _ |- _ => eapply red_sound in H as []
      | H : (_;_;_;_) = (_;_;_;_) |- _ => injection H; clear H; intros; subst
      | H : (build_nf_ty_view2 _ _ = ty_neutrals _ _) |- _ =>
          eapply ty_view2_neutral_can in H as [?%not_can_whne ?%not_can_whne] ; tea
      | H : (build_nf_view3 (tSort _) _ _ = types _ (ty_neutrals _ _)) |- _ =>
        eapply whnf_view3_ty_neutral_can in H as [?%not_can_whne ?%not_can_whne] ; tea
      | H : (build_nf_view3 _ _ _ = neutrals _ _ _) |- _ =>
        eapply whnf_view3_neutrals_can in H as [? ?%not_can_whne ?%not_can_whne] ; tea
      end).
    all: repeat match goal with | H : whne (_ _) |- _ => inversion_clear H end.
    all: try solve [now econstructor].
    - econstructor ; eauto. econstructor.
    - econstructor; tea; [intuition (auto with *)| now rewrite 2!Weakening.wk1_ren_on].
    - eapply convne_meta_conv.
      2: reflexivity.
      + econstructor.
        now eapply ctx_access_correct.
      + f_equal.
        symmetry.
        now eapply Nat.eqb_eq.
    - split; tea. econstructor ; eauto.
  Qed.

  Arguments conv_full_cod _ /.
  Arguments conv_cod _/.

  Corollary implem_tconv_graph x r :
    graph _conv x r ->
    tconv_sound_type x r.
  Proof.
    eapply funrec_graph.
    1: now apply _implem_tconv_sound.
    easy.
  Qed.

  Corollary implem_tconv_sound Γ T V :
    graph tconv (Γ,T,V) ok ->
    [Γ |-[al] T ≅ V].
  Proof.
    assert (funrec tconv (fun _ => True)
      (fun '(Γ,T,V) r => match r with | success _ => [Γ |-[al] T ≅ V] | _ => True end)) as Hrect.
    {
     intros ? _.
     funelim (tconv _) ; cbn.
     intros [] ; cbn ; [|easy].
     eintros ?%funrec_graph.
     2: now apply _implem_tconv_sound.
     all: now cbn in *.
    }
    eintros ?%funrec_graph.
    2: eassumption.
    all: now cbn in *.
  Qed.

End ConversionSound.

Section UntypedConversionSound.

  #[universes(polymorphic)]Definition uconv_sound_type
    (x : conv_state × term × term)
    (r : exn errors unit) : Type :=
  match x, r with
  | _, (exception _) => True
  | (tm_state,t,u), (success _) =>  [t ≅ u]
  | (tm_red_state,t,u), (success _) =>
      whnf t -> whnf u -> [t ≅h u]
  | (ne_state,m,n), (success _) => [m ~ n]
  | _, _ => True
  end.

  Lemma _implem_uconv_sound :
    funrec _uconv (fun _ => True) uconv_sound_type.
  Proof.
    intros x _.
    funelim (_uconv _) ; cbn ; try easy ;
      [ funelim (uconv_tm _) | funelim (uconv_tm_red _) | funelim (uconv_ne _) ].
    all: intros ; cbn ; try easy ; cbn.
    all: repeat (
      match goal with
      | |- True * _ => split ; [easy|..]
      | |- forall x : exn _ _, _ => intros [|] ; [..|easy] ; cbn
      | |- _ -> _ => cbn ; intros ?
      | |- context [match ?t with | _ => _ end] => destruct t ; cbn ; try easy
      | s : sort |- _ => destruct s
      | H : graph wh_red _ _ |- _ => eapply red_sound in H as []
      | H : (_,_) = (_,_) |- _ => injection H; clear H; intros; subst 
      end).
    all: try solve [now econstructor].
    1-4: econstructor ; eauto.
    1-4: match goal with | H : whnf ?t |- whne ?t =>
      now destruct H ; simp build_nf_view3 build_ty_view1 in Heq ; try solve [inversion Heq]
      end.
    eapply Nat.eqb_eq in Heq as ->.
    now constructor.
  Qed.

  Corollary implem_uconv_graph x r :
    graph _uconv x r ->
    uconv_sound_type x r.
  Proof.
    eapply funrec_graph.
    1: now apply _implem_uconv_sound.
    easy.
  Qed.

  Corollary implem_uconv_sound Γ T V :
    graph uconv (Γ,T,V) ok ->
    [T ≅ V].
  Proof.
    assert (funrec uconv (fun _ => True)
      (fun '(Γ,T,V) r => match r with | success _ => [T ≅ V] | _ => True end)) as Hrect.
    {
     intros ? _.
     funelim (uconv _) ; cbn.
     intros [] ; cbn ; [|easy].
     eintros ?%funrec_graph.
     2: now apply _implem_uconv_sound.
     all: now cbn in *.
    }
    eintros ?%funrec_graph.
    2: eassumption.
    all: now cbn in *.
  Qed.

End UntypedConversionSound.

(** ** Soundness of typing *)
(** Parameterised over the conversion function used and its soundness. *)

Ltac funelim_typing :=
  funelim (typing _ _); 
    [ funelim (typing_inf _ _) | 
      funelim (typing_check _ _) |
      funelim (typing_inf_red _ _) | 
      funelim (typing_wf_ty _ _) ].

Section TypingSound.
  Import AlgorithmicTypingData.

  Context `{ta : tag} `{! ConvType ta}.
  Context (conv : (context × term × term) ⇀ exn errors unit).

  Hypothesis conv_sound : forall Γ T V,
    graph conv (Γ,T,V) ok ->
    [Γ |-[ta] T ≅ V].

  #[universes(polymorphic)]Definition typing_sound_type
    (x : ∑ (c : typing_state) (_ : context) (_ : tstate_input c), term)
    (r : exn errors (tstate_output x.π1)) : Type :=
  match x, r with
  | _, (exception _) => True
  | (wf_ty_state;Γ;_;T), (success _) => [Γ |-[ta] T]
  | (inf_state;Γ;_;t), (success T) => [Γ |-[ta] t ▹ T]
  | (inf_red_state;Γ;_;t), (success T) => [Γ |-[ta] t ▹h T]
  | (check_state;Γ;T;t), (success _) => [Γ |-[ta] t ◃ T]
  end.

  Lemma _implem_typing_sound :
    funrec (typing conv) (fun _ => True) typing_sound_type.
  Proof.
    intros x _.
    funelim_typing ; cbn.
    all: intros ; simp typing_sound_type ; try easy ; cbn.
    all: repeat (
      match goal with
      | |- True * _ => split ; [easy|..]
      | |- forall x : exception _ _, _ => intros [|] ; simp typing_sound_type ; try easy ; cbn
      | |- _ -> _ => simp typing_sound_type ; intros ?
      | |- context [match ?t with | _ => _ end] => destruct t ; cbn ; simp typing_sound_type ; try easy
      | s : sort |- _ => destruct s
      | H : graph wh_red _ _ |- _ => eapply red_sound in H as []
      | H : graph conv _ _ |- _ => eapply implem_conv_sound in H ; simp conv_sound_type in H
      | H : ctx_access _ _ = _ |- _ => eapply ctx_access_correct in H
      | H : (build_ty_view1 _ = ty_view1_small _) |- _ => eapply ty_view1_small_can in H
      | H : (_;_;_) = (_;_;_) |- _ => injection H; clear H; intros; subst 
      end).
    all: try now econstructor.
    - econstructor; tea; now rewrite 2!Weakening.wk1_ren_on.
    - econstructor ; tea.
      apply conv_sound.
      now match goal with | H : unit |- _ => destruct H end.
  Qed.

  Lemma implem_typing_sound x r:
    graph (typing conv) x r ->
    typing_sound_type x r.
  Proof.
    eapply funrec_graph.
    1: now apply _implem_typing_sound.
    easy.
  Qed.

  Lemma _check_ctx_sound :
    funrec (check_ctx conv) (fun _ => True) (fun Γ r => if r then [|- Γ] else True).
  Proof.
    intros ? _.
    funelim (check_ctx _ _) ; cbn.
    - now constructor.
    - split ; [easy|].
      intros [|] ; cbn ; try easy.
      intros ? ? [] ?%implem_typing_sound ; cbn in *.
      2: easy.
      now econstructor.
  Qed.
     
  Lemma check_ctx_sound Γ :
    graph (check_ctx conv) Γ ok ->
    [|-[ta] Γ].
  Proof.
    eintros ?%funrec_graph.
    2: eapply _check_ctx_sound.
    all: easy.
  Qed.

End TypingSound.