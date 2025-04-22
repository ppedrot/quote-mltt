(** An example of a form of nested inductive type accepted by Agda, but not by Rocq *)


Unset Automatic Proposition Inductives.
Record Foo (x : Type -> Type) : Type := {}.

Fail Inductive Bar : Type -> Type :=
    | bar : Bar (Foo Bar).

(* Fails with: Non strictly positive occurrence of "Bar" in "Bar (Foo Bar)". *)

(** Rocq does not accept nested inductive types in indices, while Agda does.
  This was a source of complications when porting Loïc Pujet's first IR-free
  version of the Agda development to Rocq. *)