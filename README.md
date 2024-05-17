Presentation
=======

This repo contains the formalisation work accompanying the paper [*“Upon This Quote I Will Build My Church Thesis”*](https://www.xn--pdrot-bsa.fr/articles/quotett.pdf).

The formalization is based on a [previous work](https://github.com/coqhott/logrel-coq/) by Adjej et al ([*Martin-Löf à la Coq*, CPP'24](https://arxiv.org/abs/2310.06376)), which itself follows a similar [Agda formalization](https://github.com/mr-ohman/logrel-mltt/) (described in [*Decidability of conversion for Type Theory in Type Theory*, 2018](https://dl.acm.org/doi/10.1145/3158111)). In order to avoid some work on the syntax, this project uses the [AutoSubst](https://github.com/uds-psl/autosubst-ocaml) project to generate syntax-related boilerplate.

TL;DR HOWTO INSTALL
===================

- Install opam through your favourite means.
- Double-check that no Coq-related environment variables like COQBIN or COQPATH are set.
- Launch the following commands in the folder of this development.
```
opam switch create . --empty
eval $(opam env)
opam install ocaml-base-compiler=4.11.2
opam repo --this-switch add coq-released https://coq.inria.fr/opam/released
opam install . --deps-only
make
```

IMPORTANT NOTE
==============

The coqdocjs subfolder is **not** part of this development, but an independent project vendored here for simplicity of the build process. The upstream repository can be found at https://github.com/coq-community/coqdocjs/.

Building
===========

The project builds with Coq version `8.20.0`, and depends on the [`smpl`](https://github.com/uds-psl/smpl/) and [Equations](https://github.com/mattam82/Coq-Equations/) libraries.
If you already have an opam set-up, dependencies can be installed by simply using `opam install . --deps-only`.

Once the dependencies have been installed, you can simply issue `make` in the root folder to
build the whole development.

The `make depgraph` recipe can be used to generate the [dependency graph](https://coqhott.github.io/logrel-coq/dependency_graph.png).

The project uses the [AutoSubst](https://github.com/uds-psl/autosubst-ocaml) tool to generate syntax-related boilerplate, although it is not necessary to install it to build the project (see below for how to use it).

Browsing the development
==================

The development, rendered using `coqdoc`, can be [browsed online](https://coqhott.github.io/logrel-coq/). A dependency graph for the project is available [here](https://coqhott.github.io/logrel-coq/dependency_graph.png).

Syntax regeneration
====================

For simplicity, we include the syntax file (`Ast.v`) generated using [AutoSubst](https://github.com/uds-psl/autosubst-ocaml).

It can be re-generated using the `make autosubst` recipe, once `autosubst-ocaml` (version `>= 1.1`) has been installed.

Note that we include modified versions of the `core` and `unscoped` files, which fix their dependencies, so one should pass the `-no-static` option to `AutoSubst` to avoid overwriting them.

Getting started with using the development
=================

A few things to get accustomed to if you want to use the development.

Notations and refolding
-----------

In a style somewhat similar to the [Math Classes](https://math-classes.github.io/) project,
generic notations for typing, conversion, renaming, etc. are implemented using type-classes.
While some care has been taken to try and respect the abstractions on which the notations are
based, they might still be broken by carefree reduction performed by tactics. In this case,
the `refold` tactic can be used, as the name suggests, to refold all lost notations.

Induction principles
----------

The development relies on large, mutually-defined inductive relations. To make proofs by induction
more tractable, functions `XXXInductionConcl` are provided. These take the predicates
to be mutually proven, and construct the type of the conclusion of a proof by mutual induction.
Thus, a typical induction proof looks like the following:

``` coq-lang
Section Foo.

Let P := … .
…

Theorem Foo : XXXInductionConcl P … .
Proof.
  apply XXXInduction.

End Section.
```
The names of the arguments printed when querying `About XXXInductionConcl` should make it clear
to which mutually-defined relation each predicate corresponds.

[Utils]: ./theories/Utils.v
[BasicAst]: ./theories/BasicAst.v
[Context]: ./theories/Context.v
[AutoSubst/]: ./theories/AutoSubst/
[AutoSubst/Extra]: ./theories/AutoSubst/Extra.v
[Notations]: ./theories/Notations.v
[Automation]: ./theories/Automation.v
[NormalForms]: ./theories/NormalForms.v
[UntypedReduction]: ./theories/UntypedReduction.v
[GenericTyping]: ./theories/GenericTyping.v
[DeclarativeTyping]: ./theories/DeclarativeTyping.v
[Properties]: ./theories/Properties.v
[DeclarativeInstance]: ./theories/DeclarativeInstance.v
[LogicalRelation]: ./theories/LogicalRelation.v
[Induction]: ./theories/LogicalRelation/Induction.v
[Escape]: ./theories/Escape.v
[Reflexivity]: ./theories/Reflexivity.v
[Irrelevance]: ./theories/Irrelevance.v
[ShapeView]: ./theories/ShapeView.v
[Positivity.v]: ./theories/Positivity.v
[Weakening]: ./theories/Weakening.v
[Substitution]: ./theories/Substitution.v
[AlgorithmicTyping]: ./theories/AlgorithmicTyping.v
[AlgorithmicConvProperties]: ./theories/AlgorithmicConvProperties.v
[AlgorithmicTypingProperties]: ./theories/AlgorithmicTypingProperties.v
[LogRelConsequences]: ./theories/LogRelConsequences.v
[BundledAlgorithmicTyping]: ./theories/BundledAlgorithmicTyping.v

[autosubst-ocaml]: https://github.com/uds-psl/autosubst-ocaml
[Positivity.agda]: ./theories/Positivity.agda
