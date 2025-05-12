Browsing the sources
============================

The full table of content of the development is accessible [here](https://coqhott.github.io/logrel-coq/coqdoc/toc.html).
To complement it, here is an outline of the development's main files, roughly in dependency order.

Utilities
---------

| File | Description |
|---|----|
[Utils] | Basic generically useful definitions, notations, tactics…
[PERTactics] | Ltac2 tactics to manipulate partial equivalence relations.


Syntax
--------

Primarily in the [Syntax](https://github.com/CoqHott/logrel-coq/tree/coq-8.20/theories/Syntax) folder, contains definitions related to the syntax of terms, independent of typing: contexts, untyped reduction, normal forms, weakenings… See also the [AutoSubst](https://github.com/CoqHott/logrel-coq/tree/coq-8.20/theories/AutoSubst) folder, which contains everything related to the [AutoSubst] tool.

[Syntax.BasicAst] | Definitions preceding those of the AST of terms (for now, only sorts)
[AutoSubst.Ast] | Abstract syntax tree, definitions of renamings, substitutions and many lemmas. Generated using the [AutoSubst] tool.
[Notations] | Notations for all judgments used throughout the development. It can be used as an index for notations!
[Syntax.NormalForms] | Definition of normal and neutral forms, and properties.
[Syntax.UntypedReduction] | Definition and basic properties of untyped reduction, used to define algorithmic typing.


Basic typing-related definitions and properties
-------

Primarily in the [Typing](https://github.com/CoqHott/logrel-coq/tree/coq-8.20/theories/Typing) folder. We gather the important properties of typing in [TypingProperties.PropertiesDefinition], then derive their consequences in a series of files. Finally, we show that these properties are consequences of the fundamental lemma of the (proper instantiations of the) logical relation in [TypingProperties.LogRelConsequences]. This file also contains derivations of important meta-theoretic properties such as canonicity, consistency…

| File | Description |
|---|----|
[GenericTyping] | A generic notion of typing, used to define the logical relation. It is instantiated multiple times, with different variants of typing, to derive gradually stronger properties.
[DeclarativeTyping] | Specification of conversion and typing, in a standard, declarative fashion. |
[TypingProperties.DeclarativeInstance] | Proof that declarative typing is an instance of generic typing. |
[TypingProperties.PropertiesDefinition] | Definition of the high-level, abstract properties of conversion and typing, that we obtain as consequences of the logical relation.
[TypingProperties.LogRelConsequences] | Proofs that the properties from [TypingProperties.PropertiesDefinition] are consequences of the logical relation.

Logical relation
-----------

The files in the [LogicalRelation.Definition](https://github.com/CoqHott/logrel-coq/tree/coq-8.20/theories/LogicalRelation/Definition) folder give the definition of each of the cases of the logical relation, which are assembled in [LogicalRelation.Def]. Files in the [LogicalRelation](https://github.com/CoqHott/logrel-coq/tree/coq-8.20/theories/LogicalRelation) folder derive general properties of the logical relation, and those in [LogicalRelation.Introductions](https://github.com/CoqHott/logrel-coq/tree/coq-8.20/theories/LogicalRelation/Introductions) derive the reducibility some term formers.

However the logical relation as defined in [LogicalRelation.Def] is not a model of typing, only its closure under reducible substitution is. This is defined in [Validity.Validity], and the remaining properties are proven in the [LogRel.Validity](https://github.com/CoqHott/logrel-coq/tree/coq-8.20/theories/Validity) folder.

Finally, [Fundamental] derives the fundamental theorem of the logical relation. Note that only [TypingProperties.LogRelConsequences] directly uses this fundamental lemma. All other files only use the properties in [TypingProperties.PropertiesDefinition] instead.

| File | Description |
|---|----|
[LogicalRelation.Def] | Contains the logical relation's definition. |
[LogicalRelation.Induction] | We derive by hand better induction principles for the logical relation, which handle some repacking and universe-related shenanigans once and for all. |
[LogicalRelation.Escape] | The escape lemma: the logical relation implies conversion/typing. |
[Validity.Validity] | Definition of validity: closure of the logical relation under substitution. |
[Fundamental] | Fundamental theorem: declarative typing implies the logical relation (for any generic instance). |


Algorithmic typing
-----------------

The second big part of the formalisation explores algorithmic presentations of the type system, and decision procedures.

| File | Description |
|---|----|
[AlgorithmicJudgments] | Definition of type-directed and untyped conversion and algorithmic typing, as inductive predicates.
[Algorithmic.Bundled] | Algorithmic judgments bundled with their pre-conditions, and tailored induction principles showing invariant preservation in the "algorithm".


Implementations
----------------

The various functions for conversion-checking and type-checking are defined and verified in the [Checkers]() folder.

| File | Description |
|---|----|
[Checkers.Functions] | Definition of the conversion and type-checker (both type-directed and term-directed).
[Decidability] | Type-checking is decidable.
[Checkers.Execution] | Example executions of the type checker, in Coq.

Miscellaneous
----------------------

The [Misc]() folder contains files that are not strictly necessary for the development, but that we keep around for curiosity.

| File | Description |
|---|----|
[Misc.Positivity](https://github.com/CoqHott/logrel-coq/blob/coq-8.20/theories/Misc/Positivity.v) | A discrepancy in positivity-checking inductive types between Agda and Coq, which was a source of difficulties when first setting up the logical relation in Coq.



[Utils]: https://coqhott.github.io/logrel-coq/coqdoc/LogRel.Utils.html
[PERTactics]: https://coqhott.github.io/logrel-coq/coqdoc/LogRel.PERTactics.html
[Syntax.BasicAst]: https://coqhott.github.io/logrel-coq/coqdoc/LogRel.Syntax.BasicAst.html
[Context]: https://coqhott.github.io/logrel-coq/coqdoc/LogRel.Context.html
[AutoSubst.Extra]: https://coqhott.github.io/logrel-coq/coqdoc/LogRel.AutoSubst.Extra.html
[AutoSubst.Ast]: https://coqhott.github.io/logrel-coq/coqdoc/LogRel.AutoSubst.Ast.html
[Notations]: https://coqhott.github.io/logrel-coq/coqdoc/LogRel.Notations.html
[Syntax.NormalForms]: https://coqhott.github.io/logrel-coq/coqdoc/LogRel.Syntax.NormalForms.html
[Syntax.UntypedReduction]: https://coqhott.github.io/logrel-coq/coqdoc/LogRel.Syntax.UntypedReduction.html
[GenericTyping]: https://coqhott.github.io/logrel-coq/coqdoc/LogRel.GenericTyping.html
[DeclarativeTyping]: https://coqhott.github.io/logrel-coq/coqdoc/LogRel.DeclarativeTyping.html
[TypingProperties.DeclarativeInstance]: https://coqhott.github.io/logrel-coq/coqdoc/LogRel.TypingProperties.DeclarativeInstance.html
[TypingProperties.PropertiesDefinition]: https://coqhott.github.io/logrel-coq/coqdoc/LogRel.TypingProperties.PropertiesDefinition.html
[TypingProperties.LogRelConsequences]: https://coqhott.github.io/logrel-coq/coqdoc/LogRel.TypingProperties.LogRelConsequences.html

[LogicalRelation.Def]: https://coqhott.github.io/logrel-coq/coqdoc/LogRel.LogicalRelation.Definition.Def.html
[LogicalRelation.Induction]: https://coqhott.github.io/logrel-coq/coqdoc/LogRel.LogicalRelation.Induction.html
[LogicalRelation.Escape]: https://coqhott.github.io/logrel-coq/coqdoc/LogRel.LogicalRelation.Escape.html
[Validity.Validity]: https://coqhott.github.io/logrel-coq/coqdoc/LogRel.Validity.Validity.html
[Fundamental]: https://coqhott.github.io/logrel-coq/coqdoc/LogRel.Fundamental.html

[AlgorithmicJudgments]: https://coqhott.github.io/logrel-coq/coqdoc/LogRel.AlgorithmicJudgments.html
[Algorithmic.Bundled]: https://coqhott.github.io/logrel-coq/coqdoc/LogRel.Algorithmic.Bundled.html

[Checkers.Functions]: https://coqhott.github.io/logrel-coq/coqdoc/LogRel.Checkers.Functions.html
[Decidability]: https://coqhott.github.io/logrel-coq/coqdoc/LogRel.Decidability.html
[Checkers.Execution]: https://coqhott.github.io/logrel-coq/coqdoc/LogRel.Checkers.Execution.html

[AutoSubst]: https://github.com/uds-psl/autosubst-ocaml