# Pure MLIR institutions

`Silmaril.MLIR.Institution.regionless` and `Silmaril.MLIR.Institution.isolated`
are `ClassicInstitution`s built through `Silmaril.Logic.Institution.Room`.
The first admits only regionless operations. The second also admits operations
with ordered isolated single-block regions. In both, operand and result
positions have specified sorts. Each region has its own ordered parameter and
yield sorts. `Signature.Hom` maps sorts and operation symbols, preserving all
positions and mapping the sorts of the corresponding profiles. The maps can
identify sorts or symbols. [Definitions](../../Silmaril/SSA/MLIR/Institution/Defs.lean) ·
[Institution laws](../../Silmaril/SSA/MLIR/Institution/Thms.lean)

## Typed signature category

`Silmaril.SSA.MLIR.Signature.Thms` exposes the signature category on its own.
`Signature.withRegions` is a fully faithful functor from `Signature false` to
`Signature true`. It keeps the sorts and symbols and gives each operation zero
region slots. `includeRegionless` gives a natural family of `Room` corridors
along this functor. It translates equations forward and restricts models
backward, preserving and reflecting satisfaction in each model.
[Signature API](../../Silmaril/SSA/MLIR/Signature/Thms.lean) ·
[Institution inclusion](../../Silmaril/SSA/MLIR/Institution/Regionless/Thms.lean)

`Signature.disjointSum` is a binary coproduct for either choice of region
policy. It tags sorts and operation symbols by dialect, including when both
dialects start with the same sort type. The mediator can identify the images
of two tagged sorts. `disjointSum.isColimit` checks both factorization laws
and uniqueness in the signature category.

These arrows are typed renamings. An operation-to-block interpretation can
expand a symbol to several applications, and a model interprets symbols as
functions. The institution below uses discrete categories of such models.

```sh
lake build --wfail +Silmaril.SSA.MLIR.Signature.Thms \
  +Silmaril.SSA.MLIR.Institution.Regionless.Thms
```

## Sentences and models

A block has one expression per yielded value. An application selects a result
from a pure total operation. Each body is typed in precisely its declared
parameter context. A set model assigns a carrier to each sort and interprets
an operation as a function of its operands and one function per region. Each
region function takes a parameter assignment and returns a yield assignment.
The operation can call the region function on any typed inputs. The categories
of models are discrete. A sentence equates two blocks of the same type under
every input assignment.

`Term.map_id`, `Term.map_comp`, `Equation.map_id` and `Equation.map_comp` prove
covariance. `reductFunctor_id` and `reductFunctor_comp` prove the reduct laws.
`Term.denote_map` proves evaluation commutes with symbol and sort reindexing.
At each region slot the proof takes an arbitrary fresh parameter assignment and
uses induction for every yield. Function extensionality then gives equality of
the region arguments to the operation. `satisfaction` lifts the result to
universal equations. [Proofs](../../Silmaril/Proofs/SSA/MLIR/Institution/Laws.lean)

## Arithmetic and lowering

`Arith.translate` interprets every block of the
[scalar fragment](mlir.md), including scoped application, in the isolated
institution. It substitutes the term for an SSA definition at uses and
starts each region body with just its declared parameter. `Arith.translate_denote`
proves agreement for all typed input assignments from that fragment.
`Arith.translate_lambdaSSA_eval_iff` and `Arith.translate_letIter_eval_iff`
compose it with the existing single-exit semantics theorems.
`Arith.Examples.squareAdd_tag_denote` tags the sorts and symbols of the scoped
arithmetic example and computes 164 at width eight for an input of 20, with an
independent width-one value still in the ambient context.
[Arithmetic theorems](../../Silmaril/SSA/MLIR/Institution/Arith/Thms.lean) ·
[Examples](../../Silmaril/SSA/MLIR/Institution/Arith/Examples/Thms.lean)

A signature map replaces each symbol with one symbol at its mapped profile.
An operation-to-block lowering replaces an application with a typed program.
For example, replacing doubling by addition with materializing two and
multiplying uses a different block shape. `Arith.Examples.double_lowering_denote`
transfers the scalar rewrite to institution denotations for every positive
width. Lowerings specified by target blocks would require a translation on
syntax respecting substitution and isolated binding, with an interpretation
hypothesis for each replacement and a contextual preservation proof.

## Categorical scope

`Syntax.Context` is the raw syntax category. Arrows are tuples of terms,
identities are projections, and composition is simultaneous substitution into
the outer context. Isolated bodies retain their parameter contexts during this
substitution. `Syntax.denote` interprets arrows as total functions in `Type`.
`Syntax.map` acts on contexts and blocks and `Syntax.map_denote` proves the
reindexing square. [Syntax category](../../Silmaril/SSA/MLIR/Institution/Syntax/Defs.lean)

For a category modulo a chosen equational theory, define typed equivalence
closed under simultaneous substitution and congruence in operands and region
bodies, then prove composition and evaluation descend. Finite products need a
terminal empty context and the universal property of context concatenation.
A binder interpretation outside `Type` needs a specified representation of
region functions, for example exponentials, and their coherence laws. A
categorical comparison with [LambdaSSA or LetIter](ssa.md) also needs a target
fragment with matching interfaces and observation equivalence, a map of
contexts and typed arrows respecting composition and congruence, and an
adequacy or inverse theorem at the intended quotient. The checked comparison
here is per arithmetic block. The [existing Elgot/Freyd model interface](../../Silmaril/SSA/Thesis/Categorical/Thms.lean)
would require its own coherence hypotheses for an extension with effects.

This expression syntax treats SSA sharing as unobservable. Coverage is pure
total operations with isolated region bodies. It excludes captures, multiblock
control flow, effects, divergence, poison, and undefined behavior. The
arithmetic bridge is for positive-width signless bitvectors, constants,
unflagged addition and multiplication, and unary scoped application.

The Lean development is original and uses the existing Silmaril APIs. The
[MLIR language reference](https://mlir.llvm.org/docs/LangRef/) describes blocks
and regions. The institution interface documents its scholarly sources in
[`Basic.lean`](../../Silmaril/Logic/Institution/Basic.lean).
