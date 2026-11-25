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

`Signature.FixedSorts` gives the category over a specified common sort type.
Its arrows fix each sort and act on symbols at each complete profile.
`FixedSorts.sum` takes a disjoint sum of symbol families at each profile,
leaving one copy of the common sorts. `FixedSorts.sum.isColimit` proves the
universal property in that category. `FixedSorts.toSignature` reads these
arrows as renamings with identity sort maps. Both categories provide Mathlib's
`HasBinaryCoproducts` instance. [Fixed-sort API](../../Silmaril/SSA/MLIR/Signature/FixedSorts/Thms.lean)

`Signature.Hom` renames symbols one at a time. An `Interpretation` can expand
a regionless primitive to a target block and can forward an operation with
regions at its mapped profile. [Typed interpretations](mlir-pure-interpretations.md)

```sh
lake build --wfail +Silmaril.SSA.MLIR.Signature.Thms \
  +Silmaril.SSA.MLIR.Signature.FixedSorts.Thms \
  +Silmaril.SSA.MLIR.Institution.Regionless.Thms
```

### Extending an isolated dialect at fixed sorts

The fixed-sort coproduct allows fresh labels with region slots when the region
flag is `true`. It retains the common sorts and the full ordered operand,
result, parameter, and yield profiles. Its universal property is in the
identity-sort fiber. Two unrestricted renamings can disagree on a shared sort,
so they need not have a mediator from the fixed-sort sum. The disjoint-sort
coproduct gives them separate copies of that sort.

The checked example adds one execute-once label with an explicit parameter and
a yielded result. The body uses old Arith addition and receives only the
declared parameter. Lean identifies the coproduct mediator that keeps old
labels and maps the fresh one to Arith's existing isolated application. It
checks the doubled result before and after renaming at every positive width,
including `200 : i8` yielding `144` with an unused outer input.
[Example and theorems](../../Silmaril/SSA/MLIR/Signature/FixedSorts/Examples/Thms.lean)

The example uses the pure total expression model. Upstream `scf.execute_region`
has no entry arguments and can access dominating captures and contain multiple
blocks. The separate `scf.while` to CF development checks successor transfers,
finite returns, and divergence for its single-loop fragment. The fixed-sort
result concerns symbol renamings, with separate laws for operation-to-block
interpretations and model reducts.
[#3167 structural lowering](https://github.com/hiloopai/silmaril-lean/pull/3167) ·
[#3169 zero-region primitive extension](https://github.com/hiloopai/silmaril-lean/pull/3169) ·
[Upstream SCF reference](https://mlir.llvm.org/docs/Dialects/SCFDialect/#scfexecute_region-scfexecuteregionop)

```sh
lake build --wfail +Silmaril.SSA.MLIR.Signature.FixedSorts.Examples.Thms
make check CHECK_TARGETS=+Silmaril.SSA.MLIR.Signature.FixedSorts.Examples.Thms
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

`Arith.Examples.double_lowering_denote` transfers the scalar rewrite from
addition-based doubling to multiplication by two to institution denotations
for every positive width.

## Categorical scope

`Syntax.Context` is the raw syntax category. Arrows are tuples of terms,
identities are projections, and composition is simultaneous substitution into
the outer context. Isolated bodies retain their parameter contexts during this
substitution. `Syntax.denote` interprets arrows as total functions in `Type`.
`Syntax.map` acts on contexts and blocks and `Syntax.map_denote` proves the
reindexing square. [Syntax category](../../Silmaril/SSA/MLIR/Institution/Syntax/Defs.lean)

The observational quotient identifies parallel arrows that agree in selected
models. The empty context is terminal and concatenation gives binary products.
The arithmetic comparison relates parallel single-result arrows to typed
return observations in LambdaSSA and LetIter. [Observational quotient and comparison](mlir-pure-interpretations.md)

A binder interpretation outside `Type` needs a representation of region
functions and coherence laws. A categorical comparison with LambdaSSA or
LetIter also needs a target observation category and a composition-preserving
map of contexts and arrows. [SSA categorical results](ssa.md)

This expression syntax treats SSA sharing as unobservable. Coverage is pure
total operations with isolated region bodies. It excludes captures, multiblock
control flow, effects, divergence, poison, and undefined behavior. The
arithmetic bridge is for positive-width signless bitvectors, constants,
unflagged addition and multiplication, and unary scoped application.

The Lean development is original and uses the existing Silmaril APIs. The
[MLIR language reference](https://mlir.llvm.org/docs/LangRef/) describes blocks
and regions. The institution interface documents its scholarly sources in
[`Basic.lean`](../../Silmaril/Logic/Institution/Basic.lean).
