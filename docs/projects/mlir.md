# MLIR-style scalar SSA

Import `Silmaril.SSA.MLIR.Thms` to construct a typed scalar block, lower it to
LambdaSSA and LetIter, and reason about both targets' results. The source
constructors and lowering names live in `Silmaril.MLIR.Arith`.
[`MLIR/Thms.lean`](../../Silmaril/SSA/MLIR/Thms.lean)

The same import provides `MLIR.FuncOf` and `MLIR.FuncModule` for packaging
these or other typed bodies as named functions.
[Typed function modules](mlir-function-modules.md)

`Block Γ w` takes an `Env Γ` and denotes a `BitVec w.val`. Contexts are
newest first. Use `.letOp` and `.yield` for straight-line code. The
`.letRegion arg body rest` form passes one explicit value to an isolated
single-block body, binds the yielded value, and continues with `rest`.
The body starts with a singleton context, and applications can nest. Positive
widths, scalar signless constants, and unflagged modular addition and
multiplication define this lowering profile.
[`Arith/Defs.lean`](../../Silmaril/SSA/MLIR/Arith/Defs.lean)

```lean
import Silmaril.SSA.MLIR.Thms

open Silmaril.MLIR.Arith
open Silmaril.Isotope.Institution.Observational

def i8 : Width := ⟨8, by decide⟩
def twice : Block [i8] i8 :=
  .letOp (.binary .addi .here .here) (.yield .here)
def input : Env [i8] := .cons 200#8 .nil

example : iterBeh input.observationModel twice.toLetIter =
    {Observation.ret () (word (w := i8) 144#8) ()} :=
  twice.toLetIter_observations input

example : ssaBeh 1 input.observationModel twice.toScopedLambdaSSA =
    {Observation.ret () (0, word (w := i8) 144#8) ()} :=
  twice.toLambdaSSA_observations input
```

## Checked translations

| Theorem | Statement |
| --- | --- |
| `Block.toLambdaSSA_hasType`, `Block.toLetIter_hasType` | Both lowerings have the declared input and result types. |
| `Block.toLambdaSSA_eval_iff`, `Block.toLetIter_eval_iff` | On every typed input the lowerings return exactly the source denotation. LambdaSSA returns at exit zero. |
| `Block.toLambdaSSA_observations`, `Block.toLetIter_observations` | Under `Env.observationModel`, each full behavior set is the singleton return. |
| `Block.toLetIter_quotEquiv` | The existing single-exit quotient equivalence maps the actual LambdaSSA class to the actual LetIter class. |

`Block.toScopedLambdaSSA` packages the same region as `Block.toLambdaSSA`
with its scope evidence. `Block.toLetIter` applies `SSAIter.encodeSingle`
to that region. The quotient comparison uses `SSAIter.quotEquiv`, the
program map on the inverse side of `Observational.iterSSAIso`. The
singleton observations use the concrete arithmetic model at a typed input.
The quotient ranges over the calculi's shared observational equivalence,
which quantifies over primitive interpretations.
[LambdaSSA](../../Silmaril/SSA/MLIR/Arith/Thms.lean) ·
[LetIter](../../Silmaril/SSA/MLIR/Arith/LetIter/Thms.lean) ·
[Isotope institutions](../../Silmaril/SSA/Isotope/Institution/Thms.lean)

The `Examples.doubleMul_lambdaSSA` and `Examples.doubleMul_letIter`
theorems check doubling `200 : BitVec 8` to `144`. The
`Examples.squareAdd_lambdaSSA` and `Examples.squareAdd_letIter` theorems
check squaring `20 : BitVec 8` in an isolated region and adding it to
the original input for `164`. The theorem `Examples.double_lowering`
validates the source rewrite from `addi x x` to multiplication by two
at every width. The smoke test also checks a closed block and nested
isolated regions whose input and result widths differ.
[Examples](../../Silmaril/SSA/MLIR/Arith/Examples/Thms.lean) ·
[Smoke test](../../Silmaril/SSA/MLIR/Examples/Thms.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.MLIR.Examples.Thms +Silmaril.SSA.MLIR.Arith.Examples.Thms'
```

The pure plain and isolated-region signature institutions have a separate
general syntax and satisfaction API. This lowering covers the concrete
arithmetic blocks above. [Pure MLIR institutions](mlir-institutions.md)

## Roadmap

1. **Plain and region signatures.** A plain signature has a set of sorts and
   operation symbols with ordered operand and result sort lists. Begin with
   total models that assign a carrier (A_s) to each sort and a function between
   the corresponding products to each operation. Extend a region signature
   with an ordered list of region profiles per operation, each specifying
   parameter sorts, yielded sorts, and which captures are admitted. For
   isolated regions, an operation receives one extra argument per region
   of type (prod A_{mathrm{params}} 	o prod A_{mathrm{yields}}). Add
   captures later as explicit environment arguments, and require translation
   to respect that typing and binding structure.
2. **Signature change and institutions.** Start with typed symbol maps
   (sigma : Sigma 	o Sigma') that map sorts and operation symbols and
   preserve all mapped profiles, including region scopes. Sentences are
   equations between blocks with the same typed input and output interfaces,
   universally quantified over their inputs. (mathrm{Sen}(sigma)) maps
   symbols throughout a block, including its nested bodies. The reduct
   (M'|_sigma) pulls carriers and operation interpretations back along the
   symbol map. With discrete model categories initially, prove functoriality
   of renaming and reduct and prove the satisfaction condition
   (M' models mathrm{Sen}(sigma)(e) iff M'|_sigma models e) by a
   denotation lemma. Its region case uses the induction hypothesis at each
   parameter assignment, then the mapped operation's interpretation.
   The pure signature laws are checked. [Pure MLIR institutions](mlir-institutions.md)
3. **Categorical semantics.** Use contexts as objects and tuples of block
   results as arrows modulo a typed congruence closed under substitution
   and region contexts. Use projections for identity and capture-avoiding
   substitution or sequencing for composition. Prove the category and finite-product laws and interpret it
   in a category of total functions, with products for contexts. For
   region-bearing models, require an interpretation of the binders, for
   example using exponentials in a cartesian closed target for the pure
   function-valued region arguments above. Compare the resulting category
   and the LambdaSSA/LetIter interpretations on their common fragment using
   the checked lowering and prove naturality under signature change before
   asking for an equivalence. Effectful or iterative regions will require
   explicit laws of the chosen model, with the existing distributive Freyd
   and Elgot developments as candidates. [SSA categorical results](ssa.md)
4. **Compilation.** A lowering may implement an operation by a typed target
   block with formal operands and, for region-bearing operations, translated
   scoped bodies. Composition then substitutes blocks for operations.
   `Examples.double_lowering` checks one such replacement in the total
   bitvector model. Prove its contextual lifting before using it as a
   general pass. Equality suits this pure deterministic slice. For a
   restricted or nondeterministic source, specify an admission predicate,
   input and observation correspondence, and show that the related target
   behaviors are included in the source's allowed behaviors on admitted
   inputs. A compiler validation result is semantic preservation or
   refinement under those explicit hypotheses.

## Staged dialect coverage

| Stage | Intended slice |
| --- | --- |
| Tiny scalar dialects | Add a few flag-free bit operations and comparisons, then tuples and explicit block arguments as needed. Build the signature-change and scoped-substitution laws over these examples. |
| Static tensor | A tensor of shape `[d₀, …, dₖ₋₁]` is a total function from `Fin d₀ × … × Fin dₖ₋₁` to its element carrier, with a singleton index domain for rank zero. Start with constants, elementwise maps and shape-checked indexing. Use extensional equality. |
| Scoped affine | Integer affine maps and bounded single-block loops with typed loop-carried parameters and yields. Begin without mutable memory and relate admitted loops to finite folds. |
| Minimal LLVM and future x86 validation | Start with pure single-block scalar integers, concrete defined inputs, constants, unflagged modular add/subtract/multiply and a return. Reject every instruction outside the profile. Initially exclude flags, shifts/division, `freeze`, `undef`, poison inputs and instructions that can produce poison, pointers, memory, calls and control flow. Keep unsupported syntax an admission error, immediate UB a separate execution outcome or semantic condition, poison a deferred value state and `undef` a use-dependent choice in extensions. Add one feature at a time and prove semantic refinement on the admitted defined inputs against a specified x86 observation and ABI. |
| Larger dialects | Add small pure static-shape **StableHLO** operators first. For **Triton/Gluon**, start with layout-indexed pure tensor operations, then specify memory and parallel execution explicitly. For a **C dialect**, start with pure scalar expressions whose C types and definedness preconditions are explicit and relate those to the C semantics. |

## Sources

- The [MLIR Language Reference](https://mlir.llvm.org/docs/LangRef/) specifies
  blocks and regions. The [Arith dialect reference](https://mlir.llvm.org/docs/Dialects/ArithOps/)
  specifies the scalar operations and overflow flags.
- [VeIR](https://github.com/opencompl/veir/tree/4888294eb0bd4acba85ba530f57408b356160f05)
  is a design reference for MLIR in Lean. Its
  [license](https://github.com/opencompl/veir/blob/4888294eb0bd4acba85ba530f57408b356160f05/LICENSE)
  is Apache-2.0 with LLVM exceptions. This development uses original code and
  the existing Silmaril LambdaSSA and LetIter APIs.
- The [LLVM Language Reference](https://llvm.org/docs/LangRef.html) and
  [LLVM IR Undefined Behavior Manual](https://llvm.org/docs/UndefinedBehavior.html)
  specify the future LLVM validation boundary.
