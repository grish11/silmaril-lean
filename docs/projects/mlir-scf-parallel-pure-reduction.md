# Pure one-dimensional SCF parallel reduction

## Iteration domain

`IndexSpace` uses unbounded natural numbers for the lower bound, upper bound, and positive step.
It is the nonnegative, mathematical-index slice of the one-dimensional half-open iteration
space. The trip count is `(upper - lower + (step - 1)) / step`, with natural subtraction.
`rank_lt_tripCount` shows that exactly the ranks below this count produce indices
`lower + rank * step < upper`. These indices are at least the lower bound and are distinct.
`upper_le_exitIndex` locates the value `lower + tripCount * step` at or beyond the upper
bound, and `tripCount_eq_zero` characterizes the empty range. [Lean statements](../../Silmaril/SSA/MLIR/SCF/Parallel/Thms.lean)

The pinned upstream `scf.parallel` predicates use positive steps, half-open bounds, signed
comparison by default and optional unsigned comparison. Upstream also requires
`LB + n * Step` to be representable at the machine index width. Unbounded naturals here
give exact arithmetic for the nonnegative values. Connecting a fixed-width execution to this
slice requires checking the chosen signedness, nonnegative values and representability,
including the exit index. [Pinned SCF definitions](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/include/mlir/Dialect/SCF/IR/SCFOps.td#L820-L880)

## Admissible results and the reference fold

- A pure body supplies a typed contribution for each induction value. Each reduction slot has
  a typed initial value and a total binary combiner. The combiner's output has the same type
  as its two inputs, corresponding to the value of `scf.reduce.return`. `GroupedReduction`
  gives finitely many slots with separate carriers and combiners. Within a group, the slots
  share the trip enumeration and tree. [Typed interface](../../Silmaril/SSA/MLIR/SCF/Parallel/Defs.lean)
- An enumeration permutes the increasing list of finite trip ordinals. Theorems show that
  every trip appears and no trip appears twice. A tree has the initial value as its first
  leaf, followed by one contribution for each trip in the chosen order. All binary
  parenthesizations of that sequence are admitted. This defines the choices of the local
  pure result relation. [Upstream reduction and return](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/include/mlir/Dialect/SCF/IR/SCFOps.td#L940-L1016)
- `Reduction.denote` fixes increasing trip order and left association.
  `Reduction.returns_denote` shows that this fold is always an admissible result.
  Associativity gives equality across tree shapes at a fixed order. With commutativity
  as well, `Reduction.returns_iff_eq_denote` gives exactly one result across all
  admitted orders and shapes. The initial value is used exactly once, so the theorem
  needs no identity law. The grouped version requires the two laws at each slot. [Lean statements](../../Silmaril/SSA/MLIR/SCF/Parallel/Thms.lean)
- With zero trips, every admissible tree and the reference fold return the initial value
  for any combiner. The checked order-sensitive case uses bounds `[1, 5)` and step `3`.
  With initial value `99` and the associative combiner that returns its right input, the
  increasing order returns `4` and the reversed order returns `1`. [Lean statements](../../Silmaril/SSA/MLIR/SCF/Parallel/Thms.lean)

The model observes result values. Operational workers, shared effects, scheduling, the upstream
data-race rule and multidimensional spaces remain outside this slice. A LetIter boundary could
type the body's index argument and heterogeneous contribution tuple and give each combiner two
arguments of its slot type. Relating such a boundary to the result relation would require a
separate typing and observation theorem. Region return at this boundary supplies an SSA value
to the enclosing reduction. Resumption and scheduling events require their own operational
semantics. [SCF reference](https://mlir.llvm.org/docs/Dialects/SCFDialect/)

## Check

```sh
lake build --wfail +Silmaril.SSA.MLIR.SCF.Parallel.Thms
make check CHECK_TARGETS=+Silmaril.SSA.MLIR.SCF.Parallel.Thms
```
