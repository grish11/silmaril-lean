# Finite cost selection for cyclic Peggy candidates

This is a finite-pool slice of profitability selection in
[Peggy §8.3](https://arxiv.org/abs/1012.1802v3). It uses the existing
class-labelled extraction checks and the automatic SIMPLE reverter for
a parentless single loop with primitive guard and update slices and one
sampled return.

## Admission and selection

Each pool entry supplies a typed materialized PEG, its
source-representative assignment, and common-row evidence.
`Candidate.wire` is a constructor for entries that copy source labels
and provide new typed operands and roots. It infers a candidate demand
rank and produces the common-row evidence from the actual wiring.

`Candidate.checkLegal` validates the decreasing non-feedback rank,
the Figure 11 demand rank, the output class, and the class of each
ordered operand. The feedback-rank theorem is Definition 5.1(1) for the
actual candidate table. `Candidate.check` also requires
`Region.Automatic.extract` to return a checked boundary and schedule
for that exact graph. `Accepted.output` emits the SIMPLE program from
the resulting certificate.

`select classes cost pool` takes a finite list and a caller-supplied
natural-valued cost function on the entries. It filters the pool through
`Candidate.check`, then uses the existing left-biased `List.minOn?`.
The first admitted minimum in list order wins a tie. Empty and
all-rejected pools return `none`. `select_admitted` proves membership
and successful rechecking of the returned entry. `select_min` compares
it with every entry in the same pool for which the checker succeeds.
`select_none_iff` characterizes failure as rejection of the whole pool.

The example metric, `Candidate.primitiveRows`, counts primitive
applications once per materialized address, including dead rows if
supplied. Shared references to the same row do not add cost. It
does not weight instructions, count dynamic iterations, or model effects.

## Semantic contract

`Accepted.observe_eq` composes the checked row witnesses with the
existing cyclic Figure 11 extraction proof. For a model and input
tuple, it needs well-founded source demand and semantic validity of the
supplied source classes. The checker tests finite class labels. It does
not establish that arbitrary caller-provided labels identify equal
streams. The theorem preserves the entire typed observation tuple
(in this fragment a singleton), including bottom, at every index.

`Accepted.observe_of_returns` composes extraction and reversion to
show that a successful emitted SIMPLE return gives the corresponding
defined source observation under the exit opcode's Boolean negation law.
`Accepted.returns_iff_observe` also gives the reverse implication
under totality of the full guard and simultaneous update slices on
defined stores. These theorems characterize successful returns.
They do not distinguish divergence from primitive failure in an
undefined observation.

## Regression

The landed cyclic decrement fixture is extended to subtract two ones.
The existing self-feedback rule proves that its extra θ stream is
equal to the constant. One admissible layout uses duplicate constant
rows and costs 5. The other compacts the θ to share one constant and
costs 4. The checked update schedules use three and two bindings
respectively, and both return 1 from 7 in three iterations. The
cost-3 shortcut substitutes the live counter for both constant
operands. In isolation it can emit and return 0. Its output-class and
demand checks pass, and the ordered operand-class check rejects it. Keeping the original extra θ passes extraction
legality and fails schedule admission. The regression also exercises
tie order and both empty-result cases.

The pool is supplied explicitly. This interface makes no claim of
enumeration completeness, a global optimum over other extractions,
or support for general nested reversion, effects, or the paper's
weighted pseudo-Boolean objective.

[Definitions](../../Silmaril/SSA/Peggy/SimpleValidation/Cyclic/Cost/Defs.lean) ·
[Theorems](../../Silmaril/SSA/Peggy/SimpleValidation/Cyclic/Cost/Thms.lean) ·
[Regression](../../tests/ssa/PeggySimpleValidation.lean)

```sh
lake build --wfail +Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Thms PeggySimpleValidationTests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PeggySimpleValidation.lean
lake env leanchecker --fresh Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Thms
lake env leanchecker tests.ssa.PeggySimpleValidation
```
