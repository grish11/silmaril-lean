# Checked ordered returns from finite Peggy selection

The [finite-pool selector](peggy-finite-cost-selection.md) now accepts
materialized candidates with a nonempty ordered result tuple. The
ordered entry point is `Cost.Bundle.select`. It uses the same
`filterMap` and left-biased `List.minOn?` as the scalar entry point.
The caller supplies the pool and Nat cost. Ties keep the first admitted
minimum and an empty or all-rejected pool yields `none`.

## Two independent checks

1. The E-PEG checker checks the non-feedback rank, native demand rank,
   every ordered operand class, and each output's actual source class.
   `Accepted.root_class` exposes the check by output position, including
   repeated positions and slots of the same sort.
2. The SIMPLE reverter checks the first root with the existing
   automatic primitive-loop checker on a scalar view of the same table.
   That check supplies one parentless loop boundary, the carried θ rows
   and the primitive guard and full simultaneous update schedules.
   For each output it recovers the sampled carried port and checks the
   entire eval row. Every output must use the same exact pass row.
   Class equivalence between two different pass addresses is enough for
   extraction replay. The emitter's shared-pass condition requires
   address identity.

The emitter runs that loop once, then uses a typed SIMPLE projection
to return the chosen carried ports in order. The projection can
reorder or repeat slots. Scalar and tuple fuel runners use the same
guarded loop runner up to the completed carried store.

## Observation contract

`Accepted.observe_eq` preserves the complete ordered Figure 11 tuple,
with an `Option` at each port, at every index. Its premises are
well-founded source demand and validity of the supplied source
classes for the interpretation and input. These are semantic
contracts. The executable check compares finite class labels.
`Accepted.pass_eq` also preserves the reading of the checked pass at
its actual source representative.

Under the Boolean negation law, `Accepted.firstExit_of_exec` uses a
single successful emitted SIMPLE execution to identify the common
first pass and the fully defined original observation. Its pass
claim names both the candidate pass and its selected source
representative. `Accepted.exec_iff_observe` adds the converse under
totality of the guard and the entire simultaneous update on defined
stores. A defined head eval supplies the first exit for that direction.
The proof then recovers and compares every other result through the
one completed store. The emitted observation is a finite successful
return, with failure and divergence outside that observation.

## Regression and scope

On input `[5, 17]` the countdown takes three trips and returns
`[2, 17, 2]`. The same-typed root swap independently passes reversion
and fails the source root-class check. A candidate splitting its evals
over two class-equivalent pass rows passes extraction replay and fails
emission. Either pass address works when all roots use it together,
and the order of these equal-cost entries determines the winner.

The emitter handles direct eval roots of carried slots in the
existing parentless primitive loop fragment. Enumeration completeness,
global cost optimality, and effects are outside the result.

[Selector definitions](../../Silmaril/SSA/Peggy/SimpleValidation/Cyclic/Cost/Bundle/Defs.lean) ·
[Selector theorems](../../Silmaril/SSA/Peggy/SimpleValidation/Cyclic/Cost/Bundle/Thms.lean) ·
[Tuple reverter](../../Silmaril/SSA/PEG/Simple/Revert/While/Region/Bundle/Thms.lean) ·
[Regression](../../tests/ssa/PeggySimpleValidation.lean)

```sh
lake build --wfail +Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Thms PeggySimpleValidationTests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PeggySimpleValidation.lean
lake env leanchecker --fresh Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Thms
lake env leanchecker tests.ssa.PeggySimpleValidation
```
