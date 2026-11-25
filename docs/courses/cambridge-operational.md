# Operational semantics for L1, L2 and L3

These developments follow chapters 1–5 of Peter Sewell's *Semantics of
Programming Languages* notes for Cambridge Part IB, 2025–26, dated
12 February 2026. The course is a self-contained library leaf. Its proofs stay
near the definitions and exercise statements.

```sh
lake build --wfail Silmaril.Courses.Cambridge.L1.Course \
  Silmaril.Courses.Cambridge.L2.Course Silmaril.Courses.Cambridge.L3.Course
```

The smaller `L1`, `L2` and `L3` imports expose the language interfaces.
Their `.Course` imports add metatheory and checked derivations.
All module names below start with `Silmaril.Courses.Cambridge.`.

| Language | Features | Main proved results |
| --- | --- | --- |
| `L1` | Integers, Booleans, conditionals, finite integer stores, assignment, sequencing and loops | Determinacy; decidable sound and complete type inference; type uniqueness; progress, preservation and safety over every finite reachable trace |
| `L2` | L1 plus functions, application, strict `let` and recursive functions | Capture-avoiding substitution; decidable sound and complete type inference; type uniqueness; preservation of typing, closedness and allocated locations; progress for closed well-typed expressions |
| `L3` | L2 control and functions, plus products, sums, ordered records and allocatable references | Typed substitution, progress, preservation with store growth, finite-trace safety and a counterexample to determinacy |

The [concrete syntax guide](cambridge-concrete.md) describes the L1 and L2
UTF-8 profile, byte parsers, canonical printers and their checked round-trips.

## L1 and L2 stores and safety assumptions

Stores are finite partial maps from location names to integers. Locations are
opaque strings, and assignment updates an already allocated location; the
languages do not allocate fresh references. Core arithmetic uses unbounded
integers. The L1 machine-integer exercise separately supplies modular
`BitVec w` arithmetic and signed comparison, with explicit overflow examples.

`StoreCovers Γ s` means that every location mentioned by the typing environment
is allocated in `s`. L1 progress and safety require this premise. L2 also
requires `Expr.Closed`: no free variable names and no dangling de Bruijn
indices. Preservation proves that steps retain the required invariants.
Safety means that a reachable configuration is a value or has a next step;
it does not assert termination of programs containing loops or recursion.

| Result | Public name |
| --- | --- |
| L1 one-step determinacy | `L1.Step.deterministic` |
| Inference exactly characterizes typing | `L1.infer_iff_hasType`, `L2.infer_iff_hasType` |
| L1 progress and preservation | `L1.progress`, `L1.preservation` |
| L1 safety after finitely many steps | `L1.safety`, `L1.safety_reachable` |
| L2 typed substitution | `L2.HasType.subst`, `L2.HasType.beta` |
| L2 progress | `L2.progress` |
| L2 typing, closedness and store coverage | `L2.type_preservation` |

L2 keeps named source syntax in `RawExpr`. Resolution maps bound occurrences
to de Bruijn indices while retaining free names. `AlphaEq` is equality of the
resolved syntax; examples distinguish harmless binder renaming from capture.

## L1 and L2 evaluation strategies and executable examples

L2 has call-by-value (`Step`), call-by-name (`NameStep`) and a broader full-beta
relation (`BetaStep`). Call-by-value and call-by-name steps embed in
`BetaStep`. Their agreement is not assumed: a proved store-effect example
returns `true` under call-by-value and `false` under call-by-name because an
unused effectful argument is evaluated only in the first strategy.

The executable interfaces have different proved contracts:

| Interface | What it computes | Current guarantee |
| --- | --- | --- |
| `L1.Exercises.searchConfig` | One step with a printable derivation tree | Each returned tree proves its resulting `L1.Step` via `StepTree.toStep` |
| `L2.runFuel` | Substitution-based CBV/CBN reduction, bounded by a number of transitions | CBV and CBN implement `L2.Step` and `L2.NameStep` respectively on all configurations |
| `L2.evalClosureFuel` | CBV evaluation with lexical and recursive closures, bounded by evaluation depth | Proven agreement with the substitution interpreter on lexical-scope, recursion and store-effect examples; no general simulation theorem yet |

`L2.Config.reduce_value_iff_step` identifies each successful CBV reducer call
with a `Step`. `L2.Config.reduce_value_eq_none_iff_terminal` identifies failure
to step with relational terminality. `L2.runFuel_value_returns_terminal`
certifies a finite trace to any returned configuration, including a stuck
configuration on untyped input. Under the safety assumptions above,
`L2.runFuel_value_returns_typed_value` gives a value of the original type and
preserves closedness and store coverage.

For call-by-name, `L2.Config.reduce_name_iff_step` and
`L2.Config.reduce_name_eq_none_iff_terminal` give the corresponding results
for `L2.NameStep`. `L2.runFuel_name_returns_terminal` certifies a finite
`L2.NameSteps` trace to a `L2.NameTerminal` configuration.
`L2.runFuel_name_returns_typed_value` gives the typed-value guarantee for CBN
under the same closedness and store coverage assumptions.

`runFuel` returns `some c` when its reducer has no next step. `none` records insufficient
transition fuel. A particular fuel-exhaustion equation is not an infinite-run
proof. The closure interpreter's `none` also covers invalid operations or
missing variables; `evalClosureGround` additionally rejects function results.
Its depth fuel is not directly comparable to `runFuel`'s transition budget.

For example:

```lean
import Silmaril.Courses.Cambridge.L2.Course

open Silmaril.Courses.Cambridge

example : L2.runFuel .name 10 L2.Exercises.EvaluationStrategies.start =
    some L2.Exercises.EvaluationStrategies.nameResult :=
  L2.Exercises.CallByNameInterpreter.name_matches_exercise23

example : L2.evalClosureGround 40 L2.Exercises.Closures.lexicalStart =
    some L2.Exercises.Closures.lexicalResult :=
  L2.Exercises.Closures.lexical_closure
```

The L1 exercises also prove counterexamples for nondeterministic evaluation
order and for retaining the old typing rule after changing assignment's
result. Revised assignment typing restores preservation. A factorial-shaped
program is defined and typed; its general factorial input/output correctness
is not proved in this slice. L2's first-order exercise defines saturated
multiargument calls and proves that a partial call is untypable.
The L1 and L2 formalizations give Lean models of the abstract languages. Their
executable checks cover the Lean interpreters above.

## L3 data and mutable references

The [L3 concrete syntax guide](cambridge-l3-concrete.md) describes the UTF-8
grammar, precedence rules, canonical printers and checked byte round-trips.

`L3.NamedSyntax` implements the named grammar from §5.5, p. 78. Its
`RawExpr.resolve` maps bound variables to de Bruijn indices, including the
separate binders of sum branches. Both the expression and type models retain
record label order and require distinct labels. A record's field positions
index its expressions or types.

`L3.Step` implements the direct small-step rules of §5.5, pp. 78–80.
Pairs, records and applications evaluate left to right. Record projection
requires a record of values. The right side of assignment can step once
the left side is a location, as in the direct rule (assign2).
`L3.Store` is a finite partial map from location names to values, including
functions and locations. Natural numbers represent the location names.
Allocation may choose any name outside the store's domain. L3 has no
expression for comparing locations.

`L3.HasType` implements the rules on pp. 80–82. The location environment
records the contents type of each reference. `L3.StoreTyped` requires exact
agreement of the location and store domains and checks each stored value
against its location's contents type in the shared location environment.
The safety results use an empty variable environment for the expression
and stored values, so location literals can appear at runtime alongside
closed function values.

| Result | Public name |
| --- | --- |
| Capture-avoiding typed substitution | `L3.HasType.subst`, `L3.HasType.beta` |
| Progress (Theorem 23) | `L3.progress` |
| Preservation under a location environment that agrees on all old locations (Theorem 24, Exercise 28) | `L3.preservation` |
| Safety over every reachable finite trace (Theorem 25) | `L3.safety` |

`L3.Examples` checks a function stored and replaced through a reference, a
sum match with a product projection, the ordered writes of a record whose
first field is projected, and two distinct successors of one allocation.
It also checks branch scope and stuck configurations with an unallocated
dereference or an integer as the assignment target.

### Evaluation contexts (§5.4)

`L3.EvaluationContexts` gives the one-hole context grammar, plugging,
and the computation rules on p. 77. The single evaluation rule lifts
a step through one frame. Repeating it handles nested contexts and
carries the store through each frame.

Section 5.4 permits any value to the left of the hole in `v := □`.
The direct rule (assign2) in §5.5 requires a location in that position.
The integer-left example `L3.assignment_context_counterexample` takes a
context step on its right-hand addition and is stuck under the direct rules.
A value of reference type is a location, so the restriction disappears for
typed sources.

| Result | Public name |
| --- | --- |
| Every direct step is a step of the printed context relation | `L3.Step.toContextStep` |
| Theorem 26 for the printed contexts on typed source expressions | `L3.contextStep_iff_step_of_hasType` |
| Theorem 26 on arbitrary configurations with the (assign2) location premise | `L3.locationContextStep_iff_step` |

### Executable reduction (§5.5)

`L3.Config.reduce` selects one direct step when a successor exists. For an
allocation, `L3.Store.freshAddress` chooses one above the maximum allocated
address, using 1 for an empty store. The record reducer inspects fields in
source order and stops at the first non-value, even if that field is stuck.
Executable regressions check intermediate record writes, projection by label,
a stuck first field, and allocation in empty and nonempty stores.

| Result | Public name |
| --- | --- |
| The selected address is outside the current domain | `L3.Store.freshAddress_not_mem` |
| Every selected edge satisfies the direct rules | `L3.Config.reduce_sound` |
| The reducer stops exactly on configurations without a direct successor | `L3.Config.reduce_eq_none_iff_terminal` |
| Some executable successor exists exactly when some relational successor exists | `L3.Config.reduce_exists_iff_step_exists` |

Successor existence allows a single executable choice even when the relation
admits several. For example, allocating in the empty store may choose 0 in
the relation, while the reducer chooses 1. The operational institution below
continues to observe the original relation.

Executable type inference and a denotation for the full language remain
follow-up work. The data and reference fragment has checked finite may
adequacy. Named and resolved terms and expression types have structural
codecs. [L3 denotation](cambridge-l3-denotation.md) ·
[AST codec guide](cambridge-ast-codecs.md)

The [course notes](https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf)
are pinned as `sewell2026semantics` in [the bibliography](../../references.bib).

## Operational institution

`Silmaril.Courses.Cambridge.OperationalInstitution` exposes the L1 and
call-by-value L2 step models and the direct L3 step model over their original
configurations. Finite returns observe reachable values with their final
stores. L3 retains each fresh location choice.
[L1 and L2 observation contract](../projects/operational-institutions.md#cambridge-l1-and-l2) ·
[L3 observation contract](../projects/operational-institutions.md#cambridge-l3) ·
[Step specifications](cambridge-step-specification.md)
