# Append-only E-PEG saturation

The [transition interface](../../Silmaril/SSA/Peggy/EPEG/Saturation/Extension/Defs.lean)
extends the [finite saturation worklist](peggy-saturation.md) with one typed
PEG row per step. It follows the IR growth direction of §4 and uses the
guarded Figure 11 denotation for semantic preservation. The paper locators
below refer to arXiv:1012.1802v3, printed pp. 20–21 (§4), 23–24 (Figure 11),
and 25 (§5.3). [Paper](https://arxiv.org/pdf/1012.1802v3)

## Transition and replay

A state contains a typed PEG table and a partition of its vertices. A step
contains the new row with operands drawn from the existing table, a list of
ground merge obligations with endpoints in the enlarged table, and a merge
budget. The step retains the original row numbers, sorts, labels, ordered
edges, ordered roots and loop frame. It inserts the new row as a singleton
class, then runs the existing worklist. That worklist checks guard classes
or common-label operand classes with the enlarged partition. It may return
before closing the supplied obligations. A zero merge budget still appends
the row.

`Plan` is a typed sequence of steps. Later steps may use rows generated
earlier. `Plan.run` uses an additional append budget and returns the actual
state at the resulting prefix. Each step adds one row, so the budget also
bounds the number of added rows. `Plan.liftRef` transports any typed source
reference to its original numeric address in the output. Replay consumes
the supplied plan. Rule matching and selection of the next plan step are
client operations.

The [theorem header](../../Silmaril/SSA/Peggy/EPEG/Saturation/Extension/Thms.lean)
records the preservation guarantees.

- `Row.node_old` identifies every embedded old row with its lifted original,
  and `Row.demandWellFounded` transfers demand admission from the source.
  Old reads stay within the old table. A fresh row can only demand old
  vertices, even if its sampling edges read arbitrarily large indices.
  Existing guarded cycles are allowed. The transition adds no new cycle
  and does not change loop coordinates.
- `Row.read_old`, `Plan.read_old` and `Plan.observe_eq` prove exact old
  stream and ordered output preservation at every index, including
  bottom. They use uniqueness of the source solution restricted from
  the enlarged table.
- `Step.sound` and `Plan.sound` also prove that all pairs joined in the
  resulting partition have equal streams. These theorems require initial
  class validity and semantic contracts for the supplied obligations in
  the given interpretation and ordered input. Congruence discharges its
  law through the existing guarded graph equations. Guarded reasons still
  need proofs, and only replayed steps need contracts. Old streams and
  ordered observations are preserved by the graph construction regardless
  of which merges run. The guarantees use well-founded Figure 11 demands
  and carry no separate claim about Definition 5.1 scope or reversion.

## Generating the zero sample

`ZeroSample.matchAt` checks an actual outer eval row, a θ operand with the
same loop identity, and the designated nullary count primitive in the
second operand. A successful match generates a fresh
`eval ℓ (initial, zero)` row and one merge reason, implementing §5.3's
`eval ℓ (θℓ (initial, feedback), zero) = eval ℓ (initial, zero)`.
`ZeroSample.equates` proves the merge runs. Its semantic justification
`ZeroSample.holds` requires that the model interpret the designated
primitive as **defined zero**. The initial value and feedback may be
partial. The rule uses eval's empty prefix at count zero and θ's initial
read at that coordinate. The initializer can still depend on the loop, so
the rule generates an eval row rather than using the initializer directly.

The regression starts with a five-row PEG containing a live θ/successor
cycle and no eval of the initializer. It finds the match, adds that eval,
and has a second step use the new row. It checks both replay budgets
and merge exhaustion, the preserved ordered roots, rejection when the
count uses a different literal, and exact observations for a defined
or undefined initializer.

## Scope of §4

The paper orders IRs by inclusion of the node and equality information.
(4.1) says an analysis step is inflationary. `Row.node_old` and
`Step.extends` prove this for the append-only transition, using the
stable address injection and containment of same-class pairs.
`Plan.extends` carries class containment through replay.

(4.2) defines monotonicity for a nondeterministic analysis: if it can step
from a smaller IR, it must be able to step from a larger IR to a state
extending the smaller successor. (4.3) follows from (4.1) and (4.2) for
the delayed application of the first analysis after another step.
(4.4) concerns uniqueness of reachable normal forms for a set of such
monotonic analyses, when a normal form exists. The
[embedding comparison](peggy-node-monotonicity.md) proves (4.2) for
the zero-sample analysis under fresh append and gives the conditional
(4.3) theorem. General rule transport, other node-reuse policies and
termination remain separate obligations. The
[normal-form theorem](peggy-normal-forms.md) proves conditional (4.4)
under the stated family hypotheses. The finite worklist's
least-closure and order-independence theorems still apply per fixed
table and obligation list. This replay may add duplicate rows and has
no global deduplication, scheduling, closure, termination or extraction
theorem for unbounded generation.

```sh
lake build --wfail +Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Thms PEGRulesTests PeggyEggTests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PeggyEgg.lean
lake env leanchecker --fresh Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Thms
lake env leanchecker tests.ssa.PeggyEgg
```
