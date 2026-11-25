# Flattening a pure MLIR `scf.if` with nested while arms

Import `Silmaril.SSA.MLIR.SCF.IfWhile.Thms` for the typed source, lowering, and
correctness statements. The target and its evaluator are the existing
`Silmaril.MLIR.CF.Cfg` from [the single-while development](mlir-scf-while.md).

## Typed source and allocated blocks

`IfWhile.Program` takes a parent input context, an `i1` operand, two arms that
yield the same result tuple, and a parent continuation. The arms take no
arguments and can see the parent context. An arm is either straight-line code
ending in `scf.yield` or an arm with a straight-line prefix, one
`scf.while` with before and after regions, and a straight-line tail ending in
`scf.yield`. The representation makes the while's initial operands and
arm-local captures explicit at the while site. The prefix can produce those
captures. The loop regions and tail see their arguments followed by the
captured values and the parent input. The shared continuation sees the if
results followed by the parent input.

Each arm allocates a separate label family. A straight-line arm has an entry.
A looping arm also has before, after, and exit labels with these profiles.
The two families can have identical profiles and still name different blocks.

| Block | Local arguments | Successors |
| --- | --- | --- |
| CFG entry | Parent input | `cf.cond_br` selects the true or false arm entry. |
| Straight-line arm entry | Empty | `cf.br` passes the arm yield to the shared join. |
| Looping arm entry | Empty | `cf.br` passes initial state and captures to before. |
| Before | State, captures | `cf.cond_br` passes the condition payload and captures to after or exit. |
| After | Payload, captures | `cf.br` passes updated state and the same captures back to before. |
| Exit | Payload, captures | The arm tail runs and `cf.br` passes its yield to the join. |
| Shared join | If results | The parent continuation runs and returns the fragment result. |

`Arm.lowerBlock` takes the arm's label injection and the join label.
`Program.lower` installs the two injections and the join in one successor
table. Local arm values that survive across blocks travel as typed edge
operands. The template selects the capture slice behind the loop arguments
and weakens those operand references under each retained SSA binding. The
proof shows that they evaluate to the original captured tuple. Dominating
parent inputs use the existing CF entry environment.

## Observation and proof

The structured evaluator chooses one arm, evaluates its prefix and loop when
present, and sequences the arm yield into the parent continuation. An arm
that yields passes along the rest of the budget. The if test, selected arm
entry, and shared continuation each cost one tick. Each before visit and its
selected after region or arm tail cost two ticks together. With fewer than
two ticks left at before, the source cannot yield from that arm. The target
consumes one tick per CF block.

- `Program.lower_run` gives equality of the two optional result tuples at
  every budget, including budgets that stop before the shared continuation.
- `Program.lower_returns_iff` gives preservation and reflection of each
  finite return.
- `Program.lower_diverges_iff` gives preservation and reflection of
  divergence, defined as no return at any finite budget. Primitives are
  total and deterministic, so there is no fault outcome.

The Lean examples check a true arm with two backedges and an arm-local capture,
a straight-line false arm, and a second program with a divergent false arm.
When both arms contain loops, the two local layouts have the same profiles.
Selecting the true arm still runs two iterations and returns.

This slice covers one result-bearing if with at most one while per arm and
total scalar primitives. Arbitrary nesting needs recursive structured block
syntax, recursive allocation of fresh typed labels, and a composition proof
that tracks lexical captures, live results, and continuation edges at each
nesting level. A separate `scf.for` development would need a positive step,
an explicit comparison, an overflow contract, and checked zero-trip and
multiple-trip cases.

- [LLVM MLIR SCF dialect and `scf.if`](https://mlir.llvm.org/docs/Dialects/SCFDialect/#scfif-scfifop)
- [LLVM MLIR SCF dialect and `scf.while`](https://mlir.llvm.org/docs/Dialects/SCFDialect/#scfwhile-scfwhileop)
- [LLVM MLIR Control Flow dialect](https://mlir.llvm.org/docs/Dialects/ControlFlowDialect/)
