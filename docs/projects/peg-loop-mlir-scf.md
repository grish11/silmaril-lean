# Checked PEG loops to MLIR SCF and CF

A checked ordered PEG bundle lowers to the in-tree scalar `scf.while`.
The compiler reads the guard and update schedules already used by the
numbered RVSDG θ bridge. Each scheduled producer becomes one native
`MLIR.Pure.Code.letOp` binding with typed operands in scope. The source
slot list fixes the order of initial, carried, condition, and result
operands. [Lowering definitions](../../Silmaril/SSA/PEG/Bridge/Theta/Region/MLIR/Defs.lean)

The before region computes the continuation guard and forwards the old
packet. On true, the after region evaluates the update in that old scope
and yields the entire next packet to before. Adding a fresh result name
leaves old arguments available, and only the final yield commits the
new tuple. On false, the parent continuation returns the old packet.
An initially false guard visits before once and skips the after region.
The existing SCF-to-CF lowering produces `cf.cond_br` at before and a
typed `cf.br` backedge at after. Both target evaluators execute their own
bindings and terminators. [SCF and CF semantics](mlir-scf-while.md)

## Value profile

The executable SCF/CF interface uses positive-width bitvectors. A
`Profile` selects a width for each PEG data sort and for count-valued
primitive operands. Booleans use `i1`. The bridge interprets each PEG
primitive by encoding its operands, calling the corresponding MLIR
primitive, and decoding the result. Word data keeps its bits, and count
words decode to unsigned naturals. The theorem takes MLIR input words and
observes the PEG on their exact decoded values. `Profile.encode_decode`
proves the round trip in this direction. Encoding an arbitrary source
natural uses its low bits. Figure 11 pass indices remain unbounded
naturals and are separate from count-valued operands in the loop body.

This profile gives the same total primitive operation on both sides of
the proof. The Figure 11 theorem also requires that the certified negation
opcode implements Boolean negation in that model. The earlier
[regionless bridge](peg-ir-bridge.md) uses institution equations and
has a separate zero-loop boundary.

## Theorems and regression

- `run_eq` matches the decoded result at each SCF fuel budget with the
  numbered θ evaluator at the same budget, counting the stopping visit.
- `returns_iff_numbered` compares complete finite tuples in both directions.
  `returns_iff_observe` composes with the guarded Figure 11 tuple theorem.
  `firstExit_of_run` recovers the shared first pass and the defined prefixes
  for every eval root.
- `cf_returns_iff_observe` reuses the existing SCF-to-CF finite return theorem
  for the emitted CFG. [Bridge theorems](../../Silmaril/SSA/PEG/Bridge/Theta/Region/MLIR/Thms.lean)

The three-slot regression checks the emitted before and after bindings and
the CF backedge. Starting at `(2, 10, 1)`, both evaluators return
`(0, 11, 12)` after two updates that read old slots simultaneously. At
`(0, 10, 1)` they return the input immediately, skipping the update that
would decrement zero. [Regression](../../tests/ssa/PEGStructuredTheta.lean)

The result concerns finite successful execution of the checked pure,
total, parentless single-loop fragment with this scalar profile.
Partial primitives, traps, divergence, and textual MLIR are outside
the theorem.

```sh
make check CHECK_TARGETS="$(make -s scope BASE=origin/main)"
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PEGStructuredTheta.lean
```
