# Checked single-loop PEG regions to structured RVSDG θ

`Bridge.Theta.Region.compile` takes the existing PEG reversion region
certificate. The certificate checks the parentless loop boundary, the
guard and update schedules, and a demand rank for the original numbered
PEG. The compiler accepts the same ordered list of typed carried slots,
including the certificate's invariant-slot mode. The designated return slot
requires a nonempty carried tuple. Row numbers can be interleaved. The
adapter accepts the certificate returned by the supplied-boundary checker
or by automatic inference.
[Region checker](../../Silmaril/SSA/PEG/Simple/Revert/While/Region/Defs.lean) ·
[Compiler](../../Silmaril/SSA/PEG/Bridge/Theta/Region/Defs.lean)

Each scheduled primitive emits one numbered RVSDG vertex. Typed scope
entries resolve to carried arguments or earlier results, so shared rows
remain shared. The guard projection supplies the old tuple to a γ. A true
guard selects arm one, which computes the full next tuple, and sets the θ
feedback tag. A false guard selects arm zero, which returns the old tuple.
The update starts with all old slots in scope. Intermediate bindings add
origins, and the final ordered projection commits the new slots together.
The stopping activation executes the guard and returns the old tuple.

The interpretation is the existing PEG bridge's `TotalModel`. In the
Figure 11 interpreter, primitives still demand all of their arguments.
For the PEG observation theorem the boundary's exit opcode must implement
Boolean negation. This makes a true PEG pass sample correspond to the false
RVSDG continuation test.
[Numbered θ semantics](../../Silmaril/SSA/RVSDG/Theta/Thms.lean) ·
[Preservation statements](../../Silmaril/SSA/PEG/Bridge/Theta/Region/Thms.lean)

- `body_run` identifies the numbered body's tag and payload with the checked guard and update slices.
- `returns_iff_trace` matches a finite RVSDG return to the existing reversion trace. Every successful while body step corresponds to a θ restart, and the final false guard gives the mandatory stopping activation.
- `return_at_firstExit` recovers the PEG pass count, selected sample and defined eval prefix from the guarded observation. At this exit, the θ returns the full carried tuple from the trace.
- `returns_iff_observe` equates projecting the designated slot of a finite θ return with the original PEG's defined scalar observation, at any ambient index.

The certificate exposes one PEG eval root. The RVSDG result retains the
full tuple, with that root observed through its designated slot. The
theorems cover successful finite returns for pure, total primitives.
Partial evaluation, effects, divergence and nested loops have separate
correspondence obligations.

## Checks

```sh
make check CHECK_TARGETS='+Silmaril.SSA.PEG.Bridge.Theta.Region.Thms +tests.ssa.PEGStructuredTheta'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PEGStructuredTheta.lean
for module in \
  Silmaril.SSA.PEG.Bridge.Theta.Region.Defs \
  Silmaril.Proofs.SSA.PEG.Bridge.Theta.Region.Compilation \
  Silmaril.Proofs.SSA.PEG.Bridge.Theta.Region.Operational \
  Silmaril.SSA.PEG.Bridge.Theta.Region.Thms tests.ssa.PEGStructuredTheta; do
  SILMARIL_REPLAY_MODULE="$module" LEAN_NUM_THREADS=1 \
    lake env lean -DwarningAsError=true tools/compiler-explorer/Replay.lean
done
```

The fixture uses a distinct, interleaved three-slot PEG with the eval root
at row four. A counter and two accumulators advance from `(2, 10, 1)`
through `(1, 1, 11)` to `(0, 11, 12)`. The first accumulator copies the
old second accumulator, and the second sums both old accumulators. Reading
the new first accumulator would give `2` at the first step instead of `11`.
The checked RVSDG return projects the same value, `12`, as guarded PEG
evaluation. A second run starts at exit and returns immediately.
[Regression](../../tests/ssa/PEGStructuredTheta.lean)
