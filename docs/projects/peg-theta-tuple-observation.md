# Ordered PEG observations for a structured θ

`Bridge.Theta.Region.Ordered.check` accepts an ordinary PEG with one loop
identifier and the same typed list at the input and result boundaries.
A designated slot supplies a scalar view of the same table for the existing
single-loop certificate. This gives the checked guard and update schedules,
initial and feedback rows, parentless loop, and demand rank. Each result
reference must name an `eval 0` with the θ reference for that exact carried
position and the pass reference from that certificate. The check compares
typed references, including across slots of the same sort.
[Bundle checker](../../Silmaril/SSA/PEG/Bridge/Theta/Region/Tuple/Defs.lean) ·
[Single-loop compiler](peg-checked-vector-theta.md)

The scalar view changes only the graph's root tuple.
`Bundle.denote_scalarView` aligns its guarded valuation with that of the
full graph. The existing numbered θ compiler runs one shared loop, and
`Certificate.traceObservation` uses one successful reversion trace to
derive the first pass count and every carried slot's final value and
defined prefix. At each ordered result port, the checked eval equation
uses that count and the Figure 11 prefix rule. Typed port extensionality
assembles the individual results into the ordered observation.

`Bundle.returns_iff_observe` states that an actual numbered RVSDG θ finite
return of a tuple is equivalent to observing `some` of that tuple's value
at every PEG result position. In the reverse direction the anchor root
supplies a finite return through the scalar theorem. The forward proof
then computes its whole PEG observation. Equality at each typed position
identifies the actual returned tuple with the requested tuple.
`Bundle.firstExit_of_returns` exposes the common count, the trace, and
all defined prefixes. The model must be pure and total, and the PEG exit
opcode must implement Boolean negation so a true pass sample corresponds
to the false RVSDG continuation test.
[Preservation statements](../../Silmaril/SSA/PEG/Bridge/Theta/Region/Tuple/Thms.lean)

`defined_satisfaction_iff` equates agreement of two admitted graphs on
all fully defined ordered observations with agreement of their numbered
RVSDG finite-return relations in the induced model. Its scope is
successful observations for the checked single-loop fragment.

## Checks

```sh
make check CHECK_TARGETS="$(make -s scope BASE=origin/main)"
lake build --wfail +Silmaril.SSA.PEG.Bridge.Theta.Region.Tuple.Thms +tests.ssa.PEGStructuredTheta
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PEGStructuredTheta.lean
for module in \
  Silmaril.SSA.PEG.Simple.Revert.While.Region.Defs \
  Silmaril.Proofs.SSA.PEG.Simple.Revert.While.Region.Correctness \
  Silmaril.SSA.PEG.Simple.Revert.While.Region.Thms \
  Silmaril.SSA.PEG.Bridge.Theta.Region.Tuple.Defs \
  Silmaril.Proofs.SSA.PEG.Bridge.Theta.Region.Tuple.Observation \
  Silmaril.SSA.PEG.Bridge.Theta.Region.Tuple.Thms tests.ssa.PEGStructuredTheta; do
  SILMARIL_REPLAY_MODULE="$module" LEAN_NUM_THREADS=1 \
    lake env lean -DwarningAsError=true tools/compiler-explorer/Replay.lean
done
```

The interleaved graph's three results have sorts count, data and data.
The compiled loop returns `(0, 11, 12)` from `(2, 10, 1)`, and the
regression checks both directions of the ordered observation theorem.
Replacing the middle root with an eval that names a second pass row is
rejected even though the rows test the same predicate. Repeating the last
same-sort eval in the middle position is also rejected.
[Regression](../../tests/ssa/PEGStructuredTheta.lean)
