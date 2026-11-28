# Checked ordered PEG loops to λSSA

The adapter lowers a checked ordered single-loop PEG bundle to the existing
one-block Isotope λSSA CFG. The block parameter is a product with one field
per carried slot in order. The entry jumps to local label zero with the input
packet. A continue activation passes the next packet back to label zero.
The stop arm branches to label one inside the CFG, which leaves at external
exit zero. [Lowering definitions](../../Silmaril/SSA/PEG/Bridge/Theta/Region/LambdaSSA/Defs.lean)

The lowering uses the same checked guard and update schedules as the
[numbered θ compiler](../../Silmaril/SSA/PEG/Bridge/Theta/Region/Defs.lean).
Each scheduled primitive becomes an ordinary λSSA `let₁` whose right-hand
side is a single typed primitive application. Product elimination reads the
old carried slots. Each new binding shifts the prior slot references, so
the update reads the same old packet throughout and commits the next tuple
only at the backedge. The Boolean test converts the guard to a sum of units
for the native λSSA case. False takes the exit arm with the old packet.
True enters the update bindings. A zero-trip loop visits the header once,
runs its guard, and exits without evaluating the update.
[Schedule definitions and theorems](../../Silmaril/SSA/PEG/Bridge/Theta/Region/LambdaSSA/Schedule/Thms.lean)

`Schedule.emit_eval` matches the target bindings against successful
`runLoopFree` of the checked source schedule. `header_eval` uses the same
schedule observations to match a numbered θ body activation, including
selector polarity, ordered payload and unchanged ambient state.
The shared `Operational.loop_eval_iff` lifts a deterministic header to
finite execution of the actual CFG. `lower_eval_iff` composes that result
with the [ordered Figure 11 correspondence](https://github.com/hiloopai/silmaril-lean/pull/4012).
`firstExit_of_eval` recovers the common PEG pass count and each eval root's
defined prefix. [Loop theorems](../../Silmaril/SSA/PEG/Bridge/Theta/Region/LambdaSSA/Thms.lean)

The checked fragment is a parentless single loop with primitive-only
guard and update slices. The semantics use pure total primitives and the
Figure 11 correspondence requires Boolean negation at the certified PEG
exit opcode. Partial primitives, traps and divergence are outside the
finite-return proof. The bounded runner uses the verified numbered θ model
and counts visits including the stopping visit. Exhausting its fuel gives
no termination classification.

## Checks

```sh
make check CHECK_TARGETS="$(make -s scope BASE=origin/main)"
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PEGStructuredTheta.lean
```

The three-slot fixture checks the emitted header for a guard binding,
a native case, and the two update bindings on the feedback arm. It follows
two actual λSSA backedges to return `(0, 11, 12)` from `(2, 10, 1)`.
With an initially false guard it returns `(0, 10, 1)` on the first visit.
[Regression](../../tests/ssa/PEGStructuredTheta.lean)
