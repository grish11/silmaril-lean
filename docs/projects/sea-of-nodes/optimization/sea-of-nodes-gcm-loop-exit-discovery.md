# Discover noncontiguous exit placement from guard and feedback reads

`ExitSink.Partition.Discovery.discover` takes the actual saved-loop CFG.
It derives a mask from the header and submits it to the existing checked
partition emitter. The result records the exact scan and emitter
equalities in `Plan.scanned` and `Plan.checked`. The emitted artifact has
the indicated retained and moved subsequences in original order.
[Definitions][defs] · [Theorems][thms] · [Checked partition][partition]

The scan takes the guard and every operand of the actual true-edge
feedback packet as roots, preserving the argument order and any repeated
reads. Then it walks the typed lets backwards. Index zero names the
binding just crossed. If it is required, the binding stays and the
typed operand indices enter the demand for earlier values. Older reads
shift back one position either way. This follows dependencies through
operations as well as reading entry arguments and saved packet slots.
The mask is in input-header order.

`RetainedReads` defines the control-closed masks. They retain the
producers of guard and feedback reads and the producers of all operands
of retained lets. `scan_closed` proves the computed mask is closed.
`scan_least` proves it proposes a superset of the moves of every closed
mask and requires a subset of their entry reads. `scan_length` ties the
mask to the actual header inventory. If there is no proposed move,
`no_move_closed` rules out moves within this closure criterion.

Closure maximality concerns those guard, feedback, and retained-code reads.
The partition emitter additionally checks the actual entry, exit and
physical cut sites. In particular, its false-edge result must come from
the moved set. Discovery checks the one computed mask. The proof scope
excludes completeness for emitter acceptance or search over fallback
masks. `controlShape` reports a header terminator outside the supported
feedback/exit shape, `noMove` reports an empty proposal, and `partition`
reports rejection by the existing emitter. Each refusal carries no CFG.
[Theorems][thms]

Click's Schedule Late (§2.3) assigns Φ reads to the incoming
predecessor. Here the guard and actual feedback occurrence seed the
required set and the existing partition moves the complement's reads to
the existing exit when it succeeds. The scope is the pure total saved
single-latch loop with true-edge self-feedback and one immediate false
exit. The emitter keeps its full retained-scope packet. The public
observation laws preserve exact feedback, the reconstructed exit result,
returns and exhaustion at common block fuel, and partial denotation.
[Click PLDI ’95][paper] · [Coverage ledger][coverage] · [Theorems][thms]

The lowered interleaved fixture discovers `[false, true, false, true,
false, true]` without nominations. Roots are origins 3 and 4, and
origin 0 stays because feedback depends on it transitively. The pass
moves origins 5, 6 and 7, keeps feedback `[3, 2, 7]`, and returns 9 at fuel
5 after two feedbacks. A second fixture has a producer demanded by the
first feedback argument and has no move. A third fixture has a
nonempty proposal, but its returned value is required on feedback and
the existing emitter refuses. [Runnable example][example] · [Regression][regression]

```sh
lake build --wfail +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Discovery.Regression
cat >/tmp/gcm-exit-discovery-example.lean <<'LEAN'
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Discovery.Example.Defs
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Discovery.Example
#eval observe
#eval noMove
#eval exitRefusal
LEAN
lake env lean -DwarningAsError=true /tmp/gcm-exit-discovery-example.lean
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Discovery.Thms
```

[paper]: https://doi.org/10.1145/207110.207154
[coverage]: ../coverage.md#global-code-motionglobal-value-numbering
[partition]: sea-of-nodes-gcm-loop-exit-partition.md
[defs]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/ExitSink/Partition/Discovery/Defs.lean
[thms]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/ExitSink/Partition/Discovery/Thms.lean
[example]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/ExitSink/Partition/Discovery/Example/Defs.lean
[regression]: ../../../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopHoist/ExitSink/Partition/Discovery/Regression.lean
