# Discover an exit-only suffix of the saved loop header

`ExitSink.Suffix.discover?` scans the actual header cuts from first to last.
It returns the emitted CFG at the first cut where `sinkAt?` can move the
whole remaining suffix into the existing exit block. `discover?_spec`
proves that the emitted CFG is the nominated checker's exact result and
that no earlier cut passed. `discover?_none` rules out every split accepted
by that checker. The single-let sink remains a separate API.
[Definitions][defs] · [Theorems][thms] · [Single-let sink][single]

The typed checker requires the guard and every true-edge feedback operand
to come from the retained prefix. The false edge must carry a suffix result
to an immediate return. A retained binding precedes the entire suffix in
the typed scope, so it cannot read a suffix result. The emitter copies the
suffix to the exit in original dependency order, with the retained scope
passed on the exact false edge. This is a conservative packet carrying the
full scope, including values the moved suffix may never read.

`operation_order` gives the exact original header prefix and suffix in
their new blocks. `operand_occurrence` resolves each forwarded value on
the header's actual false edge. In the emitted exit, the site collector
reads the actual operand references and use sites of every moved binding.
`sinkAt?_legal` certifies those sites with the existing exact dominance and
local cut checker, including dependencies on earlier moved bindings.
[Theorems][thms]

Click's Schedule Late (§2.3) reads a Φ operand at the corresponding
predecessor. The original result is therefore read at the header terminator.
Sinking this suffix changes the argument packet and relocates its
internal reads as well as the returned computation. The proof covers pure
total typed lets in a contiguous nonempty suffix, one true-edge self-latch,
and one immediately returning false exit. The scope permits unused pure
lets within the suffix. Longest means longest among these checked splits.
Multiple exits, general dependency scheduling, and packet minimization
are outside this profile.
[Click PLDI ’95][paper] · [Coverage ledger][coverage] · [Schedule Late bound][late]

`header_packets` preserves the true-edge bank exactly and reconstructs
the old false-edge result by evaluating the suffix on its new packet.
Together with the reused entry packet law, `run_eq` proves identical
returns and exhaustion at every common block fuel, and `denotePart`
proves equal partial denotation. The exit reuses the original block, so
the finite execution comparison needs no fuel offset.
[Theorems][thms]

The lowered fixture moves three dependent lets to the exit at split 3.
Its exit operand sites are `[[0, 0], [1, 0], [2, 1]]`, so the final let
reads both earlier moved results. A later split passes and the preceding
split fails. The feedback packet stays `[3, 2, 7]`. Both programs exhaust
at fuel 4 and return 9 at fuel 5. Moving the feedback use to the second
producer forces split 5, where only the final consumer can move. Using
the returned value itself on feedback leaves no accepted suffix.
[Example][example] · [Regression][regression]

```sh
lake build --wfail +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Suffix.Regression
cat >/tmp/gcm-exit-suffix-example.lean <<'LEAN'
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Suffix.Example.Defs
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Suffix.Example
#eval observe
#eval retainsFeedbackProducer
#eval refusesFeedbackResult
LEAN
lake env lean -DwarningAsError=true /tmp/gcm-exit-suffix-example.lean
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Suffix.Thms
```

[paper]: https://doi.org/10.1145/207110.207154
[coverage]: ../coverage.md#global-code-motionglobal-value-numbering
[late]: sea-of-nodes-gcm-late-placement.md
[single]: sea-of-nodes-gcm-loop-exit-sink.md
[defs]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/ExitSink/Suffix/Defs.lean
[thms]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/ExitSink/Suffix/Thms.lean
[example]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/ExitSink/Suffix/Example/Defs.lean
[regression]: ../../../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopHoist/ExitSink/Suffix/Regression.lean
