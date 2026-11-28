# Guarded SCCP admission along typed capture chains

`CaptureChain.cons map tail` joins a typed capture map to a chain that
starts at its target signature. `chain.composite` forms the port map for
the independent one-shot compiler. `composite_append` and
`reduct_append` give composition of the actual maps and valuation reducts.
On success, use the existing composite compiler coverage law at the final
valuation.

Call `chain.run seed` with an already admitted guarded program. Each
`Report.passed` contains the original compiler's emitted artifacts and
success equality. The first `Report.stopped` contains the refused call's
equality and the existing diagnostic, including the typed facts and actual
drained FIFO row for a checker refusal. The diagnostic reruns the FIFO
only for a failed call that reached the checker. Later stages are
unevaluated by `run`. `report.firstFailure` gives the zero-based index
and compiler refusal. `report.lastArtifact` gives the actual last
emission if all calls passed and the chain is nonempty. In that case
`Report.compile_lastArtifact` equates it with the independent one-shot
result. The empty report retains the seed and runs no compiler.

## Checking a suffix after a refusal

`checkAllWrites` uses raw program transport to check the full bank at
each stage, even past a stopped compiler. A passing composite write
check alone leaves open aliases involving spare intermediate slots.
Use `checkAllWrites_append` to split the checks at a typed cut.
[Intermediate write aliases](rice-loop-sccp-write-admission.md)

Given a recorded FIFO refusal, `FailedStage.suffix_marks_subset` proves
that a suffix with passing staged write checks and a successful final
fact intersection can only remove marks relative to the reported row.
In particular, `neitherMarked` cannot recover a feedback route.
`Report.direct_of_failure` gives the exact one-shot outcome under passing
write checks at every stage. An empty final intersection gives
`incompatibleFacts`. A successful intersection reaches FIFO and gives
`neitherMarked`. The one-shot check may therefore stop at the fact
intersection while the stagewise check stops at FIFO. An unsafe suffix
lies outside this theorem and can trigger the one-shot write refusal.
[Single-stage FIFO law](rice-loop-sccp-first-fifo-admission.md)

The example extends the existing noninjective two-map fixture by a
read-only spare slot with value 8. The first stage admits true
feedback. The second stage shares the multiplier and threshold at 7,
so the header observes false for `7 < 7 * 1`. The third map either
inserts an unused predicate, identifies the spare 8 with the shared 7,
or aliases the spare slot with the written scratch. The same second
call is the first refusal in all three chains.

## Run the example

Save this snippet as a Lean file and run `lake env lean <file>`.

```lean
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.Chain.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.Chain.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.CaptureChain
open Example (compatible conflict aliasing successful summarize stoppedRow lastSelection)

#check run
#check FailedStage.suffix_marks_subset
#check Report.direct_of_failure
#check Report.compile_lastArtifact

#eval stoppedRow
-- The first artifact selects true. The second continuation is false,
-- only entry and exit are marked, and the FIFO stops after 9 visits with 0 pending.
#eval summarize compatible
-- All writes pass. Stage index 1 and the one-shot compiler both report neitherMarked.
#eval summarize conflict
-- All writes pass. Stage index 1 reports neitherMarked. One shot reports incompatibleFacts.
#eval summarize aliasing
-- The suffix fails its write check. Stage index 1 reports neitherMarked. One shot reports aliasedWrite.
#eval (summarize successful, lastSelection)
-- Both stages pass and the staged and direct artifacts select true.
```

[Public API](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/ContextEmbedding/FIFOAdmission/Chain/Thms.lean) ·
[Checked regressions](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/ContextEmbedding/FIFOAdmission/Chain/Regression.lean)
