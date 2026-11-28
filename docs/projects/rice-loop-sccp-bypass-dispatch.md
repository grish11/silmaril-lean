# Bypass the empty dispatcher in the compact quad loop

`SCCP.Dispatch.DeleteRoute.Bypass.bypass checked` consumes the singleton
certificate used by the four-block cleanup and emits a three-block
`Tail.Source`. `Bypass.rewrite model program inputFacts` runs the
same admission check. `compact_dispatcher` proves that the skipped
block has an empty body and an unconditional jump. `dispatcher_step`
proves that the jump passes the entire typed bank to feedback for any
bank. This construction uses the fixed compact output of the checker.
[Four-block cleanup](rice-loop-sccp-delete-route.md) ·
[Definitions](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/DeleteRoute/Bypass/Defs.lean)

The existing three-block `Tail.Program` tests after its latch
assignments. This loop tests before feedback. The three-block source
therefore keeps the test and return read on header 1, with a direct
true jump to block 2. The retained-block map sends new indices
`[0, 1, 2]` to compact indices `[0, 1, 3]`. Lean checks the
retained bodies, both header predecessor occurrences, and their
complete reaching banks. On a covered continuing arrival,
`feedback_arrival` recovers the selected original feedback bank.
[Existing tail profile](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Defs.lean) ·
[Bypass laws](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/DeleteRoute/Bypass/Thms.lean)

For inputs covered by the abstract entry contract, `ReturnsAfter`
records the number `n` of actual feedback steps before a returning
header. `return_budgets` proves that the compact source returns at
budget `3 * n + 2` and above, and the bypassed source returns at
`2 * n + 2` and above. Each exhausts below its cutoff.
`feedback_budget_eq` compares return or exhaustion at budgets allowing
the same number of feedback steps, including nonreturning cases.
`rewrite_returns_iff` and `rewrite_noFiniteReturn_iff` compose through
the compact source to the original five-block runner.

## Run the example

```lean
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Example

#eval originalBlocks (.constant ⟨false⟩)  -- some [0, 1, 4]
#eval originalBlocks (.constant ⟨true⟩)   -- some [0, 1, 3]
#eval originalBlocks .overdefined        -- none
#eval returnPair false 4                 -- some (none, some 7)
#eval returnPair true 5                  -- some (some 99, some 99)
#eval immediateExit 2                    -- some (some 7, some 7)
#eval repeatPair 6                       -- some (none, some 3)
#eval repeatPair 8                       -- some (some 3, some 3)
#eval loopPair 18                        -- some (none, none)
```

The outer option reports admission. Each pair shows the compact
observation first and the bypassed observation second. The repeated
fixture takes two feedback jumps before returning `3`. Immediate
exit visits neither dispatcher nor feedback. The continuing fixture
exercises the bypass in a loop with no finite return.
[Checked regressions](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/DeleteRoute/Bypass/Regression.lean)

Rice §3.6, Figure 3.7 (printed p. 26), supplies cyclic reachability.
The singleton certificate and empty body justify this bypass in the
fixed pure quad profile. General CFG SCCP, sparse scheduling, and
lowering this header-tested shape to other IRs are outside this slice.
[Rice dissertation](https://hdl.handle.net/1911/16807) ·
[Wegman–Zadeck](https://doi.org/10.1145/103135.103136)
