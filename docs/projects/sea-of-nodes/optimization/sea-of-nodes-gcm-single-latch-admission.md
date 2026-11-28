# Terminal hoist completeness for the saved single-latch CFG

The existing ranker always selects the latest accepted physical preheader
splice for a live origin that has one. On the supported typed CFG, the
anonymous entry jumps to the header, exactly one conditional occurrence is a
self-edge, the other targets the return block, and the origin inventory
matches the header. Either conditional slot can carry feedback.

The actual CFG is successor-closed and all three blocks are reachable.
Its self-edge is the only dominating backedge, and the certified natural-loop
forest counts precisely the header. The preheader, header and exit have
depths zero, one and zero. Consequently, a checked preheader cut wins over
every header position visited by the ranker at any walk budget. The ranker
uses the latest accepted cut within the preheader as before. This is the
represented single-latch instance of Click's dominator and loop setup and
minimum-loop-depth choice in §§2.1 and 2.4. Multi-block loop bodies,
exitless loops and global scheduling optimality are outside this theorem.
[Click PLDI ’95][paper] · [Coverage ledger][coverage] · [Cut search][search]

Import `Layout.SingleLatch.Thms` at the full path below. `control_exists`
and `control_depths` close the control admission obligation for this shape.
`rank_exists` discharges rank admission when the retained-header check
succeeds. `ranked_selects_latest` relates the winner to the exact result of
the physical cut search. `emit_supported` preserves the successor slots
after widening the header packet and validates the remaining origin
inventory by the operation count. `choose_none_iff` characterizes refusal
on any supported current layout, and `schedule_terminal` applies it to
every successful schedule's actual output without a separate shape premise.
[Public theorems][thms]

The terminal inventory excludes a splice when the origin has no checked
live retained-header placement or when no physical cut from zero through
the current saved-prefix length passes the splice checker. The regression
tests both the depth decision and a raw splice of an unused origin. The
scheduler saves the producer and its consumer, then leaves the unused
origin in the header even though the low-level emitter can move it. The
existing replay and observation laws apply to the same returned plan.
They preserve the saved packets and compare returns and exhaustion at common
CFG fuel and partial denotation under the existing layout, saved-packet and
append-prefix premises. [Regression][regression] · [Ranked discovery][discovery]

```sh
lake build --wfail +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.SingleLatch.Regression
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.SingleLatch.Thms
```

[paper]: https://doi.org/10.1145/207110.207154
[coverage]: ../coverage.md#global-code-motionglobal-value-numbering
[search]: sea-of-nodes-gcm-preheader-search.md
[discovery]: sea-of-nodes-gcm-ranked-discovery.md
[thms]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Layout/SingleLatch/Thms.lean
[regression]: ../../../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Layout/SingleLatch/Regression.lean
