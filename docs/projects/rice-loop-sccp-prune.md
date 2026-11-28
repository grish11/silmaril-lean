# Analyze and prune a carried-bank MLIR loop

Import `Silmaril.SSA.SeaOfNodes.Loop.SCCP.Prune.Thms` for the
executable `Loop.SCCP.Prune.rewrite` and its correctness laws.
Give it an existing `Loop.MLIR.CF.Bank.Program` and a typed tuple
of input facts. It computes the simultaneous SCCP solution once and
checks the backedge and exit marks.

| Backedge marked | Exit marked | Output |
| --- | --- | --- |
| No | Yes | Direct branch to the original exit with its result operand |
| Yes | No | Direct branch to the original header with the entire feedback column |
| Yes | Yes | `none` |
| No | No | `none` |

`rewrite_eq_some_iff` identifies the output with one of the two existing
branch-specific passes. `rewrite_eq_none_iff` characterizes refusal.
On inputs covered by the facts, `arrives_frame` preserves the exact
target label and typed operands at every reached header, `run_eq`
preserves execution at every block budget, and `denotePart_eq`
relates the target partial observation to the native loop.

The profile is the typed project MLIR CF pure loop with an ordered
bank of fixed-width carried words and one returned word. When exit
is infeasible, the dispatcher removes its incoming branch occurrence.
`blocks_eq` preserves the entry and exit blocks, including the
unreachable exit block. The branch-specific APIs remain available.
[Backedge removal](rice-loop-sccp-prune-exit.md) ·
[Exit-edge removal](rice-loop-sccp-prune-infeasible-exit.md) ·
[API](../../Silmaril/SSA/SeaOfNodes/Loop/SCCP/Prune/Thms.lean)

## Example

```lean
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Prune.Example.Defs

open Silmaril.SSA.SeaOfNodes.Loop.SCCP.Prune.Example

#eval run (.constant 1) 3 1  -- some (some 300)
#eval run (.constant 1) 2 1  -- some none
#eval run (.constant 0) 8 0  -- some none
#eval run .overdefined 8 0   -- none
#eval run .bottom 8 0        -- none
#eval refusesVarying         -- true
```

The same `i8, i16, i8` bank exits on flag 1 and takes feedback on flag 0.
The feedback path reads the old bank simultaneously and never returns.
The outer `none` means refusal, while `some none` means the rewritten
CFG exhausted that budget. The varying example is the earlier
counter, which takes feedback before exiting.
[Regressions](../../Silmaril/Proofs/SSA/SeaOfNodes/Loop/SCCP/Prune/Regression.lean)

## Rice source

Click's *Combining Analyses, Combining Optimizations*, §3.6 Figure 3.7
and §3.7 Figure 3.8, combines cyclic reachability with the constant
conditional test. §3.8.1 discusses applying the solved facts. This
dispatcher uses just the solved occurrence marks for one emitted
tail test. [Rice dissertation](https://hdl.handle.net/1911/16807)
