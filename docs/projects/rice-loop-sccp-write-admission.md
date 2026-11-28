# Guarded SCCP write admission under composition

The pure five-block quad compiler checks that every written destination
has a singleton fibre under a typed port map. It checks all quads in the
preheader, header, true feedback, and false feedback, including writes
that the subsequent FIFO analysis might prove unreachable.

`WriteAdmission.diagnose first second intermediate` scans the actual
intermediate quads. A returned `Conflict` contains a write occurrence
and a distinct intermediate port of the writer's sort. The second map
sends the two ports to the same final slot, and the other port has no
preimage under the first map. `diagnose_sound` certifies the returned
pair and `diagnose_none_iff` gives the exact absence criterion. The
occurrence index distinguishes repeated writes to the same port.

`staged_checks_eq` states that both staged write checks pass exactly
when the composite write check passes and the diagnostic is empty.
An intermediate competitor inside the first image has an old preimage,
so the composite check already accounts for that competitor. A port
outside the image has no old preimage for the composite check to inspect.

## After the first compiler succeeds

Given `Identification.compile first p = .ok mid`, use `checked_second_eq`
on the stored intermediate program, or `second_passes_iff` when the
composite write check passes. The first success supplies the actual
transported program and the successful first write check.

`compile_by_diagnosis` gives the exact final compiler result under that
same first-success premise. With no diagnostic, the second compiler
and the direct compiler give equal results by the existing final
program and fact-intersection laws. Equality includes emissions on
success and the precise refusal on error. With a diagnostic, the
second compiler returns `.error .aliasedWrite`.

Final FIFO admission still depends on the recomputed row. A successful
first FIFO check can select a route even when both final calls refuse
with `neitherMarked`. [Final input and FIFO equality](rice-loop-sccp-exact-fact-transport.md) ·
[Noninjective FIFO fixture](rice-loop-sccp-noninjective-admission.md)

## Run the examples

Save this snippet as a Lean file and run `lake env lean <file>`.

```lean
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.WriteAdmission.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.WriteAdmission.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding
open WriteAdmission (diagnose second_passes_iff compile_by_diagnosis)
open WriteAdmission.Example (unsafeDiagnostic readOnlyDiagnostic withinImageChecks)

#check diagnose
#check second_passes_iff
#check compile_by_diagnosis

#eval unsafeDiagnostic
-- some (0, 4, 3, 3)
-- Preheader occurrence 0 writes i8 slot 4. The spare i8 slot 3 aliases it
-- at final slot 3. True feedback also writes slot 4.
#eval FactTransport.Example.unsafeOutcomes
-- First and direct select true. The second call refuses with aliasedWrite.

#eval readOnlyDiagnostic
-- some false: the first call succeeds and the read-only merge adds no alias.
#eval (LiftComposition.Example.run 65535 true, LiftComposition.Example.run 0 false)
-- Intermediate, staged and direct CF and numbered artifacts all return
-- 99 on the covered input and 14 on the fallback input.

#eval withinImageChecks
-- (true, false, false, false): first, second, composite, diagnostic present.
-- This collision is entirely inside the first image and both paths reject.
```

[Public laws](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/ContextEmbedding/WriteAdmission/Thms.lean) ·
[Checked regressions](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/ContextEmbedding/WriteAdmission/Regression.lean)
