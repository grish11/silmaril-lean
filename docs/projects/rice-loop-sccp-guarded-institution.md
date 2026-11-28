# Compose guarded SCCP register signatures

`TwoBackedges.Reindex.Guarded.Institution.Signature` describes an ordered
typed register bank. Its default equality dictionary compares Booleans and
fixed-width words at each coordinate. A caller can supply the dictionary
already used by an existing admission. An arrow is a sort-preserving
permutation of ports. Each institution fixes the primitive interpretation,
result width, and the pure five-block profile with two feedback occurrences.
[Signature and generated artifact types](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/Reindex/Guarded/Institution/Defs.lean)

`mapAdmitted` transports the source and entry facts forward using the
existing singleton-admission theorem. `mapAdmitted_id` and `mapAdmitted_comp`
prove equality of the actual admitted records, using the typed quad and
tuple laws and determinism of the checker. The model reduct is `reduct`,
which reads a new typed valuation in the old register order. It composes in
reverse order. Equations compare partial words, including equality of two
undefined observations. Termination requires a finite return.
[Native reindexing and admission](rice-loop-sccp-guarded-reindex.md)

`nativeInst` and `generatedInst` are institutions in the repository's
`Sign ⥤ Room` interface. Generated sentences retain the admitted source
alongside the actual emitted CFG and numbered graph. `Generated.map`
re-emits from that source. Its identity and composition laws are equalities
of the generated records and therefore of the stored artifacts.
`comparison` is a comorphism over the identity signature functor for each
choice of CF, numbered RVSDG, and linked coloured Petri. `emit_natural`,
`emit_id`, and `emit_comp` compare the actual sentence maps and valuation
reducts as corridors.

`Generated.returns_map` compares exact words using independent finite
witnesses at the two signatures. CF uses block runs, numbered RVSDG uses
θ runs, and Petri uses finite completion of the net linked from the same
numbered artifact. `Generated.observe_map` includes the absence of a finite
observation. At a fixed signature, `artifactsCorridor` forgets provenance
and recovers the existing artifact comparison by `emit_artifacts`.
Cross-signature transport is defined on generated artifacts with admitted
provenance. Petri definedness is existence of a finite completed trace.
[Institution, comparison and observation laws](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/Reindex/Guarded/Institution/Thms.lean)

## Run staged and composite transport

The fixture moves `[again, select, byte]` to `[again, byte, select]`
and then to `[byte, again, select]`. The last Bool now controls coverage
at the new entry. Each printed triple is the native, CF, and numbered
result. The two orders of compilation agree for both guard outcomes.

```lean
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded.Institution.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded.Institution.Example.Defs

open CategoryTheory
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded.Institution
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded.Institution.Example
  (first second original staged direct run)

#eval (run staged true, run direct true)
-- ((some 99, some 99, some 99), some 99, some 99, some 99)

#eval (run staged false, run direct false)
-- ((some 7, some 7, some 7), some 7, some 7, some 7)

example : direct = staged :=
  Generated.map_comp first second (Generated.lower original)
```

The checked regression also exercises finite Petri returns and the
staged-versus-composite satisfaction law for both sentence forms.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/Reindex/Guarded/Institution/Regression.lean)
