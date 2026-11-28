module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission

open Example (previousWriteChecks previousRows previousOneShotRefusal embeddingRefusals embeddedAccepted)
open Identification.Example (old identify)
open Composition.Example (insertion staged direct run)
open LiftComposition.Example (compilerRefusal)
open SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example (width)
open Reindex.Guarded.Institution (AdmittedAt)
open Semantics.Dataflow (Flat)

#guard previousWriteChecks == some (true, true, true)
#guard previousRows == some
  [((.constant 7, .overdefined), (.overdefined, true, false, true)),
   ((.constant 7, .constant 7), (.constant ⟨false⟩, false, false, true)),
   ((.constant 7, .constant 7), (.constant ⟨false⟩, false, false, true))]
#guard compilerRefusal == some (.first (.checker .neitherMarked))
#guard previousOneShotRefusal == some (.checker .neitherMarked)
#guard embeddingRefusals == some (some (.first (.checker .neitherMarked)), some (.checker .neitherMarked))
#guard embeddedAccepted
#guard run staged 65535 true == some (some 99, some 99, some 99)
#guard run direct 0 true == some (some 99, some 99, some 99)
#guard run staged 0 false == some (some 14, some 14, some 14)
#guard run direct 65535 false == some (some 14, some 14, some 14)

example (source : AdmittedAt old width) :
    Identification.compile (Composition.thenMap identify insertion.portMap) source =
      Composition.compileStaged identify insertion source :=
  compile_direct_eq_staged identify insertion source

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission
