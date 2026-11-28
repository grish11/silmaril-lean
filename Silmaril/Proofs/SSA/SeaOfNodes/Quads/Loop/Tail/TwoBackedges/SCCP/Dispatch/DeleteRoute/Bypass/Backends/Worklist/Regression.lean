module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Worklist.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Worklist.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Worklist.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Worklist

open Bypass.MLIR.CF.Example (entry facts program regs word)
open Backends.Example (computesSelector stoppingFacts)
open Backends.Worklist.Example (feedbackMarks observations runPrefix)
open SeaOfNodes.Loop.MLIR.CF (Op model)

-- The preheader writes the selector Φ. Its pop wakes absent control.
#guard (SCCP.Worklist.step model computesSelector (facts .overdefined) (.phi ⟨1, by decide⟩) (runPrefix 3).state []).2 =
  [.control]
#guard (runPrefix 5).visits = [.control, .control, .phi ⟨0, by decide⟩, .phi ⟨1, by decide⟩, .phi ⟨2, by decide⟩]
#guard (runPrefix 5).pending = [.control]
#guard feedbackMarks (runPrefix 5) = (false, false)
#guard feedbackMarks (runPrefix 6) = (false, true)
#guard (runPrefix 6).pending = [.phi ⟨0, by decide⟩, .phi ⟨1, by decide⟩, .phi ⟨2, by decide⟩, .result]
#guard (runPrefix 10).pending.isEmpty

#guard observations computesSelector (facts .overdefined) (entry true true) 1 =
  .ok (false, some 7, some 7)
#guard observations program (facts (.constant ⟨false⟩)) (entry true false) 1 = .ok (false, some 7, some 7)
#guard observations program (facts (.constant ⟨true⟩)) (entry true true) 1 = .ok (true, some 99, some 99)
#guard (compile program (facts .overdefined)).map Targets.retained = .error .bothMarked
#guard (compile program stoppingFacts).map Targets.retained = .error .neitherMarked

/-- True feedback writes false to the selector, so joining with the true
entry fact widens it and eventually marks both feedback occurrences. -/
private def widensSelector : Program Op regs word :=
  { program with feedback := fun side =>
      program.feedback side ++ if side then computesSelector.preheader else [] }

#guard feedbackMarks
  (SCCP.Worklist.runSteps model widensSelector (facts (.constant ⟨true⟩)) 6 ⊥ SCCP.Worklist.initial) =
  (true, false)
#guard feedbackMarks (SCCP.Worklist.run model widensSelector (facts (.constant ⟨true⟩))) = (true, true)
#guard (compile widensSelector (facts (.constant ⟨true⟩))).map Targets.retained = .error .bothMarked

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Worklist
