module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Thms
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.LiftComposition.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Facts
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Solver
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission.Compile

/-! The guarded FIFO admission seam for a suffix that only embeds the intermediate context. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open Silmaril.MLIR.Arith (Width)
open Composition (thenMap)
open Identification (program pushFacts PortMap)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (EntryFacts admit)
open Reindex.Guarded.Institution (AdmittedAt)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {S T U : EntrySignature} {out : ValueSort Width} {result : Width}

/-- Embed a successful intersection without changing its old facts.
A failed intersection remains a failure. -/
theorem pushFacts_embedding (first : PortMap S T) (path : Embedding T U) (facts : EntryFacts S.regs) :
    pushFacts (thenMap first path.portMap) facts = (pushFacts first facts).map (embedFacts path) :=
  Proofs.pushFacts_embedding first path facts

theorem fifo_marks (path : Embedding S T) (p : Program Op S.regs out) (facts : EntryFacts S.regs) :
    (@SCCP.Worklist.solve _ _ _ _ model (program path.portMap p) T.bankEq (embedFacts path facts)).1 =
      (@SCCP.Worklist.solve _ _ _ _ model p S.bankEq facts).1 :=
  Proofs.fifo_marks path p facts

/-- The actual FIFO returns the same refusal or the transported certificate.
This can be used even when the intermediate program has no admission. -/
theorem admit_embedding (path : Embedding S T) (p : Program Op S.regs (.data result)) (facts : EntryFacts S.regs) :
    @admit _ _ T.bankEq (program path.portMap p) (embedFacts path facts) =
      (@admit _ _ S.bankEq p facts).map path.mapAdmitted :=
  Proofs.admit_embedding path p facts

theorem replay_compose (first : PortMap S T) (path : Embedding T U) (p : AdmittedAt S result) :
    Identification.replay (thenMap first path.portMap) p =
      (Identification.replay first p).map path.mapAdmitted :=
  Proofs.replay_compose first path p

/-- The one-shot call and the staged embedding call have the same outcome,
including the actual stored CF and numbered artifacts on success. -/
theorem compile_direct_eq_staged (first : PortMap S T) (path : Embedding T U) (p : AdmittedAt S result) :
    Identification.compile (thenMap first path.portMap) p = Composition.compileStaged first path p :=
  Proofs.compile_direct_eq_staged first path p

/-- For the comparison using two ordinary typed-map checkers, either the
first call refuses or all three calls succeed. Both final artifacts are
exactly the one-shot result. -/
theorem compare_embedding (first : PortMap S T) (path : Embedding T U) (p : AdmittedAt S result) :
    (LiftComposition.compare first path.portMap p).map (fun q => (q.staged, q.direct)) =
      ((Identification.compile (thenMap first path.portMap) p).map (fun q => (q, q))).mapError
        LiftComposition.Refused.first :=
  Proofs.compare_embedding first path p

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Admission
