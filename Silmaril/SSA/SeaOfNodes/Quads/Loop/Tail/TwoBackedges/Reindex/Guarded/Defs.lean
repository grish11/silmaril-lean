module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Thms
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded.Admission

/-! Re-admit a renamed program at its new typed boundary, then use the existing emitters. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open SeaOfNodes.Loop.MLIR.CF (model)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)
open SCCP.Dispatch (Checked)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted)

variable {old new : List (ValueSort Width)} {result : Width}
variable [BankDecidableEq Word (dataPorts old)] [BankDecidableEq Word (dataPorts new)]

/-- Reuse the side certificate at the new boundary. Its mark proofs use
conjugacy of the least solution of the actual renamed SCCP analysis. -/
def checked (order : Registers old new) (p : Admitted old result) :
    Checked model (program order p.source) (push order p.facts) where
  side := p.checked.side
  marked := by rw [solve_assignment]; exact p.checked.marked
  excluded := by rw [solve_assignment]; exact p.checked.excluded

/-- Transport the singleton certificate to the renamed source and facts,
with a proof that the existing FIFO checker admits them. -/
def reindex (order : Registers old new) (p : Admitted old result) : Admitted new result where
  source := program order p.source
  facts := push order p.facts
  checked := checked order p
  admitted := by exact Proofs.fifo_accepts (checked order p)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded
