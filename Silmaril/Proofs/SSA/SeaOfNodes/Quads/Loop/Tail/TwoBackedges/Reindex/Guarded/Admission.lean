module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Worklist.Thms

/-! Every certificate with exactly one marked feedback route is returned by the FIFO checker. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded.Proofs

open SeaOfNodes.Diamond (Model ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open RVSDG (Tuple)
open SCCP.Dispatch (Checked admitWith)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Worklist (admit admit_eq_simultaneous)

universe u v w

theorem fifo_accepts {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
    {regs : List (ValueSort Data)} {out : ValueSort Data}
    {m : Model.{u, v, w} Op} [BankDecidableEq m.value (dataPorts regs)]
    {p : Program Op regs out} {facts : Tuple (Fact m.value) (dataPorts regs)}
    (checked : Checked m p facts) :
    admit m p facts = .ok checked := by
  rw [admit_eq_simultaneous]
  cases checked with
  | mk side marked excluded =>
    cases side
    · change SCCP.incomingIndex (.feedback true) ∉ (SCCP.solve m p facts).1 at excluded
      simp only [SCCP.Dispatch.admit, admitWith, dite_eq_right excluded, dite_eq_left marked]
    · change SCCP.incomingIndex (.feedback false) ∉ (SCCP.solve m p facts).1 at excluded
      simp only [SCCP.Dispatch.admit, admitWith, dite_eq_left marked, dite_eq_right excluded]

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded.Proofs
