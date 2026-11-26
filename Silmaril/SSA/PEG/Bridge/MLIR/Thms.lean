module

public import Silmaril.SSA.PEG.Bridge.MLIR.Defs
public import Silmaril.SSA.PEG.Bridge.RVSDG.Thms
import Silmaril.Proofs.SSA.PEG.Bridge.MLIR.Correctness

public section

namespace Silmaril.SSA.PEG.Bridge

open RVSDG (Tuple)
open Silmaril.SSA.RVSDG.MLIR

variable {Data : Type} {P : InstructionSet.{0,0} Data}
variable {params results : List (Ty Data)} {n : Nat}

/-- The existing profile pullback recovers the same RVSDG value model. -/
theorem pullback_toMLIR (m : TotalModel P) :
    (profileMap P).pullback m.toMLIR = m.toRVSDG :=
  Proofs.pullback_toMLIR m

/-- Assemble the MLIR result slots in order to recover the guarded PEG roots. -/
theorem observe_translateMLIR (g : Graph P params results n 0) (ordered : Ordered g)
    (m : TotalModel P) (env : Tuple m.toPEG.Value params) (idx : Index 0)
    (wf : WellFounded g.Demand) :
    g.observe m.toPEG (g.denote m.toPEG env wf) idx =
      (fromPorts results (Regionless.ofAssignment (F := m.toRVSDG.Val) results (fun i =>
        (translateMLIR g ordered i).denote m.toMLIR
          (Regionless.toAssignment params (toPorts (F := m.toRVSDG.Val) env))))).map (fun _ => some) :=
  Proofs.mlir_correct g ordered m env idx wf

/-- Exact satisfaction for the ordered observation in the induced RVSDG model. -/
theorem Equation.rvsdg_satisfaction (e : Equation P) (m : TotalModel P) :
    e.toRVSDG.toRVSDG.Holds m.toRVSDG ↔ e.Holds m :=
  Proofs.rvsdg_satisfaction e m

/-- Exact satisfaction for the ordered observation in the induced MLIR model. -/
theorem Equation.mlir_satisfaction (e : Equation P) (m : TotalModel P) :
    e.toMLIR.Holds m.toMLIR ↔ e.Holds m :=
  Proofs.mlir_satisfaction e m

end Silmaril.SSA.PEG.Bridge
