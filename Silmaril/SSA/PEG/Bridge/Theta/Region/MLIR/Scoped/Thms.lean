module

public import Silmaril.SSA.PEG.Bridge.Theta.Region.MLIR.Scoped.Defs
public import Silmaril.SSA.PEG.Bridge.Theta.Region.MLIR.Thms
public import Silmaril.SSA.RVSDG.MLIR.Graph.Feedback.Theta.Thms
import Silmaril.Proofs.SSA.PEG.Bridge.Theta.Region.MLIR.Scoped.Correctness

/-! # Finite returns of the scoped block agree with the numbered θ and SCF -/

@[expose] public section

namespace Silmaril.SSA.PEG.Bridge.Theta.Region.MLIR.Scoped

open RVSDG (Port Tuple)
open RVSDG.MLIR.Graph.Feedback
open Silmaril.MLIR.Arith (Env)
open Silmaril.MLIR.Pure (Eval)
open Silmaril.SSA.PEG.Bridge.Theta.Region.Ordered (Bundle)

variable {D : Type} {P : InstructionSet.{0,0} D}
variable {carried : List (Ty D)} {t : Ty D} {n : Nat}
variable {g : Graph P carried carried n 1} {slot : Port carried t} {invariants : Bool}

/-- Lower the numbered graph emitted by the existing bundle certificate. -/
def lower (b : Bundle g slot invariants) :
    RVSDG.MLIR.Graph.Feedback.Region (signature P) (valuePorts carried) (valuePorts carried) :=
  WholeTheta.lower b.compile (valuePorts_data carried)

theorem returns_iff_numbered (b : Bundle g slot invariants) (m : TotalModel P)
    (input output : Tuple m.toPEG.Value carried) :
    (lower b).Returns (model m) (encode m input) (encode m output) ↔
      b.compile.Returns (Region.model m) (Region.encode m input) (Region.encode m output) :=
  (WholeTheta.returns_lower_iff (model m) b.compile (valuePorts_data carried) _ _).trans
    (Proofs.runtime_returns m b.compile input output).symm

/-- Compare actual native SCF execution with the generated scoped block in
the same width-indexed primitive interpretation. -/
theorem scf_returns_iff (b : Bundle g slot invariants) (profile : Profile D)
    (evalOp : Eval (MLIR.Opcode profile P)) (input output : Env (profile.widths carried)) :
    let m := MLIR.model profile evalOp
    (∃ fuel, (MLIR.lower profile b).run evalOp fuel input = some output) ↔
      (lower b).Returns (model m) (encode m (profile.decode carried input))
        (encode m (profile.decode carried output)) :=
  (MLIR.returns_iff_numbered profile evalOp b input output).trans (returns_iff_numbered b _ _ _).symm

end Silmaril.SSA.PEG.Bridge.Theta.Region.MLIR.Scoped
