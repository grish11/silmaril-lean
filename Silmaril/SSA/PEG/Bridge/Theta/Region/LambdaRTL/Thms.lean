module

public import Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaRTL.Defs
public import Silmaril.SSA.PEG.Bridge.Theta.Region.Tuple.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Theta.Operational.Thms
import Silmaril.Proofs.SSA.PEG.Bridge.Theta.Region.LambdaRTL.Correctness

public section

namespace Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaRTL

open RVSDG (Port Tuple)
open ForwardCFG (Value)
open RVSDG.LambdaSSA.Theta
open Silmaril.SSA.PEG.Bridge.Theta.Region.Ordered (Bundle)

variable {Data : Type} {P : InstructionSet.{0,0} Data} [DecidableEq Data]
variable {carried : List (Ty Data)} {t : Ty Data} {n : Nat}
variable {g : Graph P carried carried n 1} {slot : Port carried t} {invariants : Bool}
variable (b : Bundle g slot invariants) (m : TotalModel P)

/-- Two target steps per numbered θ activation. A continuing activation
runs both blocks. A stopping activation runs before and resolves the exit. -/
theorem observeFuel_eq (fuel : Nat) (input : Tuple m.toPEG.Value carried) :
    observeFuel b m fuel input =
      (Operational.runFuel (Region.model m) b.compile (fuel / 2) (encode m input)).map
        (fun result => (Label.exit, Value.pack (fromPorts (F := (Region.model m).Val) carried result))) :=
  Proofs.observeFuel_eq m b fuel input

theorem mem_observe_iff (input : Tuple m.toPEG.Value carried) (label : Label)
    (value : Value m.toPEG.Value) :
    (label, value) ∈ observe b m input ↔ ∃ fuel, observeFuel b m fuel input = some (label, value) :=
  Proofs.mem_observe_iff m b input label value

/-- Every successful return leaves by the external exit with a typed
packet in the declared carried-slot order. -/
theorem observe_result (input : Tuple m.toPEG.Value carried) {label : Label}
    {value : Value m.toPEG.Value} (ran : (label, value) ∈ observe b m input) :
    ∃ output : Tuple m.toPEG.Value carried, label = .exit ∧ value = Value.pack output :=
  Proofs.observe_result m b input ran

theorem returns_iff_numbered (input output : Tuple m.toPEG.Value carried) :
    (Label.exit, Value.pack output) ∈ observe b m input ↔
      b.compile.Returns (Region.model m) (encode m input) (encode m output) :=
  (mem_observe_iff b m input .exit (Value.pack output)).trans
    (Proofs.returns_iff_numbered m b input output)

variable (neg : ∀ flag : Bool,
  m.run b.scalar.descriptor.negate (.cons ⟨flag⟩ .nil) = ⟨!flag⟩)

include neg

/-- Finite cyclic λRTL execution returns exactly the complete, ordered
Figure 11 observation of the checked PEG loop. -/
theorem returns_iff_observe (input output : Tuple m.toPEG.Value carried) (idx : Index 1) :
    (Label.exit, Value.pack output) ∈ observe b m input ↔
      g.observe m.toPEG (g.denote m.toPEG input b.demandWellFounded) idx = output.map (fun _ => some) :=
  (returns_iff_numbered b m input output).trans (b.returns_iff_observe m input neg idx output)

/-- A finite cyclic λRTL return supplies one first exit and the defined
Figure 11 prefixes for every eval root in the bundle. -/
theorem firstExit_of_return (input output : Tuple m.toPEG.Value carried) (idx : Index 1)
    (ran : (Label.exit, Value.pack output) ∈ observe b m input) :
    ∃ (k : Nat) (start final : Tuple m.toPEG.Value (.bool :: carried)),
      b.scalar.guard.lower.runLoopFree m.toPEG input = some start ∧
      Simple.WhileTrace m.toPEG (.var .head) b.scalar.body.enableWhile k start final ∧
      carriedValues final = output ∧
      b.scalar.TraceObservation m.toPEG (g.denote m.toPEG input b.demandWellFounded) idx k final ∧
      g.observe m.toPEG (g.denote m.toPEG input b.demandWellFounded) idx = output.map (fun _ => some) :=
  b.firstExit_of_returns m input neg idx output ((returns_iff_numbered b m input output).mp ran)

end Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaRTL
