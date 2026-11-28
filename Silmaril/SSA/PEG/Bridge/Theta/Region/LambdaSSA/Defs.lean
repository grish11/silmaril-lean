module

public import Silmaril.SSA.PEG.Bridge.Theta.Region.Tuple.Defs
public import Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaSSA.Schedule.Defs

/-! # Lower a checked ordered PEG loop to the existing λSSA loop form -/

@[expose] public section

namespace Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaSSA

open RVSDG (Port Tuple)
open Silmaril.SSA.PEG.Bridge.Theta.Region.Ordered (Bundle)
open RVSDG.LambdaSSA.Theta
open Isotope.LambdaSSA (Region)
open Simple.Revert.While.Region (Certificate)

variable {Data : Type} {P : InstructionSet.{0,0} Data}
variable {carried : List (Ty Data)} {result : Ty Data} {n : Nat}
variable {g : Graph P carried carried n 1} {slot : Port carried result} {allowInvariant : Bool}

/-- The false arm returns the current packet. The true arm evaluates the
update slice on that same packet, then commits the next tuple at the backedge. -/
def route {source : Graph P carried [result] n 1} (cert : Certificate source allowInvariant)
    (outputs : Schedule.Layout P (.bool :: carried)) : Region (Primitive P) :=
  let old : Schedule.Layout P carried := fun p => outputs.shift (.tail p)
  .case (.op .test (.pair (outputs .head) .unit))
    (.br 1 (Schedule.tupleTerm old (Simple.ports carried)))
    (Schedule.emit cert.update old fun next => .br 0 (Schedule.tupleTerm next (Simple.ports carried)))

/-- The header reads the ordered packet from variable zero with native
product eliminations, then emits one let per checked guard producer. -/
def header (b : Bundle g slot allowInvariant) : Region (Primitive P) :=
  Schedule.emit b.scalar.guard (fun p => Schedule.field p (.var 0)) (route b.scalar)

/-- Emit the existing one-header CFG with an actual local feedback branch. -/
def lower (b : Bundle g slot allowInvariant) : Region (Primitive P) :=
  Operational.loop (header b)

/-- Bounded execution through the verified numbered θ model. Each unit of
fuel permits one visit to the header, including the exit visit. -/
def runFuel (b : Bundle g slot allowInvariant) (m : TotalModel P)
    (fuel : Nat) (input : Tuple m.toPEG.Value carried) : Option (Tuple m.toPEG.Value carried) :=
  (Operational.runFuel (Region.model m) b.compile fuel (encode m input)).map
    (fromPorts (F := (Region.model m).Val) carried)

end Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaSSA
