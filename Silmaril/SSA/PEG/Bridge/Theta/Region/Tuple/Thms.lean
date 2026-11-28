module

public import Silmaril.SSA.PEG.Bridge.Theta.Region.Tuple.Defs
public import Silmaril.SSA.PEG.Bridge.Theta.Region.Thms
import Silmaril.Proofs.SSA.PEG.Bridge.Theta.Region.Tuple.Observation

public section

namespace Silmaril.SSA.PEG.Bridge.Theta.Region.Ordered

open RVSDG (Port Tuple)
open Simple (WhileTrace)

variable {Data : Type} {P : InstructionSet.{0,0} Data}
variable {carried : List (Ty Data)} {result : Ty Data} {n : Nat}
variable {g : Graph P carried carried n 1} {slot : Port carried result} {allowInvariant : Bool}
variable (b : Bundle g slot allowInvariant) (m : TotalModel P)
variable (input : Tuple m.toPEG.Value carried)
variable (neg : ∀ flag : Bool, m.run b.scalar.descriptor.negate (.cons ⟨flag⟩ .nil) = ⟨!flag⟩)

include neg

/-- One finite θ execution supplies a common first pass, every carried
sample at that exit, and the defined prefixes required by all eval roots. -/
theorem Bundle.firstExit_of_returns (idx : Index 1) (output : Tuple m.toPEG.Value carried)
    (ran : b.compile.Returns (Region.model m) (encode m input) (encode m output)) :
    ∃ (k : Nat) (start final : Tuple m.toPEG.Value (.bool :: carried)),
      b.scalar.guard.lower.runLoopFree m.toPEG input = some start ∧
      WhileTrace m.toPEG (.var .head) b.scalar.body.enableWhile k start final ∧
      carriedValues final = output ∧
      b.scalar.TraceObservation m.toPEG (g.denote m.toPEG input b.demandWellFounded) idx k final ∧
      g.observe m.toPEG (g.denote m.toPEG input b.demandWellFounded) idx = output.map (fun _ => some) :=
  Proofs.firstExit_of_returns b m input neg idx output ran

/-- Exact correspondence between the numbered θ finite return and the
fully defined ordered Figure 11 observation of the same tuple. -/
theorem Bundle.returns_iff_observe (idx : Index 1) (output : Tuple m.toPEG.Value carried) :
    b.compile.Returns (Region.model m) (encode m input) (encode m output) ↔
      g.observe m.toPEG (g.denote m.toPEG input b.demandWellFounded) idx = output.map (fun _ => some) :=
  Proofs.returns_iff_observe b m input neg idx output

omit neg

variable {result' : Ty Data} {n' : Nat} {h : Graph P carried carried n' 1}
variable {slot' : Port carried result'} {allowInvariant' : Bool}

/-- Equality of all successful ordered PEG observations is equivalent to
equality of the induced finite RVSDG return relations. -/
theorem defined_satisfaction_iff (other : Bundle h slot' allowInvariant')
    (neg₁ : ∀ flag : Bool, m.run b.scalar.descriptor.negate (.cons ⟨flag⟩ .nil) = ⟨!flag⟩)
    (neg₂ : ∀ flag : Bool, m.run other.scalar.descriptor.negate (.cons ⟨flag⟩ .nil) = ⟨!flag⟩) :
    (∀ (entry : Tuple m.toPEG.Value carried) (idx : Index 1) (out : Tuple m.toPEG.Value carried),
      g.observe m.toPEG (g.denote m.toPEG entry b.demandWellFounded) idx = out.map (fun _ => some) ↔
      h.observe m.toPEG (h.denote m.toPEG entry other.demandWellFounded) idx = out.map (fun _ => some)) ↔
    (∀ (entry out : Tuple m.toPEG.Value carried),
      b.compile.Returns (Region.model m) (encode m entry) (encode m out) ↔
      other.compile.Returns (Region.model m) (encode m entry) (encode m out)) := by
  constructor
  · intro agrees entry out
    let idx : Index 1 := fun _ => 0
    exact (b.returns_iff_observe m entry neg₁ idx out).trans
      ((agrees entry idx out).trans (other.returns_iff_observe m entry neg₂ idx out).symm)
  · intro agrees entry idx out
    exact (b.returns_iff_observe m entry neg₁ idx out).symm.trans
      ((agrees entry out).trans (other.returns_iff_observe m entry neg₂ idx out))

end Silmaril.SSA.PEG.Bridge.Theta.Region.Ordered
