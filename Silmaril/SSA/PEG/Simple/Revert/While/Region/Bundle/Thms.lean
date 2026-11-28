module

public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Bundle.Defs
public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Thms
import Silmaril.Proofs.SSA.PEG.Simple.Revert.While.Region.Bundle.Observation

public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Region.Bundle

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {carried rest : List (Ty Data)} {result : Ty Data} {n : Nat}
variable {g : Graph P carried (result :: rest) n 1}
variable (cert : Certificate g) {m : Interpretation.{u,v,w} P} {input : Tuple m.Value carried}

theorem Certificate.demandWellFounded (cert : Certificate g) : WellFounded g.Demand :=
  cert.scalar.demandWellFounded

/-- One successful emitted run supplies the checked common first exit
and the complete ordered observation. -/
theorem Certificate.firstExit_of_exec
    (neg : ∀ b : Bool, m.run cert.scalar.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (idx : Index 1) {output : Tuple m.Value (result :: rest)}
    (ran : Exec m cert.revert input (some output)) :
    ∃ k, Rules.readRef (g := g) (g.denote m input cert.demandWellFounded)
        cert.scalar.descriptor.pass idx = some ⟨k⟩ ∧
      g.observe m (g.denote m input cert.demandWellFounded) idx = output.map (fun _ => some) :=
  Proofs.firstExit_of_exec cert neg idx ran

/-- The full guard and simultaneous update must be total on defined stores
for the converse from a defined Figure 11 tuple. -/
theorem Certificate.exec_iff_observe (total : cert.scalar.Total m)
    (neg : ∀ b : Bool, m.run cert.scalar.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (idx : Index 1) (output : Tuple m.Value (result :: rest)) :
    Exec m cert.revert input (some output) ↔
      g.observe m (g.denote m input cert.demandWellFounded) idx = output.map (fun _ => some) :=
  ⟨fun ran => Exists.elim (cert.firstExit_of_exec neg idx ran) (fun _ seen => seen.2),
    Proofs.exec_of_observe cert total neg idx⟩

theorem Certificate.runFuel_exec (fuel : Nat) {output : Tuple m.Value (result :: rest)}
    (ran : cert.runFuel m fuel input = some output) : Exec m cert.revert input (some output) :=
  Proofs.runFuel_exec cert fuel ran

end Silmaril.SSA.PEG.Simple.Revert.While.Region.Bundle
