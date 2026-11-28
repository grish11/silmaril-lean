module

public import Silmaril.SSA.PEG.Bridge.Theta.Region.Defs
public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Thms
import Silmaril.Proofs.SSA.PEG.Bridge.Theta.Region.Compilation
import Silmaril.Proofs.SSA.PEG.Bridge.Theta.Region.Operational

public section

namespace Silmaril.SSA.PEG.Bridge.Theta.Region

open RVSDG (Tuple)
open Simple (WhileTrace)
open Simple.Revert.While.Region (Certificate)

variable {Data : Type} {P : InstructionSet.{0,0} Data}
variable {carried : List (Ty Data)} {result : Ty Data} {n : Nat}
variable {g : Graph P carried [result] n 1} {allowInvariant : Bool}
variable (cert : Certificate g allowInvariant) (m : TotalModel P)
variable (input : Tuple m.toPEG.Value carried)

/-- The compiled body evaluates the checked guard and routes the same old
vector to either the return or the update slice. True requests feedback. -/
theorem body_run :
    ∃ (guard : ULift Bool) (old next : Tuple m.toPEG.Value carried),
      cert.guard.lower.runLoopFree m.toPEG input = some (.cons guard old) ∧
      cert.update.lower.runLoopFree m.toPEG old = some next ∧
      (compile cert).body.run (model m) (encode m input) =
        RVSDG.Theta.bodyResult (model m) guard.down (encode m (if guard.down then next else old)) :=
  Proofs.body_run m cert input

/-- Every successful SIMPLE body step accounts for one θ restart. The
final false test accounts for the mandatory stopping activation. -/
theorem returns_iff_trace (output : Tuple m.toPEG.Value carried) :
    (compile cert).Returns (model m) (encode m input) (encode m output) ↔
      ∃ (k : Nat) (start final : Tuple m.toPEG.Value (.bool :: carried)),
        cert.guard.lower.runLoopFree m.toPEG input = some start ∧
        WhileTrace m.toPEG (.var .head) cert.body.enableWhile k start final ∧
        carriedValues final = output :=
  Proofs.returns_iff_trace cert m input output

variable (neg : ∀ b : Bool, m.run cert.descriptor.negate (.cons ⟨b⟩ .nil) = ⟨!b⟩)

include neg

/-- A defined PEG result supplies an exact first-pass count and the eval
prefix. The numbered θ returns the full carried tuple at that exit. -/
theorem return_at_firstExit (idx : Index 1) (value : m.toPEG.Value result)
    (defined : g.observe m.toPEG (g.denote m.toPEG input cert.demandWellFounded) idx =
      .cons (some value) .nil) :
    ∃ (k : Nat) (start final : Tuple m.toPEG.Value (.bool :: carried)),
      cert.guard.lower.runLoopFree m.toPEG input = some start ∧
      cert.ExitWitness m.toPEG (g.denote m.toPEG input cert.demandWellFounded) idx k start final value ∧
      (compile cert).Returns (model m) (encode m input)
        (encode m (carriedValues final)) :=
  Proofs.return_at_firstExit cert m input neg idx value defined

/-- The existing checker designates one PEG eval root. Its guarded Figure
11 observation agrees exactly with projection of a finite RVSDG return. -/
theorem returns_iff_observe (idx : Index 1) (value : m.toPEG.Value result) :
    (∃ output : Tuple m.toPEG.Value carried,
      (compile cert).Returns (model m) (encode m input) (encode m output) ∧
      output.get cert.descriptor.returnSlot = value) ↔
    g.observe m.toPEG (g.denote m.toPEG input cert.demandWellFounded) idx = .cons (some value) .nil :=
  Proofs.returns_iff_observe cert m input neg idx value

end Silmaril.SSA.PEG.Bridge.Theta.Region
