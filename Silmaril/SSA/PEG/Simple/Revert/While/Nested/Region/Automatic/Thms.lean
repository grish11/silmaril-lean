module

public import Silmaril.SSA.PEG.Simple.Revert.While.Nested.Region.Automatic.Defs
public import Silmaril.SSA.PEG.Simple.Revert.While.Nested.Region.Thms

public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Nested.Region.Automatic

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {outer : List (Ty Data)} {result : Ty Data} {n l : Nat}
variable {g : Graph P outer [result] n l} {m : Interpretation.{u,v,w} P}
variable {negate : P [.bool] .bool}

theorem Recovered.negates (a : Recovered g negate)
    (law : ∀ b : Bool, m.run negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩) (b : Bool) :
    m.run a.certificate.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩ :=
  a.negate_eq.symm ▸ law b

/-- Inferred reversion has the same successful-return guarantee as the
supplied-descriptor checker. -/
theorem Recovered.observe_of_returns (a : Recovered g negate)
    (law : ∀ b : Bool, m.run negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (input : Tuple m.Value outer) (base : Index l) {value : m.Value result}
    (ran : a.certificate.revert.Returns m input value) :
    g.observe m (g.denote m input a.certificate.demandWellFounded) base = .cons (some value) .nil :=
  a.certificate.observe_of_returns (a.negates law) input base ran

theorem Recovered.returns_iff_exits (a : Recovered g negate)
    (law : ∀ b : Bool, m.run negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (input : Tuple m.Value outer)
    (slices : a.certificate.DefinedSlices m (g.denote m input a.certificate.demandWellFounded))
    (base : Index l) (value : m.Value result) :
    a.certificate.revert.Returns m input value ↔
      (∃ count, a.certificate.FirstExits m (g.denote m input a.certificate.demandWellFounded) base count) ∧
        g.observe m (g.denote m input a.certificate.demandWellFounded) base = .cons (some value) .nil :=
  a.certificate.returns_iff_exits (a.negates law) input slices base value

end Silmaril.SSA.PEG.Simple.Revert.While.Nested.Region.Automatic
