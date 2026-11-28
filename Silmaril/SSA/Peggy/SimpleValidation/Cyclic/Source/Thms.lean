module

public import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Source.Defs
public import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Thms
public import Silmaril.SSA.PEG.Simple.While.Thms

public section

namespace Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Source

open PEG PEG.Simple
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params : List (Ty Data)} {result : Ty Data}
variable {p : WhileProgram P params result} {negate : P [.bool] .bool}

/-- A successful source execution gives a defined observation in its
compiled PEG. Replay and checked reversion turn that observation into
the same successful SIMPLE return on the same input. -/
theorem Accepted.returns (a : Accepted p negate) (m : Interpretation.{u,v,w} P)
    (input : Tuple m.Value params) (total : a.cyclic.reversion.Total m)
    (neg : ∀ b : Bool, m.run negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    {value : m.Value result} (run : p.source.Returns m input value) :
    a.output.Returns m input value := by
  have targetNeg b : m.run a.cyclic.reversion.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩ := by
    rw [a.negate_eq]; exact neg b
  exact (a.cyclic.returns_iff_observe m input total targetNeg (fun _ => 0) value).mpr
    (p.translate_returns negate m input neg run (fun _ => 0))

end Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Source
