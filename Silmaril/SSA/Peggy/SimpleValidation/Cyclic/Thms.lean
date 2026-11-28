module

public import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Defs
public import Silmaril.SSA.Peggy.Optimizer.Cyclic.Thms
public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Thms

public section

namespace Silmaril.SSA.Peggy.SimpleValidation.Cyclic

open PEG
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params : List (Ty Data)} {result : Ty Data} {n : Nat}
variable {g : Graph P params [result] (n + 1) 1}
variable {allowInvariant : Bool}

theorem Accepted.sourceDemandWellFounded (a : Accepted g allowInvariant) : WellFounded g.Demand :=
  g.demandWellFounded_of_check a.sourceRank a.sourceRanked

/-- The checked rewrite equates the original and compacted observations.
The reverter's full-step and negation premises then give exact agreement
between successful SIMPLE returns and defined observations of the input. -/
theorem Accepted.returns_iff_observe (a : Accepted g allowInvariant) (m : Interpretation.{u,v,w} P)
    (input : Tuple m.Value params) (total : a.reversion.Total m)
    (neg : ∀ b : Bool, m.run a.reversion.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (i : Index 1) (value : m.Value result) :
    a.output.Returns m input value ↔
      g.observe m (g.denote m input a.sourceDemandWellFounded) i = .cons (some value) .nil := by
  rw [a.rewrite.replay.sound a.sourceDemandWellFounded m input i]
  exact a.reversion.returns_iff_observe m input total neg i value

end Silmaril.SSA.Peggy.SimpleValidation.Cyclic
