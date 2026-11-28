module

public import Silmaril.SSA.PEG.Projection.Thms
public import Silmaril.SSA.PEG.Simple.Revert.While.Nested.Projected.Defs
public import Silmaril.SSA.PEG.Simple.Revert.While.Nested.Reindexed.Automatic.Thms

public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Nested.Projected

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {outer : List (Ty Data)} {result : Ty Data} {n l : Nat}
variable {g : Graph P outer [result] n l}

/-- The full graph must have a well-founded demand relation to use its
global Figure 11 denotation. The projected reverter checks its own
demands independently of the discarded rows. -/
theorem Accepted.returns_iff_observe [DecidableEq Data] (a : Accepted g)
    (m : Interpretation.{u,v,w} P) (input : Tuple m.Value outer) (wf : WellFounded g.Demand)
    (total : a.core.form.Total m)
    (neg : ∀ b : Bool, m.run a.core.form.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (i : Index l) (value : m.Value result) :
    a.revert.Returns m input value ↔
      g.observe m (g.denote m input wf) i = .cons (some value) .nil := by
  rw [← a.projection.observe_denote m input wf a.core.demandWellFounded i]
  exact a.core.returns_iff_observe m input total neg i value

end Silmaril.SSA.PEG.Simple.Revert.While.Nested.Projected
