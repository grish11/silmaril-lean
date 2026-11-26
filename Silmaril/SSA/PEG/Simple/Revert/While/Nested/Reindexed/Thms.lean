module

public import Silmaril.SSA.PEG.Simple.Revert.While.Nested.Reindexed.Defs
public import Silmaril.SSA.PEG.Simple.Revert.While.Nested.Automatic.Thms
public import Silmaril.SSA.PEG.Semantics.Reindex.Thms

public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Nested.Reindexed

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {outer : List (Ty Data)} {result : Ty Data} {n l k : Nat}
variable {g : Graph P outer [result] n l} {rows : Fin k ≃ Fin n} {loops : Fin k ≃ Fin l}

theorem demandWellFounded [DecidableEq Data] (accepted : Automatic.Accepted (g.reindex rows loops)) :
    WellFounded g.Demand :=
  (g.demandWellFounded_reindex rows loops).mp accepted.demandWellFounded

/-- Reversion after checked renumbering preserves the defined observation
of the original graph at its original index. -/
theorem returns_iff_observe [DecidableEq Data] (accepted : Automatic.Accepted (g.reindex rows loops))
    (m : Interpretation.{u,v,w} P) (input : Tuple m.Value outer)
    (total : accepted.form.Total m)
    (neg : ∀ b : Bool, m.run accepted.form.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (i : Index l) (value : m.Value result) :
    accepted.revert.Returns m input value ↔
      g.observe m (g.denote m input (demandWellFounded accepted)) i = .cons (some value) .nil := by
  rw [← i.reindex_inverse loops]
  rw [← g.observe_denote_reindex rows loops m input (demandWellFounded accepted)
    accepted.demandWellFounded (i.reindex loops)]
  exact accepted.returns_iff_observe m input total neg (i.reindex loops) value

end Silmaril.SSA.PEG.Simple.Revert.While.Nested.Reindexed
