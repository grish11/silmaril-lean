module

public import Silmaril.SSA.PEG.Simple.Revert.While.Nested.Reindexed.Automatic.Defs
public import Silmaril.SSA.PEG.Simple.Revert.While.Nested.Reindexed.Thms

public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Nested.Reindexed.Automatic

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {outer : List (Ty Data)} {result : Ty Data} {n l : Nat}
variable {g : Graph P outer [result] n l}

theorem Accepted.graph_eq [DecidableEq Data] (a : Accepted g) :
    a.form.compile.reindex a.numbering.rows a.numbering.loops = g :=
  a.numbering.checked.graph_eq

theorem Accepted.demandWellFounded [DecidableEq Data] (a : Accepted g) :
    WellFounded g.Demand :=
  a.numbering.checked.demandWellFounded_iff.mpr
    (Structured.translate_demandWellFounded a.form.source a.form.negate)

/-- A graph-only accepted inference retains the checked return
correspondence at the input graph's original coordinates. -/
theorem Accepted.returns_iff_observe [DecidableEq Data] (a : Accepted g)
    (m : Interpretation.{u,v,w} P) (input : Tuple m.Value outer) (total : a.form.Total m)
    (neg : ∀ b : Bool, m.run a.form.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (i : Index l) (value : m.Value result) :
    a.revert.Returns m input value ↔
      g.observe m (g.denote m input a.demandWellFounded) i = .cons (some value) .nil := by
  let canonical : Certificate a.form a.form.compile := ⟨rfl⟩
  rw [a.numbering.checked.observe_denote m input canonical.demandWellFounded a.demandWellFounded i]
  exact canonical.returns_iff_observe m input total neg (i.reindex a.numbering.loops.symm) value

end Silmaril.SSA.PEG.Simple.Revert.While.Nested.Reindexed.Automatic
