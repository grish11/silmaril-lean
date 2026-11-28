module

public import Silmaril.SSA.PEG.Simple.Revert.While.Nested.Automatic.Defs
public import Silmaril.SSA.PEG.Simple.Revert.While.Nested.Thms

public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Nested.Automatic

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {outer : List (Ty Data)} {result : Ty Data} {n : Nat}
variable {g : Graph P outer [result] n n}

/-- The recovered form recompiles to the original input graph. -/
theorem Accepted.compile_eq [DecidableEq Data] (a : Accepted g) :
    (a.size.symm ▸ a.form.compile : Graph P outer [result] n n) = g := by
  obtain ⟨inner, form, size, cert⟩ := a
  subst n
  exact cert.compile_eq

theorem Accepted.demandWellFounded [DecidableEq Data] (a : Accepted g) :
    WellFounded g.Demand := by
  obtain ⟨inner, form, size, cert⟩ := a
  subst n
  exact cert.demandWellFounded

/-- Each successful inference inherits the checked two-level
correspondence, with the same totality and negation premises. -/
theorem Accepted.returns_iff_observe [DecidableEq Data] (a : Accepted g)
    (m : Interpretation.{u,v,w} P) (input : Tuple m.Value outer)
    (total : a.form.Total m)
    (neg : ∀ b : Bool, m.run a.form.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (i : Index n) (value : m.Value result) :
    a.revert.Returns m input value ↔
      g.observe m (g.denote m input a.demandWellFounded) i = .cons (some value) .nil := by
  obtain ⟨inner, form, size, cert⟩ := a
  subst n
  exact cert.returns_iff_observe m input total neg i value

end Silmaril.SSA.PEG.Simple.Revert.While.Nested.Automatic
