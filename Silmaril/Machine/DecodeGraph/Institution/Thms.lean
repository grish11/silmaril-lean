module

public import Silmaril.Machine.DecodeGraph.Institution.Defs

public section

namespace Silmaril.Machine.DecodeGraph.Institution

variable {Context Source Middle Target : Type*}

@[simp] theorem translate_id : translate (Context := Context) (id : Source → Source) = id := rfl

theorem translate_comp (first : Source → Middle) (second : Middle → Target) :
    translate (Context := Context) (second ∘ first) = translate second ∘ translate first := rfl

@[simp] theorem reduct_id (model : Graph Context Source) : reduct id model = model := rfl

theorem reduct_comp (first : Source → Middle) (second : Middle → Target) (model : Graph Context Target) :
    reduct (second ∘ first) model = reduct first (reduct second model) := rfl

/-- The institution satisfaction condition for positive exact-success atoms. -/
theorem satisfaction (f : Source → Target) (model : Graph Context Target) (atom : Atom Context Source) :
    Satisfies model (translate f atom) ↔ Satisfies (reduct f model) atom := Iff.rfl

/-- A successful target instruction with two distinct preimages gives two
successful reduct outcomes at the same query and span. -/
theorem reduct_not_deterministic_of_collision {f : Source → Target} {model : Graph Context Target}
    {input : Context × Bytes} {left right : Source} {span : Nat}
    (different : left ≠ right) (collision : f left = f right) (success : (input, (f left, span)) ∈ model) :
    ¬ Deterministic (reduct f model) := by
  intro unique
  have equal : (left, span) = (right, span) :=
    unique success (show (input, (f right, span)) ∈ model from collision ▸ success)
  exact different (congrArg Prod.fst equal)

end Silmaril.Machine.DecodeGraph.Institution
