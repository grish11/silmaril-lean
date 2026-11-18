module

/-! # Translation relations between artifacts -/

@[expose] public section

namespace Silmaril.Machine.Translation

/-- Which source and target artifacts are related, independently of any
execution model, checker, or refinement claim. -/
abbrev Relation.{u, v} (Src : Type u) (Tgt : Type v) := Src → Tgt → Prop

end Silmaril.Machine.Translation
