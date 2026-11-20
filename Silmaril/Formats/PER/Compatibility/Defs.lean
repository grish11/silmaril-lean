module
public import Silmaril.Formats.PER.Thms

@[expose] public section
namespace Silmaril.Formats.PER
variable {α : Type}

def WeaklyCompatible (R E : PER α) : Prop :=
  R ≤ E ∧ ∀ ⦃left right⦄, E.rel left right → R.rel left right ∨ ¬ R.Dom left ∨ ¬ R.Dom right

def StrictlyCompatible (R E : PER α) : Prop :=
  R ≤ E ∧ ∀ ⦃left right⦄, E.rel left right → R.rel left right ∨ (¬ R.Dom left ∧ ¬ R.Dom right)

/-- View an ordinary equivalence as a PER with total support. -/
def ofSetoid (E : Setoid α) : PER α :=
  ⟨E.r, ⟨fun _ _ h => E.iseqv.symm h, fun _ _ _ h k => E.iseqv.trans h k⟩⟩

def toSetoid (R : PER α) (total : ∀ x, R.Dom x) : Setoid α where
  r := R.rel
  iseqv := ⟨total, fun h => R.laws.symm h, fun h k => R.laws.trans h k⟩

/-- Keep the old classes; add one singleton per invalid element. -/
def singletonCompletion (R : PER α) : PER α where
  rel left right := R.rel left right ∨ left = right
  laws.symm := fun _ _ h => h.elim (fun hr => Or.inl (R.laws.symm hr)) (fun he => Or.inr he.symm)
  laws.trans := by
    rintro left middle right (h | rfl) (k | rfl)
    · exact Or.inl (R.laws.trans h k)
    all_goals first | exact Or.inl h | exact Or.inl k | exact Or.inr rfl

/-- Keep the old classes; add one class containing all invalid elements. -/
def invalidCompletion (R : PER α) : PER α where
  rel left right := R.rel left right ∨ (¬ R.Dom left ∧ ¬ R.Dom right)
  laws.symm := fun _ _ h => h.elim (fun hr => Or.inl (R.laws.symm hr)) (fun hi => Or.inr ⟨hi.2, hi.1⟩)
  laws.trans := by
    rintro left middle right (h | h) (k | k)
    · exact Or.inl (R.laws.trans h k)
    · exact (k.1 (R.dom_right h)).elim
    · exact (h.2 (R.dom_left k)).elim
    · exact Or.inr ⟨h.1, k.2⟩

end Silmaril.Formats.PER
