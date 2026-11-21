module
public import Silmaril.Formats.PER.Thms

@[expose] public section
namespace Silmaril.Formats.PER
variable {α : Type}

/-- At most one selected element per class. Invalid selections are ignored. -/
def NormalForm (R : PER α) (selected : α → Prop) : Prop :=
  ∀ ⦃left right⦄, selected left → selected right → R.rel left right → left = right

def SupportedNormalForm (R : PER α) (selected : α → Prop) : Prop :=
  (∀ ⦃x⦄, selected x → R.Dom x) ∧ R.NormalForm selected

def Covers (R : PER α) (selected : α → Prop) : Prop :=
  ∀ x, R.Dom x → ∃ y, selected y ∧ R.rel x y

/-- At most one `S` class of selected representatives per `R` class. This also
requires `S`-support for selected `R`-valid values, by taking `left = right`.
If the `S` classes themselves must refine the `R` classes, require `S ≤ R`. -/
def RelativeNormalForm (R S : PER α) (selected : α → Prop) : Prop :=
  ∀ ⦃left right⦄, selected left → selected right → R.rel left right → S.rel left right

/-- A PER may be discrete on its support without being total. -/
def DiscreteOnSupport (R : PER α) : Prop := ∀ ⦃left right⦄, R.rel left right → left = right

end Silmaril.Formats.PER
