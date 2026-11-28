module

public import Silmaril.Languages.Python.Core.Text.Defs

/-! # Slice exact Python code points -/

@[expose] public section
namespace Silmaril.Languages.Python.Core

structure SliceBounds where
  start : Option Int
  stop : Option Int
  step : Option Int
  deriving DecidableEq, Repr

structure NormalizedSlice where
  start : Int
  stop : Int
  step : Int
  deriving DecidableEq, Repr

def SliceBounds.clip (length : Nat) (low high index : Int) : Int :=
  max low (min high (if index < 0 then index + length else index))

/-- Omitted negative-step stop uses -1 directly. An explicit -1 is first
translated relative to the length, just like any other negative bound. -/
def SliceBounds.normalize (bounds : SliceBounds) (length : Nat) : NormalizedSlice :=
  let step := bounds.step.getD 1
  let low : Int := if step < 0 then -1 else 0
  let high : Int := if step < 0 then (length : Int) - 1 else length
  let clip := SliceBounds.clip length low high
  ⟨(bounds.start.map clip).getD (if step < 0 then high else low),
    (bounds.stop.map clip).getD (if step < 0 then low else high), step⟩

def NormalizedSlice.selects (slice : NormalizedSlice) (index : Nat) : Bool :=
  let i : Int := index
  if slice.step < 0 then
    decide (slice.stop < i ∧ i ≤ slice.start ∧ (slice.start - i) % (-slice.step) = 0)
  else
    decide (slice.start ≤ i ∧ i < slice.stop ∧ (i - slice.start) % slice.step = 0)

/-- Enumerate the finite in-bounds indices in traversal order. The stride
is tested arithmetically, so large clipped bounds never enlarge the scan. -/
def NormalizedSlice.indices (slice : NormalizedSlice) (length : Nat) : List (Fin length) :=
  let indices := List.finRange length
  let ordered := if slice.step < 0 then indices.reverse else indices
  ordered.filter fun index => slice.selects index.val

def Text.slice? (value : Text) (bounds : SliceBounds) : Option Text :=
  let slice := bounds.normalize value.points.length
  if slice.step = 0 then none
  else
    let points := value.points.toArray
    let atIndex (index : Fin value.points.length) := points[index.val]'(by simp [points])
    some ⟨(slice.indices value.points.length).map atIndex, by
      simp only [List.all_map, List.all_eq_true, Function.comp_apply]
      intro index _
      have checked := List.all_eq_true.mp value.valid value.points[index.val] (List.getElem_mem index.isLt)
      simpa [atIndex, points] using checked⟩

end Silmaril.Languages.Python.Core
