module

public import Silmaril.Languages.Python.Core.Text.Slice.Defs

public section
namespace Silmaril.Proofs.Languages.Python.Core.Text.Slice

open Silmaril.Languages.Python.Core

theorem normalize_bounds (bounds : SliceBounds) (length : Nat) :
    let slice := bounds.normalize length
    let low : Int := if slice.step < 0 then -1 else 0
    let high : Int := if slice.step < 0 then (length : Int) - 1 else length
    low ≤ slice.start ∧ slice.start ≤ high ∧ low ≤ slice.stop ∧ slice.stop ≤ high := by
  have clipped (index : Option Int) (low high fallback : Int)
      (within : low ≤ fallback ∧ fallback ≤ high) :
      let i := (index.map (SliceBounds.clip length low high)).getD fallback
      low ≤ i ∧ i ≤ high := by
    cases index with
    | none => exact within
    | some value =>
      simp only [Option.map_some, Option.getD_some, SliceBounds.clip]
      omega
  by_cases negative : bounds.step.getD 1 < 0
  · simp only [SliceBounds.normalize, negative, ite_true]
    have start := clipped bounds.start (-1) (length - 1) (length - 1) (by omega)
    exact ⟨start.1, start.2, clipped bounds.stop (-1) (length - 1) (-1) (by omega)⟩
  · simp only [SliceBounds.normalize, negative, ite_false]
    have start := clipped bounds.start 0 length 0 (by omega)
    exact ⟨start.1, start.2, clipped bounds.stop 0 length length (by omega)⟩

end Silmaril.Proofs.Languages.Python.Core.Text.Slice
