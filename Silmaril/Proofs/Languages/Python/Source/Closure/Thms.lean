module

public import Silmaril.Languages.Python.Source.Closure.Defs

public section
namespace Silmaril.Proofs.Languages.Python.Source.Closure

open Silmaril.Languages.Python.Source
open Silmaril.Languages.Python.Source.Closure

theorem slot_iff (parent : Scope) (capture : Capture) :
    (Slot.find? parent capture).isSome ↔ Available parent capture := by
  by_cases owner : capture.origin = parent.context.path <;>
    simp [Slot.find?, Available, owner, List.any_eq_true]

theorem layout_iff (parent : Scope) (captures : List Capture) :
    (layout? parent captures).isSome ↔ ∀ capture ∈ captures, Available parent capture := by
  induction captures with
  | nil => simp [layout?]
  | cons capture rest tail =>
    have head := slot_iff parent capture
    cases selected : Slot.find? parent capture with
    | none =>
      simp [selected] at head
      simp [layout?, selected, head]
    | some slot =>
      simp [selected] at head
      cases built : layout? parent rest with
      | none =>
        simp [built] at tail
        simp [layout?, selected, built, head, tail]
      | some layout =>
        simp [built] at tail
        simpa [layout?, selected, built, head] using tail

end Silmaril.Proofs.Languages.Python.Source.Closure
