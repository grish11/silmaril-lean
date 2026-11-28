module

import Silmaril.Machine.MulticoreVM.PlacedInstitution.Thms
import Silmaril.Semantics.ConcurrentTrace.Thms

namespace Silmaril.Proofs.Machine.MulticoreVM.PlacedInstitution

open CategoryTheory
open Silmaril.Machine.MulticoreVM
open Silmaril.Machine.MulticoreVM.Institution
open Silmaril.Machine.MulticoreVM.Placed (TaggedLetter)
open Silmaril.Semantics.ConcurrentTrace (Trace ofWord swap swap_eq_iff)

private abbrev source : Sig := ⟨Bool, Unit, Bool⟩

-- The empty successful schedule contributes a class through both direct-image routes.
example {Core Thread Choice : Type} (instruction : Placed.Instruction Unit Bool Core Thread Choice Bool)
    (initial : Placed.Config Unit Bool Core Thread) :
    (1 : source.ConcurrentTrace) ∈
      (namedToConcurrent.app source) '' ((placedToNamed.app source) '' ofPlaced (A := source) instruction initial) := by
  rw [← placed_concurrent_image]
  exact (mem_placed_concurrent_iff (A := source) instruction initial 1).mpr
    ⟨[], [], initial, .nil initial, rfl⟩

-- Swapping independent threads can change the order of their events on a shared core.
example : ¬ ∃ project : source.ConcurrentTrace → Trace source.CoreId (Option source.Event),
    ∀ word : source.PlacedWord,
      project ((placedToNamed ≫ namedToConcurrent).app source word) = ofWord (placedToCore.app source word) := by
  rintro ⟨project, agrees⟩
  let first : TaggedLetter Unit Bool Bool := .event () false false
  let second : TaggedLetter Unit Bool Bool := .event () true true
  have same : (placedToNamed ≫ namedToConcurrent).app source [first, second] =
      (placedToNamed ≫ namedToConcurrent).app source [second, first] := swap (.events (by decide))
  have projected :=
    (agrees [first, second]).symm.trans ((congrArg project same).trans (agrees [second, first]))
  rcases (swap_eq_iff first.dropThread second.dropThread).mp projected with equal | independent
  · dsimp [first, second, TaggedLetter.dropThread] at equal
    cases equal
  · dsimp [first, second, TaggedLetter.dropThread] at independent
    cases independent with
    | events distinct => exact distinct rfl

end Silmaril.Proofs.Machine.MulticoreVM.PlacedInstitution
