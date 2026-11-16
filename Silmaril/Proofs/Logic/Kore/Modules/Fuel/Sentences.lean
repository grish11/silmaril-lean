module

public import Silmaril.Proofs.Logic.Kore.Modules.Fuel.Elaboration

@[expose] public section
namespace Silmaril.Proofs.Logic.Kore.Modules.Fuel
open Silmaril.Logic.Kore.Modules

theorem sentence_add (scope : Scope) (fuel extra : Nat) (raw : RawPattern) :
    Extends (Checking.sentence scope fuel raw) (Checking.sentence scope (fuel + extra) raw) := by
  unfold Checking.sentence
  apply extends_bind (freeVariables_add fuel extra [] raw)
  intro names
  dsimp only
  split
  · exact extends_refl _
  · apply extends_bind (extends_refl _)
    intro s
    apply extends_bind (elaborate_add scope fuel extra _ s raw)
    intro body
    exact extends_refl _
end Silmaril.Proofs.Logic.Kore.Modules.Fuel
