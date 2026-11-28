module

public import Silmaril.SSA.Isotope.LetSeq.StraightLine.Structural.Categorical.Defs

public section

namespace Silmaril.Isotope.LetSeq.StraightLine.Structural.Categorical

open CategoryTheory CategoryTheory.Limits
open Silmaril.Semantics.NondeterministicTrace
open scoped MonoidalCategory Structural

variable {α Φ : Type} [Signature α Φ]

set_option backward.isDefEq.respectTransparency false

/-- One event yields a distinct computation to the same unit object. -/
theorem traceUnit_not_terminal_proof (event : Event (α := α) (Φ := Φ)) :
    ¬ Nonempty (IsTerminal (𝟙_ (Kleisli (ofTypeMonad (Trace α Φ))))) := by
  intro ⟨terminal⟩
  let U := 𝟙_ (Kleisli (ofTypeMonad (Trace α Φ)))
  let singleton : Trace α Φ PUnit := Finite.ofOutcomes {(PUnit.unit, FreeMonoid.of event)}
  let record : U ⟶ U := Kleisli.Hom.mk (TypeCat.ofHom (fun _ => singleton))
  have equal := terminal.hom_ext record (𝟙 U)
  have observe := congrArg (fun k : U ⟶ U => k.of PUnit.unit) equal
  have member : (PUnit.unit, FreeMonoid.of event) ∈ (record.of PUnit.unit).outcomes := rfl
  rw [observe] at member
  change (PUnit.unit, FreeMonoid.of event) ∈
    ({(PUnit.unit, (1 : Log α Φ))} : Set (PUnit × Log α Φ)) at member
  have log : FreeMonoid.of event = 1 := congrArg Prod.snd (Set.mem_singleton_iff.mp member)
  have word : [event] = [] := congrArg FreeMonoid.toList log
  cases word

end Silmaril.Isotope.LetSeq.StraightLine.Structural.Categorical
