module

public import Silmaril.Proofs.Logic.Kore.Modules.Fuel.Traversal

@[expose] public section
namespace Silmaril.Proofs.Logic.Kore.Modules.Fuel
open Silmaril.Logic.Kore.Modules

/-- Every recursive call consumes one unit, even for alias arguments and bodies.
Successful finite computation therefore needs no alias acyclicity hypothesis. -/
theorem elaborate_add (scope : Scope) (fuel extra : Nat) :
    ∀ {k : Nat} {Γ : Fin k → String} (vs : List (Checking.Binding scope.signature Γ))
      (s : String) (raw : RawPattern),
    Extends (Checking.elaborate scope fuel vs s raw)
      (Checking.elaborate scope (fuel + extra) vs s raw) := by
  induction fuel with
  | zero => intro k Γ vs s raw typed h; contradiction
  | succ n ih =>
      intro k Γ vs s raw
      show Extends _ _
      cases raw with
      | «variable» name actual =>
          simp only [Nat.succ_add, Checking.elaborate]
          exact extends_refl _
      | top actual =>
          simp only [Nat.succ_add, Checking.elaborate]
          exact extends_refl _
      | bottom actual =>
          simp only [Nat.succ_add, Checking.elaborate]
          exact extends_refl _
      | not actual body =>
          simp only [Nat.succ_add, Checking.elaborate]
          split
          · exact extends_refl _
          · apply extends_bind (ih vs s body); intro p; exact extends_refl _
      | and actual left right | or actual left right
      | implies actual left right | iff actual left right =>
          simp only [Nat.succ_add, Checking.elaborate]
          split
          · exact extends_refl _
          · apply extends_bind (ih vs s left); intro p
            apply extends_bind (ih vs s right); intro q
            exact extends_refl _
      | «exists» actual name b body | «forall» actual name b body =>
          simp only [Nat.succ_add, Checking.elaborate]
          split
          · exact extends_refl _
          · apply extends_bind (ih (Checking.bind name b vs) s body)
            intro p; exact extends_refl _
      | app name args =>
          show Extends _ _
          simp only [Nat.succ_add, Checking.elaborate]
          split
          · split
            · split
              · apply extends_bind (extends_collect _ _ (fun i => ih vs _ _))
                intro ps; exact extends_refl _
              · exact extends_refl _
            · exact extends_refl _
          · apply extends_bind (extends_refl _)
            intro a
            show Extends _ _
            split
            · exact extends_refl _
            · apply extends_bind (extends_mapM _ _ _ ?_)
              · intro ps; exact ih ps s a.declaration.body
              · intro pair
                rcases pair with ⟨formal, arg⟩
                apply extends_bind (ih vs formal.2 arg)
                intro p; exact extends_refl _
end Silmaril.Proofs.Logic.Kore.Modules.Fuel
