module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Capture.Carry.Defs

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Capture.Carry

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat.Capture.Carry
open Silmaril.Isotope.LambdaSSA (FiniteCFG Flat)
open Silmaril.Isotope.LetCase.LocallyNameless (Tm HasType)
open Silmaril.Isotope.SSA.FiniteSum (append append_left append_right)

universe u v

variable {τ : Type u} [TypeFormers τ] {F : Type v} [HasTy F τ]
  {blocks exits m k : Nat} {R : Fin blocks → τ} {D : Fin exits → τ}
  {β : BoundCtx τ m} {γ : BoundCtx τ k} {t : Flat F (blocks + exits) m}

/-- The row decoder installs an exact copy of the selected entry field. -/
private def decodedRenaming (β : BoundCtx τ m) (slot : Fin m) (A : τ) :
    BoundCtx.Renaming (β.snoc A)
      (((β.snoc (product A (β.get slot))).snoc A).snoc (β.get slot)) where
  toFun := decodedIndex slot
  typed := Fin.cases rfl fun i => by
    by_cases same : i = slot
    · subst i
      simp only [decodedIndex, Fin.cases_succ, ↓reduceIte]
      rfl
    · simp only [decodedIndex, Fin.cases_succ, same, ↓reduceIte]
      rfl

private theorem body_hasType (typed : t.HasType (append R D) β) {A : τ}
    (rename : BoundCtx.Renaming β γ) (slot : Fin k) (capture : γ.get slot = A) :
    (body t rename.toFun slot).HasType (append (fun i => product (R i) A) D) γ := by
  induction typed generalizing k with
  | @br m β i a typed =>
    revert a typed
    refine Fin.addCases (fun j typed => ?_) (fun j typed => ?_) i
    · rw [append_left] at typed
      simp only [body, Fin.addCases_left]
      apply Flat.HasType.br
      rw [append_left]
      exact .pair (typed.rename rename) (capture ▸ .bv)
    · rw [append_right] at typed
      simp only [body, Fin.addCases_right]
      apply Flat.HasType.br
      rw [append_right]
      exact typed.rename rename
  | let₁ a _ ih => exact .let₁ (a.rename rename) (ih (rename.up _) slot.succ capture)
  | let₂ a _ ih => exact .let₂ (a.rename rename) (ih ((rename.up _).up _) slot.succ.succ capture)
  | case a _ _ l r =>
    exact .case (a.rename rename) (l (rename.up _) slot.succ capture) (r (rename.up _) slot.succ capture)

theorem graph_hasType {g : FiniteCFG F blocks exits m} (typed : g.HasType β R D) (slot : Fin m) :
    (graph g slot).HasType β (packetTypes R β slot) D :=
  ⟨body_hasType typed.entry (.id β) slot rfl, fun i =>
    .let₂ .bv (body_hasType (typed.block i) (decodedRenaming β slot (R i)) 0 rfl)⟩

theorem graphList_hasType {g : FiniteCFG F blocks exits m} (typed : g.HasType β R D)
    (slots : List (Fin m)) : (graphList g slots).HasType β (packetTypesList R β slots) D := by
  induction slots generalizing g R with
  | nil => exact typed
  | cons slot rest ih => exact ih (graph_hasType typed slot)

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Capture.Carry
