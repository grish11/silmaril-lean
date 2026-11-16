module

public import Silmaril.Logic.Kore.Modules.Checking.Defs
public import Silmaril.Proofs.Logic.Kore.Modules.Renaming

@[expose] public section
namespace Silmaril.Logic.Kore.Modules.Checking
open Algebraic.ManySorted (Signature)

/-- Weakening an actual alias argument under a fresh binder preserves its
meaning for every value of that binder; names cannot capture the argument. -/
theorem denote_weaken {A : Signature String} (M : Matching.FirstOrder.Model A)
    {k : Nat} {Γ : Fin k → String} {s : String} (p : FirstOrder.Pattern A Γ s)
    (b : String) (v : (i : Fin k) → M.carrier (Γ i)) (x : M.carrier b) :
    FirstOrder.denote A M (Γ := Fin.cases b Γ) (Fin.cases x v)
      (rename (Γ := Γ) (Δ := Fin.cases b Γ) (fun i => ⟨i.succ, rfl⟩) p) =
        FirstOrder.denote A M v p :=
  Silmaril.Proofs.Logic.Kore.Modules.denote_rename M p (Δ := Fin.cases b Γ) _ v (Fin.cases x v) (fun _ => HEq.rfl)
end Silmaril.Logic.Kore.Modules.Checking
