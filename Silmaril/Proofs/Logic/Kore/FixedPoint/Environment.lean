module

public import Silmaril.Logic.Kore.FixedPoint.Semantics.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Proofs.Logic.Kore.FixedPoint
open Silmaril.Logic.Kore.FixedPoint Silmaril.Logic.Kore.FixedPoint.Semantics
variable {scope : Silmaril.Logic.Kore.Modules.Scope}
variable (M : Silmaril.Logic.Matching.FixedPoint.Model scope.signature)

theorem lookup_interpret (names : Names) (v : ∀ i, Set (M.carrier (context names i)))
    (name s : String) :
    lookupValue M (interpret M names v) name s =
      ((lookup names name).bind fun i =>
        if h : context names i = s then some (h ▸ v i) else none) := by
  induction names with
  | nil => rfl
  | cons entry names ih =>
      rcases entry with ⟨n, b⟩
      simp only [interpret, lookupValue, lookup]
      split
      · simp only [Option.bind_some, context, Fin.cases_zero]
        rfl
      · refine (ih (fun i => v i.succ)).trans ?_
        cases found : lookup names name with
        | none => rfl
        | some i =>
            simp only [Option.map_some, Option.bind_some]
            by_cases same : context names i = s
            · cases same
              rfl
            · simp only [context, Fin.cases_succ, same, ↓reduceDIte]

theorem collect_some {n : Nat} {α : Fin n → Type} (f : ∀ i, Option (α i))
    (xs : ∀ i, α i) (h : Silmaril.Logic.Kore.Modules.Checking.collect f = some xs) :
    ∀ i, f i = some (xs i) := by
  induction n with
  | zero => exact fun i => i.elim0
  | succ n ih =>
      simp only [Silmaril.Logic.Kore.Modules.Checking.collect] at h
      obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨tail, ht, h⟩ := Option.bind_eq_some_iff.mp h
      cases Option.some.inj h
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hx
      · exact ih _ _ ht j

theorem collect_pure {n : Nat} {α : Fin n → Type} (xs : ∀ i, α i) :
    Silmaril.Logic.Kore.Modules.Checking.collect (fun i => some (xs i)) = some xs := by
  induction n with
  | zero =>
      change some (fun i => Fin.elim0 i) = some xs
      congr 1
      funext i
      exact i.elim0
  | succ n ih =>
      simp only [Silmaril.Logic.Kore.Modules.Checking.collect, ih]
      change some (Fin.cases (xs 0) (fun i => xs i.succ)) = some xs
      congr 1
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
end Silmaril.Proofs.Logic.Kore.FixedPoint
