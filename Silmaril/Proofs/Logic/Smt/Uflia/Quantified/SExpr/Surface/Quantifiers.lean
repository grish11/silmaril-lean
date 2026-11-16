module

public import Silmaril.Proofs.Logic.Smt.Uflia.Quantified.SExpr.Surface.Adequacy

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Surface
open Silmaril.Logic.Smt.Uflia.SExpr
variable {E : Environment} (M : Model E.signature)

/-- Actual carrier nonemptiness prevents vacuous admission of rejected bodies. -/
theorem carrier_nonempty (s : SortCode String) : Nonempty (M.carriers.value s) := by
  cases s with
  | bool => infer_instance
  | int => infer_instance
  | user u => exact M.carriers.nonempty u

@[simp] theorem denoteLocals_shift {k : Nat} {Γ : Fin k → SortCode String}
    (locals : SExpr.Locals E Γ) (ρ : ∀ i, M.carriers.value (Γ i))
    (sort : SortCode String) (x : M.carriers.value sort) :
    denoteLocals M (Fin.cases x ρ) (locals.map (fun entry =>
      ((entry.1, ⟨entry.2.sort, entry.2.term.weaken sort⟩) : String × SExpr.PackedTerm E _))) =
      denoteLocals M ρ locals := by
  simp [denoteLocals, List.map_map, denote, Function.comp_def]

/-- Quantifier-list correspondence is generalized over all open source locals,
assignments and contexts. No finiteness of any carrier is assumed. -/
theorem quantify_commute (universal : Bool)
    (direct : Locals M → Expr → Option (Value M))
    (typed : ∀ {k : Nat} {Γ : Fin k → SortCode String},
      SExpr.Locals E Γ → Expr → Option (SExpr.PackedTerm E Γ))
    (commutes : ∀ {k : Nat} {Γ : Fin k → SortCode String}
      (locals : SExpr.Locals E Γ) (ρ : ∀ i, M.carriers.value (Γ i)) (e : Expr),
      direct (denoteLocals M ρ locals) e = (typed locals e).map (denote M ρ))
    {k : Nat} {Γ : Fin k → SortCode String} (locals : SExpr.Locals E Γ)
    (ρ : ∀ i, M.carriers.value (Γ i)) (binders : List (String × SortCode String)) (body : Expr) :
    quantify? M universal direct (denoteLocals M ρ locals) binders body =
      (SExpr.quantify? E universal typed locals binders body).map (denote M ρ) := by
  classical
  induction binders generalizing k Γ locals with
  | nil => exact commutes locals ρ body
  | cons binder rest ih =>
    rcases binder with ⟨name, sort⟩
    let shifted : SExpr.Locals E (Fin.cases sort Γ) := locals.map (fun entry =>
      ((entry.1, ⟨entry.2.sort, entry.2.term.weaken sort⟩) : String × SExpr.PackedTerm E _))
    let extended : SExpr.Locals E (Fin.cases sort Γ) := (name, ⟨sort, .var 0⟩) :: shifted
    have localEq (x : M.carriers.value sort) :
        denoteLocals M (Fin.cases x ρ) extended =
          (name, ⟨sort, ⟨x, none⟩⟩) :: denoteLocals M ρ locals := by
      simp only [extended, denoteLocals, List.map_cons]
      congr 1
      exact denoteLocals_shift M locals ρ sort x
    have inner (x : M.carriers.value sort) :
        quantify? M universal direct ((name, ⟨sort, ⟨x, none⟩⟩) :: denoteLocals M ρ locals) rest body =
          (SExpr.quantify? E universal typed extended rest body).map (denote M (Fin.cases x ρ)) := by
      rw [← localEq x]
      exact ih extended (Fin.cases x ρ)
    let : Nonempty (M.carriers.value sort) := carrier_nonempty M sort
    rw [quantify?, SExpr.quantify?]
    simp only [inner]
    cases hd : SExpr.quantify? E universal typed extended rest body with
    | none => simp
    | some packed =>
      rcases packed with ⟨resultSort, term⟩
      cases resultSort <;> cases universal <;>
        simp [denote, Value.expect?, SExpr.PackedTerm.expect?,
          boolean, denoteData, Quantified.eval, SExpr.integerValue?]

end Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Surface
