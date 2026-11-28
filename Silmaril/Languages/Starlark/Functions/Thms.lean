module

public import Silmaril.Languages.Starlark.Functions.Denotation.Defs
public import Silmaril.Languages.Starlark.Functions.Operational.Defs
import Silmaril.Proofs.Languages.Starlark.Functions.Eval

public section

namespace Silmaril.Languages.Starlark.Functions

open Lists
open Lists.Iteration (Flow Suite denoteSuite)

theorem mem_withoutDeclaration {available : List DeclarationId} {id other : DeclarationId} :
    other ∈ withoutDeclaration available id ↔ other ∈ available ∧ other ≠ id := by
  simp [withoutDeclaration]

theorem withoutDeclaration_length_lt {available : List DeclarationId} {id : DeclarationId}
    (permitted : id ∈ available) : (withoutDeclaration available id).length < available.length :=
  List.length_filter_lt_length_iff_exists.mpr ⟨id, permitted, by simp⟩

/-- Each permitted call enters a strictly smaller declaration set,
even if the given list contains repeated declaration IDs. -/
theorem withoutDeclaration_induction (P : List DeclarationId → Prop)
    (step : ∀ available, (∀ id ∈ available, P (withoutDeclaration available id)) → P available)
    (available : List DeclarationId) : P available :=
  step available fun id _ => withoutDeclaration_induction P step (withoutDeclaration available id)
termination_by available.length
decreasing_by exact withoutDeclaration_length_lt ‹id ∈ available›

/-- Lifting a collection suite gives precisely its existing total denotation. -/
theorem denote_total (program : Program) (available : List DeclarationId) (suite : Suite 0)
    (state : State) : denoteBody program available (.total suite) state = denoteSuite suite state := by
  rw [denoteBody]

/-- Exact adequacy for the strict core, including native expression positions,
iterator cleanup, errors and the post-call store. -/
theorem exec_iff_denoteBody (program : Program) (available : List DeclarationId) (body : Body)
    (state : State) (out : Outcome Flow) :
    Exec program available state body out ↔ denoteBody program available body state = out :=
  ⟨Proofs.Languages.Starlark.Functions.denote_eq_of_exec,
    fun h => h ▸ Proofs.Languages.Starlark.Functions.exec_denote program available body state⟩

end Silmaril.Languages.Starlark.Functions
