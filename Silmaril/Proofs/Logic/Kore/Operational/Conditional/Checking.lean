module

public import Silmaril.Logic.Kore.Operational.Conditional.Defs
import Batteries.Data.List.Lemmas

@[expose] public section
namespace Silmaril.Proofs.Logic.Kore.Operational.Conditional
open Silmaril.Logic.Kore.Operational.Conditional

/-- Successful traversal retains exactly the successfully elaborated declarations. -/
theorem mapM_members {ds : List Silmaril.Logic.Kore.Operational.Declaration} {checked : List (Context × Rule)}
    (h : ds.mapM elaborate = some checked) (pair : Context × Rule) :
    pair ∈ checked ↔ ∃ d ∈ ds, elaborate d = some pair := by
  have aligned : List.Forall₂ (fun d p => elaborate d = some p) ds checked :=
    List.mapM_eq_some_iff_forall₂.mp h
  have filtered : ds.filterMap elaborate = checked := by
    clear h
    induction aligned with
    | nil => rfl
    | @cons d p ds checked hd _ ih =>
      show (d :: ds).filterMap elaborate = p :: checked
      simp only [List.filterMap_cons, hd, ih]
  rw [← filtered, List.mem_filterMap]

end Silmaril.Proofs.Logic.Kore.Operational.Conditional
