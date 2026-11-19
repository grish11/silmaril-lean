module

public import Silmaril.Semantics.Function.Defs

public section
namespace Silmaril.Semantics.Function.Proofs
universe u

theorem reachable_iff_mem {α : Type u} {g : Graph.RelGraph α} {root : α} {seen : Set α}
    (cert : ReachCertificate g root seen) (dest : α) :
    Relation.ReflTransGen g.edge root dest ↔ dest ∈ seen := by
  refine ⟨?_, fun mem => cert.witnessed mem⟩
  intro path
  induction path with
  | refl => exact cert.root_mem
  | tail _ edge ih => exact cert.step_closed ih edge

theorem topify_covers {sig : Signature.{u}} (analysis : Analysis sig) : MayCover analysis.may analysis.topify.may := by
  rintro ⟨site, mode, callee⟩ witness
  cases mode with
  | direct => exact witness
  | indirect =>
    obtain ⟨bound, recorded, _⟩ := witness
    exact ⟨none, ⟨rfl, bound, recorded⟩, trivial⟩

end Silmaril.Semantics.Function.Proofs
