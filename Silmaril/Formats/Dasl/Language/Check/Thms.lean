module

public import Silmaril.Formats.Dasl.Language.Check.Defs
public import Silmaril.Formats.Dasl.Language.Thms
import Silmaril.Proofs.Formats.Dasl.LanguageCheck

public section

namespace Silmaril.Formats.Dasl.Check

open Silmaril.Semantics.Naming

variable {Name : Type} {store extended : Store Name} {queries : Queries store}
variable {accepts : Value → Bool} {language : Value → Prop} {fuel : Nat} {root : Name}

theorem accepted_witness (hit : run queries accepts fuel root = .accepted) :
    ∃ target, FullNames store root target ∧ accepts target.erase = true :=
  Proofs.Formats.Dasl.LanguageCheck.accepted_witness hit

theorem rejected_witness (hit : run queries accepts fuel root = .rejected) :
    ∃ target, FullNames store root target ∧ accepts target.erase = false :=
  Proofs.Formats.Dasl.LanguageCheck.rejected_witness hit

/-- Acceptance needs sound queries, not uniqueness or completeness of names. -/
theorem accepted (reflects : ∀ value, accepts value = true ↔ language value)
    (hit : run queries accepts fuel root = .accepted) : root ∈ Recognized store language := by
  obtain ⟨target, full, passes⟩ := accepted_witness hit
  exact ⟨target.erase, ⟨target, full, rfl⟩, (reflects target.erase).mp passes⟩

theorem accepted_in_extension (incl : store.Subset extended)
    (reflects : ∀ value, accepts value = true ↔ language value)
    (hit : run queries accepts fuel root = .accepted) : root ∈ Recognized extended language :=
  recognized_mono incl language (accepted reflects hit)

/-- Rejection requires an actually resolved object and binding in the reference extension.
The full witness is retained, so all other full expansions must equal it. -/
theorem rejected_in_extension (incl : store.Subset extended) (bound : extended.Binding)
    (reflects : ∀ value, accepts value = true ↔ language value)
    (hit : run queries accepts fuel root = .rejected) : root ∉ Recognized extended language :=
  Proofs.Formats.Dasl.LanguageCheck.rejected_in_extension incl bound reflects hit

end Silmaril.Formats.Dasl.Check
