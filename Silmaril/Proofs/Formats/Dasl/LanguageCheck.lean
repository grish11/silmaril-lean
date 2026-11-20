module

public import Silmaril.Formats.Dasl.Language.Check.Defs
public import Silmaril.Formats.Dasl.Language.Thms
public import Silmaril.Formats.Dasl.Resolve.Thms

public section

namespace Silmaril.Proofs.Formats.Dasl.LanguageCheck

open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.Check Silmaril.Semantics.Naming

variable {Name : Type} {store extended : Store Name} {queries : Queries store}
variable {accepts : Value → Bool} {language : Value → Prop} {fuel : Nat} {root : Name}

theorem accepted_witness (hit : run queries accepts fuel root = .accepted) :
    ∃ target, FullNames store root target ∧ accepts target.erase = true := by
  cases result : resolve queries fuel root with
  | error fault => simp [run, result, classify] at hit
  | ok witness =>
    obtain ⟨target, full⟩ := witness
    have passes : accepts target.erase = true := by simpa [run, result, classify] using hit
    exact ⟨target, full, passes⟩

theorem rejected_witness (hit : run queries accepts fuel root = .rejected) :
    ∃ target, FullNames store root target ∧ accepts target.erase = false := by
  cases result : resolve queries fuel root with
  | error fault => simp [run, result, classify] at hit
  | ok witness =>
    obtain ⟨target, full⟩ := witness
    have fails : accepts target.erase = false := by simpa [run, result, classify] using hit
    exact ⟨target, full, fails⟩

theorem rejected_in_extension (incl : store.Subset extended) (bound : extended.Binding)
    (reflects : ∀ value, accepts value = true ↔ language value)
    (hit : run queries accepts fuel root = .rejected) : root ∉ Recognized extended language := by
  obtain ⟨target, full, fails⟩ := rejected_witness hit
  rintro ⟨value, ⟨other, expands, rfl⟩, member⟩
  have same := fullNames_binding bound (full.mono incl) expands
  exact Bool.noConfusion (fails.symm.trans (same ▸ (reflects other.erase).mpr member))

end Silmaril.Proofs.Formats.Dasl.LanguageCheck
