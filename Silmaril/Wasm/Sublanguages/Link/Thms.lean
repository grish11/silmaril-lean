module

public import Silmaril.Wasm.Sublanguages.Link.Defs
public import Silmaril.Wasm.Link.Recipe
import Silmaril.Wasm.Binaryen.Exe.CoreInputCheckSound

public section

namespace Silmaril.Wasm.Sublanguages.Readback

open Binaryen.Exe

variable {language : Language} {reader : Readback language}

theorem exact?_sound {coreMod : Wasm.Module} {mod : language.Module}
    (success : reader.exact? coreMod = some mod) : language.toModule mod = coreMod := by
  obtain ⟨candidate, _, compared⟩ := Option.bind_eq_some_iff.mp success
  split at compared <;> cases compared
  exact canonicalModuleEq_sound (by assumption)

theorem exact?_complete {mod : language.Module} {bytes : List UInt8}
    (encodable : encodeModule? (language.toModule mod) = .ok bytes) :
    reader.exact? (language.toModule mod) = some mod := by
  simp [exact?, reader.onImage, canonicalModuleEq_refl_of_encoded encodable]

/-- The square uses exactly the real Core link output, not an equivalent or
normalized replacement. -/
theorem link?_square {namespaceName : String} {provider consumer linked : language.Module}
    (success : reader.link? namespaceName provider consumer = some linked) :
    Link.GC.link? namespaceName (language.toModule provider) (language.toModule consumer) =
      some (language.toModule linked) := by
  obtain ⟨image, computed, accepted⟩ := Option.bind_eq_some_iff.mp success
  rw [exact?_sound accepted]; exact computed

theorem link?_complete {namespaceName : String} {provider consumer linked : language.Module} {bytes : List UInt8}
    (square : Link.GC.link? namespaceName (language.toModule provider) (language.toModule consumer) =
      some (language.toModule linked))
    (encodable : encodeModule? (language.toModule linked) = .ok bytes) :
    reader.link? namespaceName provider consumer = some linked := by
  simpa [link?, square] using (exact?_complete (reader := reader) encodable)

/-- On a successful encodable source result, linking commutes with syntax inclusion. -/
theorem link?_natural {target : Language} (arrow : Inclusion language target) (targetReader : Readback target)
    {namespaceName : String} {provider consumer linked : language.Module} {bytes : List UInt8}
    (success : reader.link? namespaceName provider consumer = some linked)
    (encodable : encodeModule? (language.toModule linked) = .ok bytes) :
    targetReader.link? namespaceName (arrow.mod provider) (arrow.mod consumer) = some (arrow.mod linked) := by
  apply targetReader.link?_complete
  · simpa only [arrow.mod_comm] using link?_square success
  · simpa only [arrow.mod_comm] using encodable

theorem link?_valid {namespaceName : String} {provider consumer linked : language.Module}
    (success : reader.link? namespaceName provider consumer = some linked) :
    Validation.ModuleValid (language.toModule linked) := Link.GC.link?_valid (link?_square success)

theorem link?_intrinsic {namespaceName : String} {provider consumer linked : language.Module}
    (success : reader.link? namespaceName provider consumer = some linked) :
    ∃ iface, ∃ typed : Profiles.TypedModule Profiles.Wasm3 iface,
      Profiles.HasIntrinsic.eraseModule typed = language.toModule linked := by
  obtain ⟨iface, checked⟩ := link?_valid success
  exact ⟨iface, Profiles.HasIntrinsic.moduleLift checked⟩

/-- The existing recipe supplies actual validated interfaces, import
resolution and relocation for the semantic linking theorems. -/
theorem link?_recipe {namespaceName : String} {provider consumer linked : language.Module}
    (success : reader.link? namespaceName provider consumer = some linked) :
    Nonempty (Link.GC.Recipe.Assembly namespaceName
      (language.toModule provider) (language.toModule consumer) (language.toModule linked)) :=
  Link.GC.link?_recipe (link?_square success)

end Silmaril.Wasm.Sublanguages.Readback
