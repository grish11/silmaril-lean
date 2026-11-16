module

public import Silmaril.Wasi.Component.Accept.Bounds.Thms
public import Silmaril.Wasi.Component.Accept.Examples

/-! # Length bounds of component acceptors need assumptions: examples

The world models impose no length bound. The specification component for the language of
*all* byte strings accepts an infinite language, so it satisfies neither `ListLiftChecked`
nor a `CanonLowerAccept` correspondence with any core module.
-/

@[expose] public section

namespace Silmaril.Wasi.Accept.Examples

open Silmaril.Formats.Accept Silmaril.Wasi Silmaril.Wasi.Accept

/-- The component accepting every byte string accepts an infinite language. -/
theorem bytesLang_univ_infinite (run : FnName) :
    (bytesLang (importAcceptor (⊤ : ByteLang) run) : Set (List UInt8)).Infinite := by
  rw [bytesLang_importAcceptor]
  exact Set.infinite_univ

/-- So no limits check it. -/
theorem not_listLiftChecked_univ (lim : Silmaril.Wasm.Component.Limits) (run : FnName) :
    ¬ ListLiftChecked lim (importAcceptor (⊤ : ByteLang) run) acceptFn :=
  fun h => bytesLang_univ_infinite run (bytesLang_finite_of_listLiftChecked h)

/-- A finite language within the specification's limits is checked by them. -/
example (run : FnName) :
    ListLiftChecked .spec (importAcceptor ({[1, 2, 3]} : ByteLang) run) acceptFn := by
  intro w hw
  rw [bytesLang_importAcceptor] at hw
  rw [Set.mem_singleton_iff.1 hw, u8Size_eq]
  decide

end Silmaril.Wasi.Accept.Examples
