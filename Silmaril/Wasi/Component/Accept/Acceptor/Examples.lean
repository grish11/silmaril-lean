module

public import Silmaril.Wasi.Component.Accept.Acceptor.Thms
public import Silmaril.Wasi.Component.Accept.Examples
public import Silmaril.Wasm.Game.Examples.Defs
import Silmaril.Proofs.Wasi.Component.Accept.Wrappers

/-! # Acceptor wrappers: examples

* The specification component for `L` as a `ComponentAcceptor` with a separate `reject`
  import: its language, never-rejected language and strict language are `L`, every string,
  and `L` (`importAcceptor_strictLang`).
* The same component as an exported acceptor (`exportAcceptor`), and both shapes as
  `ByteAcceptor`s accepting the same language.
* A module acceptor of a real module (`exStart`) is finite and bounded by `2 ^ 32`.

Proofs: `Silmaril.Proofs.Wasi.Component.Accept.Wrappers`.
-/

@[expose] public section

namespace Silmaril.Wasi.Accept.Examples

open Silmaril.Formats.Accept Silmaril.Wasi Silmaril.Wasi.Accept
open Silmaril.Wasm.Game.Accept (ModuleAcceptor)

/-- The rejecting import of the examples. -/
def rejectFn : FnName := ⟨"", "reject"⟩

/-- The specification component for `L`, with a separate `reject` import. -/
def specAcceptor (L : ByteLang) (run : FnName) : ComponentAcceptor :=
  { I := {acceptFn}, X := {run}, model := importAcceptor L run, reject := some rejectFn }

theorem specAcceptor_lang (L : ByteLang) (run : FnName) : (specAcceptor L run).lang = L :=
  bytesLang_importAcceptor L run

/-- **It never calls `reject`**: every string is never rejected. -/
theorem specAcceptor_neverRejected (L : ByteLang) (run : FnName) :
    (specAcceptor L run).neverRejectedLang = ⊤ := by
  show (importRejected (importAcceptor L run) rejectFn (args1 bytes?))ᶜ = _
  rw [Silmaril.Proofs.Wasi.Component.Accept.importRejected_importAcceptor L run rejectFn
    (by decide), Set.compl_empty]
  rfl

theorem specAcceptor_strictLang (L : ByteLang) (run : FnName) :
    (specAcceptor L run).strictLang = L := by
  rw [ComponentAcceptor.strictLang, specAcceptor_neverRejected, specAcceptor_lang, inf_top_eq]

/-- The exported specification acceptor. -/
def specExport (L : ByteLang) : ComponentAcceptor :=
  { I := ∅, X := {acceptFn}, model := exportAcceptor L, mode := .exp }

/-- **Both shapes accept the same language.** -/
example (L : ByteLang) (run : FnName) :
    ByteAcceptor.lang (.inr (specAcceptor L run)) = ByteAcceptor.lang (.inr (specExport L)) :=
  (specAcceptor_lang L run).trans (exportBytesLang_exportAcceptor L).symm

/-- A module acceptor of a real module: finite, and bounded by the `i32` encoding. -/
example (P : Silmaril.Wasm.Numerics.Profile) :
    ((ModuleAcceptor.lang { profile := P, module := Silmaril.Wasm.Game.Examples.exStart }) :
      Set (List UInt8)).Finite :=
  ModuleAcceptor.lang_finite _

end Silmaril.Wasi.Accept.Examples
