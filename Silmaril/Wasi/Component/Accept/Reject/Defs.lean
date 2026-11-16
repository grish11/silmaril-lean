module

public import Silmaril.Wasi.Component.Accept.Defs
public import Silmaril.Semantics.Accept.Rel.Defs

/-! # Rejection, never-rejection and indexed acceptance of components

There are two universal readings of rejection, mirroring the two acceptance readings of
`Silmaril.Wasi.Component.Accept`.

* **Through an imported `reject(v)`** (`importRejected`): the values passed to `reject` in
  some play. `neverCalled σ f dec` is the complement: the values the component calls `f` with
  in **no** play, against **no** host or caller.
* **Through an exported `reject(v) -> bool`** (`exportRejected`): the values some call of the
  export answers with `false`. `neverFalse σ f dec` is the complement: the values for which no
  call of the export ever returns `false`.

Both universal sets are safety properties. They hold vacuously for values the component never
handles: a trapping, silent or never-called export never returns `false`. They are therefore
weaker than acceptance, and they *grow* when a component is refined (fewer plays, fewer
rejections; `Silmaril.Wasi.Accept.neverCalled_anti`).

**Indexed acceptance.** `importIndexed σ dec` gives one acceptor set per WIT import name, as a
`Silmaril.Accept.IndexedLang`. `layoutIndexed L σ dec` gives one per import *position* of a
`Layout`: an IR component's imports are positional, so this is the index the canonical ABI
sees.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasi.Accept

open Silmaril.Games Silmaril.Games.Accept Silmaril.Formats.Accept
open Silmaril.Wasm.Component (Val)

variable {I X : Set FnName} {α : Type}

/-- A call of the export `f` returning `false`, its arguments decoded by `dec`. -/
def exportFalseObs (f : FnName) (dec : List Val → Option α) : WEv → Option α
  | .ret g args (some [.bool false]) => if g = f then dec args else none
  | _ => none

/-- The values the component passes to the import `f` (a `reject` import) in some play. -/
def importRejected (σ : Strategy (nsig I) (nsig X)) (f : FnName) (dec : List Val → Option α) :
    Lang α :=
  importAccepted σ f dec

/-- **The import `f` is never called with the value**: in no play, against no host. -/
def neverCalled (σ : Strategy (nsig I) (nsig X)) (f : FnName) (dec : List Val → Option α) :
    Lang α :=
  (importRejected σ f dec)ᶜ

/-- The values for which some call of the export `f` returns `false`. -/
def exportRejected (σ : Strategy (nsig I) (nsig X)) (f : FnName) (dec : List Val → Option α) :
    Lang α :=
  observed (exportFalseObs f dec) (Traces σ)

/-- **The export `f` never returns `false` on the value.** -/
def neverFalse (σ : Strategy (nsig I) (nsig X)) (f : FnName) (dec : List Val → Option α) :
    Lang α :=
  (exportRejected σ f dec)ᶜ

/-- Accepted through the export `acc` (some call returns `true`), rejected through the export
`rej` by no call. -/
def exportAcceptedNotRejected (σ : Strategy (nsig I) (nsig X)) (acc rej : FnName)
    (dec : List Val → Option α) : Lang α :=
  exportAccepted σ acc dec ∩ neverFalse σ rej dec

/-! ## Indexed acceptance -/

/-- One acceptor set per WIT import name. -/
def importIndexed (σ : Strategy (nsig I) (nsig X)) (dec : List Val → Option α) :
    Silmaril.Accept.IndexedLang (fun _ : FnName => α) :=
  fun f => importAccepted σ f dec

/-- One acceptor set per import position of a layout (empty past the last import). -/
def layoutIndexed (L : Layout) (σ : Strategy (nsig I) (nsig X)) (dec : List Val → Option α) :
    Silmaril.Accept.IndexedLang (fun _ : Nat => α) :=
  fun i => match L.imports[i]? with
    | some f => importAccepted σ f dec
    | none => ∅

end Silmaril.Wasi.Accept
