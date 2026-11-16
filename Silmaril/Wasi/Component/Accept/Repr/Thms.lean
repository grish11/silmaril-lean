module

public import Silmaril.Wasi.Component.Accept.Thms
public import Silmaril.Wasm.Component.Reference.WIT.Repr.Thms

/-! # Component validators of represented Lean types

Given a WIT representation `r : Repr (Env.closed R) α t`, `reprLang r σ f` is the set of
Lean values whose WIT representation the component accepts through an imported `accept(t)`
(`exportReprLang` for an exported `accept(t) -> bool`). With it, a validator taking an event
stream `list<event>` is sound, complete or complete-within-a-bound for a Lean specification
of streams exactly when its WIT acceptor set is for the represented specification
(`sound_reprLang_iff`, …). It is invariant under equal traces and `CompEquiv`, and at
`list<u8>` it is the byte language (`reprLang_bytes`).
-/

@[expose] public section

namespace Silmaril.Wasi.Accept

open Silmaril.Games Silmaril.Formats.Accept
open Silmaril.Wasm.Component (Comp CoreModule)
open Silmaril.Wasm.Component.Algebra (CompEquiv)
open Silmaril.Wasm.Component.WIT

universe v

variable {R : Type v} {α : Type} {t : ClosedType R} {I X I' X' : Set FnName}

/-- The Lean values whose representation is accepted through the import `f`. -/
def reprLang (r : Repr (Env.closed R) α t) (σ : Strategy (nsig I) (nsig X))
    (f : FnName := acceptFn) : Set α :=
  r.pull (valLang t σ f)

/-- The Lean values whose representation makes the export `f` return `true`. -/
def exportReprLang (r : Repr (Env.closed R) α t) (σ : Strategy (nsig I) (nsig X))
    (f : FnName := acceptFn) : Set α :=
  r.pull (exportValLang t σ f)

variable (r : Repr (Env.closed R) α t) {σ : Strategy (nsig I) (nsig X)} {f : FnName}
  {S D : Set α}

theorem sound_reprLang_iff :
    Lang.Sound (valLang t σ f) (r.lang S) ↔ Lang.Sound (reprLang r σ f) S :=
  r.sound_lang_iff

theorem complete_reprLang_iff :
    Lang.Complete (valLang t σ f) (r.lang S) ↔ Lang.Complete (reprLang r σ f) S :=
  r.complete_lang_iff

theorem completeWithin_reprLang_iff :
    Lang.CompleteWithin (r.lang D) (valLang t σ f) (r.lang S) ↔
      Lang.CompleteWithin D (reprLang r σ f) S :=
  r.completeWithin_lang_iff

theorem sound_exportReprLang_iff :
    Lang.Sound (exportValLang t σ f) (r.lang S) ↔ Lang.Sound (exportReprLang r σ f) S :=
  r.sound_lang_iff

theorem complete_exportReprLang_iff :
    Lang.Complete (exportValLang t σ f) (r.lang S) ↔ Lang.Complete (exportReprLang r σ f) S :=
  r.complete_lang_iff

theorem completeWithin_exportReprLang_iff :
    Lang.CompleteWithin (r.lang D) (exportValLang t σ f) (r.lang S) ↔
      Lang.CompleteWithin D (exportReprLang r σ f) S :=
  r.completeWithin_lang_iff

theorem reprLang_eq_of_traces {τ : Strategy (nsig I') (nsig X')} (h : Traces σ = Traces τ) :
    reprLang r σ f = reprLang r τ f := by
  unfold reprLang valLang; rw [importAccepted_eq_of_traces h]

theorem exportReprLang_eq_of_traces {τ : Strategy (nsig I') (nsig X')}
    (h : Traces σ = Traces τ) : exportReprLang r σ f = exportReprLang r τ f := by
  unfold exportReprLang exportValLang; rw [exportAccepted_eq_of_traces h]

theorem reprLang_mono {τ : Strategy (nsig I) (nsig X)} (h : σ ≤ τ) :
    reprLang r σ f ⊆ reprLang r τ f :=
  fun _ hx => importAccepted_mono h hx

theorem reprLang_compModel_of_compEquiv {M : Type} [CoreModule M]
    (C : Silmaril.Wasm.Component.CoreSem M) (L : Layout) {c c' : Comp M} (h : CompEquiv C c c') :
    reprLang r (L.compModel C c) f = reprLang r (L.compModel C c') f := by
  unfold reprLang valLang; rw [importAccepted_compModel_of_compEquiv C L h]

/-- At `list<u8>`, the represented language is the byte language. -/
theorem reprLang_bytes (σ : Strategy (nsig I) (nsig X)) (f : FnName) :
    reprLang (Repr.bytes (E := Env.closed R)) σ f = bytesLang σ f := by
  unfold reprLang Repr.pull
  rw [valLang_bytes]; rfl

end Silmaril.Wasi.Accept
