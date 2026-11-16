module

public import Silmaril.Wasi.Component.Accept.Defs
public import Silmaril.Wasi.Component.Thms
public import Silmaril.Wasm.Component.Algebra.Equiv.Defs
public import Silmaril.Games.Accept.Thms
public import Silmaril.Formats.Accept.Thms

/-! # Inputs accepted by a component: theorems

* **Equivalence**: components with the same named traces accept the same inputs, through
  imports and exports alike, whatever their worlds (`importAccepted_eq_of_traces`,
  `exportAccepted_eq_of_traces`); IR components that are `CompEquiv` (equal denotations) have
  equal acceptor sets under every layout (`importAccepted_compModel_of_compEquiv`, and the
  export form), and `CompRefines` gives inclusion (`importAccepted_compModel_of_compRefines`).
* **Refinement** (`σ ≤ τ`) refines acceptance (`importAccepted_mono`, `exportAccepted_mono`).
* **Witnesses**: an input is accepted through the import iff some play ends in the call
  (`mem_importAccepted_iff`), through the export iff some play ends in the `true` return
  (`mem_exportAccepted_iff`).
* **Decoding**: `bytes?` inverts `bytesV` (`bytes?_bytesV`), and decoding at `list<u8>` is
  `bytes?` (`decode_bytes`), so the `list<u8>` value acceptors are the byte languages
  (`valLang_bytes`, `exportValLang_bytes`).
-/

@[expose] public section

namespace Silmaril.Wasi.Accept

open Silmaril.Games Silmaril.Games.Accept Silmaril.Formats.Accept
open Silmaril.Wasm.Component (Val Comp CoreModule)
open Silmaril.Wasm.Component.WIT
open Silmaril.Wasm.Component.Algebra (CompEquiv CompRefines)

universe v

variable {I X I' X' : Set FnName} {α : Type} {f : FnName} {dec : List Val → Option α}

/-! ## Equivalence and refinement -/

/-- **Components with the same named traces accept the same inputs through the import.** -/
theorem importAccepted_eq_of_traces {σ : Strategy (nsig I) (nsig X)}
    {τ : Strategy (nsig I') (nsig X')} (h : Traces σ = Traces τ) :
    importAccepted σ f dec = importAccepted τ f dec := by
  unfold importAccepted; rw [h]

/-- **Components with the same named traces accept the same inputs through the export.** -/
theorem exportAccepted_eq_of_traces {σ : Strategy (nsig I) (nsig X)}
    {τ : Strategy (nsig I') (nsig X')} (h : Traces σ = Traces τ) :
    exportAccepted σ f dec = exportAccepted τ f dec := by
  unfold exportAccepted; rw [h]

theorem traces_mono {σ τ : Strategy (nsig I) (nsig X)} (h : σ ≤ τ) : Traces σ ⊆ Traces τ :=
  Set.image_mono fun _ hs => h hs

/-- A refinement accepts no more through the import. -/
theorem importAccepted_mono {σ τ : Strategy (nsig I) (nsig X)} (h : σ ≤ τ) :
    importAccepted σ f dec ⊆ importAccepted τ f dec :=
  observed_mono (traces_mono h)

/-- A refinement accepts no more through the export. -/
theorem exportAccepted_mono {σ τ : Strategy (nsig I) (nsig X)} (h : σ ≤ τ) :
    exportAccepted σ f dec ⊆ exportAccepted τ f dec :=
  observed_mono (traces_mono h)

section IR

variable {M : Type} [CoreModule M] (C : Silmaril.Wasm.Component.CoreSem M) (L : Layout)
  {c c' : Comp M}

/-- **Denotationally equivalent IR components accept the same inputs through the import**,
under every layout. -/
theorem importAccepted_compModel_of_compEquiv (h : CompEquiv C c c') :
    importAccepted (L.compModel C c) f dec = importAccepted (L.compModel C c') f dec := by
  unfold Layout.compModel; rw [h.2]

/-- **Denotationally equivalent IR components accept the same inputs through the export.** -/
theorem exportAccepted_compModel_of_compEquiv (h : CompEquiv C c c') :
    exportAccepted (L.compModel C c) f dec = exportAccepted (L.compModel C c') f dec := by
  unfold Layout.compModel; rw [h.2]

/-- A refining IR component accepts no more through the import. -/
theorem importAccepted_compModel_of_compRefines (h : CompRefines C c c') :
    importAccepted (L.compModel C c) f dec ⊆ importAccepted (L.compModel C c') f dec :=
  importAccepted_mono (Layout.view_mono L h.2)

/-- A refining IR component accepts no more through the export. -/
theorem exportAccepted_compModel_of_compRefines (h : CompRefines C c c') :
    exportAccepted (L.compModel C c) f dec ⊆ exportAccepted (L.compModel C c') f dec :=
  exportAccepted_mono (Layout.view_mono L h.2)

end IR

/-! ## Witnesses -/

/-- Import acceptance is strategy acceptance through the event of each move. -/
theorem importAccepted_eq (σ : Strategy (nsig I) (nsig X)) :
    importAccepted σ f dec = σ.accepted (importObs f dec ∘ wev) :=
  observed_map wev fun _ => rfl

/-- Export acceptance is strategy acceptance through the event of each move. -/
theorem exportAccepted_eq (σ : Strategy (nsig I) (nsig X)) :
    exportAccepted σ f dec = σ.accepted (exportObs f dec ∘ wev) :=
  observed_map wev fun _ => rfl

theorem importObs_eq_some {e : WEv} {a : α} :
    importObs f dec e = some a ↔ ∃ args, e = .req f args ∧ dec args = some a := by
  constructor
  · intro h
    unfold importObs at h
    split at h
    · split_ifs at h with hg
      exact ⟨_, by rw [hg], h⟩
    · cases h
  · rintro ⟨args, rfl, h⟩
    simp [importObs, h]

theorem exportObs_eq_some {e : WEv} {a : α} :
    exportObs f dec e = some a ↔ ∃ args, e = .ret f args (some [.bool true]) ∧ dec args = some a := by
  constructor
  · intro h
    unfold exportObs at h
    split at h
    · split_ifs at h with hg
      exact ⟨_, by rw [hg], h⟩
    · cases h
  · rintro ⟨args, rfl, h⟩
    simp [exportObs, h]

/-- **An input is accepted through the import `f` iff some play ends in a call of `f` whose
arguments decode to it.** -/
theorem mem_importAccepted_iff (σ : Strategy (nsig I) (nsig X)) {a : α} :
    a ∈ importAccepted σ f dec ↔
      ∃ s m, s ++ [m] ∈ σ.plays ∧ ∃ args, wev m = .req f args ∧ dec args = some a := by
  rw [importAccepted_eq, Strategy.mem_accepted_iff]
  simp only [Function.comp_apply, importObs_eq_some]

/-- **An input is accepted through the export `f` iff some play ends in a `true` return of a
call of `f` whose arguments decode to it.** -/
theorem mem_exportAccepted_iff (σ : Strategy (nsig I) (nsig X)) {a : α} :
    a ∈ exportAccepted σ f dec ↔ ∃ s m, s ++ [m] ∈ σ.plays ∧
      ∃ args, wev m = .ret f args (some [.bool true]) ∧ dec args = some a := by
  rw [exportAccepted_eq, Strategy.mem_accepted_iff]
  simp only [Function.comp_apply, exportObs_eq_some]

/-! ## Decoding -/

/-- `bytes?` inverts `bytesV`. -/
@[simp] theorem bytes?_bytesV (b : List (BitVec 8)) :
    bytes? (bytesV b) = some (b.map UInt8.ofBitVec) := by
  simp only [bytes?, bytesV, ofRecord?, Option.bind_some]
  induction b with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons, List.mapM_cons, ih]
    rfl

/-- The `list<u8>` value `bytesV` of a byte string decodes to it. -/
@[simp] theorem bytes?_bytesV_toBitVec (w : List UInt8) :
    bytes? (bytesV (w.map UInt8.toBitVec)) = some w := by
  simp [Function.comp_def]

variable {R : Type v}

/-- Decoding at `list<u8>` is `bytes?`. -/
theorem decode_bytes (v : Val) : decode (ValType.bytes : ClosedType R) v = bytes? v := rfl

/-- The `list<u8>` acceptors through the import are the byte language. -/
theorem valLang_bytes {I X : Set FnName} (σ : Strategy (nsig I) (nsig X)) (f : FnName) :
    valLang (ValType.bytes : ClosedType R) σ f = bytesLang σ f := by
  rfl

/-- The `list<u8>` acceptors through the export are the byte language. -/
theorem exportValLang_bytes {I X : Set FnName} (σ : Strategy (nsig I) (nsig X)) (f : FnName) :
    exportValLang (ValType.bytes : ClosedType R) σ f = exportBytesLang σ f := by
  rfl

end Silmaril.Wasi.Accept
