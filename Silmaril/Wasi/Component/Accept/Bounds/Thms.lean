module

public import Silmaril.Wasi.Component.Accept.Bounds.Defs
public import Silmaril.Wasi.Component.Accept.Canon.Thms
public import Silmaril.Wasm.Game.Accept.Bounds.Thms
public import Silmaril.Wasm.Component.Reference.WIT.Interp.Thms

/-! # Length bounds of component acceptors: theorems

* `CanonLowerAccept` is `CanonLowerAcceptBy Callout.bytes32` (`canonLowerAccept_iff`).
* **Through a core module**, a correspondence gives equal byte languages for any decoder
  (`accepted_eq_of_canonLowerAcceptBy`). So a component lowered onto a 32-bit memory accepts
  only strings shorter than `2 ^ 32` (`bytesLang_length_lt_of_canonLowerAccept`), and onto a
  64-bit memory, shorter than `2 ^ 64` (`bytesLang_length_lt_of_canonLowerAccept64`). Both
  languages are finite.
* **Through the lift's check**, the bound is `≤ lim.maxListBytes`
  (`bytesLang_length_le_of_listLiftChecked`): `≤ 2 ^ 28 - 1` under `Limits.spec`, which is
  stricter than the `i32` address-width bound, and `≤ 2 ^ 32 - 1` under `Limits.wasmtime`,
  which coincides with it.
* Without an assumption there is no bound: the specification component for the language of
  *all* byte strings accepts strings of every length (`Silmaril.Wasi.Accept.Examples`).
-/

@[expose] public section

namespace Silmaril.Wasi.Accept

open Silmaril.Games Silmaril.Formats.Accept
open Silmaril.Wasm.Game.Accept (Callout)
open Silmaril.Wasm.Numerics (Profile)

variable {I X : Set FnName} {σ : Strategy (nsig I) (nsig X)} {f : FnName}
  {callouts : Set Callout} {imp : String × String}

theorem canonLowerAccept_iff :
    CanonLowerAccept callouts imp σ f ↔ CanonLowerAcceptBy Callout.bytes32 callouts imp σ f :=
  ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩

/-- **Correspondence gives equal byte languages**, for any decoder of the core callouts. -/
theorem accepted_eq_of_canonLowerAcceptBy {obs : Callout → Option (List UInt8)}
    (h : CanonLowerAcceptBy obs callouts imp σ f) :
    {w | ∃ o ∈ callouts, o.imp = imp ∧ obs o = some w} = bytesLang σ f := by
  ext w
  change _ ↔ w ∈ importAccepted σ f (args1 bytes?)
  rw [mem_importAccepted_iff]
  constructor
  · rintro ⟨o, ho, hi, hw⟩; exact h.lower o ho hi w hw
  · rintro ⟨s, m, hs, args, he, hw⟩; exact h.lift s m hs args w he hw

/-- **A component lowered onto a 32-bit memory accepts strings shorter than `2 ^ 32`.** -/
theorem bytesLang_length_lt_of_canonLowerAccept {P : Profile} {m : Silmaril.Wasm.Module}
    (h : CanonLowerAccept (Silmaril.Wasm.Game.Accept.Callouts P Silmaril.Wasm.Game.UEnvOk 0 m)
      imp σ f) {w : List UInt8} (hw : w ∈ bytesLang σ f) : w.length < 2 ^ 32 := by
  rw [← bytesLang_eq_of_canonLowerAccept h] at hw
  exact Silmaril.Wasm.Game.Accept.bytesLang_length_lt hw

theorem bytesLang_finite_of_canonLowerAccept {P : Profile} {m : Silmaril.Wasm.Module}
    (h : CanonLowerAccept (Silmaril.Wasm.Game.Accept.Callouts P Silmaril.Wasm.Game.UEnvOk 0 m)
      imp σ f) : (bytesLang σ f : Set (List UInt8)).Finite :=
  ByteLang.finite_of_length_lt fun _ hw => bytesLang_length_lt_of_canonLowerAccept h hw

/-- **A component lowered onto a 64-bit memory accepts strings shorter than `2 ^ 64`.** -/
theorem bytesLang_length_lt_of_canonLowerAccept64 {P : Profile}
    {Envs : Silmaril.Wasm.Execution.Core.Store Nat → Silmaril.Wasm.Game.SEnv
      Silmaril.Wasm.Game.UImp → Prop} {k : Nat} {m : Silmaril.Wasm.Module}
    (h : CanonLowerAcceptBy Callout.bytes64 (Silmaril.Wasm.Game.Accept.Callouts P Envs k m)
      imp σ f) {w : List UInt8} (hw : w ∈ bytesLang σ f) : w.length < 2 ^ 64 := by
  rw [← accepted_eq_of_canonLowerAcceptBy h] at hw
  exact Silmaril.Wasm.Game.Accept.accepted_bytes64_length_lt hw

theorem bytesLang_finite_of_canonLowerAccept64 {P : Profile}
    {Envs : Silmaril.Wasm.Execution.Core.Store Nat → Silmaril.Wasm.Game.SEnv
      Silmaril.Wasm.Game.UImp → Prop} {k : Nat} {m : Silmaril.Wasm.Module}
    (h : CanonLowerAcceptBy Callout.bytes64 (Silmaril.Wasm.Game.Accept.Callouts P Envs k m)
      imp σ f) : (bytesLang σ f : Set (List UInt8)).Finite :=
  ByteLang.finite_of_length_lt fun _ hw => bytesLang_length_lt_of_canonLowerAccept64 h hw

/-! ## The lift's length check -/

theorem u8Size_eq : u8Size = 1 := (Silmaril.Wasm.Component.WIT.layout_u8 .i32).1

/-- **Under the lift's check, accepted strings have at most `lim.maxListBytes` bytes.** -/
theorem bytesLang_length_le_of_listLiftChecked {lim : Silmaril.Wasm.Component.Limits}
    (h : ListLiftChecked lim σ f) {w : List UInt8} (hw : w ∈ bytesLang σ f) :
    w.length ≤ lim.maxListBytes := by
  simpa [u8Size_eq] using h w hw

theorem exportBytesLang_length_le_of_listLiftChecked {lim : Silmaril.Wasm.Component.Limits}
    (h : ExportListLiftChecked lim σ f) {w : List UInt8} (hw : w ∈ exportBytesLang σ f) :
    w.length ≤ lim.maxListBytes := by
  simpa [u8Size_eq] using h w hw

theorem bytesLang_finite_of_listLiftChecked {lim : Silmaril.Wasm.Component.Limits}
    (h : ListLiftChecked lim σ f) : (bytesLang σ f : Set (List UInt8)).Finite :=
  ByteLang.finite_of_length_le fun _ hw => bytesLang_length_le_of_listLiftChecked h hw

theorem exportBytesLang_finite_of_listLiftChecked {lim : Silmaril.Wasm.Component.Limits}
    (h : ExportListLiftChecked lim σ f) : (exportBytesLang σ f : Set (List UInt8)).Finite :=
  ByteLang.finite_of_length_le fun _ hw => exportBytesLang_length_le_of_listLiftChecked h hw

/-- The specification's limits: at most `2 ^ 28 - 1` bytes. -/
theorem bytesLang_length_le_spec (h : ListLiftChecked .spec σ f) {w : List UInt8}
    (hw : w ∈ bytesLang σ f) : w.length ≤ 2 ^ 28 - 1 :=
  bytesLang_length_le_of_listLiftChecked h hw

/-- wasmtime's limits: at most `2 ^ 32 - 1` bytes, the `i32` bound. -/
theorem bytesLang_length_le_wasmtime (h : ListLiftChecked .wasmtime σ f) {w : List UInt8}
    (hw : w ∈ bytesLang σ f) : w.length ≤ 2 ^ 32 - 1 :=
  bytesLang_length_le_of_listLiftChecked h hw

/-- The size filter at the checked maximum leaves the language unchanged. -/
theorem upTo_bytesLang_of_listLiftChecked {lim : Silmaril.Wasm.Component.Limits}
    (h : ListLiftChecked lim σ f) :
    Silmaril.Accept.upTo List.length lim.maxListBytes (bytesLang σ f) = bytesLang σ f :=
  ByteLang.upTo_eq_self fun _ hw => bytesLang_length_le_of_listLiftChecked h hw

end Silmaril.Wasi.Accept
