module

public import Silmaril.Wasm.Game.Accept.Consequence.Defs
public import Silmaril.Wasm.Game.Accept.Acceptor.Thms
public import Silmaril.Logic.Consequence.Acceptor.Thms

/-! # Module acceptors as consequence systems: theorems

* Judgements are language membership: `ofAcceptor_moduleAcceptor`, `moduleSystem_apply`,
  `bytesSystem_of_decode`; undecodable bytes prove nothing (`bytesSystem_of_decode_none`).
* `withModule_self`: the template's own module is read as the template itself, so
  `A.moduleSystem A.module` is the row of `A` in the acceptor system.
* The address-width bound holds for every judgement (`moduleSystem_length_lt`,
  `bytesSystem_length_lt`).
* Callout-equivalent modules have the same rows (`moduleSystem_eq_of_calloutEquiv`).
* The default entry point: `moduleBytesSystem_iff` (bytes prove exactly what their module passes
  to `env.accept`, `bytesLang`), `moduleBytesSystem_of_decode`, `moduleBytesSystem_of_decode_none`,
  `moduleBytesSystem_length_lt`.
-/

@[expose] public section

namespace Silmaril.Wasm.Game.Accept

open Silmaril.Consequence (System)
open Silmaril.Wasm.Numerics (Profile)

namespace ModuleAcceptor

variable (A : ModuleAcceptor)

@[simp] theorem ofAcceptor_moduleAcceptor (w : List UInt8) :
    System.ofAcceptor ModuleAcceptor A w ↔ w ∈ A.lang := Iff.rfl

@[simp] theorem withModule_module (m : Module) : (A.withModule m).module = m := rfl

theorem withModule_self : A.withModule A.module = A := rfl

@[simp] theorem moduleSystem_apply (m : Module) (w : List UInt8) :
    A.moduleSystem m w ↔ w ∈ (A.withModule m).lang := Iff.rfl

theorem moduleSystem_self (w : List UInt8) :
    A.moduleSystem A.module w ↔ System.ofAcceptor ModuleAcceptor A w := Iff.rfl

theorem bytesSystem_of_decode {b : ByteArray} {m : Module}
    (h : Silmaril.Wasm.Binary.Core.decode? b = some m) (w : List UInt8) :
    A.bytesSystem b w ↔ A.moduleSystem m w :=
  System.ofDecoder_of_eq_some _ h w

theorem bytesSystem_of_decode_none {b : ByteArray}
    (h : Silmaril.Wasm.Binary.Core.decode? b = none) (w : List UInt8) : ¬ A.bytesSystem b w :=
  System.ofDecoder_of_eq_none _ h w

theorem moduleSystem_length_lt {m : Module} {w : List UInt8} (h : A.moduleSystem m w) :
    w.length < addrBound A.addr :=
  (A.withModule m).length_lt h

theorem bytesSystem_length_lt {b : ByteArray} {w : List UInt8} (h : A.bytesSystem b w) :
    w.length < addrBound A.addr :=
  let ⟨_, _, hw⟩ := h; A.moduleSystem_length_lt hw

/-- Modules that are callout-equivalent under `A`'s configuration have the same row. -/
theorem moduleSystem_eq_of_calloutEquiv {m m' : Module}
    (h : CalloutEquiv A.profile A.envs A.memIdx m m') :
    A.moduleSystem m = A.moduleSystem m' :=
  funext fun w => propext <| by
    rw [moduleSystem_apply, moduleSystem_apply,
      (A.withModule m).lang_eq_of_calloutEquiv (B := A.withModule m') rfl rfl rfl rfl rfl h]

@[simp] theorem ofModule_lang (m : Module) (P : Profile) :
    (ofModule m P).lang = bytesLang P m := rfl

end ModuleAcceptor

section Default

variable (P : Profile) {b : ByteArray} {w : List UInt8}

/-- **What module bytes prove**: exactly the bytes their module passes to `env.accept`. -/
theorem moduleBytesSystem_iff :
    moduleBytesSystem P b w ↔ ∃ m, Silmaril.Wasm.Binary.Core.decode? b = some m ∧ w ∈ bytesLang P m :=
  Iff.rfl

theorem moduleBytesSystem_of_decode {m : Module} (h : Silmaril.Wasm.Binary.Core.decode? b = some m) :
    moduleBytesSystem P b w ↔ w ∈ bytesLang P m :=
  (ModuleAcceptor.default P).bytesSystem_of_decode h w

/-- Bytes that are not a core module binary prove nothing. -/
theorem moduleBytesSystem_of_decode_none (h : Silmaril.Wasm.Binary.Core.decode? b = none) :
    ¬ moduleBytesSystem P b w :=
  (ModuleAcceptor.default P).bytesSystem_of_decode_none h w

theorem moduleBytesSystem_length_lt (h : moduleBytesSystem P b w) : w.length < 2 ^ 32 :=
  (ModuleAcceptor.default P).bytesSystem_length_lt h

end Default

end Silmaril.Wasm.Game.Accept
