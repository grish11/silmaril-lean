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
-/

@[expose] public section

namespace Silmaril.Wasm.Game.Accept

open Silmaril.Consequence (System)

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

end ModuleAcceptor

end Silmaril.Wasm.Game.Accept
