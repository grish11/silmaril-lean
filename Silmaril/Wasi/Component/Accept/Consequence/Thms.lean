module

public import Silmaril.Wasi.Component.Accept.Consequence.Defs
public import Silmaril.Wasi.Component.Accept.Acceptor.Thms
public import Silmaril.Wasm.Game.Accept.Consequence.Thms

/-! # Component acceptors, and acceptors of either shape, as consequence systems: theorems

* Judgements are language membership (`compSystem_apply`, `ofAcceptor_byteAcceptor`), and the
  sum's rows are the module and component rows (`programSystem_inl`, `programSystem_inr`).
* **Component refinement is soundness of systems**: `CompRefines C c c'` puts `c`'s row below
  `c'`'s (`compSystem_le_of_compRefines`), and `CompEquiv` makes them equal
  (`compSystem_eq_of_compEquiv`).
* Bytes that decode as a module have the module row (`ByteAcceptor.bytesSystem_of_decode_module`),
  bytes that decode only as a component have the component row
  (`ByteAcceptor.bytesSystem_of_decode_component`), and bytes that decode as neither prove
  nothing (`ByteAcceptor.bytesSystem_of_decode_none`).
-/

@[expose] public section

namespace Silmaril.Wasi.Accept

open Silmaril.Consequence (System)
open Silmaril.Wasm.Component (Comp CoreModule CoreSem)
open Silmaril.Wasm.Component.Algebra (CompEquiv CompRefines)
open Silmaril.Wasm.Game.Accept (ModuleAcceptor)

namespace ComponentAcceptor

@[simp] theorem ofAcceptor_componentAcceptor (A : ComponentAcceptor) (w : List UInt8) :
    System.ofAcceptor ComponentAcceptor A w ↔ w ∈ A.lang := Iff.rfl

variable {M : Type} [CoreModule M] (C : CoreSem M) (L : Layout) (acc : FnName)
  (rej : Option FnName) (mode : Mode)

@[simp] theorem compSystem_apply (c : Comp M) (w : List UInt8) :
    compSystem C L acc rej mode c w ↔ w ∈ (ofIR C L c acc rej mode).lang := Iff.rfl

theorem compSystem_le_of_compRefines {c c' : Comp M} (h : CompRefines C c c') :
    compSystem C L acc rej mode c ≤ compSystem C L acc rej mode c' :=
  fun _ hw => ofIR_lang_of_compRefines C L acc rej mode h hw

theorem compSystem_eq_of_compEquiv {c c' : Comp M} (h : CompEquiv C c c') :
    compSystem C L acc rej mode c = compSystem C L acc rej mode c' :=
  funext fun w => propext <| by
    rw [compSystem_apply, compSystem_apply, ofIR_lang_of_compEquiv C L acc rej mode h]

theorem bytesSystem_of_decode {B : Type} {decode : B → Option (Comp M)} {b : B} {c : Comp M}
    (h : decode b = some c) (w : List UInt8) :
    bytesSystem C L acc rej mode decode b w ↔ compSystem C L acc rej mode c w :=
  System.ofDecoder_of_eq_some _ h w

end ComponentAcceptor

namespace ByteAcceptor

@[simp] theorem ofAcceptor_byteAcceptor (A : ByteAcceptor) (w : List UInt8) :
    System.ofAcceptor ByteAcceptor A w ↔ w ∈ A.lang := Iff.rfl

variable {W : Type} (A : ModuleAcceptor) (I : W → ComponentAcceptor)

@[simp] theorem programSystem_inl (m : Silmaril.Wasm.Module) (w : List UInt8) :
    programSystem A I (.inl m) w ↔ A.moduleSystem m w := Iff.rfl

@[simp] theorem programSystem_inr (x : W) (w : List UInt8) :
    programSystem A I (.inr x) w ↔ System.ofAcceptor ComponentAcceptor (I x) w := Iff.rfl

variable (C : CoreSem Silmaril.Wasm.Component.Binary.CoreMod) (L : Layout) (acc : FnName)
  (rej : Option FnName) (mode : Mode)

theorem bytesSystem_of_decode_module {b : ByteArray} {m : Silmaril.Wasm.Module}
    (h : Silmaril.Wasm.Binary.Core.decode? b = some m) (w : List UInt8) :
    bytesSystem A C L acc rej mode b w ↔ A.moduleSystem m w :=
  System.ofDecoder_of_eq_some (decode := decode) (m := .inl m)
    (interp A (ComponentAcceptor.interp C L acc rej mode)) (by simp [decode, h]) w

theorem bytesSystem_of_decode_component {b : ByteArray}
    {c : Comp Silmaril.Wasm.Component.Binary.CoreMod}
    (hm : Silmaril.Wasm.Binary.Core.decode? b = none)
    (hc : ComponentAcceptor.decodeBinary b = some c) (w : List UInt8) :
    bytesSystem A C L acc rej mode b w ↔ ComponentAcceptor.compSystem C L acc rej mode c w :=
  System.ofDecoder_of_eq_some (decode := decode) (m := .inr c)
    (interp A (ComponentAcceptor.interp C L acc rej mode)) (by simp [decode, hm, hc]) w

theorem bytesSystem_of_decode_none {b : ByteArray}
    (hm : Silmaril.Wasm.Binary.Core.decode? b = none)
    (hc : ComponentAcceptor.decodeBinary b = none) (w : List UInt8) :
    ¬ bytesSystem A C L acc rej mode b w :=
  System.ofDecoder_of_eq_none _ (by simp [decode, hm, hc]) w

end ByteAcceptor

end Silmaril.Wasi.Accept
