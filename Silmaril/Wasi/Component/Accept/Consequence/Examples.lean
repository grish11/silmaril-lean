module

public import Silmaril.Wasi.Component.Accept.Consequence.Thms
public import Silmaril.Wasi.Component.Accept.Acceptor.Examples

/-! # Wasm acceptors as consequence systems: examples

* **Acceptor view.** The specification component for a language `L`
  (`Silmaril.Wasi.Accept.Examples.specAcceptor`) proves exactly the words of `L`, as a
  component acceptor and as a `ByteAcceptor`.
* **Program view.** Reading languages as specification components gives a program system
  whose component rows are the languages; module rows obey the `i32` length bound.
* **Bytes view.** The 8-byte binary of the empty module decodes (by `rfl`) to the empty module,
  so its row is that module's row, in the module system and in the either-shape system. The
  empty byte string decodes as neither and proves nothing.
* **Simple entry points.** `moduleBytesSystem` and `componentBytesSystem C`: shape isolation
  (the empty component binary proves nothing as a module, the empty module binary nothing as a
  component), invalid bytes, and agreement with the mixed system on module bytes.
-/

@[expose] public section

namespace Silmaril.Wasi.Accept.ConsequenceExamples

open Silmaril.Consequence (System)
open Silmaril.Formats.Accept (ByteLang)
open Silmaril.Wasi.Accept.Examples (specAcceptor)
open Silmaril.Wasm.Game.Accept (ModuleAcceptor)

/-! ## Acceptor view -/

example (L : ByteLang) (run : FnName) (w : List UInt8) :
    System.ofAcceptor ComponentAcceptor (specAcceptor L run) w ↔ w ∈ L := by
  rw [ComponentAcceptor.ofAcceptor_componentAcceptor, Examples.specAcceptor_lang]

example (L : ByteLang) (run : FnName) (w : List UInt8) :
    System.ofAcceptor ByteAcceptor (.inr (specAcceptor L run)) w ↔ w ∈ L := by
  rw [ByteAcceptor.ofAcceptor_byteAcceptor, ByteAcceptor.lang_inr, Examples.specAcceptor_lang]

/-! ## Program view -/

/-- The template module acceptor of the examples: the specification profile, defaults
otherwise (`env.accept(ptr: i32, len: i32)` on memory 0, every host meeting Core's contract). -/
def template : ModuleAcceptor := { profile := .spec, module := {} }

example (L : ByteLang) (run : FnName) (w : List UInt8) :
    ByteAcceptor.programSystem template (fun L => specAcceptor L run) (.inr L) w ↔ w ∈ L := by
  rw [ByteAcceptor.programSystem_inr, ComponentAcceptor.ofAcceptor_componentAcceptor,
    Examples.specAcceptor_lang]

example (m : Silmaril.Wasm.Module) (w : List UInt8) (h : template.moduleSystem m w) :
    w.length < 2 ^ 32 :=
  template.moduleSystem_length_lt h

/-! ## Bytes view -/

/-- The binary of the empty module: magic and version 1. -/
def emptyModuleBytes : ByteArray := ⟨#[0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00]⟩

theorem decode_emptyModuleBytes :
    Silmaril.Wasm.Binary.Core.decode? emptyModuleBytes = some {} := by rfl

example (w : List UInt8) :
    template.bytesSystem emptyModuleBytes w ↔ template.moduleSystem {} w :=
  template.bytesSystem_of_decode decode_emptyModuleBytes w

example (C : Silmaril.Wasm.Component.CoreSem Silmaril.Wasm.Component.Binary.CoreMod) (L : Layout)
    (w : List UInt8) :
    ByteAcceptor.bytesSystem template C L acceptFn none .imp emptyModuleBytes w ↔
      template.moduleSystem {} w :=
  ByteAcceptor.bytesSystem_of_decode_module template C L acceptFn none .imp
    decode_emptyModuleBytes w

example (w : List UInt8) : ¬ template.bytesSystem ByteArray.empty w :=
  template.bytesSystem_of_decode_none (by decide) w

example (C : Silmaril.Wasm.Component.CoreSem Silmaril.Wasm.Component.Binary.CoreMod) (L : Layout)
    (w : List UInt8) :
    ¬ ByteAcceptor.bytesSystem template C L acceptFn none .imp ByteArray.empty w :=
  ByteAcceptor.bytesSystem_of_decode_none template C L acceptFn none .imp (by decide) (by decide) w

/-! ## Simple entry points: one shape each

`moduleBytesSystem` needs no template; `componentBytesSystem` needs only a core semantics `C`.
Each reads its own binary shape only: a module binary proves nothing as a component and a
component binary proves nothing as a module. Bytes are fixed byte strings; the decoders run in
the kernel (`decide`, `rfl`). -/

/-- The smallest component binary: magic, version `0x0d`, layer `1`. -/
def emptyComponentBytes : ByteArray := ⟨#[0x00, 0x61, 0x73, 0x6d, 0x0d, 0x00, 0x01, 0x00]⟩

/-- A truncated header, neither shape. -/
def truncatedBytes : ByteArray := ⟨#[0x00, 0x61, 0x73]⟩

theorem decodeBinary_emptyComponentBytes :
    ComponentAcceptor.decodeBinary emptyComponentBytes = some (.mk [] [] []) := by rfl

theorem decode_emptyComponentBytes :
    Silmaril.Wasm.Binary.Core.decode? emptyComponentBytes = none := by decide

theorem decodeBinary_emptyModuleBytes :
    ComponentAcceptor.decodeBinary emptyModuleBytes = none := by decide

/-- Module bytes: their module's language under the default interpretation. -/
example (w : List UInt8) :
    Silmaril.Wasm.Game.Accept.moduleBytesSystem .spec emptyModuleBytes w ↔
      w ∈ Silmaril.Wasm.Game.Accept.bytesLang .spec {} :=
  Silmaril.Wasm.Game.Accept.moduleBytesSystem_of_decode _ decode_emptyModuleBytes

/-- **Shape isolation**: component bytes prove nothing in the module system ... -/
example (w : List UInt8) :
    ¬ Silmaril.Wasm.Game.Accept.moduleBytesSystem .spec emptyComponentBytes w :=
  Silmaril.Wasm.Game.Accept.moduleBytesSystem_of_decode_none _ decode_emptyComponentBytes

/-- ... and module bytes prove nothing in the component system. -/
example (C : Silmaril.Wasm.Component.CoreSem Silmaril.Wasm.Component.Binary.CoreMod)
    (w : List UInt8) : ¬ componentBytesSystem C .imp emptyModuleBytes w :=
  componentBytesSystem_of_decode_none C .imp decodeBinary_emptyModuleBytes

/-- Component bytes: their lowered component's language, read through its own names. -/
example (C : Silmaril.Wasm.Component.CoreSem Silmaril.Wasm.Component.Binary.CoreMod)
    (w : List UInt8) :
    componentBytesSystem C .imp emptyComponentBytes w ↔
      w ∈ (ComponentAcceptor.ofComp C (.mk [] [] []) .imp).lang :=
  componentBytesSystem_of_decode C .imp decodeBinary_emptyComponentBytes

/-- **Invalid bytes** prove nothing in either system. -/
example (w : List UInt8) : ¬ Silmaril.Wasm.Game.Accept.moduleBytesSystem .spec truncatedBytes w :=
  Silmaril.Wasm.Game.Accept.moduleBytesSystem_of_decode_none _ (by decide)

example (C : Silmaril.Wasm.Component.CoreSem Silmaril.Wasm.Component.Binary.CoreMod)
    (w : List UInt8) : ¬ componentBytesSystem C .imp truncatedBytes w :=
  componentBytesSystem_of_decode_none C .imp (by decide)

/-- The mixed system agrees with the module-only one on module bytes, at the default template. -/
example (C : Silmaril.Wasm.Component.CoreSem Silmaril.Wasm.Component.Binary.CoreMod) (L : Layout)
    (w : List UInt8) :
    ByteAcceptor.bytesSystem (ModuleAcceptor.default .spec) C L acceptFn none .imp
        emptyModuleBytes w ↔
      Silmaril.Wasm.Game.Accept.moduleBytesSystem .spec emptyModuleBytes w :=
  (ByteAcceptor.bytesSystem_of_decode_module _ C L acceptFn none .imp decode_emptyModuleBytes w).trans
    (Silmaril.Wasm.Game.Accept.moduleBytesSystem_of_decode _ decode_emptyModuleBytes).symm

/-- Lowered names: the world-level `accept` import or export is `acceptFn`. -/
example : fnNameOf "accept" = acceptFn := rfl

end Silmaril.Wasi.Accept.ConsequenceExamples
