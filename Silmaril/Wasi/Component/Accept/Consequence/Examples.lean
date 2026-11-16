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

end Silmaril.Wasi.Accept.ConsequenceExamples
