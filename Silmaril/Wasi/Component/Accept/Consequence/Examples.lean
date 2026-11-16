module

public import Silmaril.Wasi.Component.Accept.Consequence.Thms
public import Silmaril.Wasi.Component.Accept.Acceptor.Examples
public import Silmaril.Wasm.Component.Binary.Encode.Defs

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
* **`list<u8>` versus `tuple<u8, u8>`**: both binaries parse; only the tuple lowers, so a typical
  `accept(list<u8>)` component proves nothing through `componentBytesSystem` today.
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

/-! ## `accept(list<u8>)` versus `accept(tuple<u8, u8>)`

Two component binaries, each importing one function `accept` and nothing else, built from their
abstract syntax with the verified encoder (`Binary.encode`, checked below). Upstream
`wasm-tools validate` 1.263.0 also accepts both. The parser reads both. The lowering into the
component IR, which every component acceptor reads, accepts only the tuple: the IR's value types
(`ValTy`) have no list type, and `Binary.lower` rejects `list` (`defValTy_list`). The gap is in
lowering and semantics, not in parsing. -/

/-- `(component (type (list u8)) (type (func (param "bs" 0))) (import "accept" (func (type 1))))`. -/
def acceptAst (t : Silmaril.Wasm.Component.Binary.DefValType) : Silmaril.Wasm.Component.Binary.Ast :=
  .mk [.types [.val t, .func ⟨[("bs", .idx 0)], none, false⟩], .imports [⟨"accept", .func 1⟩]]

/-- The binary of `acceptAst (list u8)`. -/
def listAcceptBytes : ByteArray := ⟨#[0x00, 0x61, 0x73, 0x6d, 0x0d, 0x00, 0x01, 0x00, 0x07, 0x0b,
  0x02, 0x70, 0x7d, 0x40, 0x01, 0x02, 0x62, 0x73, 0x00, 0x01, 0x00, 0x0a, 0x0b, 0x01, 0x00, 0x06,
  0x61, 0x63, 0x63, 0x65, 0x70, 0x74, 0x01, 0x01]⟩

/-- The binary of `acceptAst (tuple u8 u8)`. -/
def tupleAcceptBytes : ByteArray := ⟨#[0x00, 0x61, 0x73, 0x6d, 0x0d, 0x00, 0x01, 0x00, 0x07, 0x0d,
  0x02, 0x6f, 0x02, 0x7d, 0x7d, 0x40, 0x01, 0x02, 0x62, 0x73, 0x00, 0x01, 0x00, 0x0a, 0x0b, 0x01,
  0x00, 0x06, 0x61, 0x63, 0x63, 0x65, 0x70, 0x74, 0x01, 0x01]⟩

theorem encode_listAccept :
    Silmaril.Wasm.Component.Binary.encode (acceptAst (.list (.prim .u8))) = some listAcceptBytes := by
  decide +kernel

theorem encode_tupleAccept :
    Silmaril.Wasm.Component.Binary.encode (acceptAst (.tuple [.prim .u8, .prim .u8])) =
      some tupleAcceptBytes := by
  decide +kernel

/-- **The parser reads `list<u8>`** ... -/
theorem parse_listAcceptBytes : (Silmaril.Wasm.Component.Binary.parse listAcceptBytes).isOk = true := by
  decide +kernel

/-- ... **the lowering does not**, so the component decoder fails ... -/
theorem decodeBinary_listAcceptBytes : ComponentAcceptor.decodeBinary listAcceptBytes = none := by
  decide +kernel

/-- ... and a `list<u8>` acceptor proves nothing in `componentBytesSystem`, for every core
semantics: a genuine gap of the component IR, not of the parser. -/
example (C : Silmaril.Wasm.Component.CoreSem Silmaril.Wasm.Component.Binary.CoreMod) (mode : Mode)
    (w : List UInt8) : ¬ componentBytesSystem C mode listAcceptBytes w :=
  componentBytesSystem_of_decode_none C mode decodeBinary_listAcceptBytes

/-- The tuple acceptor lowers: its one import is `acceptFn`, at the IR type `record [u8, u8]`. -/
theorem decodeBinary_tupleAcceptBytes :
    (ComponentAcceptor.decodeBinary tupleAcceptBytes).map (fun c => (Layout.ofComp c).imports) =
      some [acceptFn] := by
  decide +kernel

example : (ComponentAcceptor.decodeBinary tupleAcceptBytes).map
    (fun c => c.imports.map (·.2.params)) =
      some [[.record [.u8, .u8]]] := by
  decide +kernel

end Silmaril.Wasi.Accept.ConsequenceExamples
