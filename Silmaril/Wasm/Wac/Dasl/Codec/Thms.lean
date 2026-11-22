module

public import Silmaril.Wasm.Wac.Dasl.Defs
import Silmaril.Proofs.Wasm.Wac.Dasl.Codec

@[expose] public section

namespace Silmaril.Wasm.Wac.Dasl

open Silmaril.Formats.Dasl
open Silmaril.Wasm.Component (ValTy)

variable {Name Ref Binary : Type}

theorem inline_recovers (item : Inline) : readInline (embedInline (Ref := Ref) (Name := Name) item) = some item :=
  Proofs.Wasm.Wac.Dasl.Codec.inline_roundtrip item

theorem source_recovers (item : Src) : srcRead (srcWrite item) = some item :=
  Proofs.Wasm.Wac.Dasl.Codec.src_roundtrip item

theorem type_recovers (item : ValTy) : typeRead (typeWrite item) = some item :=
  Proofs.Wasm.Wac.Dasl.Codec.type_roundtrip item

def inlineCodec : Encode.TotalCodec Inline (Tree Ref Name) :=
  ⟨embedInline, readInline, inline_recovers⟩

def sourceCodec : Encode.TotalCodec Src Inline := ⟨srcWrite, srcRead, source_recovers⟩

def typeCodec : Encode.TotalCodec ValTy Inline := ⟨typeWrite, typeRead, type_recovers⟩

def codec (binary : Encode.TotalCodec Binary (Tree Ref Name)) : Encode.TotalCodec (Composition Binary) (Tree Ref Name) :=
  composition ((graph typeCodec sourceCodec).then inlineCodec) ((signature typeCodec).then inlineCodec) binary

/-- The wire-neutral object codec, with exactly one raw link per package row. -/
def shallow : Encode.TotalCodec (Composition Name) (Shallow Name) := codec rawLink

/-- The expanded codec recovers the same graph, each raw name, and its raw bytes. -/
def expanded : Encode.TotalCodec (Composition (Name × ByteArray)) (Named Name) := codec rawBlob

end Silmaril.Wasm.Wac.Dasl
