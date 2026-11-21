module

public import Mathlib.Data.List.Lex
public import Silmaril.Formats.Dasl.Encode.Map.Thms
public import Silmaril.Formats.Dasl.Resolve.Defs
public import Silmaril.Semantics.Prolly.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.Prolly

open Silmaril.Semantics.Prolly

variable {Name Key Payload : Type}

/-- Byte strings in unsigned bytewise lexicographic order, including prefix keys. -/
abbrev ByteKey := List (Fin 256)

scoped instance : LinearOrder Int64 := LinearOrder.lift' Int64.toInt (fun _ _ same => Int64.toInt.inj same)

def byteKey : Encode.TotalCodec ByteKey (Shallow Name) :=
  (show Encode.TotalCodec ByteKey ByteArray from
    ⟨fun key => (key.map UInt8.ofFin).toByteArray, fun bytes => some (bytes.data.toList.map UInt8.toFin),
      fun key => by simp [List.map_map, Function.comp_def]⟩).then Encode.bytes

def intKey : Encode.TotalCodec Int64 (Shallow Name) := Encode.signed

def objectLink : Encode.TotalCodec Name (Shallow Name) :=
  ⟨fun name => .ref (.obj name), (fun | .ref (.obj name) => some name | _ => none), fun _ => rfl⟩

def entriesCodec (key : Encode.TotalCodec Key (Shallow Name)) (payload : Encode.TotalCodec Payload (Shallow Name)) :
    Encode.TotalCodec (List (Key × Payload)) (Shallow Name) :=
  Encode.listOf ((key.prod payload).then Encode.pairEntry)

/-- Project-local block profile. A branch level is a strictly positive signed-profile i64.
This grammar checks block syntax, not the order or separator correctness of a stored tree. -/
def encodeBlock (key : Encode.TotalCodec Key (Shallow Name)) (payload : Encode.TotalCodec Payload (Shallow Name)) :
    Block Name Key Payload → Option (Shallow Name)
  | .leaf entries => some (Encode.list.encode [.string "leaf", (entriesCodec key payload).encode entries])
  | .branch level children =>
    if 0 < level ∧ level < 2^63 then some (Encode.list.encode
      [.string "branch", .i64 (UInt64.ofNat level), (entriesCodec key objectLink).encode children])
    else none

def decodeBlock (key : Encode.TotalCodec Key (Shallow Name)) (payload : Encode.TotalCodec Payload (Shallow Name)) :
    Shallow Name → Option (Block Name Key Payload)
  | .list 2 values =>
    match values 0 with
    | .string "leaf" => ((entriesCodec key payload).decode? (values 1)).map Block.leaf
    | _ => none
  | .list 3 values =>
    match values 0, values 1 with
    | .string "branch", .i64 level =>
      if 0 < level.toNat ∧ level.toNat < 2^63 then
        ((entriesCodec key objectLink).decode? (values 2)).map (Block.branch level.toNat)
      else none
    | _, _ => none
  | _ => none

/-- The stored presentation includes an encoding witness at every referenced block,
so unsupported block encodings cannot be silently dropped from the specification. -/
def Stored (codec : Encode.PartialCodec (Block Name Key Payload) (Shallow Name))
    (address : Block Name Key Payload → Name) (tree : Semantics.Prolly.Tree Key Payload) (store : Store Name) : Prop :=
  ∀ block ∈ blockOccurrences address tree.level tree.root,
    ∃ value, codec.encode? block = some value ∧ store.objects (address block) value

end Silmaril.Formats.Dasl.Prolly
