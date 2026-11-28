module

import Silmaril.Formats.Parquet.BitPackedLevels.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Bytes
meta import Silmaril.Formats.Parquet.BitPackedLevels.Defs
meta import Batteries.Data.Except

/-! Pinned parquet-java producer/consumer sections, with next-section sentinels. -/

namespace Silmaril.Formats.Parquet.BitPackedLevels

private structure Vector where
  name : String
  maxLevel : Nat
  packed : Bytes
  following : Bytes
  javaRead : List Nat

private def sentinel : Bytes := .ofList [0xa5, 0x5a]
private def nullableMask : List Nat := [1, 0, 1, 1, 0]
private def group : Bytes := .ofList [0x05, 0x39, 0x77]
private def limits : Limits := ⟨16, 16⟩

private def producer (name : String) (maxLevel : Nat) (packed : Bytes) (levels : List Nat) :
    Vector :=
  ⟨name, maxLevel, packed, sentinel, levels⟩

private def valid : List Vector := [
  producer "zero-width" 0 .empty [0, 0, 0],
  producer "zero-count" 7 .empty [],
  producer "nullable-mask" 1 (.ofList [0xb0]) nullableMask,
  producer "non-power-of-two-bound" 2 (.ofList [0x86, 0]) [2, 0, 1, 2, 0],
  producer "spec-group" 7 group (List.range 8),
  producer "second-group" 7 (group.push 0x20) (List.range 8 ++ [1]),
  producer "signed-max-level" 2147483647
    (.ofList [0xff, 0xff, 0xff, 0xfe, 0, 0, 0, 0, 0, 0, 0, 8]) [2147483647, 0, 1]]

private def dirtyPadding : Vector :=
  ⟨"unused-low-bits", 1, .ofList [0xb7], sentinel, nullableMask⟩

private def spareCode : Vector := ⟨"spare-code", 2, .ofList [0xc0], sentinel, [3]⟩

private def short : Vector := ⟨"truncated", 7, group, .empty, List.range 8 ++ [0]⟩

private def hex (bytes : Bytes) : String :=
  if bytes.length = 0 then "-"
  else String.ofList (bytes.toList.flatMap fun b => [(b.toNat / 16).digitChar, (b.toNat % 16).digitChar])

private def fixtureLine (kind : String) (vector : Vector) : String :=
  String.intercalate "\t" [kind, vector.name, toString vector.maxLevel, toString vector.javaRead.length,
    hex vector.packed, hex vector.following,
    if vector.javaRead.isEmpty then "-" else String.intercalate "," (vector.javaRead.map toString)] ++ "\n"

#guard (include_str "../../../../tests/formats/parquet-bit-packed-levels/parquet-java-1.16.0.tsv") =
  String.join (valid.map (fixtureLine "producer")) ++
  String.join ([dirtyPadding, spareCode, short].map (fixtureLine "consumer"))

private def run (vector : Vector) : Except Error (List Nat × Bytes) :=
  readPrefix vector.maxLevel vector.javaRead.length limits (vector.packed.append vector.following)

#guard valid.all (fun vector => run vector == .ok (vector.javaRead, vector.following))
#guard run dirtyPadding = .ok (nullableMask, sentinel)
#guard run spareCode = .error .levelOutOfRange
#guard run short = .error .truncated

#guard readPrefix 1 5 ⟨4, 16⟩ (.ofList [0xb0]) = .error .countLimit
#guard readPrefix 7 9 ⟨16, 3⟩ (group.push 0x20) = .error .byteLimit
#guard readPrefix 0 3 ⟨3, 0⟩ sentinel = .ok ([0, 0, 0], sentinel)
#guard readPrefix 0 3 ⟨2, 0⟩ sentinel = .error .countLimit
#guard readPrefix signedLimit 0 limits .empty = .error .invalidMaxLevel
#guard readPrefix 0 signedLimit ⟨signedLimit, 0⟩ .empty = .error .countLimit
#guard readExact 1 5 limits (.ofList [0xb7]) = .ok nullableMask
#guard readExact 1 5 limits ((Bytes.ofList [0xb7]).append sentinel) = .error .trailingBytes

end Silmaril.Formats.Parquet.BitPackedLevels
