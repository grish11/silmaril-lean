module

import Silmaril.Containers.Cas.Blake3.Thms
import Silmaril.Crypto.Blake3.Range.Check.Defs
meta import Silmaril.Crypto.Blake3.Range.Check.Defs

open Silmaril.Crypto.Blake3
open Silmaril.Semantics.Naming.ByteRange (Slice Partial ofWhole)

private def run : Input → Option CV := some ∘ compress32

private def testInput (size : Nat) : Bytes := (List.range size).map (fun pos => UInt8.ofNat (pos % 251))

private def hex (bytes : Bytes) : String :=
  let digit (n : Nat) := Char.ofNat (if n < 10 then 48 + n else 87 + n)
  String.ofList (bytes.flatMap (fun byte => [digit (byte.toNat / 16), digit (byte.toNat % 16)]))

example : (hash? run (testInput 0)).map hex = some
    "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262" := by decide +kernel

example : chunkInput true true true 0 iv [] = ⟨iv, paddedBlock [], 0, 0, 11⟩ := by decide +kernel
example : (chunkInput false true false 19 iv []).counter = 19 := by decide +kernel
example (left right : CV) : parentInput true left right = ⟨iv, left ++ right, 0, 64, 12⟩ := rfl

example {Name : Type} {rel : Silmaril.Semantics.Naming.Relation Name Bytes} {name : Name}
    (named : rel name [10, 20, 30]) : Partial rel name 2 [30] :=
  (ofWhole named (offset := 1) (fragment := [20, 30]) ⟨[10], [], rfl, rfl⟩).sub ⟨[20], [], rfl, rfl⟩

#eval show IO Unit from do
  for (size, expected) in
      [(65, "de1e5fa0be70df6d2be8fffd0e99ceaa8eb6e8c93a63f2d8d1c30ecb6b263dee"),
       (1024, "42214739f095a406f3fc83deb889744ac00df831c10daa55189b5d121c855af7"),
       (1025, "d00278ae47eb27b34faecf67b4fe263f82d5412916c1ffd97c8cb7fb814b8444"),
       (2049, "5f4d72f40d7a5f82b15ca2b2e44b1de3c2ef86c426c95c1af0b6879522563030"),
       (3073, "7124b49501012f81cc7f11ca069ec9226cecb8a2c850cfe644e327d22d3e1cd3")] do
    unless (hash? run (testInput size)).map hex == some expected do
      throw (IO.userError s!"BLAKE3 vector mismatch at {size} bytes")

private def payload := testInput 1025
private def digest := (hash? run payload).getD []
private def wholeOpening := disclose (geometry 0 1025) payload
private def leftCV := (eval? run false (.leaf 0 1024) (.leaf (payload.take 1024))).getD iv
private def suffixOpening : Opening := .fork (.opaque leftCV) (.leaf [20])
private def rightCV := (eval? run false (.leaf 1 1) (.leaf [20])).getD iv
private def prefixOpening : Opening := .fork (.leaf (payload.take 1024)) (.opaque rightCV)

private def readTest (opening : Opening) (offset count : Nat) : Option Bytes :=
  (verifyRange? run 1025 1025 digest opening offset count).map Subtype.val

#eval show IO Unit from do
  for (label, actual, expected) in
      [("disclosed suffix", readTest suffixOpening 1024 1, some [20]),
       ("opaque sibling", readTest suffixOpening 1023 1, none),
       ("empty range at EOF", readTest suffixOpening 1025 0, some []),
       ("past EOF", readTest suffixOpening 1026 0, none),
       ("across a chunk boundary", readTest wholeOpening 1023 2, some [19, 20]),
       ("wrong bytes", readTest (.fork (.opaque leftCV) (.leaf [0])) 1024 1, none),
       ("wrong chunk length", readTest (.fork (.opaque leftCV) (.leaf [])) 1024 1, none),
       ("opaque root", readTest (.opaque leftCV) 1024 1, none),
       ("extent cap", (verifyRange? run 1024 1025 digest wholeOpening 0 1).map Subtype.val, none),
       ("disclosed prefix", readTest prefixOpening 0 1, some [0]),
       ("same prefix, different claimed extent",
          (verifyRange? run 1026 1026 digest prefixOpening 0 1).map Subtype.val, some [0])] do
    unless actual == expected do throw (IO.userError s!"BLAKE3 range mismatch: {label}")

example {whole fragment : Bytes} {size offset : Nat} {name : Bytes}
    (checked : Checked concrete size name offset fragment) (actual : hash? run whole = some name)
    (length : whole.length = size) :
    Slice whole offset fragment ∨ ∃ left right : Input, left ≠ right ∧ compress32 left = compress32 right :=
  (checked.sliceOrCollision (root_graph.mp actual) length).imp id concrete_collision_iff.mp

private def constantRun (_ : Input) : Option CV := some iv

example : Compression.Collision (Compression.graph constantRun) := by
  have lhs : Root (Compression.graph constantRun) 1 (digestBytes iv) (.leaf [1]) :=
    root_graph.mp (by decide +kernel)
  have rhs : Root (Compression.graph constantRun) 1 (digestBytes iv) (.leaf [2]) :=
    root_graph.mp (by decide +kernel)
  rcases lhs.agreeOrCollision rhs with agree | collision
  · cases agree
  · exact collision

private def openEOF (shape : Shape) (bytes : Bytes) : Option Opening :=
  match shape with
  | .leaf .. => some (.leaf bytes)
  | .fork left right => do
    let prefixBytes := bytes.take left.size
    let leftCV ← eval? run false left (disclose left prefixBytes)
    let tail ← openEOF right (bytes.drop left.size)
    return .fork (.opaque leftCV) tail

#eval show IO Unit from do
  for size in [0, 1, 64, 65, 128, 129, 1024, 1025, 2048, 2049, 3072, 3073, 4096, 4097] do
    let bytes := testInput size
    let some name := hash? run bytes | throw (IO.userError s!"hash failed at {size} bytes")
    let some edge := openEOF (geometry 0 size) bytes | throw (IO.userError s!"EOF opening failed at {size} bytes")
    let count := min size 1
    let hit := verifyRangeWithEOF? run size size name edge (size - count) count
    unless (hit.map Subtype.val) == some (bytes.drop (size - count)) do
      throw (IO.userError s!"EOF/range mismatch at {size} bytes")

#eval show IO Unit from do
  unless (verifyEOF? run 1025 1025 digest suffixOpening).isSome do
    throw (IO.userError "a final-chunk opening should check EOF independently of the range")
  for size in [1025, 1026] do
    unless (verifyRangeWithEOF? run size size digest prefixOpening 0 1).isNone do
      throw (IO.userError s!"the opaque last chunk must not authenticate {size} bytes")
  unless (verifyEOF? run 1026 1026 digest (.fork (.opaque leftCV) (.leaf [20, 0]))).isNone do
    throw (IO.userError "identical padded blocks with different final block lengths cannot share this digest")
  unless (verifyEOF? run 1024 1025 digest suffixOpening).isNone do
    throw (IO.userError "the extent cap should apply to EOF checking")

example {whole : Bytes} {size offset count : Nat} {name : Bytes}
    (actual : hash? run whole = some name)
    (accepted : {fragment : Bytes // Checked concrete size name offset fragment ∧
      CheckedEOF concrete size name ∧ fragment.length = count}) :
    Slice whole offset accepted.val ∨ ∃ left right : Input, left ≠ right ∧ compress32 left = compress32 right :=
  accepted.property.1.sliceOrConcreteCollisionOfEOF accepted.property.2.1 (root_graph.mp actual)

example {left right name : Bytes} (lh : hash? run left = some name) (rh : hash? run right = some name) :
    left = right ∨ ∃ lhs rhs : Input, lhs ≠ rhs ∧ compress32 lhs = compress32 rhs :=
  (Named.eqOrCollision (root_graph.mp lh) (root_graph.mp rh)).imp id concrete_collision_iff.mp

example : Compression.Collision (Compression.graph constantRun) := by
  have lhs : Named (Compression.graph constantRun) (digestBytes iv) (List.replicate 65 0) :=
    root_graph.mp (by decide +kernel)
  have rhs : Named (Compression.graph constantRun) (digestBytes iv) (List.replicate 129 0) :=
    root_graph.mp (by decide +kernel)
  have difference : (List.replicate 65 (0 : UInt8)).length ≠ (List.replicate 129 (0 : UInt8)).length := by decide
  exact (lhs.checkedEOF.extentOrCollision rhs).resolve_left difference
