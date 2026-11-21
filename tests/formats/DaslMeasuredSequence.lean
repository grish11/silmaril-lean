module

import Silmaril.Formats.Dasl.MeasuredSequence.Thms
import Silmaril.Formats.Dasl.Wire.Defs
meta import Silmaril.Formats.Dasl.MeasuredSequence.Thms
meta import Silmaril.Formats.Dasl.Wire.Defs

open Silmaril.Formats.Dasl
open Silmaril.Formats.Dasl.MeasuredSequence
open Silmaril

private def check (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

private def expect {Value : Type} (value : Option Value) (label : String) : IO Value :=
  match value with
  | some value => pure value
  | none => throw (IO.userError label)

public def main : IO Unit := do
  let item : Encode.TotalCodec Int64 (Shallow Wire.Cid) := Encode.signed
  let raw := rawCodec item
  let normalized := normalizedCodec item
  let right := Semantics.MeasuredSequence.ofList ([-1, 7, 9] : List Int64)
  let left := Semantics.MeasuredSequence.append (Semantics.MeasuredSequence.ofList ([-1, 7] : List Int64)) (.one 9)
  let leftRaw ← expect (raw.decode? (encodeShape item left)) "valid left shape"
  let rightRaw ← expect (raw.decode? (encodeShape item right)) "valid right shape"
  check (decide (leftRaw.val = left ∧ rightRaw.val = right ∧ left ≠ right)) "exact raw recovery"
  let wireRaw ← expect (Wire.render? (raw.encode leftRaw)) "render inline shape"
  let wireRight ← expect (Wire.render? (raw.encode rightRaw)) "render alternate shape"
  check (wireRaw != wireRight) "raw bytes preserve joins"
  check (decide ((Wire.parse? wireRaw).bind raw.decode? = some leftRaw)) "wire raw recovery"
  let canonical := Wire.render? (encodeNormalized item left)
  check (canonical == some ⟨#[0x83, 0x20, 0x07, 0x09]⟩) "canonical ordered DASL array"
  check (canonical == Wire.render? (encodeNormalized item right)) "joins do not affect canonical bytes"
  check (decide ((canonical.bind Wire.parse?).bind normalized.decode? = some (rebuild left))) "midpoint rebuild"
  let stale : Semantics.MeasuredSequence.Tree Int64 := .branch 99 (.one 7) (.one 9)
  let recovered ← expect (raw.decode? (encodeShape item stale)) "derived measure"
  check (decide (recovered.val = .branch 2 (.one 7) (.one 9))) "no cached measure is accepted from wire"
  check ((raw.decode? (branchShape .null (.list 1 (fun _ => .i64 9)))).isNone) "empty child"
  check ((raw.decode? (.list 1 (fun _ => .bool true))).isNone) "wrong payload type"
  check ((raw.decode? (.list 3 (fun _ => .i64 9))).isNone) "wrong branch arity"
  check (decide (raw.decode? .null = some ⟨.empty, trivial⟩)) "raw empty"
  check (decide (normalized.decode? (.list 0 Fin.elim0) = some (rebuild (.empty : Semantics.MeasuredSequence.Tree Int64))))
    "normalized empty"
  let tag (kind : UInt8) := ([0xD8, 0x2A, 0x58, 37, 0, 1, kind, 0x12, 32] ++ List.replicate 32 0).toByteArray
  let some (.ref (.obj obj)) := Wire.parse? (tag 0x71) | throw (IO.userError "object CID")
  let some (.ref (.blob blob)) := Wire.parse? (tag 0x55) | throw (IO.userError "blob CID")
  let child ← expect (raw.decode? (encodeShape item (Semantics.MeasuredSequence.ofList [(-1 : Int64), 7]))) "resolved child"
  let resolve name := if name = obj then some child else none
  let linked := branchShape (.ref (.obj obj)) (encodeShape item (.one 9))
  let linkedBytes ← expect (Wire.render? linked) "render shape with an object child"
  let linkedShape ← expect (Wire.parse? linkedBytes) "parse shape with an object child"
  check (decide (decodeShape? item resolve linkedShape = some leftRaw)) "resolved child preserves raw shape"
  check ((raw.decode? linkedShape).isNone) "missing child is not empty"
  check ((decodeShape? item resolve (branchShape (.ref (.blob blob)) (encodeShape item (.one 9)))).isNone)
    "blob link is not a subtree"
  check ((Wire.render? (branchShape (.ref (.obj blob)) (encodeShape item (.one 9)))).isNone) "wrong CID kind"
  check (((normalizeShape? item resolve linkedShape).bind Wire.render?) == canonical) "normalize resolved shape"
