module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Canon.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitCanon

/-!
# Payload decoding against the pure canonical ABI reference loaders

The decoder of `Callout.witNode` (`readVal`, `readFields`, `readVals`, at the call's memory:
`loadVals`, `witNode_loadVals`) compared with the **pure** (non-monadic) loaders of the
canonical ABI reference in `Silmaril.Wasm.Component.Reference.ABI`, memory32, UTF-8:

* **Scalar payload vectors** (`bool`, `s32`, `u32`, `s64`, `u64` only: `SPTy`):
  `loadVals_loadRecord`: the payload vector at `ptr` is `ABI.loadRecord` (REF `load_record` for
  integer and boolean fields: record alignment and full bounds, tail padding included, each field
  at `alignTo cursor (alignment t)`, little-endian, `bool` any nonzero byte), **as an equation
  of options**: the same values (`SPTy.toScalarValues`, injective by `toScalarValues_injective`)
  or the same failure (misaligned `ptr`, bytes out of bounds).
* **Strings**: `readPtrLen_load`: the `(ptr, len)` pair at `a` is the two reference loads
  `ABI.Scalar.load .u32` at `a` and `a + 4` (or the same failure);
  `readVal_string_loadStringFromRange`: given that pair, the string payload is
  `ABI.loadStringFromRange? .utf8 .i32` (REF `load_string_from_range`) **whenever
  `len ≤ ABI.maxStringByteLength`**: the same text (with the reference's `encoding = utf8`,
  `tagged_code_units = len`) or the same failure (out of bounds, invalid UTF-8); the reference
  alignment check is vacuous for UTF-8 (alignment `1`). **Above `maxStringByteLength`
  (`2^28 - 1` bytes) the reference traps and the decoder does not check**: it reads any in-bounds
  length.

## What is not related to a reference loader

* `bytes` (`list<u8>`) and `list t`: the repository has **no pure reference list loader**
  under `Reference/ABI/` (`Memory/Defs.lean` loads only scalar records, `String/Defs.lean` only
  strings). REF `load_list`/`load_list_from_range`/`load_list_from_valid_range` exist only as the
  monadic `Canon.Load.loadList`/`loadListFromRange`/`loadListFromValidRange` programs over a
  component store (`Silmaril.Wasm.Component.Reference.Canon.Load`), which are not compared here.
  In particular the decoder does not check REF `MAX_LIST_BYTE_LENGTH` (`listTooLong`).
* Mixed vectors (a scalar beside a string or list) are not stated as one record equation:
  `loadRecord` has only scalar fields. Each field of such a vector is read at its canonical
  offset (`readFields`), so the per-field theorems above apply to its bytes.
* No statement relates the decoder to the monadic `Canon.load`/`loadRecord`/`loadString`
  (component store, `LiftLowerContext`, `Limits`, `Quirks`), to flattening into core arguments
  (`ABI.flatten`: payloads always go through memory), or to the `utf16`/`latin1+utf16` string
  encodings.

New statements (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst

open Silmaril.Formats Silmaril.Wasm.Component Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.Accept

/-! ## The payload of `node` -/

/-- A call observing the memory `mem` reads its segments from `mem`. -/
theorem segment_eq_segOf {o : Callout} {mem : ByteArray} (hm : o.mem = some mem) :
    o.segment = segOf mem :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.segment_eq_segOf hm

/-- **The payload a decoded `node` names is `loadVals`** at its payload pointer: every node the
decoder admits has the payload vector that `loadVals` reads from the call's memory. -/
theorem witNode_loadVals (S : WitSig) (tagOf : BitVec 32 → Option S.Tag) {o : Callout}
    {mem : ByteArray} (hm : o.mem = some mem) {op : Σ t, S.toAstSig.Arg t}
    {hs : List (BitVec 32)} (h : Callout.witNode S tagOf o = some (op, hs)) :
    ∃ pp : BitVec 32, o.args[1]? = some (Execution.Core.Val.i32 pp) ∧
      loadVals mem (S.params op.1) pp.toNat = some op.2 :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.witNode_loadVals S tagOf hm h

/-! ## Scalar payload vectors -/

/-- **Scalar payload vectors are `ABI.loadRecord`** (memory32): the same values or the same
failure. -/
theorem loadVals_loadRecord (mem : ByteArray) (qs : List SPTy) (ptr : Nat) :
    (loadVals mem (qs.map SPTy.pty) ptr).map (SPTy.toScalarValues qs) =
      ABI.loadRecord (qs.map SPTy.scalar) mem ptr :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.loadVals_loadRecord mem qs ptr

/-- The scalar layout of a scalar payload vector is its payload layout. -/
theorem scalarRecordLayout_eq (qs : List SPTy) :
    ABI.scalarRecordLayout (qs.map SPTy.scalar) = valsLayout (qs.map SPTy.pty) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.scalarRecordLayout_eq qs

/-- The translation of a scalar payload value loses nothing. -/
theorem toScalarValue_injective (q : SPTy) : Function.Injective q.toScalarValue :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.toScalarValue_injective q

/-- The translation of a scalar payload vector loses nothing. -/
theorem toScalarValues_injective (qs : List SPTy) :
    Function.Injective (SPTy.toScalarValues qs) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.toScalarValues_injective qs

/-! ## Strings -/

/-- **A `(ptr, len)` pair is the two reference `u32` loads** (or the same failure). -/
theorem readPtrLen_load (mem : ByteArray) (a : Nat) :
    (segOf mem a 8).bind readPtrLen =
      (ABI.Scalar.load .u32 mem a).bind fun p =>
        (ABI.Scalar.load .u32 mem (a + 4)).map fun n => (p.bits.toNat, n.bits.toNat, []) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.readPtrLen_load mem a

/-- **A string payload is `ABI.loadStringFromRange?`** (UTF-8, memory32): for
`len ≤ maxStringByteLength` the same text or the same failure (bounds, invalid UTF-8); above it
the reference fails, while the decoder does not check the limit. -/
theorem readVal_string_loadStringFromRange (mem : ByteArray) {bs rest : List UInt8} {p n : Nat}
    (hp : readPtrLen bs = some (p, n, rest)) :
    (ABI.loadStringFromRange? .utf8 .i32 mem.data.toList p n).map (fun v => (v, rest)) =
      if n ≤ ABI.maxStringByteLength then
        (readVal (segOf mem) .string bs).map fun x => (⟨x.1, .utf8, n⟩, x.2)
      else none :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.readVal_string_loadStringFromRange mem hp

end Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst
