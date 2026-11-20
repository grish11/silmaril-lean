module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Cons.Thms
public import Silmaril.Wasm.Verify.Kernel.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAstLive
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAppLive
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitBinLive
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitGlyphLive

/-!
# Typed payloads and fixed arities through linear memory: soundness and non-vacuity

**The canonical ABI layout** (`layout_toWit`, `width_toWit`, `align_toWit`, `valsLayout_toWit`,
`valsWidth_toWit`, `valsAlign_toWit`): the layout of a payload type is `ABI.layout .i32` of its
WIT type `Wit.toWit t` (REF `elem_size`, `alignment`), and the layout of a payload vector is that
of the WIT tuple of its types, for the whole payload domain (records, tuples, variants,
options, results, enums, flags, fixed-length lists, narrow integers, floats, chars); kernel-checked
sizes with padding `ex_width_*` (`ex_width_glyph`, `ex_width_option_u64`, `ex_width_result`,
`ex_width_variant`, `ex_width_enum257`, `ex_width_flags`, `ex_width_fixed`, …).

**Payloads** (`readPtrLen_encode`, `readVal_rest`, `readVal_string`, `readVal_bytes`,
`readVal_list`, `readVal_list_misaligned`, `readVals_single`): a `(ptr, len)` pair written as
two little-endian `i32`s is read back; every payload value consumes exactly `PTy.width t` bytes;
strings, byte strings and lists are read through their pair from the memory at the call, lists
only at an aligned pointer. Kernel-checked examples over the memory `exMem` (`listSeg`):
`ex_string`, `ex_string_utf8` (two-byte UTF-8), `ex_bytes`, `ex_bytes_not_utf8`, `ex_list_u32`,
`ex_list_string` (two levels of indirection), `ex_list_list` (`list<list<u32>>`), `ex_vals`
(`u32` then `string`), `ex_vals_padded` (`bool` then `u32`: three padding bytes, not read),
`ex_vals_padded64` (`u32` then `s64`); the rest of the domain: `ex_s8`, `ex_u16`, `ex_s16`,
`ex_bool_two` (any nonzero byte is `true`), `ex_f32`, `ex_f64`, `ex_f32_nan`, `ex_f64_nan`
(**NaNs are canonicalised**), `ex_char`, `ex_char_astral`, `ex_fixed`, `ex_tuple`, `ex_record`,
`ex_option_none`, `ex_option_string`, `ex_variant`, `ex_variant_a`, `ex_enum`, `ex_result_ok`,
`ex_result_err`, `ex_flags`, `ex_flags_high` (**bits above the label count are ignored**),
`ex_list_tuple`, `ex_vals_glyph`. `readVal_bytes`: `bytes` is `list<u8>`, read byte for byte.

**Malformed inputs decode to no value** (`ex_bad_utf8`, `ex_out_of_bounds`, `ex_list_oob`,
`ex_list_misaligned`, `ex_list_string_bad_utf8`, `ex_list_string_oob`,
`ex_list_list_misaligned`, `ex_short`; **invalid chars** `ex_char_surrogate`, `ex_char_too_big`,
`ex_record_bad_char`; **invalid discriminants** `ex_option_bad_disc`, `ex_record_bad_disc`,
`ex_variant_bad_disc`, `ex_enum_bad_disc`, `ex_result_bad_disc`; `ex_option_string_bad_utf8`,
`ex_fixed_short`, `ex_list_tuple_misaligned`), and **malformed calls to no event** (`ex_node_*` over
`exCall`: misaligned payload or child pointers, a payload area out of bounds, a string payload
out of bounds or invalid UTF-8, a wrong child count for a fixed arity; with the well-formed
controls `ex_node_num`, `ex_node_add`, `ex_node_var`). `witWrite_none`: a call the decoder
rejects has no write event (whatever its answer), so under the bridges it never makes a handle
denote a tree: the module gains nothing from it.

**Arities** (`witNode_admits`, `witWrite_admits`): every `node` call the decoder reads, hence
every decoded write, has a number of children admitted by its tag's arity.

**Bridges** (`witFixedLang_subset`, `witWriterLang_subset`): the generic role bridges at the
typed AST roles `witRoles S tagOf` and the writer `astW S.toAstSig`, for every WIT-typed
signature `S`.

**The example `calcMod`** (`node(0, 16, 0, 0)` over the `s64` `1` stored at `[16, 24)`, the same
over `2`, both handles stored at `[0, 8)`, `node(1, 0, 0, 2)`, `accept`), for every profile,
against every environment admitted by `hiReply`:

* `calcMod_fixed_sound`: in every fixed environment and for every policy without a sentinel, it
  accepts only `add(num 1, num 2)`;
* `calcMod_sound`: the same for the writer language (no sentinel, no undefined behaviour);
* `calcMod_live`: it accepts `add(num 1, num 2)`, for every policy (traced session against the
  counting host);
* `calcMod_lang`: **its writer language is exactly `{add(num 1, num 2)}`** (no sentinel, no
  undefined behaviour).

**The example `appMod`** (string payloads: `"f"` stored at `[24, 25)` and the pair `(24, 1)` at
`[16, 24)` right before `node(0, 16, 0, 0)`, the same with `"x"`, both handles at `[0, 8)`,
`node(1, 0, 0, 2)`, `accept`), for every profile, against every environment admitted by
`hiReply`: `appMod_fixed_sound`, `appMod_sound` (Hoare proof `app_sat`), `appMod_live` (traced
session against the counting host), `appMod_lang`: **its writer language is exactly
`{app(var "f", var "x")}`** (no sentinel, no undefined behaviour).

**The example `binMod`** (a byte string and a list: the byte `FF` at `[24, 25)` and the pair
`(24, 1)` at `[16, 24)` right before `node(0, 16, 0, 0)`; the `u32`s `7`, `9` at `[24, 32)` and
the pair `(24, 2)` right before `node(1, 16, 0, 0)`; both handles at `[0, 8)`,
`node(2, 0, 0, 2)`, `accept`): `binMod_fixed_sound`, `binMod_sound` (Hoare proof `bin_sat`),
`binMod_live` (traced session), `binMod_lang`: **its writer language is exactly
`{pair(blob [0xFF], seq [7, 9])}`** (no sentinel, no undefined behaviour).

**The example `glyphMod`** (a record with a `char` and an `option<u8>`: the record
`{ ch: 'a', size: some(7) }` as one `i64` at `[16, 24)` right before `node(0, 16, 0, 0)`, the
same with `{ ch: 'λ', size: none }`, both handles at `[0, 8)`, `node(1, 0, 0, 2)`, `accept`):
`glyphMod_fixed_sound`, `glyphMod_sound` (Hoare proof `glyph_sat`), `glyphMod_live` (traced
session), `glyphMod_lang`: **its writer language is exactly
`{pair(glyph { 'a', some(7) }, glyph { 'λ', none })}`** (no sentinel, no undefined behaviour).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept.IO Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Cons Silmaril.Wasm.Game.HandleAccept.MemSound.Hi
  Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api Silmaril.Wasm.Component
open Silmaril.Wasm.Game.HandleAccept.Wit (toWit toWitList)

/-! ## The canonical ABI layout -/

section Layout

/-- **The layout of a payload type is its canonical ABI layout** (memory32). -/
theorem layout_toWit (t : PTy) :
    ABI.layout .i32 (toWit t : WIT.ClosedType Nat) = PTy.layout t :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.layout_toWit t

/-- The mode-dependent layout agrees with the canonical layout at both address widths. -/
theorem layoutFor_toWit (address : AddrType) (type : PTy) :
    PTy.layoutFor address type = ABI.layout address (toWit type) := by
  cases address
  · exact (layout_toWit type).symm
  · rfl

/-- The size of a payload value is REF `elem_size` of its WIT type. -/
theorem width_toWit (t : PTy) :
    (ABI.layout .i32 (toWit t : WIT.ClosedType Nat)).size = PTy.width t := by
  rw [layout_toWit]; rfl

/-- The alignment of a payload value is REF `alignment` of its WIT type. -/
theorem align_toWit (t : PTy) :
    (ABI.layout .i32 (toWit t : WIT.ClosedType Nat)).alignment.bytes = PTy.align t := by
  rw [layout_toWit]; rfl

/-- **The layout of a payload vector is the canonical ABI layout of its WIT tuple.** -/
theorem valsLayout_toWit (ps : List PTy) :
    ABI.layout .i32 (.tuple (toWitList ps) : WIT.ClosedType Nat) = valsLayout ps :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.valsLayout_toWit ps

theorem valsWidth_toWit (ps : List PTy) :
    (ABI.layout .i32 (.tuple (toWitList ps) : WIT.ClosedType Nat)).size = valsWidth ps := by
  rw [valsLayout_toWit]; rfl

theorem valsAlign_toWit (ps : List PTy) :
    (ABI.layout .i32 (.tuple (toWitList ps) : WIT.ClosedType Nat)).alignment.bytes =
      valsAlign ps := by
  rw [valsLayout_toWit]; rfl

end Layout

/-- `(bool, u32)`: the `u32` at offset `4`, eight bytes aligned to four. -/
theorem ex_width_bool_u32 : valsWidth [.bool, .u32] = 8 ∧ valsAlign [.bool, .u32] = 4 := by
  decide

/-- `(u32, s64)`: the `s64` at offset `8`, sixteen bytes aligned to eight. -/
theorem ex_width_u32_s64 : valsWidth [.u32, .s64] = 16 ∧ valsAlign [.u32, .s64] = 8 := by
  decide

/-- `(s64, bool)`: seven bytes of tail padding. -/
theorem ex_width_s64_bool : valsWidth [.s64, .bool] = 16 := by decide

/-- `(bool, string)`: the pair at offset `4`. -/
theorem ex_width_bool_string :
    valsWidth [.bool, .string] = 12 ∧ valsAlign [.bool, .string] = 4 := by
  decide

/-- No payload: no bytes, alignment `1`. -/
theorem ex_width_nil : valsWidth [] = 0 ∧ valsAlign [] = 1 := by decide

/-- `(u8, s16)`: the `s16` at offset `2`. -/
theorem ex_width_u8_s16 : valsWidth [.u8, .s16] = 4 ∧ valsAlign [.u8, .s16] = 2 := by decide

/-- `record { ch: char, size: option<u8> }`: the option at offset `4` (discriminant at `4`,
payload at `5`), two bytes of tail padding. -/
theorem ex_width_glyph : PTy.width glyphTy = 8 ∧ PTy.align glyphTy = 4 := by decide

/-- `option<u64>`: a one-byte discriminant, the payload at offset `8`. -/
theorem ex_width_option_u64 : PTy.width (.option .u64) = 16 ∧
    caseOffset [none, some (PTy.layout .u64)] = 8 := by decide

/-- `result<u32>` (no error payload): the payload at offset `4`. -/
theorem ex_width_result : PTy.width (.result (some .u32) none) = 8 := by decide

/-- `variant { a, b(f64), c(char) }`: the largest payload (`f64`) at offset `8`. -/
theorem ex_width_variant :
    PTy.width (.variant [("a", none), ("b", some .f64), ("c", some .char)]) = 16 := by decide

/-- An `enum` of 257 cases has a two-byte discriminant (REF `discriminant_type`). -/
theorem ex_width_enum257 :
    PTy.width (.enum (List.replicate 257 "c")) = 2 ∧ discBytes 257 = 2 ∧ discBytes 256 = 1 := by
  decide +kernel

/-- `flags` of nine labels are two bytes; of seventeen, four. -/
theorem ex_width_flags : PTy.width (.flags (List.replicate 9 "f")) = 2 ∧
    PTy.width (.flags (List.replicate 17 "f")) = 4 := by decide

/-- `list<u16, 3>`: six bytes in place, aligned to two. -/
theorem ex_width_fixed :
    PTy.width (.fixedList .u16 3) = 6 ∧ PTy.align (.fixedList .u16 3) = 2 := by
  decide

/-! ## Payloads -/

/-- **A `(ptr, len)` pair is read back.** -/
theorem readPtrLen_encode (p n : BitVec 32) (rest : List UInt8) :
    readPtrLen ((Execution.Memory.encodeLE 4 p.toNat).data.toList ++
      (Execution.Memory.encodeLE 4 n.toNat).data.toList
      ++ rest) = some (p.toNat, n.toNat, rest) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.readPtrLen_encode p n rest

/-- **A payload value consumes exactly its width** of the payload area. -/
theorem readVal_rest {seg : Nat → Nat → Option (List UInt8)} {t : PTy} {bs rest : List UInt8}
    {v : t.Val} (h : readVal seg t bs = some (v, rest)) : rest = bs.drop (PTy.width t) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.readVal_rest h

/-- **A string payload**: its pair, the segment it names, the UTF-8 text. -/
theorem readVal_string {seg : Nat → Nat → Option (List UInt8)} {bs rest cs : List UInt8}
    {p n : Nat} {str : String} (hp : readPtrLen bs = some (p, n, rest))
    (hc : seg p n = some cs) (hu : Memory.utf8? cs = some str) :
    readVal seg .string bs = some (str, rest) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.readVal_string hp hc hu

/-- **A byte-string payload** (`list<u8>`): its pair and the `len` bytes it names. -/
theorem readVal_bytes {seg : Nat → Nat → Option (List UInt8)} {bs rest cs : List UInt8}
    {p n : Nat} (hp : readPtrLen bs = some (p, n, rest)) (hc : seg p n = some cs)
    (hl : cs.length = n) : readVal seg .bytes bs = some (cs, rest) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.readVal_bytes hp hc hl

/-- **A list payload**: its pair, an aligned pointer, the segment of `len` elements, the
elements. -/
theorem readVal_list {seg : Nat → Nat → Option (List UInt8)} {t : PTy}
    {bs rest es : List UInt8} {p n : Nat} {vs : List t.Val}
    (hp : readPtrLen bs = some (p, n, rest)) (ha : p % PTy.align t = 0)
    (hc : seg p (n * PTy.width t) = some es)
    (hm : readMany (readVal seg t) n es = some (vs, [])) :
    readVal seg (.list t) bs = some (vs, rest) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.readVal_list hp ha hc hm

/-- **A misaligned list is no value** (REF `trap_if(ptr != align_to(ptr, alignment))`). -/
theorem readVal_list_misaligned {seg : Nat → Nat → Option (List UInt8)} {t : PTy}
    {bs rest : List UInt8} {p n : Nat} (hp : readPtrLen bs = some (p, n, rest))
    (ha : p % PTy.align t ≠ 0) : readVal seg (.list t) bs = none :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.readVal_list_misaligned hp ha

/-- **A one-value payload vector** is its value, read from the first `t.width` bytes. -/
theorem readVals_single (seg : Nat → Nat → Option (List UInt8)) (t : PTy) (area : List UInt8) :
    readVals seg [t] area =
      (readVal seg t (area.take (PTy.width t))).map fun (v, _) => (v, ()) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.readVals_single seg t area

/-- The string `"hi"` through the pair `(8, 2)`. -/
theorem ex_string : readVal (listSeg exMem) .string [8, 0, 0, 0, 2, 0, 0, 0] =
    some ("hi", []) := by kernel_rfl

/-- A two-byte UTF-8 character: `"é"` through `(10, 2)`. -/
theorem ex_string_utf8 : readVal (listSeg exMem) .string [10, 0, 0, 0, 2, 0, 0, 0] =
    some ("é", []) := by kernel_rfl

/-- The same pair as a byte string. -/
theorem ex_bytes : readVal (listSeg exMem) .bytes [10, 0, 0, 0, 2, 0, 0, 0] =
    some (([0xC3, 0xA9] : List UInt8), []) := by kernel_rfl

/-- A byte string need not be UTF-8. -/
theorem ex_bytes_not_utf8 : readVal (listSeg exMem) .bytes [36, 0, 0, 0, 1, 0, 0, 0] =
    some (([0xFF] : List UInt8), []) := by kernel_rfl

/-- A `list<u32>` of two elements at `12`. -/
theorem ex_list_u32 : readVal (listSeg exMem) (.list .u32) [12, 0, 0, 0, 2, 0, 0, 0] =
    some (([7, 9] : List UInt32), []) := by kernel_rfl

/-- A `list<string>`: two pairs at `20`, each naming a string. -/
theorem ex_list_string : readVal (listSeg exMem) (.list .string) [20, 0, 0, 0, 2, 0, 0, 0] =
    some ((["hi", "é"] : List String), []) := by kernel_rfl

/-- A `list<list<u32>>`: two pairs at `72`, naming `[7, 9]` and `[9]`. -/
theorem ex_list_list : readVal (listSeg exMem) (.list (.list .u32)) [72, 0, 0, 0, 2, 0, 0, 0] =
    some (([[7, 9], [9]] : List (List UInt32)), []) := by kernel_rfl

/-- A payload vector `(u32, string)`: twelve bytes, no padding. -/
theorem ex_vals : readVals (listSeg exMem) [.u32, .string]
    [5, 0, 0, 0, 8, 0, 0, 0, 2, 0, 0, 0] = some ((5 : UInt32), "hi", ()) := by kernel_rfl

/-- A payload vector `(bool, u32)`: the `u32` at offset `4`; the padding bytes are not read. -/
theorem ex_vals_padded : readVals (listSeg exMem) [.bool, .u32]
    [1, 0xAA, 0xBB, 0xCC, 5, 0, 0, 0] = some (true, (5 : UInt32), ()) := by kernel_rfl

/-- A payload vector `(u32, s64)`: the `s64` at offset `8`. -/
theorem ex_vals_padded64 : readVals (listSeg exMem) [.u32, .s64]
    [5, 0, 0, 0, 0xAA, 0xAA, 0xAA, 0xAA, 3, 0, 0, 0, 0, 0, 0, 0] =
    some ((5 : UInt32), (3 : Int64), ()) := by kernel_rfl

/-! ## Narrow integers, floats, chars and composite payloads -/

/-- An `s8`: `FF` is `-1`. -/
theorem ex_s8 : readVal (listSeg exMem) .s8 [0xFF] = some ((-1 : Int8), []) := by kernel_rfl

/-- A `u16`, little-endian. -/
theorem ex_u16 : readVal (listSeg exMem) .u16 [0x34, 0x12] = some ((0x1234 : UInt16), []) := by
  kernel_rfl

/-- An `s16`: `FE FF` is `-2`. -/
theorem ex_s16 : readVal (listSeg exMem) .s16 [0xFE, 0xFF] = some ((-2 : Int16), []) := by
  kernel_rfl

/-- `bool`: every nonzero byte is `true` (REF `convert_int_to_bool`). -/
theorem ex_bool_two : readVal (listSeg exMem) .bool [2] = some (true, []) := by kernel_rfl

/-- An `f32`: the bits of `1.0`. -/
theorem ex_f32 : readVal (listSeg exMem) .f32 [0, 0, 0x80, 0x3F] =
    some ((0x3F800000 : BitVec 32), []) := by kernel_rfl

/-- **A NaN `f32` is canonicalised**: the NaN `7FC00001` is read as `7FC00000` (REF
`canonicalize_nan32`). -/
theorem ex_f32_nan : readVal (listSeg exMem) .f32 [1, 0, 0xC0, 0x7F] =
    some ((0x7FC00000 : BitVec 32), []) := by kernel_rfl

/-- An `f64`: the bits of `-2.0`. -/
theorem ex_f64 : readVal (listSeg exMem) .f64 [0, 0, 0, 0, 0, 0, 0, 0xC0] =
    some ((0xC000000000000000 : BitVec 64), []) := by kernel_rfl

/-- **A NaN `f64` is canonicalised** (REF `canonicalize_nan64`). -/
theorem ex_f64_nan : readVal (listSeg exMem) .f64 [5, 0, 0, 0, 0, 0, 0xF8, 0xFF] =
    some ((0x7FF8000000000000 : BitVec 64), []) := by kernel_rfl

/-- A `char`: `U+0061`. -/
theorem ex_char : readVal (listSeg exMem) .char [0x61, 0, 0, 0] = some ('a', []) := by
  kernel_rfl

/-- A `char` outside the basic plane: `U+1F600`. -/
theorem ex_char_astral : readVal (listSeg exMem) .char [0x00, 0xF6, 0x01, 0] =
    some (Char.ofNat 0x1F600, []) := by kernel_rfl

/-- `list<u16, 3>`, in place. -/
theorem ex_fixed : readVal (listSeg exMem) (.fixedList .u16 3) [1, 0, 2, 0, 3, 0] =
    some ((#v[1, 2, 3] : Vector UInt16 3), []) := by kernel_rfl

/-- `tuple<u8, u32>`: the `u32` at offset `4`, the padding not read. -/
theorem ex_tuple : readVal (listSeg exMem) (.tuple [.u8, .u32]) [1, 0xAA, 0xAA, 0xAA, 5, 0, 0, 0] =
    some (((1 : UInt8), (5 : UInt32), ()), []) := by kernel_rfl

/-- **A record** `{ ch: 'a', size: some(7) }` (`glyphTy`). -/
theorem ex_record : readVal (listSeg exMem) glyphTy [0x61, 0, 0, 0, 1, 7, 0xAA, 0xAA] =
    some ((('a', (some 7 : Option UInt8), ()) : Char × Option UInt8 × Unit), []) := by kernel_rfl

/-- `option<u8>` `none`: the payload byte is not read. -/
theorem ex_option_none : readVal (listSeg exMem) (.option .u8) [0, 0xAA] =
    some ((none : Option UInt8), []) := by kernel_rfl

/-- `variant { a, b(u32) }`: the case `b(5)`, the payload at offset `4`. -/
theorem ex_variant :
    readVal (listSeg exMem) (.variant [("a", none), ("b", some .u32)]) [1, 0, 0, 0, 5, 0, 0, 0] =
      some ((Sum.inr (Sum.inl 5) : Unit ⊕ (UInt32 ⊕ Empty)), []) := by kernel_rfl

/-- `variant { a, b(u32) }`: the payload-free case `a`. -/
theorem ex_variant_a :
    readVal (listSeg exMem) (.variant [("a", none), ("b", some .u32)]) [0, 0, 0, 0, 5, 0, 0, 0] =
      some ((Sum.inl () : Unit ⊕ (UInt32 ⊕ Empty)), []) := by kernel_rfl

/-- `enum { r, g, b }`: the case `b`. -/
theorem ex_enum : readVal (listSeg exMem) (.enum ["r", "g", "b"]) [2] =
    some ((2 : Fin 3), []) := by kernel_rfl

/-- `result<u32>`: `ok(9)`. -/
theorem ex_result_ok : readVal (listSeg exMem) (.result (some .u32) none) [0, 0, 0, 0, 9, 0, 0, 0] =
    some ((Sum.inl 9 : UInt32 ⊕ Unit), []) := by kernel_rfl

/-- `result<u32>`: `err` (no payload). -/
theorem ex_result_err :
    readVal (listSeg exMem) (.result (some .u32) none) [1, 0, 0, 0, 9, 0, 0, 0] =
      some ((Sum.inr () : UInt32 ⊕ Unit), []) := by kernel_rfl

/-- `flags { a, b, c }`: the bits `a` and `c`. -/
theorem ex_flags : readVal (listSeg exMem) (.flags ["a", "b", "c"]) [0b101] =
    some ((0b101 : BitVec 3), []) := by kernel_rfl

/-- **`flags` ignore the bits above the label count** (REF `unpack_flags_from_int`): `FD` is
the same `{ a, c }`. -/
theorem ex_flags_high : readVal (listSeg exMem) (.flags ["a", "b", "c"]) [0xFD] =
    some ((0b101 : BitVec 3), []) := by kernel_rfl

/-- A `list<tuple<u16, u16>>` through the pair `(12, 2)`: `(7, 0)` and `(9, 0)`. -/
theorem ex_list_tuple :
    readVal (listSeg exMem) (.list (.tuple [.u16, .u16])) [12, 0, 0, 0, 2, 0, 0, 0] =
      some (([(7, 0, ()), (9, 0, ())] : List (UInt16 × UInt16 × Unit)), []) := by kernel_rfl

/-- `option<string>`: `some("hi")` through the pair `(8, 2)` at offset `4`. -/
theorem ex_option_string :
    readVal (listSeg exMem) (.option .string) [1, 0, 0, 0, 8, 0, 0, 0, 2, 0, 0, 0] =
      some ((some "hi" : Option String), []) := by kernel_rfl

/-- A payload vector `(glyph, f32)`: the `f32` at offset `8`. -/
theorem ex_vals_glyph : readVals (listSeg exMem) [glyphTy, .f32]
    [0xBB, 0x03, 0, 0, 0, 0xAA, 0, 0, 0, 0, 0x80, 0x3F] =
      some ((('λ', (none : Option UInt8), ()) : Char × Option UInt8 × Unit),
        (0x3F800000 : BitVec 32), ()) := by kernel_rfl

/-! ## Malformed payloads of the full domain -/

/-- **A surrogate is no `char`** (REF `trap_if(0xD800 <= i <= 0xDFFF)`). -/
theorem ex_char_surrogate : readVal (listSeg exMem) .char [0x00, 0xD8, 0, 0] = none := by
  kernel_rfl

/-- **A value `≥ 0x110000` is no `char`** (REF `trap_if(i >= 0x110000)`). -/
theorem ex_char_too_big : readVal (listSeg exMem) .char [0x00, 0x00, 0x11, 0] = none := by
  kernel_rfl

/-- A record whose `char` field is a surrogate is no value. -/
theorem ex_record_bad_char : readVal (listSeg exMem) glyphTy [0x00, 0xDC, 0, 0, 0, 0, 0, 0] =
    none := by kernel_rfl

/-- **An `option` discriminant other than `0`, `1` is no value** (REF
`trap_if(case_index >= len(cases))`). -/
theorem ex_option_bad_disc : readVal (listSeg exMem) (.option .u8) [2, 7] = none := by kernel_rfl

/-- A record whose `option` discriminant is invalid is no value. -/
theorem ex_record_bad_disc : readVal (listSeg exMem) glyphTy [0x61, 0, 0, 0, 2, 7, 0, 0] =
    none := by kernel_rfl

/-- **A variant discriminant past the last case is no value.** -/
theorem ex_variant_bad_disc :
    readVal (listSeg exMem) (.variant [("a", none), ("b", some .u32)]) [2, 0, 0, 0, 5, 0, 0, 0] =
      none := by kernel_rfl

/-- **An `enum` discriminant past the last case is no value.** -/
theorem ex_enum_bad_disc : readVal (listSeg exMem) (.enum ["r", "g", "b"]) [3] = none := by
  kernel_rfl

/-- **A `result` discriminant other than `0`, `1` is no value.** -/
theorem ex_result_bad_disc :
    readVal (listSeg exMem) (.result (some .u32) none) [5, 0, 0, 0, 9, 0, 0, 0] = none := by
  kernel_rfl

/-- An `option<string>` whose string is invalid UTF-8 (the pair `(36, 1)`) is no value. -/
theorem ex_option_string_bad_utf8 :
    readVal (listSeg exMem) (.option .string) [1, 0, 0, 0, 36, 0, 0, 0, 1, 0, 0, 0] = none := by
  kernel_rfl

/-- A `list<u16, 3>` with too few bytes is no value. -/
theorem ex_fixed_short : readVal (listSeg exMem) (.fixedList .u16 3) [1, 0, 2, 0, 3] = none := by
  kernel_rfl

/-- A `list<tuple<u16, u16>>` at an odd pointer (`13`) is no value. -/
theorem ex_list_tuple_misaligned :
    readVal (listSeg exMem) (.list (.tuple [.u16, .u16])) [13, 0, 0, 0, 1, 0, 0, 0] = none := by
  kernel_rfl

/-! ## Malformed payloads -/

/-- Invalid UTF-8 is no string. -/
theorem ex_bad_utf8 : readVal (listSeg exMem) .string [36, 0, 0, 0, 1, 0, 0, 0] = none := by
  kernel_rfl

/-- A segment out of bounds is no value. -/
theorem ex_out_of_bounds : readVal (listSeg exMem) .bytes [90, 0, 0, 0, 7, 0, 0, 0] = none := by
  kernel_rfl

/-- A list whose elements run out of bounds is no value. -/
theorem ex_list_oob : readVal (listSeg exMem) (.list .string) [20, 0, 0, 0, 10, 0, 0, 0] =
    none := by kernel_rfl

/-- A `list<u32>` at a pointer not aligned to four is no value (the four bytes at `13` are in
bounds). -/
theorem ex_list_misaligned : readVal (listSeg exMem) (.list .u32) [13, 0, 0, 0, 1, 0, 0, 0] =
    none := by kernel_rfl

/-- A `list<string>` one of whose strings is invalid UTF-8 is no value. -/
theorem ex_list_string_bad_utf8 :
    readVal (listSeg exMem) (.list .string) [40, 0, 0, 0, 2, 0, 0, 0] = none := by kernel_rfl

/-- A `list<string>` one of whose strings is out of bounds is no value. -/
theorem ex_list_string_oob :
    readVal (listSeg exMem) (.list .string) [56, 0, 0, 0, 2, 0, 0, 0] = none := by kernel_rfl

/-- A `list<list<u32>>` whose inner list is misaligned is no value. -/
theorem ex_list_list_misaligned :
    readVal (listSeg exMem) (.list (.list .u32)) [88, 0, 0, 0, 1, 0, 0, 0] = none := by
  kernel_rfl

/-- A payload area shorter than its vector is no value. -/
theorem ex_short : readVals (listSeg exMem) [.u32, .s64] [5, 0, 0, 0, 0, 0, 0, 0, 3] = none := by
  kernel_rfl

/-! ## Malformed calls -/

/-- Control: `node(0, 0, 0, 0)` of `calcSig` reads `num 0` (eight zero bytes at `0`). -/
theorem ex_node_num : Callout.witNode calcSig calcTagOf (exCall [.i32 0, .i32 0, .i32 0, .i32 0]) =
    some (⟨CalcTag.num, ((0 : Int64), ())⟩, []) := by kernel_rfl

/-- An `s64` payload at an address not aligned to eight (`12`) is no event. -/
theorem ex_node_misaligned_payload :
    Callout.witNode calcSig calcTagOf (exCall [.i32 0, .i32 12, .i32 0, .i32 0]) = none := by
  kernel_rfl

/-- A payload area out of bounds (`[96, 104)`, at an aligned address, of 96 bytes) is no
event. -/
theorem ex_node_payload_oob :
    Callout.witNode calcSig calcTagOf (exCall [.i32 0, .i32 96, .i32 0, .i32 0]) = none := by
  kernel_rfl

/-- Control: `node(1, 0, 0, 2)` of `calcSig` reads `add` with the handles `0`, `0`. -/
theorem ex_node_add : Callout.witNode calcSig calcTagOf (exCall [.i32 1, .i32 0, .i32 0, .i32 2]) =
    some (⟨CalcTag.add, ()⟩, [0, 0]) := by kernel_rfl

/-- **A wrong child count**: `add` with one child is no event. -/
theorem ex_node_one_child :
    Callout.witNode calcSig calcTagOf (exCall [.i32 1, .i32 0, .i32 0, .i32 1]) = none := by
  kernel_rfl

/-- **A wrong child count**: `add` with three children is no event. -/
theorem ex_node_three_children :
    Callout.witNode calcSig calcTagOf (exCall [.i32 1, .i32 0, .i32 0, .i32 3]) = none := by
  kernel_rfl

/-- **A wrong child count**: `num` with a child is no event. -/
theorem ex_node_leaf_child :
    Callout.witNode calcSig calcTagOf (exCall [.i32 0, .i32 0, .i32 0, .i32 1]) = none := by
  kernel_rfl

/-- Child handles at an address not aligned to four (`2`) are no event. -/
theorem ex_node_misaligned_children :
    Callout.witNode calcSig calcTagOf (exCall [.i32 1, .i32 0, .i32 2, .i32 2]) = none := by
  kernel_rfl

/-- Child handles out of bounds (`[92, 100)` of 96 bytes) are no event. -/
theorem ex_node_children_oob :
    Callout.witNode calcSig calcTagOf (exCall [.i32 1, .i32 0, .i32 92, .i32 2]) = none := by
  kernel_rfl

/-- An unknown tag is no event. -/
theorem ex_node_unknown_tag :
    Callout.witNode calcSig calcTagOf (exCall [.i32 7, .i32 0, .i32 0, .i32 0]) = none := by
  kernel_rfl

/-- Control: `node(0, 20, 0, 0)` of `appSig` reads `var "hi"` through the pair at `20`. -/
theorem ex_node_var : Callout.witNode appSig appTagOf (exCall [.i32 0, .i32 20, .i32 0, .i32 0]) =
    some (⟨AppTag.var, ("hi", ())⟩, []) := by kernel_rfl

/-- A string payload naming invalid UTF-8 (the pair `(36, 1)` at `48`) is no event. -/
theorem ex_node_bad_utf8 :
    Callout.witNode appSig appTagOf (exCall [.i32 0, .i32 48, .i32 0, .i32 0]) = none := by
  kernel_rfl

/-- A string payload out of bounds (the pair `(200, 2)` at `64`) is no event. -/
theorem ex_node_string_oob :
    Callout.witNode appSig appTagOf (exCall [.i32 0, .i32 64, .i32 0, .i32 0]) = none := by
  kernel_rfl

/-- A string payload pair at an address not aligned to four (`2`) is no event. -/
theorem ex_node_misaligned_pair :
    Callout.witNode appSig appTagOf (exCall [.i32 0, .i32 2, .i32 0, .i32 0]) = none := by
  kernel_rfl

/-! ## Arities and bridges -/

variable {S : WitSig} {tagOf : BitVec 32 → Option S.Tag} {P : Profile}
  {Envs : Store Nat → SEnv UImp → Prop} {memIdx : Nat} {m : Module}

/-- **The decoder admits only the declared arities.** -/
theorem witNode_admits {o : Callout} {op : Σ t, S.toAstSig.Arg t} {hs : List (BitVec 32)}
    (h : Callout.witNode S tagOf o = some (op, hs)) : (S.arity op.1).Admits hs.length = true :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.witNode_admits h

/-- **A decoded write has an admitted number of children.** -/
theorem witWrite_admits {ix : WitImports} {o : Callout} {w : HostReply}
    {op : Σ t, S.toAstSig.Arg t} {hs : List (BitVec 32)} {r : BitVec 32}
    (h : witWrite S tagOf ix o w = some (.write op hs r)) :
    (S.arity op.1).Admits hs.length = true :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.witWrite_admits h

/-- **A call the decoder rejects has no write event**, whatever its answer: under the bridges
(`witFixedLang_subset`, `witWriterLang_subset`) it makes no handle denote a tree. -/
theorem witWrite_none {ix : WitImports} {o : Callout} {w : HostReply}
    (h : Callout.witNode S tagOf o = none) : witWrite S tagOf ix o w = none :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.witWrite_none h

/-- **The typed AST writer bridge in a fixed environment**, for every policy. -/
theorem witFixedLang_subset {ix : WitImports} {pol : Policy (BitVec 32)}
    {ρ : Silmaril.Accept.Handle.Env (BitVec 32) (AST S.toAstSig)} {L : Set (AST S.toAstSig)}
    {reply : UCall Nat → UReply → Prop} {Inv : Store Nat → Prop}
    (hsat : MemSat P m memIdx (witRoles S tagOf ix)
      (roleWriterContract (witRoles S tagOf ix) (astW S.toAstSig) pol.sentinel ρ L reply) Inv)
    (hE : ∀ s L, Envs s L → ReplyEnvs reply s L) :
    fixedLang (astW S.toAstSig) pol {ρ} (witTraces S tagOf P Envs memIdx m ix) ⊆ L :=
  rolesFixedLang_subset
    (fun _ _ h => Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.witAccept_isAccept h)
    (fun _ _ _ h => Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.witWrite_isWrite h)
    hsat hE

/-- **The typed AST writer bridge** (store semantics, no undefined behaviour). -/
theorem witWriterLang_subset {ix : WitImports} {pol : Policy (BitVec 32)}
    {L : Set (AST S.toAstSig)} {reply : UCall Nat → UReply → Prop} {Inv : Store Nat → Prop}
    (hsat : ∀ ρ, MemSat P m memIdx (witRoles S tagOf ix)
      (roleWriterContract (witRoles S tagOf ix) (astW S.toAstSig) pol.sentinel ρ L reply) Inv)
    (hE : ∀ s L, Envs s L → ReplyEnvs reply s L) (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub) : witWriterLang S tagOf P Envs memIdx m ix pol ⊆ L :=
  rolesWriterLang_subset
    (fun _ _ h => Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.witAccept_isAccept h)
    (fun _ _ _ h => Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.witWrite_isWrite h)
    hsat hE hw ha

/-- **In a fixed environment, `calcMod` accepts only `add(num 1, num 2)`.** -/
theorem calcMod_fixed_sound (P : Profile) {pol : Policy (BitVec 32)} (hs : pol.sentinel = none)
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (AST calcSig.toAstSig)) :
    fixedLang (astW calcSig.toAstSig) pol {ρ}
      (witTraces calcSig calcTagOf P (ReplyEnvs hiReply) 0 calcMod {}) ⊆ {addTree} :=
  witFixedLang_subset
    (by rw [hs]; exact Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.calc_sat P ρ)
    (fun _ _ h => h)

/-- **`calcMod` accepts only `add(num 1, num 2)`.** -/
theorem calcMod_sound (P : Profile) {pol : Policy (BitVec 32)} (hs : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    witWriterLang calcSig calcTagOf P (ReplyEnvs hiReply) 0 calcMod {} pol ⊆ {addTree} :=
  witWriterLang_subset
    (fun ρ => by
      rw [hs]; exact Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.calc_sat P ρ)
    (fun _ _ h => h) hw ha

/-- **`calcMod` accepts `add(num 1, num 2)`**, for every policy. -/
theorem calcMod_live (P : Profile) (pol : Policy (BitVec 32)) :
    addTree ∈ witWriterLang calcSig calcTagOf P (ReplyEnvs hiReply) 0 calcMod {} pol :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.WitAst.calcMod_live P pol

/-- **The writer language of `calcMod` is exactly `{add(num 1, num 2)}`.** -/
theorem calcMod_lang (P : Profile) {pol : Policy (BitVec 32)} (hs : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    witWriterLang calcSig calcTagOf P (ReplyEnvs hiReply) 0 calcMod {} pol = {addTree} :=
  Set.Subset.antisymm (calcMod_sound P hs hw ha)
    (Set.singleton_subset_iff.2 (calcMod_live P pol))

/-! ## String payloads: `appMod` -/

/-- **In a fixed environment, `appMod` accepts only `app(var "f", var "x")`.** -/
theorem appMod_fixed_sound (P : Profile) {pol : Policy (BitVec 32)} (hs : pol.sentinel = none)
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (AST appSig.toAstSig)) :
    fixedLang (astW appSig.toAstSig) pol {ρ}
      (witTraces appSig appTagOf P (ReplyEnvs hiReply) 0 appMod {}) ⊆ {appTree} :=
  witFixedLang_subset
    (by rw [hs]; exact Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitApp.app_sat P ρ)
    (fun _ _ h => h)

/-- **`appMod` accepts only `app(var "f", var "x")`.** -/
theorem appMod_sound (P : Profile) {pol : Policy (BitVec 32)} (hs : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    witWriterLang appSig appTagOf P (ReplyEnvs hiReply) 0 appMod {} pol ⊆ {appTree} :=
  witWriterLang_subset
    (fun ρ => by
      rw [hs]; exact Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitApp.app_sat P ρ)
    (fun _ _ h => h) hw ha

/-- **`appMod` accepts `app(var "f", var "x")`**, for every policy. -/
theorem appMod_live (P : Profile) (pol : Policy (BitVec 32)) :
    appTree ∈ witWriterLang appSig appTagOf P (ReplyEnvs hiReply) 0 appMod {} pol :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.WitApp.appMod_live P pol

/-- **The writer language of `appMod` is exactly `{app(var "f", var "x")}`.** -/
theorem appMod_lang (P : Profile) {pol : Policy (BitVec 32)} (hs : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    witWriterLang appSig appTagOf P (ReplyEnvs hiReply) 0 appMod {} pol = {appTree} :=
  Set.Subset.antisymm (appMod_sound P hs hw ha)
    (Set.singleton_subset_iff.2 (appMod_live P pol))

/-! ## Byte-string and list payloads: `binMod` -/

/-- **In a fixed environment, `binMod` accepts only `pair(blob [0xFF], seq [7, 9])`.** -/
theorem binMod_fixed_sound (P : Profile) {pol : Policy (BitVec 32)} (hs : pol.sentinel = none)
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (AST binSig.toAstSig)) :
    fixedLang (astW binSig.toAstSig) pol {ρ}
      (witTraces binSig binTagOf P (ReplyEnvs hiReply) 0 binMod {}) ⊆ {binTree} :=
  witFixedLang_subset
    (by rw [hs]; exact Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitBin.bin_sat P ρ)
    (fun _ _ h => h)

/-- **`binMod` accepts only `pair(blob [0xFF], seq [7, 9])`.** -/
theorem binMod_sound (P : Profile) {pol : Policy (BitVec 32)} (hs : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    witWriterLang binSig binTagOf P (ReplyEnvs hiReply) 0 binMod {} pol ⊆ {binTree} :=
  witWriterLang_subset
    (fun ρ => by
      rw [hs]; exact Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitBin.bin_sat P ρ)
    (fun _ _ h => h) hw ha

/-- **`binMod` accepts `pair(blob [0xFF], seq [7, 9])`**, for every policy. -/
theorem binMod_live (P : Profile) (pol : Policy (BitVec 32)) :
    binTree ∈ witWriterLang binSig binTagOf P (ReplyEnvs hiReply) 0 binMod {} pol :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.WitBin.binMod_live P pol

/-- **The writer language of `binMod` is exactly `{pair(blob [0xFF], seq [7, 9])}`.** -/
theorem binMod_lang (P : Profile) {pol : Policy (BitVec 32)} (hs : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    witWriterLang binSig binTagOf P (ReplyEnvs hiReply) 0 binMod {} pol = {binTree} :=
  Set.Subset.antisymm (binMod_sound P hs hw ha)
    (Set.singleton_subset_iff.2 (binMod_live P pol))

/-! ## Record, option and char payloads: `glyphMod` -/

/-- **In a fixed environment, `glyphMod` accepts only
`pair(glyph { 'a', some(7) }, glyph { 'λ', none })`.** -/
theorem glyphMod_fixed_sound (P : Profile) {pol : Policy (BitVec 32)} (hs : pol.sentinel = none)
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (AST glyphSig.toAstSig)) :
    fixedLang (astW glyphSig.toAstSig) pol {ρ}
      (witTraces glyphSig glyphTagOf P (ReplyEnvs hiReply) 0 glyphMod {}) ⊆ {glyphPairTree} :=
  witFixedLang_subset
    (by rw [hs]; exact Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitGlyph.glyph_sat P ρ)
    (fun _ _ h => h)

/-- **`glyphMod` accepts only `pair(glyph { 'a', some(7) }, glyph { 'λ', none })`.** -/
theorem glyphMod_sound (P : Profile) {pol : Policy (BitVec 32)} (hs : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    witWriterLang glyphSig glyphTagOf P (ReplyEnvs hiReply) 0 glyphMod {} pol ⊆ {glyphPairTree} :=
  witWriterLang_subset
    (fun ρ => by
      rw [hs]; exact Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitGlyph.glyph_sat P ρ)
    (fun _ _ h => h) hw ha

/-- **`glyphMod` accepts `pair(glyph { 'a', some(7) }, glyph { 'λ', none })`**, for every
policy. -/
theorem glyphMod_live (P : Profile) (pol : Policy (BitVec 32)) :
    glyphPairTree ∈ witWriterLang glyphSig glyphTagOf P (ReplyEnvs hiReply) 0 glyphMod {} pol :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.WitGlyph.glyphMod_live P pol

/-- **The writer language of `glyphMod` is exactly
`{pair(glyph { 'a', some(7) }, glyph { 'λ', none })}`.** -/
theorem glyphMod_lang (P : Profile) {pol : Policy (BitVec 32)} (hs : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    witWriterLang glyphSig glyphTagOf P (ReplyEnvs hiReply) 0 glyphMod {} pol = {glyphPairTree} :=
  Set.Subset.antisymm (glyphMod_sound P hs hw ha)
    (Set.singleton_subset_iff.2 (glyphMod_live P pol))

end Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst
