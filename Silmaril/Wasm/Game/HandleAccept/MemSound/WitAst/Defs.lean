module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Ast.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.WordAtom.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Support.Defs
public import Silmaril.Wasm.Component.Reference.ABI.Layout.Defs
public import Silmaril.Wasm.Component.Reference.ABI.FloatChar.Defs
public import Silmaril.Wasm.Logic.Memory.Defs

/-!
# Typed payloads and fixed arities through linear memory: `node(tag, payload, children, n)`

`Silmaril.Wasm.Game.HandleAccept.MemSound.Ast` reads string tags without payloads, any number of
children (`strSig`, `Arity.star`). For a **WIT-typed signature** `S : WitSig` (payload types
`S.params t`, arities `S.arity t`) with tags numbered by `tagOf : BitVec 32 → Option S.Tag`:

* **Layout** (`PTy.layout`, `PTy.width`, `PTy.align`, `valsLayout`, `valsWidth`, `valsAlign`):
  the canonical ABI layout for memory32 (`Silmaril.Wasm.Component.ABI.layout .i32`, REF
  `elem_size` and `alignment`; agreement `layout_toWit`, `valsLayout_toWit` in `Thms`):

  | `PTy` | WIT | size | alignment |
  | --- | --- | --- | --- |
  | `bool`, `s8`, `u8` | `bool`, `s8`, `u8` | 1 | 1 |
  | `s16`, `u16` | `s16`, `u16` | 2 | 2 |
  | `s32`, `u32`, `f32`, `char` | `s32`, `u32`, `f32`, `char` | 4 | 4 |
  | `own r`, `borrow r` | `own<r>`, `borrow<r>` (an `i32` handle index) | 4 | 4 |
  | `s64`, `u64`, `f64` | `s64`, `u64`, `f64` | 8 | 8 |
  | `string`, `list t` (`bytes = list u8`) | `string`, `list<t>` | 8 (`(ptr, len)`) | 4 |
  | `fixedList t n` | `list<t, n>` | `n * t.width` | `t.align` |
  | `record fs`, `tuple ts` | `record`, `tuple` | `ABI.recordLayout` | largest field |
  | `variant cs`, `option t`, `result ok err` | the same | `ABI.variantLayout` | disc. ⊔ cases |
  | `enum cs` | `enum` | discriminant: 1, 2 or 4 (`discBytes`) | the same |
  | `flags ls` | `flags` | 1, 2 or 4 (≤ 8, ≤ 16, more labels) | the same |

  A payload vector `S.params t` is laid out as the WIT tuple of its types (`ABI.recordLayout`):
  each field at the next offset aligned to it (`ABI.placeField`), the size rounded up to the
  largest field alignment (tail padding); padding bytes are never read. A variant (and
  `option t` as `[none, some t]`, `result ok err` as `[ok, err]`, REF despecialisation) is its
  discriminant (the smallest of 1, 2, 4 bytes for its case count, REF `discriminant_type`) and
  the payload of its case at `caseOffset` (the discriminant padded to the largest case
  alignment).
* **Decoding** (`readVal`, `readFields`, `readFieldsAt`, `readCase`, `readOpt`, `readVals`, REF
  `load`, `load_record`, `load_variant`, `load_flags`, `load_string_from_range`,
  `load_list_from_range`, `load_list_from_valid_range`): scalars little-endian, `bool` any
  nonzero byte (REF `convert_int_to_bool`), floats as their bits **with NaNs canonicalised**
  (REF `decode_i32_as_float`/`decode_i64_as_float`), `char` **only a Unicode scalar value**
  (REF `convert_i32_to_char`: surrogates and values `≥ 0x110000` are no value); a `string` is
  the UTF-8 text of `[ptr, ptr + len)` (invalid UTF-8: no value), `list t` the `len` elements
  of `t` at `ptr + i * t.width` with `ptr` aligned to `t` (misaligned: no value), recursively
  (`list<string>`, `list<list<t>>`, `list<record>`, …: every inner pointer read from the same
  memory and checked in turn); fixed-length lists, records and tuples in place; variants,
  options, results and enums **only with a discriminant in range** (REF
  `trap_if(case_index >= len(cases))`), the payload of a payload-free case not read; `flags`
  the low `n` bits (**higher bits are ignored**, REF `unpack_flags_from_int`). Out of bounds:
  no value.
* `Callout.witNode S tagOf`: the call `node(tag, payload, children, n)` names the tag `tagOf tag`,
  reads its payload vector from the `valsWidth (S.params t)` bytes at `payload` (aligned to
  `valsAlign`, REF `trap_if(ptr != align_to(ptr, alignment(tuple)))` of the indirect parameter
  convention) and `n` little-endian `i32` child handles at `[children, children + 4n)`
  (`children` aligned to four, as a `list<u32>`) of the memory at the call, and **admits only
  the declared arity**: the number of children must be admitted by `S.arity t`. Every
  malformation (unknown tag, misaligned or out-of-bounds pointer, invalid UTF-8, an invalid
  `char` or discriminant at any depth, wrong child count) is **no event**: the call has no
  write event (`witWrite_none`), so under the bridges it makes no handle denote a tree.
* `witWrite`, `witAccept`, `witRoles`, `witTraces`, `witWriterLang`: the write at the answer of a
  call returning one `i32` handle, `accept(h)` at the call, and the writer language over
  `astW S.toAstSig`.

## The supported signature domain

Payloads are exactly the `Silmaril.Formats.PTy` types, i.e. (`Wit.toWit`, injective, with
left inverse `Wit.ofWit`) **the WIT value types that have a canonical-ABI memory
representation and no asynchronous semantics**: `bool`, `s8`, `u8`, `s16`, `u16`,
`s32`, `u32`, `s64`, `u64`, `f32`, `f64`, `char`, `string`, `list<t>` (so `list<u8>`, `bytes`),
`list<t, n>`, `record`, `tuple`, `variant`, `enum`, `option`, `result` (each side optional),
`flags`, nested to any depth, and the resource handles `own<r>`, `borrow<r>`. A tag's payload is
a finite vector of these (`S.params t`, laid out as a WIT tuple); its children are separate
handles, not payloads.

**Resource handles** (the stored-tree semantics, `Wit.storedEnv`):

* `own<r>`: the value in the tree is the resource's **representation**, from an **explicit
  resource table** (`Own.RT`: handle index ↦ resource type, representation, live), and the
  handle **moves** into the tree: the call consumes the table entry, and a second move of the
  same handle is an invalid write (`Own.ownHost`, policy `onWrite`). The memory decoder here
  reads no handle (`readVal` of `own` is none, so `Callout.witNode` of a tag with an `own`
  field is no event); `Own` reads **top-level** `own` fields of a payload vector as `u32` table
  indices (`WitSig.raw`) and resolves them in the table. An `own` nested inside a list, option,
  record, … is not resolved: it is no value, so the call is no event (not supported yet).
  Acceptance depends on the table **only through the handles moved** (`Own.resolve_congr`,
  `Own.run_congr`), and is otherwise trace-dependent: the table at a call is the initial one
  with every earlier move consumed.
* `borrow<r>`: **rejected in stored trees**. A borrow lives for one call, so a tree (which
  outlives it) cannot hold one: `PTy.Val (.borrow r) = Empty`, a payload vector with a `borrow`
  field has no value, and a `node` call of such a tag is no event (`Own.borrow_rejected`).

**Not payloads**: `future`, `stream` and `error-context` (asynchronous endpoints: unsupported
pending async semantics), `map<k, v>` (WIT despecialises it to `list<tuple<k, v>>`, which is a
payload type), and named types (`ref`: resolve them first). Field, case and label names are part
of the type, not of the value (`PTy.Val`: records and tuples are products, variants sums, `enum`
with `n` cases `Fin n`, `flags` with `n` labels `BitVec n`). Flag sets of more than 32 labels
(outside WIT well-formedness) read only the 32 bits of their four bytes.

**Non-claims.** The layout and the trap conditions above follow the canonical ABI; the decoder
is not proved equal to the monadic `Canon.load` programs (which run over a component store), and
the length limits `Limits.maxStringBytes`/`maxListBytes` (REF `MAX_STRING_BYTE_LENGTH`,
`MAX_LIST_BYTE_LENGTH`) are not checked: only the memory bound is. Payloads always go through
memory (the indirect convention), never flattened into core arguments; strings are UTF-8 only
(no `latin1+utf16` encoding option).

## The example `calcMod`

The signature `calcSig`: tags `num` (tag `0`, one `s64` payload, no children) and `add` (tag `1`,
no payload, **exactly two** children). Imports `0 wit.node : [i32 i32 i32 i32] → [i32]`,
`1 wit.accept : [i32] → []`; one memory page; export `run : [] → []` with two `i32` locals:

```wat
(func $run (local $a i32) (local $b i32)
  (i64.store (i32.const 16) (i64.const 1))                         ;; payload 1 at [16, 24)
  (local.set $a (call $node (i32.const 0) (i32.const 16) (i32.const 0) (i32.const 0)))
  (i64.store (i32.const 16) (i64.const 2))                         ;; payload 2 at [16, 24)
  (local.set $b (call $node (i32.const 0) (i32.const 16) (i32.const 0) (i32.const 0)))
  (i32.store (i32.const 0) (local.get $a))                         ;; children [$a $b] at 0
  (i32.store (i32.const 4) (local.get $b))
  (call $accept (call $node (i32.const 1) (i32.const 0) (i32.const 0) (i32.const 2))))
```

It builds `add(num 1, num 2)` (`addTree`). Every payload and child list is written right before
the call that reads it, since an answer may rewrite memory. The admitted hosts are those of
`hiMod` (`hiReply`).

## The example `appMod`

The signature `appSig`: tags `var` (tag `0`, one `string` payload, no children) and `app` (tag
`1`, no payload, exactly two children). Same imports, memory and locals as `calcMod`:

```wat
(func $run (local $a i32) (local $b i32)
  (i32.store8 (i32.const 24) (i32.const 0x66))                     ;; "f" at [24, 25)
  (i64.store (i32.const 16) (i64.const 0x100000018))               ;; (ptr, len) = (24, 1)
  (local.set $a (call $node (i32.const 0) (i32.const 16) (i32.const 0) (i32.const 0)))
  (i32.store8 (i32.const 24) (i32.const 0x78))                     ;; "x" at [24, 25)
  (i64.store (i32.const 16) (i64.const 0x100000018))
  (local.set $b (call $node (i32.const 0) (i32.const 16) (i32.const 0) (i32.const 0)))
  (i32.store (i32.const 0) (local.get $a))
  (i32.store (i32.const 4) (local.get $b))
  (call $accept (call $node (i32.const 1) (i32.const 0) (i32.const 0) (i32.const 2))))
```

It builds `app(var "f", var "x")` (`appTree`); both the payload pair and the string bytes it
names are written right before each call.

## The example `binMod`

The signature `binSig`: tags `blob` (tag `0`, one `bytes` payload, no children), `seq` (tag `1`,
one `list<u32>` payload, no children) and `pair` (tag `2`, no payload, exactly two children).
Same imports, memory and locals as `calcMod`:

```wat
(func $run (local $a i32) (local $b i32)
  (i32.store8 (i32.const 24) (i32.const 0xFF))                     ;; the byte FF at [24, 25)
  (i64.store (i32.const 16) (i64.const 0x100000018))               ;; (ptr, len) = (24, 1)
  (local.set $a (call $node (i32.const 0) (i32.const 16) (i32.const 0) (i32.const 0)))
  (i64.store (i32.const 24) (i64.const 0x900000007))               ;; u32s 7, 9 at [24, 32)
  (i64.store (i32.const 16) (i64.const 0x200000018))               ;; (ptr, len) = (24, 2)
  (local.set $b (call $node (i32.const 1) (i32.const 16) (i32.const 0) (i32.const 0)))
  (i32.store (i32.const 0) (local.get $a))
  (i32.store (i32.const 4) (local.get $b))
  (call $accept (call $node (i32.const 2) (i32.const 0) (i32.const 0) (i32.const 2))))
```

It builds `pair(blob [0xFF], seq [7, 9])` (`binTree`): `FF` is a byte string, not UTF-8; the
list pointer `24` is aligned to four.

## The example `glyphMod`

The signature `glyphSig`: tags `glyph` (tag `0`, one `record glyph { ch: char, size:
option<u8> }` payload (`glyphTy`: eight bytes aligned to four, `ch` at `0`, the `option`
discriminant at `4` and its payload at `5`), no children) and `pair` (tag `1`, no payload,
exactly two children). Same imports, memory, locals and code as `calcMod`, with the two `i64`
payloads `glyphA` (`61 00 00 00 01 07 00 00`: `{ ch: 'a', size: some(7) }`) and `glyphB`
(`BB 03 00 00 00 00 00 00`: `{ ch: 'λ', size: none }`). It builds
`pair(glyph { 'a', some(7) }, glyph { 'λ', none })` (`glyphPairTree`).

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept.Handle Silmaril.Accept.IO Silmaril.Formats
  Silmaril.Formats.Api Silmaril.Wasm.Game.HandleAccept.Memory
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.WordAtom
  Silmaril.Wasm.Component

/-! ## Payloads in memory: the canonical ABI layout -/

mutual
/-- **The canonical ABI layout of a payload type** (memory32, REF `elem_size`, `alignment`):
`bool`, `s8`, `u8` one byte; `s16`, `u16` two aligned to two; `s32`, `u32`, `f32`, `char`
four aligned to four; `s64`, `u64`, `f64` eight aligned to eight; `string` and `list t` the
pointer pair `(ptr, len)` (`ABI.pointerLayout .i32`: eight bytes aligned to four); `list<t, n>`
`n` elements in place; records and tuples `ABI.recordLayout`; variants, `option` (the cases
`[none, some t]`) and `result` (`[ok, err]`) `ABI.variantLayout` (the smallest discriminant,
then the payload at the largest case alignment); `enum` its discriminant; `flags` one, two or
four bytes. The same as `ABI.layout .i32 (Wit.toWit t)` (`layout_toWit`). -/
def PTy.layout : PTy → ABI.Layout
  | .bool | .s8 | .u8 => ⟨.one, 1⟩
  | .s16 | .u16 => ⟨.two, 1⟩
  | .s32 | .u32 | .f32 | .char | .own _ | .borrow _ => ⟨.four, 1⟩
  | .s64 | .u64 | .f64 => ⟨.eight, 1⟩
  | .string | .list _ => ABI.pointerLayout .i32
  | .fixedList t n => ⟨(PTy.layout t).alignment, n * (PTy.layout t).units⟩
  | .record fs => ABI.recordLayout (PTy.fieldLayouts fs)
  | .tuple ts => ABI.recordLayout (PTy.layouts ts)
  | .variant cs => ABI.variantLayout (PTy.caseLayouts cs)
  | .enum cs => ⟨ABI.discriminantAlignment cs.length, 1⟩
  | .option t => ABI.variantLayout [none, some (PTy.layout t)]
  | .result ok err => ABI.variantLayout [PTy.optLayout ok, PTy.optLayout err]
  | .flags ls => ⟨ABI.flagsAlignment ls.length, 1⟩

/-- The layouts of a list of payload types. -/
def PTy.layouts : List PTy → List ABI.Layout
  | [] => []
  | t :: ts => PTy.layout t :: PTy.layouts ts

/-- The layouts of record fields. -/
def PTy.fieldLayouts : List (String × PTy) → List ABI.Layout
  | [] => []
  | (_, t) :: fs => PTy.layout t :: PTy.fieldLayouts fs

/-- The layouts of variant case payloads. -/
def PTy.caseLayouts : List (String × Option PTy) → List (Option ABI.Layout)
  | [] => []
  | (_, o) :: cs => PTy.optLayout o :: PTy.caseLayouts cs

/-- The layout of an optional payload. -/
def PTy.optLayout : Option PTy → Option ABI.Layout
  | none => none
  | some t => some (PTy.layout t)
end

/-- The size of a payload value in memory (REF `elem_size`). -/
def PTy.width (t : PTy) : Nat := (PTy.layout t).size

/-- The alignment of a payload value in memory (REF `alignment`). -/
def PTy.align (t : PTy) : Nat := (PTy.layout t).alignment.bytes

/-- The discriminant bytes of a variant with `n` cases (REF `discriminant_type`). -/
def discBytes (n : Nat) : Nat := (ABI.discriminantAlignment n).bytes

/-- The offset of the payload of a variant with these case layouts: the discriminant, padded to
the largest case alignment (REF `align_to(ptr + disc_size, max_case_alignment)`). -/
def caseOffset (ls : List (Option ABI.Layout)) : Nat :=
  ABI.alignTo (discBytes ls.length) (ABI.maxCaseAlignment ls)

/-- **The layout of a payload vector**: the canonical ABI record (tuple) layout of its types
(`ABI.recordLayout`), the same as `ABI.layout .i32 (.tuple (Wit.toWitList ps))`
(`valsLayout_toWit`). -/
def valsLayout (ps : List PTy) : ABI.Layout := ABI.recordLayout (ps.map PTy.layout)

/-- The bytes of a payload vector, tail padding included (REF `elem_size(tuple)`). -/
def valsWidth (ps : List PTy) : Nat := (valsLayout ps).size

/-- The alignment of a payload vector (REF `alignment(tuple)`; `1` for no payload). -/
def valsAlign (ps : List PTy) : Nat := (valsLayout ps).alignment.bytes

/-- A little-endian `i32` (exactly four bytes). -/
def le32 (bs : List UInt8) : Option (BitVec 32) :=
  match le32s bs with
  | some [v] => some v
  | _ => none

/-- The little-endian unsigned integer in the first `k` bytes of `bs` (REF `load_int` of `k`
bytes, unsigned); none when fewer than `k` bytes are left. -/
def leN (k : Nat) (bs : List UInt8) : Option Nat :=
  if k ≤ bs.length then some (Logic.Core.leNat (bs.take k)) else none

/-- A `(ptr, len)` pair of little-endian `i32`s at the head of `bs`, and the rest. -/
def readPtrLen (bs : List UInt8) : Option (Nat × Nat × List UInt8) :=
  (le32 (bs.take 4)).bind fun p =>
    (le32 ((bs.drop 4).take 4)).map fun n => (p.toNat, n.toNat, bs.drop 8)

/-- `n` values read one after the other by `f`, and the rest. -/
def readMany {α : Type} (f : List UInt8 → Option (α × List UInt8)) :
    Nat → List UInt8 → Option (List α × List UInt8)
  | 0, bs => some ([], bs)
  | n + 1, bs => (f bs).bind fun (v, rest) =>
      (readMany f n rest).map fun (vs, rest') => (v :: vs, rest')

/-- A list of exactly `n` values as a vector. -/
def vecOf? {α : Type} (n : Nat) (vs : List α) : Option (Vector α n) :=
  if h : vs.length = n then some ⟨vs.toArray, by simpa using h⟩ else none

/-- A case index below `n`. -/
def finOf? (n i : Nat) : Option (Fin n) := if h : i < n then some ⟨i, h⟩ else none

mutual
/-- **One payload value** at the head of `bs`, and the rest (REF `load`). `seg a n` is the
memory segment `[a, a + n)` (none when out of bounds: REF `trap_if(ptr + n > len(memory))`).

* Scalars little-endian (signed ones as two's complement); `bool` any nonzero byte (REF
  `convert_int_to_bool`); `f32`, `f64` with NaNs canonicalised (REF `decode_i32_as_float`:
  `ABI.canonicalizeNaN`); `char` a Unicode scalar value (REF `convert_i32_to_char`:
  `ABI.convertI32ToChar?`, surrogates and values `≥ 0x110000` are no value).
* Strings: the UTF-8 bytes `[ptr, ptr + len)` (REF `load_string_from_range`: alignment `1`,
  invalid UTF-8 traps); `list t` (REF `load_list_from_range`): `ptr` must be aligned to `t`
  (`unalignedPointer`), then `len` elements of `t` at `ptr + i * t.width` (`len * t.width`
  bytes, every byte consumed), each read in turn, indirections included; `bytes = list<u8>`
  is the octets.
* In place, from the value's `t.width` bytes: `list<t, n>` its `n` elements (REF
  `load_list_from_valid_range`); records and tuples their fields at aligned offsets
  (`readFieldsAt`, `readFields`, REF `load_record`); variants, `option`, `result` the
  discriminant (REF `load_int` of `discBytes` bytes) and the payload of that case at
  `caseOffset` (REF `load_variant`: a discriminant `≥` the number of cases is no value,
  `trap_if(case_index >= len(cases))`); `enum` its discriminant, in range; `flags` the
  low `n` bits of its one, two or four bytes (REF `unpack_flags_from_int`: higher bits are
  ignored).
* Handles: **none**. Memory alone gives an `own` handle no meaning (its index names an entry of
  the module's resource table at the call); owned handles are read by the resource layer
  `Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own` (top-level `own` payload fields, read
  as `u32` indices and resolved in an explicit resource table). A `borrow` is never a stored
  value (`PTy.Val (.borrow r) = Empty`).

Every value consumes exactly `PTy.width t` bytes (`readVal_rest`). -/
def readVal (seg : Nat → Nat → Option (List UInt8)) :
    (t : PTy) → List UInt8 → Option (t.Val × List UInt8)
  | .bool, b :: bs => some (b != 0, bs)
  | .bool, [] => none
  | .s32, bs => (le32 (bs.take 4)).map fun v => (Int32.ofBitVec v, bs.drop 4)
  | .u32, bs => (le32 (bs.take 4)).map fun v => (UInt32.ofBitVec v, bs.drop 4)
  | .s64, bs => (le64 (bs.take 8)).map fun v => (Int64.ofBitVec v, bs.drop 8)
  | .u64, bs => (le64 (bs.take 8)).map fun v => (UInt64.ofBitVec v, bs.drop 8)
  | .string, bs => (readPtrLen bs).bind fun (p, n, rest) =>
      (seg p n).bind fun cs => (utf8? cs).map fun str => (str, rest)
  | .list t, bs => (readPtrLen bs).bind fun (p, n, rest) =>
      if p % PTy.align t = 0 then
        (seg p (n * PTy.width t)).bind fun es =>
          (readMany (readVal seg t) n es).bind fun (vs, r) =>
            if r.isEmpty then some (vs, rest) else none
      else none
  | .s8, bs => (leN 1 bs).map fun v => (Int8.ofBitVec (BitVec.ofNat 8 v), bs.drop 1)
  | .u8, b :: bs => some (b, bs)
  | .u8, [] => none
  | .s16, bs => (leN 2 bs).map fun v => (Int16.ofBitVec (BitVec.ofNat 16 v), bs.drop 2)
  | .u16, bs => (leN 2 bs).map fun v => (UInt16.ofBitVec (BitVec.ofNat 16 v), bs.drop 2)
  | .f32, bs => (le32 (bs.take 4)).map fun v => (ABI.canonicalizeNaN .f32 v, bs.drop 4)
  | .f64, bs => (le64 (bs.take 8)).map fun v => (ABI.canonicalizeNaN .f64 v, bs.drop 8)
  | .char, bs => (le32 (bs.take 4)).bind fun v =>
      (ABI.convertI32ToChar? v).map fun c => (c, bs.drop 4)
  | .fixedList t n, bs => (readMany (readVal seg t) n bs).bind fun x =>
      (vecOf? n x.1).map fun v => (v, bs.drop (PTy.width (.fixedList t n)))
  | .record fs, bs =>
      (readFieldsAt seg fs 0 (bs.take (PTy.width (.record fs)))).map fun v =>
        (v, bs.drop (PTy.width (.record fs)))
  | .tuple ts, bs =>
      (readFields seg ts 0 (bs.take (PTy.width (.tuple ts)))).map fun v =>
        (v, bs.drop (PTy.width (.tuple ts)))
  | .variant cs, bs => (leN (discBytes cs.length) bs).bind fun i =>
      (readCase seg cs i (((bs.take (PTy.width (.variant cs))).drop
          (caseOffset (PTy.caseLayouts cs))))).map fun v =>
        (v, bs.drop (PTy.width (.variant cs)))
  | .enum cs, bs => (leN (discBytes cs.length) bs).bind fun i =>
      (finOf? cs.length i).map fun v => (v, bs.drop (PTy.width (.enum cs)))
  | .option t, bs => (leN 1 bs).bind fun i =>
      (match i with
        | 0 => some none
        | 1 => (readVal seg t ((bs.take (PTy.width (.option t))).drop
            (caseOffset [none, some (PTy.layout t)]))).map fun x => some x.1
        | _ => none : Option (Option t.Val)).map fun v => (v, bs.drop (PTy.width (.option t)))
  | .result ok err, bs => (leN 1 bs).bind fun i =>
      (match i with
        | 0 => (readOpt seg ok ((bs.take (PTy.width (.result ok err))).drop
            (caseOffset [PTy.optLayout ok, PTy.optLayout err]))).map Sum.inl
        | 1 => (readOpt seg err ((bs.take (PTy.width (.result ok err))).drop
            (caseOffset [PTy.optLayout ok, PTy.optLayout err]))).map Sum.inr
        | _ => none : Option (PTy.OptVal ok ⊕ PTy.OptVal err)).map fun v =>
          (v, bs.drop (PTy.width (.result ok err)))
  | .flags ls, bs => (leN (ABI.flagsAlignment ls.length).bytes bs).map fun i =>
      (BitVec.ofNat ls.length i, bs.drop (PTy.width (.flags ls)))
  | .own _, _ => none
  | .borrow _, _ => none

/-- **The fields of a payload vector** in the payload area `area`, from the offset `cur`
(REF `load_record`): each field at `alignTo cur (alignment t)` (`ABI.placeField`), read from
exactly its `t.width` bytes; the next field from the end of this one. Padding bytes are not
read. -/
def readFields (seg : Nat → Nat → Option (List UInt8)) :
    (ps : List PTy) → Nat → List UInt8 → Option (PTy.Vals ps)
  | [], _, _ => some ()
  | t :: ps, cur, area =>
      let off := ABI.alignTo cur (PTy.layout t).alignment
      (readVal seg t ((area.drop off).take (PTy.width t))).bind fun (v, _) =>
        (readFields seg ps (off + PTy.width t) area).map fun vs => (v, vs)

/-- The fields of a record, as `readFields` (names are not read). -/
def readFieldsAt (seg : Nat → Nat → Option (List UInt8)) :
    (fs : List (String × PTy)) → Nat → List UInt8 → Option (PTy.FieldVals fs)
  | [], _, _ => some ()
  | (_, t) :: fs, cur, area =>
      let off := ABI.alignTo cur (PTy.layout t).alignment
      (readVal seg t ((area.drop off).take (PTy.width t))).bind fun (v, _) =>
        (readFieldsAt seg fs (off + PTy.width t) area).map fun vs => (v, vs)

/-- The payload of case `i` of a variant, at the head of `bs`; none past the last case. -/
def readCase (seg : Nat → Nat → Option (List UInt8)) :
    (cs : List (String × Option PTy)) → Nat → List UInt8 → Option (PTy.CaseVals cs)
  | [], _, _ => none
  | (_, o) :: _, 0, bs => (readOpt seg o bs).map Sum.inl
  | _ :: cs, i + 1, bs => (readCase seg cs i bs).map Sum.inr

/-- An optional payload at the head of `bs`: nothing to read when absent. -/
def readOpt (seg : Nat → Nat → Option (List UInt8)) :
    (o : Option PTy) → List UInt8 → Option (PTy.OptVal o)
  | none, _ => some ()
  | some t, bs => (readVal seg t bs).map Prod.fst
end

/-- **A payload vector** in its payload area (the `valsWidth ps` bytes at an address aligned to
`valsAlign ps`): the canonical ABI tuple of its types. -/
def readVals (seg : Nat → Nat → Option (List UInt8)) (ps : List PTy) (area : List UInt8) :
    Option (PTy.Vals ps) :=
  readFields seg ps 0 area

/-- The segment `[a, a + n)` of a list of bytes, for examples of the decoder. -/
def listSeg (mem : List UInt8) (a n : Nat) : Option (List UInt8) :=
  if a + n ≤ mem.length then some ((mem.drop a).take n) else none

/-- An example memory (96 bytes): `"hi"` at `8`, `"é"` (UTF-8 `C3 A9`) at `10`, the `u32`s `7`,
`9` at `12`; the pairs `(8, 2)`, `(10, 2)` at `20` (a list of the two strings); the invalid UTF-8
byte `FF` at `36`; the pairs `(8, 2)`, `(36, 1)` at `40` (a list of strings, the second invalid
UTF-8); `(8, 2)`, `(200, 2)` at `56` (the second out of bounds); `(12, 2)`, `(16, 1)` at `72` (a
`list<list<u32>>`); `(13, 1)` at `88` (a `list<u32>` pair whose pointer is misaligned). -/
def exMem : List UInt8 :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0x68, 0x69, 0xC3, 0xA9, 7, 0, 0, 0, 9, 0, 0, 0,
   8, 0, 0, 0, 2, 0, 0, 0, 10, 0, 0, 0, 2, 0, 0, 0, 0xFF, 0, 0, 0,
   8, 0, 0, 0, 2, 0, 0, 0, 36, 0, 0, 0, 1, 0, 0, 0,
   8, 0, 0, 0, 2, 0, 0, 0, 200, 0, 0, 0, 2, 0, 0, 0,
   12, 0, 0, 0, 2, 0, 0, 0, 16, 0, 0, 0, 1, 0, 0, 0,
   13, 0, 0, 0, 1, 0, 0, 0]

/-- A call observing the memory `exMem`, for examples of the decoder. -/
def exCall (args : List Val) : Callout := ⟨("wit", "node"), args, some exMem.toByteArray⟩

/-! ## The signature and the decoder -/

variable (S : WitSig) (tagOf : BitVec 32 → Option S.Tag)

/-- Writer events of the tagged-AST writer of `S`. -/
abbrev WitWEv := WEv (Σ t, S.toAstSig.Arg t) (BitVec 32)

/-- The named imports of the typed AST writer through memory. -/
structure WitImports where
  node : String × String := ("wit", "node")
  accept : String × String := ("wit", "accept")

/-- **`node(tag, payload, children, n)`**: the tag `tagOf tag` with its payload vector at
`payload` (the canonical ABI tuple of `S.params t`: `payload` aligned to `valsAlign`, the
`valsWidth` bytes in bounds) and the `n` little-endian child handles at
`[children, children + 4n)` (a `list<u32>` range: `children` aligned to four), when the tag
admits that many children. This success projection rejects unsupported schemas; runtime
hosts use `Checked.Defs` for typed rejection. -/
def Callout.witNode (o : Callout) : Option ((Σ t, S.toAstSig.Arg t) × List (BitVec 32)) :=
  match o.args with
  | [.num ⟨.int .i32, tg⟩, .num ⟨.int .i32, pp⟩, .num ⟨.int .i32, cp⟩, .num ⟨.int .i32, n⟩] =>
      (tagOf tg).bind fun t =>
        if pp.toNat % valsAlign (S.params t) = 0 ∧ cp.toNat % 4 = 0 ∧
            (checkPTys .memoryOnly (S.params t)).isOk = true then
          (o.segment pp.toNat (valsWidth (S.params t))).bind fun bs =>
            (readVals o.segment (S.params t) bs).bind fun a =>
              (o.segment cp.toNat (4 * n.toNat)).bind fun cs => (le32s cs).bind fun hs =>
                if (S.arity t).Admits hs.length then some (⟨t, a⟩, hs) else none
        else none
  | _ => none

/-- **The write of an answered call**: `node` answered with a handle. -/
def witWrite (ix : WitImports) (o : Callout) (w : HostReply) : Option (WitWEv S) := do
  let r ← replyI32 w
  if o.imp = ix.node then
    let (op, hs) ← Callout.witNode S tagOf o
    return .write op hs r
  else none

/-- A call of `accept(h)`. -/
def witAccept (ix : WitImports) (o : Callout) : Option (WitWEv S) :=
  if o.imp = ix.accept then (Callout.args1 Callout.i32? o.args).map .accept else none

/-- The roles of the typed AST writer: accepts at calls, writes at answers. -/
def witRoles (ix : WitImports) : Roles Unit (WitWEv S) Unit Unit where
  callIn := witAccept S ix
  answerIn := witWrite S tagOf ix

/-- **The writer traces of a module** through the typed AST imports. -/
def witTraces (P : Numerics.Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat)
    (m : Module) (ix : WitImports) : Set (List (WitWEv S)) :=
  inputsOf (some .enter) '' tagTraces P Envs memIdx m (witRoles S tagOf ix)

/-- **The writer language of a module** through the typed AST imports. -/
def witWriterLang (P : Numerics.Profile) (Envs : Store Nat → SEnv UImp → Prop) (memIdx : Nat)
    (m : Module) (ix : WitImports) (pol : Policy (BitVec 32)) : Set (AST S.toAstSig) :=
  writerLang (astW S.toAstSig) pol (witTraces S tagOf P Envs memIdx m ix)

/-! ## The example -/

/-- The tags of `calcSig`. -/
inductive CalcTag where
  | num
  | add
  deriving DecidableEq, Repr

/-- **Numbers and sums**: `num` carries an `s64` and no children, `add` exactly two. -/
def calcSig : WitSig where
  Tag := CalcTag
  params
    | .num => [.s64]
    | .add => []
  arity
    | .num => .fixed 0
    | .add => .fixed 2

/-- The tag numbers: `0` is `num`, `1` is `add`. -/
def calcTagOf (tg : BitVec 32) : Option calcSig.Tag :=
  if tg = 0 then some CalcTag.num else if tg = 1 then some CalcTag.add else none

/-- The body of `run`. -/
def calcBody : List Instr :=
  [.intConst .i32 16, .intConst .i64 1, .intStore .i64 none ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 0, .intConst .i32 16, .intConst .i32 0, .intConst .i32 0, .call ⟨0⟩,
   .localSet ⟨0⟩,
   .intConst .i32 16, .intConst .i64 2, .intStore .i64 none ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 0, .intConst .i32 16, .intConst .i32 0, .intConst .i32 0, .call ⟨0⟩,
   .localSet ⟨1⟩,
   .intConst .i32 0, .localGet ⟨0⟩, .intStore .i32 none ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 4, .localGet ⟨1⟩, .intStore .i32 none ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 1, .intConst .i32 0, .intConst .i32 0, .intConst .i32 2, .call ⟨0⟩,
   .call ⟨1⟩]

/-- **The module.** -/
def calcMod : Module where
  types := [Ast.tyTag, tyAcc, tyRun]
  imports := [⟨"wit", "node", .func ⟨0⟩⟩, ⟨"wit", "accept", .func ⟨1⟩⟩]
  memories := [⟨.i32, ⟨1, none⟩⟩]
  funcs := [⟨⟨2⟩, [.i32, .i32], calcBody⟩]
  exports := [⟨"run", .func ⟨2⟩⟩]

/-- The number `num k`. -/
def numTree (k : Int64) : AST calcSig.toAstSig :=
  AST.node (S := calcSig.toAstSig) CalcTag.num (k, ()) []

/-- **The sum `add(num 1, num 2)`.** -/
def addTree : AST calcSig.toAstSig :=
  AST.node (S := calcSig.toAstSig) CalcTag.add () [numTree 1, numTree 2]

/-! ## The example with string payloads -/

/-- The tags of `appSig`. -/
inductive AppTag where
  | var
  | app
  deriving DecidableEq, Repr

/-- **Variables and applications**: `var` carries a `string` and no children, `app` exactly two. -/
def appSig : WitSig where
  Tag := AppTag
  params
    | .var => [.string]
    | .app => []
  arity
    | .var => .fixed 0
    | .app => .fixed 2

/-- The tag numbers: `0` is `var`, `1` is `app`. -/
def appTagOf (tg : BitVec 32) : Option appSig.Tag :=
  if tg = 0 then some AppTag.var else if tg = 1 then some AppTag.app else none

/-- The payload of `var`: the pair `(ptr, len) = (24, 1)`, as one little-endian `i64`. -/
def strRef : BitVec 64 := 0x100000018

/-- The body of `run`. -/
def appBody : List Instr :=
  [.intConst .i32 24, .intConst .i32 0x66, .intStore .i32 (some .i8) ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 16, .intConst .i64 strRef, .intStore .i64 none ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 0, .intConst .i32 16, .intConst .i32 0, .intConst .i32 0, .call ⟨0⟩,
   .localSet ⟨0⟩,
   .intConst .i32 24, .intConst .i32 0x78, .intStore .i32 (some .i8) ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 16, .intConst .i64 strRef, .intStore .i64 none ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 0, .intConst .i32 16, .intConst .i32 0, .intConst .i32 0, .call ⟨0⟩,
   .localSet ⟨1⟩,
   .intConst .i32 0, .localGet ⟨0⟩, .intStore .i32 none ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 4, .localGet ⟨1⟩, .intStore .i32 none ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 1, .intConst .i32 0, .intConst .i32 0, .intConst .i32 2, .call ⟨0⟩,
   .call ⟨1⟩]

/-- **The module.** -/
def appMod : Module where
  types := [Ast.tyTag, tyAcc, tyRun]
  imports := [⟨"wit", "node", .func ⟨0⟩⟩, ⟨"wit", "accept", .func ⟨1⟩⟩]
  memories := [⟨.i32, ⟨1, none⟩⟩]
  funcs := [⟨⟨2⟩, [.i32, .i32], appBody⟩]
  exports := [⟨"run", .func ⟨2⟩⟩]

/-- The variable `var x`. -/
def varTree (x : String) : AST appSig.toAstSig :=
  AST.node (S := appSig.toAstSig) AppTag.var (x, ()) []

/-- **The application `app(var "f", var "x")`.** -/
def appTree : AST appSig.toAstSig :=
  AST.node (S := appSig.toAstSig) AppTag.app () [varTree "f", varTree "x"]

/-! ## The example with byte-string and list payloads -/

/-- The tags of `binSig`. -/
inductive BinTag where
  | blob
  | seq
  | pair
  deriving DecidableEq, Repr

/-- **Blobs, sequences and pairs**: `blob` carries `bytes` (`list<u8>`), `seq` a `list<u32>`,
neither has children; `pair` has no payload and exactly two children. -/
def binSig : WitSig where
  Tag := BinTag
  params
    | .blob => [.bytes]
    | .seq => [.list .u32]
    | .pair => []
  arity
    | .blob => .fixed 0
    | .seq => .fixed 0
    | .pair => .fixed 2

/-- The tag numbers: `0` is `blob`, `1` is `seq`, `2` is `pair`. -/
def binTagOf (tg : BitVec 32) : Option binSig.Tag :=
  if tg = 0 then some BinTag.blob else if tg = 1 then some BinTag.seq
  else if tg = 2 then some BinTag.pair else none

/-- The two `u32`s `7`, `9`, as one little-endian `i64`. -/
def seqWords : BitVec 64 := 0x900000007

/-- The payload of `seq`: the pair `(ptr, len) = (24, 2)`, as one little-endian `i64`. -/
def seqRef : BitVec 64 := 0x200000018

/-- The body of `run`. -/
def binBody : List Instr :=
  [.intConst .i32 24, .intConst .i32 0xFF, .intStore .i32 (some .i8) ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 16, .intConst .i64 strRef, .intStore .i64 none ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 0, .intConst .i32 16, .intConst .i32 0, .intConst .i32 0, .call ⟨0⟩,
   .localSet ⟨0⟩,
   .intConst .i32 24, .intConst .i64 seqWords, .intStore .i64 none ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 16, .intConst .i64 seqRef, .intStore .i64 none ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 1, .intConst .i32 16, .intConst .i32 0, .intConst .i32 0, .call ⟨0⟩,
   .localSet ⟨1⟩,
   .intConst .i32 0, .localGet ⟨0⟩, .intStore .i32 none ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 4, .localGet ⟨1⟩, .intStore .i32 none ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 2, .intConst .i32 0, .intConst .i32 0, .intConst .i32 2, .call ⟨0⟩,
   .call ⟨1⟩]

/-- **The module.** -/
def binMod : Module where
  types := [Ast.tyTag, tyAcc, tyRun]
  imports := [⟨"wit", "node", .func ⟨0⟩⟩, ⟨"wit", "accept", .func ⟨1⟩⟩]
  memories := [⟨.i32, ⟨1, none⟩⟩]
  funcs := [⟨⟨2⟩, [.i32, .i32], binBody⟩]
  exports := [⟨"run", .func ⟨2⟩⟩]

/-- The blob `blob bs`. -/
def blobTree (bs : List UInt8) : AST binSig.toAstSig :=
  AST.node (S := binSig.toAstSig) BinTag.blob (bs, ()) []

/-- The sequence `seq ws`. -/
def seqTree (ws : List UInt32) : AST binSig.toAstSig :=
  AST.node (S := binSig.toAstSig) BinTag.seq (ws, ()) []

/-- **The pair `pair(blob [0xFF], seq [7, 9])`.** -/
def binTree : AST binSig.toAstSig :=
  AST.node (S := binSig.toAstSig) BinTag.pair () [blobTree [0xFF], seqTree [7, 9]]

/-! ## The example with record, option and char payloads -/

/-- The tags of `glyphSig`. -/
inductive GlyphTag where
  | glyph
  | pair
  deriving DecidableEq, Repr

/-- `record glyph { ch: char, size: option<u8> }`: eight bytes aligned to four, `ch` at `0`,
the discriminant of `size` at `4` and its payload at `5`, two bytes of tail padding. -/
def glyphTy : PTy := .record [("ch", .char), ("size", .option .u8)]

/-- **Glyphs and pairs**: `glyph` carries one `glyph` record and no children, `pair` has no
payload and exactly two children. -/
def glyphSig : WitSig where
  Tag := GlyphTag
  params
    | .glyph => [glyphTy]
    | .pair => []
  arity
    | .glyph => .fixed 0
    | .pair => .fixed 2

/-- The tag numbers: `0` is `glyph`, `1` is `pair`. -/
def glyphTagOf (tg : BitVec 32) : Option glyphSig.Tag :=
  if tg = 0 then some GlyphTag.glyph else if tg = 1 then some GlyphTag.pair else none

/-- The record `{ ch: 'a', size: some(7) }` as one little-endian `i64`: the bytes
`61 00 00 00 01 07 00 00`. -/
def glyphA : BitVec 64 := 0x0000070100000061

/-- The record `{ ch: 'λ', size: none }` (`λ` is `U+03BB`) as one little-endian `i64`: the
bytes `BB 03 00 00 00 00 00 00`. -/
def glyphB : BitVec 64 := 0x00000000000003BB

/-- The body of `run`. -/
def glyphBody : List Instr :=
  [.intConst .i32 16, .intConst .i64 glyphA, .intStore .i64 none ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 0, .intConst .i32 16, .intConst .i32 0, .intConst .i32 0, .call ⟨0⟩,
   .localSet ⟨0⟩,
   .intConst .i32 16, .intConst .i64 glyphB, .intStore .i64 none ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 0, .intConst .i32 16, .intConst .i32 0, .intConst .i32 0, .call ⟨0⟩,
   .localSet ⟨1⟩,
   .intConst .i32 0, .localGet ⟨0⟩, .intStore .i32 none ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 4, .localGet ⟨1⟩, .intStore .i32 none ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 1, .intConst .i32 0, .intConst .i32 0, .intConst .i32 2, .call ⟨0⟩,
   .call ⟨1⟩]

/-- **The module.** -/
def glyphMod : Module where
  types := [Ast.tyTag, tyAcc, tyRun]
  imports := [⟨"wit", "node", .func ⟨0⟩⟩, ⟨"wit", "accept", .func ⟨1⟩⟩]
  memories := [⟨.i32, ⟨1, none⟩⟩]
  funcs := [⟨⟨2⟩, [.i32, .i32], glyphBody⟩]
  exports := [⟨"run", .func ⟨2⟩⟩]

/-- The glyph `glyph { ch: c, size: k }`. -/
def glyphTree (c : Char) (k : Option UInt8) : AST glyphSig.toAstSig :=
  AST.node (S := glyphSig.toAstSig) GlyphTag.glyph ((c, k, ()), ()) []

/-- **The pair `pair(glyph { 'a', some(7) }, glyph { 'λ', none })`.** -/
def glyphPairTree : AST glyphSig.toAstSig :=
  AST.node (S := glyphSig.toAstSig) GlyphTag.pair () [glyphTree 'a' (some 7), glyphTree 'λ' none]

end Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst
