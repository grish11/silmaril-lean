module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Cons.Thms
public import Silmaril.Wasm.Verify.Kernel.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAstLive
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAppLive
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitBinLive

/-!
# Typed payloads and fixed arities through linear memory: soundness and non-vacuity

**The canonical ABI layout** (`layout_toWit`, `width_toWit`, `align_toWit`, `valsLayout_toWit`,
`valsWidth_toWit`, `valsAlign_toWit`): the layout of a payload type is `ABI.layout .i32` of its
WIT type `Wit.toWit t` (REF `elem_size`, `alignment`), and the layout of a payload vector is that
of the WIT tuple of its types; kernel-checked sizes with padding `ex_width_*`.

**Payloads** (`readPtrLen_encode`, `readVal_rest`, `readVal_string`, `readVal_bytes`,
`readVal_list`, `readVal_list_misaligned`, `readVals_single`): a `(ptr, len)` pair written as
two little-endian `i32`s is read back; every payload value consumes exactly `PTy.width t` bytes;
strings, byte strings and lists are read through their pair from the memory at the call, lists
only at an aligned pointer. Kernel-checked examples over the memory `exMem` (`listSeg`):
`ex_string`, `ex_string_utf8` (two-byte UTF-8), `ex_bytes`, `ex_bytes_not_utf8`, `ex_list_u32`,
`ex_list_string` (two levels of indirection), `ex_list_list` (`list<list<u32>>`), `ex_vals`
(`u32` then `string`), `ex_vals_padded` (`bool` then `u32`: three padding bytes, not read),
`ex_vals_padded64` (`u32` then `s64`).

**Malformed inputs decode to no value** (`ex_bad_utf8`, `ex_out_of_bounds`, `ex_list_oob`,
`ex_list_misaligned`, `ex_list_string_bad_utf8`, `ex_list_string_oob`,
`ex_list_list_misaligned`, `ex_short`), and **malformed calls to no event** (`ex_node_*` over
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

universe u

variable {Resource : Type u}

/-- **The layout of a payload type is its canonical ABI layout** (memory32). -/
theorem layout_toWit (t : PTy) :
    ABI.layout .i32 (toWit t : WIT.ClosedType Resource) = PTy.layout t :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.layout_toWit t

/-- The size of a payload value is REF `elem_size` of its WIT type. -/
theorem width_toWit (t : PTy) :
    (ABI.layout .i32 (toWit t : WIT.ClosedType Resource)).size = PTy.width t := by
  rw [layout_toWit]; rfl

/-- The alignment of a payload value is REF `alignment` of its WIT type. -/
theorem align_toWit (t : PTy) :
    (ABI.layout .i32 (toWit t : WIT.ClosedType Resource)).alignment.bytes = PTy.align t := by
  rw [layout_toWit]; rfl

/-- **The layout of a payload vector is the canonical ABI layout of its WIT tuple.** -/
theorem valsLayout_toWit (ps : List PTy) :
    ABI.layout .i32 (.tuple (toWitList ps) : WIT.ClosedType Resource) = valsLayout ps :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.valsLayout_toWit ps

theorem valsWidth_toWit (ps : List PTy) :
    (ABI.layout .i32 (.tuple (toWitList ps) : WIT.ClosedType Resource)).size = valsWidth ps := by
  rw [valsLayout_toWit]; rfl

theorem valsAlign_toWit (ps : List PTy) :
    (ABI.layout .i32 (.tuple (toWitList ps) : WIT.ClosedType Resource)).alignment.bytes =
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

/-- **A byte-string payload**: its pair and the segment it names. -/
theorem readVal_bytes {seg : Nat → Nat → Option (List UInt8)} {bs rest cs : List UInt8}
    {p n : Nat} (hp : readPtrLen bs = some (p, n, rest)) (hc : seg p n = some cs) :
    readVal seg .bytes bs = some (cs, rest) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitAst.readVal_bytes hp hc

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

end Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst
