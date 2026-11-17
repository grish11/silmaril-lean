module

public import Silmaril.Wasm.Component.Reference.Sound.Defs
public import Silmaril.Wasm.Component.Binary.Defs

/-!
# Components whose exports take lists: the fragment and its lowering

The reference soundness results for simple components (`Silmaril.Wasm.Component.Reference.Simple`,
`…Reference.Sound`) cover scalar parameters only: their lowering is pure (`lowerFlatAt_toClosed`).
A parameter of type `list<t>` is lowered by the caller into the callee's linear memory
(canonical ABI `store_list_into_range`, `CanonicalABI.md`): it calls the callee's `realloc`
(a nested `canon lift` of a core function, `Canon.reallocProg`), checks the pointer's alignment
and bounds, and writes the elements; the core function then receives `(ptr, len)`.

This file defines the fragment of such components and the objects its soundness theorem
relates.

## The fragment

* `LTy`: the types `s32`, `u32`, `s64`, `list<t>`, `tuple<t, …>` and named records
  `record name { l: t, … }` (so `list<s32>`, `list<list<s32>>`,
  `list<record { coeffs: list<tuple<u32, s64>>, bound: s64 }>`, …), `LVal` their values,
  `LTy.check`, the reference values `LVal.toRef`, the resolved reference types `LTy.toClosed`
  and the canonical-ABI layouts `LTy.layout` (`size`, `align`); the parameters of an export are
  `s32`s and lists (`LTy.topLevel`);
* the emitters: `LTy.emit` (reference definitions) and `LTy.emitB` (binary type items,
  `tySections`), with one type definition per list and tuple type, and for a record its type
  definition followed by the export of that type under the record's name (an exported function
  may only mention records through named types; the export is the type index the parameter
  refers to);
* `ListExport`: an export `name: func(params) -> bool`, the `canon lift` of the core export
  `core` with the options `(memory 0) (realloc 0)`;
* `ListComp`: one core instance of a module (instantiated without imports), exporting the memory
  `memName` (the module's memory `memIdx`, which is store address `memIdx` of the import-free
  instance) and the allocator `reallocName`, and the exports. `ListComp.toRef` is the reference
  component and `ListComp.toAst` the binary component, with the same definitions in the same
  order (core module, core instance, aliases of the memory, of the allocator and of the lifted
  core functions, the list types and function types, the lifts, the exports), so that
  `toRef?` of `toAst` (`Silmaril.Project.WasmComponents.Ref.toRef?`) is `toRef` when the core
  module bytes decode to the module.

## The lowering, at the Core level

`LStore`, `LList`, `LElems` and `LParams` describe, as a relation between Core 3.0 stores
(`Silmaril.Wasm.Execution.Core.Store Nat`), what the reference lowering of list arguments does:

* `ReallocRun P ra s align size p s'`: a returning Core run of the allocator (function address
  `ra`) on `(0, 0, align, size)` from `s`, answering `p` in the store `s'`;
* `LList`: `store_list_into_range`: the allocator, asked for the element alignment, returns an
  aligned `q` with the list's `len · size` bytes in the memory (address `ma`), then the elements
  are stored (`LElems`) at `q`, `q + size`, …;
* `LStore`: `store` of one value: an `s32` or `u32` as its 4 little-endian bytes (`le32`), an
  `s64` as its 8 (`le64`), a list as `store_list_into_range` followed by the `(ptr, len)` pair,
  a tuple or record field by field (`LFields`, `store_record`: each field at the cursor rounded
  up to its alignment);
* `LParams`: the parameters left to right, each list lowered to the flat `(ptr, len)`.

The relation is generic in the module: it does not assume anything about the allocator, whose
runs it quantifies over. What a particular allocator guarantees (for example disjoint blocks
above a bump pointer) is proved about its module, and turns `LParams` into a statement about the
final memory.

## The target

`AcceptSound c`: for a well-formed `ListComp` (`Good`, `Inst`), every behaviour of the reference
machine (`exportBehaviours` over `core3P P`, the reference host, every component choice
profile) that instantiates `c.toRef` and calls export `x` on the reference images of well-typed
values `vs` and **returns `true`** has a Core-level explanation: the lowering `LParams` of `vs`
from the instance store to some store `s` with flat arguments `fl`, and a Core run of the lifted
core function from `s` on `fl` returning one `i32` other than `0`. Traps, divergence and `false`
answers are not constrained (the statement is the one that acceptor soundness needs).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference.ListLift

open Silmaril.Wasm.Component
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)

/-! ## Types and values -/

/-- Parameter and element types: `s32`, `u32`, `s64`, lists, tuples and records. A tuple
`tuple t ts` is `tuple<t, ts…>` and a record `record name l t fs` is `record { l: t, fs… }`: both
have at least one element, as the Component Model requires. A record carries the name under
which the component exports its type (an exported function may only mention records through
named types). -/
inductive LTy where
  | s32
  | list (t : LTy)
  | u32
  | s64
  | tuple (t : LTy) (ts : List LTy)
  | record (name : String) (l : String) (t : LTy) (fs : List (String × LTy))
  deriving Repr, Inhabited

/-- Values of the types: a tuple or record value is the list of its field values. -/
inductive LVal where
  | s32 (x : BitVec 32)
  | list (vs : List LVal)
  | u32 (x : BitVec 32)
  | s64 (x : BitVec 64)
  | fields (vs : List LVal)
  deriving Repr, Inhabited

mutual
/-- `v` has type `t`. -/
def LTy.check : LTy → LVal → Bool
  | .s32, .s32 _ => true
  | .u32, .u32 _ => true
  | .s64, .s64 _ => true
  | .list t, .list vs => LTy.checkList t vs
  | .tuple t ts, .fields vs => LTy.checkFields (t :: ts) vs
  | .record _ _ t fs, .fields vs => LTy.checkFields (t :: fs.map (·.2)) vs
  | _, _ => false

/-- Every value of `vs` has type `t`. -/
def LTy.checkList (t : LTy) : List LVal → Bool
  | [] => true
  | v :: vs => t.check v && LTy.checkList t vs

/-- The values `vs` have the types `ts`, in order. -/
def LTy.checkFields : List LTy → List LVal → Bool
  | [], [] => true
  | t :: ts, v :: vs => t.check v && LTy.checkFields ts vs
  | _, _ => false
end

/-- `vs` have the types `ts`, in order. -/
def LTy.checkParams : List LTy → List LVal → Bool
  | [], [] => true
  | t :: ts, v :: vs => t.check v && LTy.checkParams ts vs
  | _, _ => false

mutual
/-- The reference value of a value (an `s32` or `s64` by its two's-complement reading, a `u32`
by its unsigned reading, a tuple or record as the positional record value). -/
def LVal.toRef : LVal → Silmaril.Wasm.Component.Value.Val
  | .s32 x => .int .s32 x.toInt
  | .list vs => .list (LVal.toRefList vs)
  | .u32 x => .int .u32 x.toNat
  | .s64 x => .int .s64 x.toInt
  | .fields vs => .record (LVal.toRefList vs)

/-- `LVal.toRef` on lists. -/
def LVal.toRefList : List LVal → List Silmaril.Wasm.Component.Value.Val
  | [] => []
  | v :: vs => v.toRef :: LVal.toRefList vs
end

open Silmaril.Wasm.Component.Runtime (RtId) in
mutual
/-- The resolved reference type of a type. -/
def LTy.toClosed : LTy → Silmaril.Wasm.Component.WIT.ClosedType RtId
  | .s32 => .prim .s32
  | .list t => .list t.toClosed
  | .u32 => .prim .u32
  | .s64 => .prim .s64
  | .tuple t ts => .tuple (t.toClosed :: LTy.toClosedList ts)
  | .record _ l t fs => .record ((l, t.toClosed) :: LTy.toClosedFields fs)

/-- `LTy.toClosed` on lists. -/
def LTy.toClosedList : List LTy → List (Silmaril.Wasm.Component.WIT.ClosedType RtId)
  | [] => []
  | t :: ts => t.toClosed :: LTy.toClosedList ts

/-- `LTy.toClosed` on labelled fields. -/
def LTy.toClosedFields :
    List (String × LTy) → List (String × Silmaril.Wasm.Component.WIT.ClosedType RtId)
  | [] => []
  | (l, t) :: fs => (l, t.toClosed) :: LTy.toClosedFields fs
end

mutual
/-- The canonical-ABI layout (alignment, size) of a value of type `t` in memory, with 32-bit
pointers: an `s32` or `u32` takes 4 bytes aligned to 4, an `s64` 8 bytes aligned to 8, a list
its `(ptr, len)` pair (8 bytes aligned to 4), and a tuple or record its fields, each at the
next offset aligned to its alignment, the size rounded up to the largest field alignment
(`ABI.recordLayout`). -/
def LTy.layout : LTy → Silmaril.Wasm.Component.ABI.Layout
  | .s32 => ⟨.four, 1⟩
  | .list _ => ⟨.four, 2⟩
  | .u32 => ⟨.four, 1⟩
  | .s64 => ⟨.eight, 1⟩
  | .tuple t ts => Silmaril.Wasm.Component.ABI.recordLayout (t.layout :: LTy.layoutList ts)
  | .record _ _ t fs =>
    Silmaril.Wasm.Component.ABI.recordLayout (t.layout :: LTy.layoutFields fs)

/-- `LTy.layout` on lists. -/
def LTy.layoutList : List LTy → List Silmaril.Wasm.Component.ABI.Layout
  | [] => []
  | t :: ts => t.layout :: LTy.layoutList ts

/-- `LTy.layout` on labelled fields. -/
def LTy.layoutFields : List (String × LTy) → List Silmaril.Wasm.Component.ABI.Layout
  | [] => []
  | (_, t) :: fs => t.layout :: LTy.layoutFields fs
end

/-- The canonical-ABI size in bytes of a value of type `t` in memory (a multiple of its
alignment). -/
def LTy.size (t : LTy) : Nat := t.layout.size

/-- The canonical-ABI alignment of a value of type `t` in memory. -/
def LTy.align (t : LTy) : Silmaril.Wasm.Component.ABI.Alignment := t.layout.alignment

theorem LTy.size_s32 : LTy.s32.size = 4 := rfl
theorem LTy.size_list (t : LTy) : (LTy.list t).size = 8 := rfl

/-! ## Reference and binary syntax of the types -/

mutual
/-- The reference value type of `t`, with the type definitions it needs from type index `n`;
returns the next free type index. Each list and tuple type is one type definition; a record is
its type definition followed by the export of that type under the record's name (the export is
the next type index, which the value type refers to). -/
def LTy.emit {M : Type} : LTy → Nat → Syntax.VT × List (Syntax.Definition M) × Nat
  | .s32, n => (.prim .s32, [], n)
  | .list t, n =>
    let (v, ds, n') := t.emit n
    (.idx n', ds ++ [.type (.val (.list v))], n' + 1)
  | .u32, n => (.prim .u32, [], n)
  | .s64, n => (.prim .s64, [], n)
  | .tuple t ts, n =>
    let (v, ds, n₁) := t.emit n
    let (vs, ds', n₂) := LTy.emitList ts n₁
    (.idx n₂, ds ++ ds' ++ [.type (.val (.tuple (v :: vs)))], n₂ + 1)
  | .record name l t fs, n =>
    let (v, ds, n₁) := t.emit n
    let (vs, ds', n₂) := LTy.emitFields fs n₁
    (.idx (n₂ + 1), ds ++ ds' ++ [.type (.val (.record ((l, v) :: vs))),
      .export_ { name := name } ⟨.type, n₂⟩ none], n₂ + 2)

/-- `LTy.emit` on lists, left to right. -/
def LTy.emitList {M : Type} : List LTy → Nat →
    List Syntax.VT × List (Syntax.Definition M) × Nat
  | [], n => ([], [], n)
  | t :: ts, n =>
    let (v, ds, n₁) := t.emit n
    let (vs, ds', n₂) := LTy.emitList ts n₁
    (v :: vs, ds ++ ds', n₂)

/-- `LTy.emit` on labelled fields, left to right. -/
def LTy.emitFields {M : Type} : List (String × LTy) → Nat →
    List (String × Syntax.VT) × List (Syntax.Definition M) × Nat
  | [], n => ([], [], n)
  | (l, t) :: fs, n =>
    let (v, ds, n₁) := t.emit n
    let (vs, ds', n₂) := LTy.emitFields fs n₁
    ((l, v) :: vs, ds ++ ds', n₂)
end

/-- An item of the binary type index space: a type definition, or the export of type `i`
under a name. -/
inductive TyItem where
  | def_ (d : Binary.DefType)
  | export_ (name : String) (i : Nat)

mutual
/-- The binary value type of `t`, with its type items from index `n` (as `LTy.emit`). -/
def LTy.emitB : LTy → Nat → Binary.ValType × List TyItem × Nat
  | .s32, n => (.prim .s32, [], n)
  | .list t, n =>
    let (v, ds, n') := t.emitB n
    (.idx n', ds ++ [.def_ (.val (.list v))], n' + 1)
  | .u32, n => (.prim .u32, [], n)
  | .s64, n => (.prim .s64, [], n)
  | .tuple t ts, n =>
    let (v, ds, n₁) := t.emitB n
    let (vs, ds', n₂) := LTy.emitListB ts n₁
    (.idx n₂, ds ++ ds' ++ [.def_ (.val (.tuple (v :: vs)))], n₂ + 1)
  | .record name l t fs, n =>
    let (v, ds, n₁) := t.emitB n
    let (vs, ds', n₂) := LTy.emitFieldsB fs n₁
    (.idx (n₂ + 1), ds ++ ds' ++ [.def_ (.val (.record ((l, v) :: vs))), .export_ name n₂],
      n₂ + 2)

/-- `LTy.emitB` on lists, left to right. -/
def LTy.emitListB : List LTy → Nat → List Binary.ValType × List TyItem × Nat
  | [], n => ([], [], n)
  | t :: ts, n =>
    let (v, ds, n₁) := t.emitB n
    let (vs, ds', n₂) := LTy.emitListB ts n₁
    (v :: vs, ds ++ ds', n₂)

/-- `LTy.emitB` on labelled fields, left to right. -/
def LTy.emitFieldsB : List (String × LTy) → Nat →
    List (String × Binary.ValType) × List TyItem × Nat
  | [], n => ([], [], n)
  | (l, t) :: fs, n =>
    let (v, ds, n₁) := t.emitB n
    let (vs, ds', n₂) := LTy.emitFieldsB fs n₁
    ((l, v) :: vs, ds ++ ds', n₂)
end

/-- The binary sections of type items: each maximal run of type definitions is one `types`
section and each maximal run of type exports one `exports` section, in order. -/
def tySections : List TyItem → List Binary.Section
  | [] => []
  | .def_ d :: is =>
    match tySections is with
    | .types ds :: ss => .types (d :: ds) :: ss
    | ss => .types [d] :: ss
  | .export_ n i :: is =>
    match tySections is with
    | .exports es :: ss => .exports (⟨↑n, ⟨.type, i⟩, none⟩ :: es) :: ss
    | ss => .exports [⟨↑n, ⟨.type, i⟩, none⟩] :: ss

/-- `emit` on named parameters, left to right. -/
def emitParams {M : Type} : List (String × LTy) → Nat →
    List (String × Syntax.VT) × List (Syntax.Definition M) × Nat
  | [], n => ([], [], n)
  | (x, t) :: ps, n =>
    let (v, ds, n₁) := t.emit n
    let (vs, ds', n₂) := emitParams ps n₁
    ((x, v) :: vs, ds ++ ds', n₂)

/-- `emitB` on named parameters, left to right. -/
def emitParamsB : List (String × LTy) → Nat →
    List (String × Binary.ValType) × List TyItem × Nat
  | [], n => ([], [], n)
  | (x, t) :: ps, n =>
    let (v, ds, n₁) := t.emitB n
    let (vs, ds', n₂) := emitParamsB ps n₁
    ((x, v) :: vs, ds ++ ds', n₂)

/-! ## The fragment -/

/-- An export `name: func(params) -> bool`: the `canon lift` of core export `core` with the
memory and the allocator. -/
structure ListExport where
  /-- The component export name. -/
  name : String
  /-- The named parameters. -/
  params : List (String × LTy)
  /-- The name of the lifted core function export. -/
  core : String
  deriving Repr

/-- A component of one core instance of an import-free module that exports its memory
`memName` and allocator `reallocName`, with list-taking exports returning `bool`. -/
structure ListComp where
  /-- The core module. -/
  mod : Silmaril.Wasm.Module
  /-- The name of the memory export. -/
  memName : String
  /-- The module's memory index of the memory export `memName` (`ListComp.Inst.memExport`).
  The module has no imports, so it is also the memory's address in the instance store, which the
  lowering writes. The component itself aliases this memory as its core memory `0`. -/
  memIdx : Nat := 0
  /-- The name of the allocator export (`cabi_realloc(old, old_size, align, new_size)`). -/
  reallocName : String
  /-- The exports. -/
  exports : List ListExport

namespace ListComp

/-- The type definitions of the exports from type index `n`: for each export, its list types and
then its function type. -/
def typeDefs {M : Type} : List ListExport → Nat → List (Syntax.Definition M)
  | [], _ => []
  | x :: xs, n =>
    let (ps, ds, n') := emitParams (M := M) x.params n
    ds ++ [.type (.func { params := ps, result := some (.prim .bool) })] ++ typeDefs xs (n' + 1)

/-- The function type indices of the exports from type index `n`. -/
def funcTypeIdx : List ListExport → Nat → List Nat
  | [], _ => []
  | x :: xs, n =>
    let (_, _, n') := emitParams (M := Silmaril.Wasm.Module) x.params n
    n' :: funcTypeIdx xs (n' + 1)

/-- **The reference component.** Core memory `0` is the memory, core function `0` the
allocator and core function `i + 1` the core function of export `i`; component function `i` is
the lift of export `i`, exported under its name. -/
def toRef (c : ListComp) : Core3Component :=
  [.coreModule c.mod, .coreInstance (.instantiate 0 []),
    .alias (.coreExport 0 c.memName .memory), .alias (.coreExport 0 c.reallocName .func)] ++
  c.exports.map (fun x => .alias (.coreExport 0 x.core .func)) ++
  typeDefs c.exports 0 ++
  ((c.exports.zipIdx.zip (funcTypeIdx c.exports 0)).map fun ((_, i), t) =>
    .canon (.lift (i + 1) [.memory 0, .realloc 0] t)) ++
  c.exports.zipIdx.map (fun (x, i) => .export_ { name := x.name } ⟨.func, i⟩ none)

/-- The binary type items of the exports from type index `n`. -/
def typeDefsB : List ListExport → Nat → List TyItem
  | [], _ => []
  | x :: xs, n =>
    let (ps, ds, n') := emitParamsB x.params n
    ds ++ [.def_ (.func ⟨ps, some (.prim .bool), false⟩)] ++ typeDefsB xs (n' + 1)

/-- **The binary component** around the core module bytes `core`, with the definitions of
`toRef` in the same order (the type definitions in `types` sections, the record type exports in
`exports` sections between them: `tySections`). -/
def toAst (c : ListComp) (core : ByteArray) : Binary.Ast := .mk ([
  .coreModule core,
  .coreInstances [.instantiate 0 []],
  .aliases ([⟨.core .memory, .coreExport 0 c.memName⟩, ⟨.core .func, .coreExport 0 c.reallocName⟩]
    ++ c.exports.map fun x => ⟨.core .func, .coreExport 0 x.core⟩)] ++
  tySections (typeDefsB c.exports 0) ++ [
  .canons ((c.exports.zipIdx.zip (funcTypeIdx c.exports 0)).map fun ((_, i), t) =>
    .lift (i + 1) [.memory 0, .realloc 0] t),
  .exports (c.exports.zipIdx.map fun (x, i) => ⟨↑x.name, ⟨.func, i⟩, none⟩)])

end ListComp

/-! ## The lowering, at the Core level -/

open Silmaril.Wasm.Execution.Core (Store Steps invoke Frame vals)

/-- The 4 little-endian bytes of a word (`Memory.encodeLE 4`, as the canonical ABI's
`store_int` writes them). -/
def le32 (x : BitVec 32) : ByteArray := Silmaril.Wasm.Execution.Memory.encodeLE 4 x.toNat

/-- The 8 little-endian bytes of a 64-bit word. -/
def le64 (x : BitVec 64) : ByteArray := Silmaril.Wasm.Execution.Memory.encodeLE 8 x.toNat

/-- The byte length of memory `ma` (`0` if there is none). -/
def memLen (s : Store Nat) (ma : Nat) : Nat := ((s.mems[ma]?).map (·.bytes.size)).getD 0

/-- A returning Core run of the allocator at address `ra` on `(0, 0, align, size)` from `s`,
answering `p` in the store `s'`. -/
def ReallocRun (P : Profile) (ra : Nat) (s : Store Nat) (align size p : Nat) (s' : Store Nat) :
    Prop :=
  ∃ f', Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
    (invoke s ra [.i32 0, .i32 0, .i32 (BitVec.ofNat 32 align), .i32 (BitVec.ofNat 32 size)])
    ⟨s', f', vals [.i32 (BitVec.ofNat 32 p)]⟩ ∧ p < 2 ^ 32

mutual
/-- `store(v, t, p)`: storing the value `v` of type `t` at byte `p` of memory `ma` takes the store
`s` to `s'` (lists through the allocator at `ra`). -/
inductive LStore (P : Profile) (ra ma : Nat) : LTy → LVal → Nat → Store Nat → Store Nat → Prop
  | s32 {x p s s'} :
      Silmaril.Wasm.SingleThreaded.memWrite? s ma p (le32 x) = some s' →
      LStore P ra ma .s32 (.s32 x) p s s'
  | u32 {x p s s'} :
      Silmaril.Wasm.SingleThreaded.memWrite? s ma p (le32 x) = some s' →
      LStore P ra ma .u32 (.u32 x) p s s'
  | s64 {x p s s'} :
      Silmaril.Wasm.SingleThreaded.memWrite? s ma p (le64 x) = some s' →
      LStore P ra ma .s64 (.s64 x) p s s'
  | tuple {t ts vs p s s'} :
      LFields P ra ma (t :: ts) vs p s s' → LStore P ra ma (.tuple t ts) (.fields vs) p s s'
  | record {name l t fs vs p s s'} :
      LFields P ra ma (t :: fs.map (·.2)) vs p s s' →
      LStore P ra ma (.record name l t fs) (.fields vs) p s s'
  | list {t vs p s s₁ s₂ s'} {q : Nat} :
      LList P ra ma t vs s q s₁ →
      Silmaril.Wasm.SingleThreaded.memWrite? s₁ ma p (le32 (BitVec.ofNat 32 q)) = some s₂ →
      Silmaril.Wasm.SingleThreaded.memWrite? s₂ ma (p + 4)
        (le32 (BitVec.ofNat 32 vs.length)) = some s' →
      LStore P ra ma (.list t) (.list vs) p s s'

/-- `store_list_into_range(vs, t)`: the allocator answers `q` for the list's bytes at the
alignment of `t`, `q` is aligned and the bytes lie in memory, and the elements are stored from
`q` on. -/
inductive LList (P : Profile) (ra ma : Nat) : LTy → List LVal → Store Nat → Nat → Store Nat →
    Prop
  | mk {t vs s q s₁ s'} :
      ReallocRun P ra s t.align.bytes (vs.length * t.size) q s₁ →
      q % t.align.bytes = 0 → q + vs.length * t.size ≤ memLen s₁ ma →
      LElems P ra ma t vs q s₁ s' →
      LList P ra ma t vs s q s'

/-- The elements `vs`, stored at `p`, `p + size`, …. -/
inductive LElems (P : Profile) (ra ma : Nat) : LTy → List LVal → Nat → Store Nat → Store Nat →
    Prop
  | nil {t p s} : LElems P ra ma t [] p s s
  | cons {t v vs p s s₁ s'} :
      LStore P ra ma t v p s s₁ → LElems P ra ma t vs (p + t.size) s₁ s' →
      LElems P ra ma t (v :: vs) p s s'

/-- `store_record`: the fields `vs` of types `ts` from the cursor `p` on, each stored at the
cursor rounded up to its type's alignment, the cursor then moving past it. -/
inductive LFields (P : Profile) (ra ma : Nat) : List LTy → List LVal → Nat → Store Nat →
    Store Nat → Prop
  | nil {p s} : LFields P ra ma [] [] p s s
  | cons {t ts v vs p s s₁ s'} :
      LStore P ra ma t v (Silmaril.Wasm.Component.ABI.alignTo p t.align) s s₁ →
      LFields P ra ma ts vs (Silmaril.Wasm.Component.ABI.alignTo p t.align + t.size) s₁ s' →
      LFields P ra ma (t :: ts) (v :: vs) p s s'
end

/-- The flat lowering of the parameters: an `s32` to its `i32`, each list to its `(ptr, len)`,
left to right (the parameter types of the fragment's exports, `ListComp.Good.top`). -/
inductive LParams (P : Profile) (ra ma : Nat) :
    List LTy → List LVal → Store Nat → List Silmaril.Wasm.Execution.Core.Val → Store Nat → Prop
  | nil {s} : LParams P ra ma [] [] s [] s
  | s32 {ts vs x s fl s'} :
      LParams P ra ma ts vs s fl s' →
      LParams P ra ma (.s32 :: ts) (.s32 x :: vs) s (.i32 x :: fl) s'
  | list {t ts us vs s q s₁ fl s'} :
      LList P ra ma t us s q s₁ → LParams P ra ma ts vs s₁ fl s' →
      LParams P ra ma (.list t :: ts) (.list us :: vs) s
        (.i32 (BitVec.ofNat 32 q) :: .i32 (BitVec.ofNat 32 us.length) :: fl) s'

/-! ## The target statement -/

mutual
/-- The flat core types of a value of type `t` (`flatten`): one `i32` for an `s32` or a `u32`,
one `i64` for an `s64`, the `(ptr, len)` pair of `i32`s for a list (32-bit memory), the fields'
flat types for a tuple or record. -/
def LTy.flat : LTy → List Silmaril.Wasm.Game.ScalarType
  | .s32 => [.num (.int .i32)]
  | .list _ => [.num (.int .i32), .num (.int .i32)]
  | .u32 => [.num (.int .i32)]
  | .s64 => [.num (.int .i64)]
  | .tuple t ts => t.flat ++ LTy.flatList ts
  | .record _ _ t fs => t.flat ++ LTy.flatFields fs

/-- `LTy.flat` on lists. -/
def LTy.flatList : List LTy → List Silmaril.Wasm.Game.ScalarType
  | [] => []
  | t :: ts => t.flat ++ LTy.flatList ts

/-- `LTy.flat` on labelled fields. -/
def LTy.flatFields : List (String × LTy) → List Silmaril.Wasm.Game.ScalarType
  | [] => []
  | (_, t) :: fs => t.flat ++ LTy.flatFields fs
end

/-- The parameter types the fragment lowers: `s32` and lists (of any element type). -/
def LTy.topLevel : LTy → Bool
  | .s32 => true
  | .list _ => true
  | _ => false

/-- The flat core parameter types of an export: its parameters' `LTy.flat`, left to right. -/
def ListExport.flatParams (x : ListExport) : List Silmaril.Wasm.Game.ScalarType :=
  (x.params.map (·.2)).flatMap LTy.flat

/-- The core type `(i32, i32, i32, i32) -> i32` of `cabi_realloc` (32-bit memory). -/
def reallocFnType : Silmaril.Wasm.Game.FnType :=
  ⟨[.num (.int .i32), .num (.int .i32), .num (.int .i32), .num (.int .i32)], [.num (.int .i32)]⟩

namespace ListComp

/-- The function address of the core export named `n` in the instance (`0` if none). -/
def coreAddr (c : ListComp) (I : Silmaril.Wasm.Game.ScalarInstance) (n : String) : Nat :=
  ((Silmaril.Wasm.Component.Reference.funcExportNames c.mod).zip I.addrs |>.lookup n).getD 0

/-- The component is well formed: distinct export names, every export at most `16` flat
parameters (two per list), each an `s32` or a list (`LTy.topLevel`: `u32`, `s64`, tuples and
records occur inside lists). -/
structure Good (c : ListComp) : Prop where
  names : (c.exports.map (·.name)).Nodup
  flat : ∀ x ∈ c.exports, 2 * x.params.length ≤ 16
  top : ∀ x ∈ c.exports, ∀ p ∈ x.params, p.2.topLevel = true

/-- The module is instantiated as the statement assumes: it validates and instantiates without
imports and without a start function (`I`, as `NumModule.IsInst` reads it), `memName` is its
export of memory `memIdx` (address `memIdx` of the instance store), a 32-bit memory, and the core functions
the component runs are typed function exports of the instance:

* `reallocFunc`, `coreFuncs`: the allocator and the exports' core functions are among its
  function exports (`funcExportNames`, aliased by name);
* `realloc`: the function at the allocator's address (`coreAddr I reallocName`, the address the
  lifts' `realloc` option holds) is the instance's function export `k`, of type
  `(i32, i32, i32, i32) -> i32`;
* `core`: the function at the address of each export's core function is a function export of
  the instance of type `flatParams -> i32`.

The typing is needed: the reference machine does not check the types of flat results (REF
`types_match_values` is an assert, deviation D-f), so a core function `(param i32 i32)
(result i64)` returning `1`, lifted at `-> bool`, makes the call return `true` although no Core
run returns an `i32` (and an allocator returning an `i64` is lifted as a `u32`). Such modules
are outside the fragment. -/
structure Inst (c : ListComp) (I : Silmaril.Wasm.Game.ScalarInstance) : Prop where
  inst : ∃ mt, Silmaril.Wasm.Game.IsInstance c.mod mt I
  noImports : I.imports = []
  memExport : ∃ x ∈ c.mod.exports, x.name = c.memName ∧
    ∃ i : Silmaril.Wasm.MemIdx, x.index = .memory i ∧ i.toNat = c.memIdx
  memAddr : c.memIdx < I.store.mems.length
  /-- The allocator is a function export of the module. -/
  reallocFunc : c.reallocName ∈ Silmaril.Wasm.Component.Reference.funcExportNames c.mod
  /-- The lifted core functions are function exports of the module. -/
  coreFuncs : ∀ x ∈ c.exports, x.core ∈ Silmaril.Wasm.Component.Reference.funcExportNames c.mod
  /-- The memory is 32-bit. -/
  memI32 : Silmaril.Wasm.SingleThreaded.memAddrType? I.store c.memIdx = some .i32
  realloc : ∃ k, ∃ hk : k < I.exports.length,
    I.addrs.getD k 0 = c.coreAddr I c.reallocName ∧ I.exports[k] = reallocFnType
  core : ∀ x ∈ c.exports, ∃ k, ∃ hk : k < I.exports.length,
    I.addrs.getD k 0 = c.coreAddr I x.core ∧ I.exports[k] = ⟨x.flatParams, [.num (.int .i32)]⟩

end ListComp

/-- **Accepting calls have a Core-level explanation** (the target of this fragment's soundness
development): for every export `x` of `c` and values `vs` of its parameter types, a behaviour of
the reference machine that instantiates `c.toRef`, calls `x` on `vs` and returns `true` lowers
`vs` from the instance store (`LParams`, with the allocator at its address and the memory at
address `memIdx`) to a store `s` and flat arguments `fl`, from which the lifted core function returns
one nonzero `i32`. -/
def AcceptSound (c : ListComp) : Prop :=
  ∀ (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (I : Silmaril.Wasm.Game.ScalarInstance), c.Good → c.Inst I →
  ∀ x ∈ c.exports, ∀ vs : List LVal, LTy.checkParams (x.params.map (·.2)) vs = true →
    Outcome.returns (some [.bool true]) ∈
      exportBehaviours prof (refHost P) () c.toRef [] x.name (vs.map LVal.toRef) →
    ∃ (s : Store Nat) (fl : List Silmaril.Wasm.Execution.Core.Val) (s' : Store Nat) (f' : Frame)
      (r : BitVec 32),
      LParams P (c.coreAddr I c.reallocName) c.memIdx (x.params.map (·.2)) vs I.store fl s ∧
      Steps P Silmaril.Wasm.SingleThreaded.Det.noHost (invoke s (c.coreAddr I x.core) fl)
        ⟨s', f', vals [.i32 r]⟩ ∧ r ≠ 0

end Silmaril.Wasm.Component.Reference.ListLift
