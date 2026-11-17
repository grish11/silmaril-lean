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

* `LTy`: parameter types `s32` and `list<t>` (so `list<s32>`, `list<list<s32>>`, …), `LVal`
  their values, `LTy.check`, the reference values `LVal.toRef` and the resolved reference types
  `LTy.toClosed`;
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
* `LList`: `store_list_into_range`: the allocator returns an aligned `q` with the list's
  `len · size` bytes in the memory (address `ma`), then the elements are stored (`LElems`) at
  `q`, `q + size`, …;
* `LStore`: `store` of one value: an `s32` as its 4 little-endian bytes (`le32`), a list as
  `store_list_into_range` followed by the `(ptr, len)` pair;
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

/-- Parameter types: `s32` and lists. -/
inductive LTy where
  | s32
  | list (t : LTy)
  deriving DecidableEq, Repr, Inhabited

/-- Values of the parameter types. -/
inductive LVal where
  | s32 (x : BitVec 32)
  | list (vs : List LVal)
  deriving Repr, Inhabited

mutual
/-- `v` has type `t`. -/
def LTy.check : LTy → LVal → Bool
  | .s32, .s32 _ => true
  | .list t, .list vs => LTy.checkList t vs
  | _, _ => false

/-- Every value of `vs` has type `t`. -/
def LTy.checkList (t : LTy) : List LVal → Bool
  | [] => true
  | v :: vs => t.check v && LTy.checkList t vs
end

/-- `vs` have the types `ts`, in order. -/
def LTy.checkParams : List LTy → List LVal → Bool
  | [], [] => true
  | t :: ts, v :: vs => t.check v && LTy.checkParams ts vs
  | _, _ => false

mutual
/-- The reference value of a value (an `s32` by its two's-complement reading). -/
def LVal.toRef : LVal → Silmaril.Wasm.Component.Value.Val
  | .s32 x => .int .s32 x.toInt
  | .list vs => .list (LVal.toRefList vs)

/-- `LVal.toRef` on lists. -/
def LVal.toRefList : List LVal → List Silmaril.Wasm.Component.Value.Val
  | [] => []
  | v :: vs => v.toRef :: LVal.toRefList vs
end

open Silmaril.Wasm.Component.Runtime (RtId) in
/-- The resolved reference type of a parameter type. -/
def LTy.toClosed : LTy → Silmaril.Wasm.Component.WIT.ClosedType RtId
  | .s32 => .prim .s32
  | .list t => .list t.toClosed

/-- The canonical-ABI size (and alignment) in bytes of a value of type `t` in memory: `4` for
`s32`, `8` for a `(ptr, len)` list pair (alignment `4` in both cases). -/
def LTy.size : LTy → Nat
  | .s32 => 4
  | .list _ => 8

/-! ## Reference and binary syntax of the types -/

/-- The reference value type of `t`, with the type definitions it needs from type index `n`
(each list type is one `(type (list …))` definition); returns the next free type index. -/
def LTy.emit {M : Type} : LTy → Nat → Syntax.VT × List (Syntax.Definition M) × Nat
  | .s32, n => (.prim .s32, [], n)
  | .list t, n =>
    let (v, ds, n') := t.emit n
    (.idx n', ds ++ [.type (.val (.list v))], n' + 1)

/-- The binary value type of `t`, with its type definitions from index `n`. -/
def LTy.emitB : LTy → Nat → Binary.ValType × List Binary.DefType × Nat
  | .s32, n => (.prim .s32, [], n)
  | .list t, n =>
    let (v, ds, n') := t.emitB n
    (.idx n', ds ++ [.val (.list v)], n' + 1)

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
    List (String × Binary.ValType) × List Binary.DefType × Nat
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
  deriving Repr, DecidableEq

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

/-- The binary type definitions of the exports from type index `n`. -/
def typeDefsB : List ListExport → Nat → List Binary.DefType
  | [], _ => []
  | x :: xs, n =>
    let (ps, ds, n') := emitParamsB x.params n
    ds ++ [.func ⟨ps, some (.prim .bool), false⟩] ++ typeDefsB xs (n' + 1)

/-- **The binary component** around the core module bytes `core`, with the definitions of
`toRef` in the same order. -/
def toAst (c : ListComp) (core : ByteArray) : Binary.Ast := .mk [
  .coreModule core,
  .coreInstances [.instantiate 0 []],
  .aliases ([⟨.core .memory, .coreExport 0 c.memName⟩, ⟨.core .func, .coreExport 0 c.reallocName⟩]
    ++ c.exports.map fun x => ⟨.core .func, .coreExport 0 x.core⟩),
  .types (typeDefsB c.exports 0),
  .canons ((c.exports.zipIdx.zip (funcTypeIdx c.exports 0)).map fun ((_, i), t) =>
    .lift (i + 1) [.memory 0, .realloc 0] t),
  .exports (c.exports.zipIdx.map fun (x, i) => ⟨↑x.name, ⟨.func, i⟩, none⟩)]

end ListComp

/-! ## The lowering, at the Core level -/

open Silmaril.Wasm.Execution.Core (Store Steps invoke Frame vals)

/-- The 4 little-endian bytes of a word (`Memory.encodeLE 4`, as the canonical ABI's
`store_int` writes them). -/
def le32 (x : BitVec 32) : ByteArray := Silmaril.Wasm.Execution.Memory.encodeLE 4 x.toNat

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
  | list {t vs p s s₁ s₂ s'} {q : Nat} :
      LList P ra ma t vs s q s₁ →
      Silmaril.Wasm.SingleThreaded.memWrite? s₁ ma p (le32 (BitVec.ofNat 32 q)) = some s₂ →
      Silmaril.Wasm.SingleThreaded.memWrite? s₂ ma (p + 4)
        (le32 (BitVec.ofNat 32 vs.length)) = some s' →
      LStore P ra ma (.list t) (.list vs) p s s'

/-- `store_list_into_range(vs, t)`: the allocator answers `q` for the list's bytes, `q` is
aligned (to `4`) and the bytes lie in memory, and the elements are stored from `q` on. -/
inductive LList (P : Profile) (ra ma : Nat) : LTy → List LVal → Store Nat → Nat → Store Nat →
    Prop
  | mk {t vs s q s₁ s'} :
      ReallocRun P ra s 4 (vs.length * t.size) q s₁ →
      q % 4 = 0 → q + vs.length * t.size ≤ memLen s₁ ma →
      LElems P ra ma t vs q s₁ s' →
      LList P ra ma t vs s q s'

/-- The elements `vs`, stored at `p`, `p + size`, …. -/
inductive LElems (P : Profile) (ra ma : Nat) : LTy → List LVal → Nat → Store Nat → Store Nat →
    Prop
  | nil {t p s} : LElems P ra ma t [] p s s
  | cons {t v vs p s s₁ s'} :
      LStore P ra ma t v p s s₁ → LElems P ra ma t vs (p + t.size) s₁ s' →
      LElems P ra ma t (v :: vs) p s s'
end

/-- The flat lowering of the parameters: each list to its `(ptr, len)`, left to right. Only list
parameters are in the fragment's exports (an `s32` parameter would be one flat `i32`). -/
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

/-- The flat core types of a parameter of type `t`: one `i32` for an `s32`, the `(ptr, len)`
pair of `i32`s for a list (32-bit memory). -/
def LTy.flat : LTy → List Silmaril.Wasm.Game.ScalarType
  | .s32 => [.num (.int .i32)]
  | .list _ => [.num (.int .i32), .num (.int .i32)]

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
parameters (two per list) and no other result than `bool`. -/
structure Good (c : ListComp) : Prop where
  names : (c.exports.map (·.name)).Nodup
  flat : ∀ x ∈ c.exports, 2 * x.params.length ≤ 16

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
