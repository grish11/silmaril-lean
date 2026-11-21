module

public import Silmaril.Wasm.Profiles.ISA.Defs

@[expose] public section

namespace Silmaril.Wasm.Profiles.FunctionalISA

open Validation

/-- `structSet` is absent from the immutable grammar; declaration mutability
and the absence of imports are separately checked on a complete module. -/
inductive Atom : GCMode → Type where
  | intConst {gc : GCMode} (bits : BitVec 32) : Atom gc
  | bin {gc : GCMode} (width : IntType) (op : ISA.Binop) : Atom gc
  | localGet {gc : GCMode} (idx : LocalIdx) : Atom gc
  | refI31 {gc : GCMode} : Atom gc
  | refFunc {gc : GCMode} (idx : FuncIdx) : Atom gc
  | callRef {gc : GCMode} (type : TypeIdx) : Atom gc
  | structNew {gc : GCMode} (type : TypeIdx) : Atom gc
  | structGet {gc : GCMode} (sign : Option Signedness) (type : TypeIdx) (field : FieldIdx) : Atom gc
  | structSet (type : TypeIdx) (field : FieldIdx) : Atom .mutable
  | brIf0 {gc : GCMode} : Atom gc

def Atom.erase {gc : GCMode} : Atom gc → Instr
  | .intConst bits => .intConst .i32 bits
  | .bin width op => .intBinOp width op.toCore
  | .localGet idx => .localGet idx
  | .refI31 => .refI31
  | .refFunc idx => .refFunc idx
  | .callRef type => .callRef type
  | .structNew type => .structNew type
  | .structGet sign type field => .structGet sign type field
  | .structSet type field => .structSet type field
  | .brIf0 => .brIf ⟨0⟩

inductive Raw (gc : GCMode) where
  | done
  | cons (head : Atom gc) (tail : Raw gc)
  | blockI32 (body tail : Raw gc)

def Raw.erase {gc : GCMode} : Raw gc → Expr
  | .done => []
  | .cons head tail => head.erase :: tail.erase
  | .blockI32 body tail => .block (.value .i32) body.erase :: tail.erase

def Atom.allowWrites : Atom .immutable → Atom .mutable
  | .intConst bits => .intConst bits
  | .bin width op => .bin width op
  | .localGet idx => .localGet idx
  | .refI31 => .refI31
  | .refFunc idx => .refFunc idx
  | .callRef type => .callRef type
  | .structNew type => .structNew type
  | .structGet sign type field => .structGet sign type field
  | .brIf0 => .brIf0

def Raw.allowWrites : Raw .immutable → Raw .mutable
  | .done => .done
  | .cons head tail => .cons head.allowWrites tail.allowWrites
  | .blockI32 body tail => .blockI32 body.allowWrites tail.allowWrites

/-- Atomic witnesses record only the premises of the affected Core typing
rule. They do not store an opaque `InstrOk` derivation. -/
inductive TypedAtom (ctx : Context) : GCMode → List CValType → List CValType → Type where
  | intConst {gc : GCMode} (bits : BitVec 32) : TypedAtom ctx gc [] [.i32]
  | bin {gc : GCMode} (width : IntType) (op : ISA.Binop) :
      TypedAtom ctx gc [.num (.int width), .num (.int width)] [.num (.int width)]
  | localGet {gc : GCMode} {type : CValType} (idx : LocalIdx) (lookup : ctx.locals[idx.toNat]? = some ⟨.set, type⟩) :
      TypedAtom ctx gc [] [type]
  | refI31 {gc : GCMode} : TypedAtom ctx gc [.i32] [.refT false (.abs .i31)]
  | refFunc {gc : GCMode} {defType : DefType} (idx : FuncIdx)
      (lookup : ctx.funcs[idx.toNat]? = some defType) (declared : idx.toNat ∈ ctx.refs) :
      TypedAtom ctx gc [] [.refT false (.defHeap defType)]
  | callRef {gc : GCMode} {defType : DefType} {params results : Ty (.list .val)} (type : TypeIdx)
      (lookup : ctx.type? type = some defType) (signature : Expand defType (.func params results)) :
      TypedAtom ctx gc (params.toList ++ [.refT true (.defHeap defType)]) results.toList
  | structNew {gc : GCMode} {defType : DefType} {fs : Ty (.list .field)}
      (type : TypeIdx) (lookup : ctx.type? type = some defType) (fields : Expand defType (.struct fs)) :
      TypedAtom ctx gc (fs.toList.map fieldUnpack) [.refT false (.defHeap defType)]
  | structGet {gc : GCMode} {defType : DefType} {fs : Ty (.list .field)} {mutability : Mutability} {storage : CStorageType}
      (sign : Option Signedness) (type : TypeIdx) (field : FieldIdx)
      (lookup : ctx.type? type = some defType) (fields : Expand defType (.struct fs))
      (entry : fs.toList[field.toNat]? = some (.field mutability storage)) (packed : sign.isSome = storage.isPacked) :
      TypedAtom ctx gc [.refT true (.defHeap defType)] [storage.unpack]
  | structSet {defType : DefType} {fs : Ty (.list .field)} {storage : CStorageType} (type : TypeIdx) (field : FieldIdx)
      (lookup : ctx.type? type = some defType) (fields : Expand defType (.struct fs))
      (entry : fs.toList[field.toNat]? = some (.field .var storage)) :
      TypedAtom ctx .mutable [.refT true (.defHeap defType), storage.unpack] []
  | brIf0 {gc : GCMode} (target : ctx.labels[0]? = some [.i32]) : TypedAtom ctx gc [.i32, .i32] [.i32]

def TypedAtom.toRaw {ctx : Context} {gc : GCMode} {inputs outputs : List CValType} :
    TypedAtom ctx gc inputs outputs → Atom gc
  | .intConst bits => .intConst bits
  | .bin width op => .bin width op
  | .localGet idx _ => .localGet idx
  | .refI31 => .refI31
  | .refFunc idx .. => .refFunc idx
  | .callRef type .. => .callRef type
  | .structNew type .. => .structNew type
  | .structGet sign type field .. => .structGet sign type field
  | .structSet type field .. => .structSet type field
  | .brIf0 _ => .brIf0

/-- Code with exact stack boundaries. The only label introduced
here exits an `i32` result block; `brIf0` targets the innermost such label.
`sub` is proof-only (e.g. to pass a freshly allocated ref to `struct.get`). -/
inductive Code (gc : GCMode) : Context → List CValType → List CValType → Type where
  | done {ctx : Context} {stack : List CValType} (ok : ResultOk ctx.toTypeCtx stack) : Code gc ctx stack stack
  | cons {ctx : Context} {base inputs outputs results : List CValType}
      (frame : ResultOk ctx.toTypeCtx base) (head : TypedAtom ctx gc inputs outputs)
      (tail : Code gc ctx (base ++ outputs) results) : Code gc ctx (base ++ inputs) results
  | blockI32 {ctx : Context} {base results : List CValType} (frame : ResultOk ctx.toTypeCtx base)
      (body : Code gc (ctx.withLabel [.i32]) [] [.i32])
      (tail : Code gc ctx (base ++ [.i32]) results) : Code gc ctx base results
  | sub {ctx : Context} {inputs outputs inputs' outputs' : List CValType} (code : Code gc ctx inputs outputs)
      (sub : InstrTypeSub ctx (.plain inputs outputs) (.plain inputs' outputs'))
      (valid : InstrTypeOk ctx (.plain inputs' outputs')) : Code gc ctx inputs' outputs'

def Code.toRaw {gc : GCMode} {ctx : Context} {inputs outputs : List CValType} : Code gc ctx inputs outputs → Raw gc
  | .done _ => .done
  | .cons _ head tail => .cons head.toRaw tail.toRaw
  | .blockI32 _ body tail => .blockI32 body.toRaw tail.toRaw
  | .sub code _ _ => code.toRaw

def Code.erase {gc : GCMode} {ctx : Context} {inputs outputs : List CValType}
    (code : Code gc ctx inputs outputs) : Expr := code.toRaw.erase

end Silmaril.Wasm.Profiles.FunctionalISA
