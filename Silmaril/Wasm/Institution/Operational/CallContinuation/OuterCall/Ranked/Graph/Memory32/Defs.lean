module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Native.Defs
public import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Defs
public import Silmaril.Wasm.Institution.Operational.MemoryGrow.Defs

/-!
# Ranked V1 source with one shared Memory32

This check reuses the ranked direct-target table and the existing checker for
numeric, local, call, exit and scalar structured instructions. Each full-width memory
instruction supplies its own unsigned 32-bit offset. All declared activations
resolve slot zero to the same allocated memory address.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32

open Execution.Runtime (Frame FuncAddr MemAddr MemInst Value)
open Computed

/-- The original fixed-extent profile or growth with the allocated page limit. -/
inductive MemoryMode where
  | fixed
  | growing (maximum : Option Nat)

def MemoryMode.growthEnabled : MemoryMode → Bool
  | .fixed => false
  | .growing _ => true

def MemoryMode.matches (mode : MemoryMode) (initial : MemInst) : Prop :=
  match mode with
  | .fixed => True
  | .growing maximum => initial.max = maximum

/-- Full-width Memory32 operations and parameterless scalar structured instructions. -/
inductive Op where
  | ranked (op : Graph.Op)
  | load (offset : Fin (2 ^ 32))
  | store (offset : Fin (2 ^ 32))
  | size
  | grow
  | block (result : Option NumType) (body : List Op)
  | loop (result : Option NumType) (body : List Op)
  | if_ (result : Option NumType) (thenBody elseBody : List Op)

mutual

def supportedCode : List Op → (labels : List (List NumType) := []) → (mode : MemoryMode := .fixed) → Bool
  | [], _, _ => true
  | op :: rest, labels, mode => op.supportedIn labels mode && supportedCode rest labels mode

def Op.supportedIn : Op → List (List NumType) → (mode : MemoryMode := .fixed) → Bool
  | .load _, _, _ | .store _, _, _ => true
  | .size, _, mode | .grow, _, mode => mode.growthEnabled
  | .ranked (.numeric _), _, _ | .ranked (.set _), _, _ | .ranked (.tee _), _, _
  | .ranked (.call _), _, _ | .ranked .return_, _, _ | .ranked .unreachable, _, _ => true
  | .ranked (.br depth result), labels, _ | .ranked (.brIf depth result), labels, _ =>
    decide (labels[depth.toNat]? = some result)
  | .ranked (.brTable depths fallback result), labels, _ =>
    (fallback :: depths).all fun depth => decide (labels[depth.toNat]? = some result)
  | .ranked _, _, _ => false
  | .block result body, labels, mode => supportedCode body (result.toList :: labels) mode
  | .loop _ body, labels, mode => supportedCode body ([] :: labels) mode
  | .if_ result left right, labels, mode =>
    supportedCode left (result.toList :: labels) mode && supportedCode right (result.toList :: labels) mode

end

def Op.supported (op : Op) : Bool := op.supportedIn []

mutual

def codeTargets : List Op → List CallTarget
  | [] => []
  | op :: rest => op.targets ++ codeTargets rest

def Op.targets : Op → List CallTarget
  | .ranked op => op.targets
  | .load _ | .store _ | .size | .grow => []
  | .block _ body | .loop _ body => codeTargets body
  | .if_ _ left right => codeTargets left ++ codeTargets right

end

/-- The full-width instruction's alignment hint stays at its natural alignment. -/
def immediate (offset : Fin (2 ^ 32)) : Wasm.V1.MemArg := ⟨2, offset⟩

mutual

def v1Code : List Op → Wasm.V1.Expr
  | [] => []
  | op :: rest => op.v1 :: v1Code rest

def Op.v1 : Op → Wasm.V1.Instr
  | .ranked op => op.emit Graph.v1CodeSyntax
  | .load offset => .intLoad .i32 none (immediate offset)
  | .store offset => .intStore .i32 none (immediate offset)
  | .size => .memorySize
  | .grow => .memoryGrow
  | .block result body => .block result (v1Code body)
  | .loop result body => .loop result (v1Code body)
  | .if_ result left right => .if_ result (v1Code left) (v1Code right)

end

structure Function where
  declaration : Declaration
  rank : Nat
  initial : List Value
  code : List Op

def Function.targets (fn : Function) : List CallTarget := fn.code.flatMap Op.targets

def Function.entry (fn : Function) : Entry := ⟨fn.declaration, fn.rank, fn.targets⟩

def Function.v1Func (fn : Function) : Wasm.V1.Func :=
  ⟨fn.declaration.typeIndex, fn.declaration.locals,
    fn.initial.map Graph.v1CodeSyntax.ops.value ++ fn.code.map Op.v1⟩

/-- Each activation starts with the empty-continuation label opened by native
invocation. Explicit block and conditional labels extend this context. -/
def Function.entryLabels (fn : Function) : List (List NumType) := [fn.declaration.results]

def Function.supports (fn : Function) (op : Op) (mode : MemoryMode := .fixed) : Bool :=
  op.supportedIn fn.entryLabels mode

mutual

/-- Parameterless regions start on an empty stack and check their declared fallthrough.
Labels are innermost first. The function's results govern explicit return. -/
def Function.checkRegion (fn : Function) (stack fallthrough : List NumType) :
    List Op → (labels : List (List NumType) := []) → Bool
  | [], _ => decide (stack = fallthrough.reverse)
  | op :: rest, labels =>
    fn.checkRegionOp stack labels (fun next => fn.checkRegion next fallthrough rest labels) op

/-- The stack is top-first. A load replaces its address with an i32 result.
A store consumes the i32 word above the i32 address. -/
def Function.checkRegionOp (fn : Function) (stack : List NumType) (labels : List (List NumType))
    (resume : List NumType → Bool) : Op → Bool
  | .ranked op =>
    Graph.checkOp fn.targets (fn.declaration.params ++ fn.declaration.locals) fn.declaration.results
      labels stack fn.declaration.module.types resume op
  | .load _ | .grow => Graph.checkCondition stack (fun saved => resume (.int .i32 :: saved))
  | .size => resume (.int .i32 :: stack)
  | .store _ => Graph.checkCondition stack (fun args => Graph.checkCondition args resume)
  | .block result body =>
    fn.checkRegion [] result.toList body (result.toList :: labels) && resume (result.toList.reverse ++ stack)
  | .loop result body =>
    fn.checkRegion [] result.toList body ([] :: labels) && resume (result.toList.reverse ++ stack)
  | .if_ result left right =>
    Graph.checkCondition stack fun saved =>
      fn.checkRegion [] result.toList left (result.toList :: labels) &&
        fn.checkRegion [] result.toList right (result.toList :: labels) &&
        resume (result.toList.reverse ++ saved)

end

def Function.checkCode (fn : Function) (stack : List NumType) (code : List Op) : Bool :=
  fn.checkRegion stack fn.declaration.results code fn.entryLabels

def Function.WellTyped (fn : Function) (stack : List Value) (code : List Op) : Prop :=
  fn.checkCode (Prefix.stackTypes stack) code = true

/-- Syntax and declared branch targets are checked throughout the body. Stack
checking follows the admitted continuations. -/
def Function.checkV1 (fn : Function) (memory : MemAddr) (mode : MemoryMode := .fixed) : Bool :=
  decide (fn.declaration.results.length ≤ 1) &&
    fn.code.all (fun op => fn.supports op mode) &&
    fn.checkCode (Prefix.stackTypes fn.initial) fn.code &&
    decide (fn.declaration.module.memories[0]? = some memory)

structure Program where
  functions : List (Option Function)

def Program.lookup (program : Program) (address : FuncAddr) : Option Function :=
  program.functions[address.value]?.join

def Program.table (program : Program) : Table :=
  ⟨program.functions.map (Option.map Function.entry)⟩

def Program.checkV1 (program : Program) (memory : MemAddr) (mode : MemoryMode := .fixed) : Bool :=
  program.table.check &&
    program.functions.all (fun slot => (slot.map (fun fn => fn.checkV1 memory mode)).getD true)

/-- Native allocation is fixed outside the selected memory's bytes. -/
structure Layout {H : Type} (program : Program) (base : Wasm.V1.Execution.Store H)
    (address : MemAddr) (initial : MemInst) : Prop where
  memory : base.memories[address.value]? = some initial
  functions : ∀ a fn, program.lookup a = some fn →
    base.funcs[a.value]? = some (.wasm fn.declaration.type fn.declaration.module fn.v1Func)

def storeWithBytes {H : Type} (base : Wasm.V1.Execution.Store H)
    (address : MemAddr) (initial : MemInst) (bytes : ByteArray) : Wasm.V1.Execution.Store H :=
  Wasm.V1.Execution.setMemory base address { initial with data := bytes }

/-- The entire current store differs at most in the designated byte array.
The memory's extent and metadata stay fixed. -/
def SharedStore {H : Type} (base : Wasm.V1.Execution.Store H) (address : MemAddr)
    (initial : MemInst) (live : Wasm.V1.Execution.Store H) : Prop :=
  ∃ bytes, bytes.size = initial.data.size ∧ live = storeWithBytes base address initial bytes

/-- The live bytes remain page-aligned, within the fixed limits, and at least
as large as the initial extent. -/
def BoundedExtent (minimum : Nat) (maximum : Option Nat) (bytes : ByteArray) : Prop :=
  minimum ≤ bytes.size ∧ MemoryGrow.SizeAllows ⟨bytes, maximum⟩ 0

abbrev GrowthExtent (initial : MemInst) (bytes : ByteArray) : Prop :=
  BoundedExtent initial.data.size initial.max bytes

def MemoryMode.extent (mode : MemoryMode) (minimum : Nat) (bytes : ByteArray) : Prop :=
  match mode with
  | .fixed => bytes.size = minimum
  | .growing maximum => BoundedExtent minimum maximum bytes

/-- The selected byte array can grow while the rest of the store and the
selected memory's limit remain fixed. -/
def GrowingStore {H : Type} (base : Wasm.V1.Execution.Store H) (address : MemAddr)
    (initial : MemInst) (live : Wasm.V1.Execution.Store H) : Prop :=
  ∃ bytes, GrowthExtent initial bytes ∧ live = storeWithBytes base address initial bytes

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32
