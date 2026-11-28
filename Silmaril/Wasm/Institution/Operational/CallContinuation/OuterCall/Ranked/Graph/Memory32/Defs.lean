module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Native.Defs
public import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Defs
public import Silmaril.Wasm.Institution.Operational.MemoryGrow.Defs
public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.V1.Defs

/-!
# Checked V1 source with one shared Memory32

This check reuses the ranked direct-target table and the existing checker for
numeric, local, call, exit and scalar structured instructions. Each full-width memory
instruction supplies its own unsigned 32-bit offset. All declared activations
resolve slot zero to the same allocated memory address.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32

open Execution.Runtime (Frame FuncAddr MemAddr MemInst ModuleInst TableAddr TableInst Value)
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

/-- The default checks rank descent. The recursive profile checks the same
direct links and uses finite native runs independently of rank. -/
inductive CallMode where
  | ranked
  | recursive

def CallMode.permits : CallMode → (caller callee : Nat) → Prop
  | .ranked, caller, callee => callee < caller
  | .recursive, _, _ => True

instance (calls : CallMode) (caller callee : Nat) : Decidable (calls.permits caller callee) := by
  cases calls <;> unfold CallMode.permits <;> infer_instance

/-- Full-width Memory32 operations and parameterless scalar structured instructions. -/
inductive Op where
  | ranked (op : Graph.Op)
  | callIndirect (index : TypeIdx) (signature : Wasm.V1.FuncType)
  | load (offset : Fin (2 ^ 32))
  | store (offset : Fin (2 ^ 32))
  | size
  | grow
  | block (result : Option NumType) (body : List Op)
  | loop (result : Option NumType) (body : List Op)
  | if_ (result : Option NumType) (thenBody elseBody : List Op)

mutual

def supportedCode : List Op → (labels : List (List NumType) := []) → (mode : MemoryMode := .fixed) →
    (indirect : TypeIdx → Wasm.V1.FuncType → Bool := fun _ _ => false) → Bool
  | [], _, _, _ => true
  | op :: rest, labels, mode, indirect =>
    op.supportedIn labels mode indirect && supportedCode rest labels mode indirect

def Op.supportedIn : Op → List (List NumType) → (mode : MemoryMode := .fixed) →
    (indirect : TypeIdx → Wasm.V1.FuncType → Bool := fun _ _ => false) → Bool
  | .load _, _, _, _ | .store _, _, _, _ => true
  | .size, _, mode, _ | .grow, _, mode, _ => mode.growthEnabled
  | .callIndirect index signature, _, _, indirect => indirect index signature
  | .ranked (.numeric _), _, _, _ | .ranked (.set _), _, _, _ | .ranked (.tee _), _, _, _
  | .ranked (.call _), _, _, _ | .ranked .return_, _, _, _ | .ranked .unreachable, _, _, _ => true
  | .ranked (.br depth result), labels, _, _ | .ranked (.brIf depth result), labels, _, _ =>
    decide (labels[depth.toNat]? = some result)
  | .ranked (.brTable depths fallback result), labels, _, _ =>
    (fallback :: depths).all fun depth => decide (labels[depth.toNat]? = some result)
  | .ranked _, _, _, _ => false
  | .block result body, labels, mode, indirect => supportedCode body (result.toList :: labels) mode indirect
  | .loop _ body, labels, mode, indirect => supportedCode body ([] :: labels) mode indirect
  | .if_ result left right, labels, mode, indirect =>
    supportedCode left (result.toList :: labels) mode indirect &&
    supportedCode right (result.toList :: labels) mode indirect

end

def Op.supported (op : Op) : Bool := op.supportedIn []

mutual

def codeTargets : List Op → List CallTarget
  | [] => []
  | op :: rest => op.targets ++ codeTargets rest

def Op.targets : Op → List CallTarget
  | .ranked op => op.targets
  | .load _ | .store _ | .size | .grow | .callIndirect .. => []
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
  | .callIndirect index _ => .callIndirect index
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

def Function.supports (fn : Function) (op : Op) (mode : MemoryMode := .fixed)
    (indirect : TypeIdx → Wasm.V1.FuncType → Bool := fun _ _ => false) : Bool :=
  op.supportedIn fn.entryLabels mode indirect

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
  | .callIndirect _ signature =>
    Graph.checkCondition stack fun operands =>
      decide (operands.take signature.params.length = signature.params.reverse) &&
      resume (signature.results.reverse ++ operands.drop signature.params.length)
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
def Function.checkV1 (fn : Function) (memory : MemAddr) (mode : MemoryMode := .fixed)
    (indirect : TypeIdx → Wasm.V1.FuncType → Bool := fun _ _ => false) : Bool :=
  decide (fn.declaration.results.length ≤ 1) &&
    fn.code.all (fun op => fn.supports op mode indirect) &&
    fn.checkCode (Prefix.stackTypes fn.initial) fn.code &&
    decide (fn.declaration.module.memories[0]? = some memory)

/-- The sole consulted Table32 allocation in the V1 graph. -/
structure FixedTable where
  address : TableAddr
  table : TableInst

structure Program where
  functions : List (Option Function)
  fixedTable : Option FixedTable := none

def Program.lookup (program : Program) (address : FuncAddr) : Option Function :=
  program.functions[address.value]?.join

def Program.table (program : Program) : Table :=
  ⟨program.functions.map (Option.map Function.entry)⟩

def Program.checkLinks (program : Program) : CallMode → Bool
  | .ranked => program.table.check
  | .recursive => program.functions.all fun
    | none => true
    | some fn => fn.targets.all fun target =>
      match program.lookup target.address with
      | none => false
      | some callee => decide (callee.declaration = target.declaration ∧
          fn.declaration.module.funcs[target.index.toNat]? = some target.address)

def Program.checkTable (program : Program) : Bool :=
  (program.fixedTable.map fun fixed =>
    fixed.table.refs.all (fun entry => (entry.map fun a => (program.lookup a).isSome).getD true)).getD true

/-- Only signature-matching entries can invoke a function and must satisfy
the current call policy. Mismatching entries retain their native trap. -/
def Program.checkIndirect (program : Program) (calls : CallMode) (rank : Nat) (module : ModuleInst)
    (index : TypeIdx) (signature : Wasm.V1.FuncType) : Bool :=
  (program.fixedTable.map fun fixed =>
    decide (module.tables[0]? = some fixed.address ∧ module.types[index.toNat]? = some signature ∧
      signature.results.length ≤ 1) &&
    fixed.table.refs.all fun entry => (entry.map fun a =>
      ((program.lookup a).map fun fn => decide (fn.declaration.type = signature →
        calls.permits rank fn.rank)).getD true).getD true).getD false

def Program.checkV1 (program : Program) (memory : MemAddr) (mode : MemoryMode := .fixed)
    (calls : CallMode := .ranked) : Bool :=
  (program.checkLinks calls && program.checkTable) &&
    program.functions.all (fun slot => (slot.map fun fn =>
      fn.checkV1 memory mode (program.checkIndirect calls fn.rank fn.declaration.module)).getD true)

/-- Resolution after fixing the table from the active module's slot zero. -/
def Program.resolveIndirect (program : Program) (fixed : FixedTable) (module : ModuleInst)
    (index : TypeIdx) (selector : BitVec 32) : Option CallResolution.Indirect.Outcome :=
  CallResolution.Indirect.resolveTable fixed.table module.types[index.toNat]?
    (fun a => (program.lookup a).map (·.declaration.type)) selector

/-- Native allocation is fixed outside the selected memory's bytes. -/
structure Layout {H : Type} (program : Program) (base : Wasm.V1.Execution.Store H)
    (address : MemAddr) (initial : MemInst) : Prop where
  memory : base.memories[address.value]? = some initial
  functions : ∀ a fn, program.lookup a = some fn →
    base.funcs[a.value]? = some (.wasm fn.declaration.type fn.declaration.module fn.v1Func)
  table : ∀ fixed, program.fixedTable = some fixed → base.tables[fixed.address.value]? = some fixed.table := by
    intro _ found
    cases found

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
