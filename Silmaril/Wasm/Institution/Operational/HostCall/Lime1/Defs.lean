module

public import Silmaril.Wasm.Lime1.Execution.Callout
public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1

open Execution.Runtime (EvalCtx Frame FuncAddr FuncInst MemAddr MemInst ModuleInst Result Value)
open Wasm.Lime1.Execution
open CallContinuation.OuterCall (CallTarget)
open CallContinuation.OuterCall.Ranked

/-- The designated memory is allocated in the base store. Its live byte array
may change, while its extent, declared limit and all other allocations stay fixed. -/
structure Memory32 {H : Type} (base : Store H) where
  address : MemAddr
  initial : MemInst
  allocated : base.memories[address.value]? = some initial

namespace Memory32

def store {H : Type} {base : Store H} (memory : Memory32 base) (bytes : ByteArray) : Store H :=
  setMemory base memory.address { memory.initial with data := bytes }

def Live {H : Type} {base : Store H} (memory : Memory32 base) (bytes : ByteArray) : Prop :=
  bytes.size = memory.initial.data.size

end Memory32

/-- An allocated host target and its complete ordered numeric signature. -/
structure Site (H : Type) where
  address : FuncAddr
  type : Wasm.Lime1.FuncType
  code : H

def Site.Allocated {H : Type} (site : Site H) (base : Store H) : Prop :=
  base.funcs[site.address.value]? = some (.host site.type site.code)

def Site.Arguments {H : Type} (site : Site H) (args : List Value) : Prop :=
  args.map Value.type = site.type.params

def Site.TypedResult {H : Type} (site : Site H) : Result → Prop
  | .values vs => vs.map Value.type = site.type.results
  | .trap => True

/-- The embedding must reestablish the live store relation on every returned
outcome from this site with typed operands, including a returned trap. -/
def Site.Contract {H : Type} {base : Store H} (site : Site H) (memory : Memory32 base)
    (host : HostSemantics H) : Prop :=
  ∀ ⦃bytes args returned outcome⦄, memory.Live bytes → site.Arguments args →
    host site.code (memory.store bytes) args (.returned returned outcome) →
    ∃ next, memory.Live next ∧ returned = memory.store next ∧ site.TypedResult outcome

def Site.callout {H : Type} (site : Site H) (context : EvalCtx Wasm.Lime1.Instr) (args : List Value) :
    Execution.Runtime.Callout H Wasm.Lime1.Instr :=
  ⟨context, site.address, site.type, site.code, args⟩

def Site.pending {H : Type} (site : Site H) (s : Store H) (outer : Frame)
    (context : EvalCtx Wasm.Lime1.Instr) (args : List Value) : Config H :=
  ⟨s, outer, context.plug value (values args ++ [.invoke site.address])⟩

structure IndirectSite extends CallResolution.Indirect.Site where
  graph : Graph.Program
  memoryFunctions : List (Option Graph.Memory32.Function) := []

def IndirectSite.memoryLookup (site : IndirectSite) (address : FuncAddr) :
    Option Graph.Memory32.Function :=
  (site.memoryFunctions[address.value]?).join

structure MemoryTarget where
  address : FuncAddr
  fn : Graph.Memory32.Function

def MemoryTarget.code (callee : MemoryTarget) : Wasm.Lime1.Func := callee.fn.v1Func.toLime

def MemoryTarget.Allocated {H : Type} (callee : MemoryTarget) (base : Store H) : Prop :=
  base.funcs[callee.address.value]? =
    some (.wasm callee.fn.declaration.type callee.fn.declaration.module callee.code)

def MemoryTarget.supportedOp : Graph.Memory32.Op → Bool
  | .ranked (.numeric (.get _)) | .load _ | .store _ => true
  | _ => false

/-- Fixed-extent straight-line accesses and local reads. Reuse operand typing
with the complete ordered result list, independent of the V1 scalar guard. -/
structure MemoryTarget.Checked {H : Type} (callee : MemoryTarget) {base : Store H}
    (memory : Memory32 base) : Prop where
  slot : callee.fn.declaration.module.memories[0]? = some memory.address
  typeAt : callee.fn.declaration.module.types[callee.fn.declaration.typeIndex.toNat]? =
    some callee.fn.declaration.type
  supported : callee.fn.code.all MemoryTarget.supportedOp = true
  body : callee.fn.WellTyped callee.fn.initial callee.fn.code

structure WasmTarget where
  address : FuncAddr
  fn : Graph.Function

def WasmTarget.callTarget (callee : WasmTarget) : CallTarget :=
  ⟨⟨0⟩, callee.address, callee.fn.declaration⟩

inductive IndirectTarget (H : Type) where
  | host (site : Site H)
  | wasm (callee : WasmTarget)
  | memory (callee : MemoryTarget)

/-- The consulted table and expected type are fixed in the active module and
base store. All nonnull entries are allocated. Each matching Wasm entry
links to the direct graph or a registered memory-using function. -/
structure IndirectSite.Linked {H : Type} (site : IndirectSite) (base : Store H)
    (module : ModuleInst) : Prop where
  tableAt : frameTable base ⟨[], module⟩ = some site.table
  signatureAt : module.types[site.typeIndex.toNat]? = some site.signature
  graphChecked : site.graph.checkDirect = true
  graphAllocated : site.graph.LimeAllocated base
  entries : ∀ address, some address ∈ site.table.refs →
    ∃ fn : FuncInst Wasm.Lime1.Func H, base.funcs[address.value]? = some fn ∧
      (fn.type = site.signature → match fn with
        | .host .. => True
        | .wasm .. => (∃ checked, site.graph.lookup address = some checked) ∨
            ∃ checked, site.memoryLookup address = some checked ∧
              (⟨address, checked⟩ : MemoryTarget).Allocated base)

/-- Matching hosts supply the embedding contract. Registered memory targets
check their code and the designated memory of the actual allocated module. -/
structure IndirectSite.Contract {H : Type} {base : Store H} (site : IndirectSite) (memory : Memory32 base)
    (host : HostSemantics H) : Prop where
  hosts : ∀ address code, some address ∈ site.table.refs →
    (⟨address, site.signature, code⟩ : Site H).Allocated base →
    (⟨address, site.signature, code⟩ : Site H).Contract memory host
  memory : ∀ callee : MemoryTarget, site.memoryLookup callee.address = some callee.fn →
    callee.Checked memory

/-- A single native lookup supplies an allocated target or one of the three
trap witnesses. The selector is the unsigned i32 table index. -/
inductive IndirectSite.Lookup {H : Type} (site : IndirectSite) (base : Store H) (selector : BitVec 32) :
    Option (IndirectTarget H) → Prop where
  | bounds (entry : site.table.refs[selector.toNat]? = none) : site.Lookup base selector none
  | null (entry : site.table.refs[selector.toNat]? = some none) : site.Lookup base selector none
  | mismatch {address : FuncAddr} {fn : FuncInst Wasm.Lime1.Func H}
      (entry : site.table.refs[selector.toNat]? = some (some address))
      (allocated : base.funcs[address.value]? = some fn) (different : fn.type ≠ site.signature) :
      site.Lookup base selector none
  | host {address : FuncAddr} {code : H}
      (entry : site.table.refs[selector.toNat]? = some (some address))
      (allocated : (⟨address, site.signature, code⟩ : Site H).Allocated base) :
      site.Lookup base selector (some (.host ⟨address, site.signature, code⟩))
  | wasm {callee : WasmTarget}
      (entry : site.table.refs[selector.toNat]? = some (some callee.address))
      (found : site.graph.lookup callee.address = some callee.fn)
      (allocated : base.funcs[callee.address.value]? =
        some (.wasm callee.fn.declaration.type callee.fn.declaration.module callee.fn.limeFunc))
      (typed : callee.fn.declaration.type = site.signature) :
      site.Lookup base selector (some (.wasm callee))

  | memory {callee : MemoryTarget}
      (entry : site.table.refs[selector.toNat]? = some (some callee.address))
      (found : site.memoryLookup callee.address = some callee.fn)
      (allocated : callee.Allocated base)
      (typed : callee.fn.declaration.type = site.signature) :
      site.Lookup base selector (some (.memory callee))

def IndirectSite.lookupHead {H : Type} : Option (IndirectTarget H) → Admin
  | some (.host target) => .invoke target.address
  | some (.wasm target) => .invoke target.address
  | some (.memory target) => .invoke target.address
  | none => .trap

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1
