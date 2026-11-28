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

/-- The host and callee share one allocated byte array. Growth is opt-in and
requires a page-aligned initial allocation within its declared limits. -/
inductive MemoryExtent (initial : MemInst) where
  | fixed
  | growing (admitted : MemoryGrow.SizeAllows initial 0)

def MemoryExtent.growthEnabled {initial : MemInst} : MemoryExtent initial → Bool
  | .fixed => false
  | .growing _ => true

/-- The designated memory keeps its allocation, maximum and the other store
components when its live bytes are replaced. -/
structure Memory32 {H : Type} (base : Store H) where
  address : MemAddr
  initial : MemInst
  allocated : base.memories[address.value]? = some initial
  extent : MemoryExtent initial := .fixed

namespace Memory32

def current {H : Type} {base : Store H} (memory : Memory32 base) (bytes : ByteArray) : MemInst :=
  { memory.initial with data := bytes }

def store {H : Type} {base : Store H} (memory : Memory32 base) (bytes : ByteArray) : Store H :=
  setMemory base memory.address (memory.current bytes)

def Live {H : Type} {base : Store H} (memory : Memory32 base) (bytes : ByteArray) : Prop :=
  match memory.extent with
  | .fixed => bytes.size = memory.initial.data.size
  | .growing _ => Graph.Memory32.GrowthExtent memory.initial bytes

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
  /-- Keep rank descent by default. The opt-in recursive policy admits cyclic Wasm linkage. -/
  memoryCalls : Graph.Memory32.CallMode := .ranked

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

mutual

/-- Depth equal to the number of explicit arms reaches the function label. -/
def MemoryTarget.supportedOpAt (growthEnabled : Bool) (explicitDepth : Nat) : Graph.Memory32.Op → Bool
  | .ranked (.numeric (.get _)) | .ranked (.call _) | .load _ | .store _ | .size => true
  | .callIndirect .. => true
  | .if_ _ left right => supportedCodeAt growthEnabled (explicitDepth + 1) left && supportedCodeAt growthEnabled (explicitDepth + 1) right
  | .ranked (.brIf depth _) => decide (depth.toNat ≤ explicitDepth)
  | .grow => growthEnabled
  | _ => false

def MemoryTarget.supportedCodeAt (growthEnabled : Bool) (explicitDepth : Nat) : List Graph.Memory32.Op → Bool
  | [] => true
  | op :: rest => supportedOpAt growthEnabled explicitDepth op && supportedCodeAt growthEnabled explicitDepth rest

end

abbrev MemoryTarget.supportedOp (growthEnabled : Bool) := MemoryTarget.supportedOpAt growthEnabled 0
abbrev MemoryTarget.supportedCode (growthEnabled : Bool) := MemoryTarget.supportedCodeAt growthEnabled 0

mutual

/-- Include instructions in both branches when checking static links. -/
def MemoryTarget.sourceOps : List Graph.Memory32.Op → List Graph.Memory32.Op
  | [] => []
  | op :: rest => op :: descendants op ++ sourceOps rest

def MemoryTarget.descendants : Graph.Memory32.Op → List Graph.Memory32.Op
  | .if_ _ left right => sourceOps left ++ sourceOps right
  | _ => []

end

/-- Memory instructions, local reads, calls and conditionals under the selected
extent policy. Operand typing uses the complete ordered result list.
The per-instruction allocation links are checked by `IndirectSite.MemoryLinked`. -/
structure MemoryTarget.Checked {H : Type} (callee : MemoryTarget) {base : Store H}
    (memory : Memory32 base) : Prop where
  slot : callee.fn.declaration.module.memories[0]? = some memory.address
  typeAt : callee.fn.declaration.module.types[callee.fn.declaration.typeIndex.toNat]? =
    some callee.fn.declaration.type
  supported : callee.fn.code.all (MemoryTarget.supportedOp memory.extent.growthEnabled) = true
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

/-- A direct Wasm edge resolves in the caller's module and matches the full
declaration of an allocated registered function. -/
structure IndirectSite.MemoryDirect {H : Type} {base : Store H} (site : IndirectSite)
    (parent : MemoryTarget) (target : CallTarget) (child : MemoryTarget) : Prop where
  resolves : parent.fn.declaration.module.funcs[target.index.toNat]? = some target.address
  address : child.address = target.address
  declaration : child.fn.declaration = target.declaration
  registered : site.memoryLookup child.address = some child.fn
  allocated : child.Allocated base

/-- The declared numeric signature of a direct call and its allocated host code. -/
def Site.directTarget {H : Type} (target : CallTarget) (code : H) : Site H :=
  ⟨target.address, target.declaration.type, code⟩

/-- A direct host link checks the caller's function index and the exact
host allocation. Its payload uses the same embedding contract as an indirect host. -/
structure MemoryDirectHost {H : Type} {base : Store H} (memory : Memory32 base) (host : HostSemantics H)
    (parent : MemoryTarget) (target : CallTarget) (code : H) : Prop where
  resolves : parent.fn.declaration.module.funcs[target.index.toNat]? = some target.address
  allocated : (Site.directTarget target code).Allocated base
  contract : (Site.directTarget target code).Contract memory host

/-- Resolve a nested site's type in the active callee while using the same
fixed table and memory function registry as the enclosing dispatcher. -/
def IndirectSite.memorySite (site : IndirectSite) (index : TypeIdx)
    (signature : Wasm.V1.FuncType) : IndirectSite :=
  ⟨⟨site.table, index, ⟨signature.params, signature.results⟩⟩, ⟨[]⟩, site.memoryFunctions, site.memoryCalls⟩

/-- Every nonnull entry is allocated. Matching Wasm entries admit the selected
call policy, and matching hosts require their embedding contract. -/
structure IndirectSite.MemoryIndirect {H : Type} (site : IndirectSite) {base : Store H}
    (memory : Memory32 base) (host : HostSemantics H) (parent : MemoryTarget) (index : TypeIdx)
    (signature : Wasm.V1.FuncType) (calls : Graph.Memory32.CallMode := site.memoryCalls) : Prop where
  tableAt : frameTable base ⟨[], parent.fn.declaration.module⟩ = some site.table
  signatureAt : parent.fn.declaration.module.types[index.toNat]? = some ⟨signature.params, signature.results⟩
  entries : ∀ address, some address ∈ site.table.refs →
    ∃ fn : FuncInst Wasm.Lime1.Func H, base.funcs[address.value]? = some fn ∧
      (fn.type = ⟨signature.params, signature.results⟩ → match fn with
        | .host type code => (⟨address, type, code⟩ : Site H).Contract memory host
        | .wasm .. => ∃ child, site.memoryLookup address = some child ∧
            (⟨address, child⟩ : MemoryTarget).Allocated base ∧ calls.permits parent.fn.rank child.rank)

/-- Static checks of the address-indexed graph. Rank is a policy for admitting
Wasm links. The finite-step machine uses the underlying allocation witnesses. -/
structure IndirectSite.MemoryLinked {H : Type} {base : Store H} (site : IndirectSite)
    (memory : Memory32 base) (host : HostSemantics H) (calls : Graph.Memory32.CallMode := site.memoryCalls) : Prop where
  checked : ∀ callee : MemoryTarget, site.memoryLookup callee.address = some callee.fn → callee.Checked memory
  direct : ∀ (parent : MemoryTarget), site.memoryLookup parent.address = some parent.fn →
    ∀ target ∈ parent.fn.targets,
      (∃ child, site.MemoryDirect (base := base) parent target child ∧ calls.permits parent.fn.rank child.fn.rank) ∨
      ∃ code, MemoryDirectHost memory host parent target code
  indirect : ∀ (parent : MemoryTarget), site.memoryLookup parent.address = some parent.fn →
    ∀ index signature, .callIndirect index signature ∈ MemoryTarget.sourceOps parent.fn.code →
      site.MemoryIndirect memory host parent index signature calls

/-- Matching hosts supply the embedding contract. Registered memory targets
check their code and the designated memory of the actual allocated module. -/
structure IndirectSite.Contract {H : Type} {base : Store H} (site : IndirectSite) (memory : Memory32 base)
    (host : HostSemantics H) : Prop where
  hosts : ∀ address code, some address ∈ site.table.refs →
    (⟨address, site.signature, code⟩ : Site H).Allocated base →
    (⟨address, site.signature, code⟩ : Site H).Contract memory host
  memory : site.MemoryLinked memory host

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
