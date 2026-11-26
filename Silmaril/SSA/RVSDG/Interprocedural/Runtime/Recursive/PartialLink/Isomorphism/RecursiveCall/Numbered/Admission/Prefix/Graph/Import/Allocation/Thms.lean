module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Admission.Prefix.Graph.Import.Allocation.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Admission.Prefix.Graph.Import.Allocation.Link

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Prefix

open Continuation.Partial.Executable (Actions)
open NestedTheta.Equality (OpcodeCode)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {importsL importsR exports extra : Ports (Ty V S)}
variable {sigsL sigsR : List (Ports (Ty V S))}
variable {providerFn clientFn : Function V S} {value : ValueSort V S}

/-- Compose successful link traces at their common boundary store. -/
theorem AllocationHistory.append {actions : Actions m σ} {unitsA unitsB : List Nat}
    {start middle final : σ} (first : AllocationHistory actions unitsA start middle)
    (second : AllocationHistory actions unitsB middle final) :
    AllocationHistory actions (unitsB ++ unitsA) start final := by
  induction second with
  | empty => exact first
  | link _ ran ih => exact .link (ih first) ran

/-- Reassemble the trace with the selected provider's own history at the
recorded boundaries. -/
theorem AllocationHistory.Segment.reassemble {actions : Actions m σ} {whole units : List Nat}
    {initial final entered exited : σ}
    (segment : AllocationHistory.Segment actions whole units initial final entered exited)
    (provider : AllocationHistory actions units entered exited) : AllocationHistory actions whole initial final := by
  obtain ⟨_, _, rfl, before, after⟩ := segment
  simpa only [List.append_assoc] using (before.append provider).append after

private theorem AllocationHistory.Segment.extend {actions : Actions m σ} {whole units more : List Nat}
    {initial final entered exited next : σ}
    (segment : AllocationHistory.Segment actions whole units initial final entered exited)
    (tail : AllocationHistory actions more final next) :
    AllocationHistory.Segment actions (more ++ whole) units initial next entered exited := by
  obtain ⟨before, after, split, beforeTrace, afterTrace⟩ := segment
  exact ⟨before, more ++ after, by simp only [split, List.append_assoc], beforeTrace, afterTrace.append tail⟩

/-- A reusable checked link result and the unit namespaces reserved by
the links that produced it, most recent first. Reservations cover those
links' allocations. Globals from opaque imports are outside this history. -/
structure CheckedAllocationChain (actions : Actions m σ) (ids : GlobalRel)
    (keys : OpcodeCode (Instruction Op)) (captureCode : CaptureCode m)
    (unitsL unitsR : List Nat) (port : Port exports providerFn.port)
    (outcomeL outcomeR : Outcome m σ exports) where
  private mk ::
  checked : CheckedExport actions.toPrimitives ids keys captureCode port outcomeL outcomeR
  initialL : σ
  initialR : σ
  historyL : AllocationHistory actions unitsL initialL checked.storeL
  historyR : AllocationHistory actions unitsR initialR checked.storeR
  nodupL : unitsL.Nodup
  nodupR : unitsR.Nodup

/-- Reserve the units of the actual provider links. -/
def CheckedProvider.allocationChain {actions : Actions m σ} {ids : GlobalRel}
    {keys : OpcodeCode (Instruction Op)} {captureCode : CaptureCode m}
    {unitL unitR : Nat} {left : Omega Op importsL exports sigsL} {right : Omega Op importsR exports sigsR}
    {inputsL : Tuple m.Val importsL} {inputsR : Tuple m.Val importsR}
    {port : Port exports providerFn.port} {storeL storeR : σ}
    (provider : CheckedProvider actions ids keys captureCode unitL unitR left right inputsL inputsR port storeL storeR) :
    CheckedAllocationChain actions ids keys captureCode [unitL] [unitR] port
      (Executable.link actions unitL left inputsL storeL) (Executable.link actions unitR right inputsR storeR) :=
  CheckedAllocationChain.mk provider.checked storeL storeR
    (.link (.empty storeL) provider.checked.linkedL) (.link (.empty storeR) provider.checked.linkedR)
    (List.nodup_singleton _) (List.nodup_singleton _)

/-- The newest allocation unit is fresh against every earlier unit on its side. -/
theorem CheckedAllocationChain.fresh {actions : Actions m σ} {ids : GlobalRel}
    {keys : OpcodeCode (Instruction Op)} {captureCode : CaptureCode m}
    {unitsL unitsR : List Nat} {unitL unitR : Nat} {port : Port exports providerFn.port}
    {outcomeL outcomeR : Outcome m σ exports}
    (chain : CheckedAllocationChain actions ids keys captureCode (unitL :: unitsL) (unitR :: unitsR) port outcomeL outcomeR) :
    unitL ∉ unitsL ∧ unitR ∉ unitsR :=
  ⟨(List.nodup_cons.mp chain.nodupL).1, (List.nodup_cons.mp chain.nodupR).1⟩

private def extendWithImports [DecidableEq (Ty V S)] {keys : OpcodeCode (Instruction Op)}
    [DecidableEq keys.Key] {captureCode : CaptureCode m} (actions : Actions m σ) {ids : GlobalRel}
    (ordinary : OrdinaryOutputs Op)
    {familyL familyR : Family m} {dispatch : DispatchKeys V S keys.Key captureCode.Key}
    (prior : LinkedFamily actions.toPrimitives ids keys captureCode familyL familyR dispatch)
    {unitsL unitsR : List Nat} (nodupL : unitsL.Nodup) (nodupR : unitsR.Nodup)
    {initialL initialR storeL storeR : σ}
    (historyL : AllocationHistory actions unitsL initialL storeL)
    (historyR : AllocationHistory actions unitsR initialR storeR)
    (unitL unitR : Nat) {imports : Ports (Ty V S)} (inputsL inputsR : Tuple m.Val imports)
    (rowL : Row familyL inputsL) (rowR : Row familyR inputsR)
    {shiftedL shiftedR : Bool}
    (left : AllocatingClient Op imports clientFn value shiftedL)
    (right : AllocatingClient Op imports clientFn value shiftedR) :
    Option (CheckedAllocationChain actions ids keys captureCode (unitL :: unitsL) (unitR :: unitsR)
      (providerFn := clientFn) .head
      (Executable.link actions unitL left.toGraph inputsL storeL)
      (Executable.link actions unitR right.toGraph inputsR storeR)) :=
  if fresh : unitL ∉ unitsL ∧ unitR ∉ unitsR then
    let locals := AllocatingClient.initialLocals m
    match ranL : Executable.linkVertex actions unitL inputsL (locals shiftedL)
        (.delta left.initializer) storeL,
      ranR : Executable.linkVertex actions unitR inputsR (locals shiftedR)
        (.delta right.initializer) storeR with
    | .linked valuesL finalL, .linked valuesR finalR => do
      let scopeL := (locals shiftedL).snoc valuesL
      let scopeR := (locals shiftedR).snoc valuesR
      let some certified := prior.addLambda keys ordinary
        ((Table.empty familyL scopeL).availableWithImports prior.ordinaryL rowL)
        ((Table.empty familyR scopeR).availableWithImports prior.ordinaryR rowR) left.body right.body | none
      let calleeL := linkedLambda left.body inputsL scopeL
      let calleeR := linkedLambda right.body inputsR scopeR
      have linkedL : Executable.link actions unitL left.toGraph inputsL storeL =
          .linked (.cons calleeL .nil) finalL := by
        rw [AllocationProofs.link_body, ranL]
      have linkedR : Executable.link actions unitR right.toGraph inputsR storeR =
          .linked (.cons calleeR .nil) finalR := by
        rw [AllocationProofs.link_body, ranR]
      pure (CheckedAllocationChain.mk
        ⟨WithExport familyL calleeL, WithExport familyR calleeR,
          _, certified.down, .cons calleeL .nil, .cons calleeR .nil, finalL, finalR, linkedL, linkedR,
          WithExport.exported, WithExport.exported⟩
        initialL initialR
        (.link historyL linkedL) (.link historyR linkedR)
        (List.nodup_cons.mpr ⟨fresh.1, nodupL⟩) (List.nodup_cons.mpr ⟨fresh.2, nodupR⟩))
    | _, _ => none
  else none

/-- Link the client at the previous link's exact store. A successful
extension retains the new dispatch family and reserves the new unit against
the entire checked history on each side. -/
def CheckedAllocationChain.extend [DecidableEq (Ty V S)] {keys : OpcodeCode (Instruction Op)}
    [DecidableEq keys.Key] {captureCode : CaptureCode m} (actions : Actions m σ) {ids : GlobalRel}
    (ordinary : OrdinaryOutputs Op) (exactValue : ExactValueCheck m)
    {unitsL unitsR : List Nat} {port : Port exports providerFn.port} {outcomeL outcomeR : Outcome m σ exports}
    (prior : CheckedAllocationChain actions ids keys captureCode unitsL unitsR port outcomeL outcomeR)
    (unitL unitR : Nat) (inputsL inputsR : Tuple m.Val (providerFn.port :: extra))
    {shiftedL shiftedR : Bool}
    (left : AllocatingClient Op (providerFn.port :: extra) clientFn value shiftedL)
    (right : AllocatingClient Op (providerFn.port :: extra) clientFn value shiftedR) :
    Option (CheckedAllocationChain actions ids keys captureCode (unitL :: unitsL) (unitR :: unitsR)
      (providerFn := clientFn) .head
      (Executable.link actions unitL left.toGraph inputsL prior.checked.storeL)
      (Executable.link actions unitR right.toGraph inputsR prior.checked.storeR)) := do
  let some known := prior.checked.checkImport exactValue (inputsL.get .head) (inputsR.get .head) | none
  extendWithImports actions ordinary prior.checked.certified prior.nodupL prior.nodupR
    prior.historyL prior.historyR unitL unitR inputsL inputsR
    (Row.headOnly known.down.1) (Row.headOnly known.down.2) left right

section Join

variable {actions : Actions m σ} {ids : GlobalRel} {keys : OpcodeCode (Instruction Op)}
variable {captureCode : CaptureCode m}
variable {exportsA exportsB : Ports (Ty V S)} {fnA fnB : Function V S}
variable {unitsAL unitsAR unitsBL unitsBR : List Nat}
variable {portA : Port exportsA fnA.port} {portB : Port exportsB fnB.port}
variable {aL aR : Outcome m σ exportsA} {bL bR : Outcome m σ exportsB}

/-- Two checked histories in link order. The second starts at exactly the
first's final stores. Every reserved unit is disjoint from the other
history's units on its side. The dispatch union retains both families. -/
structure CheckedProviderJoin
    (first : CheckedAllocationChain actions ids keys captureCode unitsAL unitsAR portA aL aR)
    (second : CheckedAllocationChain actions ids keys captureCode unitsBL unitsBR portB bL bR) : Type where
  orderedL : second.initialL = first.checked.storeL
  orderedR : second.initialR = first.checked.storeR
  distinctL : (unitsBL ++ unitsAL).Nodup
  distinctR : (unitsBR ++ unitsAR).Nodup
  certified : LinkedFamily actions.toPrimitives ids keys captureCode
    (UnionIn first.checked.familyL second.checked.familyL) (UnionIn first.checked.familyR second.checked.familyR)
    (first.checked.keys.append second.checked.keys)

theorem CheckedProviderJoin.historyL
    {first : CheckedAllocationChain actions ids keys captureCode unitsAL unitsAR portA aL aR}
    {second : CheckedAllocationChain actions ids keys captureCode unitsBL unitsBR portB bL bR}
    (joined : CheckedProviderJoin first second) :
    AllocationHistory actions (unitsBL ++ unitsAL) first.initialL second.checked.storeL :=
  first.historyL.append (joined.orderedL ▸ second.historyL)

theorem CheckedProviderJoin.historyR
    {first : CheckedAllocationChain actions ids keys captureCode unitsAL unitsAR portA aL aR}
    {second : CheckedAllocationChain actions ids keys captureCode unitsBL unitsBR portB bL bR}
    (joined : CheckedProviderJoin first second) :
    AllocationHistory actions (unitsBR ++ unitsAR) first.initialR second.checked.storeR :=
  first.historyR.append (joined.orderedR ▸ second.historyR)

/-- Keep the last exact link outcome with the combined trace and dispatch. -/
def CheckedProviderJoin.toChain
    {first : CheckedAllocationChain actions ids keys captureCode unitsAL unitsAR portA aL aR}
    {second : CheckedAllocationChain actions ids keys captureCode unitsBL unitsBR portB bL bR}
    (joined : CheckedProviderJoin first second) :
    CheckedAllocationChain actions ids keys captureCode (unitsBL ++ unitsAL) (unitsBR ++ unitsAR) portB bL bR :=
  let last := second.checked
  CheckedAllocationChain.mk
    ⟨_, _, _, joined.certified, last.valuesL, last.valuesR, last.storeL, last.storeR,
      last.linkedL, last.linkedR, .inr last.knownL, .inr last.knownR⟩
    first.initialL first.initialR joined.historyL joined.historyR joined.distinctL joined.distinctR

/-- Reconcile two receipts by checking the store boundary, allocation
history and both mixed dispatch directions. Neither link runs again. -/
def CheckedAllocationChain.join [DecidableEq (Ty V S)] [DecidableEq keys.Key] [DecidableEq σ]
    (first : CheckedAllocationChain actions ids keys captureCode unitsAL unitsAR portA aL aR)
    (second : CheckedAllocationChain actions ids keys captureCode unitsBL unitsBR portB bL bR)
    (ordinary : OrdinaryOutputs Op) : Option (CheckedProviderJoin first second) :=
  if order : second.initialL = first.checked.storeL ∧ second.initialR = first.checked.storeR then
    if distinct : (unitsBL ++ unitsAL).Nodup ∧ (unitsBR ++ unitsAR).Nodup then
      (first.checked.certified.join ordinary second.checked.certified).map fun union =>
        ⟨order.1, order.2, distinct.1, distinct.2, union.down⟩
    else none
  else none

private def twoImports {family : Family m} {inputs : Tuple m.Val (fnA.port :: fnB.port :: extra)}
    (knownA : family (inputs.get .head)) (knownB : family (inputs.get (.tail .head))) : Row family inputs
  | _, .head => some ⟨knownA⟩
  | _, .tail .head => some ⟨knownB⟩
  | _, .tail (.tail _) => none

/-- Link a δ→λ client at the second history's final stores. The first two
imports must be the exact exports of the two providers in order. Additional
captures may use the ordinary-value rule. Opaque allocations lie outside
the two certified reservation histories. -/
def CheckedProviderJoin.extend [DecidableEq (Ty V S)] [DecidableEq keys.Key]
    {first : CheckedAllocationChain actions ids keys captureCode unitsAL unitsAR portA aL aR}
    {second : CheckedAllocationChain actions ids keys captureCode unitsBL unitsBR portB bL bR}
    (joined : CheckedProviderJoin first second) (ordinary : OrdinaryOutputs Op) (exactValue : ExactValueCheck m)
    (unitL unitR : Nat) (inputsL inputsR : Tuple m.Val (fnA.port :: fnB.port :: extra))
    {shiftedL shiftedR : Bool}
    (left : AllocatingClient Op (fnA.port :: fnB.port :: extra) clientFn value shiftedL)
    (right : AllocatingClient Op (fnA.port :: fnB.port :: extra) clientFn value shiftedR) :
    Option (CheckedAllocationChain actions ids keys captureCode (unitL :: (unitsBL ++ unitsAL))
      (unitR :: (unitsBR ++ unitsAR)) (providerFn := clientFn) .head
      (Executable.link actions unitL left.toGraph inputsL second.checked.storeL)
      (Executable.link actions unitR right.toGraph inputsR second.checked.storeR)) := do
  let some knownA := first.checked.checkImport exactValue (inputsL.get .head) (inputsR.get .head) | none
  let some knownB := second.checked.checkImport exactValue (inputsL.get (.tail .head)) (inputsR.get (.tail .head)) | none
  extendWithImports actions ordinary joined.certified joined.distinctL joined.distinctR
    joined.historyL joined.historyR unitL unitR inputsL inputsR
    (twoImports (Or.inl knownA.down.1) (Or.inr knownB.down.1))
    (twoImports (Or.inl knownA.down.2) (Or.inr knownB.down.2)) left right

end Join

section Assembly

variable {actions : Actions m σ} {ids : GlobalRel} {keys : OpcodeCode (Instruction Op)}
variable {captureCode : CaptureCode m}
variable {unitsL unitsR : List Nat} {port : Port exports providerFn.port}
variable {outcomeL outcomeR : Outcome m σ exports}

/-- An actual export pair at a specified port type, admitted by the
assembly's accumulated dispatch family. -/
structure ProviderExport (familyL familyR : Family m) (ty : Ty V S) where
  left : m.Val ty
  right : m.Val ty
  knownL : familyL left
  knownR : familyR right

structure NamedProviderExport (familyL familyR : Family m) where
  name : String
  ty : Ty V S
  values : ProviderExport familyL familyR ty

/-- The selected provider receipt at its original typed port and link
outcomes, before its dispatch family was lifted into the assembly. -/
structure CheckedProviderReceipt (actions : Actions m σ) (ids : GlobalRel)
    (keys : OpcodeCode (Instruction Op)) (captureCode : CaptureCode m) where
  unitsL : List Nat
  unitsR : List Nat
  fn : Function V S
  exports : Ports (Ty V S)
  port : Port exports fn.port
  outcomeL : Outcome m σ exports
  outcomeR : Outcome m σ exports
  chain : CheckedAllocationChain actions ids keys captureCode unitsL unitsR port outcomeL outcomeR

variable (provider : CheckedProviderReceipt actions ids keys captureCode)

@[expose] def CheckedProviderReceipt.left : m.Val provider.fn.port :=
  provider.chain.checked.valuesL.get provider.port

@[expose] def CheckedProviderReceipt.right : m.Val provider.fn.port :=
  provider.chain.checked.valuesR.get provider.port

/-- Singleton demand index at the selected port and the provider's own
post-link store. It reads the checked result without running the linker. -/
@[expose] def CheckedProviderReceipt.selectedL : Outcome m σ [provider.fn.port] :=
  .linked (.cons provider.left .nil) provider.chain.checked.storeL

@[expose] def CheckedProviderReceipt.selectedR : Outcome m σ [provider.fn.port] :=
  .linked (.cons provider.right .nil) provider.chain.checked.storeR

/-- A named provider in the current trace and dispatch family. -/
structure AssemblyProvider (actions : Actions m σ) (ids : GlobalRel)
    (keys : OpcodeCode (Instruction Op)) (captureCode : CaptureCode m)
    (familyL familyR : Family m) (wholeL wholeR : List Nat)
    (initialL initialR finalL finalR : σ) where
  name : String
  provider : CheckedProviderReceipt actions ids keys captureCode
  knownL : familyL provider.left
  knownR : familyR provider.right
  traceL : AllocationHistory.Segment actions wholeL provider.unitsL initialL finalL
    provider.chain.initialL provider.chain.checked.storeL
  traceR : AllocationHistory.Segment actions wholeR provider.unitsR initialR finalR
    provider.chain.initialR provider.chain.checked.storeR

/-- Give the existing export-only view of the table row. -/
def AssemblyProvider.named {familyL familyR : Family m} {wholeL wholeR : List Nat}
    {initialL initialR finalL finalR : σ}
    (entry : AssemblyProvider actions ids keys captureCode familyL familyR wholeL wholeR initialL initialR finalL finalR) :
    NamedProviderExport familyL familyR :=
  ⟨entry.name, entry.provider.fn.port, ⟨entry.provider.left, entry.provider.right, entry.knownL, entry.knownR⟩⟩

/-- A nonempty ordered assembly with one selected export name per appended
receipt. The combined trace establishes freshness among certified units
on each side, excluding allocations from opaque imports. -/
structure CheckedProviderAssembly (actions : Actions m σ) (ids : GlobalRel)
    (keys : OpcodeCode (Instruction Op)) (captureCode : CaptureCode m) where
  private mk ::
  unitsL : List Nat
  unitsR : List Nat
  latestFn : Function V S
  latestPorts : Ports (Ty V S)
  latestPort : Port latestPorts latestFn.port
  latestL : Outcome m σ latestPorts
  latestR : Outcome m σ latestPorts
  chain : CheckedAllocationChain actions ids keys captureCode unitsL unitsR latestPort latestL latestR
  entries : List (AssemblyProvider actions ids keys captureCode chain.checked.familyL chain.checked.familyR
    unitsL unitsR chain.initialL chain.initialR chain.checked.storeL chain.checked.storeR)
  uniqueEntries : (entries.map AssemblyProvider.name).Nodup

def CheckedProviderAssembly.named (assembly : CheckedProviderAssembly actions ids keys captureCode) :
    List (NamedProviderExport assembly.chain.checked.familyL assembly.chain.checked.familyR) :=
  assembly.entries.map AssemblyProvider.named

theorem CheckedProviderAssembly.uniqueNames (assembly : CheckedProviderAssembly actions ids keys captureCode) :
    (assembly.named.map NamedProviderExport.name).Nodup := by
  simpa only [CheckedProviderAssembly.named, List.map_map, Function.comp_def, AssemblyProvider.named]
    using assembly.uniqueEntries

/-- Name the selected export of the first checked provider receipt. -/
def CheckedProviderAssembly.start (name : String)
    (first : CheckedAllocationChain actions ids keys captureCode unitsL unitsR port outcomeL outcomeR) :
    CheckedProviderAssembly actions ids keys captureCode :=
  let provider : CheckedProviderReceipt actions ids keys captureCode := ⟨_, _, _, _, _, _, _, first⟩
  ⟨_, _, _, _, _, provider.outcomeL, provider.outcomeR, first,
    [⟨name, provider, first.checked.knownL, first.checked.knownR,
      ⟨[], [], by simp [provider], .empty _, .empty _⟩, ⟨[], [], by simp [provider], .empty _, .empty _⟩⟩],
    List.nodup_singleton _⟩

/-- Append one separately checked provider at the assembly's exact store
boundary. The existing join checks reservations and dispatch against the
whole prefix. Earlier export names retain their exact values. -/
def CheckedProviderAssembly.append [DecidableEq (Ty V S)] [DecidableEq keys.Key] [DecidableEq σ]
    (assembly : CheckedProviderAssembly actions ids keys captureCode) (name : String)
    (next : CheckedAllocationChain actions ids keys captureCode unitsL unitsR port outcomeL outcomeR)
    (ordinary : OrdinaryOutputs Op) : Option (CheckedProviderAssembly actions ids keys captureCode) :=
  if fresh : name ∉ assembly.entries.map AssemblyProvider.name then do
    let some joined := assembly.chain.join next ordinary | none
    let tailL : AllocationHistory actions unitsL assembly.chain.checked.storeL next.checked.storeL :=
      joined.orderedL ▸ next.historyL
    let tailR : AllocationHistory actions unitsR assembly.chain.checked.storeR next.checked.storeR :=
      joined.orderedR ▸ next.historyR
    let older := assembly.entries.map fun entry =>
      (⟨entry.name, entry.provider, .inl entry.knownL, .inl entry.knownR,
        entry.traceL.extend tailL, entry.traceR.extend tailR⟩ :
        AssemblyProvider actions ids keys captureCode joined.toChain.checked.familyL joined.toChain.checked.familyR
          (unitsL ++ assembly.unitsL) (unitsR ++ assembly.unitsR)
          assembly.chain.initialL assembly.chain.initialR next.checked.storeL next.checked.storeR)
    let provider : CheckedProviderReceipt actions ids keys captureCode := ⟨_, _, _, _, _, _, _, next⟩
    let latest := ⟨name, provider, .inr next.checked.knownL, .inr next.checked.knownR,
      ⟨_, [], rfl, joined.orderedL.symm ▸ assembly.chain.historyL, .empty _⟩,
      ⟨_, [], rfl, joined.orderedR.symm ▸ assembly.chain.historyR, .empty _⟩⟩
    have unique : ((latest :: older).map AssemblyProvider.name).Nodup := by
      simpa [latest, older, List.map_map, Function.comp_def] using
        (List.nodup_cons.mpr ⟨fresh, assembly.uniqueEntries⟩)
    pure ⟨_, _, _, _, _, provider.outcomeL, provider.outcomeR, joined.toChain, latest :: older, unique⟩
  else none

/-- A typed name resolved in this assembly. The entry retains the original
provider, its place in both traces, and dispatch membership of the exact
imported values. -/
structure CheckedProviderAssembly.LookupReceipt (assembly : CheckedProviderAssembly actions ids keys captureCode)
    (name : String) (ty : Ty V S) where
  entry : AssemblyProvider actions ids keys captureCode assembly.chain.checked.familyL assembly.chain.checked.familyR
    assembly.unitsL assembly.unitsR assembly.chain.initialL assembly.chain.initialR
    assembly.chain.checked.storeL assembly.chain.checked.storeR
  selected : assembly.entries.find? (fun entry => entry.name == name) = some entry
  port_eq : entry.provider.fn.port = ty

/-- Look up a provider receipt by name and port type without relinking. -/
def CheckedProviderAssembly.lookup [DecidableEq (Ty V S)]
    (assembly : CheckedProviderAssembly actions ids keys captureCode) (name : String) (ty : Ty V S) :
    Option (assembly.LookupReceipt name ty) :=
  match found : assembly.entries.find? (fun entry => entry.name == name) with
  | none => none
  | some entry =>
    if typed : entry.provider.fn.port = ty then some ⟨entry, found, typed⟩ else none

def CheckedProviderAssembly.LookupReceipt.values {assembly : CheckedProviderAssembly actions ids keys captureCode}
    {name : String} {ty : Ty V S} (receipt : assembly.LookupReceipt name ty) :
    ProviderExport assembly.chain.checked.familyL assembly.chain.checked.familyR ty :=
  receipt.port_eq ▸ receipt.entry.named.values

theorem CheckedProviderAssembly.LookupReceipt.values_left
    {assembly : CheckedProviderAssembly actions ids keys captureCode} {name : String} {ty : Ty V S}
    (receipt : assembly.LookupReceipt name ty) :
    receipt.values.left = (receipt.port_eq ▸ receipt.entry.provider.left) := by
  obtain ⟨entry, selected, rfl⟩ := receipt
  rfl

theorem CheckedProviderAssembly.LookupReceipt.values_right
    {assembly : CheckedProviderAssembly actions ids keys captureCode} {name : String} {ty : Ty V S}
    (receipt : assembly.LookupReceipt name ty) :
    receipt.values.right = (receipt.port_eq ▸ receipt.entry.provider.right) := by
  obtain ⟨entry, selected, rfl⟩ := receipt
  rfl

/-- Validate already materialized imports against this name's exact pair.
Both comparisons must supply equality evidence. -/
def CheckedProviderAssembly.LookupReceipt.checkImports
    {assembly : CheckedProviderAssembly actions ids keys captureCode} {name : String} {ty : Ty V S}
    (receipt : assembly.LookupReceipt name ty) (exactValue : ExactValueCheck m) (left right : m.Val ty) :
    Option (PLift (left = receipt.values.left ∧ right = receipt.values.right)) := do
  let exactL ← exactValue left receipt.values.left
  let exactR ← exactValue right receipt.values.right
  pure ⟨⟨exactL.down, exactR.down⟩⟩

/-- Resolve a named export at the requested port type, using the values
that actually linked on each side. -/
def CheckedProviderAssembly.find [DecidableEq (Ty V S)]
    (assembly : CheckedProviderAssembly actions ids keys captureCode) (name : String) (ty : Ty V S) :
    Option (ProviderExport assembly.chain.checked.familyL assembly.chain.checked.familyR ty) :=
  (assembly.lookup name ty).map LookupReceipt.values

private structure ProviderImports (familyL familyR : Family m) (ports : Ports (Ty V S)) where
  left : Tuple m.Val ports
  right : Tuple m.Val ports
  rowL : Row familyL left
  rowR : Row familyR right

private def resolveProviderImports [DecidableEq (Ty V S)]
    (assembly : CheckedProviderAssembly actions ids keys captureCode) (extraL extraR : Tuple m.Val extra) :
    {selected : Ports (Ty V S)} → Tuple (fun _ : Ty V S => String) selected →
    Option (ProviderImports assembly.chain.checked.familyL assembly.chain.checked.familyR (selected ++ extra))
  | _, .nil => some ⟨extraL, extraR, fun _ => none, fun _ => none⟩
  | _, .cons (t := ty) name rest => do
    let found ← assembly.find name ty
    let tail ← resolveProviderImports assembly extraL extraR rest
    pure ⟨.cons found.left tail.left, .cons found.right tail.right,
      (fun p => match p with | .head => some ⟨found.knownL⟩ | .tail p => tail.rowL p),
      (fun p => match p with | .head => some ⟨found.knownR⟩ | .tail p => tail.rowR p)⟩

/-- Link a δ→λ client using any typed sequence of named exports followed
by ordinary imports. Each named input is taken directly from the assembly.
The new link uses the assembly's final stores and checks its unit against
the full history on each side. -/
def CheckedProviderAssembly.extend [DecidableEq (Ty V S)] [DecidableEq keys.Key]
    (assembly : CheckedProviderAssembly actions ids keys captureCode) (ordinary : OrdinaryOutputs Op)
    (unitL unitR : Nat) {selected : Ports (Ty V S)} (names : Tuple (fun _ : Ty V S => String) selected)
    (extraL extraR : Tuple m.Val extra) {shiftedL shiftedR : Bool}
    (left : AllocatingClient Op (selected ++ extra) clientFn value shiftedL)
    (right : AllocatingClient Op (selected ++ extra) clientFn value shiftedR) :
    Option (Σ imports : Tuple m.Val (selected ++ extra) × Tuple m.Val (selected ++ extra),
      CheckedAllocationChain actions ids keys captureCode (unitL :: assembly.unitsL) (unitR :: assembly.unitsR)
        (providerFn := clientFn) .head
        (Executable.link actions unitL left.toGraph imports.1 assembly.chain.checked.storeL)
        (Executable.link actions unitR right.toGraph imports.2 assembly.chain.checked.storeR)) := do
  let some resolved := resolveProviderImports assembly extraL extraR names | none
  let checked ← extendWithImports actions ordinary assembly.chain.checked.certified
    assembly.chain.nodupL assembly.chain.nodupR assembly.chain.historyL assembly.chain.historyR
    unitL unitR resolved.left resolved.right resolved.rowL resolved.rowR left right
  pure ⟨(resolved.left, resolved.right), checked⟩

end Assembly

/-- Admit the client's actual linked export, using the retained provider
dispatch certificate. Unit inequality separates all allocations made by
the provider unit from the client's δ. Clients have one δ and one λ,
with optional empty φ padding. This check assumes the caller manages
allocation identities of any units outside this pair. -/
@[expose] def admitAllocatingClient [DecidableEq (Ty V S)] {keys : OpcodeCode (Instruction Op)}
    [DecidableEq keys.Key] {captureCode : CaptureCode m} (actions : Actions m σ) {ids : GlobalRel}
    (ordinary : OrdinaryOutputs Op) (exactValue : ExactValueCheck m)
    {providerUnitL providerUnitR : Nat} {providerL : Omega Op importsL exports sigsL}
    {providerR : Omega Op importsR exports sigsR} {providerInputsL : Tuple m.Val importsL}
    {providerInputsR : Tuple m.Val importsR} {port : Port exports providerFn.port} {storeL storeR : σ}
    (provider : CheckedProvider actions ids keys captureCode providerUnitL providerUnitR providerL providerR
      providerInputsL providerInputsR port storeL storeR)
    (unitL unitR : Nat) (inputsL inputsR : Tuple m.Val (providerFn.port :: extra))
    {shiftedL shiftedR : Bool}
    (left : AllocatingClient Op (providerFn.port :: extra) clientFn value shiftedL)
    (right : AllocatingClient Op (providerFn.port :: extra) clientFn value shiftedR) :
    Option (PLift (AdmittedExport actions.toPrimitives ids (fn := clientFn) .head
      (Executable.link actions unitL left.toGraph inputsL provider.checked.storeL)
      (Executable.link actions unitR right.toGraph inputsR provider.checked.storeR) ∧
      unitL ≠ providerUnitL ∧ unitR ≠ providerUnitR)) :=
  (provider.allocationChain.extend actions ordinary exactValue unitL unitR inputsL inputsR left right).map fun next =>
    ⟨by simpa only [CheckedProvider.allocationChain] using next.checked.admitted, fun equal => next.fresh.1 (equal.symm ▸ List.mem_cons_self),
      fun equal => next.fresh.2 (equal.symm ▸ List.mem_cons_self)⟩

/-- Read the successful export through the actual initialized row, in
either of the two allocating layouts. -/
theorem AllocatingClient.link_body {imports : Ports (Ty V S)} {shifted : Bool}
    (client : AllocatingClient Op imports clientFn value shifted)
    (actions : Actions m σ) (unit : Nat) (inputs : Tuple m.Val imports) (store : σ) :
    let locals := AllocatingClient.initialLocals m shifted
    Executable.link actions unit client.toGraph inputs store =
      match Executable.linkVertex actions unit inputs locals (.delta client.initializer) store with
      | .undefined failure => .undefined failure
      | .linked values middle => .linked (.cons (linkedLambda client.body inputs (locals.snoc values)) .nil) middle :=
  AllocationProofs.link_body client actions unit inputs store

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Prefix
