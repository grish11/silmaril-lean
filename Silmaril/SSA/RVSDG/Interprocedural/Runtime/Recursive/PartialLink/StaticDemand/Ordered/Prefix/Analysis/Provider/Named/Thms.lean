module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Analysis.Provider.Named.Defs

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix

open Continuation.Partial.Executable (Actions)
open NestedTheta.Equality (OpcodeCode)
open Isomorphism.RecursiveCall.Numbered (CaptureCode ExactValueCheck)
open Isomorphism.RecursiveCall.Numbered.Prefix (AllocationHistory AllocatingClient CheckedProviderAssembly)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {actions : Actions m σ}
variable {ids : GlobalRel} {keys : OpcodeCode (Instruction Op)} {captureCode : CaptureCode m}
variable {assembly : CheckedProviderAssembly actions ids keys captureCode} {name : String} {ty : Ty V S}

theorem selectedDemandL_linked (lookup : assembly.LookupReceipt name ty) :
    selectedDemandL lookup = .linked (.cons lookup.values.left .nil) lookup.entry.provider.chain.checked.storeL := by
  rw [lookup.values_left]
  obtain ⟨entry, selected, rfl⟩ := lookup
  rfl

theorem selectedDemandR_linked (lookup : assembly.LookupReceipt name ty) :
    selectedDemandR lookup = .linked (.cons lookup.values.right .nil) lookup.entry.provider.chain.checked.storeR := by
  rw [lookup.values_right]
  obtain ⟨entry, selected, rfl⟩ := lookup
  rfl

/-- Reindex an existing demand certificate at a named result after checking
both actual closures and their original exit stores. This reads stored values. -/
def matchNamedExport [DecidableEq σ] {summary : MemberSummary V S}
    {left right : Outcome m σ [summary.fn.port]} (lookup : assembly.LookupReceipt name summary.fn.port)
    (sound : Export actions summary left right) (exactValue : ExactValueCheck m) :
    Option (PLift (selectedDemandL lookup = left ∧ selectedDemandR lookup = right)) := do
  let sameL ← exactValue lookup.values.left sound.targetL
  let sameR ← exactValue lookup.values.right sound.targetR
  if stores : lookup.entry.provider.chain.checked.storeL = sound.store ∧
      lookup.entry.provider.chain.checked.storeR = sound.store then
    let relocate := fun (target : m.Val summary.fn.port) (store : σ) =>
      Outcome.linked (.cons target .nil) store
    some ⟨(selectedDemandL_linked lookup).trans
      ((congrArg₂ relocate sameL.down stores.1).trans sound.linkedL.symm),
      (selectedDemandR_linked lookup).trans ((congrArg₂ relocate sameR.down stores.2).trans sound.linkedR.symm)⟩
  else none

/-- Recover the full store traces using the selected provider's original
history at the boundaries recorded by the lookup. -/
theorem NamedDemand.historyL {summary : MemberSummary V S} (source : NamedDemand assembly summary) :
    AllocationHistory actions assembly.unitsL assembly.chain.initialL assembly.chain.checked.storeL :=
  source.lookup.entry.traceL.reassemble source.lookup.entry.provider.chain.historyL

theorem NamedDemand.historyR {summary : MemberSummary V S} (source : NamedDemand assembly summary) :
    AllocationHistory actions assembly.unitsR assembly.chain.initialR assembly.chain.checked.storeR :=
  source.lookup.entry.traceR.reassemble source.lookup.entry.provider.chain.historyR

/-- Use the lookup's exact import check, then transport its equalities into
the exact targets recorded by the existing demand receipt. -/
def NamedDemand.check {summary : MemberSummary V S} (source : NamedDemand assembly summary)
    (exactValue : ExactValueCheck m) (left right : m.Val summary.fn.port) :
    Option (PLift (left = source.sound.targetL ∧ right = source.sound.targetR)) := do
  let same ← source.lookup.checkImports exactValue left right
  let selectedL := (Outcome.linked.inj ((selectedDemandL_linked source.lookup).symm.trans source.sound.linkedL)).1
  let selectedR := (Outcome.linked.inj ((selectedDemandR_linked source.lookup).symm.trans source.sound.linkedR)).1
  pure ⟨same.down.1.trans (congrArg (fun values => values.get .head) selectedL),
    same.down.2.trans (congrArg (fun values => values.get .head) selectedR)⟩

/-- Check the already materialized imports at their typed ports. Each
named pair is checked against its own lookup, even at repeated signatures. -/
def NamedImports.check (exactValue : ExactValueCheck m) {extra : Ports (Ty V S)} :
    {ports : Ports (Ty V S)} → (sources : NamedImports assembly ports) →
    (inputsL inputsR : Tuple m.Val (ports ++ extra)) → Option (sources.Rows inputsL inputsR)
  | _, .nil, _, _ => some ⟨fun _ => none, fun _ => none, trivial⟩
  | _, .cons source rest, .cons left tailL, .cons right tailR =>
    match source.check exactValue left right with
    | none => none
    | some same => do
      let slot : Fin (source.sound.earlier.members.length + 1) := 0
      let knownL := Known.callable (guard := source.sound.dispatch.left) slot
        source.sound.targetL source.sound.capsL source.sound.resolvedL
      let knownR := Known.callable (guard := source.sound.dispatch.right) slot
        source.sound.targetR source.sound.capsR source.sound.resolvedR
      let tail ← rest.check exactValue tailL tailR
      pure ⟨(fun p => match p with
        | .head => some ⟨Known.oldSlot rest.dispatch.left (same.down.1.symm ▸ knownL)⟩
        | .tail p => (tail.left p).map fun member => ⟨Known.newSlot source.sound.dispatch.left member.down⟩),
        (fun p => match p with
        | .head => some ⟨Known.oldSlot rest.dispatch.right (same.down.2.symm ▸ knownR)⟩
        | .tail p => (tail.right p).map fun member => ⟨Known.newSlot source.sound.dispatch.right member.down⟩),
        ⟨same.down.1, same.down.2, tail.matched⟩⟩

/-- Analyze a client from its resolved imports and successful initializer
receipt at the assembly's store. This consumes link results and uses the
existing allocating demand analysis for the final λ. -/
def NamedImports.analyzeAllocating {ports extra : Ports (Ty V S)} {fn : Function V S}
    {value : ValueSort V S} {shifted : Bool}
    (sources : NamedImports assembly ports)
    (layout : AllocationPlan Op sources.table (ports ++ extra) fn value shifted)
    (exactValue : ExactValueCheck m) (unit : Nat) (inputsL inputsR : Tuple m.Val (ports ++ extra))
    (initial : σ) (storeL : assembly.chain.checked.storeL = initial) (storeR : assembly.chain.checked.storeR = initial)
    (receipt : layout.Initialized actions unit inputsL inputsR initial)
    (readyL : sources.Matches inputsL inputsR → layout.binding.resolved sources.dispatch.left inputsL
      ((AllocatingClient.initialLocals m shifted).snoc receipt.left))
    (readyR : sources.Matches inputsL inputsR → layout.binding.resolved sources.dispatch.right inputsR
      ((AllocatingClient.initialLocals m shifted).snoc receipt.right)) :
    Option (ExportAnalysis actions layout.binding.summary
      (Executable.link actions unit layout.numbered.toGraph inputsL assembly.chain.checked.storeL)
      (Executable.link actions unit layout.numbered.toGraph inputsR assembly.chain.checked.storeR)) := do
  let admitted ← sources.check exactValue inputsL inputsR
  let checked ← layout.analyze sources.dispatch unit inputsL inputsR initial receipt
    admitted.left admitted.right (readyL admitted.matched) (readyR admitted.matched)
  pure ⟨checked.linked.relink
    (congrArg (Executable.link actions unit layout.numbered.toGraph inputsL) storeL)
    (congrArg (Executable.link actions unit layout.numbered.toGraph inputsR) storeR),
    checked.problem, checked.mem_problem⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix
