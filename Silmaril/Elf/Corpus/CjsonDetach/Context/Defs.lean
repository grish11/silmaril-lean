module
public import Silmaril.Elf.Corpus.CjsonDetach.Source.Elaboration.Thms
public import Silmaril.Elf.Corpus.CjsonDetach.Thms
public import Silmaril.Elf.Corpus.CjsonDetach.Source.Projection.Thms
public import Silmaril.Project.Shapes.Contextual.Defs
public import Silmaril.X86.Open.Thms
/-! Restricted interior-node detachment: parent, predecessor, item, successor
and unrelated caller object are distinct live64-byte allocations. Addresses and
all320 initial payload bytes are quantified, subject to alignment/disjointness
and canonical-address bounds. Initial list links are typed stores with real
provenance. Only the four actual pointer fields may change. This is not a claim
for endpoint/null/alias/dead/cyclic inputs, concurrency or whole-TU adequacy.
All safety, entry existence, exact update, return and first-return requirements
below are obligations, never input validity/refinement/termination premises. -/
@[expose] public section
namespace Silmaril.Elf.Corpus.CjsonDetach.Context
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics
open Silmaril.Project.Shapes Silmaril.Project.Shapes.Contextual

structure Input where
  address : Fin 5 → Nat
  payload : Fin 5 → Fin 64 → BitVec 8
  aligned : ∀ j, address j % 8 = 0
  lower : ∀ j, 65536 < address j
  upper : ∀ j, address j + 64 < 2^47
  disjoint : ∀ j k, j ≠ k → address j + 64 ≤ address k ∨ address k + 64 ≤ address j

def placement : Silmaril.Project.Shapes.Placement := ⟨address, code, 0⟩

/-- Actual parameter metadata determines the struct and all three link fields. -/
def fields : Except String (Ctype × Ctype × Ctype × Ctype) := do
  let F := Source.Elaboration.function
  let [(_, parentType), (_, itemType)] := F.params | throw "two actual pointer parameters required"
  let .mk _ (.pointer _ aggregate@(.mk _ (.struct tag))) := parentType | throw "actual parent struct pointer required"
  let .mk _ (.pointer _ (.mk _ (.struct other))) := itemType | throw "actual item struct pointer required"
  unless tag.key == other.key do throw "different struct referents"
  let layout ← (Mem.Concrete.typeLayout 64 F.file.tagDefs aggregate).mapError (fun _ => "layout failed")
  unless layout.size == 64 && layout.align == 8 do throw "actual64-byte align8 required"
  let some (_, next, 0) := layout.members.find? (fun (n,_,_) => n.key == "next") | throw "next offset0 required"
  let some (_, prev, 8) := layout.members.find? (fun (n,_,_) => n.key == "prev") | throw "prev offset8 required"
  let some (_, child, 16) := layout.members.find? (fun (n,_,_) => n.key == "child") | throw "child offset16 required"
  return (aggregate, next, prev, child)

def prepare (input : Input) : Except String State := do
  let F := Source.Elaboration.function
  let [(parent, parentType), (item, itemType)] := F.params | throw "two actual parameters required"
  let (aggregate, next, prev, child) ← fields
  let allocation := fun j : Fin 5 => Mem.Concrete.Allocation.mk (input.address j) 64 false false
    (some aggregate) none .UB064_modifying_const
  let initial : Mem.Concrete.State := {
    nextId := 7, lastAddress := 524288
    allocations := Map.ofList ([(0, ⟨4096, 8, false, false, some parentType, none, .UB064_modifying_const⟩),
      (1, ⟨4104, 8, false, false, some itemType, none, .UB064_modifying_const⟩)] ++
      (List.finRange 5).map (fun j => ((j.val + 2 : Int), allocation j)))
    bytes := Map.ofList ((List.finRange 5).flatMap fun j =>
      (List.finRange 64).map fun k => ((input.address j + k.val : Int), some (input.payload j k).toNat)) }
  let store := fun memory type pointer value =>
    (Mem.Concrete.storeTyped F.file.tagDefs memory type pointer value).map Prod.snd |>.mapError (fun _ => "typed initialization failed")
  let ptr := fun j : Fin 5 => Mem.Concrete.Pointer.allocated (j.val + 2) (input.address j)
  let mut memory ← store initial parentType (.allocated 0 4096) (.pointer aggregate (ptr 0))
  memory ← store memory itemType (.allocated 1 4104) (.pointer aggregate (ptr 2))
  memory ← store memory child (.allocated 2 (input.address 0 + 16)) (.pointer aggregate (ptr 1))
  memory ← store memory next (ptr 1) (.pointer aggregate (ptr 2))
  memory ← store memory prev (.allocated 3 (input.address 1 + 8)) (.pointer aggregate (ptr 3))
  memory ← store memory next (ptr 2) (.pointer aggregate (ptr 3))
  memory ← store memory prev (.allocated 4 (input.address 2 + 8)) (.pointer aggregate (ptr 1))
  memory ← store memory next (ptr 3) (.pointer aggregate (.null aggregate))
  memory ← store memory prev (.allocated 5 (input.address 3 + 8)) (.pointer aggregate (ptr 2))
  -- Private parameter slots, parent and unrelated object are readonly.
  for id in [0,1,2,6] do
    let some a := memory.allocations.lookup id | throw "missing initialized allocation"
    memory := {memory with allocations := memory.allocations.insert id {a with readonly := some .UB064_modifying_const}}
  let env := extendEnv [(parent, .object (.pointer (.allocated 0 4096))),
    (item, .object (.pointer (.allocated 1 4104)))] ∅
  return ⟨.effectExpr F.body env, [.procedureReturn F.bodyLabels], memory⟩

/-- Independent exact four-store POSTCONDITION. It does not run a replacement
body and is absent from all entry predicates. The final source parameter load
and four excluded assignment tokens are retained as demanded record fields. -/
def expectedMemory (input : Input) (before : Mem.Concrete.State) : Except String Mem.Concrete.State := do
  let F := Source.Elaboration.function
  let (aggregate, next, prev, _) ← fields
  let store := fun memory type pointer value =>
    (Mem.Concrete.storeTyped F.file.tagDefs memory type pointer value).map Prod.snd |>.mapError (fun _ => "postcondition typed store failed")
  let mut memory ← store before next (.allocated 3 (input.address 1)) (.pointer aggregate (.allocated 5 (input.address 3)))
  memory ← store memory prev (.allocated 5 (input.address 3 + 8)) (.pointer aggregate (.allocated 3 (input.address 1)))
  memory ← store memory prev (.allocated 4 (input.address 2 + 8)) (.pointer aggregate (.null aggregate))
  memory ← store memory next (.allocated 4 (input.address 2)) (.pointer aggregate (.null aggregate))
  return {memory with nextExcluded := before.nextExcluded + 4, lastUsed := some 1}

def exactUpdate (input : Input) (before after : Mem.Concrete.State) : Prop :=
  ∃ expected, expectedMemory input before = .ok expected ∧
    {after with currentLocation := expected.currentLocation} = expected

def returnMatches (input : Input) (value : Val) : Prop :=
  value = .loaded (.specified (.pointer (.allocated 4 (input.address 2))))

abbrev Observation := Prop × List (Option (BitVec 64))

def heapWrite (input : Input) (location : Nat) : Prop :=
  (input.address 1 ≤ location ∧ location < input.address 1 + 8) ∨
  (input.address 3 + 8 ≤ location ∧ location < input.address 3 + 16) ∨
  (input.address 2 ≤ location ∧ location < input.address 2 + 16)

def context : Context Input Observation where
  sourceEntry input state := prepare input = .ok state
  machineEntry input machine :=
    SysV.CallEntry placement Source.signature 24
      (.cons (BitVec.ofNat 64 (input.address 0)) (.cons (BitVec.ofNat 64 (input.address 2)) .nil)) machine ∧
    (∀ j, input.address j + 65536 < (machine.core.read .rsp).toNat) ∧
    (∀ j, Silmaril.Process.Memory.Permitted machine.memory .read (input.address j) 64) ∧
    Silmaril.Process.Memory.Permitted machine.memory .write (input.address 1) 8 ∧
    Silmaril.Process.Memory.Permitted machine.memory .write (input.address 3 + 8) 8 ∧
    Silmaril.Process.Memory.Permitted machine.memory .write (input.address 2) 16
  related input source machine :=
    ∀ (j : Fin 5) (k : Fin 64), ∃ value : Int,
      source.memory.bytes.lookup (↑(input.address j) + ↑k.val : Int) = some (some value) ∧
      machine.memory.bytes.get? (input.address j + k.val) = some (BitVec.ofInt 8 value)
  footprint input machine location := SysV.StackBelow machine 24 location ∨ heapWrite input location
  sourceObservation input before after value :=
    (exactUpdate input before.memory after.memory ∧ returnMatches input value,
      [some (BitVec.ofNat 64 (input.address 2)),
       some (BitVec.ofNat 64 (input.address 3)), some (BitVec.ofNat 64 (input.address 1)), some 0, some 0])
  machineObservation input _ after := (True,
    [some (after.core.read .rax), Silmaril.X86.Ext.loadN after.memory (input.address 1) 8,
     Silmaril.X86.Ext.loadN after.memory (input.address 3 + 8) 8,
     Silmaril.X86.Ext.loadN after.memory (input.address 2 + 8) 8,
     Silmaril.X86.Ext.loadN after.memory (input.address 2) 8])
  callees := []

/-- UNPROVED contextual obligation, including joint-entry existence and source
safety. Complete source memory/provenance/lifetimes/stdout are demanded; target
exact32-byte heap writes and returned pointer are observed, with only24 private
stack bytes additionally writable. All other target bytes and region metadata
must remain unchanged. No equality/refinement/callee/termination law is assumed. -/
@[problem "silmaril.corpus.cjson.detach_item_via_pointer.interior_mutation"
  (title := "Actual cJSON interior detachment with pointer return and exact caller-heap mutation")]
def Task.compilesTo : Prop :=
  Source.Projection.exact ∧
  Silmaril.Elf.CodeAt Silmaril.Elf.Staged.CorpusVariants.Cjson.N1719.Default.X8664.O0.Unstripped.LibcjsonSo1.F address code ∧
  C.ElaboratesWith Source.inputs Source.ail "cJSON_DetachItemViaPointer" Source.Elaboration.function ∧
  Obligation Source.Elaboration.function Silmaril.X86.Open.isa placement context
end Silmaril.Elf.Corpus.CjsonDetach.Context
