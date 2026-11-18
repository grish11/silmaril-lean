module
public import Silmaril.Elf.Corpus.CjsonArraySize.Source.Elaboration.Thms
public import Silmaril.Elf.Corpus.CjsonArraySize.Thms
public import Silmaril.Elf.Corpus.CjsonArraySize.Source.Projection.Thms
public import Silmaril.Project.Shapes.Contextual.Defs
public import Silmaril.X86.Open.Thms
/-! A bounded, allocated, acyclic list domain for the actual traversal.
No count/result, source refinement, termination or callee law is an entry premise.
The bound64 is a deliberately finite demonstration domain, below unsigned wrap
and the source's narrowing-to-int overflow case; it is not full-input coverage.
Caller heap is observable; automatic parameter/local allocations are private.
Safety, machine first return and matching finite Core execution remain unproved. -/
@[expose] public section
namespace Silmaril.Elf.Corpus.CjsonArraySize.Context
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics
open Silmaril.Project.Shapes Silmaril.Project.Shapes.Contextual

inductive Input where
  | null
  | list (length : Fin 65)
  deriving DecidableEq, Repr

def Input.length : Input → Nat | .null => 0 | .list n => n.val

def heapAddress (index : Nat) : Nat := 1048576 + 64 * index

def rootWord : Input → BitVec 64
  | .null => 0
  | .list _ => BitVec.ofNat 64 (heapAddress 0)

def nextWord (length index : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (if index + 1 < length then heapAddress (index + 2) else 0)

def placement : Silmaril.Project.Shapes.Placement := ⟨address, code, 0⟩

/-- Parameter object0 is private. Caller root1 and nodes2..n+1 are disjoint,
properly typed allocations. The actual local-object machinery allocates below
524288, disjoint from the caller heap above1048576 and parameter at4096.
Only the fields read by the actual source are initialized, with real pointer
provenance. Caller objects become readonly after these typed stores. -/
def prepare (input : Input) : Except String State := do
  let F := Source.Elaboration.function
  let [(parameter, pointerType)] := F.params | throw "actual one-pointer parameter required"
  let .mk _ (.pointer _ aggregate@(.mk _ (.struct _))) := pointerType
    | throw "actual pointer-to-struct required"
  let layout ← (Mem.Concrete.typeLayout 64 F.file.tagDefs aggregate).mapError (fun _ => "actual layout failed")
  unless layout.size == 64 && layout.align == 8 do throw "unexpected cJSON layout"
  let some (_, childType, childOffset) := layout.members.find? (fun (name,_,_) => name.key == "child")
    | throw "missing child field"
  let some (_, nextType, nextOffset) := layout.members.find? (fun (name,_,_) => name.key == "next")
    | throw "missing next field"
  unless childOffset == 16 && nextOffset == 0 do throw "unexpected pointer field offsets"
  let length := input.length
  let heapAllocations := (List.range (length+1)).map fun index =>
    (((index+1 : Nat) : Int), Mem.Concrete.Allocation.mk (heapAddress index) 64 false false
      (some aggregate) none .UB064_modifying_const)
  let parameterAllocation : Mem.Concrete.Allocation :=
    ⟨4096, 8, false, false, some pointerType, none, .UB064_modifying_const⟩
  let initial : Mem.Concrete.State := {nextId := length+2, lastAddress := 524288, allocations := Map.ofList ((0, parameterAllocation) :: heapAllocations)}
  let store := fun memory type pointer value =>
    (Mem.Concrete.storeTyped F.file.tagDefs memory type pointer value).map Prod.snd
  let pointer := match input with
    | .null => .null aggregate
    | .list _ => .allocated 1 (heapAddress 0)
  let mut memory ← (store initial pointerType (.allocated 0 4096) (.pointer aggregate pointer)).mapError
    (fun _ => "parameter store failed")
  let first := if length == 0 then .null aggregate else .allocated 2 (heapAddress 1)
  memory ← (store memory childType (.allocated 1 (heapAddress 0 + 16)) (.pointer aggregate first)).mapError
    (fun _ => "root child store failed")
  for index in List.range length do
    let next := if index+1 == length then .null aggregate else .allocated (index+3) (heapAddress (index+2))
    memory ← (store memory nextType (.allocated (index+2) (heapAddress (index+1)))
      (.pointer aggregate next)).mapError (fun _ => "node next store failed")
  for (id, allocation) in heapAllocations do
    memory := {memory with allocations := memory.allocations.insert id {allocation with readonly := some .UB064_modifying_const}}
  let env := extendEnv [(parameter, .object (.pointer (.allocated 0 4096)))] ∅
  return ⟨.effectExpr F.body env, [.procedureReturn F.bodyLabels], memory⟩

/-- Every caller allocation, byte, pointer-provenance byte and lifetime is
observable, as are enum/function registrations and stdout. Bookkeeping for new
private automatic allocations and diagnostic source locations is not observed. -/
def callerPreserved (input : Input) (before after : Mem.Concrete.State) : Prop :=
  before.enumTypes = after.enumTypes ∧ before.functions = after.functions ∧
  before.stdout = after.stdout ∧
  ∀ (index : Nat), index < input.length+1 →
    before.allocations.lookup (((index+1 : Nat) : Int)) = after.allocations.lookup (((index+1 : Nat) : Int)) ∧
    (((index+1 : Nat) : Int) ∈ before.dead ↔ ((index+1 : Nat) : Int) ∈ after.dead) ∧
    ∀ (offset : Nat), offset < 64 →
      before.bytes.lookup (((heapAddress index + offset : Nat) : Int)) = after.bytes.lookup (((heapAddress index + offset : Nat) : Int)) ∧
      before.pointerBytes.lookup (((heapAddress index + offset : Nat) : Int)) = after.pointerBytes.lookup (((heapAddress index + offset : Nat) : Int))

abbrev Observation := Option Int × Prop

def context : Context Input Observation where
  sourceEntry input state := prepare input = .ok state
  machineEntry input machine :=
    SysV.CallEntry placement Source.signature 0 (.cons (rootWord input) .nil) machine ∧
    heapAddress 66 + 65536 < (machine.core.read .rsp).toNat ∧
    (∀ (index : Nat), index < input.length+1 → machine.memory.Permitted .read (heapAddress index) 64)
  related input _ machine :=
    (input ≠ .null → Silmaril.X86.Ext.loadN machine.memory (heapAddress 0 + 16) 8 =
      some (BitVec.ofNat 64 (if input.length == 0 then 0 else heapAddress 1))) ∧
    (∀ (index : Nat), index < input.length → Silmaril.X86.Ext.loadN machine.memory (heapAddress (index+1)) 8 =
      some (nextWord input.length index))
  footprint _ machine := SysV.StackBelow machine 0
  sourceObservation input before after value :=
    (match value with | .loaded (.specified (.integer n)) => some n | _ => none,
      callerPreserved input before.memory after.memory)
  machineObservation _ _ after := (some ((after.core.read .rax).setWidth 32).toInt, True)
  callees := []

/-- Nonvacuity and safety are obligations. Machine termination/first return and
matching finite source execution are demanded, not assumed. This does not state
universal Core termination, divergence equivalence, cyclic-list behavior or
invalid-pointer/oversized-list correctness. No source callee is replaced. -/
@[problem "silmaril.corpus.cjson.get_array_size.bounded_traversal"
  (title := "Actual cJSON_GetArraySize allocated finite-list traversal and ELF context")]
def Task.compilesTo : Prop :=
  Source.Projection.exact ∧
  Silmaril.Elf.CodeAt Silmaril.Elf.Staged.Corpus.Cjson.X8664.LibcjsonSo1.F address code ∧
  C.ElaboratesWith Source.inputs Source.ail "cJSON_GetArraySize" Source.Elaboration.function ∧
  Obligation Source.Elaboration.function Silmaril.X86.Open.isa placement context
end Silmaril.Elf.Corpus.CjsonArraySize.Context
