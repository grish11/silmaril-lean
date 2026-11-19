module
public import Silmaril.Elf.Corpus.CjsonArrayItem.Source.Elaboration.Thms
public import Silmaril.Elf.Corpus.CjsonArrayItem.Source.Projection.Thms
public import Silmaril.Elf.Corpus.CjsonArrayItem.Thms
public import Silmaril.Project.Shapes.Contextual.Defs
public import Silmaril.X86.Open.Thms
/-! Restricted contiguous finite-list caller/helper obligation, not full-input
coverage or a termination proof. All source bodies and target bytes are actual.
No safety, desired return, refinement or termination premise is supplied. -/
@[expose] public section
namespace Silmaril.Elf.Corpus.CjsonArrayItem.Context
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics
open Silmaril.Project.Shapes Silmaril.Project.Shapes.Contextual
structure Input where
  isNull : Bool
  length : Fin 65
  index : BitVec 32
  base : Nat
  payload : Nat → BitVec 8
  aligned : base % 8 = 0
  lower : 1048576 ≤ base
  upper : base + 66*64 < 2^47

def heap (i : Input) (index : Nat) : Nat := i.base+64*index
def rootWord (i : Input) : BitVec 64 := if i.isNull then 0 else BitVec.ofNat 64 i.base
def placement : Silmaril.Project.Shapes.Placement := ⟨address, code, entryOffset⟩

/-- Original parameter objects0/1 are private. Root2, nodes3..n+2 and an
unrelated object n+3 are disjoint64-byte caller allocations. Only actual child/
next links are typed pointer stores; every other payload byte remains arbitrary.
All initial objects become readonly. Actual helper arguments and local objects
are allocated/killed by the generated Core, without a substitute contract. -/
def prepare (i : Input) : Except String State := do
  let F := Source.Elaboration.function
  let [(array, pointerType), (index, intType)] := F.params
    | throw "actual pointer/int parameters missing"
  let .mk _ (.pointer _ aggregate@(.mk _ (.struct _))) := pointerType
    | throw "actual cJSON pointer missing"
  let layout ← (Mem.Concrete.typeLayout 64 F.file.tagDefs aggregate).mapError (fun _ => "actual layout failed")
  unless layout.size == 64 && layout.align == 8 do throw "unexpected cJSON layout"
  let some (_, childType, childOffset) := layout.members.find? (fun (s,_,_) => s.key == "child")
    | throw "actual child missing"
  let some (_, nextType, nextOffset) := layout.members.find? (fun (s,_,_) => s.key == "next")
    | throw "actual next missing"
  unless childOffset == 16 && nextOffset == 0 do throw "unexpected field offsets"
  let initialAllocations :=
    [(0,Mem.Concrete.Allocation.mk 4096 8 false false (some pointerType) none .UB064_modifying_const),
     (1,Mem.Concrete.Allocation.mk 4104 4 false false (some intType) none .UB064_modifying_const)] ++
    (List.range (i.length.val+2)).map (fun j =>
      (((j+2 : Nat) : Int),Mem.Concrete.Allocation.mk (heap i j) 64 false false
        (some aggregate) none .UB064_modifying_const))
  let initial : Mem.Concrete.State := {
    allocations := Map.ofList initialAllocations
    nextId := i.length.val+4
    lastAddress := 524288
    bytes := Map.ofList ((List.range ((i.length.val+2)*64)).map (fun off =>
      (((i.base+off : Nat) : Int),some ((i.payload off).toNat : Int)))) }
  let store := fun m type p value =>
    (Mem.Concrete.storeTyped F.file.tagDefs m type p value).map Prod.snd |>.mapError (fun _ => "typed initialization failed")
  let root := if i.isNull then .null aggregate else .allocated 2 (heap i 0)
  let mut memory ← store initial pointerType (.allocated 0 4096) (.pointer aggregate root)
  memory ← store memory intType (.allocated 1 4104) (.integer (.signed .int) i.index.toInt)
  let first := if i.length.val == 0 then .null aggregate else .allocated 3 (heap i 1)
  memory ← store memory childType (.allocated 2 (heap i 0+16)) (.pointer aggregate first)
  for j in List.range i.length.val do
    let next := if j+1 == i.length.val then .null aggregate else .allocated (j+4) (heap i (j+2))
    memory ← store memory nextType (.allocated (j+3) (heap i (j+1))) (.pointer aggregate next)
  for (id, allocation) in initialAllocations do
    memory := {memory with allocations := memory.allocations.insert id {allocation with readonly := some .UB064_modifying_const}}
  let env := extendEnv [(array,.object (.pointer (.allocated 0 4096))),
    (index,.object (.pointer (.allocated 1 4104)))] ∅
  return ⟨.effectExpr F.body env,[.procedureReturn F.bodyLabels],memory⟩

/-- Complete original allocation/lifetime, heap byte/provenance and output
observations; caller parameter objects are checked too. New private automatic/
argument allocations must be dead. Diagnostic currentLocation is not observed.
Private automatic-allocation bytes and allocator/excluded-action bookkeeping
are outside this caller observation. Their context-unobservability is NOT proved:
this observation-adequacy abstraction gap is specific to this nested-call problem,
not full-record memory equality or arbitrary-continuation equivalence. -/
def callerPreserved (i : Input) (a b : Mem.Concrete.State) : Prop :=
  a.enumTypes = b.enumTypes ∧ a.functions = b.functions ∧ a.stdout = b.stdout ∧
  (∀ id : Int, 0 ≤ id → id < i.length.val+4 →
    a.allocations.lookup id = b.allocations.lookup id ∧ (id ∈ a.dead ↔ id ∈ b.dead)) ∧
  (∀ off, off < (i.length.val+2)*64 →
    a.bytes.lookup ((i.base+off : Nat) : Int) = b.bytes.lookup ((i.base+off : Nat) : Int) ∧
    a.pointerBytes.lookup ((i.base+off : Nat) : Int) = b.pointerBytes.lookup ((i.base+off : Nat) : Int)) ∧
  (∀ off, off < 12 → a.bytes.lookup (4096+off) = b.bytes.lookup (4096+off) ∧
    a.pointerBytes.lookup (4096+off) = b.pointerBytes.lookup (4096+off)) ∧
  (∀ id : Int, a.nextId ≤ id → id < b.nextId → id ∈ b.dead)

/-- Projection demands provenance of a mapped caller object, not merely an
integer representation. A noncaller allocation or mismatched address is rejected.
The actual source computation determines which pointer is returned. -/
def pointerWord (i : Input) : Val → Option (BitVec 64)
  | .loaded (.specified (.pointer (.null _))) => some 0
  | .loaded (.specified (.pointer (.allocated id a))) =>
      if 2 ≤ id && id < i.length.val+4 && a == heap i (id.toNat-2) then
        some (BitVec.ofInt 64 a)
      else none
  | _ => none
abbrev Observation := Option (BitVec 64) × Prop

def context : Context Input Observation where
  sourceEntry i s := prepare i = .ok s
  machineEntry i m :=
    SysV.CallEntry placement Source.signature 72 (.cons (rootWord i) (.cons i.index .nil)) m ∧
    heap i (i.length.val+2)+65536 < SysV.rspOf m ∧
    m.memory.Permitted .read i.base ((i.length.val+2)*64)
  related i s m := ∀ off, off < (i.length.val+2)*64 →
    ∃ value, s.memory.bytes.lookup ((i.base+off : Nat) : Int) = some (some value) ∧
      m.memory.bytes.get? (i.base+off) = some (BitVec.ofInt 8 value)
  footprint _ m := SysV.StackBelow m 72
  sourceObservation i before after value :=
    (pointerWord i value,callerPreserved i before.memory after.memory)
  machineObservation _ _ after := (some (after.core.read .rax),True)
  callees := []

/-- Both actual caller/helper code are placed contiguously; the direct call
executes the helper. Source safety, joint entries, target first returns and every
first-return ABI/frame and matching source execution are demanded obligations.
No source/callee refinement or desired heap/return/termination assumption exists.
Universal termination/divergence, arbitrary graph/alias/dead inputs and whole-TU
adequacy remain outside this bounded list domain. -/
@[problem "silmaril.corpus.cjson.get_array_item.bounded_caller"
  (title := "Actual cJSON_GetArrayItem caller/helper allocated-list pointer return and ELF context")]
def Task.compilesTo : Prop :=
  Source.Projection.exact ∧
  Silmaril.Elf.CodeAt Silmaril.Elf.Staged.CorpusVariants.Cjson.N1719.Default.X8664.O0.Unstripped.LibcjsonSo1.F address code ∧
  C.ElaboratesWith Source.inputs Source.ail "cJSON_GetArrayItem" Source.Elaboration.function ∧
  Obligation Source.Elaboration.function Silmaril.X86.Open.isa placement context
end Silmaril.Elf.Corpus.CjsonArrayItem.Context
