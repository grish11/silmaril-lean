module
public import Silmaril.Elf.Corpus.CjsonInsert.Source.Elaboration.Thms
public import Silmaril.Elf.Corpus.CjsonInsert.Defs
public import Silmaril.Elf.Corpus.CjsonInsert.Source.Projection.Defs
public import Silmaril.Project.Shapes.Contextual.Defs
public import Silmaril.X86.Open.Thms
/-! Local bounded insertion draft. The four actual source definitions execute;
no helper contract, result, desired heap, safety or termination is an entry premise.
Private automatic bytes and allocator/excluded-action bookkeeping are projected
away in this nested-call context ONLY. Their contextual unobservability remains
an explicit observation-adequacy gap; this is not arbitrary-continuation equivalence. -/
@[expose] public section
namespace Silmaril.Elf.Corpus.CjsonInsert.Context
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics
open Silmaril.Project.Shapes Silmaril.Project.Shapes.Contextual
structure Input where
  append : Bool
  base : Nat
  payload : Nat → BitVec 8
  aligned : base % 8 = 0
  lower : 1048576 ≤ base
  upper : base + 384 < 2^47
def index (i : Input) : BitVec 32 := if i.append then 3 else 1
def heap (i : Input) (j : Nat) : Nat := i.base + 64*j
def placement : Silmaril.Project.Shapes.Placement := ⟨BitVec.ofNat 64 address,code,0⟩
/-- root, first, middle, tail, new item and unrelated: six disjoint live
64-byte caller objects. Three original parameter objects remain observed too. -/
def prepare (i : Input) : Except String State := do
  let F := Source.Elaboration.function
  let [(array,pointerType),(which,intType),(item,_)] := F.params | throw "actual parameters missing"
  let .mk _ (.pointer _ aggregate@(.mk _ (.struct _))) := pointerType | throw "actual pointer missing"
  let layout ← (Mem.Concrete.typeLayout 64 F.file.tagDefs aggregate).mapError (fun _ => "layout failed")
  unless layout.size == 64 && layout.align == 8 do throw "actual layout mismatch"
  let some (_,nextType,nextOffset) := layout.members.find? (fun (s,_,_) => s.key == "next") | throw "next missing"
  let some (_,_,prevOffset) := layout.members.find? (fun (s,_,_) => s.key == "prev") | throw "prev missing"
  let some (_,_,childOffset) := layout.members.find? (fun (s,_,_) => s.key == "child") | throw "child missing"
  unless nextOffset == 0 && prevOffset == 8 && childOffset == 16 do throw "field offset mismatch"
  let allocs := [(0,Mem.Concrete.Allocation.mk 4096 8 false false (some pointerType) none .UB064_modifying_const),
    (1,Mem.Concrete.Allocation.mk 4104 4 false false (some intType) none .UB064_modifying_const),
    (2,Mem.Concrete.Allocation.mk 4112 8 false false (some pointerType) none .UB064_modifying_const)] ++
    (List.range 6).map (fun j => (((j+3 : Nat) : Int),Mem.Concrete.Allocation.mk (heap i j) 64 false false (some aggregate) none .UB064_modifying_const))
  let initial : Mem.Concrete.State := {
    allocations := Map.ofList allocs, nextId := 9, lastAddress := 524288
    bytes := Map.ofList ((List.range 384).map fun off => (((i.base+off : Nat) : Int),some ((i.payload off).toNat : Int))) }
  let store := fun m type p v =>
    (Mem.Concrete.storeTyped F.file.tagDefs m type p v).map Prod.snd |>.mapError (fun _ => "typed initialization failed")
  let ptr := fun j => Mem.Concrete.Pointer.allocated (Int.ofNat (j+3)) (heap i j)
  let mut m ← store initial pointerType (.allocated 0 4096) (.pointer aggregate (ptr 0))
  m ← store m intType (.allocated 1 4104) (.integer (.signed .int) (index i).toInt)
  m ← store m pointerType (.allocated 2 4112) (.pointer aggregate (ptr 4))
  for (j,off,k) in ([(0,16,1),(1,0,2),(1,8,3),(2,0,3),(2,8,1),(3,8,2)] : List (Nat × Nat × Nat)) do
    m ← store m nextType (.allocated (Int.ofNat (j+3)) (heap i j+off)) (.pointer aggregate (ptr k))
  for j in [3,4] do m ← store m nextType (ptr j) (.pointer aggregate (.null aggregate))
  let env := extendEnv [(array,.object (.pointer (.allocated 0 4096))),
    (which,.object (.pointer (.allocated 1 4104))),(item,.object (.pointer (.allocated 2 4112)))] ∅
  return ⟨.effectExpr F.body env,[.procedureReturn F.bodyLabels],m⟩
/-- Exact postcondition stores, not an entry restriction or body replacement. -/
def updates (i : Input) : List (Nat × Nat × Nat) :=
  if i.append then [(3,0,4),(4,8,3),(1,8,4)] else [(4,0,2),(4,8,1),(2,8,4),(1,0,4)]
def expectedMemory (i : Input) (before : Mem.Concrete.State) : Except String Mem.Concrete.State := do
  let F := Source.Elaboration.function
  let [(_,pointerType),_,_] := F.params | throw "parameters missing"
  let .mk _ (.pointer _ aggregate@(.mk _ (.struct _))) := pointerType | throw "pointer missing"
  let layout ← (Mem.Concrete.typeLayout 64 F.file.tagDefs aggregate).mapError (fun _ => "layout failed")
  let some (_,nextType,_) := layout.members.find? (fun (s,_,_) => s.key == "next") | throw "next missing"
  let mut m := before
  for (j,off,k) in updates i do
    m ← (Mem.Concrete.storeTyped F.file.tagDefs m nextType
      (.allocated (Int.ofNat (j+3)) (heap i j+off))
      (.pointer aggregate (.allocated (Int.ofNat (k+3)) (heap i k)))).map Prod.snd |>.mapError (fun _ => "post store failed")
  return m
/-- Every original caller allocation, lifetime, byte, pointer provenance,
permission and stdout remains checked. All actually fresh private objects must
be dead. Hidden private bytes/bookkeeping retain the adequacy gap above. -/
def callerUpdate (i : Input) (before after : Mem.Concrete.State) : Prop :=
  ∃ expected, expectedMemory i before = .ok expected ∧
    before.enumTypes = after.enumTypes ∧ before.functions = after.functions ∧ before.stdout = after.stdout ∧
    (∀ id : Int, 0 ≤ id → id < 9 → before.allocations.lookup id = after.allocations.lookup id ∧
      (id ∈ before.dead ↔ id ∈ after.dead)) ∧
    (∀ off, off < 384 → after.bytes.lookup ((i.base+off : Nat) : Int) = expected.bytes.lookup ((i.base+off : Nat) : Int) ∧
      after.pointerBytes.lookup ((i.base+off : Nat) : Int) = expected.pointerBytes.lookup ((i.base+off : Nat) : Int)) ∧
    (∀ off, off < 24 → after.bytes.lookup (4096+off) = before.bytes.lookup (4096+off) ∧
      after.pointerBytes.lookup (4096+off) = before.pointerBytes.lookup (4096+off)) ∧
    (∀ id : Int, before.nextId ≤ id → id < after.nextId → id ∈ after.dead)
def heapWrite (i : Input) (a : Nat) : Prop :=
  ∃ j off k, (j,off,k) ∈ updates i ∧ heap i j+off ≤ a ∧ a < heap i j+off+8
abbrev Observation := Option (BitVec 32) × Prop × List (Option (BitVec 64))
def context : Context Input Observation where
  sourceEntry i s := prepare i = .ok s
  machineEntry i m :=
    SysV.CallEntry placement Source.signature 128
      (.cons (BitVec.ofNat 64 i.base) (.cons (index i) (.cons (BitVec.ofNat 64 (heap i 4)) .nil))) m ∧
    heap i 6+65536 < SysV.rspOf m ∧
    m.memory.Permitted .read i.base 384 ∧
    (∀ j off k, (j,off,k) ∈ updates i → m.memory.Permitted .write (heap i j+off) 8) ∧
    (∀ a c, (a,c) ∈ excerpts → Silmaril.X86.Ext.Loaded m.memory (BitVec.ofNat 64 a) c)
  related i s m := ∀ off, off < 384 →
    ∃ value, s.memory.bytes.lookup ((i.base+off : Nat) : Int) = some (some value) ∧
      m.memory.bytes.get? (i.base+off) = some (BitVec.ofInt 8 value)
  footprint i m a := SysV.StackBelow m 128 a ∨ heapWrite i a
  sourceObservation i before after value :=
    ((match value with | .loaded (.specified (.integer n)) => some (BitVec.ofInt 32 n) | _ => none),
      callerUpdate i before.memory after.memory,
      (updates i).map (fun (_,_,k) => some (BitVec.ofNat 64 (heap i k))))
  machineObservation i _ after := (some ((after.core.read .rax).setWidth 32),True,
    (updates i).map (fun (j,off,_) => Silmaril.X86.Ext.loadN after.memory (heap i j+off) 8))
  callees := []
/-- Bounded unproved obligation. Joint entries, source safety, machine first
returns, int32 ABI, exact heap writes and matching finite source executions are
all demanded. Endpoints, aliases, other indices, arbitrary lists, divergence,
whole-TU and observation adequacy remain outside this bounded draft. -/
@[problem "silmaril.corpus.cjson.insert_item_in_array.bounded_mutation"
  (title := "Actual cJSON insertion caller and three-helper heap mutation with O0 ELF context")]
def Task.compilesTo : Prop :=
  Source.Projection.exact ∧
  (∀ a c, (a,c) ∈ excerpts → Silmaril.Elf.CodeAt
    Silmaril.Elf.Staged.CorpusVariants.Cjson.N1719.Default.X8664.O0.Unstripped.LibcjsonSo1.F a c) ∧
  C.ElaboratesWith Source.inputs Source.ail "cJSON_InsertItemInArray" Source.Elaboration.function ∧
  Obligation Source.Elaboration.function Silmaril.X86.Open.isa placement context
end Silmaril.Elf.Corpus.CjsonInsert.Context
