module
public import Silmaril.Elf.Corpus.CjsonSuffix.Source.Elaboration.Thms
public import Silmaril.Elf.Corpus.CjsonSuffix.Source.Projection.Thms
public import Silmaril.Elf.Corpus.CjsonSuffix.Thms
public import Silmaril.Project.Shapes.Contextual.Defs
public import Silmaril.X86.Open.Thms
/-! Actual two-store mutation of distinct live cJSON objects, with a third
unrelated caller object. This deliberately restricted four-case initial domain
has no null/alias/dead objects, substitute callee or desired final-heap premise.
Exact source typed-store effects are a POSTCONDITION to discharge, not assumed.
Machine writes are bounded to the two observed fields and 24 private stack bytes;
all other bytes and all mapping metadata must be preserved. No refinement,
safety, joint-entry existence, first-return or semantic correctness is proved. -/
@[expose] public section
namespace Silmaril.Elf.Corpus.CjsonSuffix.Context
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics
open Silmaril.Project.Shapes Silmaril.Project.Shapes.Contextual

abbrev Input := Fin 4

def heapAddress (index : Nat) : Nat := 1048576 + 64 * index

def placement : Silmaril.Project.Shapes.Placement := ⟨address, code, 0⟩

/-- Source field types come from the actual parameter's actual cJSON layout. -/
def fields : Except String (Ctype × Ctype × Ctype) := do
  let F := Source.Elaboration.function
  let [(_, prevType), (_, itemType)] := F.params | throw "actual two parameters required"
  let .mk _ (.pointer _ aggregate@(.mk _ (.struct tag))) := prevType | throw "actual struct pointer required"
  let .mk _ (.pointer _ (.mk _ (.struct tag'))) := itemType | throw "actual second pointer required"
  unless tag.key == tag'.key do throw "different struct referents"
  let layout ← (Mem.Concrete.typeLayout 64 F.file.tagDefs aggregate).mapError (fun _ => "layout failed")
  unless layout.size == 64 && layout.align == 8 do throw "actual64-byte aligned layout required"
  let some (_, nextType, 0) := layout.members.find? (fun (name,_,_) => name.key == "next")
    | throw "actual next offset0 required"
  let some (_, prevFieldType, 8) := layout.members.find? (fun (name,_,_) => name.key == "prev")
    | throw "actual prev offset8 required"
  return (aggregate, nextType, prevFieldType)

/-- Initialize two distinct writable objects and a third unrelated readonly
object. The two private parameter allocations are readonly. All pointer values
are typed stores with actual allocation provenance; no source read sees a dead
or missing allocation. The four cases vary the old fields between null and the
unrelated object's address, so both overwrites are observable. -/
def prepare (input : Input) : Except String State := do
  let F := Source.Elaboration.function
  let [(prev, prevType), (item, itemType)] := F.params | throw "two actual parameters required"
  let (aggregate, nextType, prevFieldType) ← fields
  let allocation := fun index => Mem.Concrete.Allocation.mk (heapAddress index) 64 false false
    (some aggregate) none .UB064_modifying_const
  let initial : Mem.Concrete.State := {
    nextId := 5, lastAddress := 524288
    allocations := Map.ofList [(0, ⟨4096, 8, false, false, some prevType, none, .UB064_modifying_const⟩),
      (1, ⟨4104, 8, false, false, some itemType, none, .UB064_modifying_const⟩),
      (2, allocation 0), (3, allocation 1), (4, allocation 2)]
    bytes := Map.ofList ((List.range 192).map fun offset => ((heapAddress 0 + offset : Nat), some 0)) }
  let store := fun memory type pointer value =>
    (Mem.Concrete.storeTyped F.file.tagDefs memory type pointer value).map Prod.snd
  let mut memory ← (store initial prevType (.allocated 0 4096)
    (.pointer aggregate (.allocated 2 (heapAddress 0)))).mapError (fun _ => "prev parameter store failed")
  memory ← (store memory itemType (.allocated 1 4104)
    (.pointer aggregate (.allocated 3 (heapAddress 1)))).mapError (fun _ => "item parameter store failed")
  let oldNext := if input.val % 2 == 0 then .null aggregate else .allocated 4 (heapAddress 2)
  let oldPrev := if input.val / 2 == 0 then .null aggregate else .allocated 4 (heapAddress 2)
  memory ← (store memory nextType (.allocated 2 (heapAddress 0)) (.pointer aggregate oldNext)).mapError
    (fun _ => "old next initialization failed")
  memory ← (store memory prevFieldType (.allocated 3 (heapAddress 1 + 8)) (.pointer aggregate oldPrev)).mapError
    (fun _ => "old prev initialization failed")
  for id in [0,1,4] do
    let some a := memory.allocations.lookup id | throw "missing initialized allocation"
    memory := {memory with allocations := memory.allocations.insert id {a with readonly := some .UB064_modifying_const}}
  let env := extendEnv [(prev, .object (.pointer (.allocated 0 4096))),
    (item, .object (.pointer (.allocated 1 4104)))] ∅
  return ⟨.effectExpr F.body env, [.procedureReturn F.bodyLabels], memory⟩

/-- The exact two typed pointer stores determine every field of expected source
memory, including allocation/provenance/lifetime/stdout state. This function
executes no substituted source body and is never an entry assumption. -/
def expectedMemory (before : Mem.Concrete.State) : Except String Mem.Concrete.State := do
  let F := Source.Elaboration.function
  let (aggregate, nextType, prevType) ← fields
  let (_, first) ← (Mem.Concrete.storeTyped F.file.tagDefs before nextType
    (.allocated 2 (heapAddress 0)) (.pointer aggregate (.allocated 3 (heapAddress 1)))).mapError
    (fun _ => "expected first typed store rejected")
  let (_, second) ← (Mem.Concrete.storeTyped F.file.tagDefs first prevType
    (.allocated 3 (heapAddress 1 + 8)) (.pointer aggregate (.allocated 2 (heapAddress 0)))).mapError
    (fun _ => "expected second typed store rejected")
  -- Each actual negative assignment store crosses its enclosing strong bind;
  -- pinned Dynamics.liftAction allocates one excluded-action token each time.
  -- The exact increment remains a demanded postcondition, never an entry law.
  return {second with nextExcluded := before.nextExcluded + 2}

/-- ONLY diagnostic location is normalized. Parameters, caller objects,
all other memory, pointer provenance, allocation/lifetime state and stdout are
compared as a complete record against the two-store postcondition. -/
def exactUpdate (before after : Mem.Concrete.State) : Prop :=
  ∃ expected, expectedMemory before = .ok expected ∧
    {after with currentLocation := expected.currentLocation} = expected

abbrev Observation := Prop × List (Option (BitVec 64))

def heapWrite (location : Nat) : Prop :=
  (heapAddress 0 ≤ location ∧ location < heapAddress 0 + 8) ∨
  (heapAddress 1 + 8 ≤ location ∧ location < heapAddress 1 + 16)

def footprint (machine : Silmaril.X86.MState) (location : Nat) : Prop :=
  SysV.StackBelow machine 24 location ∨ heapWrite location

def context : Context Input Observation where
  sourceEntry input state := prepare input = .ok state
  machineEntry _ machine :=
    SysV.CallEntry placement Source.signature 24
      (.cons (BitVec.ofNat 64 (heapAddress 0)) (.cons (BitVec.ofNat 64 (heapAddress 1)) .nil)) machine ∧
    heapAddress 3 + 65536 < (machine.core.read .rsp).toNat ∧
    Silmaril.Process.Memory.Permitted machine.memory .write (heapAddress 0) 8 ∧
    Silmaril.Process.Memory.Permitted machine.memory .write (heapAddress 1 + 8) 8 ∧
    Silmaril.Process.Memory.Permitted machine.memory .read (heapAddress 0) 192
  related input _ machine :=
    Silmaril.X86.Ext.loadN machine.memory (heapAddress 0) 8 =
      some (BitVec.ofNat 64 (if input.val % 2 == 0 then 0 else heapAddress 2)) ∧
    Silmaril.X86.Ext.loadN machine.memory (heapAddress 1 + 8) 8 =
      some (BitVec.ofNat 64 (if input.val / 2 == 0 then 0 else heapAddress 2)) ∧
    (∀ offset : Nat, offset < 192 → ¬ heapWrite (heapAddress 0 + offset) →
      machine.memory.bytes.get? (heapAddress 0 + offset) = some (0 : BitVec 8))
  footprint _ machine := footprint machine
  sourceObservation _ before after _ :=
    (exactUpdate before.memory after.memory,
      [some (BitVec.ofNat 64 (heapAddress 1)), some (BitVec.ofNat 64 (heapAddress 0))])
  machineObservation _ _ after := (True,
    [Silmaril.X86.Ext.loadN after.memory (heapAddress 0) 8,
     Silmaril.X86.Ext.loadN after.memory (heapAddress 1 + 8) 8])
  callees := []

/-- Source exact-update is demanded by observation equality with True; the
machine must supply both actual stored pointer words. WritesWithin additionally
preserves every unrelated byte and all region metadata. Thus no arbitrary write
inside an unobserved heap footprint can satisfy this obligation. This is not a
claim for aliasing/null/dead inputs or whole-program/allocator correctness. -/
@[problem "silmaril.corpus.cjson.suffix_object.disjoint_mutation"
  (title := "Actual cJSON suffix_object two-pointer caller-heap mutation and O0 ELF context")]
def Task.compilesTo : Prop :=
  Source.Projection.exact ∧
  Silmaril.Elf.CodeAt Silmaril.Elf.Staged.CorpusVariants.Cjson.N1719.Default.X8664.O0.Unstripped.LibcjsonSo1.F address code ∧
  C.ElaboratesWith Source.inputs Source.ail "suffix_object" Source.Elaboration.function ∧
  Obligation Source.Elaboration.function Silmaril.X86.Open.isa placement context
end Silmaril.Elf.Corpus.CjsonSuffix.Context
