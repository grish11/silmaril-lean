module
public import Silmaril.Elf.Corpus.MimallocOsFlags.Source.Elaboration.Thms
public import Silmaril.Elf.Corpus.MimallocOsFlags.Source.Projection.Thms
public import Silmaril.Elf.Corpus.MimallocOsFlags.Thms
public import Silmaril.Project.Shapes.Contextual.Defs
public import Silmaril.X86.Open.Thms

/-! Initialized global-object contexts for actual mimalloc Boolean flag getters.
These getters have no source callees. No replacement contract or desired
refinement premise is assumed. These are post-startup function problems, not allocator/global-init
correctness or semantic proofs. ELF addresses use the recorded zero load bias. -/
@[expose] public section
namespace Silmaril.Elf.Corpus.MimallocOsFlags.Context
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics
open Silmaril.Project.Shapes Silmaril.Project.Shapes.Contextual

structure Input where
  overcommit : Bool
  virtualReserve : Bool

def placement (g : Getter) : Silmaril.Project.Shapes.Placement := ⟨g.address, g.code, 0⟩

def field (name : String) : Option (Ctype × Int) := do
  let (tag, _) ← Source.Elaboration.core.tagDefs.head?
  let layout ← (Mem.Concrete.typeLayout 64 Source.Elaboration.core.toFile.tagDefs
    (.mk [] (.struct tag))).toOption
  let (_, type, offset) ← layout.members.find? (fun (member, _, _) => member.key == name)
  return (type, offset)

/-- Actual 48-byte struct with all eight fields initialized. Arbitrary canonical Boolean
flag states describe the post-startup caller-visible state; no desired return
or source-machine refinement certificate is an input. -/
def prepare (g : Getter) (i : Input) : Except String State := do
  let F := Source.Elaboration.function g
  unless F.params.isEmpty do throw "getter unexpectedly has parameters"
  let [(global, _)] := Source.Elaboration.core.globs | throw "expected one actual global"
  let [(tag, _)] := Source.Elaboration.core.tagDefs | throw "expected one actual struct tag"
  let aggregate : Ctype := .mk [] (.struct tag)
  let layout ← (Mem.Concrete.typeLayout 64 F.file.tagDefs aggregate).mapError (fun _ => "layout failed")
  unless layout.size == 48 && layout.align == 8 && layout.members.length == 8 do
    throw "unexpected actual mimalloc global layout"
  let mut memory : Mem.Concrete.State :=
    {nextId := 1, lastAddress := globalAddress + 48, allocations := Map.ofList
      [(0, ⟨globalAddress, 48, false, false, some aggregate, none, .UB064_modifying_const⟩)]}
  for (name, expectedOffset, value) in
      [("page_size", 0, 4096), ("large_page_size", 8, 0),
       ("alloc_granularity", 16, 4096), ("physical_memory", 24, 34359738368),
       ("virtual_address_bits", 32, 48), ("has_overcommit", 40, cond i.overcommit 1 0),
       ("has_partial_free", 41, 0), ("has_virtual_reserve", 42, cond i.virtualReserve 1 0)] do
    let some (_, type, offset) := layout.members.find? (fun (member, _, _) => member.key == name)
      | throw "missing actual global member"
    unless offset == expectedOffset do throw "unexpected actual member offset"
    let .mk _ (.basic (.integer intType)) := type | throw "member is not an actual integer"
    let (_, stored) ← (Mem.Concrete.storeTyped F.file.tagDefs memory type
      (.allocated 0 (globalAddress + offset)) (.integer intType value)).mapError
        (fun _ => "global member store failed")
    memory := stored
  let env := extendEnv [(global, .object (.pointer (.allocated 0 globalAddress)))] ∅
  return ⟨.effectExpr F.body env, [.procedureReturn F.bodyLabels], memory⟩

def readField (name : String) (s : State) : Option Int := do
  let (type, offset) ← field name
  let (value, _) ← (Mem.Concrete.loadTyped Source.Elaboration.core.toFile.tagDefs s.memory type
    (.allocated 0 (globalAddress + offset))).toOption
  match value with
  | .integer _ n => some n
  | _ => none

abbrev Observation := Option Int × Option Int × Option Int × Prop

def context (g : Getter) : Context Input Observation where
  sourceEntry i s := prepare g i = .ok s
  machineEntry _ m :=
    SysV.CallEntry (placement g) Source.signature 0 .nil m ∧
    globalAddress + 48 < (m.core.read .rsp).toNat ∧
    m.memory.Permitted .read globalAddress 48
  related i _ m :=
    Silmaril.X86.Ext.loadN m.memory (globalAddress + 40) 1 =
      some (BitVec.ofNat 64 (cond i.overcommit 1 0)) ∧
    Silmaril.X86.Ext.loadN m.memory (globalAddress + 42) 1 =
      some (BitVec.ofNat 64 (cond i.virtualReserve 1 0))
  footprint _ m := SysV.StackBelow m 0
  sourceObservation _ s t v :=
    (match v with | .loaded (.specified (.integer n)) => some n | _ => none,
     readField "has_overcommit" t, readField "has_virtual_reserve" t,
     t.memory.allocations = s.memory.allocations ∧ t.memory.bytes = s.memory.bytes ∧
       t.memory.dead = s.memory.dead ∧ t.memory.stdout = s.memory.stdout)
  machineObservation _ _ t :=
    (some ((t.core.read .rax).setWidth 8).toNat,
     (Silmaril.X86.Ext.loadN t.memory (globalAddress + 40) 1).map (fun n => (n.toNat : Int)),
     (Silmaril.X86.Ext.loadN t.memory (globalAddress + 42) 1).map (fun n => (n.toNat : Int)), True)
  callees := []

/-- Exact TU projection, real ELF bytes, actual computed Core and nonvacuous
joint-entry/safety/effect/first-return obligations. All remain problems to prove. -/
def statement (g : Getter) : Prop :=
  Source.Projection.exact ∧
  Silmaril.Elf.CodeAt Silmaril.Elf.Staged.Corpus.Mimalloc.X8664.LibmimallocSo21.F g.address g.code ∧
  C.ElaboratesWith Source.inputs Source.ail g.name (Source.Elaboration.function g) ∧
  Obligation (Source.Elaboration.function g) Silmaril.X86.Open.isa (placement g) (context g)

/-- Actual overcommit getter; an unproved source/machine obligation. -/
@[problem "silmaril.corpus.mimalloc.os_has_overcommit.contextual_bool"
  (title := "Actual mimalloc Boolean overcommit getter with global memory and ABI")]
def Task.overcommit : Prop := statement .overcommit
/-- Actual virtual-reserve getter; an unproved source/machine obligation. -/
@[problem "silmaril.corpus.mimalloc.os_has_virtual_reserve.contextual_bool"
  (title := "Actual mimalloc Boolean virtual-reserve getter with global memory and ABI")]
def Task.virtualReserve : Prop := statement .virtualReserve
end Silmaril.Elf.Corpus.MimallocOsFlags.Context
