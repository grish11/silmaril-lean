module

public import Silmaril.Elf.Region.Calls.Semantic.Defs
public import Silmaril.Elf.Region.Calls.General.Defs
public import Silmaril.Elf.Region.Calls.Symbols.Defs
public import Silmaril.Elf.Staged.Pinned.HelloGcc.Bytes
public import Silmaril.Elf.Staged.Pinned.HelloGcc.Defs
public import Silmaril.Semantics.Function.Effects.Defs

@[expose] public section
namespace Silmaril.Elf.Region.Calls.Examples
open Silmaril.Semantics.Function
open Silmaril.Machine.Region (BinaryObject ByteSource)
open Silmaril.X86 (Byte MState)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.X86.Decompile (FunctionSpec)

def callBytes : List Byte := [0xe8, 1, 0, 0, 0]
def fixtureCode : List Byte := callBytes ++ [0xc3] ++ callBytes ++ [0xc3, 0xc3]

def objectOfCode (bytes : List Byte) : BinaryObject :=
  Silmaril.Elf.Region.object ⟨fun addr => bytes[addr]?.map UInt8.ofBitVec⟩
    [⟨1, 5, 0, 0, 0, bytes.length, bytes.length, 1⟩]

def fixture : BinaryObject := objectOfCode fixtureCode
def entry : FunctionSpec := ⟨"entry", 0, 6⟩
def worker : FunctionSpec := ⟨"worker", 6, 6⟩
def external : Stub := ⟨12, "example.export"⟩
def plan : Plan := ⟨[entry, worker], [external], []⟩
def inventory : Inventory := extract fixture plan

def entryCall : Edge signature := ⟨⟨0, 0, .invoke⟩, .direct, .localFn 6⟩
def workerCall : Edge signature := ⟨⟨6, 6, .invoke⟩, .direct, .foreign external⟩

def initial : MState where
  core := ⟨fun reg => if reg = .rsp then 48 else 0, 0, ⟨none, none, none, none, none, none⟩, 0⟩
  memory := ⟨[⟨0, fixtureCode.length, ⟨true, false, true⟩⟩, ⟨32, 16, ⟨true, true, false⟩⟩],
    Silmaril.Process.Memory.install ∅ 0 fixtureCode⟩

def afterCall (state : MState) (dest : BitVec 64) : MState :=
  let sp := state.core.read .rsp - 8#64
  let ret := state.core.rip + 5#64
  ⟨{ state.core.write .rsp sp with rip := dest },
    { state.memory with bytes := Silmaril.Process.Memory.install state.memory.bytes sp.toNat (encodeWords [ret]) }⟩

def afterEntry : MState := afterCall initial 6
def afterWorker : MState := afterCall afterEntry 12

def owner : Owner := fun _ caller pre => (caller = 0 ∧ pre = initial) ∨ (caller = 6 ∧ pre = afterEntry)
def refinedOwner : Owner := fun image caller pre => owner image caller pre ∧ pre.core.rip.toNat = caller

abbrev machine : Machine signature := extModel plan 60 owner
abbrev refinedMachine : Machine signature := extModel plan 64 refinedOwner

def entryEffects : Effects.OnEntry MState (Set (Node signature)) where
  Observation := Node signature
  occurs state dest := ∃ edge post, machine.callStep fixture edge state post ∧ edge.callee = dest
  observe dest := {dest}

abbrev SymbolicArgs := Nat × Option (BitVec 64)

/-- A caller and optional stack pointer, with no other restrictions on memory
beyond the chosen interpretation's owner predicate. -/
def argEffects : Effects.OnArgs SymbolicArgs (Set (Node signature)) :=
  entryEffects.abstractInput fun args state => owner fixture args.1 state ∧
    ∀ sp, args.2 = some sp → state.core.read .rsp = sp

def targetBound : Set (Node signature) :=
  {dest | ∃ edge, (analysis inventory).may edge ∧ edge.callee = dest}

def entryBoundary : Boundaries machine where
  view _ := ⟨⟨fun row => ⟨fun source dest => row = entry ∧ source = (0 : Nat) ∧ dest = (6 : Nat)⟩⟩,
    FunctionSpec.entry, fun row => {label | row.Covers label}, fun _ => {(6 : Nat)}⟩
  admit _ _ _ state := state = initial
  formed _ _ := True

def entryCandidates : Decomposition signature := fromRegionView
  (fun _ caller row label exits => caller = 0 ∧ row = entry ∧ label = (0 : Nat) ∧ (6 : Nat) ∈ exits)
  entryBoundary.view fixture

def indirectInventory : Inventory :=
  extract (objectOfCode [0xff, 0xd0, 0xc3]) ⟨[⟨"indirect", 0, 3⟩], [], []⟩

def ambiguousInventory : Inventory := extract fixture
  ⟨[entry, worker, {worker with name := "alias"}], [external], []⟩

def tailInventory (declared : Bool) : Inventory :=
  extract (objectOfCode [0xeb, 0x00, 0xc3])
    ⟨[⟨"tail", 0, 2⟩], [⟨2, "tail.export"⟩], if declared then [0] else []⟩

def unsupportedInventory : Inventory :=
  extract (objectOfCode [0xff, 0xd1, 0xc3]) ⟨[⟨"unsupported", 0, 3⟩], [], []⟩

def fallthroughInventory : Inventory :=
  extract (objectOfCode [0x90, 0xc3]) ⟨[⟨"fallthrough", 0, 1⟩], [], []⟩

def partitionCount : Option Nat :=
  match checkPartition fixture 0 fixtureCode.length ⟨[entry, worker, ⟨"stub", 12, 1⟩], [], [], []⟩ with
  | some (.ok result) => some result.partition.funcs.length
  | _ => none

open Silmaril.Elf.Staged.Pinned.HelloGcc in
noncomputable def helloInventory : Inventory :=
  extract (Silmaril.Elf.Region.object (ByteSource.ofKBytes K) [ph3])
    ⟨[⟨"main", s28_31.raw.value, s28_31.raw.size⟩], [⟨0x1050, "puts@GLIBC_2.2.5"⟩], []⟩

def arcLabels (rows : Inventory) : List (Nat × Nat) :=
  (directArcs rows).map fun (caller, dest) => (caller, nodeAddress dest)

def indirectBytes : List Byte := [0xff, 0xd0, 0xc3]
def mixedCode : List Byte := indirectBytes ++ callBytes ++ [0xc3, 0xc3] ++ indirectBytes
def mixedObject : BinaryObject := objectOfCode mixedCode
def mixedExternal : Stub := ⟨9, "mixed.export"⟩
def mixedPlan : Plan := ⟨[⟨"dispatch", 0, 3⟩, ⟨"worker", 3, 6⟩, ⟨"other", 10, 3⟩], [mixedExternal], []⟩
def mixedInventory : Inventory := extract mixedObject mixedPlan

def mixedTargets (site : CallSite signature) : Option (List (Node signature)) :=
  if site.caller = 0 then some [.localFn 3] else none

def widenedTargets (site : CallSite signature) : Option (List (Node signature)) :=
  if site.caller = 0 then some [.localFn 3, .localFn 10] else none

def mixedReport : GeneralReport := queryGeneral mixedInventory mixedTargets 0 3
def widenedReport : GeneralReport := queryGeneral mixedInventory widenedTargets 0 3

def mixedInitial : MState :=
  ⟨initial.core, ⟨[⟨0, mixedCode.length, ⟨true, false, true⟩⟩],
    Silmaril.Process.Memory.install ∅ 0 mixedCode⟩⟩

abbrev mixedMachine : Machine signature := extModel mixedPlan 60 (fun _ _ _ => True)

end Silmaril.Elf.Region.Calls.Examples
