module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Nested.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session

open Silmaril.Formats Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Game.IOAccept
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Accept.IO (Tag)

/-- The owning table is a separate part of the host state. A writer callback receives
resolved nodes, not guest table indices, and cannot overwrite this table. -/
structure State (Q : Type) where
  resources : RT
  writer : Q

/-- A checked node import identified by its Core host code. The writer can answer a
well-formed node with an i32, or decline it by trapping. Other imports in this contract
do not allocate or free resource slots. -/
structure Contract (S : WitSig) (Q : Type) where
  code : Nat
  name : String × String
  tagOf : BitVec 32 → Option S.Tag
  mode : NodeMode
  node : Q → Op S → List (BitVec 32) → UCall Nat → UReply → Q → Prop
  other : Q → UCall Nat → UReply → Q → Prop

variable {S : WitSig} {Q : Type}

/-- The diagnostic is computed using the state at this host call. The memory address is
resolved by the instance, not by an unchecked default when the memory is absent. -/
def Contract.attempt (K : Contract S Q) (memory : Option Nat) (rt : RT) (call : UCall Nat) :
    Except NodeIssue ((Op S × List (BitVec 32)) × RT) :=
  match memory with
  | some addr => checkedAt K.mode K.name addr call (Nested.checkedNode S K.tagOf K.mode rt)
  | none => do
    checkNodeMode K.mode
    throw .missingMemory

/-- Checked rejection is an actual Core answer, not a missing writer event. A successful
node reply commits the newly reserved slots once. Other imports, and a writer choosing
to trap on a well-formed node, cannot modify the owning table. -/
inductive Answer (K : Contract S Q) (memory : Option Nat) :
    State Q → UCall Nat → UReply → State Q → Prop where
  | reject {state : State Q} {call : UCall Nat} {issue : NodeIssue} :
      call.target = K.code → K.attempt memory state.resources call = .error issue →
      Answer K memory state call ⟨call.store, .trap⟩ state
  | decline {state : State Q} {call : UCall Nat} {op : Op S} {children : List (BitVec 32)}
      {updated : RT} :
      call.target = K.code → K.attempt memory state.resources call = .ok ((op, children), updated) →
      K.node state.writer op children call ⟨call.store, .trap⟩ state.writer →
      Answer K memory state call ⟨call.store, .trap⟩ state
  | returnHandle {state : State Q} {call : UCall Nat} {op : Op S} {children : List (BitVec 32)}
      {updated : RT} {handle : BitVec 32} {store : Store Nat} {writer : Q} :
      call.target = K.code → K.attempt memory state.resources call = .ok ((op, children), updated) →
      KeepsCode call.store store → K.node state.writer op children call ⟨store, .values [.i32 handle]⟩ writer →
      Answer K memory state call ⟨store, .values [.i32 handle]⟩ ⟨updated, writer⟩
  | other {state : State Q} {call : UCall Nat} {reply : UReply} {writer : Q} :
      call.target ≠ K.code → K.other state.writer call reply writer →
      Answer K memory state call reply ⟨state.resources, writer⟩

/-- A stateful Core host. The traced session keeps this state across all exports, even
when a node import traps. No extra divergence rule hides a rejected import. -/
def Contract.env (K : Contract S Q) (memory : Option Nat) : SEnv UImp :=
  ⟨State Q, Answer K memory, fun _ _ => False⟩

/-- A linking failure is distinct from a rejection at a running host call. -/
inductive LinkIssue where
  | wrongImport (code : Nat) (expected : String × String)
  | duplicateImport (name : String × String)
  | wrongType (code : Nat) (expected : FnType)
  deriving DecidableEq, Repr

/-- The Core node ABI uses an i32 tag and handle, even when its addresses are i64. -/
def Contract.importType (K : Contract S Q) : FnType :=
  let tag : ScalarType := .num (.int .i32)
  let word : ScalarType := match K.mode.address with
    | .i32 => tag
    | .i64 => .num (.int .i64)
  ⟨[tag, word, word, word], [tag]⟩

/-- Resolve the selected memory in the actual instance. An absent memory remains absent,
so that reached node calls report `missingMemory`, never read from a default address. -/
def Contract.link (K : Contract S Q) (m : Module) (instanceInfo : ScalarInstance)
    (initial : Config Nat) (memoryIndex : Nat) : Except LinkIssue (Option Nat) := do
  let actualName := m.imports[K.code]?.map fun i => (i.moduleName, i.name)
  if actualName ≠ some K.name then throw (.wrongImport K.code K.name)
  if (m.imports.filter fun i => (i.moduleName, i.name) == K.name).length ≠ 1 then
    throw (.duplicateImport K.name)
  if instanceInfo.imports[K.code]? ≠ some K.importType then throw (.wrongType K.code K.importType)
  return initial.frame.module.mems[memoryIndex]?

/-- Session traces of the checked host, over all spec instantiations and permitted
export sequences. The host cannot be replaced by an arbitrary reply environment. Roles
are observations only; this does not identify them with a writer's accepted trees. -/
def Contract.traces {Entry Input Output Exit : Type} (K : Contract S Q) (P : Profile)
    (m : Module) (memoryIndex : Nat) (state : State Q) (roles : Roles Entry Input Output Exit) :
    Set (List (Tag Entry Input Output Exit)) :=
  { tags | ∃ moduleType instanceInfo initial, IsSpecInstance m moduleType instanceInfo initial ∧
    ∃ memory, K.link m instanceInfo initial memoryIndex = .ok memory ∧
    ∃ phase pending current,
      TSession P (K.env memory) m memory roles initial state instanceInfo.addrs phase pending current tags }

end Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session
