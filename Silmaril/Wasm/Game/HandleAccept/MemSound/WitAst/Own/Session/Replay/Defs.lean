module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session.Audit.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session.Replay

open Silmaril.Formats Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.IOAccept
  Silmaril.Wasm.Numerics

abbrev Tree := AST ownSig.toAstSig

structure Writer where
  pending : Option Tree := none
  accepted : List Tree := []

/-- The four operands of the node call in `ownMod`. -/
def nodeArgs : List Val := [.i32 0, .i32 16, .i32 0, .i32 0]

/-- The node commit followed by the separate `accept` import, newest first. -/
def acceptedEntries : List Audit.Event :=
  [⟨1, [.i32 9], .values [], .other⟩, ⟨0, nodeArgs, .values [.i32 9], .committed⟩]

/-- The retry records its typed rejection without recording a new `accept`. -/
def rejectedEntries : List Audit.Event :=
  ⟨0, nodeArgs, .trap, .rejected (.resource (.dead 1))⟩ :: acceptedEntries

/-- A one-slot writer for the `ownMod` replay. An accepted tree must have been built at
`node`, then named by `accept`; merely returning a handle does not accept a tree. -/
def contract : Contract ownSig Writer where
  code := 0
  name := ("wit", "node")
  tagOf := ownTagOf
  mode := {}
  node before op children call reply after :=
    before.pending = none ∧ children = [] ∧ reply = ⟨call.store, .values [.i32 9]⟩ ∧
      after = { before with pending := some (resTree op.2.1) }
  other before call reply after :=
    call.target = 1 ∧ call.args = [.i32 9] ∧ reply = ⟨call.store, .values []⟩ ∧
      ∃ tree, before.pending = some tree ∧ after = ⟨none, tree :: before.accepted⟩

/-- Distinguish normal return from trap in this replay. The diagnostic itself is
retained at `Contract.attempt`, not encoded as a Core value. -/
def roles : Roles Unit Unit Unit Unit where
  result := fun _ _ => some ()

/-- Trees actually accepted by the checked `ownMod` host over all linked instances and
all export prefixes. A pending tree (only a `node` reply) is not an acceptance. -/
def language (P : Profile) (rt : RT) : Set Tree :=
  { tree | ∃ mt inst initial, IsSpecInstance ownMod mt inst initial ∧
      ∃ memory, contract.link ownMod inst initial 0 = .ok memory ∧
      ∃ phase pending current state tags,
        TSession P (contract.env memory) ownMod memory roles initial ⟨rt, {}⟩ inst.addrs
          phase pending (current, state) tags ∧ tree ∈ state.writer.accepted }

end Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session.Replay
