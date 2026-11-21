module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Trace

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Accept.IO

abbrev CommitTag := Tag Unit (BitVec 32) Unit Unit

/-- Only completed host replies can publish a node; reaching the redex is not a
commit and neither is a trap. Invocation brackets remain in the traced session. -/
def roles : IOAccept.Roles Unit (BitVec 32) Unit Unit where
  answerIn := fun _ reply => match reply.result with
    | .values [.num ⟨.int .i32, handle⟩] => some handle
    | _ => none

def commits (tags : List CommitTag) : List (BitVec 32) :=
  tags.filterMap fun | .inp handle => some handle | _ => none

def handles (initialCount newCount : Nat) : List (BitVec 32) :=
  (List.range newCount).map fun index => BitVec.ofNat 32 (initialCount + index + 1)

/-- A successful reply contributes one chronological handle and publishes one root.
The persistent state stores new trees newest first and keeps every old observation. -/
def RootHistory {Root : Type} (initial current : List Root) (tags : List CommitTag) : Prop :=
  ∃ added : List Root,
    current = added.reverse ++ initial ∧ commits tags = handles initial.length added.length

abbrev History {sig : Signature} (initial current : Endpoints.State sig) (tags : List CommitTag) : Prop :=
  RootHistory initial.accepted current.accepted tags

/-- The step contract for any publisher using the synchronous `accept-node` reply ABI. -/
def Publishes {Root : Type} (module_ : Module) (target : Nat) (reply : UReply)
    (prior next : List Root) : Prop :=
  (next = prior ∧ reply.result = .trap) ∨
    (∃ root, next = root :: prior ∧ module_.imports[target]?.isSome = true ∧
      reply.result = .values [.num ⟨.int .i32, BitVec.ofNat 32 (prior.length + 1)⟩])

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Trace
