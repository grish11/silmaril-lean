module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Transcript.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Transcript

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Transcript

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Game.IOAccept Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Component.Engine
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core (Contract)

variable {sig : Signature} {grow : SingleThreaded.GrowOracle} {contract : Contract sig}
  {memory : Option Nat}

theorem answer_effect {prior next : World grow sig} {call : UCall Nat} {reply : UReply}
    (answered : answer contract memory prior call reply next) :
    ∃ result, Effect contract memory prior next ⟨call, reply, result⟩ :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Transcript.answer_effect answered

/-- Every finite checked Core session has a typed transcript of its completed answers.
This includes rejection, traps after canonical effects, and subsequent invocations;
the observed answers match the transcript, in order, including traps. -/
theorem transcript_of_session {initial : World grow sig} {profile : Numerics.Profile} {module_ : Module}
    {start : Config Nat} {addrs : List Nat} {phase : Phase} {pending : Bool}
    {current : Config Nat × World grow sig} {tags : List Tag}
    (session : TSession profile (env contract grow memory) module_ memory roles start initial addrs
      phase pending current tags) :
    ∃ events, Timeline contract memory initial events current.2 ∧ visible module_ events = replies tags :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Transcript.transcript_of_session session

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Transcript
