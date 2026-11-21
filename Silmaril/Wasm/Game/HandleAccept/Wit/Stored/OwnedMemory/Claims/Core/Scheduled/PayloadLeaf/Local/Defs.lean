module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadLeaf.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Step.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine
open Stored.Endpoints.RecordLower (Field)

/-- The effects needed to lower a canonical handle. In particular neither
the canonical handle table operations nor the slot write calls the host. -/
def LocalStoreOp {E : CoreEngine} {Host : Type} : Op E Host → Prop
  | .get | .modify _ | .currentThread | .trap _ => True
  | _ => False

def CanonicalHandle : Field → Prop
  | .owner _ | .endpoint .. | .context _ => True
  | _ => False

/-- A canonical local handle emits no observations except a final trap. -/
def LocalLeafLabels {E : CoreEngine} {Host Result : Type} (outcome : Except TrapReason Result)
    (labels : List (Label E Host)) : Prop :=
  match outcome with
  | .ok _ => labels.all (· matches .tau) = true
  | .error reason => ∃ count, labels = List.replicate count .tau ++ [.trap reason]

/-- Keep the actual reached store even on a trap. Only a successful local
operation enters the sequence's next continuation. -/
def localLeafEnd {E : CoreEngine} {Host Result : Type} (start : Config E Host) (host : Host) (store : CStore E)
    (thread : Option ThreadId) (frames : List (Seg E Host)) (rest : List (Activation E Host))
    (finish : Result → P E Host (Ret E)) : Except TrapReason Result → Config E Host
  | .ok value => { start with store, host, ctl := ⟨thread, .prog (finish value), frames⟩ :: rest }
  | .error _ => StepDefs.trapCfg { start with store, host }

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
