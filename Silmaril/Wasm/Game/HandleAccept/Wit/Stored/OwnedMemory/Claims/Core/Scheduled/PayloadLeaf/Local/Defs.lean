module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadLeaf.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Step.Defs
public import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Defs

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

def localOccurrenceEnd {Result : Type} (result : Except TrapReason Result)
    (mark : Option ReturnFrame.Occurrence.Location) : Option ReturnFrame.Occurrence.Location :=
  match result, mark with
  | .error _, some (.active ..) => none
  | _, _ => mark

/-- Both peers execute the same local operation, with their own continuations
and hosts. Each reached store agrees; no body step changes either host. -/
inductive PairedLeafSteps {E : CoreEngine} {Host : Type} (profile : ProfileKind) (ready : HostReady Host)
    (dispatch reference : Call E → P E Host (Ret E)) :
    Config E Host → Config E Host → List (Label E Host) → Config E Host → Config E Host → Prop where
  | done {left right} (store : left.store = right.store) : PairedLeafSteps profile ready dispatch reference left right [] left right
  | step {left right middle peer after canonical label labels}
      (store : left.store = right.store)
      (checked : Step profile ready dispatch left label middle) (raw : Step profile ready reference right label peer)
      (checkHost : middle.host = left.host) (rawHost : peer.host = right.host)
      (checkedEdit : ReturnFrame.Occurrence.transitionEdit left label =
        (match label with | .trap _ => .clear | _ => .same))
      (sameEdit : ReturnFrame.Occurrence.transitionEdit right label = ReturnFrame.Occurrence.transitionEdit left label)
      (tail : PairedLeafSteps profile ready dispatch reference middle peer labels after canonical) :
      PairedLeafSteps profile ready dispatch reference left right (label :: labels) after canonical

/-- The compiled leaf at the checked focus and its successful live plan.
The field, output and continuation come from the executing program. -/
def CompiledLeafSource {sig : Stored.Signature} {grow : Silmaril.Wasm.SingleThreaded.GrowOracle}
    (state : Config (core3 grow) (HostState sig)) (plan : Option Spend) : Prop :=
  ∃ (destination : RecordDestination) (inst : InstId) (field : Field) (index : Nat) (output : Stored.Lower.Output)
    (next : Except Stored.Endpoints.RecordLower.Issue output.Result → Session grow sig (Ret (core3 grow))),
    ∃ thread frames rest,
    state.ctl = ⟨thread, .prog (Record.Effects.checkedLeaf recordClaims Component.Limits.spec Quirks.none
      (destination.context inst) destination.width field index output >>= next), frames⟩ :: rest ∧
    liveLeafPlan state.store state.host.writer index field = .ok plan

/-- The raw leaf remains pending during the checked guard, then both execute
the canonical body in lockstep with their unchanged continuations. -/
def GuardedLeafSteps {sig : Stored.Signature} {grow : Silmaril.Wasm.SingleThreaded.GrowOracle}
    (profile : ProfileKind) (ready : HostReady (HostState sig))
    (dispatch reference : Call (core3 grow) → Session grow sig (Ret (core3 grow)))
    (left right : Config (core3 grow) (HostState sig))
    (guard checked canonical : List (Label (core3 grow) (HostState sig)))
    (reached peer : Config (core3 grow) (HostState sig)) (spend : Option Spend) : Prop :=
  ∃ committed, CompiledLeafSource left spend ∧ LeafGuardSteps profile ready dispatch left guard committed spend ∧ checked = canonical ∧
    PairedLeafSteps profile ready dispatch reference committed right checked reached peer

/-- An exclusive checked guard spends its claim before the canonical leaf effects.
The projection on the peer's writer is only a proof view; the raw canonical
execution does not commit it, even on a common trap. -/
structure ExclusiveLeafWriterFlow {sig : Signature} (update : Spend)
    (left right checked canonical : HostState sig) : Prop where
  live : update.Live left.writer
  checkedHost : checked = { left with writer := update.apply left.writer }
  canonicalHost : canonical = right
  compare : left.writer.LiveClaimsAgree right.writer →
    checked.writer.LiveClaimsAgree (update.apply canonical.writer) ∧ ¬ checked.writer.LiveClaimsAgree canonical.writer

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
