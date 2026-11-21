module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Defs
public import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Defs
import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.StoreInv.Thms
import Silmaril.Wasm.Component.Reference.Canon.Handles.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicEmitterGrowth

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game.HandleAccept.Wit
open Stored (Signature TypeOf)
open Stored.Endpoints
open Stored.OwnedMemory.Claims (commitOwner)
open Stored.OwnedMemory.Claims.Core.Scheduled

variable {grow : SingleThreaded.GrowOracle} {sig : Signature}

private def GrowsFrom (base : (core3 grow).Store (CanonHost (core3 grow))) (store : CStore (core3 grow)) : Prop :=
  Core3.Grows base store.core

private theorem store_pres (base : (core3 grow).Store (CanonHost (core3 grow))) : P.Inv.StorePres (GrowsFrom base) :=
  ⟨fun mem ptr bytes store valid => valid.trans (writeMemSt_grows store mem ptr bytes),
    fun _ _ valid => valid, fun _ _ _ valid => valid, fun _ _ valid => valid,
    fun _ _ _ valid => valid, fun _ _ _ valid => valid⟩

private theorem transfer_inv (base : (core3 grow).Store (CanonHost (core3 grow)))
    (cx : LiftLowerContext (core3 grow)) (index : Nat) (object : RecordLower.Object) :
    P.Inv (GrowsFrom base)
      ((Stored.OwnedMemory.Claims.Record.authority (recordClaims (sig := sig)) Limits.spec cx).transfer index object) := by
  refine P.Inv.bind (P.Inv.bind P.Inv.hostGet fun _ => P.Inv.pure _) fun state => ?_
  cases object with
  | owner receipt =>
    dsimp only
    split
    · exact P.Inv.pure _
    · refine P.Inv.bind ?_ fun _ => P.Inv.pure _
      unfold commitOwner
      exact P.Inv.bind (P.Inv.bind P.Inv.hostGet fun _ => P.Inv.hostSet _ trivial) fun _ =>
        P.Inv.lowerOwn (store_pres base).allocRes (store_pres base).addHandle _ _ _ _
  | shared object =>
    cases object with
    | endpoint channel element id =>
      refine P.Inv.bind P.Inv.getStore fun _ => ?_
      split
      · exact P.Inv.pure _
      · exact P.Inv.bind (P.Inv.bind P.Inv.hostGet fun _ => P.Inv.hostSet _ trivial) fun _ =>
          P.Inv.bind (P.Inv.lowerAsyncValue (store_pres base).addHandle (store_pres base).setEndOwner
            (store_pres base).setEndIndex _ _ _ _) fun _ => P.Inv.pure _
    | errorContext id =>
      refine P.Inv.bind P.Inv.getStore fun _ => ?_
      split
      · exact P.Inv.pure _
      · exact P.Inv.bind (P.Inv.lowerErrorContext (store_pres base).addHandle _ _ _) fun _ => P.Inv.pure _

private theorem payload_inv (base : (core3 grow).Store (CanonHost (core3 grow)))
    (cx : LiftLowerContext (core3 grow)) (tree : Stored.OwnedMemory.Tree sig) (output : Stored.Lower.Output) :
    P.Inv (GrowsFrom base) (Stored.OwnedMemory.Claims.Record.lowerPayloadRoot recordClaims
      Limits.spec Quirks.none cx tree output) := by
  cases tree with
  | atom impossible => exact impossible.elim
  | tag label children arity =>
    exact RecordLower.compiledValue_inv _ _ _ _ (store_pres base)
      (fun _ => P.Inv.bind P.Inv.getStore fun _ => P.Inv.bind P.Inv.hostGet fun _ => P.Inv.pure _)
      (transfer_inv base cx) _ _ _ _

theorem give_payload (inst : InstId) (destination : RecordDestination) (args : List FlatValue) :
    CoreGrowing (givePayload (grow := grow) (sig := sig) inst destination args) := by
  intro base
  unfold givePayload giveToMemory
  refine P.Inv.bind ?_ (fun selected => ?_)
  · unfold selectMemoryDestination
    split
    · split
      · exact P.Inv.pure _
      · refine P.Inv.bind P.Inv.getStore fun _ => ?_
        split
        · exact P.Inv.pure _
        · refine P.Inv.bind (P.Inv.bind P.Inv.hostGet fun _ => P.Inv.pure _) fun selected => ?_
          cases selected <;> exact P.Inv.pure _
    · exact P.Inv.pure _
  · cases selected with
    | error => exact P.Inv.pure _
    | ok treePtr => exact P.Inv.bind (payload_inv base _ treePtr.1 (.memory treePtr.2)) fun _ => P.Inv.pure _

theorem give_flat (inst : InstId) (destination : RecordDestination) (payload : TypeOf) (args : List FlatValue) :
    CoreGrowing (giveFlat (grow := grow) (sig := sig) inst destination payload args) := by
  intro base
  unfold giveFlat
  refine P.Inv.bind P.Inv.currentInst? fun current => P.Inv.bind P.Inv.getStore fun store => ?_
  split
  · exact P.Inv.pure _
  · refine P.Inv.bind ?_ (fun selected => ?_)
    · unfold selectFlatDestination
      split
      · refine P.Inv.bind P.Inv.getStore fun _ => ?_
        split
        · exact P.Inv.pure _
        · refine P.Inv.bind (P.Inv.bind P.Inv.hostGet fun _ => P.Inv.pure _) fun selected => ?_
          cases selected with
          | none => exact P.Inv.pure _
          | some tree =>
            change P.Inv _ (if (!rootHasSchema tree payload) = true then pure (Except.error Issue.wrongPayloadType) else _)
            split <;> exact P.Inv.pure _
      · exact P.Inv.pure _
    · cases selected with
      | error => exact P.Inv.pure _
      | ok tree => exact P.Inv.bind (payload_inv base _ tree .flat) fun _ => P.Inv.pure _

private theorem completion_inv (base : (core3 grow).Store (CanonHost (core3 grow)))
    (reply : Event × List FlatValue) : P.Inv (GrowsFrom base)
      (writeCompletion (grow := grow) (sig := sig) reply) :=
  P.Inv.bind P.Inv.hostGet fun _ => P.Inv.bind (P.Inv.hostSet _ trivial) fun _ => P.Inv.pure _

theorem dispatch_give (bindings : List (Binding sig)) (name : String) (type : V1.FuncType) (args : List FlatValue)
    (inst : InstId) (destination : RecordDestination) (schema : Option TypeOf)
    (linked : resolveBinding bindings name type = .ok ⟨name, inst,
      schema.elim (.givePayload destination) (.giveFlat destination)⟩) :
    CoreGrowing ((host (grow := grow) bindings).embedder name type args) := by
  intro base
  change P.Inv _ (dispatchImport bindings name type args)
  unfold dispatchImport
  refine P.Inv.bind P.Inv.hostGet fun _ => P.Inv.bind (P.Inv.hostSet _ trivial) fun _ => ?_
  unfold route
  rw [linked]
  cases schema with
  | some payload => exact P.Inv.bind (give_flat inst destination payload args base) fun _ => completion_inv base _
  | none =>
    refine P.Inv.bind ?_ fun _ => completion_inv base _
    unfold Stored.OwnedMemory.Claims.Core.Scheduled.invoke
    refine P.Inv.bind P.Inv.currentInst? fun _ => P.Inv.bind P.Inv.getStore fun _ => ?_
    dsimp only
    split
    · exact P.Inv.pure _
    · exact give_payload inst destination args base

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicEmitterGrowth
