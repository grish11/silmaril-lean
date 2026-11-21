module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence.Public.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadEffects.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadRoot.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicMemorySequence

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {pointer : FlatValue}
  {profile : ProfileKind} {ready : HostReady (HostState sig)} {bindings : List (Binding sig)}

private theorem refineShape {stringLeaf fits : Field → Prop} (depth : Nat) (field : Field)
    (shape : AggregateShape stringLeaf depth field)
    (reached : ∀ leaf, Field.Descendant field leaf → stringLeaf leaf → fits leaf) : AggregateShape fits depth field := by
  induction depth generalizing field with
  | zero =>
    cases shape with
    | handle handle => exact .handle handle
    | string leaf => exact .string (reached field (.self field) leaf)
  | succ depth ih =>
    cases shape with
    | handle handle => exact .handle handle
    | string leaf => exact .string (reached field (.self field) leaf)
    | aggregate children =>
      refine .aggregate fun child member => ih child (children child member) ?_
      exact fun leaf path string => reached leaf (.aggregate member path) string

private theorem placementFits (destination : RecordDestination) (store : CStore (core3 grow)) (field : Field) (address : Nat)
    (placed : placement destination store (layout destination.width field.type) address = .ok ()) :
    ∃ bytes, (core3 grow).memSize? store.core destination.memory = some bytes ∧ SlotFits destination.width bytes field address := by
  let area := layout destination.width field.type
  have aligned : address % area.alignment.bytes = 0 := by
    by_contra invalid
    simp [placement, area, invalid] at placed
    change Except.error TrapReason.unalignedPointer = .ok () at placed
    contradiction
  cases sized : (core3 grow).memSize? store.core destination.memory with
  | none => simp [placement, area, aligned, sized] at placed
  | some bytes =>
    refine ⟨bytes, rfl, aligned, ?_⟩
    change address + area.size ≤ bytes
    by_contra invalid
    simp [placement, area, aligned, sized, Nat.lt_of_not_ge invalid] at placed

private theorem initialFrame (call : PayloadRoot.Site grow sig (.memory pointer)) (next : call.ReferenceNext)
    (older : ReturnFrame.Substitutions (core3 grow) (HostState sig)) :
    ChildFrameOver older call.checked (call.reference next) call.cursor call.cursor := by
  have segments : ∀ frames, List.Forall₂ (ReturnFrame.Related.Segment older) frames frames :=
    fun _ => List.forall₂_same.mpr fun frame _ => .same frame
  have active : ∀ act, ReturnFrame.Related.Active older act act := fun ⟨_, _, frames⟩ => .mk (segments frames)
  have saved : ∀ act, ReturnFrame.Related.Saved older act act
    | none => .none
    | some act => .some (active act)
  exact ⟨rfl, rfl, rfl, rfl, List.forall₂_same.mpr fun act _ => saved act, rfl,
    segments call.cursor.frames, List.forall₂_same.mpr fun act _ => active act⟩

theorem parked (call : PayloadRoot.Site grow sig (.memory pointer)) (linked : call.Linked bindings)
    (depth : Nat) (next : call.ReferenceNext) (shape : ParkedShape depth call.field)
    {addr : Nat} (realloc : call.destination.realloc = some addr) :
    PayloadRoot.Cut call profile ready bindings (ParkedBody call depth next profile ready bindings) := by
  apply call.parked_after_placement linked
  intro admitted placed
  obtain ⟨plan, compiled⟩ := linked.compiled
  have matched := OwnedMemory.Claims.Record.preflightValue_layout _ _ _ _ _ _ compiled
  change placement call.destination call.start.store (layout call.destination.width (sig.payload call.tag)) (flatNat pointer) = .ok () at placed
  rw [← matched.type_eq] at placed
  obtain ⟨bytes, sized, slot⟩ := placementFits call.destination call.start.store call.field (flatNat pointer) placed
  have fits : AggregateShape (StringField.Fits call.destination) depth call.field := by
    apply refineShape depth call.field shape
    intro leaf path leafShape
    obtain ⟨item, equal⟩ := leafShape
    rw [← equal] at path
    have checked := (call.destination.compiled_payload_descendant call.inst (sig.payload call.tag)
      call.payload (.memory (flatNat pointer)) (plan := plan) compiled admitted path).2
    exact ⟨item, equal, by simpa only [StringField.field, Field.type, Field.value, Lower.fits, decide_eq_true_eq] using checked⟩
  unfold ParkedBody
  have layoutMatch : call.field.LayoutMatches call.field.type := matched.type_eq.symm ▸ matched
  exact nested_rule call.destination call.inst depth call.field (flatNat pointer)
    (call.destination.check_width call.start.store linked.destination) sized realloc fits layoutMatch slot
    0 call.reply next call.checked (call.reference next) call.cursor call.cursor (initialFrame call next _)
    (Core3.Grows.refl _) rfl (call.reference_at linked next) _ (fun _ _ _ _ frame _ checked canonical => ⟨frame, checked, canonical⟩)

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicMemorySequence
