module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.FlatStrings.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadRoot.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadEffects.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicFlatStrings

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.FlatStrings

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {schema : TypeOf}
  {profile : ProfileKind} {ready : HostReady (HostState sig)} {bindings : List (Binding sig)}

private theorem initialFrame (call : PayloadRoot.Site grow sig (.flat schema)) (next : call.ReferenceNext)
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

theorem parked (call : PayloadRoot.Site grow sig (.flat schema)) (linked : call.Linked bindings)
    (depth : Nat) (next : call.ReferenceNext) (shape : Shape depth call.field)
    {addr : Nat} (realloc : call.destination.realloc = some addr) :
    PayloadRoot.Cut call profile ready bindings (Body call depth next profile ready bindings) := by
  apply call.parked_after_fit linked
  intro admitted
  obtain ⟨plan, compiled⟩ := linked.compiled
  have fits : FlatNestedFits (StringField.Fits call.destination) depth call.field := by
    apply flat_nested_refine depth call.field shape
    intro leaf path leafShape
    obtain ⟨item, equal⟩ := leafShape
    rw [← equal] at path
    have checked := (call.destination.compiled_payload_descendant call.inst (sig.payload call.tag)
      call.payload .flat (plan := plan) compiled admitted path).2
    exact ⟨item, equal, by simpa only [StringField.field, Field.type, Field.value, Lower.fits, decide_eq_true_eq] using checked⟩
  unfold Body
  exact nested_flat_strings call.destination call.inst depth call.field
    (call.destination.check_width call.start.store linked.destination) realloc fits
    (fun path => call.destination.compiled_payload_sum_tag call.inst (sig.payload call.tag) call.payload .flat compiled admitted path)
    0 call.reply next call.checked (call.reference next) call.cursor call.cursor (initialFrame call next _)
    (Core3.Grows.refl _) rfl (call.reference_at linked next)
    _ (fun _ _ _ _ _ frame _ checked canonical => ⟨frame, checked, canonical⟩)

theorem parkedMixed (call : PayloadRoot.Site grow sig (.flat schema)) (linked : call.Linked bindings)
    (depth : Nat) (next : call.ReferenceNext) (shape : MixedShape depth call.field)
    {addr : Nat} (realloc : call.destination.realloc = some addr) :
    PayloadRoot.Cut call profile ready bindings (MixedBody call depth next profile ready bindings) := by
  apply call.parked_after_fit linked
  intro admitted
  obtain ⟨plan, compiled⟩ := linked.compiled
  have fits : FlatNestedFits (fun field => CanonicalHandle field ∨ StringField.Fits call.destination field) depth call.field := by
    apply flat_nested_refine depth call.field shape
    intro leaf path leafShape
    rcases leafShape with handle | ⟨item, equal⟩
    · exact .inl handle
    · rw [← equal] at path
      have checked := (call.destination.compiled_payload_descendant call.inst (sig.payload call.tag)
        call.payload .flat (plan := plan) compiled admitted path).2
      exact .inr ⟨item, equal, by simpa only [StringField.field, Field.type, Field.value, Lower.fits, decide_eq_true_eq] using checked⟩
  unfold MixedBody bodyUsing
  exact nested_flat_rule call.destination call.inst _ _
    (fun field fit => mixed_flat_rule call.destination call.inst field
      (call.destination.check_width call.start.store linked.destination) (fun _ => ⟨_, realloc⟩) fit) depth call.field fits
    (fun path => call.destination.compiled_payload_sum_tag call.inst (sig.payload call.tag) call.payload .flat compiled admitted path)
    0 call.reply next call.checked (call.reference next) call.cursor call.cursor (initialFrame call next _)
    (Core3.Grows.refl _) rfl (call.reference_at linked next)
    _ (fun _ _ _ _ _ frame _ checked canonical => ⟨frame, checked, canonical⟩)

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PublicFlatStrings
