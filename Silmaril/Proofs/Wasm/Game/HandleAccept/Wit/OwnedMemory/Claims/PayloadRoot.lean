module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadRoot.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadEffects.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadRoot

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadRoot

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {route : GiveEffectRoute}
  {profile : ProfileKind} {ready : HostReady (HostState sig)} {bindings : List (Binding sig)}

private theorem appendSteps {first middle finish : Config (core3 grow) (HostState sig)} {front back}
    (lhs : Steps profile ready (specDispatch ready (host bindings)) first front middle)
    (rhs : Steps profile ready (specDispatch ready (host bindings)) middle back finish) :
    Steps profile ready (specDispatch ready (host bindings)) first (front ++ back) finish := by
  induction lhs with
  | refl => exact rhs
  | cons step _ next => exact .cons step (next rhs)

private theorem visibleAppend {E : CoreEngine} {Host : Type} (front back : List (Label E Host)) :
    visible (front ++ back) = visible front ++ visible back := List.filter_append ..

theorem parkedAfterPlacement (site : Site grow sig route) (linked : site.Linked bindings) (body : Prop)
    (afterFit : Lower.fits Quirks.none site.destination.encoding site.destination.width (sig.payload site.tag)
      site.payload.val.value = true →
      rootPlacement site.destination site.start.store (sig.payload site.tag) route.output = .ok () → body) :
    Cut site profile ready bindings body := by
  let dispatch := specDispatch ready (host (grow := grow) bindings)
  obtain ⟨plan, compiled⟩ := linked.compiled
  obtain ⟨front, allTau, entry⟩ := route.parked bindings site.name site.functionType site.handle site.inst site.destination
    site.tree site.start site.thread profile ready linked.parked linked.calling linked.linked linked.caller linked.mayLeave
    linked.destination linked.selected linked.admitted
  have onlyTau : ∀ label ∈ front, label = .tau := by
    intro label member
    have test := List.all_eq_true.mp allTau label member
    cases label <;> simp_all
  have replicated : front = List.replicate front.length .tau := List.eq_replicate_length.mpr onlyTau
  have silent : visible front = [] := by
    unfold visible
    apply List.filter_eq_nil_iff.mpr
    intro label member
    rw [onlyTau label member]
    simp
  let entered := site.withBody (route.run site.destination site.inst site.tree site.start.host.nextTicket)
  have entryRun : Steps profile ready dispatch site.start front entered := entry
  obtain ⟨_, _, _, started⟩ := site.destination.compiled_payload_effects (profile := profile) (ready := ready)
    (dispatch := dispatch) entered site.inst site.tag site.payload route.output site.field plan site.reply compiled
    linked.destination rfl
  cases prepared : Record.prepare entered.store entered.host.writer site.field.objects with
  | error issue =>
    rw [prepared] at started
    exact .refused issue (by rw [visibleAppend, silent]; rfl) (appendSteps entryRun started)
  | ok accepted =>
    cases accepted
    rw [prepared] at started
    cases fits : Lower.fits Quirks.none site.destination.encoding site.destination.width (sig.payload site.tag)
        site.payload.val.value with
    | false =>
      simp only [fits, Bool.not_false, ↓reduceIte] at started
      exact .refused (.preflight (.abi .allocationPrecondition))
        (by rw [visibleAppend, silent]; rfl) (appendSteps entryRun started)
    | true =>
      simp only [fits, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at started
      let root := site.withBody (Record.Effects.root recordClaims Limits.spec Quirks.none
        (site.destination.context site.inst) site.destination.width (sig.payload site.tag) site.field route.output >>= site.reply)
      have rootRun : Steps profile ready dispatch site.start (front ++ [.tau, .tau, .tau]) root := appendSteps entryRun started
      have placement := root_placement_steps (profile := profile) (ready := ready) (dispatch := dispatch)
        site.destination site.inst (sig.payload site.tag) site.field route.output root site.cursor site.reply rfl
      change (match rootPlacement site.destination site.start.store (sig.payload site.tag) route.output with
        | .ok () => ∃ labels, visible labels = [] ∧ Steps profile ready dispatch root labels site.checked
        | .error reason => ∃ count, Steps profile ready dispatch root (List.replicate count .tau ++ [.trap reason])
            (StepDefs.trapCfg site.checked)) at placement
      cases placed : rootPlacement site.destination site.start.store (sig.payload site.tag) route.output with
      | error reason =>
        rw [placed] at placement
        obtain ⟨count, halted⟩ := placement
        refine .placementTrap reason (front.length + 3 + count) placed ?_
        rw [List.replicate_add, List.replicate_add, ← replicated, List.append_assoc]
        exact appendSteps rootRun halted
      | ok _ =>
        rw [placed] at placement
        obtain ⟨labels, placementSilent, placedRun⟩ := placement
        refine .placed ?_ placed prepared (appendSteps rootRun placedRun) (afterFit fits placed)
        rw [visibleAppend, visibleAppend, silent, placementSilent]
        rfl

theorem parkedAfterFit (site : Site grow sig route) (linked : site.Linked bindings) (body : Prop)
    (afterFit : Lower.fits Quirks.none site.destination.encoding site.destination.width (sig.payload site.tag)
      site.payload.val.value = true → body) : Cut site profile ready bindings body :=
  parkedAfterPlacement site linked body (fun fits _ => afterFit fits)

theorem parked (site : Site grow sig route) (linked : site.Linked bindings) : Cut site profile ready bindings :=
  parkedAfterFit site linked True (fun _ => trivial)

theorem referenceAt (site : Site grow sig route) (bindings : List (Binding sig)) (linked : site.Linked bindings)
    (next : site.ReferenceNext) :
    (site.reference next).ctl = site.cursor.control
      (CanonicalTree.field Limits.spec Quirks.none (site.destination.context site.inst) site.destination.width
        site.field route.output >>= next) := by
  obtain ⟨plan, compiled⟩ := linked.compiled
  rw [site.destination.compiled_payload_reference site.inst _ site.payload _ _ _ compiled]
  rfl

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PayloadRoot
