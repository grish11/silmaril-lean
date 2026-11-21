module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveDispatch.Plan.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveDispatch.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Correspondence.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.Thms
import Silmaril.Wasm.Component.Reference.Machine.CoreGrowth.Thms
import Silmaril.Wasm.Component.Reference.Machine.HostFrame.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Game.HandleAccept.Wit
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open LiveDispatch ComponentCall.Delivery.FiniteSession

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind} {ready : HostReady (HostState sig)}
  {bindings : List (Binding sig)} {base : HostImpl (core3 grow) (HostState sig)}
  {start finish incoming : Config (core3 grow) (HostState sig)} {labels : Trace grow sig}
  {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}

private theorem append {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    {before middle after : Config (core3 grow) (HostState sig)} {leading trailing}
    (front : Steps profile ready dispatch before leading middle) (back : Steps profile ready dispatch middle trailing after) :
    Steps profile ready dispatch before (leading ++ trailing) after := by
  induction front with
  | refl => exact back
  | cons step _ ih => exact .cons step (ih back)

private theorem silentVisible {trace : Trace grow sig} (silent : trace.all (· matches .tau) = true) :
    PayloadPrefix.visible trace = [] := by
  induction trace with
  | nil => rfl
  | cons label trace ih =>
    have main := List.all_eq_true.mp silent label List.mem_cons_self
    cases label <;> try contradiction
    apply ih
    exact List.all_eq_true.mpr fun next member => List.all_eq_true.mp silent next (List.mem_cons_of_mem _ member)

private theorem entryVisible {route : GiveEffectRoute}
    (entry : Transition profile ready base start (.give route .entered) labels finish) : PayloadPrefix.visible labels = [] := by
  cases entry with
  | giveEntry _ _ silent _ _ _ => exact silent
  | giveStopped _ _ _ _ _ _ stopped => cases stopped

theorem source (plan : NestedPlan bindings profile ready base start labels finish) :
    Steps profile ready (specDispatch ready base) start labels finish := by
  induction plan with
  | segment path => exact path.steps
  | sequence _ _ front back => exact append front back
  | give _ _ entry checkedBody _ _ replies _ _ => exact append (append entry.steps checkedBody) (replies.1 _)
  | stop _ _ entry checkedBody _ _ _ _ _ => exact append entry.steps checkedBody

theorem runs (plan : NestedPlan bindings profile ready base start labels finish)
    (paired : HostFrame.Related.Paired older start incoming) :
    ∃ trace reached, Steps profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming trace reached ∧
      ((PayloadPrefix.visible labels = PayloadPrefix.visible trace ∧ HostFrame.Related.Paired older finish reached) ∨
        NestedCut bindings profile ready base older reached) := by
  classical
  induction plan generalizing incoming with
  | segment path =>
    cases LiveDispatch.paired_replay (bindings := bindings) paired path with
    | complete replay aligned => exact ⟨_, _, replay, .inl ⟨rfl, aligned⟩⟩
    | request _ _ replay aligned install _ => exact ⟨_, _, replay, .inr (.request aligned install)⟩
    | boundary _ _ replay aligned cut lhs rhs _ =>
      exact ⟨_, _, append replay (.cons rhs (.refl _)), .inr (.boundary aligned cut lhs rhs)⟩
  | sequence _ _ replayFront replayBack =>
    obtain ⟨_, _, front, ⟨seenFront, aligned⟩ | cut⟩ := replayFront paired
    · obtain ⟨_, _, back, ⟨seenBack, final⟩ | cut⟩ := replayBack aligned
      · refine ⟨_, _, append front back, .inl ⟨?_, final⟩⟩
        simp only [PayloadPrefix.visible, List.filter_append] at seenFront seenBack ⊢
        rw [seenFront, seenBack]
      · exact ⟨_, _, append front back, .inr cut⟩
    · exact ⟨_, _, front, .inr cut⟩
  | @give _ site linked _ _ _ _ _ checked baseline entry _ _ _ replies seen replayBody =>
    by_cases selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree
    · obtain ⟨_, _, silent, install, aligned⟩ := LiveDispatch.entry_paired (base := base) site linked paired selected
      obtain ⟨_, reached, body, ⟨bodySeen, rejoined⟩ | cut⟩ := replayBody aligned
      · have same := congrArg (fun state => HostFrame.replace state reached.host) replies.scheduler_rejoin
        change HostFrame.replace baseline reached.host = HostFrame.replace checked reached.host at same
        have baselinePair : ReturnFrame.Related.Paired older (HostFrame.replace baseline reached.host) reached := rejoined
        have caller : HostFrame.Related.Paired older checked reached :=
          show ReturnFrame.Related.Paired older (HostFrame.replace checked reached.host) reached from same ▸ baselinePair
        refine ⟨_, reached, append install body, .inl ⟨?_, caller⟩⟩
        have checkedSilent := entryVisible entry
        have installedSilent := silentVisible silent
        simp only [PayloadPrefix.visible] at seen checkedSilent installedSilent
        simp [PayloadPrefix.visible, List.filter_append] at bodySeen ⊢
        rw [checkedSilent, installedSilent, List.nil_append, List.nil_append, seen, bodySeen]
      · exact ⟨_, _, append install body, .inr cut⟩
    · exact ⟨[], _, .refl _, .inr (.unselected site linked paired selected)⟩
  | stop site linked _ checkedBody _ stopped store seen replayBody =>
    by_cases selected : Stored.Endpoints.Core.childFromHistory incoming.host.writer.accepted site.handle = some site.tree
    · obtain ⟨_, _, _, install, aligned⟩ := LiveDispatch.entry_paired (base := base) site linked paired selected
      obtain ⟨_, _, body, ⟨bodySeen, reached⟩ | cut⟩ := replayBody aligned
      · exact ⟨_, _, append install body,
          .inr (.stopped site stopped checkedBody body reached (store.trans reached.data.1) (seen.trans bodySeen))⟩
      · exact ⟨_, _, append install body, .inr cut⟩
    · exact ⟨[], _, .refl _, .inr (.unselected site linked paired selected)⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.NestedPlan
