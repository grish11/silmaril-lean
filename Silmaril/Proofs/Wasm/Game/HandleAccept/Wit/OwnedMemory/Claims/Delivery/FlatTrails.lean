module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveDispatch.Plan.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FlatTrails

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Game.HandleAccept.Wit
open Stored (Signature)
open Stored.Endpoints.RecordLower
open Stored.OwnedMemory.Claims.Core Stored.OwnedMemory.Claims.Core.Scheduled
open LinkedCallback LiveDispatch ComponentCall.Delivery.FiniteSession

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind} {ready : HostReady (HostState sig)}
  {base : HostImpl (core3 grow) (HostState sig)} {bindings : List (Binding sig)}
  {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)}
  {start incoming : Config (core3 grow) (HostState sig)} {offset : Nat} {sink : RefusalSink grow sig}

theorem sequence (destination : RecordDestination) (inst : InstId) (items : List Field)
    (child : FlatFieldTrail grow sig) (checkNext : FlatSequenceCheckNext grow sig) (canonNext : FlatSequenceCanonNext grow sig)
    (finish : FlatTrailFinish grow sig) (index : Nat) (leading : List FlatValue)
    {before : Trace grow sig} {left right : Config (core3 grow) (HostState sig)}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (rules : ∀ item ∈ items, DerivesFlatFieldTrail profile ready base bindings older origin start incoming offset
      destination inst sink child item)
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (frame : ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core left.store.core)
    (trail : ComparedSlots profile ready base bindings start incoming before left right offset)
    (checkAt : left.ctl = check.control (flatSequenceChecked destination inst items index leading checkNext))
    (canonAt : right.ctl = canon.control (flatSequenceCanonical destination inst items leading canonNext))
    (ends : ∀ words seen lhs rhs cursor peer, ChildFrameOver older lhs rhs cursor peer →
      Core3.Grows origin.core lhs.store.core → ComparedSlots profile ready base bindings start incoming seen lhs rhs offset →
      lhs.ctl = cursor.control (checkNext (.ok words)) → rhs.ctl = peer.control (canonNext words) → finish words seen lhs rhs cursor peer) :
    flatSequencePaths destination inst child checkNext canonNext finish items index leading before left right check canon := by
  induction items generalizing index leading before left right check canon with
  | nil =>
    apply ends leading before left right check canon frame growth trail
    · simpa [flatSequenceChecked, Stored.OwnedMemory.Claims.Record.Effects.flat, Prog.bind_eq, Prog.pure_eq, Except.map] using checkAt
    · simpa [flatSequenceCanonical, CanonicalTree.flat, Prog.bind_eq, Prog.pure_eq] using canonAt
  | cons item rest ih =>
    rw [flatSequencePaths]
    refine rules item (List.mem_cons_self ..) index _ _ _ before left right check canon frame growth trail ?_ ?_ ?_ ?_
    · exact admitted
    · exact checkAt.trans (congrArg check.control (flat_sequence_checked_cons destination inst item rest index leading checkNext))
    · exact canonAt.trans (congrArg canon.control (flat_sequence_canonical_cons destination inst item rest leading canonNext))
    · intro words seen lhs rhs cursor peer paired grown trails checked canonical
      exact ih (index + 1) (leading ++ (show List FlatValue from words)) (fun later member => rules later (List.mem_cons_of_mem _ member))
        paired grown trails checked canonical

theorem aggregate (destination : RecordDestination) (inst : InstId) (items : List Field) (index : Nat)
    (child : FlatFieldTrail grow sig) (checkNext : FlatSequenceCheckNext grow sig) (canonNext : FlatSequenceCanonNext grow sig)
    (finish : FlatTrailFinish grow sig) {before : Trace grow sig} {left right : Config (core3 grow) (HostState sig)}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (rules : ∀ item ∈ items, DerivesFlatFieldTrail profile ready base bindings older origin start incoming offset
      destination inst sink child item)
    (admitted : sink.admits (fun issue => checkNext (.error issue)))
    (frame : ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core left.store.core)
    (trail : ComparedSlots profile ready base bindings start incoming before left right offset)
    (checkAt : left.ctl = check.control (do
      let verdict ← Stored.OwnedMemory.Claims.Record.Effects.flat recordClaims Limits.spec Quirks.none
        (destination.context inst) destination.width items 0
      checkNext (verdict.mapError (.nested index))))
    (canonAt : right.ctl = canon.control (CanonicalTree.flat Limits.spec Quirks.none (destination.context inst)
      destination.width items >>= canonNext))
    (ends : ∀ words seen lhs rhs cursor peer, ChildFrameOver older lhs rhs cursor peer →
      Core3.Grows origin.core lhs.store.core → ComparedSlots profile ready base bindings start incoming seen lhs rhs offset →
      lhs.ctl = cursor.control (checkNext (.ok words)) → rhs.ctl = peer.control (canonNext words) → finish words seen lhs rhs cursor peer) :
    flatSequencePaths destination inst child (fun verdict => checkNext (verdict.mapError (.nested index)))
      canonNext finish items 0 [] before left right check canon := by
  have noLeading (verdict : Except Stored.Endpoints.RecordLower.Issue (List FlatValue)) : verdict.map ([] ++ ·) = verdict := by
    cases verdict <;> rfl
  exact sequence destination inst items child (fun verdict => checkNext (verdict.mapError (.nested index))) canonNext
    finish 0 [] rules (sink.nested _ admitted index) frame growth trail
    (by simpa only [flatSequenceChecked, noLeading] using checkAt) (by simpa [flatSequenceCanonical] using canonAt) ends

theorem recordMember (destination : RecordDestination) (inst : InstId) (fields : List (String × Stored.TypeOf))
    {name : String} {type : Stored.TypeOf} (member : (name, type) ∈ fields) :
    (type, liveFlatPaths profile ready base bindings older destination inst start incoming offset sink type) ∈
      liveFlatRecordPaths profile ready base bindings older destination inst start incoming offset sink fields := by
  induction fields with
  | nil => simp at member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with equal | later
    · subst first
      exact List.mem_cons_self ..
    · obtain ⟨label, schema⟩ := first
      exact List.mem_cons_of_mem _ (ih later)

theorem tupleMember (destination : RecordDestination) (inst : InstId) (types : List Stored.TypeOf)
    {type : Stored.TypeOf} (member : type ∈ types) :
    (type, liveFlatPaths profile ready base bindings older destination inst start incoming offset sink type) ∈
      liveFlatTuplePaths profile ready base bindings older destination inst start incoming offset sink types := by
  induction types with
  | nil => simp at member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | later
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih later)

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FlatTrails
