module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveDispatch.Plan.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.PayloadPrefix.Thms
import Silmaril.Wasm.Component.Reference.Canon.Prog.Thms

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

theorem variantMember (destination : RecordDestination) (inst : InstId)
    {cases : List (String × Option Stored.TypeOf)} {tag : Nat} {type : Stored.TypeOf}
    (found : (cases.map Prod.snd)[tag]? = some (some type)) :
    (∃ name, (name, some type) ∈ cases) ∧
    liveFlatVariantPaths profile ready base bindings older destination inst start incoming offset sink cases tag =
      liveFlatPaths profile ready base bindings older destination inst start incoming offset sink type := by
  induction cases generalizing tag with
  | nil => simp at found
  | cons entry rest ih =>
    obtain ⟨name, arm⟩ := entry
    cases tag with
    | zero =>
      have selected : arm = some type := by simpa using found
      subst arm
      exact ⟨⟨name, by simp⟩, rfl⟩
    | succ index =>
      obtain ⟨⟨name, member⟩, equal⟩ := ih (tag := index) (by simpa using found)
      exact ⟨⟨name, List.mem_cons_of_mem _ member⟩, by rw [liveFlatVariantPaths, equal]⟩

private theorem sumTail (width : AddrType) (type : Stored.TypeOf) (count tag : Nat) (haves : List CoreType)
    (words : List FlatValue) (checkNext : FlatSequenceCheckNext grow sig) (canonNext : FlatSequenceCanonNext grow sig)
    (finish : FlatTrailFinish grow sig) {before : Trace grow sig} {left right : Config (core3 grow) (HostState sig)}
    {check canon : PayloadPrefix.Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core left.store.core)
    (trail : ComparedSlots profile ready base bindings start incoming before left right offset)
    (checkAt : left.ctl = check.control (flatSumTail width type count tag haves words >>= fun result => checkNext (.ok result)))
    (canonAt : right.ctl = canon.control (flatSumTail width type count tag haves words >>= canonNext))
    (ends : ∀ words seen lhs rhs cursor peer, ChildFrameOver older lhs rhs cursor peer →
      Core3.Grows origin.core lhs.store.core → ComparedSlots profile ready base bindings start incoming seen lhs rhs offset →
      lhs.ctl = cursor.control (checkNext (.ok words)) → rhs.ctl = peer.control (canonNext words) → finish words seen lhs rhs cursor peer) :
    LocalPathsThen profile ready base bindings start incoming before offset (flatWordVisit finish) := by
  obtain ⟨store, result, lhsTrace, rhsTrace, lhs, rhs, seen, status⟩ :=
    PayloadPrefix.variant_tail_frame_between (profile := profile) (ready := ready) (dispatch := specDispatch ready base)
      (reference := specDispatch ready (LiveDispatch.host bindings base)) count ((flatten width type).drop 1) tag haves words
      (keep := fun store => Core3.Grows origin.core store.core) left right (frame.store ▸ growth) frame.store check canon frame.thread
      checkNext canonNext (by simpa only [flatSumTail, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.pure_bind'] using! checkAt) canonAt
  cases result with
  | error reason =>
    obtain ⟨leading, trapped⟩ := status
    exact .inl ⟨reason, leading, _, _, CallbackPrefix.appendComparedPaths trail
      ⟨lhsTrace, rhsTrace, lhs, rhs.steps, seen.trans trapped, trapped, rfl⟩, rfl, rfl⟩
  | ok value =>
    obtain ⟨grown, lhsTrack, rhsTrack⟩ := status
    have reached := CallbackPrefix.appendComparedSlots trail ⟨lhsTrace, rhsTrace, lhsTrack, rhsTrack, rfl, seen.symm⟩
    exact .inr ⟨PayloadPrefix.visible lhsTrace, _, _, check, canon, reached, rfl, value,
      ends value _ _ _ _ _ ⟨rfl, frame.pending, frame.results, frame.cancels, frame.blocked, frame.thread, frame.frames, frame.rest⟩
        grown reached rfl rfl⟩

theorem sum (destination : RecordDestination) (inst : InstId) (type : Stored.TypeOf) (arms : List (Option Stored.TypeOf))
    (tag : Nat) (selected : Option Field) (valid : tag < arms.length) (pick : Nat → FlatFieldTrail grow sig)
    (derive : ∀ field, selected = some field → DerivesFlatFieldTrail profile ready base bindings older origin start incoming offset
      destination inst sink (pick tag) field) :
    DerivesFlatFieldTrail profile ready base bindings older origin start incoming offset destination inst sink
      (flatSumPaths profile ready base bindings start incoming offset destination.width type arms pick) (.sum type arms tag selected) := by
  intro index checkNext canonNext finish before left right check canon frame growth trail admitted checkAt canonAt ends
  refine ⟨tag, selected, rfl, ?_⟩
  cases selected with
  | none =>
    apply sumTail destination.width type arms.length tag [] [] checkNext canonNext finish frame growth trail _ _ ends
    · rw [checkAt]
      let body : Session grow sig (List FlatValue) := flatSumTail destination.width type arms.length tag [] []
      change check.control ((body.bind fun value => .pure (.ok value)).bind checkNext) = _
      rw [Prog.bind_assoc]
      rfl
    · exact canonAt
  | some child =>
    let haves := flatten destination.width child.type
    refine derive child rfl 0 (flatSumCheckNext destination.width type arms.length tag index haves checkNext)
      (fun words => flatSumTail destination.width type arms.length tag haves words >>= canonNext) _ before left right check canon
      frame growth trail (sink.nested _ admitted index) ?_ ?_ ?_
    · rw [checkAt]
      let body : Session grow sig (Except Stored.Endpoints.RecordLower.Issue (List FlatValue)) :=
        Stored.OwnedMemory.Claims.Record.Effects.field recordClaims Limits.spec Quirks.none (destination.context inst)
          destination.width child 0 .flat
      let tail := flatSumTail (grow := grow) (sig := sig) destination.width type arms.length tag haves
      change check.control ((body.bind fun verdict => match verdict with
        | .error issue => .pure (.error (.nested index issue))
        | .ok words => (tail words).bind fun value => .pure (.ok value)).bind checkNext) =
          check.control (body.bind (flatSumCheckNext destination.width type arms.length tag index haves checkNext))
      rw [Prog.bind_assoc]
      apply congrArg (fun next => check.control (body.bind next))
      funext verdict
      cases verdict with
      | error _ => rfl
      | ok words => rw [Prog.bind_assoc]; rfl
    · rw [canonAt]
      congr 1
      let body : Session grow sig (List FlatValue) := CanonicalTree.field Limits.spec Quirks.none
        (destination.context inst) destination.width child .flat
      change (lowerFlatVariantWith arms.length ((flatten destination.width type).drop 1) tag haves body).bind canonNext =
        body.bind fun words => (flatSumTail destination.width type arms.length tag haves words).bind canonNext
      simp only [flatSumTail, lowerFlatVariantWith, valid, ↓reduceIte, Prog.bind_eq, Prog.pure_eq, Prog.pure_bind']
      exact Prog.bind_assoc _ _ _
    · intro words seen lhs rhs cursor peer paired grew tracks checkAt canonAt
      exact sumTail destination.width type arms.length tag haves words checkNext canonNext finish paired grew tracks checkAt canonAt ends

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.FlatTrails
