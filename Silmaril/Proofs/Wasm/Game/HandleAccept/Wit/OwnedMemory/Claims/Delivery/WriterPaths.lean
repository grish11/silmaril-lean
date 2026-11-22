module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveDispatch.Plan.Defs
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.WriterPaths

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Game.HandleAccept.Wit
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open LiveDispatch ComponentCall.Delivery.FiniteSession

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
variable {ready : HostReady (HostState sig)} {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
variable {start middle finish incoming peer target left right : Config (core3 grow) (HostState sig)}
variable {labels leading trailing checked canonical canonLeading canonTrailing actual : Trace grow sig}
variable {before after changes : List (WriterChange sig)} {updates : List Stored.OwnedMemory.Claims.Spend}

theorem ofSteps (run : Steps profile ready dispatch start labels finish) :
    ∃ changes, WriterPath profile ready dispatch start labels finish changes := by
  classical
  induction run with
  | refl state => exact ⟨[], .done state⟩
  | @cons start next _ _ _ step _ ih =>
    obtain ⟨changes, tail⟩ := ih
    by_cases same : next.host.writer = start.host.writer
    · exact ⟨changes, .same step same tail⟩
    · exact ⟨_, .changed step same tail⟩

theorem append (first : WriterPath profile ready dispatch start leading middle before)
    (rest : WriterPath profile ready dispatch middle trailing finish after) :
    WriterPath profile ready dispatch start (leading ++ trailing) finish (before ++ after) := by
  induction first with
  | done => exact rest
  | same step unchanged _ ih => exact .same step unchanged (ih rest)
  | changed step different _ ih => exact .changed step different (ih rest)

theorem spend (path : WriterPath profile ready dispatch start labels finish changes)
    (spends : List.Forall₂ WriterChange.IsSpend changes updates) :
    finish.host.writer = updates.foldl (fun state update => update.apply state) start.host.writer := by
  induction path generalizing updates with
  | done => cases spends; rfl
  | same _ unchanged _ ih => simpa only [unchanged] using ih spends
  | changed _ _ _ ih =>
    cases spends with
    | cons head tail =>
      have after : _ = _ := head.2
      rw [List.foldl_cons, ← after]
      exact ih tail

theorem firstChange {change : WriterChange sig}
    (path : WriterPath profile ready dispatch start labels finish (change :: changes)) :
    ∃ leading label trailing before after, labels = leading ++ label :: trailing ∧
      WriterPath profile ready dispatch start leading before [] ∧
      Step profile ready dispatch before label after ∧
      change = (before.host.writer, after.host.writer) ∧ after.host.writer ≠ before.host.writer ∧
      WriterPath profile ready dispatch after trailing finish changes := by
  generalize effectList : change :: changes = recorded at path
  induction path with
  | done => contradiction
  | @same start next finish first labels effects step same _ ih =>
    obtain ⟨leading, label, trailing, before, after, rfl, front, write, delta, different, tail⟩ := ih effectList
    exact ⟨first :: leading, label, trailing, before, after, rfl, .same step same front, write, delta, different, tail⟩
  | @changed start next finish label labels effects step different tail _ =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj effectList
    exact ⟨[], label, labels, start, next, rfl, .done start, step, rfl, different, tail⟩

theorem classify (change : WriterChange sig) :
    (∃ update, change.IsSpend update) ∨ (∃ tree, change.IsRegistration tree) ∨
      ((∀ update, ¬ change.IsSpend update) ∧ (∀ tree, ¬ change.IsRegistration tree)) := by
  classical
  by_cases spends : ∃ update, change.IsSpend update
  · exact .inl spends
  by_cases registers : ∃ tree, change.IsRegistration tree
  · exact .inr (.inl registers)
  exact .inr (.inr ⟨fun _ found => spends ⟨_, found⟩, fun _ found => registers ⟨_, found⟩⟩)

variable {base : HostImpl (core3 grow) (HostState sig)} {bindings : List (Binding sig)}
variable {marks : List (Option ReturnFrame.Occurrence.Location)}

theorem ofTransport (paths : OccurrenceTransport profile ready base bindings start incoming checked canonical left right marks) :
    PairedWriterPaths profile ready base bindings start incoming checked canonical left right := by
  obtain ⟨_, tracks, _⟩ := paths
  obtain ⟨leftEffects, leftPath⟩ := ofSteps (tracks none).1.steps
  obtain ⟨rightEffects, rightPath⟩ := ofSteps (tracks none).2.steps
  exact ⟨leftEffects, rightEffects, leftPath, rightPath⟩

theorem appendPaired (first : PairedWriterPaths profile ready base bindings start incoming leading canonLeading middle peer)
    (tail : PairedWriterPaths profile ready base bindings middle peer trailing canonTrailing finish target) :
    PairedWriterPaths profile ready base bindings start incoming (leading ++ trailing) (canonLeading ++ canonTrailing) finish target := by
  obtain ⟨_, _, lhs, rhs⟩ := first
  obtain ⟨_, _, leftTail, rightTail⟩ := tail
  exact ⟨_, _, append lhs leftTail, append rhs rightTail⟩

theorem checkedSpends (leftPath : WriterPath profile ready (specDispatch ready base) start checked left changes)
    (rightPath : WriterPath profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming canonical right [])
    (spends : List.Forall₂ WriterChange.IsSpend changes updates) :
    CheckedSpendFlow start.host.writer incoming.host.writer left.host.writer right.host.writer updates :=
  ⟨spend leftPath spends, spend rightPath (updates := []) .nil⟩

theorem registration {change : WriterChange sig} {tree : Stored.OwnedMemory.Tree sig}
    (path : WriterPath profile ready dispatch start labels finish [change])
    (registers : WriterChange.IsRegistration change tree) : start.host.writer.register tree = .ok finish.host.writer := by
  obtain ⟨_, _, _, before, after, _, front, _, rfl, _, tail⟩ := firstChange path
  change before.host.writer.register tree = .ok after.host.writer at registers
  have startWriter : before.host.writer = start.host.writer := spend front (updates := []) .nil
  have finalWriter : finish.host.writer = after.host.writer := spend tail (updates := []) .nil
  rw [startWriter, ← finalWriter] at registers
  exact registers

theorem visitor {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)}
    {valueType : Type} {pending : Config (core3 grow) (HostState sig) → Prop}
    {checkNext : Except Stored.Endpoints.RecordLower.Issue valueType → Session grow sig (Ret (core3 grow))}
    {canonNext : valueType → Session grow sig (Ret (core3 grow))}
    (body : ValueVisitRun profile ready base bindings older origin valueType pending checkNext canonNext start incoming actual finish) :
    ∃ checked canonical trailing left right marks, actual = checked ++ trailing ∧
      PayloadPrefix.visible checked = PayloadPrefix.visible canonical ∧ left.store = right.store ∧
      OccurrenceTransport profile ready base bindings start incoming checked canonical left right marks ∧
      PairedWriterPaths profile ready base bindings start incoming checked canonical left right ∧
      Steps profile ready (specDispatch ready base) left trailing finish ∧
      ValueVisitEnd profile ready base bindings older origin valueType pending checkNext canonNext left right trailing finish marks := by
  obtain ⟨checked, canonical, trailing, left, right, marks, split, visible, stores, tracks, tail, ending⟩ := body
  exact ⟨checked, canonical, trailing, left, right, marks, split, visible, stores, tracks, ofTransport tracks, tail, ending⟩

theorem stringSlice {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {description}
    (body : StringRunSlice profile ready base bindings older description start incoming actual finish) :
    ∃ checked canonical trailing left right marks, actual = checked ++ trailing ∧
      PayloadPrefix.visible canonical = PayloadPrefix.visible checked ∧
      OccurrenceTransport profile ready base bindings start incoming checked canonical left right marks ∧
      PairedWriterPaths profile ready base bindings start incoming checked canonical left right ∧
      left.store = right.store ∧ Steps profile ready (specDispatch ready base) left trailing finish ∧
      StringSliceEnd profile ready base bindings older description left right trailing finish marks := by
  obtain ⟨checked, canonical, trailing, left, right, marks, split, visible, tracks, stores, tail, ending⟩ := body
  exact ⟨checked, canonical, trailing, left, right, marks, split, visible, tracks, ofTransport tracks, stores, tail, ending⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.WriterPaths
