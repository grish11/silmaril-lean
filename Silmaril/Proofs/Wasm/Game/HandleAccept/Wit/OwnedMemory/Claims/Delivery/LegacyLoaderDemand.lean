module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveDispatch.Plan.Defs

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LegacyLoaderDemand

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Game.Accept (Callout)
open Silmaril.Wasm.Game.HandleAccept.Wit
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Memory (le32s)
open Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst
  (requireSome checkNodeMode checkedCallout nodeOperands)
open Stored.Endpoints.Core (Contract Issue childFromHistory checkChildren decodeChildren)
open Stored.OwnedMemory.Claims.Core (FlatSource World)
open Stored.OwnedMemory.Claims.Core.Scheduled
open LiveDispatch

private theorem visitedChildMismatch_of_mapM {Value : Type} {left right : List Value} {handles : List (BitVec 32)}
    (different : (handles.mapM fun handle => requireSome (Issue.invalidChild handle) (childFromHistory left handle)) ≠
      (handles.mapM fun handle => requireSome (Issue.invalidChild handle) (childFromHistory right handle))) :
    VisitedChildMismatch left right handles := by
  induction handles with
  | nil => exact False.elim (different rfl)
  | cons handle tail ih =>
    by_cases agrees : childFromHistory left handle = childFromHistory right handle
    · cases leftRead : childFromHistory left handle with
      | none =>
        have rightRead := agrees.symm.trans leftRead
        exact False.elim (different (by rw [List.mapM_cons, List.mapM_cons, leftRead, rightRead]; rfl))
      | some child =>
        have rightRead := agrees.symm.trans leftRead
        refine .next leftRead rightRead (ih fun equalTail => different ?_)
        rw [List.mapM_cons, List.mapM_cons, leftRead, rightRead, equalTail]
    · exact .first agrees

private theorem decodeChildren_demand {Value : Type} {left right : List Value}
    {observed : Callout} {pointer count : Nat}
    (different : decodeChildren observed left pointer count ≠ decodeChildren observed right pointer count) :
    ∃ bytes handles, observed.segment pointer (4 * count) = some bytes ∧
      le32s bytes = some handles ∧ VisitedChildMismatch left right handles := by
  unfold decodeChildren at different
  cases range : observed.segment pointer (4 * count) with
  | none => exact False.elim (different (by rw [range]; rfl))
  | some bytes =>
    cases decoded : le32s bytes with
    | none => exact False.elim (different (by simp only [range, requireSome, bind, Except.bind, decoded]))
    | some handles =>
      refine ⟨bytes, handles, rfl, decoded, visitedChildMismatch_of_mapM ?_⟩
      simpa only [range, requireSome, bind, Except.bind, decoded] using different

private theorem different_after_bind {Error A B : Type} {read : Except Error A}
    {checked canonical : A → Except Error B} (different : (read >>= checked) ≠ (read >>= canonical)) :
    ∃ result, read = .ok result ∧ checked result ≠ canonical result := by
  cases read with
  | error error => exact False.elim (different rfl)
  | ok result => exact ⟨result, rfl, different⟩

set_option maxHeartbeats 400000 in
private theorem memoryHistoryDemand {sig : Signature} {Value : Type}
    {left right : List Value} {contract : Contract sig} {check : Stored.TypeOf → Except Stored.Issue Unit}
    {memory : Option Nat} {call : UCall Nat}
    (different : contract.preflightOperands check memory left call ≠ contract.preflightOperands check memory right call) :
    LegacyMemoryChildDemand contract check memory left right call := by
  unfold Contract.preflightOperands at different
  obtain ⟨⟨⟩, mode, different⟩ := different_after_bind different
  obtain ⟨mem, memSource, different⟩ := different_after_bind different
  obtain ⟨observed, callout, different⟩ := different_after_bind different
  obtain ⟨⟨rawTag, payload, pointer, count⟩, operands, different⟩ := different_after_bind different
  obtain ⟨tag, selected, different⟩ := different_after_bind different
  obtain ⟨⟨⟩, schema, different⟩ := different_after_bind different
  refine ⟨mem, observed, rawTag, payload, pointer, count, tag, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases h : checkNodeMode contract.mode <;> simp only [h, Except.mapError] at mode <;> cases mode; rfl
  · cases memory <;> simp only [requireSome] at memSource <;> cases memSource; rfl
  · cases h : checkedCallout contract.name mem call contract.mode.address <;>
      simp only [h, Except.mapError] at callout <;> cases callout; rfl
  · cases h : nodeOperands contract.mode.address observed.args <;>
      simp only [h, requireSome] at operands <;> cases operands; rfl
  · cases h : contract.tagOf rawTag <;> simp only [h, requireSome] at selected <;> cases selected; rfl
  · cases h : check (sig.payload tag) <;> simp only [h, Except.mapError] at schema <;> cases schema; rfl
  by_cases capacity : checkChildren sig tag left.length pointer count = checkChildren sig tag right.length pointer count
  · rw [← capacity] at different
    obtain ⟨⟨⟩, checked, different⟩ := different_after_bind different
    by_cases aligned : payload % (ABI.layout contract.mode.address (sig.payload tag)).alignment.bytes = 0
    · dsimp only at different
      simp only [ite_eq_right (not_not.mpr aligned)] at different
      obtain ⟨payloadBytes, payloadRange, different⟩ := different_after_bind different
      have payloadRange : observed.segment payload (ABI.layout contract.mode.address (sig.payload tag)).size = some payloadBytes := by
        unfold requireSome at payloadRange
        split at payloadRange <;> cases payloadRange; assumption
      have selected : decodeChildren observed left pointer count ≠ decodeChildren observed right pointer count := by
        intro equal
        apply different
        rw [equal]
      obtain ⟨bytes, handles, range, words, lookup⟩ := decodeChildren_demand selected
      exact .child ⟨aligned, payloadBytes, payloadRange⟩ checked (capacity ▸ checked) range words lookup
    · apply False.elim
      apply different
      dsimp only
      simp only [ite_eq_left aligned]
      rfl
  · exact .capacity capacity

set_option maxHeartbeats 400000 in
private theorem flatHistoryDemand {sig : Signature} {grow : SingleThreaded.GrowOracle}
    {source : FlatSource sig} {store : CStore (core3 grow)} {left right : Stored.OwnedMemory.Claims.State sig}
    {args : List FlatValue}
    (different : source.preflight ⟨store, left⟩ args ≠ source.preflight ⟨store, right⟩ args) :
    LegacyFlatChildDemand source store left right args := by
  unfold FlatSource.preflight at different
  obtain ⟨⟨⟩, schema, different⟩ := different_after_bind different
  obtain ⟨observed, callout, different⟩ := different_after_bind different
  rcases args with _ | ⟨pointer, _ | ⟨count, payload⟩⟩
  · exact False.elim (different rfl)
  · exact False.elim (different rfl)
  dsimp only at different
  cases operands : (Stored.flatType pointer != ABI.pointerType source.width || Stored.flatType count != ABI.pointerType source.width)
  case true => exact False.elim (different (by simp only [operands, ite_true]; rfl))
  simp only [operands, Bool.false_eq_true, ↓reduceIte] at different
  cases types : (payload.map Stored.flatType != ABI.flatten source.width (sig.payload source.tag))
  case true => exact False.elim (different (by simp only [types, ite_true]; rfl))
  simp only [types, Bool.false_eq_true, ↓reduceIte] at different
  refine ⟨observed, pointer, count, payload, schema, ?_, rfl, operands, types, ?_⟩
  · cases h : checkedCallout source.name source.memory ⟨0, { mems := store.core.mems }, []⟩ source.width <;>
      simp only [h, Except.mapError] at callout <;> cases callout; rfl
  by_cases capacity : checkChildren sig source.tag left.accepted.length (flatNat pointer) (flatNat count) =
      checkChildren sig source.tag right.accepted.length (flatNat pointer) (flatNat count)
  · rw [← capacity] at different
    obtain ⟨⟨⟩, result, different⟩ := different_after_bind different
    have checked : checkChildren sig source.tag left.accepted.length (flatNat pointer) (flatNat count) = .ok () := by
      cases h : checkChildren sig source.tag left.accepted.length (flatNat pointer) (flatNat count) <;>
        simp only [h, Except.mapError] at result <;> cases result; rfl
    have selected : decodeChildren observed left.accepted (flatNat pointer) (flatNat count) ≠
        decodeChildren observed right.accepted (flatNat pointer) (flatNat count) := by
      intro equal
      apply different
      rw [equal]
    obtain ⟨bytes, handles, range, words, lookup⟩ := decodeChildren_demand selected
    exact .child trivial checked (capacity ▸ checked) range words lookup
  · exact .capacity capacity


theorem ofLoaderDifference {sig : Signature} {grow : SingleThreaded.GrowOracle} {bindings : List (Binding sig)}
    {name kind args inst loader} {left right : World grow sig}
    (source : LinkedCoreAcceptLoader bindings name kind args inst loader)
    (stores : left.reference = right.reference) (different : loader left ≠ loader right) :
    LinkedCoreAcceptHistoryDemand bindings name kind args left right inst loader := by
  rcases left with ⟨leftStore, leftWriter⟩
  rcases right with ⟨rightStore, rightWriter⟩
  change leftStore = rightStore at stores
  subst rightStore
  cases source with
  | memory contract memory linked =>
    refine .memory contract memory linked rfl (memoryHistoryDemand ?_)
    intro agrees
    apply different
    let call := Stored.Endpoints.Core.Scheduled.nodeCall contract leftStore args
    change Stored.OwnedMemory.Claims.Core.load contract memory ⟨leftStore, leftWriter⟩ call =
      Stored.OwnedMemory.Claims.Core.load contract memory ⟨leftStore, rightWriter⟩ call
    unfold Stored.OwnedMemory.Claims.Core.load Stored.OwnedMemory.Claims.Core.preflight
    dsimp only
    rw [agrees]
  | flat source linked =>
    refine .flat source linked rfl (flatHistoryDemand ?_)
    intro agrees
    apply different
    change source.load ⟨leftStore, leftWriter⟩ args = source.load ⟨leftStore, rightWriter⟩ args
    unfold FlatSource.load
    rw [agrees]

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.LegacyLoaderDemand
