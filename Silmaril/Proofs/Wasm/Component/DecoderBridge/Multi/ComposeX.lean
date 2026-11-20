module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.NodesRefX

/-!
# The start goal on `MultiImpFrag` from the export call with the invariant

* `nodeEnd_of_calls`, `nodeCalls_of_end`, `ends_of_calls`: a ready node's `NodeCalls` is a node
  end (`NodeEnd`) with the same calls, and conversely;
* `nodesRef_of_X`: `Task.nodesRef` is the projection of `Task.nodesRefX`;
* `startAdequacyFrag_of_X`: **`Task.startAdequacyFrag` from `Task.exportRefX`**: the IR play splits
  into its node-by-node instantiation and the calls of each node (`nodeCallsIR`), whose ends are
  chosen; the reference machine finishes the instantiation with the invariant (`nodesRefX`); the
  export call matches (`Task.exportRefX`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Conformance Silmaril.Wasm.Component.DecoderBridge
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Component.InstTests Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Wasm.Component.Reference.Core3Adder (first)
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp
open Silmaril.Wasm.SingleThreaded (profile neverFail)

/-- A node end is a ready `NodeCalls` with its calls. -/
theorem nodeCalls_of_end {n : Nat} {cm : Binary.CoreMod} {args : List Impl} {x : NodeRun}
    (h : NodeEnd n cm args x) : NodeCalls n .ready cm args x.calls := by
  obtain ⟨hJ, -, ys, hF, hst⟩ := h
  refine ⟨ys, ⟨x.inst, hJ, ?_⟩, hF⟩
  rcases hst with ⟨h1, h2, -⟩ | ⟨f, c', vs, h1, h2, h3, -⟩
  · exact .inl ⟨h1, h2⟩
  · exact .inr ⟨f, c', vs, h1, h2, h3⟩

/-- A ready `NodeCalls` of a node of the fragment has a node end with its calls. -/
theorem nodeEnd_of_calls {p : Binary.CoreMod × List Impl} (hno : NodeOk p)
    {t : List (Σ _ : sigU.Op, Option Payload)} (h : NodeCalls hostI.length .ready p.1 p.2 t) :
    ∃ x : NodeRun, x.calls = t ∧ NodeEnd hostI.length p.1 p.2 x := by
  obtain ⟨ys, ⟨J, hJ, hst⟩, hF⟩ := h
  obtain ⟨-, hsome⟩ := instOfI_cases hno.imps hno.names
  obtain ⟨mi, hp⟩ := hsome J hJ
  rcases hst with ⟨h1, rfl⟩ | ⟨f, c', vs, h1, h2, h3⟩
  · exact ⟨⟨t, J, mi, J.store⟩, rfl, hJ, hp, [], hF, .inl ⟨h1, rfl, rfl⟩⟩
  · exact ⟨⟨t, J, mi, c'.1⟩, rfl, hJ, hp, ys, hF, .inr ⟨f, c', vs, h1, h2, h3, rfl⟩⟩

theorem ends_of_calls :
    ∀ {ps : List (Binary.CoreMod × List Impl)} {ts : List (List (Σ _ : sigU.Op, Option Payload))},
      List.Forall₂ (fun q tj => NodeCalls hostI.length .ready q.1 q.2 tj) ps ts →
      (∀ p ∈ ps, NodeOk p) →
      ∃ xs : List NodeRun, xs.map NodeRun.calls = ts ∧
        List.Forall₂ (fun q x => NodeEnd hostI.length q.1 q.2 x) ps xs
  | [], [], .nil, _ => ⟨[], rfl, .nil⟩
  | p :: ps, t :: ts, .cons h hs, hok => by
    obtain ⟨x, rfl, hx⟩ := nodeEnd_of_calls (hok p List.mem_cons_self) h
    obtain ⟨xs, rfl, hxs⟩ := ends_of_calls hs (fun q hq => hok q (List.mem_cons_of_mem _ hq))
    exact ⟨x :: xs, rfl, .cons hx hxs⟩

/-- **`Task.nodesRef`, the projection of `Task.nodesRefX`.** -/
theorem nodesRef_of_X (h : Task.nodesRefX) : Task.nodesRef := by
  intro b c r ps ts hpc hr hf himp hnodes hu hNC
  obtain ⟨xs, rfl, hxs⟩ := ends_of_calls hNC (nodeOk_frag hpc hr hf hnodes)
  obtain ⟨M', inst, es, hI, hh, -⟩ := h b c r ps xs hpc hr hf himp hnodes hu hxs
  exact ⟨M', inst, es, hI, hh⟩

/-- **The start goal on the fragment from the export call with the invariant.** -/
theorem startAdequacyFrag_of_X (hd : Task.exportRefX) : Task.startAdequacyFrag := by
  intro b c r t n ws hpc hr hv hf himp hex hu hp
  obtain ⟨-, hw, -, -⟩ := multiImpFrag_inv hf
  obtain ⟨ps, hnodes, hNI⟩ := nodesInst_of_startPlay hpc hr hw hp
  rw [himp] at hNI
  obtain ⟨ts, rfl, hF⟩ := nodeCallsIR b c r ps t hpc hr hf himp hnodes hu hNI
  obtain ⟨xs, rfl, hxs⟩ := ends_of_calls hF (nodeOk_frag hpc hr hf hnodes)
  obtain ⟨M', inst, es, hI, hh, hN⟩ := nodesRefX b c r ps xs hpc hr hf himp hnodes hu hxs
  obtain ⟨f, M'', hl, hS, hh'⟩ := hd b c r ps xs n ws M' inst es hpc hr hv hf himp hnodes hex hu
    hxs hp hN
  refine ⟨M', inst, es, [f], M'', hI, ?_, ?_, ?_⟩
  · simp [hl]
  · exact hS
  · rw [hh', hh]

end Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi
