module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream.Replay

/-!
# Chunk relations from a replayed session

`Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream.sRunB` simulates the mixed host along a
decoded session with the append buffer; for chunk exports it simulates with the **chunk
buffer**:

* `cRunB W bad w₀ x₀ σ buf t`: fresh writes, export calls, accepts of defined handles, `feed`
  answers (appended to `buf`) and `finish(n, h)` answers with `n` within the buffer and `h` a
  defined, non-`bad` handle (they consume `n` values and relate them to the tree of `h`); the
  result records whether `(w₀, x₀)` was related; `run_of_cRunB`: a simulated trace has a run of
  the mixed host (store semantics);
* **`mem_moduleMixedRel_of_replaySeqC`**: if the simulation of the decoded replay of the export
  calls `cs` from the empty store and buffer relates `(w₀, x₀)`, the pair is in the module's mixed
  relation, for every profile admitting the deterministic steps of the replay interpreter.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Spec Silmaril.Wasm.Verify
  Silmaril.Wasm.Validation Silmaril.Wasm.Resource Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Writers Silmaril.Wasm.Game.HandleAccept.Parsing
  Silmaril.Wasm.Game.HandleAccept.Mixed Silmaril.Accept Silmaril.Accept.Handle
  Silmaril.Accept.Parse Silmaril.Accept.Mixed Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Proofs.Wasm.Game.HandleAccept.Replay Silmaril.Proofs.Wasm.Game.HandleAccept.Parsing
  Silmaril.Proofs.Wasm.Game.HandleAccept.Writers Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream
open Silmaril.Wasm.Numerics (Profile)

section Run

variable {Op V H X : Type} [DecidableEq H] [DecidableEq V] [DecidableEq X]

/-- **Simulate the mixed host along a trace with the chunk buffer `buf`**: `none` when a step is
not one of the simulated kinds; otherwise whether `(w₀, x₀)` is related. -/
def cRunB (W : Writer Op X) (bad : H → Bool) (w₀ : List V) (x₀ : X) :
    Env H X → List V → List (MEv Op V H) → Option Bool
  | _, _, [] => some false
  | σ, buf, .w (.write op args r) :: es =>
    match W.built σ op args with
    | some t =>
      if bad r = false ∧ σ r = none then
        cRunB W bad w₀ x₀ (Function.update σ r (some t)) buf es
      else none
    | none => none
  | σ, buf, .w (.accept h) :: es =>
    match σ h with
    | some _ => cRunB W bad w₀ x₀ σ buf es
    | none => none
  | σ, buf, .w .enter :: es => cRunB W bad w₀ x₀ σ buf es
  | σ, buf, .p (.feed c) :: es => cRunB W bad w₀ x₀ σ (buf ++ c) es
  | σ, buf, .p (.finish n h) :: es =>
    if n ≤ buf.length ∧ bad h = false then
      match σ h with
      | some x => (cRunB W bad w₀ x₀ σ (buf.drop n) es).map
          fun b => decide (buf.take n = w₀ ∧ x = x₀) || b
      | none => none
    else none
  | _, _, _ :: _ => none

/-- A simulated trace has a run of the mixed host. -/
theorem run_of_cRunB (W : Writer Op X) {bad : H → Bool} {w₀ : List V} {x₀ : X}
    {pol : Policy H} {ppol : PPolicy H} (hbad : ∀ r, pol.sentinel = some r → bad r = true)
    (hpbad : bad ppol.sentinel = true) :
    ∀ (t : List (MEv Op V H)) (σ : Env H X) (B : Set X) (acc buf : List V) (b : Bool),
      cRunB W bad w₀ x₀ σ buf t = some b →
      ∃ s A, (mixed W pol ppol).Run ⟨⟨σ, B, .live⟩, ⟨acc, buf, .live⟩⟩ t s A ∧
        (b = true → (w₀, x₀) ∈ A)
  | [], _, _, _, _, b, h => by
    simp only [cRunB, Option.some.injEq] at h
    subst h
    exact ⟨_, ∅, .nil _, by simp⟩
  | .w (.write op args r) :: es, σ, B, acc, buf, b, h => by
    simp only [cRunB] at h
    split at h
    · rename_i t ht
      split at h
      · rename_i hfr
        obtain ⟨s, A, hr, hA⟩ := run_of_cRunB W hbad hpbad es _ (insert t B) acc buf b h
        have hne : pol.sentinel ≠ some r := fun hs => by
          have := hbad r hs
          rw [hfr.1] at this
          cases this
        have hstep : MStep W pol ppol none ⟨⟨σ, B, .live⟩, ⟨acc, buf, .live⟩⟩
            (.w (.write op args r))
            ⟨⟨Function.update σ r (some t), insert t B, .live⟩, ⟨acc, buf, .live⟩⟩
            (chaosPairs .live) :=
          .w (WStep.writeOk ht ⟨hne, Or.inl hfr.2⟩ fun _ h => by cases h)
        exact ⟨s, _, .cons hstep hr, fun hb => Or.inr (hA hb)⟩
      · cases h
    · cases h
  | .w (.accept h') :: es, σ, B, acc, buf, b, h => by
    simp only [cRunB] at h
    split at h
    · rename_i t ht
      obtain ⟨s, A, hr, hA⟩ := run_of_cRunB W hbad hpbad es σ B acc buf b h
      have hstep : MStep W pol ppol none ⟨⟨σ, B, .live⟩, ⟨acc, buf, .live⟩⟩ (.w (.accept h'))
          ⟨⟨σ, B, .live⟩, ⟨acc, buf, .live⟩⟩ (chaosPairs .live) := .w (WStep.acceptOk ht)
      exact ⟨s, _, .cons hstep hr, fun hb => Or.inr (hA hb)⟩
    · cases h
  | .w .enter :: es, σ, B, acc, buf, b, h => by
    simp only [cRunB] at h
    obtain ⟨s, A, hr, hA⟩ := run_of_cRunB W hbad hpbad es σ B acc buf b h
    have hstep : MStep W pol ppol none ⟨⟨σ, B, .live⟩, ⟨acc, buf, .live⟩⟩ (.w .enter)
        ⟨⟨σ, B, .live⟩, ⟨acc, buf, .live⟩⟩ (chaosPairs .live) := .w WStep.enter
    exact ⟨s, _, .cons hstep hr, fun hb => Or.inr (hA hb)⟩
  | .p (.feed c) :: es, σ, B, acc, buf, b, h => by
    simp only [cRunB] at h
    obtain ⟨s, A, hr, hA⟩ := run_of_cRunB W hbad hpbad es σ B acc (buf ++ c) b h
    have hstep : MStep W pol ppol none ⟨⟨σ, B, .live⟩, ⟨acc, buf, .live⟩⟩ (.p (.feed c))
        ⟨⟨σ, B, .live⟩, ⟨acc, buf ++ c, .live⟩⟩ ∅ := .p rfl (PStep.feed c)
    exact ⟨s, _, .cons hstep hr, fun hb => Or.inr (hA hb)⟩
  | .p (.finish n h') :: es, σ, B, acc, buf, b, h => by
    simp only [cRunB] at h
    split at h
    · rename_i hgood
      split at h
      · rename_i x hx
        obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.1 h
        obtain ⟨s, A, hr, hA⟩ := run_of_cRunB W hbad hpbad es σ B acc _ b' hb'
        have hne : h' ≠ ppol.sentinel := fun he => by
          rw [he, hpbad] at hgood
          exact absurd hgood.2 (by simp)
        have hres : resolve ppol σ (buf.take n) h' = some {(buf.take n, x)} := by
          simp [resolve, hne, hx]
        have hstep : MStep W pol ppol none ⟨⟨σ, B, .live⟩, ⟨acc, buf, .live⟩⟩
            (.p (.finish n h')) ⟨⟨σ, B, .live⟩, ⟨acc, buf.drop n, .live⟩⟩ {(buf.take n, x)} :=
          .p rfl (PStep.ret rfl ⟨hgood.1, rfl, rfl, rfl⟩ hres)
        refine ⟨s, _, .cons hstep hr, fun hb => ?_⟩
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hb
        rcases hb with ⟨hw, hx₀⟩ | hb
        · rw [← hw, ← hx₀]
          exact Or.inl rfl
        · exact Or.inr (hA hb)
      · cases h
    · cases h
  | .w (.acceptErr _ _) :: _, _, _, _, _, _, h => by cases h
  | .w .acceptAll :: _, _, _, _, _, _, h => by cases h
  | .w (.acceptBatch _) :: _, _, _, _, _, _, h => by cases h
  | .p (.parse _ _) :: _, _, _, _, _, _, h => by cases h
  | .p (.append _) :: _, _, _, _, _, _, h => by cases h
  | .p (.done _) :: _, _, _, _, _, _, h => by cases h
  | .p .reset :: _, _, _, _, _, _, h => by cases h

end Run

/-- **A mixed pair from a replayed chunk session** (store semantics). -/
theorem mem_moduleMixedRel_of_replaySeqC {V : Type} [DecidableEq V] {m : Module}
    (hm : (instance? m).isSome = true) {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
    (wix : ConsWImports) (pix : ParseExports V) {pol : Policy (BitVec 32)}
    {ppol : PPolicy (BitVec 32)} {bad : BitVec 32 → Bool}
    (hbad : ∀ r, pol.sentinel = some r → bad r = true) (hpbad : bad ppol.sentinel = true)
    (sc : Script) (fuel n : Nat) (cs : List (instOf m).F.Op) {w₀ : List V}
    {x₀ : SExp2 (BitVec 64)}
    (hrun : cRunB (consW (BitVec 64)) bad w₀ x₀ Env.empty []
      (rdecM (consWAsk wix) (consWAns wix) (parseRet pix) [] []
        (replaySeqR (instOf m) sc fuel n (instOf m).store 0 cs)) = some true) :
    (w₀, x₀) ∈ moduleMixedRel P m wix pix pol ppol := by
  obtain ⟨mt, hI⟩ := isInstance_instOf hm
  obtain ⟨ms, q, hp, hmap⟩ := replaySeqR_path (sc := sc) (fuel := fuel) (n := n) hP cs
    (instOf m).store 0 hI.ok
  have hms : ms ∈ (instOf m).strategy P (instOf m).store :=
    ScalarInstance.mem_strategy_iff.2 ⟨q, hp⟩
  have htr : mixedEvents (consWDecAsk wix) (consWDecAns wix) (parseDec pix) ms =
      rdecM (consWAsk wix) (consWAns wix) (parseRet pix) [] []
        (replaySeqR (instOf m) sc fuel n (instOf m).store 0 cs) := by
    rw [← hmap]
    exact mixedEvents_path _ _ _ _ _ _ (consWDecAsk_eq wix) (consWDecAns_eq wix)
      (parseDec_eq pix) hp [] [] (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h)
  have hT : rdecM (consWAsk wix) (consWAns wix) (parseRet pix) [] []
      (replaySeqR (instOf m) sc fuel n (instOf m).store 0 cs) ∈ moduleMixedTraces P m wix pix :=
    ⟨ms, hms, htr.symm⟩
  obtain ⟨s, A, hr, hA⟩ := run_of_cRunB (consW (BitVec 64)) (ppol := ppol) hbad hpbad _
    Env.empty ∅ [] [] true hrun
  exact Set.mem_biUnion hT ⟨s, A, hr, hA rfl⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk
