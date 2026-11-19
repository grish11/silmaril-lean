module

public import Silmaril.Wasm.Game.HandleAccept.Mixed.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.Parse.Replay
public import Silmaril.Proofs.Wasm.Game.HandleAccept.Writer.Replay

/-!
# Mixed relations from a replayed export call

* `rdecM dAsk dAns dRet xa pa rs`: the mixed events of recorded moves: export calls as
  `enter`, import calls and answers through the raw writer decoders (answers decoded with the
  arguments `pa` of the pending import call), export answers through the raw parsing decoder
  (with the arguments `xa` of the pending export call); `mixedEvents_path`: along a path,
  `mixedEvents` is `rdecM` of the recorded moves.
* `mRunB W bad v₀ x₀ σ t`: simulates the mixed host (store semantics) along `t` with fresh
  writes whose handles are not `bad`, accepts of defined handles, export calls and `parse`
  answers naming defined handles that are not `bad`: `none` when stuck, else whether
  `([v₀], x₀)` is related; `run_of_mRunB`.
* **`mem_moduleMixedRel_of_replay`**: if the simulation of the decoded replay (with the export
  answer, `replayExportR`) from the empty store relates `([v₀], x₀)`, the pair is in the module's
  mixed relation, for every profile admitting the deterministic steps of the replay interpreter.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Verify Silmaril.Wasm.Resource
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Writers Silmaril.Wasm.Game.HandleAccept.Parsing
  Silmaril.Wasm.Game.HandleAccept.Mixed Silmaril.Accept Silmaril.Accept.Handle
  Silmaril.Accept.Parse Silmaril.Accept.Mixed Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Proofs.Wasm.Game.HandleAccept.Replay Silmaril.Proofs.Wasm.Game.HandleAccept.Parsing
  Silmaril.Proofs.Wasm.Game.HandleAccept.Writers
open Silmaril.Wasm.Numerics (Profile)

/-! ## Decoding recorded moves -/

section Decode

variable {Op V H : Type}

/-- The mixed events of recorded moves; `xa` and `pa` are the arguments of the pending export
and import calls. -/
def rdecM (dAsk : Nat → List Val → Option (WEv Op H))
    (dAns : Nat → List Val → Behaviour Val → Option (WEv Op H))
    (dRet : Nat → List Val → Behaviour Val → Option (PEv V H)) :
    List Val → List Val → List RMove → List (MEv Op V H)
  | _, _, [] => []
  | _, pa, .call _ a :: rs => .w .enter :: rdecM dAsk dAns dRet a pa rs
  | xa, _, .ask h a :: rs => ((dAsk h a).map .w).toList ++ rdecM dAsk dAns dRet xa a rs
  | xa, pa, .ans h b :: rs => ((dAns h pa b).map .w).toList ++ rdecM dAsk dAns dRet xa pa rs
  | xa, pa, .ret j b :: rs => ((dRet j xa b).map .p).toList ++ rdecM dAsk dAns dRet xa pa rs

variable {I : ScalarInstance}

/-- **Decoding a path** into mixed events with decoders factoring through raw ones. -/
theorem mixedEvents_path (decAsk : I.E.Op → Option (WEv Op H))
    (decAns : (e : I.E.Op) → I.E.Ar e → Option (WEv Op H))
    (pdec : (f : I.F.Op) → I.F.Ar f → Option (PEv V H))
    (dAsk : Nat → List Val → Option (WEv Op H))
    (dAns : Nat → List Val → Behaviour Val → Option (WEv Op H))
    (dRet : Nat → List Val → Behaviour Val → Option (PEv V H))
    (hAsk : ∀ e, decAsk e = dAsk e.1.val e.2.1)
    (hAns : ∀ e v, decAns e v = dAns e.1.val e.2.1 (Answer.toBehaviour (ft := I.imports.get e.1) v))
    (hRet : ∀ f v, pdec f v = dRet f.1.val f.2.1 (Answer.toBehaviour (ft := I.exports.get f.1) v))
    {P : Profile} :
    ∀ {q : I.HState} {ms : List (Move I.E I.F)} {q' : I.HState}, I.Path P q ms q' →
      ∀ xa pa : List Val, (∀ f s t, q = .running f s t → xa = f.2.1) →
      (∀ f s t e, q = .waiting f s t e → xa = f.2.1 ∧ pa = e.2.1) →
      mixedEvents decAsk decAns pdec ms = rdecM dAsk dAns dRet xa pa (ms.map rmv) := by
  intro q ms q' hp
  induction hp with
  | nil => intro _ _ _ _; rfl
  | @cons q₀ q₁ q₂ m p htr _ ih =>
    intro xa pa hr hw
    cases htr with
    | call s f =>
      exact congrArg (MEv.w .enter :: ·)
        (ih f.2.1 pa (fun _ _ _ h => by cases h; rfl) (fun _ _ _ _ h => by cases h))
    | @ucall f s s' t t' h args e run callout op =>
      show ((decAsk e).map MEv.w).toList ++ _ = ((dAsk e.1.val e.2.1).map MEv.w).toList ++ _
      rw [hAsk]
      exact congrArg _ (ih xa e.2.1 (fun _ _ _ h => by cases h)
        (fun _ _ _ _ h => by cases h; exact ⟨hr f s t rfl, rfl⟩))
    | @uret f s t e v =>
      obtain ⟨hx, hpa⟩ := hw f s t e rfl
      subst hx hpa
      show ((decAns e v).map MEv.w).toList ++ _ = ((dAns e.1.val e.2.1 _).map MEv.w).toList ++ _
      rw [hAns]
      exact congrArg _ (ih f.2.1 e.2.1 (fun _ _ _ h => by cases h; rfl)
        (fun _ _ _ _ h => by cases h))
    | @oret f s s' t t' r v run final answer =>
      have hx : xa = f.2.1 := hr f s t rfl
      subst hx
      show ((pdec f v).map MEv.p).toList ++ _ = ((dRet f.1.val f.2.1 _).map MEv.p).toList ++ _
      rw [hRet]
      exact congrArg _ (ih f.2.1 pa (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h))

end Decode

/-! ## Simulating the mixed host -/

section Run

variable {Op V H X : Type} [DecidableEq H] [DecidableEq V] [DecidableEq X]

/-- **Simulate the mixed host** (store semantics) from the store `σ` along a trace: fresh
non-`bad` writes, accepts of defined handles, export calls and `parse` answers naming defined
non-`bad` handles; `none` when stuck, else whether `([v₀], x₀)` is related. -/
def mRunB (W : Writer Op X) (bad : H → Bool) (v₀ : V) (x₀ : X) :
    Env H X → List (MEv Op V H) → Option Bool
  | _, [] => some false
  | σ, .w (.write op args r) :: es =>
    match W.built σ op args with
    | some t =>
      if bad r = false ∧ σ r = none then mRunB W bad v₀ x₀ (Function.update σ r (some t)) es
      else none
    | none => none
  | σ, .w (.accept h) :: es =>
    match σ h with
    | some _ => mRunB W bad v₀ x₀ σ es
    | none => none
  | σ, .w .enter :: es => mRunB W bad v₀ x₀ σ es
  | σ, .p (.parse v h) :: es =>
    if bad h = false then
      match σ h with
      | some x => (mRunB W bad v₀ x₀ σ es).map fun b => decide (v = v₀ ∧ x = x₀) || b
      | none => none
    else none
  | _, _ :: _ => none

/-- A simulated trace has a run of the mixed host. -/
theorem run_of_mRunB (W : Writer Op X) {bad : H → Bool} {v₀ : V} {x₀ : X} {pol : Policy H}
    {ppol : PPolicy H} (hbad : ∀ r, pol.sentinel = some r → bad r = true)
    (hpbad : bad ppol.sentinel = true) :
    ∀ (t : List (MEv Op V H)) (σ : Env H X) (B : Set X) (ps : PState V), ps.phase = .live →
      ∀ b, mRunB W bad v₀ x₀ σ t = some b →
      ∃ s A, (mixed W pol ppol).Run ⟨⟨σ, B, .live⟩, ps⟩ t s A ∧ (b = true → ([v₀], x₀) ∈ A)
  | [], _, _, ps, _, b, h => by
    simp only [mRunB, Option.some.injEq] at h
    subst h
    exact ⟨_, ∅, .nil _, by simp⟩
  | .w (.write op args r) :: es, σ, B, ps, hps, b, h => by
    simp only [mRunB] at h
    split at h
    · rename_i t ht
      split at h
      · rename_i hfr
        obtain ⟨s, A, hr, hA⟩ := run_of_mRunB W hbad hpbad es _ (insert t B) ps hps b h
        have hne : pol.sentinel ≠ some r := fun hs => by
          have := hbad r hs
          rw [hfr.1] at this
          cases this
        have hstep : MStep W pol ppol none ⟨⟨σ, B, .live⟩, ps⟩ (.w (.write op args r))
            ⟨⟨Function.update σ r (some t), insert t B, .live⟩, ps⟩ (chaosPairs .live) :=
          .w (WStep.writeOk ht ⟨hne, Or.inl hfr.2⟩ fun _ h => by cases h)
        exact ⟨s, _, .cons hstep hr, fun hb => Or.inr (hA hb)⟩
      · cases h
    · cases h
  | .w (.accept h') :: es, σ, B, ps, hps, b, h => by
    simp only [mRunB] at h
    split at h
    · rename_i t ht
      obtain ⟨s, A, hr, hA⟩ := run_of_mRunB W hbad hpbad es σ B ps hps b h
      have hstep : MStep W pol ppol none ⟨⟨σ, B, .live⟩, ps⟩ (.w (.accept h'))
          ⟨⟨σ, B, .live⟩, ps⟩ (chaosPairs .live) := .w (WStep.acceptOk ht)
      exact ⟨s, _, .cons hstep hr, fun hb => Or.inr (hA hb)⟩
    · cases h
  | .w .enter :: es, σ, B, ps, hps, b, h => by
    simp only [mRunB] at h
    obtain ⟨s, A, hr, hA⟩ := run_of_mRunB W hbad hpbad es σ B ps hps b h
    have hstep : MStep W pol ppol none ⟨⟨σ, B, .live⟩, ps⟩ (.w .enter)
        ⟨⟨σ, B, .live⟩, ps⟩ (chaosPairs .live) := .w WStep.enter
    exact ⟨s, _, .cons hstep hr, fun hb => Or.inr (hA hb)⟩
  | .p (.parse v h') :: es, σ, B, ps, hps, b, h => by
    simp only [mRunB] at h
    split at h
    · rename_i hgood
      split at h
      · rename_i x hx
        obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.1 h
        obtain ⟨s, A, hr, hA⟩ := run_of_mRunB W hbad hpbad es σ B ps hps b' hb'
        have hne : h' ≠ ppol.sentinel := fun he => by
          rw [he, hpbad] at hgood
          cases hgood
        have hres : resolve ppol σ [v] h' = some {([v], x)} := by
          simp [resolve, hne, hx]
        have hstep : MStep W pol ppol none ⟨⟨σ, B, .live⟩, ps⟩ (.p (.parse v h'))
            ⟨⟨σ, B, .live⟩, ps⟩ {([v], x)} :=
          .p rfl (PStep.ret hps ⟨rfl, rfl, rfl⟩ hres)
        refine ⟨s, _, .cons hstep hr, fun hb => ?_⟩
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hb
        rcases hb with ⟨rfl, rfl⟩ | hb
        · exact Or.inl rfl
        · exact Or.inr (hA hb)
      · cases h
    · cases h
  | .w (.acceptErr _ _) :: _, _, _, _, _, _, h => by cases h
  | .w .acceptAll :: _, _, _, _, _, _, h => by cases h
  | .w (.acceptBatch _) :: _, _, _, _, _, _, h => by cases h
  | .p (.append _) :: _, _, _, _, _, _, h => by cases h
  | .p (.done _) :: _, _, _, _, _, _, h => by cases h
  | .p (.feed _) :: _, _, _, _, _, _, h => by cases h
  | .p (.finish _ _) :: _, _, _, _, _, _, h => by cases h
  | .p .reset :: _, _, _, _, _, _, h => by cases h

end Run

/-! ## Relations from a replay -/

/-- **A mixed pair from a replay** (store semantics). If the simulation `mRunB` of the decoded
replay with the export answer of the call of export `j` (candidate arguments `k`, script `sc`)
from the empty store relates `([v₀], x₀)`, with handles never `bad`, the writer sentinel (if
any) and the parsing sentinel `bad`, then the pair is in the module's mixed relation, for every
profile admitting the deterministic steps of the replay interpreter. The simulation is
decidable by kernel evaluation. -/
theorem mem_moduleMixedRel_of_replay {V : Type} [DecidableEq V] {m : Module}
    (hm : (instance? m).isSome = true) {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
    (wix : ConsWImports) (pix : ParseExports V) {pol : Policy (BitVec 32)}
    {ppol : PPolicy (BitVec 32)} {bad : BitVec 32 → Bool}
    (hbad : ∀ r, pol.sentinel = some r → bad r = true) (hpbad : bad ppol.sentinel = true)
    (sc : Script) (fuel n : Nat) (j : Fin (instOf m).exports.length) (k : Nat) {v₀ : V}
    {x₀ : SExp2 (BitVec 64)}
    (hrun : mRunB (consW (BitVec 64)) bad v₀ x₀ Env.empty
      (rdecM (consWAsk wix) (consWAns wix) (parseRet pix) [] []
        (replayExportR (instOf m) sc fuel n j k)) = some true) :
    ([v₀], x₀) ∈ moduleMixedRel P m wix pix pol ppol := by
  obtain ⟨mt, hI⟩ := isInstance_instOf hm
  obtain ⟨ms, hms, hmap⟩ := replayExportR_play hI.ok (sc := sc) (fuel := fuel) (n := n) hP j k
  obtain ⟨q, hp⟩ := ScalarInstance.mem_strategy_iff.1 hms
  have htr : mixedEvents (consWDecAsk wix) (consWDecAns wix) (parseDec pix) ms =
      rdecM (consWAsk wix) (consWAns wix) (parseRet pix) [] []
        (replayExportR (instOf m) sc fuel n j k) := by
    rw [← hmap]
    exact mixedEvents_path _ _ _ _ _ _ (consWDecAsk_eq wix) (consWDecAns_eq wix)
      (parseDec_eq pix) hp [] [] (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h)
  have hT : rdecM (consWAsk wix) (consWAns wix) (parseRet pix) [] []
      (replayExportR (instOf m) sc fuel n j k) ∈ moduleMixedTraces P m wix pix :=
    ⟨ms, hms, htr.symm⟩
  obtain ⟨s, A, hr, hA⟩ := run_of_mRunB (consW (BitVec 64)) (ppol := ppol) hbad hpbad _
    Env.empty ∅ PState.init rfl true hrun
  exact Set.mem_biUnion hT ⟨s, A, hr, hA rfl⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed
