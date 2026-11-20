module

public import Silmaril.Wasm.Game.HandleAccept.Defs
public import Silmaril.Wasm.Resource.Replay.Thms
public import Silmaril.Wasm.Verify.Check.Thms
public import Silmaril.Wasm.Game.Instantiate.Thms
public import Silmaril.Wasm.Game.Strategy.Thms

/-!
# Handle traces from replayed export calls, for any decoder

The generic form of `Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers` (cons readers): a replay of
an export call (`Silmaril.Wasm.Resource.replayExport`) is a play of the instance's strategy
(`replayExport_play`), so its decoded events are a handle trace of the module, for **any**
per-move decoder that reads only the import index, the arguments and the behaviour of an answer.

* `rdecG enter dAsk dAns pa rs`: the events of the recorded moves `rs`: export calls as
  `enter`, import calls and answers through the raw decoders `dAsk h args` and `dAns h args b`
  (answers decoded with the arguments of the pending call `pa`). A replay starts with the call
  of its export, so its decoded trace starts with `enter` (`some .enter` for handle APIs).
* `playEvents_pathG`: along a path, `playEvents enter decAsk decAns` is `rdecG enter dAsk dAns`
  of the recorded moves, when `decAsk`, `decAns` factor through `dAsk`, `dAns`.
* **`rdecG_mem_handleTraces`**: the decoded replay is a handle trace of the module, for every
  profile admitting the deterministic steps of the replay interpreter.

**Readers.** `revOkB okR okA` checks a reader event with Boolean checks of reads (`okR q a`) and
accepts (`okA h`), and passes export calls; `run_of_revOkB`: if the checks are sound in `ρ`, a
checked trace has a run of the reader host accepting every tree of an accepted handle;
**`mem_readerLang_of_replay`**.

**Writers (store semantics).** `wRunB W bad x σ t` simulates the writer host along `t` with
fresh, non-`bad` handles (`writeOk`), defined accepts (`acceptOk`) and export calls (`enter`):
`none` when stuck, else
whether `x` is accepted; `run_of_wRunB`, **`mem_writerLang_of_replay`**.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Replay

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Verify Silmaril.Wasm.Resource
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game.HandleAccept
  Silmaril.Accept Silmaril.Accept.Handle
open Silmaril.Wasm.Numerics (Profile)

/-! ## Decoding recorded moves -/

/-- The returned values of a behaviour. -/
def bValsG : Behaviour Val → Option (List Val)
  | .returns vs => some vs
  | _ => none

/-- The events of recorded moves: export calls as `enter`, imports through raw decoders; `pa`
are the arguments of the pending call. -/
def rdecG {Ev : Type} (enter : Option Ev) (dAsk : Nat → List Val → Option Ev)
    (dAns : Nat → List Val → Behaviour Val → Option Ev) : List Val → List RMove → List Ev
  | _, [] => []
  | _, .ask h a :: rs => (dAsk h a).toList ++ rdecG enter dAsk dAns a rs
  | pa, .ans h b :: rs => (dAns h pa b).toList ++ rdecG enter dAsk dAns pa rs
  | pa, .call _ _ :: rs => enter.toList ++ rdecG enter dAsk dAns pa rs
  | pa, .ret _ _ :: rs => rdecG enter dAsk dAns pa rs

variable {I : ScalarInstance} {Ev : Type}

/-- **Decoding a path** with decoders factoring through raw ones. -/
theorem playEvents_pathG (enter : Option Ev) (decAsk : I.E.Op → Option Ev)
    (decAns : (e : I.E.Op) → I.E.Ar e → Option Ev) (dAsk : Nat → List Val → Option Ev)
    (dAns : Nat → List Val → Behaviour Val → Option Ev)
    (hAsk : ∀ e, decAsk e = dAsk e.1.val e.2.1)
    (hAns : ∀ e v, decAns e v = dAns e.1.val e.2.1 (Answer.toBehaviour (ft := I.imports.get e.1) v))
    {P : Profile} :
    ∀ {q : I.HState} {ms : List (Move I.E I.F)} {q' : I.HState}, I.Path P q ms q' →
      ∀ pa : List Val, (∀ f s t e, q = .waiting f s t e → pa = e.2.1) →
      playEvents enter decAsk decAns ms = rdecG enter dAsk dAns pa (ms.map rmv) := by
  intro q ms q' hp
  induction hp with
  | nil => intro _ _; rfl
  | @cons q₀ q₁ q₂ m p htr _ ih =>
    intro pa hpa
    cases htr with
    | call s f =>
      exact congrArg (enter.toList ++ ·) (ih pa fun _ _ _ _ h => by cases h)
    | @ucall f s s' t t' h args e run callout op =>
      show (decAsk e).toList ++ _ = (dAsk e.1.val e.2.1).toList ++ _
      rw [hAsk]
      exact congrArg _ (ih e.2.1 fun _ _ _ _ h => by cases h; rfl)
    | @uret f s t e v =>
      have he : pa = e.2.1 := hpa f s t e rfl
      subst he
      show (decAns e v).toList ++ _ = (dAns e.1.val e.2.1 _).toList ++ _
      rw [hAns]
      exact congrArg _ (ih e.2.1 fun _ _ _ _ h => by cases h)
    | oret run final answer =>
      exact ih pa fun _ _ _ _ h => by cases h

/-- **A decoded replay is a handle trace** of the module, for every profile admitting the
deterministic steps of the replay interpreter. -/
theorem rdecG_mem_handleTraces {m : Module} (hm : (instance? m).isSome = true) {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
    (enter : Option Ev) (decAsk : (instOf m).E.Op → Option Ev)
    (decAns : (e : (instOf m).E.Op) → (instOf m).E.Ar e → Option Ev)
    (dAsk : Nat → List Val → Option Ev) (dAns : Nat → List Val → Behaviour Val → Option Ev)
    (hAsk : ∀ e, decAsk e = dAsk e.1.val e.2.1)
    (hAns : ∀ e v, decAns e v =
      dAns e.1.val e.2.1 (Answer.toBehaviour (ft := (instOf m).imports.get e.1) v))
    (sc : Script) (fuel n : Nat) (j : Fin (instOf m).exports.length) (k : Nat) :
    rdecG enter dAsk dAns [] (replayExport (instOf m) sc fuel n j k) ∈
      handleTraces ((instOf m).strategy P (instOf m).store) enter decAsk decAns := by
  obtain ⟨mt, hI⟩ := isInstance_instOf hm
  obtain ⟨ms, hms, hmap⟩ := replayExport_play hI.ok (sc := sc) (fuel := fuel) (n := n) hP j k
  obtain ⟨q, hp⟩ := ScalarInstance.mem_strategy_iff.1 hms
  refine ⟨ms, hms, ?_⟩
  rw [← hmap]
  exact (playEvents_pathG enter decAsk decAns dAsk dAns hAsk hAns hp [] fun _ _ _ _ h => by
    cases h).symm

/-! ## Readers -/

section Reader

variable {Q A H X : Type}

/-- A reader event passes the Boolean checks of reads `okR` and accepts `okA`. -/
def revOkB (okR : Q → A → Bool) (okA : H → Bool) : REv Q A H → Bool
  | .read q a => okR q a
  | .accept h => okA h
  | .enter => true

/-- The event accepts the handle `h`. -/
def revAcc [DecidableEq H] (h : H) : REv Q A H → Bool
  | .accept h' => decide (h' = h)
  | _ => false

/-- **A checked trace has a reader run** in `ρ` (every read and accept policy), accepting every
tree denoted by an accepted handle, when the checks are sound in `ρ`. -/
theorem run_of_revOkB [DecidableEq H] (R : Reader Q A H X) {ρ : Env H X} {okR : Q → A → Bool}
    {okA : H → Bool} (hR : ∀ q a, okR q a = true → R.valid ρ q ∧ R.ok ρ q a)
    (hA : ∀ h, okA h = true → (ρ h).isSome = true) {pol : OnBadRead Q A} {oa : OnInvalid} :
    ∀ t : List (REv Q A H), t.all (revOkB okR okA) = true →
      ∃ B, (reader R pol oa ρ).Run .live t .live B ∧
        ∀ h x, t.any (revAcc h) = true → ρ h = some x → x ∈ B
  | [], _ => ⟨∅, .nil _, fun _ _ h => by simp at h⟩
  | e :: t, hall => by
    simp only [List.all_cons, Bool.and_eq_true] at hall
    obtain ⟨B, hr, hB⟩ := run_of_revOkB R hR hA t hall.2
    cases e with
    | read q a =>
      obtain ⟨hv, hok⟩ := hR q a hall.1
      have hans : answers R pol ρ q = some {a | R.ok ρ q a} := by
        unfold answers
        split
        · rfl
        · contradiction
      refine ⟨∅ ∪ B, .cons (RStep.read hans hok) hr, fun h x hh hx => ?_⟩
      simp only [List.any_cons, revAcc, Bool.false_or] at hh
      exact Or.inr (hB h x hh hx)
    | accept h' =>
      obtain ⟨t₀, ht₀⟩ := Option.isSome_iff_exists.1 (hA h' hall.1)
      refine ⟨{t₀} ∪ B, .cons (RStep.acceptOk ht₀) hr, fun h x hh hx => ?_⟩
      simp only [List.any_cons, revAcc, Bool.or_eq_true, decide_eq_true_eq] at hh
      rcases hh with rfl | hh
      · rw [ht₀] at hx
        cases hx
        exact Or.inl rfl
      · exact Or.inr (hB h x hh hx)
    | enter =>
      refine ⟨∅ ∪ B, .cons RStep.enter hr, fun h x hh hx => ?_⟩
      simp only [List.any_cons, revAcc, Bool.false_or] at hh
      exact Or.inr (hB h x hh hx)

/-- **Reader acceptance from a replay**: if the decoded replay of the call of export `j`
(candidate arguments `k`, script `sc`) passes checks sound in `ρ ∈ Envs` and accepts the handle
`h` denoting `x`, then `x` is in the reader language of the module's handle traces, for every
profile admitting the deterministic steps of the replay interpreter. -/
theorem mem_readerLang_of_replay [DecidableEq H] {m : Module} (hm : (instance? m).isSome = true)
    {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
    (decAsk : (instOf m).E.Op → Option (REv Q A H))
    (decAns : (e : (instOf m).E.Op) → (instOf m).E.Ar e → Option (REv Q A H))
    (dAsk : Nat → List Val → Option (REv Q A H))
    (dAns : Nat → List Val → Behaviour Val → Option (REv Q A H))
    (hAsk : ∀ e, decAsk e = dAsk e.1.val e.2.1)
    (hAns : ∀ e v, decAns e v =
      dAns e.1.val e.2.1 (Answer.toBehaviour (ft := (instOf m).imports.get e.1) v))
    (R : Reader Q A H X) (pol : OnBadRead Q A) (oa : OnInvalid) {Envs : Set (Env H X)}
    {ρ : Env H X} (hρ : ρ ∈ Envs) {okR : Q → A → Bool} {okA : H → Bool}
    (hR : ∀ q a, okR q a = true → R.valid ρ q ∧ R.ok ρ q a)
    (hA : ∀ h, okA h = true → (ρ h).isSome = true)
    (sc : Script) (fuel n : Nat) (j : Fin (instOf m).exports.length) (k : Nat) (h : H) {x : X}
    (hx : ρ h = some x)
    (hall : (rdecG (some .enter) dAsk dAns [] (replayExport (instOf m) sc fuel n j k)).all
      (revOkB okR okA) = true)
    (hacc : (rdecG (some .enter) dAsk dAns [] (replayExport (instOf m) sc fuel n j k)).any
      (revAcc h) = true) :
    x ∈ readerLang R pol oa Envs
      (handleTraces ((instOf m).strategy P (instOf m).store) (some .enter) decAsk decAns) := by
  have hT := rdecG_mem_handleTraces hm hP (some .enter) decAsk decAns dAsk dAns hAsk hAns sc
    fuel n j k
  obtain ⟨B, hrun, hB⟩ := run_of_revOkB R hR hA (pol := pol) (oa := oa) _ hall
  exact Set.mem_iUnion.2 ⟨⟨ρ, hρ⟩, Set.mem_biUnion hT ⟨.live, B, hrun, hB h x hacc hx⟩⟩

end Reader

/-! ## Writers (store semantics) -/

section Writer

variable {Op H X : Type} [DecidableEq H] [DecidableEq X]

/-- **Simulate the writer host** from the store `σ` along a trace, with successful fresh writes
whose handles are not `bad` and accepts of defined handles: `none` when stuck, else whether `x`
is accepted. -/
def wRunB (W : Writer Op X) (bad : H → Bool) (x : X) : Env H X → List (WEv Op H) → Option Bool
  | _, [] => some false
  | σ, .write op args r :: es =>
    match W.built σ op args with
    | some t =>
      if bad r = false ∧ σ r = none then wRunB W bad x (Function.update σ r (some t)) es
      else none
    | none => none
  | σ, .accept h :: es =>
    match σ h with
    | some t => (wRunB W bad x σ es).map fun b => decide (t = x) || b
    | none => none
  | σ, .enter :: es => wRunB W bad x σ es
  | _, _ :: _ => none

/-- A simulated trace has a run of the writer host (store semantics, no fixed environment). -/
theorem run_of_wRunB (W : Writer Op X) {bad : H → Bool} {x : X} {pol : Policy H}
    (hbad : ∀ r, pol.sentinel = some r → bad r = true) :
    ∀ (t : List (WEv Op H)) (σ : Env H X) (B : Set X) (b : Bool), wRunB W bad x σ t = some b →
      ∃ s A, (writer W pol).Run ⟨σ, B, .live⟩ t s A ∧ (b = true → x ∈ A)
  | [], _, _, b, h => by
    simp only [wRunB, Option.some.injEq] at h
    subst h
    exact ⟨_, ∅, .nil _, by simp⟩
  | .write op args r :: es, σ, B, b, h => by
    simp only [wRunB] at h
    split at h
    · rename_i t ht
      split at h
      · rename_i hfr
        obtain ⟨s, A, hr, hA⟩ := run_of_wRunB W hbad es _ (insert t B) b h
        have hne : pol.sentinel ≠ some r := fun hs => by
          have := hbad r hs
          rw [hfr.1] at this
          cases this
        have hfresh : Fresh pol σ r t := ⟨hne, Or.inl hfr.2⟩
        refine ⟨s, ∅ ∪ A, .cons (WStep.writeOk ht hfresh fun _ h => by cases h) hr, ?_⟩
        intro hb
        exact Or.inr (hA hb)
      · cases h
    · cases h
  | .accept h' :: es, σ, B, b, h => by
    simp only [wRunB] at h
    split at h
    · rename_i t ht
      obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨s, A, hr, hA⟩ := run_of_wRunB W hbad es σ B b' hb'
      refine ⟨s, {t} ∪ A, .cons (WStep.acceptOk ht) hr, ?_⟩
      intro hb
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hb
      rcases hb with rfl | hb
      · exact Or.inl rfl
      · exact Or.inr (hA hb)
    · cases h
  | .enter :: es, σ, B, b, h => by
    simp only [wRunB] at h
    obtain ⟨s, A, hr, hA⟩ := run_of_wRunB W hbad es σ B b h
    exact ⟨s, ∅ ∪ A, .cons WStep.enter hr, fun hb => Or.inr (hA hb)⟩
  | .acceptErr _ _ :: _, _, _, _, h => by cases h
  | .acceptAll :: _, _, _, _, h => by cases h
  | .acceptBatch _ :: _, _, _, _, h => by cases h

/-- **Writer acceptance from a replay** (store semantics): if the simulation of the decoded
replay from the empty store accepts `x`, with handles that are never the policy's sentinel, then
`x` is in the writer language of the module's handle traces. -/
theorem mem_writerLang_of_replay {m : Module} (hm : (instance? m).isSome = true) {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
    (decAsk : (instOf m).E.Op → Option (WEv Op H))
    (decAns : (e : (instOf m).E.Op) → (instOf m).E.Ar e → Option (WEv Op H))
    (dAsk : Nat → List Val → Option (WEv Op H))
    (dAns : Nat → List Val → Behaviour Val → Option (WEv Op H))
    (hAsk : ∀ e, decAsk e = dAsk e.1.val e.2.1)
    (hAns : ∀ e v, decAns e v =
      dAns e.1.val e.2.1 (Answer.toBehaviour (ft := (instOf m).imports.get e.1) v))
    (W : Writer Op X) {pol : Policy H} {bad : H → Bool}
    (hbad : ∀ r, pol.sentinel = some r → bad r = true)
    (sc : Script) (fuel n : Nat) (j : Fin (instOf m).exports.length) (k : Nat) {x : X}
    (hrun : wRunB W bad x Env.empty
      (rdecG (some .enter) dAsk dAns [] (replayExport (instOf m) sc fuel n j k)) = some true) :
    x ∈ writerLang W pol
      (handleTraces ((instOf m).strategy P (instOf m).store) (some .enter) decAsk decAns) := by
  have hT := rdecG_mem_handleTraces hm hP (some .enter) decAsk decAns dAsk dAns hAsk hAns sc
    fuel n j k
  obtain ⟨s, A, hr, hA⟩ := run_of_wRunB W hbad _ Env.empty ∅ true hrun
  exact Set.mem_biUnion hT ⟨s, A, hr, hA rfl⟩

end Writer

end Silmaril.Proofs.Wasm.Game.HandleAccept.Replay
