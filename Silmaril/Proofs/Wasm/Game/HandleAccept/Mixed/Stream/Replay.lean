module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Replay
public import Silmaril.Wasm.Game.Adequacy.Thms

/-!
# Streaming relations from a replayed session of several export calls

`Silmaril.Proofs.Wasm.Game.HandleAccept.Parsing.replayExportR` replays **one** export call. A
streaming parser relates a tree to the values of **several** calls (`append(x₁)`, …, `done()`),
the store persisting between them, so this file replays a session:

* `replayFromRS`: `replayFromR` that also returns, when the call is answered, the final store and
  the next callout index; `replayFromRS_path`: it is a path ending, if answered, in the idle
  state of that store, whose environment answers are values;
* `replaySeqR I sc fuel n s k cs`: the export calls `cs` replayed in turn from the store `s`,
  each from the store the previous one left; `replaySeqR_play`: from the instantiated store of a
  well-formed instance, a play of the strategy (well-formedness persists along the session by
  `ScalarInstance.WellFormed.activation`);
* `sRunB W bad clears w₀ x₀ σ acc t`: simulates the mixed host (store semantics) along `t` with
  fresh writes, export calls, `append` and `done` answers naming defined non-`bad` handles,
  tracking the append buffer `acc`; `run_of_sRunB`;
* **`mem_moduleMixedRel_of_replaySeq`**: if the simulation of the decoded session from the
  empty store relates `(w₀, x₀)`, the pair is in the module's mixed relation, for every profile
  admitting the deterministic steps of the replay interpreter.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Spec Silmaril.Wasm.Verify
  Silmaril.Wasm.Validation Silmaril.Wasm.Resource Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Writers Silmaril.Wasm.Game.HandleAccept.Parsing
  Silmaril.Wasm.Game.HandleAccept.Mixed Silmaril.Accept Silmaril.Accept.Handle
  Silmaril.Accept.Parse Silmaril.Accept.Mixed Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Proofs.Wasm.Game.HandleAccept.Replay Silmaril.Proofs.Wasm.Game.HandleAccept.Parsing
  Silmaril.Proofs.Wasm.Game.HandleAccept.Writers Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed
open Silmaril.Wasm.Numerics (Profile)

/-! ## Replaying a session -/

/-- `replayFromR`, also returning the final store and the next callout index of an answered
call. -/
def replayFromRS (I : ScalarInstance) (sc : Script) (fuel j : Nat) (rts : List ScalarType) :
    Nat → Nat → Config Nat → List RMove × Option (Store Nat × Nat)
  | 0, _, _ => ([], none)
  | n + 1, k, c =>
    match runTo? fuel c with
    | none =>
      match valsOf? (Exec.runI refOracle fuel c).1.code with
      | some vs =>
        if typedB rts vs then ([.ret j (.returns vs)], some ((Exec.runI refOracle fuel c).1.store, k))
        else ([], none)
      | none => ([], none)
    | some (d, E, a, h, args) =>
      if argsOk I h args then
        if ansOk I d.store a h (sc k h args) then
          let r := replayFromRS I sc fuel j rts n (k + 1)
            ⟨d.store, d.frame, E.fill (vals (sc k h args))⟩
          (.ask h args :: .ans h (.returns (sc k h args)) :: r.1, r.2)
        else ([.ask h args], none)
      else ([], none)

/-- **The replay of a session**: the export calls `cs` in turn from the store `s`, the `k`-th
callout first. -/
def replaySeqR (I : ScalarInstance) (sc : Script) (fuel n : Nat) :
    Store Nat → Nat → List I.F.Op → List RMove
  | _, _, [] => []
  | s, k, f :: cs =>
    let r := replayFromRS I sc fuel f.1.val (I.exports.get f.1).results n k
      (invoke s (I.addr f.1) f.2.1)
    .call f.1.val f.2.1 :: r.1 ++
      match r.2 with
      | some (s', k') => replaySeqR I sc fuel n s' k' cs
      | none => []

variable {I : ScalarInstance}

theorem path_append {P : Profile} {q q' q'' : I.HState} {p₁ p₂ : List (Move I.E I.F)}
    (h₁ : I.Path P q p₁ q') (h₂ : I.Path P q' p₂ q'') : I.Path P q (p₁ ++ p₂) q'' := by
  induction h₁ with
  | nil => exact h₂
  | cons ht _ ih => exact .cons ht (ih h₂)

/-- **A replay with the export answer is a path** ending, if answered, in the idle state of the
returned store; its environment answers are values. -/
theorem replayFromRS_path {sc : Script} {fuel : Nat} {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
    (f : I.F.Op) : ∀ (n k : Nat) (s : Store Nat) (t : Thread) (ts : List CValType),
      ConfigOk (t.config s) ts → ∃ (ms : List (Move I.E I.F)) (q : I.HState),
        I.Path P (.running f s t) ms q ∧
          ms.map rmv = (replayFromRS I sc fuel f.1.val (I.exports.get f.1).results n k
            (t.config s)).1 ∧
          (∀ s' k', (replayFromRS I sc fuel f.1.val (I.exports.get f.1).results n k
            (t.config s)).2 = some (s', k') → q = .idle s') ∧
          ∀ m, I.PlayThrowsBelow m ms
  | 0, _, _, _, _, _ => ⟨[], _, .nil _, by simp [replayFromRS], by simp [replayFromRS],
      fun _ _ _ h => by simp at h⟩
  | n + 1, k, s, t, ts, hok => by
    cases hr : runTo? fuel (t.config s) with
    | none =>
      have hsteps := Exec.runI_steps_typed (o := refOracle) fuel hok
      obtain ⟨s', t', hreach, hcfg⟩ := reach_of_steps' (Relation.ReflTransGen.mono hP _ _ hsteps)
      cases hv : valsOf? (Exec.runI refOracle fuel (t.config s)).1.code with
      | none => exact ⟨[], _, .nil _, by simp [replayFromRS, hr, hv], by
          simp [replayFromRS, hr, hv], fun _ _ _ h => by simp at h⟩
      | some vs =>
        by_cases hty : typedB (I.exports.get f.1).results vs = true
        · have hfin : ResultAt s' t' (.values vs) := by
            unfold ResultAt
            rw [hcfg]
            exact valsOf?_eq hv
          have hans : Answer.ofResult? (I.exports.get f.1) (.values vs) =
              some (.values ⟨vs, typedB_sound hty⟩) := by
            rw [Answer.ofResult?]
            split
            · rfl
            · exact absurd (typedB_sound hty) ‹_›
          have hst : (Exec.runI refOracle fuel (t.config s)).1.store = s' := by
            rw [← hcfg, Thread.config_store]
          refine ⟨[.inr (.ans f (.values ⟨vs, typedB_sound hty⟩))], _,
            .cons (.oret hreach hfin hans) (.nil _), ?_, ?_, ?_⟩
          · simp only [replayFromRS, hr, hv, hty, ↓reduceIte, List.map_cons, List.map_nil]
            rfl
          · intro s'' k' h
            simp only [replayFromRS, hr, hv, hty, ↓reduceIte, Option.some.injEq,
              Prod.mk.injEq] at h
            rw [← h.1, hst]
          · intro _ e w hm
            simp at hm
        · have hty' : typedB (I.exports.get f.1).results vs = false := Bool.eq_false_iff.2 hty
          refine ⟨[], _, .nil _, ?_, ?_, fun _ _ _ h => by simp at h⟩
          · simp only [replayFromRS, hr, hv, hty', Bool.false_eq_true, ↓reduceIte, List.map_nil]
          · intro s'' k' h
            simp only [replayFromRS, hr, hv, hty', Bool.false_eq_true, ↓reduceIte,
              reduceCtorEq] at h
    | some x =>
      obtain ⟨⟨ds, df, dc⟩, E, a, h, args⟩ := x
      obtain ⟨y, hdec, hy⟩ := Option.map_eq_some_iff.1 hr
      simp only [Prod.mk.injEq] at hy
      obtain ⟨hrun, rfl⟩ := hy
      have hdec' : decompose? ds dc = some (E, a, h, args) := by rw [hrun] at hdec; exact hdec
      have hsteps := Exec.runI_steps_typed (o := refOracle) fuel hok
      have hokd := Exec.runI_typed (o := refOracle) fuel hok
      rw [hrun] at hsteps hokd
      obtain ⟨s', t', hreach, hcfg⟩ := reach_of_steps' (Relation.ReflTransGen.mono hP _ _ hsteps)
      have hs' : s' = ds := by rw [← Thread.config_store s' t', hcfg]
      subst hs'
      have hco : CalloutAt s' t' h args := ⟨E, a, by rw [hcfg]; exact hdec'⟩
      by_cases hargs : argsOk I h args = true
      · obtain ⟨hi, hty⟩ := argsOk_sound hargs
        obtain ⟨e, he, he1, he2⟩ := importOp?_of_typedB hi hty
        have hev : e.1.val = h := by rw [he1]
        have step₁ : I.Trans P (.running f s t) (.inl (.ask e)) (.waiting f s' t' e) :=
          .ucall hreach hco he
        by_cases hans : ansOk I s' a h (sc k h args) = true
        · simp only [ansOk, Bool.and_eq_true] at hans
          obtain ⟨⟨ft, hft, hvs⟩, ⟨ft', hft', hvs'⟩⟩ :=
            And.intro (resultsOk_sound hans.1) (resultsOk_sound hans.2)
          have hget : I.imports.get e.1 = ft := by
            rw [he1]
            exact (List.getElem?_eq_some_iff.1 hft).2
          let v : I.E.Ar e := .values ⟨sc k h args, hget ▸ hvs⟩
          have hres : resumeResult s' t' (Answer.toResult (ft := I.imports.get e.1) v) =
              .active df (E.fill (vals (sc k h args))) := by
            rw [resumeResult_of_decompose (by rw [hcfg]; exact hdec'), hcfg]
            rfl
          have hokr : ConfigOk ⟨s', df, E.fill (vals (sc k h args))⟩ ts :=
            fill_typed hokd hdec' hft' hvs'
          obtain ⟨ms, q, hp, hms, hq, hth⟩ := replayFromRS_path hP f n (k + 1) s'
            (.active df (E.fill (vals (sc k h args)))) ts hokr
          have step₂ : I.Trans P (.waiting f s' t' e) (.inl (.ans e v))
              (.running f s' (.active df (E.fill (vals (sc k h args))))) := by
            have := ScalarInstance.Trans.uret (P := P) (f := f) (s := s') (t := t') v
            rwa [hres] at this
          refine ⟨.inl (.ask e) :: .inl (.ans e v) :: ms, q, .cons step₁ (.cons step₂ hp), ?_,
            ?_, ?_⟩
          · simp only [replayFromRS, hr, hargs, ↓reduceIte, List.map_cons, hms, ansOk, hans.1,
              hans.2, Bool.and_self, rmv_ask, rmv_ans, hev, he2]
            rfl
          · intro s'' k' h2
            refine hq s'' k' ?_
            have h3 := h2
            simp only [replayFromRS, hr, hargs, ↓reduceIte, ansOk, hans.1, hans.2,
              Bool.and_self] at h3
            exact h3
          · intro m e' w hm
            simp only [List.mem_cons, Sum.inl.injEq, reduceCtorEq, false_or] at hm
            rcases hm with hm | hm
            · cases hm
              trivial
            · exact hth m e' w hm
        · refine ⟨[.inl (.ask e)], _, .cons step₁ (.nil _), ?_, ?_, ?_⟩
          · simp only [replayFromRS, hr, hargs, ↓reduceIte, hans, Bool.false_eq_true,
              List.map_cons, List.map_nil, rmv_ask, hev, he2]
          · intro s'' k' h2
            simp [replayFromRS, hr, hargs, hans] at h2
          · intro _ e' w hm
            simp at hm
      · exact ⟨[], _, .nil _, by simp [replayFromRS, hr, hargs], by
          simp [replayFromRS, hr, hargs], fun _ _ _ h => by simp at h⟩

/-- **A replayed session is a path** from the idle state of a well-formed store. -/
theorem replaySeqR_path {sc : Script} {fuel n : Nat} {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c') :
    ∀ (cs : List I.F.Op) (s : Store Nat) (k : Nat), I.WellFormed s →
      ∃ (ms : List (Move I.E I.F)) (q : I.HState), I.Path P (.idle s) ms q ∧
        ms.map rmv = replaySeqR I sc fuel n s k cs
  | [], _, _, _ => ⟨[], _, .nil _, rfl⟩
  | f :: cs, s, k, hw => by
    have hinv : InvokeOk s (I.addr f.1) f.2.1 :=
      invokeOk_of_wellFormed hw f.1 ⟨f.2.1, f.2.2⟩
    obtain ⟨-, -, rs, -, -, hok⟩ := invoke_ok hw.storeOk hinv
    obtain ⟨ms, q, hp, hms, hq, hth⟩ := replayFromRS_path (sc := sc) (fuel := fuel) hP f n k s
      (I.initThread f) _ hok
    have hp' : I.Path P (.idle s) (.inr (.ask f) :: ms) q := .cons (.call _ _) hp
    cases hr : (replayFromRS I sc fuel f.1.val (I.exports.get f.1).results n k
        (invoke s (I.addr f.1) f.2.1)).2 with
    | none =>
      refine ⟨_, q, hp', ?_⟩
      simp only [replaySeqR, hr, List.map_cons, List.append_nil]
      rw [show invoke s (I.addr f.1) f.2.1 = (I.initThread f).config s from rfl, ← hms]
      rfl
    | some r =>
      obtain ⟨s', k'⟩ := r
      obtain rfl := hq s' k' hr
      have hw' : I.WellFormed s' := (ScalarInstance.WellFormed.activation hw (fun e w hm => by
        simp only [List.mem_cons, reduceCtorEq, false_or] at hm
        exact hth _ e w hm) hp').1
      obtain ⟨ms', q', hp₂, hms'⟩ := replaySeqR_path hP cs s' k' hw'
      refine ⟨_, q', path_append hp' hp₂, ?_⟩
      simp only [replaySeqR, hr, List.map_cons, List.map_append, hms', List.cons_append]
      rw [show invoke s (I.addr f.1) f.2.1 = (I.initThread f).config s from rfl, ← hms]
      rfl

/-! ## Simulating the mixed host with an append buffer -/

section Run

variable {Op V H X : Type} [DecidableEq H] [DecidableEq V] [DecidableEq X]

/-- **Simulate the mixed host** (store semantics) from the store `σ` and the append buffer
`acc` along a trace: fresh non-`bad` writes, accepts of defined handles, export calls, `append`
answers, and `done` answers naming defined non-`bad` handles; `none` when stuck, else whether
`(w₀, x₀)` is related. -/
def sRunB (W : Writer Op X) (bad : H → Bool) (clears : Bool) (w₀ : List V) (x₀ : X) :
    Env H X → List V → List (MEv Op V H) → Option Bool
  | _, _, [] => some false
  | σ, acc, .w (.write op args r) :: es =>
    match W.built σ op args with
    | some t =>
      if bad r = false ∧ σ r = none then
        sRunB W bad clears w₀ x₀ (Function.update σ r (some t)) acc es
      else none
    | none => none
  | σ, acc, .w (.accept h) :: es =>
    match σ h with
    | some _ => sRunB W bad clears w₀ x₀ σ acc es
    | none => none
  | σ, acc, .w .enter :: es => sRunB W bad clears w₀ x₀ σ acc es
  | σ, acc, .p (.append v) :: es => sRunB W bad clears w₀ x₀ σ (acc ++ [v]) es
  | σ, acc, .p (.done h) :: es =>
    if bad h = false then
      match σ h with
      | some x => (sRunB W bad clears w₀ x₀ σ (if clears then [] else acc) es).map
          fun b => decide (acc = w₀ ∧ x = x₀) || b
      | none => none
    else none
  | _, _, _ :: _ => none

/-- A simulated trace has a run of the mixed host. -/
theorem run_of_sRunB (W : Writer Op X) {bad : H → Bool} {w₀ : List V} {x₀ : X}
    {pol : Policy H} {ppol : PPolicy H} (hbad : ∀ r, pol.sentinel = some r → bad r = true)
    (hpbad : bad ppol.sentinel = true) :
    ∀ (t : List (MEv Op V H)) (σ : Env H X) (B : Set X) (acc buf : List V) (b : Bool),
      sRunB W bad ppol.doneClears w₀ x₀ σ acc t = some b →
      ∃ s A, (mixed W pol ppol).Run ⟨⟨σ, B, .live⟩, ⟨acc, buf, .live⟩⟩ t s A ∧
        (b = true → (w₀, x₀) ∈ A)
  | [], _, _, _, _, b, h => by
    simp only [sRunB, Option.some.injEq] at h
    subst h
    exact ⟨_, ∅, .nil _, by simp⟩
  | .w (.write op args r) :: es, σ, B, acc, buf, b, h => by
    simp only [sRunB] at h
    split at h
    · rename_i t ht
      split at h
      · rename_i hfr
        obtain ⟨s, A, hr, hA⟩ := run_of_sRunB W hbad hpbad es _ (insert t B) acc buf b h
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
    simp only [sRunB] at h
    split at h
    · rename_i t ht
      obtain ⟨s, A, hr, hA⟩ := run_of_sRunB W hbad hpbad es σ B acc buf b h
      have hstep : MStep W pol ppol none ⟨⟨σ, B, .live⟩, ⟨acc, buf, .live⟩⟩ (.w (.accept h'))
          ⟨⟨σ, B, .live⟩, ⟨acc, buf, .live⟩⟩ (chaosPairs .live) := .w (WStep.acceptOk ht)
      exact ⟨s, _, .cons hstep hr, fun hb => Or.inr (hA hb)⟩
    · cases h
  | .w .enter :: es, σ, B, acc, buf, b, h => by
    simp only [sRunB] at h
    obtain ⟨s, A, hr, hA⟩ := run_of_sRunB W hbad hpbad es σ B acc buf b h
    have hstep : MStep W pol ppol none ⟨⟨σ, B, .live⟩, ⟨acc, buf, .live⟩⟩ (.w .enter)
        ⟨⟨σ, B, .live⟩, ⟨acc, buf, .live⟩⟩ (chaosPairs .live) := .w WStep.enter
    exact ⟨s, _, .cons hstep hr, fun hb => Or.inr (hA hb)⟩
  | .p (.append v) :: es, σ, B, acc, buf, b, h => by
    simp only [sRunB] at h
    obtain ⟨s, A, hr, hA⟩ := run_of_sRunB W hbad hpbad es σ B (acc ++ [v]) buf b h
    have hstep : MStep W pol ppol none ⟨⟨σ, B, .live⟩, ⟨acc, buf, .live⟩⟩ (.p (.append v))
        ⟨⟨σ, B, .live⟩, ⟨acc ++ [v], buf, .live⟩⟩ ∅ := .p rfl (PStep.append v)
    exact ⟨s, _, .cons hstep hr, fun hb => Or.inr (hA hb)⟩
  | .p (.done h') :: es, σ, B, acc, buf, b, h => by
    simp only [sRunB] at h
    split at h
    · rename_i hgood
      split at h
      · rename_i x hx
        obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.1 h
        obtain ⟨s, A, hr, hA⟩ := run_of_sRunB W hbad hpbad es σ B _ buf b' hb'
        have hne : h' ≠ ppol.sentinel := fun he => by
          rw [he, hpbad] at hgood
          cases hgood
        have hres : resolve ppol σ acc h' = some {(acc, x)} := by
          simp [resolve, hne, hx]
        have hstep : MStep W pol ppol none ⟨⟨σ, B, .live⟩, ⟨acc, buf, .live⟩⟩ (.p (.done h'))
            ⟨⟨σ, B, .live⟩, ⟨if ppol.doneClears then [] else acc, buf, .live⟩⟩ {(acc, x)} :=
          .p rfl (PStep.ret rfl ⟨rfl, rfl, rfl⟩ hres)
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
  | .p (.parse _ _) :: _, _, _, _, _, _, h => by cases h
  | .p (.feed _) :: _, _, _, _, _, _, h => by cases h
  | .p (.finish _ _) :: _, _, _, _, _, _, h => by cases h
  | .p .reset :: _, _, _, _, _, _, h => by cases h

end Run

/-! ## Relations from a replayed session -/

/-- **A mixed pair from a replayed session** (store semantics). If the simulation `sRunB` of the
decoded replay of the export calls `cs` from the empty store and the empty buffer relates
`(w₀, x₀)`, with handles never `bad`, the writer sentinel (if any) and the parsing sentinel
`bad`, then the pair is in the module's mixed relation, for every profile admitting the
deterministic steps of the replay interpreter. The simulation is decidable by kernel
evaluation. -/
theorem mem_moduleMixedRel_of_replaySeq {V : Type} [DecidableEq V] {m : Module}
    (hm : (instance? m).isSome = true) {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
    (wix : ConsWImports) (pix : ParseExports V) {pol : Policy (BitVec 32)}
    {ppol : PPolicy (BitVec 32)} {bad : BitVec 32 → Bool}
    (hbad : ∀ r, pol.sentinel = some r → bad r = true) (hpbad : bad ppol.sentinel = true)
    (sc : Script) (fuel n : Nat) (cs : List (instOf m).F.Op) {w₀ : List V}
    {x₀ : SExp2 (BitVec 64)}
    (hrun : sRunB (consW (BitVec 64)) bad ppol.doneClears w₀ x₀ Env.empty []
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
  obtain ⟨s, A, hr, hA⟩ := run_of_sRunB (consW (BitVec 64)) (ppol := ppol) hbad hpbad _
    Env.empty ∅ [] [] true hrun
  exact Set.mem_biUnion hT ⟨s, A, hr, hA rfl⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream
