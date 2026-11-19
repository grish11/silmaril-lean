module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.Ring
public import Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.Replay
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.LiveRun
public import Silmaril.Wasm.Logic.Tactic.Defs

/-!
# `chunkRingN cap` relates `([7], (7))` and `([8], (8))`: a play built forwards

Kernel replay of `chunkRing` does not finish: its 64 KiB memory is a list in the kernel, and
after one `i64.store` (`ByteArray.copySlice`, rebuilt element by element by `Array.push`) the
next bounds check computes its length quadratically. The play is built here **forwards, with
the store symbolic**: the Core runs between callouts are composed from Core `Step` rules, the
straight-line parts evaluated by `Silmaril.Wasm.Logic.Core.exec_sound`, and memory accesses
reasoned about with `Memory.load`/`Memory.store` lemmas
(`Silmaril.Wasm.Logic.Core.load_store_same`, `load_store_disjoint`), never evaluating the page.

* Paths from runs: `path_ret` (a run to an export result), `path_callout` (a run to a callout,
  the scripted answer, and the rest of the path), `path_call` (an export call);
  `mem_moduleMixedRel_of_path`: a path whose recorded moves decode, by `cRunB`, to a related
  pair gives a pair of the mixed relation.
* Runs of the two exports from any store with the ring layout (`feed_run`; `fin_run₁` …
  `fin_run₄`: `finish(1)` with at least one value buffered, up to `nil()`, `word(v)`,
  `cons(a, r)` and the return), for every capacity: the straight-line pieces (`ex_f2`, `ex_l2`,
  `ex_t`) take any non-zero `rem_u` constant.
* **`chunkRingN_relates_7`, `chunkRingN_relates_8`**: the session `feed(7)`, `feed(8)`,
  `finish(1)`, `finish(1)` (the `k`-th callout answering the handle `k + 1`), for every capacity
  `2 ≤ cap ≤ 8192` (`ring_session`: the slot addresses `0` and `8` are computed from `cap`
  symbolically, `mod_small`), every profile, writer policy with sentinel (if any) `0`, and
  parsing policy with sentinel `0`.
* **`chunkRingN_relates_7_one`**: the one-value session `feed(7)`, `finish(1)`
  (`ring_session1`, the same runs), for every capacity `1 ≤ cap ≤ 8192`, the one-slot buffer
  included.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.RingLive

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Spec Silmaril.Wasm.Verify Silmaril.Wasm.Resource
  Silmaril.Formats Silmaril.Formats.Api Silmaril.Accept Silmaril.Accept.Handle
  Silmaril.Accept.Parse Silmaril.Accept.Mixed Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Writers Silmaril.Wasm.Game.HandleAccept.Writers.Builders
  Silmaril.Wasm.Game.HandleAccept.Parsing Silmaril.Wasm.Game.HandleAccept.Mixed
  Silmaril.Wasm.Game.HandleAccept.Mixed.Stream Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk
  Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Ring
  Silmaril.Proofs.Wasm.Game.HandleAccept.Replay Silmaril.Proofs.Wasm.Game.HandleAccept.Parsing
  Silmaril.Proofs.Wasm.Game.HandleAccept.Writers Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.Ring
  Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.TwoWords
open Silmaril.Wasm.Logic.Core (exec exec1 popInt popV localVal? exec_sound Steps.label
  Steps.frame Steps.append Steps.ctx Step.ctx exec_cons exec_nil toOption_except_ok ofNat_i32_width
  ofNat_i64_width intBinOp_i32_add intBinOp_i32_mul intBinOp_i32_sub)

/-! ## Paths from runs -/

section Paths

variable {I : ScalarInstance} {P : Profile}

/-- A host-free run to the values `vs` answers the export call. -/
theorem path_ret {f : I.F.Op} {s s' : Store Nat} {t : Thread} {F' : Frame} {vs : List Val}
    (hs : Steps P Det.noHost (t.config s) ⟨s', F', vals vs⟩)
    (hty : typedB (I.exports.get f.1).results vs = true) :
    ∃ ms, I.Path P (.running f s t) ms (.idle s') ∧
      ms.map rmv = [.ret f.1.val (.returns vs)] := by
  obtain ⟨s'', t', hreach, hcfg⟩ := reach_of_steps' hs
  have hs' : s'' = s' := by rw [← Thread.config_store s'' t', hcfg]
  subst hs'
  have hfin : ResultAt s'' t' (.values vs) := by
    unfold ResultAt
    rw [hcfg]
    rfl
  have hans : Answer.ofResult? (I.exports.get f.1) (.values vs) =
      some (.values ⟨vs, typedB_sound hty⟩) := by
    rw [Answer.ofResult?]
    split
    · rfl
    · exact absurd (typedB_sound hty) ‹_›
  exact ⟨[.inr (.ans f (.values ⟨vs, typedB_sound hty⟩))], .cons (.oret hreach hfin hans)
    (.nil _), rfl⟩

/-- A host-free run to a callout, the answer `vs`, and a path from the resumed thread. -/
theorem path_callout {f : I.F.Op} {s s' : Store Nat} {t : Thread} {F' : Frame}
    {code : List Admin} {E : Ctx} {a h : Nat} {args vs : List Val}
    (hs : Steps P Det.noHost (t.config s) ⟨s', F', code⟩)
    (hd : decompose? s' code = some (E, a, h, args)) (hi : h < I.imports.length)
    (hargs : typedB (I.imports.get ⟨h, hi⟩).params args = true)
    (hvs : typedB (I.imports.get ⟨h, hi⟩).results vs = true)
    {ms : List (Move I.E I.F)} {q : I.HState} {R : List RMove}
    (hrest : I.Path P (.running f s' (.active F' (E.fill (vals vs)))) ms q)
    (hR : ms.map rmv = R) :
    ∃ ms', I.Path P (.running f s t) ms' q ∧ ms'.map rmv = .ask h args :: .ans h (.returns vs) :: R
    := by
  obtain ⟨s'', t', hreach, hcfg⟩ := reach_of_steps' hs
  have hs' : s'' = s' := by rw [← Thread.config_store s'' t', hcfg]
  subst hs'
  have hco : CalloutAt s'' t' h args := ⟨E, a, by rw [hcfg]; exact hd⟩
  obtain ⟨e, he, he1, he2⟩ := importOp?_of_typedB hi hargs
  have step₁ : I.Trans P (.running f s t) (.inl (.ask e)) (.waiting f s'' t' e) :=
    .ucall hreach hco he
  have hget : I.imports.get e.1 = I.imports.get ⟨h, hi⟩ := by rw [he1]
  let v : I.E.Ar e := .values ⟨vs, hget ▸ typedB_sound hvs⟩
  have hres : resumeResult s'' t' (Answer.toResult (ft := I.imports.get e.1) v) =
      .active F' (E.fill (vals vs)) := by
    rw [resumeResult_of_decompose (by rw [hcfg]; exact hd), hcfg]
    rfl
  have step₂ : I.Trans P (.waiting f s'' t' e) (.inl (.ans e v))
      (.running f s'' (.active F' (E.fill (vals vs)))) := by
    have := ScalarInstance.Trans.uret (P := P) (f := f) (s := s'') (t := t') v
    rwa [hres] at this
  refine ⟨.inl (.ask e) :: .inl (.ans e v) :: ms, .cons step₁ (.cons step₂ hrest), ?_⟩
  simp only [List.map_cons, rmv_ask, rmv_ans, hR]
  have h1 : e.1.val = h := by rw [he1]
  rw [h1, he2]
  rfl

/-- An export call, then a path from the pending invocation. -/
theorem path_call {f : I.F.Op} {s : Store Nat} {ms : List (Move I.E I.F)} {q : I.HState}
    {R : List RMove} (hp : I.Path P (.running f s (I.initThread f)) ms q) (hR : ms.map rmv = R) :
    ∃ ms', I.Path P (.idle s) ms' q ∧ ms'.map rmv = .call f.1.val f.2.1 :: R :=
  ⟨_, .cons (.call s f) hp, by simp only [List.map_cons, hR]; rfl⟩

/-- `path_callout` with the rest of the path given as an existential. -/
theorem path_callout' {f : I.F.Op} {s s' : Store Nat} {t : Thread} {F' : Frame}
    {code : List Admin} {E : Ctx} {a h : Nat} {args vs : List Val}
    (hs : Steps P Det.noHost (t.config s) ⟨s', F', code⟩)
    (hd : decompose? s' code = some (E, a, h, args)) (hi : h < I.imports.length)
    (hargs : typedB (I.imports.get ⟨h, hi⟩).params args = true)
    (hvs : typedB (I.imports.get ⟨h, hi⟩).results vs = true) {q : I.HState} {R : List RMove}
    (hrest : ∃ ms, I.Path P (.running f s' (.active F' (E.fill (vals vs)))) ms q ∧
      ms.map rmv = R) :
    ∃ ms, I.Path P (.running f s t) ms q ∧ ms.map rmv = .ask h args :: .ans h (.returns vs) :: R :=
  have ⟨_, hp, hR⟩ := hrest
  path_callout hs hd hi hargs hvs hp hR

/-- `path_call` with the path given as an existential. -/
theorem path_call' {f : I.F.Op} {s : Store Nat} {q : I.HState} {R : List RMove}
    (hp : ∃ ms, I.Path P (.running f s (I.initThread f)) ms q ∧ ms.map rmv = R) :
    ∃ ms, I.Path P (.idle s) ms q ∧ ms.map rmv = .call f.1.val f.2.1 :: R :=
  have ⟨_, hp, hR⟩ := hp
  path_call hp hR

/-- Paths compose. -/
theorem path_trans {q q' q'' : I.HState} {R₁ R₂ : List RMove}
    (h₁ : ∃ ms, I.Path P q ms q' ∧ ms.map rmv = R₁)
    (h₂ : ∃ ms, I.Path P q' ms q'' ∧ ms.map rmv = R₂) :
    ∃ ms, I.Path P q ms q'' ∧ ms.map rmv = R₁ ++ R₂ := by
  obtain ⟨ms₁, hp₁, hm₁⟩ := h₁
  obtain ⟨ms₂, hp₂, hm₂⟩ := h₂
  exact ⟨ms₁ ++ ms₂, path_append hp₁ hp₂, by rw [List.map_append, hm₁, hm₂]⟩

end Paths

/-- **A mixed pair from a path** (store semantics): if the recorded moves `R` of a play from the
instantiated store decode, simulated by `cRunB`, to a relation of `(w₀, x₀)`, the pair is in the
module's mixed relation. -/
theorem mem_moduleMixedRel_of_path {V : Type} [DecidableEq V] {m : Module} {P : Profile}
    (wix : ConsWImports) (pix : ParseExports V) {pol : Policy (BitVec 32)}
    {ppol : PPolicy (BitVec 32)} {bad : BitVec 32 → Bool}
    (hbad : ∀ r, pol.sentinel = some r → bad r = true) (hpbad : bad ppol.sentinel = true)
    {R : List RMove} {w₀ : List V} {x₀ : SExp2 (BitVec 64)}
    (hp : ∃ ms q, (instOf m).Path P (.idle (instOf m).store) ms q ∧ ms.map rmv = R)
    (hrun : cRunB (consW (BitVec 64)) bad w₀ x₀ Env.empty []
      (rdecM (consWAsk wix) (consWAns wix) (parseRet pix) [] [] R) = some true) :
    (w₀, x₀) ∈ moduleMixedRel P m wix pix pol ppol := by
  obtain ⟨ms, q, hp, hmap⟩ := hp
  have hms : ms ∈ (instOf m).strategy P (instOf m).store :=
    ScalarInstance.mem_strategy_iff.2 ⟨q, hp⟩
  have htr : mixedEvents (consWDecAsk wix) (consWDecAns wix) (parseDec pix) ms =
      rdecM (consWAsk wix) (consWAns wix) (parseRet pix) [] [] R := by
    rw [← hmap]
    exact mixedEvents_path _ _ _ _ _ _ (consWDecAsk_eq wix) (consWDecAns_eq wix)
      (parseDec_eq pix) hp [] [] (fun _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h)
  have hT : rdecM (consWAsk wix) (consWAns wix) (parseRet pix) [] [] R ∈
      moduleMixedTraces P m wix pix := ⟨ms, hms, htr.symm⟩
  obtain ⟨s, A, hr, hA⟩ := run_of_cRunB (consW (BitVec 64)) (ppol := ppol) hbad hpbad _
    Env.empty ∅ [] [] true hrun
  exact Set.mem_biUnion hT ⟨s, A, hr, hA rfl⟩


/-! ## Straight-line runs -/

@[simp] theorem idx_toNat0 {k : IndexKind} : (⟨0⟩ : Idx k).toNat = 0 := rfl
@[simp] theorem idx_toNat1 {k : IndexKind} : (⟨1⟩ : Idx k).toNat = 1 := rfl
@[simp] theorem idx_toNat2 {k : IndexKind} : (⟨2⟩ : Idx k).toNat = 2 := rfl

theorem global?_0 {s : Store Nat} {F : Frame} (hmg : F.module.globals = [0, 1])
    {g : GlobalInst} (hg : s.globals[0]? = some g) : s.global? F ⟨0⟩ = some (0, g) := by
  simp [Store.global?, hmg, hg]

theorem global?_1 {s : Store Nat} {F : Frame} (hmg : F.module.globals = [0, 1])
    {g : GlobalInst} (hg : s.globals[1]? = some g) : s.global? F ⟨1⟩ = some (1, g) := by
  simp [Store.global?, hmg, hg]

section Exec

variable {s : Store Nat} {M : ModuleInst} {c : BitVec 32} (hmg : M.globals = [0, 1])
  (hmm : M.mems = [0])
  {g0 g1 : GlobalInst} {st cnt : BitVec 32} (hg0 : s.globals[0]? = some g0)
  (hg1 : s.globals[1]? = some g1) (hv0 : g0.value = .i32 st) (hv1 : g1.value = .i32 cnt)
include hmg

/-- The guard of `feed`. -/
theorem ex_f1 (ls : List (Option Val)) (hg1 : s.globals[1]? = some g1) (hv1 : g1.value = .i32 cnt) :
    exec s ⟨ls, M⟩ [] [.globalGet ⟨1⟩, .intConst .i32 c, .intRelOp .i32 .eq] =
      some (s, ⟨ls, M⟩, [.i32 (bool32 (cnt == c))]) := by
  simp [exec, exec1, popInt, Store.global?, hmg, hg1, hv1, Val.i32]

include hmm in
/-- The store and count update of `feed`. -/
theorem ex_f2 (hc : c ≠ 0) {x : BitVec 64} (hg0 : s.globals[0]? = some g0) (hg1 : s.globals[1]? = some g1)
    (hv0 : g0.value = .i32 st) (hv1 : g1.value = .i32 cnt)
    {mi : MemInst} (hmi : s.mems[0]? = some mi) {b : ByteArray}
    (hb : Memory.store mi.bytes ((st + cnt) % c * 8).toNat (count := 8) x = some b) :
    exec s ⟨[some (.i64 x)], M⟩ [] [.globalGet ⟨0⟩, .globalGet ⟨1⟩, .intBinOp .i32 .add,
      .intConst .i32 c, .intBinOp .i32 (.rem .unsigned), .intConst .i32 8, .intBinOp .i32 .mul,
      .localGet ⟨0⟩, .intStore .i64 none ⟨0⟩ ⟨0, 0⟩, .globalGet ⟨1⟩, .intConst .i32 1,
      .intBinOp .i32 .add, .globalSet ⟨1⟩] =
      some ((s.setMem 0 { mi with bytes := b }).setGlobal 1 (.i32 (cnt + 1)),
        ⟨[some (.i64 x)], M⟩, []) := by
  have hb' : Memory.store mi.bytes (effAddr ((st + cnt) % c * 8#32 : BitVec 32).toNat ⟨0, 0⟩)
      (count := IntType.i64.width / 8) (x.setWidth _) = some b := hb
  simp only [exec_cons, exec_nil, exec1, popInt, popV, localVal?, Frame.local?, Val.i32, Val.i64,
    Option.map_some, Option.bind_some, BitVec.ofNat_eq_ofNat, ofNat_i32_width, intBinOp_i32_add,
    intBinOp_i32_mul, remu_ok hc, global?_0 (F := ⟨_, M⟩) hmg hg0, global?_1 (F := ⟨_, M⟩) hmg hg1, hv0,
    hv1, Store.mem?, hmm, hmi, List.getElem?_cons_zero, idx_toNat0, Option.pure_def,
    Option.bind_eq_bind]
  erw [hb']
  simp [Store.setMem, Store.global?, hmg, hg1, hv1, Val.i32]

/-- The guards of `finish`: `n > count`. -/
theorem ex_g1 {a b : Val} {k : BitVec 32} (hg1 : s.globals[1]? = some g1)
    (hv1 : g1.value = .i32 cnt) :
    exec s ⟨[some (.i32 k), some a, some b], M⟩ [] [.localGet ⟨0⟩, .globalGet ⟨1⟩,
      .intRelOp .i32 (.gt .unsigned)] =
      some (s, ⟨[some (.i32 k), some a, some b], M⟩, [.i32 (bool32 (decide (k.toNat > cnt.toNat)))])
    := by
  simp [exec, exec1, popInt, localVal?, Frame.local?, Store.global?, hmg, hg1, hv1, Val.i32]

omit hmg in
/-- `n = 0`. -/
theorem ex_g2 {a b : Val} {k : BitVec 32} :
    exec s ⟨[some (.i32 k), some a, some b], M⟩ [] [.localGet ⟨0⟩, .intTestOp .i32 .eqz] =
      some (s, ⟨[some (.i32 k), some a, some b], M⟩, [.i32 (bool32 (k == 0))]) := by
  simp [exec, exec1, popInt, localVal?, Frame.local?, Val.i32, ofNat_i32_width]
  rfl

omit hmg in
/-- The setup of `finish`'s loop. -/
theorem ex_g3 {a b : Val} {k r : BitVec 32} :
    exec s ⟨[some (.i32 k), some a, some b], M⟩ [.i32 r] [.localSet ⟨2⟩, .localGet ⟨0⟩,
      .localSet ⟨1⟩] =
      some (s, ⟨[some (.i32 k), some (.i32 k), some (.i32 r)], M⟩, []) := by
  simp [exec, exec1, popV, localVal?, Frame.local?, Frame.setLocal, Val.i32]

omit hmg in
/-- `i = 0` in the loop. -/
theorem ex_l1 {k i r : BitVec 32} :
    exec s ⟨[some (.i32 k), some (.i32 i), some (.i32 r)], M⟩ [] [.localGet ⟨1⟩,
      .intTestOp .i32 .eqz] =
      some (s, ⟨[some (.i32 k), some (.i32 i), some (.i32 r)], M⟩, [.i32 (bool32 (i == 0))]) := by
  simp [exec, exec1, popInt, localVal?, Frame.local?, Val.i32, ofNat_i32_width]
  rfl

include hmm in
/-- The load of the value `i - 1` in the loop. -/
theorem ex_l2 (hc : c ≠ 0) {k i r m : BitVec 32} (hg0 : s.globals[0]? = some g0) (hv0 : g0.value = .i32 st)
    {mi : MemInst} (hmi : s.mems[0]? = some mi) {v : BitVec 64}
    (hl : Memory.load mi.bytes
      (effAddr ((st + (i + m)) % c * 8#32 : BitVec 32).toNat ⟨0, 0⟩)
      (IntType.i64.width / 8) = some v) :
    exec s ⟨[some (.i32 k), some (.i32 i), some (.i32 r)], M⟩ [] [.localGet ⟨1⟩,
      .intConst .i32 (m), .intBinOp .i32 .add, .localSet ⟨1⟩, .globalGet ⟨0⟩,
      .localGet ⟨1⟩, .intBinOp .i32 .add, .intConst .i32 c, .intBinOp .i32 (.rem .unsigned),
      .intConst .i32 8, .intBinOp .i32 .mul, .intLoad .i64 none ⟨0⟩ ⟨0, 0⟩] =
      some (s, ⟨[some (.i32 k), some (.i32 (i + m)), some (.i32 r)], M⟩,
        [.i64 v]) := by
  simp only [exec_cons, exec_nil, exec1, popInt, popV, localVal?, Frame.local?, Frame.setLocal,
    Val.i32, Val.i64, Option.map_some, Option.bind_some, BitVec.ofNat_eq_ofNat, ofNat_i32_width,
    intBinOp_i32_add, intBinOp_i32_mul, remu_ok hc, global?_0 (F := ⟨_, M⟩) hmg hg0, hv0, Store.mem?,
    hmm,
    hmi, List.getElem?_cons_zero, List.getElem?_cons_succ, List.set_cons_zero, List.set_cons_succ,
    List.length_cons, List.length_nil, idx_toNat0, idx_toNat1, Option.pure_def, Option.bind_eq_bind,
    Nat.one_lt_succ_succ, ↓reduceIte]
  erw [hl]
  rfl

omit hmg in
/-- The accumulator below the word handle. -/
theorem ex_r1 {k i r a : BitVec 32} :
    exec s ⟨[some (.i32 k), some (.i32 i), some (.i32 r)], M⟩ [.i32 a] [.localGet ⟨2⟩] =
      some (s, ⟨[some (.i32 k), some (.i32 i), some (.i32 r)], M⟩, [.i32 r, .i32 a]) := by
  simp [exec, exec1, localVal?, Frame.local?]

omit hmg in
/-- The new accumulator. -/
theorem ex_r2 {k i r c : BitVec 32} :
    exec s ⟨[some (.i32 k), some (.i32 i), some (.i32 r)], M⟩ [.i32 c] [.localSet ⟨2⟩] =
      some (s, ⟨[some (.i32 k), some (.i32 i), some (.i32 c)], M⟩, []) := by
  simp [exec, exec1, popV, Frame.setLocal]

/-- Dropping the consumed values. -/
theorem ex_t (hc : c ≠ 0) {k i r : BitVec 32} (hg0 : s.globals[0]? = some g0) (hg1 : s.globals[1]? = some g1)
    (hv0 : g0.value = .i32 st) (hv1 : g1.value = .i32 cnt) :
    exec s ⟨[some (.i32 k), some (.i32 i), some (.i32 r)], M⟩ [] [.globalGet ⟨0⟩, .localGet ⟨0⟩,
      .intBinOp .i32 .add, .intConst .i32 c, .intBinOp .i32 (.rem .unsigned), .globalSet ⟨0⟩,
      .globalGet ⟨1⟩, .localGet ⟨0⟩, .intBinOp .i32 .sub, .globalSet ⟨1⟩, .localGet ⟨0⟩,
      .localGet ⟨2⟩] =
      some ((s.setGlobal 0 (.i32 ((st + k) % c))).setGlobal 1 (.i32 (cnt - k)),
        ⟨[some (.i32 k), some (.i32 i), some (.i32 r)], M⟩, [.i32 r, .i32 k]) := by
  simp [exec, exec1, popInt, popV, localVal?, Frame.local?, Store.global?, Store.setGlobal, hmg,
    hg0, hg1, hv0, hv1, Val.i32, remu_ok hc]

end Exec

/-! ## Runs in nested labels -/

/-- Nested labels, outermost first: `(n, cont, rest)` stands for `label n cont (…) :: rest`. -/
def wrap : List (Nat × List Instr × List Admin) → List Admin → List Admin
  | [], xs => xs
  | (n, c, r) :: L, xs => .label n c (wrap L xs) :: r

theorem wrap_append (L₁ L₂ : List (Nat × List Instr × List Admin)) (xs : List Admin) :
    wrap (L₁ ++ L₂) xs = wrap L₁ (wrap L₂ xs) := by
  induction L₁ with
  | nil => rfl
  | cons p L ih =>
    obtain ⟨n, c, r⟩ := p
    simp [wrap, ih]

/-- The callout context of nested labels around `T`. -/
def lctx : List (Nat × List Instr × List Admin) → Ctx → Ctx
  | [], T => T
  | (n, c, r) :: L, T => .label [] n c (lctx L T) r

theorem lctx_fill (L : List (Nat × List Instr × List Admin)) (T : Ctx) (xs : List Admin) :
    (lctx L T).fill xs = wrap L (T.fill xs) := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    obtain ⟨n, c, r⟩ := p
    simp [lctx, wrap, Ctx.fill, vals, ih]

theorem expr_app (a b : List Instr) : expression (a ++ b) = expression a ++ expression b :=
  List.map_append

section Runs

variable {P : Profile} {host : HostSemantics Nat} {s s' : Store Nat} {F F' : Frame}
  {xs ys : List Admin}

theorem steps_wrap (L : List (Nat × List Instr × List Admin))
    (h : Steps P host ⟨s, F, xs⟩ ⟨s', F', ys⟩) :
    Steps P host ⟨s, F, wrap L xs⟩ ⟨s', F', wrap L ys⟩ := by
  induction L with
  | nil => exact h
  | cons p L ih =>
    obtain ⟨n, c, r⟩ := p
    exact Steps.append r (Steps.label n c ih)

/-- A `return` leaves nested labels. -/
theorem ret_wrap (vs : List Val) : ∀ (L : List (Nat × List Instr × List Admin))
    (rest : List Admin), ∃ rest', Steps P host ⟨s, F, wrap L (vals vs ++ .plain .return_ :: rest)⟩
      ⟨s, F, vals vs ++ .plain .return_ :: rest'⟩
  | [], rest => ⟨rest, .refl⟩
  | (n, c, r) :: L, rest => by
    obtain ⟨rest', h⟩ := ret_wrap vs L rest
    refine ⟨r, (Steps.append r (Steps.label n c h)).trans (.single ?_)⟩
    have := Step.ctx (P := P) (host := host) [] r
      (Step.returnLabel (s := s) (f := F) (n := n) (cont := c) (vs := vs) (rest := rest'))
    simpa only [vals, List.map_nil, List.nil_append, List.append_assoc, List.singleton_append,
      List.cons_append] using this

/-- A `return` leaves the function frame. -/
theorem st_retFrame {f : Frame} {n : Nat} {vs : List Val} {rest : List Admin}
    (hn : vs.length = n) :
    Steps P host ⟨s, f, [.frame n F (vals vs ++ .plain .return_ :: rest)]⟩ ⟨s, f, vals vs⟩ := by
  have := Step.returnFrame (P := P) (host := host) (s := s) (f := f) (fi := F) (vs' := [])
    (vs := vs) (rest := rest) hn
  refine .single ?_
  simpa only [vals, List.map_nil, List.nil_append, List.append_assoc, List.singleton_append]
    using this

theorem st_ifF {bt : BlockType} {b₁ b₂ : List Instr} {rest : List Admin} :
    Steps P host ⟨s, F, (Val.i32 0).toAdmin :: .plain (.if_ bt b₁ b₂) :: rest⟩
      ⟨s, F, .plain (.block bt b₂) :: rest⟩ :=
  .single (Step.ctx [] rest (Step.ifFalse (s := s) (f := F) (bt := bt) (b₁ := b₁) (b₂ := b₂)))

theorem st_ifT {c : BitVec 32} (hc : c ≠ 0) {bt : BlockType} {b₁ b₂ : List Instr}
    {rest : List Admin} :
    Steps P host ⟨s, F, (Val.i32 c).toAdmin :: .plain (.if_ bt b₁ b₂) :: rest⟩
      ⟨s, F, .plain (.block bt b₁) :: rest⟩ :=
  .single (Step.ctx [] rest (Step.ifTrue (s := s) (f := F) (bt := bt) (b₁ := b₁) (b₂ := b₂) hc))

theorem st_block {body : List Instr} {rest : List Admin} :
    Steps P host ⟨s, F, .plain (.block .empty body) :: rest⟩
      ⟨s, F, wrap [(0, [], rest)] (expression body)⟩ :=
  .single (Step.ctx [] rest (Step.block (s := s) (f := F) (bt := .empty) (body := body) (vs := [])
    (t₁ := []) (t₂ := []) rfl rfl))

theorem st_loop {body : List Instr} {rest : List Admin} :
    Steps P host ⟨s, F, .plain (.loop .empty body) :: rest⟩
      ⟨s, F, wrap [(0, [.loop .empty body], rest)] (expression body)⟩ :=
  .single (Step.ctx [] rest (Step.loop (s := s) (f := F) (bt := .empty) (body := body) (vs := [])
    (t₁ := []) (t₂ := []) rfl rfl))

theorem st_labelNil {n : Nat} {c : List Instr} {rest : List Admin} :
    Steps P host ⟨s, F, wrap [(n, c, rest)] []⟩ ⟨s, F, rest⟩ :=
  .single (Step.ctx [] rest (Step.labelVals (s := s) (f := F) (n := n) (cont := c) (vs := [])))

theorem st_br0 {cont : List Instr} {rest r : List Admin} :
    Steps P host ⟨s, F, wrap [(0, cont, r)] (.plain (.br ⟨0⟩) :: rest)⟩
      ⟨s, F, expression cont ++ r⟩ :=
  .single (Step.ctx [] r (Step.brLabelZero (s := s) (f := F) (n := 0) (cont := cont) (vs' := [])
    (vs := []) (l := ⟨0⟩) (rest := rest) rfl rfl))

theorem st_call {x : FuncIdx} {a : Nat} {fi : FuncInst Nat} {pre : List Val} {rest : List Admin}
    (hx : F.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi) :
    Steps P host ⟨s, F, vals pre ++ .plain (.call x) :: rest⟩
      ⟨s, F, vals pre ++ [.ref (.func a), .callRefType fi.type] ++ rest⟩ := by
  have := Step.ctx (P := P) (host := host) pre rest (Step.call (s := s) (f := F) hx hf)
  refine .single ?_
  simpa only [List.append_assoc, List.singleton_append] using this

theorem st_invoke {a : Nat} {fi : FuncInst Nat} {code : Func} {ps rs : Ty (.list .val)}
    {args : List Val} (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
    (hn : args.length = ps.length) (hcode : fi.code = .wasm code) :
    Steps P host (invoke s a args) ⟨s, {}, [.frame rs.length
      (Frame.forCall fi.module args code.locals) [.label rs.length [] (expression code.body)]]⟩ := by
  have h := Step.callRefFunc (P := P) (host := host) (s := s) (f := {})
    (c := .callRefType ((s.funcs[a]?.map FuncInst.type).getD default)) (vs := args)
    trivial hf he hn hcode
  exact .single h

end Runs

/-! ## The bodies, cut at their control instructions -/

section Bodies

variable (cap : Nat)

/-- The guard of `feed`. -/
abbrev fG1 : List Instr := [.globalGet ⟨1⟩, .intConst .i32 (capW cap), .intRelOp .i32 .eq]
/-- `if cnt = cap then loop forever`. -/
abbrev fIf : Instr := .if_ .empty [.loop .empty [.br ⟨0⟩]] []
/-- The store and the count update of `feed`. -/
abbrev fG2 : List Instr :=
  [.globalGet ⟨0⟩, .globalGet ⟨1⟩, .intBinOp .i32 .add, .intConst .i32 (capW cap),
   .intBinOp .i32 (.rem .unsigned), .intConst .i32 8, .intBinOp .i32 .mul, .localGet ⟨0⟩,
   .intStore .i64 none ⟨0⟩ ⟨0, 0⟩, .globalGet ⟨1⟩, .intConst .i32 1, .intBinOp .i32 .add,
   .globalSet ⟨1⟩]

theorem feed_body : ringFeedBody cap = fG1 cap ++ fIf :: (fG2 cap ++ [.return_]) := rfl

/-- The guards of `finish`. -/
abbrev nG1 : List Instr := [.localGet ⟨0⟩, .globalGet ⟨1⟩, .intRelOp .i32 (.gt .unsigned)]
abbrev nG2 : List Instr := [.localGet ⟨0⟩, .intTestOp .i32 .eqz]
abbrev nIf : Instr := .if_ .empty [.intConst .i32 0, .call ⟨0⟩, .return_] []
/-- The setup of the loop. -/
abbrev nG3 : List Instr := [.localSet ⟨2⟩, .localGet ⟨0⟩, .localSet ⟨1⟩]
/-- After the `nil()` call. -/
abbrev nR3 : List Instr := nG3 ++ [.block .empty [.loop .empty (ringLoopBody cap)], .unreachable]

theorem fin_body : ringFinBody cap = nG1 ++ nIf :: (nG2 ++ nIf :: .call ⟨0⟩ :: nR3 cap) := rfl

/-- The exit test of the loop. -/
abbrev lG1 : List Instr := [.localGet ⟨1⟩, .intTestOp .i32 .eqz]
/-- The exit of the loop. -/
abbrev lThen : List Instr :=
  [.globalGet ⟨0⟩, .localGet ⟨0⟩, .intBinOp .i32 .add, .intConst .i32 (capW cap),
   .intBinOp .i32 (.rem .unsigned), .globalSet ⟨0⟩, .globalGet ⟨1⟩, .localGet ⟨0⟩,
   .intBinOp .i32 .sub, .globalSet ⟨1⟩, .localGet ⟨0⟩, .localGet ⟨2⟩]
abbrev lIf : Instr := .if_ .empty (lThen cap ++ [.return_]) []
/-- The load of the next value. -/
abbrev lG2 : List Instr :=
  [.localGet ⟨1⟩, .intConst .i32 (BitVec.allOnes 32), .intBinOp .i32 .add, .localSet ⟨1⟩,
   .globalGet ⟨0⟩, .localGet ⟨1⟩, .intBinOp .i32 .add, .intConst .i32 (capW cap),
   .intBinOp .i32 (.rem .unsigned), .intConst .i32 8, .intBinOp .i32 .mul,
   .intLoad .i64 none ⟨0⟩ ⟨0, 0⟩]
/-- After the `word` call. -/
abbrev lTail : List Instr := [.localGet ⟨2⟩, .call ⟨1⟩, .localSet ⟨2⟩, .br ⟨0⟩]
/-- After the test. -/
abbrev lRest : List Instr := lG2 cap ++ .call ⟨2⟩ :: lTail

theorem loop_body : ringLoopBody cap = lG1 ++ lIf cap :: lRest cap := rfl

/-- The labels around the loop body: the function body, the block, the loop. -/
abbrev LL : List (Nat × List Instr × List Admin) :=
  [(2, [], []), (0, [], expression [.unreachable]), (0, [.loop .empty (ringLoopBody cap)], [])]

end Bodies

/-! ## The runs of the exports -/

section Exports

variable {cap : Nat} {P : Profile} {host : HostSemantics Nat} {s : Store Nat} {M : ModuleInst}
  {g0 g1 : GlobalInst} {st cnt : BitVec 32}

/-- **`feed(x)`** with fewer than eight values buffered stores `x` in the next slot. -/
theorem feed_run (hmg : M.globals = [0, 1]) (hmm : M.mems = [0])
    (hg0 : s.globals[0]? = some g0) (hg1 : s.globals[1]? = some g1) (hv0 : g0.value = .i32 st)
    (hv1 : g1.value = .i32 cnt) {fi : FuncInst Nat} {code : Func} {ps rs : Ty (.list .val)}
    {x : BitVec 64}
    (hf : s.funcs[4]? = some fi) (he : Expand fi.type (.func ps rs)) (hps : ps.length = 1)
    (hrs : rs.length = 0) (hcode : fi.code = .wasm code)
    (hfr : Frame.forCall fi.module [.i64 x] code.locals = ⟨[some (.i64 x)], M⟩)
    (hbody : code.body = ringFeedBody cap) (hc : bool32 (cnt == capW cap) = 0) (hc0 : capW cap ≠ 0)
    {mi : MemInst} (hmi : s.mems[0]? = some mi) {b : ByteArray}
    (hb : Memory.store mi.bytes ((st + cnt) % capW cap * 8).toNat (count := 8) x = some b) :
    Steps P host (invoke s 4 [.i64 x])
      ⟨(s.setMem 0 { mi with bytes := b }).setGlobal 1 (.i32 (cnt + 1)), {}, vals []⟩ := by
  have h₀ := st_invoke (P := P) (host := host) (args := [.i64 x]) hf he (by rw [hps]; rfl) hcode
  rw [hrs, hfr, hbody] at h₀
  have hin : Steps P host ⟨s, ⟨[some (.i64 x)], M⟩, expression (ringFeedBody cap)⟩
      ⟨(s.setMem 0 { mi with bytes := b }).setGlobal 1 (.i32 (cnt + 1)), ⟨[some (.i64 x)], M⟩,
        [.plain .return_]⟩ := by
    rw [feed_body, expr_app, show expression (fIf :: (fG2 cap ++ [.return_])) =
      .plain fIf :: (expression (fG2 cap) ++ [.plain .return_]) from by simp [expression]]
    have e₁ := ex_f1 (s := s) (c := capW cap) hmg [some (.i64 x)] hg1 hv1
    rw [hc] at e₁
    refine (exec_sound (P := P) (host := host) (rs := [])
      (.plain fIf :: (expression (fG2 cap) ++ [.plain .return_])) e₁).trans ?_
    refine st_ifF.trans (st_block.trans (st_labelNil.trans ?_))
    exact exec_sound (P := P) (host := host) (rs := []) [.plain .return_]
      (ex_f2 hmg hmm hc0 hg0 hg1 hv0 hv1 hmi hb)
  obtain ⟨rest', hr⟩ := ret_wrap (P := P) (host := host)
    (s := (s.setMem 0 { mi with bytes := b }).setGlobal 1 (.i32 (cnt + 1)))
    (F := ⟨[some (.i64 x)], M⟩) [] [(0, [], [])] []
  exact h₀.trans ((Silmaril.Wasm.Logic.Core.Steps.frame (f := {}) 0
    ((steps_wrap [(0, [], [])] hin).trans hr)).trans (st_retFrame rfl))

/-- The frame of `finish(n)` on entry. -/
abbrev F₀ (M : ModuleInst) (n : BitVec 32) : Frame :=
  ⟨[some (.i32 n), some (.i32 0), some (.i32 0)], M⟩

/-- The callout context of `nil()`. -/
abbrev E₁ (cap : Nat) (M : ModuleInst) (n : BitVec 32) : Ctx :=
  .frame [] 2 (F₀ M n) (.label [] 2 [] (.top [] (expression (nR3 cap))) []) []

/-- The frame of the loop, the accumulator `r` and the index `i`. -/
abbrev FL (M : ModuleInst) (n i r : BitVec 32) : Frame :=
  ⟨[some (.i32 n), some (.i32 i), some (.i32 r)], M⟩

/-- The callout contexts in the loop, before `rest`. -/
abbrev EL (cap : Nat) (M : ModuleInst) (n i r : BitVec 32) (rest : List Instr) : Ctx :=
  .frame [] 2 (FL M n i r) (lctx (LL cap) (.top [] (expression rest))) []

/-- **`finish(n)`**, `0 < n ≤ count`: up to the call `nil()`. -/
theorem fin_run₁ (hmg : M.globals = [0, 1]) (hfuncs : M.funcs = List.range 6)
    (hg1 : s.globals[1]? = some g1) (hv1 : g1.value = .i32 cnt)
    {fi : FuncInst Nat} {code : Func} {ps rs : Ty (.list .val)} {n : BitVec 32}
    {f0 : FuncInst Nat}
    (hf : s.funcs[5]? = some fi) (he : Expand fi.type (.func ps rs)) (hps : ps.length = 1)
    (hrs : rs.length = 2) (hcode : fi.code = .wasm code)
    (hfr : Frame.forCall fi.module [.i32 n] code.locals = F₀ M n)
    (hbody : code.body = ringFinBody cap) (hgt : bool32 (decide (n.toNat > cnt.toNat)) = 0)
    (hz : bool32 (n == 0) = 0) (hf0 : s.funcs[0]? = some f0) :
    Steps P host (invoke s 5 [.i32 n])
      ⟨s, {}, (E₁ cap M n).fill (vals [] ++ [.ref (.func 0), .callRefType f0.type])⟩ := by
  have h₀ := st_invoke (P := P) (host := host) (args := [.i32 n]) hf he (by rw [hps]; rfl) hcode
  rw [hrs, hfr, hbody] at h₀
  have hin : Steps P host ⟨s, F₀ M n, expression (ringFinBody cap)⟩
      ⟨s, F₀ M n, vals [] ++ [.ref (.func 0), .callRefType f0.type] ++ expression (nR3 cap)⟩ := by
    rw [fin_body, expr_app, show expression (nIf :: (nG2 ++ nIf :: .call ⟨0⟩ :: nR3 cap)) =
      .plain nIf :: (expression nG2 ++ .plain nIf :: .plain (.call ⟨0⟩) :: expression (nR3 cap)) from
        by simp [expression]]
    have e₁ := ex_g1 (s := s) hmg (a := .i32 0) (b := .i32 0) (k := n) hg1 hv1
    rw [hgt] at e₁
    refine (exec_sound (P := P) (host := host) (rs := [])
      (.plain nIf :: (expression nG2 ++ .plain nIf :: .plain (.call ⟨0⟩) :: expression (nR3 cap)))
      e₁).trans ?_
    refine st_ifF.trans (st_block.trans (st_labelNil.trans ?_))
    have e₂ := ex_g2 (s := s) (M := M) (a := .i32 0) (b := .i32 0) (k := n)
    rw [hz] at e₂
    refine (exec_sound (P := P) (host := host) (rs := [])
      (.plain nIf :: .plain (.call ⟨0⟩) :: expression (nR3 cap)) e₂).trans ?_
    refine st_ifF.trans (st_block.trans (st_labelNil.trans ?_))
    exact st_call (pre := []) (rest := expression (nR3 cap)) (by rw [hfuncs]; rfl) hf0
  exact h₀.trans (Silmaril.Wasm.Logic.Core.Steps.frame (f := {}) 2
    (steps_wrap [(2, [], [])] hin))

/-- **`finish(n)`**, after `nil() = r`: the first iteration, up to the call `word(v)`. -/
theorem fin_run₂ (hmg : M.globals = [0, 1]) (hmm : M.mems = [0]) (hc0 : capW cap ≠ 0)
    (hfuncs : M.funcs = List.range 6) (hg0 : s.globals[0]? = some g0) (hv0 : g0.value = .i32 st)
    {n r : BitVec 32} {f2 : FuncInst Nat} (hz : bool32 (n == 0) = 0)
    {mi : MemInst} (hmi : s.mems[0]? = some mi) {v : BitVec 64}
    (hl : Memory.load mi.bytes
      (effAddr ((st + (n + BitVec.allOnes 32)) % capW cap * 8#32 : BitVec 32).toNat ⟨0, 0⟩)
      (IntType.i64.width / 8) = some v)
    (hf2 : s.funcs[2]? = some f2) :
    Steps P host ⟨s, {}, (E₁ cap M n).fill (vals [.i32 r])⟩
      ⟨s, {}, (EL cap M n (n + BitVec.allOnes 32) r lTail).fill
        (vals [.i64 v] ++ [.ref (.func 2), .callRefType f2.type])⟩ := by
  have hloop : Steps P host ⟨s, FL M n n r, expression (ringLoopBody cap)⟩
      ⟨s, FL M n (n + BitVec.allOnes 32) r,
        vals [.i64 v] ++ [.ref (.func 2), .callRefType f2.type] ++ expression lTail⟩ := by
    rw [loop_body, expr_app, show expression (lIf cap :: lRest cap) = .plain (lIf cap) :: expression (lRest cap) from
      rfl]
    have e₁ := ex_l1 (s := s) (M := M) (k := n) (i := n) (r := r)
    rw [hz] at e₁
    refine (exec_sound (P := P) (host := host) (rs := []) (.plain (lIf cap) :: expression (lRest cap))
      e₁).trans ?_
    refine st_ifF.trans (st_block.trans (st_labelNil.trans ?_))
    rw [show expression (lRest cap) = expression (lG2 cap) ++ .plain (.call ⟨2⟩) :: expression lTail from
      by simp [expression]]
    refine (exec_sound (P := P) (host := host) (rs := [])
      (.plain (.call ⟨2⟩) :: expression lTail)
      (ex_l2 hmg hmm hc0 (k := n) (i := n) (r := r) (m := BitVec.allOnes 32) hg0 hv0 hmi
        hl)).trans ?_
    exact st_call (pre := [.i64 v]) (by rw [hfuncs]; rfl) hf2
  have hin : Steps P host ⟨s, F₀ M n, wrap [(2, [], [])] (vals [.i32 r] ++ expression (nR3 cap))⟩
      ⟨s, FL M n (n + BitVec.allOnes 32) r, wrap (LL cap)
        (vals [.i64 v] ++ [.ref (.func 2), .callRefType f2.type] ++ expression lTail)⟩ := by
    refine steps_wrap [(2, [], [])] ?_
    refine (exec_sound (P := P) (host := host) (rs := [.i32 r])
      (expression [.block .empty [.loop .empty (ringLoopBody cap)], .unreachable])
      (ex_g3 (s := s) (M := M) (a := .i32 0) (b := .i32 0) (k := n) (r := r))).trans ?_
    refine st_block.trans ?_
    refine (steps_wrap [(0, [], expression [.unreachable])] st_loop).trans ?_
    exact steps_wrap [(0, [], expression [.unreachable])]
      (steps_wrap [(0, [.loop .empty (ringLoopBody cap)], [])] hloop)
  have := Silmaril.Wasm.Logic.Core.Steps.frame (P := P) (host := host) (f := {}) 2 hin
  simpa only [Ctx.fill, lctx_fill, wrap, vals, List.map_nil, List.nil_append, List.append_nil]
    using this

/-- **`finish(n)`**, after `word(v) = a`: up to the call `cons(a, r)`. -/
theorem fin_run₃ (hfuncs : M.funcs = List.range 6) {n i r a : BitVec 32} {f1 : FuncInst Nat}
    (hf1 : s.funcs[1]? = some f1) :
    Steps P host ⟨s, {}, (EL cap M n i r lTail).fill (vals [.i32 a])⟩
      ⟨s, {}, (EL cap M n i r [.localSet ⟨2⟩, .br ⟨0⟩]).fill
        (vals [.i32 a, .i32 r] ++ [.ref (.func 1), .callRefType f1.type])⟩ := by
  have hin : Steps P host ⟨s, FL M n i r, vals [.i32 a] ++ expression lTail⟩
      ⟨s, FL M n i r, vals [.i32 a, .i32 r] ++ [.ref (.func 1), .callRefType f1.type] ++
        expression [.localSet ⟨2⟩, .br ⟨0⟩]⟩ := by
    refine (exec_sound (P := P) (host := host) (rs := [.i32 a])
      (.plain (.call ⟨1⟩) :: expression [.localSet ⟨2⟩, .br ⟨0⟩])
      (ex_r1 (s := s) (M := M) (k := n) (i := i) (r := r) (a := a))).trans ?_
    exact st_call (pre := [.i32 a, .i32 r]) (by rw [hfuncs]; rfl) hf1
  have := Silmaril.Wasm.Logic.Core.Steps.frame (P := P) (host := host) (f := {}) 2
    (steps_wrap (LL cap) hin)
  simpa only [Ctx.fill, lctx_fill, wrap, vals, List.map_nil, List.nil_append, List.append_nil]
    using this

/-- **`finish(n)`**, after `cons(a, r) = c`: the second iteration exits the loop and returns
`(n, c)`, dropping the `n` consumed values. -/
theorem fin_run₄ (hmg : M.globals = [0, 1]) (hc0 : capW cap ≠ 0) (hg0 : s.globals[0]? = some g0)
    (hg1 : s.globals[1]? = some g1) (hv0 : g0.value = .i32 st) (hv1 : g1.value = .i32 cnt)
    {n r c : BitVec 32} (hnz : bool32 ((n + BitVec.allOnes 32) == 0) ≠ 0) :
    Steps P host ⟨s, {}, (EL cap M n (n + BitVec.allOnes 32) r [.localSet ⟨2⟩, .br ⟨0⟩]).fill
        (vals [.i32 c])⟩
      ⟨(s.setGlobal 0 (.i32 ((st + n) % capW cap))).setGlobal 1 (.i32 (cnt - n)), {},
        vals [.i32 n, .i32 c]⟩ := by
  let s₄ := (s.setGlobal 0 (.i32 ((st + n) % capW cap))).setGlobal 1 (.i32 (cnt - n))
  let F₂ := FL M n (n + BitVec.allOnes 32) c
  have hit : Steps P host ⟨s, F₂, expression (ringLoopBody cap)⟩
      ⟨s₄, F₂, wrap [(0, [], expression (lRest cap))] (vals [.i32 n, .i32 c] ++ [.plain .return_])⟩ := by
    rw [loop_body, expr_app, show expression (lIf cap :: lRest cap) = .plain (lIf cap) :: expression (lRest cap) from
      rfl]
    refine (exec_sound (P := P) (host := host) (rs := []) (.plain (lIf cap) :: expression (lRest cap))
      (ex_l1 (s := s) (M := M) (k := n) (i := n + BitVec.allOnes 32) (r := c))).trans ?_
    refine (st_ifT hnz).trans (st_block.trans ?_)
    refine steps_wrap _ ?_
    rw [expr_app]
    exact exec_sound (P := P) (host := host) (rs := []) (expression [.return_])
      (ex_t hmg hc0 (k := n) (i := n + BitVec.allOnes 32) (r := c) hg0 hg1 hv0 hv1)
  have hin : Steps P host
      ⟨s, FL M n (n + BitVec.allOnes 32) r,
        wrap (LL cap) (vals [.i32 c] ++ expression [.localSet ⟨2⟩, .br ⟨0⟩])⟩
      ⟨s₄, F₂, wrap (LL cap ++ [(0, [], expression (lRest cap))])
        (vals [.i32 n, .i32 c] ++ [.plain .return_])⟩ := by
    refine (steps_wrap (LL cap) (exec_sound (P := P) (host := host) (rs := [.i32 c])
      [.plain (.br ⟨0⟩)] (ex_r2 (s := s) (M := M) (k := n) (i := n + BitVec.allOnes 32) (r := r)
        (c := c)))).trans ?_
    rw [show (LL cap) = [(2, [], []), (0, [], expression [.unreachable])] ++
      [(0, [.loop .empty (ringLoopBody cap)], [])] from rfl]
    simp only [wrap_append]
    refine (steps_wrap _ (st_br0 (rest := []) (r := []))).trans ?_
    refine (steps_wrap _ (st_loop (rest := []))).trans ?_
    exact steps_wrap _ (steps_wrap _ hit)
  obtain ⟨rest', hr⟩ := ret_wrap (P := P) (host := host) (s := s₄) (F := F₂) [.i32 n, .i32 c]
    (LL cap ++ [(0, [], expression (lRest cap))]) []
  have h := (Silmaril.Wasm.Logic.Core.Steps.frame (P := P) (host := host) (f := {}) 2
    (hin.trans hr)).trans (st_retFrame rfl)
  simpa only [Ctx.fill, lctx_fill, wrap, vals, List.map_nil, List.nil_append, List.append_nil]
    using h

end Exports

/-! ## The session -/

theorem glob_of {s : Store Nat} {a : Nat} {v : Val} (h : gval s a = some v) :
    ∃ g, s.globals[a]? = some g ∧ g.value = v := by
  unfold gval at h
  cases hg : s.globals[a]? with
  | none => simp [hg] at h
  | some g => simp only [hg, Option.map_some, Option.some.injEq] at h; exact ⟨g, rfl, h⟩

section Session

variable (cap : Nat)

theorem ri_gval0 : gval (RI cap).store 0 = some (.i32 0) := by
  rw [RI_eq]; exact ring_gval0 cap

theorem ri_gval1 : gval (RI cap).store 1 = some (.i32 0) := by
  rw [RI_eq]; exact ring_gval1 cap

theorem ri_memlen : (RI cap).store.mems.length = 1 := by
  rw [RI_eq]; exact ring_memlen cap

theorem ri_size : ((RI cap).store.mems[0]?).map (·.bytes.size) = some 65536 := by
  rw [RI_eq]; exact ring_size cap

theorem ri_exports : (RI cap).exports = chunkFTs := (ring_shape cap).exports

/-- The export calls of the session. -/
abbrev cF7 : (RI cap).F.Op :=
  ⟨⟨0, by rw [ri_exports]; decide⟩,
    ⟨[.i64 7], typedB_sound (by rw [(ring_shape cap).get]; rfl)⟩⟩
abbrev cF8 : (RI cap).F.Op :=
  ⟨⟨0, by rw [ri_exports]; decide⟩,
    ⟨[.i64 8], typedB_sound (by rw [(ring_shape cap).get]; rfl)⟩⟩
abbrev cN1 : (RI cap).F.Op :=
  ⟨⟨1, by rw [ri_exports]; decide⟩,
    ⟨[.i32 1], typedB_sound (by rw [(ring_shape cap).get]; rfl)⟩⟩

end Session

/-- The recorded moves of `finish(1)` with the callouts answered `r`, `a`, `c` (`nil()`, `word(v)`,
`cons(a, r)`). -/
def finR (v : BitVec 64) (r a c : BitVec 32) : List RMove :=
  [.call 1 [.i32 1], .ask 0 [], .ans 0 (.returns [.i32 r]), .ask 2 [.i64 v],
   .ans 2 (.returns [.i32 a]), .ask 1 [.i32 a, .i32 r], .ans 1 (.returns [.i32 c]),
   .ret 1 (.returns [.i32 1, .i32 c])]

/-- **The recorded moves of the session** `feed(7)`, `feed(8)`, `finish(1)`, `finish(1)`, the
`k`-th callout answered with the handle `k + 1`. -/
def ringR : List RMove :=
  [.call 0 [.i64 7], .ret 0 (.returns []), .call 0 [.i64 8], .ret 0 (.returns [])] ++
    finR 7 1 2 3 ++ finR 8 4 5 6

/-- **The recorded moves of the one-value session** `feed(7)`, `finish(1)`, the `k`-th callout
answered with the handle `k + 1`. -/
def ringR1 : List RMove :=
  [.call 0 [.i64 7], .ret 0 (.returns [])] ++ finR 7 1 2 3

/-- The stores of the session: after `feed(7)`, `feed(8)`, and the first `finish(1)`. -/
abbrev S₁ (cap : Nat) (mi : MemInst) (B₁ : ByteArray) : Store Nat :=
  ((RI cap).store.setMem 0 { mi with bytes := B₁ }).setGlobal 1 (.i32 (0 + 1))
abbrev S₂ (cap : Nat) (mi : MemInst) (B₁ B₂ : ByteArray) : Store Nat :=
  ((S₁ cap mi B₁).setMem 0 { mi with bytes := B₂ }).setGlobal 1 (.i32 (0 + 1 + 1))
abbrev S₃ (cap : Nat) (mi : MemInst) (B₁ B₂ : ByteArray) : Store Nat :=
  ((S₂ cap mi B₁ B₂).setGlobal 0 (.i32 ((0 + 1) % capW cap))).setGlobal 1 (.i32 (0 + 1 + 1 - 1))

theorem bool32_ne {a c : BitVec 32} (h : a ≠ c) : bool32 (a == c) = 0 := by
  simp [bool32, h]

theorem effAddr_00 (a : Nat) : effAddr a ⟨0, 0⟩ = a := rfl

theorem allOnes_succ : (1 : BitVec 32) + BitVec.allOnes 32 = 0 := by decide

theorem mod_small {cap : Nat} (h8 : cap ≤ 8192) {x : BitVec 32} (hx : x.toNat < cap) :
    x % capW cap = x :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_umod, capW_toNat h8]; exact Nat.mod_eq_of_lt hx)

/-- **The session is a play** of `chunkRingN cap`, for every capacity `2 ≤ cap ≤ 8192`, in
every profile. -/
theorem ring_session {cap : Nat} (h2 : 2 ≤ cap) (h8 : cap ≤ 8192) (P : Profile) :
    ∃ ms q, (RI cap).Path P (.idle (RI cap).store) ms q ∧ ms.map rmv = ringR := by
  have hcap : RingCap cap := ⟨by omega, h8⟩
  have hc0 : capW cap ≠ 0 := capW_ne hcap
  have hcw := capW_toNat h8
  have hne : ∀ a : BitVec 32, a.toNat < 2 → a ≠ capW cap := fun a ha h => by
    rw [h, hcw] at ha; omega
  have hS := ring_shape cap
  obtain ⟨f0, ps0, rs0, hf0, hc0', he0, hn0⟩ := hS.stub 0 (by decide)
  obtain ⟨f1, ps1, rs1, hf1, hc1, he1, hn1⟩ := hS.stub 1 (by decide)
  obtain ⟨f2, ps2, rs2, hf2, hc2, he2, hn2⟩ := hS.stub 2 (by decide)
  obtain ⟨fi4, code4, ps4, rs4, hf4, hcode4, hloc4, hbody4, he4, hps4, hrs4, -, hmg4, -⟩ :=
    hS.fn 0 (by decide)
  obtain ⟨fi5, code5, ps5, rs5, hf5, hcode5, hloc5, hbody5, he5, hps5, hrs5, hm5, hmg5, hD5⟩ :=
    hS.fn 1 (by decide)
  have hf4' : (RI cap).store.funcs[4]? = some fi4 := hf4
  have hf5' : (RI cap).store.funcs[5]? = some fi5 := hf5
  have hmm4 : fi4.module.mems = [0] := by
    have h := ring_mems4 cap
    rw [hf4'] at h
    exact Option.some.inj h
  have hmm5 : fi5.module.mems = [0] := by
    have h := ring_mems5 cap
    rw [hf5'] at h
    exact Option.some.inj h
  have hfr4 : ∀ x : BitVec 64, Frame.forCall fi4.module [.i64 x] code4.locals =
      ⟨[some (.i64 x)], fi4.module⟩ := fun x => by
    unfold Frame.forCall
    rw [hloc4]
    rfl
  have hfr5 : ∀ n : BitVec 32, Frame.forCall fi5.module [.i32 n] code5.locals = F₀ fi5.module n :=
    fun n => by
      unfold Frame.forCall
      rw [hloc5, hD5]
      rfl
  -- the slots
  have t1 : (1 : BitVec 32).toNat = 1 := rfl
  have hm1 : (1 : BitVec 32) % capW cap = 1 := mod_small h8 (by rw [t1]; omega)
  have hm0 : (0 : BitVec 32) % capW cap = 0 := mod_small h8 (show 0 < cap by omega)
  have ha0 : (((0 : BitVec 32) + 0) % capW cap * 8).toNat = 0 := by
    rw [show (0 : BitVec 32) + 0 = 0 from by decide, hm0]; decide
  have ha1 : (((0 : BitVec 32) + (0 + 1)) % capW cap * 8).toNat = 8 := by
    rw [show (0 : BitVec 32) + (0 + 1) = 1 from by decide, hm1]; decide
  have ha0' : (((0 : BitVec 32) + 0) % capW cap * 8#32).toNat = 0 := ha0
  have ha2 : (((0 + 1 : BitVec 32) % capW cap + 0) % capW cap * 8#32).toNat = 8 := by
    rw [show (0 + 1 : BitVec 32) = 1 from by decide, hm1,
      show (1 : BitVec 32) + 0 = 1 from by decide, hm1]; decide
  -- the memory
  obtain ⟨mi₀, hmi₀⟩ : ∃ mi, (RI cap).store.mems[0]? = some mi :=
    ⟨(RI cap).store.mems[0]'(by rw [ri_memlen]; decide), List.getElem?_eq_getElem _⟩
  have hsz : mi₀.bytes.size = 65536 := by
    have h := ri_size cap
    rw [hmi₀] at h
    exact Option.some.inj h
  obtain ⟨B₁, hB₁⟩ := Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.store_some
    (B := mi₀.bytes) (a := (((0 : BitVec 32) + 0) % capW cap * 8).toNat) (n := 8) (7 : BitVec 64)
    (by rw [hsz, ha0]; decide)
  obtain ⟨B₂, hB₂⟩ := Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.store_some
    (B := B₁) (a := (((0 : BitVec 32) + (0 + 1)) % capW cap * 8).toNat) (n := 8) (8 : BitVec 64)
    (by rw [Silmaril.Wasm.Logic.Core.size_store hB₁, hsz, ha1]; decide)
  -- the stores
  have hl₀ := ri_memlen cap
  obtain ⟨hm₁, hl₁, -, -⟩ := setMem_mems (s := (RI cap).store) (mi := { mi₀ with bytes := B₁ }) hl₀
  obtain ⟨hm₂, -, -, -⟩ := setMem_mems (s := S₁ cap mi₀ B₁) (mi := { mi₀ with bytes := B₂ }) hl₁
  obtain ⟨g00, hg00, hv00⟩ := glob_of (ri_gval0 cap)
  obtain ⟨g01, hg01, hv01⟩ := glob_of (ri_gval1 cap)
  obtain ⟨g10, hg10, hv10⟩ := glob_of (s := S₁ cap mi₀ B₁) (a := 0) (v := .i32 0) (by
    simp [gval_setGlobal, gval_setMem, ri_gval0])
  obtain ⟨g11, hg11, hv11⟩ := glob_of (s := S₁ cap mi₀ B₁) (a := 1) (v := .i32 (0 + 1)) (by
    simp [gval_setGlobal, gval_setMem, ri_gval1])
  obtain ⟨g20, hg20, hv20⟩ := glob_of (s := S₂ cap mi₀ B₁ B₂) (a := 0) (v := .i32 0) (by
    simp [gval_setGlobal, gval_setMem, ri_gval0])
  obtain ⟨g21, hg21, hv21⟩ := glob_of (s := S₂ cap mi₀ B₁ B₂) (a := 1) (v := .i32 (0 + 1 + 1)) (by
    simp [gval_setGlobal, gval_setMem, ri_gval1])
  obtain ⟨g30, hg30, hv30⟩ := glob_of (s := S₃ cap mi₀ B₁ B₂) (a := 0)
    (v := .i32 ((0 + 1) % capW cap)) (by simp [gval_setGlobal, gval_setMem, ri_gval0])
  obtain ⟨g31, hg31, hv31⟩ := glob_of (s := S₃ cap mi₀ B₁ B₂) (a := 1)
    (v := .i32 (0 + 1 + 1 - 1)) (by simp [gval_setGlobal, gval_setMem, ri_gval1])
  -- the loads
  have hld₁ : Memory.load B₂
      (effAddr (((0 : BitVec 32) + (1 + BitVec.allOnes 32)) % capW cap * 8#32 : BitVec 32).toNat
        ⟨0, 0⟩) (IntType.i64.width / 8) = some (7 : BitVec 64) := by
    rw [allOnes_succ, effAddr_00,
      Silmaril.Wasm.Logic.Core.load_store_disjoint hB₂ (by
        unfold Silmaril.Wasm.Logic.Core.Region.Disjoint Silmaril.Wasm.Logic.Core.Region.stop
        rw [ha0', ha1]; decide)]
    exact Silmaril.Wasm.Logic.Core.load_store_same hB₁
  have hld₂ : Memory.load B₂
      (effAddr (((0 + 1) % capW cap + (1 + BitVec.allOnes 32)) % capW cap * 8#32 :
        BitVec 32).toNat ⟨0, 0⟩) (IntType.i64.width / 8) = some (8 : BitVec 64) := by
    rw [allOnes_succ, effAddr_00, show (((0 + 1 : BitVec 32) % capW cap + 0) % capW cap *
      8#32).toNat = (((0 : BitVec 32) + (0 + 1)) % capW cap * 8).toNat from ha2.trans ha1.symm]
    exact Silmaril.Wasm.Logic.Core.load_store_same hB₂
  -- the runs
  have r₁ : Steps P Det.noHost (((RI cap).initThread (cF7 cap)).config (RI cap).store)
      ⟨S₁ cap mi₀ B₁, {}, vals []⟩ := by
    show Steps P Det.noHost (invoke (RI cap).store ((RI cap).addr (cF7 cap).1) (cF7 cap).2.1) _
    rw [hS.addr]
    exact feed_run hmg4 hmm4 hg00 hg01 hv00 hv01 hf4' he4 hps4 hrs4 hcode4 (hfr4 7) hbody4
      (bool32_ne (hne 0 (by decide))) hc0 hmi₀ hB₁
  have r₂ : Steps P Det.noHost (((RI cap).initThread (cF8 cap)).config (S₁ cap mi₀ B₁))
      ⟨S₂ cap mi₀ B₁ B₂, {}, vals []⟩ := by
    show Steps P Det.noHost (invoke (S₁ cap mi₀ B₁) ((RI cap).addr (cF8 cap).1) (cF8 cap).2.1) _
    rw [hS.addr]
    exact feed_run hmg4 hmm4 hg10 hg11 hv10 hv11 hf4' he4 hps4 hrs4 hcode4 (hfr4 8) hbody4
      (bool32_ne (hne (0 + 1) (by decide))) hc0 hm₁ hB₂
  have hdec : ∀ (s : Store Nat) (E : Ctx) (k : Nat) (fk : FuncInst Nat) (ps rs : Ty (.list .val))
      (args : List Val), s.funcs[k]? = some fk → fk.code = .host k →
      Expand fk.type (.func ps rs) → args.length = ps.length →
      decompose? s (E.fill (vals args ++ [.ref (.func k), .callRefType fk.type])) =
        some (E, k, k, args) := fun s E k fk ps rs args hf hc he hn =>
    Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.decompose_fill E trivial hf he hn hc
  have himp : ∀ (k : Nat) (hk : k < (RI cap).imports.length),
      (RI cap).imports.get ⟨k, hk⟩ = twoFTs[k]'(hS.imports ▸ hk) := fun k hk => by
    rw [List.get_eq_getElem]
    exact List.getElem_of_eq hS.imports hk
  have hil : (RI cap).imports.length = 4 := by rw [hS.imports]; rfl
  -- `finish(1)` from a store
  have fin : ∀ (s : Store Nat) (st cnt : BitVec 32) (g0 g1 : GlobalInst) (mi : MemInst)
      (v : BitVec 64) (r a c : BitVec 32), s.funcs = (RI cap).store.funcs →
      s.globals[0]? = some g0 → s.globals[1]? = some g1 → g0.value = .i32 st →
      g1.value = .i32 cnt → s.mems[0]? = some mi →
      bool32 (decide ((1 : BitVec 32).toNat > cnt.toNat)) = 0 →
      Memory.load mi.bytes
        (effAddr ((st + (1 + BitVec.allOnes 32)) % capW cap * 8#32 : BitVec 32).toNat ⟨0, 0⟩)
        (IntType.i64.width / 8) = some v →
      ∃ ms, (RI cap).Path P (.idle s) ms
        (.idle ((s.setGlobal 0 (.i32 ((st + 1) % capW cap))).setGlobal 1 (.i32 (cnt - 1)))) ∧
        ms.map rmv = finR v r a c := by
    intro s st cnt g0 g1 mi v r a c hfs hg0 hg1 hv0 hv1 hmi hgt hl
    have hfs0 : s.funcs[0]? = some f0 := by rw [hfs]; exact hf0
    have hfs1 : s.funcs[1]? = some f1 := by rw [hfs]; exact hf1
    have hfs2 : s.funcs[2]? = some f2 := by rw [hfs]; exact hf2
    have hfs5 : s.funcs[5]? = some fi5 := by rw [hfs]; exact hf5'
    refine path_call' (f := cN1 cap) ?_
    refine path_callout' (F' := {}) (h := 0) (args := []) (vs := [.i32 r]) ?_
      (hdec s (E₁ cap fi5.module 1) 0 f0 ps0 rs0 [] hfs0 hc0' he0 (by rw [hn0]; rfl))
      (by rw [hil]; decide) (by rw [himp]; rfl) (by rw [himp]; rfl) ?_
    · show Steps P Det.noHost (invoke s ((RI cap).addr (cN1 cap).1) (cN1 cap).2.1) _
      rw [hS.addr]
      exact fin_run₁ hmg5 hm5 hg1 hv1 hfs5 he5 hps5 hrs5 hcode5 (hfr5 1) hbody5 hgt (by decide)
        hfs0
    refine path_callout' (F' := {}) (h := 2) (args := [.i64 v]) (vs := [.i32 a])
      (fin_run₂ hmg5 hmm5 hc0 hm5 hg0 hv0 (by decide) hmi hl hfs2)
      (hdec s (EL cap fi5.module 1 (1 + BitVec.allOnes 32) r lTail) 2 f2 ps2 rs2 [.i64 v] hfs2
        hc2 he2 (by rw [hn2]; rfl)) (by rw [hil]; decide)
      (by rw [himp]; rfl) (by rw [himp]; rfl) ?_
    refine path_callout' (F' := {}) (h := 1) (args := [.i32 a, .i32 r]) (vs := [.i32 c])
      (fin_run₃ hm5 hfs1)
      (hdec s (EL cap fi5.module 1 (1 + BitVec.allOnes 32) r [.localSet ⟨2⟩, .br ⟨0⟩]) 1 f1
        ps1 rs1 [.i32 a, .i32 r] hfs1 hc1 he1 (by rw [hn1]; rfl))
      (by rw [hil]; decide) (by rw [himp]; rfl) (by rw [himp]; rfl) ?_
    exact path_ret (fin_run₄ hmg5 hc0 hg0 hg1 hv0 hv1 (by decide)) (by rw [hS.get]; rfl)
  have p₁ := path_call' (f := cF7 cap) (path_ret r₁ (by rw [hS.get]; rfl))
  have p₂ := path_call' (f := cF8 cap) (path_ret r₂ (by rw [hS.get]; rfl))
  have p₃ := fin (S₂ cap mi₀ B₁ B₂) 0 (0 + 1 + 1) g20 g21 { mi₀ with bytes := B₂ } 7 1 2 3 rfl
    hg20 hg21 hv20 hv21 hm₂ (by decide) hld₁
  have p₄ := fin (S₃ cap mi₀ B₁ B₂) ((0 + 1) % capW cap) (0 + 1 + 1 - 1) g30 g31
    { mi₀ with bytes := B₂ } 8 4 5 6 rfl hg30 hg31 hv30 hv31 hm₂ (by decide) hld₂
  obtain ⟨ms, hp, hm⟩ := path_trans p₁ (path_trans p₂ (path_trans p₃ p₄))
  exact ⟨ms, _, hp, hm⟩

theorem ring_session1 {cap : Nat} (h1 : 1 ≤ cap) (h8 : cap ≤ 8192) (P : Profile) :
    ∃ ms q, (RI cap).Path P (.idle (RI cap).store) ms q ∧ ms.map rmv = ringR1 := by
  have hcap : RingCap cap := ⟨by omega, h8⟩
  have hc0 : capW cap ≠ 0 := capW_ne hcap
  have hcw := capW_toNat h8
  have hne : ∀ a : BitVec 32, a.toNat < 1 → a ≠ capW cap := fun a ha h => by
    rw [h, hcw] at ha; omega
  have hS := ring_shape cap
  obtain ⟨f0, ps0, rs0, hf0, hc0', he0, hn0⟩ := hS.stub 0 (by decide)
  obtain ⟨f1, ps1, rs1, hf1, hc1, he1, hn1⟩ := hS.stub 1 (by decide)
  obtain ⟨f2, ps2, rs2, hf2, hc2, he2, hn2⟩ := hS.stub 2 (by decide)
  obtain ⟨fi4, code4, ps4, rs4, hf4, hcode4, hloc4, hbody4, he4, hps4, hrs4, -, hmg4, -⟩ :=
    hS.fn 0 (by decide)
  obtain ⟨fi5, code5, ps5, rs5, hf5, hcode5, hloc5, hbody5, he5, hps5, hrs5, hm5, hmg5, hD5⟩ :=
    hS.fn 1 (by decide)
  have hf4' : (RI cap).store.funcs[4]? = some fi4 := hf4
  have hf5' : (RI cap).store.funcs[5]? = some fi5 := hf5
  have hmm4 : fi4.module.mems = [0] := by
    have h := ring_mems4 cap
    rw [hf4'] at h
    exact Option.some.inj h
  have hmm5 : fi5.module.mems = [0] := by
    have h := ring_mems5 cap
    rw [hf5'] at h
    exact Option.some.inj h
  have hfr4 : ∀ x : BitVec 64, Frame.forCall fi4.module [.i64 x] code4.locals =
      ⟨[some (.i64 x)], fi4.module⟩ := fun x => by
    unfold Frame.forCall
    rw [hloc4]
    rfl
  have hfr5 : ∀ n : BitVec 32, Frame.forCall fi5.module [.i32 n] code5.locals = F₀ fi5.module n :=
    fun n => by
      unfold Frame.forCall
      rw [hloc5, hD5]
      rfl
  -- the slots
  have hm0 : (0 : BitVec 32) % capW cap = 0 := mod_small h8 (show 0 < cap by omega)
  have ha0 : (((0 : BitVec 32) + 0) % capW cap * 8).toNat = 0 := by
    rw [show (0 : BitVec 32) + 0 = 0 from by decide, hm0]; decide
  -- the memory
  obtain ⟨mi₀, hmi₀⟩ : ∃ mi, (RI cap).store.mems[0]? = some mi :=
    ⟨(RI cap).store.mems[0]'(by rw [ri_memlen]; decide), List.getElem?_eq_getElem _⟩
  have hsz : mi₀.bytes.size = 65536 := by
    have h := ri_size cap
    rw [hmi₀] at h
    exact Option.some.inj h
  obtain ⟨B₁, hB₁⟩ := Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.store_some
    (B := mi₀.bytes) (a := (((0 : BitVec 32) + 0) % capW cap * 8).toNat) (n := 8) (7 : BitVec 64)
    (by rw [hsz, ha0]; decide)
  -- the stores
  have hl₀ := ri_memlen cap
  obtain ⟨hm₁, -, -, -⟩ := setMem_mems (s := (RI cap).store) (mi := { mi₀ with bytes := B₁ }) hl₀
  obtain ⟨g00, hg00, hv00⟩ := glob_of (ri_gval0 cap)
  obtain ⟨g01, hg01, hv01⟩ := glob_of (ri_gval1 cap)
  obtain ⟨g10, hg10, hv10⟩ := glob_of (s := S₁ cap mi₀ B₁) (a := 0) (v := .i32 0) (by
    simp [gval_setGlobal, gval_setMem, ri_gval0])
  obtain ⟨g11, hg11, hv11⟩ := glob_of (s := S₁ cap mi₀ B₁) (a := 1) (v := .i32 (0 + 1)) (by
    simp [gval_setGlobal, gval_setMem, ri_gval1])
  -- the loads
  have hld₁ : Memory.load B₁
      (effAddr (((0 : BitVec 32) + (1 + BitVec.allOnes 32)) % capW cap * 8#32 : BitVec 32).toNat
        ⟨0, 0⟩) (IntType.i64.width / 8) = some (7 : BitVec 64) := by
    rw [allOnes_succ, effAddr_00]
    exact Silmaril.Wasm.Logic.Core.load_store_same hB₁
  -- the runs
  have r₁ : Steps P Det.noHost (((RI cap).initThread (cF7 cap)).config (RI cap).store)
      ⟨S₁ cap mi₀ B₁, {}, vals []⟩ := by
    show Steps P Det.noHost (invoke (RI cap).store ((RI cap).addr (cF7 cap).1) (cF7 cap).2.1) _
    rw [hS.addr]
    exact feed_run hmg4 hmm4 hg00 hg01 hv00 hv01 hf4' he4 hps4 hrs4 hcode4 (hfr4 7) hbody4
      (bool32_ne (hne 0 (by decide))) hc0 hmi₀ hB₁
  have hdec : ∀ (s : Store Nat) (E : Ctx) (k : Nat) (fk : FuncInst Nat) (ps rs : Ty (.list .val))
      (args : List Val), s.funcs[k]? = some fk → fk.code = .host k →
      Expand fk.type (.func ps rs) → args.length = ps.length →
      decompose? s (E.fill (vals args ++ [.ref (.func k), .callRefType fk.type])) =
        some (E, k, k, args) := fun s E k fk ps rs args hf hc he hn =>
    Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.decompose_fill E trivial hf he hn hc
  have himp : ∀ (k : Nat) (hk : k < (RI cap).imports.length),
      (RI cap).imports.get ⟨k, hk⟩ = twoFTs[k]'(hS.imports ▸ hk) := fun k hk => by
    rw [List.get_eq_getElem]
    exact List.getElem_of_eq hS.imports hk
  have hil : (RI cap).imports.length = 4 := by rw [hS.imports]; rfl
  -- `finish(1)` from a store
  have fin : ∀ (s : Store Nat) (st cnt : BitVec 32) (g0 g1 : GlobalInst) (mi : MemInst)
      (v : BitVec 64) (r a c : BitVec 32), s.funcs = (RI cap).store.funcs →
      s.globals[0]? = some g0 → s.globals[1]? = some g1 → g0.value = .i32 st →
      g1.value = .i32 cnt → s.mems[0]? = some mi →
      bool32 (decide ((1 : BitVec 32).toNat > cnt.toNat)) = 0 →
      Memory.load mi.bytes
        (effAddr ((st + (1 + BitVec.allOnes 32)) % capW cap * 8#32 : BitVec 32).toNat ⟨0, 0⟩)
        (IntType.i64.width / 8) = some v →
      ∃ ms, (RI cap).Path P (.idle s) ms
        (.idle ((s.setGlobal 0 (.i32 ((st + 1) % capW cap))).setGlobal 1 (.i32 (cnt - 1)))) ∧
        ms.map rmv = finR v r a c := by
    intro s st cnt g0 g1 mi v r a c hfs hg0 hg1 hv0 hv1 hmi hgt hl
    have hfs0 : s.funcs[0]? = some f0 := by rw [hfs]; exact hf0
    have hfs1 : s.funcs[1]? = some f1 := by rw [hfs]; exact hf1
    have hfs2 : s.funcs[2]? = some f2 := by rw [hfs]; exact hf2
    have hfs5 : s.funcs[5]? = some fi5 := by rw [hfs]; exact hf5'
    refine path_call' (f := cN1 cap) ?_
    refine path_callout' (F' := {}) (h := 0) (args := []) (vs := [.i32 r]) ?_
      (hdec s (E₁ cap fi5.module 1) 0 f0 ps0 rs0 [] hfs0 hc0' he0 (by rw [hn0]; rfl))
      (by rw [hil]; decide) (by rw [himp]; rfl) (by rw [himp]; rfl) ?_
    · show Steps P Det.noHost (invoke s ((RI cap).addr (cN1 cap).1) (cN1 cap).2.1) _
      rw [hS.addr]
      exact fin_run₁ hmg5 hm5 hg1 hv1 hfs5 he5 hps5 hrs5 hcode5 (hfr5 1) hbody5 hgt (by decide)
        hfs0
    refine path_callout' (F' := {}) (h := 2) (args := [.i64 v]) (vs := [.i32 a])
      (fin_run₂ hmg5 hmm5 hc0 hm5 hg0 hv0 (by decide) hmi hl hfs2)
      (hdec s (EL cap fi5.module 1 (1 + BitVec.allOnes 32) r lTail) 2 f2 ps2 rs2 [.i64 v] hfs2
        hc2 he2 (by rw [hn2]; rfl)) (by rw [hil]; decide)
      (by rw [himp]; rfl) (by rw [himp]; rfl) ?_
    refine path_callout' (F' := {}) (h := 1) (args := [.i32 a, .i32 r]) (vs := [.i32 c])
      (fin_run₃ hm5 hfs1)
      (hdec s (EL cap fi5.module 1 (1 + BitVec.allOnes 32) r [.localSet ⟨2⟩, .br ⟨0⟩]) 1 f1
        ps1 rs1 [.i32 a, .i32 r] hfs1 hc1 he1 (by rw [hn1]; rfl))
      (by rw [hil]; decide) (by rw [himp]; rfl) (by rw [himp]; rfl) ?_
    exact path_ret (fin_run₄ hmg5 hc0 hg0 hg1 hv0 hv1 (by decide)) (by rw [hS.get]; rfl)
  have p₁ := path_call' (f := cF7 cap) (path_ret r₁ (by rw [hS.get]; rfl))
  have p₃ := fin (S₁ cap mi₀ B₁) 0 (0 + 1) g10 g11 { mi₀ with bytes := B₁ } 7 1 2 3 rfl
    hg10 hg11 hv10 hv11 hm₁ (by decide) hld₁
  obtain ⟨ms, hp, hm⟩ := path_trans p₁ p₃
  exact ⟨ms, _, hp, hm⟩

/-- The one-value session as a play of the instance itself. -/
theorem ring_session1' {cap : Nat} (h1 : 1 ≤ cap) (h8 : cap ≤ 8192) (P : Profile) :
    ∃ ms q, (Verify.instOf (chunkRingN cap)).Path P (.idle (Verify.instOf (chunkRingN cap)).store)
      ms q ∧ ms.map rmv = ringR1 := by
  have h := ring_session1 h1 h8 P
  rw [RI_eq] at h
  exact h

/-- The session as a play of the instance itself. -/
theorem ring_session' {cap : Nat} (h2 : 2 ≤ cap) (h8 : cap ≤ 8192) (P : Profile) :
    ∃ ms q, (Verify.instOf (chunkRingN cap)).Path P (.idle (Verify.instOf (chunkRingN cap)).store)
      ms q ∧ ms.map rmv = ringR := by
  have h := ring_session h2 h8 P
  rw [RI_eq] at h
  exact h

/-! ## Related pairs -/

section Relates

variable {cap : Nat} (h2 : 2 ≤ cap) (h8 : cap ≤ 8192) {P : Profile} {pol : Policy (BitVec 32)}
  (hs : ∀ r, pol.sentinel = some r → r = 0) {ppol : PPolicy (BitVec 32)} (h0 : ppol.sentinel = 0)
include h2 h8 hs h0

/-- **The first `finish(1)` consumes one of two buffered values: `([7], (7))`.** -/
theorem chunkRingN_relates_7 :
    ([7], SExp2.ofAtoms [7]) ∈ moduleMixedRel P (chunkRingN cap) twoIx ringPix pol ppol :=
  mem_moduleMixedRel_of_path twoIx ringPix (bad := fun r => decide (r = 0))
    (fun r h => by simp [hs r h]) (by simp [h0]) (ring_session' h2 h8 P) (by decide +kernel)

/-- **The second `finish(1)` consumes the value left in memory: `([8], (8))`.** -/
theorem chunkRingN_relates_8 :
    ([8], SExp2.ofAtoms [8]) ∈ moduleMixedRel P (chunkRingN cap) twoIx ringPix pol ppol :=
  mem_moduleMixedRel_of_path twoIx ringPix (bad := fun r => decide (r = 0))
    (fun r h => by simp [hs r h]) (by simp [h0]) (ring_session' h2 h8 P) (by decide +kernel)

end Relates

/-- **One value, every capacity `1 ≤ cap ≤ 8192`** (the one-slot buffer included): `feed(7)`,
`finish(1)` relates `([7], (7))`. -/
theorem chunkRingN_relates_7_one {cap : Nat} (h1 : 1 ≤ cap) (h8 : cap ≤ 8192) {P : Profile}
    {pol : Policy (BitVec 32)} (hs : ∀ r, pol.sentinel = some r → r = 0)
    {ppol : PPolicy (BitVec 32)} (h0 : ppol.sentinel = 0) :
    ([7], SExp2.ofAtoms [7]) ∈ moduleMixedRel P (chunkRingN cap) twoIx ringPix pol ppol :=
  mem_moduleMixedRel_of_path twoIx ringPix (bad := fun r => decide (r = 0))
    (fun r h => by simp [hs r h]) (by simp [h0]) (ring_session1' h1 h8 P) (by decide +kernel)

end Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.RingLive
