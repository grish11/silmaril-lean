module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.PullMixLive

/-!
# Proofs: the stale-chunk hazard of `blobEcho`

Against `staleEnv q` (admitted by `blobReply`): the first invocation reads `68 69` (decoded as
`feed [68, 69]`) and the host traps `blob(0, 2)`, so the invocation ends with the chunk
buffered; the second invocation reads `69 68`, writes its byte atom with handle `q` and calls
`finish(2, q)`. The cursor consumes the **first** two buffered bytes `68 69`, while `q` denotes
the atom `69 68`: the mixed relation contains `(68 69, bytes 69 68)` (`be_stale`), so it is not
included in the exact relation `{(bs, bytes bs)}` (`be_not_exact`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.PullMix

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game
  Silmaril.Wasm.Game.Accept Silmaril.Wasm.Game.IOAccept Silmaril.Accept Silmaril.Accept.Handle
  Silmaril.Accept.IO Silmaril.Accept.Parse Silmaril.Accept.Mixed Silmaril.Formats
  Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.Pull
  Silmaril.Wasm.Game.HandleAccept.MemSound.PullMix
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Pull

theorem ihStore_keeps (s : Store Nat) : KeepsCode s (ihStore s) := by
  unfold ihStore
  cases s.mems[0]? with
  | none => exact ⟨rfl, rfl⟩
  | some mi =>
    simp only [Option.bind_some]
    cases Memory.store mi.bytes 0 (count := PackSize.i16.width / 8)
        ((0x6869 : BitVec 32).setWidth _) with
    | none => exact ⟨rfl, rfl⟩
    | some b => simp [KeepsCode, Store.setMem]

theorem ihStore_grows (s : Store Nat) : MemGrows s (ihStore s) := by
  intro mi hmi
  unfold ihStore
  rw [hmi]
  simp only [Option.bind_some]
  rcases hst : Memory.store mi.bytes 0 (count := PackSize.i16.width / 8)
      ((0x6869 : BitVec 32).setWidth _) with _ | b
  · exact ⟨mi, by simpa using hmi, le_rfl⟩
  · refine ⟨{ mi with bytes := b }, ?_, (Silmaril.Wasm.Logic.Core.size_store hst).ge⟩
    have hl : 0 < s.mems.length := by
      rcases hs : s.mems with _ | ⟨x, xs⟩
      · rw [hs] at hmi; cases hmi
      · simp
    simp [Store.setMem, hl]

/-- `staleEnv q` is admitted by `blobReply`. -/
theorem staleEnv_reply (q : BitVec 32) (s : Store Nat) : ReplyEnvs blobReply s (staleEnv q) := by
  have hread : ∀ (e : UCall Nat), e.target = 0 → e.args = [.i32 0, .i32 16] →
      ∀ vs, Result.values [.i32 2] = .values vs →
      (e.target = 0 → ∃ n, vs = [.i32 n] ∧ ∀ p c, e.args = [.i32 p, .i32 c] →
        n.toNat ≤ c.toNat) ∧ (e.target = 1 → ∃ h, vs = [.i32 h]) ∧ (e.target = 2 → vs = []) := by
    intro e h0 ha vs hv
    cases hv
    refine ⟨fun _ => ⟨2, rfl, fun p c hpc => ?_⟩, fun h => ?_, fun h => ?_⟩
    · rw [ha] at hpc
      have hc : Callout.i32? (Val.i32 16) = Callout.i32? (Val.i32 c) :=
        congrArg Callout.i32? (List.cons.inj (List.cons.inj hpc).2).1
      obtain rfl : (16 : BitVec 32) = c := Option.some.inj hc
      decide
    · rw [h0] at h; cases h
    · rw [h0] at h; cases h
  rintro k e a _ ⟨-, ⟨-, h0, ha, rfl⟩ | ⟨-, h1, rfl⟩ | ⟨-, h0, ha, rfl⟩ | ⟨-, h1, rfl⟩ |
    ⟨-, h2, rfl⟩⟩
  · exact ⟨hiStore_keeps _, hiStore_grows _, hread e h0 ha⟩
  · exact ⟨⟨rfl, rfl⟩, fun mi h => ⟨mi, h, le_rfl⟩, fun vs hv => by cases hv⟩
  · exact ⟨ihStore_keeps _, ihStore_grows _, hread e h0 ha⟩
  · refine ⟨⟨rfl, rfl⟩, fun mi h => ⟨mi, h, le_rfl⟩, fun vs hv => ?_⟩
    cases hv
    refine ⟨fun h => ?_, fun _ => ⟨q, rfl⟩, fun h => ?_⟩
    · rw [h1] at h; cases h
    · rw [h1] at h; cases h
  · refine ⟨⟨rfl, rfl⟩, fun mi h => ⟨mi, h, le_rfl⟩, fun vs hv => ?_⟩
    cases hv
    refine ⟨fun h => ?_, fun h => ?_, fun _ => rfl⟩
    · rw [h2] at h; cases h
    · rw [h2] at h; cases h

/-- The byte atom `69 68` as a memory atom. -/
abbrev ihBytes : MemAtom := ⟨.bytes, by decide, [0x69, 0x68]⟩

/-- **The mixed trace of the stale session.** -/
theorem stale_traces (P : Profile) (q : BitVec 32) :
    [.w .enter, .p (.feed [0x68, 0x69]), .w .enter, .p (.feed [0x69, 0x68]),
      .w (.write (.atom ihBytes) [] q), .p (.finish 2 q)] ∈
      mixTraces P (ReplyEnvs blobReply) 0 blobEcho {} {} := by
  obtain ⟨mt, Is, c₀, hI⟩ := spec_exists beSpec_some
  obtain ⟨c, st, hp, rfl, -, -⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, -, hml, -⟩ := be_facts hp
  obtain ⟨mi, hmis, hsize⟩ := one_page beMem hp
  rw [show c.withStart none = c from rfl] at hI
  have hmem0 : c.frame.module.mems[0]? = some 0 := by rw [hmems]; rfl
  have hmi : c.store.mems[0]? = some mi := by rw [hmis]; rfl
  -- the first chunk
  obtain ⟨b, hst⟩ := store_some (B := mi.bytes) (a := 0) (n := PackSize.i16.width / 8)
    ((0x6968 : BitVec 32).setWidth _) (by rw [hsize]; decide)
  have hz : b.size = 65536 := (Silmaril.Wasm.Logic.Core.size_store hst).trans hsize
  have hs₁ : hiStore c.store = c.store.setMem 0 { mi with bytes := b } := by
    simp only [hiStore, hmi, hst, Option.bind_some, Option.map_some, Option.getD_some]
  obtain ⟨hm₁', hl₁, -⟩ := setMem_mems (mi := { mi with bytes := b }) hml
  have hm : memOf (some 0) (hiStore c.store) = some b := by rw [hs₁]; exact memOf_setMem hml
  have hseg : segOf b 0 2 = some [0x68, 0x69] := by
    unfold segOf
    rw [readBytes_toList (by rw [hz]; decide)]
    exact congrArg some ((Silmaril.Wasm.Logic.Core.bytesAt_store_same hst).trans (by decide))
  have t₀ : TSession P (staleEnv q) blobEcho (some 0) mR c (0 : Nat) Is.addrs .inst false
      (c, (0 : Nat)) [] :=
    .start
  have t₁ := be_trap_round (L := staleEnv q) (k₀ := (0 : Nat)) (k₁ := (1 : Nat)) (k₂ := (2 : Nat))
    hI hp t₀ (by decide)
    ⟨[], hcode⟩ rfl (hiStore_keeps c.store).1 hm hseg ⟨rfl, .inl ⟨rfl, rfl, rfl, rfl⟩⟩
    ⟨rfl, .inr (.inl ⟨rfl, rfl, rfl⟩)⟩
  -- the second chunk
  let s₁ := hiStore c.store
  have hmi₁ : s₁.mems[0]? = some { mi with bytes := b } := by
    show (hiStore c.store).mems[0]? = _; rw [hs₁]; exact hm₁'
  have hl₁' : s₁.mems.length = 1 := by show (hiStore c.store).mems.length = 1; rw [hs₁]; exact hl₁
  obtain ⟨b', hst'⟩ := store_some (B := b) (a := 0) (n := PackSize.i16.width / 8)
    ((0x6869 : BitVec 32).setWidth _) (by rw [hz]; decide)
  have hz' : b'.size = 65536 := (Silmaril.Wasm.Logic.Core.size_store hst').trans hz
  have hs₂ : ihStore s₁ = s₁.setMem 0 { mi with bytes := b' } := by
    simp only [ihStore, hmi₁, hst', Option.bind_some, Option.map_some, Option.getD_some]
  have hm' : memOf (some 0) (ihStore s₁) = some b' := by rw [hs₂]; exact memOf_setMem hl₁'
  have hseg' : segOf b' 0 2 = some [0x69, 0x68] := by
    unfold segOf
    rw [readBytes_toList (by rw [hz']; decide)]
    exact congrArg some ((Silmaril.Wasm.Logic.Core.bytesAt_store_same hst').trans (by decide))
  obtain ⟨c'', t₂⟩ := be_round (L := staleEnv q) (k₀ := (2 : Nat)) (k₁ := (3 : Nat))
    (k₂ := (4 : Nat)) (h := q) hI hp t₁
    (by decide) ⟨.trap, rfl⟩ (hiStore_keeps c.store).1
    ((ihStore_keeps s₁).1.trans (hiStore_keeps c.store).1) hm' hseg'
    ⟨rfl, .inr (.inr (.inl ⟨rfl, rfl, rfl, rfl⟩))⟩ ⟨rfl, .inr (.inr (.inr (.inl ⟨rfl, rfl, rfl⟩)))⟩
  refine ⟨_, ⟨mt, Is, c, hI, staleEnv q, (0 : Nat), staleEnv_reply q _, .run, true, _,
    by rw [hmem0]; exact t₂⟩, ?_⟩
  rfl

/-- **The stale pair**: `blobEcho` relates `68 69` to the byte atom `69 68`, for every profile
and every pair of policies whose sentinels are not the handle `q`. -/
theorem be_stale (P : Profile) (pol : Policy (BitVec 32)) (ppol : PPolicy (BitVec 32))
    {q : BitVec 32} (hq : pol.sentinel ≠ some q) (hpq : ppol.sentinel ≠ q) :
    (([0x68, 0x69] : List UInt8), bytesAtom [0x69, 0x68]) ∈
      memMixedRel P (ReplyEnvs blobReply) 0 blobEcho {} {} pol ppol := by
  let σ : Env (BitVec 32) SymStrBytesSExp :=
    Function.update Env.empty q (some (.atom ihBytes))
  have hres : resolve ppol σ ([0x68, 0x69] : List UInt8) q =
      some {(([0x68, 0x69] : List UInt8), bytesAtom [0x69, 0x68])} := by
    unfold resolve
    split_ifs with h
    · exact absurd h.symm hpq
    · simp [σ, bytesAtom]
  let B : Set SymStrBytesSExp := insert (.atom ihBytes) ∅
  let H := mixed (V := UInt8) (sexpW MemAtom) pol ppol
  have r₆ : H.Run ⟨⟨σ, B, .live⟩, ⟨[], [0x68, 0x69, 0x69, 0x68], .live⟩⟩ [.p (.finish 2 q)]
      ⟨⟨σ, B, .live⟩, ⟨[], [0x69, 0x68], .live⟩⟩
      ({(([0x68, 0x69] : List UInt8), bytesAtom [0x69, 0x68])} ∪ ∅) :=
    .cons (.p rfl (.ret (s := ⟨[], [0x68, 0x69, 0x69, 0x68], .live⟩) (e := .finish 2 q)
      (w := [0x68, 0x69]) (h := q) rfl ⟨by decide, rfl, rfl, rfl⟩ hres)) (.nil _)
  have r₅ : H.Run ⟨⟨Env.empty, ∅, .live⟩, ⟨[], [0x68, 0x69, 0x69, 0x68], .live⟩⟩
      [.w (.write (.atom ihBytes) [] q), .p (.finish 2 q)]
      ⟨⟨σ, B, .live⟩, ⟨[], [0x69, 0x68], .live⟩⟩
      (chaosPairs .live ∪ ({(([0x68, 0x69] : List UInt8), bytesAtom [0x69, 0x68])} ∪ ∅)) :=
    .cons (.w (.writeOk (t := (.atom ihBytes : SymStrBytesSExp)) rfl ⟨hq, .inl rfl⟩
      fun _ h => by cases h)) r₆
  have r₄ : H.Run ⟨⟨Env.empty, ∅, .live⟩, ⟨[], [0x68, 0x69], .live⟩⟩
      [.p (.feed [0x69, 0x68]), .w (.write (.atom ihBytes) [] q), .p (.finish 2 q)]
      ⟨⟨σ, B, .live⟩, ⟨[], [0x69, 0x68], .live⟩⟩
      (∅ ∪ (chaosPairs .live ∪
        ({(([0x68, 0x69] : List UInt8), bytesAtom [0x69, 0x68])} ∪ ∅))) :=
    .cons (.p (ws := WState.init) rfl (.feed _)) r₅
  have hrun : H.Run MState.init
      [.w .enter, .p (.feed [0x68, 0x69]), .w .enter, .p (.feed [0x69, 0x68]),
        .w (.write (.atom ihBytes) [] q), .p (.finish 2 q)]
      ⟨⟨σ, B, .live⟩, ⟨[], [0x69, 0x68], .live⟩⟩
      (chaosPairs .live ∪ (∅ ∪ (chaosPairs .live ∪ (∅ ∪ (chaosPairs .live ∪
        ({(([0x68, 0x69] : List UInt8), bytesAtom [0x69, 0x68])} ∪ ∅)))))) :=
    .cons (.w .enter) (.cons (.p (ws := WState.init) rfl (.feed _)) (.cons (.w .enter) r₄))
  simp only [memMixedRel, mixedRel, Host.lang]
  exact Set.mem_biUnion (stale_traces P q) ⟨_, _, hrun, by simp⟩

/-- **`blobEcho` is not exact** against all admitted hosts. -/
theorem be_not_exact (P : Profile) (pol : Policy (BitVec 32)) (ppol : PPolicy (BitVec 32))
    {q : BitVec 32} (hq : pol.sentinel ≠ some q) (hpq : ppol.sentinel ≠ q) :
    ¬ memMixedRel P (ReplyEnvs blobReply) 0 blobEcho {} {} pol ppol ⊆ exactRel := fun h => by
  have := h (be_stale P pol ppol hq hpq)
  simp [exactRel, bytesAtom] at this

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.PullMix
