module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ExactLive

/-!
# Proofs: replayed sessions of `drainEcho`

* `de_traces_hi`: against `hiEnv q`, one invocation: the drain on the empty buffer, the chunk
  `68 69`, the write of its atom with handle `q`, `finish(2, q)`;
* `de_traces_two`: against `twoEnv q₁ q₂`, two invocations reading `68 69`, then `69 68`;
* `de_traces_trap`: against `trapEnv q`, a first invocation whose `blob` traps after reading
  `68 69`, then a second one: its drain meets the two stale bytes, then it reads `69 68`.

The mixed runs: the drain overruns on an empty buffer (`onOverrun` `callTrap` or `ignore`
answers an overrun with nothing and keeps the cursor); in the stale session `finish(2, z)`
consumes `68 69`, relating nothing (`z` is the parser's sentinel), and `finish(2, q)` relates
`69 68` to its atom (`de_after_trap`), where `blobEcho` relates `68 69` to it
(`PullMix.be_stale`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Exact

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game
  Silmaril.Wasm.Game.Accept Silmaril.Wasm.Game.IOAccept Silmaril.Accept Silmaril.Accept.Handle
  Silmaril.Accept.IO Silmaril.Accept.Parse Silmaril.Accept.Mixed Silmaril.Formats
  Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.Pull
  Silmaril.Wasm.Game.HandleAccept.MemSound.PullMix Silmaril.Wasm.Game.HandleAccept.MemSound.Exact
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live

/-- **The spec instance of `drainEcho z` exists for every sentinel `z`** (kernel evaluation with
`z` free: neither the validator nor the instantiation reads the value of an `i32.const`). -/
theorem deSpec_all (z : BitVec 32) :
    (Silmaril.Wasm.Verify.specInstance? (drainEcho z)).isSome = true := by
  kernel_rfl

/-- The mixed events of the drain. -/
abbrev drainEvs (z : BitVec 32) : List MixEv :=
  [.p (.finish 16 z), .p (.finish 8 z), .p (.finish 4 z), .p (.finish 2 z), .p (.finish 1 z)]

/-- The mixed events of the tail reading `cs`, writing its atom with handle `h`. -/
abbrev tailEvs (cs : List UInt8) (h : BitVec 32) : List MixEv :=
  [.p (.feed cs), .w (.write (.atom ⟨.bytes, by decide, cs⟩) [] h), .p (.finish 2 h)]

/-! ## Memory after the scripted reads -/

/-- The bytes `68 69` written by `hiStore` into a one-page memory. -/
theorem hi_mem {s : Store Nat} {mi : MemInst} (hml : s.mems.length = 1)
    (hmi : s.mems[0]? = some mi) (hsize : mi.bytes.size = 65536) :
    ∃ b, memOf (some 0) (hiStore s) = some b ∧ segOf b 0 2 = some [0x68, 0x69] ∧
      (hiStore s).mems.length = 1 ∧ (hiStore s).mems[0]? = some { mi with bytes := b } ∧
      b.size = 65536 := by
  obtain ⟨b, hst⟩ := store_some (B := mi.bytes) (a := 0) (n := PackSize.i16.width / 8)
    ((0x6968 : BitVec 32).setWidth _) (by rw [hsize]; decide)
  have hz : b.size = 65536 := (Silmaril.Wasm.Logic.Core.size_store hst).trans hsize
  have hs₁ : hiStore s = s.setMem 0 { mi with bytes := b } := by
    simp only [hiStore, hmi, hst, Option.bind_some, Option.map_some, Option.getD_some]
  obtain ⟨hm₁', hl₁, -⟩ := setMem_mems (mi := { mi with bytes := b }) hml
  refine ⟨b, by rw [hs₁]; exact memOf_setMem hml, ?_, by rw [hs₁]; exact hl₁,
    by rw [hs₁]; exact hm₁', hz⟩
  unfold segOf
  rw [readBytes_toList (by rw [hz]; decide)]
  exact congrArg some ((Silmaril.Wasm.Logic.Core.bytesAt_store_same hst).trans (by decide))

/-- The bytes `69 68` written by `ihStore` into a one-page memory. -/
theorem ih_mem {s : Store Nat} {mi : MemInst} (hml : s.mems.length = 1)
    (hmi : s.mems[0]? = some mi) (hsize : mi.bytes.size = 65536) :
    ∃ b, memOf (some 0) (ihStore s) = some b ∧ segOf b 0 2 = some [0x69, 0x68] ∧
      (ihStore s).mems.length = 1 ∧ (ihStore s).mems[0]? = some { mi with bytes := b } ∧
      b.size = 65536 := by
  obtain ⟨b, hst⟩ := store_some (B := mi.bytes) (a := 0) (n := PackSize.i16.width / 8)
    ((0x6869 : BitVec 32).setWidth _) (by rw [hsize]; decide)
  have hz : b.size = 65536 := (Silmaril.Wasm.Logic.Core.size_store hst).trans hsize
  have hs₁ : ihStore s = s.setMem 0 { mi with bytes := b } := by
    simp only [ihStore, hmi, hst, Option.bind_some, Option.map_some, Option.getD_some]
  obtain ⟨hm₁', hl₁, -⟩ := setMem_mems (mi := { mi with bytes := b }) hml
  refine ⟨b, by rw [hs₁]; exact memOf_setMem hml, ?_, by rw [hs₁]; exact hl₁,
    by rw [hs₁]; exact hm₁', hz⟩
  unfold segOf
  rw [readBytes_toList (by rw [hz]; decide)]
  exact congrArg some ((Silmaril.Wasm.Logic.Core.bytesAt_store_same hst).trans (by decide))

/-! ## Traces -/

section Traces

variable (P : Profile) {z : BitVec 32}

/-- **One invocation against `hiEnv q`.** -/
theorem de_traces_hi (q : BitVec 32) :
    [.w .enter] ++ drainEvs z ++ tailEvs [0x68, 0x69] q ∈
      mixTraces P (ReplyEnvs blobReply) 0 (drainEcho z) {} {} := by
  have hok := deOk_all z
  obtain ⟨mt, Is, c₀, hI⟩ := spec_exists (deSpec_all z)
  obtain ⟨c, st, hp, rfl, -, -⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, -, hml, ⟨mi, hmis, hsize⟩, -⟩ := de_facts hok hp
  rw [show c.withStart none = c from rfl] at hI
  have hmem0 : c.frame.module.mems[0]? = some 0 := by rw [hmems]; rfl
  have hmi : c.store.mems[0]? = some mi := by rw [hmis]; rfl
  obtain ⟨b, hm, hseg, -⟩ := hi_mem hml hmi hsize
  have t₀ : TSession P (hiEnv q) (drainEcho z) (some 0) mR c (0 : Nat) Is.addrs .inst false
      (c, (0 : Nat)) [] := .start
  obtain ⟨F, hFf, hFl, t₁⟩ := de_invoke hok hI hp t₀ (by decide) ⟨[], hcode⟩ rfl
  have t₂ := de_drains hok hp hFf rfl t₁ (fun _ => .inl ⟨rfl, rfl, rfl⟩)
  obtain ⟨F₁, f₂, -, t₃⟩ := de_tail_call (k₂ := (1 : Nat)) hok hp hFf hFl rfl
    (Pull.hiStore_keeps c.store).1 hm hseg (h := q) t₂ (.inr (.inl ⟨rfl, rfl, rfl, rfl⟩))
    (.inr (.inr ⟨rfl, rfl, rfl⟩))
  refine ⟨_, ⟨mt, Is, c, hI, hiEnv q, (0 : Nat), hiEnv_reply q _, .run, true, _,
    by rw [hmem0]; exact t₃⟩, ?_⟩
  rfl

/-- **Two invocations against `twoEnv q₁ q₂`.** -/
theorem de_traces_two (q₁ q₂ : BitVec 32) :
    [.w .enter] ++ drainEvs z ++ tailEvs [0x68, 0x69] q₁ ++
      ([.w .enter] ++ drainEvs z ++ tailEvs [0x69, 0x68] q₂) ∈
      mixTraces P (ReplyEnvs blobReply) 0 (drainEcho z) {} {} := by
  have hok := deOk_all z
  obtain ⟨mt, Is, c₀, hI⟩ := spec_exists (deSpec_all z)
  obtain ⟨c, st, hp, rfl, -, -⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, -, hml, ⟨mi, hmis, hsize⟩, -⟩ := de_facts hok hp
  rw [show c.withStart none = c from rfl] at hI
  have hmem0 : c.frame.module.mems[0]? = some 0 := by rw [hmems]; rfl
  have hmi : c.store.mems[0]? = some mi := by rw [hmis]; rfl
  obtain ⟨b, hm, hseg, hl₁, hmi₁, hz₁⟩ := hi_mem hml hmi hsize
  have hk₁ := Pull.hiStore_keeps c.store
  obtain ⟨b', hm', hseg', -⟩ := ih_mem hl₁ hmi₁ hz₁
  have hk₂ := PullMix.ihStore_keeps (hiStore c.store)
  have t₀ : TSession P (twoEnv q₁ q₂) (drainEcho z) (some 0) mR c (0 : Nat) Is.addrs .inst
      false (c, (0 : Nat)) [] := .start
  obtain ⟨F, hFf, hFl, t₁⟩ := de_invoke hok hI hp t₀ (by decide) ⟨[], hcode⟩ rfl
  have t₂ := de_drains hok hp hFf rfl t₁ (fun _ => .inl ⟨rfl, rfl, rfl⟩)
  have t₃ := de_tail_ret (k₁ := (1 : Nat)) (k₂ := (1 : Nat)) (k₃ := (1 : Nat)) hok hp hFf hFl
    rfl hk₁.1 hm hseg (h := q₁) t₂ (.inr (.inl ⟨rfl, rfl, rfl, rfl⟩))
    (.inr (.inr ⟨rfl, rfl, rfl⟩)) (.inl ⟨rfl, rfl, rfl⟩)
  obtain ⟨F', hFf', hFl', t₄⟩ := de_invoke hok hI hp t₃ (by decide) ⟨.values [], rfl⟩ hk₁.1
  have t₅ := de_drains hok hp hFf' hk₁.1 t₄ (fun _ => .inl ⟨rfl, rfl, rfl⟩)
  obtain ⟨F₁, f₂, -, t₆⟩ := de_tail_call (k₁ := (2 : Nat)) (k₂ := (2 : Nat)) hok hp hFf' hFl'
    hk₁.1 (hk₂.1.trans hk₁.1) hm' hseg' (h := q₂) t₅ (.inr (.inl ⟨rfl, rfl, rfl, rfl⟩))
    (.inr (.inr ⟨rfl, rfl, rfl⟩))
  refine ⟨_, ⟨mt, Is, c, hI, twoEnv q₁ q₂, (0 : Nat), twoEnv_reply q₁ q₂ _, .run, true, _,
    by rw [hmem0]; exact t₆⟩, ?_⟩
  rfl

/-- **The stale session against `trapEnv q`.** -/
theorem de_traces_trap (q : BitVec 32) :
    [.w .enter] ++ drainEvs z ++ [.p (.feed [0x68, 0x69])] ++
      ([.w .enter] ++ drainEvs z ++ tailEvs [0x69, 0x68] q) ∈
      mixTraces P (ReplyEnvs blobReply) 0 (drainEcho z) {} {} := by
  have hok := deOk_all z
  obtain ⟨mt, Is, c₀, hI⟩ := spec_exists (deSpec_all z)
  obtain ⟨c, st, hp, rfl, -, -⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, -, hml, ⟨mi, hmis, hsize⟩, -⟩ := de_facts hok hp
  rw [show c.withStart none = c from rfl] at hI
  have hmem0 : c.frame.module.mems[0]? = some 0 := by rw [hmems]; rfl
  have hmi : c.store.mems[0]? = some mi := by rw [hmis]; rfl
  obtain ⟨b, hm, hseg, hl₁, hmi₁, hz₁⟩ := hi_mem hml hmi hsize
  have hk₁ := Pull.hiStore_keeps c.store
  obtain ⟨b', hm', hseg', -⟩ := ih_mem hl₁ hmi₁ hz₁
  have hk₂ := PullMix.ihStore_keeps (hiStore c.store)
  have t₀ : TSession P (trapEnv q) (drainEcho z) (some 0) mR c (0 : Nat) Is.addrs .inst
      false (c, (0 : Nat)) [] := .start
  obtain ⟨F, hFf, hFl, t₁⟩ := de_invoke hok hI hp t₀ (by decide) ⟨[], hcode⟩ rfl
  have t₂ := de_drains hok hp hFf rfl t₁ (fun _ => .inl ⟨rfl, rfl, rfl⟩)
  have t₃ := de_tail_trap (k₁ := (1 : Nat)) (k₂ := (1 : Nat)) hok hp hFf hFl rfl hk₁.1 hm hseg
    t₂ (.inr (.inl ⟨rfl, rfl, rfl, rfl⟩)) (.inr (.inr ⟨rfl, rfl, rfl⟩))
  obtain ⟨F', hFf', hFl', t₄⟩ := de_invoke hok hI hp t₃ (by decide) ⟨.trap, rfl⟩ hk₁.1
  have t₅ := de_drains hok hp hFf' hk₁.1 t₄ (fun _ => .inl ⟨rfl, rfl, rfl⟩)
  obtain ⟨F₁, f₂, -, t₆⟩ := de_tail_call (k₁ := (2 : Nat)) (k₂ := (2 : Nat)) hok hp hFf' hFl'
    hk₁.1 (hk₂.1.trans hk₁.1) hm' hseg' (h := q) t₅ (.inr (.inl ⟨rfl, rfl, rfl, rfl⟩))
    (.inr (.inr ⟨rfl, rfl, rfl⟩))
  refine ⟨_, ⟨mt, Is, c, hI, trapEnv q, (0 : Nat), trapEnv_reply q _, .run, true, _,
    by rw [hmem0]; exact t₆⟩, ?_⟩
  rfl

end Traces

/-! ## Mixed runs -/

section Runs

variable {z : BitVec 32} {pol : Policy (BitVec 32)} {ppol : PPolicy (BitVec 32)}

/-- The mixed host of the sessions. -/
abbrev MH (pol : Policy (BitVec 32)) (ppol : PPolicy (BitVec 32)) :=
  mixed (V := UInt8) (sexpW MemAtom) pol ppol

/-- **The drain on an empty buffer** overruns five times, relating nothing and keeping the
cursor. -/
theorem drains_overrun (hov : ppol.onOverrun = .ignore ∨ ppol.onOverrun = .callTrap)
    {ws : WState (BitVec 32) SymStrBytesSExp} (hl : ws.phase = .live)
    {s' : MState UInt8 (BitVec 32) SymStrBytesSExp} {rest : List MixEv}
    {A : Set (List UInt8 × SymStrBytesSExp)}
    (hr : (MH pol ppol).Run ⟨ws, ⟨[], [], .live⟩⟩ rest s' A) :
    (MH pol ppol).Run ⟨ws, ⟨[], [], .live⟩⟩ (drainEvs z ++ rest) s'
      (∅ ∪ (∅ ∪ (∅ ∪ (∅ ∪ (∅ ∪ A))))) :=
  .cons (.p hl (.overrunIgnore (by decide) hov)) (.cons (.p hl (.overrunIgnore (by decide) hov))
    (.cons (.p hl (.overrunIgnore (by decide) hov)) (.cons (.p hl (.overrunIgnore (by decide) hov))
      (.cons (.p hl (.overrunIgnore (by decide) hov)) hr))))

/-- **The drain on the two stale bytes `68 69`**: `finish(16, z)`, `finish(8, z)`, `finish(4, z)`
overrun, `finish(2, z)` consumes the stale bytes relating nothing (`z` is the sentinel),
`finish(1, z)` overruns. -/
theorem drains_stale (hz : ppol.sentinel = z)
    (hov : ppol.onOverrun = .ignore ∨ ppol.onOverrun = .callTrap)
    {ws : WState (BitVec 32) SymStrBytesSExp} (hl : ws.phase = .live)
    {s' : MState UInt8 (BitVec 32) SymStrBytesSExp} {rest : List MixEv}
    {A : Set (List UInt8 × SymStrBytesSExp)}
    (hr : (MH pol ppol).Run ⟨ws, ⟨[], [], .live⟩⟩ rest s' A) :
    (MH pol ppol).Run ⟨ws, ⟨[], [0x68, 0x69], .live⟩⟩ (drainEvs z ++ rest) s'
      (∅ ∪ (∅ ∪ (∅ ∪ (∅ ∪ (∅ ∪ A))))) :=
  .cons (.p hl (.overrunIgnore (by decide) hov)) (.cons (.p hl (.overrunIgnore (by decide) hov))
    (.cons (.p hl (.overrunIgnore (by decide) hov))
      (.cons (.p hl (.ret (s := ⟨[], [0x68, 0x69], .live⟩) (e := .finish 2 z) (w := [0x68, 0x69])
          (h := z) rfl ⟨by decide, rfl, rfl, rfl⟩ (by simp [resolve, hz])))
        (.cons (.p hl (.overrunIgnore (by decide) hov)) hr))))

/-- The tail: a chunk `cs`, the write of its atom with a fresh handle `q`, `finish(2, q)`
relating `cs` to its atom. -/
theorem tail_run {σ : Env (BitVec 32) SymStrBytesSExp} {B : Set SymStrBytesSExp}
    {cs : List UInt8} (hcs : cs.length = 2) {q : BitVec 32} (hq : pol.sentinel ≠ some q)
    (hpq : ppol.sentinel ≠ q) (hfresh : σ q = none) :
    (MH pol ppol).Run ⟨⟨σ, B, .live⟩, ⟨[], [], .live⟩⟩ (tailEvs cs q)
      ⟨⟨Function.update σ q (some (.atom ⟨.bytes, by decide, cs⟩)),
        insert (.atom ⟨.bytes, by decide, cs⟩) B, .live⟩, ⟨[], [], .live⟩⟩
      (∅ ∪ (chaosPairs .live ∪ ({(cs, bytesAtom cs)} ∪ ∅))) := by
  have hres : resolve ppol (Function.update σ q (some (.atom ⟨.bytes, by decide, cs⟩))) cs q =
      some {(cs, bytesAtom cs)} := by
    unfold resolve
    split_ifs with h
    · exact absurd h.symm hpq
    · simp [bytesAtom]
  refine .cons (.p (ws := ⟨σ, B, .live⟩) rfl (.feed _)) (.cons (.w (.writeOk
    (t := (.atom ⟨.bytes, by decide, cs⟩ : SymStrBytesSExp)) rfl ⟨hq, .inl hfresh⟩
      fun _ h => by cases h)) (.cons (.p rfl (.ret (s := ⟨[], cs, .live⟩) (e := .finish 2 q)
        (w := cs) (h := q) rfl ⟨by rw [hcs], ?_, rfl, ?_⟩ hres)) (.nil _)))
  · rw [List.take_of_length_le (by rw [hcs])]
  · rw [List.drop_of_length_le (by rw [hcs])]

end Runs

/-! ## Related pairs -/

section Pairs

variable (P : Profile) {z : BitVec 32} (pol : Policy (BitVec 32)) (ppol : PPolicy (BitVec 32))

/-- **`drainEcho z` relates `68 69` to the byte atom `68 69`** (one invocation against
`hiEnv q`). -/
theorem de_live {q : BitVec 32} (hq : pol.sentinel ≠ some q)
    (hpq : ppol.sentinel ≠ q) (hov : ppol.onOverrun = .ignore ∨ ppol.onOverrun = .callTrap) :
    (([0x68, 0x69] : List UInt8), bytesAtom [0x68, 0x69]) ∈
      memMixedRel P (ReplyEnvs blobReply) 0 (drainEcho z) {} {} pol ppol := by
  have r := drains_overrun (z := z) hov (ws := WState.init) rfl
    (tail_run (σ := Env.empty) (B := ∅) (cs := [0x68, 0x69]) rfl hq hpq rfl)
  have hrun := Host.Run.cons (h := MH pol ppol) (s := MState.init) (.w .enter) r
  simp only [memMixedRel, mixedRel, Host.lang]
  exact Set.mem_biUnion (de_traces_hi P q) ⟨_, _, hrun, by simp⟩

/-- **Repeated invocations**: against `twoEnv q₁ q₂`, the second invocation relates `69 68` to
the byte atom `69 68`. -/
theorem de_repeat {q₁ q₂ : BitVec 32}
    (hq₁ : pol.sentinel ≠ some q₁) (hpq₁ : ppol.sentinel ≠ q₁) (hq₂ : pol.sentinel ≠ some q₂)
    (hpq₂ : ppol.sentinel ≠ q₂) (hne : q₂ ≠ q₁)
    (hov : ppol.onOverrun = .ignore ∨ ppol.onOverrun = .callTrap) :
    (([0x69, 0x68] : List UInt8), bytesAtom [0x69, 0x68]) ∈
      memMixedRel P (ReplyEnvs blobReply) 0 (drainEcho z) {} {} pol ppol := by
  have r₂ := drains_overrun (z := z) hov rfl
    (tail_run (σ := Function.update Env.empty q₁ (some (.atom ⟨.bytes, by decide, [0x68, 0x69]⟩)))
      (B := insert (.atom ⟨.bytes, by decide, [0x68, 0x69]⟩) ∅) (cs := [0x69, 0x68]) rfl hq₂ hpq₂
      (by simp [Function.update_of_ne hne, Env.empty]))
  have r₂' := Host.Run.cons (h := MH pol ppol)
    (s := ⟨⟨Function.update Env.empty q₁ (some (.atom ⟨.bytes, by decide, [0x68, 0x69]⟩)),
      insert (.atom ⟨.bytes, by decide, [0x68, 0x69]⟩) ∅, .live⟩, ⟨[], [], .live⟩⟩) (.w .enter) r₂
  have r₁ := drains_overrun (z := z) hov (ws := WState.init) rfl
    (Host.Run.append (tail_run (σ := Env.empty) (B := ∅) (cs := [0x68, 0x69]) rfl hq₁ hpq₁ rfl)
      r₂')
  have hrun := Host.Run.cons (h := MH pol ppol) (s := MState.init) (.w .enter) r₁
  simp only [memMixedRel, mixedRel, Host.lang]
  exact Set.mem_biUnion (de_traces_two P q₁ q₂) ⟨_, _, hrun, by simp⟩

/-- **After an interrupted invocation**: against `trapEnv q` (the first `blob` traps after `read`
answered `68 69`), the second invocation drains the stale bytes and relates `69 68` to the byte
atom `69 68`. -/
theorem de_after_trap (hsz : ppol.sentinel = z) {q : BitVec 32}
    (hq : pol.sentinel ≠ some q) (hpq : ppol.sentinel ≠ q)
    (hov : ppol.onOverrun = .ignore ∨ ppol.onOverrun = .callTrap) :
    (([0x69, 0x68] : List UInt8), bytesAtom [0x69, 0x68]) ∈
      memMixedRel P (ReplyEnvs blobReply) 0 (drainEcho z) {} {} pol ppol := by
  have r₂ := drains_stale (z := z) hsz hov (ws := WState.init) rfl
    (tail_run (σ := Env.empty) (B := ∅) (cs := [0x69, 0x68]) rfl hq hpq rfl)
  have r₂' := Host.Run.cons (h := MH pol ppol)
    (s := ⟨WState.init, ⟨[], [0x68, 0x69], .live⟩⟩) (.w .enter) r₂
  have r₁ := drains_overrun (z := z) hov (ws := WState.init) rfl
    (Host.Run.cons (h := MH pol ppol) (.p (ws := WState.init) rfl (.feed [0x68, 0x69])) r₂')
  have hrun := Host.Run.cons (h := MH pol ppol) (s := MState.init) (.w .enter) r₁
  simp only [memMixedRel, mixedRel, Host.lang]
  exact Set.mem_biUnion (de_traces_trap P q) ⟨_, _, hrun, by simp⟩

end Pairs

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Exact
